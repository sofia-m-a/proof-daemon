{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveGeneric, DeriveTraversable,
    FlexibleInstances, LambdaCase, MultiWayIf, OverloadedStrings, TupleSections #-}

-- a theorem prover for intuitionistic propositional logic,
-- based on:
-- Contraction-Free Sequent Calculi for Intuitionistic Logic
-- Author(s): Roy Dyckhoff
-- Source: The Journal of Symbolic Logic, Vol. 57, No. 3 (Sep., 1992), pp. 795-807
-- Published by: Association for Symbolic Logic
-- Stable URL: http://www.jstor.org/stable/2275431 
module Main where

import Control.Monad (forever, when, (>=>))
import Control.Monad.Except
    ( forever, when, runExcept, MonadError(throwError), Except )
import Control.Monad.State
    ( forever,
      when,
      gets,
      modify,
      MonadState(put, get),
      StateT(runStateT) )
import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isSpace)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.List (genericIndex, isPrefixOf, stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Monoid (Endo(..))
import Data.String (fromString, IsString)
import Debug.Trace
import Generic.Random (genericArbitraryRec, uniform)
import GHC.Generics (Generic)
import System.Exit ( exitSuccess )
import System.IO (hFlush, stdout)
import Test.QuickCheck ( Arbitrary(arbitrary) )

type Nat = Word

data Command
    = AxiomC Nat Prop
    | QueryC Prop
    | HelpC
    | ClearC
    | EmptyC
    | ErrorC
    | Quit
    deriving Show

main :: IO ()
main = loop Map.empty Map.empty Map.empty

loop
    :: SymbolTable    -- maps strings to simple Nats
    -> Map Nat String -- maps Nats (interned strings) back to strings
    -> Map Prop Nat   -- axioms: each proposition is mapped to the name of the axiom
    -> IO ()
loop syms names axioms = forever $ do
    putStr "command: "
    hFlush stdout
    l <- getLine
    case parse l syms names of
        Left (error, loc) -> putStrLn $
            unwords ["error at column", show loc, ":", error]
        
        Right (cmd, syms, names) -> case cmd of
            AxiomC n p -> loop syms names (Map.insert p n axioms)

            QueryC p ->
                let context = Map.map (const 0) axioms in
                case search (Sequent context p) of
                    Just proof ->
                        let
                        -- get names of axioms
                        ax = runIdentity $ 
                            Map.traverseMaybeWithKey 
                            (\_ a -> Identity $ Map.lookup a names) axioms
                        in
                        do
                            putStrLn (extractProof proof ax)
                            loop syms names axioms
                    Nothing -> putStrLn "no proof ☹" >> loop syms names axioms
            
            HelpC -> putStrLn $ unlines
                [ "commands:"
                    , "\thelp\t: shows this message"
                    , "\t? prop\t: tries to prove prop given the axioms"
                    , "\taxiom name: prop\t: adds an axiom to the context."
                        , "\t\tthe name is used for proof extraction"
                    , "\tclear\t: clears all axioms"
                    , "\tquit\t: quits"
                , ""
                , "proposition syntax:"
                    , "\tfalse: false proposition"
                    , "\tA|B: disjunction/or"
                    , "\tA&B: conjunction/and"
                    , "\tA->B: implication"
                    , "\t(A): grouping"
                    , "\t<sequence of alphanumeric characters>: atomic proposition"
                , ""
                    , "\t-> binds the tightest; & and | cannot be mixed"
                , ""
                , "Note: the extracted proofs can be overly complex, because"
                , "no simplification pass is performed"
                ]
            
            ClearC -> loop syms names Map.empty
            EmptyC -> loop syms names axioms
            ErrorC -> putStrLn "unrecognized command" >> loop syms names axioms
            Quit -> exitSuccess

data Prop
    = Absurd
    | Disj Prop Prop
    | Conj Prop Prop
    | Impl Prop Prop
    | Atomic Nat
    deriving (Eq, Ord, Show, Generic)

instance Arbitrary Prop where
    arbitrary = genericArbitraryRec uniform

-- we use this both for uncompleted trees:
-- Proof Sequent - each Sequent is a proof obligation
-- and completed trees:
-- Proof (Proof (Proof ...)) all the way down
-- (we need a newtype for this)
data Proof p
    = Axiom Nat
    | Absurdity Prop
    | ConjL (Prop, Prop) p
    | ConjR p p
    | DisjL (Prop, Prop) p p
    | DisjR1 p
    | DisjR2 p
    | ImplR Prop p
    -- ImplL is the awkward one!
    -- it gets split into cases
    | ImplLAtomic (Prop, Prop) p
    --             ↓ the two propositions making up the implication
    -- the two propositions making ↓ up the thing we're eliminating
    | ImplLConj   (Prop, Prop,     Prop, Prop             ) p
    | ImplLDisj   (Prop, Prop,     Prop, Prop             ) p
    | ImplLImpl   (Prop, Prop,     Prop, Prop             ) p p
    deriving (Show, Functor, Foldable, Traversable)

-- (greatest) fixed point of proof type; no proof obligations left
newtype CompleteProof = CompleteProof { uncompleteProof :: Proof CompleteProof }
    deriving (Show)

roll :: Proof CompleteProof -> CompleteProof
roll = CompleteProof
unroll :: CompleteProof -> Proof CompleteProof
unroll = uncompleteProof
cata :: (Proof a -> a) -> CompleteProof -> a
cata f = f . fmap (cata f) . unroll

-- multiset of Props
-- we maintain the invariant that each Prop maps to its occurences + 1,
-- so that we never have redundant prop => 0 entries
type Context = Map Prop Nat

look :: Context -> Prop -> Nat
look c prop = maybe 0 (+1) (Map.lookup prop c)

putP :: Prop -> (Context -> Context)
putP p c = case look c p of
    0 -> Map.insert p 0 c
    _ -> Map.adjust (+1) p c

elim1 :: Prop -> (Context -> Context)
elim1 p c = case look c p of
    0 -> c
    1 -> Map.delete p c
    _ -> Map.adjust (subtract 1) p c

-- elim1 clearly doesn't examine prop so any prop is fine
prop_context :: Context -> Bool
prop_context c =
    let
    prop = Absurd
    p = putP prop c
    p1 = elim1 prop p
    in
    look c prop == look p1 prop
    && look p prop == look c prop + 1

data Sequent = Sequent Context Prop
    deriving (Show)

-- all the ways we could prove the sequent.
-- iterating this is bounded by the size of the initial sequent
-- (see the paper for proof)
analyze :: Sequent -> [Proof Sequent]
analyze (Sequent c p)
    = case p of
        -- C, A => A
        Atomic n | look c p /= 0 -> (Axiom n:)
        -- C => A&B if C => A and C => B
        Conj a b -> (ConjR (Sequent c a) (Sequent c b):)
        -- C => A|B if C => A
        -- C => A|B if C => B
        Disj a b -> (DisjR1 (Sequent c a):) . (DisjR2 (Sequent c b):)
        -- C => A->B if C, A => B
        Impl a b -> (ImplR a (Sequent (putP a c) b):)
        _ -> id
    
    $ concatMap (\prop -> let d = elim1 prop c in case prop of
        -- C, false => P
        Absurd -> [Absurdity p]
        -- C, A|B => P if C, A => P and C, B => P
        Disj a b -> [DisjL (a, b) (Sequent (putP a d) p) (Sequent (putP b d) p)]
        -- C, A&B => P if C, A, B => P
        Conj a b -> [ConjL (a, b) (Sequent (putP a . putP b $ d) p)]
        -- now for the tricky stuff...

        -- Logic background
        -- ================
        -- for all props other than ->, duplicating the proposition (contraction)
        -- in the context is unneccesary.
        -- But consider, for example, ~~(A | ~A) with proof term:
        -- \n. n (Right \a. n (Left a))
        -- here we have to reuse n. This means that the naïve version of ImplL
        -- has an unbounded search tree that needs a loop checker, because
        -- the context can grow in an unbounded way.

        -- the contraction-free calculus has a weight function so that
        -- every proof rule has sub-sequents with smaller weight,
        -- so the height of the proof (search) tree is bounded

        -- the left rule for implication gets split into 4 versions, depending
        -- on A in A -> B in order to make this work
        Impl a b -> case a of
            -- if we have C, (false -> Q) => P,
            -- then we could remove that proposition
            -- because if we ever proved false,
            -- we'd already have proved the sequent.
            -- however, having extra stuff in the
            -- context does no harm
            Absurd -> []
            -- C, A -> P, A => Q if C, P, A => Q
            Atomic _ -> if look c a > 0 then [ImplLAtomic (a, b)
                (Sequent (putP b d) p)] else []
            -- C, (P&Q) -> R => S if C, P -> (Q -> R) => S
            -- this only shuffles things around, but it means that
            -- we can analyze P in the next step
            Conj f g -> [ImplLConj (a, b, f, g)
                (Sequent (putP (Impl f (Impl g b)) d) p)]
            -- C, (P|Q) -> R => S if C, P -> R, Q -> R => S
            Disj f g -> [ImplLDisj (a, b, f, g)
                (Sequent (putP (Impl f b) . putP (Impl g b) $ d) p)]
            -- C, (P->Q) -> R => S if C, R => S and C, Q -> R => P -> Q
            -- this is the most obscure rule...
            Impl f g -> [ImplLImpl (a, b, f, g)
                (Sequent (putP b d) p) (Sequent (putP (Impl g b) d) (Impl f g))]
        _ -> []
        ) (Map.keys c)

(|>) :: (a -> b) -> (b -> c) -> (a -> c)
(|>) f g = g . f

-- depth first search
-- breadth-first might take up a little too much space...
search :: Sequent -> Maybe CompleteProof
search
    -- find all next steps
    =  analyze
    -- (lazily) search through them for any solutions
    |> fmap (fmap search)
    -- turn (Proof (Maybe CompleteProof)) into Maybe (Proof CompleteProof)
    |> fmap sequenceA
    -- prune all failed branches
    |> catMaybes
    -- a proof where every subbranch is a complete proof is
    -- also complete
    |> fmap roll
    -- only take first result
    |> listToMaybe

-- budget parsec
type SymbolTable = Map String Nat

data ParseState = ParseState
    { _rest :: String
    , _symbols :: SymbolTable
    , _names :: Map Nat String
    , _column :: Nat
    }
    deriving (Show)

type Parser a = StateT ParseState (Except (String, ParseState)) a

runParser :: Parser a -> ParseState -> Either (String, ParseState) (a, ParseState)
runParser s = runStateT s |> runExcept

parseError :: String -> Parser a
parseError s = get >>= \st -> throwError (s, st)

modifyRest    :: (String         -> String)         -> Parser ()
modifySymbols :: (SymbolTable    -> SymbolTable)    -> Parser ()
modifyNames   :: (Map Nat String -> Map Nat String) -> Parser ()
modifyColumn  :: (Nat            -> Nat)            -> Parser ()
modifyRest    r = modify $ \st -> st { _rest     = r (_rest     st) }
modifySymbols r = modify $ \st -> st { _symbols  = r (_symbols  st) }
modifyNames r = modify $ \st -> st { _names  = r (_names  st) }
modifyColumn  r = modify $ \st -> st { _column   = r (_column   st) }

data Lexeme
    = ID Nat
    | LBr
    | RBr
    | And
    | Or
    | Falsum
    | Implies
    | Not
    deriving (Eq, Show)

spaces :: Parser ()
spaces = do
    (sp, r) <- gets (span isSpace . _rest)
    modifyColumn (+ fromIntegral (length sp))
    modifyRest (const r)

lexID :: Parser Nat
lexID = do
    spaces
    (name, rest) <- gets (span isAlphaNum . _rest)
    when (null name) (parseError "expected name")
    modifyColumn (+ fromIntegral (length name))
    n <- gets (fromIntegral . Map.size . _symbols)
    map <- gets (Map.lookup name . _symbols)
    n <- maybe 
        (  modifySymbols (Map.insert name n)
        >> modifyNames   (Map.insert n name)
        >> pure n)
        pure map
    modifyRest (const rest)
    pure n

lexInput :: Parser (Maybe Lexeme)
lexInput =
    let
    consume token n ss = do
        modifyColumn (+n)
        modifyRest (const ss)
        pure (Just token)
    in gets _rest >>= \case
        []                           -> pure Nothing
        (c:ss) | isSpace c           -> do
            spaces
            lexInput
        ('(':ss)              -> consume LBr 1 ss
        (')':ss)              -> consume RBr 1 ss
        ('&':ss)              -> consume And 1 ss
        ('|':ss)              -> consume Or  1 ss
        ('~':ss)              -> consume Not 1 ss
        ('-':'>':ss)          -> consume Implies 1 ss
        ss | Just ss' <- stripPrefix "false" ss 
                              -> consume Falsum  5 ss'
        (c:ss) | isAlphaNum c -> Just . ID <$> lexID
        (c:_)                 -> parseError ("unexpected character: " ++ [c])

lexeme :: Parser Lexeme
lexeme = lexInput >>= maybe (parseError "unexpected end of input") pure

peeking :: (Lexeme -> Parser (Maybe a)) -> Parser (Maybe a)
peeking f = do
    previous_st <- get
    result <- lexInput >>= maybe (pure Nothing) f
    case result of
        Nothing -> put previous_st >> pure Nothing
        Just a -> pure (Just a)
    
-- precedence scheme:
-- (0)
-- 1 | 1
-- 2 & 2 (cannot mix & and |)
-- 3 -> 3
-- ~4
parseLoop :: Nat -> Parser Prop
parseLoop prec = do
    l <- lexeme
    term <- case l of
        Not    -> do
            s <- parseLoop 4
            pure (Impl s Absurd)
        Falsum -> pure Absurd
        ID n   -> pure (Atomic n)
        LBr    -> do
            t <- parseLoop 0
            l <- lexeme
            when (l /= RBr) $ parseError "expected ')'"
            pure t
        _ -> parseError "expected a simple term, not an operator"
    loop term
    where
    loop term = fmap (fromMaybe term) $ peeking $ \op ->
        let
        next_prec = case op of
            Implies -> if prec <= 3
                then pure $ Just (3, Impl)
                else pure Nothing
            And -> if
                | prec == 1 -> parseError "mixing And with Or without brackets"
                | prec <= 2 -> pure $ Just (2, Conj)
                | otherwise -> pure Nothing
            Or -> if
                | prec == 2 -> parseError "mixing And with Or without brackets"
                | prec <= 1 -> pure $ Just (1, Disj)
                | otherwise -> pure Nothing
            RBr -> pure Nothing
            _ -> parseError "unexpected term"
        in 
        next_prec >>= maybe (pure Nothing)
            (\(prec, f) -> do
                rhs <- parseLoop 0
                term' <- loop (f term rhs)
                pure $ Just term')

parseProp :: Parser Prop
parseProp = parseLoop 0

data CommandToken
    = AxiomT
    | QueryT
    | HelpT
    | ClearT
    | EmptyT
    | ErrorT
    | QuitT
    deriving (Show)

lexTopLevel :: Parser CommandToken
lexTopLevel = do
    spaces
    s <- gets _rest
    which <- catMaybes <$> traverse (uncurry $ try s)
        [ ("axiom", AxiomT)
        , ("?"    , QueryT)
        , ("help" , HelpT )
        , ("clear", ClearT)
        , ("quit" , QuitT)
        , ("exit" , QuitT)
        ]
    if
        | null s -> pure EmptyT
        | (t:_) <- which -> pure t
        | otherwise -> pure ErrorT
    where
    try s prefix token = case stripPrefix prefix s of
        Nothing -> pure Nothing
        Just rest -> do
            modifyRest (const rest)
            modifyColumn (+ (fromIntegral $ length prefix))
            pure $ Just token

lexColon :: Parser ()
lexColon = gets _rest >>=
    \case
        (':':ss) -> modifyRest (const ss) >> modifyColumn (+1)
        _ -> parseError "expected ':' in axiom definition"

parseTopLevel :: Parser Command
parseTopLevel = lexTopLevel >>= \case
    AxiomT -> AxiomC <$> lexID <* lexColon <*> parseProp
    QueryT -> QueryC <$> parseProp
    HelpT  -> pure HelpC
    ClearT -> pure ClearC
    EmptyT -> pure EmptyC
    ErrorT -> pure ErrorC
    QuitT  -> pure Quit
    
parse :: String -> SymbolTable -> Map Nat String
    -> Either (String, Nat) (Command, SymbolTable, Map Nat String)
parse s syms names = case runParser parseTopLevel
    (ParseState s syms names 0) of

    Left (s, st) -> Left (s, _column st)

    Right (c, st) -> if null (dropWhile isSpace $ _rest st)
        then Right (c, _symbols st, _names st)
        else Left ("unparsed input", _column st)

type DStr = Endo String
instance IsString (Endo String) where
    fromString s = Endo $ \t -> s ++ t

data ExtState = ExtState
    { terms :: Map Prop DStr
    , freeVars :: Nat
    }

extInsert :: Prop -> DStr -> ExtState -> ExtState
extInsert p s (ExtState terms fv) = ExtState (Map.insert p s terms) fv

-- generate some fresh variables names
-- we prefix with @ so we don't have to worry about collisions
-- with user-defined (axiom) names
extFV :: Prop -> ExtState -> (DStr, ExtState)
extFV prop (ExtState terms fv) =
    let 
    s = if fv < 26
        then (\c -> fromString $ '@':[c]) $ genericIndex ['a' .. 'z'] fv
        else fromString $ '@':show (fv-26) in
    (s, extInsert prop s $ ExtState terms (fv + 1))

paren :: DStr -> DStr
paren s = "(" <> s <> ")"

extractProof :: CompleteProof -> Map Prop String -> String
extractProof p m = appEndo (extractProof' p
    (ExtState (Map.map fromString m) 0)) ""

-- the cata here has type:
-- cata :: (Proof (ExtState -> String) -> (ExtState -> String))
--      -> CompleteProof -> (ExtState -> String)
-- here it threads the state from the root,
--  just as the strings get combined starting from the leaves
extractProof' :: CompleteProof -> ExtState -> DStr
extractProof' = cata $ \prop st@(ExtState map fvs) ->
    let look p = fromMaybe "<bug?>" $ Map.lookup p map in
    case prop of
        Axiom n   -> look (Atomic n)
        Absurdity p -> if p == Absurd
            then look Absurd -- the identity function, so ignore it
            else "absurd " <> paren (look Absurd)

        ConjL (a, b) p ->
            let st' =
                    extInsert a ("fst " <> paren (look (Conj a b))) .
                    extInsert b ("snd " <> paren (look (Conj a b))) $ st
            in p st'
        ConjR a b ->
            mconcat ["(", a st, ", ", b st, ")"]
        
        DisjL (da, db) ca cb ->
            let (a, sta) = extFV da st in
            let (b, stb) = extFV db (st { freeVars = freeVars sta }) in
            mconcat ["case ", look (Disj da db), " of\n",
                "\t Left " , a, "-> ", ca sta, "\n",
                "\t Right ", b, "-> ", cb stb, "\n"]
        DisjR1 p -> "Left "  <> paren (p st)
        DisjR2 p -> "Right " <> paren (p st)

        ImplR a p -> let (x, st') = extFV a st in
            paren $ mconcat ["\\", x, ". ", p st']
        ImplLAtomic (a, b) p -> 
            let st' = extInsert b (look (Impl a b) <> " " <> paren (look a)) st in
            p st'
        ImplLConj (a, b, f, g) p -> p
            (extInsert (Impl f (Impl g b)) ("uncurry " <> paren (look (Impl a b))) st)
        ImplLDisj (a, b, f, g) p -> p (
            extInsert (Impl f b) (paren $ look (Impl a b) <> " . Left" ) .
            extInsert (Impl g b) (paren $ look (Impl a b) <> " . Right") $
            st)
        -- the proof term here was worked out with pencil and paper...
        -- no better way than to just do it :)
        ImplLImpl (a, b, f, g) p q ->
            let (x, sto) = extFV b          st in
            let (y, sti) = extFV (Impl g b) (st { freeVars = freeVars sto }) in
            let s = look (Impl a b) in
            mconcat ["let ", x, " = ", s,
                " (", "let ",  y, " = ", s, " . ", "const ",
                "in ", q sti, ")\n",
                "in ", p sto]
