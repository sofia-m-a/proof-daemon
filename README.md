# The Proof Daemon

A theorem prover for intuitionistic propositional logic,
based on:
> Contraction-Free Sequent Calculi for Intuitionistic Logic
> Author(s): Roy Dyckhoff
> Source: The Journal of Symbolic Logic, Vol. 57, No. 3 (Sep., 1992), pp. 795-807
> Published by: Association for Symbolic Logic
> Stable URL: http://www.jstor.org/stable/2275431 

## How it works
Some of the rules in propositional logic can be used directly for proof search. For instance, the sequent (A&B), C |- D can be immediately rewritten as A, B, C |- D. This eliminates a connective from the context and makes progress, so doing as many of these rules as apply terminates just fine.

However, this breaks down in some cases. The tricky spot is implication; the method in the paper above splits implication into 4 cases that require no contraction, so that any -> on the left can always be eliminated freely where possible. Otherwise, sometimes we could need an implication in the context *twice*, and thus cannot eliminate it.

See the section "Logic background" in (Main.hs) for more information, and the linked paper for even more.

## Status
It would be really nice to fix this up to be a lot cleaner and simpler.

TODO: use libraries like `prettyprinter`, `haskeline`, and `megaparsec`
