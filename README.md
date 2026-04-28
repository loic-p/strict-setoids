## A strict, proof-relevant setoid model

Revisiting Hofmann's setoid model using PMP's strict presheaves.
- `lib.agda`: preliminary definitions. In order to use PMP's construction, we need a definitionally proof-irrelevant equality type with a "strong J" eliminator. This is implemented by the rewrite rule `transp-refl`.
- `setoids.agda`: definition of (PMP-style) setoids, and of the universe of small setoids.
- `typeformers.agda`: definition of the setoid of natural numbers, dependent products of setoids, dependent sums, quotients (WIP)
- `views.agda`: auxiliary definitions to help doing induction on the universe of small setoids. Proof that the setoid equality is reflexive and symmetric. 
- `fibrancy.agda`: definition of transitivity for the setoid equality, and type coercion.
- `cwf.agda`: arranging all the pieces in a category with families. The resulting CwF supports Pi types (with η) and positive Σ types (without η)
- `nat.agda`: adding natural numbers with large elimination to the CwF. Nat is in its own file because it is quite slow to typecheck.
- `observational.agda`: adding observational features to the CwF. We define an observational equality which supports funext, propext, UIP. It computes via a cast operator, as in OTT.

TODO: quotients, choice principles, add a second universe level