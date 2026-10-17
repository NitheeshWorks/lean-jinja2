import LeanJinja2.APIs
import LeanJinja2.Proofs.Verified

/-!
# LeanJinja2

A clean-room port of Jinja2 to Lean 4: a template lexer, parser and total renderer with proved autoescape soundness.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
