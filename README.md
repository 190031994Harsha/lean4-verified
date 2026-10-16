# lean4-verified

Machine-checked proofs in Lean 4 + Mathlib. Everything here builds against a pinned
toolchain (`leanprover/lean4:v4.33.0-rc1`) and a pinned Mathlib commit
(`9944fe2973b8dc0b86949101ed98232c07cd54a0`), and every theorem checks against Lean's
kernel with no `sorry` and no axioms beyond the standard `propext`, `Classical.choice`,
`Quot.sound` (verified with `#print axioms`).

## What's in here

| File | Statement |
|---|---|
| `Verified/Sort/Insertion.lean` | Insertion sort is correct: `isort l` is `Pairwise (· ≤ ·)` and a `List.Perm` of the input. |
| `Verified/Sort/Merge.lean` | Bottom-up merge sort (well-founded recursion with `termination_by`/`decreasing_by`) is correct: sorted and a permutation. |
| `Verified/Sort/StableMerge.lean` | Merge sort on key/value pairs is correct **and stable**: filtering the output by any key yields the filtered input, in order. |
| `Verified/TwoPowAddOne.lean` | The only solutions of `2^a + 1 = 3^b` in natural numbers are `(1,1)` and `(3,2)` — the Levi ben Gerson case of Catalan, proved with elementary modular arithmetic (mod 16 and mod 5). |

## Build

```
elan toolchain install leanprover/lean4:v4.33.0-rc1   # if needed
lake exe cache get
lake build
```

The merge-sort developments use the well-founded recursion equation lemmas
(`merge.eq_def`, `msortP.induct`) rather than structural recursion; the stability
proof hinges on the fact that for sorted inputs, filtering a merge by a key is
exactly the concatenation of the filtered halves.
