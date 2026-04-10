# binsearch

Binary search over sorted lists, implemented and verified in **Lean 4.29.0**.

> Developed with [Claude Code](https://claude.ai/code) (Anthropic).

## Structure

### `Binsearch/Basic.lean`

#### Predicate

```lean
inductive Sorted : List Nat → Prop where
  | nil    : Sorted []
  | single : ∀ x, Sorted [x]
  | cons   : ∀ x y t, x ≤ y → Sorted (y :: t) → Sorted (x :: y :: t)
```

#### Algorithm

```lean
def bsearchAux (a : Array Nat) (target lo hi : Nat) : Option Nat
-- well-founded on (hi + 1 - lo)

def bsearch (l : List Nat) (target : Nat) : Option Nat
-- converts l to Array, calls bsearchAux on [0, size-1]
```

`bsearch` converts the list to an `Array` once for O(1) index access, then
runs the standard binary search loop. Termination is proved via the measure
`hi + 1 - lo` using `Nat.strongRecOn`.

Because Lean's kernel does not reduce well-founded recursive definitions under
`unfold`, two unfolding lemmas are provided explicitly:

```lean
theorem bsearchAux_of_le -- case lo ≤ hi
theorem bsearchAux_of_gt -- case lo > hi
```

#### Correctness

| Theorem            | Statement                                                |
|--------------------|----------------------------------------------------------|
| `bsearch_sound`    | `bsearch l target = some i → l[i]? = some target`        |
| `bsearch_complete` | `Sorted l → target ∈ l → ∃ i, bsearch l target = some i` |

Completeness relies on the auxiliary predicate:

```lean
def ArraySorted (a : Array Nat) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < j → j ≤ hi → j < a.size → a[i]! ≤ a[j]!
```

and a monotonicity lemma `ArraySorted.mono` that restricts the invariant to
sub-ranges, passed to each recursive call.

## Building

```bash
lake build
```

Requires the Lean toolchain specified in `lean-toolchain` (`leanprover/lean4:v4.29.0`).
