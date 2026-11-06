import DerivZipperLaw

/-!
DerivMixedPartials.lean

Second derivatives of a polynomial layer and the symmetry of filling. The
second derivative of a layer is the type of two-hole contexts; the two holes
are filled one after the other, and the order of filling does not matter. Each
statement is element-level: there is an explicit swap of two-hole contexts, and
filling the holes in the two orders gives equal layers.

  plug_swapXZ : plugX p (plugZ (dX p) (swapXZ p l) c) a
                  = plugZ p (plugX (dZ p) l a) c          (d^2/dZ dX = d^2/dX dZ)
  plug_swapXX : the same for two X-holes, with the two fillers exchanged
  plug_swapZZ : the same for two Z-holes

The swaps are mutually inverse. Poly has no associative-commutative quotient,
so dX (dZ p) and dZ (dX p) are different syntactic trees; the swap is the
isomorphism between their element types, and it is what the Mu-level two-hole
statement will cite.
-/

open Poly

set_option linter.unusedSimpArgs false

variable {X Z : Type}

/-! ## Mixed partials: dX (dZ p) against dZ (dX p) -/

/-- Exchange the order of differentiation on a two-hole context: X-hole inside a Z-context becomes Z-hole inside an X-context. -/
def swapXZ : (p : Poly) → Elt X Z (dX (dZ p)) → Elt X Z (dZ (dX p))
  | .zero, e => nomatch e
  | .one, e => nomatch e
  | .x, e => nomatch e
  | .z, e => nomatch e
  | .sum p _, .inl e => .inl (swapXZ p e)
  | .sum _ q, .inr e => .inr (swapXZ q e)
  | .prod p _, .inl (.inl (.pair a b)) => .inl (.inl (.pair (swapXZ p a) b))
  | .prod _ _, .inl (.inr (.pair a b)) => .inr (.inl (.pair a b))
  | .prod _ _, .inr (.inl (.pair a b)) => .inl (.inr (.pair a b))
  | .prod _ q, .inr (.inr (.pair a b)) => .inr (.inr (.pair a (swapXZ q b)))

/-- The inverse of `swapXZ`. -/
def swapZX : (p : Poly) → Elt X Z (dZ (dX p)) → Elt X Z (dX (dZ p))
  | .zero, e => nomatch e
  | .one, e => nomatch e
  | .x, e => nomatch e
  | .z, e => nomatch e
  | .sum p _, .inl e => .inl (swapZX p e)
  | .sum _ q, .inr e => .inr (swapZX q e)
  | .prod p _, .inl (.inl (.pair a b)) => .inl (.inl (.pair (swapZX p a) b))
  | .prod _ _, .inl (.inr (.pair a b)) => .inr (.inl (.pair a b))
  | .prod _ _, .inr (.inl (.pair a b)) => .inl (.inr (.pair a b))
  | .prod _ q, .inr (.inr (.pair a b)) => .inr (.inr (.pair a (swapZX q b)))

/-! Same variable twice: dX (dX p) and dZ (dZ p) are symmetric. -/

/-- Exchange the two X-holes of a two-hole context. -/
def swapXX : (p : Poly) → Elt X Z (dX (dX p)) → Elt X Z (dX (dX p))
  | .zero, e => nomatch e
  | .one, e => nomatch e
  | .x, e => nomatch e
  | .z, e => nomatch e
  | .sum p _, .inl e => .inl (swapXX p e)
  | .sum _ q, .inr e => .inr (swapXX q e)
  | .prod p _, .inl (.inl (.pair a b)) => .inl (.inl (.pair (swapXX p a) b))
  | .prod _ _, .inl (.inr (.pair a b)) => .inr (.inl (.pair a b))
  | .prod _ _, .inr (.inl (.pair a b)) => .inl (.inr (.pair a b))
  | .prod _ q, .inr (.inr (.pair a b)) => .inr (.inr (.pair a (swapXX q b)))

/-- Exchange the two Z-holes of a two-hole context. -/
def swapZZ : (p : Poly) → Elt X Z (dZ (dZ p)) → Elt X Z (dZ (dZ p))
  | .zero, e => nomatch e
  | .one, e => nomatch e
  | .x, e => nomatch e
  | .z, e => nomatch e
  | .sum p _, .inl e => .inl (swapZZ p e)
  | .sum _ q, .inr e => .inr (swapZZ q e)
  | .prod p _, .inl (.inl (.pair a b)) => .inl (.inl (.pair (swapZZ p a) b))
  | .prod _ _, .inl (.inr (.pair a b)) => .inr (.inl (.pair a b))
  | .prod _ _, .inr (.inl (.pair a b)) => .inl (.inr (.pair a b))
  | .prod _ q, .inr (.inr (.pair a b)) => .inr (.inr (.pair a (swapZZ q b)))

/-! Computation rules for the swaps, by `rfl`. -/

theorem swapXZ_sum_inl {p q : Poly} (e : Elt X Z (dX (dZ p))) :
    swapXZ (sum p q) (.inl e) = .inl (swapXZ p e) := rfl
theorem swapXZ_sum_inr {p q : Poly} (e : Elt X Z (dX (dZ q))) :
    swapXZ (sum p q) (.inr e) = .inr (swapXZ q e) := rfl
theorem swapXZ_prod_ll {p q : Poly} (a : Elt X Z (dX (dZ p))) (b : Elt X Z q) :
    swapXZ (prod p q) (.inl (.inl (.pair a b))) = .inl (.inl (.pair (swapXZ p a) b)) := rfl
theorem swapXZ_prod_lr {p q : Poly} (a : Elt X Z (dZ p)) (b : Elt X Z (dX q)) :
    swapXZ (prod p q) (.inl (.inr (.pair a b))) = .inr (.inl (.pair a b)) := rfl
theorem swapXZ_prod_rl {p q : Poly} (a : Elt X Z (dX p)) (b : Elt X Z (dZ q)) :
    swapXZ (prod p q) (.inr (.inl (.pair a b))) = .inl (.inr (.pair a b)) := rfl
theorem swapXZ_prod_rr {p q : Poly} (a : Elt X Z p) (b : Elt X Z (dX (dZ q))) :
    swapXZ (prod p q) (.inr (.inr (.pair a b))) = .inr (.inr (.pair a (swapXZ q b))) := rfl

theorem swapZX_sum_inl {p q : Poly} (e : Elt X Z (dZ (dX p))) :
    swapZX (sum p q) (.inl e) = .inl (swapZX p e) := rfl
theorem swapZX_sum_inr {p q : Poly} (e : Elt X Z (dZ (dX q))) :
    swapZX (sum p q) (.inr e) = .inr (swapZX q e) := rfl
theorem swapZX_prod_ll {p q : Poly} (a : Elt X Z (dZ (dX p))) (b : Elt X Z q) :
    swapZX (prod p q) (.inl (.inl (.pair a b))) = .inl (.inl (.pair (swapZX p a) b)) := rfl
theorem swapZX_prod_lr {p q : Poly} (a : Elt X Z (dX p)) (b : Elt X Z (dZ q)) :
    swapZX (prod p q) (.inl (.inr (.pair a b))) = .inr (.inl (.pair a b)) := rfl
theorem swapZX_prod_rl {p q : Poly} (a : Elt X Z (dZ p)) (b : Elt X Z (dX q)) :
    swapZX (prod p q) (.inr (.inl (.pair a b))) = .inl (.inr (.pair a b)) := rfl
theorem swapZX_prod_rr {p q : Poly} (a : Elt X Z p) (b : Elt X Z (dZ (dX q))) :
    swapZX (prod p q) (.inr (.inr (.pair a b))) = .inr (.inr (.pair a (swapZX q b))) := rfl

theorem swapXX_sum_inl {p q : Poly} (e : Elt X Z (dX (dX p))) :
    swapXX (sum p q) (.inl e) = .inl (swapXX p e) := rfl
theorem swapXX_sum_inr {p q : Poly} (e : Elt X Z (dX (dX q))) :
    swapXX (sum p q) (.inr e) = .inr (swapXX q e) := rfl
theorem swapXX_prod_ll {p q : Poly} (a : Elt X Z (dX (dX p))) (b : Elt X Z q) :
    swapXX (prod p q) (.inl (.inl (.pair a b))) = .inl (.inl (.pair (swapXX p a) b)) := rfl
theorem swapXX_prod_lr {p q : Poly} (a : Elt X Z (dX p)) (b : Elt X Z (dX q)) :
    swapXX (prod p q) (.inl (.inr (.pair a b))) = .inr (.inl (.pair a b)) := rfl
theorem swapXX_prod_rl {p q : Poly} (a : Elt X Z (dX p)) (b : Elt X Z (dX q)) :
    swapXX (prod p q) (.inr (.inl (.pair a b))) = .inl (.inr (.pair a b)) := rfl
theorem swapXX_prod_rr {p q : Poly} (a : Elt X Z p) (b : Elt X Z (dX (dX q))) :
    swapXX (prod p q) (.inr (.inr (.pair a b))) = .inr (.inr (.pair a (swapXX q b))) := rfl

theorem swapZZ_sum_inl {p q : Poly} (e : Elt X Z (dZ (dZ p))) :
    swapZZ (sum p q) (.inl e) = .inl (swapZZ p e) := rfl
theorem swapZZ_sum_inr {p q : Poly} (e : Elt X Z (dZ (dZ q))) :
    swapZZ (sum p q) (.inr e) = .inr (swapZZ q e) := rfl
theorem swapZZ_prod_ll {p q : Poly} (a : Elt X Z (dZ (dZ p))) (b : Elt X Z q) :
    swapZZ (prod p q) (.inl (.inl (.pair a b))) = .inl (.inl (.pair (swapZZ p a) b)) := rfl
theorem swapZZ_prod_lr {p q : Poly} (a : Elt X Z (dZ p)) (b : Elt X Z (dZ q)) :
    swapZZ (prod p q) (.inl (.inr (.pair a b))) = .inr (.inl (.pair a b)) := rfl
theorem swapZZ_prod_rl {p q : Poly} (a : Elt X Z (dZ p)) (b : Elt X Z (dZ q)) :
    swapZZ (prod p q) (.inr (.inl (.pair a b))) = .inl (.inr (.pair a b)) := rfl
theorem swapZZ_prod_rr {p q : Poly} (a : Elt X Z p) (b : Elt X Z (dZ (dZ q))) :
    swapZZ (prod p q) (.inr (.inr (.pair a b))) = .inr (.inr (.pair a (swapZZ q b))) := rfl

/-! ## The filling laws -/

theorem plug_swapXZ {p : Poly} (l : Elt X Z (dX (dZ p))) (a : X) (c : Z) :
    plugX p (plugZ (dX p) (swapXZ p l) c) a = plugZ p (plugX (dZ p) l a) c := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair t l2) (ihp l1)
      | inr l =>
        cases l with
        | pair l1 l2 => rfl
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => rfl
      | inr l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair l1 t) (ihq l2)

theorem plug_swapXX {p : Poly} (l : Elt X Z (dX (dX p))) (a b : X) :
    plugX p (plugX (dX p) l a) b = plugX p (plugX (dX p) (swapXX p l) b) a := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair t l2) (ihp l1)
      | inr l =>
        cases l with
        | pair l1 l2 => rfl
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => rfl
      | inr l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair l1 t) (ihq l2)

theorem plug_swapZZ {p : Poly} (l : Elt X Z (dZ (dZ p))) (a b : Z) :
    plugZ p (plugZ (dZ p) l a) b = plugZ p (plugZ (dZ p) (swapZZ p l) b) a := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair t l2) (ihp l1)
      | inr l =>
        cases l with
        | pair l1 l2 => rfl
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => rfl
      | inr l =>
        cases l with
        | pair l1 l2 => exact congrArg (fun t => Elt.pair l1 t) (ihq l2)

/-! ## The swaps are involutions and mutually inverse -/

theorem swapZX_swapXZ {p : Poly} (l : Elt X Z (dX (dZ p))) :
    swapZX p (swapXZ p l) = l := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]

theorem swapXZ_swapZX {p : Poly} (l : Elt X Z (dZ (dX p))) :
    swapXZ p (swapZX p l) = l := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXZ_sum_inl, swapXZ_sum_inr, swapXZ_prod_ll, swapXZ_prod_lr, swapXZ_prod_rl, swapXZ_prod_rr, swapZX_sum_inl, swapZX_sum_inr, swapZX_prod_ll, swapZX_prod_lr, swapZX_prod_rl, swapZX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]

theorem swapXX_swapXX {p : Poly} (l : Elt X Z (dX (dX p))) :
    swapXX p (swapXX p l) = l := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapXX_sum_inl, swapXX_sum_inr, swapXX_prod_ll, swapXX_prod_lr, swapXX_prod_rl, swapXX_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]

theorem swapZZ_swapZZ {p : Poly} (l : Elt X Z (dZ (dZ p))) :
    swapZZ p (swapZZ p l) = l := by
  induction p with
  | zero => cases l
  | one => cases l
  | x => cases l
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
    | inr l => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]
  | prod p q ihp ihq =>
    cases l with
    | inl l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihp]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
    | inr l =>
      cases l with
      | inl l =>
        cases l with
        | pair l1 l2 => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ]
      | inr l =>
        cases l with
        | pair l1 l2 => simp only [swapZZ_sum_inl, swapZZ_sum_inr, swapZZ_prod_ll, swapZZ_prod_lr, swapZZ_prod_rl, swapZZ_prod_rr]; try dsimp only [dX, dZ]; try simp only [plugX, plugZ, ihq]

/-! ## Example on the list layer 1 + X * Z

The two-hole context holding both the X-hole and the Z-hole of the cons cell. -/

def consHoles : Elt Nat (Mu listP Nat) (dX (dZ listP)) :=
  .inr (.inr (.inl (.pair .one .one)))

-- fill the X-hole, then the Z-hole; then after the swap, the Z-hole, then the X-hole
#eval toList (.mk (plugZ listP (plugX (dZ listP) consHoles 7) (ofList [5])))
#eval toList (.mk (plugX listP (plugZ (dX listP) (swapXZ listP consHoles) (ofList [5])) 7))
#print axioms plug_swapXZ
#print axioms plug_swapXX
#print axioms plug_swapZZ
