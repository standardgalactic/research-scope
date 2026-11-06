/-!
DerivZipperLaw.lean

Companion to Deriv.lean (derivative of a recursive type as a one-hole context).
Deriv.lean is reproduced unchanged up to the definition of `holes`; this file
adds a size measure, a total enumeration `holesT`, and proofs that it is sound
and complete for `plug`:

  plug_holes      : (c, a) in holesT t  ->  plug c a = t
  mem_holesT_iff  : (c, a) in holesT t  <->  plug c a = t
-/
set_option linter.unusedVariables false

/-- Layer codes F(X,Z): 0, 1, X, Z, sums and products. -/
inductive Poly : Type
  | zero | one | x | z
  | sum  (p q : Poly)
  | prod (p q : Poly)

open Poly

/-- Elements of one layer, with X-values and Z-values (recursive children). -/
inductive Elt (X Z : Type) : Poly → Type
  | one  : Elt X Z one
  | x    : X → Elt X Z x
  | z    : Z → Elt X Z z
  | inl  {p q : Poly} : Elt X Z p → Elt X Z (sum p q)
  | inr  {p q : Poly} : Elt X Z q → Elt X Z (sum p q)
  | pair {p q : Poly} : Elt X Z p → Elt X Z q → Elt X Z (prod p q)

/-- The least fixed point of a layer. -/
inductive Mu (p0 : Poly) (X : Type) : Type
  | mk : Elt X (Mu p0 X) p0 → Mu p0 X

/-- Derivative of a layer with respect to X. -/
def dX : Poly → Poly
  | zero => zero
  | one => zero
  | x => one
  | z => zero
  | sum p q => sum (dX p) (dX q)
  | prod p q => sum (prod (dX p) q) (prod p (dX q))

/-- Derivative of a layer with respect to Z. -/
def dZ : Poly → Poly
  | zero => zero
  | one => zero
  | x => zero
  | z => one
  | sum p q => sum (dZ p) (dZ q)
  | prod p q => sum (prod (dZ p) q) (prod p (dZ q))

variable {X Z : Type}

/-- Fill the X-hole of a layer context. -/
def plugX : (p : Poly) → Elt X Z (dX p) → X → Elt X Z p
  | zero, e, _ => nomatch e
  | one, e, _ => nomatch e
  | x, .one, a => .x a
  | z, e, _ => nomatch e
  | sum p q, .inl e, a => .inl (plugX p e a)
  | sum p q, .inr e, a => .inr (plugX q e a)
  | prod p q, .inl (.pair e b), a => .pair (plugX p e a) b
  | prod p q, .inr (.pair b e), a => .pair b (plugX q e a)

/-- Fill the Z-hole of a layer context. -/
def plugZ : (p : Poly) → Elt X Z (dZ p) → Z → Elt X Z p
  | zero, e, _ => nomatch e
  | one, e, _ => nomatch e
  | x, e, _ => nomatch e
  | z, .one, c => .z c
  | sum p q, .inl e, c => .inl (plugZ p e c)
  | sum p q, .inr e, c => .inr (plugZ q e c)
  | prod p q, .inl (.pair e b), c => .pair (plugZ p e c) b
  | prod p q, .inr (.pair b e), c => .pair b (plugZ q e c)

/-- Every way to select an X in a layer, with its context. -/
def holesX : (p : Poly) → Elt X Z p → List (Elt X Z (dX p) × X)
  | zero, e => nomatch e
  | one, .one => []
  | x, .x a => [(.one, a)]
  | z, .z _ => []
  | sum p q, .inl e => (holesX p e).map fun (c, a) => (.inl c, a)
  | sum p q, .inr e => (holesX q e).map fun (c, a) => (.inr c, a)
  | prod p q, .pair a b =>
      (holesX p a).map (fun (c, v) => (.inl (.pair c b), v)) ++
      (holesX q b).map (fun (c, v) => (.inr (.pair a c), v))

/-- Every way to descend into a recursive child, with its layer context. -/
def holesZ : (p : Poly) → Elt X Z p → List (Elt X Z (dZ p) × Z)
  | zero, e => nomatch e
  | one, .one => []
  | x, .x _ => []
  | z, .z c => [(.one, c)]
  | sum p q, .inl e => (holesZ p e).map fun (s, c) => (.inl s, c)
  | sum p q, .inr e => (holesZ q e).map fun (s, c) => (.inr s, c)
  | prod p q, .pair a b =>
      (holesZ p a).map (fun (s, c) => (.inl (.pair s b), c)) ++
      (holesZ q b).map (fun (s, c) => (.inr (.pair a s), c))

/-- A context in a recursive type: a local context and a stack of steps,
the steps ordered from the hole outward. -/
structure Ctx (p0 : Poly) (X : Type) where
  local_ : Elt X (Mu p0 X) (dX p0)
  steps  : List (Elt X (Mu p0 X) (dZ p0))

/-- Rebuild the whole structure from a context and a replacement. -/
def plug {p0 : Poly} (c : Ctx p0 X) (a : X) : Mu p0 X :=
  c.steps.foldl (fun m s => .mk (plugZ p0 s m)) (.mk (plugX p0 c.local_ a))

/-- Every context of a structure, paired with the selected element. -/
partial def holes {p0 : Poly} (t : Mu p0 X) : List (Ctx p0 X × X) :=
  match t with
  | .mk e =>
    let here := (holesX p0 e).map fun (l, a) =>
      ({ local_ := l, steps := [] }, a)
    let below := (holesZ p0 e).flatMap fun (s, child) =>
      (holes child).map fun (c, a) => ({ c with steps := c.steps ++ [s] }, a)
    here ++ below

theorem plugX_holesX {p0 : Poly} {e : Elt X Z p0} {l : Elt X Z (dX p0)} {a : X}
    (h : (l, a) ∈ holesX p0 e) : plugX p0 l a = e := by
  induction p0 with
  | zero => cases e
  | one => cases e; simp [holesX] at h
  | x =>
    cases e with
    | x a' =>
      simp [holesX] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | z => cases e with | z c => simp [holesX] at h
  | sum p q ihp ihq =>
    cases e with
    | inl e =>
      simp only [holesX, List.mem_map] at h
      obtain ⟨⟨l', a'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [plugX]
      rw [ihp hmem]
    | inr e =>
      simp only [holesX, List.mem_map] at h
      obtain ⟨⟨l', a'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [plugX]
      rw [ihq hmem]
  | prod p q ihp ihq =>
    cases e with
    | pair a b =>
      simp only [holesX, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨l', v⟩, hmem, heq⟩ | ⟨⟨l', v⟩, hmem, heq⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [plugX]
        rw [ihp hmem]
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [plugX]
        rw [ihq hmem]

theorem plugZ_holesZ {p0 : Poly} {e : Elt X Z p0} {s : Elt X Z (dZ p0)} {c : Z}
    (h : (s, c) ∈ holesZ p0 e) : plugZ p0 s c = e := by
  induction p0 with
  | zero => cases e
  | one => cases e; simp [holesZ] at h
  | x => cases e with | x a => simp [holesZ] at h
  | z =>
    cases e with
    | z c' =>
      simp [holesZ] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | sum p q ihp ihq =>
    cases e with
    | inl e =>
      simp only [holesZ, List.mem_map] at h
      obtain ⟨⟨s', c'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [plugZ]
      rw [ihp hmem]
    | inr e =>
      simp only [holesZ, List.mem_map] at h
      obtain ⟨⟨s', c'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [plugZ]
      rw [ihq hmem]
  | prod p q ihp ihq =>
    cases e with
    | pair a b =>
      simp only [holesZ, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨s', v⟩, hmem, heq⟩ | ⟨⟨s', v⟩, hmem, heq⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [plugZ]
        rw [ihp hmem]
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [plugZ]
        rw [ihq hmem]

mutual
  /-- Number of `mk` nodes below the Z-leaves of a layer. -/
  def Elt.sizeZ {p0 : Poly} : (p : Poly) → Elt X (Mu p0 X) p → Nat
    | zero, e => nomatch e
    | one, .one => 0
    | x, .x _ => 0
    | z, .z t => Mu.size t
    | sum p q, .inl e => Elt.sizeZ p e
    | sum p q, .inr e => Elt.sizeZ q e
    | prod p q, .pair a b => Elt.sizeZ p a + Elt.sizeZ q b
  /-- Number of `mk` nodes in a recursive value. -/
  def Mu.size {p0 : Poly} : Mu p0 X → Nat
    | .mk e => 1 + Elt.sizeZ p0 e
end

/-- Every child found by `holesZ` is no larger than the layer's total child size. -/
theorem size_le_of_mem_holesZ {p0 q : Poly} {e : Elt X (Mu p0 X) q}
    {s : Elt X (Mu p0 X) (dZ q)} {c : Mu p0 X}
    (h : (s, c) ∈ holesZ q e) : Mu.size c ≤ Elt.sizeZ q e := by
  induction q with
  | zero => cases e
  | one => cases e; simp [holesZ] at h
  | x => cases e with | x a => simp [holesZ] at h
  | z =>
    cases e with
    | z c' =>
      simp [holesZ] at h
      obtain ⟨_, rfl⟩ := h
      simp [Elt.sizeZ]
  | sum p q ihp ihq =>
    cases e with
    | inl e =>
      simp only [holesZ, List.mem_map] at h
      obtain ⟨⟨s', c'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [Elt.sizeZ]
      exact ihp hmem
    | inr e =>
      simp only [holesZ, List.mem_map] at h
      obtain ⟨⟨s', c'⟩, hmem, heq⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [Elt.sizeZ]
      exact ihq hmem
  | prod p q ihp ihq =>
    cases e with
    | pair a b =>
      simp only [holesZ, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨s', v⟩, hmem, heq⟩ | ⟨⟨s', v⟩, hmem, heq⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [Elt.sizeZ]
        have := ihp hmem
        dsimp only at this
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [Elt.sizeZ]
        have := ihq hmem
        dsimp only at this
        omega

/-- Total version of `holes`, by well-founded recursion on `Mu.size`. -/
def holesT {p0 : Poly} (t : Mu p0 X) : List (Ctx p0 X × X) :=
  match t with
  | .mk e =>
    let here := (holesX p0 e).map fun (l, a) =>
      ({ local_ := l, steps := [] }, a)
    let below := (holesZ p0 e).attach.flatMap fun ⟨(s, child), hmem⟩ =>
      (holesT child).map fun (c, a) => ({ c with steps := c.steps ++ [s] }, a)
    here ++ below
termination_by Mu.size t
decreasing_by
  have := size_le_of_mem_holesZ hmem
  simp only [Mu.size]
  omega

theorem plug_holesT_aux {p0 : Poly} (n : Nat) :
    ∀ t : Mu p0 X, Mu.size t ≤ n → ∀ ca ∈ holesT t, plug ca.1 ca.2 = t := by
  induction n with
  | zero =>
    intro t ht
    cases t with
    | mk e => simp [Mu.size] at ht
  | succ n ih =>
    intro t ht ca hca
    obtain ⟨c, a⟩ := ca
    cases t with
    | mk e =>
      rw [holesT] at hca
      simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_attach, true_and] at hca
      rcases hca with ⟨⟨l, a'⟩, hl, heq⟩ | ⟨⟨⟨s, child⟩, hmem⟩, hca⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        simp only [plug, List.foldl_nil]
        rw [plugX_holesX hl]
      · obtain ⟨⟨c', a'⟩, hc', heq⟩ := hca
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        have hsz : Mu.size child ≤ n := by
          have := size_le_of_mem_holesZ hmem
          simp only [Mu.size] at ht
          omega
        have h1 := ih child hsz (c', a') hc'
        simp only [plug, List.foldl_append, List.foldl_cons, List.foldl_nil] at h1 ⊢
        rw [h1, plugZ_holesZ hmem]

theorem plug_holesT {p0 : Poly} (t : Mu p0 X) :
    ∀ ca ∈ holesT t, plug ca.1 ca.2 = t :=
  plug_holesT_aux (Mu.size t) t (Nat.le_refl _)


/-! Lists: F(X,Z) = 1 + X * Z -/
def listP : Poly := sum one (prod x z)

def ofList : List X → Mu listP X
  | [] => .mk (.inl .one)
  | a :: as => .mk (.inr (.pair (.x a) (.z (ofList as))))

partial def toList : Mu listP X → List X
  | .mk (.inl .one) => []
  | .mk (.inr (.pair (.x a) (.z t))) => a :: toList t

/-! Binary trees with leaves: F(X,Z) = X + Z * Z -/
def treeP : Poly := sum x (prod z z)

def leaf (a : X) : Mu treeP X := .mk (.inl (.x a))
def node (l r : Mu treeP X) : Mu treeP X := .mk (.inr (.pair (.z l) (.z r)))

partial def leaves : Mu treeP X → List X
  | .mk (.inl (.x a)) => [a]
  | .mk (.inr (.pair (.z l) (.z r))) => leaves l ++ leaves r

def sample : Mu listP Nat := ofList [1, 2, 3]

-- stack depth of each selection, and the selected element
#eval (holes sample).map fun (c, a) => (c.steps.length, a)
-- replace each selected element by 9
#eval (holes sample).map fun (c, _) => toList (plug c 9)
-- reconstruction with the original element restores the list
#eval (holes sample).all fun (c, a) => toList (plug c a) == [1, 2, 3]

partial def shape [ToString X] : Mu treeP X → String
  | .mk (.inl (.x a)) => toString a
  | .mk (.inr (.pair (.z l) (.z r))) => "(" ++ shape l ++ " " ++ shape r ++ ")"

def sampleTree : Mu treeP Nat := node (node (leaf 1) (leaf 2)) (leaf 3)
#eval (holes sampleTree).map fun (c, a) => (c.steps.length, a)
#eval (holes sampleTree).map fun (c, _) => leaves (plug c 9)
#eval (holes sampleTree).all fun (c, a) => leaves (plug c a) == [1, 2, 3]
-- constructor-preserving view: restoration of the whole tree
#eval shape sampleTree
#eval (holes sampleTree).map fun (c, _) => shape (plug c 9)
#eval (holes sampleTree).all fun (c, a) => shape (plug c a) == shape sampleTree

theorem mem_holesX_plugX {p0 : Poly} {l : Elt X Z (dX p0)} {a : X} :
    (l, a) ∈ holesX p0 (plugX p0 l a) := by
  induction p0 with
  | zero => cases l
  | one => cases l
  | x => cases l; simp [plugX, holesX]
  | z => cases l
  | sum p q ihp ihq =>
    cases l with
    | inl l' =>
      simp only [plugX, holesX, List.mem_map]
      exact ⟨(l', a), ihp, rfl⟩
    | inr l' =>
      simp only [plugX, holesX, List.mem_map]
      exact ⟨(l', a), ihq, rfl⟩
  | prod p q ihp ihq =>
    cases l with
    | inl l1 =>
      cases l1 with
      | pair l' b =>
        simp only [plugX, holesX, List.mem_append, List.mem_map]
        exact Or.inl ⟨(l', a), ihp, rfl⟩
    | inr l1 =>
      cases l1 with
      | pair b l' =>
        simp only [plugX, holesX, List.mem_append, List.mem_map]
        exact Or.inr ⟨(l', a), ihq, rfl⟩

theorem mem_holesZ_plugZ {p0 : Poly} {s : Elt X Z (dZ p0)} {c : Z} :
    (s, c) ∈ holesZ p0 (plugZ p0 s c) := by
  induction p0 with
  | zero => cases s
  | one => cases s
  | x => cases s
  | z => cases s; simp [plugZ, holesZ]
  | sum p q ihp ihq =>
    cases s with
    | inl s' =>
      simp only [plugZ, holesZ, List.mem_map]
      exact ⟨(s', c), ihp, rfl⟩
    | inr s' =>
      simp only [plugZ, holesZ, List.mem_map]
      exact ⟨(s', c), ihq, rfl⟩
  | prod p q ihp ihq =>
    cases s with
    | inl s1 =>
      cases s1 with
      | pair s' b =>
        simp only [plugZ, holesZ, List.mem_append, List.mem_map]
        exact Or.inl ⟨(s', c), ihp, rfl⟩
    | inr s1 =>
      cases s1 with
      | pair b s' =>
        simp only [plugZ, holesZ, List.mem_append, List.mem_map]
        exact Or.inr ⟨(s', c), ihq, rfl⟩

/-- Completeness: every context-and-element pair that rebuilds `plug c a`
is enumerated by `holesT` on the rebuilt structure. -/
theorem mem_holesT_plug {p0 : Poly} (c : Ctx p0 X) (a : X) :
    (c, a) ∈ holesT (plug c a) := by
  obtain ⟨l, steps⟩ := c
  have key : ∀ rs : List (Elt X (Mu p0 X) (dZ p0)),
      ((⟨l, rs.reverse⟩ : Ctx p0 X), a) ∈ holesT (plug ⟨l, rs.reverse⟩ a) := by
    intro rs
    induction rs with
    | nil =>
      simp only [List.reverse_nil, plug, List.foldl_nil]
      rw [holesT]
      simp only [List.mem_append, List.mem_map]
      exact Or.inl ⟨(l, a), mem_holesX_plugX, rfl⟩
    | cons s rs ih =>
      have hp : plug ⟨l, (s :: rs).reverse⟩ a
          = Mu.mk (plugZ p0 s (plug ⟨l, rs.reverse⟩ a)) := by
        simp [plug, List.foldl_append]
      rw [hp, holesT]
      simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_attach, true_and]
      refine Or.inr ⟨⟨(s, plug ⟨l, rs.reverse⟩ a), mem_holesZ_plugZ⟩, ?_⟩
      exact ⟨(⟨l, rs.reverse⟩, a), ih, by simp⟩
  simpa using key steps.reverse

/-- Exact characterization of `holesT`. -/
theorem mem_holesT_iff {p0 : Poly} (t : Mu p0 X) (c : Ctx p0 X) (a : X) :
    (c, a) ∈ holesT t ↔ plug c a = t :=
  ⟨fun h => plug_holesT t (c, a) h,
   fun h => h ▸ mem_holesT_plug c a⟩

/-- Zipper law: plugging the selected element back into any context found by
`holesT` restores the original structure. -/
theorem plug_holes {p0 : Poly} (t : Mu p0 X) :
    ∀ ca ∈ holesT t, plug ca.1 ca.2 = t := plug_holesT t

-- the total enumeration agrees with the partial one on the examples
#eval (holesT sample).map fun (c, a) => (c.steps.length, a)
#eval (holesT sampleTree).map fun (c, a) => (c.steps.length, a)
#print axioms plug_holes
