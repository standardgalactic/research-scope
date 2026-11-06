import DerivZipperLaw

/-!
DerivCounting.lean

The derivative as a count: the number of one-hole contexts of a structure
equals the number of X-values it contains.

  holesT_length : (holesT t).length = Mu.count t
-/

open Poly

variable {X Z : Type}

/-- Number of x-leaves in a single layer. -/
def Elt.countX : (p : Poly) → Elt X Z p → Nat
  | .zero, e => nomatch e
  | .one, .one => 0
  | .x, .x _ => 1
  | .z, .z _ => 0
  | .sum p q, .inl e => Elt.countX p e
  | .sum p q, .inr e => Elt.countX q e
  | .prod p q, .pair a b => Elt.countX p a + Elt.countX q b

theorem holesX_length {p : Poly} (e : Elt X Z p) :
    (holesX p e).length = Elt.countX p e := by
  induction p with
  | zero => cases e
  | one => cases e; simp [holesX, Elt.countX]
  | x => cases e; simp [holesX, Elt.countX]
  | z => cases e; simp [holesX, Elt.countX]
  | sum p q ihp ihq =>
    cases e with
    | inl e => simp [holesX, Elt.countX, ihp]
    | inr e => simp [holesX, Elt.countX, ihq]
  | prod p q ihp ihq =>
    cases e with
    | pair a b => simp [holesX, Elt.countX, ihp, ihq]

mutual
  /-- Total of `Mu.count` over the z-children of a layer. -/
  def Elt.countZ {p0 : Poly} : (p : Poly) → Elt X (Mu p0 X) p → Nat
    | .zero, e => nomatch e
    | .one, .one => 0
    | .x, .x _ => 0
    | .z, .z t => Mu.count t
    | .sum p q, .inl e => Elt.countZ p e
    | .sum p q, .inr e => Elt.countZ q e
    | .prod p q, .pair a b => Elt.countZ p a + Elt.countZ q b
  /-- Number of X-values in a whole recursive structure. -/
  def Mu.count {p0 : Poly} : Mu p0 X → Nat
    | .mk e => Elt.countX p0 e + Elt.countZ p0 e
end

theorem holesZ_count {p0 q : Poly} (e : Elt X (Mu p0 X) q) :
    ((holesZ q e).map fun sc => Mu.count sc.2).sum = Elt.countZ q e := by
  induction q with
  | zero => cases e
  | one => cases e; simp [holesZ, Elt.countZ]
  | x => cases e; simp [holesZ, Elt.countZ]
  | z => cases e; simp [holesZ, Elt.countZ]
  | sum p q ihp ihq =>
    cases e with
    | inl e => simp [holesZ, Elt.countZ, List.map_map, Function.comp_def, ← ihp]
    | inr e => simp [holesZ, Elt.countZ, List.map_map, Function.comp_def, ← ihq]
  | prod p q ihp ihq =>
    cases e with
    | pair a b =>
      simp [holesZ, Elt.countZ, List.map_map, Function.comp_def, ← ihp, ← ihq]

theorem holesT_length_aux {p0 : Poly} (n : Nat) :
    ∀ t : Mu p0 X, Mu.size t ≤ n → (holesT t).length = Mu.count t := by
  induction n with
  | zero =>
    intro t ht
    cases t with
    | mk e => simp [Mu.size] at ht
  | succ n ih =>
    intro t ht
    cases t with
    | mk e =>
      rw [holesT]
      simp only [List.length_append, List.length_map, holesX_length, Mu.count]
      congr 1
      rw [← holesZ_count e, List.length_flatMap]
      simp only [List.length_map]
      have hsz : ∀ a : {x // x ∈ holesZ p0 e}, Mu.size a.1.2 ≤ n := by
        rintro ⟨⟨s, c⟩, hm⟩
        have := size_le_of_mem_holesZ hm
        simp only [Mu.size] at ht ⊢
        omega
      rw [List.map_congr_left (fun a _ => ih a.1.2 (hsz a))]
      rw [List.attach_map_val (f := fun sc : Elt X (Mu p0 X) (dZ p0) × Mu p0 X => Mu.count sc.2)]

theorem holesT_length {p0 : Poly} (t : Mu p0 X) :
    (holesT t).length = Mu.count t :=
  holesT_length_aux (Mu.size t) t (Nat.le_refl _)

def sampleCount : Mu listP Nat := ofList [1, 2, 3]
#eval (holesT sampleCount).length
#eval Mu.count sampleCount
#eval (holesT sampleTree).length
#eval Mu.count sampleTree
#eval (holesT (ofList ([] : List Nat))).length
#print axioms holesT_length
