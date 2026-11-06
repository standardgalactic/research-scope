import DerivZipperLaw

/-!
DerivNavigation.lean

A Huet zipper on `Mu p0 X`: a focused subtree together with the stack of layer
contexts above it (innermost first, the same convention as `Ctx.steps`).
Moving down uses `holesZ`, moving up uses `plugZ`, and the layer lemmas
`plugZ_holesZ` and `mem_holesZ_plugZ` make them inverse.

  up_of_mem_children      : z' in z.children  ->  z'.up = some z
  mem_children_of_up      : z.up = some z'    ->  z in z'.children
  root_up, root_of_mem_children : navigation never changes the whole structure
-/

open Poly

variable {X : Type}

/-- A focused subtree and the layer contexts above it, innermost first. -/
structure Zip (p0 : Poly) (X : Type) where
  focus : Mu p0 X
  path  : List (Elt X (Mu p0 X) (dZ p0))

/-- Rebuild the whole structure from a zipper. -/
def Zip.root {p0 : Poly} (z : Zip p0 X) : Mu p0 X :=
  z.path.foldl (fun m s => .mk (plugZ p0 s m)) z.focus

/-- Move to the parent layer, if there is one. -/
def Zip.up {p0 : Poly} : Zip p0 X → Option (Zip p0 X)
  | ⟨_, []⟩ => none
  | ⟨f, s :: ss⟩ => some ⟨.mk (plugZ p0 s f), ss⟩

/-- Every zipper obtained by descending into one recursive child. -/
def Zip.children {p0 : Poly} (z : Zip p0 X) : List (Zip p0 X) :=
  match z.focus with
  | .mk e => (holesZ p0 e).map fun (s, c) => ⟨c, s :: z.path⟩

/-- Move to the i-th recursive child. -/
def Zip.down {p0 : Poly} (i : Nat) (z : Zip p0 X) : Option (Zip p0 X) :=
  z.children[i]?

/-- The zipper positioned at the selected X of a context. -/
def Ctx.toZip {p0 : Poly} (c : Ctx p0 X) (a : X) : Zip p0 X :=
  ⟨.mk (plugX p0 c.local_ a), c.steps⟩

theorem Ctx.root_toZip {p0 : Poly} (c : Ctx p0 X) (a : X) :
    (c.toZip a).root = plug c a := rfl

theorem up_of_mem_children {p0 : Poly} {z z' : Zip p0 X}
    (h : z' ∈ z.children) : z'.up = some z := by
  obtain ⟨f, path⟩ := z
  cases f with
  | mk e =>
    simp only [Zip.children, List.mem_map] at h
    obtain ⟨⟨s, c⟩, hm, rfl⟩ := h
    simp only [Zip.up]
    rw [plugZ_holesZ hm]

theorem mem_children_of_up {p0 : Poly} {z z' : Zip p0 X}
    (h : z.up = some z') : z ∈ z'.children := by
  obtain ⟨f, path⟩ := z
  cases path with
  | nil => simp [Zip.up] at h
  | cons s ss =>
    simp only [Zip.up, Option.some.injEq] at h
    subst h
    simp only [Zip.children, List.mem_map]
    exact ⟨(s, f), mem_holesZ_plugZ, rfl⟩

theorem root_up {p0 : Poly} {z z' : Zip p0 X}
    (h : z.up = some z') : z'.root = z.root := by
  obtain ⟨f, path⟩ := z
  cases path with
  | nil => simp [Zip.up] at h
  | cons s ss =>
    simp only [Zip.up, Option.some.injEq] at h
    subst h
    simp [Zip.root, List.foldl_cons]

theorem root_of_mem_children {p0 : Poly} {z z' : Zip p0 X}
    (h : z' ∈ z.children) : z'.root = z.root := by
  have := up_of_mem_children h
  exact (root_up this).symm

theorem up_down {p0 : Poly} {z z' : Zip p0 X} (i : Nat)
    (h : z.down i = some z') : z'.up = some z :=
  up_of_mem_children (List.mem_of_getElem? h)

theorem down_up {p0 : Poly} {z z' : Zip p0 X}
    (h : z.up = some z') : ∃ i, z'.down i = some z := by
  have hm := mem_children_of_up h
  obtain ⟨i, hi, hz⟩ := List.getElem_of_mem hm
  exact ⟨i, by simp [Zip.down, List.getElem?_eq_getElem hi, hz]⟩

/-! Examples on the sample tree ((1 2) 3). -/

def zTop : Zip treeP Nat := ⟨sampleTree, []⟩

#eval zTop.children.map fun z => shape z.focus
#eval zTop.children.map fun z => z.path.length
#eval zTop.children.map fun z => (z.up.map fun u => shape u.focus)
#eval zTop.children.map fun z => shape z.root
#eval (zTop.down 0 >>= Zip.down 1).map fun z => (shape z.focus, z.path.length)
#eval (zTop.down 0 >>= Zip.down 1 >>= Zip.up >>= Zip.up).map fun z => shape z.focus
#eval zTop.down 2 |>.isNone
#print axioms up_of_mem_children
#print axioms down_up
