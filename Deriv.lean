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

