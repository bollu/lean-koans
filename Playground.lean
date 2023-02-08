import Aesop
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.TypeVec
import Mathlib.Data.Vector
import Mathlib.Data.Finite.Basic

/-
Feb 7th: Tobias and I agreed that having to use names just makes life miserable.
Find some way to sidestep having to deal with names.

- Directly encode DAGs + semantics?
- Try to use 'iris' to control semantics via DAG?
-/

namespace OpWithNoLet
inductive Op
| Add : Op → Op → Op
| Constant : Int → Op

def Op.run: Op → Int
| .Add o o' => o.run + o'.run
| .Constant i => i


-- A program with a *single* hole is
inductive OpHole -- Op with a single hole.
| Hole : OpHole
| AddHoleLeft : OpHole → Op → OpHole -- (+ <hole> <op>)
| AddHoleRight: Op → OpHole → OpHole -- (+ <op> <hole>)

def ex1 : OpHole := .AddHoleLeft .Hole (Op.Constant 1)
#print ex1

def OpHole.fill (o : Op) : OpHole → Op
| .Hole => o
| .AddHoleLeft hole r => .Add (hole.fill o) r
| .AddHoleRight l hole => .Add l (hole.fill o)

def simple_semantic_equivalence (o o': Op): Prop := o.run = o'.run

-- A rewrite from o to o' is correct iff..
def semantic_equiv (o o': Op): Prop := ∀ (hole: OpHole),
  (hole.fill o).run = (hole.fill o').run

-- (x - x)
-- 0
end OpWithNoLet


namespace MultiOpHole
/-
Ops with multiple holes that need to be filled.
-/

inductive Op
| Add : Op → Op → Op
| Constant : Int → Op

def Op.run: Op → Int
| .Add o o' => o.run + o'.run
| .Constant i => i

namespace MultiOpHoleDep
inductive OpHole: (n: Nat) → Type
| hOp: Op → OpHole 0
| hHole : OpHole 1
| hAdd : (n m : Nat) → OpHole n → OpHole m → OpHole (n + m)

-- Split a vector into two parts,
-- one with the elements in [0, k), and the
-- other with elements [k, n)
def Vector.split {t: Type} (k l: Nat) (v: Vector t (k + l)):
  Vector t k × Vector t l := sorry

def OpHole.fill (filler : Vec Op n) : OpHole n →  Op
| .hHole => filler 0
| .hOp op => op
| .hAdd n m lhole rhole =>
    let (lfill, rfill) := filler.split n v


-- Two programs are equivalent iff...
def semantic_equiv (o o': Op): Prop := ∀ (hole: OpHole),
  (hole.fill o).run = (hole.fill o').run
end MultiOpHoleDep

namespace MultiOpHoleNonDep
end MultiOpHoleNonDep

end MultiOpHole

namespace OpWithLet
/-
ops with names / binders / 'let' expressions.
-/
inductive Op
| Add : Op → Op → Op
| Constant : Int → Op
-- let <name> = <def> in <use>
-- OR
-- %name = <def>
-- <use>
| Let : (name : String) → (def_ : Op) → (use: Op) → Op
| Var : String → Op

abbrev Env := String → Option Int

def Env.extend (name : String) (v : Int) (e : Env) : Env :=
  fun name' => if name == name' then v else e name

def Op.run (e: Env): Op → Option Int
| .Add o o' =>
  match (o.run e, o'.run e) with
  | (.some v, .some v') => .some <| v + v'
  | (_, _) => .none
| .Constant i => .some <| i
| .Var v => e v
| .Let name def_ use =>
   match def_.run e with
   | .some v => use.run (e.extend name v)
   | .none => .none

inductive OpHole
| Hole : OpHole
| AddHoleLeft : OpHole → Op → OpHole
| AddHoleRight : Op → OpHole → OpHole
| LetHoleDef : (name : String) → OpHole → Op → OpHole
| LetHoleUse : (name : String) → Op → OpHole → OpHole



-- let x = <hole1>
-- ...
-- let y = <hole2>
-- ...
-- let z = y - x

def OpHole.fill (o : Op) : OpHole → Op
| .Hole => o
| .AddHoleLeft hole r => .Add (hole.fill o) r
| .AddHoleRight l hole => .Add l (hole.fill o)
| .LetHoleDef name hole use => .Let name (hole.fill o) use
| .LetHoleUse name def_ hole => .Let name def_ (hole.fill o)


def semantic_equiv_0 (o o': Op): Prop := ∀ (env: Env),
  o.run env = o'.run env

-- (f = g) <-> ∀ x, f x = g x
def semantic_equiv_1 (o o': Op): Prop := ∀ (hole: OpHole) (env: Env),
  (hole.fill o).run env  = (hole.fill o').run env

/-
Note that semantic_equiv_1 is wrong. If we have a transformation
which replaces a"("x" - "x") with b:(0), then it is a legal transformation,
but there are more cases where (b) produces a value than (a) does.
So our definition should be something like: if (a) runs
successfully and produces an answer, then so does (b) and it
produces the same answer
-/

def semantic_equiv_2 (o o': Op): Prop :=
  ∀ (hole: OpHole) (val: Int) (env: Env),
  (hole.fill o).run env = .some val →
  (hole.fill o').run env = .some val
end OpWithLet

namespace OpLargeIndexedInductive
/-
Attempt to escape the poor `mutual def` and mutual inductive support in Lean by
building a single, large, indexed inductive.
Suggested by Sebastien:
https://docs.google.com/document/d/1vru7Gdv9dEdnsgOu2Xvc9K5gjgRPLV2iW_3dyX7XHAw/edit
-/

inductive OR
| O : OR
| Os : OR
| R : OR
| Rs: OR
inductive OpRegion : OR -> Type where
 | op: (name: String)
      -> (regions: OpRegion  .Rs)
       -> OpRegion .O
 | opsnil : OpRegion .Os
 | opscons : (head : OpRegion .O)
            -> (tail: OpRegion  .Os)
            -> OpRegion .Os
 | regionsnil : OpRegion  .Rs
 | regionscons : (head : OpRegion .R)
                 -> (tail: OpRegion  .Rs)
                 -> OpRegion .Rs
 | region: (name : String)
           -> (ops: OpRegion .Os)
           ->  OpRegion  .R


abbrev Op : Type := OpRegion  .O
abbrev Region : Type := OpRegion .R
abbrev Regions : Type := OpRegion .Rs
abbrev Ops : Type := OpRegion .Os

@[match_pattern]
abbrev Op.mk
    (name: String)
    (regions: Regions)
    : OpRegion .O :=
  OpRegion.op name regions

@[match_pattern]
abbrev Region.mk
    (name: String)
    (ops: Ops): OpRegion .R :=
  OpRegion.region name ops

@[match_pattern]
abbrev Ops.nil : Ops :=
  OpRegion.opsnil

@[match_pattern]
abbrev Ops.cons   (o: Op) (os: Ops): Ops:=
  OpRegion.opscons o os

@[match_pattern]
abbrev Regions.nil:  Regions := OpRegion.regionsnil

@[match_pattern]
abbrev Regions.cons (r: Region) (rs: Regions): Regions :=
  OpRegion.regionscons r rs


mutual
  def Op.countSize : Op -> Int
  | Op.mk name regions  => 1 + Regions.countSize regions

  def Ops.countSize : Ops -> Int
  | .nil => 0
  | .cons o os => Op.countSize o + Ops.countSize os

  def Region.countSize : Region  -> Int
  | Region.mk name  ops => 1 + Ops.countSize ops

  def Regions.countSize : Regions -> Int
  | .nil => 0
  | .cons r rs => Region.countSize r + Regions.countSize rs
end
termination_by
  OpLargeIndexedInductive.Op.countSize op => sizeOf op
  OpLargeIndexedInductive.Regions.countSize rs => sizeOf rs
  OpLargeIndexedInductive.Ops.countSize ops => sizeOf ops
  OpLargeIndexedInductive.Region.countSize r => sizeOf r


/-
Note that this uses WellFounded.fix.
Why does this STILL use WellFounded.fix?
-/
#print Op.countSize._mutual

def OpRegion.countSize: OpRegion k → Int
| .regionsnil => 0
| .regionscons r rs => r.countSize + rs.countSize
| .opsnil => 0
| .opscons o os => o.countSize + os.countSize
| .op name regions  => regions.countSize + 1
| .region name ops => 1 + ops.countSize

/-
This still uses WellFounded.fix?
No, here it manages to compile into 'bRec'
-/
#print OpRegion.countSize

end OpLargeIndexedInductive

namespace OpLargeIndexedInductiveDialect
/-
Attempt to escape the poor `mutual def` and mutual inductive support in Lean by
building a single, large, indexed inductive, with a (Dialect δ) argument
Suggested by Sebastien:
https://docs.google.com/document/d/1vru7Gdv9dEdnsgOu2Xvc9K5gjgRPLV2iW_3dyX7XHAw/edit
-/

class DialectAttrIntf (α: Type) where
  eq: DecidableEq α
  str: α → String

def DialectAttrIntf.type {α} (_: DialectAttrIntf α): Type := α

class DialectTypeIntf (σ: Type) (ε: σ → Type): Type where
  inhabited: forall (s: σ), ε s
  typeEq: DecidableEq σ
  eq: forall (s: σ), DecidableEq (ε s)
  str: (s: σ) → ε s → String
  typeStr: σ → String

class Dialect (α σ) (ε: σ → Type): Type :=
  name: String
  iα: DialectAttrIntf α
  iε: DialectTypeIntf σ ε

inductive SSAVal : Type where | SSAVal : String -> SSAVal
deriving DecidableEq

inductive MLIRType (δ: Dialect α σ ε) :=
| float: Nat -> MLIRType δ
| tensor1d: MLIRType δ -- tensor of int values.
| extended: σ → MLIRType δ

-- An SSA value with a type
abbrev TypedSSAVal (δ: Dialect α σ ε) := SSAVal × MLIRType δ


inductive OR
| O : OR
| Os : OR
| R : OR
| Rs: OR
inductive OpRegion (δ: Dialect α σ ε): OR -> Type where
 | op: (name: String)
      -> (regions: OpRegion δ .Rs)
       -> OpRegion δ .O
 | opsnil : OpRegion δ .Os
 | opscons : (head : OpRegion δ .O)
            -> (tail: OpRegion δ .Os)
            -> OpRegion δ  .Os
 | regionsnil : OpRegion δ .Rs
 | regionscons : (head : OpRegion δ .R)
                 -> (tail: OpRegion δ  .Rs)
                 -> OpRegion δ .Rs
 | region: (name : String)
           -> (ops: OpRegion δ .Os)
           ->  OpRegion δ  .R


abbrev Op (δ: Dialect α σ ε): Type := OpRegion δ  .O
abbrev Region (δ: Dialect α σ ε): Type := OpRegion δ .R
abbrev Regions (δ: Dialect α σ ε) : Type := OpRegion δ  .Rs
abbrev Ops (δ: Dialect α σ ε) : Type := OpRegion δ  .Os

@[match_pattern]
abbrev Op.mk (δ: Dialect α σ ε)
    (name: String)
    (regions: Regions δ)
    : OpRegion δ .O :=
  OpRegion.op name regions

@[match_pattern]
abbrev Region.mk (δ: Dialect α σ ε)
    (name: String)
    (ops: Ops δ): OpRegion δ .R :=
  OpRegion.region name ops

@[match_pattern]
abbrev Ops.nil (δ: Dialect α σ ε) : Ops δ :=
  OpRegion.opsnil

@[match_pattern]
abbrev Ops.cons   (δ: Dialect α σ ε) (o: Op δ) (os: Ops δ): Ops δ:=
  OpRegion.opscons o os

@[match_pattern]
abbrev Regions.nil (δ: Dialect α σ ε):  Regions δ := OpRegion.regionsnil

@[match_pattern]
abbrev Regions.cons (δ: Dialect α σ ε) (r: Region δ) (rs: Regions δ): Regions δ :=
  OpRegion.regionscons r rs


mutual
  def Op.countSize: Op δ -> Int
  | Op.mk _ name regions  => 1 + Regions.countSize regions

  def Ops.countSize : Ops δ -> Int
  | .nil _ => 0
  | .cons _ o os => Op.countSize o + Ops.countSize os

  def Region.countSize : Region  δ -> Int
  | Region.mk _ name  ops => 1 + Ops.countSize ops

  def Regions.countSize : Regions δ -> Int
  | .nil _ => 0
  | .cons _ r rs => Region.countSize r + Regions.countSize rs
end
termination_by
  OpLargeIndexedInductiveDialect.Op.countSize op => sizeOf op
  OpLargeIndexedInductiveDialect.Regions.countSize rs => sizeOf rs
  OpLargeIndexedInductiveDialect.Ops.countSize ops => sizeOf ops
  OpLargeIndexedInductiveDialect.Region.countSize r => sizeOf r

/-
Note that this uses WellFounded.fix.
Why does this STILL use WellFounded.fix?
-/
#print Op.countSize
/-
So adding a parameter makes things mutual?
-/
#print Op.countSize._unary._mutual

def OpRegion.countSize: OpRegion δ k → Int
| .regionsnil => 0
| .regionscons r rs => r.countSize + rs.countSize
| .opsnil => 0
| .opscons o os => o.countSize + os.countSize
| .op name regions  => regions.countSize + 1
| .region name ops => 1 + ops.countSize

/-
This still uses WellFounded.fix?
No, here it manages to compile into 'bRec'
-/
#print OpRegion.countSize

end OpLargeIndexedInductiveDialect


namespace OpLargeIndexedInductiveDialectPlusArgs
/-
Attempt to escape the poor `mutual def` and mutual inductive support in Lean by
building a single, large, indexed inductive, with a (Dialect δ) argument
Suggested by Sebastien:
https://docs.google.com/document/d/1vru7Gdv9dEdnsgOu2Xvc9K5gjgRPLV2iW_3dyX7XHAw/edit
-/

class DialectAttrIntf (α: Type) where
  eq: DecidableEq α
  str: α → String

def DialectAttrIntf.type {α} (_: DialectAttrIntf α): Type := α

class DialectTypeIntf (σ: Type) (ε: σ → Type): Type where
  inhabited: forall (s: σ), ε s
  typeEq: DecidableEq σ
  eq: forall (s: σ), DecidableEq (ε s)
  str: (s: σ) → ε s → String
  typeStr: σ → String

class Dialect (α σ) (ε: σ → Type): Type :=
  name: String
  iα: DialectAttrIntf α
  iε: DialectTypeIntf σ ε

inductive SSAVal : Type where | SSAVal : String -> SSAVal
deriving DecidableEq

inductive MLIRType (δ: Dialect α σ ε) :=
| float: Nat -> MLIRType δ
| tensor1d: MLIRType δ -- tensor of int values.
| extended: σ → MLIRType δ

-- An SSA value with a type
abbrev TypedSSAVal (δ: Dialect α σ ε) := SSAVal × MLIRType δ


inductive OR
| O : OR
| Os : OR
| R : OR
| Rs: OR

inductive OpRegion (δ: Dialect α σ ε): OR -> Type where
 | op: (name: String)
      -> (regions: OpRegion δ .Rs)
       -> OpRegion δ .O
 | opsnil : OpRegion δ .Os
 | opscons : (head : OpRegion δ .O)
            -> (tail: OpRegion δ .Os)
            -> OpRegion δ  .Os
 | regionsnil : OpRegion δ .Rs
 | regionscons : (head : OpRegion δ .R)
                 -> (tail: OpRegion δ  .Rs)
                 -> OpRegion δ .Rs
 | region: (name : String)
           -> (ops: OpRegion δ .Os)
           ->  OpRegion δ  .R


abbrev Op (δ: Dialect α σ ε): Type := OpRegion δ  .O
abbrev Region (δ: Dialect α σ ε): Type := OpRegion δ .R
abbrev Regions (δ: Dialect α σ ε) : Type := OpRegion δ  .Rs
abbrev Ops (δ: Dialect α σ ε) : Type := OpRegion δ  .Os

@[match_pattern]
abbrev Op.mk (δ: Dialect α σ ε)
    (name: String)
    (regions: Regions δ)
    : OpRegion δ .O :=
  OpRegion.op name regions

@[match_pattern]
abbrev Region.mk (δ: Dialect α σ ε)
    (name: String)
    (ops: Ops δ): OpRegion δ .R :=
  OpRegion.region name ops

@[match_pattern]
abbrev Ops.nil (δ: Dialect α σ ε) : Ops δ :=
  OpRegion.opsnil

@[match_pattern]
abbrev Ops.cons   (δ: Dialect α σ ε) (o: Op δ) (os: Ops δ): Ops δ:=
  OpRegion.opscons o os

@[match_pattern]
abbrev Regions.nil (δ: Dialect α σ ε):  Regions δ := OpRegion.regionsnil

@[match_pattern]
abbrev Regions.cons (δ: Dialect α σ ε) (r: Region δ) (rs: Regions δ): Regions δ :=
  OpRegion.regionscons r rs


mutual
  def Op.countSize: Op δ -> Int
  | Op.mk _ name regions  => 1 + Regions.countSize regions

  def Ops.countSize : Ops δ -> Int
  | .nil _ => 0
  | .cons _ o os => Op.countSize o + Ops.countSize os

  def Region.countSize : Region  δ -> Int
  | Region.mk _ name  ops => 1 + Ops.countSize ops

  def Regions.countSize : Regions δ -> Int
  | .nil _ => 0
  | .cons _ r rs => Region.countSize r + Regions.countSize rs
end
termination_by
  OpLargeIndexedInductiveDialectPlusArgs.Op.countSize op => sizeOf op
  OpLargeIndexedInductiveDialectPlusArgs.Regions.countSize rs => sizeOf rs
  OpLargeIndexedInductiveDialectPlusArgs.Ops.countSize ops => sizeOf ops
  OpLargeIndexedInductiveDialectPlusArgs.Region.countSize r => sizeOf r

/-
Note that this uses WellFounded.fix.
Why does this STILL use WellFounded.fix?
-/
#print Op.countSize
/-
So adding a parameter makes things mutual?
-/
#print Op.countSize._unary._mutual

def OpRegion.countSize: OpRegion δ k → Int
| .regionsnil => 0
| .regionscons r rs => r.countSize + rs.countSize
| .opsnil => 0
| .opscons o os => o.countSize + os.countSize
| .op name regions  => regions.countSize + 1
| .region name ops => 1 + ops.countSize

/-
This still uses WellFounded.fix?
No, here it manages to compile into 'bRec'
-/
#print OpRegion.countSize

end OpLargeIndexedInductiveDialectPlusArgs
