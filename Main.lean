import Init.System.IO

import Std.Data.AssocList
import Std.Data.HashMap
import Std.Lean.HashSet
import Std.Data.RBMap
import Std.Data.Array.Basic

import Mathlib.Tactic

inductive Expr : Type
| add : Expr → Expr → Expr
| mul : Expr → Expr → Expr
| lit : Nat → Expr
deriving Repr

/- Exercise 1: Expr syntax and semantics -/

/- Exercise 1a: write an evaluation function. it should pass the following tests -/
def Expr.eval : Expr → Nat
| .add e1 e2 => Expr.eval e1 + Expr.eval e2
| .mul e1 e2 => Expr.eval e1 * Expr.eval e2
| .lit n => n

def e1 : Expr := .add (.lit 1) (.lit 2)
def e2 : Expr := .add (.mul (.lit 3) (.lit 4)) (.lit 2)

#eval e1.eval = 3
#eval e2.eval = 14

/- Exercise 1b: write an OfNat instance for Expr. the following expressions should then type check: -/
instance : OfNat Expr n where
  ofNat := Expr.lit n


#eval (3 : Expr)
#eval (.add 1 2 : Expr)
#eval (.mul 100 2 : Expr)

/- Exercise 1c: write Add/Mul instances for Expr -/

instance : Add Expr where
  add e1 e2 := Expr.add e1 e2

instance : Mul Expr := ⟨Expr.mul⟩  -- Just experimenting with different syntax hehe

#eval (3 * 4 : Expr)
#eval (3 * 4 : Expr).eval = 12


/- Exercise 2: a compiler for Expr
  end result: a file containing x86 or RISC-V assembly that can be assembled and runs to evaluate the given expr
  constraints:
    - don't just precompute the value at compile time :)
    - don't go straight to the string; first design an IR for assembly code.
        write a function of type Expr → IR and then another of type IR → String.

  bonus: add more fun to the Expr type, like `let` expressions or `if .. then .. else`. extend Expr.eval and Expr.compile
-/
abbrev Stack := List Nat

inductive StackIR : Type where
| add : StackIR
| mul : StackIR
| push : Nat → StackIR
deriving Repr

abbrev StackProgram := List StackIR


def StackProgram.evalRec : StackProgram → Stack → Nat
  | [], s => s.head! -- For our purposes, a stack progam is invalid if this operation fails
  | .push n :: irs, s => evalRec irs (n :: s)
  | .add :: (.push m) :: (.push n) :: irs, s => evalRec irs ((m + n) :: s)
  | .add :: _, _ => 1234556789 -- arbitrary behavior for ill-formed stack
  | .mul :: (.push m) :: (.push n) :: irs, s => evalRec irs ((m * n) :: s)
  | .mul :: _, _ => 1234556789 -- arbitrary behavior for ill-formed stack

def StackProgram.eval (p : StackProgram) : Nat := evalRec p []


def Expr.toStackProgram : Expr → StackProgram
| lit n => [.push n]
| add e1 e2 => toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.add]
| mul e1 e2 => toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.mul]

#eval (1 * 2 + 3 * 4 : Expr).toStackProgram
#eval (1 * 2 + 3 * 4 : Expr).toStackProgram.eval == 1 * 2 + 3 * 4
#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram

inductive Asm : Type where
| push : Nat →  Asm
| pop : Asm
| add : String → String → Asm -- The nats are the displacements from rsp here and in imul
| imul : String → String → Asm
deriving Repr

abbrev AsmProgram := List Asm

def StackProgram.toAsmProgram (sp : StackProgram) := 
  let rec toAsmRec : StackProgram → AsmProgram
  | [] => []
  | .push n :: sirs => Asm.push n :: toAsmRec sirs
  | .add :: sirs => .add "0x8" "0x10" :: Asm.pop :: toAsmRec sirs 
  | .mul :: sirs => .imul "0x8" "0x10" :: Asm.pop :: toAsmRec sirs 

  toAsmRec sp
#eval (1 * 2 + 3 * 4 : Expr).toStackProgram.toAsmProgram
#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram.toAsmProgram

def AsmProgram.toAsmString : AsmProgram → String
| [] => "mov %rsp %rax"
| i :: is => 
  (match i with
  | .push n => s!"push ${n}" 
  | .pop => "pop"
  | .add r s => s!"add {r}(%rsp) {s}(%rsp)" -- there was something kinda wrong with how i'm thinking about add, ngl, but i think i fixed it
  | .imul r s => s!"imul {r}(%rsp) {s}(%rsp)"
  )
  ++ "\n" ++ toAsmString is


#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram.toAsmProgram.toAsmString

open IO.FS (writeFile)
def Expr.compile : Expr → System.FilePath → IO Unit :=
  fun expr => 
    fun fp => writeFile fp expr.toStackProgram.toAsmProgram.toAsmString

def demoFile : System.FilePath := ⟨"./expr.o"⟩ 


#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).compile demoFile




/- Exercise 3: joins via polynomial multiplication

  1 Design a representation `Poly` for the set of polynomials modulo the equations:
    - x * x = x
    - x * y = 0, if x ≠ y
    You should assume the set of variables is possibly infinite;
    you can assume they are indexed by String or Nat or use a type variable
    (at this step, your representation doesn't necessarily need to care about these equations).

  2 Write a function that multiplies them (now the equations are important).
    Also a write a function `canonical : Poly → Poly` that puts a polynomial into a canonical form, that is:
      - Suppose `[r] = p` means "`(r : Poly)` represents the polynomial `p`".
        Then we want  `∀ (f, g : Poly), [f] = [g] → f.canonical = g.canonical`
-/


inductive Poly : Type where
| zero : Poly
| var : String → String → Poly
| times : Poly → Poly → Poly
| plus : Poly → Poly → Poly  
deriving Repr, BEq, Hashable


def Poly.distrib : Poly → Poly
| zero => zero
| var k v => var k v
| plus p1 p2 => plus (distrib p1) (distrib p2)
| times zero _ => zero
| times _ zero => zero
| times (plus p1 p2) q => plus (distrib (times p1 q)) (distrib (times p2 q))
| times p (plus q1 q2) => plus (distrib (times p q1)) (distrib (times p q2))
| p => p

-- This function takes a polynomial represented as a sum of products of variables and orders the monomials

def Poly.toMonomialsList : Poly → List Poly
| zero => []
| var k v => [var k v]
| plus p1 p2 => (toMonomialsList p1) ++ (toMonomialsList p2)
| times p1 p2 => [times p1 p2]

def Poly.prodToArray : Poly → Array Poly
| times p1 p2 => prodToArray p1 ++ prodToArray p2
| p => #[p]

def Poly.compare (p1 : Poly) (p2 : Poly) : Ordering :=
match p1, p2 with
--| zero, _ => .lt
--| _, zero => .gt
| var k1 v1, var k2 v2 => let cmp : Ordering := Ord.compare k1 k2
    match cmp with
    | .eq => Ord.compare v1 v2
    | _ => cmp
| _, _ => .eq -- I really only want to use this function on single variables, so I don't care

instance : Ord Poly where
  compare := Poly.compare

def sRel : Poly := .plus (
  .times (.var "country_id" "1") (.times (.var "country" "Canada") (.var "country_code" "CA"))) 
  (.times (.var "country_id" "2") (.times (.var "country" "United States") (.var "country_code" "US")))

 def rRel : Poly := 
        .plus 
              (.times (.var "user" "Smudge") (.var "country_id" "1"))
              (.plus 
                (.times (.var "user" "Sissel") (.var "country_id" "1"))
                (.times (.var "user" "Petee") (.var "country_id" "2")))

def p : Poly := .times sRel rRel

#eval ((p.distrib.toMonomialsList.map Poly.prodToArray).map Array.qsortOrd).map Lean.HashSet.ofArray |> List.map Lean.HashSet.toList

def Poly.deduplicate (monomials : List (List Poly)) : List (List Poly) := Id.run do

    let mut res : List (List Poly) := []
    for m in monomials do
      let mut hashList : List String := []
      for v in m do
        match v with
        | .var k _ => do hashList := k :: hashList
        | _ => do hashList := hashList
      if (((Lean.HashSet.ofList hashList.toArray).size) == m.length) 
      then do res := m :: res 

    return res




-- i want a function that converts canonized products to their real polynomials

def Poly.reconstructProd : List Poly → Poly
| [] => zero 
| [x] => x
| x :: xs => if x == zero then zero else times x (reconstructProd xs)

-- Converts list of monomials to sum
def Poly.reconstructSum : List Poly → Poly
| [] => zero
| [x] => x
| x :: xs => if x == zero then reconstructSum xs else plus x (reconstructSum xs)

#eval Poly.reconstructSum (Poly.reconstructProd <$> ((((p.distrib.toMonomialsList.map Poly.prodToArray).map Array.qsortOrd).map Lean.HashSet.ofArray |> List.map Lean.HashSet.toList) |> Poly.deduplicate))

open Poly in

def canonical (p : Poly) : Poly :=
  let allMonomials : List (Poly) := p.distrib.toMonomialsList
  let sortedMonomialsArrays : List (Array Poly) := ((allMonomials.map prodToArray).map Array.qsortOrd)
  let monomialsxxeqx : List (List Poly) := (sortedMonomialsArrays.map Lean.HashSet.ofArray |> List.map Lean.HashSet.toList)
  let monomialsDedupedByContrad: List (List Poly) := deduplicate monomialsxxeqx
  let (prodList : List Poly) := reconstructProd <$> monomialsDedupedByContrad
  reconstructSum prodList

def Poly.multiply p1 p2 := canonical (.times p1 p2)

#eval Poly.multiply sRel rRel

def main : IO Unit := IO.println s!"hello!"


/- Exercise 2 part 2: (harder) Design a formal semantics for your assembly IR and prove that your compiled code computes the same result as Expr
    for semantics ideas, see:
      - https://raw.githubusercontent.com/blanchette/logical_verification_2022/master/hitchhikers_guide.pdf,
      - http://adam.chlipala.net/frap/frap_book.pdf,
      - (more advanced) https://hal.science/hal-03255472v3

-/
@[simp]
theorem eval_add_eq_eval_plus_eval (e1 e2 : Expr) : (Expr.add e1 e2).eval = e1.eval + e2.eval := by rfl

open StackIR Expr in
theorem sp_add_stack_eq_sp_fst_concat_sp_snd (e1 e2 : Expr) : toStackProgram (Expr.add e1 e2) = toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.add] := by rfl

open Expr in
-- Show correctness of StackIR compiler
-- Theorem: For all Exprs, evaluating is equivalent to compiling to StackProgram and evaluating that StackProgram
theorem expr_to_stack_compile_ok' (e : Expr) (sp : StackProgram) (s : Stack) : StackProgram.evalRec (e.toStackProgram ++ sp) s = StackProgram.evalRec sp (e.eval :: s) := by
  induction e generalizing sp s with
  | lit n => 
      rfl
  | add e1 e2 ih1 ih2 => 
      rw [eval_add_eq_eval_plus_eval]
      rw [sp_add_stack_eq_sp_fst_concat_sp_snd]
      rw [List.append_assoc (toStackProgram e1) (toStackProgram e2) [StackIR.add]]
      have h1 := ih1 (toStackProgram e2 ++ [StackIR.add] ++ sp) s
      rw [h1]
  | mul e1 e2 ih1 ih2 => sorry
    


#check List.append_assoc


-- For all StackPrograms: evaluating is equivalent to compiling to AsmIR and evaluating.
theorem stack_to_asm_compile_ok' : (sp : StackProgram) : sp.eval = sp.toAsmProgram.eval := by
  sorry -- I haven't written an eval function for AsmProgram yet


