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
def Expr.eval : Expr → Int
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
abbrev Stack := List Int

inductive StackIR : Type where
| add : StackIR
| mul : StackIR
| push : Int → StackIR
deriving Repr

abbrev StackProgram := List StackIR

def StackProgram.evalRec : StackProgram → Stack → Int
  | [], s => s.head! -- For our purposes, a stack progam is invalid if this operation fails
  | .push n :: irs, s => evalRec irs (n :: s)
  | .add :: irs, n :: m :: s => evalRec irs ((m + n) :: s)
  | .add :: irs, s => evalRec irs s -- arbitrary behavior for ill-formed stack
  | .mul :: irs, n :: m :: s => evalRec irs ((m * n) :: s)
  | .mul :: irs, s => evalRec irs s -- arbitrary behavior for ill-formed stack

def StackProgram.eval (p : StackProgram) : Int := evalRec p []


def Expr.toStackProgram : Expr → StackProgram
| lit n => [.push n]
| add e1 e2 => toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.add]
| mul e1 e2 => toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.mul]

#eval (1 * 2 + 3 * 4 : Expr).toStackProgram
#eval (1 * 2 + 3 * 4 : Expr).toStackProgram.eval
#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram

def Nat.toHexString (n : Nat) : String := "0x" ++ String.mk (Nat.toDigits 16 n)
def Int.toHexString (n : Int) : String := (if n < 0 then "-" else "") ++ Nat.toHexString n.natAbs
namespace Asm
/- A representation of x86-64 instructions as in
https://web.stanford.edu/class/archive/cs/cs107/cs107.1238/resources/x86-64-reference.pdf 
-/


inductive OkDst : Type where
| mem (n : Nat) -- A memory address
| reg (r : String) -- A register
| indirect (r : String) -- (r) where r is a register
| indirectDisp (d : Int) (r : String) -- d(r) where r is a register
| indirectScaledIndex (d : Int) (rb : String) (ri : String) (s : {x : Nat // x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8}) -- d(rb, ri, s)
deriving Repr

def OkDst.toString : OkDst → String
| mem n => n.toHexString
| reg r => r
| indirect r => s!"({r})"
| indirectDisp d r => s!"{d.toHexString}({r})"
| indirectScaledIndex d rb ri s => s!"{d.toHexString}({rb}, {ri}, {s})"


instance : ToString OkDst where
  toString := OkDst.toString

inductive OkSrc : Type where
| imm (n : Int) -- Immediate
| src (okDst : OkDst) -- All other values mirror OkDst
deriving Repr

def OkSrc.toString : OkSrc → String
| imm n => "$" ++ n.toHexString
| src (okDst) => okDst.toString

instance : ToString OkSrc where
  toString := OkSrc.toString
end Asm

open Asm in
inductive Asm : Type where
| push (n : Int)
| pop (dst : OkDst)
| add (src : OkSrc) (dst : OkDst) 
| imul (src : OkSrc) (dst : OkDst)
deriving Repr


abbrev AsmProgram := List Asm

open Asm in
#check Asm.add (.src (.indirectDisp 0x8 "%rsp")) (.indirectDisp 0x10 "%rsp")


open Asm in
@[simp]
def StackProgram.toAsmProgram : StackProgram → AsmProgram
| [] => []
| .push n :: sis => Asm.push n :: toAsmProgram sis
| .add :: sis => .add  (.src (.indirectDisp 0x8 "%rsp")) (.indirectDisp 0x10 "%rsp") :: .pop (.reg "%rax") :: toAsmProgram sis 
| .mul :: sis => .imul (.src (.indirectDisp 0x8 "%rsp")) (.indirectDisp 0x10 "%rsp") :: .pop (.reg "%rax") :: toAsmProgram sis 
 
def AsmProgram.toString : AsmProgram → String
| [] => "mov %rsp %rax"
| i :: is => 
    (match i with
    | .push n => s!"push ${n.toHexString}" 
    | .pop dst => s!"pop {dst}"
    | .add src dst => s!"add {src} {dst}" 
    | .imul src dst=> s!"imul {src} {dst}")
  ++ "\n" ++ toString is

#eval (1 * 2 + 3 * 4 : Expr).toStackProgram.toAsmProgram
#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram.toAsmProgram.toString



def FinMap (α β : Type _) :=  α → Option β 
namespace FinMap

variable {α β  : Type _} [DecidableEq α] (map : FinMap α β)

def lookup (key : α) : Option β  := map key
def insert (key : α) (val : β) : FinMap α β := fun k => if k = key then val else map k

theorem insert_key : (map.insert key val).lookup key = some val := by sorry
theorem insert_key_frame (key' : α) (h : key ≠ key') : (map.insert key val).lookup key' = map.lookup key' := by sorry

end FinMap


abbrev RegMap : Type := FinMap String Int
abbrev MemMap : Type := FinMap Nat Int

section RegMem

variable {regs : RegMap} 
variable {mem : MemMap}

def readReg (r : String) : Int := (regs.lookup r).get! -- TODO: maybe make proof-based
def readMem (addr : Nat) : Int := (mem.lookup addr).get!
#check readReg
def writeToReg (n : Int) (r : String) : RegMap := regs.insert r n
#check writeToReg
def writeToMem (n : Int) (addr : Nat) : MemMap := mem.insert addr n



def calcIndirectScaledIndex {regs : RegMap}  (d : Int) (rb : String) (ri : String) (s : {x : Nat // x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8}) : Nat := 
  Int.natAbs (d + (@readReg regs rb) + s * (@readReg regs ri))

def writeToDst (n : Int) (dst : Asm.OkDst) : RegMap × MemMap :=
match dst with
| .reg r => (@writeToReg regs n r, mem)
| .mem addr => (regs, @writeToMem mem n addr)
| .indirect r => (regs, @writeToMem mem n (@readReg regs r).natAbs) -- just fixing type error. Memory addresses are nonneg but mem vals can be neg
| .indirectDisp d r => (regs, @writeToMem mem n ((@readReg regs r) + d).natAbs)
| .indirectScaledIndex d rb ri s => (regs, @writeToMem mem n (@calcIndirectScaledIndex regs d rb ri s))

def getFromSrc (dstStyleSrc : Asm.OkDst) : Int :=
  match dstStyleSrc with
  | .reg r => @readReg regs r
  | .mem addr => @readMem mem addr
  | .indirect r => @readMem mem (@readReg regs r).natAbs
  | .indirectDisp d r => @readMem mem ((@readReg regs r) + d).natAbs
  | .indirectScaledIndex d rb ri s=> @ readMem mem (@calcIndirectScaledIndex regs d rb ri s)

def mov (src : Asm.OkSrc) (dst : Asm.OkDst) : (RegMap × MemMap) :=
  match src with
  | .imm n => @writeToDst regs mem n dst
  | .src dstStyleSrc => @writeToDst regs mem (@getFromSrc regs mem dstStyleSrc) dst

/- binSrcDst represents applying a binary operator to src and dst, storing the results in dst. -/
def binSrcDst (src : Asm.OkSrc) (dst : Asm.OkDst) (f : Int → Int → Int) : (RegMap × MemMap) :=
  let op1 : Int := match src with
  | .imm n => n
  | .src dstStyleSrc => @getFromSrc regs mem dstStyleSrc

  let op2 : Int := @getFromSrc regs mem dst

  @mov regs mem (.imm (f op1 op2)) dst

end RegMem
 
def AsmProgram.evalRec (p : AsmProgram) (regs : RegMap) (mem : MemMap) :=
      match p with
      | [] => @readReg regs "%rax" -- At end of instructions, get return value from %rax
      | i :: is => 
          match i with
          | .push n => 
           -- To push, move n to memory address pointed to by %rsp and decrease %rsp's value by 0x8
            Id.run do
            let mut state := (regs, mem)
            state := @mov state.fst state.snd (.imm n) (.indirect "%rsp")
            state := @mov state.fst state.snd (.imm ((@readReg regs "%rsp") - 0x8)) (.reg "%rsp")
            evalRec is state.fst state.snd
          | .pop dst => Id.run do
           -- To pop, go 8 bytes above what %rsp points to. Move it to dst, and increase %rsp's value by 0x8
            let mut state := (regs, mem)
            state := @mov state.fst state.snd (.src (.indirectDisp 0x8 "%rsp")) dst
            state := @mov state.fst state.snd (.imm ((@readReg regs "%rsp") + 0x8)) (.reg "%rsp")
            evalRec is state.fst state.snd
          | .add src dst => 
              -- To add, add the value stored for src to the value in dst
              let state := (@binSrcDst regs mem src dst fun e1 e2 => e1 + e2)
              evalRec is state.fst state.snd 
          | .imul src dst => 
              -- To mul
              let state := (@binSrcDst regs mem src dst fun e1 e2 => e1 * e2)
              evalRec is state.fst state.snd  

/- An interpreter for AsmProgram -/
  def AsmProgram.eval (p : AsmProgram) : Int := 
  -- Can I have one finite map Σ⋆ → ℕ to represent registers
  -- And another finite map ℕ → ℕ to rrepresent memory  
      -- we need regs to contain rsp and rax having something off the bat
      evalRec p (fun r => if r == "%rsp" then some 0xfffffff else if r == "%rax" then some 0x0 else none) 
      (fun a => if a == 0xfffffff then some 0x0 else none)

#eval ((1 + 6) * 2 + 3 * (4 + 5) : Expr).toStackProgram.toAsmProgram.toString

open IO.FS (writeFile)
def Expr.compile : Expr → System.FilePath → IO Unit :=
  fun expr => 
    fun fp => writeFile fp expr.toStackProgram.toAsmProgram.toString

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
lemma eval_add_eq_eval_plus_eval (e1 e2 : Expr) : (Expr.add e1 e2).eval = e1.eval + e2.eval := by rfl

open StackIR Expr in
lemma sp_add_stack_eq_sp_fst_concat_sp_snd (e1 e2 : Expr) : toStackProgram (Expr.add e1 e2) = toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.add] := by rfl


lemma eval_mul_eq_eval_times_eval (e1 e2 : Expr) : (Expr.mul e1 e2).eval = e1.eval * e2.eval := by rfl


open StackIR Expr in
lemma sp_mul_stack_eq_sp_fst_concat_sp_snd (e1 e2 : Expr) : toStackProgram (Expr.mul e1 e2) = toStackProgram e1 ++ toStackProgram e2 ++ [StackIR.mul] := by rfl



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
      /-(toStackProgram e1)  (toStackProgram e2) [StackIR.add]]-/
      have h1 := (ih1 (toStackProgram e2 ++ [StackIR.add] ++ sp) s)
      rw [List.append_assoc (toStackProgram e1), List.append_assoc]
      rw [h1]
      have h2 := (ih2 ([StackIR.add] ++ sp) ((eval e1) :: s))
      rw [List.append_assoc (toStackProgram e2)]
      rw [h2]
      rfl
  | mul e1 e2 ih1 ih2 =>
      rw [eval_mul_eq_eval_times_eval]
      rw [sp_mul_stack_eq_sp_fst_concat_sp_snd]
      have h1 := (ih1 (toStackProgram e2 ++ [StackIR.mul] ++ sp) s)
      rw [List.append_assoc (toStackProgram e1), List.append_assoc]
      rw [h1]
      have h2 := (ih2 ([StackIR.mul] ++ sp) ((eval e1) :: s))
      rw [List.append_assoc (toStackProgram e2)]
      rw [h2]
      rfl
  
  lemma eval_eq_eval_rec_empty_stack (p : StackProgram) : p.eval = p.evalRec [] := by rfl
  theorem expr_to_stack_compile_ok (e : Expr) : e.toStackProgram.eval = e.eval := by
  cases e with
  | lit n => rfl
  | add e1 e2 => 
      rw [eval_eq_eval_rec_empty_stack]
      have : Expr.toStackProgram (Expr.add e1 e2) = Expr.toStackProgram (Expr.add e1 e2) ++ [] := by simp
      rw [this]
      rw [expr_to_stack_compile_ok']
      rfl
  | mul e1 e2 => 
      rw [eval_eq_eval_rec_empty_stack]
      have : Expr.toStackProgram (Expr.mul e1 e2) = Expr.toStackProgram (Expr.mul e1 e2) ++ [] := by simp
      rw [this]
      rw [expr_to_stack_compile_ok']
      rfl



-- I think my assembly interpreter will shove things into 


-- For all StackPrograms: evaluating is equivalent to compiling to AsmIR and evaluating.

/- I think I want to keep track of the registers and memory. And then say if you take a stack program and 
run the concantenation of it and some assembly program, that's equivalent to running that assembly program with the state generated by running a compiled version of the stack program
-/
/-
theorem stack_to_asm_compile_ok' (sp : StackProgram) (asm : AsmProgram) (regs : RegMap) (mem : MemMap) :
(sp.toAsmProgram ++ asm).evalRec regs mem = asm
-/

-- Sorry, this lemma is unhelpful for now. Also I would be shocked if it weren't built in already
lemma list_cons_append_assoc {α : Type} (x : α) (xs ys : List α) : (x :: xs) ++ ys = x :: (xs ++ ys) := by simp

lemma asm_compile_cons_eq_compile_append_compile (x : StackIR) (xs : StackProgram): StackProgram.toAsmProgram (x :: xs) = StackProgram.toAsmProgram [x] ++ xs.toAsmProgram := by
-- induction xs generalizing x with
induction xs generalizing x with
| nil =>  simp
| cons y ys ih => 
    rw [ih y]
    cases x 
    simp
    rw [ih y]
    simp
    rw [ih y]
    simp
    rw [ih y]

   


  



-- I think the assembly interpreter proof equivalent is running the stack program and putting the result into [%rsp]
theorem stack_to_asm_compile_ok' (sp : StackProgram) (ap : AsmProgram) (spIsNonEmpty : sp ≠ []) :
   (sp.toAsmProgram ++ ap).eval = AsmProgram.eval ((.push sp.eval) :: ap) := by
   induction sp generalizing ap with
   | nil => contradiction
   | cons x xs ih => 
    rw [asm_compile_cons_eq_compile_append_compile]
    simp
    -- why am i stuck?




      -- the recursive call in AsmRec exposes the new state
      -- in AsmProgram.evalRec you do some assignments based on the first instruction
      --  and then work with just the rest of the instructions.
      -- I really want to work with x directly

-- is it the case that StackProgram.toAsmProgram (x :: xs) = [x].toAsmProgram ++ xs.toAsmProgram?
-- because if that held I could just use the IH twice maybe
-- yeah that doesn't work, I think, but I was able to prove the lemma
      
   

   
-- ap.evalRec (writeToDst sp.eval Asm.OkDst.indirect "%rsp").fst (writeToDst sp.eval Asm.OkDst.indirect "%rsp").snd := by


theorem stack_to_asm_compile_ok  (sp : StackProgram) (spIsNonEmpty : sp ≠ []): sp.eval = sp.toAsmProgram.eval := by
  induction sp with
  | nil => rfl
  | cons x xs ih => 
  
  -- Unfold eval into evalrec with whatever is in registers
  -- need to build a correspondence between what happens on stack to what happens in registers


