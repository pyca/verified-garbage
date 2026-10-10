import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Impl.Weierstrass.JacMul

/-! Register forwarding within a complete public P-256 point doubling. -/
namespace VG.Impl.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass

def writeReg : Instr → Option Reg
  | .add _ d _ _ | .sub _ d _ _ | .adds _ d _ _ | .adcs _ d _ _
  | .subs _ d _ _ | .sbcs _ d _ _ | .adc _ d _ _ | .sbc _ d _ _
  | .csel _ d _ _ | .logic _ _ d _ _ | .mul _ d _ _ | .umulh d _ _
  | .madd _ d _ _ _ | .lsr _ d _ _ | .lsl _ d _ _ | .extr _ d _ _ _
  | .movz _ d _ _ | .movk _ d _ _ | .ldr _ d _ _ => some d
  | _ => none

def readRegs : Instr → List Reg
  | .add _ _ a b | .sub _ _ a b | .adds _ _ a b | .adcs _ _ a b
  | .subs _ _ a b | .sbcs _ _ a b | .adc _ _ a b | .sbc _ _ a b
  | .csel _ _ a b | .logic _ _ _ a b | .mul _ _ a b | .umulh _ a b
  | .extr _ _ a b _ => [a,b]
  | .madd _ _ a b c => [a,b,c]
  | .lsr _ _ a _ | .lsl _ _ a _ | .movk _ a _ _ | .ldr _ _ a _ => [a]
  | .str _ a b _ => [a,b]
  | .movz .. => []
  | _ => [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

def renameRead (a b : Reg) (i : Instr) : Instr :=
  let f := fun r => if r==a then b else r
  match i with
  | .add z d n m => .add z d (f n) (f m)
  | .sub z d n m => .sub z d (f n) (f m)
  | .adds z d n m => .adds z d (f n) (f m)
  | .adcs z d n m => .adcs z d (f n) (f m)
  | .subs z d n m => .subs z d (f n) (f m)
  | .sbcs z d n m => .sbcs z d (f n) (f m)
  | .adc z d n m => .adc z d (f n) (f m)
  | .sbc z d n m => .sbc z d (f n) (f m)
  | .csel z d n m => .csel z d (f n) (f m)
  | .logic o z d n m => .logic o z d (f n) (f m)
  | .mul z d n m => .mul z d (f n) (f m)
  | .umulh d n m => .umulh d (f n) (f m)
  | .madd z d n m q => .madd z d (f n) (f m) (f q)
  | .lsr z d n k => .lsr z d (f n) k
  | .lsl z d n k => .lsl z d (f n) k
  | .extr z d n m k => .extr z d (f n) (f m) k
  | .str z n m k => .str z (f n) (f m) k
  | i => i

def regDead (r : Reg) : List Instr → Bool
  | [] => true
  | i::is => if (readRegs i).contains r then false
      else if writeReg i==some r then true else regDead r is

/-- Whether `renameRead` renames every register the instruction reads: all but
`movk`, which reads the register it writes. -/
def renames : Instr → Bool
  | .movk .. => false
  | _ => true

def foldMoves : List Instr → List Instr
  | (.logic .orr .x d a b)::i::is =>
    if a==b && regDead d is && !(readRegs i).contains .x0 && writeReg i !=none && renames i then
      renameRead d a i :: foldMoves is
    else .logic .orr .x d a b :: foldMoves (i::is)
  | i::is => i::foldMoves is
  | [] => []

def put {α β : Type} [BEq α] (k : α) (v : β) (xs : List (α×β)) : List (α×β) :=
  (k,v)::xs.filter (fun x => x.1 != k)

/-- Build the output in reverse to avoid copying every emitted prefix during kernel evaluation. -/
def forward (is : List Instr) : List Instr := Id.run do
  let mut regs : List (Reg×Nat) := []
  let mut mem : List (Nat×Nat) := []
  let mut out : List Instr := []
  let mut fresh := 1
  for i in is do
    fresh := fresh+1
    match i with
    | .ldr .x d .x0 off =>
      let value := (mem.lookup off).getD fresh
      let src := if regs.lookup d==some value then some d
        else (regs.find? (fun p => p.2==value)).map Prod.fst
      match src with
      | some r => if r !=d then out := .logic .orr .x d r r :: out
      | none => out := i :: out
      regs := put d value regs
      mem := put off value mem
    | .str .x r .x0 off =>
      let value := (regs.lookup r).getD fresh
      mem := put off value mem
      regs := put r value regs
      out := i :: out
    | .movz .x r 0 _ =>
      if regs.lookup r !=some 0 then out := i :: out
      regs := put r 0 regs
    | _ =>
      out := i :: out
      match writeReg i with
      | some d => regs := put d fresh regs
      | none => regs := []; mem := []
  return out.reverse

def deadStores (is : List Instr) : List Instr := Id.run do
  let mut later : List Nat := []
  let mut out : List Instr := []
  for i in is.reverse do
    match i with
    | .str .x _ .x0 off =>
      if !later.contains off then out := i::out
      later := off::later
    | .ldr .x _ .x0 off =>
      later := later.filter (· != off)
      out := i::out
    | _ =>
      if writeReg i==none then later := []
      out := i::out
  return out

/-- Forward field words across the complete point-doubling block, remove stores
superseded before a read, and propagate one-use register copies. -/
def optimize (is : List Instr) : List Instr :=
  deadStores (foldMoves (forward is))

/-- This entry point is used only for the measured P-256 verification doublings.
Other field programs retain the ordinary field-operation compiler. -/
def double (M : Mod) (S : RcbSlots) (p o : Pt) : Prog isa :=
  .block (optimize (fprog M (dblJMul S p o)))

end VG.Impl.Weierstrass.AArch64.Forward
