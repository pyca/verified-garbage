module

public import VerifiedGarbage.Impl.Bignum.AArch64.Square

/-!
Eight-limb blocked Montgomery reduction. The eight cancellation coefficients
are retained in the eliminated low words; each subsequent eight-word modulus
block is loaded once and accumulated in registers. Callee-saved registers are
saved in the output only after the complete product has consumed the inputs.
Output aliasing the modulus and unsupported widths use the existing kernel.
The public width guard retains the existing implementation for other sizes.
-/

@[expose] public section

namespace VG.Impl.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

-- N[0] is loaded on demand so x1 can retain the extra carry bit.
def aa : List Reg := [.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26]
def nn : List Reg := [.x2,.x3,.x4,.x5,.x6,.x9,.x11]
def tt : List Reg := [.x13,.x14,.x28,.x30]
def saved : List Reg := aa ++ [.x27,.x28,.x30]
def saves (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => st r .x16 (8*i))
def restores (o : Nat) : List Instr := [ldh .x16 (sArr o)] ++
  (saved.zipIdx.map fun (r,i) => ld r .x16 (8*i))
def nsLoad : List Instr := nn.zipIdx.map fun (r,i) => ld r .x17 (8*(i+1))
def asLoad : List Instr := aa.zipIdx.map fun (r,i) => ld r .x8 (8*i)
def asStore : List Instr := aa.zipIdx.map fun (r,i) => st r .x16 (8*i)
def product (hi : Bool) (j : Nat) (t : Reg) : List Instr :=
  let ins (n : Reg) := if hi then Instr.umulh t .x27 n else Instr.mul .x t .x27 n
  if j = 0 then [ld t .x17, ins t] else [ins nn[j-1]!]
def lowChain : List Instr :=
  (List.range 4).flatMap (fun j => product false j tt[j]!) ++
  (List.range 8).flatMap (fun j =>
    [(if j = 0 then Instr.adds else Instr.adcs) .x aa[j]! aa[j]! tt[j%4]!] ++
    (if j < 4 then product false (j+4) tt[j%4]! else product true (j-4) tt[j%4]!))
def highChain : List Instr :=
  (List.range 8).flatMap (fun j =>
    [(if j = 0 then Instr.adds else Instr.adcs) .x aa[j]!
      (if j < 7 then aa[j+1]! else .x1) tt[j%4]!] ++
    (if j < 4 then product true (j+4) tt[j%4]! else []))
def cancel (i : Nat) : List Instr :=
  [.mul .x .x27 .x19 .x15, st .x27 .x8 (8*i), movi .x1 0] ++
  lowChain ++ [.adc .x .x1 .x1 .x7] ++ highChain

def tail (i : Nat) : List Instr :=
  [.adc .x .x1 .x7 .x7, ld .x27 .x8 (8*i)] ++ lowChain ++
  [.adc .x .x1 .x1 .x7, st .x19 .x16, next .x16] ++ highChain

def addMemory (pending : Bool) : List Instr :=
  (if pending then [movi .x1 1, .subs .x .x1 .x10 .x1] else []) ++
  (List.range 8).flatMap (fun i => [ld .x13 .x16 (8*i),
    (if i = 0 ∧ !pending then Instr.adds else Instr.adcs) .x aa[i]! aa[i]! .x13])

def redc : Prog isa :=
  .seq (.block [.lsr .x .x12 .x12 3, movi .x10 0])
  (.seq (.loop
    (.seq (.block (asLoad ++ [ldh .x17 (sArr Public.aN), ldh .x15 sMinv] ++ nsLoad ++
       (List.range 8).flatMap cancel ++
       [.addImm .x .x16 .x8 64, .addImm .x .x17 .x17 64,
        ldh .x15 sW, .lsr .x .x15 .x15 3, .subImm .x .x15 .x15 1]))
     (.seq (countLoop .x15 (addMemory false ++ nsLoad ++
        (List.range 8).flatMap tail ++ [.addImm .x .x17 .x17 64]))
      (.block (addMemory true ++ [.adc .x .x10 .x7 .x7] ++ asStore ++
        [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))))
    (.nonzero .x .x12))
    (.block [ldh .x12 sW, .lsl .x .x16 .x12 3, .add .x .x16 .x8 .x16,
      st .x10 .x16, st .x7 .x16 8, ldh .x10 (sArr Public.aN)]))

def square (o a : Nat) : Prog isa :=
  .seq (Square.rawSquare a) (.seq (.block (saves o))
    (.seq redc (.seq (.block (restores o ++ Square.finishBases o))
      (.seq subMod selectAcc))))

def mm (o a b : Nat) : Prog isa :=
  if a = b ∧ o ≠ Public.aN then
    .seq (.block [ldh .x12 sW, .lsr .x .x3 .x12 4, movi .x4 7,
      .logic .and .x .x4 .x12 .x4])
      (.ite (.nonzero .x .x3)
        (.ite (.zero .x .x4) (square o a) (Square.montMul o a b))
        (Square.montMul o a b))
  else Square.montMul o a b

end VG.Impl.Bignum.AArch64.BlockedRedc
