module

public import VerifiedGarbage.Impl.Mont.X86.CombTable

/-! Public and private powers reuse one immutable RSA-format comb table. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def shiftOne (ew o : Nat) : Prog isa := .seq (.block [.mov .ecx (imm 0)]) (wordLoop ew [
    .mov .eax (.mem (at_ .ebp o)), .mov .ebx (.reg .eax), .shift .shr .ebx 31,
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
    .store (at_ .ebp o) .eax, .mov .ecx (.reg .ebx)])

def toothRead (o bit : Nat) : List Instr :=
  [.mov .eax (.mem (sc (o+4*(bit/32))))] ++
  (if bit%32 == 0 then [] else [.shift .shr .eax (bit%32)]) ++
  [.alu .and .eax (imm 1)]

def digit (o d : Nat) : Prog isa :=
  .block ([.mov .ebx (imm 0)] ++ (List.range 5).flatMap (fun j =>
    toothRead o ((j+1)*d-1) ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
    [.alu .or .ebx (.reg .eax)]) ++ [.store (sc windowOffset) .ebx])

def powerDigits (n e : Nat) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let ew := (5*d+31)/32
  seq [square n, digit (slot n 8) d, shiftOne ew (slot n 8)]

def powerLookup (n e context : Nat) (pub : Bool) : Prog isa :=
  seq [powerDigits n e,
    (if pub then publicSelect n (context+16*n) (slot n 7) else wordSelect n (context+16*n) (slot n 7))]

def powerStep (n e context : Nat) (pub : Bool) : Prog isa :=
  seq [powerLookup n e context pub,
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7),
    .block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)]]

def padWords (o used total : Nat) : Prog isa :=
  if used < total then zerosW (o+4*used) (total-used) else .block []

def powerInit (n e context : Nat) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let ew := (5*d+31)/32
  seq [copyWords n (context+16*n) (slot n 6), padWords (slot n 8) e ew,
    .block [.mov .esi (imm d)]]

def combPower (n e context : Nat) (pub : Bool) : Prog isa :=
  seq [powerInit n e context,
    .loop (powerStep n e context pub) .ne,
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3)]

end VG.Impl.Mont.X86.Comb
