module

public import VerifiedGarbage.Impl.Mont.X86.CombTable

/-! Public and private powers reuse one immutable RSA-format comb table. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def combPower (n e context : Nat) (pub : Bool) : Prog isa :=
  let d := VG.Spec.Rsa.FixedBaseComb.rows (32*e)
  let ew := (5*d+31)/32
  let digit := .block ([.mov .ebx (imm 0)] ++ (List.range 5).flatMap (fun j =>
    let bit := (j+1)*d-1
    [.mov .eax (.mem (sc (slot n 8+4*(bit/32))))] ++
    (if bit%32 == 0 then [] else [.shift .shr .eax (bit%32)]) ++
    [.alu .and .eax (imm 1)] ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
    [.alu .or .ebx (.reg .eax)]) ++ [.store (sc windowOffset) .ebx])
  let shiftOne := .seq (.block [.mov .ecx (imm 0)]) (wordLoop ew [
    .mov .eax (.mem (at_ .ebp (slot n 8))), .mov .ebx (.reg .eax), .shift .shr .ebx 31,
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .ecx),
    .store (at_ .ebp (slot n 8)) .eax, .mov .ecx (.reg .ebx)])
  seq [copyWords n (context+16*n) (slot n 6),
    (if e < ew then zerosW (slot n 8+4*e) (ew-e) else .block []),
    .block [.mov .esi (imm d)],
    .loop (seq [square n, digit, shiftOne,
      (if pub then publicSelect n (context+16*n) (slot n 7) else wordSelect n (context+16*n) (slot n 7) 32),
      Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 7),
      .block [.alu .sub .esi (imm 1), .alu .cmp .esi (imm 0)]]) .ne,
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 6) (slot n 6) (slot n 3)]


end VG.Impl.Mont.X86.Comb
