module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Fast
public import VerifiedGarbage.Impl.Weave

/-! The final authentication block and AES encryption of the initial counter
are independent. The two schedules share neither registers nor writable input. -/

@[expose] public section
namespace VG.Impl.AesGcm.AArch64.Contiguous.Tag

open VG.AArch64
open VG.Impl.Gcm.AArch64.Pmull (A Y mul tReg sReg)

def round (j : Nat) : List Instr :=
  [.ldrq .v29 .x21 (16*j), .vop (.aese .v28 .v29), .vop (.aesmc .v28 .v28)]

def last (nr : Nat) : List Instr :=
  [.ldrq .v29 .x21 (16*(nr-1)), .vop (.aese .v28 .v29),
   .ldrq .v29 .x21 (16*nr), .vop (.logic .eor .v28 .v28 .v29)]

def mask (nr : Nat) : List Instr :=
  [.ldrq .v28 .x20 0] ++ (List.range (nr-1)).flatMap round ++ last nr

def lengthInput : List Instr :=
  [.ldr .x .x10 .x19 alenO, .lsl .x .x10 .x10 3, .lsl .x .x9 .x26 3,
   .vop (.ins .d2 A 0 .x10), .vop (.ins .d2 A 1 .x9), .vop (.logic .eor A A Y)]

def lengths : List Instr := lengthInput ++
    mul Y A (sReg 1) (tReg 1) ++ [.vop (.rev .rev64b Y Y)]

def finish (nr : Nat) : Prog isa := .block <|
  VG.Impl.Weave.weaveG ((mask nr).map List.singleton) (lengths.map List.singleton) ++
    [.vop (.logic .eor Y Y .v28), .strq Y .x28 0]

end VG.Impl.AesGcm.AArch64.Contiguous.Tag
