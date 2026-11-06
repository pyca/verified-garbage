module

public import VerifiedGarbage.Impl.X448.AArch64.Symmetric

/-! Narrow carry passes after the first wide pass has cleared high words. -/

@[expose] public section

namespace VG.Impl.X448.AArch64.Tail

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st TMP)

def regs : List Instr :=
  [.add .x .x4 .x4 .x6, .lsr .x .x6 .x4 56, .logic .and .x .x4 .x4 .x9]

def step (o i : Nat) (unpack : Bool) : List Instr :=
  [ld .x4 (TMP + 16 * i)] ++ regs ++
  (if unpack then [.lsr .x .x5 .x4 28, .logic .and .x .x4 .x4 .x12,
    st .x4 (o + 16 * i), st .x5 (o + 16 * i + 8)]
   else [st .x4 (TMP + 16 * i)])

def pass (o : Nat) (unpack : Bool) : List Instr :=
  Wide.passInit ++ (List.range 8).flatMap (fun i => step o i unpack)

def normalize (o : Nat) : List Instr :=
  Wide.pass TMP false ++ Wide.fold ++ pass TMP false ++ Wide.fold ++ pass o true

end VG.Impl.X448.AArch64.Tail
