module

import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Spec.RsaPkcs1Sig
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# RSASSA-PKCS1-v1_5 on PPC64LE: the frame

`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`
allocate a frame of `frameBytes` bytes (`stdu r1, -frameBytes(r1)`). Its
Parameter Save Area holds the stack arguments of the call of
`vg_rsa_public_precomputed_checked`, `scratch` and `scratch_len` (at
`r1 + 96`, `r1 + 104`). Then come our caller's `r28`–`r31` and our return
address, which the call (`bl`) overwrites in the link register (`oSave`);
the call's status (`oSt`); `recover`'s mask (`oMk`); and the two buffers
`EM₁` and `EM₂` of up to 1024 bytes (`oEM1`, `oEM2`). Our own stack
arguments are then at `r1 + frameBytes + 96 + 8 i` (`arg i`). The frame is
addressed through `r12`, which holds `r1`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)

/-- The size of the frame. -/
def frameBytes : Nat := 2224

/-- Our caller's `r28`–`r31`, our return address, the status and the mask. -/
def oSave : Nat := 112
def oLr : Nat := 144
def oSt : Nat := 152
def oMk : Nat := 160

/-- The buffers. -/
def oEM1 : Nat := 168
def oEM2 : Nat := 1192

/-- Our stack argument `i` (from 0), in the frame. -/
def arg (i : Nat) : Nat := frameBytes + 96 + 8 * i

/-- `vg_rsa_public_precomputed_checked`. -/
def pubCall : Prog isa :=
  .call "vg_rsa_public_precomputed_checked" Impl.Bignum.PPC64LE.PublicChecked.publicChecked

/-- `r12 := r1`; our caller's `r28`–`r31` and our return address into the
frame. -/
def save : List Instr :=
  [.addSp .r12 0, .store .d .r28 .r12 oSave, .store .d .r29 .r12 (oSave + 8), .store .d .r30 .r12 (oSave + 16),
    .store .d .r31 .r12 (oSave + 24), .mflr .r0, .store .d .r0 .r12 oLr]

/-- Our caller's `r28`–`r31` and our return address back from the frame. -/
def restore : List Instr :=
  [.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0, .load .d .r28 .r12 oSave, .load .d .r29 .r12 (oSave + 8),
    .load .d .r30 .r12 (oSave + 16), .load .d .r31 .r12 (oSave + 24)]

/-- `scratch` and `scratch_len` (our stack arguments 1 and 2) to the call's
stack arguments; `pre` and `pre_len` (our stack arguments 3 and 4) into `r5`
and `r6`; `r3 := EM₁`. -/
def callTail : List Instr :=
  [.load .d .r0 .r12 (arg 1), .store .d .r0 .r12 96, .load .d .r0 .r12 (arg 2), .store .d .r0 .r12 104,
    .load .d .r5 .r12 (arg 3), .load .d .r6 .r12 (arg 4), .addi .r3 .r12 oEM1]

/-- 0 returned. -/
def ret0 : List Instr := [.li .r3 0]

/-- `compare`'s registers: `EM₁`, `EM₂` and `k` (in `r`). -/
def cmpArgs (r : Reg) : List Instr := [.addSp .r12 0, .addi .r4 .r12 oEM1, .addi .r5 .r12 oEM2, mov .r6 r]

end VG.Impl.RsaPkcs1Sig.PPC64LE
