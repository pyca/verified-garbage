module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on AArch64, `sign_message`: pieces of the constant-time proofs

Untrusted: everything here is checked by Lean. What the contract says two
runs agree on, which includes what `signMessageLeak` says (`signI`), and
that the branch on `ctx_len`, the entry and the exit leak only the pointers
and the lengths (`lsr_taint`, `movz2_taint`, `enterS_taint`,
`leave_taint`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ L.key p.skLen) (bytesAt m₁ L.msg L.len.toNat) (bytesAt m₁ L.ctx L.ctxLen.toNat)
      (bytesAt m₁ L.rnd 32) =
    signMessageLeak p (bytesAt m₂ L.key p.skLen) (bytesAt m₂ L.msg L.len.toNat)
      (bytesAt m₂ L.ctx L.ctxLen.toNat) (bytesAt m₂ L.rnd 32)

/-- `μ` at `X + 840`. -/
def MuOk (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : Lay} (hL : L.Ok) (hk : L.keyLen = p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m L.key p.skLen) (bytesAt m L.msg L.len.toNat) (bytesAt m L.ctx L.ctxLen.toNat)
        (bytesAt m L.rnd 32) =
      signLeak p (bytesAt m L.key p.skLen) (H (bytesAt m (L.key + BitVec.ofNat 64 64) 64 ++ hdrBytes L ++
        bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64) (bytesAt m L.rnd 32) := by
  have := hL.hKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.skLen
  xRnd : L.XS.Disjoint ⟨L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨L.rnd, 32⟩
  inRnd : (⟨L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.wr
  inScr : ∃ R ∈ L.wr, Within ⟨L.scr, sScr p⟩ R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) (s₁.gpr .x2).toNat)
      (bytesAt s₁.mem (s₁.gpr .x3) (s₁.gpr .x4).toNat) (bytesAt s₁.mem (s₁.gpr .x5) 32) =
    signMessageLeak p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) (s₂.gpr .x2).toNat)
      (bytesAt s₂.mem (s₂.gpr .x3) (s₂.gpr .x4).toNat) (bytesAt s₂.mem (s₂.gpr .x5) 32)
  x0 : s₁.gpr .x0 = s₂.gpr .x0
  x1 : s₁.gpr .x1 = s₂.gpr .x1
  x2 : s₁.gpr .x2 = s₂.gpr .x2
  x3 : s₁.gpr .x3 = s₂.gpr .x3
  x4 : s₁.gpr .x4 = s₂.gpr .x4
  x5 : s₁.gpr .x5 = s₂.gpr .x5
  x6 : s₁.gpr .x6 = s₂.gpr .x6
  x7 : s₁.gpr .x7 = s₂.gpr .x7

/-- After the shift of `ctx_len`. -/
abbrev ALsr (x s1 : State) : Prop :=
  Only [.x9] x s1 ∧ isa.eval (.nonzero .x .x9) s1 = some (decide ¬ (x.gpr .x4).toNat < 256)

theorem lsr_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.lsr .x .x9 .x4 8]) (.block [])).isSome = true := by rfl

theorem movz2_taint :
    (taint.check (AArch64.Taint.ofRegs []) (.block [.movz .x .x0 2 0]) (.block [])).isSome = true := by rfl

theorem leave_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs [.x7]) (.block (enter .x7 p signSaves)) (.block [])).isSome = true := by
  rfl

end

end VG.Proof.MlDsa.AArch64.Message
