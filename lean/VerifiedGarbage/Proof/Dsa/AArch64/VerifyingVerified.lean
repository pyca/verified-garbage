module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInitialize
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions

/-! ### `Dsa.AArch64.VerifyingABIPre`, which this module and modules that import it used -/

section

/-! # Buffer and stack resources for a complete verification call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingABI.pre {s : State} (h : VerifyingABI s) : VerifyingPre h.input s := by
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · simpa only [Nat.mul_zero, off_zero] using stackWord_read (count := 2) (j := 0) hargs (by decide) (by decide)
  · exact (ofNat_toNat64 _).symm
  · change s.gpr .x7 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x5).isLt) h.signatureScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x6) (by rw [h.rd]; simp)
      (Nat.le_of_lt (s.gpr .x7).isLt) h.digestScratch) h.used

def VerifyingABI.call {s : State} (h : VerifyingABI s) : VerifyingCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingAgreement`, which this module and modules that import it used -/

section

/-! # Only the verifying ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyingLayout_eq {p₁ p₂ : VerifyingInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .x2 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .x2 = BitVec.ofNat 64 p₂.pLen}
    {hq₁ : s₁.gpr .x3 = BitVec.ofNat 64 p₁.qLen} {hq₂ : s₂.gpr .x3 = BitVec.ofNat 64 p₂.qLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (hcx : s₁.gpr .x3 = s₂.gpr .x3) :
    p₁.layout s₁ hp₁ hq₁ = p₂.layout s₂ hp₂ hq₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold VerifyingInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold VerifyingInput.prefixLength
    rw [hdl, hqb]
  have hfields : verifyFieldValues s₁ p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      verifyFieldValues s₂ p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [verifyFieldValues, hd, hdl, hprefix, hac, hdi, hdx, h8, hcx]
  unfold VerifyingInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem verifyingAgreement {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (hcx : s₁.gpr .x3 = s₂.gpr .x3)
    (hsp : s₁.sp = s₂.sp)
    (a0 : s₁.gpr .x6 = s₂.gpr .x6) (a1 : s₁.gpr .x7 = s₂.gpr .x7)
    (a2 : stackArg s₁ 0 = stackArg s₂ 0)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : VerifyingAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat hdx
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat hcx
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a1]
  rw [← hp, ← hq] at hpub
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen = (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  exact ⟨verifyingLayout_eq a2 hp hq a0 hdl hpb hqb hdi hdx h8 hcx, hpb, hqb, hdl, hsp⟩

theorem verifyingPublicRelated {s₁ s₂ : State} (h₁ : VerifyingABI s₁) (h₂ : VerifyingABI s₂)
    (h : (Spec.Dsa.verifyContract abi).pub s₁ s₂) : Two VerifyingStart s₁ s₂ := by
  sig_pub [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, hcx, h8, _, a0, a1, a2, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, verifyingAgreement h₁ h₂ hdi hdx h8 hcx hsp a0 a1 a2 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.VerifyingABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.VerifyingReturn`, which this module and modules that import it used -/

section

/-! # Both verifying branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def VerifyingPost (p : VerifyingInput) (original t : State) : Prop :=
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.verifyBytes p.pLen p.qLen p.key p.signature p.digest).toNat ∧
  InScr p.base usedBytes original.mem t.mem ∧ Keep coreRegs original t

theorem verifyingRejected_ok {p : VerifyingInput} {original s : State} (h : VerifyingPre p original)
    (hs : VerifyingShapePost p original h.pLength h.qLength s) (ha : p.accepted = false) :
    WP isa (.block [movi .x0 0]) s
      (VerifyingPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hfalse := verifyBytes_invalid_shape (signature := p.signature) (digest := p.digest) hparams
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = s.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hret, hmem⟩, hk⟩ => ?_
  unfold VerifyingPost
  rw [hfalse]
  exact ⟨hret,
    by rw [hmem]; exact hs.frame, (hs.keep.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Verification correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem verifyStatus_u32 (result : Bool) :
    ((BitVec.ofNat 64 result.toNat).setWidth 32).toNat = if result then 1 else 0 := by
  cases result <;> rfl

end VG.Proof.Dsa.AArch64

end

end

/-! # DSA verifying verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def verifyingSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 404 | .x2 => 128 | .x3 => 20
    | .x4 => 0x4000 | .x5 => 40 | .x6 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x80 else if a = 0x10009 then 8 else 0
  rd := [⟨0x2000, 404⟩, ⟨0x4000, 40⟩, ⟨0x5000, 0⟩, ⟨0x10000, 16⟩]
  wr := [⟨0x8000, 16384⟩]

end VG.Proof.Dsa.AArch64
