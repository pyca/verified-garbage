module

import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPrefix
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFirstRetained
import VerifiedGarbage.Proof.Ffdh.Arm.KeySuffix
import VerifiedGarbage.Proof.Ffdh.Arm.KeyCutEncoding
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes

/-! Native entropy cutting produces exactly the shared scalar encoding. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyCut_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h20 : 20 ∈ slots) (h68 : 68 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy) (dest : s.gpr .r0 = p.privateValue)
    (count : s.gpr .lr = BitVec.ofNat 32 p.scalarLead) (zero : s.gpr .r2 = 0) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy s fun t =>
      ArgumentMemory p slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k =
        VG.Proof.Ffdh.KeyScalar.cut rb p.scalarLead (p.scalarMask.setWidth 8) ∧
      Frame [⟨State.addr p.privateValue, p.k⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  have lead := p.scalarLeadBound
  have bounds := p.maxLength
  have prefixSub : (⟨State.addr p.privateValue, p.scalarLead⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Region.sub_prefix (by omega)
  have suffixSub : (scalarSuffix p).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Offset.sub_base _ (by omega)
  have firstAddr : State.addr p.scalarStart = off (State.addr p.privateValue) p.scalarLead :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have firstSub : (⟨State.addr p.scalarStart, 1⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ := by
    rw [firstAddr]
    exact Offset.sub_base _ (by omega)
  have prefixFirst : (⟨State.addr p.privateValue, p.scalarLead⟩ : Region).Disjoint ⟨State.addr p.scalarStart, 1⟩ := by
    rw [firstAddr]
    exact (Offset.disjoint_base _ (by omega) (by omega)).symm
  have prefixSuffix : (⟨State.addr p.privateValue, p.scalarLead⟩ : Region).Disjoint (scalarSuffix p) :=
    (Offset.disjoint_base _ (by omega) (by omega)).symm
  have firstSuffix : (⟨State.addr p.scalarStart, 1⟩ : Region).Disjoint (scalarSuffix p) := by
    rw [firstAddr]
    exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.cutEntropy, WP.seq_iff]
  refine WP.mono (keyPrefix_ok s h saved output domainSep stackSep source dest count zero) ?_
  rintro u ⟨contextU, bytesU, ptrU, srcU, frameU, restU⟩
  have entropyU := entropy.after_frame frameU restU (by simpa [size] using entropySep.sub_right prefixSub)
  rw [WP.seq_iff]
  refine WP.mono (keyFirst_retained u contextU saved h20 h68 entropyU size (output.after restU)
    domainSep (by rw [restU.sp]; exact stackSep) entropySep srcU ptrU) ?_
  rintro v ⟨contextV, entropyV, byteV, ptrV, srcV, countV, frameV, restV⟩
  have suffixCount : v.gpr .lr = BitVec.ofNat 32 (p.k - (p.scalarLead + 1)) := by
    rw [countV]
    congr 1
  refine WP.mono (keySuffix_ok v contextV saved entropyV size ((output.after restU).after restV)
    domainSep (by rw [restV.sp, restU.sp]; exact stackSep) entropySep srcV ptrV suffixCount) ?_
  rintro t ⟨contextT, entropyT, suffix, frameT, restT⟩
  have prefixV : Spec.Rsa.bytesAt v.mem (State.addr p.privateValue) p.scalarLead = List.replicate p.scalarLead 0 := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frameV (by omega) (by simpa using prefixFirst)]
    exact bytesU
  have prefixT : Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.scalarLead = List.replicate p.scalarLead 0 := by
    rw [VG.Proof.Bignum.Arm.rsa_bytes_frame frameT (by omega) (by simpa using prefixSuffix)]
    exact prefixV
  have byteT : t.mem (State.addr p.scalarStart) = rb.getD p.scalarLead 0 &&& p.scalarMask.setWidth 8 := by
    have same := frameT.bytes (R := ⟨State.addr p.scalarStart, 1⟩) (by simpa using firstSuffix) (by change 1 ≤ 2 ^ 64; decide) (i := 0) (by change 0 < 1; decide)
    simp only [BitVec.add_zero] at same
    exact same.trans byteV
  have encoded := keyCutEncoding (by omega : p.scalarLead < rb.length) prefixT (by rw [← firstAddr]; exact byteT)
    (by simpa only [size, scalarSuffix] using suffix)
  have fullU : Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem :=
    frameU.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, prefixSub⟩)
  have fullV : Frame [⟨State.addr p.privateValue, p.k⟩] u.mem v.mem :=
    frameV.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, firstSub⟩)
  have fullT : Frame [⟨State.addr p.privateValue, p.k⟩] v.mem t.mem :=
    frameT.sub (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact ⟨_, by simp, suffixSub⟩)
  exact ⟨contextT, entropyT, by simpa only [size] using encoded, (fullU.trans fullV).trans fullT,
    ((restU.mono (by simp)).trans restV).trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm
