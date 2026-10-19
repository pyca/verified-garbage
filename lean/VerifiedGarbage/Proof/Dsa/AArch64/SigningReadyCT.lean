module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningShapeCT
import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
public import VerifiedGarbage.Proof.Dsa.AArch64.Child
public import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
public import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
public import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
public import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
public import VerifiedGarbage.Proof.Dsa.AArch64.Parity
public import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
public import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
public import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningMain
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
public import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
public import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
public import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
public import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.SigningMain
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream

/-! # The public schedule after independent signing-workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SigningCall.schedule (c : SigningCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := c.input.prefixLength
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) c.input.digestBound

theorem SigningAgrees.prefixLength {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.input.prefixLength = reference.input.prefixLength := by
  unfold SigningInput.prefixLength
  rw [h.digestLength, h.qBytes]

theorem SigningReady.body {reference : SigningCall} {s : State} (ha : reference.input.accepted = true)
    (h : SigningReady reference s) : ∃ pi qi, SigningBodyPre (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hk⟩ := h
  have hw : ∀ i < 2 * c.layout.qLen, InRegions s.wr (c.layout.fields .out + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk.wr]
    exact c.pre.writable i hi
  have hsep : ∀ i < 2 * c.layout.qLen,
      usedBytes ≤ ofs c.layout.base (c.layout.fields .out + BitVec.ofNat 64 i) := c.pre.separate
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change SigningOperands (c.layout.withInverses pi qi) c.input.values c.input.components.y c.input.components.q s at ho
  rw [hag.layout] at hr ho hw hsep hmask
  refine ⟨pi, qi, hr, ⟨c.input.values, c.input.components.y, c.input.components.q, ho, ?_⟩,
    ⟨true, hmask⟩, hw, hsep⟩
  change (c.input.digest.take _).length = reference.input.prefixLength
  rw [List.length_take, Nat.min_comm]
  exact hag.prefixLength

theorem signingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedSigningCall => SigningReady c.val) s₁ s₂) : Two SigningBodyPre s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

theorem signingSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
        Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.signingKey M.mm, Checks.privateKey M.mm,
    Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact (signBody_ct M).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64
