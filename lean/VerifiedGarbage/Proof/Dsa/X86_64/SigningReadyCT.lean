module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningShapeCT
import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
public import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
public import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
public import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Masks
public import VerifiedGarbage.Proof.Dsa.X86_64.Parity
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
public import VerifiedGarbage.Proof.Dsa.X86_64.Save
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
public import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
public import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.RsaPss.Params

/-! # The public schedule after independent signing-workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, hk⟩ := h
  have hw : ∀ i < 2 * c.layout.qLen, InRegions s.wr (c.layout.fields .out + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk.2.2]
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
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem signingSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
        Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact (signBody_ct M Sq).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64
