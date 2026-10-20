module

public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspacesCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady

/-! # Relating independently initialized workspaces without assuming scratch equality -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure InitializationPublic where
  layout : ExecutionLayout
  pBytes : List Byte
  qBytes : List Byte
  pLength : pBytes.length = layout.pLen
  qLength : qBytes.length = layout.qLen
  pValue : Spec.Dsa.decodeBE pBytes = layout.modulus
  qValue : Spec.Dsa.decodeBE qBytes = layout.subgroup
  pOdd : layout.modulus % 2 = 1
  qOdd : layout.subgroup % 2 = 1

structure InitializationPre (p : InitializationPublic) (s : State) : Prop where
  scratch : Scr s p.layout.base usedBytes
  x0 : s.gpr .x0 = p.layout.base
  fields : ∀ f, word s.mem p.layout.base f.offset = p.layout.fields f
  pSource : Src s p.layout.base usedBytes (p.layout.fields .p) p.pBytes
  qSource : Src s p.layout.base usedBytes (p.layout.fields .q) p.qBytes

def InitializationPublic.workspace (p : InitializationPublic) : WorkspacePublic where
  base := p.layout.base
  extent := usedBytes
  pPointer := p.layout.fields .p
  qPointer := p.layout.fields .q
  pBytes := p.pBytes
  qBytes := p.qBytes
  digestLen := (p.layout.fields .digestLen).toNat
  extentBound := by decide
  pPositive := by rw [p.pLength]; have := p.layout.widths; omega
  qPositive := by rw [p.qLength]; exact p.layout.widths.1
  pBound := by rw [p.pLength]; have := p.layout.widths; omega
  qBound := by rw [p.qLength]; have := p.layout.widths; omega
  digestBound := (p.layout.fields .digestLen).isLt
  active := by decide
  lengths := by rw [p.pLength, p.qLength]; exact p.layout.lengths
  pOdd := by rw [p.pValue]; exact p.pOdd
  qOdd := by rw [p.qValue]; exact p.qOdd

def InitializationDone (p : InitializationPublic) (s : State) : Prop :=
  ∃ pi qi, Ready (p.layout.withInverses pi qi) s ∧
    word s.mem p.layout.base Field.mask.offset = p.layout.fields .mask

theorem initialization_ct : RelCT isa (Two InitializationPre) SignVerify.workspaces (Two InitializationDone) := by
  refine two_post (two_map InitializationPublic.workspace (fun p s h => ?_) workspaces_ct) ?_
  · refine ⟨h.scratch, h.x0, h.fields .p, h.fields .q, ?_, ?_, ?_, h.pSource, h.qSource⟩
    · change word s.mem p.layout.base Field.pLen.offset = BitVec.ofNat 64 p.pBytes.length
      rw [p.pLength]; exact (h.fields .pLen).trans p.layout.pLength
    · change word s.mem p.layout.base Field.qLen.offset = BitVec.ofNat 64 p.qBytes.length
      rw [p.qLength]; exact (h.fields .qLen).trans p.layout.qLength
    · change word s.mem p.layout.base Field.digestLen.offset = BitVec.ofNat 64 (p.layout.fields .digestLen).toNat
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h.fields .digestLen
  · intro p s h
    exact WP.mono (workspacesReady_ok h.scratch h.x0 h.fields h.pSource h.qSource
      p.pLength p.qLength p.pValue p.qValue p.pOdd p.qOdd)
      fun t ⟨pi, qi, hr, _, hm, _⟩ => ⟨pi, qi, hr, hm.trans (h.fields .mask)⟩

theorem initialization_related {s₁ s₂ : State} (h : Two InitializationDone s₁ s₂) : Two Ready s₁ s₂ := by
  obtain ⟨p, ⟨pi₁, qi₁, h₁, _⟩, ⟨pi₂, qi₂, h₂, _⟩, hsp⟩ := h
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁ h₂ p.pOdd p.qOdd
  exact ⟨_, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
