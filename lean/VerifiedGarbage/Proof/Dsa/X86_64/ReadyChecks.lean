module

public import VerifiedGarbage.Proof.Dsa.X86_64.Modulus
public import VerifiedGarbage.Proof.Dsa.X86_64.CheckFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.LocalCallFrame
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.MaskContext

/-! # Preserving both DSA arithmetic contexts across validation checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem nonmask_field (f : Field) (h : f ≠ .mask) : f.offset + 8 ≤ Field.mask.offset := by
  cases f <;> first | decide | exact False.elim (h rfl)

theorem rangeFrame_local {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : RangeFrame B o wx mem mem') (ho : o + slot wx 8 + tabBytes wx ≤ 2 ^ 64) :
    Frm B (localCallRanges o wx Field.mask.offset 8) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  intro x hx
  apply hf x
  · intro r hr
    have h := hx (128, 48) (by simp [localCallRanges])
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [arg, argLen] <;> omega
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have h := hx (o + 136, slot wx 8 + tabBytes wx - 136) (by simp [localCallRanges])
    rcases ofs_rebase B x (o := o) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at * <;> omega
  · exact hx (Field.mask.offset, 8) (by simp [localCallRanges])

theorem checkFrame_field {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem') (ho : pWorkspace ≤ o)
    (f : Field) (hm : f ≠ .mask) : word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  have hm' := nonmask_field f hm
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro r hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; omega
  · left; omega
  · exact Or.inl hm'

theorem Ready.afterCheck {L : ExecutionLayout} {s t : State} (side : ModulusSide)
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base side.offset (side.words L) (side.value L) (side.inverse L))
    (hf : RangeFrame L.base side.offset (side.words L) s.mem t.mem)
    (hk : Keep coreRegs s t) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hhi := (side.bounds L).2.2.2.2.1
  have ho : pWorkspace ≤ side.offset := by cases side <;> decide
  have hlf := rangeFrame_local hf (by omega)
  have hfields : ∀ f, f ≠ .mask → word t.mem L.base f.offset = L.fields f :=
    fun f hm => (checkFrame_field hlf ho f hm).trans (h.fields f hm)
  cases side
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields, hc,
      localCall_ready hlf h.qChild (by decide) (by omega) (Or.inr hpHi) (Or.inr (by decide))⟩
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields,
      localCall_ready hlf h.pChild (by decide) (by omega) (Or.inl (by change pWorkspace + slot L.pWords 8 ≤ qWorkspace; omega)) (Or.inr (by decide)), hc⟩

theorem Ready.afterMask {L : ExecutionLayout} {s t : State}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hf : Outside L.base Field.mask.offset 8 s.mem t.mem) (hk : Keep coreRegs s t) : Ready L t := by
  have hhi := (ModulusSide.p.bounds L).2.2.2.2.1
  have hqi := (ModulusSide.q.bounds L).2.2.2.2.1
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ activeBytes at hhi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqi
  have hn := h.scratch.nowrap
  have hau : activeBytes ≤ usedBytes := by decide
  refine ⟨hp, h.scratch.congr hk.2.2, ?_,
    maskWrite_child h.pChild hf (by decide) (by omega),
    maskWrite_child h.qChild hf (by decide) (by omega)⟩
  intro f hm
  exact (hf.word (Or.inl (nonmask_field f hm))
    (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).trans (h.fields f hm)

end VG.Proof.Dsa.X86_64
