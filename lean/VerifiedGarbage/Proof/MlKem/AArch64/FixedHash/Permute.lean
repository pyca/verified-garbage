module

public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset

/-! Direct permutation calls keep the fixed hash's saved link slot outside
of the permutation's 512-byte workspace. -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_ok (v : Proof.Sha3.AArch64.Permutation)
    {sc : Reg} {st wk rate : Nat} {s₀ s : State}
    (hS : HSetup sc st wk rate s₀) (hg : Rg s₀ s) :
    WP isa (.seq (.block (ptrTo .x0 sc st ++ ptrTo .x1 sc wk))
      (.call v.callee.name v.callee.code)) s fun t =>
      Kept [STr sc st s₀, ⟨s₀.gpr sc + BitVec.ofNat 64 wk,512⟩] s t ∧
      stateAt t.mem (s₀.gpr sc + BitVec.ofNat 64 st) =
        keccakF (stateAt s.mem (s₀.gpr sc + BitVec.ofNat 64 st)) := by
  have ns := Proof.Sha3.AArch64.preserved_x0_x1 sc hS.hsc.1
  refine WP.seq (wp_ptrTo ns.1.symm hS.hst fun s₁ h₁ e₁ =>
    wp_ptrTo' ns.2.symm hS.hwk fun s₂ h₂ e₂ => ?_)
  have mm : s₂.mem = s.mem := h₂.mem.trans h₁.mem
  have kk : Kept [] s s₂ := Kept.of_keep (h₁.trans h₂).keep mm (by decide)
  have ds : (STr sc st s₀).Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 wk,512⟩ :=
    hS.d.sub_right (by intro a h; exact Nat.le_trans h (show 512≤640 by decide))
  have cw : Covers [STr sc st s₀, ⟨s₀.gpr sc + BitVec.ofNat 64 wk,512⟩] s₂.wr := by
    rw [h₂.wr,h₁.wr,hg.wr]
    refine covers_cons (Covers.head hS.cov) ?_
    intro a n ⟨r,hr,hc⟩
    have er := List.mem_singleton.mp hr
    subst r
    exact Covers.tail hS.cov a n ⟨_,List.mem_singleton_self _,
      Nat.le_trans hc (show 512≤640 by decide)⟩
  refine Proof.Sha3.AArch64.call_ok v
    (by rw [h₂.get .x0 (by decide),e₁,hg.cs sc hS.hsc.1 hS.hsc.2])
    (by rw [e₂,h₁.get sc (by simpa using ns.1),hg.cs sc hS.hsc.1 hS.hsc.2]) ds cw
    fun t rd wr sp cs vc fr eq => ?_
  exact ⟨(kk.mono (by simp)).trans ⟨cs,sp,rd,wr,fr,vc⟩, by rw [eq,mm]⟩

/-- The saved return address lies beyond the permutation workspace. -/
theorem link_frame {sc : Reg} {st wk rate : Nat} {s₀ : State} {m m' : Mem}
    (hS : HSetup sc st wk rate s₀)
    (hf : Frame [STr sc st s₀, ⟨s₀.gpr sc + BitVec.ofNat 64 wk,512⟩] m m') :
    m'.readW (s₀.gpr sc + BitVec.ofNat 64 wk + 600) 64 =
      m.readW (s₀.gpr sc + BitVec.ofNat 64 wk + 600) 64 := by
  apply hf.readW (w:=64) (r:=⟨s₀.gpr sc + BitVec.ofNat 64 wk + 600,8⟩)
    (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  rcases mem2' hr with rfl | rfl
  · exact hS.d.symm.sub_left (Offset.sub_base _ (d:=600) (by decide))
  · exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.MlKem.AArch64.FixedHash
