import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFrontCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMidCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombTailCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombFinalCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombPointTail

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

variable {c : Impl.Ecdsa.X86.Cfg}

theorem vFrontWf {s : State} {extra : List Region} (hp : VPre c s extra) : VG.X86.Taint.Wf vFrontτ s := by
  have hsc := hp.sc_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, vFrontτ], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨Nat.le_trans (Cfg.stk_ge c) hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [ptr, BitVec.toNat_setWidth]; omega_using [hsc]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [vFrontτ, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr, ptr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    have := Cfg.stk_ge c
    exact hp.stk_sc.sub_left (Offset.sub_below _ (a := 20) (n := 20) this (by omega))

/-- Equal stack pointers and arguments establish the front's agreement. -/
theorem vFrontAgree {s t : State} {extra₁ extra₂ : List Region} (hp : VPre c s extra₁)
    (hq : VPre c t extra₂) (he : s.gpr .esp = t.gpr .esp) (ha : ∀ j < 4, arg s j = arg t j) :
    VG.X86.Taint.Agree vFrontτ s t := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, vFrontWf hp, vFrontWf hq,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => he,
    fun k h4 hk => ?_⟩
  · simp only [vFrontτ, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact he
  · rw [hp.wr, hq.wr]; simp only [ptr, ha 3 (by decide)]
  · simp only [vFrontτ] at hk
    rw [show VG.X86.Taint.depth vFrontτ.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp.sp_fit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hq.sp_fit; omega) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha ((k - 4) / 4) (by omega))

/-- Scratch writes preserve the four cdecl argument words. -/
theorem vKeep_arg {s₀ s : State} {extra : List Region}
    (hp : VPre c s₀ extra) (h : Keep c s₀ (ptr s₀ 3) s) {j : Nat} (hj : j < 4) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  have h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  refine h.whole.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.args_sc.sub_left (arg_subN h4 hj)
  · exact (below_disjoint_args hp.sp_lo (k := 16) (by omega) (by decide)).symm.sub_left (arg_subN h4 hj)

theorem vArgWf {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : VPre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 4 c.stk) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨by rw [he]; exact hp.sp_lo, ?_⟩
  rotate_right
  · rw [he, hw, hp.wr]
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.stk_sc
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.sp_fit; omega) hp.ret_sc hp.args_sc
  · intro p h; cases h

theorem vKeepArgAgree {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : VPre c s₀ extra₁) (hq : VPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 3) s) (kt : Keep c t₀ (ptr t₀ 3) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi] 4 c.stk) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 3 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (vArgWf _ hp ks.esp ks.wr) (vArgWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [vKeep_arg hp ks hj, vKeep_arg hq kt hj, ha j hj]

theorem vKeepCombWf {s₀ s : State} {extra : List Region} (hp : VPre p256Comb s₀ extra)
    (ks : Keep p256Comb s₀ (ptr s₀ 3) s) : VG.X86.Taint.Wf (combτAt false) s := by
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨?_, ?_, ?_, ?_, ?_⟩ fun _ => ⟨?_, ?_⟩
  rotate_right 2
  · rw [ks.esp]; exact hp.sp_lo
  · rw [ks.esp, ks.wr, hp.wr]
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact hp.stk_sc
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτAt, size], by simp, ?_⟩
    intro r hr
    rw [List.mem_singleton.mp hr]
    simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 0).base
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_zero, addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h

theorem vKeepScratchAgree {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (ks : Keep p256Comb s₀ (ptr s₀ 3) s) (kt : Keep p256Comb t₀ (ptr t₀ 3) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 4, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (scratchArgτ 4 false) s t := by
  refine scratchArgAgree (vKeepArgAgree hp hq ks kt he ha) (vKeepCombWf hp ks) (vKeepCombWf hq kt) ?_
  rw [ks.wr, kt.wr, hp.wr, hq.wr]
  simp only [ptr, ha 3 (by decide)]

end VG.Proof.Ecdsa.Verify.X86
