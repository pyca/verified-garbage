import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombMain
import VerifiedGarbage.Proof.Ecdsa.X86.CombStagesCT

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.Ecdsa.Verify.X86

variable {c : Impl.Ecdsa.X86.Cfg}

def vFrontCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combFront p256Comb
def vMidCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.combMid p256Comb
def vBitsCode : Prog isa := Impl.Weierstrass.X86.bits (p256Comb.sl U) (bitsAt p256Comb.n 0) (8 * p256Comb.n)
def vPointTailCode : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86.Cfg.save p256Comb)) <|
  .seq (Impl.Ecdsa.Verify.X86.Cfg.windowMulQ p256Comb)
    (Impl.Ecdsa.Verify.X86.Cfg.sum p256Comb)
def vFinalCode : Prog isa := Impl.Ecdsa.Verify.X86.Cfg.tail p256Comb
materialize_code vFrontCode
materialize_code vMidCode
materialize_code vBitsCode
materialize_code vPointTailCode
materialize_code vFinalCode

theorem vFront_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp] 4)) vFrontCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
theorem vMid_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4)) vMidCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
theorem vBits_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4)) vBitsCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
theorem vPointTail_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4)) vPointTailCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
theorem vFinal_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 4)) vFinalCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

theorem Front.keep {s₀ s : State} {base : Addr} (h : Front c s₀ base s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.unch⟩
theorem Mid.keep {s₀ s : State} {base : Addr} (h : Mid c s₀ base s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.unch⟩
theorem Pts.keep {s₀ s : State} {base : Addr} {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (h : Pts c s₀ base Q₁ Q₂ s) : Keep c s₀ base s :=
  ⟨h.scr, h.esp, h.rd, h.wr, h.fixed, h.unch⟩

/-- Scratch writes preserve the four cdecl argument words. -/
theorem vKeep_arg {s₀ s : State} {extra : List Region}
    (hp : VPre c s₀ extra) (h : Keep c s₀ (ptr s₀ 3) s) {j : Nat} (hj : j < 4) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  apply arg_keep (h.whole.outside (fun w hw => by
    rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  exact hp.args_sc.sub_left (arg_subN (k := 4) (by have := hp.sp_fit; omega) hj)

theorem vArgWf {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : VPre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 4) s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
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
    VG.X86.Taint.Agree (argτ [.esp, .edi] 4) s t := by
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
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
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

end VG.Proof.Ecdsa.Verify.X86
