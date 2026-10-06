import VerifiedGarbage.Proof.EcKey.X86.CombMain

/-! # Constant-time public-key stages around the comb -/
namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86
open VG.Impl.EcKey.X86 (Args.publicKey)

def pkPrepCode : Prog isa := p256Comb.prepareWith Args.publicKey
def pkTailCode : Prog isa := .seq (Impl.Weierstrass.X86.pow p256Comb.powP p256Comb.wk)
  (Impl.EcKey.X86.Cfg.middle p256Comb)
materialize_code pkPrepCode
materialize_code pkTailCode

theorem pkPrep_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp] 3)) pkPrepCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

theorem pkTail_rel : RelCT isa (VG.X86.Taint.Agree (argτ [.esp, .edi] 3)) pkTailCode (fun _ _ => True) :=
  RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)

/-- Writes within scratch leave all cdecl argument words unchanged. -/
theorem pkKeep_arg {c : Cfg} {s₀ s : State} {extra : List Region}
    (hp : PkPre c s₀ extra) (h : Keep c s₀ (ptr s₀ 2) s) {j : Nat} (hj : j < 3) :
    arg s j = arg s₀ j := by
  have he : argAddr s j = argAddr s₀ j := by simp only [argAddr, h.esp]
  change s.mem.readW (argAddr s j) 32 = _
  rw [he]
  apply arg_keep (h.whole.outside (fun w hw => by
    rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega) hj)

/-- The public argument area is disjoint from every writable buffer. -/
theorem pkArgWf {c : Cfg} {s₀ s : State} {extra : List Region} (rs : List Reg)
    (hp : PkPre c s₀ extra) (he : s.gpr .esp = s₀.gpr .esp) (hw : s.wr = s₀.wr) :
    VG.X86.Taint.Wf (argτ rs 3) s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h rfl
  · intro p h; cases h
  · intro p h; cases h
  · intro _
    rw [he, hw, hp.wr]
    refine ⟨hp.sp_fit, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by have := hp.sp_fit; omega) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by have := hp.sp_fit; omega) hp.ret_sc hp.args_sc
  · intro p h; cases h

/-- The functional stage invariant restores public cdecl arguments. -/
theorem pkKeepArgAgree {c : Cfg} {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : PkPre c s₀ extra₁) (hq : PkPre c t₀ extra₂)
    (ks : Keep c s₀ (ptr s₀ 2) s) (kt : Keep c t₀ (ptr t₀ 2) t)
    (he : s₀.gpr .esp = t₀.gpr .esp) (ha : ∀ j < 3, arg s₀ j = arg t₀ j) :
    VG.X86.Taint.Agree (argτ [.esp, .edi] 3) s t := by
  have esp : s.gpr .esp = t.gpr .esp := ks.esp.trans (he.trans kt.esp.symm)
  have edi : s.gpr .edi = t.gpr .edi := widen32_inj (ks.scr.edi.trans
    ((congrArg (BitVec.setWidth 64) (ha 2 (by decide))).trans kt.scr.edi.symm))
  refine argAgree (pkArgWf _ hp ks.esp ks.wr) (pkArgWf _ hq kt.esp kt.wr) ?_ esp ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact esp
    · exact edi
  · intro j hj
    rw [pkKeep_arg hp ks hj, pkKeep_arg hq kt hj, ha j hj]

/-- The static-table scan's scratch region is the second writable argument. -/
theorem pkKeepCombWf {s₀ s : State} {extra : List Region} (hp : PkPre p256Comb s₀ extra)
    (ks : Keep p256Comb s₀ (ptr s₀ 2) s) : VG.X86.Taint.Wf combτ s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [ks.wr, hp.wr]
    refine ⟨by simp [combτ, size], ?_, ?_⟩
    · simpa using hp.out_sc
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.out_fit]
      · simp only [ptr, BitVec.toNat_setWidth]; omega_using [hp.sc_fit]
  · intro p h
    rw [List.mem_singleton.mp h]
    simp only [VG.X86.Taint.region, ks.wr, hp.wr, List.getD_cons_succ, List.getD_cons_zero,
      addr, BitVec.add_zero]
    exact ks.scr.edi
  · intro p h; cases h
  · intro h; cases h
  · intro p h; cases h


end VG.Proof.EcKey.X86
