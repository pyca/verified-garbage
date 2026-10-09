import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallPre

namespace VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots StaticTable signRootConsts)
open Message.Optimized (rootRegions roots_reborrow)
variable {p : Params} {s : State}
/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) (h : VPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx (vlay p s) g vv m₀ t) (hr : StaticRoots 16 t) :
    WP isa (callA n c verifyArgs) t fun s' => Fin (vlay p s) g vv s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (s.gpr .x0) p.pkLen) (bytesAt t.mem (vlay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) p.sigLen);
        ((s'.gpr .x0).setWidth 32 = 1 ∧ ∃ b, w b = some true) ∨
          ((s'.gpr .x0).setWidth 32 = 0 ∧ w minBounds ≠ some true)) := by
  have hL := vlay_ok hp h h8
  refine WP.seq (WP.mono_syms (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ hsy => ?_)
  have hc1 : Ctx (vlay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hd := hV.dle.1
  have hpre := verifyK_pre hp h h8 hc ⟨hA,o⟩ hsy hr
  have hr1 : StaticRoots 16 t1 := by
    have pass {nm ws} (ht : StaticTable 16 nm ws t) : StaticTable 16 nm ws t1 := by
      apply ht.frame (W := []) ?_ (by simp) o.rd o.wr o.sp hsy
      rw [o.mem]; exact Frame.refl _ _
    exact ⟨pass hr.forward,pass hr.inverse⟩
  refine WP.callFV hV.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · change Covers ((verifyRd p s++rootRegions t1)++verifyWr p s) (t1.rd++t1.wr)
    rw [List.append_assoc]
    apply Covers.append_left
    · rw [hc1.rd,hc1.wr]
      refine covers_of_within fun r hr=>?_
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact ⟨_,by simp [vlay,h.rd],within_self _⟩
      · exact ⟨_,by simp [vlay,h.wr],mu_withinV p s⟩
      · exact ⟨_,by simp [vlay,h.rd],within_self _⟩
    · apply Covers.append_left
      · exact Covers.pair hr1.forward.readable hr1.inverse.readable
      · rw [hc1.wr]
        refine covers_of_within fun r hr=>?_
        simp only [List.mem_singleton] at hr
        subst r
        exact ⟨⟨s.gpr .x6,mScrLen p⟩,by simp [vlay,h.wr],
          within_base _ (by rw [mScr_eq]; simp only [sScr,oE]; omega)⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨s.gpr .x6, mScrLen p⟩, by simp [vlay, h.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((vlay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((vlay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sv_sScrV hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, Abi.withConsts, Sign.signRootConsts_eq, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, o.mem] at hpost
  exact hpost

end VG.Proof.MlDsa.AArch64.Message.OptimizedVerify
