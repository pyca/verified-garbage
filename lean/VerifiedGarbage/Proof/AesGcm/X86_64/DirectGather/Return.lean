module

public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Post
public import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Gcm.SealGather

/-! Write the computed tag and restore the original gather caller. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather VG.Impl.AesGcm.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)

theorem BodyDone.tagAt {M : CtxMode} {s t : State} (h : Layout M s) (f : BodyDone M s t) :
    TagAt (K s) (W s + 16#64) (W s) (SP s) .rsp 40 (Tg s) t := by
  have sub : Region.Sub ⟨SP s + 40#64, 8⟩ (argR s) := by
    rw [show 40#64 = BitVec.ofNat 64 (8 + 32) by decide, ← add_ofNat_assoc]
    exact Offset.sub_base _ (by decide)
  refine ⟨f.env, ?_, ?_⟩
  · rw [f.env.rsp]
    exact f.frame.readW (r := ⟨SP s + 40#64, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h.w_a.symm.sub_left sub, h.d_a.symm.sub_left sub, Offset.disjoint_below _ (by decide)]) (by decide)
  · rw [f.env.rsp, f.rd, f.wr]
    exact (h.oneCtx M.ge).args 4 (by decide)

theorem return_wp {M : CtxMode} {s t : State} (h : Layout M s) (f : BodyDone M s t) :
    WP isa (.block (tagOut (at_ .rsp 40) ++ restore)) t fun u =>
      gprPreserved s u ∧ Proof.AesGcm.sealGatherPostG s u := by
  have ⟨_, addr, canRead⟩ := f.tagAt h
  obtain ⟨u, run, tag, fr, regs, rd, wr⟩ := tagOut_ok f.env.r15 addr canRead f.env.perm.w
    (by rw [f.wr, h.wr]; exact covers_of_mem (r := tgR s) (by simp))
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨u, run, ?_⟩)
  have env := f.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact regs _ (by decide) (by decide) (by decide)) rd wr
  have saved := f.saved.frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact (h.t_w.sub_right (Lay.wSub (by decide))).symm)
  have ret : u.mem.readW (SP s) 64 = s.mem.readW (SP s) 64 := by
    rw [ret_kept fr (fun r hr => ?_), ret_kept f.frame (fun r hr => ?_)]
    · simp only [changed, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h.r_w, h.r_d, Offset.base_disjoint_below _ (by decide)]
    · simp only [List.mem_singleton] at hr; subst r; exact h.r_t
  have data := bytesAt_frame (p := Dst s) (n := L s) fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r; exact h.d_t) (Nat.le_of_lt (BitVec.isLt _))
  refine WP.mono (exit_ok env.r15 env.rsp (covers_left env.perm.w) saved ret) fun z ⟨abi, mem, _⟩ => ⟨abi, ?_⟩
  change Spec.Gcm.encryptWith (ciph s) (hk s) 16 (iv s) (pt s (Cnt s)) (ad s) =
    (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  rw [Proof.Gcm.encryptWith_eq, mem, data, tag, f.tag, f.cipher]

theorem return_rel {M : CtxMode} {s t : State} (hs : Layout M s) (ht : Layout M t) (pb : Pub s t) :
    RelCT isa (fun u v => BodyDone M s u ∧ BodyDone M t v)
      (.block (tagOut (at_ .rsp 40) ++ restore)) (fun _ _ => True) := by
  apply RelCT.block_append
  refine RelCT.seq (tagOut_rel (Ctx := K s) (St := W s + 16#64) (W := W s) (SP := SP s) (N := 2560) (T := Tg s) (b := .rsp) (d := 40) (by simp) ⟨_, by taint_decide⟩ ?_)
    (rel_taint [.r13, .r14, .r15, .rsp]
      (fun _ _ h => EnvAgree.regs (rs := []) ⟨h.1, h.2, fun _ h => by cases h⟩) restore_check)
  intro u v h
  refine ⟨h.1.tagAt hs, ?_⟩
  simpa only [K, SP, W, Tg, pb.rdi, pb.rsp, pb.a 4 (by decide), pb.a 5 (by decide)] using h.2.tagAt ht

end VG.Proof.AesGcm.X86_64.DirectGather
