module
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Iteration
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.PieceCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.AesGcm.X86_64.DirectGather
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Descriptor

/-! The gather loop follows the public descriptor addresses and lengths for every fragment. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.RegUpd Gather
open VG.Impl.AesGcm.X86_64
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_ite rel_skip rel_regs)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

private theorem load_rel {W P Q D : Addr} {n k pos : Nat} {s t : State}
    (p : DescriptorInput W P Q D n k pos s) (q : DescriptorInput W P Q D n k pos t) :
    RelCT isa (Eq2 s t) (.block loadPiece) TT := by
  have wp {u : State} (h : DescriptorInput W P Q D n k pos u) :
      WP isa (.block [load .r10 rO]) u (LdF .r10 .r15 256 u) := by
    have rd : InRegions (u.rd ++ u.wr) (W + 256#64) 8 := in_left (in_off h.wp (by decide) (by decide))
    rw [← h.work] at rd
    refine WP.of_runBlock ⟨_, by unfold load rO; xrun [rd], ?_⟩
    exact ⟨rfl, fun r e => gpr_setReg_of_ne _ _ e, rfl, rfl, rfl⟩
  apply Gather.rel_ld (l := loadPiece.tail) (LdF .r10 .r15 256)
  · rintro _ _ ⟨rfl,rfl⟩
    exact ⟨wp p,wp q⟩
  · refine rel_taint [.r15] ?_ ⟨_,by taint_decide⟩
    rintro _ _ ⟨rfl,rfl⟩ r hr
    rw [List.mem_singleton.mp hr,p.work,q.work]
  · refine rel_taint [.r10,.r15] (ld_agree (rs:=[.r15]) ?_ ?_) ⟨_,by taint_decide⟩
    · rintro _ _ ⟨rfl,rfl⟩ r hr
      rw [List.mem_singleton.mp hr,p.work,q.work]
    · rintro _ _ ⟨rfl,rfl⟩
      rw [p.work,q.work,p.ptr,q.ptr]

variable {M : CtxMode} {s t x y : State} {pre i : Nat}

private theorem load_wp (h : Layout M s) (a : LoopAt M s pre i x) (hi : i<Cnt s) :
    WP isa (.block loadPiece) x (LoadedAt s pre i x) := by
  have g := geometry h a hi
  have bound := g.total
  have cap : L s < 2^64 := BitVec.isLt _
  exact loadPiece_ok (descriptor_input h a hi) (BitVec.isLt _) g.skipBound (by omega)

private theorem span_work (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl)
    (h : Layout M s) (a : LoopAt M s pre i x) (hi : i<Cnt s) {u : State} (z : LoadedAt s pre i x u) :
    WP isa (runFragment v c) u fun r => r.gpr .r15 = W s :=
  (runFragment_ok v c h a hi z).mono fun _ r => r.env.r15

theorem step_rel (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl)
    (h : Layout M s) (k : Layout M t) (pb : Pub s t) (a : LoopAt M s pre i x) (b : LoopAt M t pre i y) (hi : i<Cnt s) :
    RelCT isa (Eq2 x y) (iteration v c) TT := by
  have hj : i < Cnt t := pb.cnt ▸ hi
  have w := pb.w
  have source := pb.src
  have sl := pb.sl hi
  have sb := pb.sb hi
  have dst := pb.dst
  have pos : consumed t pre i = consumed s pre i := by rw [consumed,consumed,pb.gl (Nat.le_of_lt hi)]
  have inp := descriptor_input k b hj
  simp only [w, dp, source, sb, sl, dst, pos] at inp
  apply rel_seq (load_rel (descriptor_input h a hi) inp) (load_wp h a hi) (load_wp k b hj)
  intro u u' z z'
  refine rel_seq ?_ (span_work v c h a hi z) (span_work v c k b hj z') ?_
  · obtain ⟨p, os, cs⟩ := loaded_inputs h a hi z
    obtain ⟨q, ot, ct⟩ := loaded_inputs k b hj z'
    have zx := z'.zero
    rw [sl] at zx
    have key : K t = K s := pb.rdi
    have sp : SP t = SP s := pb.rsp
    have rounds : R t = R s := congrArg BitVec.toNat pb.rsi
    simp only [qPtr, sz, dPtr, sb, sl, dst, pos, w, key, rounds, sp] at q ot ct
    refine rel_ite (b := decide (sz s pre i = 0)) z.zero zx (fun _ => rel_skip) fun ne => ?_
    exact piece_rel v c (h.oneCtx M.ge).lay p q os ot (Nat.pos_of_ne_zero (by simpa using ne)) cs ct
  · intro r r' hr hr'
    exact Proof.ChaCha20Poly1305.X86_64.Gather.rel_regs [.r15] (fun _ e => List.mem_singleton.mp e ▸ hr.trans (hr'.trans w).symm) ⟨_,by taint_decide⟩

/-- When the descriptor count is positive, each pass decreases it identically in both runs. -/
theorem loop_rel (v : GcmImpl) (c : Proof.Aes.X86_64.Ctr32ToImpl)
    (h : Layout M s) (k : Layout M t) (pb : Pub s t)
    (hi : i < Cnt s) (a : LoopAt M s pre i x) (b : LoopAt M t pre i y) :
    RelCT isa (Eq2 x y) (.loop (iteration v c) .ne) TT := by
  let I := fun n u z => ∃ j, j < Cnt s ∧ n = Cnt s-j ∧ LoopAt M s pre j u ∧ LoopAt M t pre j z
  refine (RelCT.loop (Q := TT) I (fun n => ?_) (Cnt s-i)).mono ?_ (fun _ _ z => z)
  · intro u z tr₁ tr₂ u' z' inv eu ez
    obtain ⟨j, hj, rfl, iu, iz⟩ := inv
    have hj' : j < Cnt t := pb.cnt ▸ hj
    have eq := step_rel v c h k pb iu iz hj
    have rel := eq.wp (F₁ := fun (r : State) => LoopAt M s pre (j+1) r ∧ r.zf=some (decide (Cnt s-(j+1)=0)))
      (F₂ := fun (r : State) => LoopAt M t pre (j+1) r ∧ r.zf=some (decide (Cnt t-(j+1)=0))) (by
        rintro r r' ⟨rfl,rfl⟩
        exact ⟨iteration_ok v c h iu hj,iteration_ok v c k iz hj'⟩)
    obtain ⟨tr,_,⟨iu',zu⟩,⟨iz',zz⟩⟩ := rel _ _ _ _ _ _ ⟨rfl,rfl⟩ eu ez
    rw [pb.cnt] at zz
    refine ⟨tr, by simp only [eval,zu,zz], fun _ => trivial, fun more => ?_⟩
    have positive : Cnt s-(j+1) ≠ 0 := by simp only [eval,zu] at more; simpa using more
    exact ⟨Cnt s-(j+1), by omega, j+1, by omega, rfl, iu', iz'⟩
  · rintro _ _ ⟨rfl,rfl⟩
    exact ⟨i,hi,rfl,a,b⟩

end VG.Proof.AesGcm.X86_64.DirectGather
