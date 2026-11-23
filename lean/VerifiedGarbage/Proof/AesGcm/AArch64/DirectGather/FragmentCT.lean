module

public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentLoop
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.FragmentLoop

/-! Equal descriptor metadata determines the entire address and branch trace
of both ciphertext outputs, independently of plaintext and key bytes. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.Impl.AesGcm.AArch64.DirectGather
open VG.Proof.AesGcm.AArch64 (rel_taint rel_seq rel_ite TT Eq2)

/-- Once descriptor loads have finished, all cursor and count registers
are public. Both loops and the overlapping final-word path preserve this. -/
theorem shortPiece_rel {b s t} (p : PiecePre b s) (q : PiecePre b t)
    (sp : s.sp = t.sp) (desc : s.gpr .x6 = t.gpr .x6) :
    RelCT isa (Eq2 s t) shortPiece TT := by
  change RelCT isa _ (.seq (.block decode) (.seq
      (.ite (.zero .x .x13) (.block []) (.loop (.block blockStep) (.nonzero .x .x13)))
      (.ite (.zero .x .x12) (.block []) tail))) TT
  refine rel_seq (rel_taint [.x6] sp (by agree_tac [desc]) ⟨_,by taint_decide⟩)
    (decode_ok p) (decode_ok q) fun a b' ha hb => ?_
  exact rel_taint [.x0,.x1,.x2,.x3,.x12,.x13] (ha.sp.trans (sp.trans hb.sp.symm))
    (by agree_tac [ha.ptrs.src,hb.ptrs.src,ha.ptrs.key,hb.ptrs.key,ha.ptrs.dst,hb.ptrs.dst,
      ha.ptrs.auth,hb.ptrs.auth,ha.whole,hb.whole,ha.rest,hb.rest]) ⟨_,by taint_decide⟩

/-- The public addresses, lengths and descriptor bytes on entry. -/
structure LoopPub (s t : State) : Prop where
  sp : s.sp = t.sp
  desc : ds s = ds t
  cnt : num s = num t
  key : s.gpr .x1 = t.gpr .x1
  dst : s.gpr .x2 = t.gpr .x2
  auth : s.gpr .x3 = t.gpr .x3
  bytes : ∀ j < 16*num s, s.mem (off (ds s) j) = t.mem (off (ds s) j)

theorem LoopPub.buf {s t} (pub : LoopPub s t) {i : Nat} (hi : i < num s) : curBuf s i = curBuf t i := by
  have hd : ∀ j < num s * 16, s.mem (ds s + BitVec.ofNat 64 j) = t.mem (ds s + BitVec.ofNat 64 j) :=
    fun j hj => pub.bytes j (by simpa [Nat.mul_comm] using hj)
  simp only [curBuf,gl,← pub.desc,← pub.key,← pub.dst,← pub.auth,
    Gather.gl_agree hd (Nat.le_of_lt hi),Gather.sb_agree hd hi,Gather.sl_agree hd hi]

theorem body_rel {s t i} (p : LoopPre s) (q : LoopPre t) (pub : LoopPub s t) (hi : i < num s) :
    RelCT isa (fun a b => AtDesc s i a ∧ AtDesc t i b) (.seq shortPiece (.block countDown))
      (fun a b => AtDesc s (i+1) a ∧ AtDesc t (i+1) b) := by
  have ht : i < num t := pub.cnt ▸ hi
  have base : RelCT isa (fun a b => AtDesc s i a ∧ AtDesc t i b) (.seq shortPiece (.block countDown)) TT := by
    intro a b τ υ a' b' ⟨ha,hb⟩ ex ey
    have pa := piecePre p hi ha
    have pb := piecePre q ht hb
    rw [← pub.buf hi] at pb
    exact rel_seq (shortPiece_rel pa pb (ha.sp.trans (pub.sp.trans hb.sp.symm))
      (by rw [ha.desc,hb.desc,pub.desc])) (shortPiece_ok pa) (shortPiece_ok pb)
      (fun _ _ wa wb => rel_taint [] (wa.sp.trans (ha.sp.trans (pub.sp.trans (hb.sp.symm.trans wb.sp.symm))))
        (by agree_tac []) ⟨.block [] 256,by decide⟩) _ _ _ _ _ _ ⟨rfl,rfl⟩ ex ey
  exact (base.wp fun _ _ ⟨ha,hb⟩ => ⟨body_ok p hi ha,body_ok q ht hb⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem shortLoop_rel {s t} (p : LoopPre s) (q : LoopPre t) (pub : LoopPub s t) :
    RelCT isa (Eq2 s t)
      (.ite (.zero .x .x7) (.block []) (.loop (.seq shortPiece (.block countDown)) (.nonzero .x .x7))) TT := by
  have lt : num s < 2^64 := (s.gpr .x7).isLt
  have count₁ : s.gpr .x7 = BitVec.ofNat 64 (num s) := by simp [num]
  have count₂ : t.gpr .x7 = BitVec.ofNat 64 (num s) := by simp [pub.cnt,num]
  refine rel_ite (eval_zero count₁ lt) (eval_zero count₂ lt) (fun _ => rel_taint [] pub.sp (by agree_tac [])
    ⟨.block [] 256,by decide⟩) (fun nz => ?_)
  have pos := of_decide_eq_false nz
  refine (RelCT.loop (Q := TT) (fun k a b => ∃ i, k = num s-i ∧ i < num s ∧ AtDesc s i a ∧ AtDesc t i b)
    (fun k => ?_) (num s)).mono (fun a b ⟨ha,hb⟩ => by subst a b; exact ⟨0,by simp,by omega,AtDesc.init s,AtDesc.init t⟩)
    fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hx : k = num s-i ∧ i < num s
  · obtain ⟨rfl,hi⟩ := hx
    refine (body_rel p q pub hi).mono (fun _ _ h => h.2.2) ?_
    rintro a b ⟨ha,hb⟩
    have e₁ := eval_nonzero ha.count (by omega)
    have cb : b.gpr .x7 = BitVec.ofNat 64 (num s - (i+1)) := pub.cnt ▸ hb.count
    have e₂ := eval_nonzero cb (by omega)
    refine ⟨by rw [e₁,e₂], fun _ => trivial, fun h => ?_⟩
    rw [e₁] at h
    have more : i+1 < num s := by simp at h; omega
    exact ⟨num s-(i+1),by omega,i+1,rfl,more,ha,hb⟩
  · exact RelCT.of_false fun _ _ h => hx ⟨h.1,h.2.1⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment
