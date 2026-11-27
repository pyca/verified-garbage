module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Aligned
public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Counter
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.GenericAlignedCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64
meta import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tail

/-! Only a streaming caller needs the incremented counter after encrypting its final
partial block. The terminal seal tracks that increment as a mathematical value. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tail
open VG VG.AArch64 VG.Spec.Gcm VG.Proof.Gcm
open VG.Impl.AesGcm.AArch64 (mov ptr crArgsG)
open VG.Impl.AesGcm.AArch64.Contiguous.Tail (finalAligned wordTail firstCall)
open DirectGather.Generic (EncryptedWith)
variable {wn R P n j : Nat} {Ctx St W SP D O : Addr} {k l : Reg → Addr} {iv : Block} {s t : State} {m : Mem}

abbrev terminalCounter (n : Nat) : Block → Block := if n%16 = 0 then id else inc32

private theorem counterPost (L : Lay wn Ctx St W) (h : CrMidG wn true Ctx St W SP k R iv P D O n m j s)
    (small : n-j<16) (positive : n-j ≠ 0) (o : Tag.CounterOut R s t) (f : Frame [⟨St+64#64,16⟩] s.mem t.mem)
    (val : blockAt t.mem (St+64) = ciphOf s.mem Ctx R (blockAt s.mem (St+48))) :
    Cr3Using inc32 wn true Ctx St W SP k R iv P D O n m j t := by
  have reg (r : Reg) (a : r ≠ .x13) (b : r ≠ .x14) := o.reg r a b
  have env := h.env.keep (by intro r hr; simp at hr; rcases hr with rfl|rfl|rfl <;> exact reg _ (by decide) (by decide)) o.sp o.rd o.wr
  have ow := OutAt.dataW h.outAt h.data
  have kd := ciph_frame h.frame (ctx_crFrame L ow) h.rounds
  have cf : blockAt t.mem (St+48) = blockAt s.mem (St+48) := by
    apply blockAt_frame f
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint St (.inl (by decide)) (by decide) (by decide)
  have slot (r : Region) (sep : r.Disjoint ⟨St,80⟩) :
      ∀ q ∈ [((⟨St+64#64,16⟩ : Region))], r.Disjoint q := by
    intro q hq; obtain rfl := List.mem_singleton.mp hq
    exact sep.sub_right (Lay.stSub (by decide))
  refine ⟨env,?_,h.le,small,(reg _ (by decide) (by decide)).trans h.x23,(reg _ (by decide) (by decide)).trans h.x24,
    (reg _ (by decide) (by decide)).trans h.x25,data_of_eq h.data o.rd o.wr,?_,?_,?_,?_,h.whole,?_,
    h.outAt.of_eq o.rd o.wr (reg _ (by decide) (by decide))⟩
  · intro r hr; change r ∈ [Reg.x22,.x27,.x28] at hr
    have g := h.kept r hr
    simp at hr; rcases hr with rfl|rfl|rfl <;> exact (reg _ (by decide) (by decide)).trans g
  · intro empty _; exact (positive empty).elim
  · intro _ hc
    exact ⟨s.mem,h.ctr hc,val.trans (by rw [kd]; rfl),congrArg inc32 cf⟩
  · intro hc
    rw [bytesAt_frame f (slot _ ((ow.take h.le).ok.st)) (by have := ow.ok.lt; omega)]
    exact h.done hc
  · rw [bytesAt_frame f (slot _ ((dataOk_of h.data).drop h.le).st) (by have := ow.ok.lt; omega)]
    exact h.rest
  · exact h.frame.trans (f.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact
      ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Offset.sub St (by decide) (by decide)⟩)

theorem finalAligned_ok (L : Lay wn Ctx St W) (v : GcmImpl)
    (a : CrInG wn true Ctx St W SP k R P D O n s) (hP : P%16=0)
    (hc : Ctr s.mem (St+48) (St+64) (ciphOf s.mem Ctx R) iv P) (hv : v.ctr.scratch ≤ wn-512) :
    WP isa (finalAligned v.callees) s (EncryptedWith (terminalCounter n) wn Ctx St W SP k R iv P D O n s.mem) := by
  refine WP.seq ((crArgsG_ok L true (a.mid (icb := iv) hP)).mono fun _ call => WP.seq
    ((first_ok L v call (ciph_frame call.frame (ctx_crFrame L (OutAt.dataW a.outAt a.data)) a.rounds) hv).mono ?_))
  intro u ⟨h,small⟩
  refine WP.ite _ (eval_zero h.x24 (by omega_arith)) (fun e => ?_) (fun e => ?_)
  · have zero := of_decide_eq_true e
    have eqn : 0+16*((n-0)/16) = n := by omega_arith
    have complete : n%16=0 := by omega_arith
    rw [eqn] at h
    exact WP.of_runBlock ⟨_,rfl,⟨h.env,h.kept,h.x23,h.outAt.2.2,
      by rw [h.x24,Nat.sub_self]; rfl,by rw [h.x25]; congr 1; omega_arith,
      by rw [terminalCounter,ite_eq_left complete]; exact h.ctr hc,h.done hc,h.frame⟩⟩
  · have positive := of_decide_eq_false e
    have leftover : n%16≠0 := by omega_arith
    simp only [terminalCounter,ite_eq_right leftover]
    refine WP.seq ((Tag.counterAt_ok h.env h.rounds h.x22).mono ?_)
    intro t ⟨co,fr,ct⟩
    exact DirectGather.Generic.directTailWith_ok (fun a b c d e f g h => words_ok a b c d e f g h)
      (counterPost L h small positive co fr ct) hc positive

theorem finalAligned_rel (L : Lay wn Ctx St W) (v : GcmImpl)
    (a : CrInG wn true Ctx St W SP k R P D O n s) (b : CrInG wn true Ctx St W SP l R P D O n t)
    (hP : P%16=0) (hv : v.ctr.scratch ≤ wn-512) : RelCT isa (Eq2 s t) (finalAligned v.callees) TT := by
  have hc {σ : State} {k' : Reg → Addr} (h : CrInG wn true Ctx St W SP k' R P D O n σ)
      {m' : Mem} (f : Frame (crFrame wn St W O n) σ.mem m') :=
    ciph_frame f (ctx_crFrame L (OutAt.dataW h.outAt h.data)) h.rounds
  refine rel_seq (rel_taint [.x19,.x20,.x21,.x22,.x23,.x24] (a.env.sp.trans b.env.sp.symm)
      (by agree_tac [a.env.x19,b.env.x19,a.env.x20,b.env.x20,a.env.x21,b.env.x21,
        a.x22,b.x22,a.x23,b.x23,a.x24,b.x24]) ⟨_,by taint_decide⟩)
    (crArgsG_ok L true (a.mid (icb := 0) hP)) (crArgsG_ok L true (b.mid (icb := 0) hP)) ?_
  intro _ _ x y
  refine rel_seq (first_rel v x.call y.call hv (x.env.sp.trans y.env.sp.symm))
    (first_ok L v x (hc a x.frame) hv) (first_ok L v y (hc b y.frame) hv) ?_
  intro _ _ ⟨g,_⟩ ⟨h,_⟩
  exact rel_taint [.x20,.x21,.x22,.x23,.x24,.x26] (g.env.sp.trans h.env.sp.symm)
    (by agree_tac [g.env.x20,h.env.x20,g.env.x21,h.env.x21,g.x22,h.x22,g.x23,h.x23,
      g.x24,h.x24,g.outAt.2.2,h.outAt.2.2]) ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Tail
