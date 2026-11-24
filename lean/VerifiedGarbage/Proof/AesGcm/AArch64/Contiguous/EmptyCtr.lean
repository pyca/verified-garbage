module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tail
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
public import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tail
open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Tail (firstCall)
open VG.Spec.Gcm (Block)

theorem first_ok {wn R P n j : Nat} {Ctx St W SP D O : Addr} {k : Reg → Addr}
    {iv : Block} {m : Mem} {s : State} (L : Lay wn Ctx St W) (v : GcmImpl)
    (a : Cr1G wn true Ctx St W SP k R iv P D O n m j s)
    (cipher : ciphOf s.mem Ctx R = ciphOf m Ctx R) (scratch : v.ctr.scratch ≤ wn-512) :
    WP isa (firstCall v.callees) s fun t =>
      CrMidG wn true Ctx St W SP k R iv P D O n m (j+16*((n-j)/16)) t ∧ n-(j+16*((n-j)/16))<16 := by
  have call : CtrToCall s Ctx (St+48) (D+BitVec.ofNat 64 j) (O+BitVec.ofNat 64 j)
      (W+512) R ((n-j)/16) (wn-512) := a.call
  refine WP.ite (decide ((n-j)/16=0)) (eval_zero call.x4 call.n_lt) (fun e => ?_)
    (fun _ => ctrCallG1_ok L v a cipher scratch)
  have eq := of_decide_eq_true e
  have le := a.le
  have x23 := a.x23
  have x24 := a.x24
  have out := a.outAt
  simp only [eq,Nat.mul_zero,Nat.add_zero] at x23 x24 out ⊢
  exact WP.block_nil ⟨⟨a.env,a.kept,a.x22,a.rounds,le,x23,x24,a.x25,a.data,
    a.ctr,a.done,a.rest,a.whole,a.frame,out⟩,by omega⟩

theorem first_rel {a b : State} (v : GcmImpl) {Ctx St D O W : Addr} {R n scratch : Nat}
    (x : CtrToCall a Ctx St D O W R n scratch) (y : CtrToCall b Ctx St D O W R n scratch)
    (hv : v.ctr.scratch ≤ scratch) (sp : a.sp = b.sp) : RelCT isa (Eq2 a b) (firstCall v.callees) TT := by
  refine rel_ite (eval_zero x.x4 x.n_lt) (eval_zero y.x4 y.n_lt) (fun _ => ?_) (fun _ => ?_)
  · exact rel_taint [] sp (by agree_tac []) ⟨.block [] 256,by decide⟩
  · exact ctrTo_relLe v.ctr hv (fun _ _ ⟨rfl,rfl⟩ => ⟨_,_,_,_,_,_,_,x,y,sp⟩)

end VG.Proof.AesGcm.AArch64.Contiguous.Tail
