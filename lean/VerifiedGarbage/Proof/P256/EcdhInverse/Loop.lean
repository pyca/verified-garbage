import VerifiedGarbage.Proof.P256.EcdhInverse.Batch
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvMain

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

abbrev cfg := p256.invP

def bodyMemory : List (Nat × Nat) := invW cfg++[(7104,576)]

theorem mod_keep {base : Addr} {m : Nat} {s t : State}
    (_hs : Scr s base 8192) (hM : ModOkA cfg.M 8192 m s.mem base)
    (hU : Unch base batchMemory s.mem t.mem) : ModOkA cfg.M 8192 m t.mem base := by
  refine ⟨hM.n0,hM.n10,hM.mo,hM.tmp,hM.sep,?_,hM.inv,hM.red,hM.call⟩
  rw [hU.wordsVal (by decide) (by decide)]
  exact hM.val

theorem packed_loop_ok {base : Addr} {m : Nat}
    (hL : InvLay cfg 8192) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA cfg.M 8192 m s.mem base) {X : Nat} (hX : X<m)
    (hm2 : m%2=1) (hm1 : 1<m)
    (hI : IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X 0) s)
    (h19 : s.gpr .x19=BitVec.ofNat 64 cfg.B) (hz : s.gpr .x27=0) :
    WP isa (.loop Impl.P256.EcdhInverse.batch (.nonzero .x .x19)) s fun t =>
      IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X cfg.B) t ∧
      KeepRegs batchRegs s t ∧ Unch base batchMemory s.mem t.mem := by
  have hmi : ((m:Int)*(cfg.M.minv.toNat:Int)+1)%2^64=0 := by exact_mod_cast hM.inv
  refine countLoop_ok (n:=cfg.B) (by decide)
    (Inv:=fun j t => IInv cfg base (Divstep.invRun 59 m cfg.M.minv.toNat X (cfg.B-j)) t ∧
      t.gpr .x19=BitVec.ofNat 64 j ∧ Scr t base 8192 ∧ ModOkA cfg.M 8192 m t.mem base ∧
      KeepRegs batchRegs s t ∧ Unch base batchMemory s.mem t.mem ∧ t.gpr .x27=0)
    (fun j t hj1 hjB ⟨it,xt,st,mt,kt,ut,zt⟩ => ?_)
    (fun t ⟨it,_,_,_,kt,ut,_⟩ => ⟨by simpa only [Nat.sub_zero] using it,kt,ut⟩)
    (by decide) ⟨by rw [Nat.sub_self]; exact hI,h19,hs,hM,
      ⟨fun _ _ => rfl,rfl,rfl,rfl⟩,Unch.refl _ _ _,hz⟩
  obtain ⟨bd,bf1,bf,bg,ba0,ba1,bb0,bb1⟩ := Divstep.invRun_bounds (N:=59) (by decide)
    (p:=m) (m:=cfg.M.minv.toNat) (x:=X) (by exact_mod_cast hm2)
    (by exact_mod_cast hm1) hmi (by omega) (by exact_mod_cast hX) (cfg.B-j)
  refine WP.mono (batch_ok hL st mt it (by
    have hh : ((59*(cfg.B-j):Nat):Int)≤590 := by
      have : cfg.B=10 := by decide
      omega
    omega) bf1 bf bg (by rw [abs_of_nonneg ba0]; exact ba1.le)
    (by rw [abs_of_nonneg bb0]; exact bb1.le) zt hj1 (by omega_using [hjB,show cfg.B=10 from rfl]) xt)
    fun u ⟨iu,xu,ku,uu,zu⟩ => ⟨⟨?_,xu,st.of_keepRegs ku (by decide),mod_keep st mt uu,
      kt.trans ku,fun x hx => (uu x hx).trans (ut x hx),zu⟩,xu⟩
  rw [show cfg.B-(j-1)=cfg.B-j+1 by omega]
  exact iu

end VG.Proof.P256.EcdhInverse
