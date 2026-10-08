import VerifiedGarbage.Proof.Weierstrass.AArch64.InvEarlyFinish

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The fixed batch count reaches the same finish contract, including input zero. -/
theorem finish_power_ok {P : InvCfg} {base : Addr} {size m X : Nat} [NeZero m]
    (hpr : m.Prime) (hT : InvToM m) (hL : InvLay P size)
    (hm2 : 2<m) (hR : UnitMod m (2^(64*P.M.n))) {s : State}
    (hs : Scr s base size) (hM : ModOkA P.M size m s.mem base)
    (hX : X<m) (hI : IInv P base (Divstep.invRun 59 m P.M.minv.toNat X P.B) s)
    (hC : InvOk P m) :
    WP isa (.block P.finish) s fun t =>
      KeepRegs (powClob P.M.n) s t ∧ Unch base (invW P) s.mem t.mem ∧
      wordsVal t.mem base P.acc P.M.n<m ∧
      toM m (2^(64*P.M.n)) (wordsVal t.mem base P.acc P.M.n)=
        toM m (2^(64*P.M.n)) X ^ (m-2) := by
  have hodd : m%2=1 := by
    rcases Nat.even_or_odd m with ⟨k,hk⟩|⟨k,hk⟩
    · have := hpr.eq_one_or_self_of_dvd 2 ⟨k,by omega⟩; omega
    · omega
  have hmP := hM.val ▸ wordsVal_lt s.mem base P.M.mo P.M.n
  have hfn : (m:Int)<2^(64*P.M.n) := by exact_mod_cast hmP
  have done := Divstep.divsteps_words (by exact_mod_cast hodd)
    (show (0:Int)≤X by omega) (show (X:Int)≤m by exact_mod_cast hX.le) hfn hC.bound
  have hd := (Divstep.invRun_dfg (N:=59) (p:=m) (m:=P.M.minv.toNat) (x:=X)
    (by exact_mod_cast hodd) P.B).1
  have hz : (Divstep.invRun 59 m P.M.minv.toNat X P.B).g=0 := by
    have hg := congrArg (fun x : Int×Int×Int => x.2.2) hd
    exact hg.trans done.1
  exact finish_early_ok hpr hT hL hm2 hR hs hM hX hI hz hC.C hC.Cpos hC.Cn

end VG.Proof.P256.EcdhInverse
