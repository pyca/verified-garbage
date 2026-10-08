import VerifiedGarbage.Impl.P256.EcdhInverse
import VerifiedGarbage.Proof.P256.EcdhInverse.First40
import VerifiedGarbage.Proof.P256.EcdhInverse.Chunk19

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

theorem packed_eq : Impl.P256.EcdhInverse.packed=first40++chunk19 := by decide +kernel

theorem negative_pair (a b c d : Int) :
    BitVec.ofInt 64 (-a)*BitVec.ofInt 64 (-b)+BitVec.ofInt 64 (-c)*BitVec.ofInt 64 (-d)=
      BitVec.ofInt 64 (a*b+c*d) := by
  rw [←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_add]
  apply congrArg (BitVec.ofInt 64)
  ring

theorem negative_product (a b c d : Int) :
    -(BitVec.ofInt 64 (-a)*BitVec.ofInt 64 b)-BitVec.ofInt 64 (-c)*BitVec.ofInt 64 d=
      BitVec.ofInt 64 (a*b+c*d) := by
  rw [←BitVec.ofInt_mul,←BitVec.ofInt_mul,←BitVec.ofInt_neg,←ofInt_sub']
  apply congrArg (BitVec.ofInt 64)
  ring

theorem packed_low_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+118<2^62) :
    let m := msteps 59 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)
    WP isa (.block Impl.P256.EcdhInverse.packed) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 m.d ∧
      t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧
      t.gpr .x6=BitVec.ofInt 64 m.q ∧
      t.gpr .x7=BitVec.ofInt 64 m.r ∧ Keeps packedClob s t := by
  let a := lowMatrix s d
  let b := msteps 20 (MSt.init a.d a.f a.g)
  let c := msteps 19 (MSt.init b.d b.f b.g)
  have hfull := matrix59 d (s.gpr .x2).toNat (s.gpr .x3).toNat
  change msteps 59 (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat)=
    ⟨c.d,c.f,c.g,c.u*(b.u*a.u+b.v*a.q)+c.v*(b.q*a.u+b.r*a.q),
      c.u*(b.u*a.v+b.v*a.r)+c.v*(b.q*a.v+b.r*a.r),
      c.q*(b.u*a.u+b.v*a.q)+c.r*(b.q*a.u+b.r*a.q),
      c.q*(b.u*a.v+b.v*a.r)+c.r*(b.q*a.v+b.r*a.r)⟩ at hfull
  dsimp only
  rw [hfull,packed_eq,WP.block_append_iff]
  have haodd : a.f%2=1 := msteps_f_odd
    (t:=MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) (by dsimp only [MSt.init]; omega) 20
  have hbodd : b.f%2=1 := msteps_f_odd (t:=MSt.init a.d a.f a.g) haodd 20
  have hbd : |b.d|+38<2^62 := by
    have ha := msteps_d (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20
    have hb := msteps_d (MSt.init a.d a.f a.g) 20
    change |a.d|≤|d|+2*20 at ha
    change |b.d|≤|a.d|+2*20 at hb
    omega
  refine WP.mono (first40_ok s d hd hz hf (by omega))
    fun t ⟨td,tu,tv,tq,tr,bu,bv,bq,br,tf,tg,kt⟩ => ?_
  have tzero : t.gpr .x27=0 := by rw [kt.gpr _ (by decide)]; exact hz
  have todd : (t.gpr .x2).toNat%2=1 := by
    change ((t.gpr .x2).toNat:Int)%2^24=b.f%2^24 at tf
    norm_num at tf
    omega
  have hc := third_input_cong (d:=b.d) hbodd tf tg
  obtain ⟨cd,cu,cv,cq,cr,_,_⟩ := hc
  change (lowMatrix19 t b.d).d=c.d at cd
  change (lowMatrix19 t b.d).u=c.u at cu
  change (lowMatrix19 t b.d).v=c.v at cv
  change (lowMatrix19 t b.d).q=c.q at cq
  change (lowMatrix19 t b.d).r=c.r at cr
  have ma : matA t=BitVec.ofInt 64 (b.u*a.u+b.v*a.q) := by
    rw [matA,bu,tu,bv,tq]; exact negative_pair _ _ _ _
  have mb : matB t=BitVec.ofInt 64 (b.u*a.v+b.v*a.r) := by
    rw [matB,bu,tv,bv,tr]; exact negative_pair _ _ _ _
  have mc : matC t=BitVec.ofInt 64 (b.q*a.u+b.r*a.q) := by
    rw [matC,bq,tu,br,tq]; exact negative_pair _ _ _ _
  have md : matD t=BitVec.ofInt 64 (b.q*a.v+b.r*a.r) := by
    rw [matD,bq,tv,br,tr]; exact negative_pair _ _ _ _
  refine WP.mono (chunk19_ok t b.d td tzero todd hbd) fun v ⟨vd,vu,vv,vq,vr,kv⟩ => ?_
  refine ⟨?_,?_,?_,?_,?_,kt.trans (kv.mono (by decide))⟩
  · rw [vd,cd]
  · rw [vu,cu,cv,ma,mc]; exact negative_product _ _ _ _
  · rw [vv,cu,cv,mb,md]; exact negative_product _ _ _ _
  · rw [vq,cq,cr,ma,mc]; exact negative_product _ _ _ _
  · rw [vr,cq,cr,mb,md]; exact negative_product _ _ _ _

theorem packed_ok (s : State) (d f g : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d)
    (hfword : s.gpr .x2=BitVec.ofInt 64 f) (hgword : s.gpr .x3=BitVec.ofInt 64 g)
    (hz : s.gpr .x27=0) (hfodd : f%2=1) (hbound : |d|+118<2^62) :
    let m := msteps 59 (MSt.init d f g)
    WP isa (.block Impl.P256.EcdhInverse.packed) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 m.d ∧ t.gpr .x4=BitVec.ofInt 64 m.u ∧
      t.gpr .x5=BitVec.ofInt 64 m.v ∧ t.gpr .x6=BitVec.ofInt 64 m.q ∧
      t.gpr .x7=BitVec.ofInt 64 m.r ∧ Keeps packedClob s t := by
  have hf : ((s.gpr .x2).toNat:Int)%2^64=f%2^64 := by
    rw [hfword,toNat_ofInt64,Int.emod_emod]
  have hg : ((s.gpr .x3).toNat:Int)%2^64=g%2^64 := by
    rw [hgword,toNat_ofInt64,Int.emod_emod]
  have ho : (s.gpr .x2).toNat%2=1 := by norm_num at hf; omega
  have hc : (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat).cong (MSt.init d f g) 64 :=
    ⟨rfl,rfl,rfl,rfl,rfl,hf,hg⟩
  have h := msteps_cong (show ((s.gpr .x2).toNat:Int)%2=1 by omega) hc 59 (by decide)
  obtain ⟨ed,eu,ev,eq,er,_,_⟩ := h
  refine WP.mono (packed_low_ok s d hd hz ho hbound) fun t ⟨td,tu,tv,tq,tr,kt⟩ => ?_
  exact ⟨td.trans (congrArg (BitVec.ofInt 64) ed),tu.trans (congrArg (BitVec.ofInt 64) eu),
    tv.trans (congrArg (BitVec.ofInt 64) ev),tq.trans (congrArg (BitVec.ofInt 64) eq),
    tr.trans (congrArg (BitVec.ofInt 64) er),kt⟩

end VG.Proof.P256.EcdhInverse
