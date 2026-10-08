import VerifiedGarbage.Proof.P256.EcdhInverse.ChunkMatrix
import VerifiedGarbage.Proof.P256.EcdhInverse.Compose

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Proof.Weierstrass.AArch64 VG.Proof.Divstep
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

def packedClob : List Reg :=
  [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x26,.x28]

def first40 : List Instr := chunk20A++chunk20B

theorem first40_ok (s : State) (d : Int)
    (hd : s.gpr .x1=BitVec.ofInt 64 d) (hz : s.gpr .x27=0)
    (hf : (s.gpr .x2).toNat%2=1) (hbound : |d|+80<2^62) :
    let a := lowMatrix s d
    let b := msteps 20 (MSt.init a.d a.f a.g)
    WP isa (.block first40) s fun t =>
      t.gpr .x1=BitVec.ofInt 64 b.d ∧
      t.gpr .x8=BitVec.ofInt 64 (-a.u) ∧
      t.gpr .x9=BitVec.ofInt 64 (-a.v) ∧
      t.gpr .x10=BitVec.ofInt 64 (-a.q) ∧
      t.gpr .x11=BitVec.ofInt 64 (-a.r) ∧
      t.gpr .x12=BitVec.ofInt 64 (-b.u) ∧
      t.gpr .x13=BitVec.ofInt 64 (-b.v) ∧
      t.gpr .x14=BitVec.ofInt 64 (-b.q) ∧
      t.gpr .x15=BitVec.ofInt 64 (-b.r) ∧
      ((t.gpr .x2).toNat:Int)%2^24=b.f%2^24 ∧
      ((t.gpr .x3).toNat:Int)%2^24=b.g%2^24 ∧
      Keeps packedClob s t := by
  dsimp only
  rw [first40,WP.block_append_iff]
  refine WP.mono (chunk20A_ok s d hd hz hf (by omega))
    fun a ⟨ad,au,av,aq,ar,af,ag,ka⟩ => ?_
  have hodd : (lowMatrix s d).f%2=1 :=
    msteps_f_odd (t:=MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) (by dsimp only [MSt.init]; omega) 20
  have haodd : (a.gpr .x2).toNat%2=1 := by norm_num at af; omega
  have az : a.gpr .x27=0 := by rw [ka.gpr _ (by decide)]; exact hz
  have hb : |(lowMatrix s d).d|+40<2^62 := by
    have h := msteps_d (MSt.init d (s.gpr .x2).toNat (s.gpr .x3).toNat) 20
    change |(lowMatrix s d).d|≤|d|+2*20 at h
    omega
  have hc := second_input_cong (d:=(lowMatrix s d).d) hodd af ag
  obtain ⟨cd,cu,cv,cq,cr,cf,cg⟩ := hc
  refine WP.mono (chunk20B_ok a (lowMatrix s d).d ad az haodd hb)
    fun b ⟨bd,bu,bv,bq,br,bf,bg,kb⟩ => ?_
  dsimp only [MSt.negInput] at cd cu cv cq cr cf cg
  change (lowMatrix a (lowMatrix s d).d).d=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).d at cd
  change (lowMatrix a (lowMatrix s d).d).u=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).u at cu
  change (lowMatrix a (lowMatrix s d).d).v=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).v at cv
  change (lowMatrix a (lowMatrix s d).d).q=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).q at cq
  change (lowMatrix a (lowMatrix s d).d).r=
    (msteps 20 (MSt.init (lowMatrix s d).d (lowMatrix s d).f (lowMatrix s d).g)).r at cr
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    (ka.mono (by decide)).trans (kb.mono (by decide))⟩
  · rw [bd,cd]
  · rw [kb.gpr _ (by decide)]; exact au
  · rw [kb.gpr _ (by decide)]; exact av
  · rw [kb.gpr _ (by decide)]; exact aq
  · rw [kb.gpr _ (by decide)]; exact ar
  · rw [bu,cu]
  · rw [bv,cv]
  · rw [bq,cq]
  · rw [br,cr]
  · exact second_output_cong bf cf
  · exact second_output_cong bg cg

end VG.Proof.P256.EcdhInverse
