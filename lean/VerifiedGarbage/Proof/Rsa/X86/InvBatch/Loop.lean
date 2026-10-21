module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Count
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Order.Ring.Abs
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef

/-! # The fixed public number of inversion batches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.Impl.Rsa.X86.InvBatch VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv
open VG.Proof.Rsa.Divstep (oddInput)

 def LoopAt (w n : Nat) (base : Addr) (p x iv : Nat) (s0 : State) (k : Nat) (s : State) : Prop :=
  StateAt w n base p iv (VG.Proof.Divstep.W32.invRun 30 p iv (oddInput p x) k) s ∧
  w32 s.mem base 100=3*(n+1)-k ∧ Keeps wordClob s0 s ∧ Unch base (countedWrites w) s0.mem s.mem

 theorem loop_ok {s : State} {base : Addr} {size w n p x iv : Nat}
    (hs : Scr s base size) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : StateAt w n base p iv (VG.Proof.Divstep.W32.invRun 30 p iv (oddInput p x) 0) s)
    (counter : w32 s.mem base 100=3*(n+1)) (hi : iv<2^32)
    (odd : p%2=1) (large : 1<p) (hinv : (p*iv+1)%2^32=0)
    (pc : p<2^(32*n)) (xc : x<2^(32*n)) :
    WP isa (.loop (batchCode w n) .ne) s (LoopAt w n base p x iv s (3*(n+1))) := by
  have cap : p+x<2^(32*n+1) := by rw [pow_succ]; omega
  have ox : oddInput p x≤p+x := by unfold oddInput; split_ifs <;> omega
  have start : LoopAt w n base p x iv s 0 s :=
    ⟨h,by simpa only [Nat.sub_zero] using counter,Keeps.refl _ _,Unch.refl _ _ _⟩
  refine WP.loop (M:=isa) (fun remaining u => ∃ k, k+remaining=3*(n+1) ∧ 0<remaining ∧ LoopAt w n base p x iv s k u)
    ?_ (3*(n+1)) s ⟨0,by omega,by omega,start⟩
  intro remaining u ⟨k,total,pos,I,cu,ku,ou⟩
  have hu := hs.of_keeps ku (by decide)
  obtain ⟨bd,fo,fb,gb,a0,a1,b0,b1⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap:=p+x)
    odd large hinv (by omega) ox k
  have hd : |(VG.Proof.Divstep.W32.invRun 30 p iv (oddInput p x) k).d|+64<2^30 := by
    omega
  refine WP.mono (countedBatch_ok hu hn hw he hz I hi (by omega) hinv hd fo fb gb cap
    (by rw [abs_of_nonneg a0]; omega) (by rw [abs_of_nonneg b0]; omega)
    (by omega) (by omega) cu) fun v ⟨Iv,cv,zf,kv,ov⟩ => ?_
  have Iv' : StateAt w n base p iv (VG.Proof.Divstep.W32.invRun 30 p iv (oddInput p x) (k+1)) v := Iv
  have cv' : w32 v.mem base 100=3*(n+1)-(k+1) := by rw [cv]; omega
  have keep : Keeps wordClob s v := ku.trans kv
  have frame : Unch base (countedWrites w) s.mem v.mem := fun y hy => (ov y hy).trans (ou y hy)
  have next : LoopAt w n base p x iv s (k+1) v := ⟨Iv',cv',keep,frame⟩
  by_cases last : k+1=3*(n+1)
  · left
    refine ⟨?_,by simpa only [last] using next⟩
    change v.zf.map (!·)=some false
    rw [zf]
    have zero : 3*(n+1)-k-1=0 := by omega
    simp only [zero,decide_true,Option.map_some,Bool.not_true]
  · right
    refine ⟨?_,remaining-1,by omega,k+1,by omega,by omega,next⟩
    change v.zf.map (!·)=some true
    rw [zf]
    have nz : 3*(n+1)-k-1≠0 := by omega
    simp only [nz,decide_false,Option.map_some,Bool.not_false]

end VG.Proof.Rsa.X86.InvBatch
