module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Twice
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Tactic.Ring

/-! # The fixed coefficient-scale correction loop -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch VG.Impl.Weierstrass.X86
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv

 def doubled (p a k : Nat) := (a*2^k)%p
 theorem doubled_zero {p a : Nat} (ha : a<p) : doubled p a 0=a := by
  simp only [doubled,pow_zero,Nat.mul_one,Nat.mod_eq_of_lt ha]
 theorem doubled_next (p a k : Nat) : (2*doubled p a k)%p=doubled p a (k+1) := by
  rw [doubled,doubled,Nat.mul_mod_mod,pow_succ]
  congr 1
  ring

 def DoubleAt (w n p a K : Nat) (base : Addr) (s0 : State) (k : Nat) (s : State) : Prop :=
 val32 s.mem base (offset w 6) n=doubled p a k ∧ w32 s.mem base (offset w 6+4*n)=0 ∧
 val32 s.mem base (offset w 2) n=p ∧ s.gpr .esi=BitVec.ofNat 32 (K-k) ∧
 Keeps wordClob s0 s ∧ Unch base (twiceWrites w n) s0.mem s.mem
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem doubleLoop_ok {s : State} {base : Addr} {size w n p a K : Nat}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 2) n=p) (ha : val32 s.mem base (offset w 6) n=a)
    (top : w32 s.mem base (offset w 6+4*n)=0) (hp : 0<p) (small : a<p)
    (kp : 0<K) (kl : K<2^32) (counter : s.gpr .esi=BitVec.ofNat 32 K) :
    WP isa (.loop (.block (twice w n ++ [decCounter,testCounter])) .ne) s
      (DoubleAt w n p a K base s K) := by
  have nw := hs.nowrap
  have start : DoubleAt w n p a K base s 0 s :=
    ⟨by rw [doubled_zero small,ha],top,hm,by simpa only [Nat.sub_zero] using counter,Keeps.refl _ _,Unch.refl _ _ _⟩
  refine WP.loop (M:=isa) (fun remaining u => ∃ k,k+remaining=K ∧ 0<remaining ∧ DoubleAt w n p a K base s k u)
    ?_ K s ⟨0,by omega,kp,start⟩
  intro remaining u ⟨k,total,pos,va,ta,ma,cu,ku,ou⟩
  have hu := hs.of_keeps ku (by decide)
  refine WP.block_append (WP.mono (twice_ok hu hn hw he hz ma va ta hp (Nat.mod_lt _ hp)) fun v ⟨vv,tv,kv,ov⟩ => ?_)
  have cv : v.gpr .esi=BitVec.ofNat 32 (K-k) := (kv.1 .esi (by decide)).trans cu
  refine wp_decCounter (by omega) cv fun v1 cv1 kv1 mv1 => ?_
  refine wp_testCounter (by omega) cv1 fun z F zf => WP.block_nil ?_
  have kz : Keeps wordClob u z := ((kv.mono (by decide)).trans (kv1.mono (by decide))).trans (F.keeps _)
  have mz : z.mem=v.mem := F.mem.trans mv1
  have vz : val32 z.mem base (offset w 6) n=doubled p a (k+1) := by rw [mz,vv,doubled_next]
  have tz : w32 z.mem base (offset w 6+4*n)=0 := by rw [mz,tv]
  have modz : val32 z.mem base (offset w 2) n=p := by
    rw [mz,Outs.val32 ov (by
      intro r hr; simp only [twiceWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart) (by apart),ma]
  have cz : z.gpr .esi=BitVec.ofNat 32 (K-(k+1)) := by rw [F.gpr,cv1]; congr 1
  have oz : Unch base (twiceWrites w n) s.mem z.mem := by
    rw [mz]
    exact fun y hy => (ov y hy).trans (ou y hy)
  have next : DoubleAt w n p a K base s (k+1) z := ⟨vz,tz,modz,cz,ku.trans kz,oz⟩
  by_cases last : k+1=K
  · left
    refine ⟨?_,by simpa only [last] using next⟩
    change z.zf.map (!·)=some false
    rw [zf]
    have zero : K-k-1=0 := by omega
    simp only [zero,decide_true,Option.map_some,Bool.not_true]
  · right
    refine ⟨?_,remaining-1,by omega,k+1,by omega,by omega,next⟩
    change z.zf.map (!·)=some true
    rw [zf]
    have nz : K-k-1≠0 := by omega
    simp only [nz,decide_false,Option.map_some,Bool.not_false]

end VG.Proof.Rsa.X86.InvBatch
