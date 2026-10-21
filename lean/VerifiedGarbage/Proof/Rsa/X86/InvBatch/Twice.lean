module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Csub
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.SelfAdd
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory

/-! # Doubling a coefficient modulo the active modulus -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def twiceWrites (w n : Nat) : List (Nat × Nat) := [(offset w 6,4*(n+1)),(offset w 12,4*n)]
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

 theorem twice_ok {s : State} {base : Addr} {size w n p a : Nat}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 2) n=p) (ha : val32 s.mem base (offset w 6) n=a)
    (top : w32 s.mem base (offset w 6+4*n)=0) (hp : 0<p) (small : a<p) :
    WP isa (.block (twice w n)) s fun z =>
      val32 z.mem base (offset w 6) n=(2*a)%p ∧ w32 z.mem base (offset w 6+4*n)=0 ∧
      Keeps [.eax,.ebx,.edx] s z ∧ Unch base (twiceWrites w n) s.mem z.mem := by
  have nw := hs.nowrap
  have pn : p<2^(32*n) := hm ▸ val32_lt _ _ _ _
  have wn : words (config w n)=n := by simp only [config,words]; omega
  have full : val32 s.mem base (offset w 6) (n+1)=a := by
    rw [val32_succ,ha,top,Nat.mul_zero,Nat.add_zero]
  simp only [twice]
  rw [addInPlace_eq]
  refine WP.block_append (WP.block_append (WP.mono
    (chainAdd_forward_ok hs n (acc:=offset w 6) (b:=offset w 6) (by apart) (by apart) (by omega))
    fun s1 ⟨O1,⟨carry,_,V1⟩,K1⟩ => ?_))
  rw [full] at V1
  have totalBound : 2*a<2^(32*(n+1)) := by rw [pow32_succ]; omega
  have value1 : val32 s1.mem base (offset w 6) (n+1)=2*a := by
    cases carry <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at V1 <;> omega
  have hs1 := hs.of_keeps K1 (by decide)
  have mod1 : val32 s1.mem base (config w n).mo n=p := by
    change val32 s1.mem base (offset w 2) n=p
    rw [O1.val32 (by apart) (by apart),hm]
  refine WP.mono (csub_forward_ok hs1 wn (by omega) (src:=offset w 6) (o:=offset w 6)
    (by apart) (by apart) (by dsimp only [config]; apart) (by dsimp only [config]; apart)
    (by dsimp only [config]; apart) (by dsimp only [config]; apart) (by apart) (by dsimp only [config]; apart)
    mod1 (by rw [value1]; omega)) fun s2 ⟨O2,V2,K2⟩ => ?_
  have hs2 := hs1.of_keeps K2 (by decide)
  refine WP.mono (zeros_ok hs2 (acc:=offset w 6+4*n) (k:=1) (by apart)) fun z ⟨O3,V3,K3⟩ => ?_
  refine ⟨?_,?_,((K1.mono (by decide)).trans K2).trans (K3.mono (by decide)),?_⟩
  · rw [O3.val32 (by apart) (by apart),V2,value1]
  · simpa only [val32,Nat.mul_zero,Nat.add_zero,Nat.mul_zero,Nat.add_zero] using V3
  · intro x hx
    have hA := hx (offset w 6,4*(n+1)) (by simp [twiceWrites])
    have hU := hx (offset w 12,4*n) (by simp [twiceWrites])
    rw [O3 x (by apart),O2 x (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hU
      · apart),O1 x hA]

end VG.Proof.Rsa.X86.InvBatch
