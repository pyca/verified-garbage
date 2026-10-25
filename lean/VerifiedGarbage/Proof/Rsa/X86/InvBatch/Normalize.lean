module
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Weierstrass.Unch

public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Csub
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.InvShift
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.Mont.X86

/-! # Normalizing the inverse coefficient according to the sign of f -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def normal (p a : Nat) (f : Int) : Nat := if f<0 then (p-a)%p else a
 def normalWrites (w n : Nat) : List (Nat × Nat) := [(offset w 6,4*n),(offset w 12,4*n)]
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega_arith))

 theorem normalize_ok {s : State} {base : Addr} {size w n p a : Nat} {f : Int}
    (hs : Scr s base size) (hn : 16≤n) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 2) n=p) (ha : val32 s.mem base (offset w 6) n=a)
    (top : w32 s.mem base (offset w 6+4*n)=0) (_hp : 0<p) (small : a<p)
    (sign : (2^31≤w32 s.mem base (offset w 4+4*n)) ↔ f<0) :
    WP isa (.block (normalize w n)) s fun z =>
      val32 z.mem base (offset w 6) n=normal p a f ∧ w32 z.mem base (offset w 6+4*n)=0 ∧
      Keeps wordClob s z ∧ Unch base (normalWrites w n) s.mem z.mem := by
  have nw := hs.nowrap
  have en : n-1+1=n := by omega_arith
  have pn : p<2^(32*n) := hm ▸ val32_lt _ _ _ _
  have wn : words (config w n)=n := by simp only [config,words]; omega_arith
  unfold normalize
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (VG.Proof.Weierstrass.X86.copy_ok n hs (o:=offset w 12) (a:=offset w 2)
      (by apart) (by apart) (by apart)) fun s1 ⟨V1,K1,O1⟩ => ?_))))
  rw [hm] at V1
  have hs1 := hs.of_keeps K1 (by decide)
  rw [subInPlace_eq]
  have sub := chainSubSelf_ok hs1 (n-1) (acc:=offset w 12) (b:=offset w 6)
    (by rw [en]; apart) (by rw [en]; apart) (by rw [en]; apart)
  rw [en] at sub
  refine WP.mono sub fun s2 ⟨O2,⟨borrow,_,V2⟩,K2⟩ => ?_
  rw [O1.val32 (by apart) (by apart),ha,V1] at V2
  have value2 : val32 s2.mem base (offset w 12) n=p-a := by
    have bound := val32_lt s2.mem base (offset w 12) n
    cases borrow <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at V2 <;> omega_arith
  have hs2 := hs1.of_keeps K2 (by decide)
  refine WP.mono (maskOf_ok hs2 (coefficient:=offset w 4+4*n) (by apart)) fun s3 ⟨C3,K3,M3⟩ => ?_
  rw [O2.w32 (by apart) (by apart),O1.w32 (by apart) (by apart)] at C3
  simp only [sign] at C3
  have hs3 := hs2.of_keeps K3 (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.sel_ok (decide (f<0)) n hs3
    (by simpa only [decide_eq_true_eq] using C3) (o:=offset w 6) (a:=offset w 6) (b:=offset w 12)
    (by apart) (by apart) (by apart) (by apart) (by apart)) fun s4 ⟨V4,K4,O4⟩ => ?_
  rw [M3,value2,O2.val32 (by apart) (by apart),O1.val32 (by apart) (by apart),ha] at V4
  simp only [decide_eq_true_eq] at V4
  have top4 : w32 s4.mem base (offset w 6+4*n)=0 := by
    rw [O4.w32 (by apart) (by apart),M3,O2.w32 (by apart) (by apart),O1.w32 (by apart) (by apart),top]
  have full4 : val32 s4.mem base (offset w 6) (n+1)=if f<0 then p-a else a := by
    rw [val32_succ,V4,top4,Nat.mul_zero,Nat.add_zero]
  have mod4 : val32 s4.mem base (config w n).mo n=p := by
    change val32 s4.mem base (offset w 2) n=p
    rw [O4.val32 (by apart) (by apart),M3,O2.val32 (by apart) (by apart),O1.val32 (by apart) (by apart),hm]
  have hs4 := hs3.of_keeps K4 (by decide)
  refine WP.mono (csub_forward_ok hs4 wn (by omega_arith) (src:=offset w 6) (o:=offset w 6)
    (by apart) (by apart) (by dsimp only [config]; apart) (by dsimp only [config]; apart)
    (by dsimp only [config]; apart) (by dsimp only [config]; apart) (by apart) (by dsimp only [config]; apart)
    mod4 (by rw [full4]; split_ifs <;> omega_arith)) fun z ⟨O5,V5,K5⟩ => ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [V5,full4]
    unfold normal
    split_ifs with h
    · rfl
    · exact Nat.mod_eq_of_lt small
  · rw [word_unch O5 (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [config] <;> apart) (by apart),top4]
  · exact ((((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans
      (K4.mono (by decide))).trans (K5.mono (by decide))
  · intro x hx
    have hA := hx (offset w 6,4*n) (by simp [normalWrites])
    have hU := hx (offset w 12,4*n) (by simp [normalWrites])
    rw [O5 x (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hU
      · exact hA),O4 x hA,M3,O2 x hU,O1 x hU]

end VG.Proof.Rsa.X86.InvBatch
