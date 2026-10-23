module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Defs
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.InitParts
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Operands
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Virtualize
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.StateFrame
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State

/-! # Initializing the complete batched inversion state -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv


local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega_arith))

 theorem virtualMod_odd {m : Nat} (odd : m%2=1) : virtualMod m%2=1 := by
  unfold virtualMod; split_ifs <;> omega

 theorem init_ok {s : State} {base : Addr} {size w n m x : Nat}
    (hs : Scr s base size) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (hz : offset w 15≤size)
    (hm : val32 s.mem base (offset w 8) n=m) (hx : val32 s.mem base (offset w 0) n=x)
    (odd : m%2=1) :
    WP isa (.block (init w n)) s fun z => ∃ iv,
      StateAt w n base (virtualMod m) iv
        (VG.Proof.Divstep.W32.invRun 30 (virtualMod m) iv (VG.Proof.Rsa.Divstep.oddInput (virtualMod m) x) 0) z ∧
      (virtualMod m*iv+1)%2^32=0 ∧ w32 z.mem base 100=3*(n+1) ∧
      Keeps wordClob s z ∧ Unch base (initWrites w) s.mem z.mem := by
  have nw := hs.nowrap
  unfold init
  refine WP.block_append (WP.block_append (WP.block_append (WP.block_append (WP.block_append
    (WP.mono (VG.Proof.Weierstrass.X86.copy_ok n hs (o:=offset w 2) (a:=offset w 8)
      (by apart) (by apart) (by apart)) fun s1 ⟨V1,K1,O1⟩ => ?_)))))
  rw [hm] at V1
  have hs1 := hs.of_keeps K1 (by decide)
  refine WP.mono (virtualize_ok hs1 (M:=offset w 2) (n:=n) (by omega_arith) (by apart)) fun s2 ⟨V2,K2,O2⟩ => ?_
  rw [V1] at V2
  change val32 s2.mem base (offset w 2) n=virtualMod m at V2
  have hs2 := hs1.of_keeps K2 (by decide)
  refine WP.mono (operands_ok hs2 hn hw hz) fun s3 ⟨F3,G3,D3,K3,O3⟩ => ?_
  rw [V2] at F3 G3
  rw [O2.val32 (by apart) (by apart),O1.val32 (by apart) (by apart),hx] at G3
  have hs3 := hs2.of_keeps K3 (by decide)
  refine WP.mono (coefficients_ok hs3 hn hw hz) fun s4 ⟨A4,B4,K4,O4⟩ => ?_
  have hs4 := hs3.of_keeps K4 (by decide)
  have M4 : val32 s4.mem base (offset w 2) n=virtualMod m := by
    rw [O4.val32 (by apart) (by apart),Outs.val32 O3 (by
      intro r hr; simp only [operandWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart) (by apart),V2]
  refine WP.mono (inverseSetup_ok hs4 hn hw hz M4 (virtualMod_odd odd)) fun s5 ⟨inv,K5,O5⟩ => ?_
  have hs5 := hs4.of_keeps K5 (by decide)
  let iv := w32 s5.mem base (offset w 3+28)
  have power : 1<2^(32*n) := Nat.one_lt_two_pow (by omega_arith)
  have aLow : val32 s4.mem base (offset w 6) n=0 := by
    rw [val32_succ] at A4; omega_arith
  have aTop : w32 s4.mem base (offset w 6+4*n)=0 := by
    rw [val32_succ] at A4
    by_contra h
    have bound := Nat.mul_le_mul_left (2^(32*n)) (show 1≤w32 s4.mem base (offset w 6+4*n) by omega_arith)
    omega_arith
  have bTop : w32 s4.mem base (offset w 7+4*n)=0 := by
    rw [val32_succ] at B4
    by_contra h
    have bound := Nat.mul_le_mul_left (2^(32*n)) (show 1≤w32 s4.mem base (offset w 7+4*n) by omega_arith)
    omega_arith
  have bLow : val32 s4.mem base (offset w 7) n=1 := by
    rw [val32_succ,bTop,Nat.mul_zero,Nat.add_zero] at B4; exact B4
  have I5 : StateAt w n base (virtualMod m) iv
      (VG.Proof.Divstep.W32.invRun 30 (virtualMod m) iv (VG.Proof.Rsa.Divstep.oddInput (virtualMod m) x) 0) s5 := by
    refine ⟨?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 s5.mem base (offset w 3)=1
      rw [O5.w32 (by apart) (by apart),O4.w32 (by apart) (by apart),D3]
    · rw [O5.val32 (by apart) (by apart),M4]
    · rw [O5.val32 (by apart) (by apart),O4.val32 (by apart) (by apart),F3]; rfl
    · rw [O5.val32 (by apart) (by apart),O4.val32 (by apart) (by apart),G3]; rfl
    · rw [O5.val32 (by apart) (by apart),aLow]; rfl
    · rw [O5.val32 (by apart) (by apart),bLow]; rfl
    · rw [O5.w32 (by apart) (by apart),aTop]
    · rw [O5.w32 (by apart) (by apart),bTop]
  refine WP.mono (setWord_ok (dst:=100) (BitVec.ofNat 32 (3*(n+1))) hs5 (by apart)) fun z ⟨C6,K6,O6⟩ => ?_
  have I6 := I5.keep_counter hs5 hn hw hz O6
  refine ⟨iv,I6,inv,?_,?_,?_⟩
  · rw [C6,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith)]
  · exact (((((K1.mono (by decide)).trans (K2.mono (by decide))).trans (K3.mono (by decide))).trans
      (K4.mono (by decide))).trans (K5.mono (by decide))).trans (K6.mono (by decide))
  · intro y hy
    have h0 := hy (offset w 0,8*(4*w+8)) (by simp [initWrites])
    have h11 := hy (offset w 11,4*(4*w+8)) (by simp [initWrites])
    have h100 := hy (100,4) (by simp [initWrites])
    rw [O6 y h100,O5 y (by apart),O4 y (by apart),O3 y (by
      intro r hr; simp only [operandWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart),O2 y (by apart),O1 y (by apart)]

end VG.Proof.Rsa.X86.InvBatch
