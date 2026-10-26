module

import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Init
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.CorrectionMath
import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Finish
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Encoding
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Rsa.Divstep.InvCorrectDef
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.State
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import VerifiedGarbage.Impl.Rsa.X86.InvBatch
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.X86.InvBatch.Defs

/-! # Sign, scale, and full-width output correction -/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.InvBatch VG.Impl.Weierstrass.X86
 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Inv

 def correctionCode (w n : Nat) : Prog isa := seqs [
 .block (normalize w n ++ [.mov .esi (.imm (BitVec.ofNat 32 (6*(n+1))))]),
 .loop (.block (twice w n ++ [decCounter,testCounter])) .ne,.block (finish w n)]
local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega_arith))

 theorem correction_ok {s : State} {base : Addr} {size w n p iv : Nat} {st : VG.Proof.Divstep.W32.IState}
    (hs : Scr s base size) (hn : 16≤n) (nl : n≤1024) (hw : w=2*n) (he : n%2=0) (hz : offset w 15≤size)
    (h : StateAt w n base p iv st s) (hp : 0<p) (a0 : 0≤st.a) (ap : st.a<p) (fb : |st.f|<2^(32*n)) :
    WP isa (correctionCode w n) s fun z =>
      val32 z.mem base (offset w 1) w=st.f.natAbs ∧
      val32 z.mem base (offset w 3) w=(VG.Proof.Rsa.Divstep.corrected p st (3*(n+1))).toNat ∧
      Keeps wordClob s z ∧ Unch base (initWrites w) s.mem z.mem := by
  have nw := hs.nowrap
  let a := st.a.toNat
  have sa : st.a=(a : Int) := (Int.toNat_of_nonneg a0).symm
  have small : a<p := by exact_mod_cast (sa ▸ ap)
  have ha : val32 s.mem base (offset w 6) n=a := by exact_mod_cast h.a.trans sa
  have sign := GcdBatch.encoding_sign h.f fb
  unfold correctionCode
  simp only [seqs,VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.block_append (WP.mono (normalize_ok hs hn hw he hz h.modulus ha h.aTop hp small sign)
    fun s1 ⟨V1,T1,K1,O1⟩ => ?_))
  refine wp_movS rfl fun s2 U2 _ => WP.block_nil ?_
  have k2 : Keeps wordClob s s2 := K1.trans (U2.keeps.mono (by decide))
  have hs2 := hs.of_keeps k2 (by decide)
  have mod2 : val32 s2.mem base (offset w 2) n=p := by
    rw [U2.mem,Outs.val32 O1 (by
      intro r hr; simp only [normalWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart) (by apart),h.modulus]
  refine WP.seq (WP.mono (doubleLoop_ok hs2 hn hw he hz mod2 (by rw [U2.mem,V1]) (by rw [U2.mem,T1]) hp
    (normal_range st.f hp small) (by omega_arith) (by omega_arith) U2.gpr) fun s3 ⟨V3,T3,M3,C3,K3,O3⟩ => ?_)
  have hs3 := hs2.of_keeps K3 (by decide)
  have f3 : (val32 s3.mem base (offset w 4) (n+1) : Int)%2^(32*(n+1))=st.f%2^(32*(n+1)) := by
    rw [Outs.val32 O3 (by
      intro r hr; simp only [twiceWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart) (by apart),U2.mem,Outs.val32 O1 (by
      intro r hr; simp only [normalWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> apart) (by apart)]
    exact h.f
  refine WP.mono (finish_ok hs3 hn hw hz fb (GcdBatch.encoding_low f3) (GcdBatch.encoding_sign f3 fb) V3)
    fun z ⟨G4,A4,K4,O4⟩ => ?_
  refine ⟨G4,A4.trans (correction_eq small sa), (k2.trans K3).trans (K4.mono (by decide)),?_⟩
  intro y hy
  have h0 := hy (offset w 0,8*(4*w+8)) (by simp [initWrites])
  have h11 := hy (offset w 11,4*(4*w+8)) (by simp [initWrites])
  rw [O4 y (by
    intro r hr; simp only [finishWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> apart),O3 y (by
    intro r hr; simp only [twiceWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> apart),U2.mem,O1 y (by
    intro r hr; simp only [normalWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> apart)]

end VG.Proof.Rsa.X86.InvBatch
