module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Body
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.FrameBase
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Init
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Batch
import Init.Prelude
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Algebra.Order.Ring.Abs
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import VerifiedGarbage.Proof.Divstep.Tc32
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Divstep.Steps
import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.BitVec
import Mathlib.Tactic.Linarith
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Finish
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Encoding
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
import VerifiedGarbage.Proof.Rsa.X86.InvLoop
/-! # Closed arithmetic proofs supplied at RSA registration -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/Frame.lean`, which only this module imported.
section

/-! # The batched GCD stays within the existing inverse bank -/

section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.Impl.Rsa.X86.GcdBatch VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Rsa.X86.Keys


theorem init_own {base : Addr} {n : Nat} {m m' : Mem} (h : Unch base (initWrites n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.cover
  intro w hw
  simp only [initWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · refine ⟨(offset n 11,4*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega

theorem batch_own {base : Addr} {n : Nat} {m m' : Mem} (h : Unch base (batchWrites n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.cover
  intro w hw
  simp only [batchWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl
  · refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · refine ⟨(offset n 11,4*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega
  · exact ⟨(100,4),by simp [ownRanges],by decide,by decide⟩

theorem result_own {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base (offset n 1) (4*n) m m') :
    Unch base (ownRanges n) m m' := by
  apply h.unch.cover
  intro w hw
  rw [List.mem_singleton] at hw
  subst w
  refine ⟨(offset n 0,8*(4*n+8)),by simp [ownRanges],?_,?_⟩ <;> dsimp only [offset] <;> omega

end VG.Proof.Rsa.X86.GcdBatch
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/Loop.lean`, which only this module imported.
section

/-! # A fixed public number of GCD batches -/

section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Weierstrass.X86 (countLoop_ok)

structure Facts (I : Int × Int × Int) (p : Nat) : Prop where
  delta : |I.1|+64<2^30
  odd : I.2.1%2=1
  f : |I.2.1| ≤ p
  g : |I.2.2| ≤ p

theorem loop_ok {s : State} {base : Addr} {size n p B : Nat} {m x : Int}
    (hs : Scr s base size) (hn : 16 ≤ n) (hz : offset n 15 ≤ size)
    (hB : 0<B) (hB32 : B<2^32) (hp : p<2^(32*n+1))
    (hI : StateAt n base (1,m,x) s) (hc : w32 s.mem base 100=B)
    (facts : ∀ i<B,Facts (Divstep.divsteps (30*i) (1,m,x)) p) :
    WP isa (.loop (batch n) .ne) s fun z =>
      StateAt n base (Divstep.divsteps (30*B) (1,m,x)) z ∧
      Keeps wordClob s z ∧ Unch base (batchWrites n) s.mem z.mem := by
  let J := fun j u => Scr u base size ∧
    StateAt n base (Divstep.divsteps (30*(B-j)) (1,m,x)) u ∧
    w32 u.mem base 100=j ∧ Keeps wordClob s u ∧ Unch base (batchWrites n) s.mem u.mem
  refine countLoop_ok (Inv:=J) (n:=B) ?_ ?_ hB ?_
  · intro j u hj hjB hJ
    obtain ⟨hu,Iu,Cu,Ku,Ou⟩ := hJ
    have F := facts (B-j) (by omega)
    refine WP.mono (batch_ok hu hn hz Iu F.delta F.odd F.f F.g hp hj (by omega) Cu)
      fun z ⟨Iz,Cz,Zz,Kz,Oz⟩ => ⟨?_,Zz⟩
    refine ⟨hu.of_keeps Kz (by decide),?_,Cz,Ku.trans Kz,(Ou.trans Oz).mono (by
      intro w hw
      simpa only [List.mem_append,or_self] using hw)⟩
    rw [show 30*(B-(j-1))=30*(B-j)+30 by omega,Divstep.divsteps_add]
    exact Iz
  · intro u hJ
    obtain ⟨_,Iu,_,Ku,Ou⟩ := hJ
    simpa only [Nat.sub_zero] using (show StateAt n base (Divstep.divsteps (30*(B-0)) (1,m,x)) u ∧
      Keeps wordClob s u ∧ Unch base (batchWrites n) s.mem u.mem from ⟨Iu,Ku,Ou⟩)
  · exact ⟨hs,by simpa only [Nat.sub_self,Nat.mul_zero,Divstep.divsteps] using hI,hc,
      Keeps.refl _ _,Unch.refl _ _ _⟩

end VG.Proof.Rsa.X86.GcdBatch
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/Facts.lean`, which only this module imported.
section

/-! # Arithmetic bounds for all RSA GCD batches -/

section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG.Proof.Divstep

theorem runFacts {n m x p i : Nat} (hn : n ≤ 1024) (hi : i<3*(n+1))
    (hm : m%2=1) (mp : m≤p) (xp : x≤p) :
    Facts (divsteps (30*i) (1,m,x)) p := by
  have d := W32.divsteps_d (1,m,x) (30*i)
  have ho := divsteps_odd (d:=1) (f:=m) (g:=x) (by decide) (by exact_mod_cast hm) (30*i)
  have fg := W32.divsteps_le (M:=p) (d:=1) (f:=m) (g:=x) (by decide) (by exact_mod_cast hm)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (m:Int)≤p by exact_mod_cast mp))
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using (show (x:Int)≤p by exact_mod_cast xp)) (30*i)
  refine ⟨?_,ho.2,fg.1,fg.2⟩
  norm_num only [abs_one,Nat.cast_mul,Nat.cast_ofNat] at d
  omega

theorem initial_bound {n m x : Nat} (hm : m<2^(32*n)) (hx : x<2^(32*n)) :
    max m (VG.Proof.Rsa.Divstep.oddInput m x)<2^(32*n+1) := by
  have h := VG.Proof.Rsa.Divstep.oddInput_lt hm hx
  have pos := Nat.two_pow_pos (32*n)
  rw [Nat.pow_succ]
  omega

end VG.Proof.Rsa.X86.GcdBatch
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/GcdBatch/BodyProof.lean`, which only this module imported.
section

/-! # Functional correctness of the complete batched RSA GCD -/

section
namespace VG.Proof.Rsa.X86.GcdBatch
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.GcdBatch
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Rsa.X86.Keys
open VG.Proof.Weierstrass.X86.Inv (wordClob setWord_ok)

local macro "apart" : tactic => `(tactic| (dsimp only [offset] at *; omega))

theorem body_ok_proof {s : State} {base : Addr} {size n : Nat}
    (hs : Scr s base size) (hn : 16 ≤ n) (hnMax : n ≤ 1024) (hz : offset n 15 ≤ size)
    (hm : val32 s.mem base (offset n 8) n % 2=1) :
    WP isa (body n) s fun z =>
      val32 z.mem base (offset n 1) n =
        Nat.gcd (val32 s.mem base (offset n 8) n) (val32 s.mem base (offset n 0) n) ∧
      Keeps wordClob s z ∧ Keep base n invArrs invSlots s.mem z.mem := by
  have nowrap := hs.nowrap
  let m := val32 s.mem base (offset n 8) n
  let x := val32 s.mem base (offset n 0) n
  let y := VG.Proof.Rsa.Divstep.oddInput m x
  let B := 3*(n+1)
  have bpos : 0<B := by dsimp only [B]; omega
  have b32 : B<2^32 := by dsimp only [B]; omega
  have mp : m<2^(32*n) := val32_lt _ _ _ _
  have xp : x<2^(32*n) := val32_lt _ _ _ _
  have done := VG.Proof.Rsa.Divstep.oddInput_done hm mp xp
  unfold body
  simp only [VG.Impl.Rsa.X86.GcdBatch.seqs,VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.block_append (WP.mono (init_ok hs hn hz) fun s₁ ⟨F₁,G₁,D₁,K₁,O₁⟩ => ?_))
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (setWord_ok (dst:=100) (BitVec.ofNat 32 B) hs₁ (by apart)) fun s₂ ⟨C₂,K₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  have I₂ : StateAt n base (1,m,y) s₂ := by
    refine ⟨?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      change w32 s₂.mem base (offset n 3)=_
      rw [O₂.w32 (by apart) (by apart),D₁]
      rfl
    · rw [O₂.val32 (by apart) (by apart),F₁]
    · rw [O₂.val32 (by apart) (by apart),G₁]
  have C : w32 s₂.mem base 100=B := by
    rw [C₂,BitVec.toNat_ofNat,Nat.mod_eq_of_lt b32]
  refine WP.seq (WP.mono (loop_ok hs₂ hn hz bpos b32 (initial_bound mp xp) I₂ C
    (fun i hi => runFacts hnMax hi hm (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    fun s₃ ⟨I₃,K₃,O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  let f := (Divstep.divsteps (30*B) (1,m,y)).2.1
  have gcdBound : Nat.gcd m x<2^(32*n) :=
    (Nat.gcd_le_left x (by dsimp only [m]; omega)).trans_lt mp
  have absBound : |f|<(2:Int)^(32*n) := by
    have hNat : f.natAbs<2^(32*n) := by rw [done.2]; exact gcdBound
    have hInt : (f.natAbs : Int)<(2:Int)^(32*n) := by exact_mod_cast hNat
    simpa only [Int.natCast_natAbs] using hInt
  refine WP.mono (finish_ok hs₃ hn hz absBound (encoding_low I₃.f) (encoding_sign I₃.f absBound))
    fun z ⟨V₄,K₄,O₄⟩ => ⟨V₄.trans done.2,?_,?_⟩
  · have Kstart : Keeps wordClob s s₁ := K₁.mono (by decide)
    exact ((Kstart.trans (K₂.mono (by decide))).trans K₃).trans (K₄.mono (by decide))
  · have P₁ := own_keep (init_own O₁)
    have P₂ : Keep base n invArrs invSlots s₁.mem s₂.mem := Keep.of_slot O₂ (by decide)
    exact ((P₁.trans P₂).trans (own_keep (batch_own O₃))).trans (own_keep (result_own O₄))

end VG.Proof.Rsa.X86.GcdBatch
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86
instance batchLaw : BatchLaw where
  gcd_ok := GcdBatch.body_ok_proof
  inv_ok := InvBatchRt.body_ok
end VG.Proof.Rsa.X86
