module

import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Frame
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Facts
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Finish
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Encoding
import VerifiedGarbage.Proof.Weierstrass.X86.InvSetWord
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import Mathlib.Data.Nat.GCD.Basic
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatch
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.Divstep.OddInput
import Mathlib.Data.BitVec
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-! # Functional correctness of the complete batched RSA GCD -/

@[expose] public section
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
