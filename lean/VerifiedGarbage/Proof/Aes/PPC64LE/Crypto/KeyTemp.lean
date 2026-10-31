module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyGroups
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the public word index selects the two FIPS key-schedule transformations.
/-! # POWER8 AES key-schedule temporary word -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.KeyWords (sub32 temp32)
open VG.Impl.Aes.KeyWords (rc)

theorem div_pred_zero {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (hi : nk ≤ i) (h : i % nk = 0) :
    (i-1)/nk+1 = i/nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem div_pred_ne {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8) (h : i % nk ≠ 0) :
    (i-1)/nk = i/nk := by
  rcases h3 with rfl | rfl | rfl <;> omega

theorem temp_rotate_ok (s : State) {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hi : nk ≤ i) (hlim : i < 4*(nk+7)) (hmod : i%nk = 0)
    (hrc : s.gpr .r6 = (rc ((i-1)/nk+1)).setWidth 64) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.subWord ++ Impl.Aes.PPC64LE.Crypto.rotTail)) s fun t =>
      (t.gpr .r9).setWidth 32 = temp32 nk i ((s.gpr .r9).setWidth 32) ∧
      t.gpr .r6 = (rc (i/nk+1)).setWidth 64 ∧ Local [.r0, .r6, .r8, .r9] [.v0] s t := by
  have hdiv := div_pred_zero h3 hi hmod
  have hj : 1 ≤ i/nk ∧ i/nk < 11 := by rcases h3 with rfl | rfl | rfl <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (subWord_ok s) fun u ⟨hv, he⟩ => ?_
  refine WP.mono (rotTail_ok u) fun t ⟨ht, hc, hf⟩ => ?_
  have hrcu : u.gpr .r6 = (rc (i/nk)).setWidth 64 := by rw [he.keep.gpr (by decide), hrc, hdiv]
  refine ⟨?_, ?_, (he.trans hf).weaken (by simp [or_left_comm]) (by simp)⟩
  · rw [ht, hv, hrcu, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      BitVec.setWidth_setWidth_of_le _ (by decide), temp32, ite_eq_left hmod]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq]
  · rw [hc, hrcu]
    exact rcNext_rc ⟨i/nk, hj.2⟩ hj.1

/-- Subtract-and-test implements a comparison of two public small integers. -/
theorem test_choice (r : Reg) (a b : Nat) (s : State) (yes no : Prog isa) (Q : State → Prop)
    (hr : r ≠ .r0) (ha : a < 2^64) (hb : b ≤ 2^15) (hreg : s.gpr r = BitVec.ofNat 64 a)
    (hy : a = b → WP isa yes (s.write .r0 (s.gpr r - BitVec.ofNat 64 b)) Q)
    (hn : a ≠ b → WP isa no (s.write .r0 (s.gpr r - BitVec.ofNat 64 b)) Q) :
    WP isa (.seq (.block [.subi .r0 r b]) (.ite (.zero .d .r0) yes no)) s Q := by
  refine WP.seq (WP.mono (testWord_ok r b s hr hb) fun t ht => ?_)
  subst t
  have he : eval (.zero .d .r0) (s.write .r0 (s.gpr r - BitVec.ofNat 64 b)) = some (decide (a=b)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write_self, hreg]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq ha (by omega))
  by_cases hab : a = b
  · refine WP.ite true (by simpa only [hab, decide_true] using he) (fun _ => hy hab) (by simp)
  · refine WP.ite false (by simpa only [hab, decide_false] using he) (by simp) (fun _ => hn hab)

/-- The non-boundary key words only apply SubWord for AES-256 word four. -/
theorem temp_nonrot_ok (s : State) {nk q : Nat} (hnk : nk ≤ 8) (hq : q < nk)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (4*q)) (h7 : s.gpr .r7 = BitVec.ofNat 64 (4*nk)) :
    WP isa (.seq (.block [.subi .r0 .r12 16])
      (.ite (.zero .d .r0)
        (.seq (.block [.subi .r0 .r7 32])
          (.ite (.zero .d .r0) (.block Impl.Aes.PPC64LE.Crypto.subWord) (.block []))) (.block []))) s fun t =>
      (t.gpr .r9).setWidth 32 = (if nk = 8 ∧ q = 4 then sub32 ((s.gpr .r9).setWidth 32) else (s.gpr .r9).setWidth 32) ∧
      Local [.r0, .r9] [.v0] s t := by
  refine test_choice .r12 (4*q) 16 s _ _ _ (by decide) (by omega) (by decide) h12 ?_ ?_
  · intro hq4
    have hqe : q = 4 := by omega
    have hloc := Local.write s .r0 (s.gpr .r12 - BitVec.ofNat 64 16)
    refine test_choice .r7 (4*nk) 32 _ _ _ _ (by decide) (by omega) (by decide)
      (by rw [hloc.keep.gpr (by decide)]; exact h7) ?_ ?_
    · intro hn8
      have hnke : nk = 8 := by omega
      have hloc' := Local.write (s.write .r0 (s.gpr .r12 - BitVec.ofNat 64 16)) .r0
        ((s.write .r0 (s.gpr .r12 - BitVec.ofNat 64 16)).gpr .r7 - BitVec.ofNat 64 32)
      refine WP.mono (subWord_ok _) fun t ⟨hv, he⟩ => ⟨?_, ?_⟩
      · rw [hv, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq,
          hloc'.keep.gpr (by decide), hloc.keep.gpr (by decide)]
        simp only [hnke, hqe, and_self, ite_true]
      · exact ((hloc.trans hloc').trans he).weaken (by simp) (by simp)
    · intro hn8
      have hnke : nk ≠ 8 := by omega
      refine WP.block_nil ⟨?_, ?_⟩
      · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, hnke, false_and, ite_false]
      · exact (hloc.trans (Local.write _ .r0 _)).weaken (by simp) (by simp)
  · intro hq4
    have hqe : q ≠ 4 := by omega
    refine WP.block_nil ⟨?_, (Local.write s .r0 (s.gpr .r12 - BitVec.ofNat 64 16)).weaken (by simp) (by simp)⟩
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, hqe, and_false, ite_false]

theorem tempWord_ok (s : State) {nk i : Nat} (h3 : nk = 4 ∨ nk = 6 ∨ nk = 8)
    (hi : nk ≤ i) (hlim : i < 4*(nk+7))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (4*(i%nk))) (h7 : s.gpr .r7 = BitVec.ofNat 64 (4*nk))
    (hrc : s.gpr .r6 = (rc ((i-1)/nk+1)).setWidth 64) :
    WP isa Impl.Aes.PPC64LE.Crypto.tempWord s fun t =>
      (t.gpr .r9).setWidth 32 = temp32 nk i ((s.gpr .r9).setWidth 32) ∧
      t.gpr .r6 = (rc (i/nk+1)).setWidth 64 ∧ Local [.r0, .r6, .r8, .r9] [.v0] s t := by
  have hnk : 0 < nk ∧ nk ≤ 8 := by omega
  have hrem : i%nk < nk := Nat.mod_lt _ hnk.1
  have he := eval_zero_ofNat s .r12 (by omega) h12
  change eval (.zero .d .r12) s = some (decide (4*(i%nk)=0)) at he
  rw [Impl.Aes.PPC64LE.Crypto.tempWord]
  by_cases hmod : i%nk = 0
  · refine WP.ite true (by simpa only [hmod, Nat.mul_zero, decide_true] using he)
      (fun _ => temp_rotate_ok s h3 hi hlim hmod hrc) (by simp)
  · refine WP.ite false (by simpa only [show ¬4*(i%nk)=0 by omega, decide_false] using he) (by simp) (fun _ => ?_)
    refine WP.mono (temp_nonrot_ok s hnk.2 hrem h12 h7) fun t ⟨hv, hf⟩ => ⟨?_, ?_, ?_⟩
    · have heq : (nk > 6 ∧ i%nk = 4) ↔ (nk = 8 ∧ i%nk = 4) := by omega
      simpa only [temp32, ite_eq_right hmod, propext heq] using hv
    · rw [hf.keep.gpr (by decide), hrc, div_pred_ne h3 hmod]
    · exact hf.weaken (by simp) (by simp)

end VG.Proof.Aes.PPC64LE.Crypto
