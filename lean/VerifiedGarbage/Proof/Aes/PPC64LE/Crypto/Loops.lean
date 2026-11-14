module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Invariant
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: counted batch and tail loops use the same termination argument.
/-! # POWER8 AES data loops -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE

theorem LoopInv.write12 {inverse ctr : Bool} {base s : State} {nr n k : Nat} {D E : Addr} {icb : Spec.Gcm.Block}
    (h : LoopInv inverse ctr base nr n D E icb k s) (x : BitVec 64) :
    LoopInv inverse ctr base nr n D E icb k (s.write .r12 x) := by
  have he := Local.write s .r12 x
  refine ⟨h.bound, (h.keep.trans he.keep).mono (by simp [loopGprs]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he.keep.gpr (by decide)]; exact h.ptr
  · rw [he.keep.gpr (by decide)]; exact h.left
  · rw [he.mem]; exact h.processed
  · rw [he.mem]; exact h.frame
  · rw [he.v _ (by simp)]; exact h.mask
  · intro ht; rw [he.v _ (by simp)]; exact h.control ht
  · intro ht; rw [he.v _ (by simp)]; exact h.counter ht

theorem quotient_ok (s : State) : WP isa (.block [.lsr .d .r12 .r7 3]) s
    (· = s.write .r12 (s.gpr .r7 >>> 3)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.read, Size.ext, Size.bits, BitVec.setWidth_eq,
    show 3 < 64 by decide, ite_true, Option.some.injEq, exists_eq_left']

theorem quotient_zero {j : Nat} (hj : j < 2^64) :
    (BitVec.ofNat 64 j >>> 3) = 0 ↔ j < 8 := by
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
      Nat.shiftRight_eq_div_pow] at hh
    change j / 8 = 0 at hh
    omega_using [hh]
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
      Nat.shiftRight_eq_div_pow]
    change j / 8 = 0
    exact Nat.div_eq_of_lt h


theorem count_test (r : Reg) (s : State) {left N : Nat}
    (hz : s.gpr r = 0 ↔ left < N) :
    (left < N → eval (.nonzero .d r) s = some false) ∧
      (N ≤ left → eval (.nonzero .d r) s = some true) := by
  have he : eval (.nonzero .d r) s = some (s.gpr r != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
  constructor
  · intro h; rw [he, hz.mpr h]; rfl
  · intro h
    have hn : s.gpr r ≠ 0 := fun he => by have := hz.mp he; omega_using [h, this]
    exact he.trans (by simpa using hn)

theorem zero_test (r : Reg) (s : State) (b : Bool)
    (h : eval (.nonzero .d r) s = some b) : eval (.zero .d r) s = some (!b) := by
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq] at h ⊢
  have hh := Option.some.inj h
  rw [← hh]
  simp only [bne, Bool.not_not]

/-- Bit `c` of a number below `2 c` is set exactly when it is at least `c`. -/
theorem bit_test {c m : Nat} (hc : c = 1 ∨ c = 2 ∨ c = 4) (hm : m < 2 * c) :
    (BitVec.ofNat 64 m &&& BitVec.ofNat 64 c == 0) = decide (m < c) := by
  have h : ∀ c ∈ [1, 2, 4], ∀ m : Fin 8, m.val < 2 * c →
      (BitVec.ofNat 64 m.val &&& BitVec.ofNat 64 c == 0) = decide (m.val < c) := by decide
  exact h c (by rcases hc with rfl | rfl | rfl <;> simp) ⟨m, by rcases hc with rfl | rfl | rfl <;> omega_using [hm]⟩ hm

theorem tail_step_ok {inverse ctr : Bool} {o : Reg} {base s : State} {nr n j c : Nat} {D E : Addr}
    {icb : Spec.Gcm.Block} (hc4 : c = 1 ∨ c = 2 ∨ c = 4)
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb j s)
    (hlt : n - j < 2 * c) :
    WP isa (Impl.Aes.PPC64LE.Crypto.tailStep inverse ctr c o) s
      fun t => ∃ j', j' ≤ n ∧ n - j' < c ∧ LoopInv inverse ctr base nr n D E icb j' t := by
  have hc8 : c < 2 ^ 15 := by rcases hc4 with rfl | rfl | rfl <;> decide
  have hb : WP isa (.block [.li .r12 c, .logic .and .r12 .r7 .r12]) s
      (· = (s.write .r12 (BitVec.ofNat 64 c)).write .r12 (s.gpr .r7 &&& BitVec.ofNat 64 c)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, hc8, ite_true, RegUpd.gpr_write,
      reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  rw [Impl.Aes.PPC64LE.Crypto.tailStep]
  refine WP.seq (WP.mono hb fun t ht => ?_)
  subst t
  have ht := (h.write12 (BitVec.ofNat 64 c)).write12 (s.gpr .r7 &&& BitVec.ofNat 64 c)
  have hz : isa.eval (.zero .d .r12) ((s.write .r12 (BitVec.ofNat 64 c)).write .r12 (s.gpr .r7 &&& BitVec.ofNat 64 c))
      = some (decide (n - j < c)) := by
    rw [eval_zero, RegUpd.gpr_write_self, h.left, bit_test hc4 hlt]
  by_cases hl : n - j < c
  · exact WP.ite true (by rw [hz, decide_eq_true hl]) (fun _ => WP.block_nil ⟨j, h.bound, hl, ht⟩) (by simp)
  · refine WP.ite false (by rw [hz, decide_eq_false hl]) (by simp) (fun _ => ?_)
    exact WP.mono (loop_group_ok hc ht (by rcases hc4 with rfl | rfl | rfl <;> decide) (by omega_using [hc4, hl]))
      fun u hu => ⟨j + c, by omega_using [hc4, hl], by omega_using [hlt], hu⟩

theorem batch_loop_ok {inverse ctr : Bool} {o : Reg} {base s : State} {nr n k : Nat} {D E : Addr} {icb : Spec.Gcm.Block}
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb k s)
    (hk : k+8 ≤ n) :
    WP isa (.loop (.seq (Impl.Aes.PPC64LE.Crypto.group inverse ctr 8 o)
      (.block [.lsr .d .r12 .r7 3])) (.nonzero .d .r12)) s
      fun t => ∃ j, j ≤ n ∧ n-j < 8 ∧ LoopInv inverse ctr base nr n D E icb j t := by
  let I : Nat → State → Prop := fun j t => LoopInv inverse ctr base nr n D E icb j t ∧
    t.gpr .r12 = BitVec.ofNat 64 (n-j) >>> 3
  have step : ∀ j t, j+8 ≤ n → LoopInv inverse ctr base nr n D E icb j t →
      WP isa (.seq (Impl.Aes.PPC64LE.Crypto.group inverse ctr 8 o) (.block [.lsr .d .r12 .r7 3])) t (I (j+8)) := by
    intro j t hj ht
    refine WP.seq (WP.mono (loop_group_ok hc ht (by decide) hj) fun u hu => ?_)
    refine WP.mono (quotient_ok u) fun v hv => ?_
    subst v
    exact ⟨hu.write12 _, by rw [RegUpd.gpr_write_self, hu.left]⟩
  have test : ∀ j t, j ≤ n → I j t →
      (n-j < 8 → eval (.nonzero .d .r12) t = some false) ∧
      (8 ≤ n-j → eval (.nonzero .d .r12) t = some true) := by
    intro j t hj ht
    apply count_test
    rw [ht.2]
    exact quotient_zero (by have := hc.size; omega_using [this])
  -- The first iteration computes the quotient before the loop condition is tested.
  refine WP.loop (M := isa) (fun m t => ∃ j, m = n-j ∧ j+8 ≤ n ∧ LoopInv inverse ctr base nr n D E icb j t)
    (fun m t ht => ?_) (n-k) s ⟨k, rfl, hk, h⟩
  obtain ⟨j, rfl, hj, ht⟩ := ht
  refine WP.mono (step j t hj ht) fun u hu => ?_
  have he := test (j+8) u hj hu
  by_cases hl : n-(j+8) < 8
  · exact Or.inl ⟨he.1 hl, j+8, hj, hl, hu.1⟩
  · exact Or.inr ⟨he.2 (by omega_using [hl]), n-(j+8), by omega_using [hj], j+8, rfl, by omega_using [hl], hu.1⟩

theorem batches_ok {inverse ctr : Bool} {o : Reg} {base s : State} {nr n k : Nat} {D E : Addr} {icb : Spec.Gcm.Block}
    (hc : LoopConfig inverse ctr o base nr n D E) (h : LoopInv inverse ctr base nr n D E icb k s) :
    WP isa (Impl.Aes.PPC64LE.Crypto.batches inverse ctr o) s
      (LoopInv inverse ctr base nr n D E icb n) := by
  rw [Impl.Aes.PPC64LE.Crypto.batches]
  refine WP.seq (WP.mono (quotient_ok s) fun t ht => ?_)
  subst t
  have hs := h.write12 (s.gpr .r7 >>> 3)
  have hz : (s.write .r12 (s.gpr .r7 >>> 3)).gpr .r12 = 0 ↔ n-k < 8 := by
    rw [RegUpd.gpr_write_self, h.left]
    exact quotient_zero (by have := hc.size; omega_using [this])
  have full : WP isa (.ite (.zero .d .r12) (.block [])
      (.loop (.seq (Impl.Aes.PPC64LE.Crypto.group inverse ctr 8 o) (.block [.lsr .d .r12 .r7 3]))
        (.nonzero .d .r12))) (s.write .r12 (s.gpr .r7 >>> 3))
      (fun t => ∃ j, j ≤ n ∧ n-j < 8 ∧ LoopInv inverse ctr base nr n D E icb j t) := by
    have he := count_test .r12 (s.write .r12 (s.gpr .r7 >>> 3)) hz
    by_cases hl : n-k < 8
    · refine WP.ite true (by simpa using zero_test _ _ false (he.1 hl)) (fun _ => ?_) (by simp)
      exact WP.block_nil ⟨k, h.bound, hl, hs⟩
    · refine WP.ite false (by simpa using zero_test _ _ true (he.2 (by omega_using [hl]))) (by simp) (fun _ => ?_)
      exact batch_loop_ok hc hs (by omega_using [hl])
  refine WP.seq (WP.mono full fun t ⟨j, hj, hl, ht⟩ => ?_)
  refine WP.seq (WP.mono (tail_step_ok (c := 4) (by decide) hc ht (by omega_using [hl])) fun t ⟨j, hj, hl, ht⟩ => ?_)
  refine WP.seq (WP.mono (tail_step_ok (c := 2) (by decide) hc ht (by omega_using [hl])) fun t ⟨j, hj, hl, ht⟩ => ?_)
  refine WP.mono (tail_step_ok (c := 1) (by decide) hc ht (by omega_using [hl])) fun t ⟨j, hj, hl, ht⟩ => ?_
  exact (show j = n by omega_using [hj, hl]) ▸ ht

end VG.Proof.Aes.PPC64LE.Crypto
