module

public import VerifiedGarbage.Proof.Rsa.X86.InvDispatch
import VerifiedGarbage.Proof.Rsa.X86.InvChoice
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # The public guard of the batched inverse

`guard_ok`: CF set exactly for the lengths the batches take (`Eligible`), the inputs kept.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.KeyRt

/-- `n_len` a multiple of 16 and at least 128, and the primes' lengths at most `n_len / 2`. -/
def Eligible (args : Nat → BitVec 32) : Prop :=
  (args 7).toNat % 16 = 0 ∧ 128 ≤ (args 7).toNat ∧ (args 9).toNat < (args 7).toNat / 2 + 1 ∧
    (args 11).toNat < (args 7).toNat / 2 + 1

instance (args : Nat → BitVec 32) : Decidable (Eligible args) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Guarded (args : Nat → BitVec 32) (base : Addr) (size len P Q : Nat) (s t : State) : Prop where
  input : InvInput args base size len P Q t
  keeps : Keeps [.eax, .ecx] s t
  mem : t.mem = s.mem
  cf : t.cf = some (decide (Eligible args))

theorem reject_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.InvBatchRt.reject s fun t =>
      InvInput args base size len P Q t ∧ Keeps [.eax] s t ∧ t.mem = s.mem ∧ t.cf = some false := by
  refine cmpBoth rfl fun t T _ cf => WP.block_nil ?_
  have K : Keeps [.eax] s t := T.keeps _
  exact ⟨h.rest K (by decide) (by decide) T.mem, K, T.mem, by simpa using cf⟩

theorem and15 (x : BitVec 32) : (x &&& 15 == 0) = decide (x.toNat % 16 = 0) := by
  have e : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← e]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq h

theorem guard_ok {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) :
    WP isa VG.Impl.Rsa.X86.InvBatchRt.guard s (Guarded args base size len P Q s) := by
  unfold VG.Impl.Rsa.X86.InvBatchRt.guard
  -- `n_len % 16`.
  refine WP.seq (wp_movS h.gate.nArg.readSrc fun u₁ U₁ _ =>
    VG.Proof.Bignum.X86.CrtRt.wp_andZ rfl fun u U z => WP.block_nil ?_)
  have K : Keeps [.eax] s u := U₁.keeps.trans U.keeps
  have m : u.mem = s.mem := U.mem.trans U₁.mem
  have hu := h.rest K (by decide) (by decide) m
  rw [U₁.gpr, and15] at z
  refine WP.ite (decide ((args 7).toNat % 16 = 0)) z ?_ ?_
  · intro m16
    -- `128 ≤ n_len`.
    refine WP.seq (WP.mono (invCompare_ok hu hu.gate.nArg (limit := 128) (by decide)) fun v ⟨hv, kv, mv, _, cv⟩ => ?_)
    refine WP.ite (!decide ((args 7).toNat < 128)) (by simp only [eval, cv, Option.map_some]) ?_ ?_
    · intro big
      -- `p_len ≤ n_len / 2`.
      refine WP.seq (wp_movS hv.gate.nArg.readSrc fun w₁ W₁ _ => ?_)
      refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun w₂ W₂ => wp_addS rfl fun w₃ W₃ _ => ?_
      have K₃ : Keeps [.eax] v w₃ := (W₁.keeps.trans W₂.keeps).trans W₃.keeps
      have m₃ : w₃.mem = v.mem := by rw [W₃.mem, W₂.mem, W₁.mem]
      have h₃ := hv.rest K₃ (by decide) (by decide) m₃
      have half : (w₃.gpr .eax).toNat = (args 7).toNat / 2 + 1 := by
        rw [W₃.gpr, W₂.gpr, W₁.gpr, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        have := (args 7).isLt
        simp only [Nat.pow_one, show BitVec.toNat (1 : BitVec 32) = 1 from rfl]
        omega
      refine wp_movS h₃.gate.pArg.readSrc fun w₄ W₄ _ => cmpBoth rfl fun w₅ W₅ _ c₅ => WP.block_nil ?_
      have K₅ : Keeps [.ecx] w₃ w₅ := W₄.keeps.trans (W₅.keeps _)
      have m₅ : w₅.mem = w₃.mem := W₅.mem.trans W₄.mem
      have h₅ := h₃.rest K₅ (by decide) (by decide) m₅
      have eax₄ : w₄.gpr .eax = w₃.gpr .eax := W₄.other _ (by decide)
      rw [W₄.gpr, eax₄, half] at c₅
      refine WP.ite (decide ((args 9).toNat < (args 7).toNat / 2 + 1)) c₅ ?_ ?_
      · intro py
        -- `q_len ≤ n_len / 2`.
        refine wp_movS h₅.gate.qArg.readSrc fun w₆ W₆ _ => cmpBoth rfl fun z Z zf cz => WP.block_nil ?_
        have Kz : Keeps [.ecx] w₅ z := W₆.keeps.trans (Z.keeps _)
        have mz : z.mem = w₅.mem := Z.mem.trans W₆.mem
        have eax₆ : w₆.gpr .eax = w₃.gpr .eax := by
          rw [W₆.other _ (by decide), K₅.1 _ (by decide)]
        rw [W₆.gpr, eax₆, half] at cz
        refine ⟨h₅.rest Kz (by decide) (by decide) mz,
          ((((K.mono (by decide)).trans (kv.mono (by decide))).trans (K₃.mono (by decide))).trans
            (K₅.mono (by decide))).trans (Kz.mono (by decide)),
          by rw [mz, m₅, m₃, mv, m], ?_⟩
        rw [cz]
        simp only [Eligible, of_decide_eq_true m16, true_and, of_decide_eq_true py]
        simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at big
        simp only [big, true_and]
      · intro py
        refine WP.mono (reject_ok h₅) fun z ⟨hz, kz, mz, cz⟩ => ?_
        refine ⟨hz, ((((K.mono (by decide)).trans (kv.mono (by decide))).trans (K₃.mono (by decide))).trans
          (K₅.mono (by decide))).trans (kz.mono (by decide)), by rw [mz, m₅, m₃, mv, m], ?_⟩
        rw [cz]
        simp only [Eligible, of_decide_eq_false py, false_and, and_false, decide_false]
    · intro small
      refine WP.mono (reject_ok hv) fun z ⟨hz, kz, mz, cz⟩ => ?_
      refine ⟨hz, ((K.mono (by decide)).trans (kv.mono (by decide))).trans (kz.mono (by decide)),
        by rw [mz, mv, m], ?_⟩
      rw [cz]
      simp only [Bool.not_eq_false', decide_eq_true_eq] at small
      simp only [Eligible, show ¬ 128 ≤ (args 7).toNat by omega, false_and, and_false, decide_false]
  · intro no
    refine WP.mono (reject_ok hu) fun z ⟨hz, kz, mz, cz⟩ => ?_
    refine ⟨hz, (K.mono (by decide)).trans (kz.mono (by decide)), by rw [mz, m], ?_⟩
    rw [cz]
    simp only [Eligible, of_decide_eq_false no, false_and, decide_false]

end VG.Proof.Rsa.X86.CrtValuesRt
