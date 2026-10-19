module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Init
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Ffdh.Generation
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitValues
import VerifiedGarbage.Proof.Framework.Omega

/-! # Native validation branches and invalid-input output for FFDH generation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation

def cleared (m : Mem) (B : Addr) : Mem :=
  (((m.writeW B (0 : BitVec 64)).writeW (off B 8) (0 : BitVec 64)).writeW
    (off B 16) (0 : BitVec 64)).writeW (off B 24) (0 : BitVec 64)

theorem clear_ok {s : State} {B : Addr} (scr : Scr s B 128) (hdi : s.gpr .rdi = B) :
    WP isa clear s fun t => t.gpr .rax = 0 ∧ t.mem = cleared s.mem B := by
  have hstore : ∀ j < 4, InRegions s.wr (off B (8 * j)) 8 :=
    fun j hj => scr.st (by omega_using [hj])
  unfold clear cleared
  xrun [field, State.ea, off, BitVec.ofInt_natCast, hdi,
    hstore 0 (by decide), hstore 1 (by decide), hstore 2 (by decide), hstore 3 (by decide)]
  simp only [Nat.reduceMul, BitVec.add_zero]
  rfl

theorem cleared_words (m : Mem) (B : Addr) :
    Spec.Rsa.wordsAt (cleared m B) B 4 = List.replicate 4 (0 : BitVec 64) := by
  have hm : cleared m B = initialized m B 0 := by
    simp only [cleared, initialized, Spec.Ffdh.parameterAttempts, Spec.Ffdh.parameterEntropy,
      Nat.zero_mul, Nat.zero_add, Nat.reduceDiv, Nat.mul_zero]
    rfl
  rw [hm]
  have hw := initialized_words m B 0
  simp only [Spec.Ffdh.parameterAttempts, Spec.Ffdh.parameterEntropy, Nat.zero_mul,
    Nat.zero_add, Nat.reduceDiv, Nat.mul_zero] at hw
  change Spec.Rsa.wordsAt (initialized m B 0) B 4 =
    [BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 0]
  exact hw

private theorem compared_keep {s t : State} {r : Reg}
    (k : Keep [r] s t) (hr : t.gpr r = s.gpr r) : Keep [] s t := by
  refine ⟨fun q _ => ?_, k.2⟩
  by_cases he : q = r
  · subst he; exact hr
  · exact k.gpr (by simpa only [List.mem_singleton] using he)

theorem lower_guard (s : State) :
    WP isa (.block [.alu .cmp .rsi (.imm 512)]) s fun t =>
      (eval .b t = some (decide ((s.gpr .rsi).toNat < 512)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    eval .b t = some (decide ((s.gpr .rsi).toNat < 512)) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ =>
        ⟨⟨he, hm⟩, compared_keep k hr⟩
  have h : BitVec.signExtend 64 (512 : BitVec 32) = (512 : BitVec 64) := by decide
  xrun [h, eval]
  rfl

theorem upper_guard (s : State) :
    WP isa (.block [.alu .cmp .rsi (.imm 8193)]) s fun t =>
      (eval .ae t = some (decide (8193 ≤ (s.gpr .rsi).toNat)) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rsi] (Q := fun t =>
    eval .ae t = some (decide (8193 ≤ (s.gpr .rsi).toNat)) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ =>
        ⟨⟨he, hm⟩, compared_keep k hr⟩
  have h : BitVec.signExtend 64 (8193 : BitVec 32) = (8193 : BitVec 64) := by decide
  xrun [h, eval]
  change (!decide ((s.gpr .rsi).toNat < 8193)) = decide (8193 ≤ (s.gpr .rsi).toNat)
  by_cases hb : 8193 ≤ (s.gpr .rsi).toNat
  · simp only [show ¬(s.gpr .rsi).toNat < 8193 by omega_using [hb], decide_false,
      Bool.not_false, hb, decide_true]
  · simp only [show (s.gpr .rsi).toNat < 8193 by omega_using [hb], decide_true,
      Bool.not_true, hb, decide_false]

theorem generator_guard (s : State) (n : BitVec 32) :
    WP isa (.block [.alu32 .cmp .rdx (.imm n)]) s fun t =>
      (eval .e t = some (((s.gpr .rdx).setWidth 32) == n) ∧ t.mem = s.mem) ∧ Keep [] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    eval .e t = some (((s.gpr .rdx).setWidth 32) == n) ∧ t.mem = s.mem ∧
      t.gpr .rdx = s.gpr .rdx) ?_ rfl) fun t ⟨⟨he, hm, hr⟩, k⟩ =>
        ⟨⟨he, hm⟩, compared_keep k hr⟩
  xrun [eval]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  bv_omega

theorem generator_guard_nat (s : State) (n : Nat) (hn : n < 2 ^ 32) :
    WP isa (.block [.alu32 .cmp .rdx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      (eval .e t = some (decide (((s.gpr .rdx).setWidth 32).toNat = n)) ∧ t.mem = s.mem) ∧
        Keep [] s t := by
  have he : (((s.gpr .rdx).setWidth 32) == BitVec.ofNat 32 n) =
      decide (((s.gpr .rdx).setWidth 32).toNat = n) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact WP.mono (generator_guard s (BitVec.ofNat 32 n)) fun _ ⟨⟨hg, hm⟩, k⟩ =>
    ⟨⟨hg.trans (congrArg some he), hm⟩, k⟩

end VG.Proof.Ffdh.X86_64.Generation
