module

public import VerifiedGarbage.Impl.Bignum.X86_64.Fill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! `tileFill` writes only `rax` and the flags. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem tileFill_one_ok (s : State) {i : Instr}
    (hi : i = .movImm64 .rax 0 ∨ i = .alu .add .rax (.imm 1)) :
    WP isa (.block [i]) s fun t => t.mem = s.mem ∧ Keep [.rax] s t := by
  rcases hi with rfl | rfl <;>
  · refine WP.keep [.rax] (Q := fun t => t.mem = s.mem) ?_ rfl
    xrun []

theorem tileFill_ok (s : State) (a b : Nat) :
    WP isa (.block (tileFill a b)) s fun t => t.mem = s.mem ∧ Keep [.rax] s t := by
  unfold tileFill
  induction a generalizing s with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    induction b generalizing s with
    | zero => exact WP.block_nil ⟨rfl, Keep.refl _ _⟩
    | succ b ih =>
      rw [List.replicate_succ, show (Instr.alu .add .rax (.imm 1) :: List.replicate b _) =
        [.alu .add .rax (.imm 1)] ++ List.replicate b _ from rfl, WP.block_append_iff]
      exact WP.mono (tileFill_one_ok s (Or.inr rfl)) fun u ⟨mu, ku⟩ =>
        WP.mono (ih u) fun t ⟨mt, kt⟩ => ⟨mt.trans mu, (ku.trans kt).mono (by simp)⟩
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, show (Instr.movImm64 .rax 0 :: (List.replicate a _ ++ _)) =
      [.movImm64 .rax 0] ++ (List.replicate a _ ++ _) from rfl, WP.block_append_iff]
    exact WP.mono (tileFill_one_ok s (Or.inl rfl)) fun u ⟨mu, ku⟩ =>
      WP.mono (ih u) fun t ⟨mt, kt⟩ => ⟨mt.trans mu, (ku.trans kt).mono (by simp)⟩

end VG.Proof.Bignum.X86_64
