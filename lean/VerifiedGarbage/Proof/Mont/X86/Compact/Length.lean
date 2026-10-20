module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Prepared public widths for paired-word compact multiplication -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem doubles_ok (r : Reg) (k : Nat) (s : State) :
    WP isa (.block (List.replicate k (.alu .add r (.reg r)))) s fun t =>
      (t.gpr r).toNat = (s.gpr r).toNat * 2 ^ k % 2 ^ 32 ∧ t.mem = s.mem ∧ Keeps [r] s t := by
  induction k generalizing s with
  | zero => exact WP.block_nil ⟨by simp only [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (s.gpr r).isLt], rfl, Keeps.refl _ _⟩
  | succ k ih =>
    rw [List.replicate_succ]
    refine wp_addS rfl fun a A _ => ?_
    refine WP.mono (ih a) ?_
    rintro t ⟨value, M, K⟩
    refine ⟨?_, M.trans A.mem, A.keeps.trans K⟩
    rw [value, A.gpr, BitVec.toNat_add, Nat.mod_mul_mod, Nat.add_mul, ← Nat.mul_two,
      Nat.mul_assoc, ← Nat.pow_succ]

theorem lenTimes_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32}
    (hw : Ws s W L) (ha : Args s W L A) (base : (A 0).toNat = W.toNat)
    {r t : Reg} (headerFit : 52 ≤ L) (k : Nat) :
    WP isa (.block (Compact.lenTimes r t k)) s fun u =>
      (u.gpr r).toNat = w32 s.mem W 48 * 2 ^ (3 + k) % 2 ^ 32 ∧
      u.mem = s.mem ∧ Keeps [r, t] s u := by
  unfold Compact.lenTimes
  rw [WP.block_append_iff]
  refine wp_movS (ha.read 0 (by decide)) fun a B _ => ?_
  have ptr : PtrAt a W t 0 := by
    rw [PtrAt, B.gpr, base, Nat.add_zero, Nat.mod_eq_of_lt]
    have := hw.nowrap
    omega
  refine wp_movS (readSrc_ptr (hw.of_keeps B.keeps) ptr (d := 48) (by omega)) fun b C _ => WP.block_nil ?_
  refine WP.mono (doubles_ok r (3 + k) b) ?_
  rintro u ⟨value, M, K⟩
  refine ⟨?_, M.trans (C.mem.trans B.mem), (B.keeps.mono (by simp)).trans
    ((C.keeps.mono (by simp)).trans (K.mono (by simp)))⟩
  rw [value, C.gpr, B.mem, Nat.zero_add]

end VG.Proof.Mont.X86.Compact
