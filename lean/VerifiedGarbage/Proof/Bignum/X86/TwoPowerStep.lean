module

public import VerifiedGarbage.Impl.Bignum.X86.TwoPower
public import VerifiedGarbage.Proof.Bignum.X86.TwoPowerMath
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! One masked native rotation retains the input index and all memory. -/

@[expose] public section
namespace VG.Proof.Bignum.X86.TwoPower
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.TwoPower

private theorem bit_ok {j : Nat} (hj : j < 5) {s : State} {x : BitVec 32} (input : s.gpr .ecx = x) :
    WP isa (.block (bit j)) s fun t =>
      t.gpr .ebx = (x >>> j) &&& 1 ∧ t.mem = s.mem ∧ Keeps [.ebx] s t := by
  unfold bit
  by_cases zero : j = 0
  · subst j
    simp only [ite_true, List.append_nil, List.cons_append, List.nil_append]
    refine wp_movS rfl fun u U _ => wp_logicS (Or.inl rfl) rfl fun t T => WP.block_nil ?_
    exact ⟨by rw [T.gpr, U.gpr, input, BitVec.ushiftRight_zero]; rfl,
      T.mem.trans U.mem, U.keeps.trans T.keeps⟩
  · simp only [zero, ite_false, List.cons_append, List.nil_append]
    refine wp_movS rfl fun u U _ => wp_shr (by omega) fun v V _ =>
      wp_logicS (Or.inl rfl) rfl fun t T => WP.block_nil ?_
    exact ⟨by rw [T.gpr, V.gpr, U.gpr, input]; rfl,
      T.mem.trans (V.mem.trans U.mem), (U.keeps.trans V.keeps).trans T.keeps⟩

theorem step_ok {j : Nat} (hj : j < 5) {s : State} {x y : BitVec 32}
    (input : s.gpr .ecx = x) (value : s.gpr .eax = y) :
    WP isa (.block (step j)) s fun t =>
      t.gpr .eax = rotateStep j x y ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have shift : 1 ≤ 32 - 2 ^ j ∧ 32 - 2 ^ j ≤ 31 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide
  unfold step
  refine WP.block_append (WP.mono (bit_ok hj input) ?_)
  rintro u ⟨bit, mem, K⟩
  have old : u.gpr .eax = y := (K.1 .eax (by decide)).trans value
  refine wp_movS rfl fun a A _ => wp_subS rfl fun b B _ => wp_movS rfl fun c C _ =>
    wp_ror shift fun d D => wp_logicS (Or.inr rfl) rfl fun e E =>
      wp_logicS (Or.inl rfl) rfl fun f F => wp_logicS (Or.inr rfl) rfl fun t T => WP.block_nil ?_
  have mask : b.gpr .edx = 0 - ((x >>> j) &&& 1) := by
    rw [B.gpr, A.gpr, A.other .ebx (by decide), bit]
  have saved : c.gpr .ebx = y := by rw [C.gpr, B.other .eax (by decide), A.other .eax (by decide), old]
  have rotated : d.gpr .eax = y.rotateRight (32 - 2 ^ j) := by
    rw [D.gpr, C.other .eax (by decide), B.other .eax (by decide), A.other .eax (by decide), old]
  refine ⟨?_, ?_, ?_⟩
  · rw [T.gpr, F.gpr, E.gpr, rotated, D.other .ebx (by decide), saved,
      E.other .edx (by decide), D.other .edx (by decide), C.other .edx (by decide), mask,
      F.other .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide), saved]
    change ((y.rotateRight (32 - 2 ^ j) ^^^ y) &&& (0 - ((x >>> j) &&& 1))) ^^^ y = _
    exact BitVec.xor_comm _ _
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem, mem]
  · exact (((((((K.mono (by decide)).trans (A.keeps.mono (by decide))).trans
      (B.keeps.mono (by decide))).trans (C.keeps.mono (by decide))).trans
      (D.keeps.mono (by decide))).trans (E.keeps.mono (by decide))).trans
      (F.keeps.mono (by decide))).trans (T.keeps.mono (by decide))

theorem step_input_ok {j : Nat} (hj : j < 5) {s : State} {x y : BitVec 32}
    (input : s.gpr .ecx = x) (value : s.gpr .eax = y) :
    WP isa (.block (step j)) s fun t =>
      t.gpr .eax = rotateStep j x y ∧ t.gpr .ecx = x ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .edx] s t :=
  WP.mono (step_ok hj input value) fun _ ⟨v, m, K⟩ => ⟨v, (K.1 .ecx (by decide)).trans input, m, K⟩

end VG.Proof.Bignum.X86.TwoPower
