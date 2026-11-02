module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA public-key operation on RISC-V: the output

`output_ok`: the result's `k` bytes from array 4, most significant first,
masked by the validity mask in `s9`, to `out`, and the return value.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_le)

theorem mask_byte (x : BitVec 8) (b : Bool) :
    ((x.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) =
      if b then x else 0 := by
  cases b
  · simp
  · simp only [ite_true, show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega_arith

theorem read1_setWidth (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  show (m.read (a + 1) 0 ++ m a).toNat % 2 ^ 64 = (m a).toNat % 2 ^ 64
  rw [BitVec.toNat_append]
  simp [Mem.read]

/-- `output`, the mask of `b` in `s9`: `out`'s (`s10`) byte `i` is array 4's
byte `k - 1 - i` if `b`, else 0; `a0` is 1 if `b`, else 0. -/
theorem output_ok {s : State} {B O : Addr} {Z w k : Nat} {b : Bool} (hs : Scr s B Z) (ho : Scr s O k)
    (h7 : s.gpr .a7 = off B (slot w 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .s11 = BitVec.ofNat 64 k) (h10 : s.gpr .s10 = off O 0)
    (h9 : s.gpr .s9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hZ : slot w 8 ≤ Z)
    (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa output s fun t =>
      ((∀ i < k, t.mem (off O i) = if b then s.mem (off B (slot w 4 + (k - 1 - i))) else 0) ∧
        Outside O 0 k s.mem t.mem ∧ t.gpr .a0 = BitVec.ofNat 64 (if b then 1 else 0)) ∧
      Keep [.s0, .a0, .t4, .t3, .t5] s t := by
  have hnw := hs.nowrap
  have hno := ho.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e4 := e 4; have e8 := e 8
  unfold output
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .t4) (by decide) h7 h5 4) fun s₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t3, .t5] (Q := fun s₂ => s₂.gpr .t4 = off B (slot w 4 + (k - 1)) ∧
    s₂.gpr .t3 = off O 0 ∧ s₂.gpr .t5 = BitVec.ofNat 64 k ∧ s₂.mem = s₁.mem)
    (by brun [a4, (k1.gpr (r := .s11) (by decide)).trans h11, (k1.gpr (r := .s10) (by decide)).trans h10, off_add,
        add_ofNat_zero]
        rw [off_sub _ (by omega_arith)]; congr 2; omega_arith) (by rfl) (by rfl)) fun s₂ ⟨⟨b4, b3, b5, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have h9' : s₂.gpr .s9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) :=
    (k12.gpr (by decide)).trans h9
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t4 = off B (slot w 4 + (k - 1) - j) ∧ t.gpr .t3 = off O j ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = if b then s.mem (off B (slot w 4 + (k - 1 - i))) else 0) ∧
      Keep [.s0, .t4, .t3, .t5] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .b .s0 .t4 0, .logic .and .s0 .s0 .s9,
      .store .b .s0 .t3 0, .addi .t3 .t3 1, .addi .t4 .t4 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t3, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4]; rfl, b3, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k12.mono (by decide)⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ?_)
  · have hrd : InRegions (t.rd ++ t.wr) (off B (slot w 4 + (k - 1) - j)) 1 := by
      rw [tk.2.1, tk.2.2]; exact hs.ld (show slot w 4 + (k - 1) - j + 1 ≤ Z by have := slot_le (w := w) (j := 4) (by decide); omega_arith)
    have hst : WP isa (.block [.load .b .s0 .t4 0, .logic .and .s0 .s0 .s9, .store .b .s0 .t3 0, .addi .t3 .t3 1,
        .addi .t4 .t4 (-1), .addi .t5 .t5 (-1)]) t fun t' => t' = ((({ ((t.write .s0
          ((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64)).write .s0
          ((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)))) with
          mem := t.mem.write (off O j) 1 (((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) } :
            State).write .t3 (off O (j + 1))).write .t4
              (off B (slot w 4 + (k - 1) - j) - BitVec.ofNat 64 1)).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t4, t3, (tk.gpr (r := .s9) (by decide)).trans h9, hrd, add_ofNat_zero,
        (ho.congr tk.2.2).st (d := j) (n := 1) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem O (d := j) (((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
      (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) (by omega_arith)
    have harr : t.mem (off B (slot w 4 + (k - 1) - j)) = s.mem (off B (slot w 4 + (k - 1) - j)) := by
      refine tout _ (Or.inr ?_)
      by_contra hc
      have := hsep (off B (slot w 4 + (k - 1) - j)) (by omega_arith)
      rw [show ofs B (off B (slot w 4 + (k - 1) - j)) = slot w 4 + (k - 1) - j from
        Mem.sub_ofNat_toNat B (by have := slot_le (w := w) (j := 4) (by decide); omega_arith)] at this
      have := slot_le (w := w) (j := 4) (by decide)
      omega_arith
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub _ (by have := slot_le (w := w) (j := 4) (by decide); unfold slot hdrBytes at *; omega_arith),
        show slot w 4 + (k - 1) - j - 1 = slot w 4 + (k - 1) - (j + 1) by omega_arith]
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
    · intro i hi
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
      · rw [write1_self, read1_setWidth, show slot w 4 + (k - 1 - i) = slot w 4 + (k - 1) - i by omega_arith, ← harr]
        exact mask_byte _ b
    · refine Keep.trans' tk (Keep.mono (rs := [Reg.s0] ++ [Reg.s0] ++ [] ++ [Reg.t3] ++ [Reg.t4] ++ [Reg.t5])
        (rs' := [.s0, .t4, .t3, .t5]) ?_ (by decide))
      exact (((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.mem _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)
  · refine WP.mono (WP.keep [.a0] (Q := fun t' => t'.gpr .a0 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      t'.mem = t.mem) ?_ (by rfl) (by rfl)) fun t' ⟨⟨a3, tm⟩, k5⟩ => ⟨⟨by rw [tm]; exact tb, by rw [tm]; exact tout, a3⟩,
        (tk.trans k5).mono (by decide)⟩
    brun [(tk.gpr (r := .s9) (by decide)).trans h9, exec_li]
    cases b <;> decide

end VG.Proof.Bignum.RISCV64.Pub
