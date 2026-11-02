module

public import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.Crt
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: the recombination

* `xb_ok`: the base of `X`'s array `j`, from `s6` and `s11`;
* `exportM2_ok`: `m₂`'s `q_len` bytes, most significant first, from `Q`'s
  array 4 into `X`'s array 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.Crt VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

theorem xb_cons (rd : Reg) (j : Nat) : xb rd (j + 1) = xb rd j ++ ([.add rd rd .s11] : List Instr) := by
  simp only [xb, List.replicate_succ', List.cons_append]

/-- `xb rd j`: the base of `X`'s array `j`, `X` at `s6` and its arrays' size
in `s11`. -/
theorem xb_ok {t : State} {BX : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .s11)
    (h6 : t.gpr .s6 = BX) (h11 : t.gpr .s11 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (xb rd j)) t fun t' =>
      (t'.gpr rd = off BX (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    simp only [xb, List.replicate_zero]
    apply WP.of_runBlock
    refine ⟨t.write rd (off BX (slot w 0)), ?_, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
    rw [runBlock_cons, exec_addi_nat (show hdrBytes < 2048 by decide), runStep_some, runBlock_nil, h6]
    simp [off, slot]
  | j + 1 => by
    rw [xb_cons, WP.block_append_iff]
    refine WP.mono (xb_ok hrd h6 h11 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr (r := .s11) (by simpa using Ne.symm hrd)).trans h11]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

/-- `exportM2`: `m₂`'s `L = q_len` bytes (the header's word `oQLen`) from
`Q`'s array 4 (at `BQ`), most significant first, into `X`'s array 1. -/
theorem exportM2_ok {s : State} {BQ BX : Addr} {ZQ ZX wQ wX L : Nat} (hq : Scr s BQ ZQ) (hx : Scr s BX ZX)
    (h7 : s.gpr .a7 = off BQ (slot wQ 0)) (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (wQ + 2)))
    (h6 : s.gpr .s6 = BX) (h11 : s.gpr .s11 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hL : word s.mem BX oQLen = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLq : L ≤ 8 * wQ) (hLx : L ≤ 8 * wX) (hZQ : slot wQ 24 ≤ ZQ) (hZX : slot wX 8 ≤ ZX)
    (hsep : ∀ x, ofs BX x < ZX → ZQ ≤ ofs BQ x) :
    WP isa exportM2 s fun t =>
      ((∀ i < L, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
        Outside BX (slot wX 1) L s.mem t.mem) ∧ Keep [.s0, .t3, .t4, .t5] s t := by
  have hnq := hq.nowrap
  have hnx := hx.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have e4 := e wQ 4; have e8 := e wQ 24; have x1 := e wX 1; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  unfold exportM2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) h7 h5 4) fun s₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t5] (Q := fun s₂ => s₂.gpr .t4 = off BQ (slot wQ 4 + (L - 1)) ∧
    s₂.gpr .t5 = BitVec.ofNat 64 L ∧ s₂.mem = s₁.mem) ?_ (by rfl) (by rfl)) fun s₂ ⟨⟨b4, b5, m2⟩, k2⟩ => ?_
  · have hL' : s₁.mem.readW (off BX 56) 64 = BitVec.ofNat 64 L := by rw [m1]; exact hL
    brun [a4, (k1.gpr (r := .s6) (by decide)).trans h6, oQLen, (hx.congr k1.2.2).ld (show 56 + 8 ≤ ZX by omega_arith),
      (hx.congr k1.2.2).al8 (show 56 + 8 ≤ ZX by omega_arith) (by decide), hL', off_add, BitVec.add_zero]
    rw [off_sub _ (by omega_arith)]; congr 2; omega_arith
  refine WP.mono (xb_ok (rd := .t3) (by decide) ((k1.trans k2).gpr (by decide) |>.trans h6)
    ((k1.trans k2).gpr (by decide) |>.trans h11) 1) fun s₃ ⟨⟨b3, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have b4' : s₃.gpr .t4 = off BQ (slot wQ 4 + (L - 1)) := (k3.gpr (by decide)).trans b4
  have b5' : s₃.gpr .t5 = BitVec.ofNat 64 L := (k3.gpr (by decide)).trans b5
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .t4 = off BQ (slot wQ 4 + (L - 1) - j) ∧ t.gpr .t3 = off BX (slot wX 1 + j) ∧
      Outside BX (slot wX 1) j s.mem t.mem ∧
      (∀ i < j, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
      Keep [.s0, .t3, .t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .b .s0 .t4 0, .store .b .s0 .t3 0, .addi .t3 .t3 1,
      .addi .t4 .t4 (-1)] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := L) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t3, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4']; rfl, by rw [b3]; rfl, by rw [m3, m2, m1]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_arith), k13.mono (by decide)⟩ b5') fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off BQ (slot wQ 4 + (L - 1) - j)) 1 := by
    rw [tk.2.1, tk.2.2]; exact hq.ld (show slot wQ 4 + (L - 1) - j + 1 ≤ ZQ by omega_arith)
  have hst : WP isa (.block [.load .b .s0 .t4 0, .store .b .s0 .t3 0, .addi .t3 .t3 1,
      .addi .t4 .t4 (-1), .addi .t5 .t5 (-1)]) t fun t' => t' = (((({ (t.write .s0
        ((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off BX (slot wX 1 + j)) 1
          (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .t3 (off BX (slot wX 1 + j + 1))).write .t4
            (off BQ (slot wQ 4 + (L - 1) - j) - BitVec.ofNat 64 1)).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [t4, t3, hrd, (hx.congr tk.2.2).st (d := slot wX 1 + j) (n := 1) (by omega_arith), add_ofNat_zero]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem BX (d := slot wX 1 + j)
    (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) (by omega_arith)
  have harr : t.mem (off BQ (slot wQ 4 + (L - 1) - j)) = s.mem (off BQ (slot wQ 4 + (L - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off BQ (slot wQ 4 + (L - 1) - j)) (by omega_arith)
    rw [show ofs BQ (off BQ (slot wQ 4 + (L - 1) - j)) = slot wQ 4 + (L - 1) - j from
      ofs_off0 BQ (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp; rw [Nat.add_assoc], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub _ (by omega_arith), show slot wQ 4 + (L - 1) - j - 1 = slot wQ 4 + (L - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 BX (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, show slot wQ 4 + (L - 1 - i) = slot wQ 4 + (L - 1) - i by omega_arith, ← harr, read_one']
  · exact Keep.trans' tk ((((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

end VG.Proof.Bignum.RISCV64.Crt
