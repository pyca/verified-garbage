module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: `X`'s arrays and `m₂`'s bytes

`xb_ok`: the base of `X`'s array `j`. `exportM2_ok`: `m₂`'s `q_len` bytes,
most significant first, from `Q`'s array 4 into `X`'s array 1.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem xb_cons (rd : Reg) (j : Nat) : xb rd (j + 1) = xb rd j ++ ([.add rd rd .r28] : List Instr) := by
  simp only [xb, List.replicate_succ', List.cons_append]

/-- `xb rd j`, `X`'s array 0 at `r27` and its arrays' size in `r28`. -/
theorem xb_ok {t : State} {B : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .r0) (hrd28 : rd ≠ .r28)
    (h27 : t.gpr .r27 = off B (slot w 0)) (h28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (xb rd j)) t fun t' =>
      (t'.gpr rd = off B (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    apply WP.of_runBlock
    simp only [xb, List.replicate_zero, runBlock_cons, exec_addi (show Reg.r27 ≠ .r0 by decide)
      (show 0 < 2 ^ 15 by decide), runStep_some, runBlock_nil, BitVec.add_zero, h27]
    exact ⟨_, rfl, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
  | j + 1 => by
    rw [xb_cons, WP.block_append_iff]
    refine WP.mono (xb_ok hrd hrd28 h27 h28 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr .r28 (by simpa using Ne.symm hrd28)).trans h28]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_arith]

/-- `exportM2`, `Q`'s working space at `BQ` (`r10`, `r29`), `X`'s at `BX` (`r23`,
`r27`, `r28`) apart from it, and `q_len = L` in the header: `X`'s array 1's
first `L` bytes := `Q`'s array 4's first `L`, reversed. -/
theorem exportM2_ok {s : State} {BQ BX : Addr} {ZQ ZX wQ wX L : Nat} (hq : Scr s BQ ZQ) (hx : Scr s BX ZX)
    (h10 : s.gpr .r10 = off BQ (slot wQ 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wQ + 2)))
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) (hL : word s.mem BX oQLen = BitVec.ofNat 64 L)
    (hL1 : 1 ≤ L) (hLq : L ≤ 8 * wQ) (hLx : L ≤ 8 * wX) (hZQ : slot wQ 8 ≤ ZQ) (hZX : slot wX 8 ≤ ZX)
    (hsep : ∀ x, ofs BX x < ZX → ZQ ≤ ofs BQ x) :
    WP isa exportM2 s fun t =>
      ((∀ i < L, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
        Outside BX (slot wX 1) L s.mem t.mem) ∧ Keep [.r0, .r15, .r16, .r17] s t := by
  have hnq := hq.nowrap
  have hnx := hx.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have e4 := e wQ 4; have e8 := e wQ 8; have x1 := e wX 1; have x8 := e wX 8
  have hh : hdrBytes = 256 := rfl
  unfold exportM2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a15, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15, .r17] (Q := fun s₂ => s₂.gpr .r15 = off BQ (slot wQ 4 + (L - 1)) ∧
    s₂.gpr .r17 = BitVec.ofNat 64 L ∧ s₂.mem = s₁.mem) ?_ (by decide)) fun s₂ ⟨⟨b15, b17, m2⟩, k2⟩ => ?_
  · have hL' : s₁.mem.readW (off BX 56) 64 = BitVec.ofNat 64 L := by rw [m1]; exact hL
    prun [a15, (k1.gpr .r23 (by decide)).trans h23, oQLen, (hx.congr k1.wr).ld (show 56 + 8 ≤ ZX by omega_arith), hL',
      off_add, BitVec.add_zero]
    rw [off_sub1 _ (by omega_arith)]; congr 2; omega_arith
  refine WP.mono (xb_ok (rd := .r16) (by decide) (by decide) ((k1.trans k2).gpr _ (by decide) |>.trans h27)
    ((k1.trans k2).gpr _ (by decide) |>.trans h28) 1) fun s₃ ⟨⟨b16, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  have b15' : s₃.gpr .r15 = off BQ (slot wQ 4 + (L - 1)) := (k3.gpr _ (by decide)).trans b15
  have b17' : s₃.gpr .r17 = BitVec.ofNat 64 L := (k3.gpr _ (by decide)).trans b17
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r15 = off BQ (slot wQ 4 + (L - 1) - j) ∧ t.gpr .r16 = off BX (slot wX 1 + j) ∧
      Outside BX (slot wX 1) j s.mem t.mem ∧
      (∀ i < j, t.mem (off BX (slot wX 1 + i)) = s.mem (off BQ (slot wQ 4 + (L - 1 - i)))) ∧
      Keep [.r0, .r15, .r16, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := L) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t15, t16, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b15']; rfl, by rw [b16]; rfl, by rw [m3, m2, m1]; exact Outside.refl _ _ _ _,
      fun _ h => absurd h (by omega_arith), k13.mono⟩ b17') fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hrd : InRegions (t.rd ++ t.wr) (off BQ (slot wQ 4 + (L - 1) - j)) 1 := by
    rw [tk.rd, tk.wr]; exact hq.ld (show slot wQ 4 + (L - 1) - j + 1 ≤ ZQ by omega_arith)
  have hst : WP isa (.block [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1, .subi .r17 .r17 1]) t fun t' => t' = (((({ (t.write .r0
        ((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64)) with
        mem := t.mem.write (off BX (slot wX 1 + j)) 1
          (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) } :
          State).write .r16 (off BX (slot wX 1 + j + 1))).write .r15
            (off BQ (slot wQ 4 + (L - 1) - j) - BitVec.ofNat 64 1)).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1)) := by
    prun [t15, t16, exec_lbz' (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
      (hx.congr tk.wr).st (d := slot wX 1 + j) (n := 1) (by omega_arith), off_add]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem BX (d := slot wX 1 + j)
    (((t.mem.read (off BQ (slot wQ 4 + (L - 1) - j)) 1).setWidth 64).setWidth 8) (by omega_arith)
  have harr : t.mem (off BQ (slot wQ 4 + (L - 1) - j)) = s.mem (off BQ (slot wQ 4 + (L - 1) - j)) := by
    refine tout _ (Or.inr ?_)
    by_contra hc
    have := hsep (off BQ (slot wQ 4 + (L - 1) - j)) (by omega_arith)
    rw [show ofs BQ (off BQ (slot wQ 4 + (L - 1) - j)) = slot wQ 4 + (L - 1) - j from
      Mem.sub_ofNat_toNat BQ (by omega_arith)] at this
    omega_arith
  refine ⟨⟨?_, by gsimp; rw [Nat.add_assoc], ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; rw [off_sub1 _ (by omega_arith), show slot wQ 4 + (L - 1) - j - 1 = slot wQ 4 + (L - 1) - (j + 1) by omega_arith]
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 BX (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self, show slot wQ 4 + (L - 1 - i) = slot wQ 4 + (L - 1) - i by omega_arith, ← harr]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, Mem.read]; rw [BitVec.toNat_append]; simpa using (t.mem _).isLt
  · exact tk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
      (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Bignum.PPC64LE.Crt
