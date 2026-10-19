module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightLoad
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcBlock
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

def lowBlock : List Instr := loadAccumulator ++
  VG.Impl.Bignum.AArch64.BlockedRedc.nsLoad ++
  ([.adds .x .x1 .x7 .x7] : List Instr) ++
  (List.range 8).flatMap VG.Impl.Bignum.AArch64.BlockedRedc.tail

/-- The low half of an eight-by-eight product is emitted, retaining the
high half in registers. No inverse property is used. -/
theorem lowBlock_ok {s : State} {B : Addr} {Z eQ eT eN : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h7 : s.gpr .x7 = 0) (hQ : eQ + 64 ≤ Z) (hT : eT + 64 ≤ Z)
    (hN : eN + 64 ≤ Z) (hQT : eQ + 64 ≤ eT ∨ eT + 64 ≤ eQ)
    (hNT : eN + 64 ≤ eT ∨ eT + 64 ≤ eN) :
    WP isa (.block lowBlock) s fun t =>
      wv t.mem B eT 8 + (2 ^ 64) ^ 8 * blockValue (accumulator t) =
        wv s.mem B eT 8 + wv s.mem B eQ 8 * wv s.mem B eN 8 ∧
      t.c = false ∧ t.gpr .x16 = off B (eT + 64) ∧
      Outside B eT 64 s.mem t.mem ∧ Keep blockRegs s t := by
  rewrite [lowBlock, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (loadAccumulator_ok hs h16 hT) fun a ⟨⟨hav, ham, _⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (nsLoad_ok (hs.congr ka.wr) ((ka.gpr .x17 (by decide)).trans h17) hN)
    fun b ⟨⟨hbn, hbm, _⟩, kb⟩ => ?_
  have kab := ka.trans kb
  apply WP.block_append
  refine WP.mono (clearCarry_ok ((kab.gpr .x7 (by decide)).trans h7))
    fun c ⟨⟨hcc, hcm⟩, kc⟩ => ?_
  have kabc := kab.trans kc
  have cm := hcm.trans (hbm.trans ham)
  have hacc : blockValue (accumulator c) = wv s.mem B eT 8 := by
    rw [keep_accumulator kc (by decide), keep_accumulator kb (by decide)]
    exact (blockValue_congr hav).trans (blockValue_words s.mem B eT)
  have hin : blockValue (accumulator c) + (2 ^ 64) ^ 8 * c.c.toNat = 0 + wv s.mem B eT 8 := by
    rw [hacc, hcc]
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  have hr : 2 ^ (64 * 8) = (2 ^ 64) ^ 8 := Nat.pow_mul 2 64 8
  refine WP.mono (tailTile_ok (hs.congr kabc.wr)
    ((kabc.gpr .x8 (by decide)).trans h8) ((kabc.gpr .x16 (by decide)).trans h16)
    ((kabc.gpr .x17 (by decide)).trans h17) ((kabc.gpr .x7 (by decide)).trans h7)
    hQ hT (by omega) hQT (by omega) hin (by decide)
    (Nat.lt_of_lt_of_le (wv_lt s.mem B eT 8) (Nat.le_of_eq hr))) fun t ⟨hI, hc⟩ => ?_
  have hn : blockValue (operand c (word c.mem B eN)) = wv s.mem B eN 8 := by
    rw [keep_operand kc (by decide), hcm]
    have n0 := congrArg (fun m : Mem => word m B eN) hbm
    rw [n0]
    exact (blockValue_congr hbn).trans ((blockValue_words a.mem B eN).trans
      (congrArg (fun m : Mem => wv m B eN 8) ham))
  have hq := congrArg (fun m : Mem => wv m B eQ 8) cm
  have hv : wv t.mem B eT 8 + (2 ^ 64) ^ 8 *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
      (0 + wv s.mem B eT 8) + wv c.mem B eQ 8 *
        blockValue (operand c (word c.mem B eN)) :=
    (congrArg (fun r => wv t.mem B eT 8 + r *
      (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat)) hr.symm).trans
      (hI.value.trans (congrArg (· + wv c.mem B eQ 8 *
        blockValue (operand c (word c.mem B eN))) hin))
  have hplain := zero_carry_value (congrArg Bool.toNat hc) hv
  have hp := (congrArg (· * blockValue (operand c (word c.mem B eN))) hq).trans
    (congrArg (wv s.mem B eQ 8 * ·) hn)
  refine ⟨hplain.trans ((congrArg (· + wv c.mem B eQ 8 *
    blockValue (operand c (word c.mem B eN))) (Nat.zero_add _)).trans
      (congrArg (wv s.mem B eT 8 + ·) hp)), hc, hI.ptr, ?_,
    (kabc.trans hI.keep).mono (by decide)⟩
  intro x hx
  exact (hI.frame x hx).trans (congrArg (fun m : Mem => m x) cm)

end VG.Proof.Bignum.AArch64.ProductEight
