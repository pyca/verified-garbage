module

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastWord
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCancel
public import VerifiedGarbage.Impl.Bignum.AArch64.BlockedRedcFast
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFastMath

@[expose] public section
namespace VG.Proof.Bignum.AArch64.BlockedRedcFast
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

/-- Execution and frames need no inverse condition. The arithmetic identity
uses precisely the inverse condition already required by Montgomery correctness. -/
theorem cancelChains_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN)
    (h1 : s.gpr .x1 = 0) (h7 : s.gpr .x7 = 0) (hN : eN + 8 ≤ Z)
    (hq : s.gpr .x27 = s.gpr .x19 * s.gpr .x15) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedcFast.lowChain ++
      cancelMid ++ VG.Impl.Bignum.AArch64.BlockedRedc.highChain)) s fun t =>
      (((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
          blockValue (accumulator s) + (s.gpr .x27).toNat *
            blockValue (operand s (word s.mem B eN))) ∧
      t.mem = s.mem ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ ([.x1] : List Reg)) s t := by
  rewrite [List.append_assoc]
  apply WP.block_append
  refine WP.mono (lowChain_ok hs h17 hN) fun b ⟨⟨hbC, hbV, hbH, hbM⟩, kb⟩ => ?_
  apply WP.block_append
  refine WP.mono (cancelMid_ok ((kb.gpr .x1 (by decide)).trans h1)
    ((kb.gpr .x7 (by decide)).trans h7)) fun c ⟨⟨hc1, hcM, hcC⟩, kc⟩ => ?_
  refine WP.mono (highChain_ok c) fun t ⟨⟨htC, htV, htM⟩, kt⟩ => ?_
  refine ⟨?_, htM.trans (hcM.trans hbM), ((kb.trans kc).trans kt).mono (by decide)⟩
  intro hinv
  have kbc := kb.trans kc
  have hhi := highTerms_value (word s.mem B eN)
    ((kc.gpr .x13 (by decide)).trans (hbH 0 (by decide)))
    ((kc.gpr .x14 (by decide)).trans (hbH 1 (by decide)))
    ((kc.gpr .x28 (by decide)).trans (hbH 2 (by decide)))
    ((kc.gpr .x30 (by decide)).trans (hbH 3 (by decide)))
    (kbc.gpr .x27 (by decide)) (kbc.gpr .x5 (by decide))
    (kbc.gpr .x6 (by decide)) (kbc.gpr .x9 (by decide)) (kbc.gpr .x11 (by decide))
  have hl := zeroLow_chain_value hbC hbV
  have hp0 : lowProduct s (word s.mem B eN) = BlockedRedc.lowProduct s (word s.mem B eN) := by
    funext i
    by_cases hi : i = 0
    · subst i
      exact (canceled_product (s.gpr .x19) (s.gpr .x15) (word s.mem B eN) hinv).symm.trans
        (congrArg (· * word s.mem B eN) hq.symm)
    · simp only [lowProduct, hi, ↓reduceIte]
  rw [hp0] at hl
  have hh := (chain_result_value htC htV).trans (Nat.add_zero _)
  rw [hhi] at hh
  have hx1 : (c.gpr .x1).toNat = b.c.toNat := by
    rw [hc1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := Bool.toNat_le b.c; omega)
  have hv := shifted_value (zeroLow c)
  have hacc : accumulator (zeroLow c) = accumulator (zeroLow b) := by
    rw [zeroLow_accumulator, zeroLow_accumulator, keep_accumulator kc (by decide)]
  rw [zeroLow_shifted, hacc] at hv
  change 0 + 2 ^ 64 * blockValue (shifted c) =
    blockValue (accumulator (zeroLow b)) + (2 ^ 64) ^ 8 * (c.gpr .x1).toNat at hv
  rw [Nat.zero_add, hx1] at hv
  have hp := block_product_value s (word s.mem B eN)
  omega_using [hl, hv, hh, hp]

theorem cancel_eq (i : Nat) : VG.Impl.Bignum.AArch64.BlockedRedcFast.cancel i =
    cancelHead i ++ VG.Impl.Bignum.AArch64.BlockedRedcFast.lowChain ++
      cancelMid ++ VG.Impl.Bignum.AArch64.BlockedRedc.highChain := by
  simp only [VG.Impl.Bignum.AArch64.BlockedRedcFast.cancel, VG.Impl.Bignum.AArch64.BlockedRedc.cancel,
    VG.Impl.Bignum.AArch64.BlockedRedcFast.lowChain, cancelHead, cancelMid,
    List.append_assoc]

theorem cancelRow_ok {s : State} {B : Addr} {Z eQ eN i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hN : eN + 8 ≤ Z) (hi : i < 8)
    (hsep : eQ + 8 * i + 8 ≤ eN ∨ eN + 8 ≤ eQ + 8 * i) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedcFast.cancel i)) s fun t =>
      (((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
          blockValue (accumulator s) + (s.gpr .x19 * s.gpr .x15).toNat *
            blockValue (operand s (word s.mem B eN)) ∧ t.c = false) ∧
      t.mem = s.mem.writeW (off B (eQ + 8 * i)) (s.gpr .x19 * s.gpr .x15) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ ([.x1, .x27] : List Reg)) s t := by
  rewrite [cancel_eq, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (cancelHead_ok hs h8 hQ hi) fun a ⟨⟨ha1, haQ, haM⟩, ka⟩ => ?_
  have hq : a.gpr .x27 = a.gpr .x19 * a.gpr .x15 := by
    rw [ka.gpr .x19 (by decide), ka.gpr .x15 (by decide)]
    exact haQ
  refine WP.mono (cancelChains_ok (hs.congr ka.wr)
    ((ka.gpr .x17 (by decide)).trans h17) ha1
    ((ka.gpr .x7 (by decide)).trans h7) hN hq) fun t ⟨hv, hm, kt⟩ => ?_
  refine ⟨?_, hm.trans haM, (ka.trans kt).mono (by decide)⟩
  intro hinv
  have hmem : word a.mem B eN = word s.mem B eN :=
    (congrArg (fun m : Mem => word m B eN) haM).trans
      ((writeW_outside s.mem B _ (by have := hs.nowrap; omega)).word
        (by omega) (by have := hs.nowrap; omega))
  have hinv' : ((word a.mem B eN).toNat * (a.gpr .x15).toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem, ka.gpr .x15 (by decide)]
    exact hinv
  have hv' := hv hinv'
  have haOp := (keep_operand ka (by decide) (word a.mem B eN)).trans
    (congrArg (operand s) hmem)
  rw [keep_accumulator ka (by decide), haQ, haOp] at hv'
  have hc0 := cancel_carry_zero (lo := 0) (by decide : 0 < 2 ^ 64)
    (blockValue_lt (accumulator s)) (s.gpr .x19 * s.gpr .x15).isLt
    (blockValue_lt (operand s (word s.mem B eN))) ((Nat.zero_add _).trans hv')
  refine ⟨hv', ?_⟩
  cases he : t.c with
  | false => rfl
  | true => simp only [he, Bool.toNat_true] at hc0; omega

end VG.Proof.Bignum.AArch64.BlockedRedcFast
