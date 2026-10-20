module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Layout

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The cancellation prefix saves its coefficient in the word being eliminated. -/
def cancelHead (i : Nat) : List Instr :=
  [.mul .x .x27 .x19 .x15, st .x27 .x8 (8 * i), movi .x1 0]

def cancelMid : List Instr := [.adc .x .x1 .x1 .x7]

theorem cancel_eq (i : Nat) : VG.Impl.Bignum.AArch64.BlockedRedc.cancelBasic i =
    cancelHead i ++ VG.Impl.Bignum.AArch64.BlockedRedc.lowChain ++
      cancelMid ++ VG.Impl.Bignum.AArch64.BlockedRedc.highChain := by
  simp only [VG.Impl.Bignum.AArch64.BlockedRedc.cancelBasic, cancelHead, cancelMid,
    List.append_assoc]

theorem cancelHead_ok {s : State} {B : Addr} {Z eQ i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hi : i < 8) :
    WP isa (.block (cancelHead i)) s fun t =>
      (t.gpr .x1 = 0 ∧ t.gpr .x27 = s.gpr .x19 * s.gpr .x15 ∧
       t.mem = s.mem.writeW (off B (eQ + 8 * i)) (s.gpr .x19 * s.gpr .x15)) ∧
      Keep [.x1, .x27] s t := by
  have enc : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := ⟨by omega, by omega⟩
  refine WP.keep [.x1, .x27] ?_ rfl rfl rfl
  brun [cancelHead, h8, enc, hs.st hQ]

theorem cancelMid_ok {s : State} (h1 : s.gpr .x1 = 0) (h7 : s.gpr .x7 = 0) :
    WP isa (.block cancelMid) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 s.c.toNat ∧ t.mem = s.mem ∧ t.c = s.c) ∧
      Keep [.x1] s t := by
  refine WP.keep [.x1] ?_ rfl rfl rfl
  brun [cancelMid, h1, h7]
  simp only [zero_add64]

/-- The two chains used for cancellation conserve the complete value before
invoking the inverse property. This lemma also covers malformed inverses. -/
theorem cancelChains_ok {s : State} {B : Addr} {Z eN : Nat}
    (hs : Scr s B Z) (h17 : s.gpr .x17 = off B eN)
    (h1 : s.gpr .x1 = 0) (h7 : s.gpr .x7 = 0) (hN : eN + 8 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.lowChain ++
      cancelMid ++ VG.Impl.Bignum.AArch64.BlockedRedc.highChain)) s fun t => ∃ lo : Word,
      lo.toNat + 2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
        blockValue (accumulator s) + (s.gpr .x27).toNat *
          blockValue (operand s (word s.mem B eN)) ∧
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
  have kbc := kb.trans kc
  have hhi := highTerms_value (word s.mem B eN)
    ((kc.gpr .x13 (by decide)).trans (hbH 0 (by decide)))
    ((kc.gpr .x14 (by decide)).trans (hbH 1 (by decide)))
    ((kc.gpr .x28 (by decide)).trans (hbH 2 (by decide)))
    ((kc.gpr .x30 (by decide)).trans (hbH 3 (by decide)))
    (kbc.gpr .x27 (by decide)) (kbc.gpr .x5 (by decide))
    (kbc.gpr .x6 (by decide)) (kbc.gpr .x9 (by decide)) (kbc.gpr .x11 (by decide))
  have hl := (chain_result_value hbC hbV).trans (Nat.add_zero _)
  have hh := (chain_result_value htC htV).trans (Nat.add_zero _)
  rw [hhi] at hh
  have hx1 : (c.gpr .x1).toNat = 0 + b.c.toNat := by
    rw [hc1, BitVec.toNat_ofNat]
    have := Bool.toNat_le b.c
    omega
  have hv := shifted_value c
  rw [keep_accumulator kc (by decide), kc.gpr .x19 (by decide), hx1] at hv
  have hp := block_product_value s (word s.mem B eN)
  have hrow := chained_row_value hl hv hh hp
  have hrow' := hrow.trans ((congrArg (fun z => blockValue (accumulator s) +
    (s.gpr .x27).toNat * blockValue (operand s (word s.mem B eN)) + z)
    (Nat.mul_zero ((2 ^ 64) ^ 8))).trans (Nat.add_zero _))
  exact ⟨b.gpr .x19, hrow', htM.trans (hcM.trans hbM),
    ((kb.trans kc).trans kt).mono (by decide)⟩

/-- One cancellation row, with the exact coefficient store and register frame.
The modulus word must be disjoint from the coefficient slot. -/
theorem cancelRow_ok {s : State} {B : Addr} {Z eQ eN i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hN : eN + 8 ≤ Z) (hi : i < 8)
    (hsep : eQ + 8 * i + 8 ≤ eN ∨ eN + 8 ≤ eQ + 8 * i) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.cancelBasic i)) s fun t => ∃ lo : Word,
      lo.toNat + 2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
        blockValue (accumulator s) + (s.gpr .x19 * s.gpr .x15).toNat *
          blockValue (operand s (word s.mem B eN)) ∧
      t.c = false ∧
      t.mem = s.mem.writeW (off B (eQ + 8 * i)) (s.gpr .x19 * s.gpr .x15) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ ([.x1, .x27] : List Reg)) s t := by
  rewrite [cancel_eq, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (cancelHead_ok hs h8 hQ hi) fun a ⟨⟨ha1, haQ, haM⟩, ka⟩ => ?_
  refine WP.mono (cancelChains_ok (hs.congr ka.wr)
    ((ka.gpr .x17 (by decide)).trans h17) ha1
    ((ka.gpr .x7 (by decide)).trans h7) hN) fun t ⟨lo, hv, hm, kt⟩ => ?_
  have hmem : word a.mem B eN = word s.mem B eN :=
    (congrArg (fun m : Mem => word m B eN) haM).trans
      ((writeW_outside s.mem B _ (by have := hs.nowrap; omega)).word
        (by omega) (by have := hs.nowrap; omega))
  have haAcc := congrArg blockValue (keep_accumulator ka (by decide))
  have haQN := congrArg BitVec.toNat haQ
  have haOp := (keep_operand ka (by decide) (word a.mem B eN)).trans
    (congrArg (operand s) hmem)
  have haNV := congrArg blockValue haOp
  have hv' := hv.trans (by
    rewrite [haAcc, haQN, haNV]
    rfl)
  have hc0 := cancel_carry_zero (by decide : 0 < 2 ^ 64)
    (blockValue_lt (accumulator s)) (s.gpr .x19 * s.gpr .x15).isLt
    (blockValue_lt (operand s (word s.mem B eN))) hv'
  have hc : t.c = false := by
    cases he : t.c with
    | false => rfl
    | true => simp only [he, Bool.toNat_true] at hc0; omega
  exact ⟨lo, hv', hc, hm.trans haM, (ka.trans kt).mono (by decide)⟩

/-- With a valid inverse, a cancellation row exactly divides the updated
integer by the word radix, retaining the complete high carry. -/
theorem cancelRow_exact {s : State} {B : Addr} {Z eQ eN i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hN : eN + 8 ≤ Z) (hi : i < 8)
    (hsep : eQ + 8 * i + 8 ≤ eN ∨ eN + 8 ≤ eQ + 8 * i)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .x15).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.cancelBasic i)) s fun t =>
      2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
        blockValue (accumulator s) + (s.gpr .x19 * s.gpr .x15).toNat *
          blockValue (operand s (word s.mem B eN)) ∧
      t.c = false ∧
      t.mem = s.mem.writeW (off B (eQ + 8 * i)) (s.gpr .x19 * s.gpr .x15) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ ([.x1, .x27] : List Reg)) s t := by
  refine WP.mono (cancelRow_ok hs h8 h17 h7 hQ hN hi hsep) fun t ⟨lo, hv, hc, hm, kt⟩ => ?_
  have hz : lo.toNat = 0 := congrArg BitVec.toNat (cancel_low hinv hv)
  refine ⟨?_, hc, hm, kt⟩
  exact (Nat.zero_add _).symm.trans ((congrArg (· + 2 ^ 64 *
    (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat)) hz.symm).trans hv)

end VG.Proof.Bignum.AArch64.BlockedRedc
