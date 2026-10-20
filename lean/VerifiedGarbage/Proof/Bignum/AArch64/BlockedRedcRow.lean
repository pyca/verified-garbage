module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Capture the incoming carry and fetch one previously canceled coefficient. -/
def tailHead (i : Nat) : List Instr :=
  [.adc .x .x1 .x7 .x7, ld .x27 .x8 (8 * i)]

def tailMid : List Instr :=
  [.adc .x .x1 .x1 .x7, st .x19 .x16, next .x16]

theorem tail_eq (i : Nat) : VG.Impl.Bignum.AArch64.BlockedRedc.tail i =
    tailHead i ++ VG.Impl.Bignum.AArch64.BlockedRedc.lowChain ++
      tailMid ++ VG.Impl.Bignum.AArch64.BlockedRedc.highChain := by
  simp only [VG.Impl.Bignum.AArch64.BlockedRedc.tail, tailHead, tailMid, List.append_assoc,
    List.cons_append, List.nil_append]

theorem tailHead_ok {s : State} {B : Addr} {Z eQ i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hi : i < 8) :
    WP isa (.block (tailHead i)) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 s.c.toNat ∧
       t.gpr .x27 = word s.mem B (eQ + 8 * i) ∧ t.mem = s.mem ∧ t.c = s.c) ∧
      Keep [.x1, .x27] s t := by
  have enc : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := ⟨by omega, by omega⟩
  refine WP.keep [.x1, .x27] ?_ rfl rfl rfl
  brun [tailHead, h8, h7, enc, hs.ld hQ]
  simp only [zero_add64]

theorem tailMid_ok {s : State} {B : Addr} {Z eT : Nat} {c : Bool}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (h7 : s.gpr .x7 = 0)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 c.toNat) (hT : eT + 8 ≤ Z) :
    WP isa (.block tailMid) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 (c.toNat + s.c.toNat) ∧
       t.gpr .x16 = off B (eT + 8) ∧
       t.mem = s.mem.writeW (off B eT) (s.gpr .x19) ∧ t.c = s.c) ∧
      Keep [.x1, .x16] s t := by
  refine WP.keep [.x1, .x16] ?_ rfl rfl rfl
  brun [tailMid, h16, h7, h1, hs.st hT]
  simp only [add_zero64, BitVec.ofNat_add]


/-- A complete scheduled row emits one word and shifts the full remaining
value into the register block and carry. The statement holds for arbitrary
operands and inverse values; cancellation is a separate property. -/
theorem tailRow_ok {s : State} {B : Addr} {Z eQ eT eN i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h7 : s.gpr .x7 = 0) (hQ : eQ + 8 * i + 8 ≤ Z) (hT : eT + 8 ≤ Z)
    (hN : eN + 8 ≤ Z) (hi : i < 8) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.tail i)) s fun t => ∃ lo : Word,
      lo.toNat + 2 ^ 64 * (blockValue (accumulator t) + (2 ^ 64) ^ 8 * t.c.toNat) =
        blockValue (accumulator s) + (word s.mem B (eQ + 8 * i)).toNat *
          blockValue (operand s (word s.mem B eN)) + (2 ^ 64) ^ 8 * s.c.toNat ∧
      t.mem = s.mem.writeW (off B eT) lo ∧ t.gpr .x16 = off B (eT + 8) ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++
        VG.Impl.Bignum.AArch64.BlockedRedc.tt ++ ([.x1, .x27, .x16] : List Reg)) s t := by
  rewrite [tail_eq]
  rewrite [List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (tailHead_ok hs h8 h7 hQ hi)
    fun a ⟨⟨ha1, haQ, haM, haC⟩, ka⟩ => ?_
  have a17 := (ka.gpr .x17 (by decide)).trans h17
  apply WP.block_append
  refine WP.mono (lowChain_ok (hs.congr ka.wr) a17 hN)
    fun b ⟨⟨hbC, hbV, hbH, hbM⟩, kb⟩ => ?_
  have kab := ka.trans kb
  have b16 := (kab.gpr .x16 (by decide)).trans h16
  have b7 := (kab.gpr .x7 (by decide)).trans h7
  have b1 := (kb.gpr .x1 (by decide)).trans ha1
  apply WP.block_append
  refine WP.mono (tailMid_ok (hs.congr kab.wr) b16 b7 b1 hT)
    fun c ⟨⟨hc1, hc16, hcM, hcC⟩, kc⟩ => ?_
  refine WP.mono (highChain_ok c) fun t ⟨⟨htC, htV, htM⟩, kt⟩ => ?_
  have kbc := kb.trans kc
  have hhi := highTerms_value (word a.mem B eN)
    ((kc.gpr .x13 (by decide)).trans (hbH 0 (by decide)))
    ((kc.gpr .x14 (by decide)).trans (hbH 1 (by decide)))
    ((kc.gpr .x28 (by decide)).trans (hbH 2 (by decide)))
    ((kc.gpr .x30 (by decide)).trans (hbH 3 (by decide)))
    (kbc.gpr .x27 (by decide)) (kbc.gpr .x5 (by decide))
    (kbc.gpr .x6 (by decide)) (kbc.gpr .x9 (by decide)) (kbc.gpr .x11 (by decide))
  have hl := (chain_result_value hbC hbV).trans (Nat.add_zero _)
  have hh := (chain_result_value htC htV).trans (Nat.add_zero _)
  rw [hhi] at hh
  have hx1 : (c.gpr .x1).toNat = s.c.toNat + b.c.toNat := by
    rw [hc1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := Bool.toNat_le s.c; have := Bool.toNat_le b.c; omega)
  have hv := shifted_value c
  rw [keep_accumulator kc (by decide), kc.gpr .x19 (by decide), hx1] at hv
  have hp := block_product_value a (word a.mem B eN)
  have hrow := chained_row_value
    (b := 2 ^ 64) (r := (2 ^ 64) ^ 8) (a := blockValue (accumulator a))
    (q := (a.gpr .x27).toNat) (n := blockValue (operand a (word a.mem B eN)))
    (low := blockValue (lowProduct a (word a.mem B eN)))
    (high := blockValue (highProduct a (word a.mem B eN)))
    (aLow := blockValue (accumulator b)) (cLow := b.c.toNat)
    (shifted := blockValue (shifted c)) (aHigh := blockValue (accumulator t))
    (cHigh := t.c.toNat) (cin := s.c.toNat) (lo := (b.gpr .x19).toNat)
    hl hv hh hp
  have haAcc := congrArg blockValue (keep_accumulator ka (by decide))
  have haQN := congrArg BitVec.toNat haQ
  have haN0 := congrArg (fun m : Mem => word m B eN) haM
  have haOp := (keep_operand ka (by decide) (word a.mem B eN)).trans
    (congrArg (operand s) haN0)
  have haNV := congrArg blockValue haOp
  have hrow' := hrow.trans (by
    rewrite [haAcc, haQN, haNV]
    rfl)
  refine ⟨b.gpr .x19, hrow', ?_, (kt.gpr .x16 (by decide)).trans hc16,
    ((kab.trans kc).trans kt).mono (by decide)⟩
  exact htM.trans (hcM.trans (congrArg (fun m : Mem => m.writeW (off B eT) (b.gpr .x19))
    (hbM.trans haM)))

end VG.Proof.Bignum.AArch64.BlockedRedc
