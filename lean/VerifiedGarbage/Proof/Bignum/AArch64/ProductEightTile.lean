module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightBlock
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

abbrev tileRegs := blockRegs ++ [.x10, .x17]

theorem combine {r lo hi carry middle oldLo oldHi prod pending : Nat}
    (hl : lo + r * middle = oldLo + prod)
    (hh : hi + r * carry = middle + oldHi + pending) :
    (lo + r * hi) + r * r * carry = (oldLo + r * oldHi) + prod + r * pending := by
  have h := congrArg (r * ·) hh
  grind

theorem nextOperand_ok {s : State} {B : Addr} {eN : Nat}
    (h17 : s.gpr .x17 = off B eN) :
    WP isa (.block [.addImm .x .x17 .x17 64]) s fun t =>
      (t.gpr .x17 = off B (eN + 64) ∧ t.mem = s.mem) ∧ Keep [.x17] s t := by
  refine WP.keep [.x17] ?_ rfl rfl rfl
  brun [h17]

theorem offBlock_eq : VG.Impl.Bignum.AArch64.ProductEight.offBlock =
    lowBlock ++ (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true ++
      ([.adc .x .x10 .x7 .x7] : List Instr) ++ VG.Impl.Bignum.AArch64.BlockedRedc.asStore) ++
      ([.addImm .x .x17 .x17 64] : List Instr) := by
  simp only [VG.Impl.Bignum.AArch64.ProductEight.offBlock, lowBlock, loadAccumulator,
    List.append_assoc]

/-- Complete eight-by-eight multiply-accumulate, including a pending carry
from the previous column and the carry for the next column. -/
theorem offBlock_ok {s : State} {B : Addr} {Z eQ eT eN : Nat} {p : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h7 : s.gpr .x7 = 0) (h10 : s.gpr .x10 = BitVec.ofNat 64 p.toNat)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 128 ≤ Z) (hN : eN + 64 ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 128 ≤ eQ)
    (hNT : eN + 64 ≤ eT ∨ eT + 128 ≤ eN) :
    WP isa (.block VG.Impl.Bignum.AArch64.ProductEight.offBlock) s fun t =>
      wv t.mem B eT 16 + ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * (t.gpr .x10).toNat =
        wv s.mem B eT 16 + wv s.mem B eQ 8 * wv s.mem B eN 8 + (2 ^ 64) ^ 8 * p.toNat ∧
      (t.gpr .x10).toNat ≤ 1 ∧ t.gpr .x16 = off B (eT + 64) ∧
      t.gpr .x17 = off B (eN + 64) ∧ Outside B eT 128 s.mem t.mem ∧ Keep tileRegs s t := by
  have hnw := hs.nowrap
  rewrite [offBlock_eq, List.append_assoc]
  apply WP.block_append
  refine WP.mono (lowBlock_ok hs h8 h16 h17 h7 hQ (by omega) hN (by omega) (by omega))
    fun a ⟨hal, _, ha16, hao, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (finishBlock_ok (hs.congr ka.wr) ha16 (by omega)
    ((ka.gpr .x10 (by decide)).trans h10) ((ka.gpr .x7 (by decide)).trans h7))
    fun b ⟨hbh, hbc, hbo, kb⟩ => ?_
  have kab := ka.trans kb
  refine WP.mono (nextOperand_ok ((kab.gpr .x17 (by decide)).trans h17))
    fun t ⟨⟨ht17, htm⟩, kt⟩ => ?_
  have haHi := hao.wv (d := eT + 64) (k := 8) (by omega) (by omega)
  have hbLo := hbo.wv (d := eT) (k := 8) (by omega) (by omega)
  have hbFull := wv_radix_add b.mem B eT 8 8
  have hsFull := wv_radix_add s.mem B eT 8 8
  have hplain := combine hal (hbh.trans (congrArg
    (fun z => blockValue (accumulator a) + z + p.toNat) haHi))
  have hplain' : wv b.mem B eT 16 + ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * (b.gpr .x10).toNat =
      wv s.mem B eT 16 + wv s.mem B eQ 8 * wv s.mem B eN 8 + (2 ^ 64) ^ 8 * p.toNat := by
    calc
      _ = (wv a.mem B eT 8 + (2 ^ 64) ^ 8 * wv b.mem B (eT + 64) 8) +
          ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * (b.gpr .x10).toNat :=
        congrArg (· + ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * (b.gpr .x10).toNat)
          (hbFull.trans (congrArg (· + (2 ^ 64) ^ 8 * wv b.mem B (eT + 64) 8) hbLo))
      _ = _ := hplain.trans (congrArg (fun z => z + wv s.mem B eQ 8 * wv s.mem B eN 8 +
        (2 ^ 64) ^ 8 * p.toNat) hsFull.symm)
  have ht10 := kt.gpr .x10 (by decide)
  refine ⟨?_, ?_, (kt.gpr .x16 (by decide)).trans ((kb.gpr .x16 (by decide)).trans ha16),
    ht17, ?_, (kab.trans kt).mono (by decide)⟩
  · exact ((congrArg (fun m : Mem => wv m B eT 16 +
      ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * (t.gpr .x10).toNat) htm).trans
        (congrArg (fun z => wv b.mem B eT 16 + ((2 ^ 64) ^ 8 * (2 ^ 64) ^ 8) * z)
          (congrArg BitVec.toNat ht10))).trans hplain'
  · exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat ht10)) hbc
  · have ho := (hao.mono (by omega) (by omega)).trans (hbo.mono (o' := eT) (n' := 128) (by omega) (by omega))
    intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (ho x hx)

end VG.Proof.Bignum.AArch64.ProductEight
