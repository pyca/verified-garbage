module

import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRowMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcTile
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcFinish

/-! ### `Bignum.AArch64.ProductEightColumns`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.ProductEightTile`, which only this module used -/

section

/-! ### `Bignum.AArch64.ProductEightBlock`, which only this module used -/

section

/-! ### `Bignum.AArch64.ProductEightLoad`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

def loadAccumulator : List Instr :=
  VG.Impl.Bignum.AArch64.BlockedRedc.aa.zipIdx.map fun (r,i) => ld r .x16 (8*i)

theorem loadAccumulator_ok {s : State} {B : Addr} {Z eT : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z) :
    WP isa (.block loadAccumulator) s fun t =>
      ((∀ i < 8, accumulator t i = word s.mem B (eT + 8 * i)) ∧
       t.mem = s.mem ∧ t.c = s.c) ∧
      Keep VG.Impl.Bignum.AArch64.BlockedRedc.aa s t := by
  have hld : ∀ i < 8, InRegions (s.rd ++ s.wr) (off B (eT + 8 * i)) 8 :=
    fun i hi => hs.ld (by omega_using [hT, hi])
  refine WP.keep VG.Impl.Bignum.AArch64.BlockedRedc.aa ?_ (by decide) (by decide) (by decide)
  have hcode : loadAccumulator =
    [ld .x19 .x16 0, ld .x20 .x16 8, ld .x21 .x16 16, ld .x22 .x16 24,
     ld .x23 .x16 32, ld .x24 .x16 40, ld .x25 .x16 48, ld .x26 .x16 56] := rfl
  brun [hcode, h16, hs.ld (show eT + 8 ≤ Z by omega_using [hT]), hld 0 (by decide),
    hld 1 (by decide), hld 2 (by decide), hld 3 (by decide), hld 4 (by decide),
    hld 5 (by decide), hld 6 (by decide), hld 7 (by decide)]
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem clearCarry_ok {s : State} (h7 : s.gpr .x7 = 0) :
    WP isa (.block [.adds .x .x1 .x7 .x7]) s fun t =>
      (t.c = false ∧ t.mem = s.mem) ∧ Keep [.x1] s t := by
  refine WP.keep [.x1] ?_ rfl rfl rfl
  brun [h7]

end VG.Proof.Bignum.AArch64.ProductEight

end

end


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
    hQ hT (by omega_using [hN]) hQT (by omega_using [hNT]) hin (by decide)
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

end

end


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
  refine WP.mono (lowBlock_ok hs h8 h16 h17 h7 hQ (by omega_using [hT]) hN (by omega_using [hQT]) (by omega_using [hNT]))
    fun a ⟨hal, _, ha16, hao, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (finishBlock_ok (hs.congr ka.wr) ha16 (by omega_using [hT])
    ((ka.gpr .x10 (by decide)).trans h10) ((ka.gpr .x7 (by decide)).trans h7))
    fun b ⟨hbh, hbc, hbo, kb⟩ => ?_
  have kab := ka.trans kb
  refine WP.mono (nextOperand_ok ((kab.gpr .x17 (by decide)).trans h17))
    fun t ⟨⟨ht17, htm⟩, kt⟩ => ?_
  have haHi := hao.wv (d := eT + 64) (k := 8) (by omega_using []) (by omega_using [hT, hnw])
  have hbLo := hbo.wv (d := eT) (k := 8) (by omega_using []) (by omega_using [hT, hnw])
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
  · have ho := (hao.mono (by omega_using []) (by omega_using [])).trans (hbo.mono (o' := eT) (n' := 128) (by omega_using []) (by omega_using []))
    intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans (ho x hx)

end VG.Proof.Bignum.AArch64.ProductEight

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc

abbrev productColumnRegs := tileRegs ++ [.x15]

structure ProductColumnInv (s : State) (B : Addr) (eQ eT eN k j : Nat) (t : State) : Prop where
  value : wv t.mem B eT (8 * (k + 1)) +
      2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (t.gpr .x10).toNat =
    wv s.mem B eT (8 * (k + 1)) + wv s.mem B eQ 8 * wv s.mem B eN (8 * j)
  carry : (t.gpr .x10).toNat ≤ 1
  ptrT : t.gpr .x16 = off B (eT + 64 * j)
  ptrN : t.gpr .x17 = off B (eN + 64 * j)
  frame : Outside B eT (64 * (j + 1)) s.mem t.mem
  keep : Keep productColumnRegs s t

theorem decrement_ok {s : State} :
    WP isa (.block [.subImm .x .x15 .x15 1]) s fun t =>
      (t.gpr .x15 = s.gpr .x15 - BitVec.ofNat 64 1 ∧ t.mem = s.mem) ∧
        Keep [.x15] s t := by
  refine WP.keep [.x15] ?_ rfl rfl rfl
  brun []

theorem bit_word {x : Word} (h : x.toNat ≤ 1) :
    ∃ p : Bool, x = BitVec.ofNat 64 p.toNat := by
  by_cases hz : x.toNat = 0
  · exact ⟨false, BitVec.eq_of_toNat_eq hz⟩
  · exact ⟨true, BitVec.eq_of_toNat_eq (by simpa using (show x.toNat = 1 by omega_arith))⟩

/-- Compose overlapping two-block products without losing the pending carry. -/
theorem productColumnStep_ok {s t : State} {B : Addr} {Z eQ eT eN j k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hj : j < k) (hI : ProductColumnInv s B eQ eT eN k j t) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.offBlock ++
      ([.subImm .x .x15 .x15 1] : List Instr))) t fun u =>
      ProductColumnInv s B eQ eT eN k (j + 1) u ∧
        u.gpr .x15 = t.gpr .x15 - BitVec.ofNat 64 1 := by
  have hnw := hs.nowrap
  obtain ⟨p, hp⟩ := bit_word hI.carry
  have q := hI.frame.wv (d := eQ) (k := 8) (by omega_arith) (by omega_arith)
  have n := hI.frame.wv (d := eN + 64 * j) (k := 8) (by omega_arith) (by omega_arith)
  apply WP.block_append
  refine WP.mono (offBlock_ok (hs.congr hI.keep.wr)
    ((hI.keep.gpr .x8 (by decide)).trans h8) hI.ptrT hI.ptrN
    ((hI.keep.gpr .x7 (by decide)).trans h7) hp
    hQ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun a ⟨hav, hac, ha16, ha17, hao, ka⟩ => ?_
  refine WP.mono (decrement_ok (s := a)) fun u ⟨⟨hu15, hum⟩, ku⟩ => ?_
  have hf := wv_window_delta (n := 8 * (k + 1)) (j := 8 * j) (k := 16)
    (by omega_arith : eT + 8 * (8 * (k + 1)) ≤ 2 ^ 64) (by omega_arith)
    (show Outside B (eT + 8 * (8 * j)) (8 * 16) t.mem a.mem from
      by simpa only [show 8 * (8 * j) = 64 * j by omega_arith] using hao)
  have havAligned := hav
  have hoff : eT + 64 * j = eT + 8 * (8 * j) := by omega_arith
  rewrite [hoff] at havAligned
  have he := window_lift hf havAligned
  have hc : (t.gpr .x10).toNat = p.toNat := by
    rw [hp]
    cases p <;> rfl
  have hv := column_value hI.value
    (show wv a.mem B eT (8 * (k + 1)) +
        2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (2 ^ 64) ^ 8 * (a.gpr .x10).toNat =
      wv t.mem B eT (8 * (k + 1)) +
        2 ^ (64 * (8 * j)) * (wv s.mem B eQ 8 * wv s.mem B (eN + 64 * j) 8) +
        2 ^ (64 * (8 * j)) * (2 ^ 64) ^ 8 * (t.gpr .x10).toNat from by
      simpa only [q, n, hc, Nat.mul_assoc] using he)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ((hI.keep.trans ka).trans ku).mono (by decide)⟩,
    hu15.trans (congrArg (· - BitVec.ofNat 64 1) (ka.gpr .x15 (by decide)))⟩
  · rewrite [hum, ku.gpr .x10 (by decide), pow_blocks_succ, wv_blocks_succ s.mem B eN j]
    exact hv
  · exact Nat.le_trans (Nat.le_of_eq (congrArg BitVec.toNat (ku.gpr .x10 (by decide)))) hac
  · exact ((ku.gpr .x16 (by decide)).trans ha16).trans (congrArg (off B) (by omega_arith))
  · exact ((ku.gpr .x17 (by decide)).trans ha17).trans (congrArg (off B) (by omega_arith))
  · have ho : Outside B (eT + 64 * j) 128 t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hum).trans (hao x hx)
    exact (hI.frame.mono (by omega_arith) (by omega_arith)).trans (ho.mono (by omega_arith) (by omega_arith))

/-- All columns of an eight-limb multiplication row. -/
theorem productColumns_ok {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hk : 0 < k) (hk' : k < 2 ^ 64) :
    WP isa (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) s
      (ProductColumnInv s B eQ eT eN k k) := by
  have h0 : ProductColumnInv s B eQ eT eN k 0 s := by
    refine ⟨?_, ?_, h16, h17, Outside.refl _ _ _ _, Keep.refl _ _⟩
    · simp only [h10, show (0 : Word).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, wv, Nat.zero_add]
    · rw [h10]; exact Nat.zero_le 1
  unfold countLoop
  exact wp_countdown hk' hk (ProductColumnInv s B eQ eT eN k)
    (fun j hj t hI _ => productColumnStep_ok hs h8 h7 hQ hT hN hQT hNT hj hI) h0 h15

/-- With the outer-row bound, the final pending carry is zero. The bound
also admits the all-zero multiplier. -/
theorem productColumns_bounded {s : State} {B : Addr} {Z eQ eT eN k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ) (h7 : s.gpr .x7 = 0)
    (h10 : s.gpr .x10 = 0)
    (h16 : s.gpr .x16 = off B eT) (h17 : s.gpr .x17 = off B eN)
    (h15 : s.gpr .x15 = BitVec.ofNat 64 k)
    (hQ : eQ + 64 ≤ Z) (hT : eT + 64 * (k + 1) ≤ Z) (hN : eN + 64 * k ≤ Z)
    (hQT : eQ + 64 ≤ eT ∨ eT + 64 * (k + 1) ≤ eQ)
    (hNT : eN + 64 * k ≤ eT ∨ eT + 64 * (k + 1) ≤ eN)
    (hk : 0 < k) (hk' : k < 2 ^ 64)
    (hbound : wv s.mem B eT (8 * (k + 1)) ≤ wv s.mem B eN (8 * k)) :
    WP isa (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock) s fun t =>
      ProductColumnInv s B eQ eT eN k k t ∧ t.gpr .x10 = 0 ∧
        wv t.mem B eT (8 * (k + 1)) = wv s.mem B eT (8 * (k + 1)) +
          wv s.mem B eQ 8 * wv s.mem B eN (8 * k) := by
  refine WP.mono (productColumns_ok hs h8 h7 h10 h16 h17 h15 hQ hT hN hQT hNT hk hk')
    fun t hI => ?_
  have hq := wv_lt s.mem B eQ 8
  have hb := wv_lt s.mem B eN (8 * k)
  have hv := hI.value
  have hc := row_carry_zero (radix := (2 ^ 64) ^ 8) (span := 2 ^ (64 * (8 * k)))
    (by decide) hbound (by simpa only [Nat.pow_mul] using hq) hb
    (by simpa only [Nat.mul_comm (2 ^ (64 * (8 * k))), Nat.mul_assoc] using hv)
  have hz : t.gpr .x10 = 0 := BitVec.eq_of_toNat_eq hc
  refine ⟨hI, hz, ?_⟩
  simpa only [hc, Nat.mul_zero, Nat.add_zero] using hv

end VG.Proof.Bignum.AArch64.ProductEight

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.BlockedRedc (wv_blocks_succ)

abbrev rawRegs := productColumnRegs ++ [.x8, .x12]
abbrev productBase (k : Nat) := slot (8 * k) Public.aAcc + 16

structure ProductRowsInv (s : State) (B : Addr) (Z k a b i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep rawRegs s t
  ptr : t.gpr .x8 = off B (slot (8 * k) a + 64 * i)
  frame : Outside B (productBase k) (8 * (16 * k + 2)) s.mem t.mem
  value : wv t.mem B (productBase k) (16 * k + 2) =
    wv s.mem B (slot (8 * k) a) (8 * i) * wv s.mem B (slot (8 * k) b) (8 * k)

theorem rowEnd_ok {s : State} {B : Addr} {e : Nat} (h8 : s.gpr .x8 = off B e) :
    WP isa (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]) s fun t =>
      (t.gpr .x8 = off B (e + 64) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) ∧ Keep [.x8, .x12] s t := by
  refine WP.keep [.x8, .x12] ?_ rfl rfl rfl
  brun [h8]

/-- The eight-limb outer row preserves the complete product, including padding. -/
theorem productRow_ok {s t : State} {B : Addr} {Z k a b i : Nat} {minv : BitVec 64}
    (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (ha : a < 8) (hb : b < 8)
    (hk : k < 2 ^ 56) (hi : i < k)
    (hA : slot (8 * k) a + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) a)
    (hB : slot (8 * k) b + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) b)
    (hI : ProductRowsInv s B Z k a b i t) :
    WP isa (.seq (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b))
      (.seq (countLoop .x15 VG.Impl.Bignum.AArch64.ProductEight.offBlock)
        (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]))) t fun u =>
      ProductRowsInv s B Z k a b (i + 1) u ∧
        u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have hP : productBase k + 8 * (16 * k + 2) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega_arith
  have haZ : slot (8 * k) a + 64 * k ≤ Z := by
    have := slot_le (w := 8 * k) ha
    omega_arith
  have hbZ : slot (8 * k) b + 64 * k ≤ Z := by
    have := slot_le (w := 8 * k) hb
    omega_arith
  have hHt : Hdr t.mem B (8 * k) minv :=
    (Square.scratch_arrays (by simpa only [productBase, show 2 * (8 * k) = 16 * k by omega_arith] using hI.frame)).hdr hH
  refine WP.seq (WP.mono (rowSetup_ok hI.scr
    ((hI.keep.gpr .x0 (by decide)).trans h0) hHt hZ ha hb hk hI.ptr)
    fun v ⟨⟨hv16, hv17, hv15, hv10, hvm⟩, kv⟩ => ?_)
  have hv8 := (kv.gpr .x8 (by decide)).trans hI.ptr
  have hv7 := (kv.gpr .x7 (by decide)).trans ((hI.keep.gpr .x7 (by decide)).trans h7)
  have hq := hI.frame.wv (d := slot (8 * k) a + 64 * i) (k := 8) (by omega_arith) (by omega_arith)
  have hbv := hI.frame.wv (d := slot (8 * k) b) (k := 8 * k) (by omega_arith) (by omega_arith)
  have hbSlice : wv v.mem B (productBase k + 64 * i) (8 * (k + 1)) ≤
      wv v.mem B (slot (8 * k) b) (8 * k) := by
    have hw := wv_window_le t.mem B (productBase k) (16 * k + 2) (8 * i) (8 * (k + 1)) (by omega_arith)
    rw [hI.value] at hw
    have hbnd := row_window_bound (by exact Nat.two_pow_pos _)
      (wv_lt s.mem B (slot (8 * k) a) (8 * i)) hw
    simpa only [hvm, hbv, show 8 * (8 * i) = 64 * i by omega_arith] using hbnd
  refine WP.seq (WP.mono (productColumns_bounded (eT := productBase k + 64 * i) (hI.scr.congr kv.wr) hv8 hv7 hv10 hv16 hv17 hv15
    (by omega_arith) (by omega_arith) hbZ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hbSlice)
    fun v' ⟨hC, _, hcv⟩ => ?_)
  have hv'8 := (hC.keep.gpr .x8 (by decide)).trans hv8
  refine WP.mono (rowEnd_ok hv'8) fun u ⟨⟨hu8, hu12, hum⟩, ku⟩ => ?_
  have hframe := wv_window_delta (n := 16 * k + 2) (j := 8 * i) (k := 8 * (k + 1))
    (by omega_arith : productBase k + 8 * (16 * k + 2) ≤ 2 ^ 64) (by omega_arith)
    (by simpa only [show 8 * (8 * i) = 64 * i by omega_arith,
      show 8 * (8 * (k + 1)) = 64 * (k + 1) by omega_arith] using hC.frame)
  have hcv' := hcv
  rewrite [hvm, hq, hbv] at hcv'
  have hh := hframe
  rewrite [show 8 * (8 * i) = 64 * i by omega_arith, hvm] at hh
  have he := row_value hh hcv' hI.value
  refine ⟨⟨hI.scr.congr (ku.wr.trans (hC.keep.wr.trans kv.wr)),
    (((hI.keep.trans kv).trans hC.keep).trans ku).mono (by decide),
    hu8.trans (congrArg (off B) (by omega_arith)), ?_, ?_⟩, ?_⟩
  · have ho : Outside B (productBase k + 64 * i) (64 * (k + 1)) t.mem u.mem := by
      intro x hx
      exact (congrArg (fun m : Mem => m x) hum).trans
        ((hC.frame x hx).trans (congrArg (fun m : Mem => m x) hvm))
    exact hI.frame.trans (ho.mono (by omega_arith) (by omega_arith))
  · rewrite [hum, wv_blocks_succ]
    exact he
  · exact hu12.trans (congrArg (· - BitVec.ofNat 64 1)
      ((hC.keep.gpr .x12 (by decide)).trans (kv.gpr .x12 (by decide))))

theorem rows_noVec (a b : Nat) :
    (VG.Impl.Bignum.AArch64.ProductEight.rows a b).allInstrs
      (fun i => (vdstOf i).isNone) = true := by
  rfl

/-- Exact full multiplication for every positive supported tile count. -/
theorem productRows_ok {s : State} {B : Addr} {Z k a b : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8 * k) minv) (hZ : slot (8 * k) 8 ≤ Z)
    (h8 : s.gpr .x8 = off B (slot (8 * k) a)) (h12 : s.gpr .x12 = BitVec.ofNat 64 k)
    (ha : a < 8) (hb : b < 8) (hk : 0 < k) (hk' : k < 2 ^ 56)
    (hA : slot (8 * k) a + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) a)
    (hB : slot (8 * k) b + 64 * k ≤ productBase k ∨
      productBase k + 8 * (16 * k + 2) ≤ slot (8 * k) b)
    (hz : wv s.mem B (productBase k) (16 * k + 2) = 0) :
    WP isa (VG.Impl.Bignum.AArch64.ProductEight.rows a b) s fun t =>
      ProductRowsInv s B Z k a b k t ∧ ∀ v, t.v v = s.v v := by
  have hinit : ProductRowsInv s B Z k a b 0 s := by
    refine ⟨hs, Keep.refl _ _, h8, Outside.refl _ _ _ _, ?_⟩
    simpa only [Nat.mul_zero, wv, Nat.zero_mul] using hz
  have hp : WP isa (VG.Impl.Bignum.AArch64.ProductEight.rows a b) s
      (ProductRowsInv s B Z k a b k) :=
    wp_countdown (by omega_arith) hk (ProductRowsInv s B Z k a b)
      (fun i hi t hI _ => productRow_ok h0 h7 hH hZ ha hb hk' hi hA hB hI) hinit h12
  obtain ⟨tr, t, he, ht⟩ := hp
  refine ⟨tr, t, he, ht, fun v => Exec.vec ?_ he⟩
  have hc := rows_noVec a b
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  intro i hi h
  have hn := hc i hi
  rw [h] at hn
  contradiction

end VG.Proof.Bignum.AArch64.ProductEight
