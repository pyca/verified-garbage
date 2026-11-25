module

public import VerifiedGarbage.Impl.X25519.AArch64.Ladder
public import VerifiedGarbage.Proof.Ed25519.AArch64.Pairs
public import VerifiedGarbage.Proof.X25519.AArch64.Squares
public import VerifiedGarbage.Proof.Framework.AArch64.InterleavePairs
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X25519.Ladder
import VerifiedGarbage.Proof.X25519.AArch64.Ops

-- separate module: the step's symbolic execution builds without the ladder's loop and contract, which change apart from it.

@[expose] public section

namespace VG.Proof.X25519.AArch64.Ladder

open VG VG.AArch64 VG.Impl.X25519.AArch64.Ladder VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Pairs
open VG.Impl.X25519.AArch64 (BITS)
open VG.Impl.X25519.AArch64.Squares VG.Proof.X25519.AArch64.Squares
open VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.AArch64.Pairs VG.Proof.Ed25519.Word64 VG.Proof.X25519
variable {large : Bool}

theorem sumAB_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x11 .x4 .x5 .x6 + v4 s .x7 .x21 .x22 .x23 < 2 ^ 256 + 2 ^ 191) :
    WP isa (.block (sum3 .x16 .x17 .x20 .x24 .x11 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x2 .x3)) s fun t =>
      toFe (v4 t .x16 .x17 .x20 .x24) = toFe (v4 s .x11 .x4 .x5 .x6) + toFe (v4 s .x7 .x21 .x22 .x23) ∧
      Keeps [.x16, .x17, .x20, .x24, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum3_value _ _ _ _ _ _ _ _ hb)

theorem diffAB_ok (s : State) (hz : s.gpr .x10 = 0) (hb : v4 s .x7 .x21 .x22 .x23 < 2 ^ 256 - 38) :
    WP isa (.block (diff4 .x11 .x4 .x5 .x6 .x11 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x2 .x3)) s fun t =>
      toFe (v4 t .x11 .x4 .x5 .x6) = toFe (v4 s .x11 .x4 .x5 .x6) - toFe (v4 s .x7 .x21 .x22 .x23) ∧
      Keeps [.x11, .x4, .x5, .x6, .x2, .x3] s t := by
  sum_run hz
  sum_done (diff4_value (s.gpr .x11) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) _ _ _ _ hb)

theorem sumCD_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x12 .x13 .x14 .x15 + v4 s .x21 .x22 .x23 .x24 < 2 ^ 256 + 2 ^ 191) :
    WP isa (.block (sum3 .x4 .x5 .x6 .x7 .x12 .x13 .x14 .x15 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x4 .x5 .x6 .x7) = toFe (v4 s .x12 .x13 .x14 .x15) + toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x4, .x5, .x6, .x7, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum3_value _ _ _ _ _ _ _ _ hb)

theorem diffCD_ok (s : State) (hz : s.gpr .x10 = 0) (hb : v4 s .x21 .x22 .x23 .x24 < 2 ^ 256 - 38) :
    WP isa (.block (diff4 .x12 .x13 .x14 .x15 .x12 .x13 .x14 .x15 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = toFe (v4 s .x12 .x13 .x14 .x15) - toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x12, .x13, .x14, .x15, .x2, .x3] s t := by
  sum_run hz
  sum_done (diff4_value (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) _ _ _ _ hb)

/-! ## `AA + a24 E` -/

theorem a24Const_ok (s : State) :
    WP isa (.block a24Const) s fun t => t.gpr .x11 = 121665 ∧ Keeps [.x11] s t := by
  apply WP.of_runBlock
  simp only [a24Const, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  have h : r ≠ .x11 := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

theorem a24Low_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 A0 A1 A2 A3 R0 R1 R2 R3 R4 D0 D1 D2 D3 D4 : Nat}
    (f0 : R0 + 2 ^ 64 * D0 = A0 + L0 + 0) (f1 : R1 + 2 ^ 64 * D1 = A1 + L1 + D0) (f2 : R2 + 2 ^ 64 * D2 = A2 + L2 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = A3 + L3 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3) (d3 : D3 ≤ 1)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) (h3 : H3 < 2 ^ 17) (r4 : R4 < 2 ^ 64) :
    R0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 + 2 ^ 64 * H0 + 2 ^ 128 * H1 + 2 ^ 192 * H2 =
      A0 + 2 ^ 64 * A1 + 2 ^ 128 * A2 + 2 ^ 192 * A3 + (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) ∧
      R4 < 2 ^ 18 := by
  omega_using [f0, f1, f2, f3, f4, d3, m0, m1, m2, m3, h3, r4]

theorem mulHi_a24 (a : Word) {k : Word} (hk : k.toNat = 121665) : (mulHi a k).toNat < 2 ^ 17 := by
  have h := mul_lo_hi a k
  have ha := a.isLt
  rw [hk] at h
  omega_using [h, ha]

theorem a24Low_value (a0 a1 a2 a3 e0 e1 e2 e3 : Word) {k : Word} (hk : k.toNat = 121665) :
    let d0 := carryOut a0 (e0 * k) false
    let d1 := carryOut a1 (e1 * k) d0
    let d2 := carryOut a2 (e2 * k) d1
    let d3 := carryOut a3 (e3 * k) d2
    val4 (addCarry a0 (e0 * k) false) (addCarry a1 (e1 * k) d0) (addCarry a2 (e2 * k) d1)
        (addCarry a3 (e3 * k) d2) + 2 ^ 256 * (addCarry (mulHi e3 k) 0 d3).toNat +
        2 ^ 64 * (mulHi e0 k).toNat + 2 ^ 128 * (mulHi e1 k).toNat +
        2 ^ 192 * (mulHi e2 k).toNat = val4 a0 a1 a2 a3 + val4 e0 e1 e2 e3 * k.toNat ∧
      (addCarry (mulHi e3 k) 0 d3).toNat < 2 ^ 18 := by
  intro d0 d1 d2 d3
  simp only [val4]
  rw [show (e0.toNat + 2 ^ 64 * e1.toNat + 2 ^ 128 * e2.toNat + 2 ^ 192 * e3.toNat) * k.toNat =
    e0.toNat * k.toNat + 2 ^ 64 * (e1.toNat * k.toNat) + 2 ^ 128 * (e2.toNat * k.toNat) +
      2 ^ 192 * (e3.toNat * k.toNat) by simp only [Nat.add_mul, Nat.mul_assoc]]
  exact a24Low_arith (addCarry_value a0 (e0 * k) false) (addCarry_value a1 (e1 * k) d0)
    (addCarry_value a2 (e2 * k) d1) (addCarry_value a3 (e3 * k) d2)
    (addCarry_value (mulHi e3 k) 0 d3) (Bool.toNat_le d3)
    (mul_lo_hi e0 k) (mul_lo_hi e1 k) (mul_lo_hi e2 k) (mul_lo_hi e3 k) (mulHi_a24 e3 hk)
    (addCarry (mulHi e3 k) 0 d3).isLt

theorem a24Low_ok (s : State) (hz : s.gpr .x10 = 0) {k : Word} (hk : k.toNat = 121665) (h11 : s.gpr .x11 = k) :
    WP isa (.block a24Low) s fun t =>
      (v4 t .x4 .x5 .x6 .x7 + 2 ^ 256 * (t.gpr .x20).toNat +
        2 ^ 64 * (mulHi (s.gpr .x12) k).toNat + 2 ^ 128 * (mulHi (s.gpr .x13) k).toNat +
        2 ^ 192 * (mulHi (s.gpr .x14) k).toNat =
          v4 s .x4 .x5 .x6 .x7 + v4 s .x12 .x13 .x14 .x15 * k.toNat ∧ (t.gpr .x20).toNat < 2 ^ 18) ∧
      Keeps [.x2, .x3, .x8, .x9, .x20, .x4, .x5, .x6, .x7] s t := by
  apply WP.of_runBlock
  simp only [v4, a24Low, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, h11, Option.some.injEq, exists_eq_left']
  sum_done (a24Low_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15) hk)

theorem a24High_ok (s : State) (h20 : (s.gpr .x20).toNat < 2 ^ 18) {k : Word} (h11 : s.gpr .x11 = k) :
    WP isa (.block a24High) s fun t =>
      t.gpr .x2 = mulHi (s.gpr .x12) k ∧ t.gpr .x3 = mulHi (s.gpr .x13) k ∧
      t.gpr .x8 = mulHi (s.gpr .x14) k ∧
      (t.gpr .x9).toNat = 19 * ((s.gpr .x20).toNat * 2 + (s.gpr .x7).toNat / 2 ^ 63) ∧
      (t.gpr .x7).toNat = (s.gpr .x7).toNat % 2 ^ 63 ∧ Keeps [.x2, .x3, .x8, .x9, .x7, .x11, .x16] s t := by
  apply WP.of_runBlock
  simp only [a24High, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (1 : Nat) < 64 from by decide, show 16 * 0 < Size.w.bits from by decide, ↓reduceIte,
    Option.some.injEq, exists_eq_left', ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, reduceCtorEq, h11]
  obtain h7 := (s.gpr .x7).isLt
  refine ⟨trivial, trivial, trivial, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · have c19 : (BitVec.setWidth 64 (BitVec.setWidth 32 (19 : BitVec 16) <<< (16 * 0))).toNat = 19 := by decide
    obtain hc : (decide (2 ^ 64 ≤ (s.gpr .x7).toNat + (s.gpr .x7).toNat + false.toNat)).toNat =
        (s.gpr .x7).toNat / 2 ^ 63 := by
      by_cases h : 2 ^ 63 ≤ (s.gpr .x7).toNat
      · rw [decide_eq_true (by simp only [Bool.toNat_false]; omega_arith)]; simp only [Bool.toNat_true]; omega_arith
      · rw [decide_eq_false (by simp only [Bool.toNat_false]; omega_arith)]; simp only [Bool.toNat_false]; omega_arith
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, hc, c19]
    omega_arith
  · simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Bool.toNat_false,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr, ite_false]

theorem a24Sum_ok (s : State) (h7 : (s.gpr .x7).toNat < 2 ^ 63) (h8 : (s.gpr .x8).toNat < 2 ^ 17) :
    WP isa (.block a24Sum) s fun t =>
      v4 t .x12 .x13 .x14 .x15 = v4 s .x4 .x5 .x6 .x7 + (s.gpr .x9).toNat + 2 ^ 64 * (s.gpr .x2).toNat +
        2 ^ 128 * (s.gpr .x3).toNat + 2 ^ 192 * (s.gpr .x8).toNat ∧ Keeps [.x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [v4, a24Sum, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · obtain e := add4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x9) (s.gpr .x2) (s.gpr .x3)
      (s.gpr .x8) false
    obtain l4 := (s.gpr .x4).isLt
    obtain l5 := (s.gpr .x5).isLt
    obtain l6 := (s.gpr .x6).isLt
    obtain l9 := (s.gpr .x9).isLt
    obtain l2 := (s.gpr .x2).isLt
    obtain l3 := (s.gpr .x3).isLt
    obtain n := val4_lt (addCarry (s.gpr .x4) (s.gpr .x9) false)
      (addCarry (s.gpr .x5) (s.gpr .x2) (carryOut (s.gpr .x4) (s.gpr .x9) false))
      (addCarry (s.gpr .x6) (s.gpr .x3) (carryOut (s.gpr .x5) (s.gpr .x2) (carryOut (s.gpr .x4) (s.gpr .x9) false)))
      (addCarry (s.gpr .x7) (s.gpr .x8) (carryOut (s.gpr .x6) (s.gpr .x3) (carryOut (s.gpr .x5) (s.gpr .x2)
        (carryOut (s.gpr .x4) (s.gpr .x9) false))))
    change val4 (addCarry (s.gpr .x4) (s.gpr .x9) false) _ _ _ = _
    dsimp only [addCarry, carryOut, Size.bits] at e n ⊢
    revert e n
    generalize val4 (s.gpr .x4 + _ + _) _ _ _ = R
    intro e n
    simp only [val4, Bool.toNat_false, Nat.add_zero] at e ⊢
    omega_arith
  · reg_keeps

/-- `AA + a24 E` into `x12`–`x15`, for `AA` in `x4`–`x7` and `E` in `x12`–`x15`. -/
theorem a24_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block (a24Const ++ a24Low ++ a24High ++ a24Sum)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = toFe (v4 s .x4 .x5 .x6 .x7) + Spec.X25519.a24 * toFe (v4 s .x12 .x13 .x14 .x15) ∧
      Keeps lclob s t := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (a24Const_ok s) fun a ⟨a11, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (a24Low_ok a ((ka.gpr _ (by decide)).trans hz) (k := a.gpr .x11) (by rw [a11]; rfl) rfl) fun b ⟨⟨eb, b20⟩, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (a24High_ok b b20 (kb.gpr _ (by decide))) fun c ⟨c2, c3, c8, c9, c7, kc⟩ => ?_
  refine WP.mono (a24Sum_ok c (by rw [c7]; exact Nat.mod_lt _ (by decide)) (by rw [c8]; exact mulHi_a24 _ (by rw [a11]; rfl)))
    fun t ⟨et, kt⟩ => ⟨?_, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans
      ((kc.mono (by decide)).trans (kt.mono (by decide))))⟩
  apply toFe_addA24
  obtain g : ∀ r ∈ [Reg.x12, .x13, .x14, .x15], b.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact (kb.gpr _ (by decide)).trans (ka.gpr _ (by decide))
  obtain h : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15], a.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ka.gpr _ (by decide)
  rw [g .x12 (by decide), g .x13 (by decide), g .x14 (by decide)] at *
  rw [v4, v4, v4, h .x12 (by decide), h .x13 (by decide), h .x14 (by decide), h .x15 (by decide),
    h .x4 (by decide), h .x5 (by decide), h .x6 (by decide), h .x7 (by decide)] at eb
  rw [c2, c3, c8, c9] at et
  rw [a11, show (121665 : Word).toNat = 121665 from rfl] at eb
  rw [a11] at et
  rw [show v4 c .x4 .x5 .x6 .x7 = (b.gpr .x4).toNat + 2 ^ 64 * (b.gpr .x5).toNat + 2 ^ 128 * (b.gpr .x6).toNat +
      2 ^ 192 * ((b.gpr .x7).toNat % 2 ^ 63) by
    rw [v4, val4, kc.gpr _ (by decide), kc.gpr _ (by decide), kc.gpr _ (by decide), c7]] at et
  rw [show v4 s .x4 .x5 .x6 .x7 + 121665 * v4 s .x12 .x13 .x14 .x15 = v4 t .x12 .x13 .x14 .x15 +
      VG.Spec.X25519.P * ((b.gpr .x20).toNat * 2 + (b.gpr .x7).toNat / 2 ^ 63) by
    rw [Nat.mul_comm 121665, show v4 s .x4 .x5 .x6 .x7 + v4 s .x12 .x13 .x14 .x15 * 121665 = _ from eb.symm, et]
    simp only [val4, VG.Spec.X25519.P]
    omega_using [], Nat.add_mul_mod_self_left]

/-! ## The swap -/

/-- The bytes of the scalar's bits: `b t` at `BITS + t`. -/
def BitsAt (m : Mem) (base : Addr) (b : Nat → Nat) : Prop :=
  ∀ t < 256, m (off base (BITS + t)) = BitVec.ofNat 8 (b t)

private theorem bit_eq : ∀ a < 2, ∀ b < 2,
    decide ((((BitVec.ofNat 8 a).setWidth 64 ^^^ (BitVec.ofNat 8 b).setWidth 64) &&&
      ((BitVec.ofNat 8 a).setWidth 64 ^^^ (BitVec.ofNat 8 b).setWidth 64) : Word) = 0) = decide (a = b) := by decide

theorem swapTest_ok {s : State} {base : Addr} (hs : Scr s base large) {b : Nat → Nat} (hb : BitsAt s.mem base b)
    {n : Nat} (hn : n < 255) (b0 : b n < 2) (b1 : b (n + 1) < 2) (h19 : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block swapTest) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.zf = decide (b n = b (n + 1)) ∧ Keeps [.x16, .x17, .x19] s t := by
  have hw := workSize_ge large
  have hB : BITS = 1984 := rfl
  have e19 : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
    rw [h19, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have ad : ∀ d, base + BitVec.ofNat 64 n + BitVec.ofNat 64 (BITS + d) = off base (BITS + (n + d)) := fun d => by
    rw [Offset.add_add, show n + (BITS + d) = BITS + (n + d) by omega_using []]
  have hin : ∀ d ≤ 1, InRegions (s.rd ++ s.wr) (off base (BITS + (n + d))) 1 := fun d hd =>
    ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega_using [hw, hB, hn, hd])⟩
  have hbyte : ∀ (m : Mem) (a : Addr), ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := read1_toNat
  have a0 := ad 0
  have a1 := ad 1
  have i0 := hin 0 (by decide)
  have i1 := hin 1 (by decide)
  simp only [Nat.add_zero] at a0 i0
  apply WP.of_runBlock
  simp only [swapTest, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, show (1 : Nat) < 4096 from by decide,
    Nat.mod_one, show BITS < 4096 * 1 from by decide, show BITS + 1 < 4096 * 1 from by decide, and_self,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hs.x0, e19, a0, a1, i0, i1, hbyte,
    hb n (by omega_using [hn]), hb (n + 1) (by omega_using [hn]), bit_eq _ b0 _ b1,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem swapRegs_ok (s : State) :
    WP isa (.block swapRegs) s fun t =>
      v4 t .x11 .x4 .x5 .x6 = (if s.zf = true then v4 s .x4 .x5 .x6 .x7 else v4 s .x12 .x13 .x14 .x15) ∧
      v4 t .x12 .x13 .x14 .x15 = (if s.zf = true then v4 s .x12 .x13 .x14 .x15 else v4 s .x4 .x5 .x6 .x7) ∧
      v4 t .x7 .x21 .x22 .x23 = (if s.zf = true then v4 s .x21 .x22 .x23 .x24 else v4 s .x2 .x3 .x8 .x9) ∧
      v4 t .x2 .x3 .x8 .x9 = (if s.zf = true then v4 s .x2 .x3 .x8 .x9 else v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23] s t := by
  apply WP.of_runBlock
  simp only [swapRegs, swapWord, List.cons_append, List.nil_append, v4, runBlock_cons, runStep_some, runBlock_nil,
    exec, read_x, CondCode.holds, RegUpd.zf_write, ite_bnot,
    ↓RegUpd.gpr_write, BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left', ite_val4]
  refine ⟨trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## The sums and differences of the swapped elements -/

theorem sumsAB_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0)
    (ha : v4 s .x11 .x4 .x5 .x6 < 2 ^ 255 + 2 ^ 136) (hb : v4 s .x7 .x21 .x22 .x23 < 2 ^ 255 + 2 ^ 136) :
    WP isa (.block sumsAB) s fun t =>
      env t.mem base 5 = toFe (v4 s .x11 .x4 .x5 .x6) + toFe (v4 s .x7 .x21 .x22 .x23) ∧
      env t.mem base 6 = toFe (v4 s .x11 .x4 .x5 .x6) - toFe (v4 s .x7 .x21 .x22 .x23) ∧
      fe t.mem base (offset 4) = v4 s .x2 .x3 .x8 .x9 ∧
      v4 t .x12 .x13 .x14 .x15 = v4 s .x12 .x13 .x14 .x15 ∧
      (∀ i : Slot, i ≠ 4 → i ≠ 5 → i ≠ 6 → env t.mem base i = env s.mem base i) ∧ LF base s t := by
  simp only [sumsAB, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hs 4 (by decide) _ _ _ _) fun a ⟨pa, ga, fa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sumAB_ok a (pa.zero hz) (by
      obtain h : v4 s .x11 .x4 .x5 .x6 + v4 s .x7 .x21 .x22 .x23 < 2 ^ 256 + 2 ^ 191 := by omega_using [ha, hb]
      rw [v4, v4, ga]; exact h)) fun b ⟨eb, kb⟩ => ?_
  obtain hsb := (pa.scr hs).of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hsb 5 (by decide) _ _ _ _) fun c ⟨pc, gc, fc⟩ => ?_
  obtain gx : ∀ r ∈ [Reg.x11, .x4, .x5, .x6, .x7, .x21, .x22, .x23], c.gpr r = s.gpr r := by
    intro r hr
    rw [gc]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact (kb.gpr _ (by decide)).trans (by rw [ga])
  obtain vx : v4 c .x11 .x4 .x5 .x6 = v4 s .x11 .x4 .x5 .x6 := by
    rw [v4, gx _ (by decide), gx _ (by decide), gx _ (by decide), gx _ (by decide)]
  obtain vz : v4 c .x7 .x21 .x22 .x23 = v4 s .x7 .x21 .x22 .x23 := by
    rw [v4, gx _ (by decide), gx _ (by decide), gx _ (by decide), gx _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (diffAB_ok c (pc.zero ((kb.gpr _ (by decide)).trans (pa.zero hz))) (by rw [vz]; omega_using [hb]))
    fun d ⟨ed, kd⟩ => ?_
  refine WP.mono (putPairs_ok ((pc.scr hsb).of_keeps kd (by decide)) 6 (by decide) _ _ _ _) fun t ⟨pt, gt, ft⟩ => ?_
  rw [vx, vz] at ed
  rw [v4, v4, v4, ga] at eb
  refine ⟨?_, ?_, ?_, ?_, fun i h4 h5 h6 => ?_, ?_⟩
  · rw [pt.env, Function.update_of_ne (by decide), kd.mem, pc.env, Function.update_self, F, fc]
    exact eb
  · rw [pt.env, Function.update_self, F, ft]
    exact ed
  · rw [pt.fe (by decide), kd.mem, pc.fe (by decide), kb.mem, fa]
  · rw [v4, gt, kd.gpr _ (by decide), kd.gpr _ (by decide), kd.gpr _ (by decide), kd.gpr _ (by decide), gc,
      kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide), ga]
  · rw [pt.env, Function.update_of_ne h6, kd.mem, pc.env, Function.update_of_ne h5, kb.mem, pa.env,
      Function.update_of_ne h4]
  · exact (pa.lf (by decide)).trans ((LF.of_keeps kb (by decide)).trans ((pc.lf (by decide)).trans
      ((LF.of_keeps kd (by decide)).trans (pt.lf (by decide)))))

theorem sumsCD_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0)
    (ha : v4 s .x12 .x13 .x14 .x15 < 2 ^ 255 + 2 ^ 136) (hb : Sm s.mem base 4) :
    WP isa (.block sumsCD) s fun t =>
      env t.mem base 7 = toFe (v4 s .x12 .x13 .x14 .x15) + env s.mem base 4 ∧
      env t.mem base 8 = toFe (v4 s .x12 .x13 .x14 .x15) - env s.mem base 4 ∧
      (∀ i : Slot, i ≠ 7 → i ≠ 8 → env t.mem base i = env s.mem base i) ∧ LF base s t := by
  simp only [sumsCD, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hs 4 (by decide) (by decide)) fun a ⟨ea, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  obtain va : v4 a .x12 .x13 .x14 .x15 = v4 s .x12 .x13 .x14 .x15 := by
    rw [v4, ka.gpr _ (by decide), ka.gpr _ (by decide), ka.gpr _ (by decide), ka.gpr _ (by decide)]
  obtain za := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (sumCD_ok a za (by rw [va, ea]; omega_using [ha, hb])) fun b ⟨eb, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hsb 7 (by decide) _ _ _ _) fun c ⟨pc, gc, fc⟩ => ?_
  obtain vx : v4 c .x12 .x13 .x14 .x15 = v4 s .x12 .x13 .x14 .x15 := by
    rw [← va, v4, gc, kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide)]
  obtain vz : v4 c .x21 .x22 .x23 .x24 = fe s.mem base (offset 4) := by
    rw [← ea, v4, gc, kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (diffCD_ok c (pc.zero ((kb.gpr _ (by decide)).trans za)) (by rw [vz]; omega_using [hb]))
    fun d ⟨ed, kd⟩ => ?_
  refine WP.mono (putPairs_ok ((pc.scr hsb).of_keeps kd (by decide)) 8 (by decide) _ _ _ _) fun t ⟨pt, _, ft⟩ => ?_
  rw [vx, vz] at ed
  rw [va, ea] at eb
  refine ⟨?_, ?_, fun i h7 h8 => ?_, ?_⟩
  · rw [pt.env, Function.update_of_ne (by decide), kd.mem, pc.env, Function.update_self, F, fc]
    exact eb
  · rw [pt.env, Function.update_self, F, ft]
    exact ed
  · rw [pt.env, Function.update_of_ne h8, kd.mem, pc.env, Function.update_of_ne h7, kb.mem, ka.mem]
  · exact (LF.of_keeps ka (by decide)).trans ((LF.of_keeps kb (by decide)).trans ((pc.lf (by decide)).trans
      ((LF.of_keeps kd (by decide)).trans (pt.lf (by decide)))))

theorem loadAll_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block loadAll) s fun t =>
      v4 t .x4 .x5 .x6 .x7 = fe s.mem base (offset 1) ∧ v4 t .x12 .x13 .x14 .x15 = fe s.mem base (offset 3) ∧
      v4 t .x21 .x22 .x23 .x24 = fe s.mem base (offset 2) ∧ v4 t .x2 .x3 .x8 .x9 = fe s.mem base (offset 4) ∧
      Keeps lclob s t := by
  simp only [loadAll, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hs 1 (by decide) (by decide)) fun a ⟨ea, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hsa 3 (by decide) (by decide)) fun b ⟨eb, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hsb 2 (by decide) (by decide)) fun c ⟨ec, kc⟩ => ?_
  refine WP.mono (getPairs_ok (hsb.of_keeps kc (by decide)) 4 (by decide) (by decide)) fun t ⟨et, kt⟩ => ?_
  rw [ka.mem] at eb
  rw [kb.mem, ka.mem] at ec
  rw [kc.mem, kb.mem, ka.mem] at et
  refine ⟨?_, ?_, ?_, et, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans ((kc.mono (by decide)).trans
    (kt.mono (by decide))))⟩
  · rw [← ea, v4, kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), kt.gpr _ (by decide),
      kc.gpr _ (by decide), kb.gpr _ (by decide), kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide),
      kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide)]
  · rw [← eb, v4, kt.gpr _ (by decide), kc.gpr _ (by decide), kt.gpr _ (by decide), kc.gpr _ (by decide),
      kt.gpr _ (by decide), kc.gpr _ (by decide), kt.gpr _ (by decide), kc.gpr _ (by decide)]
  · rw [← ec, v4, kt.gpr _ (by decide), kt.gpr _ (by decide), kt.gpr _ (by decide), kt.gpr _ (by decide)]

/-- The ladder's elements are below `2²⁵⁵ + 2¹³⁶`. -/
abbrev Sm4 (m : Mem) (base : Addr) : Prop := Sm m base 1 ∧ Sm m base 2 ∧ Sm m base 3 ∧ Sm m base 4

/-- The swap and the four sums and differences, for the bits `n` and `n + 1`. -/
theorem front_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (hm : Sm4 s.mem base)
    {b : Nat → Nat} (hb : BitsAt s.mem base b) {n : Nat} (hn : n < 255) (b0 : b n < 2) (b1 : b (n + 1) < 2)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block front) s fun t =>
      let z := decide (b n = b (n + 1))
      let x2 := if z = true then env s.mem base 1 else env s.mem base 3
      let x3 := if z = true then env s.mem base 3 else env s.mem base 1
      let z2 := if z = true then env s.mem base 2 else env s.mem base 4
      let z3 := if z = true then env s.mem base 4 else env s.mem base 2
      env t.mem base 5 = x2 + z2 ∧ env t.mem base 6 = x2 - z2 ∧ env t.mem base 7 = x3 + z3 ∧
      env t.mem base 8 = x3 - z3 ∧ env t.mem base 0 = env s.mem base 0 ∧
      t.gpr .x19 = BitVec.ofNat 64 n ∧ t.gpr .x10 = 0 ∧
      (∀ r, r ∉ .x19 :: lclob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 64 448 s.mem t.mem := by
  obtain ⟨m1, m2, m3, m4⟩ := hm
  rw [front, WP.block_append_iff]
  refine WP.mono (loadAll_ok hs) fun a ⟨a1, a3, a2, a4, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (swapTest_ok hsa (by rw [ka.mem]; exact hb) hn b0 b1 ((ka.gpr _ (by decide)).trans h19))
    fun c ⟨c19, cz, kc⟩ => ?_
  obtain hsc := hsa.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (swapRegs_ok c) fun d ⟨d2, d3, dz2, dz3, kd⟩ => ?_
  obtain hsd := hsc.of_keeps kd (by decide)
  obtain md : d.mem = s.mem := by rw [kd.mem, kc.mem, ka.mem]
  obtain zd : d.gpr .x10 = 0 := by rw [kd.gpr _ (by decide), kc.gpr _ (by decide), ka.gpr _ (by decide), hz]
  obtain k4 : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x12, .x13, .x14, .x15, .x21, .x22, .x23, .x24, .x2, .x3, .x8, .x9],
      c.gpr r = a.gpr r := by
    intro r hr
    refine kc.gpr _ fun h => ?_
    revert r
    decide
  rw [cz] at d2 d3 dz2 dz3
  rw [show v4 c .x4 .x5 .x6 .x7 = fe s.mem base (offset 1) by
      rw [← a1, v4, k4 _ (by decide), k4 _ (by decide), k4 _ (by decide), k4 _ (by decide)],
    show v4 c .x12 .x13 .x14 .x15 = fe s.mem base (offset 3) by
      rw [← a3, v4, k4 _ (by decide), k4 _ (by decide), k4 _ (by decide), k4 _ (by decide)]] at d2 d3
  rw [show v4 c .x21 .x22 .x23 .x24 = fe s.mem base (offset 2) by
      rw [← a2, v4, k4 _ (by decide), k4 _ (by decide), k4 _ (by decide), k4 _ (by decide)],
    show v4 c .x2 .x3 .x8 .x9 = fe s.mem base (offset 4) by
      rw [← a4, v4, k4 _ (by decide), k4 _ (by decide), k4 _ (by decide), k4 _ (by decide)]] at dz2 dz3
  generalize decide (b n = b (n + 1)) = z at *
  obtain lt : ∀ {x y : Nat}, x < 2 ^ 255 + 2 ^ 136 → y < 2 ^ 255 + 2 ^ 136 →
      (if z = true then x else y) < 2 ^ 255 + 2 ^ 136 := fun hx hy => by cases z; exact hy; exact hx
  obtain tf : ∀ x y : Nat, toFe (if z = true then x else y) = if z = true then toFe x else toFe y :=
    fun x y => by cases z <;> rfl
  rw [WP.block_append_iff]
  refine WP.mono (sumsAB_ok hsd zd (by rw [d2]; exact lt m1 m3) (by rw [dz2]; exact lt m2 m4))
    fun e ⟨e5, e6, e4, e12, er, le⟩ => ?_
  refine WP.mono (sumsCD_ok (le.scr hsd) (le.zero zd) (by rw [e12, d3]; exact lt m3 m1) (by
      rw [Sm, e4, dz3]; exact lt m4 m2)) fun t ⟨t7, t8, tr, lt'⟩ => ?_
  rw [d2, dz2, tf, tf] at e5 e6
  rw [e12, d3, tf, show env e.mem base 4 = toFe (fe e.mem base (offset 4)) from rfl, e4, dz3, tf] at t7 t8
  obtain l := le.trans lt'
  refine ⟨?_, ?_, t7, t8, ?_, ?_, l.zero zd, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [tr _ (by decide) (by decide)]; exact e5
  · rw [tr _ (by decide) (by decide)]; exact e6
  · rw [tr _ (by decide) (by decide), er _ (by decide) (by decide) (by decide), md]
  · rw [l.gpr _ (by decide), kd.gpr _ (by decide), c19]
  · simp only [List.mem_cons, not_or] at hr
    rw [l.gpr _ hr.2, kd.gpr _ fun h => hr.2 ((by decide : ∀ q ∈ [Reg.x2, .x3, .x4, .x5, .x6, .x7, .x8,
      .x9, .x11, .x12, .x13, .x14, .x15, .x21, .x22, .x23], q ∈ lclob) r h), kc.gpr _ fun h => ?_, ka.gpr _ hr.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact hr.2 (by decide)
    · exact hr.2 (by decide)
    · exact hr.1 rfl
  · rw [l.rd, kd.rd, kc.rd, ka.rd]
  · rw [l.wr, kd.wr, kc.wr, ka.wr]
  · rw [l.sp, kd.sp, kc.sp, ka.sp]
  · rw [← md]; exact l.mem

/-! ## The products of an iteration -/

theorem pack_arith {a b c d e w0 w1 w2 w3 k0 k1 k2 k3 b' c' d' e' : Nat}
    (hd : d < 2 ^ 52) (he : e < 2 ^ 51 + 2 ^ 17) (hb' : b' = b * 2 ^ 51 % 2 ^ 64) (hc' : c' = c * 2 ^ 38 % 2 ^ 64)
    (hd' : d' = d * 2 ^ 25 % 2 ^ 64) (he' : e' = e * 2 ^ 12 % 2 ^ 64)
    (f0 : w0 + 2 ^ 64 * k0 = a + b' + 0) (f1 : w1 + 2 ^ 64 * k1 = b / 2 ^ 13 + c' + k0)
    (f2 : w2 + 2 ^ 64 * k2 = c / 2 ^ 26 + d' + k1) (f3 : w3 + 2 ^ 64 * k3 = d / 2 ^ 39 + e' + k2)
    (hw : w3 < 2 ^ 64) (h2 : k2 ≤ 1) :
    w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 = a + 2 ^ 51 * b + 2 ^ 102 * c + 2 ^ 153 * d + 2 ^ 204 * e := by
  have q1 : b = b / 2 ^ 13 * 2 ^ 13 + b % 2 ^ 13 := by omega_using []
  have q2 : c = c / 2 ^ 26 * 2 ^ 26 + c % 2 ^ 26 := by omega_using []
  have q3 : d = d / 2 ^ 39 * 2 ^ 39 + d % 2 ^ 39 := by omega_using []
  have r1 : b' = b % 2 ^ 13 * 2 ^ 51 := by omega_using [hb']
  have r2 : c' = c % 2 ^ 26 * 2 ^ 38 := by omega_using [hc']
  have r3 : d' = d % 2 ^ 39 * 2 ^ 25 := by omega_using [hd']
  have r4 : e' = e * 2 ^ 12 := by omega_using [he', he]
  have l3 : d / 2 ^ 39 < 2 ^ 13 := by omega_using [hd]
  have hk : k3 = 0 := by omega_using [f3, r4, l3, he, h2, hw]
  generalize b / 2 ^ 13 = b1 at *
  generalize b % 2 ^ 13 = b0 at *
  generalize c / 2 ^ 26 = c1 at *
  generalize c % 2 ^ 26 = c0 at *
  generalize d / 2 ^ 39 = d1 at *
  generalize d % 2 ^ 39 = d0 at *
  omega_using [q1, q2, q3, r1, r2, r3, r4, f0, f1, f2, f3, hk]

/-- The five limbs packed. -/
theorem pack_value {a b c d e : Word} (hd : d.toNat < 2 ^ 52) (he : e.toNat < 2 ^ 51 + 2 ^ 17) :
    let c0 := carryOut a (b <<< 51) false
    let c1 := carryOut (b >>> 13) (c <<< 38) c0
    let c2 := carryOut (c >>> 26) (d <<< 25) c1
    val4 (addCarry a (b <<< 51) false) (addCarry (b >>> 13) (c <<< 38) c0) (addCarry (c >>> 26) (d <<< 25) c1)
        (addCarry (d >>> 39) (e <<< 12) c2) =
      a.toNat + 2 ^ 51 * b.toNat + 2 ^ 102 * c.toNat + 2 ^ 153 * d.toNat + 2 ^ 204 * e.toNat := by
  intro c0 c1 c2
  have f0 := addCarry_value a (b <<< 51) false
  have f1 := addCarry_value (b >>> 13) (c <<< 38) c0
  have f2 := addCarry_value (c >>> 26) (d <<< 25) c1
  have f3 := addCarry_value (d >>> 39) (e <<< 12) c2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at f1 f2 f3
  exact pack_arith hd he (by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]) (by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq])
    (by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]) (by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]) f0 f1 f2 f3
    (addCarry (d >>> 39) (e <<< 12) c2).isLt (Bool.toNat_le c2)

theorem packLoad_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (h8 : o % 8 = 0) (ho : o + 40 ≤ 4096) :
    WP isa (.block (packLoad o)) s fun t =>
      t.gpr .x2 = word s.mem base o ∧ t.gpr .x3 = word s.mem base (o + 8) ∧ t.gpr .x8 = word s.mem base (o + 16) ∧
      t.gpr .x9 = word s.mem base (o + 24) ∧ t.gpr .x16 = word s.mem base (o + 32) ∧
      Keeps [.x2, .x3, .x8, .x9, .x16] s t := by
  have hw := workSize_ge large
  apply WP.of_runBlock
  have e0 : ∀ {u : State}, Scr u base large → ∀ (r : Reg) (d : Nat), d % 8 = 0 → d + 8 ≤ o + 40 →
      exec (.ldr .x r .x0 d) u = some (u.write .x r (word u.mem base d)) := fun hu r d h1 h2 =>
    load_sc hu h1 (by omega_using [h2, ho, hw]) r
  have h1 := hs.write (r := .x2) (by decide) (word s.mem base o)
  have h2 := h1.write (r := .x3) (by decide) (word s.mem base (o + 8))
  have h3 := h2.write (r := .x8) (by decide) (word s.mem base (o + 16))
  have h4 := h3.write (r := .x9) (by decide) (word s.mem base (o + 24))
  simp only [packLoad, runBlock_cons, runStep_some, runBlock_nil, e0 hs _ o h8 (by omega_using []),
    e0 h1 _ (o + 8) (by omega_using [h8]) (by omega_using []), e0 h2 _ (o + 16) (by omega_using [h8]) (by omega_using []),
    e0 h3 _ (o + 24) (by omega_using [h8]) (by omega_using []), e0 h4 _ (o + 32) (by omega_using [h8]) (by omega_using []),
    RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem packAA_ok (s : State) (h9 : (s.gpr .x9).toNat < 2 ^ 52) (h16 : (s.gpr .x16).toNat < 2 ^ 51 + 2 ^ 17) :
    WP isa (.block (packSum .x4 .x5 .x6 .x7)) s fun t =>
      v4 t .x4 .x5 .x6 .x7 = (s.gpr .x2).toNat + 2 ^ 51 * (s.gpr .x3).toNat + 2 ^ 102 * (s.gpr .x8).toNat +
        2 ^ 153 * (s.gpr .x9).toNat + 2 ^ 204 * (s.gpr .x16).toNat ∧
      Keeps [.x4, .x5, .x6, .x7, .x3, .x8, .x9, .x17] s t := by
  apply WP.of_runBlock
  simp only [v4, packSum, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (51 : Nat) < 64 from by decide, show (13 : Nat) < 64 from by decide, show (38 : Nat) < 64 from by decide,
    show (26 : Nat) < 64 from by decide, show (25 : Nat) < 64 from by decide, show (39 : Nat) < 64 from by decide,
    show (12 : Nat) < 64 from by decide,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  sum_done (pack_value (a := s.gpr .x2) (b := s.gpr .x3) (c := s.gpr .x8) h9 h16)

theorem packBB_ok (s : State) (h9 : (s.gpr .x9).toNat < 2 ^ 52) (h16 : (s.gpr .x16).toNat < 2 ^ 51 + 2 ^ 17) :
    WP isa (.block (packSum .x21 .x22 .x23 .x24)) s fun t =>
      v4 t .x21 .x22 .x23 .x24 = (s.gpr .x2).toNat + 2 ^ 51 * (s.gpr .x3).toNat + 2 ^ 102 * (s.gpr .x8).toNat +
        2 ^ 153 * (s.gpr .x9).toNat + 2 ^ 204 * (s.gpr .x16).toNat ∧
      Keeps [.x21, .x22, .x23, .x24, .x3, .x8, .x9, .x17] s t := by
  apply WP.of_runBlock
  simp only [v4, packSum, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show (51 : Nat) < 64 from by decide, show (13 : Nat) < 64 from by decide, show (38 : Nat) < 64 from by decide,
    show (26 : Nat) < 64 from by decide, show (25 : Nat) < 64 from by decide, show (39 : Nat) < 64 from by decide,
    show (12 : Nat) < 64 from by decide,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  sum_done (pack_value (a := s.gpr .x2) (b := s.gpr .x3) (c := s.gpr .x8) h9 h16)

/-- The bounds of the limbs that the squares leave. -/
abbrev OutLt (m : Mem) (base : Addr) (e : Nat) : Prop := ∀ k < 5, out m base e k < 2 ^ 51 + 2 ^ 17

theorem outVal_lt {m : Mem} {base : Addr} {e : Nat} (h : OutLt m base e) :
    outVal m base e < 2 ^ 256 - 38 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  simp only [outVal]
  omega_using [h0, h1, h2, h3, h4]

theorem packAA {s : State} {base : Addr} (hs : Scr s base large) (h : OutLt s.mem base 0) :
    WP isa (.block (packLoad OUT ++ packSum .x4 .x5 .x6 .x7)) s fun t =>
      v4 t .x4 .x5 .x6 .x7 = outVal s.mem base 0 ∧ Keeps [.x4, .x5, .x6, .x7, .x2, .x3, .x8, .x9, .x16, .x17] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (packLoad_ok hs (by decide) (by decide)) fun a ⟨a2, a3, a8, a9, a16, ka⟩ => ?_
  refine WP.mono (packAA_ok a (by rw [a9]; exact Nat.lt_trans (h 3 (by decide)) (by decide)) (by rw [a16]; exact h 4 (by decide)))
    fun t ⟨et, kt⟩ => ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [et, a2, a3, a8, a9, a16]
  rfl

theorem packBB {s : State} {base : Addr} (hs : Scr s base large) (h : OutLt s.mem base 1) :
    WP isa (.block (packLoad (OUT + 48) ++ packSum .x21 .x22 .x23 .x24)) s fun t =>
      v4 t .x21 .x22 .x23 .x24 = outVal s.mem base 1 ∧
      Keeps [.x21, .x22, .x23, .x24, .x2, .x3, .x8, .x9, .x16, .x17] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (packLoad_ok hs (by decide) (by decide)) fun a ⟨a2, a3, a8, a9, a16, ka⟩ => ?_
  refine WP.mono (packBB_ok a (by rw [a9]; exact Nat.lt_trans (h 3 (by decide)) (by decide)) (by rw [a16]; exact h 4 (by decide)))
    fun t ⟨et, kt⟩ => ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [et, a2, a3, a8, a9, a16]
  rfl

theorem outVal_outside {m m' : Mem} {base : Addr} {o : Slot} (h : Outside base (offset o) 32 m m') {e : Nat} (he : e < 2) :
    (∀ k < 5, out m' base e k = out m base e k) ∧ outVal m' base e = outVal m base e := by
  have hO : OUT = 1024 := rfl
  have w : ∀ k < 5, out m' base e k = out m base e k := fun k hk => by
    rw [out, h.word (Or.inr (by simp only [offset]; omega_arith)) (by omega_using [hk, he, hO])]
  exact ⟨w, by simp only [outVal, w 0 (by decide), w 1 (by decide), w 2 (by decide), w 3 (by decide), w 4 (by decide)]⟩

/-- `AA`, `BB` and `E` into slots 9, 10 and 11. -/
theorem packE_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0)
    (h0 : OutLt s.mem base 0) (h1 : OutLt s.mem base 1) :
    WP isa (.block packE) s fun t =>
      env t.mem base = Function.update (Function.update (Function.update (env s.mem base) 9 (toFe (outVal s.mem base 0))) 10
        (toFe (outVal s.mem base 1))) 11 (toFe (outVal s.mem base 0) - toFe (outVal s.mem base 1)) ∧
      (∀ i : Slot, i ≠ 9 → i ≠ 10 → i ≠ 11 → fe t.mem base (offset i) = fe s.mem base (offset i)) ∧ LF base s t := by
  rw [packE, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (packAA hs h0) fun a ⟨ea, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hsa 9 (by decide) _ _ _ _) fun b ⟨pb, gb, fb⟩ => ?_
  have hsb := pb.scr hsa
  obtain ⟨wb, ob⟩ := outVal_outside pb.mem (e := 1) (by decide)
  rw [ka.mem] at wb ob
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (packBB hsb fun k hk => by rw [wb k hk]; exact h1 k hk) fun c ⟨ec, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [ob] at ec
  rw [WP.block_append_iff]
  refine WP.mono (putPairs_ok hsc 10 (by decide) _ _ _ _) fun d ⟨pd, gd, fd⟩ => ?_
  have hsd := pd.scr hsc
  have va : v4 d .x4 .x5 .x6 .x7 = outVal s.mem base 0 := by
    rw [← ea, v4, gd, kc.gpr _ (by decide), kc.gpr _ (by decide), kc.gpr _ (by decide), kc.gpr _ (by decide), gb]
  have vb : v4 d .x21 .x22 .x23 .x24 = outVal s.mem base 1 := by rw [← ec, v4, gd]
  have zd : d.gpr .x10 = 0 := by rw [gd, kc.gpr _ (by decide), gb, ka.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (diffReg_ok d zd (by rw [vb]; exact outVal_lt h1)) fun f ⟨ef, kf⟩ => ?_
  refine WP.mono (putPairs_ok (hsd.of_keeps kf (by decide)) 11 (by decide) _ _ _ _) fun t ⟨pt, _, ft⟩ => ?_
  rw [va, vb] at ef
  refine ⟨?_, fun i h9 h10 h11 => ?_, ?_⟩
  · rw [pt.env, F, ft, ef, kf.mem, pd.env, F, fd, ec, kc.mem, pb.env, F, fb, ea, ka.mem]
  · rw [pt.fe h11, kf.mem, pd.fe h10, kc.mem, pb.fe h9, ka.mem]
  · exact (LF.of_keeps ka (by decide)).trans ((pb.lf (by decide)).trans ((LF.of_keeps kc (by decide)).trans
      ((pd.lf (by decide)).trans ((LF.of_keeps kf (by decide)).trans (pt.lf (by decide))))))

theorem sumSqr_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (ha : Sm s.mem base 12)
    (hb : Sm s.mem base 13) :
    WP isa (.block (sumDACB ++ squareRegs ++ toSlot 3)) s fun t => Put base 3 s t ∧
      F t.mem base (offset 3) = (env s.mem base 12 + env s.mem base 13) * (env s.mem base 12 + env s.mem base 13) ∧
      fe t.mem base (offset 3) < 2 ^ 255 + 2 ^ 135 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (sumRegs_ok hs hz 12 13 (by decide) (by decide) ha hb) fun u ⟨e, k⟩ => ?_
  refine WP.mono (squareTo_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) 3 (by decide))
    fun t ⟨p, h, l⟩ => ?_
  exact ⟨Put.of_keeps k (fun _ h => h) p, by rw [h, e], l⟩

theorem diffSqr_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (hb : Sm s.mem base 13) :
    WP isa (.block (diffDACB ++ squareRegs ++ toSlot 4)) s fun t => Put base 4 s t ∧
      F t.mem base (offset 4) = (env s.mem base 12 - env s.mem base 13) * (env s.mem base 12 - env s.mem base 13) ∧
      fe t.mem base (offset 4) < 2 ^ 255 + 2 ^ 135 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffRegs_ok hs hz 12 13 (by decide) (by decide) hb) fun u ⟨e, k⟩ => ?_
  refine WP.mono (squareTo_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) 4 (by decide))
    fun t ⟨p, h, l⟩ => ?_
  exact ⟨Put.of_keeps k (fun _ h => h) p, by rw [h, e], l⟩

theorem mulE_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) :
    WP isa (.block mulE) s fun t =>
      Put base 2 s t ∧ F t.mem base (offset 2) = env s.mem base 11 *
        (env s.mem base 9 + Spec.X25519.a24 * env s.mem base 11) ∧
      fe t.mem base (offset 2) < 2 ^ 255 + 2 ^ 135 := by
  rw [show mulE = loadPairs (offset 9) .x4 .x5 .x6 .x7 ++
      (loadPairs (offset 11) .x12 .x13 .x14 .x15 ++ ((a24Const ++ a24Low ++ a24High ++ a24Sum) ++ mulInto 2 11)) by
    simp only [mulE, List.append_assoc], WP.block_append_iff]
  refine WP.mono (getPairs_ok hs 9 (by decide) (by decide)) fun a ⟨ea, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok (hs.of_keeps ka (by decide)) 11 (by decide) (by decide)) fun b ⟨eb, kb⟩ => ?_
  obtain kab : Keeps lclob s b := (ka.mono (by decide)).trans (kb.mono (by decide))
  obtain va : v4 b .x4 .x5 .x6 .x7 = fe s.mem base (offset 9) := by
    rw [← ea, v4, kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide), kb.gpr _ (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (a24_ok b ((kab.gpr _ (by decide)).trans hz)) fun c ⟨ec, kc⟩ => ?_
  obtain kk : Keeps lclob s c := kab.trans kc
  refine WP.mono (mulInto_ok (hs.of_keeps kk (by decide)) ((kk.gpr _ (by decide)).trans hz) 2 11 (by decide))
    fun t ⟨p, h, l⟩ => ?_
  refine ⟨Put.of_keeps kk (fun _ h => h) p, ?_, l⟩
  rw [h, kk.mem, ec, va, eb, ka.mem]
  rfl

/-- The frame of an iteration's products: `LF`, with the vector code's results. -/
structure BF (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ lclob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 1056 s.mem t.mem

theorem BF.trans {base : Addr} {s t u : State} (h : BF base s t) (k : BF base t u) : BF base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem BF.of_lf {base : Addr} {s t : State} (h : LF base s t) : BF base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩

theorem BF.scr {base : Addr} {s t : State} (h : BF base s t) (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BF.zero {base : Addr} {s t : State} (h : BF base s t) (hz : s.gpr .x10 = 0) : t.gpr .x10 = 0 :=
  (h.gpr _ (by decide)).trans hz

theorem backA_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) :
    WP isa (.block backA) s fun t =>
      let e := env s.mem base
      let DA := e 8 * e 5
      let CB := e 7 * e 6
      env t.mem base = Function.update (Function.update (Function.update (Function.update e 13 CB) 12 DA) 4
        ((DA - CB) * (DA - CB))) 3 ((DA + CB) * (DA + CB)) ∧
      fe t.mem base (offset 3) < 2 ^ 255 + 2 ^ 135 ∧ LF base s t ∧
      fe t.mem base (offset 5) = fe s.mem base (offset 5) ∧ fe t.mem base (offset 6) = fe s.mem base (offset 6) := by
  rw [backA, WP.block_append_iff]
  refine WP.mono (mulSlots_ok hs hz 13 7 6 (by decide) (by decide)) fun a ⟨pa, fa, ba⟩ => ?_
  obtain hsa := pa.scr hs
  obtain za := pa.zero hz
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hsa za 12 8 5 (by decide) (by decide)) fun b ⟨pb, fb, bb⟩ => ?_
  obtain hsb := pb.scr hsa
  obtain zb := pb.zero za
  obtain m12 : Sm b.mem base 12 := by rw [Sm]; omega_using [bb]
  obtain m13 : Sm b.mem base 13 := by rw [Sm, pb.fe (by decide)]; omega_using [ba]
  rw [WP.block_append_iff]
  refine WP.mono (diffSqr_ok hsb zb m13) fun c ⟨pc, fc, bc⟩ => ?_
  refine WP.mono (sumSqr_ok (pc.scr hsb) (pc.zero zb) (by rw [Sm, pc.fe (by decide)]; exact m12)
    (by rw [Sm, pc.fe (by decide)]; exact m13)) fun t ⟨pt, ft, bt⟩ => ?_
  obtain ea := pa.env
  obtain eb := pb.env
  obtain ec := pc.env
  obtain et := pt.env
  simp only [fa] at ea
  simp only [fb, ea, Function.update_apply, Fin.reduceEq, ite_false] at eb
  simp only [fc, eb, Function.update_apply, Fin.reduceEq, ite_true, ite_false] at ec
  simp only [ft, ec, Function.update_apply, Fin.reduceEq, ite_true, ite_false] at et
  refine ⟨et, bt, (pa.lf (by decide)).trans ((pb.lf (by decide)).trans ((pc.lf (by decide)).trans (pt.lf (by decide)))), ?_, ?_⟩
  · rw [pt.fe (by decide), pc.fe (by decide), pb.fe (by decide), pa.fe (by decide)]
  · rw [pt.fe (by decide), pc.fe (by decide), pb.fe (by decide), pa.fe (by decide)]

theorem back_indeps : Interleave.Indeps .x0 (backA.flatMap Interleave.expand)
    ((squares (offset 5) (offset 6)).flatMap Interleave.expand) :=
  Interleave.indeps_of_check (by decide +kernel)

/-- `backA`, and the squares of `A` and `B` beside it. -/
theorem woven_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (hc : Consts s.mem base) :
    WP isa (.block (VG.Impl.AArch64Weave.weave backA (squares (offset 5) (offset 6)))) s fun t =>
      let e := env s.mem base
      let DA := e 8 * e 5
      let CB := e 7 * e 6
      env t.mem base = Function.update (Function.update (Function.update (Function.update e 13 CB) 12 DA) 4
        ((DA - CB) * (DA - CB))) 3 ((DA + CB) * (DA + CB)) ∧
      fe t.mem base (offset 3) < 2 ^ 255 + 2 ^ 135 ∧ BF base s t ∧ OutLt t.mem base 0 ∧ OutLt t.mem base 1 ∧
      toFe (outVal t.mem base 0) = e 5 * e 5 ∧ toFe (outVal t.mem base 1) = e 6 * e 6 := by
  refine Interleave.WP.weavePairs back_indeps (WP.mono (backA_ok hs hz) fun a ⟨ea, ba, la, a5, a6⟩ => ?_)
  refine WP.mono (squares_ok (la.scr hs) (hc.outside (la.mem.mono (by decide) (by decide))) (a := offset 5) (b := offset 6)
    (by decide) (by decide) (by decide) (by decide)) fun t ⟨o, om, og, or, ow, op⟩ => ?_
  obtain ⟨o0, v0⟩ := o 0 (by decide)
  obtain ⟨o1, v1⟩ := o 1 (by decide)
  have ef : ∀ i : Fin 22, fe t.mem base (offset i) = fe a.mem base (offset i) := fun i =>
    om.fe (Or.inl (by simp only [offset, OUT]; omega_arith)) (by simp only [offset]; omega_arith)
  refine ⟨by rw [← ea]; funext i; exact congrArg toFe (ef i), by rw [ef 3]; exact ba,
    (BF.of_lf la).trans ⟨fun r _ => by rw [og], or, ow, op, om.mono (by decide) (by decide)⟩, o0, o1, ?_, ?_⟩
  · refine toFe_mul (v0.trans ?_)
    show fe a.mem base (offset 5) * fe a.mem base (offset 5) % _ = _
    rw [a5]
  · refine toFe_mul (v1.trans ?_)
    show fe a.mem base (offset 6) * fe a.mem base (offset 6) % _ = _
    rw [a6]

/-- The products of an iteration, from `A, B, C, D` in slots 5–8 and `x_1` in slot 0. -/
theorem back_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (hc : Consts s.mem base) :
    WP isa (.block back) s fun t =>
      let e := env s.mem base
      let AA := e 5 * e 5
      let BB := e 6 * e 6
      let E := AA - BB
      let DA := e 8 * e 5
      let CB := e 7 * e 6
      env t.mem base 0 = e 0 ∧ env t.mem base 1 = AA * BB ∧ env t.mem base 2 = E * (AA + Spec.X25519.a24 * E) ∧
      env t.mem base 3 = (DA + CB) * (DA + CB) ∧ env t.mem base 4 = e 0 * ((DA - CB) * (DA - CB)) ∧
      Sm4 t.mem base ∧ BF base s t := by
  rw [back, WP.block_append_iff]
  refine WP.mono (woven_ok hs hz hc) fun a ⟨ea, ba, la, o0, o1, v0, v1⟩ => ?_
  obtain hsa := la.scr hs
  obtain za := la.zero hz
  rw [WP.block_append_iff]
  refine WP.mono (packE_ok hsa za o0 o1) fun b ⟨eb, fb, lb⟩ => ?_
  obtain hsb := lb.scr hsa
  obtain zb := lb.zero za
  rw [WP.block_append_iff]
  refine WP.mono (mulSlots_ok hsb zb 1 9 10 (by decide) (by decide)) fun c ⟨pc, fc, bc⟩ => ?_
  obtain hsc := pc.scr hsb
  obtain zc := pc.zero zb
  rw [WP.block_append_iff]
  refine WP.mono (mulE_ok hsc zc) fun d ⟨pd, fd, bd⟩ => ?_
  refine WP.mono (mulSlots_ok (pd.scr hsc) (pd.zero zc) 4 0 4 (by decide) (by decide)) fun t ⟨pt, ft, bt⟩ => ?_
  obtain ec := pc.env
  obtain ed := pd.env
  obtain et := pt.env
  simp only [v0, v1] at eb
  simp only [fc] at ec
  simp only [fd] at ed
  simp only [ft] at et
  simp only [et, ed, ec, eb, ea, Function.update_apply, Fin.reduceEq, ite_true, ite_false]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Sm, pt.fe (by decide), pd.fe (by decide)]; omega_using [bc]
  · rw [Sm, pt.fe (by decide)]; omega_using [bd]
  · rw [Sm, pt.fe (by decide), pd.fe (by decide), pc.fe (by decide), fb _ (by decide) (by decide) (by decide)]; omega_using [ba]
  · rw [Sm]; omega_using [bt]
  · exact la.trans ((BF.of_lf lb).trans ((BF.of_lf (pc.lf (by decide))).trans ((BF.of_lf (pd.lf (by decide))).trans
      (BF.of_lf (pt.lf (by decide))))))

end VG.Proof.X25519.AArch64.Ladder
