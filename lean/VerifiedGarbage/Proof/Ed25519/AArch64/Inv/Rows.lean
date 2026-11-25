module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
public import VerifiedGarbage.Proof.Mont.AArch64.Words
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Divstep.SignedWords
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Ed25519 and X25519 on AArch64: the rows of the inversion's update

The blocks of a batch's update as arithmetic on the row (`row`, `x2`, `x3`,
`x8`–`x10`) and the operand (`opd`, `x11`–`x14`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Divstep

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Divstep
open VG.Proof.Ed25519.AArch64 Word64
open VG.Proof.Mont.AArch64 (KeepRegs)

variable {large : Bool}

/-! ## Loads and stores -/

theorem ldp_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) {t1 t2 : Reg} (ht : t1 ≠ t2) :
    exec (.ldp t1 t2 .x0 d) s = some ((s.write .x t1 (word s.mem base d)).write .x t2
      (word s.mem base (d + 8))) := by
  have := workSize_ge large
  have e8 : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have h1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    rw [hs.x0]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  have h2 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d + 8) 8 := by
    rw [hs.x0, e8, Offset.add_add]
    exact ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  simp only [exec, ne_eq, ht, not_false_eq_true, ha, hd, and_self, ite_true, State.load, h1, h2,
    Option.bind_some, Option.map_some, BitVec.setWidth_eq]
  rw [hs.x0, e8, Offset.add_add]
  rfl

theorem stp_ok {s : State} {base : Addr} (hs : Scr s base large) {d : Nat}
    (ha : d % 8 = 0) (hd : d ≤ 504) (t1 t2 : Reg) :
    exec (.stp t1 t2 .x0 d) s = some { s with
      mem := (s.mem.writeW (off base d) (s.gpr t1)).writeW (off base (d + 8)) (s.gpr t2) } := by
  have := workSize_ge large
  have e8 : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have h1 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    rw [hs.x0]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  have h2 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d + 8) 8 := by
    rw [hs.x0, e8, Offset.add_add]
    exact ⟨_, hs.wr, contains_scWith (large := large) (by omega_using [hd, this])⟩
  simp only [exec, ha, hd, and_self, ite_true, State.store, h1, Option.bind_some, read_x, BitVec.setWidth_eq]
  simp only [h2]
  rw [hs.x0, e8, Offset.add_add]
  rfl

/-- Offsets of `ldp` and `stp`. -/
abbrev Off4 (o : Nat) : Prop := o % 8 = 0 ∧ o ≤ 488

theorem ldp4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (ldp4 o a b c d)) s fun t =>
      t.gpr a = word s.mem base o ∧ t.gpr b = word s.mem base (o + 8) ∧
      t.gpr c = word s.mem base (o + 16) ∧ t.gpr d = word s.mem base (o + 24) ∧
      Keeps [a, b, c, d] s t := by
  obtain ⟨halign, hbound⟩ := ho
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, ha0⟩, ⟨hbc, hbd, hb0⟩, ⟨hcd, hc0⟩, ⟨hd0, _⟩⟩ := hd
  apply WP.of_runBlock
  simp only [ldp4, runBlock_cons, runStep_some, runBlock_nil,
    ldp_ok hs halign (by omega_using [hbound]) hab,
    ldp_ok ((hs.write ha0 _).write hb0 _) (show (o + 16) % 8 = 0 by omega_using [halign]) (by omega_using [hbound]) hcd,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_write, had, hac, hab, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hbd, hbc, ite_false, ite_true, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, hcd, ite_false, ite_true, BitVec.setWidth_eq, RegUpd.mem_write]
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.mem_write]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem stp4_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) (a b c d : Reg) :
    WP isa (.block (stp4 o a b c d)) s fun s' =>
      s' = { s with mem := st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) } := by
  obtain ⟨halign, hbound⟩ := ho
  apply WP.of_runBlock
  simp only [stp4, runBlock_cons, runStep_some, runBlock_nil,
    stp_ok hs halign (by omega_using [hbound]),
    stp_ok (hs.setMem _) (show (o + 16) % 8 = 0 by omega_using [halign]) (by omega_using [hbound]),
    Option.some.injEq, exists_eq_left']
  rfl

/-! ## The row and the operand -/

/-- The row's value. -/
def row (s : State) : Nat :=
  val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10).toNat

/-- The operand's value. -/
def opd (s : State) : Nat := val4 (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)

/-- Its four low words'. -/
def lo (s : State) : Nat := val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9)

theorem lo_lt (s : State) : lo s < 2 ^ 256 := val4_lt _ _ _ _

theorem row_lt (s : State) : row s < 2 ^ 256 * 2 ^ 64 := by
  have := val4_lt (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9)
  have := (s.gpr .x10).isLt
  unfold row; omega_arith

theorem opd_lt (s : State) : opd s < 2 ^ 256 := val4_lt _ _ _ _

theorem opd_keeps {rs : List Reg} {s t : State} (k : Keeps rs s t) (h : .x11 ∉ rs ∧ .x12 ∉ rs ∧ .x13 ∉ rs ∧ .x14 ∉ rs) :
    opd t = opd s := by
  unfold opd; rw [k.gpr _ h.1, k.gpr _ h.2.1, k.gpr _ h.2.2.1, k.gpr _ h.2.2.2]

theorem row_keeps {rs : List Reg} {s t : State} (k : Keeps rs s t)
    (h : .x2 ∉ rs ∧ .x3 ∉ rs ∧ .x8 ∉ rs ∧ .x9 ∉ rs ∧ .x10 ∉ rs) : row t = row s := by
  unfold row
  rw [k.gpr _ h.1, k.gpr _ h.2.1, k.gpr _ h.2.2.1, k.gpr _ h.2.2.2.1, k.gpr _ h.2.2.2.2]

/-- The operand from memory. -/
theorem ldOpd_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : Off4 o) :
    WP isa (.block (ldp4 o .x11 .x12 .x13 .x14)) s fun t =>
      opd t = fe s.mem base o ∧ Keeps [.x11, .x12, .x13, .x14] s t :=
  WP.mono (ldp4_ok hs ho (by decide)) fun t ⟨a, b, c, d, k⟩ => ⟨by unfold opd; rw [a, b, c, d], k⟩

/-! ## Products -/

theorem mulFirst_arith {L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3 R1 R2 R3 R4 D1 D2 D3 D4 : Nat}
    (f1 : R1 + 2 ^ 64 * D1 = H0 + L1 + 0) (f2 : R2 + 2 ^ 64 * D2 = H1 + L2 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = H2 + L3 + D2) (f4 : R4 + 2 ^ 64 * D4 = H3 + 0 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3)
    (p0 : P0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p1 : P1 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1))
    (p2 : P2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (p3 : P3 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) :
    L0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 =
      P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3 := by
  omega_using [f1, f2, f3, f4, m0, m1, m2, m3, p0, p1, p2, p3]

theorem mulFirst_value (a b0 b1 b2 b3 : Word) :
    let d1 := carryOut (mulHi a b0) (a * b1) false
    let d2 := carryOut (mulHi a b1) (a * b2) d1
    let d3 := carryOut (mulHi a b2) (a * b3) d2
    val4 (a * b0) (addCarry (mulHi a b0) (a * b1) false)
        (addCarry (mulHi a b1) (a * b2) d1) (addCarry (mulHi a b2) (a * b3) d2) +
        2 ^ 256 * (addCarry (mulHi a b3) 0 d3).toNat =
      a.toNat * val4 b0 b1 b2 b3 := by
  intro d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact mulFirst_arith (addCarry_value (mulHi a b0) (a * b1) false)
    (addCarry_value (mulHi a b1) (a * b2) d1) (addCarry_value (mulHi a b2) (a * b3) d2)
    (addCarry_value (mulHi a b3) 0 d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)
    (mul_le a b0) (mul_le a b1) (mul_le a b2) (mul_le a b3)

/-- The registers the products write. -/
abbrev rowRegs : List Reg := [.x2, .x3, .x8, .x9, .x10, .x15]

/-- What the frame of a straight block of register arithmetic needs. -/
macro "row_frame" : tactic => `(tactic| plain_simp_names (
  exact ⟨by reg_keeps, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩))

theorem mulFirst_ok (s : State) {u : Reg} (hu : u = .x4 ∨ u = .x6) (hz : s.gpr .x16 = 0) :
    WP isa (.block (mulFirst u)) s fun t =>
      row t = (s.gpr u).toNat * opd s ∧ Keeps rowRegs s t := by
  have h := fun a => mulFirst_value a (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14)
  dsimp only [addCarry, carryOut, mulHi] at h
  apply WP.of_runBlock
  rcases hu with rfl | rfl <;>
  · simp only [mulFirst, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write, row, opd,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    exact ⟨h _, by row_frame⟩

theorem mulAcc_arith {T0 T1 T2 T3 T4 L0 L1 L2 L3 H0 H1 H2 H3 P0 P1 P2 P3
    S0 S1 S2 S3 U R1 R2 R3 R4 C0 C1 C2 C3 C4 D1 D2 D3 D4 : Nat}
    (e0 : S0 + 2 ^ 64 * C0 = T0 + L0 + 0) (e1 : S1 + 2 ^ 64 * C1 = T1 + L1 + C0)
    (e2 : S2 + 2 ^ 64 * C2 = T2 + L2 + C1) (e3 : S3 + 2 ^ 64 * C3 = T3 + L3 + C2)
    (e4 : U + 2 ^ 64 * C4 = T4 + 0 + C3)
    (f1 : R1 + 2 ^ 64 * D1 = S1 + H0 + 0) (f2 : R2 + 2 ^ 64 * D2 = S2 + H1 + D1)
    (f3 : R3 + 2 ^ 64 * D3 = S3 + H2 + D2) (f4 : R4 + 2 ^ 64 * D4 = U + H3 + D3)
    (m0 : L0 + 2 ^ 64 * H0 = P0) (m1 : L1 + 2 ^ 64 * H1 = P1)
    (m2 : L2 + 2 ^ 64 * H2 = P2) (m3 : L3 + 2 ^ 64 * H3 = P3) :
    S0 + 2 ^ 64 * R1 + 2 ^ 128 * R2 + 2 ^ 192 * R3 + 2 ^ 256 * R4 + 2 ^ 256 * 2 ^ 64 * (C4 + D4) =
      T0 + 2 ^ 64 * T1 + 2 ^ 128 * T2 + 2 ^ 192 * T3 + 2 ^ 256 * T4 +
        (P0 + 2 ^ 64 * P1 + 2 ^ 128 * P2 + 2 ^ 192 * P3) := by
  omega_using [e0, e1, e2, e3, e4, f1, f2, f3, f4, m0, m1, m2, m3]

theorem mulAcc_value (a b0 b1 b2 b3 t0 t1 t2 t3 t4 : Word) :
    let c0 := carryOut t0 (a * b0) false
    let c1 := carryOut t1 (a * b1) c0
    let c2 := carryOut t2 (a * b2) c1
    let c3 := carryOut t3 (a * b3) c2
    let s1 := addCarry t1 (a * b1) c0
    let s2 := addCarry t2 (a * b2) c1
    let s3 := addCarry t3 (a * b3) c2
    let u := addCarry t4 0 c3
    let d1 := carryOut s1 (mulHi a b0) false
    let d2 := carryOut s2 (mulHi a b1) d1
    let d3 := carryOut s3 (mulHi a b2) d2
    ∃ k, val4 (addCarry t0 (a * b0) false) (addCarry s1 (mulHi a b0) false)
        (addCarry s2 (mulHi a b1) d1) (addCarry s3 (mulHi a b2) d2) +
        2 ^ 256 * (addCarry u (mulHi a b3) d3).toNat + 2 ^ 256 * 2 ^ 64 * k =
      val4 t0 t1 t2 t3 + 2 ^ 256 * t4.toNat + a.toNat * val4 b0 b1 b2 b3 := by
  intro c0 c1 c2 c3 s1 s2 s3 u d1 d2 d3
  simp only [val4]
  rw [mul_val4]
  exact ⟨_, mulAcc_arith (addCarry_value t0 (a * b0) false) (addCarry_value t1 (a * b1) c0)
    (addCarry_value t2 (a * b2) c1) (addCarry_value t3 (a * b3) c2) (addCarry_value t4 0 c3)
    (addCarry_value s1 (mulHi a b0) false) (addCarry_value s2 (mulHi a b1) d1)
    (addCarry_value s3 (mulHi a b2) d2) (addCarry_value u (mulHi a b3) d3)
    (mul_lo_hi a b0) (mul_lo_hi a b1) (mul_lo_hi a b2) (mul_lo_hi a b3)⟩

theorem mulAcc_ok (s : State) {v : Reg} (hv : v = .x5 ∨ v = .x7) (hz : s.gpr .x16 = 0) :
    WP isa (.block (mulAcc v)) s fun t =>
      (∃ k, row t + 2 ^ 256 * 2 ^ 64 * k = row s + (s.gpr v).toNat * opd s) ∧ Keeps rowRegs s t := by
  have h := fun a => mulAcc_value a (s.gpr .x11) (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x2) (s.gpr .x3)
    (s.gpr .x8) (s.gpr .x9) (s.gpr .x10)
  dsimp only [addCarry, carryOut, mulHi] at h
  apply WP.of_runBlock
  rcases hv with rfl | rfl <;>
  · simp only [mulAcc, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, ↓RegUpd.c_write, row, opd,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    exact ⟨h _, by row_frame⟩

/-! ## Signs -/

/-- Four words' value in two's complement. -/
def sv (X : Nat) : Int := if X < 2 ^ 255 then X else X - 2 ^ 256

theorem opd_msb (s : State) : (s.gpr .x14).msb = decide (2 ^ 255 ≤ opd s) := by
  have := (s.gpr .x11).isLt; have := (s.gpr .x12).isLt; have := (s.gpr .x13).isLt; have := (s.gpr .x14).isLt
  rw [BitVec.msb_eq_decide]
  apply decide_eq_decide.mpr
  unfold opd val4
  constructor <;> intro <;> omega_arith

theorem signed_ok (s : State) {u : Reg} (hu : u ∈ [Reg.x4, .x5, .x6, .x7]) (hz : s.gpr .x16 = 0) :
    WP isa (.block (signed u)) s fun t =>
      (∃ k, row t + 2 ^ 256 * (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) = row s + 2 ^ 256 * 2 ^ 64 * k) ∧
      Keeps [.x10, .x15] s t := by
  have hm := opd_msb s
  apply WP.of_runBlock
  have fin : ∀ w : Word, w = (if (s.gpr .x14).msb = true then s.gpr u else 0) →
      ∃ k, val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10 - w).toNat +
        2 ^ 256 * (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) =
      val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) + 2 ^ 256 * (s.gpr .x10).toNat + 2 ^ 256 * 2 ^ 64 * k := by
    intro w hw
    have e : (if 2 ^ 255 ≤ opd s then (s.gpr u).toNat else 0) = w.toNat := by
      rw [hw, hm]
      by_cases h : 2 ^ 255 ≤ opd s
      · simp only [h, decide_true, ↓reduceIte]
      · simp only [h, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl
    rw [e, BitVec.toNat_sub]
    have h1 := w.isLt
    have h2 := (s.gpr .x10).isLt
    generalize val4 (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) = V
    generalize (s.gpr .x10).toNat = x at *
    generalize w.toNat = y at *
    by_cases h : y ≤ x
    · exact ⟨0, by omega_using [h1, h2, h]⟩
    · exact ⟨1, by omega_using [h1, h2, h]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
  · simp only [signed, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, CondCode.holds,
      ↓RegUpd.gpr_write, row, BitVec.and_self,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
    refine ⟨fin _ rfl, ?_, rfl, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

/-! ## Sums, differences and shifts -/

theorem addOpd_ok (s : State) :
    WP isa (.block addOpd) s fun t =>
      (∃ k, lo t + 2 ^ 256 * k = lo s + opd s) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have h := add4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14) false
  dsimp only [addCarry, carryOut] at h
  apply WP.of_runBlock
  simp only [addOpd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨_, h⟩, by row_frame⟩

theorem subOpd_ok (s : State) :
    WP isa (.block subOpd) s fun t =>
      (∃ k, lo t + opd s = lo s + 2 ^ 256 * k) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have h := sub4_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14) true
  dsimp only [addCarry, carryOut] at h
  apply WP.of_runBlock
  simp only [subOpd, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, opd,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨⟨_, h⟩, by row_frame⟩

theorem shift_arith {t0 t1 t2 t3 t4 : Nat} (h4 : t4 < 2 ^ 64) :
    (t0 / 2 ^ 59 + 2 ^ 5 * (t1 % 2 ^ 59)) + 2 ^ 64 * (t1 / 2 ^ 59 + 2 ^ 5 * (t2 % 2 ^ 59)) +
      2 ^ 128 * (t2 / 2 ^ 59 + 2 ^ 5 * (t3 % 2 ^ 59)) + 2 ^ 192 * (t3 / 2 ^ 59 + 2 ^ 5 * (t4 % 2 ^ 59)) +
      2 ^ 256 * (t4 / 2 ^ 59) =
    (t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4) / 2 ^ 59 := by
  omega_using [h4]

theorem shift_ok (s : State) :
    WP isa (.block shift) s fun t =>
      (∃ k, lo t + 2 ^ 256 * k = row s / 2 ^ 59) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  apply WP.of_runBlock
  simp only [shift, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, lo, row, show 59 < Size.x.bits from by decide, val4,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨(s.gpr .x10).toNat / 2 ^ 59, ?_⟩, by row_frame⟩
  rw [← shift_arith (s.gpr .x10).isLt]
  dsimp only [Size.bits]
  rw [Divstep.extr59, Divstep.extr59, Divstep.extr59, Divstep.extr59]

/-! ## The offset of `a` and `b`'s rows -/

theorem twoP_ok (s : State) (hz : s.gpr .x16 = 0) :
    WP isa (.block twoP) s fun t =>
      t.gpr .x15 = BitVec.ofNat 64 (2 ^ 64 - 38) ∧ t.gpr .x17 = BitVec.ofNat 64 (2 ^ 64 - 1) ∧
      Keeps [.x15, .x17] s t := by
  apply WP.of_runBlock
  simp only [twoP, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, show 16 * 0 < Size.x.bits from by decide, show (1 : Nat) < 4096 from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨by decide, by decide, by row_frame⟩

/-- `2 p` less a number at most `2 p`. -/
theorem negRow_ok (s : State) (h15 : s.gpr .x15 = BitVec.ofNat 64 (2 ^ 64 - 38))
    (h17 : s.gpr .x17 = BitVec.ofNat 64 (2 ^ 64 - 1)) (h : lo s ≤ 2 ^ 256 - 38) :
    WP isa (.block negRow) s fun t =>
      lo t + lo s = 2 ^ 256 - 38 ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
  have e := sub4_value (s.gpr .x15) (s.gpr .x17) (s.gpr .x17) (s.gpr .x17)
    (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) true
  have c : val4 (s.gpr .x15) (s.gpr .x17) (s.gpr .x17) (s.gpr .x17) = 2 ^ 256 - 38 := by rw [h15, h17]; decide
  rw [c] at e
  dsimp only [addCarry, carryOut] at e
  have run : WP isa (.block negRow) s fun t =>
      (∃ k, lo t + lo s = 2 ^ 256 - 38 + 2 ^ 256 * k) ∧ Keeps [.x2, .x3, .x8, .x9] s t := by
    apply WP.of_runBlock
    simp only [negRow, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo,
      BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
    exact ⟨⟨_, e⟩, by row_frame⟩
  refine WP.mono run fun t ⟨⟨k, hk⟩, kt⟩ => ⟨?_, kt⟩
  have := lo_lt t
  omega_using [hk, this, h]

theorem extr5 (s0 s1 : BitVec 64) :
    ((s1 ++ s0).extractLsb' 5 64).toNat = s0.toNat / 2 ^ 5 + 2 ^ 59 * (s1.toNat % 2 ^ 5) := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt s0.isLt, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := s0.isLt; have := s1.isLt
  omega_using []

theorem lsl59 (w : BitVec 64) : (w <<< 59).toNat = 2 ^ 59 * (w.toNat % 2 ^ 5) := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega_using []

/-- The five words of `x11`–`x15`. -/
def off5 (s : State) : Nat := opd s + 2 ^ 256 * (s.gpr .x15).toNat

theorem subShift_arith {d0 d1 d2 d3 d4 L O k : Nat}
    (e : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + O + (1 - true.toNat) = L + 2 ^ 256 * k) (hk : k ≤ 1)
    (h4 : d4 = (2 ^ 64 - 1) * k) :
    2 ^ 59 * (d0 % 2 ^ 5) + 2 ^ 64 * (d0 / 2 ^ 5 + 2 ^ 59 * (d1 % 2 ^ 5)) +
      2 ^ 128 * (d1 / 2 ^ 5 + 2 ^ 59 * (d2 % 2 ^ 5)) + 2 ^ 192 * (d2 / 2 ^ 5 + 2 ^ 59 * (d3 % 2 ^ 5)) +
      2 ^ 256 * (d3 / 2 ^ 5 + 2 ^ 59 * (d4 % 2 ^ 5)) + 2 ^ 59 * O = 2 ^ 59 * L + 2 ^ 256 * 2 ^ 64 * k := by
  have e : d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + O = L + 2 ^ 256 * k := e
  omega_using [e, hk, h4]

theorem subShift_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let c0 := carryOut a0 (~~~b0) true
    let c1 := carryOut a1 (~~~b1) c0
    let c2 := carryOut a2 (~~~b2) c1
    let c3 := carryOut a3 (~~~b3) c2
    let d0 := addCarry a0 (~~~b0) true
    let d1 := addCarry a1 (~~~b1) c0
    let d2 := addCarry a2 (~~~b2) c1
    let d3 := addCarry a3 (~~~b3) c2
    let d4 := addCarry 0 (~~~0) c3
    ∃ k, val4 (d0 <<< 59) ((d1 ++ d0).extractLsb' 5 64) ((d2 ++ d1).extractLsb' 5 64) ((d3 ++ d2).extractLsb' 5 64) +
      2 ^ 256 * ((d4 ++ d3).extractLsb' 5 64).toNat + 2 ^ 59 * val4 b0 b1 b2 b3 =
        2 ^ 59 * val4 a0 a1 a2 a3 + 2 ^ 256 * 2 ^ 64 * k := by
  intro c0 c1 c2 c3 d0 d1 d2 d3 d4
  have e : val4 d0 d1 d2 d3 + val4 b0 b1 b2 b3 + (1 - true.toNat) = val4 a0 a1 a2 a3 + 2 ^ 256 * (1 - c3.toNat) :=
    sub4_value a0 a1 a2 a3 b0 b1 b2 b3 true
  have m : d4.toNat = (2 ^ 64 - 1) * (1 - c3.toNat) := by
    show (addCarry 0 (~~~0) c3).toNat = _
    cases c3 <;> decide
  refine ⟨1 - c3.toNat, ?_⟩
  simp only [val4]
  rw [extr5, extr5, extr5, extr5, lsl59]
  exact subShift_arith e (Nat.sub_le _ _) m

theorem subShift_ok (s : State) (hz : s.gpr .x16 = 0) :
    WP isa (.block subShift) s fun t =>
      (∃ k, off5 t + 2 ^ 59 * opd s = 2 ^ 59 * lo s + 2 ^ 256 * 2 ^ 64 * k) ∧ t.gpr .x17 = 19 ∧
      Keeps [.x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x17] s t := by
  have e := subShift_value (s.gpr .x2) (s.gpr .x3) (s.gpr .x8) (s.gpr .x9) (s.gpr .x11) (s.gpr .x12) (s.gpr .x13)
    (s.gpr .x14)
  dsimp only [addCarry, carryOut] at e
  apply WP.of_runBlock
  simp only [subShift, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, off5, opd,
    show 59 < Size.x.bits from by decide, show 5 < Size.x.bits from by decide,
    show 16 * 0 < Size.x.bits from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  exact ⟨e, by decide, by row_frame⟩

/-! ## The fold -/

theorem fold_arith {t0 t1 t2 t3 t4 e0 e1 e2 e3 e4 r0 r1 r2 r3 r4 c0 c1 c2 c3 c4 : Nat}
    {y cy h ch x9 l k P s0 s1 s2 s3 d0 d1 d2 d3 W K : Nat}
    (a0 : r0 + 2 ^ 64 * c0 = t0 + e0 + 0) (a1 : r1 + 2 ^ 64 * c1 = t1 + e1 + c0)
    (a2 : r2 + 2 ^ 64 * c2 = t2 + e2 + c1) (a3 : r3 + 2 ^ 64 * c3 = t3 + e3 + c2)
    (a4 : r4 + 2 ^ 64 * c4 = t4 + e4 + c3)
    (lr0 : r0 < 2 ^ 64) (lr1 : r1 < 2 ^ 64) (lr2 : r2 < 2 ^ 64) (lr3 : r3 < 2 ^ 64) (lr4 : r4 < 2 ^ 64)
    (b0 : y + 2 ^ 64 * cy = r3 + r3 + 0) (ly : y < 2 ^ 64) (b1 : h + 2 ^ 64 * ch = r4 + r4 + cy)
    (b2 : x9 = y / 2)
    (mk : l + 2 ^ 64 * k = P) (hP : P = h * 19)
    (d0e : s0 + 2 ^ 64 * d0 = r0 + l + 0) (d1e : s1 + 2 ^ 64 * d1 = r1 + k + d0)
    (d2e : s2 + 2 ^ 64 * d2 = r2 + 0 + d1) (d3e : s3 + 2 ^ 64 * d3 = x9 + 0 + d2)
    (hW : t0 + 2 ^ 64 * t1 + 2 ^ 128 * t2 + 2 ^ 192 * t3 + 2 ^ 256 * t4 +
      (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 + 2 ^ 256 * e4) = W + 2 ^ 256 * 2 ^ 64 * K)
    (lW : W < 2 ^ 256 * 2 ^ 61) :
    s0 + 2 ^ 64 * s1 + 2 ^ 128 * s2 + 2 ^ 192 * s3 = W % 2 ^ 255 + 19 * (W / 2 ^ 255) := by
  have lk : k < 2 ^ 64 := by omega_using [mk, hP, b1, lr4, b0, lr3, ly]
  have eW : W = r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * r3 + 2 ^ 256 * r4 := by
    omega_using [a0, a1, a2, a3, a4, lr0, lr1, lr2, lr3, lr4, hW, lW]
  have l4 : r4 < 2 ^ 61 := by omega_using [eW, lW]
  have eh : h = 2 * r4 + cy := by omega_using [b1, l4, b0, lr3]
  have e3 : x9 + 2 ^ 63 * cy = r3 := by omega_using [b0, b2, ly]
  have lx : x9 < 2 ^ 63 := by omega_using [b2, ly]
  have q : W / 2 ^ 255 = h := by
    rw [eW, ← e3, eh]; omega_using [lr0, lr1, lr2, lx]
  have m : W % 2 ^ 255 = r0 + 2 ^ 64 * r1 + 2 ^ 128 * r2 + 2 ^ 192 * x9 := by
    rw [eW, ← e3]; omega_using [lr0, lr1, lr2, lx]
  rw [q, m]
  omega_using [d0e, d1e, d2e, d3e, mk, hP, eh, l4, lx, lr0, lr1, lr2, b0, lr3]

theorem lsr1 (w : BitVec 64) : (w >>> 1).toNat = w.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem fold_ok (s : State) (hz : s.gpr .x16 = 0) (h17 : s.gpr .x17 = 19) {W K : Nat}
    (hW : row s + off5 s = W + 2 ^ 256 * 2 ^ 64 * K) (lW : W < 2 ^ 256 * 2 ^ 61) :
    WP isa (.block fold) s fun t =>
      lo t = W % 2 ^ 255 + 19 * (W / 2 ^ 255) ∧ Keeps [.x2, .x3, .x8, .x9, .x10, .x11, .x12] s t := by
  apply WP.of_runBlock
  simp only [fold, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    ↓RegUpd.gpr_write, ↓RegUpd.gpr_addWithCarry, ↓RegUpd.c_addWithCarry, lo, val4,
    show 1 < Size.x.bits from by decide, hz,
    BitVec.setWidth_eq, ↓reduceIte, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by row_frame⟩
  dsimp only [Size.bits]
  refine fold_arith (addCarry_value (s.gpr .x2) (s.gpr .x11) false) (addCarry_value (s.gpr .x3) (s.gpr .x12) _)
    (addCarry_value (s.gpr .x8) (s.gpr .x13) _) (addCarry_value (s.gpr .x9) (s.gpr .x14) _)
    (addCarry_value (s.gpr .x10) (s.gpr .x15) _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (addCarry_value _ _ false) (BitVec.isLt _) (addCarry_value _ _ _) (lsr1 _)
    (mul_lo_hi _ _) (by rw [h17]; rfl) (addCarry_value _ _ false) (addCarry_value _ _ _) (addCarry_value _ _ _)
    (addCarry_value _ _ _) hW lW

end VG.Proof.Ed25519.AArch64.Divstep
