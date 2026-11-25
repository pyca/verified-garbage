module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Pairs
public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Field elements in pairs of words, on AArch64: correctness

`ldp` and `stp` are two loads and two stores; the carry chains of sums and differences
(`sum3_value`, `sum4_value`, `diff4_value`), run on given registers by `sum_run` and `sum_done`;
and the products, by the rows' and the reduction's lemmas of `Field.lean`. An operation that
stores a slot changes it and the registers of `lclob` alone (`Put`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Pairs

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Pairs
open VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.X25519
variable {large : Bool}

/-! ## Loads and stores of pairs -/

/-- `ldp` is two loads. -/
theorem exec_ldp2 {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0) (hb : o ≤ 504)
    {a b : Reg} (hab : a ≠ b) (ha : a ≠ .x0) :
    exec (.ldp a b .x0 o) s = (exec (ld a o) s).bind (exec (ld b (o + 8))) := by
  have hw := workSize_ge large
  rw [load_sc hs ho (by omega_using [hb, hw]), Option.bind_some, load_sc (hs.write ha _) (by omega_using [ho]) (by omega_using [hb, hw])]
  have hin : ∀ d, d + 8 ≤ workSize large → InRegions (s.rd ++ s.wr) (off base d) 8 := fun d hd =>
    ⟨_, List.mem_append_right _ hs.wr, contains_scWith (large := large) hd⟩
  have e : base + BitVec.ofNat 64 o + 8 = off base (o + 8) := Offset.add_add ..
  simp only [exec, hab, ne_eq, not_false_eq_true, ho, hb, and_self, ite_true, hs.x0, State.load, e,
    hin o (by omega_using [hb, hw]), hin (o + 8) (by omega_using [hb, hw]), Option.bind_some, Option.map_some,
    RegUpd.mem_write, word, Mem.readW]

/-- `stp` is two stores. -/
theorem exec_stp2 {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0) (hb : o ≤ 504)
    (a b : Reg) : exec (.stp a b .x0 o) s = (exec (st a o) s).bind (exec (st b (o + 8))) := by
  have hw := workSize_ge large
  rw [store_sc hs ho (by omega_using [hb, hw]), Option.bind_some, store_sc (hs.setMem _) (by omega_using [ho]) (by omega_using [hb, hw])]
  have hin : ∀ d, d + 8 ≤ workSize large → InRegions s.wr (off base d) 8 := fun d hd =>
    ⟨_, hs.wr, contains_scWith (large := large) hd⟩
  have e : base + BitVec.ofNat 64 o + 8 = off base (o + 8) := Offset.add_add ..
  simp only [exec, ho, hb, and_self, ite_true, hs.x0, State.store, e,
    hin o (by omega_using [hb, hw]), hin (o + 8) (by omega_using [hb, hw]), Option.bind_some, State.read, Mem.writeW]
  rfl

theorem runBlock_bind2 (i j : Instr) (is : List Instr) (s : State) :
    runBlock isa (i :: j :: is) s = ((exec i s).bind (exec j)).bind (runBlock isa is) := by
  show (exec i s).bind (fun u => (exec j u).bind (runBlock isa is)) = _
  rw [Option.bind_assoc]

theorem loadPairs_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0) (hb : o ≤ 488)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (loadPairs o a b c d)) s fun t =>
      t.gpr a = word s.mem base o ∧ t.gpr b = word s.mem base (o + 8) ∧
      t.gpr c = word s.mem base (o + 16) ∧ t.gpr d = word s.mem base (o + 24) ∧
      Keeps [a, b, c, d] s t := by
  have hw := workSize_ge large
  obtain ⟨u, hu, hp⟩ := Interleave.runBlock_of_WP (loads_ok hs (o := o) ⟨ho, by omega_using [hb, hw]⟩ hd)
  refine WP.of_runBlock ⟨u, ?_, hp⟩
  rw [← hu]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, ha0⟩, ⟨hbc, hbd, hb0⟩, ⟨hcd, hc0⟩, ⟨hd0, _⟩⟩ := hd
  rw [loads, runBlock_bind2, ← exec_ldp2 hs ho (by omega_using [hb]) hab ha0]
  show (exec (.ldp a b .x0 o) s).bind _ = _
  refine Option.bind_congr fun v hv => ?_
  rw [exec_ldp2 hs ho (by omega_using [hb]) hab ha0, load_sc hs ho (by omega_using [hb, hw]), Option.bind_some,
    load_sc (hs.write ha0 _) (by omega_using [ho]) (by omega_using [hb, hw])] at hv
  cases hv
  rw [runBlock_bind2]
  show (exec (.ldp c d .x0 (o + 16)) _).bind _ = _
  rw [exec_ldp2 ((hs.write ha0 _).write hb0 _) (by omega_using [ho]) (by omega_using [hb]) hcd hc0]

theorem storePairs_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat} (ho : o % 8 = 0) (hb : o ≤ 488)
    (a b c d : Reg) :
    WP isa (.block (storePairs o a b c d)) s fun s' =>
      s' = { s with mem := st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) } := by
  have hw := workSize_ge large
  obtain ⟨u, hu, hp⟩ := Interleave.runBlock_of_WP (stores_ok hs (o := o) ⟨ho, by omega_using [hb, hw]⟩ a b c d)
  refine WP.of_runBlock ⟨u, ?_, hp⟩
  rw [← hu, stores, runBlock_bind2, ← exec_stp2 hs ho (by omega_using [hb])]
  show (exec (.stp a b .x0 o) s).bind _ = _
  refine Option.bind_congr fun v hv => ?_
  rw [exec_stp2 hs ho (by omega_using [hb]), store_sc hs ho (by omega_using [hb, hw]), Option.bind_some,
    store_sc (hs.setMem _) (by omega_using [ho]) (by omega_using [hb, hw])] at hv
  cases hv
  rw [runBlock_bind2]
  show (exec (.stp c d .x0 (o + 16)) _).bind _ = _
  rw [exec_stp2 ((hs.setMem _).setMem _) (by omega_using [ho]) (by omega_using [hb])]

/-! ## Sums and differences -/

/-- The word 38, as `movz` makes it. -/
theorem movz38 : BitVec.setWidth 64 (BitVec.setWidth 32 (38 : BitVec 16) <<< (16 * 0)) = (38 : Word) := by decide

/-- The sum's carry chain, its carry folded into the low three words. -/
theorem sum3_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 < 2 ^ 256 + 2 ^ 191) :
    let c0 := carryOut a0 b0 false
    let c1 := carryOut a1 b1 c0
    let c2 := carryOut a2 b2 c1
    let c3 := carryOut a3 b3 c2
    let u : Word := if c3 = true then 38 else 0
    let d0 := addCarry a0 b0 false
    let d1 := addCarry a1 b1 c0
    let d2 := addCarry a2 b2 c1
    let k0 := carryOut d0 u false
    let k1 := carryOut d1 0 k0
    toFe (val4 (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry a3 b3 c2)) =
      toFe (val4 a0 a1 a2 a3) + toFe (val4 b0 b1 b2 b3) := by
  intro c0 c1 c2 c3 u d0 d1 d2 k0 k1
  apply toFe_add
  obtain e : val4 d0 d1 d2 (addCarry a3 b3 c2) + 2 ^ 256 * c3.toNat = val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
    simpa only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] using add4_value a0 a1 a2 a3 b0 b1 b2 b3 false
  obtain f0 := addCarry_value d0 u false
  obtain f1 := addCarry_value d1 0 k0
  obtain f2 := addCarry_value d2 0 k1
  obtain hu : u.toNat = 38 * c3.toNat := carry38_sel c3
  obtain hc := Bool.toNat_le c3
  obtain hk := Bool.toNat_le (carryOut d2 0 k1)
  obtain z : (0 : Word).toNat = 0 := rfl
  obtain l0 := (addCarry d0 u false).isLt
  obtain l1 := (addCarry d1 0 k0).isLt
  obtain l2 := (addCarry d2 0 k1).isLt
  obtain m0 := d0.isLt
  obtain m1 := d1.isLt
  obtain m2 := d2.isLt
  obtain m3 := (addCarry a3 b3 c2).isLt
  rw [← e] at hb
  rw [show (val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3) =
    val4 (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry a3 b3 c2) +
      VG.Spec.X25519.P * (2 * c3.toNat) by
    rw [← e]
    simp only [VG.Spec.X25519.P, val4, Bool.toNat_false, Nat.add_zero, z, hu] at f0 f1 f2 hb ⊢
    change _ + 2 ^ 64 * k0.toNat = _ at f0
    change _ + 2 ^ 64 * k1.toNat = _ at f1
    rcases (show c3.toNat = 0 ∨ c3.toNat = 1 by omega_using [hc]) with h | h
    · rw [h] at f0 hb ⊢
      omega_using [f0, f1, f2, hk, l0, l1, l2, m0, m1, m2]
    · rw [h] at f0 hb ⊢
      omega_using [f0, f1, f2, hk, hb, l0, l1, l2, m0, m1, m2, m3], Nat.add_mul_mod_self_left]

/-- The difference's borrow chain, its borrow folded. -/
theorem diff4_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb : val4 b0 b1 b2 b3 < 2 ^ 256 - 38) :
    let c0 := carryOut a0 (~~~b0) true
    let c1 := carryOut a1 (~~~b1) c0
    let c2 := carryOut a2 (~~~b2) c1
    let c3 := carryOut a3 (~~~b3) c2
    let u : Word := if c3 = true then 0 else 38
    let d0 := addCarry a0 (~~~b0) true
    let d1 := addCarry a1 (~~~b1) c0
    let d2 := addCarry a2 (~~~b2) c1
    let d3 := addCarry a3 (~~~b3) c2
    let k0 := carryOut d0 (~~~u) true
    let k1 := carryOut d1 (~~~0) k0
    let k2 := carryOut d2 (~~~0) k1
    toFe (val4 (addCarry d0 (~~~u) true) (addCarry d1 (~~~0) k0) (addCarry d2 (~~~0) k1)
        (addCarry d3 (~~~0) k2)) = toFe (val4 a0 a1 a2 a3) - toFe (val4 b0 b1 b2 b3) := by
  intro c0 c1 c2 c3 u d0 d1 d2 d3 k0 k1 k2
  apply toFe_sub
  obtain e := sub4_value a0 a1 a2 a3 b0 b1 b2 b3 true
  obtain f := sub4_value d0 d1 d2 d3 u 0 0 0 true
  obtain hu : u.toNat = 38 * (1 - c3.toNat) := by
    show (if c3 = true then (0 : Word) else 38).toNat = _
    cases c3 <;> decide
  simp only [Bool.toNat_true, Nat.sub_self, Nat.add_zero] at e f
  obtain z : (0 : Word).toNat = 0 := rfl
  obtain hl := val4_lt (addCarry d0 (~~~u) true) (addCarry d1 (~~~0) k0) (addCarry d2 (~~~0) k1) (addCarry d3 (~~~0) k2)
  obtain hl1 := val4_lt d0 d1 d2 d3
  obtain hu' : val4 u 0 0 0 = 38 * (1 - c3.toNat) := by simp only [val4, z, hu]; omega_using []
  rw [hu'] at f
  change val4 d0 d1 d2 d3 + val4 b0 b1 b2 b3 = val4 a0 a1 a2 a3 + 2 ^ 256 * (1 - c3.toNat) at e
  change val4 (addCarry d0 (~~~u) true) (addCarry d1 (~~~0) k0) (addCarry d2 (~~~0) k1) (addCarry d3 (~~~0) k2) +
    38 * (1 - c3.toNat) = val4 d0 d1 d2 d3 + 2 ^ 256 * (1 - (carryOut d3 (~~~0) k2).toNat) at f
  generalize val4 (addCarry d0 (~~~u) true) (addCarry d1 (~~~0) k0) (addCarry d2 (~~~0) k1)
    (addCarry d3 (~~~0) k2) = R at *
  obtain hc := Bool.toNat_le c3
  obtain hk := Bool.toNat_le (carryOut d3 (~~~0) k2)
  rw [show R + val4 b0 b1 b2 b3 = val4 a0 a1 a2 a3 + VG.Spec.X25519.P * (2 * (1 - c3.toNat)) by
    simp only [VG.Spec.X25519.P]
    omega_using [e, f, hb, hl, hl1, hc, hk], Nat.add_mul_mod_self_left]

/-- The sum's carry chain, its carry folded into all four words. -/
theorem sum4_value (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 < 2 * 2 ^ 256 - 38) :
    let c0 := carryOut a0 b0 false
    let c1 := carryOut a1 b1 c0
    let c2 := carryOut a2 b2 c1
    let c3 := carryOut a3 b3 c2
    let u : Word := if c3 = true then 38 else 0
    let d0 := addCarry a0 b0 false
    let d1 := addCarry a1 b1 c0
    let d2 := addCarry a2 b2 c1
    let d3 := addCarry a3 b3 c2
    let k0 := carryOut d0 u false
    let k1 := carryOut d1 0 k0
    let k2 := carryOut d2 0 k1
    toFe (val4 (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry d3 0 k2)) =
      toFe (val4 a0 a1 a2 a3) + toFe (val4 b0 b1 b2 b3) := by
  intro c0 c1 c2 c3 u d0 d1 d2 d3 k0 k1 k2
  apply toFe_add
  obtain e : val4 d0 d1 d2 d3 + 2 ^ 256 * c3.toNat = val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 := by
    simpa only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] using add4_value a0 a1 a2 a3 b0 b1 b2 b3 false
  obtain f := add4_value d0 d1 d2 d3 u 0 0 0 false
  obtain hu : u.toNat = 38 * c3.toNat := carry38_sel c3
  obtain hu' : val4 u 0 0 0 = 38 * c3.toNat := by
    simp only [val4, show (0 : Word).toNat = 0 from rfl, hu]; omega_using []
  simp only [Bool.toNat_false, Nat.add_zero] at f
  rw [hu'] at f
  change val4 (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry d3 0 k2) +
    2 ^ 256 * (carryOut d3 0 k2).toNat = val4 d0 d1 d2 d3 + 38 * c3.toNat at f
  obtain hl := val4_lt (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry d3 0 k2)
  obtain hl1 := val4_lt d0 d1 d2 d3
  generalize val4 (addCarry d0 u false) (addCarry d1 0 k0) (addCarry d2 0 k1) (addCarry d3 0 k2) = R at *
  obtain hc := Bool.toNat_le c3
  obtain hk := Bool.toNat_le (carryOut d3 0 k2)
  rw [show val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3 = R + VG.Spec.X25519.P * (2 * c3.toNat) by
    simp only [VG.Spec.X25519.P]
    omega_using [e, f, hb, hl, hl1, hc, hk], Nat.add_mul_mod_self_left]

/-- The value of four registers. -/
abbrev v4 (s : State) (a b c d : Reg) : Nat := val4 (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d)

/-- Runs a block of `sum3` or `diff4`. -/
macro "sum_run" hz:term : tactic => `(tactic| plain_simp_names (
  apply WP.of_runBlock
  simp only [v4, sum3, sum4, diff4, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, $hz:term, show 16 * 0 < Size.w.bits from by decide,
    movz38, Option.some.injEq, exists_eq_left']))

/-- Closes what `sum_run` leaves, from the chain's value. -/
macro "sum_done" h:term : tactic => `(tactic| plain_simp_names (
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := $h
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps))

theorem sumReg_ok (s : State) (hz : s.gpr .x10 = 0)
    (hb : v4 s .x4 .x5 .x6 .x7 + v4 s .x21 .x22 .x23 .x24 < 2 ^ 256 + 2 ^ 191) :
    WP isa (.block (sum3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = toFe (v4 s .x4 .x5 .x6 .x7) + toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x12, .x13, .x14, .x15, .x2, .x3] s t := by
  sum_run hz
  sum_done (sum3_value _ _ _ _ _ _ _ _ hb)

theorem diffReg_ok (s : State) (hz : s.gpr .x10 = 0) (hb : v4 s .x21 .x22 .x23 .x24 < 2 ^ 256 - 38) :
    WP isa (.block (diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = toFe (v4 s .x4 .x5 .x6 .x7) - toFe (v4 s .x21 .x22 .x23 .x24) ∧
      Keeps [.x12, .x13, .x14, .x15, .x2, .x3] s t := by
  sum_run hz
  sum_done (diff4_value (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) _ _ _ _ hb)

/-! ## Selections -/

theorem ite_val4 (z : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val4 (if z = true then a0 else b0) (if z = true then a1 else b1) (if z = true then a2 else b2)
      (if z = true then a3 else b3) = if z = true then val4 a0 a1 a2 a3 else val4 b0 b1 b2 b3 := by
  cases z <;> rfl

theorem ite_bnot {α : Type} (z : Bool) (a b : α) :
    (if (!z) = true then a else b) = if z = true then b else a := by cases z <;> rfl

/-! ## What an operation keeps -/

/-- The registers the ladder's operations write. -/
def lclob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x20, .x21, .x22, .x23, .x24]

/-- The state `t` is `s` but for the registers of `lclob` and slot `o`. -/
structure Put (base : Addr) (o : Slot) (s t : State) : Prop where
  gpr : ∀ r, r ∉ lclob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base (offset o) 32 s.mem t.mem

theorem Put.scr {base : Addr} {o : Slot} {s t : State} (h : Put base o s t) (hs : Scr s base large) :
    Scr t base large := ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Put.zero {base : Addr} {o : Slot} {s t : State} (h : Put base o s t) (hz : s.gpr .x10 = 0) :
    t.gpr .x10 = 0 := (h.gpr _ (by decide)).trans hz

theorem Put.env {base : Addr} {o : Slot} {s t : State} (h : Put base o s t) :
    env t.mem base = Function.update (env s.mem base) o (F t.mem base (offset o)) := env_update o h.mem

theorem Put.fe {base : Addr} {o i : Slot} {s t : State} (h : Put base o s t) (hi : i ≠ o) :
    fe t.mem base (offset i) = fe s.mem base (offset i) := by
  have hne : i.val ≠ o.val := fun h => hi (Fin.ext h)
  exact h.mem.fe (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith)

theorem Put.of_keeps {base : Addr} {o : Slot} {rs : List Reg} {s t u : State} (k : Keeps rs s t)
    (hr : ∀ r ∈ rs, r ∈ lclob) (h : Put base o t u) : Put base o s u :=
  ⟨fun r h' => (h.gpr r h').trans (k.gpr r fun hm => h' (hr r hm)), h.rd.trans k.rd, h.wr.trans k.wr,
    h.sp.trans k.sp, k.mem ▸ h.mem⟩

/-- The slots' element `o` from four registers. -/
theorem putPairs_ok {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (ho : o.val < 14) (a b c d : Reg) :
    WP isa (.block (storePairs (offset o) a b c d)) s fun t =>
      Put base o s t ∧ t.gpr = s.gpr ∧ fe t.mem base (offset o) = v4 s a b c d := by
  refine WP.mono (storePairs_ok hs (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith) a b c d)
    fun t ht => ?_
  subst t
  exact ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, st4_outside _ _ (by simp only [offset]; omega_arith) _ _ _ _⟩, rfl,
    fe_st4 _ _ (by simp only [offset]; omega_arith) _ _ _ _⟩

theorem getPairs_ok {s : State} {base : Addr} (hs : Scr s base large) (o : Slot) (ho : o.val < 14)
    {a b c d : Reg} (hd : ([a, b, c, d, .x0] : List Reg).Nodup) :
    WP isa (.block (loadPairs (offset o) a b c d)) s fun t =>
      v4 t a b c d = fe s.mem base (offset o) ∧ Keeps [a, b, c, d] s t :=
  WP.mono (loadPairs_ok hs (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith) hd)
    fun t ⟨e0, e1, e2, e3, k⟩ => ⟨by rw [v4, e0, e1, e2, e3], k⟩

/-! ## Products -/

theorem toSlot_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o : Slot) (ho : o.val < 14) :
    WP isa (.block (toSlot o)) s fun t => Put base o s t ∧ F t.mem base (offset o) = toFe (wide s) ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 := by
  rw [toSlot, WP.block_append_iff]
  refine WP.mono (reduceWide_ok s hz) fun u ⟨e, _, k, b⟩ => ?_
  refine WP.mono (putPairs_ok (hs.of_keeps k (by decide)) o ho _ _ _ _) fun t ⟨p, _, h⟩ => ?_
  exact ⟨Put.of_keeps k (by decide) p, by rw [F, h]; exact e, by rw [h]; exact b⟩

/-- A product into slot `o`, which leaves its operand in `x12`–`x15`. -/
theorem mulKeep_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o a : Slot)
    (ho : o.val < 14) :
    WP isa (.block (mulInto o a)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = env s.mem base a * toFe (v4 s .x12 .x13 .x14 .x15) ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 ∧ v4 t .x12 .x13 .x14 .x15 = v4 s .x12 .x13 .x14 .x15 := by
  rw [mulInto, toSlot, WP.block_append_iff]
  refine WP.mono (mulRows_ok hs (slot_rangeWith a) hz rfl) fun u ⟨e, k⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceWide_ok u ((k.gpr _ (by decide)).trans hz)) fun v ⟨ev, _, kv, bv⟩ => ?_
  refine WP.mono (putPairs_ok ((hs.of_keeps k (by decide)).of_keeps kv (by decide)) o ho _ _ _ _) fun t ⟨p, g, h⟩ => ?_
  refine ⟨Put.of_keeps k (by decide) (Put.of_keeps kv (by decide) p), ?_, by rw [h]; exact bv, ?_⟩
  · rw [F, h, show toFe (v4 v .x4 .x5 .x6 .x7) = toFe (wide u) from ev, e]; exact toFe_mul rfl
  · rw [v4, g, kv.gpr _ (by decide), kv.gpr _ (by decide), kv.gpr _ (by decide), kv.gpr _ (by decide),
      k.gpr _ (by decide), k.gpr _ (by decide), k.gpr _ (by decide), k.gpr _ (by decide)]

theorem mulInto_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o a : Slot)
    (ho : o.val < 14) :
    WP isa (.block (mulInto o a)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = env s.mem base a * toFe (v4 s .x12 .x13 .x14 .x15) ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 :=
  WP.mono (mulKeep_ok hs hz o a ho) fun _ ⟨p, h, b, _⟩ => ⟨p, h, b⟩

/-- A product of slots, which leaves the second operand in `x12`–`x15`. -/
theorem mulSlotsKeep_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o a b : Slot)
    (ho : o.val < 14) (hb : b.val < 14) :
    WP isa (.block (mulSlots o a b)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = env s.mem base a * env s.mem base b ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 ∧ v4 t .x12 .x13 .x14 .x15 = fe s.mem base (offset b) := by
  rw [mulSlots, WP.block_append_iff]
  refine WP.mono (getPairs_ok hs b hb (by decide)) fun u ⟨e, k⟩ => ?_
  refine WP.mono (mulKeep_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) o a ho) fun t ⟨p, h, l, kt⟩ => ?_
  exact ⟨Put.of_keeps k (by decide) p, by rw [h, e, k.mem]; rfl, l, kt.trans e⟩

theorem mulSlots_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o a b : Slot)
    (ho : o.val < 14) (hb : b.val < 14) :
    WP isa (.block (mulSlots o a b)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = env s.mem base a * env s.mem base b ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 :=
  WP.mono (mulSlotsKeep_ok hs hz o a b ho hb) fun _ ⟨p, h, l, _⟩ => ⟨p, h, l⟩

theorem squareRegs_ok (s : State) (hz : s.gpr .x10 = 0) :
    WP isa (.block squareRegs) s fun t =>
      wide t = v4 s .x12 .x13 .x14 .x15 * v4 s .x12 .x13 .x14 .x15 ∧
      Keeps [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x16, .x17, .x21, .x22, .x23, .x24] s t := by
  simp only [squareRegs, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sqrCross_ok s hz) fun s₂ ⟨e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sqrDouble_ok s₂ ((k2.gpr _ (by decide)).trans hz)) fun s₃ ⟨e3, k3⟩ => ?_
  refine WP.mono (sqrDiag_ok s₃) fun s₄ ⟨c, e4, k4⟩ => ?_
  refine ⟨?_, ((k2.mono (by decide)).trans (k3.mono (by decide))).trans (k4.mono (by decide))⟩
  obtain A : ∀ r ∈ [Reg.x12, .x13, .x14, .x15], s₃.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (k3.gpr _ (by decide)).trans (k2.gpr _ (by decide))
  rw [A .x12 (by decide), A .x13 (by decide), A .x14 (by decide), A .x15 (by decide), e3, e2] at e4
  obtain hlt : v4 s .x12 .x13 .x14 .x15 * v4 s .x12 .x13 .x14 .x15 < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  obtain hx := sq_expand (s.gpr .x12).toNat (s.gpr .x13).toNat (s.gpr .x14).toNat (s.gpr .x15).toNat
  dsimp only [wide]
  rw [show v4 s .x12 .x13 .x14 .x15 * v4 s .x12 .x13 .x14 .x15 = _ from hx] at hlt ⊢
  omega_using [e4, hlt]

theorem squareTo_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o : Slot)
    (ho : o.val < 14) :
    WP isa (.block (squareRegs ++ toSlot o)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = toFe (v4 s .x12 .x13 .x14 .x15) * toFe (v4 s .x12 .x13 .x14 .x15) ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 := by
  rw [WP.block_append_iff]
  refine WP.mono (squareRegs_ok s hz) fun u ⟨e, k⟩ => ?_
  refine WP.mono (toSlot_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) o ho) fun t ⟨p, h, b⟩ => ?_
  exact ⟨Put.of_keeps k (by decide) p, by rw [h, e]; exact toFe_mul rfl, b⟩

theorem sqrSlots_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (o a : Slot)
    (ho : o.val < 14) (ha : a.val < 14) :
    WP isa (.block (sqrSlots o a)) s fun t => Put base o s t ∧
      F t.mem base (offset o) = env s.mem base a * env s.mem base a ∧
      fe t.mem base (offset o) < 2 ^ 255 + 2 ^ 135 := by
  rw [sqrSlots, List.append_assoc, WP.block_append_iff]
  refine WP.mono (getPairs_ok hs a ha (by decide)) fun u ⟨e, k⟩ => ?_
  refine WP.mono (squareTo_ok (hs.of_keeps k (by decide)) ((k.gpr _ (by decide)).trans hz) o ho) fun t ⟨p, h, l⟩ => ?_
  exact ⟨Put.of_keeps k (by decide) p, by rw [h, e]; rfl, l⟩

/-! ## The sums of an iteration's products -/

/-- Elements below this fold once. -/
abbrev Sm (m : Mem) (base : Addr) (i : Slot) : Prop := fe m base (offset i) < 2 ^ 255 + 2 ^ 136

theorem two_ok {s : State} {base : Addr} (hs : Scr s base large) (a b : Slot) (ha : a.val < 14) (hb : b.val < 14) :
    WP isa (.block (loadPairs (offset a) .x4 .x5 .x6 .x7 ++ loadPairs (offset b) .x21 .x22 .x23 .x24)) s fun t =>
      v4 t .x4 .x5 .x6 .x7 = fe s.mem base (offset a) ∧ v4 t .x21 .x22 .x23 .x24 = fe s.mem base (offset b) ∧
      Keeps [.x4, .x5, .x6, .x7, .x21, .x22, .x23, .x24] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (getPairs_ok hs a ha (by decide)) fun u ⟨e, k⟩ => ?_
  refine WP.mono (getPairs_ok (hs.of_keeps k (by decide)) b hb (by decide)) fun t ⟨f, l⟩ => ?_
  refine ⟨?_, by rw [f, k.mem], (k.mono (by decide)).trans (l.mono (by decide))⟩
  rw [v4, l.gpr _ (by decide), l.gpr _ (by decide), l.gpr _ (by decide), l.gpr _ (by decide)]
  exact e

theorem diffRegs_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (a b : Slot)
    (ha : a.val < 14) (hb : b.val < 14) (sb : Sm s.mem base b) :
    WP isa (.block (loadPairs (offset a) .x4 .x5 .x6 .x7 ++ loadPairs (offset b) .x21 .x22 .x23 .x24 ++
        diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = env s.mem base a - env s.mem base b ∧ Keeps lclob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (two_ok hs a b ha hb) fun u ⟨ea, eb, k⟩ => ?_
  refine WP.mono (diffReg_ok u ((k.gpr _ (by decide)).trans hz) (by rw [eb]; omega_using [sb])) fun t ⟨e, l⟩ => ?_
  exact ⟨by rw [e, ea, eb]; rfl, (k.mono (by decide)).trans (l.mono (by decide))⟩

theorem sumRegs_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x10 = 0) (a b : Slot)
    (ha : a.val < 14) (hb : b.val < 14) (sa : Sm s.mem base a) (sb : Sm s.mem base b) :
    WP isa (.block (loadPairs (offset a) .x4 .x5 .x6 .x7 ++ loadPairs (offset b) .x21 .x22 .x23 .x24 ++
        sum3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3)) s fun t =>
      toFe (v4 t .x12 .x13 .x14 .x15) = env s.mem base a + env s.mem base b ∧ Keeps lclob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (two_ok hs a b ha hb) fun u ⟨ea, eb, k⟩ => ?_
  refine WP.mono (sumReg_ok u ((k.gpr _ (by decide)).trans hz) (by rw [ea, eb]; omega_using [sa, sb])) fun t ⟨e, l⟩ => ?_
  exact ⟨by rw [e, ea, eb]; rfl, (k.mono (by decide)).trans (l.mono (by decide))⟩

/-- The state `t` is `s` but for the registers of `lclob` and slots 0–13. -/
structure LF (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ lclob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 448 s.mem t.mem

theorem LF.trans {base : Addr} {s t u : State} (h : LF base s t) (k : LF base t u) : LF base s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem LF.of_keeps {base : Addr} {rs : List Reg} {s t : State} (k : Keeps rs s t) (hr : ∀ r ∈ rs, r ∈ lclob) :
    LF base s t :=
  ⟨fun r h => k.gpr r fun hm => h (hr r hm), k.rd, k.wr, k.sp, by rw [k.mem]; exact Outside.refl _ _ _ _⟩

theorem Put.lf {base : Addr} {o : Slot} {s t : State} (h : Put base o s t) (ho : o.val < 14) : LF base s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by simp only [offset]; omega_arith) (by simp only [offset]; omega_arith)⟩

theorem LF.scr {base : Addr} {s t : State} (h : LF base s t) (hs : Scr s base large) : Scr t base large :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem LF.zero {base : Addr} {s t : State} (h : LF base s t) (hz : s.gpr .x10 = 0) : t.gpr .x10 = 0 :=
  (h.gpr _ (by decide)).trans hz

theorem movs_ok (s : State) :
    WP isa (.block [mov .x12 .x4, mov .x13 .x5, mov .x14 .x6, mov .x15 .x7]) s fun t =>
      v4 t .x12 .x13 .x14 .x15 = v4 s .x4 .x5 .x6 .x7 ∧ Keeps [.x12, .x13, .x14, .x15] s t := by
  apply WP.of_runBlock
  simp only [mov, v4, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (0 : Nat) < 4096 by decide,
    BitVec.add_zero, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.Ed25519.AArch64.Pairs
