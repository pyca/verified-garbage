module
public import VerifiedGarbage.Impl.Bignum.Arm.WindowExp
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Proof.Bignum.Arm.WindowTable

import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Building the table of the windowed ARMv7 exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem rest_round {rs : List Reg} {s t : State} (h : Rest rs s t) : Rest roundClobbers s t :=
  h.mono fun r _ => by cases r <;> simp [roundClobbers]

/-- The exponentiation's own controls: the exponent's pointer and count, the
bits left in the byte and the byte. -/
def KeepsExp (base : BitVec 32) (m m' : Mem) : Prop :=
  ∀ e ∈ [128, 132, 192, 200], m'.readW (off (State.addr base) e) 32 = m.readW (off (State.addr base) e) 32

theorem KeepsExp.refl (base : BitVec 32) (m : Mem) : KeepsExp base m m := fun _ _ => rfl

theorem KeepsExp.trans {base : BitVec 32} {m₁ m₂ m₃ : Mem} (h₁ : KeepsExp base m₁ m₂)
    (h₂ : KeepsExp base m₂ m₃) : KeepsExp base m₁ m₃ := fun e he => (h₂ e he).trans (h₁ e he)

theorem KeepsExp.of_keeps {m m' : Mem} {base : BitVec 32} {len w o : Nat}
    (keep : Keeps (State.addr base) len w o m m') (size : 256 ≤ 8 * len) : KeepsExp base m m' := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact keeps_header_readW keep size (by decide)

theorem KeepsExp.of_outside {m m' : Mem} {base : BitVec 32} {o n : Nat}
    (outside : Outside (State.addr base) o n m m') (ho : 204 ≤ o) : KeepsExp base m m' := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> exact outside_read32 outside (Or.inl (by omega_arith)) (by omega_arith)

/-- A header word that neither of two writes touches. -/
theorem read_after_writes (m : Mem) (base : BitVec 32) {d e a : Nat} (v u : BitVec 32)
    (hd : a + 4 ≤ d ∨ d + 4 ≤ a) (he : a + 4 ≤ e ∨ e + 4 ≤ a) (fit : d + 4 ≤ 256) (fit' : e + 4 ≤ 256)
    (fa : a + 4 ≤ 256) :
    ((m.writeW (off (State.addr base) d) v).writeW (off (State.addr base) e) u).readW
      (off (State.addr base) a) 32 = m.readW (off (State.addr base) a) 32 := by
  have o1 := writeW32_outside m (State.addr base) (d := d) v (by omega_arith)
  have o2 := writeW32_outside (m.writeW (off (State.addr base) d) v) (State.addr base) (d := e) u (by omega_arith)
  rw [outside_read32 o2 he (by omega_arith), outside_read32 o1 hd (by omega_arith)]

/-- Writes to header words 196 and later (the window's controls) alone. -/
theorem KeepsExp.of_writes (m : Mem) (base : BitVec 32) {d e : Nat} (v u : BitVec 32)
    (hd : 204 ≤ d ∨ d = 196) (hd' : d + 4 ≤ 256) (he : 204 ≤ e ∨ e = 196) (he' : e + 4 ≤ 256) :
    KeepsExp base m ((m.writeW (off (State.addr base) d) v).writeW (off (State.addr base) e) u) := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  have o1 := writeW32_outside m (State.addr base) (d := d) v (by omega_arith)
  have o2 := writeW32_outside (m.writeW (off (State.addr base) d) v) (State.addr base) (d := e) u (by omega_arith)
  rw [outside_read32 o2 (by omega_arith) (by omega_arith), outside_read32 o1 (by omega_arith) (by omega_arith)]

/-- The table's first `j` entries are built, array 1 holds `x^(j-1) R`, and
the controls point to entry `j`. -/
structure BuildInv (base : BitVec 32) (len w M x j : Nat) (s : State) : Prop where
  power : ExpState base len w M x 0 s
  table : TableHolds s.mem base w M x j
  fits : arrAt w 16 ≤ 8 * len
  prodBound : numAt s.mem (State.addr base) w 1 < M
  prodValue : numAt s.mem (State.addr base) w 1 % M = x ^ (j - 1) * 2 ^ (64 * w) % M
  entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))
  index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j

theorem header_after_writes (m : Mem) (base : BitVec 32) (v u : BitVec 32) :
    ((m.writeW (off (State.addr base) 220) v).writeW (off (State.addr base) 228) u).readW
        (off (State.addr base) 220) 32 = v ∧
      ((m.writeW (off (State.addr base) 220) v).writeW (off (State.addr base) 228) u).readW
        (off (State.addr base) 228) 32 = u := by
  have outside := writeW32_outside (m.writeW (off (State.addr base) 220) v) (State.addr base) (d := 228) u
    (by decide)
  exact ⟨by rw [outside_read32 outside (d := 220) (by decide) (by decide), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _⟩

/-- Array `a` copied to entry `j`, then the controls moved to entry `j + 1`:
the exponentiation's state, the entries before `j` and array 1 are kept. -/
theorem entryStep_ok (s : State) {base : BitVec 32} {len w M x E a j : Nat}
    (h : ExpState base len w M x E s) (table : TableHolds s.mem base w M x j) (fits : arrAt w 16 ≤ 8 * len)
    (ha : a < 8) (hj : j < 8)
    (entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j)))
    (index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j)
    (bound : numAt s.mem (State.addr base) w a < M)
    (value : numAt s.mem (State.addr base) w a % M = x ^ j * 2 ^ (64 * w) % M) :
    WP isa (.seq (entryCopy a) (.block entryNext)) s fun t => ExpState base len w M x E t ∧
      TableHolds t.mem base w M x (j + 1) ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 ∧
      t.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))) ∧
      t.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 (j + 1) ∧
      t.z = decide (j + 1 = 8) ∧ KeepsExp base s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  have fe := Nat.le_trans (array_end_le (w := w) (show 8 + j < 16 by omega_arith)) fits
  have sepHdr (d : Nat) (hd : d + 4 ≤ 256) : d + 4 ≤ arrAt w (8 + j) := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith
  rw [WP.seq_iff]
  refine WP.mono (entryCopy_ok s h.ready fits ha hj entry) ?_
  rintro u ⟨ready, copied, outside, keeps, frameU, restU⟩
  have power := h.after_other ready keeps (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  have entryU : u.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j)) := by
    rw [outside_read32 outside (Or.inl (sepHdr 220 (by decide))) (by omega_arith)]; exact entry
  have indexU : u.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j := by
    rw [outside_read32 outside (Or.inl (sepHdr 228 (by decide))) (by omega_arith)]; exact index
  have tableU : TableHolds u.mem base w M x (j + 1) := by
    intro i hi
    by_cases e : i = j
    · subst e; rw [copied]; exact ⟨bound, value⟩
    · rw [outside_num outside fits nowrap (by omega_arith) (by omega_arith)]; exact table i (by omega_arith)
  have prodU := outside_num outside fits nowrap (q := 1) (by omega_arith) (by omega_arith)
  refine WP.mono (entryNext_ok u ready hj entryU indexU) ?_
  rintro t ⟨memT, zT, restT⟩
  have ctl : CtlOnly base u.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have ptr : t.gpr .r0 = base := (restT.gpr .r0 (by simp)).trans ready.ptr
  obtain ⟨powerT, frameT⟩ := power.after_ctl ctl restT ptr
  obtain ⟨e220, e228⟩ := header_after_writes u.mem base (base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))))
    (BitVec.ofNat 32 (j + 1))
  have keeps : KeepsExp base s.mem t.mem :=
    (KeepsExp.of_outside outside (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith)).trans (by
      rw [memT]; exact KeepsExp.of_writes _ _ _ _ (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide))
  refine ⟨powerT, tableU.after_ctl ctl fits nowrap (by omega_arith), ?_, by rw [memT]; exact e220,
    by rw [memT]; exact e228, zT, keeps, frameU.trans frameT, restU.trans (rest_round restT)⟩
  rw [ctl_num (len := len) ctl (Nat.le_trans (arrAt_le (by decide)) fits) nowrap, prodU]

/-- One entry of the loop: `[1] := [1] · x R`, then copied to entry `j`. -/
theorem tableBody_ok (s : State) {base : BitVec 32} {len w M x j : Nat}
    (h : BuildInv base len w M x j s) (hj : 2 ≤ j) (hj' : j < 8) :
    WP isa tableBody s fun t => BuildInv base len w M x (j + 1) t ∧ t.z = decide (j + 1 = 8) ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith) fits
  rw [tableBody, WP.seq_iff]
  refine WP.mono (montOp_ok s h.power.ready (o := 1) (a := 1) (b := 5)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.power.modulus]; exact h.power.inputBound)) ?_
  rintro u ⟨ready, modulus, bound, value, keeps, frameU, restU⟩
  rw [h.power.modulus] at bound value
  have power := h.power.after_other ready keeps (by decide) (by decide) (by decide) (by decide) (by decide)
  have prod : numAt u.mem (State.addr base) w 1 % M = x ^ j * 2 ^ (64 * w) % M := by
    have := mont_mulx h.power.coprime h.prodValue h.power.inputValue value
    rwa [show j - 1 + 1 = j by omega_arith] at this
  have entryU := (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.entry
  have indexU := (keeps_header_readW keeps size (d := 228) (bits := 32) (by decide)).trans h.index
  refine WP.mono (entryStep_ok u power (h.table.of_keeps keeps fits (by decide) (by omega_arith)) fits
    (a := 1) (by decide) hj' entryU indexU bound prod) ?_
  rintro t ⟨powerT, tableT, prodT, entryT, indexT, zT, keepsT, frameT, restT⟩
  refine ⟨⟨powerT, tableT, fits, by rw [prodT]; exact bound, ?_, entryT, indexT⟩, zT,
    (KeepsExp.of_keeps keeps size).trans keepsT, frameU.trans frameT, restU.trans restT⟩
  rw [prodT, show j + 1 - 1 = j by omega_arith]
  exact prod

theorem tableLoop_ok (s : State) {base : BitVec 32} {len w M x : Nat} (h : BuildInv base len w M x 2 s) :
    WP isa (.loop tableBody .ne) s fun t => BuildInv base len w M x 8 t ∧ KeepsExp base s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ 2 ≤ j ∧ BuildInv base len w M x j t ∧
    KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M := isa) inv ?_ 6 s ?_
  · intro k t hk
    obtain ⟨j, hjk, hk, hj, hi, keeps, frame, rest⟩ := hk
    refine WP.mono (tableBody_ok t hi hj (by omega_arith)) ?_
    rintro u ⟨hu, hz, keepsU, frameU, restU⟩
    by_cases he : j + 1 = 8
    · left
      refine ⟨?_, he ▸ hu, keeps.trans keepsU, frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, j + 1, by omega_arith, by omega_arith, by omega_arith, hu, keeps.trans keepsU, frame.trans frameU,
        rest.trans restU⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨2, rfl, by decide, Nat.le_refl _, h, KeepsExp.refl _ _, Frame.refl _ _, Rest.refl _ _⟩

/-- Before entry `j` is built. -/
structure TablePre (base : BitVec 32) (len w M x j : Nat) (s : State) : Prop where
  power : ExpState base len w M x 0 s
  table : TableHolds s.mem base w M x j
  fits : arrAt w 16 ≤ 8 * len
  entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))
  index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j

theorem tableStage0_ok (s : State) {base : BitVec 32} {len w M x : Nat}
    (h : ExpState base len w M x 0 s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa (.block tableInit) s fun t => TablePre base len w M x 0 t ∧ KeepsExp base s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (tableInit_ok s h.ready) ?_
  rintro u ⟨memU, restU⟩
  have ctl : CtlOnly base s.mem u.mem := by
    rw [memU]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerU, frameU⟩ := h.after_ctl ctl restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  obtain ⟨e220, e228⟩ := header_after_writes s.mem base (base + BitVec.ofNat 32 (arrAt w (8 + 0)))
    (BitVec.ofNat 32 0)
  rw [← memU] at e220 e228
  refine ⟨⟨powerU, fun _ hi => absurd hi (Nat.not_lt_zero _), fits, e220, e228⟩, ?_, frameU, rest_round restU⟩
  rw [memU]; exact KeepsExp.of_writes _ _ _ _ (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide)

theorem tableStageStep_ok (s : State) {base : BitVec 32} {len w M x a j : Nat}
    (h : TablePre base len w M x j s) (ha : a < 8) (hj : j < 8)
    (bound : numAt s.mem (State.addr base) w a < M)
    (value : numAt s.mem (State.addr base) w a % M = x ^ j * 2 ^ (64 * w) % M) :
    WP isa (.seq (entryCopy a) (.block entryNext)) s fun t => TablePre base len w M x (j + 1) t ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t :=
  WP.mono (entryStep_ok s h.power h.table h.fits ha hj h.entry h.index bound value)
    fun _ ⟨power, table, _, entry, index, _, keeps, frame, rest⟩ =>
      ⟨⟨power, table, h.fits, entry, index⟩, keeps, frame, rest⟩

/-- Array 1 `:= x R`, for the loop. -/
theorem prodInit_ok (s : State) {base : BitVec 32} {len w M x : Nat} (h : TablePre base len w M x 2 s) :
    WP isa (.seq (.block [.mov .r11 (.imm 1)]) (selectArray 1 1 5)) s fun t => BuildInv base len w M x 2 t ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  rw [WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun z c => WP.block_nil ?_
  have readyZ : ArithmeticReady base len w z :=
    h.power.ready.of_mem c.mem (c.rest (ws := [.r11]) (by simp)) ((c.other .r0 (by decide)).trans h.power.ready.ptr)
  refine WP.mono (selectArray_ok z readyZ.workspace readyZ.layout readyZ.width readyZ.ptr
    (o := 1) (a := 1) (b := 5) (by decide) (by decide) (by decide) (by rw [c.gpr]; decide)
    readyZ.stackRead readyZ.stackSep readyZ.saved) ?_
  rintro q ⟨_, _, value, outside, frameQ, restQ, ptrQ⟩
  rw [c.gpr] at value
  have keeps := outside_array_keeps outside (len := len) (by omega_arith)
  have readyQ := (readyZ.after_array (by decide) keeps frameQ restQ ptrQ).1
  rw [c.mem] at keeps outside frameQ
  have powerQ := h.power.after_other readyQ keeps (by decide) (by decide) (by decide) (by decide) (by decide)
  have sepHdr (d : Nat) (hd : d + 4 ≤ 256) : d + 4 ≤ arrAt w 1 := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith
  have tableQ : TableHolds q.mem base w M x 2 := by
    intro i hi
    rw [outside_num outside fits nowrap (by omega_arith) (by omega_arith)]
    exact h.table i hi
  refine ⟨⟨powerQ, tableQ, fits, ?_, ?_, ?_, ?_⟩,
    KeepsExp.of_outside outside (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith), frameQ,
    (rest_round (c.rest (ws := [.r11]) (by simp))).trans restQ⟩
  · rw [value, c.mem]; exact h.power.inputBound
  · rw [value, c.mem, show 2 - 1 = 1 from rfl, Nat.pow_one]; exact h.power.inputValue
  · rw [outside_read32 outside (Or.inl (sepHdr 220 (by decide))) (by omega_arith)]; exact h.entry
  · rw [outside_read32 outside (Or.inl (sepHdr 228 (by decide))) (by omega_arith)]; exact h.index

/-- The table built from the encoded input: `T[j] = x^j R mod M`. -/
theorem tableBuild_ok (s : State) {base : BitVec 32} {len w M x : Nat}
    (h : ExpState base len w M x 0 s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa tableBuild s fun t => ExpState base len w M x 0 t ∧ TableHolds t.mem base w M x 8 ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [tableBuild, WP.seq_iff]
  refine WP.mono (tableStage0_ok s h fits) ?_
  rintro u ⟨preU, keepsU, frameU, restU⟩
  have step0 := tableStageStep_ok u preU (a := 6) (by decide) (by decide) preU.power.powerBound
    preU.power.powerValue
  rw [WP.seq_iff] at step0
  rw [WP.seq_iff]
  refine WP.mono step0 fun v hv => ?_
  rw [WP.seq_iff]
  refine WP.mono hv ?_
  rintro v ⟨preV, keepsV, frameV, restV⟩
  have step1 := tableStageStep_ok v preV (a := 5) (by decide) (by decide) preV.power.inputBound
    (by rw [Nat.pow_one]; exact preV.power.inputValue)
  rw [WP.seq_iff] at step1
  rw [WP.seq_iff]
  refine WP.mono step1 fun y hy => ?_
  rw [WP.seq_iff]
  refine WP.mono hy ?_
  rintro y ⟨preY, keepsY, frameY, restY⟩
  have init := prodInit_ok y preY
  rw [WP.seq_iff] at init
  rw [WP.seq_iff]
  refine WP.mono init fun z hz => ?_
  rw [WP.seq_iff]
  refine WP.mono hz ?_
  rintro q ⟨inv, keepsQ, frameQ, restQ⟩
  refine WP.mono (tableLoop_ok q inv) ?_
  rintro t ⟨invT, keepsT, frameT, restT⟩
  exact ⟨invT.power, invT.table, keepsU.trans (keepsV.trans (keepsY.trans (keepsQ.trans keepsT))),
    frameU.trans (frameV.trans (frameY.trans (frameQ.trans frameT))),
    restU.trans (restV.trans (restY.trans (restQ.trans restT)))⟩

end VG.Proof.Bignum.Arm
