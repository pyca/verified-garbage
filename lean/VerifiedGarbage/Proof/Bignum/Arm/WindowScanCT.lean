module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectCT
import VerifiedGarbage.Proof.Bignum.Arm.SelectArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! ### `Bignum.Arm.WindowBuildCT`, which this module and modules that import it used -/

section

/-! # Building the table leaks only public addresses and counts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

/-- A selection whose pointers and count agree, then the workspace pointer
from the stack. -/
theorem selectStep_ct :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r10 = t.gpr .r10 ∧ s.gpr .r12 = t.gpr .r12 ∧
      s.gpr .lr = t.gpr .lr ∧ s.sp = t.sp) (.seq selectRow (.block [.ldrSp .r0 0])) (fun _ _ => True) := by
  have sub : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r10 = t.gpr .r10 ∧
      s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr ∧ s.sp = t.sp) selectRow (fun _ _ => True) :=
    fun s t tr1 tr2 u v h e1 e2 =>
      ⟨selectRow_ct s t tr1 tr2 u v trivial trivial ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ e1 e2, trivial⟩
  exact (relCT_keep_sp sub (fun _ _ h => h.2.2.2.2)).seq ((loadStack_ct .r0 0).mono (fun _ _ h => h)
    (fun _ _ _ => trivial))

/-- The registers of a selection from `a` or `b` to `o`. -/
def SelectRegs (base : BitVec 32) (w o a b : Nat) (s : State) : Prop :=
  s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧ s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a) ∧
    s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)

theorem selectRegs_ct {base : BitVec 32} {w o a b : Nat} :
    RelCT isa (fun s t => SelectRegs base w o a b s ∧ SelectRegs base w o a b t ∧ s.sp = t.sp)
      (.seq selectRow (.block [.ldrSp .r0 0])) (fun _ _ => True) :=
  selectStep_ct.mono (fun _ _ h => ⟨h.1.1.trans h.2.1.1.symm, h.1.2.1.trans h.2.1.2.1.symm,
    h.1.2.2.1.trans h.2.1.2.2.1.symm, h.1.2.2.2.trans h.2.1.2.2.2.symm, h.2.2⟩) (fun _ _ h => h)

/-- Ready, with the controls at entry `j`. -/
def EntryReady (base : BitVec 32) (len w j : Nat) (s : State) : Prop :=
  ArithmeticReady base len w s ∧
    s.mem.readW (VG.Proof.Mont.off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))

theorem entryCopy_ct {base : BitVec 32} {len w a j : Nat} (ha : a < 8) :
    RelCT isa (fun s t => EntryReady base len w j s ∧ EntryReady base len w j t ∧ s.sp = t.sp)
      (entryCopy a) (fun _ _ => True) := by
  unfold entryCopy
  refine relCT_chain (Q₁ := SelectRegs base w (8 + j) (8 + j) a) (Q₂ := SelectRegs base w (8 + j) (8 + j) a)
    ((entryCopyArgs_ct a ha).mono (fun _ _ h => h.1.1.ptr.trans h.2.1.1.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (entryCopyArgs_ok s h.1 ha h.2) fun _ j => ⟨j.2.2.2.1, j.2.2.2.2.1, j.2.1, j.2.2.1⟩)
    (fun s h => WP.mono (entryCopyArgs_ok s h.1 ha h.2) fun _ j => ⟨j.2.2.2.1, j.2.2.2.2.1, j.2.1, j.2.2.1⟩)
    selectRegs_ct

/-- An entry copied, then the controls advanced. -/
theorem entryStepCT {base : BitVec 32} {len w a j : Nat} (ha : a < 8) (hj : j < 8) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => EntryReady base len w j s ∧ EntryReady base len w j t ∧ s.sp = t.sp)
      (.seq (entryCopy a) (.block entryNext)) (fun _ _ => True) :=
  relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base) (entryCopy_ct ha)
    (fun s h => WP.mono (entryCopy_ok s h.1 fits ha hj h.2) fun _ k => k.1.ptr)
    (fun s h => WP.mono (entryCopy_ok s h.1 fits ha hj h.2) fun _ k => k.1.ptr)
    (entryNext_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem tableBody_ct {base : BitVec 32} {len w M1 M2 x1 x2 j : Nat} (hj : j < 8)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => BuildInv base len w M1 x1 j s ∧ BuildInv base len w M2 x2 j t ∧ s.sp = t.sp)
      tableBody (fun _ _ => True) := by
  have entryOf (s : State) {M x : Nat} (h : BuildInv base len w M x j s) :
      WP isa (montOp 1 1 5) s (EntryReady base len w j) := by
    have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) h.fits
    refine WP.mono (montOp_ok s h.power.ready (o := 1) (a := 1) (b := 5)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
      (by rw [h.power.modulus]; exact h.power.inputBound)) ?_
    rintro t ⟨ready, _, _, _, keeps, _, _⟩
    exact ⟨ready, (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.entry⟩
  unfold tableBody
  exact relCT_chain (Q₁ := EntryReady base len w j) (Q₂ := EntryReady base len w j)
    ((montOp_ct (base := base) (o := 1) (a := 1) (b := 5)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit).mono
      (fun _ _ h => ⟨⟨h.1.power.ready, by rw [h.1.power.modulus]; exact h.1.power.inputBound⟩,
        ⟨h.2.1.power.ready, by rw [h.2.1.power.modulus]; exact h.2.1.power.inputBound⟩, h.2.2⟩)
      (fun _ _ h => h))
    (fun s h => entryOf s h) (fun s h => entryOf s h) (entryStepCT (by decide) hj fits)

theorem tableLoop_ct {base : BitVec 32} {len w M1 M2 x1 x2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => BuildInv base len w M1 x1 2 s ∧ BuildInv base len w M2 x2 2 t ∧ s.sp = t.sp)
      (.loop tableBody .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧ 2 ≤ j ∧
    BuildInv base len w M1 x1 j s ∧ BuildInv base len w M2 x2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) tableBody fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hj, hs, ht, sp⟩ := h
    have ct := relCT_keep_sp (tableBody_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (j := j)
      (by omega_using [jk, hk]) fit fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _⟩ := tableBody_ok s hs hj (by omega_using [jk, hk])
    obtain ⟨_, _, run2, next2, zero2, _, _⟩ := tableBody_ok t ht hj (by omega_using [jk, hk])
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], by omega_using [hj], next1, next2, sp'⟩
  exact (RelCT.loop I step 6).mono
    (fun _ _ h => ⟨2, rfl, by decide, Nat.le_refl _, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

theorem prodInit_ct {base : BitVec 32} {len w M1 M2 x1 x2 : Nat} :
    RelCT isa (fun s t => TablePre base len w M1 x1 2 s ∧ TablePre base len w M2 x2 2 t ∧ s.sp = t.sp)
      (.seq (.block [.mov .r11 (.imm 1)]) (selectArray 1 1 5)) (fun _ _ => True) := by
  have ready (s : State) {M x : Nat} (h : TablePre base len w M x 2 s) :
      WP isa (.block [.mov .r11 (.imm 1)]) s (SelectArrayReady base len w) :=
    wp_mov (op2_imm (by decide)) fun z c => WP.block_nil
      ⟨h.power.ready.workspace.congr c.wr, by rw [c.mem]; exact h.power.ready.layout,
        by rw [c.mem]; exact h.power.ready.width, (c.other .r0 (by decide)).trans h.power.ready.ptr⟩
  exact relCT_chain (setBit_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm)
    (fun _ _ h => h)) (fun s h => ready s h) (fun s h => ready s h)
    (selectArray_ct (by decide) (by decide) (by decide))

theorem tableBuild_ct {base : BitVec 32} {len w M1 M2 x1 x2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState base len w M1 x1 0 s ∧ ExpState base len w M2 x2 0 t ∧ s.sp = t.sp)
      tableBuild (fun _ _ => True) := by
  have entry (j : Nat) {M x : Nat} (s : State) (h : TablePre base len w M x j s) : EntryReady base len w j s :=
    ⟨h.power.ready, h.entry⟩
  unfold tableBuild
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 0) (Q₂ := TablePre base len w M2 x2 0)
    (tableInit_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1)
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1) ?_
  apply RelCT.assoc
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 1) (Q₂ := TablePre base len w M2 x2 1)
    ((entryStepCT (a := 6) (j := 0) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 0 _ h.1, entry 0 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1) ?_
  apply RelCT.assoc
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 2) (Q₂ := TablePre base len w M2 x2 2)
    ((entryStepCT (a := 5) (j := 1) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 1 _ h.1, entry 1 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1) ?_
  apply RelCT.assoc
  exact relCT_chain (Q₁ := BuildInv base len w M1 x1 2) (Q₂ := BuildInv base len w M2 x2 2) prodInit_ct
    (fun s h => WP.mono (prodInit_ok s h) fun _ k => k.1) (fun s h => WP.mono (prodInit_ok s h) fun _ k => k.1)
    (tableLoop_ct fit fits)

end VG.Proof.Bignum.Arm

end

end

/-! # Selecting `T[digit]` reads every entry: its trace does not depend on the digit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- The registers of the selection of entry `j` into array 1, from a ready
state with the same memory. -/
def ScanSelect (base : BitVec 32) (len w j : Nat) (s : State) : Prop :=
  SelectRegs base w 1 1 (8 + j) s ∧ (s.gpr .r11).toNat ≤ 1 ∧
    ∃ s0, ArithmeticReady base len w s0 ∧ s.mem = s0.mem ∧ Rest roundClobbers s0 s

theorem scanHead_ok (s : State) {base : BitVec 32} {len w M x A d j : Nat}
    (h : ScanInv base len w M x A d j s) (hj : j < 8) :
    WP isa (.block (scanBit ++ scanArgs)) s (ScanSelect base len w j) := by
  apply WP.block_append_iff.mpr
  refine WP.mono (scanBit_ok s h.power.ready h.digitLt hj h.digit h.index) ?_
  rintro u ⟨bit, memU, restU⟩
  have readyU := h.power.ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.power.ready.ptr)
  refine WP.mono (scanArgs_ok u readyU (by rw [memU]; exact h.entry)) ?_
  rintro v ⟨p0, p10, p12, count, memV, restV⟩
  refine ⟨⟨p0, p10, p12, count⟩, by rw [restV.gpr .r11 (by simp), bit]; split <;> decide,
    s, h.power.ready, memV.trans memU, (rest_round restU).trans (rest_round restV)⟩

theorem scanSelect_ok (s : State) {base : BitVec 32} {len w j : Nat} (h : ScanSelect base len w j s)
    (fits : arrAt w 16 ≤ 8 * len) (hj : j < 8) :
    WP isa (.seq selectRow (.block [.ldrSp .r0 0])) s fun t => t.gpr .r0 = base := by
  obtain ⟨⟨p0, p10, p12, count⟩, bit, s0, ready, mem, rest⟩ := h
  exact WP.mono (selectAt_ok s ready mem rest fits (o := 1) (a := 1) (b := 8 + j) (by decide) (by decide)
    (by decide) (by omega_using [hj]) p0 p10 p12 count bit) fun _ k => k.1.ptr

theorem scanBody_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 d1 d2 j : Nat} (hj : j < 8)
    (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ScanInv base len w M1 x1 A1 d1 j s ∧ ScanInv base len w M2 x2 A2 d2 j t ∧ s.sp = t.sp)
      scanBody (fun _ _ => True) := by
  unfold scanBody
  refine relCT_chain (Q₁ := ScanSelect base len w j) (Q₂ := ScanSelect base len w j)
    (scanHead_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => scanHead_ok s h hj) (fun s h => scanHead_ok s h hj) ?_
  apply RelCT.assoc
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (selectRegs_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => scanSelect_ok s h fits hj) (fun s h => scanSelect_ok s h fits hj)
    (entryNext_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem scanLoop_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 d1 d2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ScanInv base len w M1 x1 A1 d1 0 s ∧ ScanInv base len w M2 x2 A2 d2 0 t ∧ s.sp = t.sp)
      (.loop scanBody .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧
    ScanInv base len w M1 x1 A1 d1 j s ∧ ScanInv base len w M2 x2 A2 d2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) scanBody fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have ct := relCT_keep_sp (scanBody_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (A1 := A1) (A2 := A2) (d1 := d1) (d2 := d2) (j := j) (by omega_using [jk, hk]) fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _, _⟩ := scanBody_ok s hs (by omega_using [jk, hk])
    obtain ⟨_, _, run2, next2, zero2, _, _, _⟩ := scanBody_ok t ht (by omega_using [jk, hk])
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], next1, next2, sp'⟩
  exact (RelCT.loop I step 8).mono (fun _ _ h => ⟨0, rfl, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

/-- The exponentiation's state, the table and a digit. -/
structure ScanPre (base : BitVec 32) (len w M x A d : Nat) (s : State) : Prop where
  power : ExpState base len w M x A s
  table : TableHolds s.mem base w M x 8
  digitLt : d < 8
  digit : s.mem.readW (VG.Proof.Mont.off (State.addr base) 196) 32 = BitVec.ofNat 32 d

theorem scan_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 d1 d2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ScanPre base len w M1 x1 A1 d1 s ∧ ScanPre base len w M2 x2 A2 d2 t ∧ s.sp = t.sp)
      scan (fun _ _ => True) := by
  unfold scan
  exact relCT_chain (Q₁ := ScanInv base len w M1 x1 A1 d1 0) (Q₂ := ScanInv base len w M2 x2 A2 d2 0)
    ((show RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0) (.block scanInit) (fun _ _ => True) from tableInit_ct).mono
      (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (scanStage0_ok s h.power h.table fits h.digitLt h.digit) fun _ k => k.1)
    (fun s h => WP.mono (scanStage0_ok s h.power h.table fits h.digitLt h.digit) fun _ k => k.1)
    (scanLoop_ct fits)

theorem windowApply_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 d1 d2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ScanPre base len w M1 x1 A1 d1 s ∧ ScanPre base len w M2 x2 A2 d2 t ∧ s.sp = t.sp)
      windowApply (fun _ _ => True) := by
  have mulReady (s : State) {M x A d : Nat} (h : ScanPre base len w M x A d s) :
      WP isa scan s fun t => ArithmeticReady base len w t ∧
        numAt t.mem (State.addr base) w 1 < numAt t.mem (State.addr base) w 0 := by
    refine WP.mono (scan_ok s h.power h.table fits h.digitLt h.digit) ?_
    rintro t ⟨power, table, selected, _, _, _, _⟩
    exact ⟨power.ready, by rw [selected, power.modulus]; exact (table d h.digitLt).1⟩
  have ptr (s : State) (h : ArithmeticReady base len w s ∧
      numAt s.mem (State.addr base) w 1 < numAt s.mem (State.addr base) w 0) :
      WP isa (montOp 6 6 1) s fun t => t.gpr .r0 = base :=
    WP.mono (montOp_ok s h.1 (o := 6) (a := 6) (b := 1)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) h.2) fun _ k => k.1.ptr
  unfold windowApply
  refine relCT_chain (scan_ct fits) (fun s h => mulReady s h) (fun s h => mulReady s h) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (montOp_ct (base := base) (o := 6) (a := 6) (b := 1)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit)
    (fun s h => ptr s h) (fun s h => ptr s h)
    (windowReset_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
