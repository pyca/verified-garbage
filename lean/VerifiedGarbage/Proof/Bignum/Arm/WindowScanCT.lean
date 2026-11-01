module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuildCT
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
    (by decide) (by omega) p0 p10 p12 count bit) fun _ k => k.1.ptr

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
      (A1 := A1) (A2 := A2) (d1 := d1) (d2 := d2) (j := j) (by omega) fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _, _⟩ := scanBody_ok s hs (by omega)
    obtain ⟨_, _, run2, next2, zero2, _, _, _⟩ := scanBody_ok t ht (by omega)
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
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
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
