module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block

/-! # Build a three-bit table using the shared Montgomery callee

The byte-copy and table-control programs are the existing RSA programs.
Only the multiplication is supplied by the caller's arithmetic interface.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (A : TwoExp.Montgomery base len w P regions)

theorem sharedTableBody_ok (s : State) {M x j : Nat}
    (h : BuildInv base len w M x j s) (hp : P s) (hj : 2 ≤ j) (hj' : j < 8) :
    WP isa (SharedWindow.tableBody A.op) s fun t =>
      BuildInv base len w M x (j + 1) t ∧ t.z = decide (j + 1 = 8) ∧
      KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [SharedWindow.tableBody, WP.seq_iff]
  refine WP.mono (A.op_ok s 1 1 5 h.power.ready hp
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.power.modulus]; exact h.power.inputBound)) ?_
  rintro u ⟨ready, modulus, bound, value, keeps, pu, frameU, restU⟩
  rw [h.power.modulus] at bound value
  have power := h.power.after_other ready keeps (by decide) (by decide) (by decide) (by decide) (by decide)
  have prod : numAt u.mem (State.addr base) w 1 % M = x ^ j * 2 ^ (64 * w) % M := by
    have := mont_mulx h.power.coprime h.prodValue h.power.inputValue value
    rwa [show j - 1 + 1 = j by omega] at this
  have entryU := (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.entry
  have indexU := (keeps_header_readW keeps size (d := 228) (bits := 32) (by decide)).trans h.index
  refine WP.mono (entryStep_ok u power (h.table.of_keeps keeps fits (by decide) (by omega)) fits
    (a := 1) (by decide) hj' entryU indexU bound prod) ?_
  rintro t ⟨powerT, tableT, prodT, entryT, indexT, zT, keepsT, frameT, restT⟩
  refine ⟨⟨powerT, tableT, fits, by rw [prodT]; exact bound, ?_, entryT, indexT⟩, zT,
    (KeepsExp.of_keeps keeps size).trans keepsT, A.stable frameT restT pu,
    frameU.trans (frameT.mono (by simpa using A.workspace)), restU.trans restT⟩
  rw [prodT, show j + 1 - 1 = j by omega]
  exact prod

theorem sharedTableLoop_ok (s : State) {M x : Nat}
    (h : BuildInv base len w M x 2 s) (hp : P s) :
    WP isa (.loop (SharedWindow.tableBody A.op) .ne) s fun t =>
      BuildInv base len w M x 8 t ∧ KeepsExp base s.mem t.mem ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ 2 ≤ j ∧ BuildInv base len w M x j t ∧
    KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M := isa) inv ?_ 6 s ?_
  · intro k t hk
    obtain ⟨j, hjk, hk, hj, hi, keeps, pt, frame, rest⟩ := hk
    refine WP.mono (sharedTableBody_ok A t hi pt hj (by omega)) ?_
    rintro u ⟨hu, hz, keepsU, pu, frameU, restU⟩
    by_cases he : j + 1 = 8
    · left
      refine ⟨?_, he ▸ hu, keeps.trans keepsU, pu, frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, by omega,
        hu, keeps.trans keepsU, pu, frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨2, rfl, by decide, Nat.le_refl _, h, KeepsExp.refl _ _, hp, Frame.refl _ _, Rest.refl _ _⟩

include A in
theorem sharedTablePrepare_ok (s : State) {M x : Nat}
    (h : ExpState base len w M x 0 s) (hp : P s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa SharedWindow.tablePrepare s fun t =>
      BuildInv base len w M x 2 t ∧ KeepsExp base s.mem t.mem ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [SharedWindow.tablePrepare, WP.seq_iff]
  refine WP.mono (tableStage0_ok s h fits) ?_
  rintro u ⟨preU, keepsU, frameU, restU⟩
  have pu := A.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (tableStageStep_ok u preU (a := 6) (by decide) (by decide)
    preU.power.powerBound preU.power.powerValue) ?_
  rintro v ⟨preV, keepsV, frameV, restV⟩
  have pv := A.stable frameV restV pu
  rw [WP.seq_iff]
  refine WP.mono (tableStageStep_ok v preV (a := 5) (by decide) (by decide)
    preV.power.inputBound (by rw [Nat.pow_one]; exact preV.power.inputValue)) ?_
  rintro y ⟨preY, keepsY, frameY, restY⟩
  have py := A.stable frameY restY pv
  refine WP.mono (prodInit_ok y preY) ?_
  rintro t ⟨inv, keepsT, frameT, restT⟩
  exact ⟨inv, keepsU.trans (keepsV.trans (keepsY.trans keepsT)), A.stable frameT restT py,
    (frameU.trans (frameV.trans (frameY.trans frameT))).mono (by simpa using A.workspace),
    restU.trans (restV.trans (restY.trans restT))⟩

theorem sharedTableBuild_ok (s : State) {M x : Nat}
    (h : ExpState base len w M x 0 s) (hp : P s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa (SharedWindow.tableBuild A.op) s fun t =>
      ExpState base len w M x 0 t ∧ TableHolds t.mem base w M x 8 ∧
      KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [SharedWindow.tableBuild, WP.seq_iff]
  refine WP.mono (sharedTablePrepare_ok A s h hp fits) ?_
  rintro u ⟨inv, keepsU, pu, frameU, restU⟩
  refine WP.mono (sharedTableLoop_ok A u inv pu) ?_
  rintro t ⟨invT, keepsT, pt, frameT, restT⟩
  exact ⟨invT.power, invT.table, keepsU.trans keepsT, pt, frameU.trans frameT, restU.trans restT⟩

end
end VG.Proof.Bignum.Arm
