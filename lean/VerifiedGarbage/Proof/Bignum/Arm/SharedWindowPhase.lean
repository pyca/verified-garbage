module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState

/-! ### `Bignum.Arm.SharedWindowBuild`, which this module and modules that import it used -/

section

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
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) fits
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
    rwa [show j - 1 + 1 = j by omega_using [hj]] at this
  have entryU := (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.entry
  have indexU := (keeps_header_readW keeps size (d := 228) (bits := 32) (by decide)).trans h.index
  refine WP.mono (entryStep_ok u power (h.table.of_keeps keeps fits (by decide) (by omega_using [hj'])) fits
    (a := 1) (by decide) hj' entryU indexU bound prod) ?_
  rintro t ⟨powerT, tableT, prodT, entryT, indexT, zT, keepsT, frameT, restT⟩
  refine ⟨⟨powerT, tableT, fits, by rw [prodT]; exact bound, ?_, entryT, indexT⟩, zT,
    (KeepsExp.of_keeps keeps size).trans keepsT, A.stable frameT restT pu,
    frameU.trans (frameT.mono (by simpa using A.workspace)), restU.trans restT⟩
  rw [prodT, show j + 1 - 1 = j by omega_using []]
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
    refine WP.mono (sharedTableBody_ok A t hi pt hj (by omega_using [hjk, hk])) ?_
    rintro u ⟨hu, hz, keepsU, pu, frameU, restU⟩
    by_cases he : j + 1 = 8
    · left
      refine ⟨?_, he ▸ hu, keeps.trans keepsU, pu, frame.trans frameU, rest.trans restU⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 1, by omega_using [hjk, hk], by omega_using [hjk, hk, he], by omega_using [hj],
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

end

end

/-! ### `Bignum.Arm.SharedWindowBytes`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.SharedWindowBit`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.SharedWindowApply`, which this module and modules that import it used -/

section

/-! The window table is selected once, then multiplied through a shared call. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)
theorem sharedWindowApply_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x A d : Nat}
    (h : ExpState base len w M x A s) (hp : P s) (table : TableHolds s.mem base w M x 8) (fits : arrAt w 16 ≤ 8 * len)
    (hd : d < 8) (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d) :
    WP isa (SharedWindow.apply K.op) s fun t => ExpState base len w M x (A + d) t ∧ TableHolds t.mem base w M x 8 ∧
      t.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 0 ∧
      t.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 0 ∧
      KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) fits
  rw [SharedWindow.apply, WP.seq_iff]
  refine WP.mono (scan_ok s h table fits hd digit) ?_
  rintro u ⟨powerU, tableU, selected, _, keepsU, frameU, restU⟩
  have entry := tableU d hd
  rw [← selected] at entry
  have pU := K.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (K.op_ok u 6 6 1 powerU.ready pU
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [powerU.modulus]; exact entry.1)) ?_
  rintro v ⟨ready, modulus, bound, value, keeps, pV, frameV, restV⟩
  rw [powerU.modulus] at modulus bound value
  have powerV := powerU.after_y ready modulus keeps bound
    (mont_mulpow powerU.coprime powerU.powerValue entry.2 value)
  have tableV := tableU.of_keeps keeps fits (by decide) (by decide)
  refine WP.mono (windowReset_ok v ready) ?_
  rintro t ⟨memT, restT⟩
  have ctl : CtlOnly base v.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerT, frameT⟩ := powerV.after_ctl ctl restT ((restT.gpr .r0 (by simp)).trans ready.ptr)
  have outside := writeW32_outside (v.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 0))
    (State.addr base) (d := 204) (BitVec.ofNat 32 0) (by decide)
  refine ⟨powerT, tableV.after_ctl ctl fits nowrap (by decide), ?_, by rw [memT]; exact Mem.readW_writeW_self32 _ _ _,
    keepsU.trans ((KeepsExp.of_keeps keeps size).trans ?_), K.stable frameT (rest_round restT) pV,
    (Frame.mono frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)).trans
      (frameV.trans (Frame.mono frameT (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace))),
    restU.trans (restV.trans (rest_round restT))⟩
  · rw [memT, outside_read32 outside (d := 196) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [memT]
    exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide)

end VG.Proof.Bignum.Arm

end

end

/-! Each fixed-window bit calls the shared square and product kernels. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)
theorem sharedWindowSquare_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x A p q V : Nat}
    (h : WinState base len w M x A p q s) (hp : P s)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (K.op 6 6 6) s fun u => WinState base len w M x (2 * A) p q u ∧
      u.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V ∧
      KeepsExp base s.mem u.mem ∧ P u ∧ Frame regions s.mem u.mem ∧ Rest roundClobbers s u := by
  have fits := h.fits
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) fits
  refine WP.mono (sharedExpSquare_ok K s h.power hp) ?_
  rintro u ⟨powerU, keepsU, pU, frameU, restU⟩
  have hdrU (d : Nat) (hd : d + 4 ≤ 256) :=
    keeps_header_readW keepsU size (d := d) (bits := 32) (by omega_using [hd])
  exact ⟨⟨powerU, h.table.of_keeps keepsU fits (by decide) (by decide), fits,
    (hdrU 196 (by decide)).trans h.digit, (hdrU 204 (by decide)).trans h.pending, h.bound, h.short⟩,
    (hdrU 200 (by decide)).trans byte, KeepsExp.of_keeps keepsU size, pU, frameU, restU⟩


theorem sharedWindowBit_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x A p q V : Nat}
    (h : WinState base len w M x A p q s) (hp : P s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (SharedWindow.bit K.op) s fun t => (∃ A' p', WinState base len w M x A' p' ((q + 1) % 3) t ∧
      A' + p' = 2 * (A + p) + V / 128 % 2) ∧
      KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have hq := h.short
  rw [SharedWindow.bit, WP.seq_iff]
  refine WP.mono (sharedWindowSquare_ok K s h hp byte) ?_
  rintro u ⟨stateU, byteU, keepsU, pU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (windowJoin_ok u stateU hv byteU) ?_
  rintro v ⟨powerV, tableV, boundV, digitV, pendingV, zV, keepsV, frameV, restV⟩
  have pV := K.stable frameV restV pU
  have frameV' := Frame.mono frameV (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)
  have bit : V / 128 % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases full : q + 1 = 3
  · refine WP.ite true (by simp [eval, zV, full]) (fun _ => ?_) (by simp)
    have small : 2 * p + V / 128 % 2 < 8 := by
      rw [full] at boundV
      exact boundV
    refine WP.mono (sharedWindowApply_ok K v powerV pV tableV fits small digitV) ?_
    rintro t ⟨powerT, tableT, digitT, pendingT, keepsT, pT, frameT, restT⟩
    refine ⟨⟨_, 0, ⟨powerT, tableT, fits, digitT, by rw [full]; exact pendingT, by rw [full]; decide,
      by rw [full]; decide⟩, ?_⟩, keepsU.trans (keepsV.trans keepsT), pT, frameU.trans (frameV'.trans frameT),
      restU.trans (restV.trans restT)⟩
    omega_using []
  · refine WP.ite false (by simp [eval, zV, full]) (by simp) (fun _ => WP.block_nil ?_)
    have mod : (q + 1) % 3 = q + 1 := Nat.mod_eq_of_lt (by omega_using [hq, full])
    refine ⟨⟨_, _, ⟨powerV, tableV, fits, digitV, by rw [mod]; exact pendingV, by rw [mod]; exact boundV,
      by omega_using []⟩, ?_⟩, keepsU.trans keepsV, pV, frameU.trans frameV', restU.trans restV⟩
    omega_using []

theorem sharedWindowRound_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x A p q V c : Nat}
    (h : WinState base len w M x A p q s) (hp : P s) (hv : V < 2 ^ 32) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V)
    (count : s.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 c) :
    WP isa (SharedWindow.round K.op) s fun t => (∃ A' p', WinState base len w M x A' p' ((q + 1) % 3) t ∧
      A' + p' = 2 * (A + p) + V / 128 % 2) ∧
      t.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 (V + V) ∧
      t.mem.readW (off (State.addr base) 192) 32 = BitVec.ofNat 32 (c - 1) ∧
      t.z = decide (c = 1) ∧ KeepsPtr base s.mem t.mem ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) fits
  rw [SharedWindow.round, WP.seq_iff]
  refine WP.mono (sharedWindowBit_ok K s h hp hv byte) ?_
  rintro u ⟨⟨A', p', stateU, sum⟩, keepsU, pU, frameU, restU⟩
  have byteU := (keepsU 200 (by simp)).trans byte
  have countU := (keepsU 192 (by simp)).trans count
  rw [WP.seq_iff]
  refine WP.mono (expShift_ok u stateU.power.ready.workspace (by omega_using [size]) stateU.power.ready.ptr byteU) ?_
  rintro v ⟨memV, restV⟩
  have readyV := stateU.power.ready
  refine WP.mono (expDecrement_ok v (readyV.workspace.congr restV.wr) (by omega_using [size])
    ((restV.gpr .r0 (by simp)).trans readyV.ptr) hc hc' (by
      have outside := writeW32_outside u.mem (State.addr base) (d := 200) (BitVec.ofNat 32 (V + V)) (by decide)
      rw [← memV] at outside
      rw [outside_read32 outside (d := 192) (by decide) (by decide)]; exact countU)) ?_
  rintro t ⟨memT, flag, restT⟩
  rw [memV] at memT
  have ctl : CtlOnly base u.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have restUT : Rest roundClobbers u t := (rest_round restV).trans (rest_round restT)
  obtain ⟨powerT, frameT⟩ := stateU.power.after_ctl ctl restUT
    ((restT.gpr .r0 (by simp)).trans ((restV.gpr .r0 (by simp)).trans readyV.ptr))
  obtain ⟨byteT, countT⟩ := two_writes u.mem base (d := 200) (e := 192)
    (BitVec.ofNat 32 (V + V)) (BitVec.ofNat 32 (c - 1)) (by decide) (by decide) (by decide)
  rw [← memT] at byteT countT
  have keep (a : Nat) (ha : a + 4 ≤ 192 ∨ 204 ≤ a) (ha' : a + 4 ≤ 256) :
      t.mem.readW (off (State.addr base) a) 32 = u.mem.readW (off (State.addr base) a) 32 := by
    rw [memT]; exact read_after_writes _ _ _ _ (by omega_using [ha]) (by omega_using [ha]) (by decide) (by decide) ha'
  refine ⟨⟨A', p', ⟨powerT, stateU.table.after_ctl ctl fits nowrap (by decide), fits, ?_, ?_,
    stateU.bound, stateU.short⟩, sum⟩, byteT, countT, flag, ?_, K.stable frameT restUT pU,
    frameU.trans (Frame.mono frameT (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)), restU.trans restUT⟩
  · rw [memT, read_after_writes _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact stateU.digit
  · rw [keep 204 (by decide) (by decide)]; exact stateU.pending
  · refine keepsU.ptr.trans ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact keep 128 (by decide) (by decide)
    · exact keep 132 (by decide) (by decide)


theorem sharedWindowBits_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x E v n : Nat}
    (h : WinBitState base len w M x E v n 0 s) (hp : P s) (hv : v < 256) :
    WP isa (SharedWindow.bits K.op) s fun t => (∃ A p, WinState base len w M x A p ((n + 8) % 3) t ∧ A + p = 256 * E + v) ∧
      KeepsPtr base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ WinBitState base len w M x E v n j t ∧
    KeepsPtr base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold SharedWindow.bits
  refine WP.loop (M := isa) I ?_ 8 s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, ⟨⟨A, p, state, sum⟩, byte, count⟩, keeps, pt, frame, rest⟩ := inv
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega_using [jk, hk] : j ≤ 7)
    have valueFit : v * 2 ^ j < 2 ^ 32 := by
      have := Nat.mul_le_mul_left v hp
      omega_using [hv, this]
    refine WP.mono (sharedWindowRound_ok K t state pt valueFit (by omega_using [jk, hk]) (by omega_using []) byte count) ?_
    rintro u ⟨⟨A', p', stateU, sumU⟩, byteU, countU, zero, keepsU, pU, frameU, restU⟩
    rw [Nat.mod_add_mod] at stateU
    have expEq : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
        E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
      rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega_using [jk, hk]), show 7 - j = 8 - (j + 1) by omega_using [],
        Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
    rw [sum, expEq] at sumU
    have next : WinBitState base len w M x E v n (j + 1) u := by
      refine ⟨⟨A', p', stateU, sumU⟩, ?_, ?_⟩
      · rw [byteU, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countU]; congr 1
    by_cases last : j + 1 = 8
    · left
      refine ⟨?_, ?_, keeps.trans keepsU, pU, frame.trans frameU, rest.trans restU⟩
      · change some (!u.z) = some false
        simp only [zero, show 8 - j = 1 by omega_using [last], decide_true, Bool.not_true]
      · refine ⟨A', p', by rw [show n + 8 = n + j + 1 by omega_using [last]]; exact stateU, ?_⟩
        simpa only [last, Nat.sub_self, Nat.pow_zero, Nat.div_one, show 2 ^ 8 = 256 from rfl,
          Nat.mul_comm E 256] using sumU
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, last], next, keeps.trans keepsU, pU, frame.trans frameU,
        rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, show (8 - j = 1) = False by simp; omega_using [last], decide_false, Bool.not_false]
  · exact ⟨0, by decide, by decide, h, KeepsPtr.refl _ _, hp, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm

end

end

/-! The existing three-bit window's byte loop, with shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem sharedWindowByteStep_ok {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    {P : State → Prop} {regions : List Region} (K : TwoExp.Montgomery base len w P regions) (t : State)
    (h : WinByteLoop base ep len w M x eb j t) (hp : P t) (hj : j < eb.length)
    (separateAll : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (.seq expByteHead (.seq (SharedWindow.bits K.op) (.block expByteNext))) t fun z =>
      WinByteLoop base ep len w M x eb (j + 1) z ∧ z.z = decide (j + 1 = eb.length) ∧
      P z ∧ Frame regions t.mem z.mem ∧ Rest roundClobbers t z := by
  obtain ⟨⟨A, p, state, sum⟩, ptr, counter, countFit, sourceFit, read, separate, bytes⟩ := h
  have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
    addr_add (by omega_using [hj, sourceFit])
  have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
    rw [address]
    exact CallLay.inRegions_sub read (by omega_using [hj]) (by omega_using [countFit])
  have currentByte : t.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
    rw [address]; exact bytes j hj
  rw [WP.seq_iff]
  refine WP.mono (windowByteHead_ok t state ptr currentRead) ?_
  rintro u ⟨stateU, byteU, countU, keepsU, frameU, restU⟩
  have pu := K.stable frameU restU hp
  rw [currentByte] at byteU
  have v256 := (eb[j]).isLt
  rw [WP.seq_iff]
  refine WP.mono (sharedWindowBits_ok K u (E := pre eb j) (v := (eb[j]).toNat) (n := 8 * j)
    ⟨⟨A, p, stateU, by rw [sum, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt v256, Nat.add_zero]⟩, by rw [Nat.pow_zero, Nat.mul_one]; exact byteU, countU⟩ pu v256) ?_
  rintro y ⟨⟨A', p', stateY, sumY⟩, keepsY, py, frameY, restY⟩
  rw [show 8 * j + 8 = 8 * (j + 1) by omega_using []] at stateY
  have ptrY := (keepsY 128 (by simp)).trans ((keepsU 128 (by simp)).trans ptr)
  have countY := (keepsY 132 (by simp)).trans ((keepsU 132 (by simp)).trans counter)
  refine WP.mono (expByteNext_mem y stateY.power.ready (c := eb.length - j) (by omega_using [hj]) (by omega_using [countFit]) ptrY countY) ?_
  rintro z ⟨memZ, zero, restZ⟩
  have ctl : CtlOnly base y.mem z.mem := by
    rw [memZ]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have fits := stateY.fits
  have nowrap := stateY.power.ready.workspace.nowrap
  obtain ⟨powerZ, frameZ⟩ := stateY.power.after_ctl ctl restZ
    ((restZ.gpr .r0 (by simp)).trans stateY.power.ready.ptr)
  obtain ⟨ptrZ, counterZ⟩ := two_writes y.mem base (d := 128) (e := 132)
    (ep + BitVec.ofNat 32 j + 1) (BitVec.ofNat 32 (eb.length - j - 1)) (by decide) (by decide) (by decide)
  rw [← memZ] at ptrZ counterZ
  have keep (a : Nat) (ha : 136 ≤ a) (ha' : a + 4 ≤ 256) :
      z.mem.readW (off (State.addr base) a) 32 = y.mem.readW (off (State.addr base) a) 32 := by
    rw [memZ]; exact read_after_writes _ _ _ _ (by omega_using [ha]) (by omega_using [ha]) (by decide) (by decide) ha'
  have stateZ : WinState base len w M x A' p' (8 * (j + 1) % 3) z :=
    ⟨powerZ, stateY.table.after_ctl ctl fits nowrap (by decide), fits,
      by rw [keep 196 (by decide) (by decide)]; exact stateY.digit,
      by rw [keep 204 (by decide) (by decide)]; exact stateY.pending, stateY.bound, stateY.short⟩
  have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [prefixEq] at sumY
  have pz := K.stable frameZ (rest_round restZ) py
  have frameAll := (frameU.mono (by simpa using K.workspace)).trans
    (frameY.trans (frameZ.mono (by simpa using K.workspace)))
  have restAll := restU.trans (restY.trans (rest_round restZ))
  refine ⟨⟨⟨A', p', stateZ, sumY⟩, ?_, ?_, countFit, sourceFit, ?_, separate, ?_⟩, ?_, pz, frameAll, restAll⟩
  · rw [ptrZ]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [counterZ]; congr 1
  · rw [restAll.rd, restAll.wr]; exact read
  · intro i hi
    rw [frameAll.bytes (R := ⟨State.addr ep, eb.length⟩)
      separateAll
      (by change eb.length ≤ 2 ^ 64; omega_using [countFit]) hi]
    exact bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega_using [])

theorem sharedWindowBytes_ok {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    {P : State → Prop} {regions : List Region} (K : TwoExp.Montgomery base len w P regions) (s : State)
    (h : WinByteLoop base ep len w M x eb 0 s) (hp : P s) (positive : 0 < eb.length)
    (separateAll : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.bytes K.op) s fun t =>
      (∃ A p, WinState base len w M x A p (8 * eb.length % 3) t ∧ A + p = Spec.Rsa.os2ip eb) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧ WinByteLoop base ep len w M x eb j t ∧ P t ∧
    Frame regions s.mem t.mem ∧ Rest roundClobbers s t
  unfold SharedWindow.bytes
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, state, pt, frame, rest⟩ := inv
    refine WP.mono (sharedWindowByteStep_ok K t state pt (by omega_using [jk, hk]) separateAll) ?_
    rintro z ⟨stateZ, zero, pz, frameZ, restZ⟩
    by_cases last : j + 1 = eb.length
    · left
      obtain ⟨A', p', winZ, sumZ⟩ := stateZ.state
      refine ⟨?_, ⟨A', p', by rw [← last]; exact winZ, by rw [sumZ, last, pre_len]⟩, pz, frame.trans frameZ,
        rest.trans restZ⟩
      change some (!z.z) = some false
      simp only [zero, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, last], stateZ, pz, frame.trans frameZ, rest.trans restZ⟩
      change some (!z.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega_using [], positive, h, hp, Frame.refl _ _, Rest.refl _ _⟩


end VG.Proof.Bignum.Arm

end

end

/-! # Three-bit exponentiation through shared arithmetic calls

The exponent source is separate from every permitted working region,
including the callee's saved-register stack, throughout the fixed schedule.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

section
variable {base ep : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (K : TwoExp.Montgomery base len w P regions)

theorem sharedPhaseInit_ready (s : State) {M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (hp : P s)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.init K.op) s fun t =>
      ExpByteState base ep len w M x eb 0 t ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sharedWindowInit_ok K s h.ready hp h.modulus h.odd h.input h.r2bound h.r2value) ?_
  rintro t ⟨power, header, pt, frame, rest⟩
  refine ⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, pt, frame, rest⟩
  · rw [header 128 (by decide), BitVec.add_zero]; exact h.pointer
  · rw [header 132 (by decide)]; exact h.count
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) separate
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega_using [this]) hi]
    exact h.bytes i hi

theorem sharedPhaseTable_ok (s : State) {M x : Nat} {eb : List Byte}
    (ready : ExpByteState base ep len w M x eb 0 s) (hp : P s)
    (fits : arrAt w 16 ≤ 8 * len)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.tableBuild K.op) s fun t =>
      WinReady base ep len w M x eb t ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sharedTableBuild_ok K s ready.power hp fits) ?_
  rintro t ⟨power, table, keeps, pt, frame, rest⟩
  refine ⟨⟨power, table, fits, ?_, ?_, ready.countFit, ready.sourceFit,
    by rw [rest.rd, rest.wr]; exact ready.read, ready.separate, ?_⟩, pt, frame, rest⟩
  · rw [keeps 128 (by simp), ready.pointer, BitVec.add_zero]
  · rw [keeps 132 (by simp), ready.count, Nat.sub_zero]
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) separate
      (by change eb.length ≤ 2 ^ 64; have := ready.countFit; omega_using [this]) hi]
    exact ready.bytes i hi

theorem sharedWindowExpPhase_ok (s : State) {M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (hp : P s) (fits : arrAt w 16 ≤ 8 * len)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (SharedWindow.phase K.op) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [SharedWindow.phase, WP.seq_iff]
  refine WP.mono (sharedPhaseInit_ready K s h hp separate) ?_
  rintro u ⟨ready, pu, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (sharedPhaseTable_ok K u ready pu fits separate) ?_
  rintro v ⟨readyV, pv, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (phaseReset_ok v readyV) ?_
  rintro z ⟨loopZ, frameZ, restZ⟩
  have pz := K.stable frameZ restZ pv
  rw [WP.seq_iff]
  refine WP.mono (sharedWindowBytes_ok K z loopZ pz h.positive separate) ?_
  rintro y ⟨⟨A, p, stateY, sum⟩, py, frameY, restY⟩
  rw [WP.seq_iff]
  refine WP.mono (sharedWindowApply_ok K y stateY.power py stateY.table fits
    (pending_digit stateY) stateY.digit) ?_
  rintro r ⟨powerR, _, _, _, _, pr, frameR, restR⟩
  rw [sum] at powerR
  refine WP.mono (sharedExpFinish_ok K r powerR pr) ?_
  rintro t ⟨final, value, keeps, pt, frameT, restT⟩
  have fits8 : arrAt w 8 ≤ 8 * len := powerR.ready.width ▸ powerR.ready.layout.2.2.1
  have modulus := (keeps_array_num keeps fits8 (q := 0)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.modulus
  have r2 := (keeps_array_num keeps fits8 (q := 4)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.r2
  have one := (keeps_array_num keeps fits8 (q := 7)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.one
  exact ⟨final, value, modulus, r2, one, pt,
    frameU.trans (frameV.trans ((frameZ.mono (by simpa using K.workspace)).trans
      (frameY.trans (frameR.trans frameT)))),
    restU.trans (restV.trans (restZ.trans (restY.trans (restR.trans restT))))⟩

end
end VG.Proof.Bignum.Arm
