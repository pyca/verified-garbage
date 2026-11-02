module
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApply
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBit
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic

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
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  refine WP.mono (sharedExpSquare_ok K s h.power hp) ?_
  rintro u ⟨powerU, keepsU, pU, frameU, restU⟩
  have hdrU (d : Nat) (hd : d + 4 ≤ 256) :=
    keeps_header_readW keepsU size (d := d) (bits := 32) (by omega)
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
    omega
  · refine WP.ite false (by simp [eval, zV, full]) (by simp) (fun _ => WP.block_nil ?_)
    have mod : (q + 1) % 3 = q + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨_, _, ⟨powerV, tableV, fits, digitV, by rw [mod]; exact pendingV, by rw [mod]; exact boundV,
      by omega⟩, ?_⟩, keepsU.trans keepsV, pV, frameU.trans frameV', restU.trans restV⟩
    omega

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
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [SharedWindow.round, WP.seq_iff]
  refine WP.mono (sharedWindowBit_ok K s h hp hv byte) ?_
  rintro u ⟨⟨A', p', stateU, sum⟩, keepsU, pU, frameU, restU⟩
  have byteU := (keepsU 200 (by simp)).trans byte
  have countU := (keepsU 192 (by simp)).trans count
  rw [WP.seq_iff]
  refine WP.mono (expShift_ok u stateU.power.ready.workspace (by omega) stateU.power.ready.ptr byteU) ?_
  rintro v ⟨memV, restV⟩
  have readyV := stateU.power.ready
  refine WP.mono (expDecrement_ok v (readyV.workspace.congr restV.wr) (by omega)
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
    rw [memT]; exact read_after_writes _ _ _ _ (by omega) (by omega) (by decide) (by decide) ha'
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
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
    have valueFit : v * 2 ^ j < 2 ^ 32 := by
      have := Nat.mul_le_mul_left v hp
      omega
    refine WP.mono (sharedWindowRound_ok K t state pt valueFit (by omega) (by omega) byte count) ?_
    rintro u ⟨⟨A', p', stateU, sumU⟩, byteU, countU, zero, keepsU, pU, frameU, restU⟩
    rw [Nat.mod_add_mod] at stateU
    have expEq : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
        E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
      rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
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
        simp only [zero, show 8 - j = 1 by omega, decide_true, Bool.not_true]
      · refine ⟨A', p', by rw [show n + 8 = n + j + 1 by omega]; exact stateU, ?_⟩
        simpa only [last, Nat.sub_self, Nat.pow_zero, Nat.div_one, show 2 ^ 8 = 256 from rfl,
          Nat.mul_comm E 256] using sumU
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, next, keeps.trans keepsU, pU, frame.trans frameU,
        rest.trans restU⟩
      change some (!u.z) = some true
      simp only [zero, show (8 - j = 1) = False by simp; omega, decide_false, Bool.not_false]
  · exact ⟨0, by decide, by decide, h, KeepsPtr.refl _ _, hp, Frame.refl _ _, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm
