module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBit
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

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
    addr_add (by omega)
  have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
    rw [address]
    exact CallLay.inRegions_sub read (by omega) (by omega)
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
  rw [show 8 * j + 8 = 8 * (j + 1) by omega] at stateY
  have ptrY := (keepsY 128 (by simp)).trans ((keepsU 128 (by simp)).trans ptr)
  have countY := (keepsY 132 (by simp)).trans ((keepsU 132 (by simp)).trans counter)
  refine WP.mono (expByteNext_mem y stateY.power.ready (c := eb.length - j) (by omega) (by omega) ptrY countY) ?_
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
    rw [memZ]; exact read_after_writes _ _ _ _ (by omega) (by omega) (by decide) (by decide) ha'
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
      (by change eb.length ≤ 2 ^ 64; omega) hi]
    exact bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega)

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
    refine WP.mono (sharedWindowByteStep_ok K t state pt (by omega) separateAll) ?_
    rintro z ⟨stateZ, zero, pz, frameZ, restZ⟩
    by_cases last : j + 1 = eb.length
    · left
      obtain ⟨A', p', winZ, sumZ⟩ := stateZ.state
      refine ⟨?_, ⟨A', p', by rw [← last]; exact winZ, by rw [sumZ, last, pre_len]⟩, pz, frame.trans frameZ,
        rest.trans restZ⟩
      change some (!z.z) = some false
      simp only [zero, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, stateZ, pz, frame.trans frameZ, rest.trans restZ⟩
      change some (!z.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega, positive, h, hp, Frame.refl _ _, Rest.refl _ _⟩


end VG.Proof.Bignum.Arm
