module

import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBit
import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! # Windowed private RSA exponentiation implements the modular-exponentiation specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str wp_subs op2_imm dpVal ofNat_beq_zero)

/-- `expByteNext`'s two header writes. -/
theorem expByteNext_mem (s : State) {base ep : BitVec 32} {len w c : Nat}
    (h : ArithmeticReady base len w s) (hc : 0 < c) (hc' : c < 2 ^ 32)
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 c) :
    WP isa (.block expByteNext) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) 128) (ep + 1)).writeW (off (State.addr base) 132)
        (BitVec.ofNat 32 (c - 1)) ∧ t.z = decide (c = 1) ∧ Rest [.r1] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_arith
  have addr (d : Nat) (hd : d ≤ 252) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega_arith)
  unfold expByteNext
  refine wp_ldr (a := off (State.addr base) 128) (by decide) (addr 128 (by decide))
    (h.workspace.read (by omega_arith)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_str (a := off (State.addr base) 128) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 128 (by decide))
    (by rw [b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun z d => ?_
  have memZ : z.mem = s.mem.writeW (off (State.addr base) 128) (ep + 1) := by
    rw [d.mem, b.mem, a.mem, b.gpr, dpVal, a.gpr, pointer]
  have outsideZ := writeW32_outside s.mem (State.addr base) (d := 128) (ep + 1) (by decide)
  rw [← memZ] at outsideZ
  refine wp_ldr (a := off (State.addr base) 132) (by decide)
    (by rw [congrFun d.gpr .r0, b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 132 (by decide))
    (by rw [d.rd, d.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega_arith)) fun q e => ?_
  refine wp_subs (op2_imm (by decide)) fun r f zero => ?_
  refine wp_str_z (a := off (State.addr base) 132) (by decide)
    (by rw [f.other .r0 (by decide), e.other .r0 (by decide), congrFun d.gpr .r0, b.other .r0 (by decide),
      a.other .r0 (by decide)]; exact addr 132 (by decide))
    (by rw [f.wr, e.wr, d.wr, b.wr, a.wr]; exact h.workspace.write (by omega_arith)) fun t g zeroT => WP.block_nil ?_
  have value : r.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [f.gpr, e.gpr, outside_read32 outsideZ (d := 132) (by decide) (by decide), count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)
  refine ⟨by rw [g.mem, f.mem, e.mem, memZ, value], ?_,
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((d.rest _).trans ((e.rest (by decide)).trans
      ((f.rest (by decide)).trans (g.rest _)))))⟩
  rw [zeroT, zero, ← f.gpr, value, ofNat_beq_zero (by omega_arith)]
  exact decide_eq_decide.mpr (by omega_arith)

/-- The first `j` exponent bytes are applied; the exponent buffer is where it was. -/
structure WinByteLoop (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (j : Nat) (s : State) : Prop where
  state : ∃ A p, WinState base len w M x A p (8 * j % 3) s ∧ A + p = pre eb j
  pointer : s.mem.readW (off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j
  count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 (eb.length - j)
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem windowByteStep_ok (t : State) {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    (h : WinByteLoop base ep len w M x eb j t) (hj : j < eb.length) :
    WP isa (.seq expByteHead (.seq windowBits (.block expByteNext))) t fun z =>
      WinByteLoop base ep len w M x eb (j + 1) z ∧ z.z = decide (j + 1 = eb.length) ∧
      Frame [⟨State.addr base, 8 * len⟩] t.mem z.mem ∧ Rest roundClobbers t z := by
  obtain ⟨⟨A, p, state, sum⟩, ptr, counter, countFit, sourceFit, read, separate, bytes⟩ := h
  have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
    addr_add (by omega_arith)
  have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
    rw [address]
    exact CallLay.inRegions_sub read (by omega_arith) (by omega_arith)
  have currentByte : t.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
    rw [address]; exact bytes j hj
  rw [WP.seq_iff]
  refine WP.mono (windowByteHead_ok t state ptr currentRead) ?_
  rintro u ⟨stateU, byteU, countU, keepsU, frameU, restU⟩
  rw [currentByte] at byteU
  have v256 := (eb[j]).isLt
  rw [WP.seq_iff]
  refine WP.mono (windowBits_ok u (E := pre eb j) (v := (eb[j]).toNat) (n := 8 * j)
    ⟨⟨A, p, stateU, by rw [sum, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt v256, Nat.add_zero]⟩, by rw [Nat.pow_zero, Nat.mul_one]; exact byteU, countU⟩ v256) ?_
  rintro y ⟨⟨A', p', stateY, sumY⟩, keepsY, frameY, restY⟩
  rw [show 8 * j + 8 = 8 * (j + 1) by omega_arith] at stateY
  have ptrY := (keepsY 128 (by decide)).trans ((keepsU 128 (by decide)).trans ptr)
  have countY := (keepsY 132 (by decide)).trans ((keepsU 132 (by decide)).trans counter)
  refine WP.mono (expByteNext_mem y stateY.power.ready (c := eb.length - j) (by omega_arith) (by omega_arith) ptrY countY) ?_
  rintro z ⟨memZ, zero, restZ⟩
  have ctl : CtlOnly base y.mem z.mem := by
    rw [memZ]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have fits := stateY.fits
  have nowrap := stateY.power.ready.workspace.nowrap
  obtain ⟨powerZ, frameZ⟩ := stateY.power.after_ctl ctl restZ
    ((restZ.gpr .r0 (by decide)).trans stateY.power.ready.ptr)
  obtain ⟨ptrZ, counterZ⟩ := two_writes y.mem base (d := 128) (e := 132)
    (ep + BitVec.ofNat 32 j + 1) (BitVec.ofNat 32 (eb.length - j - 1)) (by decide) (by decide) (by decide)
  rw [← memZ] at ptrZ counterZ
  have keep (a : Nat) (ha : 136 ≤ a) (ha' : a + 4 ≤ 256) :
      z.mem.readW (off (State.addr base) a) 32 = y.mem.readW (off (State.addr base) a) 32 := by
    rw [memZ]; exact read_after_writes _ _ _ _ (by omega_arith) (by omega_arith) (by decide) (by decide) ha'
  have stateZ : WinState base len w M x A' p' (8 * (j + 1) % 3) z :=
    ⟨powerZ, stateY.table.after_ctl ctl fits nowrap (by decide), fits,
      by rw [keep 196 (by decide) (by decide)]; exact stateY.digit,
      by rw [keep 204 (by decide) (by decide)]; exact stateY.pending, stateY.bound, stateY.short⟩
  have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [prefixEq] at sumY
  have frameAll := frameU.trans (frameY.trans frameZ)
  have restAll := restU.trans (restY.trans (rest_round restZ))
  refine ⟨⟨⟨A', p', stateZ, sumY⟩, ?_, ?_, countFit, sourceFit, ?_, separate, ?_⟩, ?_, frameAll, restAll⟩
  · rw [ptrZ]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [counterZ]; congr 1
  · rw [restAll.rd, restAll.wr]; exact read
  · intro i hi
    rw [frameAll.bytes (R := ⟨State.addr ep, eb.length⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact separate)
      (by change eb.length ≤ 2 ^ 64; omega_arith) hi]
    exact bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega_arith)

theorem windowBytes_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : WinByteLoop base ep len w M x eb 0 s) (positive : 0 < eb.length) :
    WP isa windowBytes s fun t =>
      (∃ A p, WinState base len w M x A p (8 * eb.length % 3) t ∧ A + p = Spec.Rsa.os2ip eb) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧ WinByteLoop base ep len w M x eb j t ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  unfold windowBytes
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, state, frame, rest⟩ := inv
    refine WP.mono (windowByteStep_ok t state (by omega_arith)) ?_
    rintro z ⟨stateZ, zero, frameZ, restZ⟩
    by_cases last : j + 1 = eb.length
    · left
      obtain ⟨A', p', winZ, sumZ⟩ := stateZ.state
      refine ⟨?_, ⟨A', p', by rw [← last]; exact winZ, by rw [sumZ, last, pre_len]⟩, frame.trans frameZ,
        rest.trans restZ⟩
      change some (!z.z) = some false
      simp only [zero, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, j + 1, by omega_arith, by omega_arith, stateZ, frame.trans frameZ, rest.trans restZ⟩
      change some (!z.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · exact ⟨0, by omega_arith, positive, h, Frame.refl _ _, Rest.refl _ _⟩

/-- The table built, the exponent's controls as `expInit` left them. -/
structure WinReady (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (s : State) : Prop where
  power : ExpState base len w M x 0 s
  table : TableHolds s.mem base w M x 8
  fits : arrAt w 16 ≤ 8 * len
  pointer : s.mem.readW (off (State.addr base) 128) 32 = ep
  count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem phaseTable_ok (u : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (ready : ExpByteState base ep len w M x eb 0 u) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa tableBuild u fun v => WinReady base ep len w M x eb v ∧
      Frame [⟨State.addr base, 8 * len⟩] u.mem v.mem ∧ Rest roundClobbers u v := by
  refine WP.mono (tableBuild_ok u ready.power fits) ?_
  rintro v ⟨powerV, tableV, keepsV, frameV, restV⟩
  refine ⟨⟨powerV, tableV, fits, by rw [keepsV 128 (by decide), ready.pointer, BitVec.add_zero],
    by rw [keepsV 132 (by decide), ready.count, Nat.sub_zero], ready.countFit, ready.sourceFit,
    by rw [restV.rd, restV.wr]; exact ready.read, ready.separate, ?_⟩, frameV, restV⟩
  intro i hi
  rw [frameV.bytes (R := ⟨State.addr ep, eb.length⟩)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ready.separate)
    (by change eb.length ≤ 2 ^ 64; have := ready.countFit; omega_arith) hi]
  exact ready.bytes i hi

theorem phaseReset_ok (v : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : WinReady base ep len w M x eb v) :
    WP isa (.block windowReset) v fun z => WinByteLoop base ep len w M x eb 0 z ∧
      Frame [⟨State.addr base, 8 * len⟩] v.mem z.mem ∧ Rest roundClobbers v z := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  refine WP.mono (windowReset_ok v h.power.ready) ?_
  rintro z ⟨memZ, restZ⟩
  have ctl : CtlOnly base v.mem z.mem := by
    rw [memZ]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerZ, frameZ⟩ := h.power.after_ctl ctl restZ ((restZ.gpr .r0 (by decide)).trans h.power.ready.ptr)
  obtain ⟨digitZ, pendingZ⟩ := two_writes v.mem base (d := 196) (e := 204)
    (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (by decide) (by decide) (by decide)
  rw [← memZ] at digitZ pendingZ
  have keepsZ : KeepsExp base v.mem z.mem := by
    rw [memZ]; exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide)
  have stateZ : WinState base len w M x 0 0 0 z :=
    ⟨powerZ, h.table.after_ctl ctl fits nowrap (by decide), fits, digitZ, pendingZ, by decide, by decide⟩
  refine ⟨⟨⟨0, 0, stateZ, by rw [pre_zero]⟩, by rw [keepsZ 128 (by decide), h.pointer, BitVec.add_zero],
    by rw [keepsZ 132 (by decide), h.count, Nat.sub_zero], h.countFit, h.sourceFit,
    by rw [restZ.rd, restZ.wr]; exact h.read, h.separate, ?_⟩, frameZ, rest_round restZ⟩
  intro i hi
  rw [frameZ.bytes (R := ⟨State.addr ep, eb.length⟩)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
    (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega_arith) hi]
  exact h.bytes i hi

theorem pending_digit {A p L : Nat} {base : BitVec 32} {len w M x : Nat} {s : State}
    (h : WinState base len w M x A p (8 * L % 3) s) : p < 8 := by
  have := h.bound
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 * L % 3 ≤ 2 by omega_arith)
  simp only [show 2 ^ 2 = 4 from rfl] at this
  omega_arith

theorem windowExpPhase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa windowExpPhase s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [windowExpPhase, WP.seq_iff]
  refine WP.mono (expPhase_init_ready s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (phaseTable_ok u ready fits) ?_
  rintro v ⟨readyV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (phaseReset_ok v readyV) ?_
  rintro z ⟨loopZ, frameZ, restZ⟩
  rw [WP.seq_iff]
  refine WP.mono (windowBytes_ok z loopZ h.positive) ?_
  rintro y ⟨⟨A, p, stateY, sum⟩, frameY, restY⟩
  rw [WP.seq_iff]
  refine WP.mono (windowApply_ok y stateY.power stateY.table fits (pending_digit stateY) stateY.digit) ?_
  rintro r ⟨powerR, _, _, _, _, frameR, restR⟩
  rw [sum] at powerR
  refine WP.mono (exp_finish_ok r powerR) ?_
  rintro t ⟨final, value, keeps, frameT, restT⟩
  have fits8 : arrAt w 8 ≤ 8 * len := powerR.ready.width ▸ powerR.ready.layout.2.2.1
  have modulus := (keeps_array_num keeps fits8 (q := 0)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.modulus
  have r2 := (keeps_array_num keeps fits8 (q := 4)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.r2
  have one := (keeps_array_num keeps fits8 (q := 7)
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans powerR.one
  exact ⟨final, value, modulus, r2, one,
    frameU.trans (frameV.trans (frameZ.trans (frameY.trans (frameR.trans frameT)))),
    restU.trans (restV.trans (restZ.trans (restY.trans (restR.trans restT))))⟩

end VG.Proof.Bignum.Arm
