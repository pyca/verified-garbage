module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
public import VerifiedGarbage.Proof.Bignum.Arm.ExpPhaseInput

/-! # Windowed private RSA exponentiation implements the modular-exponentiation specification -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)
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
  have size : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have addr (d : Nat) (hd : d ≤ 252) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold expByteNext
  refine wp_ldr (a := off (State.addr base) 128) (by decide) (addr 128 (by decide))
    (h.workspace.read (by omega)) fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_str (a := off (State.addr base) 128) (by decide)
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 128 (by decide))
    (by rw [b.wr, a.wr]; exact h.workspace.write (by omega)) fun z d => ?_
  have memZ : z.mem = s.mem.writeW (off (State.addr base) 128) (ep + 1) := by
    rw [d.mem, b.mem, a.mem, b.gpr, dpVal, a.gpr, pointer]
  have outsideZ := writeW32_outside s.mem (State.addr base) (d := 128) (ep + 1) (by decide)
  rw [← memZ] at outsideZ
  refine wp_ldr (a := off (State.addr base) 132) (by decide)
    (by rw [congrFun d.gpr .r0, b.other .r0 (by decide), a.other .r0 (by decide)]; exact addr 132 (by decide))
    (by rw [d.rd, d.wr, b.rd, b.wr, a.rd, a.wr]; exact h.workspace.read (by omega)) fun q e => ?_
  refine wp_subs (op2_imm (by decide)) fun r f zero => ?_
  refine wp_str_z (a := off (State.addr base) 132) (by decide)
    (by rw [f.other .r0 (by decide), e.other .r0 (by decide), congrFun d.gpr .r0, b.other .r0 (by decide),
      a.other .r0 (by decide)]; exact addr 132 (by decide))
    (by rw [f.wr, e.wr, d.wr, b.wr, a.wr]; exact h.workspace.write (by omega)) fun t g zeroT => WP.block_nil ?_
  have value : r.gpr .r1 = BitVec.ofNat 32 (c - 1) := by
    rw [f.gpr, e.gpr, outside_read32 outsideZ (d := 132) (by decide) (by decide), count]
    change BitVec.ofNat 32 c - BitVec.ofNat 32 1 = _
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
  refine ⟨by rw [g.mem, f.mem, e.mem, memZ, value], ?_,
    (a.rest (by simp)).trans ((b.rest (by simp)).trans ((d.rest _).trans ((e.rest (by simp)).trans
      ((f.rest (by simp)).trans (g.rest _)))))⟩
  rw [zeroT, zero, ← f.gpr, value, ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem windowBytes_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : WinState base len w M x 0 0 0 s) (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (sourceFit : ep.toNat + eb.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length)
    (separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩)
    (bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i])
    (pointer : s.mem.readW (off (State.addr base) 128) 32 = ep)
    (count : s.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 eb.length) :
    WP isa windowBytes s fun t =>
      (∃ A p, WinState base len w M x A p (8 * eb.length % 3) t ∧ A + p = Spec.Rsa.os2ip eb) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let I := fun k t => ∃ j, j + k = eb.length ∧ 0 < k ∧
    (∃ A p, WinState base len w M x A p (8 * j % 3) t ∧ A + p = pre eb j) ∧
    t.mem.readW (off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j ∧
    t.mem.readW (off (State.addr base) 132) 32 = BitVec.ofNat 32 k ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  unfold windowBytes
  refine WP.loop (M := isa) I ?_ eb.length s ?_
  · intro k t inv
    obtain ⟨j, jk, hk, ⟨A, p, state, sum⟩, ptr, counter, frame, rest⟩ := inv
    have hj : j < eb.length := by omega
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have currentRead : InRegions (t.rd ++ t.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [rest.rd, rest.wr, address]
      exact CallLay.inRegions_sub read (by omega) (by omega)
    have currentByte : t.mem (State.addr (ep + BitVec.ofNat 32 j)) = eb[j] := by
      rw [address, frame.bytes (R := ⟨State.addr ep, eb.length⟩)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact separate)
        (by change eb.length ≤ 2 ^ 64; omega) hj]
      exact bytes j hj
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
    rw [show 8 * j + 8 = 8 * (j + 1) by omega] at stateY
    have ptrY := (keepsY 128 (by simp)).trans ((keepsU 128 (by simp)).trans ptr)
    have countY := (keepsY 132 (by simp)).trans ((keepsU 132 (by simp)).trans counter)
    refine WP.mono (expByteNext_mem y stateY.power.ready hk (by omega) ptrY countY) ?_
    rintro z ⟨memZ, zero, restZ⟩
    have ctl : CtlOnly base y.mem z.mem := by
      rw [memZ]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    have fits := stateY.fits
    have nowrap := stateY.power.ready.workspace.nowrap
    obtain ⟨powerZ, frameZ⟩ := stateY.power.after_ctl ctl restZ
      ((restZ.gpr .r0 (by simp)).trans stateY.power.ready.ptr)
    obtain ⟨ptrZ, counterZ⟩ := two_writes y.mem base (d := 128) (e := 132)
      (ep + BitVec.ofNat 32 j + 1) (BitVec.ofNat 32 (k - 1)) (by decide) (by decide) (by decide)
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
    have ptrNext : z.mem.readW (off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 (j + 1) := by
      rw [ptrZ]
      change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have frameAll := frame.trans (frameU.trans (frameY.trans frameZ))
    have restAll := rest.trans (restU.trans (restY.trans (rest_round restZ)))
    by_cases last : k = 1
    · left
      refine ⟨?_, ⟨A', p', by rw [← show j + 1 = eb.length by omega]; exact stateZ,
        by simpa only [show j + 1 = eb.length by omega, pre_len] using sumY⟩, frameAll, restAll⟩
      change some (!z.z) = some false
      simp only [zero, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, ⟨A', p', stateZ, sumY⟩, ptrNext,
        counterZ, frameAll, restAll⟩
      change some (!z.z) = some true
      simp only [zero, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, positive, ⟨0, 0, h, by rw [pre_zero]⟩, ?_, count, Frame.refl _ _, Rest.refl _ _⟩
    simpa only [BitVec.add_zero] using pointer

theorem windowExpPhase_ok (s : State) {base ep : BitVec 32} {len w M x : Nat} {eb : List Byte}
    (h : ExpPhaseInput base ep len w M x eb s) (fits : arrAt w 16 ≤ 8 * len) :
    WP isa windowExpPhase s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x (Spec.Rsa.os2ip eb) M ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      numAt t.mem (State.addr base) w 7 = 1 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  rw [windowExpPhase, WP.seq_iff]
  refine WP.mono (expPhase_init_ready s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (tableBuild_ok u ready.power fits) ?_
  rintro v ⟨powerV, tableV, keepsV, frameV, restV⟩
  rw [WP.seq_iff]
  refine WP.mono (windowReset_ok v powerV.ready) ?_
  rintro z ⟨memZ, restZ⟩
  have ctl : CtlOnly base v.mem z.mem := by
    rw [memZ]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerZ, frameZ⟩ := powerV.after_ctl ctl restZ ((restZ.gpr .r0 (by simp)).trans powerV.ready.ptr)
  obtain ⟨digitZ, pendingZ⟩ := two_writes v.mem base (d := 196) (e := 204)
    (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (by decide) (by decide) (by decide)
  rw [← memZ] at digitZ pendingZ
  have keepsZ : KeepsExp base u.mem z.mem := keepsV.trans (by
    rw [memZ]; exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide))
  have stateZ : WinState base len w M x 0 0 0 z :=
    ⟨powerZ, tableV.after_ctl ctl fits nowrap (by decide), fits, digitZ, pendingZ, by decide, by decide⟩
  have frameUZ := frameV.trans frameZ
  have restUZ : Rest roundClobbers u z := restV.trans (rest_round restZ)
  rw [WP.seq_iff]
  refine WP.mono (windowBytes_ok z stateZ h.positive ready.countFit ready.sourceFit
    (by rw [restUZ.rd, restUZ.wr]; exact ready.read) ready.separate
    (by
      intro i hi
      rw [frameUZ.bytes (R := ⟨State.addr ep, eb.length⟩)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ready.separate)
        (by change eb.length ≤ 2 ^ 64; have := ready.countFit; omega) hi]
      exact ready.bytes i hi)
    (by rw [keepsZ 128 (by simp), ready.pointer, BitVec.add_zero])
    (by rw [keepsZ 132 (by simp), ready.count, Nat.sub_zero])) ?_
  rintro y ⟨⟨A, p, stateY, sum⟩, frameY, restY⟩
  rw [WP.seq_iff]
  have small : p < 8 := by
    have := stateY.bound
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 * eb.length % 3 ≤ 2 by omega)
    simp only [show 2 ^ 2 = 4 from rfl] at this
    omega
  refine WP.mono (windowApply_ok y stateY.power stateY.table fits small stateY.digit) ?_
  rintro r ⟨powerR, _, _, _, _, frameR, restR⟩
  rw [sum] at powerR
  refine WP.mono (exp_finish_ok r powerR) ?_
  rintro t ⟨final, value, keeps, frameT, restT⟩
  have fits8 : arrAt w 8 ≤ 8 * len := powerR.ready.width ▸ powerR.ready.layout.2.2.1
  have modulus := (keeps_array_num keeps fits8 (q := 0)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans powerR.modulus
  have r2 := (keeps_array_num keeps fits8 (q := 4)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans powerR.r2
  have one := (keeps_array_num keeps fits8 (q := 7)
    (by simp [Spec.Rsa.Mont.Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide)).trans powerR.one
  exact ⟨final, value, modulus, r2, one, frameU.trans (frameUZ.trans (frameY.trans (frameR.trans frameT))),
    restU.trans (restUZ.trans (restY.trans (restR.trans restT)))⟩

end VG.Proof.Bignum.Arm
