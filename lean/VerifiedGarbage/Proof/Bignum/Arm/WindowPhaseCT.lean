module
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase

import VerifiedGarbage.Proof.Bignum.Arm.WindowBitCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpInitCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowScanCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! # Windowed private RSA exponentiation hides the exponent, input, and modulus values -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem windowByteBody_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 j : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) (hj1 : j < eb1.length)
    (hj2 : j < eb2.length) :
    RelCT isa (fun s t => WinByteLoop base ep len w M1 x1 eb1 j s ∧ WinByteLoop base ep len w M2 x2 eb2 j t ∧
      s.sp = t.sp) (.seq expByteHead (.seq windowBits (.block expByteNext))) (fun _ _ => True) := by
  -- after the head: the bits of the byte
  have head (s : State) {M x : Nat} {eb : List Byte} (h : WinByteLoop base ep len w M x eb j s)
      (hj : j < eb.length) :
      WP isa expByteHead s (WinBitState base len w M x (pre eb j) (eb[j]).toNat (8 * j) 0) := by
    obtain ⟨⟨A, p, state, sum⟩, ptr, _, _, sourceFit, read, _, bytes⟩ := h
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have current : InRegions (s.rd ++ s.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [address]; exact CallLay.inRegions_sub read (by omega) (by omega)
    refine WP.mono (windowByteHead_ok s state ptr current) ?_
    rintro u ⟨stateU, byteU, countU, _, _, _⟩
    rw [address, bytes j hj] at byteU
    have v256 := (eb[j]).isLt
    exact ⟨⟨A, p, stateU, by rw [sum, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt v256, Nat.add_zero]⟩, by rw [Nat.pow_zero, Nat.mul_one]; exact byteU, countU⟩
  have bits (u : State) {M x E v n : Nat} (h : WinBitState base len w M x E v n 0 u) (hv : v < 256) :
      WP isa windowBits u fun y => y.gpr .r0 = base :=
    WP.mono (windowBits_ok u h hv) fun _ ⟨⟨_, _, k, _⟩, _⟩ => k.power.ready.ptr
  refine relCT_chain (Q₁ := WinBitState base len w M1 x1 (pre eb1 j) (eb1[j]).toNat (8 * j) 0)
    (Q₂ := WinBitState base len w M2 x2 (pre eb2 j) (eb2[j]).toNat (8 * j) 0)
    ((expByteHead_ct (base := base) (ep := ep + BitVec.ofNat 32 j) (len := len) (w := w)).mono
      (fun _ _ h => ⟨⟨(Classical.choose_spec (Classical.choose_spec h.1.state)).1.power.ready, h.1.pointer⟩,
        ⟨(Classical.choose_spec (Classical.choose_spec h.2.1.state)).1.power.ready, h.2.1.pointer⟩⟩)
      (fun _ _ h => h))
    (fun s h => head s h hj1) (fun s h => head s h hj2) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (windowBits_ct fit fits (eb1[j]).isLt (eb2[j]).isLt)
    (fun s h => bits s h (eb1[j]).isLt) (fun s h => bits s h (eb2[j]).isLt)
    (expByteNext_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem windowBytes_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => WinByteLoop base ep len w M1 x1 eb1 0 s ∧ WinByteLoop base ep len w M2 x2 eb2 0 t ∧
      s.sp = t.sp) windowBytes (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    WinByteLoop base ep len w M1 x1 eb1 j s ∧ WinByteLoop base ep len w M2 x2 eb2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq windowBits (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have ct := relCT_keep_sp (windowByteBody_ct (base := base) (ep := ep) (M1 := M1) (M2 := M2) (x1 := x1)
      (x2 := x2) (j := j) (eb1 := eb1) (eb2 := eb2) fit fits (by omega) (by omega)) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _⟩ := windowByteStep_ok s hs (by omega)
    obtain ⟨_, _, run2, next2, zero2, _, _⟩ := windowByteStep_ok t ht (by omega)
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2, length]
    · intro again
      have notLast : j + 1 ≠ eb1.length := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, next1, next2, sp'⟩
  unfold windowBytes
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

theorem windowExpPhase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => ExpPhaseInput base ep len w M1 x1 eb1 s ∧
      ExpPhaseInput base ep len w M2 x2 eb2 t ∧ s.sp = t.sp) windowExpPhase (fun _ _ => True) := by
  -- the last window applied, then the result out of Montgomery form
  let F := fun (M x : Nat) (eb : List Byte) (s : State) =>
    ∃ A p, WinState base len w M x A p (8 * eb.length % 3) s ∧ A + p = Spec.Rsa.os2ip eb
  have finishReady (s : State) {M x : Nat} {eb : List Byte} (h : F M x eb s) :
      WP isa windowApply s fun t => ArithmeticReady base len w t ∧
        numAt t.mem (State.addr base) w 7 < numAt t.mem (State.addr base) w 0 := by
    obtain ⟨A, p, state, _⟩ := h
    refine WP.mono (windowApply_ok s state.power state.table fits (pending_digit state) state.digit) ?_
    rintro t ⟨power, _, _, _, _, _, _⟩
    exact ⟨power.ready, by rw [power.one]; exact power.ready.modulus⟩
  have apply : RelCT isa (fun s t => F M1 x1 eb1 s ∧ F M2 x2 eb2 t ∧ s.sp = t.sp) windowApply
      (fun _ _ => True) := by
    intro s t tr1 tr2 u z h e1 e2
    obtain ⟨⟨A1, p1, state1, _⟩, ⟨A2, p2, state2, _⟩, sp⟩ := h
    exact windowApply_ct fit fits s t tr1 tr2 u z ⟨⟨state1.power, state1.table, pending_digit state1,
      state1.digit⟩, ⟨state2.power, state2.table, pending_digit state2, state2.digit⟩, sp⟩ e1 e2
  unfold windowExpPhase
  refine relCT_chain (Q₁ := ExpByteState base ep len w M1 x1 eb1 0) (Q₂ := ExpByteState base ep len w M2 x2 eb2 0)
    ((expInit_ct fit).mono (fun _ _ h => ⟨⟨h.1.ready, by rw [h.1.modulus]; exact h.1.r2bound⟩,
      ⟨h.2.1.ready, by rw [h.2.1.modulus]; exact h.2.1.r2bound⟩, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (expPhase_init_ready s h) fun _ k => k.1)
    (fun s h => WP.mono (expPhase_init_ready s h) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := WinReady base ep len w M1 x1 eb1) (Q₂ := WinReady base ep len w M2 x2 eb2)
    ((tableBuild_ct fit fits).mono (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (phaseTable_ok s h fits) fun _ k => k.1)
    (fun s h => WP.mono (phaseTable_ok s h fits) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := WinByteLoop base ep len w M1 x1 eb1 0) (Q₂ := WinByteLoop base ep len w M2 x2 eb2 0)
    (windowReset_ct.mono (fun _ _ h => h.1.power.ready.ptr.trans h.2.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (phaseReset_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (phaseReset_ok s h) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := F M1 x1 eb1) (Q₂ := F M2 x2 eb2) (windowBytes_ct fit fits positive length)
    (fun s h => WP.mono (windowBytes_ok s h positive) fun _ k => k.1)
    (fun s h => WP.mono (windowBytes_ok s h (by omega)) fun _ k => k.1) ?_
  exact relCT_chain apply (fun s h => finishReady s h) (fun s h => finishReady s h)
    (montOp_ct (base := base) (o := 6) (a := 6) (b := 7)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit)

end VG.Proof.Bignum.Arm
