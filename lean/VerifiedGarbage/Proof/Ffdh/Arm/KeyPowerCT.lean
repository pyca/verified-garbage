module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower

import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpStep
import VerifiedGarbage.Impl.Bignum.Arm.TwoExp
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteState
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.ExpByteHeadCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhase
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBytes
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Impl.Ffdh.Arm.KeyPowerDetect
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.EqualCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
/-! # Imported public-generator dispatch retains private-scalar timing -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/TwoExpBytesCT.lean`, which only this module imported.
section

/-! # The generator-two exponent-buffer loop has a public schedule

The two compared buffers may contain arbitrary different scalars. Only
their common address and length determine the loop's trace.
-/

section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm

theorem byte_ct {base ep : BitVec 32} {len w M1 M2 E1 E2 : Nat} {b1 b2 : Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) :
    RelCT isa (fun s t => (ByteInput base ep len w M1 E1 b1 s ∧ P s) ∧
      (ByteInput base ep len w M2 E2 b2 t ∧ P t) ∧ s.sp = t.sp)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext)))
      (fun _ _ => True) := by
  have head (s : State) {M E : Nat} {b : Byte} (h : ByteInput base ep len w M E b s ∧ P s) :
      WP isa expByteHead s fun t => BitState base len w M E b.toNat 0 t ∧ P t := by
    refine WP.mono (byteHead_ok s h.1.power h.1.pointer h.1.read) ?_
    rintro t ⟨state, _, frame, rest⟩
    rw [h.1.byte] at state
    exact ⟨state, K.stable frame (rest.mono (by decide)) h.2⟩
  have bits (s : State) {M E : Nat} {b : Byte} (h : BitState base len w M E b.toNat 0 s ∧ P s) :
      WP isa (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) s (ArithmeticReady base len w) :=
    WP.mono (bits_ok K s h.1 h.2 b.isLt) fun _ k => k.1.ready
  refine relCT_chain
    (expByteHead_ct.mono
      (fun _ _ h => ⟨⟨h.1.1.power.ready, h.1.1.pointer⟩, ⟨h.2.1.1.power.ready, h.2.1.1.pointer⟩⟩)
      (fun _ _ h => h)) (fun s h => head s h) (fun s h => head s h) ?_
  exact relCT_chain (bits_ct K ct b1.isLt b2.isLt) (fun s h => bits s h) (fun s h => bits s h)
    (expByteNext_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h))

theorem byteBody_ct {base ep : BitVec 32} {len w M1 M2 j : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) (hj1 : j < eb1.length) (hj2 : j < eb2.length) :
    RelCT isa (fun s t => ByteState base ep len w M1 P regions eb1 j s ∧
      ByteState base ep len w M2 P regions eb2 j t ∧ s.sp = t.sp)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext)))
      (fun _ _ => True) :=
  (byte_ct K ct).mono
    (fun _ _ h => ⟨⟨h.1.input hj1, h.1.persistent⟩, ⟨h.2.1.input hj2, h.2.1.persistent⟩, h.2.2⟩)
    (fun _ _ h => h)

theorem bytes_ct {base ep : BitVec 32} {len w M1 M2 : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Kernel base len w P regions) (ct : Timing K) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => ByteState base ep len w M1 P regions eb1 0 s ∧
      ByteState base ep len w M2 P regions eb2 0 t ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.TwoExp.bytes K.square K.twice) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    ByteState base ep len w M1 P regions eb1 j s ∧ ByteState base ep len w M2 P regions eb2 j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k)
      (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.TwoExp.bits K.square K.twice) (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have c := relCT_keep_sp (byteBody_ct (ep := ep) (M1 := M1) (M2 := M2) K ct (by omega : j < eb1.length) (by omega : j < eb2.length))
      (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := c s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, _⟩ := byteState_step K s hs (by omega)
    obtain ⟨_, _, run2, next2, zero2, _, _⟩ := byteState_step K t ht (by omega)
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
  unfold VG.Impl.Bignum.Arm.TwoExp.bytes
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm.TwoExp
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/TwoExpPhaseCT.lean`, which only this module imported.
section

/-! # Generator-two initialization, full scalar loop, and decoding are constant time -/

section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)

theorem init_ct {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (ct : MontgomeryTiming A) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ P s) ∧
      (ArithmeticReady base len w t ∧ P t) ∧ s.sp = t.sp) A.init (fun _ _ => True) := by
  have one (s : State) (h : ArithmeticReady base len w s ∧ P s) :
      WP isa (smallConst 7 1) s (OpInput base len w P 7) := by
    refine WP.mono (smallConst_ok s (1 : BitVec 32) h.1 (o := 7)
      (by decide) (by decide) (by decide) (by decide)) ?_
    rintro t ⟨ready, value, _, _, frame, rest⟩
    refine ⟨ready, A.stable frame rest h.2, ?_⟩
    change numAt t.mem (State.addr base) w 7 = 1 at value
    rw [value]; exact ready.modulus
  have multiply (s : State) (h : OpInput base len w P 7 s) :
      WP isa (A.op 6 4 7) s fun t => ArithmeticReady base len w t ∧ P t := by
    refine WP.mono (A.op_ok s 6 4 7 h.1 h.2.1
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) h.2.2) ?_
    rintro t ⟨ready, _, _, _, _, pt, _, _⟩
    exact ⟨ready, pt⟩
  unfold Montgomery.init
  refine relCT_chain
    ((smallConst_ct (1 : BitVec 32) (o := 7) (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) one one ?_
  exact relCT_chain
    (ct.op_ct 6 4 7
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])) multiply multiply
    ((smallConst_ct (2 : BitVec 32) (o := 5) (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))

theorem finish_ct {base : BitVec 32} {len w M1 M2 E1 E2 : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (ct : MontgomeryTiming A) :
    RelCT isa (fun s t => (Power base len w M1 E1 s ∧ P s) ∧
      (Power base len w M2 E2 t ∧ P t) ∧ s.sp = t.sp) (A.op 6 6 7) (fun _ _ => True) :=
  (ct.op_ct 6 6 7
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])).mono
    (fun _ _ h => ⟨⟨h.1.1.ready, h.1.2, by rw [h.1.1.one]; exact h.1.1.ready.modulus⟩,
      ⟨h.2.1.1.ready, h.2.1.2, by rw [h.2.1.1.one]; exact h.2.1.1.ready.modulus⟩, h.2.2⟩)
    (fun _ _ h => h)

theorem phase_ct {base ep : BitVec 32} {len w M1 M2 : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (ct : MontgomeryTiming A)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => Input base ep len w M1 P regions eb1 s ∧
      Input base ep len w M2 P regions eb2 t ∧ s.sp = t.sp) A.phase (fun _ _ => True) := by
  have initial (s : State) {M : Nat} {eb : List Byte} (h : Input base ep len w M P regions eb s) :
      WP isa A.init s (ByteState base ep len w M P regions eb 0) :=
    WP.mono (init_bytes_ready A s h) fun _ k => k.1
  have loop (s : State) {M : Nat} {eb : List Byte} (h : ByteState base ep len w M P regions eb 0 s)
      (positive : 0 < eb.length) :
      WP isa (VG.Impl.Bignum.Arm.TwoExp.bytes A.kernel.square A.kernel.twice) s fun t =>
        Power base len w M (Spec.Rsa.os2ip eb) t ∧ P t :=
    WP.mono (bytes_ok A.kernel s (by simpa only [pre_zero] using h.power) h.persistent positive h.countFit
      h.sourceFit h.read h.separate h.bytes (by simpa only [BitVec.add_zero] using h.pointer)
      (by simpa only [Nat.sub_zero] using h.count)) fun _ k => ⟨k.1, k.2.1⟩
  unfold Montgomery.phase VG.Impl.Bignum.Arm.TwoExp.phase
  refine relCT_chain
    ((init_ct A ct).mono
      (fun _ _ h => ⟨⟨h.1.phase.ready, h.1.persistent⟩, ⟨h.2.1.phase.ready, h.2.1.persistent⟩, h.2.2⟩)
      (fun _ _ h => h)) (fun s h => initial s h) (fun s h => initial s h) ?_
  exact relCT_chain (bytes_ct A.kernel (ct.kernelTiming fit hn) positive length)
    (fun s h => loop s h positive) (fun s h => loop s h (by rw [← length]; exact positive))
    (finish_ct A ct)

end VG.Proof.Bignum.Arm.TwoExp
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyPowerDetectCT.lean`, which only this module imported.
section

/-! Generator detection uses no operand-dependent branch or address. -/

section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

theorem detectTwo_ct {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.detectTwo (fun _ _ => True) := by
  have ready (s : State) (h : ArithmeticReady base len w s) :
      WP isa (VG.Impl.Bignum.Arm.smallConst 5 2) s (ArithmeticReady base len w) :=
    WP.mono (smallConst_ok s 2 h (o := 5) (by decide) (by decide) (by decide) (by decide)) fun _ k => k.1
  unfold VG.Impl.Ffdh.Arm.detectTwo
  exact relCT_chain (smallConst_ct 2 (o := 5) (by decide) (by decide) (by decide)) ready ready
    (equal_ct
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 1)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 5))

end VG.Proof.Ffdh.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeyPowerPhaseCT.lean`, which only this module imported.
section

/-! # The generator dispatch reveals only the public generator -/

section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem Detected.of_mem {base ep : BitVec 32} {len w M x : Nat} {P : State → Prop}
    {regions : List Region} {eb : List Byte} {s t : State}
    (A : TwoExp.Montgomery base len w P regions) (h : Detected base ep len w M x P regions eb s)
    (mem : t.mem = s.mem) (rest : Rest [] s t) : Detected base ep len w M x P regions eb t :=
  ⟨h.input.of_mem A mem rest (by simp) ((rest.gpr .r0 (by simp)).trans h.input.phase.ready.ptr),
    (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem phase_ct {base ep : BitVec 32} {len w M1 M2 x : Nat} {P : State → Prop}
    {regions : List Region} {eb1 eb2 : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fallback : Fallback base len w P regions)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => PhaseInput base ep len w M1 x P regions eb1 s ∧
      PhaseInput base ep len w M2 x P regions eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyPower.phase A.phase fallback.code) (fun _ _ => True) := by
  have branches : RelCT isa (fun s t => Detected base ep len w M1 x P regions eb1 s ∧
      Detected base ep len w M2 x P regions eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.Domain.ifFlag A.phase fallback.code) (fun _ _ => True) := by
    apply ifFlag_pair_ct (decide (x = 2))
      (fun s h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun s h => by simpa only [decide_eq_true_eq] using h.flag)
      (fun _ _ h mem rest => h.of_mem A mem rest) (fun _ _ h mem rest => h.of_mem A mem rest)
    · intro hb
      have two : x = 2 := of_decide_eq_true hb
      subst x
      exact (TwoExp.phase_ct A ct fit hn positive length).mono
        (fun _ _ h => ⟨⟨h.1.input.phase, h.1.input.persistent, h.1.input.separate⟩,
          ⟨h.2.1.input.phase, h.2.1.input.persistent, h.2.1.input.separate⟩, h.2.2⟩) (fun _ _ h => h)
    · intro _
      exact (fallback.ct positive length).mono
        (fun _ _ h => ⟨h.1.input, h.2.1.input, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyPower.phase
  exact relCT_chain
    (detectTwo_ct.mono (fun _ _ h => ⟨h.1.phase.ready, h.2.1.phase.ready, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (detected_ok A s h) fun _ k => k.1)
    (fun s h => WP.mono (detected_ok A s h) fun _ k => k.1) branches

end VG.Proof.Ffdh.Arm.KeyPower
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem import_ct {base src ep : BitVec 32} {len w M1 M2 : Nat} {bb eb1 eb2 : List Byte}
    (_length : eb1.length = eb2.length) :
    RelCT isa (fun s t => PowerInput base src ep len w M1 bb eb1 s ∧
      PowerInput base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.powerImport (fun _ _ => True) := by
  have controls := expControls_ct.mono
    (P' := fun (s t : State) => PowerInput base src ep len w M1 bb eb1 s ∧
      PowerInput base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h)
  have importCT := (importOperand_ct (base := base) (src := src) (len := len) (w := w) (k := bb.length)
    (by decide : 1 < 8)).mono
    (P' := fun (s t : State) => PowerPrepared base src ep len w M1 bb eb1 s ∧
      PowerPrepared base src ep len w M2 bb eb2 t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.input.ready, h.2.1.input.ready, h.1.input.source,
      h.2.1.input.source, h.1.input.count, h.2.1.input.count, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.powerImport
  exact relCT_chain controls
    (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1)
    (fun s h => WP.mono (powerControls_ok s h) fun _ k => k.1) importCT

theorem power_ct {base src ep : BitVec 32} {len w M1 M2 : Nat} {P : State → Prop}
    {regions : List Region} {bb eb1 eb2 : List Byte}
    (A : TwoExp.Montgomery base len w P regions) (ct : TwoExp.MontgomeryTiming A)
    (fallback : Fallback base len w P regions)
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length) :
    RelCT isa (fun s t => Input base src ep len w M1 P regions bb eb1 s ∧
      Input base src ep len w M2 P regions bb eb2 t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyPower.power A.phase fallback.code) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeyPower.power
  exact relCT_chain
    ((import_ct length).mono (fun _ _ h => ⟨h.1.power, h.2.1.power, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (import_ok A s h) fun _ k => k.1)
    (fun s h => WP.mono (import_ok A s h) fun _ k => k.1)
    (phase_ct A ct fallback fit hn positive length)

end VG.Proof.Ffdh.Arm.KeyPower
