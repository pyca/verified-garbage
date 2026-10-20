module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpBytes
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # Generator-two initialization, full scalar loop, and decoding are constant time -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt arrAt Operand)

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
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide) h.2.2) ?_
    rintro t ⟨ready, _, _, _, _, pt, _, _⟩
    exact ⟨ready, pt⟩
  unfold Montgomery.init
  refine relCT_chain
    ((smallConst_ct (1 : BitVec 32) (o := 7) (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h)) one one ?_
  exact relCT_chain
    (ct.op_ct 6 4 7
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
      (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])) multiply multiply
    ((smallConst_ct (2 : BitVec 32) (o := 5) (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))

theorem finish_ct {base : BitVec 32} {len w M1 M2 E1 E2 : Nat} {P : State → Prop} {regions : List Region}
    (A : Montgomery base len w P regions) (ct : MontgomeryTiming A) :
    RelCT isa (fun s t => (Power base len w M1 E1 s ∧ P s) ∧
      (Power base len w M2 E2 t ∧ P t) ∧ s.sp = t.sp) (A.op 6 6 7) (fun _ _ => True) :=
  (ct.op_ct 6 6 7
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])
    (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp])).mono
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
