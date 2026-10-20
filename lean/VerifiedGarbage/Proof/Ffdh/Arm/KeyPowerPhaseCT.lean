module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerPhase
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpPhaseCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyPowerDetectCT
import VerifiedGarbage.Proof.Ffdh.Arm.FlagCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

/-! # The generator dispatch reveals only the public generator -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeyPower
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)
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
