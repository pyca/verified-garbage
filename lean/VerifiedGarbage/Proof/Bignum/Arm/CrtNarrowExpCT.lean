module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel

public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowExp
import VerifiedGarbage.Proof.Bignum.Arm.ExpControlsCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowPhaseCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareRedCT

/-! # The narrow exponentiation hides the factor, the reduced input and the exponent -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Spec.Rsa.Mont (arrAt)

theorem crt_narrowExp_ct {base ep : BitVec 32} {len v M1 M2 x1 x2 eLen es : Nat} {eb1 eb2 : List Byte}
    (fit : arrAt v 3 + 32 ≤ 8 * len) (fits : arrAt v 16 ≤ 8 * len) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => NarrowExpInput base ep len v M1 x1 eLen es eb1 s ∧
      NarrowExpInput base ep len v M2 x2 eLen es eb2 t ∧ s.sp = t.sp) ((narrowExpWith kernel.code) es) (fun _ _ => True) := by
  let Loaded := fun (M x : Nat) (eb : List Byte) (s : State) =>
    NarrowExpInput base ep len v M x eLen es eb s ∧ s.gpr .r1 = ep ∧ s.gpr .r2 = BitVec.ofNat 32 eLen
  have args : RelCT isa (fun s t => NarrowExpInput base ep len v M1 x1 eLen es eb1 s ∧
      NarrowExpInput base ep len v M2 x2 eLen es eb2 t ∧ s.sp = t.sp) (.block (exponentArgs es)) (fun _ _ => True) :=
    (stackLoads_ct [(.r1, es), (.r2, es + 4)]).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have argsWP (s : State) {M x : Nat} {eb : List Byte} (h : NarrowExpInput base ep len v M x eLen es eb s) :
      WP isa (.block (exponentArgs es)) s (Loaded M x eb) :=
    (crt_exponentArgs_ok s h).mono fun _ j => ⟨h.of_mem j.2.2.1 j.2.2.2, j.1, j.2.1⟩
  have controls : RelCT isa (fun s t => Loaded M1 x1 eb1 s ∧ Loaded M2 x2 eb2 t ∧ s.sp = t.sp)
      (.block expControls) (fun _ _ => True) :=
    expControls_ct.mono (fun _ _ h => h.1.1.ready.ptr.trans h.2.1.1.ready.ptr.symm) (fun _ _ _ => trivial)
  let Phase := fun (M x : Nat) (eb : List Byte) (s : State) => ExpPhaseInput base ep len v M x eb s ∧ eb.length = eLen
  have controlsWP (s : State) {M x : Nat} {eb : List Byte} (h : Loaded M x eb s) :
      WP isa (.block expControls) s (Phase M x eb) :=
    (crt_narrowControls_ready s h.1 h.2.1 h.2.2).mono fun _ j => ⟨j.1, h.1.exponent.length⟩
  have phase : RelCT isa (fun s t => Phase M1 x1 eb1 s ∧ Phase M2 x2 eb2 t ∧ s.sp = t.sp)
      kernel.code (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact kernel.ct fit fits h.1.1.positive (h.1.2.trans h.2.1.2.symm) s t tr1 tr2 u w
      ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  rw [narrowExpWith]
  exact crt_seq_ct args (fun s h => argsWP s h) (fun s h => argsWP s h)
    (crt_seq_ct controls (fun s h => controlsWP s h) (fun s h => controlsWP s h) phase)

end VG.Proof.Bignum.Arm
