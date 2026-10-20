module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedPair
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInput
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Importing the secret representative has a trace fixed by public geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem precomputedInput_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputedPair base bytes len args) (PrecomputedFn.importInput (Spec.Rsa.modulusWords len))
      (PrecomputedPair base bytes len args) := by
  intro s t tr ur sf tf H E F
  have CT := VG.RelCT.seq (loadArguments_relCT 6 7 (args 6) (args 7))
    (loadBE_relCT (Spec.Rsa.modulusWords len) (VG.Impl.Bignum.X86.PublicContext.slot (Spec.Rsa.modulusWords len) 6))
  have T := (CT _ _ _ _ _ _ ⟨H.agree, (H.left.stack 6 (by decide)).readSrc,
    (H.right.stack 6 (by decide)).readSrc, (H.left.stack 7 (by decide)).readSrc,
    (H.right.stack 7 (by decide)).readSrc⟩ E F).1
  have W (u : State) (I : PrecomputedInputs base bytes len args u) :=
    PublicContext.precomputedInput_ok I.scratch I.dimensions.1 I.space (by have := I.lower; omega)
      I.dimensions.2.2 (I.stack 6 (by decide))
      (by rw [← I.inLen]; exact I.stack 7 (by decide)) I.inFit I.inRead I.inApart
  obtain ⟨_, Os, Ks⟩ := wp_result (W s H.left) E
  obtain ⟨_, Ot, Kt⟩ := wp_result (W t H.right) F
  have sz := H.left.space
  have bound := PublicContext.slot_bound (n := Spec.Rsa.modulusWords len) (i := 6) (by decide)
  simp only [VG.Impl.Bignum.X86.PublicContext.stride] at bound
  exact ⟨T, H.keep Ks Kt (by decide) (by decide) (Os.mono (by omega) (by omega))
    (Ot.mono (by omega) (by omega))⟩

end VG.Proof.Bignum.X86
