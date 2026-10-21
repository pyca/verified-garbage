module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBodyTiming
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The outer native key frame preserves trace equivalence -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def FramedPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop :=
  BodyPair E sp e p q p' q' (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (FramedPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.code (fun _ _ => True) := by
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.RsaKeyGen.X86.Key.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace E v sp e p q p' q' release) restore).mono
    (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Key
