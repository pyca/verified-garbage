module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessMont
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareData
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessMont
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy

/-! # Witness conversion has a trace independent of the sampled value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessMont
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

def Input (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Prepare.Data g c capacity p s ∧ c % 2 = 1 ∧ 0 < c

def InputPair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ Input g capacity p s ∧ Input g capacity p t

theorem input_mul {g : Geometry} {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Input g capacity p s) : MulInput g capacity 4 p s := by
  obtain ⟨c, A, odd, positive⟩ := S
  exact ⟨A.ready.context, ⟨c, A.ready.modulus, odd, by rw [A.r2]; exact Nat.mod_lt _ positive⟩, A.ready.caller⟩

theorem code_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (InputPair g capacity p) (VG.Impl.RsaKeyGen.X86.WitnessMont.code name mont)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessMont.code
  refine RelCT.seq ?_ (copy_relCT v 5 6 (by decide) (by decide))
  exact (mulY_relCT (p := p) (b := 4) verified noSp stack v length
    (by unfold Spec.Rsa.Mont.Operand; decide)).mono
    (fun _ _ H => ⟨H.1, input_mul H.2.1, input_mul H.2.2⟩) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.WitnessMont
