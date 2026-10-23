module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Square
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Prepared R² squarings leak no candidate or intermediate residue -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

def SquareInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array 6) g.words < c

def SquarePair (g : Geometry) (capacity : Nat) (p : BitVec 32) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ SquareInput g capacity p s ∧ SquareInput g capacity p t

theorem square_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (SquarePair g capacity p) (VG.Impl.MillerRabin.X86.mulY name mont 6)
      (SquarePair g capacity p) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  have input {a : State} (I : SquareInput g capacity p a) : MulInput g capacity 6 p a := by
    obtain ⟨c, A, odd, lt⟩ := I
    exact ⟨A.context, ⟨c, A.modulus, odd, lt⟩, A.caller⟩
  have post {a : State} (I : SquareInput g capacity p a) :
      WP isa (VG.Impl.MillerRabin.X86.mulY name mont 6) a (SquareInput g capacity p) := by
    obtain ⟨c, A, odd, lt⟩ := I
    refine WP.mono (FastR2.square_ok verified noSp stack v A.context length A.modulus A.caller odd lt)
      fun b ⟨Cb, Mb, caller, bound, _, _, K, _⟩ => ?_
    exact ⟨c, ⟨Cb, Mb, caller, A.scratch.of_keeps K (by decide)⟩, odd, bound⟩
  obtain ⟨trace, pair⟩ := mulY_relCT (p := p) verified noSp stack v length
    (by unfold Spec.Rsa.Mont.Operand; decide) _ _ _ _ _ _ ⟨H, input S, input T⟩ E G
  exact ⟨trace, pair, wp_result (post S) E, wp_result (post T) G⟩

theorem squares_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity)
    (n : Nat) :
    RelCT isa (SquarePair g capacity p)
      (VG.Impl.Rsa.X86.Keys.seqs (List.replicate (n + 1) (VG.Impl.MillerRabin.X86.mulY name mont 6)))
      (SquarePair g capacity p) := by
  induction n with
  | zero => exact square_pair verified noSp stack v length
  | succ n ih => exact RelCT.seq (square_pair verified noSp stack v length) ih

end VG.Proof.RsaKeyGen.X86.PreparedR2
