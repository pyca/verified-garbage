module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Square
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Squares
import VerifiedGarbage.Proof.Bignum.Math

/-! # Six prepared Montgomery calls complete the short R² setup -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

structure SquaresState (g : Geometry) (c capacity : Nat) (p : BitVec 32) (s t : State) : Prop where
  ready : Ready g c capacity p t
  workspace : WorkspaceFrame g (montWrites g 6) s.mem t.mem
  memory : Frame ([⟨g.W, g.L⟩] ++ [below p 40]) s.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx] s t

theorem squares_ready {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (odd : c % 2 = 1)
    (value : val32 s.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 (VG.Impl.MillerRabin.X86.mulY name mont 6))) s fun t =>
      SquaresState g c capacity p s t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c := by
  let num : State → Nat := fun t => val32 t.mem g.W (g.array 6) g.words
  have positive : 0 < c := by omega
  have initial : SquaresState g c capacity p s s :=
    ⟨S, WorkspaceFrame.refl _ _ _, Frame.refl _ _, Keeps.refl _ _⟩
  have step (a : State) (A : SquaresState g c capacity p s a) (lt : num a < c) :
      WP isa (VG.Impl.MillerRabin.X86.mulY name mont 6) a fun b =>
        SquaresState g c capacity p s b ∧ num b < c ∧
          num b * 2 ^ (64 * g.w) % c = num a * num a % c := by
    refine WP.mono (FastR2.square_ok verified noSp stack v A.ready.context length A.ready.modulus
      A.ready.caller odd lt) fun b ⟨Cb, Mb, caller, bound, congruence, O, K, F⟩ => ?_
    exact ⟨⟨⟨Cb, Mb, caller, A.ready.scratch.of_keeps K (by decide)⟩,
      A.workspace.trans O, A.memory.trans F, A.keeps.trans K⟩, bound, congruence⟩
  refine WP.mono (FastR2.squares_ok (VG.Impl.MillerRabin.X86.mulY name mont 6)
    (SquaresState g c capacity p s) num (VG.Proof.Bignum.coprime_pow2 odd _) step 5 (E := g.w) initial
    (by dsimp only [num]; rw [value]; exact Nat.mod_lt _ positive)
    (by dsimp only [num]; rw [value, Nat.mod_mod])) fun t ⟨T, lt, congruence⟩ => ?_
  refine ⟨T, ?_⟩
  rw [Nat.mod_eq_of_lt lt] at congruence
  exact congruence

end VG.Proof.RsaKeyGen.X86.PreparedR2
