module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.MillerRabin.X86.DataMultiply
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.Word32
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame

/-! # A prepared Montgomery product composes with the next round stage -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.multiply {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp code) (stack : stackUse code ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (b : Nat) (right : Spec.Rsa.Mont.Operand b) (odd : c % 2 = 1) (rightLt : A b < c)
    (bKnown : b ∈ Js) (yKnown : aY ∈ Js) :
    WP isa (mulY name code b) s fun t =>
      Stage g capacity c p (setAt A aY (Word32.mm c g.w (A aY) (A b))) Js V Ds t ∧
      WorkspaceFrame g (montWrites g aY) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  refine WP.mono (S.data.multiply verified noSp stack v length S.modulus S.caller right odd
    rightLt bKnown yKnown S.noScratch) fun t ⟨D, M, C, O, K⟩ => ?_
  exact ⟨⟨D, M, C, S.noScratch⟩, O, K⟩

end VG.Proof.MillerRabin.X86
