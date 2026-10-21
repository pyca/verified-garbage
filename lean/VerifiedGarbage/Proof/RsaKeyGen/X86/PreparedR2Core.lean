module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Squares

/-! # The complete fast R² calculation with generic prepared Montgomery calls -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem core_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (bound : g.w ≤ 64)
    (odd : c % 2 = 1) (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.code (modulus g.w) (g.array 2) (g.array 6)
      (VG.Impl.MillerRabin.X86.mulY name mont 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 40]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t := by
  refine WP.seq (WP.mono (doubles_ready v S bound odd top) fun a ⟨A, value, O, K⟩ => ?_)
  refine WP.mono (squares_ready verified noSp stack v length A odd value) fun t ⟨T, V⟩ => ?_
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 40]) s.mem a.mem :=
    (workspaceGlobalFrame O (fun r mem => phase_fits v mem)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T.ready, V, F.trans T.memory, K.widen T.keeps⟩

end VG.Proof.RsaKeyGen.X86.PreparedR2
