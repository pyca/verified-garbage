module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Squares

/-! # The complete fast R² calculation with generic prepared Montgomery calls -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def coreRanges (g : Geometry) : List (Nat × Nat) := phaseRanges g ++ montWrites g 6

theorem core_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (bound : g.w ≤ 64)
    (odd : c % 2 = 1) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) (top : 2 ^ e ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.codeAt (modulus g.w) e (g.array 2) (g.array 6)
      (VG.Impl.MillerRabin.X86.mulY name mont 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t ∧ WorkspaceFrame g (coreRanges g) s.mem t.mem := by
  refine WP.seq (WP.mono (doublesAt_ready v S bound odd positive eLt top) fun a ⟨A, value, O, K⟩ => ?_)
  refine WP.mono (squares_ready verified noSp stack v length A odd value) fun t ⟨T, V⟩ => ?_
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame O (fun r mem => phase_fits v mem)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨T.ready, V, F.trans T.memory, K.widen T.keeps,
    ((WorkspaceFrame.of_outs S.scratch.nowrap O).mono (fun r mem => List.mem_append_left _ mem)).trans
      (T.workspace.mono (fun r mem => List.mem_append_right _ mem))⟩

theorem core_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (bound : g.w ≤ 64)
    (odd : c % 2 = 1) (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.FastR2.code (modulus g.w) (g.array 2) (g.array 6)
      (VG.Impl.MillerRabin.X86.mulY name mont 6)) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t ∧ WorkspaceFrame g (coreRanges g) s.mem t.mem :=
  core_okAt verified noSp stack v length S bound odd (e := 64 * g.w - 1)
    (by have := v.minWidth; omega) (by have := v.minWidth; omega) top

end VG.Proof.RsaKeyGen.X86.PreparedR2
