module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.MontFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.FastR2Square
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.TCB.X86.State

/-! ### `RsaKeyGen.X86.PreparedR2Core`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.PreparedR2Squares`, which this module and modules that import it used -/

section

/-! # Six prepared Montgomery calls complete the short R² setup -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FastR2Squares.lean`, which only this module imported.
section

/-! # The six squarings in fast R² setup, generic over a verified multiplier -/

section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Impl.Rsa.X86.Keys

theorem squares_ok (square : Prog isa) (P : State → Prop) (value : State → Nat) {m R : Nat}
    (coprime : Nat.Coprime R m)
    (step : ∀ s, P s → value s < m → WP isa square s fun t =>
      P t ∧ value t < m ∧ value t * R % m = value s * value s % m)
    (count : Nat) {s : State} {E : Nat} (S : P s) (lt : value s < m)
    (congruent : value s % m = 2 ^ E * R % m) :
    WP isa (seqs (List.replicate (count + 1) square)) s fun t =>
      P t ∧ value t < m ∧ value t % m = 2 ^ (2 ^ (count + 1) * E) * R % m := by
  induction count generalizing s E with
  | zero =>
    exact WP.mono (step s S lt) fun t ⟨T, bound, mul⟩ =>
      ⟨T, bound, VG.Proof.Bignum.mont_sq coprime congruent mul⟩
  | succ count ih =>
    change WP isa (.seq square (seqs (List.replicate (count + 1) square))) s _
    refine WP.seq (WP.mono (step s S lt) fun a ⟨A, bound, mul⟩ => ?_)
    refine WP.mono (ih A bound (VG.Proof.Bignum.mont_sq coprime congruent mul))
      fun t ⟨T, bound, V⟩ => ⟨T, bound, ?_⟩
    rw [V, show 2 ^ (count + 1 + 1) = 2 ^ (count + 1) * 2 from rfl, Nat.mul_assoc]

end VG.Proof.RsaKeyGen.X86.FastR2
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

structure SquaresState (g : Geometry) (c capacity : Nat) (p : BitVec 32) (s t : State) : Prop where
  ready : Ready g c capacity p t
  workspace : WorkspaceFrame g (montWrites g 6) s.mem t.mem
  memory : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx] s t

theorem squares_ready {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (odd : c % 2 = 1)
    (value : val32 s.mem g.W (g.array 6) g.words = 2 ^ g.w * 2 ^ (64 * g.w) % c) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 (VG.Impl.MillerRabin.X86.mulY name mont 6))) s fun t =>
      SquaresState g c capacity p s t ∧
      val32 t.mem g.W (g.array 6) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c := by
  let num : State → Nat := fun t => val32 t.mem g.W (g.array 6) g.words
  have positive : 0 < c := by omega_using [odd]
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

end

end

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

end VG.Proof.RsaKeyGen.X86.PreparedR2

end

end

/-! # Retain fast R² in its final prepared Miller–Rabin array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def ranges (g : Geometry) : List (Nat × Nat) := coreRanges g ++ [(g.array 4, 4 * g.words)]

theorem code_okAt {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (bound : g.w ≤ 64)
    (odd : c % 2 = 1) {e : Nat} (positive : 1 ≤ e) (eLt : e < 64 * g.w) (top : 2 ^ e ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt e g.w name mont) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t ∧ WorkspaceFrame g (ranges g) s.mem t.mem := by
  unfold VG.Impl.RsaKeyGen.X86.PreparedR2.codeAt
  rw [Prepared.slot_eq, Prepared.slot_eq]
  refine WP.seq (WP.mono (core_okAt verified noSp stack v length S bound odd positive eLt top)
    fun a ⟨A, value, F, K, W⟩ => ?_)
  refine WP.mono (copy_ok v A.context 4 6 (by decide) (by decide)) fun t ⟨copy, O, Kt, C⟩ => ?_
  have Ot := WorkspaceFrame.of_outs A.scratch.nowrap (Outs.of_outside O (List.mem_singleton_self _))
  have Mt := A.modulus.keep v Ot
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 4; omega))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide)))
  have fit : g.array 4 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have caller := A.caller.keepOuts Kt (by decide) (Outs.of_outside O (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) a.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside O (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨⟨C, Mt, caller, A.scratch.of_keeps Kt (by decide)⟩,
    copy.trans value, F.trans Ft, K.widen Kt,
    (W.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Ot.mono (fun r mem => List.mem_append_right _ mem))⟩

end VG.Proof.RsaKeyGen.X86.PreparedR2
