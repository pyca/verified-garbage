module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingWords
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares
public import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.MillerRabin.X86.PrepareRun
import VerifiedGarbage.Proof.MillerRabin.X86.WordLoop
import VerifiedGarbage.Proof.MillerRabin.X86.RoundMarker
import VerifiedGarbage.Proof.MillerRabin.X86.StageLastSquares
import VerifiedGarbage.Proof.MillerRabin.X86.TimingStage

/-! # Private arithmetic state through the complete round's timing composition -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen VG.Impl.MillerRabin.X86

structure CoreSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  k : Nat
  origin : Mem

def CoreMath (g : Geometry) (σ : CoreSecret) : Prop :=
  σ.c % 2 = 1 ∧ σ.A aX < σ.c ∧ σ.A aOne < σ.c ∧ σ.k < 64 ∧
    σ.origin.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ σ.k % 2 ^ 32) ∧
    σ.origin.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ σ.k / 2 ^ 32)

def CoreStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A initialArrays σ.V [] s ∧ CoreMath g σ ∧ s.mem = σ.origin

def runV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  setAt (setAt σ.V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32

def CoreRun (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (runValues σ.A σ.c g.w) runArrays (runV g σ) wordFields s ∧
    CoreMath g σ ∧ WorkspaceFrame g (roundWrites g) σ.origin s.mem

def endA (g : Geometry) (σ : CoreSecret) : Nat → Nat :=
  exponentValues (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words

def endV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  exponentCounters (runV g σ) (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words

def endFlag (g : Geometry) (σ : CoreSecret) : Bool :=
  (exponentState (runValues σ.A σ.c g.w) σ.c g.w g.words false g.words).2

def CoreWords (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (endA g σ) runArrays (endV g σ) wordFields s ∧
    CoreMath g σ ∧ WorkspaceFrame g (roundWrites g) σ.origin s.mem

def finalV (g : Geometry) (σ : CoreSecret) : Nat → BitVec 32 :=
  setAt (setAt (endV g σ) sThreshold (BitVec.ofNat 32 (4 - sigOf σ.k))) sSquares 3#32

def CoreFinal (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : CoreSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (endA g σ) runArrays (finalV g σ) ([sThreshold, sSquares] ++ wordFields) s ∧ CoreMath g σ

theorem CoreStart.prepare {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp code) (stack : stackUse code ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreStart g capacity p σ s) (length : g.L = 8 * capacity) :
    WP isa (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) s (CoreRun g capacity p σ) := by
  refine WP.mono (prepareRun_ok verified noSp stack v H.1 length H.2.1.1 H.2.1.2.1) fun _ R => ?_
  exact ⟨R.1, H.2.1, H.2.2 ▸ R.2.1⟩

theorem CoreMath.run_window {g : Geometry} {σ : CoreSecret} (H : CoreMath g σ) :
    WindowMath ⟨σ.c, runValues σ.A σ.c g.w, runV g σ, false⟩ := by
  refine ⟨H.1, ?_, ?_, ?_, rfl⟩
  · change runValues σ.A σ.c g.w aY < σ.c
    rw [runValues_y]; exact H.2.2.1
  · change runValues σ.A σ.c g.w aTable = runValues σ.A σ.c g.w aOne
    rw [← runValues_identity, runValues_y, runValues_one]
  · intro j digit
    change runValues σ.A σ.c g.w (aTable + j) < σ.c
    rw [runValues_power σ.A σ.c g.w digit]
    exact Word32.tp_lt (by have := H.2.1; omega : 0 < σ.c) H.2.1 H.2.2.1 j

theorem CoreRun.wordInput {g : Geometry} {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreRun g capacity p σ s) : WordInput g capacity p g.words s :=
  ⟨⟨σ.c, runValues σ.A σ.c g.w, runV g σ, false⟩, H.1, H.2.1.run_window, rfl, Nat.le_refl _⟩

theorem CoreRun.words {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp code) (stack : stackUse code ≤ 16)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreRun g capacity p σ s) (length : g.L = 8 * capacity) :
    WP isa (.loop (wordStep name code) .ne) s (CoreWords g capacity p σ) := by
  have math := H.2.1.run_window
  refine WP.mono (wordLoop_ok verified noSp stack v H.1 length math.1 math.2.1 runArrays_y runArrays_one
    runArrays_minus runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit) math.2.2.1 math.2.2.2.1
    false rfl rfl) fun _ R => ⟨R.1, H.2.1, H.2.2.trans R.2.1⟩

theorem CoreWords.marker {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32}
    {σ : CoreSecret} {s : State} (H : CoreWords g capacity p σ s) :
    WP isa (.block lastSquares) s (CoreFinal g capacity p σ) := by
  have lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ σ.k % 2 ^ 32) := by
    have R := roundFrame_marker32 v H.2.2 (extra := 0) (Or.inl rfl)
    rw [Nat.add_zero] at R
    exact R.trans H.2.1.2.2.2.2.1
  have hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ σ.k / 2 ^ 32) :=
    (roundFrame_marker32 v H.2.2 (extra := 4) (Or.inr rfl)).trans H.2.1.2.2.2.2.2
  exact WP.mono (H.1.lastSquares v H.2.1.2.2.2.1 lo hi) fun _ R => ⟨R.1, H.2.1⟩

theorem CoreFinal.squareInput {g : Geometry} {capacity : Nat} {p : BitVec 32} {σ : CoreSecret} {s : State}
    (H : CoreFinal g capacity p σ s) : SquareInput g capacity p 3 s := by
  have lt : endA g σ aY < σ.c := by
    rw [endA, exponentValues, setAt_self]
    exact exponentState_lt _ (by have := H.2.2.1; omega : 0 < σ.c) g.w g.words false
      (by rw [runValues_y]; exact H.2.2.2.1) g.words
  refine H.1.squareInput H.2.1 lt runArrays_y runArrays_minus
    (by omega : 4 - sigOf σ.k < 2 ^ 31) (by decide : 3 < 2 ^ 31) (endFlag g σ) ?_ rfl rfl rfl
  intro d mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
