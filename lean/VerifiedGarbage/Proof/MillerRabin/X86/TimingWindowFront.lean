module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.RunView
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowState
import VerifiedGarbage.Proof.MillerRabin.X86.TimingStage
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.TimingScan
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
import VerifiedGarbage.Proof.MillerRabin.X86.FourSquares
import VerifiedGarbage.Proof.MillerRabin.X86.SquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.StageScan
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Window squaring and scanning retain each run's private canonical values -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

structure WindowSecret where
  c : Nat
  A : Nat → Nat
  V : Nat → BitVec 32
  flag : Bool

def WindowMath (σ : WindowSecret) : Prop :=
  σ.c % 2 = 1 ∧ σ.A aY < σ.c ∧ σ.A aTable = σ.A aOne ∧
    (∀ j < 16, σ.A (aTable + j) < σ.c) ∧ σ.V sFlag = BitVec.ofNat 32 σ.flag.toNat

def WindowStart (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A runArrays σ.V windowFields s ∧ WindowMath σ

def windowFourV (σ : WindowSecret) : Nat → BitVec 32 := setAt (setAt σ.V sThreshold 0#32) sSquares 4#32

def WindowFour (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p σ.A runArrays (windowFourV σ) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

def WindowSquared (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (squareValues σ.A σ.c g.w 0 4 σ.flag 4) runArrays
    (windowSquaresV σ.V σ.A σ.c g.w σ.flag) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

def WindowScanned (g : Geometry) (capacity : Nat) (p : BitVec 32) (σ : WindowSecret) (s : State) : Prop :=
  Stage g capacity σ.c p (windowScanA σ.V σ.A σ.c g.w σ.flag) (aX :: runArrays)
    (windowSquaresV σ.V σ.A σ.c g.w σ.flag) (sSquares :: sThreshold :: windowFields) s ∧ WindowMath σ

theorem windowFour_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (WindowStart g capacity p)) (.block fourSquares) (Two g (WindowFour g capacity p)) := by
  refine private_attach ((checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.1.2.2) (fun _ _ H => H))
    ?_ (fun _ _ H => H.1.data.context)
  intro σ s ⟨S, math⟩
  exact WP.mono (fourSquares_ok v S) fun _ R => ⟨R.1, math⟩

theorem windowSquares_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (WindowFour g capacity p)) (squareLoop name code) (Two g (WindowSquared g capacity p)) := by
  have known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ sSquares :: sThreshold :: windowFields := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> decide
  have guard {s : State} {σ : WindowSecret} (H : WindowFour g capacity p σ s) : SquareInput g capacity p 4 s :=
    H.1.squareInput H.2.1 H.2.2.1 runArrays_y runArrays_minus (by decide : 0 < 2 ^ 31)
      (by decide : 4 < 2 ^ 31) σ.flag known rfl rfl H.2.2.2.2.2
  refine private_attach ((squareLoop_relCT (p := p) verified noSp stack v length (by decide : 0 < 4)).mono
    (fun _ _ H => ⟨H.1, guard H.2.1.choose_spec, guard H.2.2.choose_spec⟩) (fun _ _ H => H.2.2))
    ?_ (fun _ _ H => H.1.data.context)
  intro σ s ⟨S, math⟩
  refine WP.mono (squareLoop_ok verified noSp stack v S length math.1 math.2.1 runArrays_y runArrays_minus
    (by decide : 0 < 4) (by decide : 4 < 2 ^ 31) (by decide : 0 < 2 ^ 31) σ.flag
    known (by decide) rfl rfl math.2.2.2.2) fun _ R => ⟨R.1, math⟩

theorem windowScan_relCT {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (Two g (WindowSquared g capacity p)) scan (Two g (WindowScanned g capacity p)) := by
  refine private_lift (scan_relCT v) ?_
  intro σ s ⟨S, math⟩
  exact WP.mono (S.scan v (fun _ digit => runArrays_power digit) (by decide) (by decide)) fun _ R => ⟨R.1, math⟩

end VG.Proof.MillerRabin.X86
