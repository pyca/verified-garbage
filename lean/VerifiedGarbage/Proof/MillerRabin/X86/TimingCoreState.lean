module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquares
public import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingPrivate
public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.RunView
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowState
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context

import VerifiedGarbage.Proof.MillerRabin.X86.PrepareRun
import VerifiedGarbage.Proof.MillerRabin.X86.WordLoop
import VerifiedGarbage.Proof.MillerRabin.X86.RoundMarker
import VerifiedGarbage.Proof.MillerRabin.X86.StageLastSquares
import VerifiedGarbage.Proof.MillerRabin.X86.TimingStage
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSelect
import VerifiedGarbage.Proof.MillerRabin.X86.Mask
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.X86.TimingSquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
import VerifiedGarbage.Proof.MillerRabin.X86.FourSquares
import VerifiedGarbage.Proof.MillerRabin.X86.SquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.StageScan
import VerifiedGarbage.Proof.MillerRabin.X86.TimingEqual
import VerifiedGarbage.Proof.MillerRabin.X86.Window
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.Pointer
import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MillerRabin.X86.WordStep
/-! # Private arithmetic state through the complete round's timing composition -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingScan.lean`, which only this module imported.
section

/-! # All sixteen powers are scanned independently of the secret digit -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem maskIndex_pair_relCT {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (Pair g [.edi]) (.block (maskIndex j)) fun s t =>
      Pair g [.edi] s t ∧ masked g s ∧ masked g t := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := maskIndex_relCT j _ _ _ _ _ _ H.2.2 E G
  obtain ⟨Mu, _, _, Cu⟩ := wp_result (maskIndex_ok v H.1 j digit) E
  obtain ⟨Mz, _, _, Cz⟩ := wp_result (maskIndex_ok v H.2.1 j digit) G
  refine ⟨trace, ⟨Cu, Cz, A⟩, ?_, ?_⟩
  · refine ⟨decide ((s.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mu
  · refine ⟨decide ((t.mem.readW (off g.W sValue) 32 >>> 28).toNat = j), ?_⟩
    simpa using Mz

theorem scanFrom_relCT {g : Geometry} (v : g.Valid) (n : Nat) :
    ∀ j, j + n ≤ 16 → RelCT isa (Pair g [.edi]) (scanFrom j n) (Pair g [.edi]) := by
  induction n with
  | zero => intro j _; exact RelCT.block_nil (fun _ _ H => H)
  | succ n ih =>
    intro j bound
    exact RelCT.seq (maskIndex_pair_relCT v j (by omega))
      (RelCT.seq (selectEntry_relCT v j (by omega)) (ih (j + 1) (by omega)))

theorem scan_relCT {g : Geometry} (v : g.Valid) : RelCT isa (Pair g [.edi]) scan (Pair g [.edi]) :=
  RelCT.seq (copy_relCT v aX aTable (by decide) (by decide)) (scanFrom_relCT v 15 1 (by decide))

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWindowFront.lean`, which only this module imported.
section

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
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
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
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWindow.lean`, which only this module imported.
section

/-! # A complete four-bit window has no secret-dependent address or branch -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86

theorem WindowScanned.mulInput {g : Geometry} {capacity : Nat} {p : BitVec 32}
    {σ : WindowSecret} {s : State} (H : WindowScanned g capacity p σ s) : MulInput g capacity aX p s := by
  refine H.1.mulInput H.2.1 (List.mem_cons_self ..) ?_
  rw [windowScanA, setAt_self, squareValues,
    setAt_other _ _ (by unfold aTable aY; omega : aTable + windowDigit σ.V ≠ aY)]
  exact H.2.2.2.2.1 (windowDigit σ.V) (digit_lt _)

theorem window_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (length : g.L = 8 * capacity) :
    RelCT isa (Two g (WindowStart g capacity p)) (window name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (.block fourSquares) (.seq (squareLoop name code) (.seq scan
    (.seq (mulY name code aX) (.seq (equal sEq1 aY aOne) (.seq (equal sEq2 aY aMinusOne) (.block windowEnd))))))) _
  refine RelCT.seq (windowFour_relCT v) (RelCT.seq (windowSquares_relCT verified noSp stack v length)
    (RelCT.seq (windowScan_relCT v) ?_))
  refine RelCT.seq ((mulY_relCT (p := p) verified noSp stack v length
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide)).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec.mulInput, H.2.2.choose_spec.mulInput⟩) (fun _ _ H => H)) ?_
  refine RelCT.seq (equal_relCT v sEq1 aY aOne (by unfold scratchWord sEq1; simp) (by decide) (by decide)) ?_
  exact RelCT.seq (equal_relCT v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp) (by decide) (by decide))
    (windowEnd_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H))

def WindowInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ σ, WindowStart g capacity p σ s ∧ σ.V sWindows = BitVec.ofNat 32 q ∧ q < 2 ^ 32

theorem WindowInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WindowInput g capacity p q s) : Context g s := by
  obtain ⟨_, ⟨S, _⟩, _⟩ := I
  exact S.data.context

theorem WindowInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WindowInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (window name code) s fun t => WindowInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨σ, ⟨S, odd, lt, one, tableLt, flag⟩, count, bound⟩ := I
  refine WP.mono (window_ok verified noSp stack v S length odd lt runArrays_y runArrays_one runArrays_minus
    runArrays_notX (fun _ digit => runArrays_power digit) one tableLt positive bound σ.flag flag count)
    fun t ⟨St, Z, _, _⟩ => ?_
  let A := setAt σ.A aY (windowResult σ.V σ.A σ.c g.w σ.flag).1
  let V := windowCounters σ.V σ.A σ.c g.w q σ.flag
  let F := (windowResult σ.V σ.A σ.c g.w σ.flag).2
  refine ⟨⟨⟨σ.c, A, V, F⟩, ⟨St, odd, ?_, ?_, ?_, rfl⟩, rfl, by omega⟩, Z⟩
  · change (windowResult σ.V σ.A σ.c g.w σ.flag).1 < σ.c
    exact Word32.mm_lt (by omega : 0 < σ.c)
  · exact one
  · intro j digit
    change setAt σ.A aY _ (aTable + j) < σ.c
    rw [setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j digit

theorem windowLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WindowInput g capacity p q s ∧ WindowInput g capacity p q t)
      (.loop (window name code) .ne) (Pair g [.edi]) := by
  refine (private_count_loop (F := fun q (_ : Unit) s => WindowInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  refine (window_trace (p := p) verified noSp stack v length).mono ?_ (fun _ _ H => H)
  intro s t ⟨P, ⟨_, σ, S, _⟩, ⟨_, ρ, T, _⟩⟩
  exact ⟨P, ⟨σ, S⟩, ⟨ρ, T⟩⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/WordPointer.lean`, which only this module imported.
section

/-! # Address the exponent word using the public native-word countdown -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def wordPointer : List Instr :=
  ptr .ebp aExponent ++ [.mov .eax (.mem (slot sWords)), .alu .sub .eax (.imm 1),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .ebp (.reg .eax)]

theorem wordPointer_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (q : Nat) (positive : 0 < q) (bound : q ≤ g.words)
    (count : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q) :
    WP isa (.block wordPointer) s fun t =>
      PtrAt t g.W .ebp (g.array aExponent + 4 * (q - 1)) ∧ t.mem = s.mem ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have header := v.headerFit
  have expFit := v.arrayFit (j := aExponent) (by decide)
  have small : q ≤ 256 := by have := v.maxWidth; unfold Geometry.words at bound; omega
  unfold wordPointer
  refine WP.block_append (WP.mono (C.ptr v aExponent (by decide) .ebp (by decide) (by decide))
    fun u ⟨P, Mu, Ku⟩ => ?_)
  have Cu := C.keepMem Ku (by decide) Mu
  refine wp_movS (Cu.readScalar sWords (by unfold sWords; omega)) fun a A _ => ?_
  refine wp_subS rfl fun b B _ => wp_addS rfl fun c D _ => wp_addS rfl fun d H _ => ?_
  have Kd : Keeps [.eax, .edx, .ebp] s d :=
    ((((Ku.mono (by decide)).widen A.keeps).widen B.keeps).widen D.keeps).widen H.keeps
  have Md : d.mem = s.mem := H.mem.trans (D.mem.trans (B.mem.trans (A.mem.trans Mu)))
  have bp : PtrAt d g.W .ebp (g.array aExponent) := by
    rw [PtrAt, H.other .ebp (by decide), D.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide)]; exact P
  have indexVal : (d.gpr .eax).toNat = 4 * (q - 1) := by
    rw [H.gpr, D.gpr, B.gpr, A.gpr, Mu, count]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    change (((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 +
      ((2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32 + (2 ^ 32 - 1 + q % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
    omega
  refine wp_addS rfl fun e I _ => ?_
  have Ke : Keeps [.eax, .edx, .ebp] s e := Kd.widen I.keeps
  have Me : e.mem = s.mem := I.mem.trans Md
  have be : PtrAt e g.W .ebp (g.array aExponent + 4 * (q - 1)) := by
    rw [PtrAt, I.gpr, ptr_add bp, indexVal]
  exact WP.block_nil ⟨be, Me, Ke⟩

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingLoadWord.lean`, which only this module imported.
section

/-! # Exponent loads use the public word counter, even for a secret exponent -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem wordPointer_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold wordPointer
  refine RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp aExponent (by decide) (by decide) [.edi] (by decide)) ?_)
  exact (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi]) (by kernel_rfl) (by kernel_rfl)).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem wordPointer_relCT {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi, .ebp])) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, A⟩ := wordPointer_trace v _ _ _ _ _ _ H E G
  obtain ⟨Pu, _, _⟩ := wp_result (wordPointer_ok v H.1 q positive bound S) E
  obtain ⟨Pz, _, _⟩ := wp_result (wordPointer_ok v H.2.1 q positive bound T) G
  refine ⟨trace, round_add_regs (round_forget A) ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact round_regs A (by decide)
  · exact ptr_agree Pu Pz

theorem loadWord_trace {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block loadWord) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.block (wordPointer ++ [.mov .eax (.mem (at_ .ebp 0)), .store (slot sValue) .eax,
    .mov .eax (.imm 8), .store (slot sWindows) .eax])) _
  exact RelCT.block_append (RelCT.seq (wordPointer_relCT v q positive bound)
    (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp, .eax]) (by kernel_rfl) (by kernel_rfl)))

end VG.Proof.MillerRabin.X86
end

end

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/TimingWords.lean`, which only this module imported.
section

/-! # Exponent words execute eight windows and decrement a public counter -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def WordInput (g : Geometry) (capacity : Nat) (p : BitVec 32) (q : Nat) (s : State) : Prop :=
  ∃ σ : WindowSecret, Stage g capacity σ.c p σ.A runArrays σ.V wordFields s ∧ WindowMath σ ∧
    σ.V sWords = BitVec.ofNat 32 q ∧ q ≤ g.words

theorem WordInput.context {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : Context g s := by
  obtain ⟨_, S, _⟩ := I
  exact S.data.context

theorem WordInput.count {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q := by
  obtain ⟨σ, S, _, count, _⟩ := I
  exact (S.data.slotValues sWords (by decide)).2.trans count

theorem WordInput.bound {g : Geometry} {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) : q ≤ g.words := by
  obtain ⟨_, _, _, _, bound⟩ := I
  exact bound

theorem WordInput.load {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) (positive : 0 < q) :
    WP isa (.block loadWord) s (WindowInput g capacity p 8) := by
  obtain ⟨σ, S, math, count, bound⟩ := I
  let x := s.mem.readW (off g.W (g.array aExponent + 4 * (q - 1))) 32
  refine WP.mono (S.loadWord v q positive bound count x rfl) fun t ⟨St, _, _⟩ => ?_
  refine ⟨⟨σ.c, σ.A, setAt (setAt σ.V sValue x) sWindows 8#32, σ.flag⟩,
    ⟨St, math.1, math.2.1, math.2.2.1, math.2.2.2.1, math.2.2.2.2⟩, rfl, by decide⟩

theorem wordStep_trace {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WordInput g capacity p q s ∧ WordInput g capacity p q t)
      (wordStep name code) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.seq (.block loadWord) (.seq (.loop (window name code) .ne) (.block wordEnd))) _
  refine RelCT.seq (R := fun s t => Pair g [.edi] s t ∧ WindowInput g capacity p 8 s ∧ WindowInput g capacity p 8 t) ?_
    (RelCT.seq (windowLoop_relCT verified noSp stack v length (by decide : 0 < 8)) ?_)
  · intro s t tr ur u z ⟨H, S, T⟩ E G
    obtain ⟨trace, A⟩ := loadWord_trace v q positive S.bound _ _ _ _ _ _ ⟨H, S.count, T.count⟩ E G
    have U := wp_result (S.load v positive) E
    have Z := wp_result (T.load v positive) G
    exact ⟨trace, ⟨U.context, Z.context, A⟩, U, Z⟩
  · exact (checkedBlockInvariant rfl rfl).mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem WordInput.step {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32} {s : State}
    (I : WordInput g capacity p q s) (length : g.L = 8 * capacity) (positive : 0 < q) :
    WP isa (wordStep name code) s fun t => WordInput g capacity p (q - 1) t ∧ t.zf = some (decide (q = 1)) := by
  obtain ⟨σ, S, ⟨odd, lt, one, tableLt, flag⟩, count, bound⟩ := I
  refine WP.mono (wordStep_ok verified noSp stack v S length odd lt runArrays_y runArrays_one runArrays_minus
    runArrays_exp runArrays_notX (fun _ digit => runArrays_power digit) one tableLt positive bound σ.flag flag count)
    fun t ⟨St, Z, _, _⟩ => ?_
  let x := exponentWord (σ.A aExponent) (q - 1)
  let A := wordValues σ.A σ.c g.w x σ.flag 8
  let V := wordEndSlots σ.V σ.A σ.c g.w x σ.flag q
  let F := (wordState σ.A σ.c g.w x σ.flag 8).2
  refine ⟨⟨⟨σ.c, A, V, F⟩, St, ⟨odd, ?_, ?_, ?_, rfl⟩, rfl, by omega⟩, Z⟩
  · change (wordState σ.A σ.c g.w x σ.flag 8).1 < σ.c
    exact wordState_lt σ.A (by omega : 0 < σ.c) g.w x σ.flag lt 8
  · exact one
  · intro j digit
    change setAt σ.A aY _ (aTable + j) < σ.c
    rw [setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j digit

theorem wordLoop_relCT {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity q : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (positive : 0 < q) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ WordInput g capacity p q s ∧ WordInput g capacity p q t)
      (.loop (wordStep name code) .ne) (Pair g [.edi]) := by
  refine (private_count_loop (F := fun q (_ : Unit) s => WordInput g capacity p q s) ?_ q positive).mono
    (fun _ _ H => ⟨H.1, ⟨(), H.2.1⟩, ⟨(), H.2.2⟩⟩) (fun _ _ H => H.1)
  intro n positive
  refine private_control ?_ (fun _ s I => I.step verified noSp stack v length positive)
    (fun _ _ I => I.context) positive
  exact (wordStep_trace (p := p) verified noSp stack v length positive).mono
    (fun _ _ H => ⟨H.1, H.2.1.choose_spec, H.2.2.choose_spec⟩) (fun _ _ H => H)

end VG.Proof.MillerRabin.X86
end

end

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
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
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
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
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
