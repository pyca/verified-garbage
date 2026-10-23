module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingWindowFront
import VerifiedGarbage.Proof.MillerRabin.X86.TimingStage
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.TimingEqual
import VerifiedGarbage.Proof.MillerRabin.X86.Window
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach

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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
