module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingWindow
import VerifiedGarbage.Proof.MillerRabin.X86.TimingLoadWord
import VerifiedGarbage.Proof.MillerRabin.X86.TimingAttach
import VerifiedGarbage.Proof.MillerRabin.X86.WordStep
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.Context

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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
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
