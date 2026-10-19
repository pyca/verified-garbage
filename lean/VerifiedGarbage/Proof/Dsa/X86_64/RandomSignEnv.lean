module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEntry

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Framework.Omega

/-! Saved public arguments retained throughout randomized signing. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (88, stackArg s 0), (96, stackArg s 1),
    (104, stackArg s 2), (112, stackArg s 3), (120, stackArg s 4),
    (128, stackArg s 5), (136, stackArg s 6)]

def RandomSaved (s : State) (m : Mem) : Prop :=
  ∀ p ∈ randomSavedValues s, word m (randomBase s) p.1 = p.2

theorem random_saved_bound {s : State} {p : Nat × BitVec 64} (hp : p ∈ randomSavedValues s) :
    40 ≤ p.1 ∧ p.1 + 8 ≤ 144 := by
  simp only [randomSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

theorem RandomSaved.congr {s : State} {m m' : Mem} (h : RandomSaved s m)
    (hw : ∀ d, 40 ≤ d → d + 8 ≤ 144 → word m' (randomBase s) d = word m (randomBase s) d) : RandomSaved s m' :=
  fun p hp => (hw _ (random_saved_bound hp).1 (random_saved_bound hp).2).trans (h p hp)

theorem random_entry_stackWord (s : State) (j : Nat) :
    word s.mem (randomBase s) (256 + 8 * j) = stackArg s j := by
  unfold VG.Proof.Bignum.word
  rw [random_incoming_address]
  rfl

theorem random_saved_entry (s : State) :
    RandomSaved s (randomSlotsMem (randomBase s)
      (randomEntryHeaderMem (allocState Random.frameBytes s) (randomBase s)) RandomSign.incomingSlots) := by
  have hv := random_entry_values (allocState Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ randomSavedValues s, p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [randomSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [randomEntryValues, allocState, State.setReg, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2, random_entry_stackWord s 3,
        random_entry_stackWord s 4, random_entry_stackWord s 5, random_entry_stackWord s 6]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.X86_64
