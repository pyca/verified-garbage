module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEntry

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
import VerifiedGarbage.Proof.Framework.Omega

/-! Saved public arguments retained throughout randomized signing. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomSavedValues (s : State) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (96, s.gpr .x7),
    (104, stackArg s 0), (112, stackArg s 1), (120, stackArg s 2),
    (128, stackArg s 3), (136, stackArg s 4)]

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
      (randomEntryHeaderMem (allocated Random.frameBytes s) (randomBase s)) RandomSign.incomingSlots) := by
  have hv := random_entry_values (allocated Random.frameBytes s) (randomBase s)
  have hs : ∀ p ∈ randomSavedValues s, p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s) := by
    intro p hp
    simp only [randomSavedValues, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [randomEntryValues, allocated, random_entry_stackWord s 0,
        random_entry_stackWord s 1, random_entry_stackWord s 2, random_entry_stackWord s 3,
        random_entry_stackWord s 4]
  exact fun p hp => hv p (hs p hp)

end VG.Proof.Dsa.AArch64
