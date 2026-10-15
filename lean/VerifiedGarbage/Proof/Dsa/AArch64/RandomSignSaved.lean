module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEntry
import VerifiedGarbage.Proof.Framework.Omega

/-! Values of the saved arguments and retry state after wrapper entry. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def randomEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .x0), (48, s.gpr .x1), (56, s.gpr .x2), (64, s.gpr .x3),
    (72, s.gpr .x4), (80, s.gpr .x5), (88, s.gpr .x6), (96, s.gpr .x7), (232, s.gpr .x30),
    (168, s.gpr .x3 + s.gpr .x5), (144, 0), (152, 8),
    (104, word s.mem B 256), (112, word s.mem B 264), (120, word s.mem B 272),
    (128, word s.mem B 280), (136, word s.mem B 288)]

theorem random_entry_values (s : State) (B : Addr) :
    ∀ p ∈ randomEntryValues s B,
      word (randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots) B p.1 = p.2 := by
  intro p hp
  simp only [randomEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [RandomSign.incomingSlots, randomSlotsMem, randomEntryHeaderMem,
      RandomSign.oLink, Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oAttempts, Random.oQLen, Random.oDigest, Random.oDigestLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := omega) only [word_writeW_self, random_word_write_other]

end VG.Proof.Dsa.AArch64
