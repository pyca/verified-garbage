module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEntry
import VerifiedGarbage.Proof.Framework.Omega

/-! Values of the saved arguments and retry state after wrapper entry. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def randomEntryValues (s : State) (B : Addr) : List (Nat × BitVec 64) :=
  [(40, s.gpr .rdi), (48, s.gpr .rsi), (56, s.gpr .rdx), (64, s.gpr .rcx),
    (72, s.gpr .r8), (80, s.gpr .r9), (168, s.gpr .rcx + s.gpr .r9), (144, 0), (152, 8),
    (88, word s.mem B 256), (96, word s.mem B 264), (104, word s.mem B 272),
    (112, word s.mem B 280), (120, word s.mem B 288), (128, word s.mem B 296), (136, word s.mem B 304)]

theorem random_entry_values (s : State) (B : Addr) :
    ∀ p ∈ randomEntryValues s B,
      word (randomSlotsMem B (randomEntryHeaderMem s B) RandomSign.incomingSlots) B p.1 = p.2 := by
  intro p hp
  simp only [randomEntryValues, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [RandomSign.incomingSlots, randomSlotsMem, randomEntryHeaderMem,
      Random.oOut, Random.oOutLen, Random.oUsedPtr, Random.oKey, Random.oKeyLen, Random.oPLen,
      Random.oQ, Random.oUsed, Random.oAttempts, Random.oQLen, Random.oDigest, Random.oDigestLen,
      Random.oRand, Random.oRandLen, Random.oScratch, Random.oScratchLen] <;>
    simp (disch := omega) only [word_writeW_self, random_word_write_other]

end VG.Proof.Dsa.X86_64
