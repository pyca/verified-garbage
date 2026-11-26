module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# More on code generic over what it calls (x86-64)

Additions to `ScrubCall.lean` for the AEADs over GHASH and ChaCha20:
`calleeSide` of an implementation with a block appended (an implementation
that clears or zeroes something before it returns), and `Fill.mono`.
-/

@[expose] public section

namespace VG.X86_64.Scrub

open VG.X86_64

/-- An implementation followed by a block meets `calleeSide` if both do. -/
theorem calleeSide_seqBlock {c : Prog isa} {b : List Instr} {k n : Nat}
    (h : calleeSide c k n = true)
    (hb : (Code.block b : Prog isa).allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    calleeSide (.seq c (.block b)) k n = true := by
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Code.x86_64Depth]; exact Nat.max_le.mpr ⟨h.1.1, Nat.zero_le _⟩
  · show c.allInstrs _ && (Code.block b : Prog isa).allInstrs _ = true
    rw [h.1.2, hb]; rfl
  · simpa [UpperLock.inames] using h.2

/-- `Fill` at a level, at any level above it. -/
theorem Fill.mono {k k' : Nat} {n : String → Nat} {a b : Prog isa} (hk : k ≤ k') (h : Fill k n a b) :
    Fill k' n a b := by
  induction h with
  | block is => exact .block is
  | hole f g hd => exact .hole f g (calleeSide_mono hk (Nat.le_refl _) hd)
  | seq _ _ iha ihb => exact .seq iha ihb
  | ite c _ _ iht ihe => exact .ite c iht ihe
  | loop c _ ih => exact .loop c ih
  | call f g _ ih => exact .call f g ih
  | frame i j _ ih => exact .frame i j ih
  | icall i f _ _ ihb ihx => exact .icall i f ihb ihx

end VG.X86_64.Scrub
