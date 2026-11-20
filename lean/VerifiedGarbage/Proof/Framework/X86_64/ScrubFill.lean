module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

/-!
# More on code generic over what it calls (x86-64)

Additions to `ScrubCall.lean` for the AEADs over GHASH and ChaCha20:
`calleeSide` of an implementation with a block appended (an implementation
that clears or zeroes something before it returns), `Fill.refl` (code that
the stub and the implementations share, such as interleaved loops a
variant names, relates to itself), and `fill_calls_refl`, `fill_calls` that
closes such shared code by `Fill.refl` (and `fill_calls_wide`, which does
the same breadth first, for large code).
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

/-- Code relates to itself: what the stub and the implementations share. -/
theorem Fill.refl {k : Nat} {n : String → Nat} : ∀ c : Prog isa, Fill k n c c
  | .block is => .block is
  | .seq a b => .seq (Fill.refl a) (Fill.refl b)
  | .ite c t e => .ite c (Fill.refl t) (Fill.refl e)
  | .loop b c => .loop c (Fill.refl b)
  | .call f b => .call f f (Fill.refl b)
  | .frame i b j => .frame i j (Fill.refl b)
  | .icall i f b x => .icall i f (Fill.refl b) (Fill.refl x)

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

/-- `fill_calls`, closing code the stub and the implementations share by
`Fill.refl` where it does not unfold to a constructor. -/
macro "fill_calls_refl" : tactic => `(tactic| repeat' (first
  | exact Fill.block _
  | exact Fill.hole _ _ (by assumption)
  | refine Fill.seq ?_ ?_
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | refine Fill.ifp ?_ ?_
  | refine Fill.if_pos ?_ (by assumption)
  | refine Fill.if_neg ?_ (by assumption)
  | exact Fill.refl _))

/-- `fill_calls_refl` breadth first, a step on every goal at a time, for
code too large for `repeat'`'s recursion, which follows one goal's subgoals
before the next goal's; without `Fill.if_pos` and `Fill.if_neg`, whose
`assumption` would compare every hypothesis with the condition, evaluating
the large ones. `Fill.seq` first: most of a function's code is sequences,
and each alternative that fails unfolds the goal again. -/
macro "fill_calls_wide" : tactic => `(tactic| repeat (any_goals (first
  | refine Fill.seq ?_ ?_
  | exact Fill.block _
  | exact Fill.hole _ _ (by assumption)
  | refine Fill.ite _ ?_ ?_
  | refine Fill.loop _ ?_
  | refine Fill.call _ _ ?_
  | refine Fill.frame _ _ ?_
  | refine Fill.icall _ _ ?_ ?_
  | refine Fill.ifp ?_ ?_
  | exact Fill.refl _)))

end VG.X86_64.Scrub
