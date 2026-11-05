module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH key generation from the context on i686: the comb's traces

Runs of the comb with the same public width leak the same traces
(`comb_trace`). The row counters come from the context, so the taint
analysis cannot tell they are public: the runs are related row by row
(`relCT_countLoop`) with the counters' values, and each tooth's bit index,
`esi`, is public in its bit's check (`τAs`) because both runs hold the same
one.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)

/-! ## The taint checks -/

/-- A tooth's bit index. -/
abbrev toothHead (j : Nat) : List Instr :=
  [.mov .esi (.mem (sc iOff)), .alu .sub .esi (.imm 1)] ++ List.replicate j (.alu .add .esi (.mem (sc rowsOff)))

/-- A tooth's bit into the window word. -/
abbrev toothTail (j : Nat) : List Instr :=
  [.alu .and .eax (.imm 1)] ++ List.replicate j (.alu .add .eax (.reg .eax)) ++
    [.alu .or .eax (.mem (sc winOff)), .store (sc winOff) .eax]

theorem tooth_eq (j : Nat) : tooth j = .seq (.block (toothHead j)) (.seq bit (.block (toothTail j))) := rfl

/-- The bit, with its index public. -/
abbrev SCheck (p : Prog isa) : Prop := (VG.Taint.check taint τAs p (VG.Taint.hintOf taint τAs p)).isSome = true

theorem bit_check : SCheck Generate.bit := by dsimp only [SCheck]; taint_decide

theorem toothHead_check : ∀ j < 5, ACheck (.block (toothHead j)) := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [ACheck]; taint_decide)

theorem toothTail_check : ∀ j < 5, ACheck (.block (toothTail j)) := by
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [ACheck]; taint_decide)

theorem zero_check : ACheck (.block [.mov .eax (.imm 0), .store (sc winOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

theorem select_check : ACheck Generate.select := by dsimp only [ACheck]; taint_decide

theorem dec_check : ACheck (.block [.mov .eax (.mem (sc iOff)), .alu .sub .eax (.imm 1), .store (sc iOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

theorem init_check : ACheck (.block [.mov .ecx (.mem (VG.Impl.Bignum.X86.PublicRt.argAt 0 ctxArg)),
    .mov .eax (.mem (at_ .ecx 16)), .store (sc rowsOff) .eax, .store (sc iOff) .eax]) := by
  dsimp only [ACheck]; taint_decide

end VG.Proof.Ffdh.X86.Cached
