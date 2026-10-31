module

import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.SlotTaint

/-!
# Public values through memory, in the PPC64LE slot taint analysis

A function that needs every register saves the callee-saved ones in its
working space and restores them from there. `VG.PPC64LE.slotTaint` keeps a
public register public through that round trip, when the working space is a
writable region whose base it knows, and forgets it when a secret may have
overwritten the slot in between.
-/

namespace VG.Test.PPC64LESlotTaint

open VG VG.PPC64LE

/-- `r29` public, `r5` the base of the first writable region (of at least 64
bytes). -/
def τ₀ : SlotTaint.T := SlotTaint.mk' [.r5, .r29] [64] [(.r5, 0)]

/-- Saves `r29` at `r5 + 16`, overwrites it with a secret, stores the secret
at `r5`, restores `r29` and loads through it. -/
def roundTrip : Prog isa :=
  .block [.store .d .r29 .r5 16, .load .d .r29 .r5 32, .store .d .r29 .r5 0, .load .d .r29 .r5 16,
    .load .d .r3 .r29 0]

theorem roundTrip_ct : ConstantTime isa (fun _ => True) (SlotTaint.Agree τ₀) roundTrip :=
  VG.Taint.constantTime (A := slotTaint) τ₀ (fun _ _ _ _ h => h) (by taint_decide)

/-- The taint after `is`, from `τ₀`. -/
def after (is : List Instr) : Option SlotTaint.T :=
  is.foldl (fun τ i => τ.bind (SlotTaint.step · i)) (some τ₀)

-- The round trip keeps `r29` public.
example : (after [.store .d .r29 .r5 16, .li .r29 0, .load .d .r29 .r5 16]).map
    (SlotTaint.pub · .r29) = some true := by decide

-- So does a pointer moved by `addi` and copied by `mr`.
example : (after [.addi .r6 .r5 8, .logic .or .r7 .r6 .r6, .store .d .r29 .r7 8, .li .r29 0,
    .load .d .r29 .r5 16]).map (SlotTaint.pub · .r29) = some true := by decide

-- A secret stored over the slot makes it secret.
example : (after [.store .d .r29 .r5 16, .load .d .r29 .r5 32, .store .w .r29 .r5 20,
    .load .d .r29 .r5 16]).map (SlotTaint.pub · .r29) = some false := by decide

-- So does a secret stored through a public register whose base is not known.
example : (after [.store .d .r29 .r5 16, .load .d .r29 .r5 32, .li .r6 0, .store .d .r29 .r6 0,
    .load .d .r29 .r5 16]).map (SlotTaint.pub · .r29) = some false := by decide

-- Writing the base register forgets where it points, but not where a copy points.
example : (after [.store .d .r29 .r5 16, .addi .r6 .r5 0, .li .r5 0, .load .d .r29 .r5 16]).map
    (SlotTaint.pub · .r29) = some false := by decide

example : (after [.store .d .r29 .r5 16, .addi .r6 .r5 0, .li .r5 0, .load .d .r29 .r6 16]).map
    (SlotTaint.pub · .r29) = some true := by decide

end VG.Test.PPC64LESlotTaint
