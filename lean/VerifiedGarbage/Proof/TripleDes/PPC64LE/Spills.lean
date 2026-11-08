module

public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Feistel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# The scratch buffer of the block functions

The block saves `r14`–`r28` in slots 0–14 of the scratch buffer at `r5` and
stores the round function's words of constants in slots 15–61 (`ConstsAt`).
The rounds write no memory, so their frame is the two slots left
(`spillRegion`), which keeps the constants and the saved registers.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

/-- The scratch buffer's 64 words, writable. -/
def scratchCfg : Cfg := { base := .r5, slots := 64, ext := .r5, exts := 0 }

/-- The slots the rounds may write: the two after the constants. -/
def spillRegion (s : State) : Region := ⟨s.gpr .r5 + BitVec.ofNat 64 496, 16⟩

/-- Slots 15–61 hold the round function's words of constants. -/
def ConstsAt (s : State) : Prop :=
  ∀ c < 47, s.mem.readW (wordAddr (s.gpr .r5) (15 + c)) 64 = roundConsts.getD c 0

theorem ConstsAt.of_frame {s t : State} (h : ConstsAt s) (hb : t.gpr .r5 = s.gpr .r5)
    (hf : Frame [spillRegion s] s.mem t.mem) : ConstsAt t := by
  intro c hc
  rw [hb, ← h c hc]
  exact hf.readW (r := ⟨wordAddr (s.gpr .r5) (15 + c), 8⟩) (Region.contains_self _ _)
    (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)) (by decide)

theorem ConstsAt.congr {s t : State} (h : ConstsAt s) (hb : t.gpr .r5 = s.gpr .r5)
    (hm : t.mem = s.mem) : ConstsAt t :=
  h.of_frame hb (by rw [hm]; exact Frame.refl _ _)

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

end VG.Proof.TripleDes.PPC64LE
