module

public import VerifiedGarbage.Proof.Modes.Arm.Wide
public import VerifiedGarbage.Impl.Modes.Arm.Wide
import VerifiedGarbage.Proof.Modes.Arm.Ctr
import VerifiedGarbage.Proof.Modes.Arm.CbcChained
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# CTR, CBC decryption and CFB decryption a group at a time on ARMv7

`ctrW`, `cbcDecW` and `cfbDecW` (`Impl/Modes/Arm/Wide.lean`), in groups of
8, 4 and 2 blocks of 16 bytes (`wideLevels`, with the buffer of `wideBuf`
bytes), are what `Core.seqW` needs of a wide mode (`LevelOk`): a group
leaves the data, the chaining block and the spare block as that many steps
of `ctr`, `cbcDecChained` or `cfbDec` do (`WideSim`), which evaluating both
on any blocks shows.
-/

@[expose] public section

namespace VG.Proof.Modes.Arm

open VG VG.Arm VG.Impl.Modes.Arm

theorem ctrW_sim : ∀ lg ∈ wideLevels, WideSim ctr ctrW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, ctrW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, ctr, Blks.set, Blks.get,
      List.range_succ]

theorem cbcDecW_sim : ∀ lg ∈ wideLevels, WideSim cbcDecChained cbcDecW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, cbcDecW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, cbcDecChained, cbcDec,
      Blks.set, Blks.get, List.range_succ]

theorem cfbDecW_sim : ∀ lg ∈ wideLevels, WideSim cfbDec cfbDecW (2 ^ lg) := by
  intro lg h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> constructor <;> intro ciph b <;>
    simp [wstep, cfbDecW, wrunOps, wrunOp, wset, wciph, runSeq, stepOf, runOps, runOp, cfbDec, Blks.set, Blks.get,
      List.range_succ]

/-- The levels of a wide mode whose groups compute the steps of `M`, on a
core of 16-byte blocks. -/
theorem levels_of_sim {c : Core} (hbs : c.bs = 16) {M : Mode} {wm : WMode} (hb : M.byte = false)
    (hpre : ∀ lg ∈ wideLevels, (wm.pre (2 ^ lg)).all (wopOk 16 (2 ^ lg)) = true)
    (hpost : ∀ lg ∈ wideLevels, (wm.post (2 ^ lg)).all (wopOk 16 (2 ^ lg)) = true)
    (hsim : ∀ lg ∈ wideLevels, WideSim M wm (2 ^ lg)) : ∀ lg ∈ wideLevels, LevelOk c M wm wideBuf lg := by
  intro lg h
  have h' := h
  simp only [wideLevels, List.mem_cons, List.not_mem_nil, or_false] at h'
  refine ⟨⟨?_, hb, by rw [hbs]; exact hpre lg h, by rw [hbs]; exact hpost lg h, hsim lg h⟩, ?_, ?_, ?_, ?_⟩
  · rcases h' with rfl | rfl | rfl <;> decide
  · rcases h' with rfl | rfl | rfl <;> decide
  · rw [hbs]; rcases h' with rfl | rfl | rfl <;> decide
  · rcases h' with rfl | rfl | rfl <;> decide
  · rw [hbs]; rcases h' with rfl | rfl | rfl <;> decide

theorem ctrW_levels {c : Core} (hbs : c.bs = 16) : ∀ lg ∈ wideLevels, LevelOk c ctr ctrW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) ctrW_sim

theorem cbcDecW_levels {c : Core} (hbs : c.bs = 16) :
    ∀ lg ∈ wideLevels, LevelOk c cbcDecChained cbcDecW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) cbcDecW_sim

theorem cfbDecW_levels {c : Core} (hbs : c.bs = 16) : ∀ lg ∈ wideLevels, LevelOk c cfbDec cfbDecW wideBuf lg :=
  levels_of_sim hbs rfl (by decide) (by decide) cfbDecW_sim

/-- The buffer's frame. -/
theorem wideBuf_ok : BufOk wideBuf := ⟨by decide, by decide, by decide, by decide⟩

end VG.Proof.Modes.Arm
