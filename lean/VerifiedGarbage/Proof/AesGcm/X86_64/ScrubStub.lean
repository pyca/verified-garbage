module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill

/-!
# AES-GCM on x86-64: the stubs its cleanups are evaluated on

A function over AES-GCM's callees (`GcmImpl.callees`) is evaluated, for its
cleanup, once on its code over stubs of `vg_aes_ctr32`, the key expansion
and `vg_ghash` (`stubCallees`), each code empty: each implementation states
what the cleanup needs of its own code (`calleeSide`, its `side`), and
`Fill` joins them (`X86_64.Scrub.verifiedScrubbedAllFill`). The cleanup's
level is the highest of the implementations' and of the code's own
(`GcmImpl.lv`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)

/-- The stub of `vg_aes_ctr32`. -/
def ctrStub : Impl.AesGcm.X86_64.Fn := ⟨"c", .block []⟩

/-- The stub of `vg_ghash`. -/
def ghStub : Impl.AesGcm.X86_64.Fn := ⟨"g", .block []⟩

/-- AES-GCM's callees over the stubs, the blocks functions with the
interleaved loops `enc` and `dec`, if any, and `full` as `GcmImpl.callees`
has them. -/
def stubCallees (enc dec : Option (Prog isa) := none) (full : Bool := false) : Impl.AesGcm.X86_64.Callees :=
  ⟨ctrStub, ⟨"k", .block []⟩, ghStub,
    ⟨"e", Impl.AesGcm.X86_64.Blocks.encrypt ctrStub ghStub enc false full⟩,
    ⟨"d", Impl.AesGcm.X86_64.Blocks.decrypt ctrStub ghStub dec⟩⟩

/-- The level of the cleanup of a function over `i`'s callees whose own code
is at the level `own`. -/
def GcmImpl.lv (i : GcmImpl) (own : VecLevel) : VecLevel :=
  ((i.ctr.level.join i.key.level).join i.gh.level).join own

theorem GcmImpl.lv_le (i : GcmImpl) (own : VecLevel) :
    i.ctr.level.level ≤ (i.lv own).level ∧ i.key.level.level ≤ (i.lv own).level ∧
      i.gh.level.level ≤ (i.lv own).level ∧ own.level ≤ (i.lv own).level := by
  unfold GcmImpl.lv
  have e1 := level_join_left ((i.ctr.level.join i.key.level).join i.gh.level) own
  have e2 := level_join_right ((i.ctr.level.join i.key.level).join i.gh.level) own
  have e5 := level_join_left (i.ctr.level.join i.key.level) i.gh.level
  have e6 := level_join_right (i.ctr.level.join i.key.level) i.gh.level
  have e7 := level_join_left i.ctr.level i.key.level
  have e8 := level_join_right i.ctr.level i.key.level
  omega

/-- What the cleanup needs of `i`'s `vg_aes_ctr32`, key expansion and
`vg_ghash`, at the level `i.lv own`. -/
theorem GcmImpl.sides (i : GcmImpl) (own : VecLevel) :
    calleeSide i.ctr.callee.code (i.lv own).level 0 = true ∧ calleeSide i.key.fn.code (i.lv own).level 0 = true ∧
      calleeSide i.gh.fn.code (i.lv own).level 0 = true :=
  have h := i.lv_le own
  ⟨calleeSide_mono h.1 (Nat.le_refl 0) i.ctr.side, calleeSide_mono h.2.1 (Nat.le_refl 0) i.key.side,
    calleeSide_mono h.2.2.1 (Nat.le_refl 0) i.gh.side⟩

end VG.Proof.AesGcm.X86_64
