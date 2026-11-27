module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacInit
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.HmacFin
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the functions, verified

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Core.lean`): what the kernel checks of a
hash function's code does not depend on its compression function or its
streaming functions, which our functions only call: `core H` is `H` with them
replaced by empty code, and `CoreOK` is what the kernel checks of `core H`
(the taint checks of the pieces between calls and that HMAC's buffers fit),
once for each hash function. How deeply frames nest in our functions follows
from the callees' (`hmacInit_fdepth`, …): ours push none. From them, HMAC's
`init` and `finalize`, `iterate` and `pbkdf2` are verified against the shared
contracts of `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`.

There is no stack pointer to check (`writesSp` is always `false` on AArch64),
so the artifacts' `spSafe` is `Code.all_of_forall`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (initG finG)
open VG.Proof.Pbkdf2.AArch64 (iterK iterImp)

/-- `H` without the functions it calls: its own code. -/
def core (H : Hash) : Hash :=
  ⟨H.P, H.D, H.W, "", .block [], "", .block [], "", .block [], "", .block [], "", "", "", ""⟩

/-! ## How deeply frames nest -/

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

section
variable {H : Hash}

theorem hmacInit_fdepth (hi : H.initC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) :
    H.hmacInit.aarch64Depth ≤ 1 := by
  simp only [Hash.hmacInit, Hash.stream, Hash.initKeys, Hash.keyLoop, Impl.Pbkdf2.Md.AArch64.Stream.callInit,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, Code.aarch64Depth,
    fdepth_of_noFrames hc]
  omega_using [hi]

theorem hmacFin_fdepth (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) :
    H.hmacFin.aarch64Depth ≤ 1 := by
  simp only [Hash.hmacFin, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.callFin, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Code.aarch64Depth, fdepth_of_noFrames hc]
  omega_using [hf]

theorem iterate_fdepth (hc : H.compC.noFrames = true) : H.iterate.aarch64Depth ≤ 1 := by
  simp only [Hash.iterate, Impl.Pbkdf2.AArch64.iterate, Impl.Pbkdf2.AArch64.main,
    Impl.Pbkdf2.AArch64.body, Impl.Pbkdf2.AArch64.compressBlock, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, Code.aarch64Depth, fdepth_of_noFrames hc]
  omega_using []

end

/-! ## A test of every instruction, from the own code's and the callees'

A test of every instruction of one of our functions and of what it calls
(`Scrub.sideAll`: the cleanup of the functions as emitted needs that none
writes PSTATE.DIT, and that nothing is called indirectly) holds if it holds
of the own code (`core H`) and of the hash function's code it calls. -/

section
open VG.AArch64.Scrub (sideAll)
variable {p : Instr → Bool} {H : Hash}

theorem hmacInit_side (h0 : sideAll p (core H).hmacInit = true) (hi : sideAll p H.initC = true)
    (hc : sideAll p H.compC = true) : sideAll p H.hmacInit = true := by
  simp only [core, Hash.hmacInit, Hash.stream, Hash.initKeys, Hash.keyLoop,
    Impl.Pbkdf2.Md.AArch64.Stream.callInit, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' (first | exact id | exact fun _ => hi | exact fun _ => hc | refine And.imp ?_ ?_)

theorem hmacFin_side (h0 : sideAll p (core H).hmacFin = true) (hf : sideAll p H.finC = true)
    (hc : sideAll p H.compC = true) : sideAll p H.hmacFin = true := by
  simp only [core, Hash.hmacFin, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.callFin,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' (first | exact id | exact fun _ => hf | exact fun _ => hc | refine And.imp ?_ ?_)

theorem pbkdf2_side (h0 : sideAll p (core H).pbkdf2 = true) (hi : sideAll p H.initC = true)
    (hu : sideAll p H.updC = true) (hf : sideAll p H.finC = true) (hc : sideAll p H.compC = true) :
    sideAll p H.pbkdf2 = true := by
  simp only [core, Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.AArch64.iterate, Impl.Pbkdf2.AArch64.main,
    Impl.Pbkdf2.AArch64.body, Impl.Pbkdf2.AArch64.compressBlock, Hash.stream, Hash.initKeys, Hash.keyLoop,
    Impl.Pbkdf2.Md.AArch64.Stream.callInit, Impl.Pbkdf2.Md.AArch64.Stream.callFin,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hi
    | exact fun _ => hu
    | exact fun _ => hf
    | exact fun _ => hc
    | refine And.imp ?_ ?_

theorem hmacInitAny_side (h0 : sideAll p (core H).hmacInitAny = true) (hi : sideAll p H.initC = true)
    (hu : sideAll p H.updC = true) (hf : sideAll p H.finC = true) (hc : sideAll p H.compC = true) :
    sideAll p H.hmacInitAny = true := by
  simp only [core, Hash.hmacInitAny, Hash.key, Hash.hashKey, Hash.hmacInit, Hash.stream, Hash.initKeys,
    Hash.keyLoop, Impl.Pbkdf2.Md.AArch64.Stream.callInit, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hi
    | exact fun _ => hu
    | exact fun _ => hf
    | exact fun _ => hc
    | refine And.imp ?_ ?_

/-- The shared streaming `update` (`Impl.MdStream.AArch64.update`) over a
compression function, from its own code's and the compression function's. -/
theorem mdUpdate_side (P : Impl.MdStream.AArch64.Params) (n : String) {c : Prog isa}
    (h0 : sideAll p (Impl.MdStream.AArch64.update P "" (.block [])) = true) (hc : sideAll p c = true) :
    sideAll p (Impl.MdStream.AArch64.update P n c) = true := by
  simp only [Impl.MdStream.AArch64.update, Impl.MdStream.AArch64.updateMain, Impl.MdStream.AArch64.updateBody,
    Impl.MdStream.AArch64.compressN, Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hc
    | refine And.imp ?_ ?_

/-- The shared streaming `finalize`, likewise. -/
theorem mdFinalize_side (P : Impl.MdStream.AArch64.Params) (n : String) {c : Prog isa}
    (h0 : sideAll p (Impl.MdStream.AArch64.finalize P "" (.block [])) = true) (hc : sideAll p c = true) :
    sideAll p (Impl.MdStream.AArch64.finalize P n c) = true := by
  simp only [Impl.MdStream.AArch64.finalize, Impl.MdStream.AArch64.finalizeMain,
    Impl.MdStream.AArch64.finalizeBody, Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith,
    sideAll, Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hc
    | refine And.imp ?_ ?_

/-- The shared one-shot digest (`Impl.MdStream.AArch64.OneShot.digest`), likewise. -/
theorem mdDigest_side (P : Impl.MdStream.AArch64.Params) (init : Prog isa) (n : String) {c : Prog isa}
    (h0 : sideAll p (Impl.MdStream.AArch64.OneShot.digest P init "" (.block [])) = true)
    (hc : sideAll p c = true) : sideAll p (Impl.MdStream.AArch64.OneShot.digest P init n c) = true := by
  simp only [Impl.MdStream.AArch64.OneShot.digest, Impl.MdStream.AArch64.OneShot.body,
    Impl.MdStream.AArch64.OneShot.whole, Impl.MdStream.AArch64.OneShot.tail,
    Impl.MdStream.AArch64.OneShot.compressBuf, Impl.MdStream.AArch64.OneShot.compressWith, sideAll,
    Bool.and_eq_true] at h0 ⊢
  revert h0
  repeat' first
    | exact id
    | exact fun _ => hc
    | refine And.imp ?_ ?_

/-- What the cleanup of the functions as emitted needs of every instruction
(`Scrub.verifiedScrubbedOf`): that it does not write PSTATE.DIT. -/
abbrev noDit : Instr → Bool := fun i => !i.writesDit

/-- `noDit` of the own code of a hash function's HMAC and PBKDF2 functions
(`core H`), which calls nothing indirectly: evaluated by the kernel, once for
each hash function. -/
structure CoreSide (C : Hash) : Prop where
  init : sideAll noDit C.hmacInit = true
  fin : sideAll noDit C.hmacFin = true
  any : sideAll noDit C.hmacInitAny = true
  pbk : sideAll noDit C.pbkdf2 = true

/-- `noDit` of the code of a hash function that HMAC and PBKDF2 call, which
calls nothing indirectly: evaluated by the kernel where each implementation
is listed (`Proof/Variants/MdHash/AArch64.lean`). -/
structure CalleeSide (H : Hash) : Prop where
  comp : sideAll noDit H.compC = true
  init : sideAll noDit H.initC = true
  upd : sideAll noDit H.updC = true
  fin : sideAll noDit H.finC = true

end

section
open VG.AArch64.Scrub (sideAll)
open VG.Impl.StackScratch.AArch64

private theorem stores_noDit (n : Nat) : ∀ i ∈ wipePairStores n, noDit i = true := by
  intro i hi
  simp only [wipePairStores, List.mem_map] at hi
  obtain ⟨k, -, rfl⟩ := hi
  rfl

private theorem chunk_noDit (o j n : Nat) : ∀ i ∈ wipePairChunk o j n, noDit i = true := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | h
  · rfl
  · exact stores_noDit _ _ h

private theorem chunks_noDit (o n : Nat) : ∀ i ∈ wipePairChunks o n, noDit i = true := by
  intro i hi
  unfold wipePairChunks at hi
  rcases List.mem_append.mp hi with h | h
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h
    exact chunk_noDit _ _ _ _ hj
  · split at h
    · exact absurd h List.not_mem_nil
    · exact chunk_noDit _ _ _ _ h

/-- The instructions that wipe a function's working space write no PSTATE.DIT. -/
theorem wipe_noDit (words : Nat) : ∀ i ∈ wipe words, noDit i = true := by
  intro i hi
  unfold wipe wipeAt at hi
  rcases List.mem_cons.mp hi with rfl | h
  · rfl
  rcases List.mem_append.mp h with h | h
  · exact chunks_noDit _ _ _ h
  · split at h
    · exact absurd h List.not_mem_nil
    · rcases List.mem_singleton.mp h with rfl
      rfl

/-- `noDit` of code in a frame of its own that it wipes (`withStackScratchWiped`). -/
theorem sideAll_withStackScratchWiped {bytes words : Nat} {r : Reg} {c : Prog isa}
    (hc : sideAll noDit c = true) : sideAll noDit (withStackScratchWiped bytes r words c) = true := by
  refine Scrub.sideAll_withStackScratch rfl rfl rfl ?_
  simp only [sideAll, Bool.and_eq_true, Code.allInstrs_eq, instrs, List.all_eq_true]
  exact ⟨hc, wipe_noDit words⟩

end

/-- How deeply the frames of the shared streaming functions nest: one, their
own, over a compression function that has none. -/
theorem mdUpdate_depth (P : Impl.MdStream.AArch64.Params) (n : String) (c : Prog isa)
    (h : (Impl.MdStream.AArch64.updateMain P n c).aarch64Depth = 0) :
    (Impl.MdStream.AArch64.update P n c).aarch64Depth ≤ 1 := by
  simp only [Impl.MdStream.AArch64.update, Code.aarch64Depth, h, Instr.frameUnits, Nat.zero_add, Nat.le_refl]

theorem mdFinalize_depth (P : Impl.MdStream.AArch64.Params) (n : String) (c : Prog isa)
    (h : (Impl.MdStream.AArch64.finalizeMain P n c).aarch64Depth = 0) :
    (Impl.MdStream.AArch64.finalize P n c).aarch64Depth ≤ 1 := by
  simp only [Impl.MdStream.AArch64.finalize, Code.aarch64Depth, h, Instr.frameUnits, Nat.zero_add, Nat.le_refl]

/-- The frames of code whose own nest at most once, in a frame of `F` bytes,
fit in `16 + F` bytes of stack. -/
theorem depth_frame_le {F : Nat} {r : Reg} {c : Prog isa} (h : c.aarch64Depth ≤ 1) :
    16 * (Impl.StackScratch.AArch64.withStackScratch F r c).aarch64Depth ≤ 16 + F := by
  rw [Scrub.depth_withStackScratch]; omega

/-- The frame of the shared one-shot digest is its only one, over an `init`
and a compression function that have none. -/
theorem mdDigest_depth (P : Impl.MdStream.AArch64.Params) (init : Prog isa) (n : String) (c : Prog isa)
    (hi : init.aarch64Depth = 0) (hc : c.noFrames = true) :
    16 * (Impl.MdStream.AArch64.OneShot.digest P init n c).aarch64Depth ≤
      Impl.MdStream.AArch64.OneShot.frameBytes P := by
  simp only [Impl.MdStream.AArch64.OneShot.digest, Impl.MdStream.AArch64.OneShot.body,
    Impl.MdStream.AArch64.OneShot.whole, Impl.MdStream.AArch64.OneShot.tail,
    Impl.MdStream.AArch64.OneShot.compressBuf, Impl.MdStream.AArch64.OneShot.compressWith,
    Impl.MdStream.AArch64.OneShot.copyTail, Impl.MdStream.AArch64.OneShot.bytesTail, Code.aarch64Depth, hi,
    fdepth_of_noFrames hc, Instr.frameUnits, Nat.max_self, Nat.zero_add]
  exact Nat.mul_div_le _ _

theorem hmacInitAny_fdepth {H : Hash} (hi : H.initC.aarch64Depth ≤ 1) (hu : H.updC.aarch64Depth ≤ 1)
    (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) : H.hmacInitAny.aarch64Depth ≤ 1 := by
  have h1 := hmacInit_fdepth hi hc
  simp only [Hash.hmacInitAny, Hash.key, Hash.hashKey, Code.aarch64Depth, Nat.max_le, Nat.zero_le, hi, hu, hf,
    h1, and_self]

theorem pbkdf2_fdepth {H : Hash} (hi : H.initC.aarch64Depth ≤ 1) (hu : H.updC.aarch64Depth ≤ 1)
    (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) : H.pbkdf2.aarch64Depth ≤ 1 := by
  have h1 := hmacInit_fdepth hi hc
  have h2 := hmacFin_fdepth hf hc
  have h3 := iterate_fdepth (H := H) hc
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Code.aarch64Depth, Nat.max_le, Nat.zero_le, hi, hu, hf, h1, h2, h3, and_self]

/-! ## The taint checks, which look only at the own code -/

theorem HmacInit.Checks.of_core {H : Hash} (h : HmacInit.Checks (core H)) : HmacInit.Checks H :=
  ⟨h.pro, h.argI, h.keys, h.mid, h.restore⟩

theorem HmacFin.Checks.of_core {H : Hash} (h : HmacFin.Checks (core H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

theorem Pbk.Checks.of_core {H : Hash} (h : Pbk.Checks (core H)) : Pbk.Checks H :=
  ⟨h.entry, h.hk1, h.hk3, h.hk5, h.hk7, h.keyShr, h.keySub, h.short, h.su1, h.su3, h.loopRegs,
    h.pieceA, h.finArgs, h.pieceC, h.tail, h.exit⟩

/-- What the kernel checks of a hash function's own code (`core H`): the
taint checks of the pieces between calls, and that HMAC's buffers fit in
the working space. -/
structure CoreOK (C : Hash) : Prop where
  pbk : Pbk.Checks C
  iter : VG.Proof.Pbkdf2.AArch64.Checks C.P C.D
  hinit : HmacInit.Checks C
  hfin : HmacFin.Checks C
  /-- HMAC's buffers fit in the working space. -/
  fitI : C.stream.buf ≤ 8 * C.W
  fitF : C.stream.buf + C.stream.F ≤ 8 * C.W

/-! ## The functions, verified -/

/-- A state satisfying `pbkdf2`'s precondition, with `8 sc` bytes of scratch
space: an empty password, salt and output, and `c = 1`. -/
def pbkSat (sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x4 => 1 | .x5 => 0x30000 | .x7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩]
  wr := [⟨0x30000, 0⟩, ⟨0x40000, sc * 8⟩]

/-- A state satisfying the precondition of `pbkdf2` with its working space on
the stack: `pbkSat` without the working space. -/
def pbkFrameSat : State := { pbkSat 0 with wr := [⟨0x30000, 0⟩] }

section
variable {H : Hash} (hH : HashOK H) (C : CoreOK (core H))
include hH C

theorem hmacInit_ok (hsat : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (initG hH.SH H.W) :=
  HmacInit.verified hH (HmacInit.Checks.of_core C.hinit) C.fitI (initImp _ _ hsat).sat_left

theorem hmacFin_ok (hsat : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH H.W) :=
  HmacFin.verified hH (HmacFin.Checks.of_core C.hfin) C.fitF
    (finImp _ _ hsat).sat_left

theorem iterate_ok (hsat : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (iterK hH.SH H.W) :=
  VG.Proof.Pbkdf2.AArch64.verified hH.iterOk C.iter hH.comp (iterImp _ _ hsat).sat_left

/-- HMAC's `init`, verified against the shared contract. -/
theorem hmacInit_verified (hsat : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16) :=
  (hmacInit_ok hH C hsat).of_implies (initImp _ _ hsat)

/-- HMAC's `finalize`, verified against the shared contract. -/
theorem hmacFin_verified (hsat : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (Proof.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16) :=
  (hmacFin_ok hH C hsat).of_implies (finImp _ _ hsat)

/-- `iterate`, verified against the shared contract. -/
theorem iterate_verified (hsat : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (Proof.Pbkdf2.iterateContract hH.SH H.W AArch64.abi) :=
  (iterate_ok hH C hsat).of_implies (iterImp _ _ hsat)

/-- `pbkdf2`, verified against the shared contract. -/
theorem pbkdf2_verified
    (hsI : ∃ s, (Proof.Hmac.initScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsF : ∃ s, (Proof.Hmac.finalizeScratchContract hH.SH H.W AArch64.abi 16).pre s)
    (hsT : ∃ s, (Proof.Pbkdf2.iterateContract hH.SH H.W AArch64.abi).pre s)
    (hsat : ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (Proof.Pbkdf2.pbkdf2ScratchContract hH.SH (H.W + H.S) AArch64.abi 16) :=
  (Pbk.verified hH (Pbk.Checks.of_core C.pbk)
    (hmacInit_ok hH C hsI) (hmacInit_fdepth hH.stream.initDepth hH.comp.noFrames)
    (hmacFin_ok hH C hsF) (hmacFin_fdepth hH.stream.finDepth hH.comp.noFrames)
    (iterate_ok hH C hsT) (iterate_fdepth hH.comp.noFrames)
    (pbkImp _ _ hsat).sat_left).of_implies (pbkImp _ _ hsat)

end

end VG.Proof.Pbkdf2.Md.AArch64
