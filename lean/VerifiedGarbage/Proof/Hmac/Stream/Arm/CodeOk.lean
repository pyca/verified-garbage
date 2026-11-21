module

public import VerifiedGarbage.Impl.Hmac.Stream.Arm
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.MdStream.Arm.ShaScrub
public import VerifiedGarbage.Proof.Md5.Arm.Scrub

/-!
# What the cleanup needs of HMAC's and PBKDF2's code on ARMv7

The cleanup of HMAC's `init` and `finalize`, of PBKDF2 and of scrypt
(`Impl.Scrub.Arm.scrubAll`, `Arm.Scrub.scrubSideF`) needs of their code
that its frames are within the stack it zeroes and that it makes no indirect
call (`CodeOk`). That follows from the same of the hash function's code
alone (`MdOk`: its streaming functions and compression function, which use
no stack and call nothing indirectly), which each hash function proves of
its own code where it is proven (`Proof/MdStream/Arm/ShaScrub.lean`,
`Proof/Md5/Arm/Scrub.lean`, by `lit_decide`): the generic code
(`Impl/Pbkdf2/Md/Arm.lean`, `Impl/Pbkdf2/Whole/Arm.lean`) only adds its own
pushes, 8 bytes around the streaming `finalize` and HMAC's functions and 16
around `update` (`hmacInit_ok`, …, `pbkdf2_ok`), and its frames
(`initCode_ok`, `finCode_ok`, `pbkdf2Code_ok`), which this proves once for
every hash function.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.Arm

open VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Impl.Hmac.Stream.Arm

/-- A hash function's code, as HMAC and PBKDF2 call it: its streaming
functions and its compression function use no stack and make no indirect
call. -/
structure MdOk (M : Hash) : Prop where
  init : CodeOk M.st.initC 0
  upd : CodeOk M.st.updC 0
  fin : CodeOk M.st.finC 0
  comp : CodeOk M.compC 0

namespace MdOk

variable {M : Hash} (h : MdOk M)
include h

theorem init_stack : armStack M.st.initC = 0 := Nat.le_zero.mp h.init.1
theorem upd_stack : armStack M.st.updC = 0 := Nat.le_zero.mp h.upd.1
theorem fin_stack : armStack M.st.finC = 0 := Nat.le_zero.mp h.fin.1
theorem comp_stack : armStack M.compC = 0 := Nat.le_zero.mp h.comp.1

theorem hmacInit_stack : armStack M.hmacInit = 0 := by
  simp only [Hash.hmacInit, Hash.blocks, Hash.keyLoop, Hash.compressBlock,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith,
    armStack, h.init_stack, h.comp_stack, Nat.max_self]

theorem hmacInit_noIcall : noIcall M.hmacInit = true := by
  simp only [Hash.hmacInit, Hash.blocks, Hash.keyLoop, Hash.compressBlock,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith,
    noIcall, h.init.2, h.comp.2, Bool.and_self]

theorem hmacFin_stack : armStack M.hmacFin = 8 := by
  simp only [Hash.hmacFin, Hash.compressBlock, Impl.Pbkdf2.Stream.Arm.Hash.callFin,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith, armStack, h.fin_stack, h.comp_stack,
    List.length_cons, List.length_nil]
  decide

theorem hmacFin_noIcall : noIcall M.hmacFin = true := by
  simp only [Hash.hmacFin, Hash.compressBlock, Impl.Pbkdf2.Stream.Arm.Hash.callFin,
    Impl.MdStream.Arm.compressAt, Impl.MdStream.Arm.compressWith, noIcall, h.fin.2, h.comp.2, Bool.and_self]

theorem iterate_stack : armStack M.iterate = 0 := by
  simp only [Hash.iterate, Hash.body, Hash.compressBlock, Impl.MdStream.Arm.compressAt,
    Impl.MdStream.Arm.compressWith, armStack, h.comp_stack, Nat.max_self]

theorem iterate_noIcall : noIcall M.iterate = true := by
  simp only [Hash.iterate, Hash.body, Hash.compressBlock, Impl.MdStream.Arm.compressAt,
    Impl.MdStream.Arm.compressWith, noIcall, h.comp.2, Bool.and_self]

theorem hmacInit_ok : CodeOk M.hmacInit 0 := ⟨Nat.le_of_eq h.hmacInit_stack, h.hmacInit_noIcall⟩
theorem hmacFin_ok : CodeOk M.hmacFin 8 := ⟨Nat.le_of_eq h.hmacFin_stack, h.hmacFin_noIcall⟩
theorem iterate_ok : CodeOk M.iterate 0 := ⟨Nat.le_of_eq h.iterate_stack, h.iterate_noIcall⟩

/-! ## PBKDF2's functions -/

variable (I : Spec.Hmac.Instance)

theorem hmacInitAny_stack : armStack (fnsOf I M).hmacInitAny = 16 := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.hmacInitAny, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Stream.Arm.Hash.callInit, fnsOf, armStack,
    h.init_stack, h.upd_stack, h.fin_stack, h.hmacInit_stack, List.length_cons, List.length_nil]
  decide

theorem hmacInitAny_noIcall : noIcall (fnsOf I M).hmacInitAny = true := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.hmacInitAny, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Stream.Arm.Hash.callInit, fnsOf, noIcall,
    h.init.2, h.upd.2, h.fin.2, h.hmacInit_noIcall, Bool.and_self]

theorem pbkdf2_stack : armStack (fnsOf I M).pbkdf2 = 16 := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.pbkdf2, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Whole.Arm.Fns.setup, Impl.Pbkdf2.Whole.Arm.Fns.block,
    Impl.Pbkdf2.Whole.Arm.Fns.outLen, Impl.Pbkdf2.Whole.Arm.Fns.outLoop, Impl.Pbkdf2.Stream.Arm.copy,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, fnsOf, armStack, h.init_stack, h.upd_stack, h.fin_stack,
    h.hmacInit_stack, h.hmacFin_stack, h.iterate_stack, List.length_cons, List.length_nil]
  decide

theorem pbkdf2_noIcall : noIcall (fnsOf I M).pbkdf2 = true := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.pbkdf2, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Whole.Arm.Fns.setup, Impl.Pbkdf2.Whole.Arm.Fns.block,
    Impl.Pbkdf2.Whole.Arm.Fns.outLen, Impl.Pbkdf2.Whole.Arm.Fns.outLoop, Impl.Pbkdf2.Stream.Arm.copy,
    Impl.Pbkdf2.Stream.Arm.Hash.callInit, fnsOf, noIcall, h.init.2, h.upd.2, h.fin.2,
    h.hmacInit_noIcall, h.hmacFin_noIcall, h.iterate_noIcall, Bool.and_self]

theorem pbkdf2_ok : CodeOk (fnsOf I M).pbkdf2 16 := ⟨Nat.le_of_eq (h.pbkdf2_stack I), h.pbkdf2_noIcall I⟩

/-! ## In their frames -/

/-- HMAC's `init`, in the frames of its two paths, within `n` bytes. -/
theorem initCode_ok {n : Nat} (hs : frame I ≤ n) (hl : 16 + anyFrame I ≤ n) :
    CodeOk (initCode I M.hmacInit (fnsOf I M)) n := by
  refine ⟨?_, ?_⟩
  · simp only [initCode, Impl.Pbkdf2.Whole.Arm.initEntry, Code.iteCold,
      Impl.StackScratch.Arm.withStackScratch, Impl.StackScratch.Arm.withStackScratchWiped, armStack,
      h.hmacInit_stack, h.hmacInitAny_stack I, Nat.max_self, Nat.zero_max, Nat.max_zero]
    omega
  · simp only [initCode, Impl.Pbkdf2.Whole.Arm.initEntry, Code.iteCold,
      Impl.StackScratch.Arm.withStackScratch, Impl.StackScratch.Arm.withStackScratchWiped, noIcall,
      h.hmacInit_noIcall, h.hmacInitAny_noIcall I, Bool.and_self]

/-- HMAC's `finalize`, in its frame, within `n` bytes. -/
theorem finCode_ok {n : Nat} (hn : 8 + frame I ≤ n) : CodeOk (finCode I M) n := by
  refine ⟨?_, ?_⟩
  · simp only [finCode, Impl.StackScratch.Arm.withStackScratch, armStack, h.hmacFin_stack,
      Nat.zero_max]
    omega
  · simp only [finCode, Impl.StackScratch.Arm.withStackScratch, noIcall, h.hmacFin_noIcall, Bool.and_self]

/-- PBKDF2, in its frame, within `n` bytes. -/
theorem pbkdf2Code_ok {n : Nat} (hn : 16 + pbkFrame I ≤ n) : CodeOk (pbkdf2Code I (fnsOf I M)) n := by
  refine ⟨?_, ?_⟩
  · simp only [pbkdf2Code, Impl.StackScratch.Arm.withStackScratch, armStack, h.pbkdf2_stack I,
      Nat.zero_max]
    omega
  · simp only [pbkdf2Code, Impl.StackScratch.Arm.withStackScratch, noIcall, h.pbkdf2_noIcall I,
      Bool.and_self]

end MdOk

/-! ## The hash functions

Each from what its own proofs state of its code. -/

open VG.Proof.MdStream.Arm.ShaScrub

theorem md5_mdOk : MdOk md5Md :=
  ⟨CodeOk.block _, Proof.Md5.Arm.Scrub.stream_update_ok, Proof.Md5.Arm.Scrub.stream_finalize_ok,
    Proof.Md5.Arm.Scrub.compress_ok⟩

theorem sha1_mdOk : MdOk sha1Md := ⟨CodeOk.block _, sha1_update, sha1_finalize, sha1_compress⟩

theorem sha224_mdOk : MdOk sha224Md := ⟨CodeOk.block _, sha256_update, sha256_finalize, sha256_compress⟩

theorem sha256_mdOk : MdOk sha256Md := ⟨CodeOk.block _, sha256_update, sha256_finalize, sha256_compress⟩

theorem sha512_mdOk (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) :
    MdOk (sha512Md D initN iv) :=
  ⟨CodeOk.block _, sha512_update, sha512_finalize, sha512_compress⟩

end VG.Proof.Hmac.Stream.Arm
