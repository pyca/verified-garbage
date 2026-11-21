module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.X86.Frame
public import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Impl.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesGcm.X86.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86.Gather.Verified
meta import VerifiedGarbage.Proof.AesGcm.X86.OpenTo.Verified
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.AesGcm.RoundsTo
meta import VerifiedGarbage.Impl.AesGcm.X86.Fn
meta import VerifiedGarbage.Proof.AesGcm.Scratch
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# AES-GCM on x86 (32-bit), without secret residue

Every function of AES-GCM on x86, as emitted (`Impl.AesGcm.X86.Fn`), is its
code in its frame of working space (`withStackScratch`) followed by the
zeroing of the stack its contract reserves below `esp` (that frame, and the
frames of its calls of `vg_aes_ctr32_to`, `vg_aes_expand_key_scratch` and
`vg_ghash`, which use no stack of their own) and by the clearing of the
registers (`Impl.Scrub.X86.scrubAll`). One theorem each states
`VerifiedScrubbed` of it, for every implementation `v` it calls
(`init_scrubbed`, …), from `X86.Scrub.verifiedScrubbedAll` with:

* the postcondition reading the memory on return only within the key
  context, the state and the buffers (`initOut`, …, as on ARMv7,
  `Proof/AesGcm/Arm/Scrub.lean`);
* what the cleanup needs of the code (`scrubFSide`) for every `v`
  (`init_scrub`, …): from AES-GCM's code with stub implementations, whose
  code is `.block []`, which the kernel evaluates once here (`init_side`,
  …), the implementations' own facts (`Ctr32Impl.scrub`, `expandScrub`,
  `GhashImpl.scrub`, their stack, 0), and `Fill`, which `fill_calls` proves
  of any implementation by walking only AES-GCM's code. AES-GCM's code does
  not depend on the implementations but through the calls, so one stub
  serves all of them.

`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`'s code without the
cleanup, as the internal `vg_aes_gcm_seal<suffix>_core` (`Gather.sealFn`):
its own cleanup zeroes the stack of that call.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86.Scrub

open VG VG.X86 VG.X86.Scrub VG.Impl.AesGcm.X86 VG.Proof.AesGcm.X86
open VG.Proof.AesGcm (agree_of bytesAt_congr streamRepr_congr)
open VG.Impl.StackScratch.X86 (withStackScratch)

/-! ## Reading memory only within the buffers -/

/-- The `n` bytes at `p`, of a buffer of at least `n` bytes there on which
the memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L n : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n :=
  bytesAt_congr fun i hi => agree_of h i (by omega_using [hn, hi])

theorem len_le (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat := by
  show (x.setWidth 32).toNat ≤ x.toNat
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract X86.abi stack) (Spec.Gcm.initSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain (Proof.AesGcm.initPostOut_local _)

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract X86.abi stack) (Spec.Gcm.streamInitSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamInitPostOut_local _)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract X86.abi stack) (Spec.Gcm.streamAadSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesGcm.streamAadPostOut_local _)

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptContract X86.abi stack) (Spec.Gcm.streamCryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a p hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a p hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptContract X86.abi stack) (Spec.Gcm.streamCryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT _
      obtain ⟨g₁, g₂⟩ := h key hk iv a c hr hA hT
      exact ⟨streamRepr_congr (fun i hi => agree_of hb.2.1 i (by omega_using [hi])) g₁,
        (bytesAt_of hb.2.2 (len_le len)).trans g₂⟩

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Gcm.streamFinishContract X86.abi stack) (Spec.Gcm.streamFinishSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT
      exact (bytesAt_of hb.2.2 (Nat.le_refl _)).trans (h key hk iv a c hr hA hT)

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract X86.abi stack) (Spec.Gcm.streamVerifySig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

theorem sealOut (stack : Nat) :
    PostOut (Spec.Gcm.sealContract X86.abi stack) (Spec.Gcm.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      exact (h key hk).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openOut (stack : Nat) :
    PostOut (Spec.Gcm.openContract X86.abi stack) (Spec.Gcm.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tagLen], _ =>
      simp only [Spec.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw data) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.1 (len_le len)]
      exact h'

theorem sealGatherOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherContract X86.abi stack) (Spec.Gcm.sealGatherSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk hl
      exact (h key hk hl).trans (Prod.ext (bytesAt_of hb.2.2.2.1 (len_le len)).symm
        (bytesAt_of hb.2.2.2.2 (Nat.le_refl _)).symm)

theorem openToOut (stack : Nat) :
    PostOut (Spec.Gcm.openToContract X86.abi stack) (Spec.Gcm.openToSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tagLen], _ =>
      simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      obtain ⟨-, hd⟩ := hpre
      have hd' : ((ArgWord.int abi.ptrBits).ofRaw len).toNat ≤ dl.toNat := by
        rw [← hd]; exact len_le dl
      intro key hk
      have h' := h key hk
      rw [show Spec.Aes.bytesAt m₂ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat =
          Spec.Aes.bytesAt m₁ (ArgWord.addr.ofRaw dst) ((ArgWord.int abi.ptrBits).ofRaw len).toNat from
        bytesAt_of hb.2.2.2.2.1 hd']
      exact h'

/-! ## What the cleanup needs of the code -/

/-- An implementation with no code. -/
def stubFn : Impl.AesGcm.X86.Fn := ⟨"", .block []⟩

/-- Implementations of `vg_aes_ctr32_to`, `vg_aes_expand_key_scratch` and
`vg_ghash` with no code. -/
def stub : Callees := ⟨stubFn, stubFn, stubFn⟩

-- AES-GCM's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code initStub := withStackScratch 2580 3 (init stub)
materialize_code streamInitStub := withStackScratch 2584 4 (streamInit stub)
materialize_code streamAadStub := withStackScratch 2592 6 (streamAad stub)
materialize_code streamEncryptStub := withStackScratch 2604 9 (streamEncrypt stub)
materialize_code streamDecryptStub := withStackScratch 2604 9 (streamDecrypt stub)
materialize_code streamFinishStub := withStackScratch 2600 8 (streamFinish stub)
materialize_code streamVerifyStub := withStackScratch 2604 9 (streamVerify stub)
materialize_code sealStub := withStackScratch 2604 9 («seal» stub)
materialize_code openStub := withStackScratch 2608 10 («open» stub)
materialize_code openToStub := withStackScratch 2616 12 (Open.openTo stub stubFn)
materialize_code sealGatherStub :=
  SealGather.sealGather "" (withStackScratch 2604 9 («seal» stub))

theorem init_side : scrubFSide (withStackScratch 2580 3 (init stub)) [] 2612 = true := by lit_decide
theorem streamInit_side : scrubFSide (withStackScratch 2584 4 (streamInit stub)) [] 2608 = true := by
  lit_decide
theorem streamAad_side : scrubFSide (withStackScratch 2592 6 (streamAad stub)) [] 2616 = true := by
  lit_decide
theorem streamEncrypt_side : scrubFSide (withStackScratch 2604 9 (streamEncrypt stub)) [] 2636 = true := by
  lit_decide
theorem streamDecrypt_side : scrubFSide (withStackScratch 2604 9 (streamDecrypt stub)) [] 2636 = true := by
  lit_decide
theorem streamFinish_side : scrubFSide (withStackScratch 2600 8 (streamFinish stub)) [] 2632 = true := by
  lit_decide
theorem streamVerify_side : scrubFSide (withStackScratch 2604 9 (streamVerify stub)) [] 2636 = true := by
  lit_decide
theorem seal_side : scrubFSide (withStackScratch 2604 9 («seal» stub)) [] 2636 = true := by lit_decide
theorem open_side : scrubFSide (withStackScratch 2608 10 («open» stub)) [] 2640 = true := by lit_decide
theorem openTo_side : scrubFSide (withStackScratch 2616 12 (Open.openTo stub stubFn)) [] 2696 = true := by
  lit_decide
theorem sealGather_side :
    scrubFSide (SealGather.sealGather "" (withStackScratch 2604 9 («seal» stub))) [] 2688 = true := by
  lit_decide

variable (v : GcmImpl)

/-- What `Fill` needs of the implementations `v` calls: their code meets
`calleeOk` and uses no stack. -/
structure Holes : Prop where
  ctr : calleeSide v.ctr.callee.code 0 = true
  key : calleeSide v.ctr.expand.code 0 = true
  gh : calleeSide v.gh.fn.code 0 = true

theorem holes : Holes v :=
  ⟨calleeSide_of_eq v.ctr.stack v.ctr.scrub, calleeSide_of_eq v.ctr.expandStack v.ctr.expandScrub,
    calleeSide_of_eq v.gh.stack v.gh.scrub⟩

theorem init_scrub : scrubFSide (withStackScratch 2580 3 (init v.callees)) [] 2612 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) init_side

theorem streamInit_scrub : scrubFSide (withStackScratch 2584 4 (streamInit v.callees)) [] 2608 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamInit_side

theorem streamAad_scrub : scrubFSide (withStackScratch 2592 6 (streamAad v.callees)) [] 2616 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamAad_side

theorem streamEncrypt_scrub :
    scrubFSide (withStackScratch 2604 9 (streamEncrypt v.callees)) [] 2636 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamEncrypt_side

theorem streamDecrypt_scrub :
    scrubFSide (withStackScratch 2604 9 (streamDecrypt v.callees)) [] 2636 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamDecrypt_side

theorem streamFinish_scrub :
    scrubFSide (withStackScratch 2600 8 (streamFinish v.callees)) [] 2632 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamFinish_side

theorem streamVerify_scrub :
    scrubFSide (withStackScratch 2604 9 (streamVerify v.callees)) [] 2636 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) streamVerify_side

theorem seal_scrub : scrubFSide (withStackScratch 2604 9 («seal» v.callees)) [] 2636 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) seal_side

theorem open_scrub : scrubFSide (withStackScratch 2608 10 («open» v.callees)) [] 2640 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) open_side

theorem openTo_scrub :
    scrubFSide (withStackScratch 2616 12 (Open.openTo v.callees (OpenTo.toFn v))) [] 2696 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) openTo_side

theorem sealGather_scrub :
    scrubFSide (SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code) [] 2688 = true := by
  obtain ⟨hc, hk, hg⟩ := holes v
  exact scrubFSide_of_fill (n := 0) (by fill_calls) sealGather_side

/-! ## The functions as emitted -/

theorem init_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.init v.callees) (Spec.Gcm.initContract X86.abi 2612) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.initApi)
    { code := withStackScratch 2580 3 (init v.callees)
      verified := init_framed v
      spSafe := withStackScratch_spSafe (init_spSafe v) }
    (initOut _) (hs := init_scrub v)

theorem streamInit_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamInit v.callees)
      (Spec.Gcm.streamInitContract X86.abi 2608) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamInitApi)
    { code := withStackScratch 2584 4 (streamInit v.callees)
      verified := streamInit_framed v
      spSafe := withStackScratch_spSafe (streamInit_spSafe v) }
    (streamInitOut _) (hs := streamInit_scrub v)

theorem streamAad_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamAad v.callees)
      (Spec.Gcm.streamAadContract X86.abi 2616) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamAadApi)
    { code := withStackScratch 2592 6 (streamAad v.callees)
      verified := streamAad_framed v
      spSafe := withStackScratch_spSafe (streamAad_spSafe v) }
    (streamAadOut _) (hs := streamAad_scrub v)

theorem streamEncrypt_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamEncrypt v.callees)
      (Spec.Gcm.streamEncryptContract X86.abi 2636) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamEncryptApi)
    { code := withStackScratch 2604 9 (streamEncrypt v.callees)
      verified := Proof.AesGcm.streamEncrypt_keyed (streamEncrypt_framed v)
      spSafe := withStackScratch_spSafe (streamEncrypt_spSafe v) }
    (streamEncryptOut _) (hs := streamEncrypt_scrub v)

theorem streamDecrypt_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamDecrypt v.callees)
      (Spec.Gcm.streamDecryptContract X86.abi 2636) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamDecryptApi)
    { code := withStackScratch 2604 9 (streamDecrypt v.callees)
      verified := Proof.AesGcm.streamDecrypt_keyed (streamDecrypt_framed v)
      spSafe := withStackScratch_spSafe (streamDecrypt_spSafe v) }
    (streamDecryptOut _) (hs := streamDecrypt_scrub v)

theorem streamFinish_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamFinish v.callees)
      (Spec.Gcm.streamFinishContract X86.abi 2632) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamFinishApi)
    { code := withStackScratch 2600 8 (streamFinish v.callees)
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed v)
      spSafe := withStackScratch_spSafe (streamFinish_spSafe v) }
    (streamFinishOut _) (hs := streamFinish_scrub v)

theorem streamVerify_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.streamVerify v.callees)
      (Spec.Gcm.streamVerifyContract X86.abi 2636) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.streamVerifyApi)
    { code := withStackScratch 2604 9 (streamVerify v.callees)
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed v)
      spSafe := withStackScratch_spSafe (streamVerify_spSafe v) }
    (streamVerifyOut _) (hs := streamVerify_scrub v)

theorem seal_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.«seal» v.callees) (Spec.Gcm.sealContract X86.abi 2636) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealApi)
    { code := withStackScratch 2604 9 («seal» v.callees)
      verified := Proof.AesGcm.seal_keyed (seal_framed v)
      spSafe := withStackScratch_spSafe (seal_spSafe v) }
    (sealOut _) (hs := seal_scrub v)

/-- `vg_aes_gcm_open`. (`@openOut`: applied without `@`, the elaborator
reduces its type to see what it is a function of.) -/
theorem open_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.«open» v.callees) (Spec.Gcm.openContract X86.abi 2640) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.openApi)
    { code := withStackScratch 2608 10 («open» v.callees)
      verified := Proof.AesGcm.open_keyed (open_framed v)
      spSafe := withStackScratch_spSafe (open_spSafe v) }
    (@openOut _) (hs := open_scrub v)

theorem openTo_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.openTo v.callees (OpenTo.toFn v))
      (Spec.Gcm.openToContract X86.abi 2696) 32 :=
  verifiedScrubbedAll (api := Spec.Gcm.openToApi)
    { code := withStackScratch 2616 12 (Open.openTo v.callees (OpenTo.toFn v))
      verified := Proof.AesGcm.openTo_keyed (OpenTo.openTo_framed v)
      spSafe := OpenTo.openTo_spSafe v }
    (@openToOut _) (hs := openTo_scrub v)

theorem sealGather_scrubbed :
    VerifiedScrubbed target (Impl.AesGcm.X86.Fn.sealGather v.callees v.suffix)
      (Spec.Gcm.sealGatherContract X86.abi 2688) 0 :=
  verifiedScrubbedAll (api := Spec.Gcm.sealGatherApi)
    { code := SealGather.sealGather (Gather.sealFn v).name (Gather.sealFn v).code
      verified := Proof.AesGcm.sealGather_keyed (Gather.sealGather_verified (Gather.sealFn v))
      spSafe := Gather.sealGather_spSafe v }
    (sealGatherOut _) (hs := sealGather_scrub v)

/-! ## `spSafe` of the functions as emitted, which their registrations state -/

theorem init_spSafeF : (Impl.AesGcm.X86.Fn.init v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (init_spSafe v))
theorem streamInit_spSafeF :
    (Impl.AesGcm.X86.Fn.streamInit v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamInit_spSafe v))
theorem streamAad_spSafeF : (Impl.AesGcm.X86.Fn.streamAad v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamAad_spSafe v))
theorem streamEncrypt_spSafeF :
    (Impl.AesGcm.X86.Fn.streamEncrypt v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamEncrypt_spSafe v))
theorem streamDecrypt_spSafeF :
    (Impl.AesGcm.X86.Fn.streamDecrypt v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamDecrypt_spSafe v))
theorem streamFinish_spSafeF :
    (Impl.AesGcm.X86.Fn.streamFinish v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamFinish_spSafe v))
theorem streamVerify_spSafeF :
    (Impl.AesGcm.X86.Fn.streamVerify v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (streamVerify_spSafe v))
theorem seal_spSafeF : (Impl.AesGcm.X86.Fn.«seal» v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (seal_spSafe v))
theorem open_spSafeF : (Impl.AesGcm.X86.Fn.«open» v.callees).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (withStackScratch_spSafe (open_spSafe v))
theorem openTo_spSafeF :
    (Impl.AesGcm.X86.Fn.openTo v.callees (OpenTo.toFn v)).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (OpenTo.openTo_spSafe v)
theorem sealGather_spSafeF :
    (Impl.AesGcm.X86.Fn.sealGather v.callees v.suffix).all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Gather.sealGather_spSafe v)

end VG.Proof.AesGcm.X86.Scrub
