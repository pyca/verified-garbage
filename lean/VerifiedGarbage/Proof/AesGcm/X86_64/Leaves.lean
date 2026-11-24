module
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousMasks
public import VerifiedGarbage.Proof.AesGcm.X86_64.ContiguousEntryCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedReady
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedGuard

public import VerifiedGarbage.Impl.AesGcm.X86_64.BoundedGather
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.General
import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Bulk
import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill

public import VerifiedGarbage.Proof.AesGcm.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
public import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.AesGcm.X86_64.Flag
import VerifiedGarbage.Proof.AesGcm.X86_64.Scrub
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
import VerifiedGarbage.Proof.AesGcm.ScratchPrepared16
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512
public import VerifiedGarbage.Impl.AesGcm.X86_64.StreamClr
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Base
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubStub
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM on x86-64: the prepared, streaming and one-shot functions, without secret residue

Untrusted: everything here is checked by Lean. Each function over a variant
(`GcmVariant`) is its code followed by `Impl.Scrub.X86_64.scrubAll`, which
clears the vector and caller-saved registers and wipes its whole frame in
16-byte stores that are aligned (`…_scrubbed`, by
`X86_64.Scrub.verifiedScrubbedAllFill`): the code with a stub in the place
of the functions it calls is checked once (`…_stub`), and the functions of
each variant meet what the cleanup needs of them where they are defined
(`CalleesSide`). Each function's postcondition reads the memory on return
only within its buffers (`…Out`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

section
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-! ## `vg_aes_gcm_seal_prepared_vaes_vpclmul` without secret residue -/

open VG.X86_64.Scrub VG.Impl.Scrub.X86_64

open VG.X86_64.Scrub in
/-- `vg_aes_gcm_seal_prepared`'s postcondition reads the memory on return
only within the buffers: the data and the tag. -/
theorem sealPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealPreparedContract X86_64.abi stack) (Spec.Gcm.sealPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith), Scrub.bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read 16 powers: by
the count, its code on them or its code on the key context
(`sealCodeF16`). -/
def sealF16Plain (v : GcmVariant) (r : R16 v) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := sealCodeF16 v (sealBlkR16 v)
  stack := 2624
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inl rfl) (sealCodeF16_verified v r (sealBlkR16 v)))
  spSafe := sealCodeF16_spAll v (sealBlkR16 v)

/-! ## `vg_aes_gcm_seal_prepared_aesni_pclmul` -/

open VG.X86_64.Scrub in
/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read only the key
context. -/
def sealWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := withStackArgScratch 2600 3 (v.impl.sealCode v.impl.callees)
  stack := 2624
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_of_base (sealSel_framed v.impl Short.shortFacts))
  spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v.impl v.impl.blkB)

section
open VG.X86_64.Scrub
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_stream_encrypt_prepared`'s postcondition reads the memory on
return only within the buffers: the state and the data. -/
theorem streamEncryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptPreparedContract X86_64.abi stack) (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a p hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a p hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [Scrub.bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

/-- `streamEncryptPreparedOut` for `vg_aes_gcm_stream_decrypt_prepared`. -/
theorem streamDecryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptPreparedContract X86_64.abi stack) (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a c hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a c hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [Scrub.bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

end

/-! ## The streaming functions over callees that need working space

`vg_ghash` and `vg_aes_ctr32` of the baseline implementations write secrets
in their working space, at `W + 512`. The streaming functions of the variants
that call them call `vg_ghash_w` and `vg_aes_ctr32_w` instead, which zero it
before they return (`GhashImpl.wipe`, `Ctr32Impl.wipe`), and whole-blocks
functions that zero the working space they give those callees before they
return (`BlkFn.wipeS`). -/

open Gcm.X86_64.Stitch (CtxMode)

open VG.X86_64.Scrub in
/-- `vg_aes_gcm_open_prepared`'s postcondition reads the memory on return
only within the buffers: the data. -/
theorem openPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openPreparedContract X86_64.abi stack) (Spec.Gcm.openPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Gcm.openPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m data len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ data len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ data len.toNat = Spec.Aes.bytesAt m data len.toNat)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith)]
      exact h key hk

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read only the key
context. -/
def openWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := withStackArgScratch 2608 4 (v.impl.openCode v.impl.callees)
  stack := 2632
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_of_base (openSel_framed v.impl Short.shortFacts))
  spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v.impl v.impl.blkB)

/-! ## The one-shot functions wiped whole

The one-shot functions are followed by the clearing of their whole frame,
in 16-byte stores that are aligned (an 8-byte chunk at the top, the stack
pointer on entry being 8 off 16), which asks no proof of what the code
leaves: the wipe, 32 bytes a store at every level but SSE's, costs the same
whatever the length of the input. -/

/-- `vg_aes_gcm_open_to_prepared`'s postcondition reads the memory on return
only within the buffers: the output, as long as the input by the
precondition. -/
theorem openToPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openToPreparedContract X86_64.abi stack) (Spec.Gcm.openToPreparedSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tl], _ =>
      simp only [Spec.Gcm.openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      have hdl : dl.toNat = len.toNat := hpre.2.1
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m src len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = List.replicate len.toNat 0)
      rw [Scrub.bytesAt_of0 hb.2.2.2.2.1 (by omega_arith)]
      exact h key hk

/-- `vg_aes_gcm_open_to_prepared` of a variant whose loops read only the key
context. -/
def openToWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openToCode v
  verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToCode_keyed v)
  spSafe := openToCode_spAll v

/-- `vg_aes_gcm_seal_gather_prepared`'s postcondition reads the memory on
return only within the buffers: the output and the tag. -/
theorem sealGatherPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherPreparedContract X86_64.abi stack)
      (Spec.Gcm.sealGatherPreparedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk hg
      show _ = (Spec.Aes.bytesAt m₂ dst len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [Scrub.bytesAt_of0 hb.2.2.2.1 (by omega_arith), Scrub.bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk hg

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read only the
key context. -/
def sealGatherWPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (Flag.sealGather_of_base
    (Gather.sealGather_framed (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))
  spSafe := X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl))

/-! ## The one-shot functions over the prepared powers, wiped whole

The one-shot functions of the variants whose loops read prepared powers (48
of them, `stitchR`, or 16, `R16`), by the flag or the count on those or on
the key context: each followed by the clearing of its whole frame, which
clears `zmm16`–`zmm31` too for the AVX-512 variant's code, which writes
them. -/

/-- `vg_aes_gcm_seal_prepared` of a variant whose loops read the 48 prepared
powers: by the flag, its code on those or on the key context. -/
def sealRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := sealCodeF v (sealBlkR v)
  verified := VG.Proof.AesGcm.Flag.seal_keyed (Flag.seal_ofB (Or.inr rfl) (sealCodeF_verified v (sealBlkR v)))
  spSafe := sealCodeF_spAll v (sealBlkR v)

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read the 48 prepared
powers: by the flag, its code on those or on the key context. -/
def openRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openCodeF v
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inr rfl) (openCodeF_verified v))
  spSafe := openCodeF_spAll v

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read the 48
prepared powers: by the flag, its code on those or on the key context. -/
def sealGatherRPlain (v : GcmVariant) : Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 48 (sealGatherCodeF v)
    (Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR_onFlag v)
  spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF_spAll v)
    (X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))

/-- `vg_aes_gcm_open_prepared` of a variant whose loops read 16 prepared
powers: by the count, its code on those or on the key context. -/
def openR16Plain (v : GcmVariant) (r : R16 v) : Unscrubbed Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := openCodeF16 v
  verified := VG.Proof.AesGcm.Flag.open_keyed (Flag.open_ofB (Or.inl rfl) (openCodeF16_verified v r))
  spSafe := openCodeF16_spAll v

/-- `vg_aes_gcm_seal_gather_prepared` of a variant whose loops read 16
prepared powers: by the count, its code on those or on the key context. -/
def sealGatherR16Plain (v : GcmVariant) (r : R16 v) :
    Unscrubbed Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.Gcm.X86_64.Flag.onFlag 16 (sealGatherCodeF16 v r)
    (Impl.StackScratch.X86_64.withStackArgScratch 240 5
      (Impl.AesGcm.X86_64.SealGather.sealGather (shortFn v).quick (shortFn v).fast (shortFn v).test
        (shortFn v).code (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn))
  verified := VG.Proof.AesGcm.Flag.sealGather_keyed (sealGatherR16_onFlag v r)
  spSafe := VG.X86_64.onFlag_spSafe (sealGatherCodeF16_spAll v r)
    (X86_64.withStackArgScratch_spSafe
      (Gather.sealGather_spAll (shortFn v) (initFn v.impl) (aadFn v.impl) (toFn v) (finFn v.impl)))

end

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's functions on a prepared key context, on x86-64, without secret residue

Each function of a variant `v` of AES-GCM on a key context of
`vg_aes_gcm_prepare`, followed by the clearing of every register it may
write and of its whole frame (`Impl.AesGcm.X86_64.Fn`), at the level
`GcmVariant.lv`: the highest of its callees' and of its interleaved loops'
(`GcmVariant.own`). The code over stubs of the callees, and of the
functions it calls that are built from them (the whole-blocks functions,
`blk*_sides`), is evaluated once for each kind of interleaved loops.
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)

/-- The level of the cleanup of `v`'s `open` on prepared powers, whose code
past the short path is in VEX (`FastOpen.openFin`). -/
def GcmVariant.lvA (v : GcmVariant) : VecLevel := v.impl.lv (v.own.join .avx)

theorem GcmVariant.lv_le_lvA (v : GcmVariant) : v.lv.level ≤ v.lvA.level := by
  unfold GcmVariant.lv GcmVariant.lvA GcmImpl.lv
  generalize (v.impl.ctr.level.join v.impl.key.level).join v.impl.gh.level = a
  generalize v.own = b
  cases a <;> cases b <;> decide

/-! ## The whole-blocks functions -/

theorem encrypt_fill {k : Nat} {n : String → Nat} (ctr gh : Fn) (hc : calleeSide ctr.code k (n "c") = true)
    (hg : calleeSide gh.code k (n "g") = true) (P PS : Option (Prog isa)) (al F S S4 : Bool) :
    Fill k n (Impl.AesGcm.X86_64.Blocks.encrypt ctrStub ghStub P al F S S4 PS)
      (Impl.AesGcm.X86_64.Blocks.encrypt ctr gh P al F S S4 PS) := by
  unfold Impl.AesGcm.X86_64.Blocks.encrypt Impl.AesGcm.X86_64.Blocks.blocks Impl.AesGcm.X86_64.Blocks.body
  cases P <;> cases F <;> fill_calls_refl

theorem encryptSeparate_fill {k : Nat} {n : String → Nat} (ctr gh : Fn) (hc : calleeSide ctr.code k (n "c") = true)
    (hg : calleeSide gh.code k (n "g") = true) :
    Fill k n (Impl.AesGcm.X86_64.Blocks.encryptSeparate ctrStub ghStub)
      (Impl.AesGcm.X86_64.Blocks.encryptSeparate ctr gh) := by
  unfold Impl.AesGcm.X86_64.Blocks.encryptSeparate Impl.AesGcm.X86_64.Blocks.blocks Impl.AesGcm.X86_64.Blocks.body
  fill_calls_refl

theorem decrypt_fill {k : Nat} {n : String → Nat} (ctr gh : Fn) (hc : calleeSide ctr.code k (n "c") = true)
    (hg : calleeSide gh.code k (n "g") = true) (P PS : Option (Prog isa)) (al F S S4 : Bool) :
    Fill k n (Impl.AesGcm.X86_64.Blocks.decrypt ctrStub ghStub P al F S S4 PS)
      (Impl.AesGcm.X86_64.Blocks.decrypt ctr gh P al F S S4 PS) := by
  unfold Impl.AesGcm.X86_64.Blocks.decrypt Impl.AesGcm.X86_64.Blocks.blocks Impl.AesGcm.X86_64.Blocks.body
  cases P <;> cases F <;> fill_calls_refl

/-- `v`'s `vg_aes_gcm_encrypt_blocks` and `_decrypt_blocks`, for the key
context of `vg_aes_gcm_init`, meet what the cleanup of their callers needs
of them. -/
theorem blkB_sides (v : GcmVariant) :
    calleeSide v.impl.callees.enc.code v.lv.level 8 = true ∧ calleeSide v.impl.callees.dec.code v.lv.level 8 = true := by
  obtain ⟨h1, -, h3⟩ := v.impl.sides v.own
  have hl := (v.impl.lv_le v.own).2.2.2
  have hc := calleeSide_mono (Nat.le_trans v.ctr.ctrToLevel (v.impl.lv_le v.own).1) (Nat.le_refl 0) v.ctr.ctrTo.side
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact ⟨calleeSide_of_fill (ks := 0) (encryptSeparate_fill (n := fun _ => 0) _ _ hc h3) hl
      (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false) hl
      (by lit_decide)⟩
  · cases name
    · exact ⟨calleeSide_of_fill (ks := 1)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .vaes)) none false false false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 1)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .vaes)) none false false false false) hl
        (by lit_decide)⟩
    · exact ⟨calleeSide_of_fill (ks := 2)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .vaesAvx512)) none false false false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 2)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .vaesAvx512)) none false false false false) hl
        (by lit_decide)⟩
    · exact ⟨calleeSide_of_fill (ks := 1)
        (encrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.enc .aesniAvx)) none false true false false) hl
        (by lit_decide),
        calleeSide_of_fill (ks := 1)
        (decrypt_fill (n := fun _ => 0) _ _ h1 h3 (some (StitchName.dec .aesniAvx)) none false false false false) hl
        (by lit_decide)⟩

open Gcm.X86_64.Stitch (CtxMode) in
/-- `i.blkM none`, the whole-blocks functions without loops, meet what the
cleanup of their callers needs of them, at the level `i.lv own`. -/
theorem blkM_none_sides {M : CtxMode} {al : Bool} (i : GcmImpl) (own : VecLevel) (e d : String) :
    calleeSide (i.blkM (M := M) (aligned := al) none e d).enc.code (i.lv own).level 8 = true ∧
      calleeSide (i.blkM (M := M) (aligned := al) none e d).dec.code (i.lv own).level 8 = true := by
  obtain ⟨h1, -, h3⟩ := i.sides own
  cases al
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false)
        (Nat.zero_le _) (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false)
        (Nat.zero_le _) (by lit_decide)⟩
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none true false false false)
        (Nat.zero_le _) (by lit_decide),
      calleeSide_of_fill (ks := 0) (decrypt_fill (n := fun _ => 0) _ _ h1 h3 none none true false false false)
        (Nat.zero_le _) (by lit_decide)⟩

open Gcm.X86_64.Stitch (CtxMode) in
/-- `i.blkM (some st)` for loops `st` on prepared powers, those named `n`,
meet what the cleanup of their callers needs of them, at the level
`i.lv n.lv`, from their code over stubs (`hae`, `had`, by `lit_decide`). -/
theorem blkM_prep_sides {M : CtxMode} (i : GcmImpl) (n : StitchName) (st : StitchCode M true) (e d : String)
    (hst : st.enc = n.encR ∧ st.dec = n.decR ∧ st.full = n.fullR ∧ st.fullD = n.fullDR ∧ st.small = n.smallR ∧
      st.smallD = n.smallR ∧ st.small4 = n.small4R ∧ st.encS = n.encRS ∧ st.decS = n.decRS)
    (hae : stubCallee (Impl.AesGcm.X86_64.Blocks.encrypt ctrStub ghStub (some n.encR) true n.fullR n.smallR
      n.small4R (some n.encRS)) n.lv.level (fun _ => 0) 8 = true)
    (had : stubCallee (Impl.AesGcm.X86_64.Blocks.decrypt ctrStub ghStub (some n.decR) true n.fullDR n.smallR
      n.small4R (some n.decRS)) n.lv.level (fun _ => 0) 8 = true) :
    calleeSide (i.blkM (some st) e d).enc.code (i.lv n.lv).level 8 = true ∧
      calleeSide (i.blkM (some st) e d).dec.code (i.lv n.lv).level 8 = true := by
  obtain ⟨h1, -, h3⟩ := i.sides n.lv
  have hl := (i.lv_le n.lv).2.2.2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := hst
  refine ⟨?_, ?_⟩
  · show calleeSide (Impl.AesGcm.X86_64.Blocks.encrypt i.callees.ctr i.callees.gh (some st.enc) true st.full st.small
      st.small4 (some st.encS)) _ 8 = true
    rw [e1, e3, e5, e7, e8]
    exact calleeSide_of_fill (encrypt_fill (n := fun _ => 0) _ _ h1 h3 _ _ _ _ _ _) hl hae
  · show calleeSide (Impl.AesGcm.X86_64.Blocks.decrypt i.callees.ctr i.callees.gh (some st.dec) true st.fullD st.smallD
      st.small4 (some st.decS)) _ 8 = true
    rw [e2, e4, e6, e7, e9]
    exact calleeSide_of_fill (decrypt_fill (n := fun _ => 0) _ _ h1 h3 _ _ _ _ _ _) hl had

/-- `v`'s whole-blocks functions on 48 prepared powers (`blkR`) meet what the
cleanup of their callers needs of them. -/
theorem blkR_sides (v : GcmVariant) :
    calleeSide (blkR v).enc.code v.lv.level 8 = true ∧ calleeSide (blkR v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_prep_sides _ .vaesAvx512 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

/-- `v`'s whole-blocks functions on 16 prepared powers (`blkR16`), as
`blkR_sides`. -/
theorem blkR16_sides (v : GcmVariant) :
    calleeSide (blkR16 v).enc.code v.lv.level 8 = true ∧ calleeSide (blkR16 v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · cases name <;> exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_none_sides _ _ _ _
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)


/-! ## Cleanup of the shared whole-block seal kernels -/

section SharedSeal

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Impl.AesGcm.X86_64 (Fn)

private theorem seal_fill {k : Nat} (c g : Fn) (p : Prog isa) {minimum : Nat}
    (hc : calleeSide c.code k 0 = true) (hg : calleeSide g.code k 0 = true) :
    Fill k (fun _ => 0) (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared ctrStub ghStub p true minimum)
      (Impl.AesGcm.X86_64.BlocksToDec.sealPrepared c g p true minimum) := by
  fill_calls_wide

private theorem level_of_backend {v : GcmVariant} {nm : StitchToName} (h : v.shortBackend = some nm) :
    nm.lv.level ≤ v.lvG.level := by
  suffices v.toLv = nm.lv by rw [← this]; exact level_join_right _ _
  rcases he : v.stitch with _ | pt
  · simp [GcmVariant.shortBackend,he] at h
  · rcases hp : pt.toPart with _ | x
    · simp [GcmVariant.shortBackend,he,hp] at h
    · simp [GcmVariant.shortBackend,he,hp] at h
      simp [GcmVariant.toLv,he,hp,h]

theorem selectSealLeaf_side {M} (v : GcmVariant) (name : String)
    (supported : Bool) (short : FusedShortOk M) (wide : Option (PLift (WideSealOk M))) :
    ∀ b ∈ selectSealLeaf v name supported short wide, calleeSide b.fn.code v.lvG.level 8 = true := by
  intro b mem
  have hc := calleeSide_mono (Nat.le_trans (level_join_right v.lv v.ctrTo.level)
    (level_join_left (v.lv.join v.ctrTo.level) v.toLv)) (Nat.le_refl _) v.ctrTo.side
  have hg := calleeSide_mono (Nat.le_trans (v.impl.lv_le v.own).2.2.1
    (show v.lv.level ≤ v.lvG.level from Nat.le_trans (level_join_left _ _) (level_join_left _ _)))
    (Nat.le_refl _) v.impl.gh.side
  cases supported with
  | false => simp [selectSealLeaf] at mem
  | true =>
    cases hn : v.shortBackend with
    | none => simp [selectSealLeaf,hn] at mem
    | some nm =>
      have hl := level_of_backend hn
      cases nm with
      | vaes =>
        simp [selectSealLeaf,hn] at mem
        subst b
        exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)
      | aesniAvx =>
        simp [selectSealLeaf,hn] at mem
        subst b
        exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)
      | vaesAvx512 =>
        cases wide with
        | none => simp [selectSealLeaf,hn] at mem
        | some ok =>
          simp [selectSealLeaf,hn] at mem
          subst b
          exact calleeSide_of_fill (seal_fill _ _ _ hc hg) hl (by lit_decide)

theorem sealLeafF_side (v : GcmVariant) : ∀ b ∈ sealLeafF v, calleeSide b.fn.code v.lvG.level 24 = true :=
  fun b h => calleeSide_mono (Nat.le_refl _) (by decide : 8 ≤ 24) (selectSealLeaf_side v _ _ _ _ b h)

theorem sealLeafF16_side (v : GcmVariant) : ∀ b ∈ sealLeafF16 v, calleeSide b.fn.code v.lvG.level 24 = true :=
  fun b h => calleeSide_mono (Nat.le_refl _) (by decide : 8 ≤ 24) (selectSealLeaf_side v _ _ _ _ b h)

theorem withSameDst_side (f : Fn) {k : Nat} (h : calleeSide f.code k 8 = true) :
    calleeSide f.withSameDst.code k 8 = true := by
  have level : (Instr.mov .r10 (.reg .r8)).vecLevel = 0 := rfl
  simpa [level, Impl.AesGcm.X86_64.Fn.withSameDst, calleeSide, Code.x86_64Depth, Code.allInstrs,
    UpperLock.inames, Instr.vecLevelR, loadsMxcsr] using h

end SharedSeal

theorem sealBlkR_sides (v : GcmVariant) :
    calleeSide (sealBlkR v).enc.code v.lv.level 8 = true ∧ calleeSide (sealBlkR v).dec.code v.lv.level 8 = true := by
  have base := blkR_sides v
  cases hf : sealLeafR v with
  | none => simpa only [sealBlkR,hf] using base
  | some f =>
    by_cases lv : v.lvG.level ≤ v.lv.level
    · simp only [sealBlkR,hf,ite_eq_left lv]
      have mem : f ∈ sealLeafR v := by simp [hf]
      exact ⟨withSameDst_side _ (calleeSide_mono lv (Nat.le_refl _) (selectSealLeaf_side v _ _ _ _ f mem)),base.2⟩
    · simpa only [sealBlkR,hf,ite_eq_right lv] using base


theorem sealBlkR16_sides (v : GcmVariant) :
    calleeSide (sealBlkR16 v).enc.code v.lv.level 8 = true ∧ calleeSide (sealBlkR16 v).dec.code v.lv.level 8 = true := by
  have base := blkR16_sides v
  cases hf : sealLeafR16 v with
  | none => simpa only [sealBlkR16,hf] using base
  | some f =>
    by_cases lv : v.lvG.level ≤ v.lv.level
    · simp only [sealBlkR16,hf,ite_eq_left lv]
      have mem : f ∈ sealLeafR16 v := by simp [hf]
      exact ⟨withSameDst_side _ (calleeSide_mono lv (Nat.le_refl _) (selectSealLeaf_side v _ _ _ _ f mem)),base.2⟩
    · simpa only [sealBlkR16,hf,ite_eq_right lv] using base

/-! ## The functions -/

open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- AES-GCM's callees, each a stub: the whole-blocks functions too. -/
def stub5 : Callees := ⟨ctrStub, ⟨"k", .block []⟩, ghStub, ⟨"e", .block []⟩, ⟨"d", .block []⟩⟩

/-- The stack the stubs of `stub5` stand for: the whole-blocks functions'
calls, and at most as much for the others. -/
def blkN : String → Nat := fun _ => 8

/-- What the cleanup needs of AES-GCM's callees `c`, at the level `k`. -/
structure CalleesSide (k : Nat) (c : Callees) : Prop where
  ctr : calleeSide c.ctr.code k 8 = true
  key : calleeSide c.key.code k 8 = true
  gh : calleeSide c.gh.code k 8 = true
  enc : calleeSide c.enc.code k 8 = true
  dec : calleeSide c.dec.code k 8 = true

theorem CalleesSide.mono {k k' : Nat} {c : Callees} (hk : k ≤ k') (h : CalleesSide k c) : CalleesSide k' c :=
  ⟨calleeSide_mono hk (Nat.le_refl _) h.ctr, calleeSide_mono hk (Nat.le_refl _) h.key,
    calleeSide_mono hk (Nat.le_refl _) h.gh, calleeSide_mono hk (Nat.le_refl _) h.enc,
    calleeSide_mono hk (Nat.le_refl _) h.dec⟩

/-- `v`'s callees meet `CalleesSide`. -/
theorem callees_side (v : GcmVariant) : CalleesSide v.lv.level v.impl.callees :=
  have h := v.impl.sides v.own
  ⟨calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.1, calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.2.1,
    calleeSide_mono (Nat.le_refl _) (Nat.zero_le 8) h.2.2, (blkB_sides v).1, (blkB_sides v).2⟩

/-- `v`'s callees with whole-blocks functions `B` meet `CalleesSide`, if `B` does. -/
theorem withBlk_side {M : Gcm.X86_64.Stitch.CtxMode} (v : GcmVariant) (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true ∧ calleeSide B.dec.code v.lv.level 8 = true) :
    CalleesSide v.lv.level (v.impl.withBlk B) :=
  have h := callees_side v
  ⟨h.ctr, h.key, h.gh, hB.1, hB.2⟩

theorem sealCode_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) (f : Bool) :
    Fill k blkN (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.sealCode
  cases s <;> cases f <;> fill_calls_wide

theorem openCode_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) :
    Fill k blkN (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.openCode
  cases s <;> fill_calls_wide

theorem sealCodeP_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) (f : Bool) :
    Fill k blkN (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.sealCodeP
  cases s <;> cases f <;> fill_calls_wide

theorem openCodeP_fill {k : Nat} (c : Callees) (h : CalleesSide k c) (s : Bool) :
    Fill k blkN (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  unfold Impl.AesGcm.X86_64.Fn.openCodeP
  cases s <;> fill_calls_wide

theorem streamEncrypt_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamDecrypt_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem sealW_of (v : GcmVariant) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hf := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5))
    (sealWPlain v) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openW_of (v : GcmVariant) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5)) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hf := openCode_fill _ (callees_side v) v.impl.short
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5))
    (openWPlain v) v.lv (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptW_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hf := streamEncrypt_fill _ (callees_side v)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))
    ({ suffix := v.impl.suffix
       code := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.impl.callees)
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed (Flag.streamEncrypt_of_base (streamEncrypt_framed v.impl))
       spSafe := X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl) }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptW_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hf := streamDecrypt_fill _ (callees_side v)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))
    ({ suffix := v.impl.suffix
       code := withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees)
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_of_base (streamDecrypt_framed v.impl))
       spSafe := X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem sealR_of (v : GcmVariant) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5))) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (sealBlkR v) (sealBlkR_sides v)) v.impl.short v.impl.fin
  have hb := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
    (sealRPlain v) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openR_of (v : GcmVariant) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lvA.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hp := openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR v) (blkR_sides v))) v.impl.short
  have hb := openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
    (openRPlain v) v.lvA (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptR_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamEncrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))
  have hb := streamEncrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)))
    ({ suffix := v.impl.suffix
       code := streamEncryptCodeF v
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
         (Flag.streamEncrypt_ofB (Or.inr rfl) (streamEncryptCodeF_verified v))
       spSafe := streamEncryptCodeF_spAll v }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptR_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamDecrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))
  have hb := streamDecrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)))
    ({ suffix := v.impl.suffix
       code := Impl.Gcm.X86_64.Flag.onFlag 48
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR v))))
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag
         (streamDecryptPrepared_framed v.impl (blkR v)) (streamDecrypt_framed v.impl))
       spSafe := VG.X86_64.onFlag_spSafe
         (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
         (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem sealR16_of (v : GcmVariant) (r : R16 v) (s : Bool) (f : Bool) (ks : Nat) (hs : v.impl.short = s) (hf : v.impl.fin = f) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5))) ks blkN 2624 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR16 v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (sealBlkR16 v) (sealBlkR16_sides v)) v.impl.short v.impl.fin
  have hb := sealCode_fill _ (callees_side v) v.impl.short v.impl.fin
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5)) (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
    (sealF16Plain v r) v.lv (sealPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem openR16_of (v : GcmVariant) (r : R16 v) (s : Bool) (ks : Nat) (hs : v.impl.short = s) (hks : ks ≤ v.lvA.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rw [← hs] at ha
  have hp := openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v))) v.impl.short
  have hb := openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5)) (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
    (openR16Plain v r) v.lvA (openPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamEncryptR16_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamEncrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))
  have hb := streamEncrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamEncryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5)))
    ({ suffix := v.impl.suffix
       code := streamEncryptCodeF16 v
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamEncrypt_keyed
         (Flag.streamEncrypt_ofB (Or.inl rfl) (streamEncryptCodeF16_verified v))
       spSafe := streamEncryptCodeF16_spAll v }) v.lv (streamEncryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

theorem streamDecryptR16_of (v : GcmVariant) (ks : Nat) (hks : ks ≤ v.lv.level)
    (ha : stubSide (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5))) ks blkN 2608 [] = true) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  have hp := streamDecrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))
  have hb := streamDecrypt_fill _ (callees_side v)
  have hf := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) hp) hb)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.streamDecryptPreparedApi) (ks := ks) (n := blkN) (a := Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)) (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt stub5)))
    ({ suffix := v.impl.suffix
       code := Impl.Gcm.X86_64.Flag.onFlag 16
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt (v.impl.withBlk (blkR16 v))))
         (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt v.impl.callees))
       stack := 2608
       verified := VG.Proof.AesGcm.Flag.streamDecrypt_keyed (Flag.streamDecrypt_onFlag16
         (streamDecryptPrepared16_framed v.impl (blkR16 v)) (streamDecrypt_framed v.impl))
       spSafe := VG.X86_64.onFlag_spSafe
         (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
         (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)) }) v.lv (streamDecryptPreparedOut _) hf hks (Nat.le_refl _) (ha := ha)

/-! ## By the kind of interleaved loops -/

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealW_of _ false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealW_of _ false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealW_of _ true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealW_of _ false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openW_of _ false 0 rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact openW_of _ false 1 rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact openW_of _ true 2 rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact openW_of _ false 1 rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptW_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptW_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptW_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptW_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptW_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptW_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealR_of _ false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealR_of _ false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealR_of _ true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealR_of _ false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (by lit_decide)
  · cases name
    · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2 (by lit_decide)
    · exact openR_of _ true 2 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2 (by lit_decide)
    · exact openR_of _ false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptR_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptR_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptR_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptR_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptR_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptR_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.sealPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `sealR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem sealR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR16 v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealR16_of _ r false false 0 rfl rfl (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealR16_of _ r false false 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealR16_of _ r true false 2 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealR16_of _ r false true 1 rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.openPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `openR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem openR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.openPreparedApi.contract X86_64.abi 2632) 32 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (by lit_decide)
  · cases name
    · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2 (by lit_decide)
    · exact openR16_of _ r true 2 rfl (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2 (by lit_decide)
    · exact openR16_of _ r false 1 rfl (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamEncryptR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamEncryptR16_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamEncryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamEncryptR16_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamEncryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamEncryptR16_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamEncryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function as emitted over `v` meets its contract in
constant time and returns without secret residue: `streamDecryptR16_of`, its code over
stubs evaluated for each kind of interleaved loops. -/
theorem streamDecryptR16_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.streamDecryptPreparedApi.contract X86_64.abi 2608) 0 := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact streamDecryptR16_of _ 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact streamDecryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact streamDecryptR16_of _ 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact streamDecryptR16_of _ 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's `vg_aes_gcm_open_to_prepared` on x86-64, without secret residue

On the key context, `vg_aes_gcm_open_to_prepared` calls `vg_aes_gcm_open_split`
(`openSplitFnB`), which calls the callees and `vg_aes_gcm_decrypt_blocks_to`
(`blkToDecB`), which calls `vg_ghash` and the out-of-place `vg_aes_ctr32_to`
(`GcmVariant.ctrTo`). Each is evaluated once over stubs of what it calls
(`calleeSide_of_fill`), and the function over a stub of the first
(`verifiedScrubbedAllFill`), at the level `GcmVariant.lvTW` (`lvT` on prepared powers).
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- The level of the cleanup of `v`'s `open_to`: `lvA`'s, its out-of-place
`vg_aes_ctr32_to`'s and its out-of-place loops'. -/
def GcmVariant.lvT (v : GcmVariant) : VecLevel := (v.lvA.join v.ctrTo.level).join v.toLv

theorem GcmVariant.lvA_le_lvT (v : GcmVariant) : v.lvA.level ≤ v.lvT.level :=
  Nat.le_trans (level_join_left _ _) (level_join_left _ _)

theorem GcmVariant.toLv_le_lvT (v : GcmVariant) : v.toLv.level ≤ v.lvT.level := level_join_right _ _

/-- The level of the cleanup of `v`'s `open_to` on the key context: `lv`'s
and its out-of-place `vg_aes_ctr32_to`'s. -/
def GcmVariant.lvTW (v : GcmVariant) : VecLevel := v.lv.join v.ctrTo.level

theorem join_mono_left {a b : VecLevel} (c : VecLevel) (h : a.level ≤ b.level) :
    (a.join c).level ≤ (b.join c).level := by
  revert h; cases a <;> cases b <;> cases c <;> decide

theorem GcmVariant.lvTW_le_lvT (v : GcmVariant) : v.lvTW.level ≤ v.lvT.level :=
  Nat.le_trans (join_mono_left _ v.lv_le_lvA) (level_join_left _ _)

theorem GcmVariant.one_le_lvT (v : GcmVariant) : 1 ≤ v.lvT.level :=
  Nat.le_trans (Nat.le_trans (level_join_right v.own .avx) (v.impl.lv_le _).2.2.2) v.lvA_le_lvT

/-- The stub of `vg_aes_ctr32_to`. -/
def ctrToStub : Fn := ⟨"t", .block []⟩

/-- The stub of `vg_aes_gcm_decrypt_blocks_to`. -/
def toDecStub : Fn := ⟨"T", .block []⟩

/-- The stub of `vg_aes_gcm_open_split`. -/
def splitStub : Fn := ⟨"S", .block []⟩

theorem decryptTo_fill {k : Nat} {n : String → Nat} (g c : Fn) (hg : calleeSide g.code k (n "g") = true)
    (hc : calleeSide c.code k (n "t") = true) :
    Fill k n (Impl.AesGcm.X86_64.BlocksToDec.decryptTo ghStub ctrToStub)
      (Impl.AesGcm.X86_64.BlocksToDec.decryptTo g c) := by
  fill_calls_wide

theorem openSplit_fill {k : Nat} {n : String → Nat} (c : Callees) (T : Fn)
    (h1 : calleeSide c.ctr.code k (n "c") = true) (h3 : calleeSide c.gh.code k (n "g") = true)
    (hT : calleeSide T.code k (n "T") = true) :
    Fill k n (Impl.AesGcm.X86_64.OpenSplit.openSplit stub5 toDecStub)
      (Impl.AesGcm.X86_64.OpenSplit.openSplit c T) := by
  fill_calls_wide

/-- `openSplit`'s code over stubs, evaluated once. -/
theorem openSplit_stub : stubCallee (Impl.AesGcm.X86_64.OpenSplit.openSplit stub5 toDecStub) 0 (fun _ => 24) 56 = true := by
  lit_decide

theorem openToSplit_fill {k : Nat} {n : String → Nat} (S : Fn) (hS : calleeSide S.code k (n "S") = true) :
    Fill k n (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub))
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S)) := by
  fill_calls_wide

/-- `v`'s callees meet `CalleesSide` at the level `lvTW`. -/
theorem callees_sideTW (v : GcmVariant) : CalleesSide v.lvTW.level v.impl.callees :=
  CalleesSide.mono (level_join_left _ _) (callees_side v)

/-- `v`'s callees meet `CalleesSide` at the level `lvT`. -/
theorem callees_sideT (v : GcmVariant) : CalleesSide v.lvT.level v.impl.callees :=
  CalleesSide.mono v.lvTW_le_lvT (callees_sideTW v)

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to` on the key context. -/
theorem blkToDecB_side (v : GcmVariant) : calleeSide (blkToDecB v v.ctrTo).fn.code v.lvTW.level 24 = true :=
  have hl := Nat.le_trans (v.impl.lv_le v.own).2.2.1 (level_join_left _ _)
  calleeSide_of_fill (ks := 0)
    (decryptTo_fill (n := fun _ => 0) _ _ (calleeSide_mono hl (Nat.le_refl 0) v.impl.gh.side)
      (calleeSide_mono (level_join_right _ _) (Nat.le_refl 0) v.ctrTo.side))
    (Nat.zero_le _) (by lit_decide)

/-- `v`'s `vg_aes_gcm_open_split` on the key context. -/
theorem openSplitFnB_side (v : GcmVariant) : calleeSide (openSplitFnB v v.ctrTo).fn.code v.lvTW.level 56 = true :=
  have h := callees_sideTW v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvTW.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecB_side v))
    (Nat.zero_le _) openSplit_stub

/-- `Spec.Gcm.openToPreparedApi`'s function on the key context, as emitted
over `v` (`Impl.AesGcm.X86_64.Fn.openToW`), meets its contract in constant
time and returns without secret residue. -/
theorem openToW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (ks := 0) (n := fun _ => 56)
    (a := withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub))
    (openToWPlain v) v.lvTW (openToPreparedOut _) (openToSplit_fill _ (openSplitFnB_side v))
    (Nat.zero_le _) (Nat.le_refl _)

/-! ## On prepared powers -/

/-- `open`'s code on 48 prepared powers or on the key context, over stubs. -/
theorem openCodeF_fill (v : GcmVariant) :
    Fill v.lvA.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
      (openCodeF v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR v) (blkR_sides v))) v.impl.short))
    (openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short))

/-- `open`'s code on 16 prepared powers or on the key context, over stubs. -/
theorem openCodeF16_fill (v : GcmVariant) :
    Fill v.lvA.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP v.impl.short stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode v.impl.short stub5)))
      (openCodeF16 v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (openCodeP_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v))) v.impl.short))
    (openCode_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)) v.impl.short))

theorem openCodeF_side_of (v : GcmVariant) (s : Bool) (hs : v.impl.short = s) (ks : Nat) (hks : ks ≤ v.lvA.level)
    (ha : stubCallee (Impl.Gcm.X86_64.Flag.onFlag 48 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 = true) :
    calleeSide (openCodeF v) v.lvA.level 2632 = true := by
  rw [← hs] at ha
  exact calleeSide_of_fill (openCodeF_fill v) hks ha

theorem openCodeF16_side_of (v : GcmVariant) (s : Bool) (hs : v.impl.short = s) (ks : Nat) (hks : ks ≤ v.lvA.level)
    (ha : stubCallee (Impl.Gcm.X86_64.Flag.onFlag 16 (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) ks blkN 2632 = true) :
    calleeSide (openCodeF16 v) v.lvA.level 2632 = true := by
  rw [← hs] at ha
  exact calleeSide_of_fill (openCodeF16_fill v) hks ha

theorem openP_stub (s : Bool) (t : Nat) (ht : t = 16 ∨ t = 48) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCodeP s stub5))
        (withStackArgScratch 2608 4 (Impl.AesGcm.X86_64.Fn.openCode s stub5))) (if s then 2 else 1) blkN 2632 = true := by
  rcases ht with rfl | rfl <;> cases s <;> lit_decide

/-- `v`'s `open` on 48 prepared powers meets what the cleanup of its callers
needs of it. -/
theorem openCodeF_side (v : GcmVariant) : calleeSide (openCodeF v) v.lvA.level 2632 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (openP_stub false 48 (.inr rfl))
  · cases name
    · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2
        (openP_stub false 48 (.inr rfl))
    · exact openCodeF_side_of _ true rfl 2 (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2
        (openP_stub true 48 (.inr rfl))
    · exact openCodeF_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2
        (openP_stub false 48 (.inr rfl))

/-- `v`'s `open` on 16 prepared powers, as `openCodeF_side`. -/
theorem openCodeF16_side (v : GcmVariant) : calleeSide (openCodeF16 v) v.lvA.level 2632 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((VecLevel.sse).join .avx)).2.2.2 (openP_stub false 16 (.inl rfl))
  · cases name
    · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .vaes).join .avx)).2.2.2
        (openP_stub false 16 (.inl rfl))
    · exact openCodeF16_side_of _ true rfl 2 (GcmImpl.lv_le _ ((StitchName.lv .vaesAvx512).join .avx)).2.2.2
        (openP_stub true 16 (.inl rfl))
    · exact openCodeF16_side_of _ false rfl 1 (GcmImpl.lv_le _ ((StitchName.lv .aesniAvx).join .avx)).2.2.2
        (openP_stub false 16 (.inl rfl))

/-- `v`'s whole-blocks functions on the flagged context of 48 powers (`blkF`). -/
theorem blkF_sides (v : GcmVariant) :
    calleeSide (blkF v).enc.code v.lv.level 8 = true ∧ calleeSide (blkF v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_prep_sides _ .vaesAvx512 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

/-- `v`'s whole-blocks functions on the flagged context of 16 powers (`blkF16`). -/
theorem blkF16_sides (v : GcmVariant) :
    calleeSide (blkF16 v).enc.code v.lv.level 8 = true ∧ calleeSide (blkF16 v).dec.code v.lv.level 8 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, _ | q, tP⟩⟩
  · exact blkM_none_sides _ _ _ _
  · cases name <;> exact blkM_none_sides _ _ _ _
  · cases name
    · exact blkM_prep_sides _ .vaes _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide) (by lit_decide)
    · exact blkM_none_sides _ _ _ _
    · exact blkM_prep_sides _ .aesniAvx _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (by lit_decide)
        (by lit_decide)

theorem toDec_fill {k : Nat} {n : String → Nat} (dec : Fn) (hd : calleeSide dec.code k (n "d") = true)
    (P : Option (Prog isa)) (al : Bool) :
    Fill k n (Impl.AesGcm.X86_64.BlocksToDec.decrypt ⟨"d", .block []⟩ P al)
      (Impl.AesGcm.X86_64.BlocksToDec.decrypt dec P al) := by
  cases P <;> fill_calls_wide

/-- `BlocksToDec.decrypt` over stubs, with the out-of-place loops named `n`
if any, evaluated once for each. -/
theorem toDec_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksToDec.decrypt ⟨"d", .block []⟩ (n.map StitchToName.decToR) true)
      ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem toDecF_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.dec.code v.lv.level 8 = true) (st : Option (StitchToDecCode M true)) (n : Option StitchToName)
    (hst : st.map (·.dec) = n.map StitchToName.decToR) (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvT.level) :
    calleeSide (BlkToDecFn.ofBlocks "" B st).fn.code v.lvT.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksToDec.decrypt B.dec (st.map (·.dec)) true) _ 24 = true
  rw [hst]
  exact calleeSide_of_fill (toDec_fill (n := fun _ => 8) _
    (calleeSide_mono (Nat.le_trans v.lv_le_lvA v.lvA_le_lvT) (Nat.le_refl _) hB) _ true) hn (toDec_stub n)

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to_prepared` meets what the cleanup of
its callers needs of it. -/
theorem blkToDecF_side (v : GcmVariant) : calleeSide (blkToDecF v).fn.code v.lvT.level 24 = true := by
  have hB := (blkF_sides v).2
  have hl := v.toLv_le_lvT
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, _ | q⟩⟩⟩
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · cases tname
    · exact toDecF_side_of _ _ hB _ (some .vaes) rfl hl
    · exact toDecF_side_of _ _ hB _ (some .vaesAvx512) rfl hl
    · exact toDecF_side_of _ _ hB _ (some .aesniAvx) rfl hl

/-- `v`'s `vg_aes_gcm_open_split_prepared`, as `openSplitFnB_side`. -/
theorem openSplitFnF_side (v : GcmVariant) : calleeSide (openSplitFnF v).fn.code v.lvT.level 56 = true :=
  have h := callees_sideT v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvT.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecF_side v))
    (Nat.zero_le _) openSplit_stub

/-- `v`'s `vg_aes_gcm_decrypt_blocks_to_prepared16` meets what the cleanup of
its callers needs of it. -/
theorem blkToDecF16_side (v : GcmVariant) : calleeSide (blkToDecF16 v).fn.code v.lvT.level 24 = true := by
  have hB := (blkF16_sides v).2
  have hl := v.toLv_le_lvT
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, _ | q⟩⟩⟩
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
  · cases tname
    · exact toDecF_side_of _ _ hB _ (some .vaes) rfl hl
    · exact toDecF_side_of _ _ hB _ none rfl (Nat.zero_le _)
    · exact toDecF_side_of _ _ hB _ (some .aesniAvx) rfl hl

/-- `v`'s `vg_aes_gcm_open_split_prepared16`, as `openSplitFnB_side`. -/
theorem openSplitFnF16_side (v : GcmVariant) : calleeSide (openSplitFnF16 v).fn.code v.lvT.level 56 = true :=
  have h := callees_sideT v
  have m := fun {c : Prog isa} (hc : calleeSide c v.lvT.level 8 = true) =>
    calleeSide_mono (Nat.le_refl _) (show 8 ≤ 24 by decide) hc
  calleeSide_of_fill (ks := 0)
    (openSplit_fill (n := fun _ => 24) _ _ (m h.ctr) (m h.gh) (blkToDecF16_side v))
    (Nat.zero_le _) openSplit_stub

theorem openToStackF_eq (v : GcmVariant) : openToStackF v = 2776 := by
  unfold openToStackF openToStackR openToStack; split <;> rfl

theorem openToStackF16_eq (v : GcmVariant) : openToStackF16 v = 2776 := by
  unfold openToStackF16 openToStackR16 openToStack; split <;> rfl

/-- The stub of `vg_aes_gcm_open_prepared<suffix>_core`. -/
def openStubO : Fn := ⟨"O", .block []⟩

/-- The stub of `vg_aes_gcm_open_split_prepared`. -/
def splitStubF : Fn := ⟨"F", .block []⟩

/-- The stack the stubs of `open_to` on prepared powers stand for. -/
def openToN : String → Nat := fun s => if s = "O" then 2632 else 56

theorem openToP_fill {k : Nat} {n : String → Nat} (t : Nat) (sel : Bool)
    (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (fO fS S : Fn)
    (hO : calleeSide fO.code k (n "O") = true) (hF : calleeSide fS.code k (n "F") = true)
    (hS : calleeSide S.code k (n "S") = true) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w openStubO splitStubF)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
      (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w fO fS)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S))) := by
  unfold Impl.AesGcm.X86_64.Fn.openToCodeP
  fill_calls_wide

/-- The level of `copyBytes w`: SSE's, VEX's or EVEX's. -/
def widthLv : Impl.ChaCha20Poly1305.X86_64.SealGather.Width → Nat
  | .x16 => 0
  | .y32 => 1
  | .z64 => 2

theorem copyW_cases (i : GcmImpl) : i.copyW = .x16 ∨ i.copyW = .y32 := by
  unfold GcmImpl.copyW; split
  · exact .inr rfl
  · exact .inl rfl

theorem openToP_stub (t : Nat) (ht : t = 16 ∨ t = 48) (sel : Bool) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width)
    (hw : w = .x16 ∨ w = .y32) :
    stubSide (Impl.Gcm.X86_64.Flag.onFlag t (Impl.AesGcm.X86_64.Fn.openToCodeP sel w openStubO splitStubF)
        (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
      (widthLv w) openToN 2776 [] = true := by
  rcases ht with rfl | rfl <;> rcases hw with rfl | rfl <;> cases sel <;> lit_decide

theorem width_le (v : GcmVariant) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (hw : w = .x16 ∨ w = .y32) :
    widthLv w ≤ v.lvT.level := by
  rcases hw with rfl | rfl
  · exact Nat.zero_le _
  · exact v.one_le_lvT

/-- `Spec.Gcm.openToPreparedApi`'s function over `v` on 48 prepared powers or
the key context, as emitted (`Impl.AesGcm.X86_64.Fn.openToP`), meets its
contract in constant time and returns without secret residue. -/
theorem openToR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
        (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 := by
  have hO := calleeSide_mono v.lvA_le_lvT (show 2632 ≤ openToN "O" by decide) (openCodeF_side v)
  have hF := calleeSide_mono (Nat.le_refl _) (show 56 ≤ openToN "F" by decide) (openSplitFnF_side v)
  have hS := calleeSide_mono v.lvTW_le_lvT (show 56 ≤ openToN "S" by decide) (openSplitFnB_side v)
  have ha := openToP_stub 48 (.inr rfl) v.stitchToDecR.isSome v.impl.copyW (copyW_cases v.impl)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (n := openToN) (rb := 32) (stack := 2776)
    (a := Impl.Gcm.X86_64.Flag.onFlag 48 (Impl.AesGcm.X86_64.Fn.openToCodeP v.stitchToDecR.isSome v.impl.copyW openStubO splitStubF)
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
    { suffix := v.impl.suffix
      code := Impl.Gcm.X86_64.Flag.onFlag 48 (openToCodeF v) (openToCode v)
      stack := 2776
      verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToStackF_eq v ▸ openToCodeR_onFlag v)
      spSafe := openToCodeR_onFlag_spAll v } v.lvT (openToPreparedOut _) (openToP_fill 48 _ _ _ _ _ hO hF hS) (width_le v _ (copyW_cases v.impl)) (Nat.le_refl _)
    (ha := ha)

/-- `Spec.Gcm.openToPreparedApi`'s function over `v` on 16 prepared powers or
the key context, as emitted (`Impl.AesGcm.X86_64.Fn.openToP`), meets its
contract in constant time and returns without secret residue. -/
theorem openToR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn (openSplitFnF16 v).fn
        (openSplitFnB v v.ctrTo).fn)
      (Spec.Gcm.openToPreparedApi.contract X86_64.abi 2776) 32 := by
  have hO := calleeSide_mono v.lvA_le_lvT (show 2632 ≤ openToN "O" by decide) (openCodeF16_side v)
  have hF := calleeSide_mono (Nat.le_refl _) (show 56 ≤ openToN "F" by decide) (openSplitFnF16_side v)
  have hS := calleeSide_mono v.lvTW_le_lvT (show 56 ≤ openToN "S" by decide) (openSplitFnB_side v)
  have ha := openToP_stub 16 (.inl rfl) v.stitchToDecR16.isSome v.impl.copyW (copyW_cases v.impl)
  exact verifiedScrubbedAllFill (api := Spec.Gcm.openToPreparedApi) (n := openToN) (rb := 32) (stack := 2776)
    (a := Impl.Gcm.X86_64.Flag.onFlag 16 (Impl.AesGcm.X86_64.Fn.openToCodeP v.stitchToDecR16.isSome v.impl.copyW openStubO splitStubF)
      (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit splitStub)))
    { suffix := v.impl.suffix
      code := Impl.Gcm.X86_64.Flag.onFlag 16 (openToCodeF16 v r) (openToCode v)
      stack := 2776
      verified := VG.Proof.AesGcm.Flag.openTo_keyed (openToStackF16_eq v ▸ openToCodeR16_onFlag v r)
      spSafe := openToCodeR16_onFlag_spAll v r } v.lvT (openToPreparedOut _) (openToP_fill 16 _ _ _ _ _ hO hF hS) (width_le v _ (copyW_cases v.impl)) (Nat.le_refl _)
    (ha := ha)

end VG.Proof.AesGcm.X86_64

/-!
## AES-GCM's `vg_aes_gcm_seal_gather_prepared` on x86-64, without secret residue

`vg_aes_gcm_seal_gather_prepared` calls `vg_aes_gcm_seal` (`sealFn`),
`vg_aes_gcm_seal_split` (`splitFn`) and the streaming functions (`initFn`,
`aadFn`, `toFn`, `finFn`), which call the callees, the whole-blocks
functions and their out-of-place forms (`blkTo`). Each is evaluated once
over stubs of what it calls (`calleeSide_of_fill`), for each kind of
interleaved loops where its code depends on them, and the function over
stubs of the first (`verifiedScrubbedAllFill`), at the level `GcmVariant.lvG`.
-/

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

theorem GcmVariant.lv_le_lvG (v : GcmVariant) : v.lv.level ≤ v.lvG.level :=
  Nat.le_trans (level_join_left _ _) (level_join_left _ _)

theorem GcmVariant.toLv_le_lvG (v : GcmVariant) : v.toLv.level ≤ v.lvG.level := level_join_right _ _

theorem GcmVariant.own_le_lvG (v : GcmVariant) : v.own.level ≤ v.lvG.level :=
  Nat.le_trans (v.impl.lv_le v.own).2.2.2 v.lv_le_lvG

/-- A stub, named `s`. -/
def fnStub (s : String) : Fn := ⟨s, .block []⟩

/-! ## The streaming functions it calls -/

/-- What the cleanup needs of AES-GCM's callees `c`, at the level `k`, each
in the stack `n` says by its stub's name. -/
structure CalleesSideN (k : Nat) (n : String → Nat) (c : Callees) : Prop where
  ctr : calleeSide c.ctr.code k (n "c") = true
  key : calleeSide c.key.code k (n "k") = true
  gh : calleeSide c.gh.code k (n "g") = true
  enc : calleeSide c.enc.code k (n "e") = true
  dec : calleeSide c.dec.code k (n "d") = true

/-- The stack the stubs of `stub5` stand for, each its own: none for
`vg_aes_ctr32`, the key expansion and `vg_ghash`. -/
def blkN0 : String → Nat := fun s => if s = "e" then 8 else if s = "d" then 8 else 0

/-- `v`'s callees meet `CalleesSideN` with the stacks `blkN0`. -/
theorem callees_side0 (v : GcmVariant) : CalleesSideN v.lv.level blkN0 v.impl.callees :=
  have h := v.impl.sides v.own
  ⟨calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.1, calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.2.1,
    calleeSide_mono (Nat.le_refl _) (Nat.zero_le _) h.2.2,
    calleeSide_mono (Nat.le_refl _) (by simp [blkN0]) (blkB_sides v).1,
    calleeSide_mono (Nat.le_refl _) (by simp [blkN0]) (blkB_sides v).2⟩

theorem streamInitS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit stub5))
      (withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamAadS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad stub5))
      (withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamFinishS_fill {k : Nat} {n : String → Nat} (c : Callees) (h : CalleesSideN k n c) :
    Fill k n (withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish stub5))
      (withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish c)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem initFn_side (v : GcmVariant) : calleeSide (initFn v.impl).fn.code v.lv.level 2576 = true :=
  calleeSide_of_fill (ks := 0) (streamInitS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem aadFn_side (v : GcmVariant) : calleeSide (aadFn v.impl).fn.code v.lv.level 2576 = true :=
  calleeSide_of_fill (ks := 0) (streamAadS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem finFn_side (v : GcmVariant) : calleeSide (finFn v.impl).fn.code v.lv.level 2584 = true :=
  calleeSide_of_fill (ks := 0) (streamFinishS_fill _ (callees_side0 v)) (Nat.zero_le _) (by lit_decide)

theorem encFn_side (v : GcmVariant) : calleeSide (encFn v.impl).fn.code v.lv.level 2608 = true :=
  calleeSide_of_fill (ks := 0) (streamEncrypt_fill _ (callees_side v)) (Nat.zero_le _) (by lit_decide)

/-! ## `vg_aes_gcm_seal` -/

theorem sealFn_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f) (ks : Nat)
    (hks : ks ≤ v.lv.level)
    (ha : stubCallee (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)) ks blkN 2624 = true) :
    calleeSide (sealFn v.impl).fn.code v.lv.level 2624 = true := by
  rw [← hs, ← hf] at ha
  exact calleeSide_of_fill (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin) hks ha

theorem sealFn_side (v : GcmVariant) : calleeSide (sealFn v.impl).fn.code v.lv.level 2624 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealFn_side_of _ false false rfl rfl 0 (Nat.zero_le _) (by lit_decide)
  · cases name
    · exact sealFn_side_of _ false false rfl rfl 1 (GcmImpl.lv_le _ (StitchName.lv .vaes)).2.2.2 (by lit_decide)
    · exact sealFn_side_of _ true false rfl rfl 2 (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2 (by lit_decide)
    · exact sealFn_side_of _ false true rfl rfl 1 (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2 (by lit_decide)

/-! ## The out-of-place whole-blocks functions -/

theorem blocksTo_fill {k : Nat} {n : String → Nat} (enc : Fn) (he : calleeSide enc.code k (n "e") = true)
    (P : Option (Prog isa)) (al F : Bool) :
    Fill k n (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ P al F)
      (Impl.AesGcm.X86_64.BlocksTo.encrypt enc P al F) := by
  cases P <;> fill_calls_wide

/-- `BlocksTo.encrypt` over a stub, with the out-of-place loop `P` (of the
level `l`), evaluated once for each. -/
theorem blocksTo_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ (n.map StitchToName.enc) false
      ((n.map StitchToName.full).getD false)) ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem blkTo_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M false)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.enc ∧ encFullTo st = (n.map StitchToName.full).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level) :
    calleeSide (StreamTo.BlkToFn.ofBlocks "" B st).fn.code v.lvG.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksTo.encrypt B.enc (st.map (·.enc)) false (encFullTo st)) _ 24 = true
  rw [hst.1, hst.2]
  exact calleeSide_of_fill (blocksTo_fill (n := fun _ => 8) _
    (calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB) _ false _) hn (blocksTo_stub n)

/-- `v`'s `vg_aes_gcm_encrypt_blocks_to`. -/
theorem blkTo_side (v : GcmVariant) : calleeSide (blkTo v).fn.code v.lvG.level 24 = true := by
  have hB := (blkB_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, tpR, tpD⟩⟩⟩
  · exact blkTo_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkTo_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkTo_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkTo_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkTo_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

theorem streamTo_fill {k : Nat} {n : String → Nat} (blk enc : Fn) (hb : calleeSide blk.code k (n "B") = true)
    (he : calleeSide enc.code k (n "E") = true) :
    Fill k n (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt (fnStub "B") (fnStub "E")))
      (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt blk enc)) := by
  fill_calls_wide

/-- The stack the stubs of `vg_aes_gcm_stream_encrypt_to` stand for. -/
def streamToN : String → Nat := fun s => if s = "B" then 24 else 2608

theorem streamTo_stub :
    stubCallee (withStackArgScratch 2232 3 (Impl.AesGcm.X86_64.StreamTo.encrypt (fnStub "B") (fnStub "E")))
      0 streamToN 4856 = true := by
  lit_decide

/-- `v`'s `vg_aes_gcm_stream_encrypt_to`. -/
theorem toFn_side (v : GcmVariant) : calleeSide (toFn v).fn.code v.lvG.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _ (calleeSide_mono (Nat.le_refl _) (show 24 ≤ streamToN "B" by decide) (blkTo_side v))
    (calleeSide_mono v.lv_le_lvG (show 2608 ≤ streamToN "E" by decide) (encFn_side v))) (Nat.zero_le _) streamTo_stub

/-! ## `vg_aes_gcm_seal_split` -/

/-- The stub of `vg_aes_gcm_encrypt_blocks_to`. -/
def toStub : Fn := fnStub "T"

/-- `GcmImpl.splitFin` over stubs. -/
def stubSplitFin (s f : Bool) : Prog isa :=
  if s then Impl.AesGcm.X86_64.Short.finish
  else if f then Impl.AesGcm.X86_64.Short.finishWith Impl.AesGcm.X86_64.Short.finKsA
  else Impl.AesGcm.X86_64.SealSplit.finCalls stub5

/-- `GcmImpl.splitMid` over stubs. -/
def stubSplitMid (s f : Bool) : Prog isa :=
  if s then Impl.AesGcm.X86_64.SealSplit.runShort stub5 toStub (stubSplitFin s f)
  else Impl.AesGcm.X86_64.SealSplit.run stub5 toStub (stubSplitFin s f)

/-- The stack the stubs of `seal_split` stand for. -/
def splitN : String → Nat := fun s => if s = "T" then 24 else 8

theorem splitMid_fill {k : Nat} {n : String → Nat} (i : GcmImpl) (c : Callees) (fTo : Fn)
    (h : CalleesSideN k n c) (h₀ : CalleesSideN k n i.callees) (hT : calleeSide fTo.code k (n "T") = true) :
    Fill k n (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMid i.short i.fin)))
      (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (i.splitMid c fTo))) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  obtain ⟨g1, g2, g3, ge, gd⟩ := h₀
  unfold GcmImpl.splitMid GcmImpl.splitFin stubSplitMid stubSplitFin
  fill_calls_wide

/-- `v`'s callees meet `CalleesSideN` with the stacks `splitN`. -/
theorem callees_sideS (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (k : Nat)
    (hk : v.lv.level ≤ k) (hB : calleeSide B.enc.code k 8 = true ∧ calleeSide B.dec.code k 8 = true) :
    CalleesSideN k splitN (v.impl.withBlk B) :=
  have h := callees_side v
  ⟨calleeSide_mono hk (by simp [splitN]) h.ctr, calleeSide_mono hk (by simp [splitN]) h.key,
    calleeSide_mono hk (by simp [splitN]) h.gh, calleeSide_mono (Nat.le_refl _) (by simp [splitN]) hB.1,
    calleeSide_mono (Nat.le_refl _) (by simp [splitN]) hB.2⟩

theorem splitFn_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f) (ks : Nat)
    (hk : v.own.level = ks)
    (ha : stubCallee (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMid s f))) ks splitN
      2672 = true) :
    calleeSide (splitFn v).fn.code v.lvG.level 2672 = true := by
  rw [← hs, ← hf] at ha
  have hks := v.own_le_lvG
  rw [hk] at hks
  have hB := blkB_sides v
  exact calleeSide_of_fill (splitMid_fill v.impl _ _
    (callees_sideS v v.impl.blkB _ v.lv_le_lvG ⟨calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.1,
      calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.2⟩)
    (callees_sideS v v.impl.blkB _ v.lv_le_lvG ⟨calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.1,
      calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB.2⟩)
    (calleeSide_mono (Nat.le_refl _) (by simp [splitN]) (blkTo_side v))) hks ha

/-- `v`'s `vg_aes_gcm_seal_split`. -/
theorem splitFn_side (v : GcmVariant) : calleeSide (splitFn v).fn.code v.lvG.level 2672 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFn_side_of _ false false rfl rfl 0 rfl (by lit_decide)
  · cases name
    · exact splitFn_side_of _ false false rfl rfl 1
        rfl (by lit_decide)
    · exact splitFn_side_of _ true false rfl rfl 2
        rfl (by lit_decide)
    · exact splitFn_side_of _ false true rfl rfl 1
        rfl (by lit_decide)

/-! ## `vg_aes_gcm_seal_gather_prepared` on the key context -/

/-- The stack the stubs of `seal_gather` stand for. -/
def gatherN : String → Nat := fun s =>
  if s = "Se" ∨ s = "SeF" then 2624 else if s = "Sp" ∨ s = "SpF" then 2672 else if s = "To" ∨ s = "ToF" then 4856
  else if s = "Fi" then 2584 else if s = "I" ∨ s = "A" then 2576 else if s = "e" ∨ s = "d" then 8 else 0

theorem gather_fill {k : Nat} {n : String → Nat} (t ts : Nat) (Se Sp I A To Fi : Fn)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true) :
    Fill k n (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
        (fnStub "To") (fnStub "Fi"))
      (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi) := by
  fill_calls_wide

/-- `seal_gather` over stubs, copying below `t` bytes and sealing a first
slice of `ts` bytes in place: those of each kind of out-of-place loops. -/
theorem gather_stub : (n : Option StitchToName) →
    stubSide (Impl.AesGcm.X86_64.Fn.sealGatherCode
        (match n with | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1)
        (match n with | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17)
        (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A") (fnStub "To") (fnStub "Fi"))
      0 gatherN 5128 [] = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem copyBelow_eq (v : GcmVariant) : copyBelow v =
    match (v.stitch.bind (·.toPart)).map (·.name) with
    | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1 := rfl

theorem splitFrom_eq (v : GcmVariant) : splitFrom v =
    match (v.stitch.bind (·.toPart)).map (·.name) with
    | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17 := rfl

/-- `Spec.Gcm.sealGatherPreparedApi`'s function on the key context, as
emitted over `v` (`Impl.AesGcm.X86_64.Fn.sealGatherW`), meets its contract in
constant time and returns without secret residue. -/
theorem sealGatherW_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
        (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hSe := calleeSide_mono v.lv_le_lvG (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono v.lv_le_lvG (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono v.lv_le_lvG (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono (Nat.le_refl _) (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono v.lv_le_lvG (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have ha := gather_stub ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← copyBelow_eq, ← splitFrom_eq] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 0) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp")
      (fnStub "I") (fnStub "A") (fnStub "To") (fnStub "Fi"))
    (sealGatherWPlain v) v.lvG (sealGatherPreparedOut _) (gather_fill _ _ _ _ _ _ _ _ hSe hSp hI hA hTo hFi)
    (Nat.zero_le _) (Nat.le_refl _) (ha := ha)

/-! ## On prepared powers: what `seal_gather` calls -/

/-- `seal`'s code on 48 prepared powers or on the key context, over stubs. -/
theorem sealCodeF_fill (v : GcmVariant) :
    Fill v.lv.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 48
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
      (sealCodeF v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (sealCodeP_fill _ (withBlk_side v (blkR v) (blkR_sides v)) v.impl.short v.impl.fin))
    (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin))

/-- `seal`'s code on 16 prepared powers or on the key context, over stubs. -/
theorem sealCodeF16_fill (v : GcmVariant) :
    Fill v.lv.level blkN
      (Impl.Gcm.X86_64.Flag.onFlag 16
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP v.impl.short v.impl.fin stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode v.impl.short v.impl.fin stub5)))
      (sealCodeF16 v) :=
  Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
    (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
      (sealCodeP_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v)) v.impl.short v.impl.fin))
    (sealCode_fill _ (callees_side v) v.impl.short v.impl.fin))

theorem sealP_stub (t : Nat) (ht : t = 16 ∨ t = 48) (s f : Bool) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCodeP s f stub5))
        (withStackArgScratch 2600 3 (Impl.AesGcm.X86_64.Fn.sealCode s f stub5)))
      (if s then 2 else if f then 1 else 0) blkN 2624 = true := by
  rcases ht with rfl | rfl <;> cases s <;> cases f <;> lit_decide

theorem sealCodeF_side_of (v : GcmVariant) (s f : Bool) (hs : v.impl.short = s) (hf : v.impl.fin = f)
    (hks : (if s then 2 else if f then 1 else 0) ≤ v.lv.level) :
    calleeSide (sealCodeF v) v.lv.level 2624 = true ∧ calleeSide (sealCodeF16 v) v.lv.level 2624 = true := by
  have h₁ := sealP_stub 48 (.inr rfl) s f
  have h₂ := sealP_stub 16 (.inl rfl) s f
  rw [← hs, ← hf] at h₁ h₂
  rw [← hs, ← hf] at hks
  exact ⟨calleeSide_of_fill (sealCodeF_fill v) hks h₁, calleeSide_of_fill (sealCodeF16_fill v) hks h₂⟩

/-- `v`'s `seal` on 48 and on 16 prepared powers. -/
theorem sealCodeF_sides (v : GcmVariant) :
    calleeSide (sealCodeF v) v.lv.level 2624 = true ∧ calleeSide (sealCodeF16 v) v.lv.level 2624 = true := by
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact sealCodeF_side_of _ false false rfl rfl (Nat.zero_le _)
  · cases name
    · exact sealCodeF_side_of _ false false rfl rfl (Nat.zero_le _)
    · exact sealCodeF_side_of _ true false rfl rfl (GcmImpl.lv_le _ (StitchName.lv .vaesAvx512)).2.2.2
    · exact sealCodeF_side_of _ false true rfl rfl (GcmImpl.lv_le _ (StitchName.lv .aesniAvx)).2.2.2

/-- `stream_encrypt` on 48 or 16 prepared powers or on the key context, over stubs. -/
theorem streamEncP_stub (t : Nat) (ht : t = 16 ∨ t = 48) :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt stub5))) 0 blkN 2608 = true := by
  rcases ht with rfl | rfl <;> lit_decide

/-- `v`'s `stream_encrypt` on 48 prepared powers. -/
theorem streamEncryptCodeF_side (v : GcmVariant) : calleeSide (streamEncryptCodeF v) v.lv.level 2608 = true :=
  calleeSide_of_fill
    (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48)) (Fill.ite .ae
      (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
        (streamEncrypt_fill _ (withBlk_side v (blkR v) (blkR_sides v))))
      (streamEncrypt_fill _ (callees_side v))))
    (Nat.zero_le _) (streamEncP_stub 48 (.inr rfl))

/-- `v`'s `stream_encrypt` on 16 prepared powers. -/
theorem streamEncryptCodeF16_side (v : GcmVariant) : calleeSide (streamEncryptCodeF16 v) v.lv.level 2608 = true :=
  calleeSide_of_fill
    (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
      (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
        (streamEncrypt_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v))))
      (streamEncrypt_fill _ (callees_side v))))
    (Nat.zero_le _) (streamEncP_stub 16 (.inl rfl))

theorem streamEncryptClr_fill {k : Nat} (c : Callees) (h : CalleesSide k c) :
    Fill k blkN (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))
      (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr c .avx)) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  fill_calls_wide

theorem streamEncClr_stub :
    stubCallee (Impl.Gcm.X86_64.Flag.onFlag 16
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))
        (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncryptClr stub5 .avx))) 1 blkN 2608 = true := by
  lit_decide

/-- `v`'s `stream_encrypt` on 16 prepared powers as `seal_gather` calls it
(`streamEncryptCodeF16S`), at the level `lvA`. -/
theorem streamEncryptCodeF16S_side (v : GcmVariant) :
    calleeSide (streamEncryptCodeF16S v) v.lvA.level 2608 = true := by
  unfold streamEncryptCodeF16S
  split
  · exact calleeSide_of_fill
      (Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 16)) (Fill.ite .ae
        (Fill.seq (Fill.seq (Fill.block []) (Fill.block []))
          (streamEncryptClr_fill _ (CalleesSide.mono v.lv_le_lvA (withBlk_side v (blkR16 v) (blkR16_sides v)))))
        (streamEncryptClr_fill _ (CalleesSide.mono v.lv_le_lvA (callees_side v)))))
      (Nat.le_trans (level_join_right v.own .avx) (v.impl.lv_le _).2.2.2) streamEncClr_stub
  · exact calleeSide_mono v.lv_le_lvA (Nat.le_refl _) (streamEncryptCodeF16_side v)

/-- `BlocksTo.encrypt` over a stub on prepared powers, with the out-of-place
loop named `n` if any, evaluated once for each. -/
theorem blocksToP_stub : (n : Option StitchToName) →
    stubCallee (Impl.AesGcm.X86_64.BlocksTo.encrypt ⟨"e", .block []⟩ (n.map StitchToName.encR) true
      ((n.map StitchToName.fullR).getD false)) ((n.map StitchToName.lv).getD .sse).level (fun _ => 8) 24 = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem blkToP_legacy_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M true)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.encR ∧ encFullTo st = (n.map StitchToName.fullR).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level) :
    calleeSide (StreamTo.BlkToFn.ofBlocks "" B st).fn.code v.lvG.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st)) _ 24 = true
  rw [hst.1, hst.2]
  exact calleeSide_of_fill (blocksTo_fill (n := fun _ => 8) _
    (calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB) _ true _) hn (blocksToP_stub n)

theorem encryptPrepared_fill {k : Nat} {n : String → Nat} (c g : Fn) (p : Prog isa) {minimum : Nat}
    (hc : calleeSide c.code k (n "t") = true) (hg : calleeSide g.code k (n "g") = true) :
    Fill k n (Impl.AesGcm.X86_64.BlocksToDec.encryptPrepared ctrToStub ghStub p true minimum)
      (Impl.AesGcm.X86_64.BlocksToDec.encryptPrepared c g p true minimum) := by
  fill_calls_wide

theorem encryptPrepared_stub (n : StitchToName) :
    stubCallee (Impl.AesGcm.X86_64.BlocksToDec.encryptPrepared ctrToStub ghStub n.encR true)
      n.lv.level (fun _ => 0) 24 = true := by
  cases n <;> lit_decide

theorem encryptVaesShort_stub :
    stubCallee (Impl.AesGcm.X86_64.BlocksToDec.encryptPrepared ctrToStub ghStub
      Impl.Gcm.X86_64.StitchR.encToFromTwo true 2) 1 (fun _ => 0) 24 = true := by lit_decide

theorem encryptAesniShort_stub :
    stubCallee (Impl.AesGcm.X86_64.BlocksToDec.encryptPrepared ctrToStub ghStub
      Impl.Gcm.X86_64.StitchAvx8.encBuffers true 5) 1 (fun _ => 0) 24 = true := by lit_decide

theorem blkToP_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M true)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.encR ∧ encFullTo st = (n.map StitchToName.fullR).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level)
    (flags : ∀ nm, n = some nm → v.shortBackend = some nm)
    (fused : FusedShortOk M) :
    calleeSide (StreamTo.BlkToFn.ofPreparedBlocks "" v.gh.impl v.ctr.ctrTo B v.shortBackend fused st).fn.code v.lvG.level 24 = true := by
  cases st with
  | none =>
    cases n with
    | none => exact blkToP_legacy_side_of v B hB none none ⟨rfl,rfl⟩ hn
    | some nm => simp at hst
  | some q =>
    obtain ⟨p,full,ok,pc⟩ := q
    cases n with
    | none => simp at hst
    | some nm =>
      have he : p = nm.encR := Option.some.inj hst.1
      have hf : full = true := by
        cases nm <;> exact hst.2
      subst p
      subst full
      have hc := calleeSide_mono (Nat.le_trans (level_join_right v.lv v.ctrTo.level)
        (level_join_left (v.lv.join v.ctrTo.level) v.toLv)) (Nat.le_refl _) v.ctrTo.side
      have hg := calleeSide_mono (Nat.le_trans (v.impl.lv_le v.own).2.2.1 v.lv_le_lvG) (Nat.le_refl _) v.impl.gh.side
      simp only [StreamTo.BlkToFn.ofPreparedBlocks, flags nm rfl]
      cases nm
      · exact calleeSide_of_fill (encryptPrepared_fill (n := fun _ => 0) _ _ _ hc hg) hn encryptVaesShort_stub
      · exact calleeSide_of_fill (encryptPrepared_fill (n := fun _ => 0) _ _ _ hc hg) hn (encryptPrepared_stub .vaesAvx512)
      · exact calleeSide_of_fill (encryptPrepared_fill (n := fun _ => 0) _ _ _ hc hg) hn encryptAesniShort_stub

/-- `v`'s `blkToR`. -/
theorem blkToR_side (v : GcmVariant) : calleeSide (blkToR v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR_sides v).1
  have fused : FusedShortOk Gcm.X86_64.Stitch.CtxMode.prepared := ⟨fun _ h =>
    Gcm.X86_64.StitchR.encToFromTwo_ok 24 (by decide) h, fun _ h =>
    Gcm.X86_64.StitchAvx8.encBuffers_ok 24 (by decide) h⟩
  have side := blkToP_side_of v (blkR v) hB v.stitchToR
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname
    · exact side (some .vaes) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side (some .vaesAvx512) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side (some .aesniAvx) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused

/-- `v`'s `blkToF`. -/
theorem blkToF_side (v : GcmVariant) : calleeSide (blkToF v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF_sides v).1
  have fused : FusedShortOk Gcm.X86_64.Stitch.CtxMode.flagged := ⟨fun _ h =>
    Gcm.X86_64.StitchR.encToFromTwo_ok 24 (by decide) (sPreTo_ofFlagged h), fun _ h =>
    Gcm.X86_64.StitchAvx8.encBuffers_ok 24 (by decide) (sPreTo_ofFlagged h)⟩
  have side := blkToP_side_of v (blkF v) hB (v.stitchToR.map StitchToCode.flagged)
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname
    · exact side (some .vaes) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side (some .vaesAvx512) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side (some .aesniAvx) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused

/-- `v`'s `blkToR16`. -/
theorem blkToR16_side (v : GcmVariant) : calleeSide (blkToR16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR16_sides v).1
  have fused : FusedShortOk Gcm.X86_64.Stitch.CtxMode.prepared16 := ⟨fun _ h =>
    Gcm.X86_64.StitchR.encToFromTwo_ok 8 (by decide) h, fun _ h =>
    Gcm.X86_64.StitchAvx8.encBuffers_ok 8 (by decide) h⟩
  have side := blkToP_side_of v (blkR16 v) hB v.stitchToR16
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname <;> exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname
    · exact side (some .vaes) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
    · exact side (some .aesniAvx) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused

/-- `v`'s `blkToF16`. -/
theorem blkToF16_side (v : GcmVariant) : calleeSide (blkToF16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF16_sides v).1
  have fused : FusedShortOk (Gcm.X86_64.Stitch.CtxMode.flaggedT 16) := ⟨fun _ h =>
    Gcm.X86_64.StitchR.encToFromTwo_ok 8 (by decide) (sPreTo_ofFlagged16 h), fun _ h =>
    Gcm.X86_64.StitchAvx8.encBuffers_ok 8 (by decide) (sPreTo_ofFlagged16 h)⟩
  have side := blkToP_side_of v (blkF16 v) hB (v.stitchToR16.map StitchToCode.flagged16)
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname <;> exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
  · cases tname
    · exact side (some .vaes) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused
    · exact side none ⟨rfl, rfl⟩ (Nat.zero_le _) (by simp) fused
    · exact side (some .aesniAvx) ⟨rfl, rfl⟩ hl (by intro nm h; cases h; rfl) fused

/-! ## `vg_aes_gcm_seal_split_prepared` -/

/-- The level of the cleanup of `v`'s `seal_gather` on prepared powers:
`lvG`'s, and VEX's for its path for TLS records (`Fast.sel`). -/
def GcmVariant.lvGA (v : GcmVariant) : VecLevel := v.lvG.join .avx

theorem GcmVariant.lvG_le_lvGA (v : GcmVariant) : v.lvG.level ≤ v.lvGA.level := level_join_left _ _

theorem GcmVariant.one_le_lvGA (v : GcmVariant) : 1 ≤ v.lvGA.level := level_join_right v.lvG .avx

/-- `GcmImpl.splitPre` over stubs. -/
def stubSplitPre : Option OnePassName → Prog isa
  | some .r => Impl.AesGcm.X86_64.SealSplit.prefixS ctrStub toStub OnePassName.r.code
  | some .z => Impl.AesGcm.X86_64.SealSplit.prefixN toStub OnePassName.z.code
  | none => Impl.AesGcm.X86_64.SealSplit.«prefix» toStub

/-- `GcmImpl.splitMidR` over stubs. -/
def stubSplitMidR (s f : Bool) (op : Option OnePassName) : Prog isa :=
  if s then Impl.AesGcm.X86_64.Fast.sel stub5 (stubSplitPre op) Impl.AesGcm.X86_64.Short.finKs (stubSplitFin s f)
    (stubSplitMid s f)
  else Impl.AesGcm.X86_64.Fast.sel stub5 (stubSplitPre op) Impl.AesGcm.X86_64.Short.finKsA (stubSplitFin s f)
    (stubSplitMid s f) true

theorem splitMidR_fill {k : Nat} {n : String → Nat} (i : GcmImpl) (c : Callees) (fTo : Fn)
    (h : CalleesSideN k n c) (h₀ : CalleesSideN k n i.callees) (hT : calleeSide fTo.code k (n "T") = true) :
    Fill k n (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMidR i.short i.fin i.onePass)))
      (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (i.splitMidR c fTo))) := by
  obtain ⟨h1, h2, h3, he, hd⟩ := h
  obtain ⟨g1, g2, g3, ge, gd⟩ := h₀
  unfold GcmImpl.splitMidR GcmImpl.splitPre GcmImpl.splitMid GcmImpl.splitFin stubSplitMidR stubSplitPre stubSplitMid
    stubSplitFin
  generalize i.onePass = op
  rcases op with _ | _ | _ <;> fill_calls_wide

theorem splitFnP_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) (T : Fn)
    (hB : calleeSide B.enc.code v.lv.level 8 = true ∧ calleeSide B.dec.code v.lv.level 8 = true)
    (hT : calleeSide T.code v.lvG.level 24 = true) (s f : Bool) (op : Option OnePassName)
    (hs : v.impl.short = s) (hf : v.impl.fin = f) (hop : v.impl.onePass = op) (ks : Nat) (hk : ks ≤ v.lvGA.level)
    (ha : stubCallee (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (stubSplitMidR s f op))) ks
      splitN 2672 = true) :
    calleeSide (withStackArgScratch 2616 5 (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk B) T)))
      v.lvGA.level 2672 = true := by
  rw [← hs, ← hf, ← hop] at ha
  have hB₀ := blkB_sides v
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  exact calleeSide_of_fill (splitMidR_fill v.impl _ _
    (callees_sideS v B _ hl ⟨calleeSide_mono hl (Nat.le_refl _) hB.1, calleeSide_mono hl (Nat.le_refl _) hB.2⟩)
    (callees_sideS v v.impl.blkB _ hl ⟨calleeSide_mono hl (Nat.le_refl _) hB₀.1,
      calleeSide_mono hl (Nat.le_refl _) hB₀.2⟩)
    (calleeSide_mono v.lvG_le_lvGA (by simp [splitN]) hT)) hk ha

/-- `v`'s `vg_aes_gcm_seal_split_prepared`. -/
theorem splitFnF_side (v : GcmVariant) : calleeSide (splitFnF v).fn.code v.lvGA.level 2672 = true := by
  have hB := blkR_sides v
  have hT := blkToR_side v
  have hk := Nat.le_trans v.own_le_lvG v.lvG_le_lvGA
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFnP_side_of _ _ _ hB hT false false none rfl rfl rfl 1 (GcmVariant.one_le_lvGA _) (by lit_decide)
  · cases name
    · exact splitFnP_side_of _ _ _ hB hT false false (some .r) rfl rfl rfl 1 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT true false (some .z) rfl rfl rfl 2 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT false true none rfl rfl rfl 1 hk (by lit_decide)

/-- `v`'s `vg_aes_gcm_seal_split_prepared16`. -/
theorem splitFnF16_side (v : GcmVariant) (r : R16 v) : calleeSide (splitFnF16 v r).fn.code v.lvGA.level 2672 = true := by
  have hB := blkR16_sides v
  have hT := blkToR16_side v
  have hk := Nat.le_trans v.own_le_lvG v.lvG_le_lvGA
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact splitFnP_side_of _ _ _ hB hT false false none rfl rfl rfl 1 (GcmVariant.one_le_lvGA _) (by lit_decide)
  · cases name
    · exact splitFnP_side_of _ _ _ hB hT false false (some .r) rfl rfl rfl 1 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT true false (some .z) rfl rfl rfl 2 hk (by lit_decide)
    · exact splitFnP_side_of _ _ _ hB hT false true none rfl rfl rfl 1 hk (by lit_decide)

/-- `v`'s `vg_aes_gcm_stream_encrypt_to_prepared`. -/
theorem toFnF_side (v : GcmVariant) : calleeSide (toFnF v).fn.code v.lvG.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _ (calleeSide_mono (Nat.le_refl _) (show 24 ≤ streamToN "B" by decide) (blkToF_side v))
    (calleeSide_mono v.lv_le_lvG (show 2608 ≤ streamToN "E" by decide) (streamEncryptCodeF_side v))) (Nat.zero_le _)
    streamTo_stub

theorem GcmVariant.lvA_le_lvGA (v : GcmVariant) : v.lvA.level ≤ v.lvGA.level := by
  unfold GcmVariant.lvA GcmVariant.lvGA GcmVariant.lvG GcmVariant.lv GcmImpl.lv
  generalize (v.impl.ctr.level.join v.impl.key.level).join v.impl.gh.level = a
  generalize v.own = b
  generalize v.toLv = c
  generalize v.ctrTo.level = d
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- `v`'s `vg_aes_gcm_stream_encrypt_to_prepared16`. -/
theorem toFnF16_side (v : GcmVariant) : calleeSide (toFnF16 v).fn.code v.lvGA.level 4856 = true :=
  calleeSide_of_fill (streamTo_fill _ _
    (calleeSide_mono v.lvG_le_lvGA (show 24 ≤ streamToN "B" by decide) (blkToF16_side v))
    (calleeSide_mono v.lvA_le_lvGA (show 2608 ≤ streamToN "E" by decide) (streamEncryptCodeF16S_side v)))
    (Nat.zero_le _) streamTo_stub

/-! ## `vg_aes_gcm_seal_gather_prepared` on prepared powers -/

theorem gatherP_fill {k : Nat} {n : String → Nat} (c : Nat) (lg : Bool) (t ts : Nat)
    (SeF SpF ToF Se Sp To I A Fi : Fn)
    (hSeF : calleeSide SeF.code k (n "SeF") = true) (hSpF : calleeSide SpF.code k (n "SpF") = true)
    (hToF : calleeSide ToF.code k (n "ToF") = true)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts (fnStub "SeF") (fnStub "SpF") (fnStub "I") (fnStub "A")
          (fnStub "ToF") (fnStub "Fi") false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      (Impl.Gcm.X86_64.Flag.onFlag c (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts SeF SpF I A ToF Fi false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi)) := by
  fill_calls_wide

/-- `streamInit`, `streamAad` and `streamFinish` over stubs, as stubs of
their instances, which `seal_gather` on 16 prepared powers inlines. -/
def initStub : Fn := ⟨"I", withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit stub5)⟩
def aadStub : Fn := ⟨"A", withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad stub5)⟩
def finStub : Fn := ⟨"Fi", withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish stub5)⟩

theorem gatherP16_fill {k : Nat} {n : String → Nat} (c : Nat) (lg : Bool) (t ts : Nat)
    (SeF SpF ToF Se Sp To I A Fi : Fn)
    (hSeF : calleeSide SeF.code k (n "SeF") = true) (hSpF : calleeSide SpF.code k (n "SpF") = true)
    (hToF : calleeSide ToF.code k (n "ToF") = true)
    (hSe : calleeSide Se.code k (n "Se") = true) (hSp : calleeSide Sp.code k (n "Sp") = true)
    (hI : calleeSide I.code k (n "I") = true) (hA : calleeSide A.code k (n "A") = true)
    (hTo : calleeSide To.code k (n "To") = true) (hFi : calleeSide Fi.code k (n "Fi") = true)
    (fI : Fill k n initStub.code I.code) (fA : Fill k n aadStub.code A.code) (fFi : Fill k n finStub.code Fi.code) :
    Fill k n (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts (fnStub "SeF") (fnStub "SpF") initStub aadStub
          (fnStub "ToF") finStub true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      (Impl.Gcm.X86_64.Flag.onFlag c (Impl.AesGcm.X86_64.Fn.sealGatherCodeP lg t ts SeF SpF I A ToF Fi true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode t ts Se Sp I A To Fi)) := by
  fill_calls_wide
  all_goals first | exact fI | exact fA | exact fFi

/-- The shapes of `seal_gather` by the kind of out-of-place loops. -/
def gLong (n : Option StitchToName) : Bool := match n with | some .vaesAvx512 => true | _ => false
def gT (n : Option StitchToName) : Nat :=
  match n with | some .vaesAvx512 => 768 | some .vaes => 16384 | some .aesniAvx => 3072 | none => 2 ^ 31 - 1
def gTs (n : Option StitchToName) : Nat :=
  match n with | some .vaesAvx512 => 752 | some .vaes => 1024 | some .aesniAvx => 384 | none => 2 ^ 31 - 17

theorem gatherP_stub (c : Nat) (hc : c = 16 ∨ c = 48) : (n : Option StitchToName) →
    stubSide (Impl.Gcm.X86_64.Flag.onFlag c
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (gLong n) (gT n) (gTs n) (fnStub "SeF") (fnStub "SpF") (fnStub "I")
          (fnStub "A") (fnStub "ToF") (fnStub "Fi") false)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode (gT n) (gTs n) (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      1 gatherN 5128 [] = true
  | none => by rcases hc with rfl | rfl <;> lit_decide
  | some .vaes => by rcases hc with rfl | rfl <;> lit_decide
  | some .vaesAvx512 => by rcases hc with rfl | rfl <;> lit_decide
  | some .aesniAvx => by rcases hc with rfl | rfl <;> lit_decide

theorem gatherP16_stub : (n : Option StitchToName) →
    stubSide (Impl.Gcm.X86_64.Flag.onFlag 16
        (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (gLong n) (gT n) (gTs n) (fnStub "SeF") (fnStub "SpF") initStub
          aadStub (fnStub "ToF") finStub true)
        (Impl.AesGcm.X86_64.Fn.sealGatherCode (gT n) (gTs n) (fnStub "Se") (fnStub "Sp") (fnStub "I") (fnStub "A")
          (fnStub "To") (fnStub "Fi")))
      1 gatherN 5128 [] = true
  | none => by lit_decide
  | some .vaes => by lit_decide
  | some .vaesAvx512 => by lit_decide
  | some .aesniAvx => by lit_decide

theorem tlsLong_eq (v : GcmVariant) : tlsLong v = gLong ((v.stitch.bind (·.toPart)).map (·.name)) := rfl
theorem copyBelow_eq' (v : GcmVariant) : copyBelow v = gT ((v.stitch.bind (·.toPart)).map (·.name)) := rfl
theorem splitFrom_eq' (v : GcmVariant) : splitFrom v = gTs ((v.stitch.bind (·.toPart)).map (·.name)) := rfl

/-- `v`'s callees meet `CalleesSideN` with the stacks `gatherN`. -/
theorem callees_sideG (v : GcmVariant) : CalleesSideN v.lvGA.level gatherN v.impl.callees :=
  have h := v.impl.sides v.own
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  ⟨calleeSide_mono hl (Nat.zero_le _) h.1, calleeSide_mono hl (Nat.zero_le _) h.2.1,
    calleeSide_mono hl (Nat.zero_le _) h.2.2,
    calleeSide_mono hl (by simp [gatherN]) (blkB_sides v).1,
    calleeSide_mono hl (by simp [gatherN]) (blkB_sides v).2⟩

/-- `Spec.Gcm.sealGatherPreparedApi`'s function over `v` on 48 prepared powers
or the key context, as emitted (`Impl.AesGcm.X86_64.Fn.sealGatherP`), meets
its contract in constant time and returns without secret residue. -/
theorem sealGatherR_scrubbed (v : GcmVariant) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
        (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn false)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  have hSeF := calleeSide_mono hl (show 2624 ≤ gatherN "SeF" by decide) (sealCodeF_sides v).1
  have hSpF := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "SpF" by decide) (splitFnF_side v)
  have hToF := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "ToF" by decide) (toFnF_side v)
  have hSe := calleeSide_mono hl (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono v.lvG_le_lvGA (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono hl (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono hl (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono hl (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have ha := gatherP_stub 48 (.inr rfl) ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← tlsLong_eq, ← copyBelow_eq', ← splitFrom_eq'] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 1) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.Gcm.X86_64.Flag.onFlag 48
      (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (tlsLong v) (copyBelow v) (splitFrom v) (fnStub "SeF") (fnStub "SpF")
        (fnStub "I") (fnStub "A") (fnStub "ToF") (fnStub "Fi") false)
      (Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp") (fnStub "I")
        (fnStub "A") (fnStub "To") (fnStub "Fi")))
    (sealGatherRPlain v) v.lvGA (sealGatherPreparedOut _)
    (gatherP_fill 48 _ _ _ _ _ _ _ _ _ _ _ _ hSeF hSpF hToF hSe hSp hI hA hTo hFi)
    v.one_le_lvGA (Nat.le_refl _) (ha := ha)

/-- `Spec.Gcm.sealGatherPreparedApi`'s function over `v` on 16 prepared powers
or the key context, as `sealGatherR_scrubbed`. -/
theorem sealGatherR16_scrubbed (v : GcmVariant) (r : R16 v) :
    VerifiedScrubbed target
      (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
        (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn true)
      (Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 5128) 0 := by
  have hl := Nat.le_trans v.lv_le_lvG v.lvG_le_lvGA
  have hSeF := calleeSide_mono hl (show 2624 ≤ gatherN "SeF" by decide) (sealCodeF_sides v).2
  have hSpF := calleeSide_mono (Nat.le_refl _) (show 2672 ≤ gatherN "SpF" by decide) (splitFnF16_side v r)
  have hToF := calleeSide_mono (Nat.le_refl _) (show 4856 ≤ gatherN "ToF" by decide) (toFnF16_side v)
  have hSe := calleeSide_mono hl (show 2624 ≤ gatherN "Se" by decide) (sealFn_side v)
  have hSp := calleeSide_mono v.lvG_le_lvGA (show 2672 ≤ gatherN "Sp" by decide) (splitFn_side v)
  have hI := calleeSide_mono hl (show 2576 ≤ gatherN "I" by decide) (initFn_side v)
  have hA := calleeSide_mono hl (show 2576 ≤ gatherN "A" by decide) (aadFn_side v)
  have hTo := calleeSide_mono v.lvG_le_lvGA (show 4856 ≤ gatherN "To" by decide) (toFn_side v)
  have hFi := calleeSide_mono hl (show 2584 ≤ gatherN "Fi" by decide) (finFn_side v)
  have fI := streamInitS_fill _ (callees_sideG v)
  have fA := streamAadS_fill _ (callees_sideG v)
  have fFi := streamFinishS_fill _ (callees_sideG v)
  have ha := gatherP16_stub ((v.stitch.bind (·.toPart)).map (·.name))
  rw [← tlsLong_eq, ← copyBelow_eq', ← splitFrom_eq'] at ha
  exact verifiedScrubbedAllFill (api := Spec.Gcm.sealGatherPreparedApi) (ks := 1) (n := gatherN) (rb := 0)
    (stack := 5128)
    (a := Impl.Gcm.X86_64.Flag.onFlag 16
      (Impl.AesGcm.X86_64.Fn.sealGatherCodeP (tlsLong v) (copyBelow v) (splitFrom v) (fnStub "SeF") (fnStub "SpF")
        initStub aadStub (fnStub "ToF") finStub true)
      (Impl.AesGcm.X86_64.Fn.sealGatherCode (copyBelow v) (splitFrom v) (fnStub "Se") (fnStub "Sp") (fnStub "I")
        (fnStub "A") (fnStub "To") (fnStub "Fi")))
    (sealGatherR16Plain v r) v.lvGA (sealGatherPreparedOut _)
    (gatherP16_fill 16 _ _ _ _ _ _ _ _ _ _ _ _ hSeF hSpF hToF hSe hSp hI hA hTo hFi fI fA fFi)
    v.one_le_lvGA (Nat.le_refl _) (ha := ha)

/-! ## What the registrations bind

Of each function as emitted over `v` (`Impl.AesGcm.X86_64.Fn`), on the key
context alone (`…W`), or by the flag on 48 prepared powers (`…R`), or by the
count on 16 (`…R16`, given `R16 v`), beside its theorem (`…_scrubbed`), the
registration (`Artifacts/AesGcm/X86_64.lean`) binds that its code writes the
stack pointer only in its frames and calls (`…_spSafeFn`). -/

/-- `sealPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames and
calls (the registration's `spSafe`). -/
theorem sealW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealWPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames and
calls (the registration's `spSafe`). -/
theorem openW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((openWPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames
and calls (the registration's `spSafe`). -/
theorem openToW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((openToWPlain v).spSafe)

/-- `streamEncryptPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem streamEncryptW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))

/-- `streamDecryptPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem streamDecryptW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl))

/-- `sealGatherPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem sealGatherW_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
            (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealGatherWPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames and
calls (the registration's `spSafe`). -/
theorem sealR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealRPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames and
calls (the registration's `spSafe`). -/
theorem openR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((openRPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`: its code writes the stack pointer only in its frames
and calls (the registration's `spSafe`). -/
theorem openToR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
            (openSplitFnB v v.ctrTo).fn).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (openToCodeR_onFlag_spAll v)

/-- `streamEncryptPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem streamEncryptR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (streamEncryptCodeF_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem streamDecryptR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (VG.X86_64.onFlag_spSafe
        (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
        (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`: its code writes the stack pointer only in its
frames and calls (the registration's `spSafe`). -/
theorem sealGatherR_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
            (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
            (aadFn v.impl).fn (finFn v.impl).fn false).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealGatherRPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack pointer
only in its frames and calls (the registration's `spSafe`). -/
theorem sealR16_spSafeFn (v : GcmVariant) (r : R16 v) :
    (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (sealBlkR16 v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealF16Plain v r).spSafe)

/-- `openPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack pointer
only in its frames and calls (the registration's `spSafe`). -/
theorem openR16_spSafeFn (v : GcmVariant) (r : R16 v) :
    (Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((openR16Plain v r).spSafe)

/-- `openToPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack
pointer only in its frames and calls (the registration's `spSafe`). -/
theorem openToR16_spSafeFn (v : GcmVariant) (r : R16 v) :
    (Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn
            (openSplitFnF16 v).fn (openSplitFnB v v.ctrTo).fn).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (openToCodeR16_onFlag_spAll v r)

/-- `streamEncryptPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack
pointer only in its frames and calls (the registration's `spSafe`). -/
theorem streamEncryptR16_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (streamEncryptCodeF16_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack
pointer only in its frames and calls (the registration's `spSafe`). -/
theorem streamDecryptR16_spSafeFn (v : GcmVariant) :
    (Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (VG.X86_64.onFlag_spSafe
        (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
        (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`, on 16 prepared powers: its code writes the stack
pointer only in its frames and calls (the registration's `spSafe`). -/
theorem sealGatherR16_spSafeFn (v : GcmVariant) (r : R16 v) :
    (Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
            (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
            (aadFn v.impl).fn (finFn v.impl).fn true).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ((sealGatherR16Plain v r).spSafe)

end VG.Proof.AesGcm.X86_64

/-! Stack, vector cleanup and control-register obligations of the direct gather entries. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.DirectGather
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.Gcm.X86_64.Flag (onFlag)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

abbrev baseCore (c : Callees) (ctr : Fn) := enter (general c ctr none)
abbrev readyCore (c : Callees) (ctr f : Fn) := dispatch (quick f) (general c ctr (some f))
abbrev baseStub := Finished (baseCore stub5 ctrToStub)
abbrev readyStub := Finished (readyCore stub5 ctrToStub (fnStub "B"))
abbrev rawStub := withStackArgScratch 2616 5 baseStub
abbrev flagStub (n : Nat) := onFlag n (withStackArgScratch 2616 5 readyStub) rawStub

private theorem fillBase {k : Nat} {c : Callees} {ctr : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 24=true) :
    Fill k (fun _ => 24) baseStub (Finished (baseCore c ctr)) := by
  obtain ⟨a,b,g,e,d⟩ := hs
  have ac := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) a
  have gh := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) g
  fill_calls_wide

private theorem fillReady {k : Nat} {c : Callees} {ctr f : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 24=true) (hf : calleeSide f.code k 24=true) :
    Fill k (fun _ => 24) readyStub (Finished (readyCore c ctr f)) := by
  obtain ⟨a,b,g,e,d⟩ := hs
  have ac := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) a
  have gh := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) g
  fill_calls_wide

private theorem sp_general (v : GcmImpl) (ctr : Fn) (f : Option Fn)
    (ht : ctr.code.all (fun i => !isa.writesSp i)=true)
    (hf : ∀ b∈f,b.code.all (fun i => !isa.writesSp i)=true) :
    (general v.callees ctr f).all (fun i => !isa.writesSp i)=true := by
  have a := seal_spSafe v
  simp only [Impl.AesGcm.X86_64.«seal»,Code.all,Bool.and_eq_true] at a
  obtain ⟨_,aa,_,_,⟨tg,_⟩,_⟩ := a
  have tail : (Impl.AesGcm.X86_64.cryptTailG v.callees true).all (fun i => !isa.writesSp i)=true := by
    simp only [Impl.AesGcm.X86_64.cryptTailG,Code.all,GcmImpl.callees,v.ctr.spSafe]
    decide +kernel
  cases f with
  | none =>
    simp only [general,pieces,Option.map_none,Option.getD_none,whole,Code.all,ht,aa,tg,tail,Bool.true_and,Bool.and_true]
    decide +kernel
  | some b =>
    have bf := hf b rfl
    simp only [general,pieces,Option.map_some,Option.getD_some,bulk,callSeal,whole,Code.all,bf,ht,aa,tg,tail,Bool.true_and,Bool.and_true]
    decide +kernel

private theorem baseStub_ok : stubCallee baseStub 0 (fun _=>24) 56 = true := by lit_decide
private theorem readyStub_ok : stubCallee readyStub 1 (fun _=>24) 56 = true := by lit_decide

private theorem of_side {p : Prog isa} {k : Nat} (sp : (Finished p).all (fun i => !isa.writesSp i)=true)
    (hc : calleeSide (Finished p) k 56=true) : CoreSafe p := by
  simp only [calleeSide,Bool.and_eq_true,decide_eq_true_eq] at hc
  refine ⟨sp,hc.1.1,?_⟩
  have both := (Code.allInstrs_eq _ _).symm.trans hc.1.2
  exact (Code.allInstrs_eq _ _).trans (List.all_eq_true.mpr (fun i hi => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp both i hi)).2))

theorem baseSafe (v : GcmImpl) (ctr : Fn) {k : Nat} (hs : CalleesSide k v.callees)
    (ht : calleeSide ctr.code k 24=true) (sp : ctr.code.all (fun i => !isa.writesSp i)=true) :
    CoreSafe (baseCore v.callees ctr) := by
  apply of_side _ (calleeSide_of_fill (fillBase hs ht) (Nat.zero_le _) baseStub_ok)
  have g := sp_general v ctr none sp (by simp)
  simp only [baseCore,enter,Code.all,g,Bool.and_true]
  decide +kernel

theorem preparedSafe (v : GcmImpl) (ctr f : Fn) {k : Nat} (hk : 1≤k) (hc : CalleesSide k v.callees)
    (ht : calleeSide ctr.code k 24=true) (hf : calleeSide f.code k 24=true)
    (sp : ctr.code.all (fun i => !isa.writesSp i)=true) (fp : f.code.all (fun i => !isa.writesSp i)=true) :
    CoreSafe (readyCore v.callees ctr f) := by
  apply of_side _ (calleeSide_of_fill (fillReady hc ht hf) hk readyStub_ok)
  have g := sp_general v ctr (some f) sp (fun b hb => (Option.mem_some_iff.mp hb) ▸ fp)
  have q : (quick f).all (fun i => !isa.writesSp i)=true := by
    simp only [quick,firstBlocks,callSeal,Code.all,fp,Bool.and_true]
    decide +kernel
  simp only [readyCore,dispatch,enter,Code.all,g,q,Bool.and_true]
  decide +kernel

private theorem frameFill {k : Nat} {a b : Prog isa} (f : Fill k (fun _=>24) a b) :
    Fill k (fun _=>24) (withStackArgScratch 2616 5 a) (withStackArgScratch 2616 5 b) :=
  .frame _ _ (.seq (.block _) f)

private theorem raw_ok : stubSide rawStub 0 (fun _=>24) 2672 []=true := by lit_decide
private theorem flag_ok {n : Nat} (hn : n=16 ∨ n=48) : stubSide (flagStub n) 1 (fun _=>24) 2672 []=true := by
  rcases hn with rfl|rfl <;> lit_decide

abbrev publicContract := Spec.Gcm.sealGatherPreparedApi.contract X86_64.abi 2672

theorem base_scrub {c : Callees} {ctr : Fn} (lv : VecLevel) (hs : CalleesSide lv.level c)
    (ct : calleeSide ctr.code lv.level 24=true)
    (verified : Verified target (plain c ctr) publicContract) (safe : CoreSafe (baseCore c ctr)) :
    VerifiedScrubbed target (scrubAll lv 0 2672 (plain c ctr)) publicContract 0 :=
  verifiedScrubbedAllFill (api:=Spec.Gcm.sealGatherPreparedApi)
    { suffix := "", code := plain c ctr, stack := 2672, verified := verified, spSafe := withStackArgScratch_spSafe safe.sp }
    lv (sealGatherPreparedOut _) (frameFill (fillBase hs ct)) (Nat.zero_le _) (Nat.le_refl _) (ha:=raw_ok)

theorem prepared_scrub {c : Callees} {ctr b : Fn} (lv : VecLevel) (hk : 1≤lv.level) {n : Nat} (hn : n=16 ∨ n=48)
    (hs : CalleesSide lv.level c) (ct : calleeSide ctr.code lv.level 24=true) (bt : calleeSide b.code lv.level 24=true)
    (verified : Verified target (onFlag n (prepared c ctr b) (plain c ctr)) publicContract)
    (rs : CoreSafe (readyCore c ctr b)) (ws : CoreSafe (baseCore c ctr)) :
    VerifiedScrubbed target (scrubAll lv 0 2672 (onFlag n (prepared c ctr b) (plain c ctr))) publicContract 0 := by
  have f := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag n))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) (frameFill (fillReady hs ct bt))) (frameFill (fillBase hs ct)))
  exact verifiedScrubbedAllFill (api:=Spec.Gcm.sealGatherPreparedApi)
    { suffix := "", code := onFlag n (prepared c ctr b) (plain c ctr), stack := 2672, verified := verified,
      spSafe := onFlag_spSafe (withStackArgScratch_spSafe rs.sp) (withStackArgScratch_spSafe ws.sp) }
    lv (sealGatherPreparedOut _) f hk (Nat.le_refl _) (ha:=flag_ok hn)

abbrev boundedCore (c : Callees) (ctr f : Fn) :=
  dispatch (withBounded (quick f)) (withBounded (general c ctr (some f)))
private abbrev boundedStub := Finished (boundedCore stub5 ctrToStub (fnStub "B"))

private theorem fillBounded {k : Nat} {c : Callees} {ctr f : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 24=true) (hf : calleeSide f.code k 24=true) :
    Fill k (fun _ => 24) boundedStub (Finished (boundedCore c ctr f)) := by
  obtain ⟨a,b,g,e,d⟩ := hs
  have ac := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) a
  have gh := calleeSide_mono (Nat.le_refl k) (show 8≤24 by decide) g
  repeat (any_goals (first
    | exact Fill.refl _
    | refine Fill.seq ?_ ?_
    | exact Fill.hole _ _ (by assumption)
    | refine Fill.ite _ ?_ ?_
    | refine Fill.loop _ ?_
    | refine Fill.call _ _ ?_
    | refine Fill.frame _ _ ?_))

private theorem boundedStub_ok : stubCallee boundedStub 2 (fun _=>24) 56 = true := by lit_decide
private theorem boundedFlag_ok :
    stubSide (onFlag 48 (withStackArgScratch 2616 5 boundedStub) rawStub) 2 (fun _=>24) 2672 []=true := by lit_decide

private theorem bounded_sp {p : Prog isa} (h : p.all (fun i => !isa.writesSp i)=true) :
    (withBounded p).all (fun i => !isa.writesSp i)=true := by
  simp only [withBounded, Code.all, h, Bool.true_and]
  decide +kernel

theorem boundedSafe (v : GcmImpl) (ctr f : Fn) {k : Nat} (hk : 2≤k) (hc : CalleesSide k v.callees)
    (ht : calleeSide ctr.code k 24=true) (hf : calleeSide f.code k 24=true)
    (sp : ctr.code.all (fun i => !isa.writesSp i)=true) (fp : f.code.all (fun i => !isa.writesSp i)=true) :
    CoreSafe (boundedCore v.callees ctr f) := by
  apply of_side _ (calleeSide_of_fill (fillBounded hc ht hf) hk boundedStub_ok)
  have g := bounded_sp (sp_general v ctr (some f) sp (fun b hb => (Option.mem_some_iff.mp hb) ▸ fp))
  have q : (quick f).all (fun i => !isa.writesSp i)=true := by
    simp only [quick,firstBlocks,callSeal,Code.all,fp,Bool.and_true]
    decide +kernel
  have bq := bounded_sp q
  simp only [boundedCore,dispatch,enter,Code.all,g,bq,Bool.and_true]
  decide +kernel

theorem bounded_scrub {c : Callees} {ctr b : Fn} (lv : VecLevel) (hk : 2≤lv.level)
    (hs : CalleesSide lv.level c) (ct : calleeSide ctr.code lv.level 24=true) (bt : calleeSide b.code lv.level 24=true)
    (verified : Verified target (onFlag 48 (preparedBounded c ctr b) (plain c ctr)) publicContract)
    (rs : CoreSafe (boundedCore c ctr b)) (ws : CoreSafe (baseCore c ctr)) :
    VerifiedScrubbed target (scrubAll lv 0 2672 (onFlag 48 (preparedBounded c ctr b) (plain c ctr))) publicContract 0 := by
  have f := Fill.seq (Fill.block (Impl.Gcm.X86_64.Flag.testFlag 48))
    (Fill.ite .ae (Fill.seq (Fill.seq (Fill.block []) (Fill.block [])) (frameFill (fillBounded hs ct bt))) (frameFill (fillBase hs ct)))
  exact verifiedScrubbedAllFill (api:=Spec.Gcm.sealGatherPreparedApi)
    { suffix := "", code := onFlag 48 (preparedBounded c ctr b) (plain c ctr), stack := 2672, verified := verified,
      spSafe := onFlag_spSafe (withStackArgScratch_spSafe rs.sp) (withStackArgScratch_spSafe ws.sp) }
    lv (sealGatherPreparedOut _) f hk (Nat.le_refl _) (ha:=boundedFlag_ok)

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Dispatch the verified gather entry to the bounded whole-record call or its existing bulk implementation. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather Short Layout VG.Impl.AesGcm.X86_64.DirectGather
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {s t u v : State} {fallback : Prog isa}

theorem Layout.withBounded_wp (p : Layout (CtxMode.flaggedT 48) s) (hf : ShortFacts) (e : Initial s u)
    (next : ∀ w, Initial s w → WP isa fallback w (BodyDone (CtxMode.flaggedT 48) s)) :
    WP isa (withBounded fallback) u (BodyDone (CtxMode.flaggedT 48) s) := by
  refine WP.seq (WP.mono (p.testBoth e) fun w h => WP.ite (decide ¬Eligible s) (by simp only [eval,h.2])
    (fun _ => next _ h.1) (fun ok => ?_))
  have good := Classical.not_not.mp (of_decide_eq_false ok)
  exact p.gather_wp hf (FitsCount.hasPair good.2) (IsShortAt.full good.1) h.1

theorem Layout.withBounded_rel (p : Layout (CtxMode.flaggedT 48) s) (q : Layout (CtxMode.flaggedT 48) t)
    (hf : ShortFacts) (pb : Pub s t) (e : Initial s u) (f : Initial t v)
    (next : ∀ x y, Initial s x → Initial t y → RelCT isa (fun a b => a=x ∧ b=y) fallback (fun _ _ => True)) :
    RelCT isa (fun a b => a=u ∧ b=v) (withBounded fallback) (fun _ _ => True) := by
  have check := (rel_next (p.testBoth_rel q pb) (fun _ h => p.testBoth h) (fun _ h => q.testBoth h)).mono
    (P':=fun a b => a=u ∧ b=v) (fun _ _ h => by obtain ⟨rfl,rfl⟩ := h; exact ⟨e,f⟩) (fun _ _ h => h)
  refine RelCT.seq check (rel_ite_e (fun _ _ h => by simp only [h.1.2,h.2.2,pubEligible pb]) ?_ ?_)
  · intro x y a b x' y' h ex ey
    exact next x y h.1.1.1 h.1.2.1 x y a b x' y' ⟨rfl,rfl⟩ ex ey
  · intro x y a b x' y' h ex ey
    have sh := Classical.not_not.mp (of_decide_eq_false (Option.some.inj (h.1.1.2.symm.trans h.2)))
    exact p.gather_rel q hf pb (FitsCount.hasPair sh.2) (IsShortAt.full sh.1) x y a b x' y' ⟨h.1.1.1,h.1.2.1⟩ ex ey

theorem bounded_rounds (hf : ShortFacts) {c : Callees} {ctr : Fn} (T : BlocksTo.SealFn (CtxMode.flaggedT 48))
    (h : InitializedProof (CtxMode.flaggedT 48) (general c ctr (some T.fn)))
    (safe : CoreSafe (dispatch (withBounded (quick T.fn)) (withBounded (general c ctr (some T.fn))))) :
    Verified X86_64.target (preparedBounded c ctr T.fn) (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract 48 X86_64.abi 2672) :=
  ready_framed (by decide)
    (fun p => p.dispatch_wp (fun _ e g => p.withBounded_wp hf e (fun _ ex => p.quick_wp hf T (by decide) ex g))
      (fun _ e => p.withBounded_wp hf e (fun _ ex => h.run p ex)))
    (fun p q pb => p.dispatch_rel q pb (fun _ _ e f g => p.withBounded_rel q hf pb e f
      (fun _ _ ex fx => p.quick_rel q hf T (by decide) pb ex fx g)) (fun _ _ e f =>
        p.withBounded_rel q hf pb e f (fun _ _ ex fx => h.rel p q pb ex fx))) safe

end VG.Proof.AesGcm.X86_64.DirectGather

/-! Instantiate direct gather sealing for the key-only, 16-power and 48-power callers. -/
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.AesGcm.X86_64.DirectGather (general directBase directPrepared directSeal)
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

abbrev ctrFn (v : GcmVariant) : Fn := ⟨v.ctrTo.callee.name,v.ctrTo.callee.code⟩
abbrev PlainOk (v : GcmVariant) :=
  InitializedProof CtxMode.base (general v.impl.callees (ctrFn v) none)
abbrev ReadyOk (v : GcmVariant) {n : Nat} (b : BlocksTo.SealFn (CtxMode.flaggedT n)) :=
  InitializedProof (CtxMode.flaggedT n) (general v.impl.callees (ctrFn v) (some b.fn))

private theorem generalProof (v : GcmVariant) {M : CtxMode} {f : Option Fn}
    (wp : PrefixWP M f) (ct : PrefixCT M f) :
    InitializedProof M (general v.impl.callees (ctrFn v) f) where
  run := general_wp v.impl v.ctrTo wp
  rel := general_rel v.impl v.ctrTo wp ct

theorem plainProof (v : GcmVariant) : PlainOk v :=
  generalProof v plainPrefix_wp plainPrefix_rel

theorem readyProof (v : GcmVariant) {n : Nat} (b : BlocksTo.SealFn (CtxMode.flaggedT n)) : ReadyOk v b :=
  generalProof v (bulkPrefix_wp b) (bulkPrefix_rel b)

theorem ctr_side (v : GcmVariant) :
    calleeSide (ctrFn v).code v.lvTW.level 24 = true :=
  calleeSide_mono (level_join_right _ _) (Nat.zero_le _) v.ctrTo.side

theorem plain_safe (v : GcmVariant) : CoreSafe (baseCore v.impl.callees (ctrFn v)) :=
  baseSafe v.impl (ctrFn v) (callees_sideTW v) (ctr_side v) v.ctrTo.spSafe

/-- The key-context-only gather clears the stack and registers used by its counter backend. -/
theorem base_verified (v : GcmVariant) :
    VerifiedScrubbed target (directBase v.lvTW v.impl.callees (ctrFn v)) publicContract 0 :=
  base_scrub v.lvTW (callees_sideTW v) (ctr_side v)
    (plain_public (plain_rounds (plainProof v) (plain_safe v))) (plain_safe v)

theorem base_spSafe (v : GcmVariant) :
    (directBase v.lvTW v.impl.callees (ctrFn v)).all (fun i => !isa.writesSp i)=true :=
  scrubKs_spSafe (withStackArgScratch_spSafe (plain_safe v).sp)

theorem lvG_le_T (v : GcmVariant) : v.lvG.level ≤ v.lvT.level := by
  exact join_mono_left _ (join_mono_left _ v.lv_le_lvA)

private theorem ready_safe (v : GcmVariant) {n : Nat} (b : BlocksTo.SealFn (CtxMode.flaggedT n))
    (bt : calleeSide b.fn.code v.lvG.level 24=true) : CoreSafe (readyCore v.impl.callees (ctrFn v) b.fn) :=
  preparedSafe v.impl (ctrFn v) b.fn v.one_le_lvT (callees_sideT v)
    (calleeSide_mono v.lvTW_le_lvT (Nat.le_refl _) (ctr_side v))
    (calleeSide_mono (lvG_le_T v) (Nat.le_refl _) bt) v.ctrTo.spSafe b.spAll

/-- A prepared context can use the fixed-shape and general direct entries; both preserve its public contract. -/
theorem prepared_verified (v : GcmVariant) (n : Nat) (hn : n=16 ∨ n=48) (b : BlocksTo.SealFn (CtxMode.flaggedT n))
    (bt : calleeSide b.fn.code v.lvG.level 24=true) :
    VerifiedScrubbed target (directPrepared v.lvT n v.impl.callees (ctrFn v) b.fn) publicContract 0 := by
  have ht : 16≤n ∧ n≤48 := by rcases hn with rfl|rfl <;> decide
  have cs := calleeSide_mono v.lvTW_le_lvT (Nat.le_refl _) (ctr_side v)
  have bs := calleeSide_mono (lvG_le_T v) (Nat.le_refl _) bt
  have ws := plain_safe v
  have rs := ready_safe v b bt
  exact prepared_scrub v.lvT v.one_le_lvT hn (callees_sideT v) cs bs (prepared_public hn
    (prepared_rounds ht.1 ht.2 Short.shortFacts b (readyProof v b) rs) (plain_rounds (plainProof v) ws)) rs ws

theorem prepared_spSafe (v : GcmVariant) (n : Nat) (b : BlocksTo.SealFn (CtxMode.flaggedT n))
    (bt : calleeSide b.fn.code v.lvG.level 24=true) :
    (directPrepared v.lvT n v.impl.callees (ctrFn v) b.fn).all (fun i => !isa.writesSp i)=true :=
  scrubKs_spSafe (onFlag_spSafe (withStackArgScratch_spSafe (ready_safe v b bt).sp)
    (withStackArgScratch_spSafe (plain_safe v).sp))

theorem selected_verified (v : GcmVariant) (n : Nat) (hn : n=16 ∨ n=48)
    (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT n)))
    (side : ∀ b ∈ leaf, calleeSide b.fn.code v.lvG.level 24 = true) :
    VerifiedScrubbed target (directSeal v.lvTW v.lvT n v.impl.callees (ctrFn v) (leaf.map (·.fn))) publicContract 0 := by
  cases leaf with
  | none => exact base_verified v
  | some b => exact prepared_verified v n hn b (side b (by simp))

theorem selected_spSafe (v : GcmVariant) (n : Nat) (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT n)))
    (side : ∀ b ∈ leaf, calleeSide b.fn.code v.lvG.level 24 = true) :
    (directSeal v.lvTW v.lvT n v.impl.callees (ctrFn v) (leaf.map (·.fn))).all (fun i => !isa.writesSp i)=true := by
  cases leaf with
  | none => exact base_spSafe v
  | some b => exact prepared_spSafe v n b (side b (by simp))

open VG.Impl.AesGcm.X86_64.DirectGather (directSeal48)

theorem boundedSelected (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (VG.Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    let code := Impl.AesGcm.X86_64.DirectGather.directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (DirectGather.ctrFn v) (leaf.map (·.fn))
    VerifiedScrubbed X86_64.target code DirectGather.publicContract 0 ∧ code.all (fun i => !X86_64.isa.writesSp i)=true := by
  dsimp only
  cases leaf with
  | none => exact ⟨DirectGather.base_verified v,DirectGather.base_spSafe v⟩
  | some b =>
    have bt := side b (by simp)
    simp only [Option.map_some, Impl.AesGcm.X86_64.DirectGather.directSeal48]
    split
    · next eligible =>
      have level : 2≤v.lvT.level := by rw [eligible.2]; decide
      have cs := X86_64.Scrub.calleeSide_mono v.lvTW_le_lvT (Nat.le_refl _) (DirectGather.ctr_side v)
      have bs := X86_64.Scrub.calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _) bt
      have ws := DirectGather.plain_safe v
      have rs := DirectGather.boundedSafe v.impl (DirectGather.ctrFn v) b.fn level (callees_sideT v) cs bs v.ctrTo.spSafe b.spAll
      exact ⟨DirectGather.bounded_scrub v.lvT level (callees_sideT v) cs bs (DirectGather.prepared_public (.inr rfl)
        (DirectGather.bounded_rounds Short.shortFacts b (DirectGather.readyProof v b) rs)
        (DirectGather.plain_rounds (DirectGather.plainProof v) ws)) rs ws,
        X86_64.Scrub.scrubKs_spSafe (X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe rs.sp)
          (X86_64.withStackArgScratch_spSafe ws.sp))⟩
    · exact ⟨DirectGather.prepared_verified v 48 (.inr rfl) b bt,DirectGather.prepared_spSafe v 48 b bt⟩

theorem bounded_selected_verified (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    VerifiedScrubbed X86_64.target (directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (ctrFn v) (leaf.map (·.fn))) publicContract 0 :=
  (boundedSelected v leaf side).1

theorem bounded_selected_spSafe (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    (directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (ctrFn v) (leaf.map (·.fn))).all (fun i => !isa.writesSp i)=true :=
  (boundedSelected v leaf side).2

end VG.Proof.AesGcm.X86_64.DirectGather

namespace VG.Proof.AesGcm.X86_64.ContiguousSeal
open VG VG.X86_64 VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.Contiguous

abbrev allowance := fun (_ : String) => 8

private theorem fillBody {k : Nat} {c : Callees} (hs : CalleesSide k c)
    {sk ker : Prog isa} (fk : Fill k allowance sk ker) (vec wide prep : Bool) :
    Fill k allowance (core (body stub5 vec wide prep sk)) (core (body c vec wide prep ker)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  cases vec <;> cases wide <;> cases prep <;>
    repeat (any_goals (first
      | exact Fill.refl _
      | exact fk
      | refine Fill.seq ?_ ?_
      | exact Fill.hole _ _ (by assumption)
      | refine Fill.ite _ ?_ ?_
      | refine Fill.loop _ ?_
      | refine Fill.call _ _ ?_
      | refine Fill.frame _ _ ?_))

private theorem fillDeferred {k : Nat} {c : Callees} {ctr : Fn} (hs : CalleesSide k c)
    (ht : calleeSide ctr.code k 8=true) :
    Fill k allowance (core (deferredBody stub5 ctrToStub)) (core (deferredBody c ctr)) := by
  obtain ⟨hc,_,hg,_,_⟩ := hs
  fill_calls_wide

private theorem fillSeparate {k : Nat} {ctr gh : Fn} (ct : calleeSide ctr.code k 8=true)
    (hg : calleeSide gh.code k 8=true) :
    Fill k allowance (separate ctrToStub stub5.gh) (separate ctr gh) := by fill_calls_wide

private theorem fillFused {k : Nat} {f : Fn} (hf : calleeSide f.code k 8 = true) :
    Fill k allowance (fused (fnStub "B")) (fused f) := by fill_calls_wide

private theorem frameFill {k : Nat} {r s : Prog isa} (f : Fill k allowance (core r) (core s)) :
    Fill k allowance (framed r) (framed s) := .frame _ _ (.seq (.block _) f)

theorem selectedFill {k : Nat} {c : Callees} {ctr : Fn} {blocks : Option Fn}
    (defer wide : Bool) (n : Nat) (hs : CalleesSide k c) (ct : calleeSide ctr.code k 8=true)
    (hb : ∀ f∈blocks, calleeSide f.code k 8=true) :
    Fill k allowance (selected defer wide n stub5 ctrToStub (blocks.map fun _ => fnStub "B"))
      (selected defer wide n c ctr blocks) := by
  cases blocks with
  | none =>
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) false wide false)
    · exact frameFill (fillDeferred hs ct)
  | some f =>
    have ready := frameFill (fillBody hs (fillFused (hb f rfl)) true wide true)
    refine .seq (.block _) (.ite _ (.seq (.seq (.block _) (.block _)) ready) ?_)
    cases defer
    · exact frameFill (fillBody hs (fillSeparate ct hs.gh) true wide false)
    · exact frameFill (fillDeferred hs ct)

theorem plainSide (defer : Bool) :
    stubSide (selected defer false 16 stub5 ctrToStub none) 0 allowance 2640 []=true := by
  cases defer <;> lit_decide

theorem vectorSide (wide : Bool) :
    stubSide (selected false wide (if wide then 48 else 16) stub5 ctrToStub (some (fnStub "B")))
      (if wide then 2 else 1) allowance 2640 []=true := by
  cases wide <;> lit_decide

private theorem spParts (v : GcmImpl) :
    Sp (Impl.AesGcm.X86_64.oneAad v.callees) ∧ Sp (Impl.AesGcm.X86_64.cryptTailG v.callees true) ∧
    Sp (Impl.AesGcm.X86_64.oneTag v.callees 0) := by
  have a := seal_spSafe v
  simp only [Impl.AesGcm.X86_64.«seal»,Code.all,Bool.and_eq_true] at a
  obtain ⟨_,aa,_,_,⟨tg,_⟩,_⟩ := a
  refine ⟨aa,?_,tg⟩
  simp only [Sp,Impl.AesGcm.X86_64.cryptTailG,Code.all,GcmImpl.callees,v.ctr.spSafe]
  decide +kernel

private theorem spBody (v : GcmImpl) {p : Prog isa} (hp : Sp p) (vec wide prep : Bool) :
    Sp (core (body v.callees vec wide prep p)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  cases vec <;> cases wide <;> cases prep <;>
    simp only [core,body,aad,bulk,finishScalar,Code.all,hp,aa,tail,tg,Bool.true_and,Bool.and_true,ite_true,ite_false,
      Bool.false_eq_true,Bool.false_and] <;> decide +kernel

private theorem spDeferred (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) :
    Sp (core (deferredBody v.callees ctr)) := by
  obtain ⟨aa,tail,tg⟩ := spParts v
  unfold Sp at *
  simp only [Impl.AesGcm.X86_64.oneTag,Code.all,Bool.and_eq_true] at tg
  simp only [core,deferredBody,bulk,Impl.AesGcm.X86_64.Contiguous.call,Code.all,ct,aa,tail,tg.2,Bool.true_and,Bool.and_true]
  decide +kernel

private theorem rawSafe {r : Prog isa} {k : Nat} (sp : Sp (core r)) (h : calleeSide (core r) k 24=true) :
    CoreSafe r := by
  simp only [calleeSide,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨sp,h.1.1,?_⟩
  have both := (Code.allInstrs_eq _ _).symm.trans h.1.2
  exact (Code.allInstrs_eq _ _).trans (List.all_eq_true.mpr fun i hi =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp both i hi)).2)

private theorem separateCoreSide (vec wide : Bool) :
    stubCallee (core (body stub5 vec wide false (separate ctrToStub stub5.gh)))
      (if vec then (if wide then 2 else 1) else 0) allowance 24=true := by
  cases vec <;> cases wide <;> lit_decide

private theorem fusedCoreSide (wide : Bool) :
    stubCallee (core (body stub5 true wide true (fused (fnStub "B"))))
      (if wide then 2 else 1) allowance 24=true := by cases wide <;> lit_decide

private theorem delayedCoreSide :
    stubCallee (core (deferredBody stub5 ctrToStub)) 0 allowance 24=true := by lit_decide

private theorem separateSp (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) : Sp (separate ctr v.callees.gh) := by
  simp only [Sp,separate,Impl.AesGcm.X86_64.Contiguous.call,Code.all,GcmImpl.callees,v.gh.spSafe,ct,Bool.true_and,Bool.and_true]
  decide +kernel

private theorem fusedSp {f : Fn} (h : Sp f.code) : Sp (fused f) := by
  simp only [Sp,fused,Impl.AesGcm.X86_64.Contiguous.call,Code.all,h,Bool.and_true]
  decide +kernel

theorem separateSafe (v : GcmImpl) (vec wide : Bool) {ctr : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hc : calleeSide ctr.code k 8=true) (sp : Sp ctr.code) (hk : (if vec then (if wide then 2 else 1) else 0)≤k) :
    CoreSafe (body v.callees vec wide false (separate ctr v.callees.gh)) :=
  rawSafe (spBody v (separateSp v sp) vec wide false)
    (calleeSide_of_fill (fillBody hs (fillSeparate hc hs.gh) vec wide false) hk (separateCoreSide vec wide))

theorem fusedSafe (v : GcmImpl) (wide : Bool) {f : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hf : calleeSide f.code k 8=true) (sp : Sp f.code) (hk : (if wide then 2 else 1)≤k) :
    CoreSafe (body v.callees true wide true (fused f)) :=
  rawSafe (spBody v (fusedSp sp) true wide true)
    (calleeSide_of_fill (fillBody hs (fillFused hf) true wide true) hk (fusedCoreSide wide))

theorem delayedSafe (v : GcmImpl) {ctr : Fn} {k : Nat} (hs : CalleesSide k v.callees)
    (hc : calleeSide ctr.code k 8=true) (sp : Sp ctr.code) : CoreSafe (deferredBody v.callees ctr) :=
  rawSafe (spDeferred v sp) (calleeSide_of_fill (fillDeferred hs hc) (Nat.zero_le _) delayedCoreSide)

theorem selectedSp (v : GcmImpl) {ctr : Fn} (defer wide : Bool) (n : Nat) {b : Option Fn}
    (ct : Sp ctr.code) (hb : ∀ f∈b, Sp f.code) : Sp (selected defer wide n v.callees ctr b) := by
  have base (vec : Bool) : Sp (if defer then framed (deferredBody v.callees ctr) else one v.callees vec wide false (separate ctr v.callees.gh)) := by
    cases defer
    · exact withStackArgScratch_spSafe (spBody v (separateSp v ct) vec wide false)
    · exact withStackArgScratch_spSafe (spDeferred v ct)
  cases b with
  | none => exact base false
  | some f =>
    exact onFlag_spSafe (withStackArgScratch_spSafe (spBody v (fusedSp (hb f rfl)) true wide true)) (base true)

open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open DirectGather (ctrFn)

theorem plainProof (v : GcmVariant) (defer vec wide : Bool) {k : Nat} (backend : v.lvTW.level≤k)
    (level : (if vec then (if wide then 2 else 1) else 0)≤k) {M : CtxMode} :
    RecordProof M (if defer then deferredBody v.impl.callees (ctrFn v) else
      body v.impl.callees vec wide false (separate (ctrFn v) v.impl.callees.gh)) := by
  have side : calleeSide (ctrFn v).code k 8=true :=
    calleeSide_mono (Nat.le_trans (level_join_right _ _) backend) (Nat.zero_le _) v.ctrTo.side
  cases defer
  · have bulk : BulkOk M (Impl.AesGcm.X86_64.Contiguous.bulk (separate (ctrFn v) v.impl.callees.gh)) :=
      fun h o a b c => separate_bulk_ok v.ctrTo v.impl.gh h o a b c
    exact ⟨plain_ok Short.shortFacts v.impl vec wide _ bulk,plain_ct Short.shortFacts v.impl vec wide bulk
      (separate_ct v.ctrTo v.impl.gh) (separate_keeps v.ctrTo v.impl.gh),
      separateSafe v.impl vec wide ((callees_sideTW v).mono backend) side v.ctrTo.spSafe level⟩
  · exact ⟨deferred_ok v.impl v.ctrTo,deferred_ct v.impl v.ctrTo,
      delayedSafe v.impl ((callees_sideTW v).mono backend) side v.ctrTo.spSafe⟩

private theorem preparedProof {np : Nat} {hn : 8≤np ∧ np≤24} (v : GcmVariant) (wide : Bool)
    (leaf : BlocksTo.SealFn (CtxMode.preparedN np hn))
    (pow : wide → Short.PowOk (CtxMode.preparedN np hn) Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP)
    (side : calleeSide leaf.fn.code v.lvT.level 8=true) (level : (if wide then 2 else 1)≤v.lvT.level) :
    RecordProof (CtxMode.preparedN np hn) (body v.impl.callees true wide true (fused leaf.fn)) := by
  have bulk : BulkOk _ (Impl.AesGcm.X86_64.Contiguous.bulk (fused leaf.fn)) := fun h o a b c => fused_bulk_ok leaf h o a b c
  exact ⟨prepared_ok Short.shortFacts v.impl wide pow _ bulk,prepared_ct Short.shortFacts v.impl wide pow
    (fun _ => Short.powersP_ct) bulk (fused_ct leaf) (fused_keeps leaf),fusedSafe v.impl wide (callees_sideT v)
    side leaf.spAll level⟩

theorem ready16Proof (v : GcmVariant) {leaf} (selected : leaf∈sealLeafR16 v) (level : 1≤v.lvT.level) :
    RecordProof CtxMode.prepared16 (body v.impl.callees true false true (fused leaf.fn)) :=
  preparedProof v false leaf (fun h => Bool.noConfusion h) (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ selected)) level

theorem ready48Proof (v : GcmVariant) {leaf} (selected : leaf∈sealLeafR v) (level : 2≤v.lvT.level) :
    RecordProof CtxMode.prepared (body v.impl.callees true true true (fused leaf.fn)) :=
  preparedProof v true leaf (fun _ => Short.powOk_powersP) (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ selected)) level


open VG.Spec.Gcm
open VG.X86_64.Scrub
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Impl.AesGcm.X86_64.Contiguous
open DirectGather (ctrFn)

abbrev Certificate (code : Prog isa) := VerifiedScrubbed target code apiContract 0 ∧ Sp code

theorem verified {code : Prog isa} (p : Certificate code) : VerifiedScrubbed target code apiContract 0 := p.1

theorem spSafe {code : Prog isa} (p : Certificate code) : Sp code := p.2

/-- One unstitched record, sealed from either source layout. Both legacy
AES-NI backends can defer GHASH until the ciphertext is complete. -/
theorem unstitched (v : GcmVariant) (defer : Bool) : Certificate
    (prepared v.lvTW defer false 16 v.impl.callees (ctrFn v) none) := by
  have p := plainProof (M:=CtxMode.base) v defer false false (Nat.le_refl _) (Nat.zero_le _)
  have raw := plainPublic (framedVerified (P:=preparedP) p preparedLocal (fun h => ⟨h.1,trivial⟩) prepInhabited)
  have h : Verified target (selected defer false 16 v.impl.callees (ctrFn v) none) apiContract := by
    cases defer <;> exact raw
  have sp := selectedSp v.impl (ctr:=ctrFn v) (b:=none) defer false 16 v.ctrTo.spSafe (fun _ h => nomatch h)
  have ct : calleeSide (ctrFn v).code v.lvTW.level 8=true := calleeSide_mono (level_join_right _ _) (show 0≤8 by decide) v.ctrTo.side
  exact ⟨verifiedScrubbedAllFill (api:=sealContiguousPreparedApi)
    {suffix:="",code:=_,stack:=2640,verified:=h,spSafe:=sp} v.lvTW outputLocal
    (selectedFill (ctr:=ctrFn v) (blocks:=none) defer false 16 (callees_sideTW v) ct (fun _ mem => nomatch mem))
    (Nat.zero_le _) (Nat.le_refl _) (ha:=plainSide defer),scrubKs_spSafe sp⟩

private theorem masksFill (narrow : Bool) {k : Nat} {c : Callees} {ctr enc : Fn} (hs : CalleesSide k c)
    (ct : calleeSide ctr.code k 8=true) (aes : calleeSide enc.code k 8=true) :
    Fill k allowance (core (softwareBody narrow stub5 ctrToStub (fnStub "aes"))) (core (softwareBody narrow c ctr enc)) := by
  let gh (o : Nat) : Fill k allowance (Impl.AesGcm.X86_64.ghash1 stub5 o .r15 96) (Impl.AesGcm.X86_64.ghash1 c o .r15 96) :=
    .seq (.block _) (.hole _ _ hs.gh)
  let len (o : Nat) : Fill k allowance (Impl.AesGcm.X86_64.lens stub5 o) (Impl.AesGcm.X86_64.lens c o) :=
    .seq (.block _) (gh o)
  let pad (o : Nat) : Fill k allowance (Impl.AesGcm.X86_64.absorbPad stub5 o) (Impl.AesGcm.X86_64.absorbPad c o) :=
    .seq (.seq (.block _) (.ite _ (.block _) (.seq (.block _) (.hole _ _ hs.gh))))
      (.seq (.block _) (.ite _ (.block _) (.seq (.block _) (.seq (.refl _) (gh o)))))
  have nonce : Fill k allowance (Impl.AesGcm.X86_64.j0 stub5) (Impl.AesGcm.X86_64.j0 c) :=
    .seq (.block _) (.seq (.ite _ (.block _) (.seq (.block _) (.seq (pad 0) (.seq (.block _) (len 0))))) (.block _))
  have kernel := fillSeparate ct hs.gh
  refine Fill.seq (.block _) (.seq ?_ (.refl _))
  have batch : Fill k allowance (batchMasks stub5 (fnStub "aes")) (batchMasks c enc) :=
    .seq (.seq (.block _) (.seq (.refl _) (.seq (.block _) (.hole _ _ aes)))) (.seq (.refl _)
      (.seq (.block _) (.seq (.hole _ _ hs.gh) (.seq (.block _) (.seq (len 16) (.block _))))))
  refine Fill.seq (.seq nonce (.seq (.block _) (pad 16))) (.seq (.block _) (.ite _ batch
    (.seq (.seq (.block _) (.ite _ (.block _) (.seq kernel (.block _)))) ?_)))
  have masks : Fill k allowance (finishMasks stub5 (fnStub "aes")) (finishMasks c enc) :=
    .seq (.block _) (.seq (.seq (.block _) (.hole _ _ aes)) (.seq (.refl _)
    (.seq (.block _) (.seq (pad 16) (.seq (.block _) (.seq (len 16) (.block _)))))))
  have one : Fill k allowance (alignedTag stub5 (fnStub "aes")) (alignedTag c enc) :=
    .seq (.block _) (.seq (len 16) (.seq (.seq (.block _) (.hole _ _ aes)) (.block _)))
  exact .seq (.block _) (.ite _ one masks)

private theorem masksCoreSide (narrow : Bool) :
    stubCallee (core (softwareBody narrow stub5 ctrToStub (fnStub "aes"))) 0 allowance 24=true := by cases narrow <;> lit_decide

private theorem masksSide (narrow : Bool) :
    stubSide (framed (softwareBody narrow stub5 ctrToStub (fnStub "aes"))) 0 allowance 2640 []=true := by cases narrow <;> lit_decide

private theorem spMasks (narrow : Bool) (v : GcmImpl) {ctr : Fn} (ct : Sp ctr.code) : Sp (core (softwareBody narrow v.callees ctr maskAES)) := by
  obtain ⟨aa,_,tag⟩ := spParts v
  have sep := separateSp (ctr:=ctr) v ct
  have enc : Sp maskAES.code := Proof.Aes.X86_64.BlocksImpl.scalar.encSpSafe
  have gh : Sp v.callees.gh.code := v.gh.spSafe
  unfold Sp at *
  simp only [Impl.AesGcm.X86_64.oneTag,Impl.AesGcm.X86_64.tag,Code.all,Bool.and_eq_true] at tag
  have pad := tag.2.1
  have lens := tag.2.2.2.1
  simp only [core,softwareBody,chooseBatch,batchMasks,batchKeys,batchText,batchAuth,gh,maskFinish,maskChoice,alignedTag,directEcbTag,VG.Impl.AesGcm.X86_64.Contiguous.oneMask,bulk,finishMasks,VG.Impl.AesGcm.X86_64.Contiguous.makeMasks,VG.Impl.AesGcm.X86_64.Contiguous.call,
    VG.Impl.AesGcm.X86_64.Contiguous.maskXor,maskAuth,Code.all,aa,sep,enc,pad,lens,Bool.true_and,Bool.and_true]
  cases narrow <;> decide +kernel

/-- The software AES backends share one bounded counter batch for both layouts. -/
theorem masks (narrow : Bool) (v : GcmVariant) : Certificate (preparedMasks narrow v.lvTW v.impl.callees (ctrFn v)) := by
  let ctr := ctrFn v
  have hc : calleeSide ctr.code v.lvTW.level 8=true :=
    calleeSide_mono (level_join_right _ _) (show 0≤8 by decide) v.ctrTo.side
  have enc : calleeSide maskAES.code v.lvTW.level 8=true :=
    calleeSide_mono (Nat.zero_le _) (show 0≤8 by decide) Proof.Aes.X86_64.BlocksImpl.scalar.encSide
  have fill := masksFill narrow (callees_sideTW v) hc enc
  have sp := spMasks narrow (ctr:=ctr) v.impl v.ctrTo.spSafe
  have safe := rawSafe sp (calleeSide_of_fill fill (Nat.zero_le _) (masksCoreSide narrow))
  have p : RecordProof CtxMode.base (softwareBody narrow v.impl.callees ctr maskAES) :=
    ⟨softwareRecord_ok narrow v.impl v.ctrTo,softwareRecord_ct narrow v.impl v.ctrTo,safe⟩
  have raw := plainPublic (framedVerified (P:=preparedP) p preparedLocal (fun h => ⟨h.1,trivial⟩) prepInhabited)
  have wrapper : Sp (framed (softwareBody narrow v.impl.callees ctr maskAES)) := withStackArgScratch_spSafe sp
  exact ⟨verifiedScrubbedAllFill (api:=sealContiguousPreparedApi)
    {suffix:="",code:=_,stack:=2640,verified:=raw,spSafe:=wrapper} v.lvTW outputLocal (frameFill fill)
    (Nat.zero_le _) (Nat.le_refl _) (ha:=masksSide narrow),scrubKs_spSafe wrapper⟩

private theorem stitched {M : CtxMode} (v : GcmVariant) (wide : Bool) (leaf : BlocksTo.SealFn M)
    (level : (if wide then 2 else 1)≤v.lvT.level)
    (side : calleeSide leaf.fn.code v.lvT.level 8=true)
    (p : RecordProof M (body v.impl.callees true wide true (fused leaf.fn)))
    (input : ∀ {k r m}, powerP (if wide then 48 else 16) k r m → plainP k r m ∧ M.ok m k) :
    Certificate (prepared v.lvT false wide (if wide then 48 else 16) v.impl.callees (ctrFn v) (some leaf.fn)) := by
  let n : Nat := if wide then 48 else 16
  have hn : n=16 ∨ n=48 := by cases wide <;> decide
  have hn' : n≤48 := by cases hn <;> omega
  have ready := framedVerified (P:=powerP n) p (powersLocal n) input (powerInhabited hn')
  have plain := framedVerified (P:=preparedP) (plainProof (M:=CtxMode.base) v false true wide v.lvTW_le_lvT level)
    preparedLocal (fun h => ⟨h.1,trivial⟩) prepInhabited
  have h := onPowers hn ready plain
  have sp := selectedSp v.impl (ctr:=ctrFn v) (b:=some leaf.fn) false wide n v.ctrTo.spSafe (by
    intro f hf; obtain rfl : leaf.fn=f := Option.mem_some_iff.mp hf; exact leaf.spAll)
  have ct : calleeSide (ctrFn v).code v.lvT.level 8=true := calleeSide_mono (Nat.le_trans (level_join_right _ _) v.lvTW_le_lvT) (show 0≤8 by decide) v.ctrTo.side
  exact ⟨verifiedScrubbedAllFill (api:=sealContiguousPreparedApi)
    {suffix:="",code:=_,stack:=2640,verified:=h,spSafe:=sp} v.lvT outputLocal
    (selectedFill (ctr:=ctrFn v) (blocks:=some leaf.fn) false wide n (callees_sideT v) ct (by
      intro f hf; obtain rfl : leaf.fn=f := Option.mem_some_iff.mp hf; exact side))
    level (Nat.le_refl _) (ha:=vectorSide wide),scrubKs_spSafe sp⟩

theorem stitched16 (v : GcmVariant) {b} (hb : b∈sealLeafR16 v) : Certificate
    (prepared v.lvT false false 16 v.impl.callees (ctrFn v) (some b.fn)) :=
  stitched v false b v.one_le_lvT (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ hb)) (ready16Proof v hb v.one_le_lvT)
    (fun h => ⟨h.1,h.2.2.1 h.2.1⟩)

theorem stitched48 (v : GcmVariant) {b} (hb : b∈sealLeafR v) (level : 2≤v.lvT.level) : Certificate
    (prepared v.lvT false true 48 v.impl.callees (ctrFn v) (some b.fn)) :=
  stitched v true b level (calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _)
    (selectSealLeaf_side v _ _ _ _ _ hb)) (ready48Proof v hb level)
    (fun h => ⟨h.1,h.2.2.2 h.2.1⟩)

end VG.Proof.AesGcm.X86_64.ContiguousSeal
