module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Prepared
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher

/-!
# AES-GCM's key setup on x86-64, without secret residue

`vg_aes_gcm_init` over an implementation of `vg_aes_ctr32` that needs no
working space (`Aes.X86_64.Ctr32Impl.free`), with `vg_aes_expand_key_scratch_aesni`,
which needs none either, in a frame of only the 176 bytes it writes itself
(`initF_framed`), followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives its residue
analysis (`Aes.X86_64.Ctr32Impl.gcmInitRes`, on `Aes.X86_64.gcmInitCodeF`).
Over the others, as before, in a frame of 2.5 KB, of which the analysis
cannot tell what may hold secrets. Its postcondition reads the memory on
return only within the key context, for a key of the lengths the
precondition allows (`X86_64.Scrub.PostOut`). `vg_aes_gcm_stream_init` and
`vg_aes_gcm_stream_aad` are not here, though the analysis handles them:
`vg_aes_gcm_seal_gather_prepared` calls them by name, with their code as it is.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.AesGcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl gcmInitCodeF)

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega)

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega)
  simpa using this

end

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract X86_64.abi stack) (Spec.Gcm.initSig.retBits 64) :=
  Proof.Aes.X86_64.Scrub.postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Gcm.KeyRepr m₁ ctx _ at h
      change Spec.Gcm.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

/-! ## `vg_aes_gcm_init` -/

/-- The implementations `vg_aes_gcm_init` calls with `c`: `c`, the key
expansion for the same CPUs, and no GHASH (as the registration file's). -/
def gcmOf (c : Ctr32Impl) : GcmImpl :=
  { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni,
    gh := GhashName.scalar.impl }

/-- With `vg_aes_expand_key_scratch_aesni`, which needs no working space. -/
def gcmOfF (c : Ctr32Impl) : GcmImpl := { ctr := c, key := KeyImpl.aesni, gh := GhashName.scalar.impl }

theorem initCodeF_eq (c : Ctr32Impl) :
    Impl.StackScratch.X86_64.withStackScratch 184 .rcx (Impl.AesGcm.X86_64.init (gcmOfF c).callees) =
      gcmInitCodeF c.callee := rfl

open VG.X86_64.RScrub in
/-- `vg_aes_gcm_init` over `c`: with no working space for an implementation
that needs none, and without secret residue where the analysis handles it. -/
def initReg (c : Ctr32Impl) : Registration Spec.Gcm.initApi X86_64.target :=
  match c.free with
  | some fc =>
    withScrub {
      suffix := c.suffix
      code := gcmInitCodeF c.callee
      stack := 192
      verified := initCodeF_eq c ▸ initF_framed (gcmOfF c) KeyImpl.aesniFree fc
      spSafe := initCodeF_eq c ▸ VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOfF c)) }
      (initOut _) [] (pubOk_nil _) c.gcmInitRes
  | none => withScrubAll {
      suffix := c.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init (gcmOf c).callees)
      stack := 2576
      verified := init_framed (gcmOf c)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOf c)) } (initOut _)

/-! ## `vg_aes_gcm_stream_init` and `vg_aes_gcm_stream_aad`

GHASH alone, over each implementation of `vg_ghash`, in a frame of only the
working space they use: the 272 bytes they use themselves over
`vg_ghash_pclmul` and `vg_ghash_vpclmul`, which need none
(`streamInit_framed28`, `streamAad_framed22`), and with `vg_ghash`'s 256
bytes at 512, 768 (`_framed96`), rather than 2.5 KB; followed by the
clearing of that whole frame (`X86_64.Scrub.withScrubAll`): the residue
analysis would keep all of it, as it cannot place the byte copies into the
state. SM4-GCM's are the same functions (`Spec.Sm4.Gcm.streamInitApi`,
`streamAadApi`). The instances `vg_aes_gcm_seal_gather_prepared` calls are
internal functions of their own, `vg_aes_gcm_stream_init<suffix>_core`, …
(`initFn`, `aadFn`), with the code as it was. -/

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract X86_64.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, np, nl, st], _ =>
      simp only [Spec.Gcm.streamInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change ∀ ciph, Spec.Gcm.StreamRepr m₁ st ciph _ _ [] [] at h
      change ∀ ciph, Spec.Gcm.StreamRepr m₂ st ciph _ _ [] []
      exact fun ciph => Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.2) (h ciph)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract X86_64.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, d, ln], _ =>
      simp only [Spec.Gcm.streamAadSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change ∀ ciph iv a, Spec.Gcm.StreamRepr m st ciph _ iv a [] → _ → Spec.Gcm.StreamRepr m₁ st ciph _ iv _ [] at h
      change ∀ ciph iv a, Spec.Gcm.StreamRepr m st ciph _ iv a [] → _ → Spec.Gcm.StreamRepr m₂ st ciph _ iv _ []
      exact fun ciph iv a hr hl => Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) (h ciph iv a hr hl)

/-- The implementations the GHASH-only functions call with `n` (as the
registration files'). -/
def ghOf (n : GhashName) : GcmImpl :=
  { ctr := Ctr32Impl.scalar, key := KeyImpl.scalar, gh := n.impl }

/-- `vg_aes_gcm_stream_init` over `n`, in 240 bytes of stack (784 over
`vg_ghash`), all cleared. -/
def streamInitReg (n : GhashName) : Registration Spec.Gcm.streamInitApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
    stack := 240
    verified := streamInit_framed28 (ghOf n) f
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) } (streamInitOut _)
  | none => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
    stack := 784
    verified := streamInit_framed96 (ghOf n)
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) } (streamInitOut _)

/-- `vg_aes_gcm_stream_aad` over `n`, in 192 bytes of stack (784 over
`vg_ghash`), all cleared. -/
def streamAadReg (n : GhashName) : Registration Spec.Gcm.streamAadApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
    stack := 192
    verified := streamAad_framed22 (ghOf n) f
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) } (streamAadOut _)
  | none => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
    stack := 784
    verified := streamAad_framed96 (ghOf n)
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) } (streamAadOut _)

/-- `vg_sm4_gcm_stream_init` over `n`: `streamInitReg`'s function. -/
def sm4StreamInitReg (n : GhashName) : Registration Spec.Sm4.Gcm.streamInitApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
    stack := 240
    verified := streamInit_framed28 (ghOf n) f
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) } (streamInitOut _)
  | none => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
    stack := 784
    verified := streamInit_framed96 (ghOf n)
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) } (streamInitOut _)

/-- `vg_sm4_gcm_stream_aad` over `n`: `streamAadReg`'s function. -/
def sm4StreamAadReg (n : GhashName) : Registration Spec.Sm4.Gcm.streamAadApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
    stack := 192
    verified := streamAad_framed22 (ghOf n) f
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) } (streamAadOut _)
  | none => withScrubAll {
    suffix := n.impl.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
    stack := 784
    verified := streamAad_framed96 (ghOf n)
    spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) } (streamAadOut _)

/-! ## `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify`

Over an implementation of `vg_aes_ctr32` that needs no working space
(`Aes.X86_64.Ctr32Impl.free`), in a frame of only the working space they
use rather than 2.5 KB: over `vg_ghash_pclmul` and `vg_ghash_vpclmul`,
which need none either, the 208 and 272 bytes they use themselves
(`streamFinish_framed26`, `streamVerify_framed34`), and with `vg_ghash`'s
256 bytes at 512, 768 (`_framed96`); followed by the clearing of that whole
frame (`X86_64.Scrub.withScrubAll`). Over the others, as before.
`vg_aes_gcm_seal_gather_prepared` calls the first by name: the instances
over the first are internal functions of their own,
`vg_aes_gcm_stream_finish<suffix>_core` (`finFn`), with the code as it was. -/

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Gcm.streamFinishContract X86_64.abi stack) (Spec.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      intro key hk _ _ iv a c hr hA hT
      show Spec.Aes.bytesAt m₂ tag 16 = _
      rw [bytesAt_of0 hb.2.2 (by decide)]
      exact h key hk iv a c hr hA hT

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract X86_64.abi stack) (Spec.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

/-- The implementations AES-GCM's streaming functions call with `c` and `n`
(as the registration file's). -/
def pairOf (c : Ctr32Impl) (n : GhashName) : GcmImpl :=
  { ctr := c, key := if c.features.isEmpty then KeyImpl.scalar else KeyImpl.aesni, gh := n.impl }

/-- `vg_aes_gcm_stream_finish` over `c` and `n`: in 232 bytes of stack (792
over `vg_ghash`), all cleared, for an implementation of `vg_aes_ctr32` that
needs no working space. -/
def streamFinishReg (c : Ctr32Impl) (n : GhashName) : Registration Spec.Gcm.streamFinishApi X86_64.target :=
  match c.free, (pairOf c n).gh.free with
  | some f, some g =>
    withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 224 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 232
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed26 (pairOf c n) f g)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) } (streamFinishOut _)
  | some f, none =>
    withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 792
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed96 (pairOf c n) f)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) } (streamFinishOut _)
  | none, _ => withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 2584
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed (pairOf c n))
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) } (streamFinishOut _)

/-- `vg_aes_gcm_stream_verify` over `c` and `n`: in 304 bytes of stack (800
over `vg_ghash`), all cleared, for an implementation of `vg_aes_ctr32` that
needs no working space. -/
def streamVerifyReg (c : Ctr32Impl) (n : GhashName) : Registration Spec.Gcm.streamVerifyApi X86_64.target :=
  match c.free, (pairOf c n).gh.free with
  | some f, some g =>
    withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 296 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 304
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed34 (pairOf c n) f g)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) } (streamVerifyOut _)
  | some f, none =>
    withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 792 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 800
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed96 (pairOf c n) f)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) } (streamVerifyOut _)
  | none, _ => withScrubAll {
      suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 2592
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed (pairOf c n))
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) } (streamVerifyOut _)

/-! ## The functions over implementations that need working space

Over an implementation of `vg_aes_ctr32` or `vg_ghash` that needs working
space of its own (`Aes.X86_64.Ctr32Impl.free`, `GhashImpl.free`: `none`),
whose frames keep their 2.5 KB, followed by the clearing of their whole
stack (`X86_64.Scrub.withScrubAll`): AES or GHASH in software takes far
longer than the clearing. Their postconditions read the memory on return
only within their buffers. -/

theorem sealPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealPreparedContract X86_64.abi stack) (Spec.Gcm.sealPreparedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk

theorem openPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openPreparedContract X86_64.abi stack) (Spec.Gcm.openPreparedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Gcm.openPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk
      erw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _)]
      exact h key hk

theorem streamEncryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptPreparedContract X86_64.abi stack)
      (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a p hr hA hT
      obtain ⟨h₁, h₂⟩ := h key hk iv a p hr hA hT
      exact ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h₁,
        by erw [bytesAt_of0 hb.2.2 (Nat.le_refl _)]; exact h₂⟩

theorem streamDecryptPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptPreparedContract X86_64.abi stack)
      (Spec.Gcm.streamCryptPreparedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk _ _ iv a c hr hA hT
      obtain ⟨h₁, h₂⟩ := h key hk iv a c hr hA hT
      exact ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h₁,
        by erw [bytesAt_of0 hb.2.2 (Nat.le_refl _)]; exact h₂⟩

theorem sealGatherPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherPreparedContract X86_64.abi stack) (Spec.Gcm.sealGatherPreparedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      intro key hk hg
      show _ = (Spec.Aes.bytesAt m₂ dst len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk hg

theorem openToPreparedOut (stack : Nat) :
    PostOut (Spec.Gcm.openToPreparedContract X86_64.abi stack) (Spec.Gcm.openToPreparedSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tl], _ =>
      simp only [Spec.Gcm.openToPreparedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      have hd : dl.toNat = len.toNat := hpre.2.1
      intro key hk
      erw [bytesAt_of0 hb.2.2.2.2.1 (Nat.le_of_eq hd.symm)]
      exact h key hk

/-- Whether `v` calls an implementation of `vg_aes_ctr32` or `vg_ghash` that
needs working space of its own. -/
def _root_.VG.Proof.AesGcm.X86_64.GcmImpl.needsWork (v : GcmImpl) : Bool :=
  v.ctr.free.isNone || v.gh.free.isNone

/-- `r`, with its whole stack cleared (`X86_64.Scrub.withScrubAll`) if `v`
needs working space of its own (`GcmImpl.needsWork`); otherwise as it is. -/
def scrubIfWork {api : Api} (v : GcmImpl) (r : Registration api X86_64.target)
    (hpost : PostOut r.contract
      (api.sig.retBits ((X86_64.abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api X86_64.target :=
  if v.needsWork then withScrubAll r hpost else r

/-! ## SM4-GCM

Every SM4-GCM function calls `vg_sm4_ctr32`, SM4 in software with a frame
of 3.2 KB of its own: they keep their frames, and clear their whole stack
after (`X86_64.Scrub.withScrubAll`). -/

theorem sm4InitOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.initContract X86_64.abi stack) (Spec.Sm4.Gcm.initSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, ctx], _ =>
      simp only [Spec.Sm4.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change Spec.Sm4.Gcm.KeyRepr m₁ ctx _ at h
      change Spec.Sm4.Gcm.KeyRepr m₂ ctx _
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [Proof.Sm4.scheduleAt_congr fun k hk => Proof.AesGcm.agree_of hb.2 k (by omega)]
        exact h1
      · simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

theorem sm4SealOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.sealContract X86_64.abi stack) (Spec.Sm4.Gcm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Sm4.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h

theorem sm4OpenOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.openContract X86_64.abi stack) (Spec.Sm4.Gcm.openSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Sm4.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sm4.Gcm.openPost 64 ctx nonce nl aad al data len tag tl m m₂ r
      unfold Spec.Sm4.Gcm.openPost
      erw [bytesAt_of0 hb.2.2.2.1 (Nat.le_refl _)]
      exact h

theorem sm4StreamEncryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamEncryptContract X86_64.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, data, len], _ =>
      simp only [Spec.Sm4.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sm4.Gcm.streamEncryptPost 64 ctx st al tl data len m m₂ r
      change Spec.Sm4.Gcm.streamEncryptPost 64 ctx st al tl data len m m₁ r at h
      unfold Spec.Sm4.Gcm.streamEncryptPost at h ⊢
      intro _ _ iv a p hr hA hT
      obtain ⟨h₁, h₂⟩ := h iv a p hr hA hT
      exact ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h₁,
        by erw [bytesAt_of0 hb.2.2 (Nat.le_refl _)]; exact h₂⟩

theorem sm4StreamDecryptOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamDecryptContract X86_64.abi stack) (Spec.Sm4.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, data, len], _ =>
      simp only [Spec.Sm4.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Sm4.Gcm.streamDecryptPost 64 ctx st al tl data len m m₂ r
      change Spec.Sm4.Gcm.streamDecryptPost 64 ctx st al tl data len m m₁ r at h
      unfold Spec.Sm4.Gcm.streamDecryptPost at h ⊢
      intro _ _ iv a c hr hA hT
      obtain ⟨h₁, h₂⟩ := h iv a c hr hA hT
      exact ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h₁,
        by erw [bytesAt_of0 hb.2.2 (Nat.le_refl _)]; exact h₂⟩

theorem sm4StreamFinishOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamFinishContract X86_64.abi stack) (Spec.Sm4.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, tl, tag], _ =>
      simp only [Spec.Sm4.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      show Spec.Sm4.Gcm.streamFinishPost 64 ctx st al tl tag m m₂ r
      change Spec.Sm4.Gcm.streamFinishPost 64 ctx st al tl tag m m₁ r at h
      unfold Spec.Sm4.Gcm.streamFinishPost at h ⊢
      intro _ _ iv a c hr hA hT
      erw [bytesAt_of0 hb.2.2 (by decide)]
      exact h iv a c hr hA hT

theorem sm4StreamVerifyOut (stack : Nat) :
    PostOut (Spec.Sm4.Gcm.streamVerifyContract X86_64.abi stack) (Spec.Sm4.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, st, al, tl, tag, tagLen], _ => exact h

end VG.Proof.AesGcm.X86_64.Scrub
