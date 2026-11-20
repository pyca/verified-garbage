module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubStub
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fn
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Aes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM's key setup on x86-64, without secret residue

`vg_aes_gcm_init` over an implementation of `vg_aes_ctr32` that needs no
working space (`Aes.X86_64.Ctr32Impl.free`), with `vg_aes_expand_key_scratch_aesni`,
which needs none either, in a frame of only the 176 bytes it writes itself
(`initF_framed`), followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives its residue
analysis (`Aes.X86_64.Ctr32Impl.gcmInitRes`, on `Aes.X86_64.gcmInitCodeF`).
Over the others, in a frame of 2.5 KB, of which the analysis cannot tell
what may hold secrets, followed by the clearing of that whole frame, in
chunks whose 16-byte stores are aligned (`X86_64.RScrub.withScrubAllC`). Its
postcondition reads the memory on
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
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this])

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega_using [hn])
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

theorem init_fill (i : GcmImpl) (n : Nat) (hs : i.stitch = none) :
    Fill (i.lv .sse).level (fun _ => 0)
      (Impl.StackScratch.X86_64.withStackScratch n .rcx (Impl.AesGcm.X86_64.init (stubCallees none none false)))
      (Impl.StackScratch.X86_64.withStackScratch n .rcx (Impl.AesGcm.X86_64.init i.callees)) := by
  obtain ⟨h1, h2, h3⟩ := i.sides .sse
  simp only [GcmImpl.callees, hs, Option.map_none, Option.any_none]
  fill_calls

/-- `Spec.Gcm.initApi`'s function as emitted over `c`, for an implementation
that needs no working space (`Impl.AesGcm.X86_64.Fn.init`, in 192 bytes),
meets its contract in constant time and returns without secret residue. -/
theorem initF_scrubbed (c : Ctr32Impl) (fc : Proof.Aes.X86_64.Ctr32Free c.callee) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.init ((gcmOfF c).lv .sse) 192 (gcmOfF c).callees)
      (Spec.Gcm.initApi.contract X86_64.abi 192) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.initApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 184 .rcx (Impl.AesGcm.X86_64.init (stubCallees none none false)))
    { suffix := c.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 184 .rcx (Impl.AesGcm.X86_64.init (gcmOfF c).callees)
      contract := Spec.Gcm.initContract abi 192
      verified := initF_framed (gcmOfF c) KeyImpl.aesniFree fc
      spSafe := VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOfF c)) }
    _ (initOut _) (init_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.initApi`'s function as emitted over `c`, in 2576 bytes, as
`initF_scrubbed`. -/
theorem init_scrubbed (c : Ctr32Impl) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.init ((gcmOf c).lv .sse) 2576 (gcmOf c).callees)
      (Spec.Gcm.initApi.contract X86_64.abi 2576) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.initApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init (stubCallees none none false)))
    { suffix := c.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesGcm.X86_64.init (gcmOf c).callees)
      stack := 2576
      verified := init_framed (gcmOf c)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOf c)) }
    _ (initOut _) (init_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `vg_aes_gcm_init` over `c`: with no working space for an implementation
that needs none; over the others, in 2576 bytes. -/
def initReg (c : Ctr32Impl) : Registration Spec.Gcm.initApi X86_64.target :=
  match c.free with
  | some fc =>
    { suffix := c.suffix
      code := Impl.AesGcm.X86_64.Fn.init ((gcmOfF c).lv .sse) 192 (gcmOfF c).callees
      verified := .scrubbed (initF_scrubbed c fc)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOfF c))) }
  | none =>
    { suffix := c.suffix
      code := Impl.AesGcm.X86_64.Fn.init ((gcmOf c).lv .sse) 2576 (gcmOf c).callees
      verified := .scrubbed (init_scrubbed c)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (init_spSafe (gcmOf c))) }

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

theorem streamInit_fill (i : GcmImpl) (m : Nat) (hs : i.stitch = none) :
    Fill (i.lv .sse).level (fun _ => 0)
      (Impl.StackScratch.X86_64.withStackScratch m .r8 (Impl.AesGcm.X86_64.streamInit (stubCallees none none false)))
      (Impl.StackScratch.X86_64.withStackScratch m .r8 (Impl.AesGcm.X86_64.streamInit i.callees)) := by
  obtain ⟨h1, h2, h3⟩ := i.sides .sse
  simp only [GcmImpl.callees, hs, Option.map_none, Option.any_none]
  fill_calls

/-- `Spec.Gcm.streamInitApi`'s function as emitted over `n`, in 240 bytes
(`Impl.AesGcm.X86_64.Fn.streamInit`), meets its contract in constant time and
returns without secret residue. -/
theorem streamInitF_scrubbed (n : GhashName) (f : GhashFree (ghOf n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees)
      (Spec.Gcm.streamInitApi.contract X86_64.abi 240) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamInitApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
      stack := 240
      verified := streamInit_framed28 (ghOf n) f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) }
    _ (streamInitOut _) (streamInit_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Sm4.Gcm.streamInitApi`'s function as emitted over `n`, in 240 bytes
(`Impl.AesGcm.X86_64.Fn.streamInit`), meets its contract in constant time and
returns without secret residue. -/
theorem sm4StreamInitF_scrubbed (n : GhashName) (f : GhashFree (ghOf n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees)
      (Spec.Sm4.Gcm.streamInitApi.contract X86_64.abi 240) 0 :=
  verifiedScrubbedAllFill (api := Spec.Sm4.Gcm.streamInitApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 232 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
      stack := 240
      verified := streamInit_framed28 (ghOf n) f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) }
    _ (streamInitOut _) (streamInit_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamInitApi`'s function as emitted over `n`, in 784 bytes
(`Impl.AesGcm.X86_64.Fn.streamInit`), meets its contract in constant time and
returns without secret residue. -/
theorem streamInit_scrubbed (n : GhashName) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees)
      (Spec.Gcm.streamInitApi.contract X86_64.abi 784) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamInitApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
      stack := 784
      verified := streamInit_framed96 (ghOf n)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) }
    _ (streamInitOut _) (streamInit_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Sm4.Gcm.streamInitApi`'s function as emitted over `n`, in 784 bytes
(`Impl.AesGcm.X86_64.Fn.streamInit`), meets its contract in constant time and
returns without secret residue. -/
theorem sm4StreamInit_scrubbed (n : GhashName) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees)
      (Spec.Sm4.Gcm.streamInitApi.contract X86_64.abi 784) 0 :=
  verifiedScrubbedAllFill (api := Spec.Sm4.Gcm.streamInitApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 776 .r8 (Impl.AesGcm.X86_64.streamInit (ghOf n).callees)
      stack := 784
      verified := streamInit_framed96 (ghOf n)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n)) }
    _ (streamInitOut _) (streamInit_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamInitApi`'s function over `n`: in 240 bytes of stack (784 over
`vg_ghash`). -/
def streamInitReg (n : GhashName) : Registration Spec.Gcm.streamInitApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees
      verified := .scrubbed (streamInitF_scrubbed n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n))) }
  | none =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees
      verified := .scrubbed (streamInit_scrubbed n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n))) }

/-- `Spec.Sm4.Gcm.streamInitApi`'s function over `n`: in 240 bytes of stack (784 over
`vg_ghash`). -/
def sm4StreamInitReg (n : GhashName) : Registration Spec.Sm4.Gcm.streamInitApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 240 (ghOf n).callees
      verified := .scrubbed (sm4StreamInitF_scrubbed n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n))) }
  | none =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamInit ((ghOf n).lv .sse) 784 (ghOf n).callees
      verified := .scrubbed (sm4StreamInit_scrubbed n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamInit_spSafe (ghOf n))) }

theorem streamAad_fill (i : GcmImpl) (m : Nat) (hs : i.stitch = none) :
    Fill (i.lv .sse).level (fun _ => 0)
      (Impl.StackScratch.X86_64.withStackScratch m .r9 (Impl.AesGcm.X86_64.streamAad (stubCallees none none false)))
      (Impl.StackScratch.X86_64.withStackScratch m .r9 (Impl.AesGcm.X86_64.streamAad i.callees)) := by
  obtain ⟨h1, h2, h3⟩ := i.sides .sse
  simp only [GcmImpl.callees, hs, Option.map_none, Option.any_none]
  fill_calls

/-- `Spec.Gcm.streamAadApi`'s function as emitted over `n`, in 192 bytes
(`Impl.AesGcm.X86_64.Fn.streamAad`), meets its contract in constant time and
returns without secret residue. -/
theorem streamAadF_scrubbed (n : GhashName) (f : GhashFree (ghOf n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees)
      (Spec.Gcm.streamAadApi.contract X86_64.abi 192) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamAadApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
      stack := 192
      verified := streamAad_framed22 (ghOf n) f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) }
    _ (streamAadOut _) (streamAad_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Sm4.Gcm.streamAadApi`'s function as emitted over `n`, in 192 bytes
(`Impl.AesGcm.X86_64.Fn.streamAad`), meets its contract in constant time and
returns without secret residue. -/
theorem sm4StreamAadF_scrubbed (n : GhashName) (f : GhashFree (ghOf n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees)
      (Spec.Sm4.Gcm.streamAadApi.contract X86_64.abi 192) 0 :=
  verifiedScrubbedAllFill (api := Spec.Sm4.Gcm.streamAadApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 184 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
      stack := 192
      verified := streamAad_framed22 (ghOf n) f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) }
    _ (streamAadOut _) (streamAad_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamAadApi`'s function as emitted over `n`, in 784 bytes
(`Impl.AesGcm.X86_64.Fn.streamAad`), meets its contract in constant time and
returns without secret residue. -/
theorem streamAad_scrubbed (n : GhashName) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees)
      (Spec.Gcm.streamAadApi.contract X86_64.abi 784) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamAadApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
      stack := 784
      verified := streamAad_framed96 (ghOf n)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) }
    _ (streamAadOut _) (streamAad_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Sm4.Gcm.streamAadApi`'s function as emitted over `n`, in 784 bytes
(`Impl.AesGcm.X86_64.Fn.streamAad`), meets its contract in constant time and
returns without secret residue. -/
theorem sm4StreamAad_scrubbed (n : GhashName) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees)
      (Spec.Sm4.Gcm.streamAadApi.contract X86_64.abi 784) 0 :=
  verifiedScrubbedAllFill (api := Spec.Sm4.Gcm.streamAadApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (stubCallees none none false)))
    { suffix := n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 776 .r9 (Impl.AesGcm.X86_64.streamAad (ghOf n).callees)
      stack := 784
      verified := streamAad_framed96 (ghOf n)
      spSafe := VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n)) }
    _ (streamAadOut _) (streamAad_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamAadApi`'s function over `n`: in 192 bytes of stack (784 over
`vg_ghash`). -/
def streamAadReg (n : GhashName) : Registration Spec.Gcm.streamAadApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees
      verified := .scrubbed (streamAadF_scrubbed n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n))) }
  | none =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees
      verified := .scrubbed (streamAad_scrubbed n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n))) }

/-- `Spec.Sm4.Gcm.streamAadApi`'s function over `n`: in 192 bytes of stack (784 over
`vg_ghash`). -/
def sm4StreamAadReg (n : GhashName) : Registration Spec.Sm4.Gcm.streamAadApi X86_64.target :=
  match (ghOf n).gh.free with
  | some f =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 192 (ghOf n).callees
      verified := .scrubbed (sm4StreamAadF_scrubbed n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n))) }
  | none =>
    { suffix := n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamAad ((ghOf n).lv .sse) 784 (ghOf n).callees
      verified := .scrubbed (sm4StreamAad_scrubbed n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (streamAad_spSafe (ghOf n))) }

/-! ## `vg_aes_gcm_stream_finish` and `vg_aes_gcm_stream_verify`

Over an implementation of `vg_aes_ctr32` that needs no working space
(`Aes.X86_64.Ctr32Impl.free`), in a frame of only the working space they
use rather than 2.5 KB: over `vg_ghash_pclmul` and `vg_ghash_vpclmul`,
which need none either, the 208 and 272 bytes they use themselves
(`streamFinish_framed26`, `streamVerify_framed34`), and with `vg_ghash`'s
256 bytes at 512, 768 (`_framed96`); followed by the clearing of that whole
frame (`X86_64.Scrub.withScrubAll`). Over the bitsliced `vg_aes_ctr32`, whose
working space is most of the frame, in the frame of 2.5 KB, wiped whole in
chunks whose 16-byte stores are aligned (`X86_64.RScrub.withScrubAllC`), as
`vg_cmac_aes_finish` over it is.
`vg_aes_gcm_seal_gather_prepared` calls the first by name: it calls
internal functions of its own instead,
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

theorem streamFinish_fill (i : GcmImpl) (m : Nat) (hs : i.stitch = none) :
    Fill (i.lv .sse).level (fun _ => 0)
      (Impl.StackScratch.X86_64.withStackArgScratch m 0 (Impl.AesGcm.X86_64.streamFinish (stubCallees none none false)))
      (Impl.StackScratch.X86_64.withStackArgScratch m 0 (Impl.AesGcm.X86_64.streamFinish i.callees)) := by
  obtain ⟨h1, h2, h3⟩ := i.sides .sse
  simp only [GcmImpl.callees, hs, Option.map_none, Option.any_none]
  fill_calls

/-- `Spec.Gcm.streamFinishApi`'s function as emitted over `c` and `n`, in 232
bytes (`Impl.AesGcm.X86_64.Fn.streamFinish`), meets its contract in constant time
and returns without secret residue. -/
theorem streamFinishFF_scrubbed (c : Ctr32Impl) (n : GhashName) (f : Proof.Aes.X86_64.Ctr32Free c.callee) (g : GhashFree (pairOf c n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 232 (pairOf c n).callees)
      (Spec.Gcm.streamFinishApi.contract X86_64.abi 232) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamFinishApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 224 0 (Impl.AesGcm.X86_64.streamFinish (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 224 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 232
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed26 (pairOf c n) f g)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) }
    _ (streamFinishOut _) (streamFinish_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamFinishApi`'s function as emitted over `c` and `n`, in 792
bytes (`Impl.AesGcm.X86_64.Fn.streamFinish`), meets its contract in constant time
and returns without secret residue. -/
theorem streamFinishF_scrubbed (c : Ctr32Impl) (n : GhashName) (f : Proof.Aes.X86_64.Ctr32Free c.callee) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 792 (pairOf c n).callees)
      (Spec.Gcm.streamFinishApi.contract X86_64.abi 792) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamFinishApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (Impl.AesGcm.X86_64.streamFinish (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 784 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 792
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed96 (pairOf c n) f)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) }
    _ (streamFinishOut _) (streamFinish_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamFinishApi`'s function as emitted over `c` and `n`, in 2584
bytes (`Impl.AesGcm.X86_64.Fn.streamFinish`), meets its contract in constant time
and returns without secret residue. -/
theorem streamFinish_scrubbed (c : Ctr32Impl) (n : GhashName)  :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 2584 (pairOf c n).callees)
      (Spec.Gcm.streamFinishApi.contract X86_64.abi 2584) 0 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamFinishApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish (pairOf c n).callees)
      stack := 2584
      verified := Proof.AesGcm.streamFinish_keyed (streamFinish_framed (pairOf c n))
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n)) }
    _ (streamFinishOut _) (streamFinish_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `vg_aes_gcm_stream_finish` over `c` and `n`: in 232 bytes of stack (792
over `vg_ghash`) for an implementation of `vg_aes_ctr32` that needs no
working space; for the others, in 2584 bytes. -/
def streamFinishReg (c : Ctr32Impl) (n : GhashName) : Registration Spec.Gcm.streamFinishApi X86_64.target :=
  match c.free, (pairOf c n).gh.free with
  | some f, some g =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 232 (pairOf c n).callees
      verified := .scrubbed (streamFinishFF_scrubbed c n f g)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n))) }
  | some f, none =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 792 (pairOf c n).callees
      verified := .scrubbed (streamFinishF_scrubbed c n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n))) }
  | none, _ =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamFinish ((pairOf c n).lv .sse) 2584 (pairOf c n).callees
      verified := .scrubbed (streamFinish_scrubbed c n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamFinish_spSafe (pairOf c n))) }

theorem streamVerify_fill (i : GcmImpl) (m : Nat) (hs : i.stitch = none) :
    Fill (i.lv .sse).level (fun _ => 0)
      (Impl.StackScratch.X86_64.withStackArgScratch m 1 (Impl.AesGcm.X86_64.streamVerify (stubCallees none none false)))
      (Impl.StackScratch.X86_64.withStackArgScratch m 1 (Impl.AesGcm.X86_64.streamVerify i.callees)) := by
  obtain ⟨h1, h2, h3⟩ := i.sides .sse
  simp only [GcmImpl.callees, hs, Option.map_none, Option.any_none]
  fill_calls

/-- `Spec.Gcm.streamVerifyApi`'s function as emitted over `c` and `n`, in 304
bytes (`Impl.AesGcm.X86_64.Fn.streamVerify`), meets its contract in constant time
and returns without secret residue. -/
theorem streamVerifyFF_scrubbed (c : Ctr32Impl) (n : GhashName) (f : Proof.Aes.X86_64.Ctr32Free c.callee) (g : GhashFree (pairOf c n).gh.fn.code) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 304 (pairOf c n).callees)
      (Spec.Gcm.streamVerifyApi.contract X86_64.abi 304) 32 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamVerifyApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 296 1 (Impl.AesGcm.X86_64.streamVerify (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 296 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 304
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed34 (pairOf c n) f g)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) }
    _ (streamVerifyOut _) (streamVerify_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamVerifyApi`'s function as emitted over `c` and `n`, in 800
bytes (`Impl.AesGcm.X86_64.Fn.streamVerify`), meets its contract in constant time
and returns without secret residue. -/
theorem streamVerifyF_scrubbed (c : Ctr32Impl) (n : GhashName) (f : Proof.Aes.X86_64.Ctr32Free c.callee) :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 800 (pairOf c n).callees)
      (Spec.Gcm.streamVerifyApi.contract X86_64.abi 800) 32 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamVerifyApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 792 1 (Impl.AesGcm.X86_64.streamVerify (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 792 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 800
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed96 (pairOf c n) f)
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) }
    _ (streamVerifyOut _) (streamVerify_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Gcm.streamVerifyApi`'s function as emitted over `c` and `n`, in 2592
bytes (`Impl.AesGcm.X86_64.Fn.streamVerify`), meets its contract in constant time
and returns without secret residue. -/
theorem streamVerify_scrubbed (c : Ctr32Impl) (n : GhashName)  :
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 2592 (pairOf c n).callees)
      (Spec.Gcm.streamVerifyApi.contract X86_64.abi 2592) 32 :=
  verifiedScrubbedAllFill (api := Spec.Gcm.streamVerifyApi) (ks := 0) (n := fun _ => 0)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify (stubCallees none none false)))
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamVerify (pairOf c n).callees)
      stack := 2592
      verified := Proof.AesGcm.streamVerify_keyed (streamVerify_framed (pairOf c n))
      spSafe := VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n)) }
    _ (streamVerifyOut _) (streamVerify_fill _ _ rfl) (Nat.zero_le _) (Nat.le_refl _)

/-- `vg_aes_gcm_stream_verify` over `c` and `n`: in 304 bytes of stack (800
over `vg_ghash`) for an implementation of `vg_aes_ctr32` that needs no
working space; for the others, in 2592 bytes. -/
def streamVerifyReg (c : Ctr32Impl) (n : GhashName) : Registration Spec.Gcm.streamVerifyApi X86_64.target :=
  match c.free, (pairOf c n).gh.free with
  | some f, some g =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 304 (pairOf c n).callees
      verified := .scrubbed (streamVerifyFF_scrubbed c n f g)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n))) }
  | some f, none =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 800 (pairOf c n).callees
      verified := .scrubbed (streamVerifyF_scrubbed c n f)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n))) }
  | none, _ =>
    { suffix := c.suffix ++ n.impl.suffix
      code := Impl.AesGcm.X86_64.Fn.streamVerify ((pairOf c n).lv .sse) 2592 (pairOf c n).callees
      verified := .scrubbed (streamVerify_scrubbed c n)
      spSafe := scrubKs_spSafe (VG.X86_64.withStackArgScratch_spSafe (streamVerify_spSafe (pairOf c n))) }

end VG.Proof.AesGcm.X86_64.Scrub
