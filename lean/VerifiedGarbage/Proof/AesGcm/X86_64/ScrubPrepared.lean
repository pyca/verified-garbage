module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Leaves
public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubStub
public import VerifiedGarbage.Impl.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM's functions on a prepared key context, on x86-64, without secret residue

Each function of a variant `v` of AES-GCM on a key context of
`vg_aes_gcm_prepare`, followed by the clearing of every register it may
write and of its whole frame (`Impl.AesGcm.X86_64.Fn`), at the level
`GcmVariant.lv`: the highest of its callees' and of its interleaved loops'
(`GcmVariant.own`). The code over stubs of the callees, and of the
functions it calls that are built from them (the whole-blocks functions,
`blk*_sides`), is evaluated once for each kind of interleaved loops.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)

/-- The level of the vector instructions of the loops named `n`. -/
def StitchName.lv : StitchName → VecLevel
  | .vaes => .avx
  | .vaesAvx512 => .evex
  | .aesniAvx => .avx

/-- The level of the vector instructions of `v`'s own code: its loops'. -/
def GcmVariant.own (v : GcmVariant) : VecLevel :=
  match v.stitch with
  | none => .sse
  | some p => p.name.lv

/-- The level of the cleanup of `v`'s functions. -/
def GcmVariant.lv (v : GcmVariant) : VecLevel := v.impl.lv v.own

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
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, tP⟩⟩
  · exact ⟨calleeSide_of_fill (ks := 0) (encrypt_fill (n := fun _ => 0) _ _ h1 h3 none none false false false false) hl
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
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (blkR v) (blkR_sides v)) v.impl.short v.impl.fin
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
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees)
      (Spec.Gcm.sealPreparedApi.contract X86_64.abi 2624) 0 := by
  rw [← hs, ← hf] at ha
  have hp := sealCodeP_fill _ (withBlk_side v (blkR16 v) (blkR16_sides v)) v.impl.short v.impl.fin
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
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees)
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
    VerifiedScrubbed target (Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees)
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
