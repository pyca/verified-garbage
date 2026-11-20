module

public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubOpenTo
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM's `vg_aes_gcm_seal_gather_prepared` on x86-64, without secret residue

`vg_aes_gcm_seal_gather_prepared` calls `vg_aes_gcm_seal` (`sealFn`),
`vg_aes_gcm_seal_split` (`splitFn`) and the streaming functions (`initFn`,
`aadFn`, `toFn`, `finFn`), which call the callees, the whole-blocks
functions and their out-of-place forms (`blkTo`). Each is evaluated once
over stubs of what it calls (`calleeSide_of_fill`), for each kind of
interleaved loops where its code depends on them, and the function over
stubs of the first (`verifiedScrubbedAllFill`), at the level `GcmVariant.lvG`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- The level of the cleanup of `v`'s `seal_gather` on the key context:
`lv`'s and its out-of-place loops'. -/
def GcmVariant.lvG (v : GcmVariant) : VecLevel := v.lv.join v.toLv

theorem GcmVariant.lv_le_lvG (v : GcmVariant) : v.lv.level ≤ v.lvG.level := level_join_left _ _

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

theorem blkToP_side_of (v : GcmVariant) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    (hB : calleeSide B.enc.code v.lv.level 8 = true) (st : Option (StitchToCode M true)) (n : Option StitchToName)
    (hst : st.map (·.enc) = n.map StitchToName.encR ∧ encFullTo st = (n.map StitchToName.fullR).getD false)
    (hn : ((n.map StitchToName.lv).getD .sse).level ≤ v.lvG.level) :
    calleeSide (StreamTo.BlkToFn.ofBlocks "" B st).fn.code v.lvG.level 24 = true := by
  show calleeSide (Impl.AesGcm.X86_64.BlocksTo.encrypt B.enc (st.map (·.enc)) true (encFullTo st)) _ 24 = true
  rw [hst.1, hst.2]
  exact calleeSide_of_fill (blocksTo_fill (n := fun _ => 8) _
    (calleeSide_mono v.lv_le_lvG (Nat.le_refl _) hB) _ true _) hn (blocksToP_stub n)

/-- `v`'s `blkToR`. -/
theorem blkToR_side (v : GcmVariant) : calleeSide (blkToR v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToF`. -/
theorem blkToF_side (v : GcmVariant) : calleeSide (blkToF v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .vaesAvx512) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToR16`. -/
theorem blkToR16_side (v : GcmVariant) : calleeSide (blkToR16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkR16_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname <;> exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

/-- `v`'s `blkToF16`. -/
theorem blkToF16_side (v : GcmVariant) : calleeSide (blkToF16 v).fn.code v.lvG.level 24 = true := by
  have hB := (blkF16_sides v).1
  have hl := v.toLv_le_lvG
  rcases v with ⟨ctr, key, gh, _ | ⟨name, sfx, fs, eP, dP, pP, pR, _ | ⟨tname, tpiece, tpP, _ | q, tpD⟩⟩⟩
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname <;> exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
  · cases tname
    · exact blkToP_side_of _ _ hB _ (some .vaes) ⟨rfl, rfl⟩ hl
    · exact blkToP_side_of _ _ hB _ none ⟨rfl, rfl⟩ (Nat.zero_le _)
    · exact blkToP_side_of _ _ hB _ (some .aesniAvx) ⟨rfl, rfl⟩ hl

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
  cases a <;> cases b <;> cases c <;> decide

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

/-! ## The registrations

Each binds a function as emitted over `v` (`Impl.AesGcm.X86_64.Fn`) and its
theorem: on the key context alone (`…W`), or by the flag on 48 prepared
powers (`…R`), or by the count on 16 (`…R16`, given `R16 v`). -/

/-- `sealPreparedApi`'s function over `v`. -/
def sealPrepW (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealW v.lv v.impl.short v.impl.fin v.impl.callees
  verified := .scrubbed (sealW_scrubbed v)
  spSafe := scrubKs_spSafe ((sealWPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`. -/
def openPrepW (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openW v.lv v.impl.short v.impl.callees
  verified := .scrubbed (openW_scrubbed v)
  spSafe := scrubKs_spSafe ((openWPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`. -/
def openToPrepW (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToW v.lvTW (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToW_scrubbed v)
  spSafe := scrubKs_spSafe ((openToWPlain v).spSafe)

/-- `streamEncryptPreparedApi`'s function over `v`. -/
def streamEncryptPrepW (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptW v.lv v.impl.callees
  verified := .scrubbed (streamEncryptW_scrubbed v)
  spSafe := scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v.impl))

/-- `streamDecryptPreparedApi`'s function over `v`. -/
def streamDecryptPrepW (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptW v.lv v.impl.callees
  verified := .scrubbed (streamDecryptW_scrubbed v)
  spSafe := scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl))

/-- `sealGatherPreparedApi`'s function over `v`. -/
def sealGatherPrepW (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherW v.lvG (copyBelow v) (splitFrom v) (sealFn v.impl).fn (splitFn v).fn
        (initFn v.impl).fn (aadFn v.impl).fn (toFn v).fn (finFn v.impl).fn
  verified := .scrubbed (sealGatherW_scrubbed v)
  spSafe := scrubKs_spSafe ((sealGatherWPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`. -/
def sealPrepR (v : GcmVariant) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealP v.lv 48 v.impl.short v.impl.fin (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (sealR_scrubbed v)
  spSafe := scrubKs_spSafe ((sealRPlain v).spSafe)

/-- `openPreparedApi`'s function over `v`. -/
def openPrepR (v : GcmVariant) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openP v.lvA 48 v.impl.short (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (openR_scrubbed v)
  spSafe := scrubKs_spSafe ((openRPlain v).spSafe)

/-- `openToPreparedApi`'s function over `v`. -/
def openToPrepR (v : GcmVariant) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 48 v.stitchToDecR.isSome v.impl.copyW (openFnF v).fn (openSplitFnF v).fn
        (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToR_scrubbed v)
  spSafe := scrubKs_spSafe (openToCodeR_onFlag_spAll v)

/-- `streamEncryptPreparedApi`'s function over `v`. -/
def streamEncryptPrepR (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (streamEncryptR_scrubbed v)
  spSafe := scrubKs_spSafe (streamEncryptCodeF_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`. -/
def streamDecryptPrepR (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 48 (v.impl.withBlk (blkR v)) v.impl.callees
  verified := .scrubbed (streamDecryptR_scrubbed v)
  spSafe := scrubKs_spSafe (VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`. -/
def sealGatherPrepR (v : GcmVariant) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 48 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF v).fn
        (splitFnF v).fn (toFnF v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn false
  verified := .scrubbed (sealGatherR_scrubbed v)
  spSafe := scrubKs_spSafe ((sealGatherRPlain v).spSafe)

/-- `sealPreparedApi`'s function over `v`, on 16 prepared powers. -/
def sealPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealP v.lv 16 v.impl.short v.impl.fin (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (sealR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((sealF16Plain v r).spSafe)

/-- `openPreparedApi`'s function over `v`, on 16 prepared powers. -/
def openPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openP v.lvA 16 v.impl.short (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (openR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((openR16Plain v r).spSafe)

/-- `openToPreparedApi`'s function over `v`, on 16 prepared powers. -/
def openToPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.openToPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.openToP v.lvT 16 v.stitchToDecR16.isSome v.impl.copyW (openFnF16 v r).fn
        (openSplitFnF16 v).fn (openSplitFnB v v.ctrTo).fn
  verified := .scrubbed (openToR16_scrubbed v r)
  spSafe := scrubKs_spSafe (openToCodeR16_onFlag_spAll v r)

/-- `streamEncryptPreparedApi`'s function over `v`, on 16 prepared powers. -/
def streamEncryptPrepR16 (v : GcmVariant) : Registration Spec.Gcm.streamEncryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamEncryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (streamEncryptR16_scrubbed v)
  spSafe := scrubKs_spSafe (streamEncryptCodeF16_spAll v)

/-- `streamDecryptPreparedApi`'s function over `v`, on 16 prepared powers. -/
def streamDecryptPrepR16 (v : GcmVariant) : Registration Spec.Gcm.streamDecryptPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.streamDecryptP v.lv 16 (v.impl.withBlk (blkR16 v)) v.impl.callees
  verified := .scrubbed (streamDecryptR16_scrubbed v)
  spSafe := scrubKs_spSafe (VG.X86_64.onFlag_spSafe
      (X86_64.withStackArgScratch_spSafe (streamDecryptM_spSafe v.impl (blkR16 v)))
      (X86_64.withStackArgScratch_spSafe (streamDecrypt_spSafe v.impl)))

/-- `sealGatherPreparedApi`'s function over `v`, on 16 prepared powers. -/
def sealGatherPrepR16 (v : GcmVariant) (r : R16 v) : Registration Spec.Gcm.sealGatherPreparedApi X86_64.target where
  suffix := v.impl.suffix
  code := Impl.AesGcm.X86_64.Fn.sealGatherP v.lvGA 16 (tlsLong v) (copyBelow v) (splitFrom v) (sealFnF16 v r).fn
        (splitFnF16 v r).fn (toFnF16 v).fn (sealFn v.impl).fn (splitFn v).fn (toFn v).fn (initFn v.impl).fn
        (aadFn v.impl).fn (finFn v.impl).fn true
  verified := .scrubbed (sealGatherR16_scrubbed v r)
  spSafe := scrubKs_spSafe ((sealGatherR16Plain v r).spSafe)

end VG.Proof.AesGcm.X86_64
