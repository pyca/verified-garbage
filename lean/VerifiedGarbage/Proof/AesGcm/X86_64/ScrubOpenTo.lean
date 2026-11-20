module

public import VerifiedGarbage.Proof.AesGcm.X86_64.ScrubPrepared
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM's `vg_aes_gcm_open_to_prepared` on x86-64, without secret residue

On the key context, `vg_aes_gcm_open_to_prepared` calls `vg_aes_gcm_open_split`
(`openSplitFnB`), which calls the callees and `vg_aes_gcm_decrypt_blocks_to`
(`blkToDecB`), which calls `vg_ghash` and the out-of-place `vg_aes_ctr32_to`
(`GcmVariant.ctrTo`). Each is evaluated once over stubs of what it calls
(`calleeSide_of_fill`), and the function over a stub of the first
(`verifiedScrubbedAllFill`), at the level `GcmVariant.lvTW` (`lvT` on prepared powers).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Impl.AesGcm.X86_64 (Callees Fn)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)

/-- The level of the vector instructions of the out-of-place loops named `n`. -/
def StitchToName.lv : StitchToName → VecLevel
  | .vaes => .avx
  | .vaesAvx512 => .evex
  | .aesniAvx => .avx

/-- The level of `v`'s out-of-place loops, if any. -/
def GcmVariant.toLv (v : GcmVariant) : VecLevel :=
  match v.stitch with
  | some p => (p.toPart.map (·.name.lv)).getD .sse
  | none => .sse

/-- The level of the cleanup of `v`'s `open_to`: `lvA`'s, its out-of-place
`vg_aes_ctr32_to`'s and its out-of-place loops'. -/
def GcmVariant.lvT (v : GcmVariant) : VecLevel := (v.lvA.join v.ctrTo.level).join v.toLv

theorem GcmVariant.lvA_le_lvT (v : GcmVariant) : v.lvA.level ≤ v.lvT.level :=
  Nat.le_trans (level_join_left _ _) (level_join_left _ _)

theorem GcmVariant.ctrTo_le_lvT (v : GcmVariant) : v.ctrTo.level.level ≤ v.lvT.level :=
  Nat.le_trans (level_join_right _ _) (level_join_left _ _)

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
