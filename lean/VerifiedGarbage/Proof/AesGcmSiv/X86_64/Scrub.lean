module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFill
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-GCM-SIV on x86-64: returning without secret residue

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` over the implementations
`v`, each followed by the clearing of every register it may write and of its
whole stack (`Impl.AesGcmSiv.X86_64.Fn`): in registers (`sivReg`), code that
calls nothing, whose stub is the code itself; else over `v`'s callees,
which each state what the cleanup needs of their code (`calleeSide`), with
the code over a stub of each evaluated once (`verifiedScrubbedAllFill`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86_64

open VG.X86_64 VG.X86_64.Scrub
open VG.Impl.Scrub.X86_64 (VecLevel)
open VG.Proof.AesGcm.X86_64 (GcmImpl)
open VG.Impl.StackScratch.X86_64 (withStackArgScratch)
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)

/-- The callees of a stub: every function's code empty, called by its own
name. -/
def stubCallees : Impl.AesGcm.X86_64.Callees :=
  ⟨⟨"c", .block []⟩, ⟨"k", .block []⟩, ⟨"g", .block []⟩, ⟨"e", .block []⟩, ⟨"d", .block []⟩⟩

/-- The block function of a stub. -/
def stubEcb : Impl.AesGcm.X86_64.Fn := ⟨"b", .block []⟩

theorem loopsOf_cases (v : GcmImpl) :
    loopsOf v = none ∨ loopsOf v = some Impl.AesGcmSiv.X86_64Stitch.vaesLoops ∨
      loopsOf v = some Impl.AesGcmSiv.X86_64StitchAvx.loops := by
  unfold loopsOf
  split
  · exact .inr (.inl rfl)
  · split
    · exact .inr (.inr rfl)
    · exact .inl rfl

/-- The level of the vector instructions of `seal` and `open`'s own code:
VEX with the AVX2 copies or interleaved loops. -/
def ownLevel (wide : Bool) (lp : Option Loops) : VecLevel := if wide || lp.isSome then .avx else .sse

/-- The level of the cleanup of `seal` and `open` over `v`'s callees. -/
def softLevel (v : GcmImpl) (wide : Bool) (lp : Option Loops) : VecLevel :=
  (((v.ctr.level.join v.key.level).join v.gh.level).join (ecbOf v).level).join (ownLevel wide lp)

theorem softLevel_le (v : GcmImpl) (wide : Bool) (lp : Option Loops) :
    v.ctr.level.level ≤ (softLevel v wide lp).level ∧ v.key.level.level ≤ (softLevel v wide lp).level ∧
      v.gh.level.level ≤ (softLevel v wide lp).level ∧ (ecbOf v).level.level ≤ (softLevel v wide lp).level ∧
      (ownLevel wide lp).level ≤ (softLevel v wide lp).level := by
  unfold softLevel
  have e1 := level_join_left (((v.ctr.level.join v.key.level).join v.gh.level).join (ecbOf v).level) (ownLevel wide lp)
  have e2 := level_join_right (((v.ctr.level.join v.key.level).join v.gh.level).join (ecbOf v).level) (ownLevel wide lp)
  have e3 := level_join_left ((v.ctr.level.join v.key.level).join v.gh.level) (ecbOf v).level
  have e4 := level_join_right ((v.ctr.level.join v.key.level).join v.gh.level) (ecbOf v).level
  have e5 := level_join_left (v.ctr.level.join v.key.level) v.gh.level
  have e6 := level_join_right (v.ctr.level.join v.key.level) v.gh.level
  have e7 := level_join_left v.ctr.level v.key.level
  have e8 := level_join_right v.ctr.level v.key.level
  omega

theorem join_mono_right (a : VecLevel) {b c : VecLevel} (h : b.level ≤ c.level) :
    (a.join b).level ≤ (a.join c).level := by
  revert h; cases a <;> cases b <;> cases c <;> decide

/-- The cleanup with the AVX2 copies is at a level at least that without. -/
theorem softLevel_wide (v : GcmImpl) (lp : Option Loops) :
    (softLevel v false lp).level ≤ (softLevel v true lp).level :=
  join_mono_right _ (by unfold ownLevel; cases lp.isSome <;> decide)

/-- The level of the cleanup of `seal` and `open` in registers. -/
def regLevel (lp : Option Loops) : VecLevel := if lp.isSome then .avx else .sse

/-! ## In registers -/

/-- `Spec.GcmSiv.sealApi`'s function in registers, as emitted, over `v`'s
loops (`Impl.AesGcmSiv.X86_64.Fn.sealReg`), meets its contract in constant
time and returns without secret residue. -/
theorem sealReg_scrubbed (v : GcmImpl) :
    VerifiedScrubbed target (Impl.AesGcmSiv.X86_64.Fn.sealReg (regLevel (loopsOf v)) (loopsOf v))
      (Spec.GcmSiv.sealApi.contract X86_64.abi 784) 0 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.sealApi) (ks := (regLevel (loopsOf v)).level)
    (k := (regLevel (loopsOf v)).level) (n := fun _ => 0)
    (a := withStackArgScratch 776 2 (Impl.AesGcmSiv.X86_64.Fn.regSealCode (loopsOf v)))
    { suffix := v.suffix
      code := withStackArgScratch 776 2 (regSeal (loopsOf v))
      stack := 784
      verified := Proof.AesGcmSiv.seal_keyed (regSeal_framed v)
      spSafe := regSeal_sp v }
    _ (sealOut _) (Fill.refl _) (Nat.le_refl _) (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> lit_decide)

theorem sealReg_spSafeFn (v : GcmImpl) :
    (Impl.AesGcmSiv.X86_64.Fn.sealReg (regLevel (loopsOf v)) (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (regSeal_sp v)

/-- `Spec.GcmSiv.openApi`'s function in registers, as `sealReg_scrubbed`. -/
theorem openReg_scrubbed (v : GcmImpl) :
    VerifiedScrubbed target (Impl.AesGcmSiv.X86_64.Fn.openReg (regLevel (loopsOf v)) (loopsOf v))
      (Spec.GcmSiv.openApi.contract X86_64.abi 784) 32 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.openApi) (ks := (regLevel (loopsOf v)).level)
    (k := (regLevel (loopsOf v)).level) (n := fun _ => 0)
    (a := withStackArgScratch 776 2 (Impl.AesGcmSiv.X86_64.Fn.regOpenCode (loopsOf v)))
    { suffix := v.suffix
      code := withStackArgScratch 776 2 (regOpen (loopsOf v))
      stack := 784
      verified := Proof.AesGcmSiv.open_keyed (regOpen_framed v)
      spSafe := regOpen_sp v }
    _ (@openOut _) (Fill.refl _) (Nat.le_refl _) (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> lit_decide)

theorem openReg_spSafeFn (v : GcmImpl) :
    (Impl.AesGcmSiv.X86_64.Fn.openReg (regLevel (loopsOf v)) (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (regOpen_sp v)

/-! ## Over the callees -/

/-- `seal`'s code over the callees, in its frame, is its code over a stub of
each, with the callees' code where it calls them. -/
theorem seal_fill (v : GcmImpl) (wide : Bool) :
    Fill (softLevel v wide (loopsOf v)).level (fun _ => 0)
      (withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.Fn.sealCode stubCallees stubEcb wide (loopsOf v)))
      (withStackArgScratch 3848 2 (sealWith v wide (loopsOf v))) := by
  obtain ⟨l1, l2, l3, l4, -⟩ := softLevel_le v wide (loopsOf v)
  have h1 := calleeSide_mono l1 (Nat.le_refl 0) v.ctr.side
  have h2 := calleeSide_mono l2 (Nat.le_refl 0) v.key.side
  have h3 := calleeSide_mono l3 (Nat.le_refl 0) v.gh.side
  have h4 := calleeSide_mono l4 (Nat.le_refl 0) (ecbOf v).encSide
  generalize softLevel v wide (loopsOf v) = L at h1 h2 h3 h4 ⊢
  unfold sealWith
  cases loopsOf v <;> fill_calls_refl

/-- `open`'s, as `seal_fill`. -/
theorem open_fill (v : GcmImpl) (wide : Bool) :
    Fill (softLevel v wide (loopsOf v)).level (fun _ => 0)
      (withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.Fn.openCode stubCallees stubEcb wide (loopsOf v)))
      (withStackArgScratch 3848 2 (openWith v wide (loopsOf v))) := by
  obtain ⟨l1, l2, l3, l4, -⟩ := softLevel_le v wide (loopsOf v)
  have h1 := calleeSide_mono l1 (Nat.le_refl 0) v.ctr.side
  have h2 := calleeSide_mono l2 (Nat.le_refl 0) v.key.side
  have h3 := calleeSide_mono l3 (Nat.le_refl 0) v.gh.side
  have h4 := calleeSide_mono l4 (Nat.le_refl 0) (ecbOf v).encSide
  generalize softLevel v wide (loopsOf v) = L at h1 h2 h3 h4 ⊢
  unfold openWith
  cases loopsOf v <;> fill_calls_refl

/-- `Spec.GcmSiv.sealApi`'s function over `v`'s callees, as emitted
(`Impl.AesGcmSiv.X86_64.Fn.sealSoft`), meets its contract in constant time
and returns without secret residue. -/
theorem sealSoft_scrubbed (v : GcmImpl) (wide : Bool) :
    VerifiedScrubbed target
      (Impl.AesGcmSiv.X86_64.Fn.sealSoft (softLevel v wide (loopsOf v)) v.callees (ecbFn v) wide (loopsOf v))
      (Spec.GcmSiv.sealApi.contract X86_64.abi 3856) 0 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.sealApi) (ks := (ownLevel wide (loopsOf v)).level)
    (n := fun _ => 0)
    (a := withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.Fn.sealCode stubCallees stubEcb wide (loopsOf v)))
    { suffix := v.suffix
      code := withStackArgScratch 3848 2 (sealWith v wide (loopsOf v))
      stack := 3856
      verified := Proof.AesGcmSiv.seal_keyed (sealWith_framed v wide)
      spSafe := X86_64.withStackArgScratch_spSafe (sealWith_spSafe v wide) }
    _ (sealOut _) (seal_fill v wide) (softLevel_le v wide (loopsOf v)).2.2.2.2 (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> cases wide <;> lit_decide)

theorem sealSoft_spSafeFn (v : GcmImpl) (wide : Bool) :
    (Impl.AesGcmSiv.X86_64.Fn.sealSoft (softLevel v wide (loopsOf v)) v.callees (ecbFn v) wide (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (sealWith_spSafe v wide))

/-- `Spec.GcmSiv.openApi`'s function over `v`'s callees, as `sealSoft_scrubbed`. -/
theorem openSoft_scrubbed (v : GcmImpl) (wide : Bool) :
    VerifiedScrubbed target
      (Impl.AesGcmSiv.X86_64.Fn.openSoft (softLevel v wide (loopsOf v)) v.callees (ecbFn v) wide (loopsOf v))
      (Spec.GcmSiv.openApi.contract X86_64.abi 3856) 32 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.openApi) (ks := (ownLevel wide (loopsOf v)).level)
    (n := fun _ => 0)
    (a := withStackArgScratch 3848 2 (Impl.AesGcmSiv.X86_64.Fn.openCode stubCallees stubEcb wide (loopsOf v)))
    { suffix := v.suffix
      code := withStackArgScratch 3848 2 (openWith v wide (loopsOf v))
      stack := 3856
      verified := Proof.AesGcmSiv.open_keyed (openWith_framed v wide)
      spSafe := X86_64.withStackArgScratch_spSafe (openWith_spSafe v wide) }
    _ (@openOut _) (open_fill v wide) (softLevel_le v wide (loopsOf v)).2.2.2.2 (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> cases wide <;> lit_decide)

theorem openSoft_spSafeFn (v : GcmImpl) (wide : Bool) :
    (Impl.AesGcmSiv.X86_64.Fn.openSoft (softLevel v wide (loopsOf v)) v.callees (ecbFn v) wide (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (openWith_spSafe v wide))

/-! ## With the AVX2 copies -/

/-- `seal`'s code with the AVX2 copies, as `seal_fill`. -/
theorem sealAvx2_fill (v : GcmImpl) :
    Fill (softLevel v true (loopsOf v)).level (fun _ => 0)
      (Impl.AesGcmSiv.X86_64.Fn.sealAvx2Code stubCallees stubEcb (sivWide v) (loopsOf v)) (avx2SealCode v) := by
  have hw := seal_fill v true
  have hn := Fill.mono (softLevel_wide v (loopsOf v)) (seal_fill v false)
  unfold avx2SealCode Impl.AesGcmSiv.X86_64.Fn.sealAvx2Code Impl.AesGcmSiv.X86_64.Fn.bySize Code.iteCold
  exact Fill.ifp hw (.seq (.block _) (.ite _ (.seq (.seq (.block _) (.block _)) hw) hn))

/-- `open`'s, as `sealAvx2_fill`. -/
theorem openAvx2_fill (v : GcmImpl) :
    Fill (softLevel v true (loopsOf v)).level (fun _ => 0)
      (Impl.AesGcmSiv.X86_64.Fn.openAvx2Code stubCallees stubEcb (sivWide v) (loopsOf v)) (avx2OpenCode v) := by
  have hw := open_fill v true
  have hn := Fill.mono (softLevel_wide v (loopsOf v)) (open_fill v false)
  unfold avx2OpenCode Impl.AesGcmSiv.X86_64.Fn.openAvx2Code Impl.AesGcmSiv.X86_64.Fn.bySize Code.iteCold
  exact Fill.ifp hw (.seq (.block _) (.ite _ (.seq (.seq (.block _) (.block _)) hw) hn))

/-- `Spec.GcmSiv.sealApi`'s function with the AVX2 copies, as emitted
(`Impl.AesGcmSiv.X86_64.Fn.sealAvx2`), meets its contract in constant time
and returns without secret residue. -/
theorem sealAvx2_scrubbed (v : GcmImpl) :
    VerifiedScrubbed target
      (Impl.AesGcmSiv.X86_64.Fn.sealAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v))
      (Spec.GcmSiv.sealApi.contract X86_64.abi 3856) 0 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.sealApi) (ks := (ownLevel true (loopsOf v)).level)
    (n := fun _ => 0)
    (a := Impl.AesGcmSiv.X86_64.Fn.sealAvx2Code stubCallees stubEcb (sivWide v) (loopsOf v))
    { suffix := v.suffix ++ "_avx2"
      code := avx2SealCode v
      stack := 3856
      verified := Proof.AesGcmSiv.seal_keyed (avx2Seal_verified v)
      spSafe := avx2Seal_spSafe v }
    _ (sealOut _) (sealAvx2_fill v) (softLevel_le v true (loopsOf v)).2.2.2.2 (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> cases sivWide v <;> lit_decide)

theorem sealAvx2_spSafeFn (v : GcmImpl) :
    (Impl.AesGcmSiv.X86_64.Fn.sealAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (avx2Seal_spSafe v)

/-- `Spec.GcmSiv.openApi`'s function with the AVX2 copies, as `sealAvx2_scrubbed`. -/
theorem openAvx2_scrubbed (v : GcmImpl) :
    VerifiedScrubbed target
      (Impl.AesGcmSiv.X86_64.Fn.openAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v))
      (Spec.GcmSiv.openApi.contract X86_64.abi 3856) 32 :=
  verifiedScrubbedAllFill (api := Spec.GcmSiv.openApi) (ks := (ownLevel true (loopsOf v)).level)
    (n := fun _ => 0)
    (a := Impl.AesGcmSiv.X86_64.Fn.openAvx2Code stubCallees stubEcb (sivWide v) (loopsOf v))
    { suffix := v.suffix ++ "_avx2"
      code := avx2OpenCode v
      stack := 3856
      verified := Proof.AesGcmSiv.open_keyed (avx2Open_verified v)
      spSafe := avx2Open_spSafe v }
    _ (@openOut _) (openAvx2_fill v) (softLevel_le v true (loopsOf v)).2.2.2.2 (Nat.le_refl _)
    (ha := by rcases loopsOf_cases v with h | h | h <;> rw [h] <;> cases sivWide v <;> lit_decide)

theorem openAvx2_spSafeFn (v : GcmImpl) :
    (Impl.AesGcmSiv.X86_64.Fn.openAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (avx2Open_spSafe v)

/-! ## The registrations

Each binds a function as emitted (`Impl.AesGcmSiv.X86_64.Fn`) and its
theorem: in registers where `v` has the instructions (`sivReg`), else over
its callees. -/

/-- `vg_aes_gcm_siv_seal` over `v`. -/
def sealReg (v : GcmImpl) : Registration Spec.GcmSiv.sealApi X86_64.target :=
  if sivReg v then
    { suffix := v.suffix
      code := Impl.AesGcmSiv.X86_64.Fn.sealReg (regLevel (loopsOf v)) (loopsOf v)
      verified := .scrubbed (sealReg_scrubbed v)
      spSafe := sealReg_spSafeFn v }
  else
    { suffix := v.suffix
      code := Impl.AesGcmSiv.X86_64.Fn.sealSoft (softLevel v (sivWide v) (loopsOf v)) v.callees (ecbFn v)
        (sivWide v) (loopsOf v)
      verified := .scrubbed (sealSoft_scrubbed v (sivWide v))
      spSafe := sealSoft_spSafeFn v (sivWide v) }

/-- `vg_aes_gcm_siv_open` over `v`. -/
def openReg (v : GcmImpl) : Registration Spec.GcmSiv.openApi X86_64.target :=
  if sivReg v then
    { suffix := v.suffix
      code := Impl.AesGcmSiv.X86_64.Fn.openReg (regLevel (loopsOf v)) (loopsOf v)
      verified := .scrubbed (openReg_scrubbed v)
      spSafe := openReg_spSafeFn v }
  else
    { suffix := v.suffix
      code := Impl.AesGcmSiv.X86_64.Fn.openSoft (softLevel v (sivWide v) (loopsOf v)) v.callees (ecbFn v)
        (sivWide v) (loopsOf v)
      verified := .scrubbed (openSoft_scrubbed v (sivWide v))
      spSafe := openSoft_spSafeFn v (sivWide v) }

/-- `vg_aes_gcm_siv_seal` over `v`, with the AVX2 copies. -/
def wideSealReg (v : GcmImpl) : Registration Spec.GcmSiv.sealApi X86_64.target where
  suffix := v.suffix ++ "_avx2"
  code := Impl.AesGcmSiv.X86_64.Fn.sealAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)
  verified := .scrubbed (sealAvx2_scrubbed v)
  spSafe := sealAvx2_spSafeFn v

/-- `vg_aes_gcm_siv_open` over `v`, with the AVX2 copies. -/
def wideOpenReg (v : GcmImpl) : Registration Spec.GcmSiv.openApi X86_64.target where
  suffix := v.suffix ++ "_avx2"
  code := Impl.AesGcmSiv.X86_64.Fn.openAvx2 (softLevel v true (loopsOf v)) v.callees (ecbFn v) (sivWide v) (loopsOf v)
  verified := .scrubbed (openAvx2_scrubbed v)
  spSafe := openAvx2_spSafeFn v

end VG.Proof.AesGcmSiv.X86_64
