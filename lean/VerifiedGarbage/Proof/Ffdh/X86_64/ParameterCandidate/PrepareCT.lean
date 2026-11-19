module

public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
public import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRangeCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Montgomery
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Ffdh.X86_64.ParameterCandidate.PrepareConstantsCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.PrepareR2CT`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.PreparePrefix`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: public entry to the selected R² implementation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem preparePrefix_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs [.block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))]]) s
      fun t => ∃ mi', R2Pre ⟨⟨B, Z, w, mi'⟩, N⟩ t ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hO8 := Nat.le_trans (slot_le (w := w) (show aOne < 8 by decide)) hZ
  have hw31 : w < 2 ^ 31 := by omega_using [hw']
  have hN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := w) _ _ _ (by omega_using [hw]), hn, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact hodd
  simp only [seqs]
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun s₁ ⟨hg₁, hinv₁, _, hcx₁, h12₁, hm₁, k₁⟩ => ?_)
  generalize hmi : s₁.gpr .r15 = mi' at hg₁ hinv₁ hm₁
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_using [hZ, hnw])]; exact hn
  have hw0₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hm₁, hdrStore_word _ _ _ (by decide) (by decide) (by omega_using [hZ, hnw])]
  refine WP.seq (WP.mono (setWord_ok hg₁.scr hg₁.rdi hg₁.hdr hZ h12₁ (by omega_using [hw]) hw31 (o := aOne) (by decide) (ri := .rcx)
    (by decide) (i := 0) (by omega_using [hw]) hcx₁) fun s₂ ⟨_, ho₂, k₂⟩ => ?_)
  have ha₂ : Arrays B w [aOne] s₁.mem s₂.mem := Arrays.of_outside (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hg₂ : Good s₂ B Z w mi' := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ha₂.hdr hg₁.hdr⟩
  have hn₂ : wv s₂.mem B (slot w aN) w = N := by rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega_using [hZ, hnw])]; exact hn₁
  have hw0₂ : word s₂.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₂.word0_of_not_mem (by decide) (by decide) (by omega_using [hZ, hnw]) (by omega_using [hw])]; exact hw0₁
  have hl : InRegions (s₂.rd ++ s₂.wr) (off B (8 * sArr aN)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this])
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w aN) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hg₂.hdr.harr aN (by decide)]) rfl)
    fun t ⟨⟨h10, hm⟩, k⟩ => ?_
  have hgt : Good t B Z w mi' := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi, by rw [hm]; exact hg₂.hdr⟩
  exact ⟨mi', ⟨⟨hgt, hZ⟩, hw, hw', by rw [hm]; exact hn₂,
    by rw [hm, hw0₂]; exact hinv₁,
    ((k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁)), h10, hodd, hlo⟩,
    ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of inverse and R² setup -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.MlKem.X86_64

def R2Entry (d : PreparePublic) (s : State) : Prop := ∃ mi, R2Pre ⟨⟨d.I, d.IZ, d.w, mi⟩, d.N⟩ s

private theorem prefix_entry (d : PreparePublic) (s : State) (h : PrepareBefore d s) :
    WP isa (seqs [.block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))]]) s (R2Entry d) := by
  obtain ⟨⟨mi, hg, hd, _, _, _⟩, hn, ho, _, hlo⟩ := h
  exact WP.mono (preparePrefix_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128]) hn ho hlo)
    fun _ ⟨mi', hp, _⟩ => ⟨mi', hp⟩

private theorem entry_r2 {s₁ s₂ : State} (h : Two R2Entry s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun d t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨mi₁, hr₁⟩ := h₁
  obtain ⟨mi₂, hr₂⟩ := h₂
  have hr₁keep := hr₁
  have hr₂keep := hr₂
  obtain ⟨_, hw, _, hn₁, hi₁, _, _, ho, _⟩ := hr₁
  obtain ⟨_, _, _, hn₂, hi₂, _, _, _, _⟩ := hr₂
  change 2 ≤ d.w at hw
  have he₁ : (word t₁.mem d.I (slot d.w aN)).toNat = d.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.w) _ _ _ (by omega_using [hw]), hn₁]
  have he₂ : (word t₂.mem d.I (slot d.w aN)).toNat = d.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.w) _ _ _ (by omega_using [hw]), hn₂]
  rw [he₁] at hi₁
  rw [he₂] at hi₂
  have heq := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact ho) hi₁ hi₂
  cases heq
  exact ⟨_, hr₁keep, hr₂keep⟩

theorem prepareR2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two PrepareBefore) (prepareR2 R.code) fun _ _ => True := by
  unfold prepareR2
  refine RelCT.seqs_append (a := [.block prepareHead, setWord aOne .rcx,
      .block [.mov .r10 (.mem (hdr (sArr aN)))]]) (b := [R.code]) (by simp) (by simp) ?_
  exact RelCT.seq (two_post
    (two_map PreparePublic.inner (fun _ _ h => h.1.header) inner_preparePrefix_ct) prefix_entry)
    (R.ct.mono (fun _ _ h => entry_r2 h) (fun _ _ h => h))

theorem prepareR2_ready (M : Mont) (R : R2Impl M) (d : PreparePublic) (s : State) (h : PrepareBefore d s) :
    WP isa (prepareR2 R.code) s (R2Ready d) := by
  obtain ⟨⟨mi, hg, hd, hz, hw, hk⟩, hn, ho, hN, hlo⟩ := h
  refine WP.mono (prepareR2_ok M R hg hd.z (by omega_using [hd.w4])
    (by omega_using [hd.w128]) hn ho hlo) fun t ⟨mi', ht, hinv, hnt, hone, hr2, _, _, k⟩ => ?_
  exact ⟨mi', ht, hd, hz, k.2.2.trans hw, hk, hinv, hnt, hone, hr2, ho, hN⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of Montgomery constants -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

private theorem multiply_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (M.mm aY aR2 aOne) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, _, _, hN⟩ := h
  refine WP.mono (M.mm_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hi (by rw [hone, hn]; exact hN))
    fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

private theorem copy_header (d : PreparePublic) (s : State) (h : HeaderGood d s) :
    WP isa copyR1 s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk⟩ := h
  have hfit : slot d.w aR1 + 8 * (d.w + 2) ≤ d.IZ := by
    simp only [slot, aR1] at hz ⊢; omega_using [hz]
  refine WP.mono (copyToExt_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (a := aY) (d := aR1) (by decide) (by decide) hfit) fun t ⟨_, hf, k⟩ => ?_
  exact ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside hf (by unfold slot; omega_using [])⟩, hd, hz, k.2.2.trans hw, hk⟩

theorem prepareConstants_ct (M : Mont) :
    RelCT isa (Two R2Ready) (prepareConstants M.mm) fun _ _ => True := by
  unfold prepareConstants
  refine RelCT.seq (two_post
    (two_map (fun d : PreparePublic => (⟨d.I, d.IZ, d.w⟩ : Ws)) (fun _ _ h => by
      obtain ⟨mi, hg, hd, _, _, _, _⟩ := h; exact ⟨mi, hg, hd.z⟩)
      (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide))) (multiply_header M)) ?_
  exact RelCT.seq (two_post
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_copyR1_ct) copy_header)
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_negateR1_ct)

theorem prepareConstants_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (prepareConstants M.mm) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, hr2, ho, hN⟩ := h
  have hfit : slot d.w aRm1 + 8 * (d.w + 2) ≤ d.IZ := by simp only [slot, aRm1] at hz ⊢; omega_using [hz]
  refine WP.mono (prepareConstants_ok M hg hd.z hfit (by omega_using [hd.w4])
    (by omega_using [hd.w128]) hn hi hone ho hN hr2) fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundBodyCT`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundRunCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundResultCT`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: timing of a known round result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.RsaKeyGen.X86_64.Candidate (kFlag)
open VG.Proof.MlKem.X86_64

structure RunPublic where
  p : WitnessParams
  wr : List Region
  sp : Addr
  sample : Option Nat
  i : Nat
  checks : Nat

def RunContext (d : RunPublic) (s : State) : Prop :=
  ∃ rp used bs, DrawState d.p rp used bs s ∧ RoundRoom d.p rp bs s ∧ s.gpr .rsp = d.sp ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 d.i ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ d.i < 2 ^ 31 ∧ d.checks < 2 ^ 31

theorem RunContext.link {d : RunPublic} {s : State} (h : RunContext d s) :
    LinkHeader ⟨d.p.O, d.wr⟩ s := by
  obtain ⟨_, _, _, ht, _, _, hw, hk, _⟩ := h
  exact ⟨hk, ht.ready.good.rdi, hw, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact ht.link⟩

def FlagBefore (d : RunPublic) (s : State) : Prop := RunContext d s ∧
  word s.mem d.p.I (8 * kFlag) = mask (Spec.Ffdh.mrRound d.p.N (d.sample.getD 0))

def FlagAfter (d : RunPublic) (s : State) : Prop := LinkHeader ⟨d.p.O, d.wr⟩ s ∧
  s.zf = some (!(Spec.Ffdh.mrRound d.p.N (d.sample.getD 0)))

private theorem flag_after (d : RunPublic) (s : State) (h : FlagBefore d s) :
    WP isa (.block [.mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)]) s (FlagAfter d) := by
  obtain ⟨rp, used, bs, ht, _, _, hw, hk, _⟩ := h.1
  refine WP.mono (roundFlag_ok ht.ready.good.scr (by
    have hz := d.p.dims.z; unfold slot VG.Impl.Bignum.hdrBytes at hz; omega_using [hz])
    ht.ready.good.rdi h.2) fun t ⟨hz, hm, k⟩ => ?_
  refine ⟨⟨hk, (k.gpr (by decide)).trans ht.ready.good.rdi, k.2.2.trans hw, ?_⟩, hz⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  rw [hm]; exact ht.link

theorem roundResult_ct : RelCT isa (Two FlagBefore) roundResult fun _ _ => True := by
  unfold roundResult
  refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact h₁.1.choose_spec.choose_spec.choose_spec.1.ready.good.rdi.trans
      h₂.1.choose_spec.choose_spec.choose_spec.1.ready.good.rdi.symm)
    (by taint_decide) flag_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1) roundFail_ct
  · exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1) roundPass_ct

theorem roundResult_link (d : RunPublic) (s : State) (h : FlagBefore d s) :
    WP isa roundResult s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  obtain ⟨rp, used, bs, ht, _, _, hw, hk, hi, hc, hi32, hc32⟩ := h.1
  refine WP.mono (roundResult_ok ht h.2 hi hc hi32 hc32)
    fun t ⟨ht', _, _, _, _, k⟩ => ?_
  exact ⟨hk, ht'.ready.good.rdi, k.2.2.trans hw, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact ht'.link⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of an optional sampled round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def SampleAt (d : RunPublic) (s : State) : Prop := match d.sample with
  | none => word s.mem d.p.O (8 * oStatus) = 0
  | some a => word s.mem d.p.O (8 * oStatus) = 1 ∧ wv s.mem d.p.I (slot d.p.w aXm) d.p.w = a

def RunBefore (d : RunPublic) (s : State) : Prop := RunContext d s ∧ SampleAt d s

def RunFlagged (d : RunPublic) (s : State) : Prop := RunBefore d s ∧ s.zf = some d.sample.isNone

def LiveRun (d : RunPublic) (s : State) : Prop := RunBefore d s ∧ d.sample.isSome = true

private theorem status_after (d : RunPublic) (s : State) (h : RunBefore d s) :
    WP isa (.block statusTest) s (RunFlagged d) := by
  obtain ⟨rp, used, bs, ht, hroom, hsp, hw, hk, hi, hc, hi32, hc32⟩ := h.1
  have houter : Scr s d.p.O 256 := by
    simpa [off] using ht.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  have hstatus : word s.mem d.p.O (8 * oStatus) = BitVec.ofNat 64 (if d.sample.isSome then 1 else 0) := by
    cases he : d.sample with
    | none => simpa [SampleAt, he] using h.2
    | some a =>
      have hh := h.2
      simp only [SampleAt, he] at hh
      simpa [he] using hh.1
  have hsmall : (if d.sample.isSome then 1 else 0) < 2 ^ 64 := by split <;> decide
  refine WP.mono (statusTest_ok ht.ready.good.scr d.p.space_bounds.2.1 houter ht.ready.good.rdi
    ht.link hstatus hsmall) fun t ⟨hz, hm, k⟩ => ?_
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨⟨rp, used, bs, ht.same_mem hm k ((k.gpr (by decide)).trans ht.ready.good.rdi),
    hroom.congr hst, hst.trans hsp, k.2.2.trans hw, hk, by rw [hm]; exact hi, by rw [hm]; exact hc, hi32, hc32⟩, ?_⟩, ?_⟩
  · simpa only [SampleAt, hm] using h.2
  · have he : decide ((if d.sample.isSome then 1 else 0) = 0) = d.sample.isNone := by
      cases d.sample <;> rfl
    simpa only [he] using hz

private theorem live_witness {d : RunPublic} {s : State} (h : LiveRun d s) :
    wv s.mem d.p.I (slot d.p.w aXm) d.p.w = d.sample.getD 0 := by
  cases he : d.sample with
  | none =>
    have hx := h.2
    simp only [he, Option.isSome_none, Bool.false_eq_true] at hx
  | some a =>
    have hx := h.1.2
    simp only [SampleAt, he] at hx
    simpa only [he, Option.getD_some] using hx.2

private theorem live_before {d : RunPublic} {s : State} (h : LiveRun d s) :
    BeforeRound ⟨⟨d.p.I, d.p.IZ, d.p.w⟩, d.p.N, d.sample.getD 0, d.sp⟩ s := by
  obtain ⟨_, _, _, ht, hroom, hsp, _, _, _⟩ := h.1.1
  refine ⟨d.p.mi, ht.ready, d.p.dims, ?_, hroom.call, hsp, d.p.odd, d.p.n3, live_witness h⟩
  change slot d.p.w 28 ≤ d.p.Z - 256
  omega_using [d.p.room]

private theorem live_round (M : Mont) (K : Kernel) (d : RunPublic) (s : State) (h : LiveRun d s) :
    WP isa (witnessRound M.mm K.run) s (FlagBefore d) := by
  obtain ⟨rp, used, bs, ht, hroom, hsp, hw, hk, hi, hc, hi32, hc32⟩ := h.1.1
  refine WP.mono (witnessRound_state_ok M K ht hroom (live_witness h))
    fun t ⟨ht', hflag, hwords, _, k⟩ => ?_
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨⟨rp, used, bs, ht', hroom.congr hst, hst.trans hsp, k.2.2.trans hw, hk,
    (hwords _ (by decide)).trans hi, (hwords _ (by decide)).trans hc, hi32, hc32⟩, hflag⟩

theorem roundRun_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two RunBefore) (roundRun M.mm K.run)
      (Two fun (d : RunPublic) s => LinkHeader ⟨d.p.O, d.wr⟩ s) := by
  unfold roundRun
  refine RelCT.seq (two_post
    (two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) statusTest_ct)
    status_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2])
    (two_piece [] (VG.Proof.RsaKeyGen.X86_64.pins_nil _) (by taint_decide)
      (fun _ _ h => WP.block_nil h.1.1.1.link)) ?_
  have hc : RelCT isa (Two LiveRun) (.seq (witnessRound M.mm K.run) roundResult)
      (Two fun (d : RunPublic) s => LinkHeader ⟨d.p.O, d.wr⟩ s) :=
    RelCT.seq (two_post
      (two_map (fun d : RunPublic => (⟨⟨d.p.I, d.p.IZ, d.p.w⟩, d.p.N, d.sample.getD 0, d.sp⟩ : RoundPublic))
        (fun _ _ h => live_before h) (witnessRound_ct M K)) (live_round M K)) (two_post roundResult_ct roundResult_link)
  refine hc.mono ?_ (fun _ _ h => h)
  rintro s₁ s₂ ⟨d, h₁, h₂⟩
  have hs : d.sample.isSome = true := by
    have hx : d.sample.isNone = false := by simpa only [eval, h₁.1.2, Option.some.injEq] using h₁.2
    cases he : d.sample <;> simp_all
  exact ⟨d, ⟨h₁.1.1, hs⟩, ⟨h₂.1.1, hs⟩⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.CutRestoreCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawCTData`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: public witness-sampling state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

structure DrawPublic where
  p : WitnessParams
  rp : Addr
  used : Nat
  bs : List Byte
  wr : List Region

def DrawBefore (d : DrawPublic) (s : State) : Prop :=
  DrawState d.p d.rp d.used d.bs s ∧ s.wr = d.wr ∧ InnerKW d.p.O d.wr

theorem DrawBefore.link {d : DrawPublic} {s : State} (h : DrawBefore d s) :
    LinkHeader ⟨d.p.O, d.wr⟩ s :=
  ⟨h.2.2, h.1.ready.good.rdi, h.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact h.1.link⟩

def DrawPublic.inner (d : DrawPublic) : InnerPublic :=
  ⟨d.p.O, d.p.w, d.wr, d.p.op, d.p.len, 0⟩

/-- A byte cut temporarily uses RDI for the output buffer; the saved
modulus words still belong to the inner frame. -/
structure CutBefore (d : DrawPublic) (s : State) : Prop where
  retained : ∃ s₀ : State, ModulusReady s₀ d.p.I d.p.IZ d.p.w d.p.mi d.p.N ∧ s.wr = s₀.wr ∧
    ∀ off, off + 8 ≤ d.p.IZ → word s.mem d.p.I off = word s₀.mem d.p.I off
  scr : Scr s d.p.O d.p.Z
  link : word s.mem d.p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = d.p.O
  outPtr : word s.mem d.p.O (8 * oOut) = d.p.op
  len : word s.mem d.p.O (8 * oWitnessLen) = BitVec.ofNat 64 d.p.len
  rdi : s.gpr .rdi = d.p.op
  rsi : s.gpr .rsi = d.rp
  rbp : s.gpr .rbp = d.p.I
  rcx : s.gpr .rcx = BitVec.ofNat 64 d.p.len
  rdx : s.gpr .rdx = BitVec.ofNat 64 d.p.bits
  src : Src s d.p.O d.p.Z d.rp (d.bs.take d.p.len)
  out : OutOk s d.p.O d.p.Z d.p.op d.p.len
  apart : Apart d.p.op d.p.len d.rp (d.bs.take d.p.len).length
  available : d.p.len ≤ d.bs.length
  wr : s.wr = d.wr
  kw : InnerKW d.p.O d.wr

theorem drawSetup_cut (d : DrawPublic) (s : State) (h : DrawBefore d s) (ha : d.p.len ≤ d.bs.length) :
    WP isa (.block drawSetup) s (CutBefore d) := by
  have houter : Scr s d.p.O 256 := by
    simpa [off] using h.1.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  refine WP.mono (drawSetup_ok h.1.ready.good.scr d.p.space_bounds.2.1 houter h.1.ready.good.rdi
    h.1.link h.1.outPtr h.1.ptr h.1.left h.1.usedWord h.1.len h.1.bits
    (by omega_using [d.p.width_bounds.2.2.2.1]) ha)
    fun t ⟨hm, hsi, hdi, hbp, hcx, hdx, k⟩ => ?_
  have hf : Frm d.p.O [(8 * oRandPtr, 24)] s.mem t.mem := by rw [hm]; exact advanceMem_frame _ _ _ _ _ _
  have hi : InScr d.p.O d.p.Z s.mem t.mem := InScr.of_frm hf (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    change 120 ≤ d.p.Z; omega_using [d.p.space_bounds.1])
  have hw : ∀ off, off + 8 ≤ d.p.IZ → word t.mem d.p.I off = word s.mem d.p.I off :=
    outer_words (Z := d.p.IZ) hf (by simp [oRandPtr]) (by
      have hz64 := Nat.le_trans (Nat.le_add_left _ _) h.1.scr.nowrap
      omega_using [hz64, d.p.space_bounds.2.2])
  have hh : ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → word t.mem d.p.O (8 * j) = word s.mem d.p.O (8 * j) := by
    intro j hj h12 h13 h14
    apply hf.word_eq
    · intro r hr; simp only [List.mem_singleton] at hr; subst r
      change 8 * j + 8 ≤ 96 ∨ 120 ≤ 8 * j; omega_using [h12, h13, h14]
    · omega_using [hj]
  exact ⟨⟨s, h.1.ready, k.2.2, hw⟩, h.1.scr.congr k.2.2,
    (hw _ d.p.space_bounds.2.1).trans h.1.link,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.1.outPtr,
    (hh _ (by decide) (by decide) (by decide) (by decide)).trans h.1.len,
    hdi, hsi, hbp, hcx, hdx, source_take (h.1.rand.congrK hi k) d.p.len,
    ⟨fun i hi => by rw [k.2.2]; exact h.1.out.wr i hi, h.1.out.sep⟩,
    fun i hi j hj => h.1.apart i hi j (by rw [List.length_take] at hj; omega_using [hj]), ha,
    k.2.2.trans h.2.1, h.2.2⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of masking and workspace restoration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Rsa.X86_64.Crt (sLink ws)
open VG.Proof.MlKem.X86_64

structure CutAfter (d : DrawPublic) (s : State) : Prop where
  rbp : s.gpr .rbp = d.p.I
  link : word s.mem d.p.I (8 * sLink) = d.p.O
  wr : s.wr = d.wr
  kw : InnerKW d.p.O d.wr

private theorem cutBefore_pins : Pins CutBefore [.rdi, .rsi, .rcx, .rdx] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h₁.rdi.trans h₂.rdi.symm
  · exact h₁.rsi.trans h₂.rsi.symm
  · exact h₁.rcx.trans h₂.rcx.symm
  · exact h₁.rdx.trans h₂.rdx.symm

private theorem cut_after (d : DrawPublic) (s : State) (h : CutBefore d s) :
    WP isa witnessCut s (CutAfter d) := by
  have hlen : (d.bs.take d.p.len).length = d.p.len := by rw [List.length_take, Nat.min_eq_left h.available]
  refine WP.mono (witnessCut_ok (by omega_using [d.p.bits1]) d.p.bits2
    (show (d.bs.take d.p.len).length = (d.p.bits + 7) / 8 from hlen) h.rsi h.rdi
    (by rw [hlen]; exact h.rcx) h.rdx h.src.rd (fun i hi => h.out.wr i (by omega_using [hlen, hi]))
    (fun i hi => by
      rw [h.src.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => h.apart j (by omega_using [hlen, hj]) i hi he.symm))
    fun t ⟨_, _, hf, k⟩ => ?_
  have hfi : OutOk s d.p.I d.p.IZ d.p.op d.p.len :=
    output_inner h.out (Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap)
  have hframe : ∀ a, (∀ i < d.p.len, a ≠ off d.p.op i) → t.mem a = s.mem a := by simpa only [hlen] using hf
  have hw := words_outside_bytes (show d.p.IZ ≤ 2 ^ 64 by
    have hz64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
    unfold WitnessParams.IZ; omega_using [hz64]) hframe hfi.sep
  exact ⟨(k.gpr (by decide)).trans h.rbp,
    (hw _ d.p.space_bounds.2.1).trans h.link, k.2.2.trans h.wr, h.kw⟩

private theorem cutAfter_restore (d : DrawPublic) (s : State) (h : CutAfter d s) :
    WP isa (.block [.mov .rdi (.reg .rbp)]) s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = d.p.I ∧ t.mem = s.mem)
    (by xrun [h.rbp]) rfl) fun t ⟨⟨hd, hm⟩, k⟩ => ?_
  refine ⟨h.kw, hd, k.2.2.trans h.wr, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  rw [hm]; exact h.link

private theorem drawLoad_ct : RelCT isa (Two CutAfter) (.block drawLoad) fun _ _ => True := by
  unfold drawLoad
  change RelCT isa (Two CutAfter) (.block ([.mov .rdi (.reg .rbp)] ++ _)) _
  refine RelCT.block_append (RelCT.seq
    (two_piece [.rbp] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h₁.rbp.trans h₂.rbp.symm)
      (by taint_decide) cutAfter_restore) ?_)
  exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) drawLoadTail_ct

theorem cutRestore_ct : RelCT isa (Two CutBefore) cutRestore fun _ _ => True := by
  unfold cutRestore
  exact RelCT.seq (two_post (witnessCut_ct cutBefore_pins) cut_after) drawLoad_ct

theorem cutRestore_inner (d : DrawPublic) (s : State) (h : CutBefore d s) :
    WP isa cutRestore s (InnerNumber d.inner) := by
  obtain ⟨s₀, hr, hwr, hw⟩ := h.retained
  refine WP.mono (cutRestore_ok hr hwr hw h.scr h.link h.outPtr h.len h.rdi h.rsi h.rbp h.rcx h.rdx
    h.src h.out h.apart (by rw [List.length_take, Nat.min_eq_left h.available]))
    fun t ⟨ht, hsi, hcx, _, _, _, _, k⟩ => ?_
  exact ⟨⟨h.kw, VG.Proof.RsaKeyGen.X86_64.good_hp ht.good (k.2.2.trans h.wr)⟩, hsi, hcx⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawLoopCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawBodyCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.DrawSampleCT`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: timing of one sampled witness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawAvailable (d : DrawPublic) (s : State) : Prop := DrawBefore d s ∧ d.p.len ≤ d.bs.length

theorem drawPrefix_ct : RelCT isa (Two DrawAvailable) drawPrefix fun _ _ => True := by
  unfold drawPrefix cutLoad
  refine RelCT.seq (two_post
    (two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) drawSetup_ct)
    (fun d s h => drawSetup_cut d s h.1 h.2)) ?_
  exact RelCT.seq (two_post cutRestore_ct cutRestore_inner)
    (two_map DrawPublic.inner (fun _ _ h => h) inner_loadWitness_ct)

def SampleLoaded (d : DrawPublic) (s : State) : Prop :=
  DrawState d.p (off d.rp d.p.len) (d.used + d.p.len) (d.bs.drop d.p.len) s ∧
    wv s.mem d.p.I (slot d.p.w aXm) d.p.w = Spec.Rsa.os2ip (d.bs.take d.p.len) % 2 ^ d.p.bits ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr

private theorem prefix_loaded (d : DrawPublic) (s : State) (h : DrawAvailable d s) :
    WP isa drawPrefix s (SampleLoaded d) :=
  WP.mono (drawPrefix_ok h.1.1 h.2) fun _ ⟨ht, hx, _, _, k⟩ => ⟨ht, hx, k.2.2.trans h.1.2.1, h.1.2.2⟩

private theorem loaded_range (d : DrawPublic) (s : State) (h : SampleLoaded d s) :
    WP isa witnessRange s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  refine WP.mono (witnessRange_ok h.1.ready d.p.dims d.p.odd h.2.1)
    fun t ⟨_, _, ht, _, hf, k⟩ => ?_
  have hlo : ∀ r ∈ [(slot d.p.w aTmp, 8 * d.p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)],
      136 ≤ r.1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold slot VG.Impl.Bignum.hdrBytes aTmp; omega_using []
    · decide
  refine ⟨h.2.2.2, ht.good.rdi, k.2.2.trans h.2.2.1, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  exact (inner_link hf hlo).trans h.1.link

theorem drawSample_ct : RelCT isa (Two DrawAvailable) drawSample fun _ _ => True := by
  unfold drawSample
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post drawPrefix_ct prefix_loaded) (RelCT.seq (two_post ?_ loaded_range) ?_)
  · refine two_map (fun d : DrawPublic => (⟨d.p.I, d.p.IZ, d.p.w⟩ : Ws)) (fun d _ h => ?_) witnessRange_ct
    exact ⟨⟨d.p.mi, h.1.ready.good, d.p.dims.z⟩,
      by change 1 ≤ d.p.w; omega_using [d.p.width_bounds.1],
      by change d.p.w < 2 ^ 31; omega_using [d.p.width_bounds.2.1]⟩
  · exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) drawFinish_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of a rejection-sampling step -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

def DrawHeadAfter (d : DrawPublic) (s : State) : Prop :=
  DrawBefore d s ∧ s.cf = some (decide (d.bs.length < d.p.len))

private theorem head_after (d : DrawPublic) (s : State) (h : DrawBefore d s) :
    WP isa (.block drawHead) s (DrawHeadAfter d) := by
  have houter : Scr s d.p.O 256 := by
    simpa [off] using h.1.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  refine WP.mono (drawHead_ok h.1.ready.good.scr d.p.space_bounds.2.1 houter h.1.ready.good.rdi
    h.1.link h.1.left h.1.len (by omega_using [h.1.countBound])
    (by omega_using [d.p.width_bounds.2.2.2.1])) fun t ⟨hcf, hm, k⟩ => ?_
  exact ⟨⟨h.1.same_mem hm k ((k.gpr (by decide)).trans h.1.ready.good.rdi),
    k.2.2.trans h.2.1, h.2.2⟩, hcf⟩

theorem drawBody_ct : RelCT isa (Two DrawBefore) drawBody fun _ _ => True := by
  unfold drawBody
  refine RelCT.seq (two_post
    (two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.link) drawHead_ct)
    head_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.link) drawShort_ct
  · refine two_map (fun d : DrawPublic => d) (fun d s h => ?_) drawSample_ct
    refine ⟨h.1.1, ?_⟩
    have hx : decide (d.bs.length < d.p.len) = false := by simpa only [eval, h.1.2, Option.some.injEq] using h.2
    omega_using [of_decide_eq_false hx]

def DrawAfter (d : DrawPublic) (s : State) : Prop :=
  (if d.p.len ≤ d.bs.length then
    DrawState d.p (off d.rp d.p.len) (d.used + d.p.len) (d.bs.drop d.p.len) s ∧
      s.zf = some (!decide (2 ≤ drawValue d.p d.bs ∧ drawValue d.p d.bs < d.p.N - 1))
   else DrawState d.p d.rp d.used d.bs s ∧ s.zf = some false) ∧
    s.wr = d.wr ∧ InnerKW d.p.O d.wr

theorem drawBody_after (d : DrawPublic) (s : State) (h : DrawBefore d s) :
    WP isa drawBody s (DrawAfter d) := by
  refine WP.mono (drawBody_ok h.1) fun t ⟨hstep, _, _, k⟩ => ?_
  refine ⟨?_, k.2.2.trans h.2.1, h.2.2⟩
  by_cases ha : d.p.len ≤ d.bs.length
  · simp only [ite_eq_left ha] at hstep ⊢
    exact ⟨hstep.1, hstep.2.2.1⟩
  · simp only [ite_eq_right ha] at hstep ⊢
    exact ⟨hstep.1, hstep.2.1⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of uniform rejection sampling -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private def drawInv (n : Nat) : State → State → Prop :=
  Two fun d s => d.bs.length = n ∧ DrawBefore d s

private theorem draw_step (n : Nat) : RelCT isa (drawInv n) drawBody fun s₁ s₂ =>
    isa.eval .e s₁ = isa.eval .e s₂ ∧ (isa.eval .e s₁ = some false → True) ∧
      (isa.eval .e s₁ = some true → ∃ m < n, drawInv m s₁ s₂) := by
  have hc : RelCT isa (drawInv n) drawBody
      (Two fun d s => d.bs.length = n ∧ DrawAfter d s) :=
    two_post (two_map (fun d : DrawPublic => d) (fun _ _ h => h.2) drawBody_ct)
      (fun d s h => WP.mono (drawBody_after d s h.2) fun _ ht => ⟨h.1, ht⟩)
  refine hc.mono (fun _ _ h => h) ?_
  rintro s₁ s₂ ⟨d, ⟨hsize, h₁⟩, ⟨_, h₂⟩⟩
  by_cases ha : d.p.len ≤ d.bs.length
  · simp only [DrawAfter, ite_eq_left ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, fun _ => ?_⟩
    let d' : DrawPublic := { d with rp := off d.rp d.p.len, used := d.used + d.p.len, bs := d.bs.drop d.p.len }
    refine ⟨d'.bs.length, ?_, d', ⟨rfl, ⟨h₁.1.1, h₁.2⟩⟩, ⟨rfl, ⟨h₂.1.1, h₂.2⟩⟩⟩
    change (d.bs.drop d.p.len).length < n
    rw [List.length_drop]
    omega_using [ha, hsize, d.p.width_bounds.2.2.1]
  · simp only [DrawAfter, ite_eq_right ha] at h₁ h₂
    refine ⟨by simp only [eval, h₁.1.2, h₂.1.2], fun _ => trivial, ?_⟩
    intro he
    simp only [eval, h₁.1.2, Option.some.injEq, Bool.false_eq_true] at he

theorem drawWitness_ct : RelCT isa (Two DrawBefore) drawWitness fun _ _ => True := by
  rintro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨d, h₁, h₂⟩ e₁ e₂
  exact RelCT.loop drawInv draw_step d.bs.length s₁ s₂ tr₁ tr₂ t₁ t₂
    ⟨d, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩ e₁ e₂

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of a complete policy iteration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

structure PolicyPublic extends DrawPublic where
  sp : Addr
  i : Nat
  checks : Nat

def PolicyBefore (d : PolicyPublic) (s : State) : Prop :=
  DrawBefore d.toDrawPublic s ∧ RoundRoom d.p d.rp d.bs s ∧ s.gpr .rsp = d.sp ∧
    word s.mem d.p.O (8 * oIndex) = BitVec.ofNat 64 d.i ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ d.i < 2 ^ 31 ∧ d.checks < 2 ^ 31

def PolicyPublic.run (d : PolicyPublic) : RunPublic :=
  ⟨d.p, d.wr, d.sp, (Spec.Ffdh.drawWitness d.p.N d.bs).map Prod.fst, d.i, d.checks⟩

private theorem witness_run (d : PolicyPublic) (s : State) (h : PolicyBefore d s) :
    WP isa drawWitness s (RunBefore d.run) := by
  obtain ⟨hd, hroom, hsp, hi, hc, hi32, hc32⟩ := h
  refine WP.mono (drawWitness_ok hd.1) fun t ⟨n, _, ht, hresult, _, hsaved, _, k⟩ => ?_
  refine ⟨⟨off d.rp n, d.used + n, d.bs.drop n, ht,
    hroom.after_draw k (by decide) n, (k.gpr (by decide)).trans hsp,
    k.2.2.trans hd.2.1, hd.2.2,
    (hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi,
    (hsaved _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc,
    hi32, hc32⟩, ?_⟩
  cases he : Spec.Ffdh.drawWitness d.p.N d.bs with
  | none => simpa only [SampleAt, PolicyPublic.run, he, Option.map_none] using hresult
  | some ar =>
    obtain ⟨a, rest⟩ := ar
    simp only [he] at hresult
    simpa only [SampleAt, PolicyPublic.run, he, Option.map_some] using And.intro hresult.1 hresult.2.2

theorem roundBody_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two PolicyBefore) (roundBody M.mm K.run) fun _ _ => True := by
  unfold roundBody
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map PolicyPublic.toDrawPublic (fun _ _ h => h.1) drawWitness_ct) witness_run) ?_
  refine RelCT.seq (two_map PolicyPublic.run (fun _ _ h => h) (roundRun_ct M K)) ?_
  exact two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) statusMore_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of complete modulus preparation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

theorem prepareModulus_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two PrepareBefore) (prepareModulus M.mm R.code) fun _ _ => True := by
  unfold prepareModulus
  exact RelCT.seq (two_post (prepareR2_ct M R) (prepareR2_ready M R))
    (RelCT.seq (two_post (prepareConstants_ct M) (prepareConstants_header M))
      (two_map PreparePublic.inner (fun _ _ h => h.header) inner_expSetup_ct))

end VG.Proof.Ffdh.X86_64.ParameterCandidate
