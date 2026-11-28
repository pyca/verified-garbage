module

-- separate module: the calls of forsSign and xmssTree, rebuilt only when their contracts or Ctx change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignCtx
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: the calls of `forsSign` and `xmssTree`

Each from a state of `Ctx` where `x0 = S`, its output (`x1` for `forsSign`,
`x2` for `xmssTree`) a part of `sig`, and the lanes hold `Env`: the call
keeps `Ctx`, as what the internal functions change is free (`changes_free`),
and the callee-saved registers but `x30`; its postcondition gives the rest
(`forsCall_ok`, `xmssCall_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)

theorem changes_in {p : Params} (hz : Sz p) {σ : State} :
    ∀ r ∈ changes p (σ.gpr .x7), Region.Sub r (SCR σ) ∧ r.Disjoint (PROT σ) := by
  have hn := hz.n32
  have hsc : scratchLen = 65536 := rfl
  intro r hr
  have hfree : ∀ {o l : Nat}, o + l ≤ scratchLen → (o + l ≤ Layout.oTop ∨ Layout.oTop + 256 ≤ o) →
      Region.Sub ⟨at' (σ.gpr .x7) o, l⟩ (SCR σ) ∧ Region.Disjoint ⟨at' (σ.gpr .x7) o, l⟩ (PROT σ) := fun {o l} h₁ h₂ =>
    ⟨Offset.sub_base _ h₁, Offset.disjoint _ (by simp only [Layout.oTop] at h₂ ⊢; omega) (by omega)
      (by simp only [Layout.oTop]; omega)⟩
  simp only [changes, laneTails, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hr
  rcases hr with ((h | h) | ⟨k, hk, h | h⟩) | (h | h | h | h | h) <;> subst h
  · have := hfree (o := 0) (l := workUsed) (by simp only [workUsed]; omega) (by simp only [workUsed, Layout.oTop]; omega)
    simpa using this
  · exact hfree (by simp only [Layout.oVars, Layout.frameLen]; omega) (by simp only [Layout.oVars, Layout.frameLen, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.laneA, Layout.oA, Layout.strideA]; omega)
      (by simp only [Layout.laneA, Layout.oA, Layout.strideA, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)
      (by simp only [Layout.laneB, Layout.oB, Layout.strideB, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.oDigits]; omega) (by simp only [Layout.oDigits, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.oN, Layout.nodeSlots]; omega) (by simp only [Layout.oN, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.oRoots, Layout.oN, Layout.nodeSlots]; omega)
      (by simp only [Layout.oRoots, Layout.oN, Layout.nodeSlots, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.oMsg]; omega) (by simp only [Layout.oMsg, Layout.oTop]; omega)
  · exact hfree (by simp only [Layout.oFidx]; omega) (by simp only [Layout.oFidx, Layout.oTop]; omega)

theorem changes_free {p : Params} (hz : Sz p) {σ : State} : ∀ r ∈ changes p (σ.gpr .x7), Free p σ r :=
  fun r hr => .inl (changes_in hz r hr)

/-- A part of `sig`, with the regions a call of an internal function writing it is given. -/
theorem call_covers {p : Params} {σ t : State} (hK : SG p σ) (hc : Ctx p σ t) {off l : Nat}
    (hl : off + l ≤ p.sigLen) :
    Covers ([] ++ [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩]) (t.rd ++ t.wr) ∧
      Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩] t.wr := by
  have hw : Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩] t.wr := by
    rw [hc.wr, hK.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_self .., off, rfl, hl⟩
  exact ⟨by rw [List.nil_append]; exact Covers.right hw, hw⟩

/-- `SK.seed`, from the keys `Ctx` keeps. -/
theorem Ctx.skAt {p : Params} {σ t : State} (hc : Ctx p σ t) :
    SkAt p t.mem (σ.gpr .x7) (bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * 0)) p.n) := hc.keys 0 (by decide)

/-- A part of `sig` as the output of an internal function. -/
theorem part_regions {p : Params} (hsl : p.sigLen < 2 ^ 63) {σ : State} (hK : SG p σ) {off l : Nat}
    (hl : off + l ≤ p.sigLen) (hl0 : 0 < l) :
    (σ.gpr .x6 + BitVec.ofNat 64 off).toNat + l ≤ 2 ^ 64 ∧
      Region.Disjoint ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩ ⟨σ.gpr .x7, Layout.oSigTmp⟩ := by
  have hf := hK.f_sig
  have eT : Layout.oSigTmp = 30144 := rfl
  have hsc : scratchLen = 65536 := rfl
  refine ⟨?_, (hK.sig_scr.sub_left (Offset.sub_base _ hl)).sub_right (Region.sub_prefix (by omega))⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem xmssCall_ok {p : Params} (hz : Sz p) (hsl : p.sigLen < 2 ^ 63) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    {σ u : State} (hK : SG p σ) (hc : Ctx p σ u) (h0 : u.gpr .x0 = σ.gpr .x7) (h1 : (u.gpr .x1).toNat < 2 ^ 32)
    {off : Nat} (h2 : u.gpr .x2 = σ.gpr .x6 + BitVec.ofNat 64 off) (hoff : off + p.xmssSigLen ≤ p.sigLen)
    (hxp : 0 < p.xmssSigLen)
    {pkSeed a16 : List Byte} (henv : Env p u.mem (σ.gpr .x7) pkSeed a16) {Q : State → Prop}
    (k : ∀ s', Ctx p σ s' → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r) →
      Env p s'.mem (σ.gpr .x7) pkSeed a16 →
      bytesAt s'.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
        xmssNode p (bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * 0)) p.n) 0 p.hp pkSeed (treeAdrs a16) →
      ((u.gpr .x1).toNat < 2 ^ p.hp → bytesAt s'.mem (σ.gpr .x6 + BitVec.ofNat 64 off) p.xmssSigLen =
        xmssSign p (bytesAt u.mem (at' (σ.gpr .x7) Layout.oMsg) p.n)
          (bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * 0)) p.n) (u.gpr .x1).toNat pkSeed (treeAdrs a16)) →
      Frame (changes p (σ.gpr .x7) ++ [⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩]) u.mem s'.mem → Q s') :
    WP isa (.call f.xmssName (Impl.SlhDsa.AArch64.Shake.xmssCode p f)) u Q := by
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain ⟨hcv, hcw⟩ := call_covers (l := p.xmssSigLen) hK hc hoff
  obtain ⟨hfo, hdo⟩ := part_regions hsl hK hoff hxp
  refine WP.callV hx.1 ⟨⟨by simp, by rw [hg _ (by decide), hg _ (by decide), h0, h2]; rfl, by
      rw [hg _ (by decide), h0]; exact hK.f_scr, by rw [hg _ (by decide)]; rw [h2]; exact hfo,
      by rw [hg _ (by decide), hg _ (by decide), h0, h2]; exact hdo, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, by rw [hg _ (by decide), h0]; exact henv⟩,
      by rw [hg _ (by decide)]; exact h1⟩ hcv hcw (fun s' hrd hwr hsp hfr hpres _ hv hpost => ?_) hxn
  dsimp only [xmssContract] at hpost
  simp only [hg _ (show Reg.x0 ∉ linkRegs by decide),
    hg _ (show Reg.x1 ∉ linkRegs by decide), hg _ (show Reg.x2 ∉ linkRegs by decide), h0, h2] at hpost
  obtain ⟨he, hroot, hsig, hF⟩ := hpost _ _ _ henv hc.skAt
  have hc' : Ctx p σ s' := hc.of_frame hz.n32 hK hrd hwr hsp (hpres _ (by decide) (by decide))
    (fun r hr => hpres r (by revert r; decide) (by revert r; decide)) hv hF fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact changes_free hz r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub_base _ hoff))
  exact k s' hc' hpres he hroot hsig hF

theorem forsCall_ok {p : Params} (hz : Sz p) (hsl : p.sigLen < 2 ^ 63) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true)
    {σ u : State} (hK : SG p σ) (hc : Ctx p σ u) (h0 : u.gpr .x0 = σ.gpr .x7) (h2 : (u.gpr .x2).toNat < 2 ^ 32)
    {off : Nat} (h1 : u.gpr .x1 = σ.gpr .x6 + BitVec.ofNat 64 off) (hoff : off + p.forsSigLen ≤ p.sigLen)
    (hfp : 0 < p.forsSigLen)
    {pkSeed a16 : List Byte} (henv : Env p u.mem (σ.gpr .x7) pkSeed a16) {Q : State → Prop}
    (k : ∀ s', Ctx p σ s' → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u.gpr r) →
      Env p s'.mem (σ.gpr .x7) pkSeed a16 →
      bytesAt s'.mem (σ.gpr .x6 + BitVec.ofNat 64 off) p.forsSigLen =
        forsSign p (mdAt p u.mem (σ.gpr .x7)) (bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * 0)) p.n) pkSeed
          (forsAdrs a16 (u.gpr .x2).toNat) →
      bytesAt s'.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
        forsPkFromSig p (forsSign p (mdAt p u.mem (σ.gpr .x7)) (bytesAt σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (p.n * 0)) p.n)
          pkSeed (forsAdrs a16 (u.gpr .x2).toNat)) (mdAt p u.mem (σ.gpr .x7)) pkSeed (forsAdrs a16 (u.gpr .x2).toNat) →
      Frame (changes p (σ.gpr .x7) ++ [⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩]) u.mem s'.mem → Q s') :
    WP isa (.call f.forsName (Impl.SlhDsa.AArch64.Shake.forsCode p f)) u Q := by
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain ⟨hcv, hcw⟩ := call_covers (l := p.forsSigLen) hK hc hoff
  obtain ⟨hfo, hdo⟩ := part_regions hsl hK hoff hfp
  refine WP.callV hx.1 ⟨⟨by simp, by rw [hg _ (by decide), hg _ (by decide), h0, h1]; rfl, by
      rw [hg _ (by decide), h0]; exact hK.f_scr, by rw [hg _ (by decide)]; rw [h1]; exact hfo,
      by rw [hg _ (by decide), hg _ (by decide), h0, h1]; exact hdo, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, by rw [hg _ (by decide), h0]; exact henv⟩,
      by rw [hg _ (by decide)]; exact h2⟩ hcv hcw (fun s' hrd hwr hsp hfr hpres _ hv hpost => ?_) hxn
  dsimp only [forsContract] at hpost
  simp only [hg _ (show Reg.x0 ∉ linkRegs by decide),
    hg _ (show Reg.x1 ∉ linkRegs by decide), hg _ (show Reg.x2 ∉ linkRegs by decide), h0, h1] at hpost
  obtain ⟨he, hsig, hpk, hF⟩ := hpost _ _ _ henv hc.skAt
  have hc' : Ctx p σ s' := hc.of_frame hz.n32 hK hrd hwr hsp (hpres _ (by decide) (by decide))
    (fun r hr => hpres r (by revert r; decide) (by revert r; decide)) hv hF fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact changes_free hz r hr
      · simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl (Offset.sub_base _ hoff))
  exact k s' hc' hpres he hsig hpk hF

theorem xmss_pre {p : Params} (hsl : p.sigLen < 2 ^ 63)
    {σ u : State} (hK : SG p σ) (hc : Ctx p σ u) (h0 : u.gpr .x0 = σ.gpr .x7) (h1 : (u.gpr .x1).toNat < 2 ^ 32)
    {off : Nat} (h2 : u.gpr .x2 = σ.gpr .x6 + BitVec.ofNat 64 off) (hoff : off + p.xmssSigLen ≤ p.sigLen)
    (hxp : 0 < p.xmssSigLen) {pkSeed a16 : List Byte} (henv : Env p u.mem (σ.gpr .x7) pkSeed a16) :
    (xmssContract p).pre (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩]) ∧
    Covers ([] ++ [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩] u.wr := by
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.xmssSigLen⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain ⟨hcv, hcw⟩ := call_covers (l := p.xmssSigLen) hK hc hoff
  obtain ⟨hfo, hdo⟩ := part_regions hsl hK hoff hxp
  exact ⟨⟨⟨by simp, by rw [hg _ (by decide), hg _ (by decide), h0, h2]; rfl, by
      rw [hg _ (by decide), h0]; exact hK.f_scr, by rw [hg _ (by decide)]; rw [h2]; exact hfo,
      by rw [hg _ (by decide), hg _ (by decide), h0, h2]; exact hdo, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, by rw [hg _ (by decide), h0]; exact henv⟩,
      by rw [hg _ (by decide)]; exact h1⟩, hcv, hcw⟩

theorem fors_pre {p : Params} (hsl : p.sigLen < 2 ^ 63)
    {σ u : State} (hK : SG p σ) (hc : Ctx p σ u) (h0 : u.gpr .x0 = σ.gpr .x7) (h2 : (u.gpr .x2).toNat < 2 ^ 32)
    {off : Nat} (h1 : u.gpr .x1 = σ.gpr .x6 + BitVec.ofNat 64 off) (hoff : off + p.forsSigLen ≤ p.sigLen)
    (hfp : 0 < p.forsSigLen) {pkSeed a16 : List Byte} (henv : Env p u.mem (σ.gpr .x7) pkSeed a16) :
    (forsContract p).pre (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩]) ∧
    Covers ([] ++ [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩] u.wr := by
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [] [⟨σ.gpr .x7, scratchLen⟩,
      ⟨σ.gpr .x6 + BitVec.ofNat 64 off, p.forsSigLen⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain ⟨hcv, hcw⟩ := call_covers (l := p.forsSigLen) hK hc hoff
  obtain ⟨hfo, hdo⟩ := part_regions hsl hK hoff hfp
  exact ⟨⟨⟨by simp, by rw [hg _ (by decide), hg _ (by decide), h0, h1]; rfl, by
      rw [hg _ (by decide), h0]; exact hK.f_scr, by rw [hg _ (by decide)]; rw [h1]; exact hfo,
      by rw [hg _ (by decide), hg _ (by decide), h0, h1]; exact hdo, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, by rw [hg _ (by decide), h0]; exact henv⟩,
      by rw [hg _ (by decide)]; exact h2⟩, hcv, hcw⟩

end VG.Proof.SlhDsa.AArch64.Sign
