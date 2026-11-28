module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignLoop
public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignHash
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopIdx
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `sign`: the body

The block after the hashes: `PK.seed` to the lanes, the digest's indices
and layer 0's tree address in the lanes, and FORS's arguments (`fblock_ok`);
then the body as a whole (`body_ok`): `slh_sign_internal` of the formatted
message to `sig` (`SignTopSpec.signInternal_eq`), and 1.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Sign

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa (layerTree treeAdrs forsAdrs)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_movz)

/-- The digest's indices. -/
abbrev Tv (p : Params) (σ : State) : Nat := (splitDigest p (Dv p σ)).2.1
abbrev Iv (p : Params) (σ : State) : Nat := (splitDigest p (Dv p σ)).2.2

/-- The block after the hashes. -/
abbrev fblock (p : Params) : List Instr :=
  Impl.SlhDsa.AArch64.Shake.seedLanes p ++ Impl.SlhDsa.AArch64.Shake.parseIdx p ++
    ([.movz .x .x10 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.Shake.treeLanes p .x10 .x22 ++
    ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, .addImm .x .x1 .x25 p.n, Impl.SlhDsa.AArch64.Thash4.mov .x2 .x23] :
      List Instr)

/-- What holds at FORS's call. -/
structure FPre (p : Params) (σ u : State) : Prop where
  ctx : Ctx p σ u
  env : Env p u.mem (σ.gpr .x7) (chunk (skB p σ) p.n 2) (layerTree 0 (Tv p σ))
  x0 : u.gpr .x0 = σ.gpr .x7
  x1 : u.gpr .x1 = σ.gpr .x6 + BitVec.ofNat 64 p.n
  x2 : u.gpr .x2 = BitVec.ofNat 64 (Iv p σ)
  x22 : u.gpr .x22 = BitVec.ofNat 64 (Tv p σ)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (Iv p σ)
  x25 : u.gpr .x25 = σ.gpr .x6
  r : bytesAt u.mem (σ.gpr .x6) p.n = Rv p σ
  dig : bytesAt u.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ

theorem seed_free {p : Params} (hn : p.n ≤ 32) (σ : State) : ∀ r ∈ seedRegions p.n (σ.gpr .x7), Free p σ r := by
  intro r hr
  simp only [seedRegions, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨k, hk, rfl | rfl⟩ := hr
  · exact .inl ⟨Offset.sub_base _ (by rw [laneA_eq]; simp only [scratchLen]; omega),
      Offset.disjoint _ (by rw [laneA_eq]; simp only [Layout.oTop]; omega) (by rw [laneA_eq]; omega)
        (by simp only [Layout.oTop]; omega)⟩
  · exact .inl ⟨Offset.sub_base _ (by rw [laneB_eq]; simp only [scratchLen]; omega),
      Offset.disjoint _ (by rw [laneB_eq]; simp only [Layout.oTop]; omega) (by rw [laneB_eq]; omega)
        (by simp only [Layout.oTop]; omega)⟩

/-- The lanes' regions lie between `oA` and `oN`. -/
theorem lane_regions {n : Nat} (hn : n ≤ 32) {S : Addr} {r : Region} (h : r ∈ seedRegions n S ∨ r ∈ adrsRegions n S) :
    ∃ e k, r = ⟨at' S e, k⟩ ∧ Layout.oA ≤ e ∧ e + k ≤ Layout.oN := by
  rcases h with h | h
  · simp only [seedRegions, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨k, hk, rfl | rfl⟩ := h
    · exact ⟨_, _, rfl, by rw [laneA_eq]; simp only [Layout.oA]; omega, by rw [laneA_eq]; simp only [Layout.oN]; omega⟩
    · exact ⟨_, _, rfl, by rw [laneB_eq]; simp only [Layout.oA]; omega, by rw [laneB_eq]; simp only [Layout.oN]; omega⟩
  · simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨k, hk, b, hb, rfl⟩ := h
    have := laneAdrs_lt (n := n) hn hk hb
    exact ⟨_, _, rfl, by simp only [Layout.oA]; omega, by simp only [Layout.oN]; omega⟩

/-- What lies below `oA` in `scratch`, or in `sig`, is apart from the lanes. -/
theorem lane_disj {p : Params} {σ : State} (hK : SG p σ) {r : Region}
    (h : r ∈ seedRegions p.n (σ.gpr .x7) ∨ r ∈ adrsRegions p.n (σ.gpr .x7)) (hn : p.n ≤ 32) :
    (∀ {o l : Nat}, o + l ≤ Layout.oA → Region.Disjoint ⟨at' (σ.gpr .x7) o, l⟩ r) ∧
      ∀ {off l : Nat}, off + l ≤ p.sigLen → Region.Disjoint ⟨σ.gpr .x6 + BitVec.ofNat 64 off, l⟩ r := by
  obtain ⟨e, k, rfl, h1, h2⟩ := lane_regions hn h
  refine ⟨fun {o l} hl => Offset.disjoint _ (by omega) (by simp only [Layout.oA] at hl; omega)
    (by simp only [Layout.oN] at h2; omega), fun {off l} hl => ?_⟩
  exact (hK.sig_scr.sub_left (Offset.sub_base _ hl)).sub_right
    (Offset.sub_base _ (by simp only [Layout.oN, scratchLen] at h2 ⊢; omega))

theorem fblock_ok {p : Params} (hp : VPar p) {σ t : State} (hK : SG p σ) (hc : Ctx p σ t) (hr : HRegs σ t)
    (hR : bytesAt t.mem (σ.gpr .x6) p.n = Rv p σ)
    (hD : bytesAt t.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ) :
    WP isa (.block (fblock p)) t (FPre p σ) := by
  have hz : Sz p := ⟨hp.n, hp.len, hp.w4, hp.fam⟩
  have hn := hz.n32
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.wr := by rw [hc.wr, hK.wr]; simp
  have hsig : p.n ≤ p.sigLen := by simp only [Params.sigLen]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hsc : scratchLen = 65536 := rfl
  have hm := hp.m64
  have sD : ∀ r, (r ∈ seedRegions p.n (σ.gpr .x7) ∨ r ∈ adrsRegions p.n (σ.gpr .x7)) →
      Region.Disjoint ⟨at' (σ.gpr .x7) Layout.oDigest, p.m⟩ r := fun r h =>
    (lane_disj hK h hn).1 (by simp only [Layout.oDigest, Layout.oA]; omega)
  have sR : ∀ r, (r ∈ seedRegions p.n (σ.gpr .x7) ∨ r ∈ adrsRegions p.n (σ.gpr .x7)) →
      Region.Disjoint ⟨σ.gpr .x6, p.n⟩ r := fun r h => by
    have := (lane_disj hK h hn).2 (off := 0) (l := p.n) (by omega); simpa using this
  simp only [fblock, List.append_assoc]
  refine seedLanes_ok (p := p) hz.nv hc.x19 hw fun s₁ i₁ => ?_
  have c₁ : Ctx p σ s₁ := hc.of_frame hn hK i₁.keep.rd i₁.keep.wr i₁.keep.sp (i₁.keep.get .x19)
    (fun r hr => i₁.keep.get r (by revert r; decide)) i₁.keep.vcs i₁.frame (seed_free hn σ)
  refine parseIdx_ok hp c₁.x19 (by rw [c₁.wr, hK.wr]; simp) fun s₂ o₂ e22 e23 => ?_
  rw [bytesAt_frame i₁.frame (fun r hr => sD r (.inl hr)) (by omega), hD] at e22 e23
  refine wp_movz fun s₃ o₃ e₃ => ?_
  have hT : Tv p σ < 2 ^ 64 := by
    have := hp.tb; have := hp.tb'; simp only [Tv, splitDigest]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  have hI : Iv p σ < 2 ^ p.hp := by simp only [Iv, splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine treeLanes_ok (p := p) hz.nv (by decide) (by rw [o₃.get .x19, o₂.get .x19, c₁.x19])
    (by rw [o₃.wr, o₂.wr, c₁.wr, hK.wr]; simp) (by rw [e₃]; decide) fun s₄ k₄ f₄ a₄ => ?_
  rw [e₃, o₃.get .x22, e22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at a₄
  refine wp_addImm (by decide) fun s₅ o₅ e₅ => wp_addImm (by omega) fun s₆ o₆ e₆ =>
    wp_addImm (by decide) fun s₇ o₇ e₇ => wp_nil ?_
  have k₇ : Keep [.x9, .x10, .x22, .x11, .x23, .x10, .x12, .x13, .x14, .x0, .x1, .x2] s₁ s₇ :=
    ((o₂.trans o₃).keep.trans (k₄.trans (o₅.trans (o₆.trans o₇)).keep)).mono (by decide)
  have hm₇ : s₇.mem = s₄.mem := by rw [o₇.mem, o₆.mem, o₅.mem]
  have hm₃ : s₃.mem = s₁.mem := by rw [o₃.mem, o₂.mem]
  have g : ∀ r ∈ [Reg.x19, .x25], s₇.gpr r = t.gpr r := fun r hr => by
    rw [k₇.get r (by revert r; decide), i₁.keep.get r (by revert r; decide)]
  have hlow : ∀ {a : Addr} {l : Nat}, l ≤ 2 ^ 64 →
      (∀ r, (r ∈ seedRegions p.n (σ.gpr .x7) ∨ r ∈ adrsRegions p.n (σ.gpr .x7)) → Region.Disjoint ⟨a, l⟩ r) →
      bytesAt s₇.mem a l = bytesAt t.mem a l := fun hl h => by
    rw [hm₇, bytesAt_frame f₄ (fun r hr => h r (.inr hr)) hl, hm₃, bytesAt_frame i₁.frame (fun r hr => h r (.inl hr)) hl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine c₁.of_frame hn hK k₇.rd k₇.wr k₇.sp (k₇.get .x19) (fun r hr => k₇.get r (by revert r; decide)) k₇.vcs
      (by rw [hm₇, ← hm₃]; exact f₄) (adrs_free hn σ)
  · rw [hm₇]
    refine env_adrs hn (fun k hk => ?_) (fun k hk => ?_) f₄ a₄
    · rw [hm₃, (i₁.lanes k hk).1, show Layout.oPkSeed = Layout.oKeys + 32 * 2 from rfl, hc.keys 2 (by decide),
        key_chunk p σ (by decide)]
    · rw [hm₃, (i₁.lanes k hk).2, show Layout.oPkSeed = Layout.oKeys + 32 * 2 from rfl, hc.keys 2 (by decide),
        key_chunk p σ (by decide)]
  · rw [o₇.get .x0, o₆.get .x0, e₅, BitVec.add_zero, k₄.get .x19, o₃.get .x19, o₂.get .x19, c₁.x19]
  · rw [o₇.get .x1, e₆, o₅.get .x25, k₄.get .x25, o₃.get .x25, o₂.get .x25, i₁.keep.get .x25, hr.x25]
  · rw [e₇, BitVec.add_zero, o₆.get .x23, o₅.get .x23, k₄.get .x23, o₃.get .x23, e23]
  · rw [o₇.get .x22, o₆.get .x22, o₅.get .x22, k₄.get .x22, o₃.get .x22, e22]
  · rw [o₇.get .x23, o₆.get .x23, o₅.get .x23, k₄.get .x23, o₃.get .x23, e23]
  · rw [g .x25 (by decide), hr.x25]
  · rw [hlow (by omega) fun r h => sR r h, hR]
  · rw [hlow (by omega) fun r h => sD r h, hD]

theorem bytesAt_take (m : Mem) (a : Addr) {k L : Nat} (h : k ≤ L) : (bytesAt m a L).take k = bytesAt m a k := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h₁ h₂
  simp [bytesAt]

theorem signBody_eq (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    Impl.SlhDsa.AArch64.Shake.signBody p f =
      .seq (.block (proCode p)) (.seq (Impl.SlhDsa.AArch64.Shake.hashM' p f [.scr Layout.oSkPrf, .reg .x24] (.reg .x25) p.n)
        (.seq (Impl.SlhDsa.AArch64.Shake.hashM' p f [.reg .x25, .scr Layout.oPkSeed, .scr Layout.oPkRoot]
          (.scr Layout.oDigest) p.m)
          (.seq (.block (fblock p))
            (.seq (.call f.forsName (Impl.SlhDsa.AArch64.Shake.forsCode p f))
              (.seq (.block (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x25 (p.n + p.forsSigLen)))
                (.seq (.loop (Impl.SlhDsa.AArch64.Shake.layerBody p f) (.nonzero .x .x9))
                  (.block (Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
                    ([.movz .x .x0 1 0] : List Instr))))))))) := by
  simp only [Impl.SlhDsa.AArch64.Shake.signBody, fblock, List.append_assoc]

/-- FORS's signature and public key, of the entry state `σ`. -/
abbrev sigFv (p : Params) (σ : State) : List Byte :=
  forsSign p (splitDigest p (Dv p σ)).1 (chunk (skB p σ) p.n 0) (chunk (skB p σ) p.n 2)
    (forsAdrs (layerTree 0 (Tv p σ)) (Iv p σ))
abbrev pkFv (p : Params) (σ : State) : List Byte :=
  forsPkFromSig p (sigFv p σ) (splitDigest p (Dv p σ)).1 (chunk (skB p σ) p.n 2) (forsAdrs (layerTree 0 (Tv p σ)) (Iv p σ))

/-- After FORS. -/
structure FP (p : Params) (σ s' : State) : Prop where
  ctx : Ctx p σ s'
  x22 : s'.gpr .x22 = BitVec.ofNat 64 (Tv p σ)
  x23 : s'.gpr .x23 = BitVec.ofNat 64 (Iv p σ)
  x25 : s'.gpr .x25 = σ.gpr .x6
  msg : bytesAt s'.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = pkFv p σ
  sig : bytesAt s'.mem (σ.gpr .x6) (p.n + p.forsSigLen) = Rv p σ ++ sigFv p σ
  env : ∃ a16, Env p s'.mem (σ.gpr .x7) (chunk (skB p σ) p.n 2) a16

theorem Tv_lt {p : Params} (hp : VPar p) (σ : State) : Tv p σ < 2 ^ 64 := by
  have := hp.tb; have := hp.tb'; simp only [Tv, splitDigest]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))

theorem Iv_lt {p : Params} (hp : VPar p) (σ : State) : Iv p σ < 2 ^ p.hp := by
  simp only [Iv, splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The call of FORS. -/
theorem fors_ok {p : Params} (hp : VPar p) (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hfn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true)
    {σ u : State} (hK : SG p σ) (hu : FPre p σ u) :
    WP isa (.call f.forsName (Impl.SlhDsa.AArch64.Shake.forsCode p f)) u (FP p σ) := by
  have hz := hP.sz
  have hn := hz.n32
  have hsl := hP.sigLt
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hP.sigLen]; omega
  have hI := Iv_lt hp σ
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hP.hp9
  refine forsCall_ok hz hsl hf hfn hK hu.ctx hu.x0 (by rw [hu.x2, BitVec.toNat_ofNat]; omega) hu.x1
    (by omega) hp.fpos hu.env fun s' hcs hpres he hsig hpk hF => ?_
  have g : ∀ r ∈ [Reg.x19, .x22, .x23, .x25], s'.gpr r = u.gpr r := fun r hr =>
    hpres r (by revert r; decide) (by revert r; decide)
  have hmd : mdAt p u.mem (σ.gpr .x7) = (splitDigest p (Dv p σ)).1 := by
    simp only [mdAt, splitDigest]
    rw [← hu.dig, bytesAt_take _ _ (by rw [hp.m]; omega)]
  rw [hmd, hu.x2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), key_chunk p σ (by decide)] at hsig hpk
  have hR' : bytesAt s'.mem (σ.gpr .x6) p.n = Rv p σ := by
    rw [bytesAt_frame hF (fun r hr => ?_) (by omega), hu.r]
    rcases List.mem_append.mp hr with hr | hr
    · exact (hK.sig_scr.sub_left (Region.sub_prefix (base := σ.gpr .x6) (len := p.n) (len' := p.sigLen) (by omega))).sub_right
        (changes_in hz r hr).1
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
  exact ⟨hcs, by rw [g .x22 (by decide), hu.x22], by rw [g .x23 (by decide), hu.x23], by rw [g .x25 (by decide), hu.x25],
    hpk, by rw [KeyGen.bytesAt_add', hR', hsig], ⟨_, he⟩⟩

/-- The block after FORS. -/
theorem init_wp {p : Params} (hP : LP p) {σ t : State} (hK : SG p σ) (ht : FP p σ t) :
    WP isa (.block (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x25 (p.n + p.forsSigLen))) t
      (LI p σ (Rv p σ ++ sigFv p σ) (pkFv p σ) (Tv p σ) (Iv p σ) 0) := by
  have hsl := hP.sigLt
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hP.sigLen]; omega
  rw [← List.append_nil (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x25 (p.n + p.forsSigLen))]
  refine init_ok (p := p) (is := []) (by omega) fun w o e21 e20 => wp_nil ?_
  exact ⟨ht.ctx.of_frame hP.sz.n32 hK o.rd o.wr o.sp (o.get .x19) (fun r hr => o.get r (by revert r; decide)) o.vcs
      (rs := []) (fun x _ => by rw [o.mem]) (fun _ h => absurd h List.not_mem_nil),
    by rw [e20, ht.x25, Nat.zero_mul, Nat.add_zero], by rw [e21]; rfl,
    by rw [o.get .x22, ht.x22]; rfl, by rw [o.get .x23, ht.x23]; rfl,
    by rw [o.mem, ht.msg]; rfl,
    by rw [o.mem, Nat.zero_mul, Nat.add_zero, ht.sig]; simp,
    by obtain ⟨a, he⟩ := ht.env; exact ⟨a, by rw [o.mem]; exact he⟩⟩

/-- The body of `sign`, for any `forsSign` and `xmssTree` verified against their contracts. -/
theorem body_ok {p : Params} (hp : VPar p) (hP : LP p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (hx : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.xmssCode p f) (xmssContract p))
    (hxn : (Impl.SlhDsa.AArch64.Shake.xmssCode p f).noFrames = true)
    (hf : Verified AArch64.target (Impl.SlhDsa.AArch64.Shake.forsCode p f) (forsContract p))
    (hfn : (Impl.SlhDsa.AArch64.Shake.forsCode p f).noFrames = true)
    {σ s : State} (hK : SG p σ) (h4 : (σ.gpr .x4).toNat < 256) (hs : Only [.x9] σ s) :
    WP isa (Impl.SlhDsa.AArch64.Shake.signBody p f) s (BodyPost p σ) := by
  have hz := hP.sz
  rw [signBody_eq]
  refine WP.seq (WP.mono (pro_ok hz hK h4 hs) fun t₁ ⟨c₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (hashR_ok hz v hv hK c₁ r₁) fun t₂ ⟨c₂, r₂, R₂⟩ => ?_)
  refine WP.seq (WP.mono (hashD_ok hz hp.m64 v hv hK c₂ r₂ R₂) fun t₃ ⟨c₃, r₃, R₃, D₃⟩ => ?_)
  refine WP.seq (WP.mono (fblock_ok hp hK c₃ r₃ R₃ D₃) fun u hu => ?_)
  refine WP.seq (WP.mono (fors_ok hp hP hf hfn hK hu) fun s' hs' => ?_)
  refine WP.seq (WP.mono (init_wp hP hK hs') fun w hw => ?_)
  refine WP.seq (WP.mono (loop_ok hP hx hxn hp.d1 hK (Tv_lt hp σ) (Iv_lt hp σ) hw) fun t₄ h₄ => ?_)
  refine WP.mono (epi_ok hK h₄.ctx) fun w ⟨habi, hret, hm⟩ => ⟨habi, hret, ?_⟩
  rw [hm, hP.sigLen, h₄.sig, X86_64.SignTop.signInternal_eq hp]

end VG.Proof.SlhDsa.AArch64.Sign
