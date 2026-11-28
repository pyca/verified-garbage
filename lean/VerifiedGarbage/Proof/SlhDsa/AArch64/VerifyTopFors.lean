module

-- separate module: FORS's block and call, rebuilt only when forsPk's contract or the lanes' blocks change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopHash
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsV
public import VerifiedGarbage.Proof.SlhDsa.AArch64.SignBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: FORS

The block after the digest: `PK.seed` to the lanes, the digest's indices
and layer 0's tree address in the lanes, and `forsPk`'s arguments
(`fblock_ok`, to `FPre`); the call of `forsPk` (`fors_ok`), which leaves
FORS's public key `pkF` at `oMsg` (`FP`); and the free regions the callees
write (`changes_free`, `adrs_free`, `seed_free`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa (layerTree treeAdrs forsAdrs)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)
open VG.Proof.SlhDsa.AArch64.Sign (SCR PROT lane_regions env_adrs)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_movz)

theorem Sz.of_vpar {p : Params} (hp : VPar p) : Sz p := ⟨hp.n, hp.len, hp.w4, hp.fam⟩

/-! ## Free regions -/

theorem changes_free {p : Params} (hz : Sz p) {σ : State} : ∀ r ∈ changes p (σ.gpr .x7), Free σ r :=
  fun r hr => .inl (Sign.changes_in hz r hr)

theorem seed_free {n : Nat} (hn : n ≤ 32) (σ : State) : ∀ r ∈ seedRegions n (σ.gpr .x7), Free σ r := by
  intro r hr
  obtain ⟨e, k, rfl, h1, h2⟩ := lane_regions hn (.inl hr)
  exact .inl ⟨Offset.sub_base _ (by simp only [Layout.oN, scratchLen] at h2 ⊢; omega),
    Offset.disjoint _ (by simp only [Layout.oA, Layout.oTop] at h1 ⊢; omega) (by simp only [Layout.oN] at h2 ⊢; omega)
      (by simp only [Layout.oTop]; omega)⟩

theorem adrs_free {n : Nat} (hn : n ≤ 32) (σ : State) : ∀ r ∈ adrsRegions n (σ.gpr .x7), Free σ r := by
  intro r hr
  obtain ⟨e, k, rfl, h1, h2⟩ := lane_regions hn (.inr hr)
  exact .inl ⟨Offset.sub_base _ (by simp only [Layout.oN, scratchLen] at h2 ⊢; omega),
    Offset.disjoint _ (by simp only [Layout.oA, Layout.oTop] at h1 ⊢; omega) (by simp only [Layout.oN] at h2 ⊢; omega)
      (by simp only [Layout.oTop]; omega)⟩

/-- What lies below `oA` in `scratch` is apart from the lanes. -/
theorem lane_disj {n : Nat} (hn : n ≤ 32) {S : Addr} {r : Region} (h : r ∈ seedRegions n S ∨ r ∈ adrsRegions n S)
    {o l : Nat} (hl : o + l ≤ Layout.oA) : Region.Disjoint ⟨at' S o, l⟩ r := by
  obtain ⟨e, k, rfl, h1, h2⟩ := lane_regions hn h
  exact Offset.disjoint _ (by omega) (by simp only [Layout.oA] at hl; omega) (by simp only [Layout.oN] at h2; omega)

/-! ## The block after the digest -/

/-- The block after the digest. -/
abbrev fblock (p : Params) : List Instr :=
  Impl.SlhDsa.AArch64.Shake.seedLanes p ++ Impl.SlhDsa.AArch64.Shake.parseIdx p ++
    ([.movz .x .x10 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.Shake.treeLanes p .x10 .x22 ++
    ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, .addImm .x .x1 .x24 p.n, Impl.SlhDsa.AArch64.Thash4.mov .x2 .x23] :
      List Instr)

/-- What holds at `forsPk`'s call. -/
structure FPre (p : Params) (σ u : State) : Prop where
  ctx : Ctx p σ u
  env : Env p u.mem (σ.gpr .x7) (PKs p σ) (layerTree 0 (Tv p σ))
  x0 : u.gpr .x0 = σ.gpr .x7
  x1 : u.gpr .x1 = σ.gpr .x5 + BitVec.ofNat 64 p.n
  x2 : u.gpr .x2 = BitVec.ofNat 64 (Iv p σ)
  x22 : u.gpr .x22 = BitVec.ofNat 64 (Tv p σ)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (Iv p σ)
  dig : bytesAt u.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ

theorem Tv_lt {p : Params} (hp : VPar p) (σ : State) : Tv p σ < 2 ^ 64 := by
  have := hp.tb; have := hp.tb'; simp only [Tv, splitDigest]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))

theorem Iv_lt {p : Params} (hp : VPar p) (σ : State) : Iv p σ < 2 ^ p.hp := by
  simp only [Iv, splitDigest, hp.hd]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fblock_ok {p : Params} (hp : VPar p) {σ t : State} (hK : VG p σ) (hc : Ctx p σ t)
    (hD : bytesAt t.mem (at' (σ.gpr .x7) Layout.oDigest) p.m = Dv p σ) :
    WP isa (.block (fblock p)) t (FPre p σ) := by
  have hz := Sz.of_vpar hp
  have hn := hz.n32
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.wr := by rw [hc.wr, hK.wr]; simp
  have hm := hp.m64
  have sD : ∀ r, (r ∈ seedRegions p.n (σ.gpr .x7) ∨ r ∈ adrsRegions p.n (σ.gpr .x7)) →
      Region.Disjoint ⟨at' (σ.gpr .x7) Layout.oDigest, p.m⟩ r := fun r h =>
    lane_disj hn h (by simp only [Layout.oDigest, Layout.oA]; omega)
  simp only [fblock, List.append_assoc]
  refine seedLanes_ok (p := p) hz.nv hc.x19 hw fun s₁ i₁ => ?_
  have c₁ : Ctx p σ s₁ := hc.of_frame hn hK i₁.keep.rd i₁.keep.wr i₁.keep.sp (i₁.keep.get .x19) (i₁.keep.get .x24)
    (fun r hr => i₁.keep.get r (by revert r; decide)) i₁.keep.vcs i₁.frame (seed_free hn σ)
  refine parseIdx_ok hp c₁.x19 (by rw [c₁.wr, hK.wr]; simp) fun s₂ o₂ e22 e23 => ?_
  rw [bytesAt_frame i₁.frame (fun r hr => sD r (.inl hr)) (by omega), hD] at e22 e23
  refine wp_movz fun s₃ o₃ e₃ => ?_
  have hT := Tv_lt hp σ
  refine treeLanes_ok (p := p) hz.nv (by decide) (by rw [o₃.get .x19, o₂.get .x19, c₁.x19])
    (by rw [o₃.wr, o₂.wr, c₁.wr, hK.wr]; simp) (by rw [e₃]; decide) fun s₄ k₄ f₄ a₄ => ?_
  rw [e₃, o₃.get .x22, e22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at a₄
  refine wp_addImm (by decide) fun s₅ o₅ e₅ => wp_addImm (by omega) fun s₆ o₆ e₆ =>
    wp_addImm (by decide) fun s₇ o₇ e₇ => wp_nil ?_
  have k₇ : Keep [.x9, .x10, .x22, .x11, .x23, .x10, .x12, .x13, .x14, .x0, .x1, .x2] s₁ s₇ :=
    ((o₂.trans o₃).keep.trans (k₄.trans (o₅.trans (o₆.trans o₇)).keep)).mono (by decide)
  have hm₇ : s₇.mem = s₄.mem := by rw [o₇.mem, o₆.mem, o₅.mem]
  have hm₃ : s₃.mem = s₁.mem := by rw [o₃.mem, o₂.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine c₁.of_frame hn hK k₇.rd k₇.wr k₇.sp (k₇.get .x19) (k₇.get .x24)
      (fun r hr => k₇.get r (by revert r; decide)) k₇.vcs (by rw [hm₇, ← hm₃]; exact f₄) (adrs_free hn σ)
  · rw [hm₇]
    have hk0 := hc.keys 0 (by decide)
    rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero, BitVec.add_zero] at hk0
    refine env_adrs hn (fun k hk => ?_) (fun k hk => ?_) f₄ a₄
    · rw [hm₃, (i₁.lanes k hk).1, hk0]
    · rw [hm₃, (i₁.lanes k hk).2, hk0]
  · rw [o₇.get .x0, o₆.get .x0, e₅, BitVec.add_zero, k₄.get .x19, o₃.get .x19, o₂.get .x19, c₁.x19]
  · rw [o₇.get .x1, e₆, o₅.get .x24, k₄.get .x24, o₃.get .x24, o₂.get .x24, c₁.x24]
  · rw [e₇, BitVec.add_zero, o₆.get .x23, o₅.get .x23, k₄.get .x23, o₃.get .x23, e23]
  · rw [o₇.get .x22, o₆.get .x22, o₅.get .x22, k₄.get .x22, o₃.get .x22, e22]
  · rw [o₇.get .x23, o₆.get .x23, o₅.get .x23, k₄.get .x23, o₃.get .x23, e23]
  · rw [hm₇, bytesAt_frame f₄ (fun r hr => sD r (.inr hr)) (by omega), hm₃,
      bytesAt_frame i₁.frame (fun r hr => sD r (.inl hr)) (by omega), hD]

/-! ## The call of `forsPk` -/

theorem empty_disj (S : Addr) (r : Region) : Region.Disjoint ⟨S, 0⟩ r := fun _ h _ => by
  simp [Region.Contains] at h

/-- A part of the signature, as a read-only region of a callee with `scratch`. -/
theorem part_ok {p : Params} {σ u : State} (hK : VG p σ) (hc : Ctx p σ u) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    {off l : Nat} (hl : off + l ≤ p.sigLen) (hl0 : 0 < l) :
    Covers ([⟨σ.gpr .x5 + BitVec.ofNat 64 off, l⟩] ++ [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩] u.wr ∧
      (σ.gpr .x5 + BitVec.ofNat 64 off).toNat + l ≤ 2 ^ 64 ∧
      Region.Disjoint ⟨σ.gpr .x5 + BitVec.ofNat 64 off, l⟩ ⟨σ.gpr .x7, scratchLen⟩ := by
  have hf := hK.f_sig
  rw [hsl] at hf
  have hw : Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩] u.wr := by
    rw [hc.wr, hK.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_self .., 0, by simp, by simp only [scratchLen]; omega⟩
  refine ⟨?_, hw, ?_, hK.sig_scr.sub_left (Offset.sub_base _ (by rw [hsl]; omega))⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [hc.rd, hc.wr, hK.rd, hK.wr]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨σ.gpr .x5, (σ.gpr .x6).toNat⟩, by simp, off, rfl, by simp only; omega⟩
    · exact ⟨⟨σ.gpr .x7, scratchLen⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨σ.gpr .x7, scratchLen⟩, by simp, 0, by simp, by simp only [scratchLen]; omega⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- After `forsPk`. -/
structure FP (p : Params) (σ s' : State) : Prop where
  ctx : Ctx p σ s'
  x22 : s'.gpr .x22 = BitVec.ofNat 64 (Tv p σ)
  x23 : s'.gpr .x23 = BitVec.ofNat 64 (Iv p σ)
  msg : bytesAt s'.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = pkF p σ
  env : ∃ a16, Env p s'.mem (σ.gpr .x7) (PKs p σ) a16

/-- The call of `forsPk`. -/
theorem fors_ok {p : Params} (hp : VPar p) {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (fn : String) {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    (hu : FPre p σ u) :
    WP isa (.call fn (Impl.SlhDsa.AArch64.Verify.forsPk p f)) u (FP p σ) := by
  have hz := Sz.of_vpar hp
  have hn := hz.n32
  have hsl31 := hp.sigLt
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hp.sigLen]; omega
  have hI := Iv_lt hp σ
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hp.hp9
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [⟨σ.gpr .x5 + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]).gpr r = u.gpr r :=
    fun r h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  obtain ⟨hcv, hcw, hfo, hdo⟩ := part_ok hK hu.ctx hsl (off := p.n) (l := p.forsSigLen) hfsl hp.fpos
  refine ForsPk.forsPkcall_ok hz hp.p6 T ht fn ⟨⟨by rw [State.withRegions_rd, hg _ (by decide), hu.x1],
      by rw [State.withRegions_wr, hg _ (by decide), hu.x0], by rw [hg _ (by decide), hu.x0]; exact hK.f_scr,
      by rw [hg _ (by decide), hu.x0]; have := hK.f_scr; simp only [scratchLen] at this; simp; omega,
      by rw [hg _ (by decide), hu.x0]; exact empty_disj _ _,
      fun r hr => by
        rw [hg _ (by decide), hu.x1] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hfo,
      fun r hr => by
        rw [hg _ (by decide), hu.x1] at hr; simp only [List.mem_singleton] at hr; subst hr
        rw [hg _ (by decide), hu.x0]; exact hdo⟩,
    ⟨_, _, by rw [hg _ (by decide), hu.x0]; exact hu.env⟩,
    by rw [hg _ (by decide), hu.x2, BitVec.toNat_ofNat]; omega⟩ hcv hcw
    fun s' hrd hwr hsp hfr hpres hv hpost => ?_
  dsimp only [forsPkContract] at hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.x0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.x1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.x2 ∉ linkRegs by decide), hu.x0, hu.x1, hu.x2] at hpost
  obtain ⟨he, hpk, hF⟩ := hpost _ _ hu.env
  have g : ∀ r ∈ [Reg.x19, .x22, .x23, .x24], s'.gpr r = u.gpr r := fun r hr =>
    hpres r (by revert r; decide) (by revert r; decide)
  have hmd : mdAt p u.mem (σ.gpr .x7) = (splitDigest p (Dv p σ)).1 := by
    simp only [mdAt, splitDigest]
    rw [← hu.dig, bytesAt_take _ _ (by rw [hp.m]; omega)]
  have hsF : bytesAt u.mem (σ.gpr .x5 + BitVec.ofNat 64 p.n) p.forsSigLen = sigF p σ :=
    hu.ctx.bytes_out (by omega) hdo (hK.stk_sig.sub_right (Offset.sub_base _ (by rw [hsl]; exact hfsl))).symm
  rw [hmd, hsF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hpk
  refine ⟨hu.ctx.of_frame hn hK hrd hwr hsp (g .x19 (by decide)) (g .x24 (by decide))
      (fun r hr => hpres r (by revert r; decide) (by revert r; decide)) hv hF (changes_free hz),
    by rw [g .x22 (by decide), hu.x22], by rw [g .x23 (by decide), hu.x23], hpk, ⟨_, he⟩⟩

end VG.Proof.SlhDsa.AArch64.VerifyTop
