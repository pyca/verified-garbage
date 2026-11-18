module

public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt`

The table stored and the constants loaded (`pro_ok`); each of the first
seven layers is `layerF` on words (`lay_ok` with `bfly_core`, and `blkL_ok`
or `blkS_ok` for its blocks), which leaves words congruent to the
specification's (`layersF_rel`), and the last is `layerFC`, which leaves its
coefficients (`layerFC_val`, `ntt_split`), all in the frames that save
`r4`–`r10` (`wp_saving`). `LI`, `pro_ok`, `PreE` and `pre_entry` serve `NTT⁻¹`
too. All of it is for either product by a zeta (`u`: with `umaal` or
without); with `umaal` the code is constant time by `taintU`, for which what
a `umaal` writes is secret (`ct_of_savingU`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith.Ntt

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

/-- `ct_saving`, with `umaal`: `saving rs body` is constant time if `taintU`
proves `body` constant time from the registers `ps` public. -/
theorem ct_savingU (rs : List Reg) (body : Prog isa) (ps : List Reg) {hc : VG.Taint.Hint VG.Arm.taintU.T}
    (h : (VG.Arm.taintU.check (Taint.ofRegs ps) body hc).isSome = true) :
    ∀ P : State → State → Prop, (∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r) →
      RelCT isa P (saving rs body) fun _ _ => True := by
  induction rs with
  | nil =>
    intro P hP
    exact RelCT.taint (A := VG.Arm.taintU) (Taint.ofRegs ps)
      (fun s₁ s₂ hp => Taint.agree_ofRegs (hP s₁ s₂ hp).2) h
  | cons r rs ih =>
    intro P hP
    refine RelCT.frame (fun s₁ s₂ hp => (hP s₁ s₂ hp).1) (ih _ fun a b ⟨s₁, s₂, hp, h₁, h₂⟩ => ?_)
    obtain ⟨rfl, -⟩ := push_pushed' h₁
    obtain ⟨rfl, -⟩ := push_pushed' h₂
    obtain ⟨hsp, hg⟩ := hP s₁ s₂ hp
    exact ⟨by rw [pushed_sp, pushed_sp, hsp], fun r hr => by rw [pushed_gpr, pushed_gpr]; exact hg r hr⟩

/-- `ct_of_saving`, with `umaal`. -/
theorem ct_of_savingU {k : Contract isa} (rs : List Reg) (body : Prog isa) (ps : List Reg)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ ps, s₁.gpr r = s₂.gpr r)
    {hc : VG.Taint.Hint VG.Arm.taintU.T} (h : (VG.Arm.taintU.check (Taint.ofRegs ps) body hc).isSome = true) :
    ConstantTime isa k.pre k.pub (saving rs body) :=
  RelCT.constantTime (ct_savingU rs body ps h _ fun s₁ s₂ hp => hpub s₁ s₂ hp.2.2)

section
variable (s : State)

abbrev pf : BitVec 32 := s.gpr .r0
abbrev ps : BitVec 32 := s.gpr .r1
abbrev F : Addr := State.addr (pf s)
abbrev S : Addr := State.addr (ps s)

end

/-- The precondition of both transforms, on entry. -/
structure PreE (s : State) : Prop where
  sp : 28 ≤ s.sp.toNat
  rd : s.rd = []
  wr : s.wr = [polyRegion (F s), polyRegion (S s)]
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  sF : (belowA s.sp 28).Disjoint (polyRegion (F s))
  sS : (belowA s.sp 28).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

/-- What the transforms need of the state after the pushes. -/
structure PreB (s : State) : Prop where
  wF : polyRegion (F s) ∈ s.wr
  wS : polyRegion (S s) ∈ s.wr
  fs : (polyRegion (F s)).Disjoint (polyRegion (S s))
  fitF : (pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (F s)

theorem pre_entry {s s₁ : State} (hp : PreE s) (hE : Entry 28 s s₁) :
    PreB s₁ ∧ polyAt s₁.mem (F s₁) = polyAt s.mem (F s) ∧ F s₁ = F s ∧ S s₁ = S s := by
  have g := hE.gpr
  have eF : F s₁ = F s := by simp only [F, pf, g]
  have eS : S s₁ = S s := by simp only [S, ps, g]
  have dF : ∀ r ∈ [belowA s.sp 28], (polyRegion (F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame hE.frame dF, eF, eS⟩
  · rw [eF]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eS]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eF, eS]; exact hp.fs
  · simp only [pf, g]; exact hp.fitF
  · simp only [ps, g]; exact hp.fitS
  · rw [eF]; exact reduced_frame hE.frame dF hp.red

/-- Between layers: the words `G` at `f`, the table `tab` at `scratch`,
entry `k` of the table at `r1`, `-q` in `r4` and `q` in `r5`, from the state
`s₁` after the pushes. -/
structure LI (tab : Nat → Nat) (s₁ : State) (G : LPoly) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf s₁
  r1 : s.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k)
  r4 : s.gpr .r4 = Nw
  r5 : s.gpr .r5 = Qw
  poly : LP s.mem (F s₁) G
  tab : Tab tab s.mem (S s₁)
  frame : Frame [polyRegion (F s₁), polyRegion (S s₁)] s₁.mem s.mem
  keep : Keep [.r11, .lr] s₁ s

theorem LI.step {tab : Nat → Nat} {s₁ : State} {G G' : LPoly} {k k' : Nat} {s s' : State}
    (hI : LI tab s₁ G k s) (hP : LP s'.mem (F s₁) G') (hf : Frame [polyRegion (F s₁)] s.mem s'.mem)
    (h0 : s'.gpr .r0 = pf s₁) (h1 : s'.gpr .r1 = ps s₁ + BitVec.ofNat 32 (4 * k'))
    (hk : Keep [.r4, .r5, .r11, .lr] s s') (hd : (polyRegion (S s₁)).Disjoint (polyRegion (F s₁))) :
    LI tab s₁ G' k' s' :=
  ⟨h0, h1, (hk.gpr .r4 (by decide)).trans hI.r4, (hk.gpr .r5 (by decide)).trans hI.r5, hP,
    hI.tab.frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd),
    hI.frame.trans (hf.mono (by simp)), hI.keep.trans (hk.mono (by decide))⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ Chain (256 / len) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEnd : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEnd (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 128 / len + 128 / len = 256 / len ∧ 256 / len ≤ 256 := by decide

theorem zetaTab_of : TabOf zetaTab zetas := fun k _ => zetaNat_eq k

theorem zetaTab_lt : ∀ k < 256, zetaTab k < q := fun k _ => zetaNat_lt k

/-- A layer of `NTT` whose blocks are `blk`, with the butterfly `op`. -/
theorem layF_ok {u : Bool} {s₁ : State} (hp : PreB s₁) {blk : Prog isa} {op : Word → Word → Zq → Word × Word}
    {len : Nat} (hlen : len ∈ nttLens) (hblk : BlockOk blk op (tabOf u zetaTab) zetas .add len (pf s₁) (ps s₁))
    {G : LPoly} {s : State} (hI : LI (tabOf u zetaTab) s₁ G (128 / len) s) :
    WP isa (nttLay blk len) s fun s' =>
      LI (tabOf u zetaTab) s₁ (Lazy.layF (lblk op zetas) G len (fun c => 128 / len + c) (128 / len))
        (256 / len) s' := by
  obtain ⟨h1, h2⟩ := lens_fwd len hlen
  refine WP.mono (lay_ok hblk hlen (fun c => 128 / len + c) (fun c hc => by omega_using [h1, h2, hc])
    (fun c _ => by
      simp only [nextZ, ite_true, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
        ← BitVec.ofNat_add]
      congr 2)
    G s hI.r0 (by rw [hI.r1]; rfl) hI.r4 hI.r5 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
    (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
    fun s' ⟨hP, hf, h0, h1', hk'⟩ => hI.step hP hf h0 (by rw [h1', ← h1]) hk' hp.fs.symm

theorem lays_ok {u : Bool} {s₁ : State} (hp : PreB s₁) (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : LPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ nttLens ∧ BlockOk (blk len) (opF u) (tabOf u zetaTab) zetas .add len (pf s₁) (ps s₁)) →
      Chain k ls → LI (tabOf u zetaTab) s₁ G k s →
      WP isa (lays blk ls) s fun s' => LI (tabOf u zetaTab) s₁ (ls.foldl (layerF u) G) (chainEnd k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, hblk⟩ := hls len (List.mem_cons_self ..)
    exact WP.seq (WP.mono (layF_ok hp hlen hblk (hk ▸ hI)) fun s' hI' =>
      lays_ok hp blk ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc hI')

/-- The table `tab` to `scratch`, `-q` to `r4`, `q` to `r5`, and `r1` at
entry `k`. -/
theorem pro_ok {s : State} (hp : PreB s) (tab : Nat → Nat) (ht : ∀ k < 256, tab k < 2 ^ 32) (d : BitVec 32) (k : Nat)
    (hd : BitVec.ofNat 32 (4 * k) = d) (he : encodable d = true) :
    WP isa (.block (storeTab tab 256 ++ loadNQ .r4 ++ loadQ .r5 ++ ([.dp .add .r1 .r1 (.imm d)] : List Instr))) s
      (LI tab s (lift (polyAt s.mem (F s))) k) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeTab_ok tab ht s (zB := ps s) rfl hp.fitS hp.wS) fun s₁ ⟨ht₁, hf₁, k₁⟩ => ?_
  have e1 : s₁.gpr .r1 = ps s := k₁.gpr .r1 (by decide)
  have e0 : s₁.gpr .r0 = pf s := k₁.gpr .r0 (by decide)
  run_block [loadNQ, loadQ, e0, e1, he, loadNQ_val, loadQ_val]
  refine ⟨by simp [e0], by simp [hd], by simp, by simp, ?_, ht₁, hf₁.mono (by simp), ?_⟩
  · exact lp_lift (polyIs_frame hf₁ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs)
      ⟨hp.red, rfl⟩)
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [k₁.gpr _ (by decide : Reg.r11 ∈ _), k₁.gpr _ (by decide : Reg.lr ∈ _)],
      k₁.rd, k₁.wr, k₁.sp⟩

/-- `NTT`, as the code's three runs of layers. -/
theorem ntt_split (w : Poly) :
    Spec.MlDsa.ntt w = nttLayer ([4, 2].foldl nttLayer ([128, 64, 32, 16, 8].foldl nttLayer w)) 1 := by
  rw [VG.Proof.MlDsa.Arith.ntt_eq_layers]
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem pre_of {s : State} (h : (Proof.MlDsa.nttContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The frames' region is disjoint from the buffers. -/
theorem stack_disj {s : State} (hp : PreE s) :
    ∀ R ∈ [polyRegion (F s), polyRegion (S s)], (belowA s.sp (4 * nttSaved.length)).Disjoint R := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [hp.sF, hp.sS]

/-- The callee-saved registers, from those `saving nttSaved` restores. -/
theorem preserved_of {s s' s₂ : State}
    (hg : ∀ r, s'.gpr r = if r ∈ nttSaved then s.gpr r else s₂.gpr r)
    (h11 : s₂.gpr .r11 = s.gpr .r11) (hlr : s₂.gpr .lr = s.gpr .lr) : ∀ r ∈ preserved, s'.gpr r = s.gpr r :=
  preserved_of_saving hg fun r hr hn => by
    simp only [preserved, nttSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    exacts [h11, hlr]

theorem correct (u : Bool) {s : State} (hp : PreE s) :
    WP isa (Impl.MlDsa.Arm.Arith.ntt u) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.ntt (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp)
    (fun _ _ _ hf ⟨h11, hlr, hq⟩ => ⟨h11, hlr, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (stack_disj hp _ (List.mem_cons_self ..)).symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB (tabOf u zetaTab) (tabOf_lt u zetaTab_lt) 4 1 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkL u (Impl.MlDsa.Arm.Arith.bfly u len) len .add)
    [128, 64, 32, 16, 8] _ 1 s₂ (fun len hl => ?_) (by simp only [Chain]; decide) hI) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok (bfly_core u) zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)
        (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkS u (Impl.MlDsa.Arm.Arith.bfly u len) len .add)
    [4, 2] _ 32 s₃ (fun len hl => ?_) (by simp only [Chain]; decide) hI₃) fun s₄ hI₄ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by decide, blkS_ok (bfly_core u) zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)⟩
  refine WP.mono (layF_ok hpB (len := 1) (by decide)
    (blkS_ok (bflyC_core u) zetaTab_of hpB.fitF hpB.fitS (by decide) .add (.inl rfl) (by decide)) hI₄)
    fun s₅ hI₅ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI₅.frame
  · rw [hI₅.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [hI₅.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · have hr := layersF_rel u [4, 2] _ _ _ (by decide) (by decide)
      (layersF_rel u [128, 64, 32, 16, 8] 1 _ _ (by decide) (by decide) (lift_rel (polyAt s₁.mem (F s₁))))
    rw [← eP, ← eF, ntt_split]
    refine polyIs_of_toNat fun j hj => ?_
    rw [hI₅.poly j hj]
    exact layerFC_val u (by decide) hr (by decide) (by rw [n_eq] at hj; exact hj)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

/-- The public data of the transforms' contract are the stack pointer and
the two pointers. -/
theorem pub_of {t : Poly → Poly} {s₁ s₂ : State} (h : (Proof.MlDsa.inPlaceContract Arm.abi t 28).pub s₁ s₂) :
    s₁.sp = s₂.sp ∧ ∀ r ∈ [Reg.r0, Reg.r1], s₁.gpr r = s₂.gpr r := by
  sig_pub [Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨hsp, h0, h1⟩ := h
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem ct_base : ConstantTime isa (Proof.MlDsa.nttContract Arm.abi 28).pre (Proof.MlDsa.nttContract Arm.abi 28).pub
    (Impl.MlDsa.Arm.Arith.ntt false) :=
  ct_of_saving nttSaved _ [.r0, .r1] (fun _ _ h => pub_of h) (by native_taint_decide)

theorem ct_umaal : ConstantTime isa (Proof.MlDsa.nttContract Arm.abi 28).pre (Proof.MlDsa.nttContract Arm.abi 28).pub
    (Impl.MlDsa.Arm.Arith.ntt true) :=
  ct_of_savingU nttSaved _ [.r0, .r1] (fun _ _ h => pub_of h) (by taint_decide)

theorem verified (u : Bool) :
    Verified Arm.target (Impl.MlDsa.Arm.Arith.ntt u) (Proof.MlDsa.nttContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, by cases u <;> [exact ct_base; exact ct_umaal], ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct u (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Ntt
