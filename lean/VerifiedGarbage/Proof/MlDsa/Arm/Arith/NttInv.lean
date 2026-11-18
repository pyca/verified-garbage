module

public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`), with the negated zetas, from the last, and
`bflyInv_core`: the first seven layers leave words congruent to those of
`NTT⁻¹`'s (`layerI`, `layersI_rel`). The last layer's one block is the loop
over groups of four of `bflyInvS` (`grpLoop_ok` with `bflyInvS_core`), with
`8347681 = 256⁻¹ mod q` and the layer's zeta times it in registers
(`scalePre_ok`): it leaves the last layer's coefficients times `256⁻¹`
(`lastInv_val`), which `nttInv_split` says is `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Arith.NttInv

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.Ntt
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ ChainInv (128 / len - 1) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEndInv : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEndInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ nttInvLens, len ∈ nttLens ∧ 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 256 ∧
    256 / len = 2 * (128 / len) := by decide

theorem negZetaTab_of : TabOf negZetaTab (fun m => -zetas m) := fun k _ => negZetaNat_eq k

theorem negZetaTab_lt : ∀ k < 256, negZetaTab k < q := fun k _ => negZetaNat_lt k

theorem lays_ok {u : Bool} {s₁ : State} (hp : PreB s₁) (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : LPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ nttInvLens ∧
        BlockOk (blk len) (opI u) (tabOf u negZetaTab) (fun m => -zetas m) .sub len (pf s₁) (ps s₁)) →
      ChainInv k ls → LI (tabOf u negZetaTab) s₁ G k s →
      WP isa (lays blk ls) s fun s' => LI (tabOf u negZetaTab) s₁ (ls.foldl (layerI u) G) (chainEndInv k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen', hblk⟩ := hls len (List.mem_cons_self ..)
    obtain ⟨hlen, h1, h2, h3⟩ := lens_inv len hlen'
    have hl0 := (lens_facts len hlen).2.2.2.1
    refine WP.seq (WP.mono (lay_ok hblk hlen
      (fun c => 256 / len - 1 - c) (fun c hc => by omega_using [h2])
      (fun c hc => by
        simp only [nextZ, reduceCtorEq, ite_false]
        rw [show 4 * (256 / len - 1 - c) = 4 * (256 / len - 1 - (c + 1)) + 4 by omega_using [h1, hc], BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact BitVec.add_sub_cancel _ _)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.r5 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    exact lays_ok hp blk ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1']; congr 3; omega_using [h3]) hk' hp.fs.symm)

/-! ## The last layer -/

theorem scaleZeta_eq : scaleZeta = (-zetas 1 * cInv).val := by
  rw [Fin.val_mul, ← negZetaNat_eq]; rfl

theorem scaleZeta_lt : scaleZeta < q := by rw [scaleZeta_eq]; exact Fin.isLt _

/-- What `loadZ` leaves of a constant less than `q`: the constant, and what
goes with it. -/
theorem loadZ_word {c : Nat} (hc : c < q) (z : Zq) (hz : c = z.val) :
    (BitVec.ofNat 16 (c / 65536) ++ ((BitVec.ofNat 16 (c % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
        zb z ∧
      (BitVec.ofNat 16 (zsOf c / 65536) ++ ((BitVec.ofNat 16 (zsOf c % 65536)).setWidth 32).extractLsb' 0 16 :
        BitVec 32) = bzs (zb z) := by
  constructor
  · exact (tab_word (t := fun _ => c) (fun _ _ => Nat.lt_trans hc (by decide)) 0 (by decide)).trans
      (congrArg (BitVec.ofNat 32) hz)
  · refine (tab_word (t := fun _ => zsOf c) (fun _ _ => zsN_lt hc) 0 (by decide)).trans ?_
    rw [bzs, toNat_val, hz]; rfl

/-- The constants of the last layer, and the count of its groups. -/
theorem scalePre_ok (u : Bool) {s : State} (h4 : s.gpr .r4 = Nw) (h5 : s.gpr .r5 = Qw) :
    WP isa (.block (scalePre u)) s fun s' =>
      ScaleIn u (-zetas 1) s' ∧ s'.gpr .r3 = BitVec.ofNat 32 (1 * (32 - 0)) ∧ s'.mem = s.mem ∧
        Keep [.r0, .r11, .lr] s s' := by
  obtain ⟨c1, c2⟩ := loadZ_word (c := 8347681) (by decide) cInv rfl
  obtain ⟨z1, z2⟩ := loadZ_word scaleZeta_lt (-zetas 1 * cInv) scaleZeta_eq
  cases u <;>
  · run_block [scalePre, loadZ, quot, bquot, zw_false, zw_true, ScaleIn, ZetaIn, h4, h5, c1, c2, z1, z2,
      Bool.false_eq_true]
    keep_simp

/-- `NTT⁻¹`, as the code's runs of layers and its last layer. -/
theorem nttInv_split (w : Poly) : Spec.MlDsa.nttInv w =
    (nttInvLayer ([8, 16, 32, 64].foldl nttInvLayer ([1, 2, 4].foldl nttInvLayer w)) 128).map (· * cInv) := by
  rw [VG.Proof.MlDsa.Arith.nttInv_eq_layers]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

theorem pre_of {s : State} (h : (Proof.MlDsa.nttInvContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem correct (u : Bool) {s : State} (hp : PreE s) :
    WP isa (Impl.MlDsa.Arm.Arith.nttInv u) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp)
    (fun _ _ _ hf ⟨h11, hlr, hq⟩ => ⟨h11, hlr, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (stack_disj hp _ (List.mem_cons_self ..)).symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB (tabOf u negZetaTab) (tabOf_lt u negZetaTab_lt) 1020 255 rfl (by decide))
    fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkS u (Impl.MlDsa.Arm.Arith.bflyInv u len) len .sub)
    [1, 2, 4] _ 255 s₂ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;>
      exact ⟨by decide, blkS_ok (bflyInv_core u) negZetaTab_of hpB.fitF hpB.fitS (by decide) .sub (.inr rfl)
        (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hpB (fun len => nttBlkL u (Impl.MlDsa.Arm.Arith.bflyInv u len) len .sub)
    [8, 16, 32, 64] _ 31 s₃ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI₃) fun s₄ hI₄ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok (bflyInv_core u) negZetaTab_of hpB.fitF hpB.fitS (by decide) .sub (.inr rfl)
        (by decide) (by decide)⟩
  refine WP.seq (WP.mono (scalePre_ok u hI₄.r4 hI₄.r5) fun s₅ ⟨hz, e3, m₅, k₅⟩ => ?_)
  have hG := hI₄.poly
  rw [← m₅] at hG
  refine WP.mono (grpLoop_ok (bflyInvS_core u) (fun _ _ _ hk h => h.keep hk) hpB.fitF (len := 128) (start := 0)
    (N := 32) (by decide) (by decide) (by decide) (by decide) (by decide) (-zetas 1) _ s₅
    (by rw [k₅.gpr .r0 (by decide), hI₄.r0]; simp) hz hG
    (by rw [k₅.wr, hI₄.keep.wr]; exact hpB.wF) e3) fun s₆ ⟨hP, hf, _, k₆⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI₄.frame.trans (by rw [← m₅]; exact hf.mono (by simp))
  · rw [k₆.gpr .r11 (by decide), k₅.gpr .r11 (by decide), hI₄.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [k₆.gpr .lr (by decide), k₅.gpr .lr (by decide), hI₄.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · have h8 : Rel 8 _ _ := layersI_rel u [1, 2, 4] 1 _ _ (by decide) (Nat.le_refl 1) (by decide)
      (lift_rel (polyAt s₁.mem (F s₁)))
    have hr : Rel 128 _ _ := layersI_rel u [8, 16, 32, 64] 8 _ _ (by decide) (by decide) (by decide) h8
    rw [← eP, ← eF, nttInv_split]
    refine polyIs_of_toNat fun j hj => ?_
    rw [hP j hj]
    exact lastInv_val u hr (by rw [n_eq] at hj; exact hj)

theorem ct_base :
    ConstantTime isa (Proof.MlDsa.nttInvContract Arm.abi 28).pre (Proof.MlDsa.nttInvContract Arm.abi 28).pub
      (Impl.MlDsa.Arm.Arith.nttInv false) :=
  ct_of_saving nttSaved _ [.r0, .r1] (fun _ _ h => pub_of h) (by native_taint_decide)

theorem ct_umaal :
    ConstantTime isa (Proof.MlDsa.nttInvContract Arm.abi 28).pre (Proof.MlDsa.nttInvContract Arm.abi 28).pub
      (Impl.MlDsa.Arm.Arith.nttInv true) :=
  ct_of_savingU nttSaved _ [.r0, .r1] (fun _ _ h => pub_of h) (by taint_decide)

theorem verified (u : Bool) :
    Verified Arm.target (Impl.MlDsa.Arm.Arith.nttInv u) (Proof.MlDsa.nttInvContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, by cases u <;> [exact ct_base; exact ct_umaal], ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct u (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.NttInv
