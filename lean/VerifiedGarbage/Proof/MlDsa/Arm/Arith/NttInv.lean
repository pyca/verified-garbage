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
`bflyInv_spec`: the eight layers leave words congruent to those of `NTT⁻¹`
(`layerI`, `layersI_rel`); then every coefficient is multiplied by
`8347681 = 256⁻¹ mod q` and reduced (`scale_ok`, `map_ok`), which
`nttInv_eq_layers` says is `NTT⁻¹`.
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

theorem lens_inv : ∀ len ∈ nttInvLens, len ∈ nttLens ∧ 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 256 ∧
    256 / len = 2 * (128 / len) := by decide

theorem negZetaTab_of : TabOf negZetaTab (fun m => -zetas m) := fun k _ => negZetaNat_eq k

theorem negZetaTab_lt : ∀ k < 256, negZetaTab k < q := fun k _ => negZetaNat_lt k

theorem lays_ok {s₁ : State} (hp : PreB s₁) :
    ∀ (ls : List Nat) (G : LPoly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttInvLens) → ChainInv k ls →
      LI negZetaTab 1072693376 s₁ G k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', LI negZetaTab 1072693376 s₁ (ls.foldl layerI G) k' s'
  | [], G, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, h1, h2, h3⟩ := lens_inv len (hls len (List.mem_cons_self ..))
    have hl0 := (lens_facts len hlen).2.2.2.1
    refine WP.seq (WP.mono (lay_ok bflyInv_spec negZetaTab_of hp.fitF hp.fitS hlen .sub (.inr rfl)
      (fun c => 256 / len - 1 - c) (fun c hc => by omega_using [h2])
      (fun c hc => by
        simp only [nextZ, reduceCtorEq, ite_false]
        rw [show 4 * (256 / len - 1 - c) = 4 * (256 / len - 1 - (c + 1)) + 4 by omega_using [h1, hc], BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact BitVec.add_sub_cancel _ _)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.r5 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    refine lays_ok hp ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1']; congr 3; omega_using [h3]) hk' hp.fs.symm)

theorem chain_inv : ChainInv 255 nttInvLens := by simp only [nttInvLens, ChainInv]; decide

/-! ## The scaling -/

/-- The multiplier of the scaling. -/
abbrev cInv : Zq := 8347681

theorem scale_ok : MapOk scaleBody (fun v => bcsub (bprod v cInv)) (ZetaIn Qw cInv) := by
  intro s x c h0 h3 ⟨h4, h5, h6, h7⟩ iA oA
  run_block [scaleBody, mulz, red, mulq, csub, bmulz, bmulq, bred, bcsub, ZetaIn, h0, h3, h4, h5, h6, h7, iA, oA]
  keep_simp

theorem scalePre_ok {s : State} (h4 : s.gpr .r4 = Nw) :
    WP isa (.block scalePre) s fun s' =>
      ZetaIn Qw cInv s' ∧ s'.gpr .r3 = BitVec.ofNat 32 256 ∧ s'.mem = s.mem ∧ Keep [.r0, .r11, .lr] s s' := by
  run_block [scalePre, loadQ, quot, bquot, ZetaIn, loadQ_val, h4]
  refine ⟨by decide, ?_⟩
  keep_simp

theorem pre_of {s : State} (h : (Proof.MlDsa.nttInvContract Arm.abi 28).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.nttInv s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (F s), polyRegion (S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (F s) (Spec.MlDsa.nttInv (polyAt s.mem (F s))))
    s hp.sp (stack_disj hp)
    (fun _ _ _ hf ⟨h11, hlr, hq⟩ => ⟨h11, hlr, polyIs_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (stack_disj hp _ (List.mem_cons_self ..)).symm) hq⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := pre_entry hp hE
  refine WP.seq (WP.mono (pro_ok hpB negZetaTab negZetaTab_lt 0x80 0x3FF0 1072693376 1020 255 (by decide) rfl
    (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (lays_ok hpB nttInvLens _ 255 s₂ (fun _ h => h) chain_inv hI) fun s₃ ⟨k, hI'⟩ => ?_)
  refine WP.seq (WP.mono (scalePre_ok hI'.r4) fun s₄ ⟨hz, e3, m₄, k₄⟩ => ?_)
  refine WP.mono (map_ok scale_ok hpB.fitF (by rw [k₄.wr, hI'.keep.wr]; exact hpB.wF)
    ((k₄.gpr .r0 (by decide)).trans hI'.r0) e3 hz) fun s₅ ⟨hc, hf, k₅⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI'.frame.trans (by rw [← m₄]; exact hf.mono (by simp))
  · rw [k₅.gpr .r11 (by decide), k₄.gpr .r11 (by decide), hI'.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [k₅.gpr .lr (by decide), k₄.gpr .lr (by decide), hI'.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · have hr := layersI_rel nttInvLens 1 _ _ (fun l hl => (lens_inv l hl).1) (Nat.le_refl 1) (by decide)
      (lift_rel (polyAt s₁.mem (F s₁)))
    rw [← eP, ← eF, VG.Proof.MlDsa.Arith.nttInv_eq_layers]
    refine polyIs_of_toNat fun j hj => ?_
    have hj' : j < 256 := by rw [n_eq] at hj; exact hj
    rw [hc j hj', m₄, scale_val (hI'.poly j hj), (hr j hj').2, map_mul_get _ _ hj]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.nttInv (Proof.MlDsa.nttInvContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
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
