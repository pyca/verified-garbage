module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Narrow
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Verified
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNttInv.Narrow
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Verified
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub

/-! # ML-DSA's vector inverse NTT on PPC64LE: `vg_mldsa_inv_ntt`

The table of `invK` and the constants (`fill_ok`, `consts_run`, `setup_env`),
the layers of `len = 1` and `len = 2` (`inarrow_ok`), of `len = 4 … 128`
(`iwide_ok`), then the product by `f` (`scale_ok`): Algorithm 42
(`nttInv_eq_layers`). -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)

theorem nttInv_eq_eight (P : Spec.MlDsa.Poly) :
    Spec.MlDsa.nttInv P = (wideInvLens.foldl nttInvLayer (nttInvLayer (nttInvLayer P 1) 2)).map (· * 8347681) := by
  rw [nttInv_eq_layers]
  simp only [nttInvLens, wideInvLens, List.foldl_cons, List.foldl_nil]

/-- An environment kept through a frame that writes only scratch registers. -/
theorem EnvK.fr {K : Nat → Nat} {s₀ u t : State} (h : EnvK K s₀ u) {vs : List VReg} {gs : List Reg}
    (hf : Fr vs gs u t) (hv : ∀ r ∈ vs, r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v16 ∧ r ≠ .v17 ∧ r ≠ .v18 ∧ r ≠ .v19)
    (hg : ∀ r ∈ gs, r ∈ written ∧ r ≠ .r3) : EnvK K s₀ t :=
  ⟨by rw [hf.g _ fun e => (hg _ e).2 rfl]; exact h.r3,
   fun i hi => by rw [hf.v _ fun e => (hv _ e).1 rfl]; exact h.v4 i hi,
   by rw [hf.v _ fun e => (hv _ e).2.1 rfl, h.v5],
   by rw [hf.v _ fun e => (hv _ e).2.2.1 rfl, h.v16], by rw [hf.v _ fun e => (hv _ e).2.2.2.1 rfl, h.v17],
   by rw [hf.v _ fun e => (hv _ e).2.2.2.2.1 rfl, h.v18], by rw [hf.v _ fun e => (hv _ e).2.2.2.2.2 rfl, h.v19],
   fun r hr => by rw [hf.g _ fun e => hr (hg _ e).1]; exact h.keep r hr,
   by rw [hf.rd, h.rd], by rw [hf.wr, h.wr], by rw [hf.sp, h.sp], by rw [hf.lr, h.lr],
   by rw [hf.mem]; exact h.frame, by rw [hf.mem]; exact h.tab⟩

theorem e32 (x : BitVec 64) : x.extractLsb' 0 32 = x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

/-- `v` in each lane of `d`, through `r12`. -/
theorem splat_imm (u : State) {d : VReg} {v : Nat} (hv : v < 2 ^ 32) :
    WP isa (.block (loadImm .r12 v ++ ([.mtvsrd d .r12, .vop (.splat true d d 1)] : List Instr))) u fun t =>
      (∀ i < 4, (vword (t.vpr d) i).toNat = v) ∧ Fr [d] [.r12] u t := by
  unfold loadImm
  refine WP.cons exec_lis (WP.cons exec_ori (WP.cons rfl (WP.cons rfl (wp_nil ?_))))
  refine ⟨fun i hi => ?_, ⟨fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · simp only [State.writeV, State.write, ite_true]
    rw [vword_ofVWords _ hi, (vword_append _ _).2.1, e32, loadImm_lo hv]
    simpa using hv
  · simp only [List.mem_singleton] at hr
    simp only [State.writeV, hr, ite_false]; rfl
  · simp only [List.mem_singleton] at hr
    simp only [State.writeV, State.write, hr, ite_false]

theorem split2 (l : List Instr) (a b : Instr) (t : List Instr) : l ++ a :: b :: t = (l ++ [a, b]) ++ t := by
  simp

theorem scale_ok {s₀ : State} (hp : Pre s₀) {R : Spec.MlDsa.Poly} {s : State} (h : ILInv s₀ R 256 63 s) :
    WP isa scale s fun s' => IEnv s₀ s' ∧ PolyIs s'.mem (F s₀) (R.map (· * 8347681)) := by
  unfold scale
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (splat_imm s (d := .v2) (v := fInv) (by decide)) fun u₁ ⟨l₁, f₁⟩ => ?_
  rw [split2, WP.block_append_iff]
  refine WP.mono (splat_imm u₁ (d := .v3) (v := shoup fInv) (by decide)) fun u₂ ⟨l₂, f₂⟩ => ?_
  have e₂ : IEnv s₀ u₂ := (h.env.fr f₁ (by decide) (by decide)).fr f₂ (by decide) (by decide)
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by
    rw [f₂.g _ (by simp [hr]), f₁.g _ (by simp [hr])]
  have v2 : ∀ i < 4, (vword (u₂.vpr .v2) i).toNat = (8347681 : Spec.MlDsa.Zq).val := fun i hi => by
    rw [f₂.v _ (by decide), l₁ i hi]; rfl
  have v3 : ∀ i < 4, (vword (u₂.vpr .v3) i).toNat = (8347681 : Spec.MlDsa.Zq).val * 2 ^ 32 / Spec.MlDsa.q :=
    fun i hi => by rw [l₂ i hi]; rfl
  refine WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl,
    WP.block_cons_iff.2 ⟨_, rfl, WP.block_cons_iff.2 ⟨_, rfl, WP.block_nil ?_⟩⟩⟩⟩⟩
  refine wp_loop_nz (fun g t => SclInv s₀ R g t) (N := 16) (by decide) (fun g hg t ht => sgroup_ok hp hg ht)
    (fun t ht => ⟨ht.env, by rw [← smix_sixteen]; exact ht.poly⟩) ?_
  refine ⟨((((e₂.write (by decide) (by decide) _).write (by decide) (by decide) _).write
      (by decide) (by decide) _).write (by decide) (by decide) _).write (by decide) (by decide) _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.write, reduceCtorEq, ite_false, ite_true]; rw [g₂ _ (by decide), h.env.r3, coeffAddr]
  · simp only [State.write, reduceCtorEq, ite_false]; rw [g₂ _ (by decide)]; exact h.r9
  · rfl
  · rfl
  · rfl
  · rfl
  · exact v2
  · exact v3
  · show PolyIs u₂.mem _ _
    rw [f₂.mem, f₁.mem, smix_zero]; exact h.poly

theorem icorrect {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (F s₀) (Spec.MlDsa.nttInv (polyAt s₀.mem (F s₀))) := by
  unfold nttInv
  have hwr : ∀ p < 256, InRegions s₀.wr (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 4 := fun p hp' => by
    rw [hp.wr]
    exact ⟨polyRegion (S s₀), by simp, VG.Offset.contains_base (k := 1024) _ (by omega_using [hp']) (by omega_using [hp'])⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok invK hwr) fun u hu => WP.mono (consts_run u) fun t ht => ?_
  obtain ⟨env, hP⟩ := setup_env hp hu ht
  refine WP.seq (WP.mono (inarrow_ok hp env hP) fun s₁ ⟨e₁, p₁⟩ => WP.seq (WP.mono (iwide_ok hp e₁ p₁)
    fun s₂ h₂ => WP.mono (scale_ok hp h₂) fun s₃ ⟨e₃, p₃⟩ => ?_))
  refine ⟨fun r hr => e₃.keep r (by revert r hr; decide), e₃.sp, e₃.lr, ?_⟩
  rw [nttInv_eq_eight]; exact p₃

/-! ## Verified -/

theorem ipre_of {s : State} (h : (Proof.MlDsa.nttInvContract PPC64LE.abi 96).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨_, h2, h3, h4, _, _, h7, h8, h9⟩ := h
  exact ⟨h2, h3, h4, h7, h8, h9⟩

theorem iverified : Verified PPC64LE.target nttInv (Proof.MlDsa.nttInvContract PPC64LE.abi 96) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4])
    (fun s₁ s₂ _ _ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := icorrect (ipre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    refine ⟨h.1, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Proof.MlDsa.PPC64LE.Arith.AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.VNtt
