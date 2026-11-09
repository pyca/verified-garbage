module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Narrow
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Narrow
meta import VerifiedGarbage.Proof.MlDsa.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.AddSub

/-! # ML-DSA's vector NTT on PPC64LE: `vg_mldsa_ntt`

The table of `z'` and the constants (`fill_ok`, `consts_run`) give the
layers' environment (`Env`), then the six layers of `len ≥ 4` (`wide_ok`)
and the two of `len = 2` and `len = 1` (`narrow_ok`) are the eight of
Algorithm 41 (`ntt_eq_layers`). The code has no frame and writes only
volatile registers. -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt
open VG.Proof.MlDsa.Arith

theorem ntt_eq_eight (P : Spec.MlDsa.Poly) :
    Spec.MlDsa.ntt P = nttLayer (nttLayer (wideLens.foldl nttLayer P) 2) 1 := by
  rw [ntt_eq_layers]
  simp only [nttLens, wideLens, List.foldl_cons, List.foldl_nil]

theorem setup_env {K : Nat → Nat} {s₀ : State} (hp : Pre s₀) {u t : State} (hu : FillInv K s₀ 255 u)
    (ht : ConstsOut u t) : EnvK K s₀ t ∧ PolyIs t.mem (F s₀) (polyAt s₀.mem (F s₀)) := by
  have fr : Frame [polyRegion (S s₀)] s₀.mem t.mem := by rw [ht.mem]; exact hu.frame
  refine ⟨⟨by rw [ht.gpr _ (by decide) (by decide), hu.gpr _ (by decide)], ht.q, ht.v5, ht.v16, ht.v17,
    ht.v18, ht.v19, fun r hr => ?_, by rw [ht.rd, hu.rd], by rw [ht.wr, hu.wr], by rw [ht.sp, hu.sp],
    by rw [ht.lr, hu.lr], fr.mono (by simp), fun p hp0 hp1 => ?_⟩, ?_⟩
  · have h11 : r ≠ .r11 := fun e => hr (e ▸ by decide)
    have h12 : r ≠ .r12 := fun e => hr (e ▸ by decide)
    rw [ht.gpr _ h11 h12, hu.gpr _ h12]
  · rw [ht.mem]; exact hu.tab p hp0 (by omega)
  · refine polyIs_frame fr (fun r hr => ?_) ⟨hp.red, rfl⟩
    rw [List.mem_singleton] at hr; subst hr; exact hp.disj

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ntt s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.lr = s₀.lr ∧
      PolyIs s.mem (F s₀) (Spec.MlDsa.ntt (polyAt s₀.mem (F s₀))) := by
  unfold ntt
  have hwr : ∀ p < 256, InRegions s₀.wr (s₀.gpr .r4 + BitVec.ofNat 64 (4 * p)) 4 := fun p hp' => by
    rw [hp.wr]
    exact ⟨polyRegion (S s₀), by simp, VG.Offset.contains_base (k := 1024) _ (by omega) (by omega)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok scrK hwr) fun u hu => WP.mono (consts_run u) fun t ht => ?_
  obtain ⟨env, hP⟩ := setup_env hp hu ht
  refine WP.seq (WP.mono (wide_ok hp env hP) fun s₁ h₁ => WP.mono (narrow_ok hp h₁) fun s₂ ⟨e₂, p₂⟩ => ?_)
  refine ⟨fun r hr => e₂.keep r (by revert r hr; decide), e₂.sp, e₂.lr, ?_⟩
  rw [ntt_eq_eight]; exact p₂

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.nttContract PPC64LE.abi 96).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨_, h2, h3, h4, _, _, h7, h8, h9⟩ := h
  exact ⟨h2, h3, h4, h7, h8, h9⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified PPC64LE.target ntt (Proof.MlDsa.nttContract PPC64LE.abi 96) := by
  refine ⟨fun s hs => ?_, VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4])
    (fun s₁ s₂ _ _ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hlr, h⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp, hlr⟩, ?_⟩
    sig_post [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs]
    exact h
  · sig_pub [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
      PPC64LE.argRegs] at h
    refine ⟨h.1, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, PPC64LE.abi,
        PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact Proof.MlDsa.PPC64LE.Arith.AddSub.reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.VNtt
