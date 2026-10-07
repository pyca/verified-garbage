import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombContract
import VerifiedGarbage.Proof.Ecdsa.X86.CombSat

/-! # Verified P-256 signature verification using the x86 comb -/
namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass

def vCombSatState : State := { combSatState with
  rd := [⟨0x1000, 65⟩, ⟨0x2000, 32⟩, ⟨0x3000, 64⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] }

theorem vCombSat_spec : vCombSpec.pre vCombSatState := by
  have a0 : arg vCombSatState 0 = 0x1000 := (combSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg vCombSatState 1 = 0x2000 := (combSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg vCombSatState 2 = 0x3000 := (combSat_arg 2 (by decide)).trans (by decide)
  have a3 : arg vCombSatState 3 = 0x4000 := (combSat_arg 3 (by decide)).trans (by decide)
  have held : ∀ i < p256W.length, vCombSatState.mem.readW
      ((vCombSatState.syms "VG_P256_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 :=
    combSatMem_held
  generalize e : vCombSatState = s
  sig_pre [vCombSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p256W_length]; rfl
  · rw [p256W_length]; decide
  · rw [p256W_length]
    intro r hr
    change r ∈ [⟨0x4000, 8192⟩, ⟨0x20004, 16⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2, a3]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem vComb_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : Verified X86.target vCombCode vCombSpec := by
  have hs : ∃ s, vCombSpec.pre s := ⟨vCombSatState, vCombSat_spec⟩
  have sl : ∃ s, vCombLocal.pre s := ⟨_, vComb_pre vCombSat_spec⟩
  have hv : Verified X86.target vCombCode vCombLocal := Verified.of_correct (k := vCombLocal)
    (fun s h => by obtain ⟨tr, t, e, a, p⟩ := vComb_ok hL hI h; exact ⟨tr, t, e, a, p⟩)
    (vComb_ct hL hI) (.refl sl)
  refine Verified.narrowTo hv vCombRd vCombWr (fun _ h => vComb_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := vComb_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simpa only [vCombRd, vCombWr, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [(vComb_regions h).2]
    simp only [vCombWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact List.mem_cons_self ..
  · intro s t _ h
    sig_post [vCombSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simpa only [vCombLocal, VPost, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p256Comb.C = Spec.P256.curve from rfl,
      Spec.P256.curve, Nat.reduceMul, Nat.reduceAdd] using h
  · intro s t _ _ h
    sig_pub [vCombSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hy, _leak, a0, a1, a2, a3⟩ := h
    refine ⟨he, ?_, hy⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3

end VG.Proof.Ecdsa.Verify.X86
