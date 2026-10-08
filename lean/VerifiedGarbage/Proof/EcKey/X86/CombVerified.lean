import VerifiedGarbage.Proof.EcKey.X86.CombContract

/-! # Verified P-256 public-key generation using the x86 comb -/
namespace VG.Proof.EcKey.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass

def pkCombSatState : State := { combSatState with
  rd := [⟨0x2000, 32⟩, ⟨0x100000, 151552⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x3000, 8192⟩, ⟨0x20004, 12⟩] }

theorem pkCombSat_spec : pkCombSpec.pre pkCombSatState := by
  have a0 : arg pkCombSatState 0 = 0x1000 := (combSat_arg 0 (by decide)).trans (by decide)
  have a1 : arg pkCombSatState 1 = 0x2000 := (combSat_arg 1 (by decide)).trans (by decide)
  have a2 : arg pkCombSatState 2 = 0x3000 := (combSat_arg 2 (by decide)).trans (by decide)
  have held : ∀ i < p256W.length, pkCombSatState.mem.readW
      ((pkCombSatState.syms "VG_P256_COMB").setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = p256W.getD i 0 :=
    combSatMem_held
  generalize e : pkCombSatState = s
  sig_pre [pkCombSpec, Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  refine ⟨by decide, by decide, ?_, held, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p256W_length]; rfl
  · rw [p256W_length]; decide
  · rw [p256W_length]
    intro r hr
    change r ∈ [⟨0x1000, 65⟩, ⟨0x3000, 8192⟩, ⟨0x20004, 12⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [p256W_length]; exact Region.disjoint_of_sep (by decide)
  · rw [a0, a1, a2]
    refine ⟨rfl, rfl, ?_⟩
    repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem pkComb_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : Verified X86.target pkCombCode pkCombSpec := by
  have hs : ∃ s, pkCombSpec.pre s := ⟨pkCombSatState, pkCombSat_spec⟩
  have sl : ∃ s, pkCombLocal.pre s := ⟨_, pkComb_pre pkCombSat_spec⟩
  have hv : Verified X86.target pkCombCode pkCombLocal := Verified.of_correct (k := pkCombLocal)
    (fun s h => by obtain ⟨tr, t, e, a, p⟩ := pkComb_ok hL hI h; exact ⟨tr, t, e, a, p⟩)
    (pkComb_ct hL hI) (.refl sl)
  refine Verified.narrowTo hv pkCombRd pkCombWr (fun _ h => pkComb_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := pkComb_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simp only [pkCombRd, pkCombWr] at hr
    generalize Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts = C at hr ⊢
    simp only [List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | h | rfl | rfl <;> simp [h]
  · intro s h a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [(pkComb_regions h).2]
    simp only [pkCombWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · intro s t _ h
    sig_post [pkCombSpec, Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simp only [pkCombLocal, PkPost, dk, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p256Comb.C = Spec.P256.curve from rfl,
      Spec.P256.curve, Nat.reduceMul, Nat.reduceAdd] at h
    dsimp only [p256Comb, p256, Spec.P256.curve, Spec.EcKey.bytesAt, Spec.Ecdsa.bytesAt] at h ⊢
    generalize hq : Spec.EcKey.publicKey _ _ = q at h ⊢
    rcases q with _ | _ | ⟨x, y⟩ <;> exact h
  · intro s t _ _ h
    sig_pub [pkCombSpec, Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hy, a0, a1, a2⟩ := h
    refine ⟨he, ?_, hy⟩
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2

end VG.Proof.EcKey.X86
