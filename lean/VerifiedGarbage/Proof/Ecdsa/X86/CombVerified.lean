import VerifiedGarbage.Proof.Ecdsa.X86.CombSat

/-! # The comb signing implementation satisfies the shared API contract -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Weierstrass

theorem combSign_regions {s : State} (h : combSignSpec.pre s) :
    s.rd = [dR p256Comb s, digestR p256Comb s, kR p256Comb s] ++
      Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts ∧
    s.wr = [outR p256Comb s, scR s, argsR s] := by
  sig_pre [combSignSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
    Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow] at h
  obtain ⟨_, _, hd, _, _, _, _, _, ht, hw, _⟩ := h
  refine ⟨?_, hw⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]
  simp only [p256Comb_consts, Abi.constRegions_cons, Abi.constRegions_nil,
    dR, digestR, kR, ptr, show p256Comb.C.len = 32 from rfl]

theorem signComb_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) : Verified X86.target signP256Comb combSignSpec := by
  have hs : ∃ s, combSignSpec.pre s := ⟨combSatState, combSat_spec⟩
  have sl : ∃ s, combSignLocal.pre s := ⟨_, combSign_pre combSat_spec⟩
  have co : ∀ d, p256Comb.comb = some d → CombOk p256Comb d := by
    intro d h
    have e : p256d = d := Option.some.inj h
    rw [← e]; exact p256Comb_shape
  have hv : Verified X86.target signP256Comb combSignLocal := Verified.of_correct (k := combSignLocal)
    (fun s h => by
      obtain ⟨tr, t, e, a, p⟩ := signComb_ok (p256Comb_ok hI) hL (p256Comb_tables hL) co p256Comb_am3 rfl signComb_spG
        signComb_spTail h
      exact ⟨tr, t, e, a, p⟩)
    (signComb_ct (p256Comb_ok hI) hL (p256Comb_tables hL) p256Comb_shape p256Comb_am3 signComb_spMul) (.refl sl)
  refine Verified.narrowTo hv combSignRd combSignWr (fun _ h => combSign_pre h) ?_ ?_ ?_ ?_ hs
  · intro s h a n ⟨r, hr, hc⟩
    obtain ⟨rd, wr⟩ := combSign_regions h
    refine ⟨r, ?_, hc⟩
    rw [rd, wr]
    simp only [combSignRd, combSignWr, signRd, signWr] at hr
    generalize Abi.constRegions (fun n => (s.syms n).setWidth 64) p256Comb.combConsts = C at hr ⊢
    simp only [List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | h | rfl | rfl <;>
      simp [h, outR, dR, digestR, kR, scR, argsR, show p256Comb.C.len = 32 from rfl, ptr, size]
  · intro s h a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [(combSign_regions h).2]
    simp only [combSignWr, signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · intro s t _ h
    sig_post [combSignSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts]
    have er : (t.gpr .edx ++ t.gpr .eax).setWidth 32 = t.gpr .eax := BitVec.setWidth_append_eq_right
    rw [er]
    simp only [combSignLocal, SignPost, State.withRegions_mem, State.withRegions_gpr,
      arg_withRegions, ptr, show p256Comb.C = Spec.P256.curve from rfl,
      Spec.P256.curve, Nat.reduceMul] at h
    split at h <;> rename_i he
    all_goals simp only [he]; exact h
  · intro s t _ _ h
    sig_pub [combSignSpec, Spec.Ecdsa.P256.inst, Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig, Spec.P256.curve, Spec.Ecdsa.scratchWords, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, p256Comb_consts, Abi.withConsts] at h
    obtain ⟨he, hy, a0, a1, a2, a3, a4⟩ := h
    refine ⟨he, ?_, ?_⟩
    · intro j hj
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hj' with rfl | rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
    · exact hy

end VG.Proof.Ecdsa.X86
