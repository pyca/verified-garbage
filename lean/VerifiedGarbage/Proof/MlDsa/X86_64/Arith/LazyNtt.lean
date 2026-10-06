import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNormalize

/-! Lazy forward NTT: range/congruence through eight layers, followed by
canonical reduction, under the existing public NTT contract. -/
namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep yconst_ok)
open VG.Spec.MlDsa (ntt polyAt)

def transform (F : Poly) : Poly :=
  layer (layer (layer (layer (layer (layer (layer (layer F 128) 64) 32) 16) 8) 4) 2) 1

theorem transform_rel (f : VG.Spec.MlDsa.Poly) : Rel 17 (transform (lift f)) (ntt f) := by
  have h0 := lift_rel f
  have h1 := layer_rel (by decide : 1 ≤ 15) h0 (by decide : 128 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h2 := layer_rel (by decide : 3 ≤ 15) h1 (by decide : 64 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h3 := layer_rel (by decide : 5 ≤ 15) h2 (by decide : 32 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h4 := layer_rel (by decide : 7 ≤ 15) h3 (by decide : 16 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h5 := layer_rel (by decide : 9 ≤ 15) h4 (by decide : 8 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h6 := layer_rel (by decide : 11 ≤ 15) h5 (by decide : 4 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h7 := layer_rel (by decide : 13 ≤ 15) h6 (by decide : 2 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h8 := layer_rel (by decide : 15 ≤ 15) h7 (by decide : 1 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  simpa only [ntt_eq_layers, nttLens, List.foldl_cons, List.foldl_nil, transform] using h8

theorem lift_mem {m : Mem} {p : Addr} {f : VG.Spec.MlDsa.Poly} (hp : VG.Spec.MlDsa.PolyIs m p f) :
    PolyIs m p (lift f) := by
  intro i hi
  rw [VG.Proof.MlDsa.Arith.polyIs_toNat hp hi, getElem!_pos (lift f) i hi, lift, Vector.getElem_map,
    getElem!_pos f i hi]

theorem correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa lazyNtt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    ynttBody_ok hs k1 f1 (G := ntt (polyAt s.mem (s.gpr .rdi))) fun s2 hI hdi hsi hwf hw => ?_
  refine WP.seq (WP.mono (yconst_ok .xmm11 16760834 s2) fun w ⟨lc, kc, mc, _, oc⟩ => ?_)
  have hc : YConsts w := fun l hl => ⟨⟨by
      rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).q,
    by rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).qinv⟩,
    by rw [State.proj_xmm, lc l hl]; rfl⟩
  have hi : LIY (s.gpr .rdi) (s.gpr .rsi) s2 (lift (polyAt s.mem (s.gpr .rdi))) w :=
    ⟨by rw [mc]; exact lift_mem hI.P, by rw [mc]; exact hI.T, hc,
      kc.mono (by simp), by rw [mc]; exact Frame.refl _ _⟩
  refine LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hi
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay4_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay2_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay1_ok hd) ?_ hI
  intro u hu
  refine WP.seq (WP.mono (normalize_ok (transform_rel _) u hu.c
    (by rw [hu.keep.gpr (by decide), hdi]) hu.P (by rw [hu.keep.2.2]; exact hwf)) fun v ⟨hv, hb⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = v.mem) (by simp only [yepi]; vrund; rfl) fun u' hm => ?_
  rw [hm]
  exact ⟨hv, hu.frame.trans hb.frame⟩

theorem ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub lazyNtt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem verified : Verified X86_64.target lazyNtt (Spec.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    mldsa_implies [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith.Lazy
