import VerifiedGarbage.Proof.P256.EcdhJac.BuildStep

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem buildLoop_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hi : CoZInv base P k 2 s) :
    WP isa (.loop Impl.P256.EcdhJac.buildStep (.nonzero .x .x4)) s fun t =>
      Frame base buildWork s t ∧ CoZInv base P k 16 t := by
  refine WP.loop (M:=isa)
    (fun j t => 1≤j ∧ j≤14 ∧ Frame base buildWork s t ∧ CoZInv base P k (16-j) t)
    (fun j a ⟨hj,hj14,hf,hi⟩ => ?_) 14 s ⟨by decide,by decide,AllocatedFrame.refl _ _ _ _,hi⟩
  refine WP.mono (buildStep_ok hC ha hO hP (by omega) (by omega) hi) fun t ⟨kt,it,ct⟩ => ?_
  have hn : 16-j+1=16-(j-1) := by omega
  rw [hn] at it ct
  have hz : (t.read .x .x4 != 0)=decide (j-1≠0) := by
    rw [read_x,ct]
    by_cases h : j-1=0
    · rw [h]; rfl
    · rw [decide_eq_true h,bne_iff_ne,ne_eq]
      intro he
      have hh : BitVec.ofNat 64 (16-(j-1)) = (16 : BitVec 64) := by bv_omega
      have he' := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_ofNat,show (16 : BitVec 64).toNat=16 from rfl,
        Nat.mod_eq_of_lt (show 16-(j-1)<2^64 by omega)] at he'
      omega
  by_cases h : j-1=0
  · refine Or.inl ⟨?_,hf.trans kt,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz,h]; rfl
    · simpa only [h,Nat.sub_zero] using it
  · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,hf.trans kt,it⟩
    show some (t.read .x .x4 != 0)=some true
    rw [hz,decide_eq_true h]

/-- The fixed sixteen-entry co-Z table supports every scalar, including invalid inputs. -/
theorem build_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hf : Fixed base P k s) :
    WP isa Impl.P256.EcdhJac.build s fun t =>
      Frame base buildWork s t ∧ Fixed base P k t ∧ TblOk base P 16 t := by
  unfold Impl.P256.EcdhJac.build
  refine WP.seq (WP.mono (buildStart_ok hf) fun a ⟨ka,ia⟩ => ?_)
  obtain ⟨tr,b,he,kb,ib⟩ := buildDblu_ok hC ha hO hP ia
  cases he with
  | seq h1 h2 =>
    obtain ⟨tr,t,ht,kt,it⟩ := buildLoop_ok hC ha hO hP ib
    exact ⟨_,t,.seq h1 (.seq h2 ht),ka.trans (kb.trans kt),it.inv.fixed,it.inv.table⟩
end VG.Proof.P256.EcdhJac
