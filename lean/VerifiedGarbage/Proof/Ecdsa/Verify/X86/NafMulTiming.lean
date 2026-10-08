import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulReady

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass

theorem windowMulQ_relCT (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (ha : AM3 p256Comb.C)
    {base : Addr} {P : Point p256Comb.C} {k : Nat} {x y : Fe p256Comb.C}
    (hk : k<2^256) (hP : onCurve p256Comb.C P=true) :
    RelCT isa (fun s t => NafMulInput p256Comb base P k x y s ∧ NafMulInput p256Comb base P k x y t ∧ NafPublic s t)
      (Cfg.windowMulQ p256Comb) (fun _ _ => True) := by
  have setup := (nafSetup_relCT (base:=base) hc).mono
    (P':=fun s t => NafMulInput p256Comb base P k x y s ∧ NafMulInput p256Comb base P k x y t ∧ NafPublic s t)
    (fun _ _ ⟨hs,ht,hp⟩ => ⟨hs.scr,ht.scr,hp,by
      have e := hs.scalar.trans ht.scalar.symm
      change wordsVal _ _ _ 4=wordsVal _ _ _ 4 at e
      simpa only [wordsVal_eq_val32] using e⟩) (fun _ _ h => h)
  have setup' := setup.wpDep (fun _ _ ⟨hs,ht,_⟩ => ⟨nafMulReady_ok hc hC hs,nafMulReady_ok hc hC ht⟩)
  have after : RelCT isa (fun s t => True ∧ ∃ a b,
      (NafMulInput p256Comb base P k x y a ∧ NafMulInput p256Comb base P k x y b ∧ NafPublic a b) ∧
      (Keeps powClob a s ∧ NafMulReady base P k x y s) ∧
      (Keeps powClob b t ∧ NafMulReady base P k x y t))
      (.seq (Naf.window nafK p256Comb.SP) (Naf.finish nafK p256Comb.SP)) (fun _ _ => True) := by
    intro s t ts tt u v ⟨_,_,_,⟨_,_,pub⟩,⟨ks,hs⟩,⟨kt,ht⟩⟩ es et
    have pair := nafMulReady_pair hs ht (pub.keep ks kt (by decide) (by decide))
    have win := nafWindow_relCT (base:=base) (E:=tmv p256Comb.C p256Comb.n base s) (counter:=257)
      (nafQLay rfl) rfl (nafQWk hc rfl) (by decide)
      (unitMod_pow_two hc.p_odd _) hC ha (by decide) hk hP nafWindow_checks
    have finish : RelCT isa (NafRunPair nafK p256Comb.C base size P (Naf5.byte k) k 0)
        (Naf.finish nafK p256Comb.SP) (fun _ _ => True) := by
      intro a b ta tb a' b' ⟨⟨_,hp⟩,_⟩ ea eb
      exact scratch_relCT nafWindow_checks.finish _ _ _ _ _ _ hp ea eb
    exact (win.seq finish) _ _ _ _ _ _ ⟨pair,hs.input,ht.input⟩ es et
  unfold Cfg.windowMulQ
  apply RelCT.assoc
  exact setup'.seq after

end VG.Proof.Ecdsa.Verify.X86
