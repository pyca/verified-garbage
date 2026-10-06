import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.Jac
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStore

/-! Field environments after multi-coordinate public table transfers. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- A multiple-slot update can reconstruct its environment from the resulting
memory. Bounds on changed slots and the frame preserve every initialized slot. -/
theorem Inv.of_progKeep {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V W : List Nat}
    {E : Nat → Fin m} {s t : State} (hI : Inv M base size m Sl V E s)
    (hk : ProgKeep M base W s t) (hW : ∀ x ∈ W, Sl x)
    (hlt : ∀ x ∈ W, wordsVal t.mem base x M.n < m) :
    Inv M base size m Sl (W++V)
      (fun x => toM m (2^(64*M.n)) (wordsVal t.mem base x M.n)) t := by
  have hn := hI.scr.nowrap
  have hm : ∀ w ∈ W.map (·,8*M.n) ++ [(M.tmp,8*M.n)],
      M.mo+8*M.n ≤ w.1 ∨ w.1+w.2 ≤ M.mo := by
    intro w hw
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · exact (hL.mo x (hW x hx)).symm
    · exact hI.mod.sep
  refine ⟨hk.scr hI.scr,hI.mod.unch hk.unch hm hn,?_,?_,fun _ _ => rfl⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hW x hx
    · exact hI.sl x hx
  · intro x hx
    by_cases hw : x ∈ W
    · exact hlt x hw
    · have hv : x ∈ V := (List.mem_append.mp hx).resolve_left hw
      have hb := hL.le x (hI.sl x hv)
      rw [hk.unch.wordsVal (fun w hw' => ?_) (by omega)]
      · exact hI.lt x hv
      · simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw'
        rcases hw' with ⟨y,hy,rfl⟩ | rfl
        · exact hL.apart x y (hI.sl x hv) (hW y hy) (fun he => hw (he ▸ hy))
        · exact hL.tmp x (hI.sl x hv)

/-- Public lookup initializes the destination point in the field environment
and preserves the selected table point's Jacobian meaning. -/
theorem jacPublicPoint_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hn : K.M.n=4) (hy : K.E.y=K.E.x+32) (hz : K.E.z=K.E.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h2 : s.gpr .x2 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ht : K.tbl<4096)
    (hD : ∀ x ∈ [K.E.x,K.E.y,K.E.z], Sl x)
    (hT : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], x ∈ V)
    (hap : K.E.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.E.x)
    {P : Spec.Weierstrass.Point C}
    (hJ : InvJ C (E (Jacobian.tablePt K a).x) (E (Jacobian.tablePt K a).y)
      (E (Jacobian.tablePt K a).z) P) :
    WP isa (.block (Jacobian.publicEntry K)) s fun t =>
      ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t ∧
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z]++V) (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t K.E.x) (tmv C K.M.n base t K.E.y)
        (tmv C K.M.n base t K.E.z) P := by
  have hdz := hL.le K.E.z (hD _ (by simp))
  have htz := hL.le (Jacobian.tablePt K a).z (hI.sl _ (hT _ (by simp)))
  have hnw := hI.scr.nowrap
  rw [hn,hz] at hdz
  simp only [Jacobian.tablePt,hn] at htz
  refine WP.mono (jacPublicEntry_ok K hI.scr h2 ha ht (by omega)
    (hAl.sl _ (hD _ (by simp))) (by omega) hap) fun t ⟨hv,hk,ho⟩ => ?_
  have kp : ProgKeep K.M base [K.E.x,K.E.y,K.E.z] s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl <;> simp [clob]
    · have hx₀ := hx K.E.x (by simp)
      have hx₁ := hx K.E.y (by simp)
      have hx₂ := hx K.E.z (by simp)
      rw [hn] at hx₀ hx₁ hx₂
      rw [hy] at hx₁
      rw [hz] at hx₂
      omega
  have vx : wordsVal t.mem base K.E.x K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).x K.M.n := by
    simpa only [hn,Jacobian.tablePt,Nat.mul_zero,Nat.add_zero] using jacWords_coord (c := 0) (by decide) hv
  have vy : wordsVal t.mem base K.E.y K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).y K.M.n := by
    simpa only [hn,hy,Jacobian.tablePt,Nat.mul_one] using jacWords_coord (c := 1) (by decide) hv
  have vz : wordsVal t.mem base K.E.z K.M.n = wordsVal s.mem base (Jacobian.tablePt K a).z K.M.n := by
    simpa only [hn,hz,Jacobian.tablePt,show 32*2=64 from rfl] using jacWords_coord (c := 2) (by decide) hv
  have hlt : ∀ x ∈ [K.E.x,K.E.y,K.E.z], wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hT _ (by simp))
    · rw [vy]; exact hI.lt _ (hT _ (by simp))
    · rw [vz]; exact hI.lt _ (hT _ (by simp))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp)),hI.val _ (hT _ (by simp))]
  exact hJ

/-- Store a Jacobian accumulator into a table entry, initializing its three
field slots and retaining the point's meaning. -/
theorem jacStorePoint_ok {K : WinCfg} {base : Addr} {size a : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl)
    (hn : K.M.n=4) (hy : K.R.y=K.R.x+32) (hz : K.R.z=K.R.x+64)
    {V : List Nat} {E : Nat → Spec.Weierstrass.Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s)
    (h20 : s.gpr .x20 = off base (K.tbl+96*(a-1))) (hr8 : K.R.x%8=0)
    (hD : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z], Sl x)
    (hR : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ V)
    (hap : K.R.x+96 ≤ K.tbl+96*(a-1) ∨ K.tbl+96*(a-1)+96 ≤ K.R.x)
    {P : Spec.Weierstrass.Point C} (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa (.block (Jacobian.tableStore K)) s fun t =>
      ProgKeep K.M base [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z] s t ∧
      Inv K.M base size C.p Sl ([(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z]++V)
        (tmv C K.M.n base t) t ∧
      InvJ C (tmv C K.M.n base t (Jacobian.tablePt K a).x)
        (tmv C K.M.n base t (Jacobian.tablePt K a).y) (tmv C K.M.n base t (Jacobian.tablePt K a).z) P := by
  have hrz := hL.le K.R.z (hI.sl _ (hR _ (by simp)))
  have hdz := hL.le (Jacobian.tablePt K a).z (hD _ (by simp))
  rw [hn,hz] at hrz
  simp only [Jacobian.tablePt,hn] at hdz
  refine WP.mono (jacStoreWords_ok (n := 12) hI.scr h20 (by omega) (by omega) hr8
    (Or.symm hap) 12 (Nat.le_refl _)) fun t ⟨hv,hk,ho⟩ => ?_
  have kp : ProgKeep K.M base [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z] s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => ho x ?_⟩
    · simp only [List.mem_singleton] at hh
      subst hh; simp [clob]
    · have hx₀ := hx (Jacobian.tablePt K a).x (by simp)
      have hx₁ := hx (Jacobian.tablePt K a).y (by simp)
      have hx₂ := hx (Jacobian.tablePt K a).z (by simp)
      simp only [Jacobian.tablePt,hn] at hx₀ hx₁ hx₂
      omega
  have vx : wordsVal t.mem base (Jacobian.tablePt K a).x K.M.n = wordsVal s.mem base K.R.x K.M.n := by
    simpa only [hn,Jacobian.tablePt,Nat.mul_zero,Nat.add_zero] using jacWords_coord (c := 0) (by decide) hv
  have vy : wordsVal t.mem base (Jacobian.tablePt K a).y K.M.n = wordsVal s.mem base K.R.y K.M.n := by
    simpa only [hn,hy,Jacobian.tablePt,Nat.mul_one] using jacWords_coord (c := 1) (by decide) hv
  have vz : wordsVal t.mem base (Jacobian.tablePt K a).z K.M.n = wordsVal s.mem base K.R.z K.M.n := by
    simpa only [hn,hz,Jacobian.tablePt,show 32*2=64 from rfl] using jacWords_coord (c := 2) (by decide) hv
  have hlt : ∀ x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z],
      wordsVal t.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vx]; exact hI.lt _ (hR _ (by simp))
    · rw [vy]; exact hI.lt _ (hR _ (by simp))
    · rw [vz]; exact hI.lt _ (hR _ (by simp))
  refine ⟨kp,hI.of_progKeep hL kp hD hlt,?_⟩
  unfold tmv
  rw [vx,vy,vz,hI.val _ (hR _ (by simp)),hI.val _ (hR _ (by simp)),hI.val _ (hR _ (by simp))]
  exact hJ

end VG.Proof.Weierstrass.AArch64
