module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.TableLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Math

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

abbrev Table (base : Addr) (P Q : Point C) (m : Nat) (s : State) : Prop :=
  ∀ d,1 ≤ d → d ≤ m → PointAt base s (tablePt d) (pair P Q (d%4) (d/4))

theorem entry_from_generator : CopyLayout entry gSource := ⟨by decide,by decide,by decide,by decide,by decide⟩
theorem entry_from_peer : CopyLayout entry qSource := ⟨by decide,by decide,by decide,by decide,by decide⟩

theorem tableStep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P = true) (hQ : onCurve C Q = true)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s) :
    WP isa (tableStep d) s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q d t := by
  have hp : previous d < d := previous_lt h1
  have hp15 : previous d ≤ 15 := by omega
  let A := pair P Q ((previous d)%4) ((previous d)/4)
  have prep : WP isa (.block (if previous d=0 then infinity else copyPt 4 resultPt (tablePt (previous d)))) s
      fun t => Changes base loopWork s t ∧ Inputs base P Q t ∧ PointAt base t resultPt A := by
    by_cases hz : previous d=0
    · rw [ite_eq_left hz]
      refine WP.mono (infinity_ok hi.scr hc hC) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      refine ⟨W,hi.unch (W.mono loopWork_sub),?_⟩
      have e : A=.infinity := by dsimp only [A]; rw [hz]; exact pair_zero P Q
      rw [e]; exact p
    · rw [ite_eq_right hz]
      refine WP.mono (copy_point hi.scr (load_layout (by omega) hp15)
        (ht (previous d) (by omega) (by omega))) fun t ⟨k,p,_⟩ => ?_
      have W := k.mono resultWork_sub
      exact ⟨W,hi.unch (W.mono loopWork_sub),p⟩
  have code : tableStep d = .seq (.block ((if previous d=0 then infinity else copyPt 4 resultPt (tablePt (previous d))) ++
    affineEntry (if d%4=0 then PX else GX) (if d%4=0 then PY else GY)))
    (.seq addPoints (.block (copyPt 4 (tablePt d) resultPt))) := by
    by_cases hz : d%4=0
    · simp only [tableStep,previous,ite_eq_left hz]
    · simp only [tableStep,previous,ite_eq_right hz]
  rw [code]
  rw [WP.seq_iff,WP.block_append_iff]
  refine WP.mono prep fun s₁ ⟨k₁,I₁,R₁⟩ => ?_
  have aff : WP isa (.block (affineEntry (if d%4=0 then PX else GX) (if d%4=0 then PY else GY))) s₁
      fun t => Changes base entryWork s₁ t ∧ PointAt base t entry (if d%4=0 then Q else P) := by
    by_cases hz : d%4=0
    · simp only [ite_eq_left hz]
      change WP isa (.block (copyPt 4 entry qSource)) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_peer I₁.peer) fun t ⟨k,p,_⟩ => ⟨k,p⟩
    · simp only [ite_eq_right hz]
      change WP isa (.block (copyPt 4 entry gSource)) s₁ _
      exact WP.mono (copy_point I₁.scr entry_from_generator I₁.generator) fun t ⟨k,p,_⟩ => ⟨k,p⟩
  refine WP.mono aff fun s₂ ⟨k₂,E₂⟩ => ?_
  have W₂ := k₁.trans (k₂.mono entryWork_sub)
  have I₂ := hi.unch (W₂.mono loopWork_sub)
  have R₂ := k₂.point I₁.scr R₁ (by decide) (by decide)
  have he : onCurve C (if d%4=0 then Q else P)=true := by
    by_cases hz : d%4=0
    · rw [ite_eq_left hz]; exact hQ
    · rw [ite_eq_right hz]; exact hP
  have hA : onCurve C A=true := pair_curve hC hP hQ _ _
  refine WP.seq (WP.mono (sum_points hc hC I₂.scr I₂.mod I₂.a I₂.b I₂.a_lt I₂.b_lt he hA E₂ R₂)
    fun s₃ ⟨k₃,R₃,_⟩ => ?_)
  have W₃ := W₂.trans (k₃.mono addWork_sub)
  have I₃ := hi.unch (W₃.mono loopWork_sub)
  have e : add (if d%4=0 then Q else P) A=pair P Q (d%4) (d/4) := table_step hC hP hQ h1
  rw [e] at R₃
  refine WP.mono (copy_point I₃.scr (store_layout h1 h15) R₃) fun t ⟨k₄,R₄,_⟩ => ?_
  have W₄ := (W₃.mono loopWork_sub).trans (k₄.cover (tableWork_cover h1 h15))
  refine ⟨W₄,hi.unch W₄,fun j hj hjd => ?_⟩
  by_cases heq : j=d
  · subst j; exact R₄
  · have hj' : j < d := by omega
    have old := W₃.table hi.scr hj (by omega) (ht j hj (by omega))
    exact k₄.point I₃.scr old
      (fun x hx => Nat.le_trans (table_coord_bounds hj (by omega) x hx).2.1 (by decide))
      (earlier_table_apart hj hj')

theorem build_ok {base : Addr} {P Q : Point C}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true) :
    ∀ m,m ≤ 15 → ∀ {s : State},Inputs base P Q s →
      WP isa (build m) s fun t =>
        Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q m t
  | 0,_,s,hi => WP.block_nil
      ⟨⟨rfl,rfl,rfl,rfl,Unch.refl _ _ _⟩,hi,fun _ h1 h0 => False.elim (by omega)⟩
  | m+1,hm,s,hi => by
    rw [build]
    refine WP.seq (WP.mono (build_ok hc hC hP hQ m (by omega) hi) fun t ⟨k,I,T⟩ => ?_)
    refine WP.mono (tableStep_ok hc hC hP hQ (by omega) hm I (by simpa only [Nat.add_sub_cancel] using T))
      fun u ⟨k',I',T'⟩ => ⟨k.trans k',I',T'⟩
end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
