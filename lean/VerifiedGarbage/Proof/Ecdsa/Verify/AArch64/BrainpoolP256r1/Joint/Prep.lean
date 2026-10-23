module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Table
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.Math
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout

/-! Building the joint digit-pair table with the existing complete addition. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem tablePrep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s) :
    WP isa (tablePrep d) s fun t =>
      Changes base loopWork s t ∧ Inputs base P Q t ∧
      PointAt base t resultPt (pair P Q ((previous d)%4) ((previous d)/4)) ∧
      PointAt base t entry (if d%4=0 then Q else P) := by
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
  have code : tablePrep d = .block ((if previous d=0 then infinity else copyPt 4 resultPt (tablePt (previous d))) ++
      affineEntry (if d%4=0 then PX else GX) (if d%4=0 then PY else GY)) := by
    by_cases hz : d%4=0
    · simp only [tablePrep,previous,ite_eq_left hz]
    · simp only [tablePrep,previous,ite_eq_right hz]
  rw [code,WP.block_append_iff]
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
  exact ⟨W₂,I₂,R₂,E₂⟩
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
