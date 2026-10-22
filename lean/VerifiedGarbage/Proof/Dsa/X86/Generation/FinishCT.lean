module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Correct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Two runs of one geometry's search and result leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- `fStatus` for the search's result. -/
def stOf : Option Spec.Dsa.Params → Nat
  | none => 2
  | some _ => 1

theorem SRes.status {E : Env} {g : Geo} {m : Mem} {R : Option Spec.Dsa.Params} (h : SRes E g m R) :
    m.readW (off E.base fStatus) 32 = BitVec.ofNat 32 (stOf R) := by
  rcases R with _ | a
  · exact h
  · exact h.1

/-- The pointers and the count of a copy or a clearing of `out`. -/
def outPins (E : Env) (src : Reg) (n : Nat) (r : Reg) : BitVec 32 :=
  if r = src then E.base.setWidth 32 + BitVec.ofNat 32 sPk
  else if r = .ebx ∨ r = .esi then E.out.setWidth 32
  else if r = .ecx then BitVec.ofNat 32 n
  else if r = .eax then 0
  else baseVal E r

theorem finish_ct {g : Geo} {E : Env} (v : E.Valid) :
    RelCT isa (Both fun (R : Option Spec.Dsa.Params) t => Base E t ∧ SRes E g t.mem R) g.finish
      fun _ _ => True := by
  have sz := v.size_ge
  have hb : ∀ (R : Option Spec.Dsa.Params) t, Base E t ∧ SRes E g t.mem R → Base E t := fun _ _ h => h.1
  unfold Geo.finish
  simp only [seqs]
  refine cmpF_ct (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) (by decide) stOf hb
    (fun R t h => h.2.status) (fun R => by rcases R with _ | _ <;> simp [stOf]) ?_ ?_
  · -- p||q||g out.
    refine RelCT.seq (both_post (Ψ := fun _ t => ∀ r ∈ [Reg.esp, .edi, .ebx, .esi, .ecx],
        t.gpr r = outPins E .esi (2 * g.pLen + g.qLen) r)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins (h.1.base hb))
        (tcheckE _ _ (.block ([.mov .ebx (.mem (sc 0))] ++ scr .esi 0 ++ [.mov .ecx (.imm 0)])) rfl
          (by decide +kernel) (by decide +kernel))) fun R t h => ?_)
      (both_agree _ _ (fun _ _ h => h) (tcheck _ _ (by decide +kernel)))
    have B := h.1.base hb
    refine ld_ok B.scr (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ _ _ _ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    have pins := base_pins B
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, B.outW]; rfl
    · rw [u₄.other _ (by decide), e₃, u₂.other _ (by decide), B.edi]; rfl
    · rw [u₄.gpr]; rfl
  · -- Zeros out.
    refine RelCT.seq (both_post (Ψ := fun _ t => ∀ r ∈ [Reg.esp, .edi, .esi, .ecx, .eax],
        t.gpr r = outPins E .edx (2 * g.pLen + g.qLen) r)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins (h.1.base hb))
        (tcheckE _ _ (.block [.mov .esi (.mem (sc 0)), .mov .ecx (.imm 0), .mov .eax (.imm 0)]) rfl
          (by decide +kernel) (by decide +kernel))) fun R t h => ?_)
      (both_agree _ _ (fun _ _ h => h) (tcheck _ _ (by decide +kernel)))
    have B := h.1.base hb
    refine ld_ok B.scr (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_
    have pins := base_pins B
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact pins _ (by simp)
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, B.outW]; rfl
    · rw [u₄.other _ (by decide), u₃.gpr]; rfl
    · rw [u₄.gpr]; rfl

theorem generate_ct {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen) :
    RelCT isa (Both fun (_ : Unit) => SIn E) g.generate fun _ _ => True := by
  unfold Geo.generate
  refine RelCT.seq (both_post (Ψ := fun _ t => Base E t ∧ SRes E g t.mem (outcome E g)) (search_ct G v hp hq)
    fun _ s ⟨B, hS, hL, hst, hU⟩ => WP.mono (search_ok G v hp hq B hS hL hst hU) fun t ⟨K, R⟩ => ⟨K.base, R⟩) ?_
  exact both_map (fun _ => outcome E g) (fun _ _ h => h) (finish_ct v)

end VG.Proof.Dsa.X86.Generation
