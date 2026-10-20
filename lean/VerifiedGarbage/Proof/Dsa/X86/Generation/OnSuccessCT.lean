module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess

/-! # A continuation branches only on the public phase status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem onSuccess_ct {α : Type} {Φ : α → State → Prop} {next : Prog isa}
    (base : α → Addr) (status : α → BitVec 32)
    (view : ∀ p s, Φ p s → SearchFrame s (base p) ∧ s.mem.readW (off (base p) 76) 32 = status p)
    (stable : ∀ p s t, Φ p s → t.mem = s.mem → Keeps [.eax] s t → Φ p t)
    (nextCT : RelCT isa (Two fun p s => Φ p s ∧ status p = 1) next (fun _ _ => True)) :
    RelCT isa (Two Φ) (onSuccess next) (fun _ _ => True) := by
  unfold onSuccess
  refine RelCT.seq (two_piece (Ψ := fun p s => Φ p s ∧ s.zf = some (decide (status p = 1))) [.esp] ?_
    (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq ((view p s hs).1.esp_toNat.trans (view p t ht).1.esp_toNat.symm)
  · intro p s R
    obtain ⟨frame, value⟩ := view p s R
    refine WP.mono (frameSuccess_ok frame (observedWords_rep (base p) s)) fun t ⟨zf, mem, K⟩ => ?_
    exact ⟨stable p s t R mem K, by rw [zf]; change some (decide (s.mem.readW (off (base p) 76) 32 = 1)) = _; rw [value]⟩
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · refine nextCT.mono (fun _ _ => two_mono (fun p s h => ⟨h.1.1, ?_⟩)) (fun _ _ h => h)
      have z : s.zf = some true := h.2
      rw [h.1.2, Option.some.injEq, decide_eq_true_eq] at z
      exact z
    · exact RelCT.nil (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
