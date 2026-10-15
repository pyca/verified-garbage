module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgC
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Add retained error polynomials from the tail of scratch -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

theorem add_read_ok {s₀ : State} (hp : Pre P s₀) {f g : Nat} (hf : PolyOff P f) (hg : g + 1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P s₀ s)
    (rf : Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (rg : Reduced s.mem (kA s₀ 3 + BitVec.ofNat 64 g)) :
    WP isa (addAt f g) s fun s' => KB P s₀ s' ∧ Frame [R (kA s₀) 3 f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 f)
        (add (polyAt s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (polyAt s.mem (kA s₀ 3 + BitVec.ofNat 64 g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨hf1, hf2⟩ := hf
  have ff : f + 1024 ≤ kL P 3 := by kl
  have fg : g + 1024 ≤ kL P 3 := by kl
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kl)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine add_call (f := kA s₀ 3 + BitVec.ofNat 64 f) (g := kA s₀ 3 + BitVec.ofNat 64 g)
    (by rw [h₂.get .x0, e₁, hk.x28]) (by rw [e₂, h₁.get .x28, hk.x28])
    (hp.args.rdisj (by decide) (by decide) ff fg (by omega)) (by rw [m₂]; exact rf) (by rw [m₂]; exact rg)
    (covers_cons (cov_r hp kb₂ (b := 3) (by decide) fg) (cov_r hp kb₂ (b := 3) (by decide) ff))
    (cov_w hp kb₂ (b := 3) (by decide) ff) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact kb_disj hp (by decide) ff (by kl) (by decide),
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.KeyGen
