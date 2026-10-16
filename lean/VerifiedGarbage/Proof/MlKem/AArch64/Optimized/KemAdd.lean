module

public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Accumulation from retained error polynomials in scratch -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem acc_read_ok {s₀ : State} (hp : Pre P L s₀) {op : Poly → Poly → Poly} {c : Prog isa} {name : String}
    (hc : ∀ {s : State} {f g : Addr}, s.gpr .x0 = f → s.gpr .x1 = g → Region.Disjoint ⟨f, 1024⟩ ⟨g, 1024⟩ →
      Reduced s.mem f → Reduced s.mem g → Covers [⟨g, 1024⟩, ⟨f, 1024⟩] (s.rd ++ s.wr) →
      Covers [⟨f, 1024⟩] s.wr → ∀ {Q : State → Prop},
      (∀ s', Kept [⟨f, 1024⟩] s s' → PolyIs s'.mem f (op (polyAt s.mem f) (polyAt s.mem g)) → Q s') →
      WP isa (.call name c) s Q)
    {f g : Nat} (hf : PO P f) (hg : g+1024 ≤ P.scl) (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (.seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) (.call name c)) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ f) (op (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg : g+1024 ≤ L.len L.sc := by rw [hp.scl]; exact hg
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  refine hc (f := sA L s₀ f) (g := sA L s₀ g) (by rw [h₂.get .x0, e₁, e28 hk]) (by rw [e₂, h₁.get .x28, e28 hk])
    (hp.args.rdisj hp.scb hp.scb (hp.fs ff) fg (.inl rfl) (.inr d)) (by rw [m₂]; exact rf) (by rw [m₂]; exact rg)
    (covers_cons (cov_r hp kb₂ hp.scb fg) (cov_sr hp kb₂ ff)) (cov_s hp kb₂ ff) fun s₃ k₃ p₃ => ?_
  refine ⟨kb₂.call k₃ fun r hr => by rw [List.mem_singleton.mp hr]; exact hf.safe hp,
    by rw [← m₂]; exact k₃.frame, by rw [← m₂]; exact p₃,
    by rw [k₃.cs _ (by decide) (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem add_read_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : g+1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : Reduced s.mem (sA L s₀ f)) (rg : Reduced s.mem (sA L s₀ g)) :
    WP isa (addAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ f) (add (polyAt s.mem (sA L s₀ f)) (polyAt s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 :=
  acc_read_ok hp (fun h0 h1 hd rf rg hc hw => add_call h0 h1 hd rf rg hc hw) hf hg d hk rf rg

end VG.Proof.MlKem.AArch64.Kem
