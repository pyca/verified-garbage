module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgT
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Core
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec

/-! # Fused key-generation rows preserve the existing phase invariant -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

theorem fused_tl {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {i : Nat}
    (hi : i < P.k) (h : TL P s₀ mB v i s) (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Poly}
    (hd : Dot.LoopData s (s.gpr .x28 + BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Impl.MlKem.AArch64.Dot.dot (TP P) terms) s fun s' =>
      TL P s₀ mB v i s' ∧
      Frame [R (kA s₀) 3 (TP P) 1024] s.mem s'.mem ∧
      PolyIs s'.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) (Dot.polySum terms F G) := by
  have hw := hp.wf
  refine WP.mono (Dot.dot_ok (by lom) terms hd) fun t ⟨hk,hf,hpoly⟩ => ?_
  rw [h.c.kb.x28] at hf hpoly
  have hkb : KB P s₀ t := h.c.kb.frame hk hf (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (by decide) (by kl) (by kl) (by decide))
  exact ⟨h.frame hp hkb (hk.get .x24 (by decide)) hf (apart_TP hp hi),hf,hpoly⟩

end VG.Proof.MlKem.AArch64.KeyGen
