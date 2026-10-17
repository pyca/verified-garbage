module

public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Ready
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DotSpec

/-! # Fused polynomial products preserve the KEM call invariant -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem fused_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : Dot.LoopData s (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Impl.MlKem.AArch64.Dot.dot off terms) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024] s.mem t.mem ∧
      PolyIs t.mem (sA L s₀ off) (Dot.polySum terms F G) ∧ t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  have hoff := ho.le
  refine WP.mono (Dot.dot_ok (by kom) terms hd) fun t ⟨kt,ft,pt⟩ => ?_
  rw [e28 hk] at ft pt
  exact ⟨hk.frame kt ft (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ho.safe hp),ft,pt,kt.get .x24 (by decide)⟩

theorem fused_einv {s₀ s : State} (hp : Pre P L s₀) {kE eo kC co : Nat}
    (A : EncArgs P L kE eo kC co) {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte} {i : Nat}
    (hi : i ≤ P.k) (h : EInv P L s₀ kC co mE mB v rv mv P.k i s)
    (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : Dot.LoopData s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Impl.MlKem.AArch64.Dot.dot (TP P) terms) s fun t =>
      EInv P L s₀ kC co mE mB v rv mv P.k i t ∧
      Frame [R (kA s₀) L.sc (TP P) 1024] s.mem t.mem ∧
      PolyIs t.mem (sA L s₀ (TP P)) (Dot.polySum terms F G) := by
  have hw := hp.wf
  exact WP.mono (fused_ok hp (po_TP hw) h.kb terms hd) fun t ⟨kt,ft,pt,xt⟩ =>
    ⟨h.frame hp kt xt ft (far_one hp A (Nat.le_refl _) hi (by lom) (by lom)),ft,pt⟩

end VG.Proof.MlKem.AArch64.Kem
