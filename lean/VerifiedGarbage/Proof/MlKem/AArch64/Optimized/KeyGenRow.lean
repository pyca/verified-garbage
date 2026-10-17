module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenDot
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenAdd
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized

/-! # One fused key-generation row with a precomputed error polynomial -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay}

def rowTerms (P : KemLay) (i : Nat) : List (Nat × Nat) :=
 (List.range P.k).map fun j => (aOff P i j,sOff P j)

def rowWrites (P : KemLay) (s₀ : State) (i : Nat) : List Region :=
 [R (kA s₀) 3 (TP P) 1024,R (kA s₀) 1 (384*i) 384,R (kA s₀) 2 (384*P.k+384*i) 384]

theorem fused_row {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : TL P s₀ mB v i s)
    {F G : (Nat × Nat) → Poly}
    (hd : Dot.LoopData s (s.gpr .x28+BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA")
      (rowTerms P i) (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues)
    (hsum : Dot.polySum (rowTerms P i) F G = KPke.dotK (aM P s₀ mB i) (KPke.kgS P.params (dB s₀)) P.k)
    (he : PolyIs s.mem (kA s₀ 3+BitVec.ofNat 64 (noiseOff P i)) (KPke.kgE P.params (dB s₀) i)) :
    WP isa (Impl.MlKem.AArch64.Optimized.kgRow P i) s fun t =>
      TL P s₀ mB v (i+1) t ∧ Frame (rowWrites P s₀ i) s.mem t.mem := by
  have hw := hp.wf
  have eg := Noise.noise_fits hr hi
  have ep := Noise.noise_past_kg hr i
  change WP isa (seqs [_,_,_,_]) s _
  refine WP.seq (WP.mono (fused_tl hp hi h (rowTerms P i) hd) fun s₂ ⟨tl₂,f₂,t₂⟩ => ?_)
  rw [hsum] at t₂
  have e₂ := polyIs_frame f₂ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) eg (by kl) (by lom)) he
  refine WP.seq (WP.mono (add_read_ok hp (f := TP P) (g := noiseOff P i) (po_TP hw) eg
    (.inl (by lom)) tl₂.c.kb t₂.1 e₂.1) fun s₇ ⟨kb₇,f₇,t₇,x₇⟩ => ?_)
  have tl₇ := tl₂.frame hp kb₇ x₇ f₇ (apart_TP hp hi)
  rw [t₂.2,e₂.2] at t₇
  have tv : PolyIs s₇.mem (kA s₀ 3+BitVec.ofNat 64 (TP P)) (tV P s₀ mB i) := t₇
  refine WP.seq (WP.mono (enc_ok hp (off := TP P) (b := 1) (o := 384*i) (po_TP hw) (.inl rfl)
    (by kl) kb₇ tv.1) fun s₈ ⟨kb₈,f₈,b₈,x₈⟩ => ?_)
  have tl₈ := tl₇.frame hp kb₈ x₈ f₈ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_ek hp hi
  have tv₈ := polyIs_frame f₈ (fun r hr' => by
    rw [List.mem_singleton.mp hr']
    exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) tv
  refine WP.mono (enc_ok hp (off := TP P) (b := 2) (o := 384*P.k+384*i) (po_TP hw) (.inr rfl)
    (by kl) kb₈ tv₈.1) fun s₉ ⟨kb₉,f₉,b₉,x₉⟩ => ?_
  have tl₉ := tl₈.frame hp kb₉ x₉ f₉ fun r hr' => by
    rw [List.mem_singleton.mp hr']; exact apart_dk hp hi
  refine ⟨⟨tl₉.c,tl₉.sp,tl₉.dk,fun i' hi' => ?_⟩,?_⟩
  · rcases (by omega : i'<i ∨ i'=i) with hi' | rfl
    · exact tl₉.ek i' hi'
    · refine ⟨?_,by rw [b₉,tv₈.2]⟩
      rw [bytesAt_frame f₉ (fun r hr' => by
        rw [List.mem_singleton.mp hr']
        exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))) (by decide),b₈,tv.2]
  · exact (((f₂.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites])).trans
      (f₇.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₈.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))).trans
      (f₉.mono (by intro r hr'; rw [List.mem_singleton.mp hr']; simp [rowWrites]))

end VG.Proof.MlKem.AArch64.KeyGen
