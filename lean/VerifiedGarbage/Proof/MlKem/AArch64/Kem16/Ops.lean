module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemReadonlyTransform
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
public import VerifiedGarbage.Proof.MlKem.AArch64.AddSubW
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec12W.Dec
public import VerifiedGarbage.Proof.MlKem.AArch64.Widen16
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc

/-! # The building blocks of the 16-bit `encaps` and `decaps`

As `KemOps.lean`, for the blocks of `Impl.MlKem.AArch64.Kem16` on polynomials
stored with 16 bits in the first half of a buffer of `scratch`: the fused dot
product (`fusedW_ok`), the inverse transform (`invW_ok`), the sum (`addW_read_ok`),
the widening (`widenW_ok`) and `ByteDecode₁₂` (`dec12W_ok`). Each keeps `KB` and
`x24` and changes only its whole 1024-byte buffers. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64.DotW (half_sub)

variable {P : KemLay} {L : Layout}

theorem fusedW_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28+BitVec.ofNat 64 off) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Kem16.dotAt off terms) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024] s.mem t.mem ∧
      PolyIsW 16 t.mem (sA L s₀ off) (Dot.polySum terms F G) ∧ t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  have hoff := ho.le
  refine WP.mono (DotW.dotW_ok (by decide) (by kom) terms hd) fun t ⟨kt,ft,pt⟩ => ?_
  rw [e28 hk] at ft pt
  have ft' : Frame [R (kA s₀) L.sc off 1024] s.mem t.mem :=
    ft.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  exact ⟨hk.frame kt ft' (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ho.safe hp),ft',pt,kt.get .x24 (by decide)⟩

theorem invW_ok {s₀ s : State} (hp : Pre P L s₀) {off : Nat} (ho : PO P off)
    (hk : KB P L s₀ s) (hr : ReducedW 16 s.mem (sA L s₀ off)) (ht : Optimized.TransformTables s) :
    WP isa (Ntt16.Readonly.nttInvAtWithW off NS) s fun t =>
      KB P L s₀ t ∧ Frame [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s.mem t.mem ∧
      PolyIsW 16 t.mem (sA L s₀ off) (nttInv (polyAtW 16 s.mem (sA L s₀ off))) ∧
      t.gpr .x24 = s.gpr .x24 := by
  have hw := hp.wf
  have hc := covers_cons (cov_s hp hk ho.le) (cov_s hp hk (o:=NS) (l:=1024) (by kom))
  have hc' := covers_cons (cov_s hp hk (o:=off) (l:=512) (by have := ho.le; omega))
    (cov_s hp hk (o:=NS) (l:=512) (by kom))
  refine WP.mono (Ntt16.W.nttInvAtWithW_ok (by obtain ⟨_,hh⟩:=ho; kom) (by decide)
    (by rw [e28 hk]) (by rw [e28 hk]) (((ho.ns hp).sub_left (half_sub _)).sub_right (half_sub _))
    ⟨hr,rfl⟩ hc' (ht.inverse.ready hc)) fun t ⟨kt,pt⟩ => ?_
  have kt' : Kept [R (kA s₀) L.sc off 1024,R (kA s₀) L.sc NS 1024] s t := kt.sub fun r hh => by
    rcases mem2' hh with rfl|rfl
    · exact ⟨_, List.mem_cons_self .., half_sub _⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), half_sub _⟩
  refine ⟨hk.call kt' ?_,kt'.frame,pt,kt.cs _ (by decide) (by decide)⟩
  intro r hh
  rcases mem2' hh with rfl|rfl
  · exact ho.safe hp
  · exact safe_scr hp (by kom)

theorem addW_read_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : g+1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s)
    (rf : ReducedW 16 s.mem (sA L s₀ f)) (rg : ReducedW 16 s.mem (sA L s₀ g)) :
    WP isa (Kem16.addWAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc f 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (sA L s₀ f) (add (polyAtW 16 s.mem (sA L s₀ f)) (polyAtW 16 s.mem (sA L s₀ g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg : g+1024 ≤ L.len L.sc := by rw [hp.scl]; exact hg
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = sA L s₀ f := by rw [h₂.get .x0, e₁, e28 hk]
  have x1 : s₂.gpr .x1 = sA L s₀ g := by rw [e₂, h₁.get .x28, e28 hk]
  have cw := cov_s hp kb₂ ff
  have cr := cov_r hp kb₂ hp.scb fg
  refine WP.mono (AddSubW.addW_ok ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x1]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x0, x1]
    exact ((hp.args.rdisj hp.scb hp.scb (hp.fs ff) fg (.inl rfl) (.inr d)).sub_left (half_sub _)).sub_right
      (half_sub _)
  · rw [x0, m₂]; exact rf
  · rw [x1, m₂]; exact rg
  rw [x0, x1, m₂] at p₃
  rw [x0] at f₃
  have f₃' : Frame [R (kA s₀) L.sc f 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact hf.safe hp,
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem widenW_ok {s₀ : State} (hp : Pre P L s₀) {f g : Nat} (hf : PO P f) (hg : PO P g)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P L s₀ s) {F : Poly}
    (pf : PolyIsW 16 s.mem (sA L s₀ f) F) :
    WP isa (Kem16.widenAt f g) s fun s' => KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc g 1024] s.mem s'.mem ∧
      PolyIs s'.mem (sA L s₀ g) F ∧ s'.gpr .x24 = s.gpr .x24 := by
  have ff := hf.le
  have fg := hg.le
  refine WP.seq (wp_ptrTo (by decide) (by kom) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kom)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = sA L s₀ f := by rw [h₂.get .x0, e₁, e28 hk]
  have x1 : s₂.gpr .x1 = sA L s₀ g := by rw [e₂, h₁.get .x28, e28 hk]
  have cw := cov_s hp kb₂ fg
  have cr := cov_sr hp kb₂ ff
  refine WP.mono (Widen16.widen_ok (F := F) ⟨?_, fun j hj => ?_, fun j hj => ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0, m₂]; exact pf
  · rw [x0]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x1]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x0, x1]; exact (papart hp hf hg d).sub_left (half_sub _)
  rw [x1] at f₃ p₃
  refine ⟨kb₂.frame k₃ f₃ (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact hg.safe hp,
    by rw [← m₂]; exact f₃, p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem dec12W_ok {s₀ : State} (hp : Pre P L s₀) {k o off : Nat} (hk4 : k < 4)
    (f : o + 384 ≤ L.len (L.slot k)) (ho : PO P off) (hs : L.slot k ≠ L.sc ∨ o + 384 ≤ off ∨ off + 1024 ≤ o)
    {s : State} (hk : KB P L s₀ s) :
    WP isa (Kem16.dec12WAt (slotReg k) o off) s fun s' =>
      KB P L s₀ s' ∧ Frame [R (kA s₀) L.sc off 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (sA L s₀ off) (decode12 (bytesAt s.mem (kA s₀ (L.slot k) + BitVec.ofNat 64 o) 384)) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hb := hp.lt hk4
  refine WP.seq (wp_ptrTo (slot_ne hk4 .x0 (by decide)) (slot_off hp hk4 f) fun s₁ h₁ e₁ =>
    wp_ptrTo' (by decide) (by obtain ⟨-, h⟩ := ho; kom) fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = kA s₀ (L.slot k) + BitVec.ofNat 64 o := by rw [h₂.get .x0, e₁, hk.ptr k hk4]
  have x1 : s₂.gpr .x1 = sA L s₀ off := by rw [e₂, h₁.get .x28, e28 hk]
  have cw := cov_s hp kb₂ fo
  have cr := cov_r hp kb₂ hb f
  refine WP.mono (Codec12W.decW_ok ⟨fun j n hj => ?_, fun j hj => ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x1]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x0, x1]
    exact (hp.args.rdisj hb hp.scb f (hp.fs fo) (.inr (.inr hp.scw)) hs).sub_right (half_sub _)
  rw [x1] at f₃ p₃
  rw [Decode12.B, Decode12.bP, x0, m₂] at p₃
  have f₃' : Frame [R (kA s₀) L.sc off 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp,
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.Kem
