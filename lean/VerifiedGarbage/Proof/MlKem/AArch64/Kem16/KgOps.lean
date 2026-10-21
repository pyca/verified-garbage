module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgCommon
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.AddSubW
import VerifiedGarbage.Proof.MlKem.AArch64.Codec12W.Enc
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DotReady
import VerifiedGarbage.Proof.MlKem.AArch64.DotW

/-! # The building blocks of the 16-bit key generation

As `Kem16/Ops.lean`, in key generation's context (`KeyGen.KB`): the fused dot
product (`fusedW_tl`), the sum (`addW_read_okK`) and `ByteEncode₁₂`
(`enc12W_okK`) of polynomials stored with 16 bits. -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64.DotW (half_sub)
variable {P : KemLay}

theorem binvW_zero {w16 : Bool} {s₀ s : State} (h : AfterA P s₀ s) : BInvW w16 P s₀ 0 s :=
  ⟨h.kb, h.rho, h.sig, by rw [h.x24, ite_eq_left (show allOk P s₀ 0 from fun e he => absurd he (Nat.not_lt_zero e))],
    fun e he => absurd he (Nat.not_lt_zero e), fun e he => absurd he (Nat.not_lt_zero e)⟩

theorem fusedW_tl {s₀ s : State} (hp : Pre P s₀) {mB : Mem} {v : BitVec 64} {n i : Nat}
    (hi : i < P.k) (h : TLW P s₀ mB v n i s) (terms : List (Nat × Nat))
    {F G : (Nat × Nat) → Poly}
    (hd : DotW.LoopDataW s .x28 .x28 (s.gpr .x28 + BitVec.ofNat 64 (TP P)) (s.syms "VG_MLKEM_GAMMA") terms
      (Dot.polyValues F) (Dot.polyValues G) Dot.gammaValues) :
    WP isa (Kem16.dotAt (TP P) terms) s fun s' =>
      TLW P s₀ mB v n i s' ∧
      Frame [R (kA s₀) 3 (TP P) 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P)) (Dot.polySum terms F G) := by
  have hw := hp.wf
  refine WP.mono (DotW.dotW_ok (by decide) (by lom) terms hd) fun t ⟨hk,hf,hpoly⟩ => ?_
  rw [h.c.kb.x28] at hf hpoly
  have hf' : Frame [R (kA s₀) 3 (TP P) 1024] s.mem t.mem :=
    hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  have hkb : KB P s₀ t := h.c.kb.frame hk hf' (by decide) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact kb_disj hp (by decide) (by kl) (by kl) (by decide))
  exact ⟨h.frame hp hkb (hk.get .x24 (by decide)) hf' (apart_TP hp hi),hf',hpoly⟩

theorem addW_read_okK {s₀ : State} (hp : Pre P s₀) {f g : Nat} (hf : PolyOff P f) (hg : g + 1024 ≤ P.scl)
    (d : f + 1024 ≤ g ∨ g + 1024 ≤ f) {s : State} (hk : KB P s₀ s)
    (rf : ReducedW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (rg : ReducedW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 g)) :
    WP isa (Kem16.addWAt f g) s fun s' => KB P s₀ s' ∧ Frame [R (kA s₀) 3 f 1024] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (kA s₀ 3 + BitVec.ofNat 64 f)
        (add (polyAtW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 f)) (polyAtW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 g))) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨hf1, hf2⟩ := hf
  have ff : f + 1024 ≤ kL P 3 := by kl
  have fg : g + 1024 ≤ kL P 3 := by kl
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' (by decide) (by kl)
    fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = kA s₀ 3 + BitVec.ofNat 64 f := by rw [h₂.get .x0, e₁, hk.x28]
  have x1 : s₂.gpr .x1 = kA s₀ 3 + BitVec.ofNat 64 g := by rw [e₂, h₁.get .x28, hk.x28]
  have cw := cov_w hp kb₂ (b := 3) (by decide) ff
  have cr := cov_r hp kb₂ (b := 3) (by decide) fg
  refine WP.mono (AddSubW.addW_ok ⟨fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩) fun s₃ ⟨k₃,f₃,p₃⟩ => ?_
  · rw [x0]; exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x1]; exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · rw [x0, x1]
    exact ((hp.args.rdisj (by decide) (by decide) ff fg (by omega)).sub_left (half_sub _)).sub_right
      (half_sub _)
  · rw [x0, m₂]; exact rf
  · rw [x1, m₂]; exact rg
  rw [x0, x1, m₂] at p₃
  rw [x0] at f₃
  have f₃' : Frame [R (kA s₀) 3 f 1024] s₂.mem s₃.mem :=
    f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact half_sub _⟩
  refine ⟨kb₂.frame k₃ f₃' (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact kb_disj hp (by decide) ff (by kl) (by decide),
    by rw [← m₂]; exact f₃', p₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

theorem enc12W_okK {s₀ : State} (hp : Pre P s₀) {off b o : Nat} (ho : PolyOff P off) (hb : b = 1 ∨ b = 2)
    (fo : o + 384 ≤ kL P b) {s : State} (hk : KB P s₀ s) {F : Poly}
    (hr : PolyIsW 16 s.mem (kA s₀ 3 + BitVec.ofNat 64 off) F) :
    WP isa (Kem16.enc12WAt off (breg b) o) s fun s' => KB P s₀ s' ∧ Frame [R (kA s₀) b o 384] s.mem s'.mem ∧
      bytesAt s'.mem (kA s₀ b + BitVec.ofNat 64 o) 384 = encode12 F ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨ho1, ho2⟩ := ho
  have hb4 : b < 4 := by omega
  have fo3 : off + 1024 ≤ kL P 3 := by kl
  have hol : o < 65536 := by have := kL_le hp.wf b; omega
  have hx : Reg.x1 ≠ breg b := by rcases hb with rfl | rfl <;> decide
  have hx0 : breg b ≠ Reg.x0 := by rcases hb with rfl | rfl <;> decide
  refine WP.seq (wp_ptrTo (by decide) (by kl) fun s₁ h₁ e₁ => wp_ptrTo' hx hol fun s₂ h₂ e₂ => ?_)
  have kb₂ := hk.block (h₁.trans h₂).keep (by rw [h₂.mem, h₁.mem]) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have x0 : s₂.gpr .x0 = kA s₀ 3 + BitVec.ofNat 64 off := by rw [h₂.get .x0, e₁, hk.x28]
  have x1 : s₂.gpr .x1 = kA s₀ b + BitVec.ofNat 64 o := by
    rw [e₂, h₁.get (breg b) (by simpa using hx0), hk.breg hb4]
  have cr := cov_r hp kb₂ (b := 3) (by decide) fo3
  have cw := cov_w hp kb₂ ⟨by omega, hb4⟩ fo
  refine WP.mono (Codec12W.encW_ok (P := F) x0 x1 ⟨by rw [m₂]; exact hr, fun j hj => ?_, fun j n hj => ?_, ?_⟩)
    fun s₃ ⟨k₃,f₃,b₃⟩ => ?_
  · exact cr _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · exact cw _ _ (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  · exact (hp.args.rdisj (b₁ := 3) (o₁ := off) (l₁ := 1024) (by decide) hb4 fo3 fo (by omega)).sub_left
      (half_sub _)
  refine ⟨kb₂.frame k₃ f₃ (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact kb_disj hp hb4 fo (.inl (by omega)) (by omega),
    by rw [← m₂]; exact f₃, b₃, by rw [k₃.get .x24 (by decide), h₂.get .x24, h₁.get .x24]⟩

end VG.Proof.MlKem.AArch64.KeyGen
