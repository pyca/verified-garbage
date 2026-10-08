import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Load
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH

/-! # A GCM batch using cached AES round keys -/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp cb dp dR pR bAddr blk ctb ciph sch sch_frame addr_eq in_sub)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (batch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok xorDataZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

open VG.Proof.Gcm.X86_64.StitchZ (AInv aregs_ok)

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInv s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => AInv s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batch j g) s fun s' => AInv s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batch_keeps j g hgh) h)
      (fun t ⟨⟨ha, hq, hg, hl, hf⟩, hh⟩ => ⟨ha, hq, hg, hl, hf, hCache.keep hh (ha.keys hp)⟩)

  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (WP.hkeep (by decide) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc)) fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys (hI.keys hp) f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  refine WP.mono (xorDataZ_ok .xmm13 .rdx aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, show BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) =
        BitVec.ofNat 64 (64 * j + 16 * (4 * k)) by rw [BitVec.ofInt_natCast]; congr 1; omega, addr]
      exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (bAddr s₀ (c + (4 * k + l))) =
        blockAt s.mem (bAddr s₀ (c + (4 * k + l))) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [show 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) by omega, addr] at this
  have fr' : Frame [⟨bAddr s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
    by rw [g₃, f₂.gpr, f₁.gpr, hI.rsi], by rw [g₃, f₂.gpr, f₁.gpr, hI.r10], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, f₁.gpr], kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 16) → blockAt s₃.mem (bAddr s₀ k) = blockAt s.mem (bAddr s₀ k) :=
      fun hn => blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 16 by omega, ite_true]
    · by_cases hhi : k < c + 16
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
        have hj : i / 4 < aregs.length := by simp [aregs]; omega
        rw [hb3 (i / 4) hj (i % 4) (by omega), hI.blocks _ hk, ks (i / 4) hj (i % 4) (by omega),
          show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Gcm.X86_64.StitchZH
