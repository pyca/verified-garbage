import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Load
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo

/-! # A cached-key GCM batch from one buffer to another -/

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

theorem batchTo_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (batchTo j g).all Instr.keepsH = true := by
  simp [batchTo, Code.all, StitchZH.aes_keeps _ g hg, Impl.Aes.X86_64.VaesZ.ctrsZ,
    Impl.Gcm.X86_64.StitchZTo.xorDataZTo, aregs, Instr.keepsH]

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvTo s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (op s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batchTo_keeps j g hgh) h)
      (fun t ⟨⟨ha, hq, hg, hl, hf⟩, hh⟩ => ⟨ha, hq, hg, hl, hf, hCache.keep hh (ha.keys hp)⟩)

  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hw := hp.wrap_o
  have hws := hp.wrap_s
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
    (by rw [f₁.gpr, hI.rsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) = oAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  have saddr : ∀ i, s.gpr .rdx + s.gpr .r8 + BitVec.ofNat 64 (64 * j + 16 * i) = sAddr s₀ (c + i) := fun i => by
    rw [hI.r8]; exact src_addr (addr i)
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega
  refine WP.mono (xorDataZTo_ok .xmm13 .rdx .r8 aregs j s₂ hnd h13 (sR s₀) (oR s₀) hp.s_o
      (fun k hk => by
        rw [hg₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e64, saddr]
        exact in_sub hp.s_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [hg₂, f₂.wr, f₁.wr, hI.wr, e64, addr]
        exact in_sub hp.o_in (by simp [aregs] at hk; omega))
      (fun k hk l hl => by
        rw [hg₂, e16, saddr]
        exact Offset.sub_base _ (by simp [aregs] at hk; omega))
      (by
        rw [hg₂, show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero]
        exact Offset.sub_base _ (by simp [aregs]; omega))
      (by rw [hg₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hg₂] at b₃ fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (oAddr s₀ (c + (4 * k + l))) =
        pblk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, addr, saddr, hI.src hp (by simp [aregs] at h; omega)] at this
  have fr' : Frame [⟨oAddr s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], by rw [gs, hI.r8], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the output.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨oR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  · intro k hk
    by_cases hlo : k < c
    · rw [blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw (by omega) hc (by omega) h₁ h₂]
      exact hI.blocks k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 4) hj (i % 4) (by omega), ks (i / 4) hj (i % 4) (by omega),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]

end VG.Proof.Gcm.X86_64.StitchZHTo
