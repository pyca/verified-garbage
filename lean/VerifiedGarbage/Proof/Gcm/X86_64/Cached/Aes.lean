module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Base

/-! # A GCM batch using cached AES round keys

`batchM_ok`: `StitchZH.batch j g ix` encrypts the sixteen data blocks at
`rdx + 64 j` into the output, over the data or, out of place (`ix`), at
`rdx + r8 + 64 j` (`StitchZ.AInvM`, `xorDataZM_ok`), as `Stitch.batchM_ok`
does with eight blocks; `batch_ok` is the in-place case. -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp cb dp dR pR bAddr blk ctb ciph sch sch_frame addr_eq in_sub)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (batch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

open VG.Proof.Gcm.X86_64.StitchZ (AInv AInvM AInv.toM aregs_ok)

theorem batchM_ok {ix st ld : Bool} {s₀ : State} (hp : Stitch.LPre ix s₀) (hst : st = (ix && !ld))
    (hld : ld = true → ix = true) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ nb s₀) {s : State} (hI : AInvM ix s₀ c s)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true)
    (hr8 : ix = true → s.gpr .r8 = if ld then dp s₀ - Stitch.op s₀ else Stitch.op s₀ - dp s₀)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (Stitch.wp ld s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batch j g st ld) s fun s' => AInvM ix s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batch_keeps j g hgh st ld) h)
      (fun t ⟨⟨ha, hq, hg, hl, hf⟩, hh⟩ => ⟨ha, hq, hg, hl, hf, hCache.keep hh (ha.keys hp)⟩)

  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hwd := hp.wrap_d
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
  have hw := hp.wrap_w
  have hg₂ : s₂.gpr = s.gpr := by rw [f₂.gpr, f₁.gpr]
  have hwr : (Stitch.wp ld s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64 := by
    cases ld
    · exact hwd
    · obtain rfl := hld rfl; exact hw
  have raddr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) =
      Stitch.wp ld s₀ + BitVec.ofNat 64 (16 * (c + i)) := fun i => addr_eq (by omega)
  have addr : ∀ i, Stitch.oA s ld + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i => by
    cases ld
    · exact raddr i
    · show s.gpr .rdx + s.gpr .r8 + _ = dp s₀ + _
      rw [hr8 (hld rfl)]
      exact StitchZTo.src_addr (raddr i)
  have oaddr : ∀ i, Stitch.oA s st + BitVec.ofNat 64 (64 * j + 16 * i) = Stitch.wAddr ix s₀ (c + i) := fun i => by
    subst hst
    cases ix <;> cases ld
    · exact raddr i
    · exact absurd (hld rfl) (by decide)
    · show s.gpr .rdx + s.gpr .r8 + _ = Stitch.op s₀ + _
      rw [hr8 rfl]
      exact StitchZTo.src_addr (raddr i)
    · exact raddr i
  have e64 : ∀ k, BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) = BitVec.ofNat 64 (64 * j + 16 * (4 * k)) :=
    fun k => by rw [BitVec.ofInt_natCast]; congr 1; omega
  have e16 : ∀ k l, 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) := fun k l => by omega
  have o₂ : Stitch.oA s₂ st = Stitch.oA s st := Stitch.oA_congr st hg₂
  have i₂ : Stitch.oA s₂ ld = Stitch.oA s ld := Stitch.oA_congr ld hg₂
  refine WP.mono (StitchZ.xorDataZM_ok st ld .xmm13 aregs j s₂ hnd h13
      (fun k hk => by
        rw [i₂, f₂.rd, f₁.rd, f₂.wr, f₁.wr, hI.rd, hI.wr, e64, addr]
        exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (fun k hk => by
        rw [o₂, f₂.wr, f₁.wr, hI.wr, e64, oaddr]
        exact in_sub hp.w_in (by simp [aregs] at hk; omega))
      (fun a b hab hb l hl => by
        rw [i₂, o₂, e16, show 64 * (j + a) = 64 * j + 16 * (4 * a) by omega, addr, oaddr]
        simp only [aregs, List.length_cons, List.length_nil] at hb
        cases ix
        · cases ld
          · exact Offset.disjoint _ (Or.inr (by omega)) (by omega) (by omega)
          · exact absurd (hld rfl) (by decide)
        · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right
            (Offset.sub_base _ (by omega)))
      (by simp only [aregs, List.length_cons, List.length_nil]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, i₂, o₂] at b₃
  rw [hm₂, o₂] at fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, oaddr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      blockAt s₃.mem (Stitch.wAddr ix s₀ (c + (4 * k + l))) =
        blk s₀ (c + (4 * k + l)) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [e16, oaddr, addr, hI.src _ (by simp [aregs] at h; omega) (by omega)] at this
  have fr' : Frame [⟨Stitch.wAddr ix s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  have gs : s₃.gpr = s.gpr := by rw [g₃, hg₂]
  have dsep : ∀ k < nb s₀, c + 16 ≤ k → ∀ r ∈ [(⟨Stitch.wAddr ix s₀ c, 256⟩ : Region)],
      Region.Disjoint ⟨bAddr s₀ k, 16⟩ r := fun k hk hck r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    cases ix
    · intro a h₁ h₂
      exact VG.Proof.Aes.X86_64.AesNi.run_sep hwd hk hc (by omega) h₁ h₂
    · exact ((hp.d_w rfl).sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [gs, hI.rdi],
    by rw [gs, hI.rsi], by rw [gs, hI.r10], ?_, ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    gs, kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2 rfl) l hl, hI.inc l hl]
  · refine hI.frame.trans (fr'.sub fun r hr => ⟨Stitch.wR ix s₀, List.mem_cons_self, fun a ha => ?_⟩)
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
      exact hI.out k hlo
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
      have hj : i / 4 < aregs.length := by simp [aregs]; omega
      rw [hb3 (i / 4) hj (i % 4) (by omega), ks (i / 4) hj (i % 4) (by omega),
        show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]
  · intro k hk hck
    rw [blockAt_frame fr' (dsep k hk hck)]
    exact hI.src k hk (by omega)

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
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' :=
  WP.mono (batchM_ok (ld := false) (Stitch.SPre.toM hp) rfl (fun h => absurd h (by decide)) g G hG Q hg hq hqx hc hI.toM
    hCache hgh (fun h => absurd h (by decide)) hrdx hQ)
    fun _ ⟨hA, h⟩ => ⟨hA.toAInv, h⟩

end VG.Proof.Gcm.X86_64.StitchZH
