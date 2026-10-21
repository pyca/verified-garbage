module

public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Keep
public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZHTo
public import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # A cached-key GCM batch from one buffer to another -/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre SPreTo CtxMode sp op sR oR nb nr kp cp yp pp cb ciph sch dp dR pR
  cR yR bAddr addr_eq in_sub sch_frame)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZHTo (batchTo)
open VG.Proof.Gcm.X86_64.StitchZTo hiding batchTo_ok
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

theorem batchTo_keeps (j : Nat) (g : Nat → List Instr)
    (hg : ∀ j, (g j).all Instr.keepsH = true) : (batchTo j g).all Instr.keepsH = true := by
  simp only [batchTo, Code.all, StitchZH.aes_keeps _ g hg, StitchZH.ctrsM_keeps, Bool.true_and]
  simp [Impl.Gcm.X86_64.StitchZTo.xorDataZTo, aregs, Instr.keepsH]

theorem batchTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (hq1 : ∀ s s', Q 1 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [Slot.slotR (pp s₀)] s.mem s'.mem → Q 1 s')
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
      Frame [⟨oAddr s₀ c, 256⟩, Slot.slotR (pp s₀)] s.mem s'.mem ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  suffices h : WP isa (batchTo j g) s fun s' => AInvTo s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨oAddr s₀ c, 256⟩, Slot.slotR (pp s₀)] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (batchTo_keeps j g hgh) h)
      (fun t ⟨⟨ha, hq, hg, hl, hf⟩, hh⟩ => ⟨ha, hq, hg, hl, hf, hCache.keep hh (ha.keys hp)⟩)
  obtain ⟨hnd, h13, _⟩ := aregs_ok
  refine WP.seq (WP.mono (WP.hkeep StitchZH.ctrsM_keeps (ctrsTo_ok hp (Q 1) hq1 hI hQ))
    fun s₁ ⟨⟨e₁, c₁, m₁, g₁, rd₁, wr₁, z₁, _, hK₁, hQ₁⟩, hh₁⟩ => ?_)
  have hCache₁ := hCache.keep hh₁ hK₁
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => (hG r h).1) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hCache₁ hQ₁
    (by rw [g₁, hI.rsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  have k₂ : ∀ r, r ≠ .xmm13 → r ∉ aregs → r ∉ G → ∀ l < 4, s₂.zlane r l = s.zlane r l :=
    fun r h13' hr hg' l hl => by rw [f₂.zlane r (by simp [h13', hr, hg']) l hl, z₁ r hr l hl]
  refine WP.mono (xorTo_ok hp (Q 10) hqx hc hI hrdx (by rw [f₂.mem]; exact c₁) (by rw [f₂.mem]; exact m₁)
    (by rw [f₂.gpr, g₁]) (by rw [f₂.rd, rd₁]) (by rw [f₂.wr, wr₁])
    (fun k h l hl => (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm)
    (fun l hl => by rw [k₂ _ (by decide) (by decide) (fun h => (hG _ h).2.2.1 rfl) l hl, hI.msk l hl]) hQ₂)
    fun s₃ ⟨hA, hQ₃, g₃, x₃, fr₃⟩ =>
      ⟨hA, hQ₃, g₃, fun r h13' _ hr hg' l hl => by rw [x₃ r h13' hr l hl, k₂ r h13' hr hg' l hl], fr₃⟩

end VG.Proof.Gcm.X86_64.StitchZHTo
