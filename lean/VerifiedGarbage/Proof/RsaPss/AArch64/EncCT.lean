module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCTEnc
import VerifiedGarbage.Proof.RsaPss.AArch64.EncTop
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncCTEnc
meta import VerifiedGarbage.Proof.RsaPss.AArch64.EncTop
meta import VerifiedGarbage.Proof.RsaPss.AArch64.CtHashCT
meta import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
meta import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp

/-!
# EMSA-PSS's encoding on AArch64: constant time

`code_ct`: two runs of `encode` from entry states with the same public data
leak the same trace. The prologue and the checks of the lengths branch on
the lengths only (the taint analysis, and correctness for the branches); the
encoding is `encEnc_ct`; the copy to `em` loads `em` from its slot, public by
correctness (`copyArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (wp_nil wp_movz eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_map two_ite two_alloc)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off two_taintE two_step pins_nil zH PssChecks fitH_ok saltFits_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- `a; (b; c)` as `(a; b); c`. -/
theorem relct_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

/-- 0 returned: the stack pointer is kept. -/
theorem ret0_ct {Φ : State → State → Prop} (hΦ : ∀ a u, Φ a u → u.sp = fb a) :
    RelCT isa (Two Φ) ret0 (Two fun a t => t.sp = fb a) :=
  two_post (two_taint [] (pins_nil fun a s₁ s₂ h₁ h₂ => by rw [hΦ a s₁ h₁, hΦ a s₂ h₂]) (by taint_decide))
    fun a u h => by
      unfold ret0
      exact wp_movz fun t o _ => wp_nil (by rw [o.sp, hΦ a u h])

/-- After the checks of the lengths. -/
structure AtM (D : Nat) (s w : State) : Prop where
  e : AtE s w
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (D + 2))
  fit : D + (s.gpr .x4).toNat + 2 ≤ (s.gpr .x1).toNat

/-- The encoding's start. -/
theorem sr_of {D : Nat} {a w : State} (h : ∃ s, E D a s ∧ AtM D s w) : SR D (sregs0 D) sslots a w := by
  obtain ⟨s, e, hm⟩ := h
  have hp := e.1
  have hk1 := hp.k1; have hk2 := hp.k2
  have hf := hm.fit
  have L := lay_of hp hm.e.sp hm.e.x20 hm.e.wr
  rw [e.fb, show s.gpr .x6 = scr a from e.scr] at L
  have h1 := e.gpr (r := .x1) (by decide)
  have h4 := e.gpr (r := .x4) (by decide)
  refine ⟨⟨s, e, hm.e.rd, hm.e.wr⟩, L, fun q hq => ?_, fun q hq => ?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [sregs0, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [hm.e.x19]; exact congrArg (off · oSt) e.scr
    · rw [hm.e.x21]; exact congrArg (off · oDig) e.scr
    · rw [hm.e.x23, h1]
    · rw [hm.x9, h1]; rfl
  · simp only [sslots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [← e.fb]; exact (hm.e.fr.rs (.x2, sDig) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact (hm.e.fr.rs (.x3, sSalt) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact (hm.e.fr.rs (.x4, sSaltLen) (by simp [encSlots])).trans (e.gpr (by decide))
    · rw [← e.fb]; exact hm.e.lo
  · show 1 ≤ (a.gpr .x1).toNat; rw [← h1]; exact hk1
  · show (a.gpr .x1).toNat ≤ 1024; rw [← h1]; exact hk2
  · show D + (a.gpr .x4).toNat + 2 ≤ (a.gpr .x1).toNat - 0
    rw [← h1, ← h4]; omega

section
variable {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
  (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (hc : PssChecks H.P H.D)

include hH hGh hGl hG hc in
/-- After the checks: the encoding, its copy and 1. -/
theorem main_ct : RelCT isa (Two fun a w => ∃ s, E H.D a s ∧ AtM H.D s w) (encMain H) fun _ _ => True := by
  unfold encMain seqs seqs
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E H.D a s ∧ AtCopy s (encF G H.D s) t)
    (two_map (fun a => a) (fun a w h => sr_of h) (encEnc_ct hH hGh hGl hG hc))
    fun a w ⟨s, e, hm⟩ => WP.mono (enc_ok hH hGh hGl hG e.1 hm.e hm.x9 hm.fit) fun t ht => ⟨s, e, ht⟩) ?_
  unfold copyOut
  refine relct_assoc' (two_step (Ψ := fun a u => u.sp = fb a ∧ u.gpr .x11 = off (scr a) oEm ∧
      u.gpr .x14 = a.gpr .x0 ∧ u.gpr .x12 = a.gpr .x1)
    (two_taint [] (pins_nil fun a s₁ s₂ ⟨_, e₁, h₁⟩ ⟨_, e₂, h₂⟩ => by rw [h₁.sp, h₂.sp, e₁.fb, e₂.fb])
      (by taint_decide))
    (fun a t ⟨s, e, ht⟩ => WP.mono (copyArgs_ok e.1 ht) fun u ⟨O, h11, h14, h12⟩ =>
      ⟨by rw [O.sp, ht.sp, e.fb], by rw [h11, ← e.scr], by rw [h14, e.gpr (by decide)],
        by rw [h12, e.gpr (by decide)]⟩)
    (two_taint [.x11, .x14, .x12] (fun a s₁ s₂ h₁ h₂ => ⟨by rw [h₁.1, h₂.1], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2, h₂.2.2.2]⟩) (by taint_decide)))

include hH hGh hGl hG hc in
theorem code_ct : RelCT isa (Two (E H.D)) (encode H) fun _ _ => True := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  unfold encode
  refine two_alloc (R := fun _ _ => True) ?_
  unfold encBody seqs seqs seqs
  refine RelCT.seq (two_post (Ψ := fun a u => ∃ s, E H.D a s ∧ AtE s u ∧
      u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ (u.gpr .x10 != 0) = decide ((s.gpr .x1).toNat < H.D + 2))
    (two_taintE [] (fun _ _ _ ⟨s₁, h₁, e₁⟩ ⟨s₂, h₂, e₂⟩ => ⟨by rw [e₁, e₂]; simp only [allocated, h₁.2.sp, h₂.2.sp],
        fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block (encPrologue ++ fitH zH))) rfl (by taint_decide))
    fun a u ⟨s, h, hu⟩ => ?_) ?_
  · subst hu
    have hk2 := h.1.k2
    rw [WP.block_append_iff]
    exact WP.mono (prologue_ok h.1 (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
      (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun t ht =>
      WP.mono (fitH_ok H hD (k := (s.gpr .x1).toNat) (by rw [ht.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq])
        (by omega)) fun t' ⟨O, x9, x10⟩ => ⟨s, h, ht.only O, x9, x10⟩
  refine RelCT.seq ?_ (two_taint (Φ := fun a t => t.sp = fb a) [] (fun a t₁ t₂ h₁ h₂ =>
    ⟨by rw [h₁, h₂], fun _ h => absurd h List.not_mem_nil⟩) (by taint_decide))
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, x₁⟩ ⟨s₂, h₂, _, _, x₂⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x1) (by decide), h₂.gpr (r := .x1) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.sp, h.fb]) ?_
  refine RelCT.seq (two_post (Ψ := fun a w => ∃ s, E H.D a s ∧ AtE s w ∧
      w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)) ∧
      (w.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - (H.D + 2) < (s.gpr .x4).toNat) ∧
      ¬ (s.gpr .x1).toNat < H.D + 2)
    (two_taintE [] (fun a u₁ u₂ ⟨⟨s₁, h₁, j₁, _⟩, _⟩ ⟨⟨s₂, h₂, j₂, _⟩, _⟩ =>
      ⟨by rw [j₁.sp, j₂.sp, h₁.fb, h₂.fb], fun _ h => absurd h List.not_mem_nil⟩)
      (c' := Code.eraseOff (.block ([ld .x12 sSaltLen] ++ saltFits zH))) rfl (by taint_decide))
    fun a u ⟨⟨s, h, j, x9, x10⟩, hb⟩ => ?_) ?_
  · rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    have hk2 := h.1.k2
    exact WP.mono (saltFits_ok H hD (F := fb s) j.sp
      (by rw [j.rd, j.wr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide))))
      (a := (s.gpr .x1).toNat) (sl := (s.gpr .x4).toNat) (by omega) (by omega) x9
      (by rw [j.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (s.gpr .x4).isLt) fun w ⟨O, x9', x10'⟩ => ⟨s, h, j.only O, x9', x10', hb⟩
  refine two_ite (fun a u₁ u₂ ⟨s₁, h₁, _, _, x₁, _⟩ ⟨s₂, h₂, _, _, x₂, _⟩ => by
      rw [eval_nonzero, eval_nonzero, x₁, x₂, h₁.gpr (r := .x1) (by decide), h₂.gpr (r := .x1) (by decide),
        h₁.gpr (r := .x4) (by decide), h₂.gpr (r := .x4) (by decide)])
    (ret0_ct fun a u ⟨⟨s, h, j, _⟩, _⟩ => by rw [j.sp, h.fb]) ?_
  have hm : ∀ a w, ((∃ s, E H.D a s ∧ AtE s w ∧ w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x1).toNat - (H.D + 2)) ∧
      (w.gpr .x10 != 0) = decide ((s.gpr .x1).toNat - (H.D + 2) < (s.gpr .x4).toNat) ∧
      ¬ (s.gpr .x1).toNat < H.D + 2) ∧ isa.eval (.nonzero .x .x10) w = some false) →
      ∃ s, E H.D a s ∧ AtM H.D s w := fun a w ⟨⟨s, h, j, x9, x10, hk⟩, hb⟩ => by
    rw [eval_nonzero, x10, Option.some.injEq, decide_eq_false_iff_not] at hb
    exact ⟨s, h, j, x9, by omega⟩
  exact two_post (two_map (fun a => a) hm (main_ct hH hGh hGl hG hc)) fun a w hw => by
    obtain ⟨s, h, m⟩ := hm a w hw
    exact WP.mono (encMain_ok hH hGh hGl hG h.1 m.e m.x9 m.fit) fun t ⟨mt, _⟩ => by rw [mt.sp, h.fb]

end

end VG.Proof.RsaPss.AArch64.Enc
