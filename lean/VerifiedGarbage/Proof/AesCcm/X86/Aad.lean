import VerifiedGarbage.Proof.AesCcm.X86.Absorb

/-!
# AES-CCM on x86: the associated data (`header`, `aadHead y`, `aad y`)

Untrusted: everything here is checked by Lean. `header` zeroes `B` and
writes the encoding of the length `a < 2³²` of the associated data (kept at
`W + nO`) to its start, and its length `h` (2 or 6) to `W + bO`
(`header_ok`); `aadHead y` copies the first `min (a, 16 − h)` bytes of the
associated data after it and chains the block (`aadHead_ok`); `aad y` does
that and chains the rest of the associated data, padded, if there is any
(`aad_ok`): the blocks `Proof.AesCcm.adataBlocks`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 minLen dO nO bO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold zero4_bytes' length_bytesAt LoopPre
  CopyPost copyLoop_ok ofNat_sub32 and_self_beq32 ofNat16_sub)
open VG.Proof.AesCcm (hdrLen headLen adataBlocks)

/-! ## `minLen` -/

/-- `ecx := min (16 − b, n)`, for `n` at `W + nO` and `b` at `W + bO`. -/
theorem minLen_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {n b : Nat}
    (hn : slotv s.mem W nO = BitVec.ofNat 32 n) (hb : slotv s.mem W bO = BitVec.ofNat 32 b) (hb16 : b ≤ 16)
    (hnlt : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min (16 - b) n) ∧ s'.gpr .ebp = W ∧
      s'.gpr .esp = SP ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e16 := ofNat16_sub hb16
  obtain ⟨s₁, run₁, cx, ax, cf, bp, sp, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (imm 16), .alu .sub .ecx (slot bO), .mov .eax (slot nO), .alu .cmp .eax (.reg .ecx)] s = some s₁ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (16 - b) ∧ s₁.gpr .eax = BitVec.ofNat 32 n ∧
      s₁.cf = some (decide (n < 16 - b)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.mem = s.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hn, hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cregs [e16]
    · cregs []
    · cmems [e16, toNat_ofNat32 hnlt, toNat_ofNat32 (show 16 - b < 2 ^ 32 by omega)]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n < 16 - b)) (eval_b cf) (fun ht => ?_) (fun hf => ?_)
  · have hlt : n < 16 - b := by simpa using ht
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cregs [ax]; congr 1; omega
    · cregs [bp]
    · cregs [sp]
    all_goals cmems [m₁, rd₁, wr₁]
  · have hle : ¬ n < 16 - b := by simpa using hf
    exact WP.block_nil ⟨by rw [cx]; congr 1; omega, bp, sp, m₁, rd₁, wr₁⟩

/-! ## The encoding of the length -/

/-- `B` zeroed, then the encoding of the length `a` (at `W + nO`) of the
associated data at its start, and its length at `W + bO`. -/
theorem header_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {a : Nat} (ha : a < 2 ^ 32)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 a) :
    WP isa header s fun s' => Env K W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem s'.mem ∧
      slotv s'.mem W bO = BitVec.ofNat 32 (hdrLen a) ∧
      bytesAt s'.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  have hz := zero4_fold s.mem W 32
  simp only [Nat.reduceAdd] at hz
  obtain ⟨s₁, run₁, hm₁, hax, hcf₁, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      (zero4 blkO ++ [.mov .eax (slot nO), .alu .cmp .eax (imm 0xff00)]) s = some s₁ ∧
      s₁.mem = Cmac.zero4 s.mem (w64 W + BitVec.ofNat 64 32) ∧ s₁.gpr .eax = BitVec.ofNat 32 a ∧
      s₁.cf = some (decide (a < 2 ^ 16 - 2 ^ 8)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [zero4, E.ebp, L.aW, E.perm.wW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hz]
    · cregs [hn]
    · cmems [hn, toNat_ofNat32 ha]; rfl
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have hz' : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 = Spec.Ccm.zeros 16 := by rw [hm₁, zero4_bytes']; rfl
  have fz : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, ⟨w64 W + BitVec.ofNat 64 bO, 4⟩] s.mem s₁.mem := by
    rw [hm₁]; exact (Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨w64 W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains (w64 W) h₁ (by omega) (by decide)
  have cO : (⟨w64 W + BitVec.ofNat 64 bO, 4⟩ : Region).Contains (w64 W + BitVec.ofNat 64 280) 4 :=
    Region.contains_self _ _
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (a < 2 ^ 16 - 2 ^ 8)) (eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · -- `[a]₁₆`.
    have h₁ := of_decide_eq_true ht
    refine WP.of_runBlock ⟨_, by crun [hbp, L.aW, E₁.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (by cregs []) (by cregs []) (by cmems []) (by cmems [])
    · cmems [hrd₁]
    · cmems [hwr₁]
    · cmems []
      exact (fz.writeW (List.mem_cons_self) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ cO
    · cmems []; rw [hdrLen_lo h₁]
    · cmems [hax]
      rw [Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 280, 4⟩])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
          (by decide),
        bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz', show bswap (BitVec.ofNat 32 a) =
          byteRev32 (BitVec.ofNat 32 a) from rfl, ← enc_lo32 h₁]
      rfl
  · -- `0xff ‖ 0xfe ‖ [a]₃₂`.
    have h₁ := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [hbp, L.aW, E₁.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact E₁.keep (by cregs []) (by cregs []) (by cmems []) (by cmems [])
    · cmems [hrd₁]
    · cmems [hwr₁]
    · cmems []
      exact ((fz.writeW (List.mem_cons_self) _ (cB 32 4 (by decide) (by decide))).writeW
        (List.mem_cons_self) _ (cB 34 4 (by decide) (by decide))).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ cO
    · cmems []; rw [hdrLen_mid h₁ ha]
    · cmems [hax]
      rw [Proof.AesGcm.X86.bytesAt_frame (rs := [⟨w64 W + BitVec.ofNat 64 280, 4⟩])
          ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
          (by decide),
        show w64 W + BitVec.ofNat 64 34 = w64 W + BitVec.ofNat 64 32 + BitVec.ofNat 64 2 by rw [add_ofNat_assoc],
        bytesAt_writeW32_at _ _ _ (by decide) (by decide), bytesAt_writeW32_base _ _ _ (by decide) (by decide), hz',
        show bswap (BitVec.ofNat 32 a) = byteRev32 (BitVec.ofNat 32 a) from rfl, ← enc_mid32 h₁ ha]
      rfl

/-! ## The first block of the associated data -/

/-- The first block of the associated data (`a` bytes at `A`, kept at
`W + dO`, `a` at `W + nO`), chained into `W + y`; `dO` and `nO` then the
rest. -/
theorem aadHead_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {a : Nat} (hA : Buf W SP s A a) (ha0 : 0 < a) (ha : a < 2 ^ 32)
    (hd : slotv s.mem W dO = A) (hn : slotv s.mem W nO = BitVec.ofNat 32 a) :
    WP isa (aadHead v.callee v.suffix y) s fun s' => Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          [Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a))]) s' ∧
        slotv s'.mem W dO = A + BitVec.ofNat 32 (headLen a) ∧
        slotv s'.mem W nO = BitVec.ofNat 32 (a - headLen a) := by
  have hh := Proof.AesCcm.hdrLen_le a
  have hh2 : 2 ≤ hdrLen a := by unfold hdrLen; split <;> (try split) <;> omega
  have hh6 : hdrLen a ≤ 6 := by unfold hdrLen; split <;> (try split) <;> omega
  have hn1 : 1 ≤ headLen a ∧ headLen a ≤ a ∧ hdrLen a + headLen a ≤ 16 := by unfold headLen; omega
  refine WP.seq (WP.mono (header_ok L E ha hn) fun s₁ ⟨E₁, hrd₁, hwr₁, f₁, hb₁, hB₁⟩ => ?_)
  have k₁ : ∀ o, (112 ≤ o ∧ o + 4 ≤ 280 ∨ 284 ≤ o ∧ o + 4 ≤ 2560) → slotv s₁.mem W o = slotv s.mem W o :=
    fun o ho => f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
      · exact Lay.w_w (by simp only [bO]; omega) (by omega) (by decide)) (by decide)
  have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 a := by rw [k₁ _ (by decide)]; exact hn
  have hd₁ : slotv s₁.mem W dO = A := by rw [k₁ _ (by decide)]; exact hd
  refine WP.seq (WP.mono (minLen_ok L E₁ hn₁ hb₁ (by omega) ha) fun s₂ ⟨hcx₂, hbp₂, hsp₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  rw [show min (16 - hdrLen a) a = headLen a by unfold headLen; omega] at hcx₂
  have hn₂ : slotv s₂.mem W nO = BitVec.ofNat 32 a := by rw [hm₂]; exact hn₁
  have hd₂ : slotv s₂.mem W dO = A := by rw [hm₂]; exact hd₁
  have hb₂ : slotv s₂.mem W bO = BitVec.ofNat 32 (hdrLen a) := by rw [hm₂]; exact hb₁
  have eh : W + BitVec.ofNat 32 32 + BitVec.ofNat 32 (hdrLen a) = W + BitVec.ofNat 32 (32 + hdrLen a) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have es : BitVec.ofNat 32 a - BitVec.ofNat 32 (headLen a) = BitVec.ofNat 32 (a - headLen a) :=
    ofNat_sub32 hn1.2.1 ha
  obtain ⟨s₃, run₃, hm₃, hdi, hdx, hcx₃, hbp₃, hsp₃, hrd₃, hwr₃⟩ : ∃ s₃, runBlock isa
      [.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO), .alu .add .edx (slot bO),
        .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
        .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax] s₂ = some s₃ ∧
      s₃.mem = (s₂.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (a - headLen a))).writeW
        (w64 W + BitVec.ofNat 64 dO) (A + BitVec.ofNat 32 (headLen a)) ∧
      s₃.gpr .edi = A ∧ s₃.gpr .edx = W + BitVec.ofNat 32 (32 + hdrLen a) ∧
      s₃.gpr .ecx = BitVec.ofNat 32 (headLen a) ∧ s₃.gpr .ebp = W ∧ s₃.gpr .esp = SP ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by crun [hbp₂, L.aW, E₁.perm.wW, E₁.perm.wR, hrd₂, hwr₂, hd₂, hn₂, hb₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · cmems [hd₂, hn₂, hcx₂, es]
    · cregs [hd₂]
    · cregs [hbp₂, eh]
    · cregs [hcx₂]
    · cregs [hbp₂]
    · cregs [hsp₂]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have E₃ : Env K W SP s₃ := ⟨hbp₃, hsp₃, E.perm.of_eq (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])⟩
  have hA₃ := hA.of_eq (s' := s₃) (by rw [hrd₃, hrd₂, hrd₁]) (by rw [hwr₃, hwr₂, hwr₁])
  have aB : w64 (W + BitVec.ofNat 32 (32 + hdrLen a)) = w64 W + BitVec.ofNat 64 (32 + hdrLen a) := L.aW (by omega)
  have dAB : (⟨w64 A, headLen a⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 (32 + hdrLen a), headLen a⟩ :=
    (hA.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right (Lay.wSub (by omega))
  have lp : LoopPre s₃ A (W + BitVec.ofNat 32 (32 + hdrLen a)) (headLen a) :=
    ⟨hdi, hdx, hcx₃, hn1.1, by omega, by have := hA.wrap; omega, by rw [L.nW (by omega)]; have := L.fw; omega,
      (hA₃.take hn1.2.1).rd, by rw [aB]; exact E₃.perm.wC (by omega), by rw [aB]; exact dAB⟩
  refine WP.seq (WP.mono (copyLoop_ok s₃ lp) fun s₄ P₄ => ?_)
  have E₄ : Env K W SP s₄ := E₃.keep (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [P₄.other _ (by decide) (by decide) (by decide) (by decide)]) P₄.rd P₄.wr
  -- What was written.
  have f₃ : Frame [wC W] s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fC : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
    rw [P₄.mem, aB]
    exact writeBytes_frame _ _ _ (by
      rw [length_bytesAt]
      exact Offset.contains (w64 W) (d := 32 + hdrLen a) (n := headLen a) (e := 32) (k := 16) (by omega) (by omega)
        (by decide))
  have fB : Frame [⟨w64 W + BitVec.ofNat 64 32, 16⟩, wC W] s.mem s₄.mem := by
    refine ((f₁.sub fun r hr => ?_).trans ?_).trans (fC.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · rw [← hm₂]; exact f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨wC W, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  have fM : Frame (macR W SP y) s.mem s₄.mem := fB.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact sub_mac (by simp)
  have hAk : bytesAt s₃.mem (w64 A) (headLen a) = (bytesAt s.mem (w64 A) a).take (headLen a) := by
    have dA : ∀ {rs : List Region}, (∀ r ∈ rs, ∃ r', r' = (⟨w64 W, 2560⟩ : Region) ∧ Region.Sub r r') →
        ∀ r ∈ rs, (⟨w64 A, headLen a⟩ : Region).Disjoint r := fun h r hr => by
      obtain ⟨r', rfl, hs⟩ := h r hr
      exact (hA.w.sub_left (Region.sub_prefix hn1.2.1)).sub_right hs
    rw [Proof.AesGcm.X86.bytesAt_frame f₃ (dA fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, rfl, Lay.wSub (by decide)⟩) (by omega), hm₂,
      Proof.AesGcm.X86.bytesAt_frame f₁ (dA fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact ⟨_, rfl, Lay.wSub (by decide)⟩) (by omega),
      Proof.AesCcm.bytesAt_prefix _ _ hn1.2.1]
  have hB₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 32) 16 =
      Spec.Ccm.pad16 (Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a)) := by
    have hl := Proof.AesCcm.length_encodeLen a
    have htl : ((bytesAt s.mem (w64 A) a).take (headLen a)).length = headLen a := by
      rw [List.length_take, length_bytesAt]; omega
    have hB₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 32) 16 = bytesAt s₁.mem (w64 W + BitVec.ofNat 64 32) 16 := by
      rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), hm₂]
    rw [P₄.mem, aB, show w64 W + BitVec.ofNat 64 (32 + hdrLen a) = w64 W + BitVec.ofNat 64 32 +
        BitVec.ofNat 64 (hdrLen a) by rw [add_ofNat_assoc],
      bytesAt_writeBytes_at _ _ _ (by rw [length_bytesAt]; omega) (by decide), length_bytesAt, hAk, hB₃, hB₁]
    rcases Proof.AesCcm.pad16_short (r := Spec.Ccm.encodeLen a ++ (bytesAt s.mem (w64 A) a).take (headLen a))
      (by rw [List.length_append, hl, htl]; omega) with e | e
    · rw [e, List.length_append, hl, htl, List.take_left' hl, ← hl, List.drop_append, hl, List.append_assoc]
      simp only [Spec.Ccm.zeros, List.drop_replicate]
      rw [List.drop_eq_nil_of_le (by rw [hl]; omega), List.nil_append, List.append_assoc,
        show 16 - hdrLen a - (hdrLen a + headLen a - hdrLen a) = 16 - (hdrLen a + headLen a) by omega]
    · exact absurd (congrArg List.length e) (by rw [List.length_append, hl]; simp; omega)
  -- The slots.
  have k₄ : ∀ o, (112 ≤ o ∧ o + 4 ≤ 240 ∨ 240 ≤ o ∧ o + 4 ≤ 2560) →
      slotv s₄.mem W o = slotv s₃.mem W o := fun o ho =>
    fC.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega)) (by omega) (by decide))
      (by decide)
  have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ => by
    rw [show slotv s₃.mem W o = slotv s₂.mem W o from f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
      (by decide), hm₂, k₁ _ (.inl ⟨h₁, by omega⟩)]
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok v L E₄ hR (by rw [k₄ _ (by decide), k₃ _ (by decide) (by decide)]; exact hK)
    (by rw [k₄ _ (by decide), k₃ _ (by decide) (by decide)]; exact hRo) hy)
    fun s₅ ⟨E₅, rd₅, wr₅, f₅, o₅⟩ => ⟨⟨E₅, fM.trans (f₅.sub fun r hr => ?_), ?_,
      by rw [rd₅, P₄.rd, hrd₃, hrd₂, hrd₁], by rw [wr₅, P₄.wr, hwr₃, hwr₂, hwr₁]⟩, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_mac (by simp)
    · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact sub_mac (by simp)
  · have hY₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 := by
      refine Proof.AesGcm.X86.bytesAt_frame fB (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rcases hy with rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    rw [o₅, hY₄, hB₄, ctxCiph_frame fM (k_macR L (by omega)) hRb]
  · have k : slotv s₅.mem W dO = slotv s₄.mem W dO := f₅.readW (r := ⟨w64 W + BitVec.ofNat 64 dO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide)
    rw [k, k₄ _ (by decide), hm₃]
    exact Mem.readW_writeW_self32 _ _ _
  · have k : slotv s₅.mem W nO = slotv s₄.mem W nO := f₅.readW (r := ⟨w64 W + BitVec.ofNat 64 nO, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm) (by decide)
    rw [k, k₄ _ (by decide), hm₃, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _

/-! ## The associated data -/

/-- The associated data (`al` bytes at `A`, kept at `W + aadO` and
`W + alenO`), formatted and chained into `W + y`. -/
theorem aad_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {A : BitVec 32} {al : Nat} (hAp : slotv s.mem W aadO = A)
    (hal : slotv s.mem W alenO = BitVec.ofNat 32 al) (hA : Buf W SP s A al) (hl : al < 2 ^ 32) :
    WP isa (aad v.callee v.suffix y) s (Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
        (adataBlocks (bytesAt s.mem (w64 A) al)))) := by
  obtain ⟨s₁, run₁, hm₁, hzf, hbp, hsp, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa
      [.mov .eax (slot aadO), .store (at_ .ebp dO) .eax, .mov .eax (slot alenO), .store (at_ .ebp nO) .eax,
        .alu .test .eax (.reg .eax)] s = some s₁ ∧
      s₁.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 dO) A).writeW (w64 W + BitVec.ofNat 64 nO)
        (BitVec.ofNat 32 al) ∧
      s₁.zf = some (decide (al = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hAp, hal], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [hAp, hal]
    · cmems [hal]; rw [and_self_beq32 hl]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have f₁ : Frame [wC W] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have fm : Frame (macR W SP y) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
      (by decide)
  have hY₁ : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hA₁ : bytesAt s₁.mem (w64 A) al = bytesAt s.mem (w64 A) al :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hA.w.sub_right (Lay.wSub (by decide)))
      (by have := hA.lt; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hc₁ : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  refine WP.ite (decide (al = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, E₁, fm, ?_, hrd₁, hwr₁⟩
    simp only [hY₁, adataBlocks, length_bytesAt, h0, ↓reduceIte]; rfl
  · have h0 : al ≠ 0 := of_decide_eq_false hf
    have hK₁ : slotv s₁.mem W ctxO = K := by rw [k₁ _ (by decide) (by decide)]; exact hK
    have hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R := by rw [k₁ _ (by decide) (by decide)]; exact hRo
    have hd₁ : slotv s₁.mem W dO = A := by
      rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
      exact Mem.readW_writeW_self32 _ _ _
    have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 al := by rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
    have hk : headLen al ≤ al := by unfold headLen; omega
    refine WP.seq (WP.mono (aadHead_ok v L E₁ hR hK₁ hR₁ hy (hA.of_eq hrd₁ hwr₁) (by omega) hl hd₁ hn₁)
      fun s₂ ⟨A₂, hd₂, hn₂⟩ => ?_)
    have hT : 0 < al - headLen al → Buf W SP s₂ (A + BitVec.ofNat 32 (headLen al)) (al - headLen al) := fun h =>
      (hA.drop hk (by have := hA.wrap; omega)).of_eq (by rw [A₂.rd, hrd₁]) (by rw [A₂.wr, hwr₁])
    refine WP.mono (absorbPad_ok v L A₂.env hR (by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact hK₁)
      (by rw [slot_kept L hy A₂.frame (by decide) (by decide)]; exact hR₁) hy hT (by omega) hd₂ hn₂)
      fun s₃ A₃ => ⟨A₃.env, fm.trans (A₂.frame.trans A₃.frame), ?_, by rw [A₃.rd, A₂.rd, hrd₁],
        by rw [A₃.wr, A₂.wr, hwr₁]⟩
    have hrest : bytesAt s₂.mem (w64 (A + BitVec.ofNat 32 (headLen al))) (al - headLen al) =
        (bytesAt s.mem (w64 A) al).drop (headLen al) := by
      by_cases h : al - headLen al = 0
      · rw [h, List.drop_eq_nil_of_le (by rw [length_bytesAt]; omega)]; rfl
      · have hw : A.toNat + headLen al < 2 ^ 32 := by have := hA.wrap; omega
        rw [buf_kept (hT (by omega)) (by omega) A₂.frame, Buf.ptr hw, Proof.AesCcm.bytesAt_suffix _ _ hk, hA₁]
    rw [A₃.out, A₂.out, ctxCiph_frame A₂.frame (k_macR L (by omega)) hRb, hrest, hY₁, hc₁, hA₁,
      ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ↓reduceIte]

end VG.Proof.AesCcm.X86
