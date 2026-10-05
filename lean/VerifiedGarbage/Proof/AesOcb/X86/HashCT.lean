import VerifiedGarbage.Proof.AesOcb.X86.FrontCT

/-!
# AES-OCB on x86: `HASH` in constant time

Untrusted: everything here is checked by Lean. `HASH` runs a loop of
chunks, each a loop filling the buffer (`hashFill_ct`, `fillLoop_ct`), a
call and a loop adding the buffer to the sum (`hashSum_ct`): `chunk_ct`;
the number of chunks and of their blocks is public (`hashLoop_ct`). The
counts and the buffer's address are loaded from their slots. Then the rest
(`hashRest_ct`) if there is one (`hashTail_ct`): `hash_ct`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4)
open VG.Proof.AesGcm.X86 (CT w64 w64_add slotv slotv_eq toNat_add32 covers_off)

/-- The fill loop's state after `i` of the `c` blocks of a chunk from block
`j`, for some cipher, `L_*`, associated data and start. -/
def FillI (p : Prm) (j c i : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, HCtx p ciph l a s₀ ∧ FillInv p ciph l a s₀ j c t i

/-- `HASH`'s state after `j` whole blocks. -/
def HI (p : Prm) (j : Nat) (t : State) : Prop :=
  ∃ ciph l a s₀, HCtx p ciph l a s₀ ∧ HInv p ciph l a s₀ t j

/-- One block into the buffer. -/
theorem hashFill_ct {p : Prm} (L : Lay p) {j c i : Nat} (hi : i < c) (hjc : j + c ≤ p.al / 16) :
    CT (FillI p j c i) hashFill := by
  have hal := L.al32
  unfold hashFill
  refine CT.seq (J := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (lNtz_ct L (i := j + i + 1) (by omega) (by omega) fun t ⟨_, _, _, _, _, F⟩ => ⟨F.env, F.edi⟩)
    (fun t ⟨_, _, _, _, _, F⟩ => WP.mono (lNtz_ok L F.env (by omega) (by omega) F.edi F.l0) fun t₁ P₁ =>
      ⟨P₁.env L F.env, by rw [P₁.gpr _ (by decide) (by decide) (by decide), F.esi], by
        rw [← F.fp]
        exact P₁.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)⟩) ?_
  simp only [List.append_assoc, List.singleton_append]
  refine RelCT.block_append (CT.seq (J := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (j + i)) ∧
      slotv t.mem p.W fpO = p.W + BitVec.ofNat 32 (bufO + 16 * i))
    (CT.taint [.ebp] (pin_ebp fun t h => h.1.ebp) (by taint_decide)) (fun t h => ?_) ?_)
  · obtain ⟨E, si, fp⟩ := h
    obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E (s := lO) (d := ohO) (by decide) (by decide)
      (.inl (by decide))
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
      rw [m₂]; exact xorMem16_frame _ _ _ _ _
    refine WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (frame_toMut f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))),
      by rw [g₂ _ (by decide), si], ?_⟩
    rw [← fp]
    exact f₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 fpO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (by decide) (by decide) (by decide)) (by decide)
  refine load_blk_ct L (r := .edx) (o := fpO) (by decide) (fun t h => ⟨h.1, h.2.2⟩)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) (CT.taint [.ebp, .esi, .edx]
      (pin3 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h, Ld.reg (by decide) (fun s h => h.2.1) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- The fill loop: `c` blocks into the buffer. -/
theorem fillLoop_ct {p : Prm} (L : Lay p) {j c : Nat} (hc0 : 0 < c) (hc : c ≤ 8) (hjc : j + c ≤ p.al / 16) :
    CT (FillI p j c 0) (.loop hashFill .ne) := by
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ c ∧ FillI p j c (c - n) t) (fun n => ?_)
    (fun n t ⟨hn0, hn, _, _, _, _, C, F⟩ => WP.mono (fill_step C hc hjc (by omega) F) fun t' ⟨F', zf'⟩ =>
      ⟨hn0, by rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega,
        fun h1 => ⟨by omega, by omega, _, _, _, _, C, by rw [show c - (n - 1) = c - n + 1 by omega]; exact F'⟩⟩) c).mono
    fun t h => ⟨hc0, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  by_cases hn : 0 < n
  · exact (hashFill_ct L (i := c - n) (by omega) hjc).mono fun _ h => h.2.2
  · exact RelCT.of_false fun _ _ h => hn h.1.1

/-- The sum of the buffer. -/
theorem hashSum_ct {p : Prm} (L : Lay p) {c : Nat} :
    CT (fun t => Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c) hashSum := by
  unfold hashSum
  exact load_ct L (r := .ebx) (o := cntO) (by decide) (fun t h => h)
    (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
    (CT.taint [.ebp, .ebx] (pin2 fun t h => ⟨Ld.reg (by decide) (fun s h => h.1.ebp) t h,
      by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))

/-- A chunk, from block `j`. -/
theorem chunk_ct (v : BlocksImpl) {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.al / 16) :
    CT (HI p j) (hashChunk (callees v)) := by
  have hal := L.al32
  unfold hashChunk
  refine RelCT.assoc (CT.seq (J := fun t => HI p j t ∧ t.gpr .ebx = BitVec.ofNat 32 (min 8 (p.al / 16 - j)))
    (load_ct L (r := .ebx) (o := hlO) (v := BitVec.ofNat 32 (p.al / 16 - j)) (by decide)
      (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.hl⟩) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebx] (pin1 fun t h => by obtain ⟨_, _, hv, _⟩ := h; exact hv) (by taint_decide)))
    (fun t ⟨_, _, _, _, C, H⟩ => WP.mono (chunkHead_ok C H) fun t' ⟨H', bx⟩ => ⟨⟨_, _, _, _, C, H'⟩, bx⟩) ?_)
  generalize hc : min 8 (p.al / 16 - j) = c
  have hc0 : 0 < c := by omega
  have hc8 : c ≤ 8 := by omega
  have hjc : j + c ≤ p.al / 16 := by omega
  -- The chunk's count and the buffer's start.
  refine CT.seq (J := FillI p j c 0)
    (CT.taint [.ebp] (pin_ebp fun t h => by obtain ⟨⟨_, _, _, _, _, H⟩, _⟩ := h; exact H.env.ebp) (by taint_decide))
    (fun t ⟨⟨_, _, _, _, C, H⟩, bx⟩ => by
      obtain ⟨t₁, run₁, F⟩ := chunkStart_ok C H bx
      exact WP.of_runBlock ⟨t₁, run₁, _, _, _, _, C, F⟩) ?_
  -- The fill loop.
  refine CT.seq (J := FillI p j c c) (fillLoop_ct L hc0 hc8 hjc)
    (fun t ⟨_, _, _, _, C, F⟩ => WP.mono (fill_ok C hc0 hc8 hjc F) fun t' F' => ⟨_, _, _, _, C, F'⟩) ?_
  -- The call.
  have hargs : ∀ t, FillI p j c c t → ∃ s₁, runBlock isa [.mov .edx (.reg .ebp), .alu .add .edx (imm bufO),
      .mov .ebx (slot cntO)] t = some s₁ ∧ s₁.gpr .edx = p.W + BitVec.ofNat 32 bufO ∧
      s₁.gpr .ebx = BitVec.ofNat 32 c ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s₁.gpr r = t.gpr r) ∧ s₁.mem = t.mem ∧
      s₁.rd = t.rd ∧ s₁.wr = t.wr := fun t ⟨_, _, _, _, _, F⟩ => by
    have hcnt := F.cnt
    simp only [slotv_eq] at hcnt
    exact ⟨_, by grun [F.env.ebp, L.aW, F.env.perm.wR, hcnt], by gregs [F.env.ebp], by gregs [hcnt],
      fun r _ h₂ _ h₄ => by gregs [h₂, h₄], by gmems [], by gmems [], by gmems []⟩
  have hD : ∀ t, FillI p j c c t → DReg p t (p.W + BitVec.ofNat 32 bufO) c := fun t ⟨_, _, _, _, _, F⟩ =>
    DReg.w L F.env (d := bufO) (n := c) (by simp only [bufO, scrO]; omega) (.inr (.inr (.inr (by decide))))
  refine CT.seq (J := fun t => Env p t ∧ slotv t.mem p.W cntO = BitVec.ofNat 32 c)
    (callBlocks_ct v.encOk v.encCt v.encNosp v.encStack L
      (fun t h => ⟨by obtain ⟨_, _, _, _, _, F⟩ := h; exact F.env, hD t h, hargs t h⟩)
      fun hJ => by exact CT.taint [.ebp] (pin_ebp hJ) (by taint_decide))
    (fun t h => ?_) ?_
  · obtain ⟨_, _, _, _, _, F⟩ := h
    refine WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L F.env
      (hargs t ⟨_, _, _, _, ‹_›, F⟩) (hD t ⟨_, _, _, _, ‹_›, F⟩)) fun t' P => ⟨P.env, ?_⟩
    rw [← F.cnt]
    have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
    exact P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 cntO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  -- The sum, and the blocks left.
  refine CT.seq (J := Env p) (hashSum_ct L) (fun t ⟨E, hcnt⟩ => WP.mono (hashSum_ok L E hc0 hc8 hcnt
      (g := fun k => blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 (bufO + 16 * k))) fun _ _ => rfl)
      fun t' ⟨fr, _, g, rd, wr⟩ => E.mut L (by rw [g _ (by decide) (by decide) (by decide), E.ebp])
        (by rw [g _ (by decide) (by decide) (by decide), E.esp]) rd wr
        (frame_toMut fr fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide))))
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The chunks: from block `8 (k − n)`, `n` of the `k = ⌈m / 8⌉` left. -/
theorem hashLoop_ct (v : BlocksImpl) {p : Prm} (L : Lay p) (hm : 0 < p.al / 16) :
    CT (HI p 0) (.loop (hashChunk (callees v)) .ne) := by
  have hal := L.al32
  have hk : ∀ n, 0 < n → n ≤ (p.al / 16 + 7) / 8 → 8 * ((p.al / 16 + 7) / 8 - n) < p.al / 16 := fun n h₁ h₂ => by
    omega
  refine (CT.loopN (fun n t => 0 < n ∧ n ≤ (p.al / 16 + 7) / 8 ∧ HI p (8 * ((p.al / 16 + 7) / 8 - n)) t)
    (fun n => ?_) (fun n t ⟨hn0, hn, _, _, _, _, C, H⟩ => ?_) ((p.al / 16 + 7) / 8)).mono
    fun t h => ⟨by omega, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  · by_cases h : 0 < n ∧ n ≤ (p.al / 16 + 7) / 8
    · exact (chunk_ct v L (hk n h.1 h.2)).mono fun _ h => h.2.2
    · exact RelCT.of_false fun _ _ h' => h ⟨h'.1.1, h'.1.2.1⟩
  refine WP.mono (hashChunk_ok v C H (hk n hn0 hn)) fun t' ⟨H', zf'⟩ => ⟨hn0, ?_, fun h1 => ⟨by omega, by omega,
    _, _, _, _, C, ?_⟩⟩
  · rw [eval_ne zf']; congr 1; by_cases h : n = 1 <;> simp [h] <;> omega
  · rw [show 8 * ((p.al / 16 + 7) / 8 - (n - 1)) = 8 * ((p.al / 16 + 7) / 8 - n) +
      min 8 (p.al / 16 - 8 * ((p.al / 16 + 7) / 8 - n)) by omega]
    exact H'

/-- The rest of the associated data. -/
theorem hashRest_ct (v : BlocksImpl) {p : Prm} (L : Lay p) (hr : 0 < p.al % 16) :
    CT (HI p (p.al / 16)) (hashRest (callees v)) := by
  have hal := L.aw
  have hS : ∀ t, Env p t → SBuf p t (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) (p.al % 16) := fun t E => by
    have a16 : w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))) = w64 p.A + BitVec.ofNat 64 (16 * (p.al / 16)) :=
      w64_add (by omega)
    have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * (p.al / 16))), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
      rw [a16]; exact Offset.sub_base _ (by omega)
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega)]; omega
    · rw [a16]; exact covers_off E.perm.aad (by omega) (by omega)
  -- After the head: the environment, the rest's address and length.
  let J : State → Prop := fun t => Env p t ∧ t.gpr .esi = p.A + BitVec.ofNat 32 (16 * (p.al / 16)) ∧
    slotv t.mem p.W restO = BitVec.ofNat 32 (p.al % 16)
  unfold hashRest
  refine CT.seq (J := J) ?_ (fun t ⟨_, _, _, _, _, H⟩ => ?_) ?_
  · exact load_blk_ct L (r := .ebx) (o := ctxO) (by decide) (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.env.slots.ctx⟩)
      (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide))
      (CT.taint [.ebp, .ebx] (pin2 fun t h => ⟨Ld.reg (by decide)
        (fun s (h : HI p (p.al / 16) s) => by obtain ⟨_, _, _, _, _, H⟩ := h; exact H.env.ebp) t h,
        by obtain ⟨_, _, hv, _⟩ := h; exact hv⟩) (by taint_decide))
  · obtain ⟨t₂, run₂, E₂, m₂, g₂, rd₂, wr₂⟩ := hashRestHead_ok L H.env
    refine WP.of_runBlock ⟨t₂, run₂, E₂, by rw [g₂ _ (by decide) (by decide), H.esi], ?_⟩
    rw [← H.rest, slotv_eq, slotv_eq, m₂]
    exact (xorMem16_frame _ _ _ _ _).readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  -- `pad(A_*)`, its offset, the call and the sum.
  refine CT.seq (J := Env p) (padTo_ct L (.inl rfl) fun t h => h)
    (fun t ⟨E, si, rest⟩ => WP.mono (padTo_ok L E (d := bufO) (cO := restO) hr (by omega) (by decide) (by decide)
      (.inl (by decide)) si rest (hS t E)) fun t' ⟨fr, _, g, rd, wr⟩ =>
        E.mut L (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.ebp])
          (by rw [g _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd wr
          (frame_toMut fr fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    ?_
  refine CT.seq (J := Env p) (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide)) (fun t E => ?_) ?_
  · obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16W_ok L E (s := ohO) (d := bufO) (by decide) (by decide)
      (.inl (by decide))
    exact WP.of_runBlock ⟨t₂, run₂, E.mut L (by rw [g₂ _ (by decide), E.ebp]) (by rw [g₂ _ (by decide), E.esp])
      rd₂ wr₂ (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))⟩
  refine CT.seq (J := Env p) (oneCall_ct v.encOk v.encCt v.encNosp v.encStack L (.inr rfl) fun _ h => h)
    (fun t E => WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E
      (oneBlock_ok E bufO) (DReg.w L E (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
      fun _ P => P.env)
    (CT.taint [.ebp] (pin_ebp fun _ h => h.ebp) (by taint_decide))

/-- The rest, if there is one. -/
theorem hashTail_ct (v : BlocksImpl) {p : Prm} (L : Lay p) :
    CT (HI p (p.al / 16)) (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (callees v)))) := by
  refine load_ct L (r := .eax) (o := restO) (v := BitVec.ofNat 32 (p.al % 16)) (by decide)
    (fun t ⟨_, _, _, _, _, H⟩ => ⟨H.env, H.rest⟩) (CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)) ?_
  refine CT.seq (J := fun t => HI p (p.al / 16) t ∧ t.zf = some (decide (p.al % 16 = 0)))
    (CT.taint [] (fun _ _ _ _ _ h => by simp at h) (by taint_decide)) (fun t ⟨s₀, h₀, ax, g, m, rd, wr⟩ => ?_)
    (CT.ite (decide (p.al % 16 = 0)) (fun _ h => eval_e h.2) (fun _ => CT.nil)
      (fun hb => (hashRest_ct v L (by have := of_decide_eq_false hb; omega)).mono fun _ h => h.1))
  obtain ⟨_, _, _, _, C, H⟩ := h₀
  have hal := L.al32
  refine WP.of_runBlock ⟨_, by grun [], ⟨_, _, _, _, C, H.of_keep (fun r h₁ _ _ _ => by gregs [g r h₁]) (by gmems [m])
    (by gmems [rd]) (by gmems [wr])⟩, ?_⟩
  gmems [ax, BitVec.and_self, beq_zero32 (show p.al % 16 < 2 ^ 32 by omega)]

/-- `HASH`. -/
theorem hash_ct (v : BlocksImpl) {p : Prm} (L : Lay p) :
    CT (fun t => ∃ ciph l a, HCtx p ciph l a t ∧ Env p t ∧
      blockAtMem t.mem (w64 p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l 0) (Impl.AesOcb.X86.hash (callees v)) := by
  unfold Impl.AesOcb.X86.hash
  refine CT.seq (J := fun t => HI p 0 t ∧ t.zf = some (decide (p.al / 16 = 0)))
    (CT.taint [.ebp] (pin_ebp fun _ h => by obtain ⟨_, _, _, _, E, _⟩ := h; exact E.ebp) (by taint_decide))
    (fun t ⟨_, _, _, C, E, hl0⟩ => WP.mono (hashHead_ok C E hl0) fun t' ⟨H, zf⟩ => ⟨⟨_, _, _, _, C, H⟩, zf⟩) ?_
  refine CT.seq (J := HI p (p.al / 16))
    (CT.ite (decide (p.al / 16 = 0)) (fun _ h => eval_e h.2) (fun _ => CT.nil)
      (fun hb => (hashLoop_ct v L (by have := of_decide_eq_false hb; omega)).mono fun _ h => h.1))
    (fun t ⟨⟨_, _, _, _, C, H⟩, zf⟩ => WP.ite (decide (p.al / 16 = 0)) (eval_e zf)
      (fun hb => WP.block_nil ⟨_, _, _, _, C, by rw [of_decide_eq_true hb]; exact H⟩)
      (fun hb => WP.mono (hashLoop_ok v C H (by have := of_decide_eq_false hb; omega)) fun t' H' =>
        ⟨_, _, _, _, C, H'⟩)) (hashTail_ct v L)

end VG.Proof.AesOcb.X86
