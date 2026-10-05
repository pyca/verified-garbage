import VerifiedGarbage.Proof.AesOcb.X86.HashChunk
import VerifiedGarbage.Proof.AesOcb.X86.PadTo

/-!
# AES-OCB on x86: `HASH` (`hash`)

Untrusted: everything here is checked by Lean. `hash` zeroes the sum and the
offset, keeps the number of whole blocks of the associated data and the
length of the rest in `W`, takes the whole blocks a chunk at a time
(`hashChunk_ok`), and the rest, padded, XORed with `Offset_m ⊕ L_*` and
enciphered (`hashRest_ok`): the sum is §4.1's `HASH(K, A)` (`hash_ok`,
`Proof.Ocb.hash_eq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem blockAt lAt ntz ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt hsum)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off
  length_bytesAt)

/-- `L_*`, after a frame within `mutR`. -/
theorem lstar_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (mutR p) m m') :
    ctxLstar m' (w64 p.K) = ctxLstar m (w64 p.K) :=
  Proof.Ocb.blockAtMem_frame h fun r hr => (k_mut L r hr).sub_left (Offset.sub_base _ (by decide))

/-- The padded rest of the associated data, after its `m` whole blocks. -/
theorem hashRest_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H : HInv p ciph l a s₀ t (p.al / 16)) (hr : 0 < p.al % 16) :
    WP isa (hashRest (callees v)) t fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  have L := C.lay
  have E := H.env
  have hal := L.aw
  generalize hm : p.al / 16 = m at H
  -- `Offset_m ⊕ L_*`
  have hc := E.slots.ctx
  simp only [slotv_eq] at hc
  obtain ⟨t₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .ebx (slot ctxO)] t = some t₁ ∧
      t₁.gpr .ebx = p.K ∧ (∀ r, r ≠ .ebx → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hc], by gregs [hc], fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
  have E₁ : Env p t₁ := E.keep (by rw [g₁ _ (by decide)]) (by rw [g₁ _ (by decide)]) rd₁ wr₁ m₁
  obtain ⟨t₂, run₂, m₂, g₂, rd₂, wr₂⟩ := xor16R_ok L E₁ (b := .ebx) (by decide) bx₁ L.kw L.k_w
    E₁.perm.k (s := 240) (d := ohO) (by decide) (by decide)
  have fr₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] t.mem t₂.mem := by
    rw [m₂, m₁]; exact xorMem16_frame _ _ _ _ _
  have E₂ : Env p t₂ := E₁.mut L (by rw [g₂ _ (by decide), E₁.ebp]) (by rw [g₂ _ (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (by rw [m₂]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩)))
  have oh₂ : blockAtMem t₂.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [m₂, xorMem16_block, m₁, H.oh, ← C.lstar, ← lstar_mut L (wR_mut (hashR_wR H.frame))]; rfl
  have fH₂ : Frame (hashR p) s₀.mem t₂.mem := H.frame.trans (fr₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  -- `pad(A_*)`
  have si₂ : t₂.gpr .esi = p.A + BitVec.ofNat 32 (16 * m) := by rw [g₂ _ (by decide), g₁ _ (by decide), H.esi]
  have rest₂ : slotv t₂.mem p.W restO = BitVec.ofNat 32 (p.al % 16) := by
    rw [← H.rest]
    exact fr₂.readW (r := ⟨w64 p.W + BitVec.ofNat 64 restO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide)
  have a16 : w64 (p.A + BitVec.ofNat 32 (16 * m)) = w64 p.A + BitVec.ofNat 64 (16 * m) := w64_add (by omega)
  have sub : Region.Sub ⟨w64 (p.A + BitVec.ofNat 32 (16 * m)), p.al % 16⟩ ⟨w64 p.A, p.al⟩ := by
    rw [a16]; exact Offset.sub_base _ (by omega)
  have hS : SBuf p t₂ (p.A + BitVec.ofNat 32 (16 * m)) (p.al % 16) := by
    refine ⟨?_, L.a_w.sub_left sub, ?_⟩
    · rw [toNat_add32 (by omega)]; omega
    · rw [a16]; exact covers_off E₂.perm.aad (by omega) (by omega)
  have hrestb : bytesAt t₂.mem (w64 (p.A + BitVec.ofNat 32 (16 * m))) (p.al % 16) = a.drop (16 * (a.length / 16)) := by
    rw [C.len, hm, ← C.aad, Proof.Ocb.bytesAt_drop _ _ (by omega), show p.al - 16 * m = p.al % 16 by omega, a16]
    have ad : ∀ r ∈ mutR p, (⟨w64 p.A, p.al⟩ : Region).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact L.a_w.sub_right (Region.sub_prefix (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.a_w.sub_right (Lay.wSub (by decide))
      · exact L.ba.symm
      · exact L.a_d
    exact Proof.AesGcm.X86.bytesAt_frame (wR_mut (hashR_wR fH₂))
      (fun r hr => (ad r hr).sub_left (Offset.sub_base _ (by omega))) (by omega)
  unfold hashRest
  refine WP.seq (WP.of_runBlock ⟨t₂, runBlock_app_of run₁ run₂, ?_⟩)
  refine WP.seq (WP.mono (padTo_ok L E₂ (d := bufO) (cO := restO) hr (by omega) (by decide) (by decide)
    (.inl (by decide)) si₂ rest₂ hS) fun t₃ ⟨fr₃, pad₃, g₃, rd₃, wr₃⟩ => ?_)
  rw [hrestb] at pad₃
  have E₃ : Env p t₃ := E₂.mut L (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.ebp])
    (by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), E₂.esp]) rd₃ wr₃
    (frame_toMut fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  have oh₃ : blockAtMem t₃.mem (w64 p.W + BitVec.ofNat 64 ohO) = offAt 0 l m ^^^ l := by
    rw [Proof.Ocb.blockAtMem_frame fr₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide), oh₂]
  -- XORed with the offset
  obtain ⟨t₄, run₄, m₄, g₄, rd₄, wr₄⟩ := xor16W_ok L E₃ (s := ohO) (d := bufO) (by decide) (by decide)
    (.inl (by decide))
  have E₄ : Env p t₄ := E₃.mut L (by rw [g₄ _ (by decide), E₃.ebp]) (by rw [g₄ _ (by decide), E₃.esp]) rd₄ wr₄
    (frame_toMut (by rw [m₄]; exact xorMem16_frame _ _ _ _ _) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩))))
  have buf₄ : blockAtMem t₄.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l) := by rw [m₄, xorMem16_block, pad₃, oh₃]
  have fH₄ : Frame (hashR p) s₀.mem t₄.mem := fH₂.trans ((fr₃.trans (by rw [m₄]; exact xorMem16_frame _ _ _ _ _)).sub
    fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩))))))
  refine WP.seq (WP.of_runBlock ⟨t₄, run₄, ?_⟩)
  -- enciphered
  refine WP.seq (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encStack L E₄
    (oneBlock_ok E₄ bufO) (DReg.w L E₄ (d := bufO) (n := 1) (by decide) (.inr (.inr (.inr (by decide))))))
    fun t₅ P₅ => ?_)
  have aB : w64 (p.W + BitVec.ofNat 32 bufO) = w64 p.W + BitVec.ofNat 64 bufO := L.aW (by decide)
  have buf₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 bufO) =
      ciph (pad (a.drop (16 * (a.length / 16))) ^^^ (offAt 0 l m ^^^ l)) := by
    have := P₅.enc (i := 0) (by decide)
    rw [aB, show w64 p.W + BitVec.ofNat 64 bufO + BitVec.ofNat 64 (16 * 0) = w64 p.W + BitVec.ofNat 64 bufO from
      BitVec.add_zero _] at this
    rw [this, buf₄, C.ciph' (wR_mut (hashR_wR fH₄))]
  have fH₅ : Frame (hashR p) s₀.mem t₅.mem := fH₄.trans (P₅.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [aB]; exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inr ⟨by decide, by decide⟩)))))
    · exact ⟨_, by simp, fun _ h => h⟩)
  have kS : ∀ {rs : List Region} {u u' : State}, Frame rs u.mem u'.mem →
      (∀ r ∈ rs, (⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩ : Region).Disjoint r) →
      blockAtMem u'.mem (w64 p.W + BitVec.ofNat 64 sumO) = blockAtMem u.mem (w64 p.W + BitVec.ofNat 64 sumO) :=
    fun h hd => Proof.Ocb.blockAtMem_frame h hd
  have sum₅ : blockAtMem t₅.mem (w64 p.W + BitVec.ofNat 64 sumO) = hsum ciph l a m := by
    rw [kS P₅.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [aB]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm),
      kS (u := t₃) (rs := [⟨w64 p.W + BitVec.ofNat 64 bufO, 16⟩]) (by rw [m₄]; exact xorMem16_frame _ _ _ _ _)
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS fr₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      kS (u := t) (rs := [⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩]) fr₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      H.sum]
  -- added to the sum
  obtain ⟨t₆, run₆, m₆, g₆, rd₆, wr₆⟩ := xor16W_ok L P₅.env (s := bufO) (d := sumO) (by decide) (by decide)
    (.inr (by decide))
  refine WP.of_runBlock ⟨t₆, run₆, P₅.env.mut L (by rw [g₆ _ (by decide), P₅.env.ebp])
    (by rw [g₆ _ (by decide), P₅.env.esp]) rd₆ wr₆ (frame_toMut (by rw [m₆]; exact xorMem16_frame _ _ _ _ _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inl (by decide))),
    fH₅.trans (by
      rw [m₆]
      exact (xorMem16_frame _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact inHashR p (.inl ⟨by decide, by decide⟩)), ?_,
    by rw [rd₆, P₅.rd, rd₄, rd₃, rd₂, rd₁, H.rd], by rw [wr₆, P₅.wr, wr₄, wr₃, wr₂, wr₁, H.wr]⟩
  rw [m₆, xorMem16_block, sum₅, buf₅, Proof.Ocb.hash_eq]
  simp only [C.len, hm]
  have hlen : (a.drop (16 * m)).length = p.al % 16 := by simp [C.len]; omega
  simp only [hlen, show p.al % 16 > 0 from hr, ↓reduceIte]

/-- After the whole blocks: the rest, if any. -/
theorem hashTail_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H : HInv p ciph l a s₀ t (p.al / 16)) :
    WP isa (.seq (.block [.mov .eax (slot restO), .alu .test .eax (.reg .eax)])
      (.ite .e (.block []) (hashRest (callees v)))) t fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
        blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
        t'.wr = s₀.wr := by
  have L := C.lay
  have rest := H.rest
  simp only [slotv_eq] at rest
  obtain ⟨t₁, run₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa [.mov .eax (slot restO), .alu .test .eax (.reg .eax)] t =
      some t₁ ∧ t₁.zf = some (decide (p.al % 16 = 0)) ∧
      (∀ r, r ≠ .eax → t₁.gpr r = t.gpr r) ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [H.env.ebp, L.aW, H.env.perm.wR, rest], ?_, fun r h => by gregs [h], by gmems [], by gmems [],
      by gmems []⟩
    gmems [rest, BitVec.and_self, beq_zero32 (show p.al % 16 < 2 ^ 32 by omega)]
  have H₁ := H.of_keep (fun r h₁ _ _ _ => g₁ r h₁) m₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (p.al % 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have h0 : p.al % 16 = 0 := of_decide_eq_true hb
    refine ⟨H₁.env, H₁.frame, ?_, H₁.rd, H₁.wr⟩
    rw [H₁.sum, Proof.Ocb.hash_eq, C.len]
    have hlen : (a.drop (16 * (p.al / 16))).length = 0 := by simp [C.len]; omega
    simp [hlen]
  · exact hashRest_ok v C H₁ (by have := of_decide_eq_false hb; omega)

theorem shr4_32 {v : Nat} (hv : v < 2 ^ 32) : BitVec.ofNat 32 v >>> 4 = BitVec.ofNat 32 (v / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat32 hv, toNat_ofNat32 (by omega), Nat.shiftRight_eq_div_pow]

/-- The start of `HASH`: the sum and the offset zeroed, the counts. -/
theorem hashHead_ok {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State} (C : HCtx p ciph l a s₀)
    (E : Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block (zero4 sumO ++ zero4 ohO ++
      [.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)])) s₀ fun s =>
      HInv p ciph l a s₀ s 0 ∧ s.zf = some (decide (p.al / 16 = 0)) := by
  have L := C.lay
  have hal := L.al32
  have hA := E.slots.aad
  have hn := E.slots.alen
  simp only [slotv_eq] at hA hn
  have z₁ := zero4_fold s₀.mem p.W sumO
  have z₂ := zero4_fold (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) p.W ohO
  have fz : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩] s₀.mem
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO)) (w64 p.W + BitVec.ofNat 64 ohO)) :=
    ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)).trans ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have rz : ∀ {d : Nat}, 176 ≤ d → d + 4 ≤ 2560 →
      (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).readW (w64 p.W + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW (w64 p.W + BitVec.ofNat 64 d) 32 := fun h h' =>
    fz.readW (r := ⟨w64 p.W + BitVec.ofNat 64 _, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (.inr (by simp only [sumO, ohO]; omega)) h' (by decide)) (by decide)
  have hA' := (rz (d := aadO) (by decide) (by decide)).trans hA
  have hn' := (rz (d := alenO) (by decide) (by decide)).trans hn
  simp only [sumO, ohO, aadO, alenO, Nat.reduceAdd] at hA' hn'
  obtain ⟨s₁, run₁, m₁, si₁, di₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa (zero4 sumO ++ zero4 ohO ++
      [.mov .esi (slot aadO), .mov .eax (slot alenO), .mov .ecx (.reg .eax), .alu .and .ecx (imm 15),
       .store (at_ .ebp restO) .ecx, .shift .shr .eax 4, .store (at_ .ebp hlO) .eax, .mov .edi (imm 1),
       .alu .test .eax (.reg .eax)]) s₀ = some s₁ ∧
      s₁.mem = ((Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)).writeW (w64 p.W + BitVec.ofNat 64 restO)
          (BitVec.ofNat 32 (p.al % 16))).writeW (w64 p.W + BitVec.ofNat 64 hlO) (BitVec.ofNat 32 (p.al / 16)) ∧
      s₁.gpr .esi = p.A ∧ s₁.gpr .edi = BitVec.ofNat 32 1 ∧ s₁.zf = some (decide (p.al / 16 = 0)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
    refine ⟨_, by grun [zero4, E.ebp, L.aW, E.perm.wR, E.perm.wW, hA, hn, z₁, z₂, hA', hn'], ?_, by gregs [hA, hA'], by gregs [],
      ?_, fun r h₁ h₂ h₃ h₄ => by gregs [h₁, h₂, h₃, h₄], by gmems [], by gmems []⟩
    · gmems [hA', hn', z₁, z₂, and15_32 hal, shr4_32 hal]
    · gmems [hA', hn', z₁, z₂, shr4_32 hal, BitVec.and_self, beq_zero32 (show p.al / 16 < 2 ^ 32 by omega)]
  have F : Frame [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] s₀.mem s₁.mem := by
    rw [m₁]
    have hm : (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 sumO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 ohO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩] := by simp
    exact (((fz.mono (by simp)).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276) (n := 4) (by decide)
      (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264) (n := 4) (by decide)
      (by decide) (by decide)))
  have fH : Frame (hashR p) s₀.mem s₁.mem := F.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact inHashR p (.inl ⟨by decide, by decide⟩)
    · exact inHashR p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inHashR p (.inr (.inr (.inr (.inr (.inl ⟨by decide, by decide⟩)))))
  have kz : ∀ {d : Nat}, d + 16 ≤ 264 → blockAtMem s₁.mem (w64 p.W + BitVec.ofNat 64 d) =
      blockAtMem (Proof.Cmac.zero4 (Proof.Cmac.zero4 s₀.mem (w64 p.W + BitVec.ofNat 64 sumO))
        (w64 p.W + BitVec.ofNat 64 ohO)) (w64 p.W + BitVec.ofNat 64 d) := fun h => by
    rw [m₁]
    have hm := List.mem_singleton_self (⟨w64 p.W + BitVec.ofNat 64 hlO, 16⟩ : Region)
    exact Proof.Ocb.blockAtMem_frame (((Frame.refl _ _).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 276)
      (n := 4) (by decide) (by decide) (by decide))).writeW hm _ (Offset.contains _ (e := 264) (k := 16) (d := 264)
      (n := 4) (by decide) (by decide) (by decide))) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl h) (by omega) (by decide)
  refine WP.of_runBlock ⟨s₁, run₁, ⟨E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.ebp])
      (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁ (wR_mut (hashR_wR fH)), fH,
      rd₁, wr₁, Nat.zero_le _, ?_, ?_, by rw [si₁]; exact (BitVec.add_zero _).symm, di₁, ?_, ?_, ?_⟩, zf₁⟩
  · have fz0 : ∀ (m : Mem) (c : Addr), Frame [⟨c, 16⟩] m (Proof.Cmac.zero4 m c) :=
      fun m c => Proof.Cmac.frame_store4 _ _ _ _ _
    rw [kz (by decide), Proof.Ocb.blockAtMem_frame (fz0 _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)),
      blockAtMem_zero4]; rfl
  · rw [kz (by decide), blockAtMem_zero4]; rfl
  · rw [slotv_eq, m₁, Mem.readW_writeW_self32, Nat.sub_zero]
  · rw [slotv_eq, m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [kz (by decide), Proof.Ocb.blockAtMem_frame fz (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.w_w (by decide) (by decide) (by decide)), hl0]

/-- The chunks of `HASH`, from the first. -/
theorem hashLoop_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) {t : State} (H₀ : HInv p ciph l a s₀ t 0) (hm : 0 < p.al / 16) :
    WP isa (.loop (hashChunk (callees v)) .ne) t fun u => HInv p ciph l a s₀ u (p.al / 16) := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ HInv p ciph l a s₀ u j) ?_
    (p.al / 16 - 0) _ ⟨0, rfl, hm, H₀⟩
  rintro k u ⟨j, rfl, hj, H⟩
  refine WP.mono (hashChunk_ok v C H hj) fun u' ⟨H', hz⟩ => ?_
  by_cases he : p.al / 16 - (j + min 8 (p.al / 16 - j)) = 0
  · left
    have hje : j + min 8 (p.al / 16 - j) = p.al / 16 := by omega
    exact ⟨(eval_ne hz).trans (by simp [he]), hje ▸ H'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.al / 16 - (j + min 8 (p.al / 16 - j)), by omega,
      j + min 8 (p.al / 16 - j), rfl, by omega, H'⟩

theorem hash_ok (v : BlocksImpl) {p : Prm} {ciph : Cipher} {l : Block} {a : List Byte} {s₀ : State}
    (C : HCtx p ciph l a s₀) (E : Env p s₀) (hl0 : blockAtMem s₀.mem (w64 p.W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (Impl.AesOcb.X86.hash (callees v)) s₀ fun t' => Env p t' ∧ Frame (hashR p) s₀.mem t'.mem ∧
      blockAtMem t'.mem (w64 p.W + BitVec.ofNat 64 sumO) = Spec.Ocb.hash ciph l a ∧ t'.rd = s₀.rd ∧
      t'.wr = s₀.wr := by
  unfold Impl.AesOcb.X86.hash
  refine WP.seq (WP.mono (hashHead_ok C E hl0) fun s₃ ⟨H₀, zf₃⟩ => ?_)
  refine WP.seq (WP.ite (decide (p.al / 16 = 0)) (eval_e zf₃) (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : p.al / 16 = 0 := of_decide_eq_true hb
    exact hashTail_ok v C (h0 ▸ H₀)
  · exact WP.mono (hashLoop_ok v C H₀ (Nat.pos_of_ne_zero (of_decide_eq_false hb))) fun u H => hashTail_ok v C H

end VG.Proof.AesOcb.X86
