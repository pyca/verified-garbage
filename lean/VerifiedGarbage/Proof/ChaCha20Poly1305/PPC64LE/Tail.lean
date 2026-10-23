module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Mac
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp

/-!
# ChaCha20-Poly1305 on PPC64LE: the other parts

The encryption, the lengths block, the arguments of
`vg_poly1305_finalize_scratch` and the tag, restoring the registers, and
comparing tags.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

theorem lenOff_eq : lenOff = 432 := rfl
theorem tagOff_eq : tagOff = 448 := rfl
theorem scrOff_eq : scrOff = 520 := rfl

/-! ## Encrypting -/

theorem set12_initState (key nonce : List Byte) :
    (Spec.ChaCha20.initState key 0 nonce).set 12 1 = Spec.ChaCha20.initState key 1 nonce := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_set, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  by_cases h : 12 = i
  · subst h; simp
  · simp only [h, ite_false, show ¬ i = 12 from fun h' => h h'.symm]

theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (off p 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (d := 4 * i) (by omega) (by decide) (by omega)

theorem cryptA_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.li .r12 1, .store .w .r12 .r24 (stOff + 48), .addi .r3 .r24 stOff, mov .r4 .r27,
      mov .r5 .r28, mov .r6 .r24]) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 48)) (1 : BitVec 32) ∧ s'.gpr .r3 = off (cx s₀) stOff ∧
      s'.gpr .r4 = dp s₀ ∧ s'.gpr .r5 = s₀.gpr .r8 ∧ s'.gpr .r6 = cx s₀ ∧
      Kept [sub s₀ (stOff + 48) 4] s s' := by
  have h14 := h.regs.r24
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_stw (a := off (cx s₀) (stOff + 48)) (by decide) (by decide) (by rw [u₁.other _ (by decide), h14])
    (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ u₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), h14]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.regs.r27]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.regs.r28]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h14]
  · refine ⟨fun r hr => ?_, by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp],
      by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_⟩
    · rw [u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr),
        u₃.other _ (ne_of_pres hr), u₂.gpr, u₁.other _ (ne_of_pres hr)]
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (contains_sub s₀ (w := 32 / 8) (by omega) (by omega) (by decide))

theorem length_encrypt (key nonce m : List Byte) : (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

/-- The data encrypted (or decrypted) from block counter 1, with the ChaCha20
state for counter 0 at `ctx + stOff`. -/
theorem crypt_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 (stOff + 64), dR s₀] s s' ∧
      bytesAt s'.mem (dp s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold crypt
  refine WP.seq (WP.mono (cryptA_ok hp h) fun s₁ ⟨m₁, h3, h4, h5, h6, k₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by decide) (by decide)
  have hw : Covers [⟨off (cx s₀) stOff, 64⟩, ⟨dp s₀, L s₀⟩, ⟨cx s₀, 320⟩] s₁.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, stOff, rfl, by exact (by decide : stOff + 64 ≤ 648)⟩
    · exact ⟨dR s₀, by rw [i₁.wr]; exact hp.d_wr, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨ctxR s₀, by rw [i₁.wr]; exact hp.ctx_wr, 0, (BitVec.add_zero _).symm,
        by exact (by decide : 0 + 320 ≤ 648)⟩
  have hL : s₀.gpr .r8 = BitVec.ofNat 64 (L s₀) := by simp [L]
  have hcv : Covers ([] ++ [⟨off (cx s₀) stOff, 64⟩, ⟨dp s₀, L s₀⟩, ⟨cx s₀, 320⟩]) (s₁.rd ++ s₁.wr) := by
    rw [List.nil_append]; exact covers_right hw
  have hSD : (⟨off (cx s₀) stOff, 64⟩ : Region).Disjoint ⟨dp s₀, L s₀⟩ :=
    hp.d_c.symm.sub_left (sub_ctx s₀ (by decide))
  have hSB : (⟨off (cx s₀) stOff, 64⟩ : Region).Disjoint ⟨cx s₀, 320⟩ := by
    rw [← sub_zero s₀ 320]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have hDB : (⟨dp s₀, L s₀⟩ : Region).Disjoint ⟨cx s₀, 320⟩ := by
    rw [← sub_zero s₀ 320]; exact hp.d_c.sub_right (sub_ctx s₀ (by decide))
  have h5' : s₁.gpr .r5 = BitVec.ofNat 64 (L s₀) := by rw [h5, hL]
  refine xor_call h3 h4 h5' h6 (s₀.gpr .r8).isLt hSD hSB hDB hp.fit_d hcv hw
    fun s₂ k₂ data₂ => ?_
  have hsub : ∀ r ∈ [(⟨off (cx s₀) stOff, 64⟩ : Region), ⟨dp s₀, L s₀⟩, ⟨cx s₀, 320⟩],
      ∃ r' ∈ [sub s₀ 0 (stOff + 64), dR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub (cx s₀) (by decide) (by decide)⟩
    · exact ⟨dR s₀, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      rw [← sub_zero s₀ 320]; exact Offset.sub (cx s₀) (by decide) (by decide)
  have k₁₂ : Kept [sub s₀ 0 (stOff + 64), dR s₀] s s₂ :=
    (k₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub (cx s₀) (by decide) (by decide)⟩).trans (k₂.sub hsub)
  have i₂ := h.step k₁₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩
      · exact ⟨dR s₀, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by decide) (by decide) (by decide)
      · exact (hp.d_c.sub_right (sub_ctx s₀ (by decide))).symm)
  refine ⟨i₂, k₁₂, ?_⟩
  have d₁ : bytesAt s₁.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
    bytesAt_frame k₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.d_c.sub_right (sub_ctx s₀ (by decide)))
      (Nat.le_of_lt (s₀.gpr .r8).isLt)
  have st₁ : stateAt s₁.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
    rw [m₁, show off (cx s₀) (stOff + 48) = off (off (cx s₀) stOff) 48 from (off_off _ _ _).symm,
      stateAt_writeW_counter, hst, set12_initState]
  rw [show Spec.ChaCha20.bytesAt = bytesAt from rfl] at data₂
  rw [data₂, st₁, d₁, encrypt_eq, VG.Proof.Poly1305.length_bytesAt]

/-! ## The lengths block -/

theorem lengthsA_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block [.store .d .r26 .r24 lenOff, .store .d .r28 .r24 (lenOff + 8), .addi .r4 .r24 lenOff,
      .li .r5 1]) s fun s' =>
      s'.gpr .r4 = off (cx s₀) lenOff ∧ s'.gpr .r5 = BitVec.ofNat 64 1 ∧ Kept [sub s₀ lenOff 16] s s' ∧
      bytesAt s'.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
  have h14 := h.regs.r24
  refine wp_std (a := off (cx s₀) lenOff) (by decide) (by decide) (by rw [h14])
    (by rw [h.wr]; exact hp.in_ctx (by decide)) fun s₁ g₁ => ?_
  refine wp_std (a := off (cx s₀) (lenOff + 8)) (by decide) (by decide) (by rw [g₁.gpr, h14])
    (by rw [g₁.wr, h.wr]; exact hp.in_ctx (by decide)) fun s₂ g₂ => ?_
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, g₁.gpr, h14]
  · rw [u₄.gpr]
  · refine ⟨fun r hr => by rw [u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), g₂.gpr, g₁.gpr],
      by rw [u₄.sp, u₃.sp, g₂.sp, g₁.sp], by rw [u₄.rd, u₃.rd, g₂.rd, g₁.rd], by rw [u₄.wr, u₃.wr, g₂.wr, g₁.wr], ?_⟩
    rw [u₄.mem, u₃.mem, g₂.mem, g₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega) (by omega) (by decide))
  · rw [u₄.mem, u₃.mem, g₂.mem, g₁.mem, g₁.gpr, show (16 : Nat) = 8 + 8 from rfl, VG.Proof.Poly1305.bytesAt_add,
      VG.Proof.Poly1305.bytesAt_leBytes_64, VG.Proof.Poly1305.bytesAt_leBytes_64, off_add,
      readW_writeW_off _ _ _ (d := lenOff) (e := lenOff + 8) (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64, Mem.readW_writeW_self64, h.regs.r26, h.regs.r28]

theorem lengths_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa lengths s fun s' => Inv s₀ s' ∧ Kept (macR s₀ ++ [sub s₀ lenOff 16]) s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg →
        Repr s'.mem (cx s₀) key (msg ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))) := by
  unfold lengths
  refine WP.seq (WP.mono (lengthsA_ok hp h) fun s₁ ⟨h4, h5, k₁, len₁⟩ => ?_)
  have i₁ := h.step1 k₁ (by decide) (by decide)
  have hdj : (sub s₀ 0 128).Disjoint ⟨off (cx s₀) lenOff, 16 * 1⟩ := sub_disj s₀ (by decide) (by decide) (by decide)
  have hbp : (belR s₀).Disjoint ⟨off (cx s₀) lenOff, 16 * 1⟩ := hp.b_c.sub_right (sub_ctx s₀ (by decide))
  have hfit : (off (cx s₀) lenOff).toNat + 16 * 1 ≤ 2 ^ 64 := by
    have := hp.fit_c; rw [off_toNat _ (by rw [lenOff_eq]; omega), lenOff_eq]; omega
  have hc : Covers [(⟨off (cx s₀) lenOff, 16 * 1⟩ : Region)] (s₀.rd ++ s₀.wr) :=
    covers_right (covers1 hp rfl (a := lenOff) (n := 16 * 1) (by decide))
  refine WP.mono (absorb_ok hp i₁ (n := 1) h4 h5 (by decide) hdj hbp hfit hc)
    fun s₂ ⟨i₂, k₂, repr₂⟩ => ⟨i₂, ?_, fun key msg hr => ?_⟩
  · exact (k₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩).trans
      (k₂.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩)
  have hr₁ : Repr s₁.mem (cx s₀) key msg := Repr.frame k₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)) hr
  have := repr₂ key msg hr₁
  rwa [show 16 * 1 = 16 from rfl, len₁] at this

/-! ## The arguments of `vg_poly1305_finalize_scratch` -/

/-- `⌈n / 16⌉` into `d`, through `t`: only `d` and `t` change. -/
theorem ceil16_ok {d t n : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ d → r ≠ t → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) (ht : t ≠ .r0 := by decide) :
    WP isa (.block (ceil16 d t n ++ rest)) s Q := by
  unfold ceil16
  simp only [List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_and fun s₃ u₃ =>
    wp_addi ht (by decide) fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => wp_add fun s₆ u₆ =>
    k s₆ (fun r h₁ h₂ => ?_) ?_ ?_ ?_ ?_
  · rw [u₆.other r h₁, u₅.other r h₂, u₄.other r h₂, u₃.other r h₂, u₂.other r h₂, u₁.other r h₁]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

theorem shl4_mod (x : BitVec 64) : (x <<< 4).toNat % 16 = 0 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- The arguments of `vg_poly1305_finalize_scratch`, with `out` set to `O`
by the instruction `out`. -/
theorem finArgs_ok {s₀ : State} {s : State} (h : Inv s₀ s) {out : Instr} {O : Addr}
    (hout : ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 O → WP isa (.block rest) t' Q) →
      WP isa (.block (out :: rest)) t Q) :
    WP isa (.block (finalizeArgs out)) s fun s' => Inv s₀ s' ∧ Kept [] s s' ∧ s'.gpr .r3 = cx s₀ ∧
      s'.gpr .r5 = O ∧ s'.gpr .r6 = off (cx s₀) scrOff ∧ (s'.gpr .r4).toNat % 16 = 0 := by
  unfold finalizeArgs
  rw [List.append_assoc]
  refine ceil16_ok fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ceil16_ok fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have e₂ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r a b c => by
    rw [g₂ r b c, g₁ r a c]
  refine wp_add fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => ?_
  have g14 : s₅.gpr .r24 = cx s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide) (by decide) (by decide), h.regs.r24]
  refine hout s₆ _ _ (by rw [u₆.other _ (by decide), g14])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide) (by decide) (by decide)])
    fun s₇ u₇ => wp_addi (by decide) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have hk : Kept [] s s₈ := ⟨fun r hr => by
      rw [u₈.other _ (ne_of_pres hr), u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), e₂ r (ne_of_pres hr) (ne_of_pres hr) (ne_of_pres hr)],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁], by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁],
    by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, m₁]; exact Frame.refl _ _⟩
  refine ⟨h.step0 hk, hk, ?_, ?_, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g14]
  · rw [u₈.other _ (by decide), u₇.gpr]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g14]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    exact shl4_mod _

/-- `seal`'s `out`: `tag`. -/
theorem out_seal {s₀ s : State} (h : Inv s₀ s) :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 (tp s₀) → WP isa (.block rest) t' Q) →
      WP isa (.block (mov .r5 .r29 :: rest)) t Q := fun _ _ _ _ t19 k =>
  wp_mov fun t' u => k t' ⟨by rw [u.gpr, t19, h.regs.r29], u.other, u.mem, u.rd, u.wr, u.sp, u.lr⟩

/-- `open`'s `out`: the tag computed, in the context. -/
theorem out_open {s₀ s : State} :
    ∀ (t : State) (rest : List Instr) (Q : State → Prop), t.gpr .r24 = cx s₀ →
      t.gpr .r29 = s.gpr .r29 → (∀ t', Upd t t' .r5 (off (cx s₀) tagOff) → WP isa (.block rest) t' Q) →
      WP isa (.block (.addi .r5 .r24 tagOff :: rest)) t Q := fun _ _ _ t14 _ k =>
  wp_addi (by decide) (by decide) fun t' u => k t' ⟨by rw [u.gpr, t14], u.other, u.mem, u.rd, u.wr, u.sp, u.lr⟩

/-! ## The tag -/

/-- Where `out` may be: 16 writable bytes disjoint from the Poly1305 state,
the working space of `vg_poly1305_finalize_scratch` and the saved registers. -/
structure OutOk (s₀ : State) (O : Addr) : Prop where
  dP : (sub s₀ 0 128).Disjoint ⟨O, 16⟩
  dS : (⟨O, 16⟩ : Region).Disjoint (sub s₀ scrOff 128)
  dSv : (sub s₀ savOff 56).Disjoint ⟨O, 16⟩
  w : ∃ r ∈ s₀.wr, ∃ k, O = r.base + BitVec.ofNat 64 k ∧ k + 16 ≤ r.len

/-- `open`'s tag computed. -/
theorem outOk_tag {s₀ : State} (hp : APre e s₀) : OutOk s₀ (off (cx s₀) tagOff) :=
  ⟨sub_disj s₀ (by decide) (by decide) (by decide), sub_disj s₀ (by decide) (by decide) (by decide),
    sub_disj s₀ (by decide) (by decide) (by decide), ⟨ctxR s₀, hp.ctx_wr, tagOff, rfl, by exact (by decide : tagOff + 16 ≤ 648)⟩⟩

/-- `seal`'s `tag`. -/
theorem outOk_tP {s₀ : State} (hp : APre true s₀) : OutOk s₀ (tp s₀) :=
  ⟨hp.t_c.symm.sub_left (sub_ctx s₀ (by decide)), hp.t_c.sub_right (sub_ctx s₀ (by decide)),
    hp.t_c.symm.sub_left (sub_ctx s₀ (by decide)), ⟨tR s₀, hp.t_wr, 0, (BitVec.add_zero _).symm, by exact (by decide : 0 + 16 ≤ 16)⟩⟩

theorem fin_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) {O : Addr} (ho : OutOk s₀ O)
    (h3 : s.gpr .r3 = cx s₀) (h4 : (s.gpr .r4).toNat % 16 = 0) (h5 : s.gpr .r5 = O)
    (h6 : s.gpr .r6 = off (cx s₀) scrOff) :
    WP isa finalize s fun s' =>
      Kept [sub s₀ 0 128, ⟨O, 16⟩, sub s₀ scrOff 128] s s' ∧
      ∀ key msg, Repr s.mem (cx s₀) key msg → bytesAt s'.mem O 16 = mac key msg := by
  have hPO : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨O, 16⟩ := by rw [← sub_zero s₀ 128]; exact ho.dP
  have hPS : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨off (cx s₀) scrOff, 128⟩ := by
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have hw : Covers [⟨cx s₀, 128⟩, ⟨O, 16⟩, ⟨off (cx s₀) scrOff, 128⟩] s.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, 0, (BitVec.add_zero _).symm,
        by exact (by decide : 0 + 128 ≤ 648)⟩
    · obtain ⟨r', hr', k, hk, hl⟩ := ho.w
      exact ⟨r', by rw [h.wr]; exact hr', k, hk, hl⟩
    · exact ⟨ctxR s₀, by rw [h.wr]; exact hp.ctx_wr, scrOff, rfl, by exact (by decide : scrOff + 128 ≤ 648)⟩
  have hc : Covers ([] ++ [⟨cx s₀, 128⟩, ⟨O, 16⟩, ⟨off (cx s₀) scrOff, 128⟩]) (s.rd ++ s.wr) := by
    rw [List.nil_append]; exact covers_right hw
  refine finalize_call h3 rfl h5 h6 hPO hPS ho.dS hc hw fun s' hk htag => ?_
  rw [← sub_zero s₀ 128] at hk
  refine ⟨hk, fun key msg hr => htag key msg (VG.Proof.Poly1305.Repr.buffered hr) ?_⟩
  obtain ⟨hl, _, _⟩ := hr
  rw [h4, hl]

/-! ## Restoring the registers -/

theorem restore_eq : restore = ([mov .r12 .r24, .load .d .r0 .r12 (savOff + 48), .mtlr .r0] : List Instr) ++
    (List.range 6).flatMap fun i => [.load .d (saved i) .r12 (savOff + 8 * i)] := rfl

theorem saved_inj : ∀ i < 6, ∀ j < 6, saved i = saved j → i = j := by decide

theorem r12_ne_saved : ∀ i < 6, Reg.r12 ≠ saved i := by decide

/-- The first `n` registers restored, from the state `sB` the loads start in. -/
structure RI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = cx s₀
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 6, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = sB.lr

theorem restore_step {s₀ sB : State} (hp : APre e s₀) (hrd : sB.rd = s₀.rd) (hwr : sB.wr = s₀.wr)
    (hsv : Saved s₀ sB.mem) {n : Nat} (hn : n < 6) {s : State} (h : RI s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r12 (savOff + 8 * n)]) s (RI s₀ sB (n + 1)) := by
  refine wp_ld (a := off (cx s₀) (savOff + 8 * n)) (by decide) (by rw [savOff_eq]; omega) (by rw [h.r12])
    (by rw [h.rd, h.wr, hrd, hwr]; exact hp.in_ctx' (by rw [savOff_eq]; omega)) fun s' u => WP.block_nil ?_
  refine ⟨by rw [u.other _ (r12_ne_saved n hn), h.r12], fun i hi => ?_, fun r hr => ?_, by rw [u.mem, h.mem],
    by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp], by rw [u.lr, h.lr]⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [u.other _ (fun e => absurd (saved_inj i (by omega) n hn e) (by omega)), h.restored i hi]
    · rw [u.gpr, h.mem, hsv.1 i hn]
  · rw [u.other r (hr n hn), h.others r hr]

/-- Restoring `r24`–`r29` and the return address from `ctx[464, 520)`, through `r12`. -/
theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (h14 : s.gpr .r24 = cx s₀) (hsv : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ i < 6, s'.gpr (saved i) = s₀.gpr (saved i)) ∧ s'.lr = s₀.lr ∧
      (∀ r, (∀ i < 6, r ≠ saved i) → r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ => wp_ld (a := off (cx s₀) (savOff + 48)) (by decide) (by decide)
    (by rw [u₁.gpr, h14]) (by rw [u₁.rd, u₁.wr, hrd, hwr]; exact hp.in_ctx' (by decide)) fun s₂ u₂ =>
    wp_mtlr fun s₃ l₃ => ?_
  have m₃ : s₃.mem = s.mem := by rw [l₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (wp_range_flatMap (M := isa) (RI s₀ s₃)
    (fun k t hk ht => restore_step hp (by rw [l₃.rd, u₂.rd, u₁.rd, hrd]) (by rw [l₃.wr, u₂.wr, u₁.wr, hwr])
      (by rw [m₃]; exact hsv) hk ht) 6 (Nat.le_refl _) s₃
    ⟨by rw [l₃.gpr, u₂.other _ (by decide), u₁.gpr, h14], fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩)
    fun s' h' => ⟨h'.restored, ?_, fun r hr h0 h12 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h'.lr, l₃.lr, u₂.gpr, u₁.mem]; exact hsv.2
  · rw [h'.others r hr, l₃.gpr, u₂.other r h0, u₁.other r h12]
  · rw [h'.mem, m₃]
  · rw [h'.sp, l₃.sp, u₂.sp, u₁.sp]
  · rw [h'.rd, l₃.rd, u₂.rd, u₁.rd]
  · rw [h'.wr, l₃.wr, u₂.wr, u₁.wr]

/-! ## Comparing the tags -/

/-- `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
theorem nz_bit (x : BitVec 64) : (x ||| (BitVec.ofNat 64 0 - x)) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    have hneg : (BitVec.ofNat 64 0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (BitVec.ofNat 64 0).toNat = 0 from rfl]; omega
    have h1 : 2 ^ 63 ≤ (x ||| (BitVec.ofNat 64 0 - x)).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h2 | h2
      · exact Nat.le_trans (by omega) (Nat.right_le_or (n := x.toNat))
      · exact Nat.le_trans h2 Nat.left_le_or
    have h2 := (x ||| (BitVec.ofNat 64 0 - x)).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

theorem sel_eq {x : BitVec 64} {p : Prop} [Decidable p] (h : x = 0 ↔ p) :
    (BitVec.ofNat 64 1 - if x = 0 then 0 else 1) = if p then 1 else 0 := by
  by_cases hp : p
  · have hx : x = 0 := h.mpr hp
    simp only [hx, hp, ↓reduceIte]
    decide
  · have hx : ¬ x = 0 := fun e => hp (h.mp e)
    simp only [hx, hp, ↓reduceIte]
    decide

/-- Doublewords with the same bytes are equal. -/
theorem readW64_eq_of_bytes {m : Mem} {p q : Addr}
    (h : ∀ i < 8, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i)) : m.readW p 64 = m.readW q 64 := by
  have e : m.read p 8 = m.read q 8 :=
    Mem.read_eq_of_bytes fun i hi => by rw [Mem.extractLsb'_read m q hi]; exact h i hi
  simp only [Mem.readW]
  rw [e]

/-- The tags differ in no bit if and only if they are equal. -/
theorem tag_eq (m : Mem) (c t : Addr) :
    ((m.readW (off c tagOff) 64 ^^^ m.readW (off t 0) 64) |||
      (m.readW (off c (tagOff + 8)) 64 ^^^ m.readW (off t 8) 64)) = 0#64 ↔
      bytesAt m (off c tagOff) 16 = bytesAt m t 16 := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine bytes_of_dwords (n := 2) fun k hk => ?_
    match k, hk with
    | 0, _ => exact (congrArg (m.readW · 64) (BitVec.add_zero _)).trans h0
    | 1, _ => rw [off_add]; exact h1
  · intro h
    have hb : ∀ i < 16, m (off c (tagOff + i)) = m (off t i) := fun i hi => by
      have := congrArg (fun l => l.getD i 0) h
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some] at this
      rwa [off_add] at this
    refine ⟨readW64_eq_of_bytes fun i hi => ?_, readW64_eq_of_bytes fun i hi => ?_⟩
    · rw [off_add, off_add, Nat.zero_add]; exact hb i (by omega)
    · rw [off_add, off_add, Nat.add_assoc]; exact hb (8 + i) (by omega)

/-- The tags compared: the one computed, at `ctx + tagOff`, and `tag`. -/
theorem compare_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', s'.gpr .r3 = (if bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 then 1 else 0) →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.lr = s.lr → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.ChaCha20Poly1305.PPC64LE.compare ++ rest)) s Q := by
  unfold Impl.ChaCha20Poly1305.PPC64LE.compare
  simp only [List.cons_append, List.nil_append]
  have h14 := h.regs.r24
  have h19 : s.gpr .r29 = tp s₀ := h.regs.r29
  have ic : ∀ d, d + 8 ≤ 648 → InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.in_ctx' hd
  have it : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (off (tp s₀) d) 8 := fun d hd =>
    ⟨tR s₀, by rw [h.rd]; exact List.mem_append_left _ hp.t_rd, Offset.contains_base _ hd (by omega)⟩
  refine wp_ld (a := off (cx s₀) tagOff) (by decide) (by decide) (by rw [h14]) (ic _ (by decide))
    fun s₁ u₁ => ?_
  refine wp_ld (a := off (tp s₀) 0) (by decide) (by decide) (by rw [u₁.other _ (by decide), h19])
    (by rw [u₁.rd, u₁.wr]; exact it 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := off (cx s₀) (tagOff + 8)) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h14])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact ic _ (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := off (tp s₀) 8) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h19])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact it 8 (by decide)) fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => k s₁₃ ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_ ?_
  · have x₃ : s₃.gpr .r3 = s.mem.readW (off (cx s₀) tagOff) 64 ^^^ s.mem.readW (off (tp s₀) 0) 64 := by
      rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₁.mem]
    have x₆ : s₆.gpr .r4 = s.mem.readW (off (cx s₀) (tagOff + 8)) 64 ^^^ s.mem.readW (off (tp s₀) 8) 64 := by
      rw [u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    have x₇ := u₇.gpr
    rw [u₆.other _ (by decide), x₆, u₅.other _ (by decide), u₄.other _ (by decide), x₃] at x₇
    rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₉.gpr, u₈.gpr,
      u₈.other _ (by decide), x₇, nz_bit]
    exact sel_eq (tag_eq s.mem (cx s₀) (tp s₀))
  · rw [u₁₃.other _ (ne_of_pres hr), u₁₂.other _ (ne_of_pres hr), u₁₁.other _ (ne_of_pres hr), u₁₀.other _ (ne_of_pres hr), u₉.other _ (ne_of_pres hr), u₈.other _ (ne_of_pres hr), u₇.other _ (ne_of_pres hr), u₆.other _ (ne_of_pres hr), u₅.other _ (ne_of_pres hr), u₄.other _ (ne_of_pres hr), u₃.other _ (ne_of_pres hr), u₂.other _ (ne_of_pres hr), u₁.other _ (ne_of_pres hr)]
  · rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₁₃.lr, u₁₂.lr, u₁₁.lr, u₁₀.lr, u₉.lr, u₈.lr, u₇.lr, u₆.lr, u₅.lr, u₄.lr, u₃.lr, u₂.lr, u₁.lr]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.ChaCha20Poly1305.PPC64LE
