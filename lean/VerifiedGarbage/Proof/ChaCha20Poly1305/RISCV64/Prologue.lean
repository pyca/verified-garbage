module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Entry
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Poly1305.Spec
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64

/-!
# ChaCha20-Poly1305 on RISC-V: the prologue

Saving the registers, moving the arguments, and the ChaCha20 state for
counter 0, the zeros of the padding and the lengths block in the context,
byte by byte.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.RISCV64.Steps VG.RISCV64.Bytes VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes)
open VG.Spec.ChaCha20 (stateAt initState)

variable {e : Bool}

/-! ## The ChaCha20 state from its bytes -/

/-- A 16-word state whose bytes are the constants, a key, a counter and a nonce. -/
theorem stateAt_init {m : Mem} {p : Addr} {key nonce : List Byte} {c : Spec.ChaCha20.Word}
    (hσ : ∀ i < 16, m (off p i) = Proof.ChaCha20.sigma.getD i 0)
    (hK : ∀ i < 32, m (off p (16 + i)) = key.getD i 0)
    (hc : ∀ i < 4, m (off p (48 + i)) = c.extractLsb' (8 * i) 8)
    (hN : ∀ i < 12, m (off p (52 + i)) = nonce.getD i 0) :
    stateAt m p = initState key c nonce := by
  apply Vector.ext; intro j hj
  simp only [initState, Vector.getElem_ofFn]
  by_cases h4 : j < 4
  · simp only [h4, ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := Proof.ChaCha20.sigma)
      fun i hi => hσ _ (by omega), Proof.ChaCha20.sigma_words j h4]
  simp only [h4, ↓reduceIte]
  by_cases h12 : j < 12
  · simp only [h12, ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := List.replicate 16 0 ++ key) fun i hi => ?_,
      Proof.ChaCha20.wordLE_append_right (a := 4) (by simp) (by omega)]
    rw [Proof.ChaCha20.getD_append_right (by simp; omega), List.length_replicate]
    have := hK (4 * j + i - 16) (by omega)
    rwa [show 16 + (4 * j + i - 16) = 4 * j + i by omega] at this
  simp only [h12, ↓reduceIte]
  by_cases h' : j = 12
  · subst h'
    simp only [stateAt, Vector.getElem_ofFn]
    refine Proof.ChaCha20.word_ext fun i hi => ?_
    rw [← Mem.readW_byte m _ hi, Offset.add_add]
    exact hc i hi
  · simp only [h', ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := List.replicate 52 0 ++ nonce) fun i hi => ?_,
      Proof.ChaCha20.wordLE_append_right (a := 13) (by simp) (by omega)]
    rw [Proof.ChaCha20.getD_append_right (by simp; omega), List.length_replicate]
    have := hN (4 * j + i - 52) (by omega)
    rwa [show 52 + (4 * j + i - 52) = 4 * j + i by omega] at this

/-! ## Memory of the context -/

/-- A doubleword of the context after a doubleword written elsewhere in it. -/
theorem slot_other (s₀ : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a + 8 ≤ 608) (hb : b + 8 ≤ 608) :
    (m.writeW (off (cx s₀) b) v).readW (off (cx s₀) a) 64 = m.readW (off (cx s₀) a) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

/-- A byte of the context outside a part written. -/
theorem byte_sub (s₀ : State) {m m' : Mem} {k n i : Nat} (hf : Frame [sub s₀ k n] m m')
    (h : i + 1 ≤ k ∨ k + n ≤ i) (hk : k + n ≤ 608) (hi : i < 608) :
    m' (off (cx s₀) i) = m (off (cx s₀) i) :=
  hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (cx s₀) h (by omega) (by omega) _ (Region.contains_self _ _) hc

theorem fw_sub (s₀ : State) {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 608) :
    Frame [wR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sub_work s₀ h⟩

theorem sv_sub (s₀ : State) {m m' : Mem} {k n : Nat} (h : Saved s₀ m) (hf : Frame [sub s₀ k n] m m')
    (hk : k + n ≤ savOff) : Saved s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by simp only [savOff] at hk ⊢; omega) (by decide) (by simp only [savOff] at hk ⊢; omega)

/-- A byte of a region apart from the working space, through a frame of it. -/
theorem byte_out (s₀ : State) {m m' : Mem} (hf : Frame [wR s₀] m m') {R : Region} (hd : R.Disjoint (wR s₀))
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  hf.bytes (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi

/-! ## Saving the registers -/

/-- After `save`. -/
structure PostS (s₀ s : State) : Prop where
  t0 : s.gpr .t0 = cx s₀
  gpr : ∀ r, r ≠ .t0 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [sub s₀ savOff 48] s₀.mem s.mem

theorem save_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, PostS s₀ s → WP isa (.block rest) s Q) : WP isa (.block (save ++ rest)) s₀ Q := by
  simp only [save, List.cons_append]
  refine wp_addi (imm := 7) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ => ?_
  have t0 : s₂.gpr .t0 = cx s₀ := by rw [u₂.gpr, u₁.gpr]; exact align_eq _
  have g₂ : ∀ r, r ≠ .t0 → s₂.gpr r = s₀.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have hin : ∀ d, d + 8 ≤ 48 → InRegions s₂.wr (off (cx s₀) (savOff + d)) 8 := fun d hd => by
    rw [w₂]; exact hp.in_w (by simp only [savOff]; omega)
  have hal : ∀ d, d % 8 = 0 → (off (cx s₀) (savOff + d)).toNat % 8 = 0 := fun d hd =>
    cx_al s₀ (by simp only [savOff]; omega)
  refine wp_sd (a := off (cx s₀) (savOff + 0)) (by decide) (by rw [t0]; rfl) (hal 0 (by decide))
    (hin 0 (by decide)) fun s₃ g₃ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 8)) (by decide) (by rw [g₃.gpr, t0]) (hal 8 (by decide))
    (by rw [g₃.wr]; exact hin 8 (by decide)) fun s₄ g₄ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 16)) (by decide) (by rw [g₄.gpr, g₃.gpr, t0])
    (hal 16 (by decide)) (by rw [g₄.wr, g₃.wr]; exact hin 16 (by decide)) fun s₅ g₅ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 24)) (by decide) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 24 (by decide)) (by rw [g₅.wr, g₄.wr, g₃.wr]; exact hin 24 (by decide)) fun s₆ g₆ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 32)) (by decide) (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 32 (by decide)) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr]; exact hin 32 (by decide)) fun s₇ g₇ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 40)) (by decide)
    (by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 40 (by decide)) (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr]; exact hin 40 (by decide))
    fun s₈ g₈ => k s₈ ?_
  have eg : s₈.gpr = s₂.gpr := by rw [g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr]
  have em : s₈.mem = ((((((s₂.mem.writeW (off (cx s₀) (savOff + 0)) (s₀.gpr .s7)).writeW
      (off (cx s₀) (savOff + 8)) (s₀.gpr .s8)).writeW (off (cx s₀) (savOff + 16)) (s₀.gpr .s9)).writeW
      (off (cx s₀) (savOff + 24)) (s₀.gpr .s10)).writeW (off (cx s₀) (savOff + 32)) (s₀.gpr .s11)).writeW
      (off (cx s₀) (savOff + 40)) (s₀.gpr .ra)) := by
    rw [g₈.mem, g₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr,
      g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide), g₂ _ (by decide),
      g₂ _ (by decide)]
  have hm₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [eg, t0], fun r hr => by rw [eg, g₂ r hr], by rw [g₈.sp, g₇.sp, g₆.sp, g₅.sp, g₄.sp,
    g₃.sp, u₂.sp, u₁.sp], by rw [g₈.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, u₂.rd, u₁.rd],
    by rw [g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, w₂], ?_, ?_⟩
  · rw [em]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [slot_other, Mem.readW_writeW_self64, Nat.add_zero]
  · rw [em, hm₂]
    have c : ∀ d, d + 8 ≤ 48 → (sub s₀ savOff 48).Contains (off (cx s₀) (savOff + d)) (64 / 8) :=
      fun d hd => contains_sub s₀ (by omega) (by simp only [savOff]; omega) (by decide)
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
      (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide))).writeW (List.mem_singleton_self _) _
      (c 40 (by decide))


/-! ## The prologue -/

/-- After the prologue. -/
structure PostP (s₀ s : State) : Prop where
  inv : Inv s₀ s
  a0 : s.gpr .a0 = cx s₀
  fw : Frame [wR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)
  zero : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0
  lens : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)

open VG.Impl.ChaCha20.RISCV64.Stream (sigmaBytes) in
open VG.Proof.ChaCha20.RISCV64.Stream (sigmaBytes_lt sigmaBytes_length sigmaBytes_eq) in
theorem prologue_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ setup)) s₀ (PostP s₀) := by
  rw [List.append_assoc]
  refine save_ok hp fun sa ha => ?_
  simp only [moves, mov, List.cons_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun sb u₅ => ?_
  have gb : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → sb.gpr r = sa.gpr r :=
    fun r h7 h8 h9 h10 h11 => by rw [u₅.other r h11, u₄.other r h10, u₃.other r h9, u₂.other r h8, u₁.other r h7]
  have rb : Regs s₀ sb :=
    ⟨by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.gpr, ha.gpr _ (by decide)],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
        u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), ha.gpr _ (by decide)]⟩
  have mb : sb.mem = sa.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rdb : sb.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, ha.rd]
  have wrb : sb.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, ha.wr]
  have spb : sb.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, ha.sp]
  have t0b : sb.gpr .t0 = cx s₀ := by rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide), ha.t0]
  have a0b : sb.gpr .a0 = kp s₀ := by
    rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide), ha.gpr _ (by decide)]
  have a1b : sb.gpr .a1 = np s₀ := by
    rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide), ha.gpr _ (by decide)]
  have fb : Frame [wR s₀] s₀.mem sb.mem := by rw [mb]; exact fw_sub s₀ ha.frame (by decide)
  -- The constants.
  rw [List.nil_append]
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok (tmp := .t1) (dst := .t0) (doff := 0) (bs := sigmaBytes) (by decide)
    sigmaBytes_lt (by decide) (fun i hi => by
      rw [t0b, wrb]; exact hp.in_w (by rw [sigmaBytes_length] at hi; omega))) fun sc hc => ?_
  have t0c : sc.gpr .t0 = cx s₀ := by rw [hc.gpr _ (by decide), t0b]
  have fc : Frame [sub s₀ 0 16] sb.mem sc.mem := by have := hc.frame; rwa [t0b, sigmaBytes_length] at this
  have σc : ∀ j < 16, sc.mem (off (cx s₀) j) = Proof.ChaCha20.sigma.getD j 0 := fun j hj => by
    have := hc.stored j (by rw [sigmaBytes_length]; exact hj)
    rw [t0b, Nat.zero_add] at this
    rw [this, sigmaBytes_eq j hj]
  -- The key.
  rw [WP.block_append_iff]
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a0) (dst := .t0) (soff := 0) (doff := 16) (n := 32)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [hc.gpr _ (by decide), a0b, hc.rd, rdb]
      exact ⟨kR s₀, List.mem_append_left _ hp.k_rd, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [t0c, hc.wr, wrb]; exact hp.in_w (by omega))
    (fun i hi hcon => by
      rw [t0c, hc.gpr _ (by decide), a0b] at hcon
      exact hp.k_w _ (Offset.contains_base _ (by omega) (by omega)) (sub_work s₀ (k := 16) (n := 32)
        (by decide) _ hcon))) fun sd hd => ?_
  have t0d : sd.gpr .t0 = cx s₀ := by rw [hd.gpr _ (by decide), t0c]
  have fd : Frame [sub s₀ 16 32] sc.mem sd.mem := by have := hd.frame; rwa [t0c] at this
  have fwc : Frame [wR s₀] s₀.mem sc.mem := fb.trans (fw_sub s₀ fc (by decide))
  have kd : ∀ j < 32, sd.mem (off (cx s₀) (16 + j)) = (K s₀).getD j 0 := fun j hj => by
    have := hd.copied j hj
    rw [t0c, hc.gpr _ (by decide), a0b, Nat.zero_add] at this
    rw [this, byte_out s₀ fwc (R := kR s₀) hp.k_w (by show 32 ≤ 2 ^ 64; decide) hj]
    exact (Proof.ChaCha20.bytesAt_getD _ _ hj).symm
  -- The counter.
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok (tmp := .t1) (dst := .t0) (doff := 48) (bs := [0, 0, 0, 0]) (by decide)
    (by decide) (by decide) (fun i hi => by
      rw [t0d, hd.wr, hc.wr, wrb]; exact hp.in_w (by simp at hi; omega))) fun se he => ?_
  have t0e : se.gpr .t0 = cx s₀ := by rw [he.gpr _ (by decide), t0d]
  have fe : Frame [sub s₀ 48 4] sd.mem se.mem := by have := he.frame; rwa [t0d] at this
  have ce : ∀ j < 4, se.mem (off (cx s₀) (48 + j)) = (0 : Spec.ChaCha20.Word).extractLsb' (8 * j) 8 :=
    fun j hj => by
      have := he.stored j (by simpa using hj)
      rw [t0d] at this
      rw [this]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  -- The nonce.
  rw [WP.block_append_iff]
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a1) (dst := .t0) (soff := 0) (doff := 52) (n := 12)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b, he.rd, hd.rd, hc.rd, rdb]
      exact ⟨nR s₀, List.mem_append_left _ hp.n_rd, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => by rw [t0e, he.wr, hd.wr, hc.wr, wrb]; exact hp.in_w (by omega))
    (fun i hi hcon => by
      rw [t0e, he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b] at hcon
      exact hp.n_w _ (Offset.contains_base _ (by omega) (by omega)) (sub_work s₀ (k := 52) (n := 12)
        (by decide) _ hcon))) fun sf hf => ?_
  have t0f : sf.gpr .t0 = cx s₀ := by rw [hf.gpr _ (by decide), t0e]
  have ff : Frame [sub s₀ 52 12] se.mem sf.mem := by have := hf.frame; rwa [t0e] at this
  have fwe : Frame [wR s₀] s₀.mem se.mem :=
    (fwc.trans (fw_sub s₀ fd (by decide))).trans (fw_sub s₀ fe (by decide))
  have nf : ∀ j < 12, sf.mem (off (cx s₀) (52 + j)) = (N s₀).getD j 0 := fun j hj => by
    have := hf.copied j hj
    rw [t0e, he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b, Nat.zero_add] at this
    rw [this, byte_out s₀ fwe (R := nR s₀) hp.n_w (by show 12 ≤ 2 ^ 64; decide) hj]
    exact (Proof.ChaCha20.bytesAt_getD _ _ hj).symm
  -- The padding, the lengths block and the context into `a0`.
  have wrf : sf.wr = s₀.wr := by rw [hf.wr, he.wr, hd.wr, hc.wr, wrb]
  have hin : ∀ d, d + 8 ≤ 32 → InRegions sf.wr (off (cx s₀) (zeroOff + d)) 8 := fun d hd => by
    rw [wrf]; exact hp.in_w (by simp only [zeroOff]; omega)
  refine wp_li (imm := 0) (by decide) fun sg ug => ?_
  have t0g : sg.gpr .t0 = cx s₀ := by rw [ug.other _ (by decide), t0f]
  refine wp_sd (a := off (cx s₀) zeroOff) (by decide) (by rw [t0g]) (cx_al s₀ (by decide))
    (by rw [ug.wr]; simpa using hin 0 (by decide)) fun sh gh => ?_
  refine wp_sd (a := off (cx s₀) (zeroOff + 8)) (by decide) (by rw [gh.gpr, t0g]) (cx_al s₀ (by decide))
    (by rw [gh.wr, ug.wr]; exact hin 8 (by decide)) fun si gi => ?_
  refine wp_sd (a := off (cx s₀) lenOff) (by decide) (by rw [gi.gpr, gh.gpr, t0g]) (cx_al s₀ (by decide))
    (by rw [gi.wr, gh.wr, ug.wr]; exact hin 16 (by decide)) fun sj gj => ?_
  refine wp_sd (a := off (cx s₀) (lenOff + 8)) (by decide) (by rw [gj.gpr, gi.gpr, gh.gpr, t0g])
    (cx_al s₀ (by decide)) (by rw [gj.wr, gi.wr, gh.wr, ug.wr]; exact hin 24 (by decide)) fun sk gk₀ => ?_
  refine wp_mv fun sl ul => WP.block_nil ?_
  -- What the registers hold.
  have gk : ∀ r, r ≠ .t1 → sk.gpr r = sb.gpr r := fun r hr => by
    rw [gk₀.gpr, gj.gpr, gi.gpr, gh.gpr, ug.other r hr, hf.gpr r hr, he.gpr r hr, hd.gpr r hr, hc.gpr r hr]
  have gl : ∀ r, r ≠ .t1 → r ≠ .a0 → sl.gpr r = sb.gpr r := fun r h1 h0 => by rw [ul.other r h0, gk r h1]
  have v1 : sg.gpr .t1 = 0 := ug.gpr
  have v8 : sg.gpr .s8 = s₀.gpr .a3 := by rw [ug.other _ (by decide), hf.gpr _ (by decide),
    he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), rb.s8]
  have v10 : sg.gpr .s10 = s₀.gpr .a5 := by rw [ug.other _ (by decide), hf.gpr _ (by decide),
    he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), rb.s10]
  have ml : sl.mem = (((sf.mem.writeW (off (cx s₀) zeroOff) (0 : BitVec 64)).writeW (off (cx s₀) (zeroOff + 8))
      (0 : BitVec 64)).writeW
      (off (cx s₀) lenOff) (s₀.gpr .a3)).writeW (off (cx s₀) (lenOff + 8)) (s₀.gpr .a5) := by
    rw [ul.mem, gk₀.mem, gj.mem, gi.mem, gh.mem, ug.mem, gj.gpr, gi.gpr, gh.gpr, v1, v8, v10]
  have fk : Frame [sub s₀ zeroOff 32] sf.mem sl.mem := by
    rw [ml]
    have c : ∀ d, d + 8 ≤ 32 → (sub s₀ zeroOff 32).Contains (off (cx s₀) (zeroOff + d)) (64 / 8) :=
      fun d hd => contains_sub s₀ (by omega) (by simp only [zeroOff]; omega) (by decide)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
      (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))
  have fwl : Frame [wR s₀] s₀.mem sl.mem :=
    (fwe.trans (fw_sub s₀ ff (by decide))).trans (fw_sub s₀ fk (by decide))
  have r0 : sl.mem.readW (off (cx s₀) zeroOff) 64 = 0 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r1 : sl.mem.readW (off (cx s₀) (zeroOff + 8)) 64 = 0 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r2 : sl.mem.readW (off (cx s₀) lenOff) 64 = s₀.gpr .a3 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r3 : sl.mem.readW (off (cx s₀) (lenOff + 8)) 64 = s₀.gpr .a5 := by
    rw [ml, Mem.readW_writeW_self64]
  -- The bytes of the ChaCha20 state, from the part that wrote each.
  have early : ∀ i < 64, sl.mem (off (cx s₀) i) = sf.mem (off (cx s₀) i) := fun i hi =>
    byte_sub s₀ fk (by simp only [zeroOff]; omega) (by decide) (by omega)
  have hst : stateAt sl.mem (cx s₀) = initState (K s₀) 0 (N s₀) := by
    refine stateAt_init (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · rw [early i (by omega), byte_sub s₀ ff (by omega) (by decide) (by omega),
        byte_sub s₀ fe (by omega) (by decide) (by omega), byte_sub s₀ fd (by omega) (by decide) (by omega),
        σc i hi]
    · rw [early _ (by omega), byte_sub s₀ ff (by omega) (by decide) (by omega),
        byte_sub s₀ fe (by omega) (by decide) (by omega), kd i hi]
    · rw [early _ (by omega), byte_sub s₀ ff (by omega) (by decide) (by omega), ce i hi]
    · rw [early _ (by omega), nf i hi]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_, ?_, ?_, fwl.mono (by simp)⟩, ?_, fwl, hst, ?_, ?_⟩
  · rw [gl _ (by decide) (by decide), rb.s7]
  · rw [gl _ (by decide) (by decide), rb.s8]
  · rw [gl _ (by decide) (by decide), rb.s9]
  · rw [gl _ (by decide) (by decide), rb.s10]
  · rw [gl _ (by decide) (by decide), rb.s11]
  · have h : r ≠ .t1 ∧ r ≠ .a0 ∧ r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 ∧ r ≠ .s10 ∧ r ≠ .s11 ∧ r ≠ .t0 := by
      revert r; decide
    rw [gl r h.1 h.2.1, gb r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1,
      ha.gpr r h.2.2.2.2.2.2.2]
  · rw [ul.sp, gk₀.sp, gj.sp, gi.sp, gh.sp, ug.sp, hf.sp, he.sp, hd.sp, hc.sp, spb]
  · rw [ul.rd, gk₀.rd, gj.rd, gi.rd, gh.rd, ug.rd, hf.rd, he.rd, hd.rd, hc.rd, rdb]
  · rw [ul.wr, gk₀.wr, gj.wr, gi.wr, gh.wr, ug.wr, wrf]
  · refine sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (by rw [mb]; exact ha.saved) fc (by decide))
      fd (by decide)) fe (by decide)) ff (by decide)) fk (by decide)
  · rw [ul.gpr, gk _ (by decide), t0b]
  · intro i hi
    rcases (by omega : i < 8 ∨ 8 ≤ i) with h | h
    · rw [← off_off (cx s₀) zeroOff i, ← Proof.ChaCha20.readW64_byte sl.mem (off (cx s₀) zeroOff) h, r0]; simp
    · rw [show zeroOff + i = zeroOff + 8 + (i - 8) by omega, ← off_off (cx s₀) (zeroOff + 8) (i - 8),
        ← Proof.ChaCha20.readW64_byte sl.mem (off (cx s₀) (zeroOff + 8)) (show i - 8 < 8 by omega), r1]; simp
  · rw [show (16 : Nat) = 8 + 8 from rfl, Proof.Poly1305.bytesAt_add, Proof.Poly1305.bytesAt_leBytes_64,
      Proof.Poly1305.bytesAt_leBytes_64, r2]
    have r3' : sl.mem.readW (off (cx s₀) lenOff + BitVec.ofNat 64 8) 64 = s₀.gpr .a5 := by
      rw [Offset.add_add (cx s₀) lenOff 8]; exact r3
    rw [r3']

end VG.Proof.ChaCha20Poly1305.RISCV64
