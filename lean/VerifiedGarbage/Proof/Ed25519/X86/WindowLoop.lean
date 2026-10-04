import VerifiedGarbage.Proof.Ed25519.X86.WindowStep

/-!
# Verification's windows: the bytes and the loops

After the bytes of the scalars from `i` up, the sum represents
`[k / 256^i]A + [S / 256^i](-B)` (`wsum`). The bytes of `k` above its low 32
have no byte of `S` beside them (`S < 256^32`); its leading zero bytes are
skipped, where the sum is zero.
-/

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Proof.Ed25519 Edwards

abbrev verificationScalar (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 1 + BitVec.ofNat 32 32).setWidth 64) 32)
abbrev verificationChallenge (s : State) : Nat := Spec.Ed25519.decodeLE
  (Spec.Ed25519.bytesAt s.mem ((arg s 2 + BitVec.ofNat 32 0).setWidth 64) 64)

/-- Byte `i` of `k`. -/
abbrev kByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2 + BitVec.ofNat 32 0).setWidth 64) 64).getD i 0

/-- Byte `i` of `S`. -/
abbrev sByte (s₀ : State) (i : Nat) : Byte :=
  (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64) 32).getD i 0

/-- The sum after the bytes from `i` up. -/
def wsum (s₀ : State) (Aa : EPoint dZ) (i : Nat) : EPoint dZ :=
  (verificationChallenge s₀ / 256 ^ i) • Aa + (verificationScalar s₀ / 256 ^ i) • (-baseAff)

theorem kByte_val (s₀ : State) (i : Nat) :
    (kByte s₀ i).toNat = verificationChallenge s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

theorem sByte_val (s₀ : State) (i : Nat) :
    (sByte s₀ i).toNat = verificationScalar s₀ / 256 ^ i % 256 := (decodeLE_byte _ i).symm

theorem nib_lt16 (b : Byte) : b.toNat / 16 < 16 := by have := b.isLt; omega
theorem low_lt16 (b : Byte) : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)

/-- `k`'s digit at byte `i`, from its high (`hi`) or low nibble. -/
theorem digitK_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 64)
    (high : Bool) (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (if high then digitHigh 12 0 else digitLow 12 0)) t fun u => EaxKeep t u ∧
      u.gpr .eax = BitVec.ofNat 32 (if high then (kByte s₀ i).toNat / 16 else (kByte s₀ i).toNat % 16) := by
  cases high
  · exact digitLow_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge hi et
  · exact digitHigh_ok (a := 2) ht.pre.scratch ht.saved (by decide) ht.pre.challenge hi et

theorem digitS_ok {s₀ : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {i : Nat} (hi : i < 32)
    (high : Bool) (t : State) (ht : WinCtx s₀ Aa R t) (et : t.gpr .esi = BitVec.ofNat 32 i) :
    WP isa (.block (if high then digitHigh 8 32 else digitLow 8 32)) t fun u => EaxKeep t u ∧
      u.gpr .eax = BitVec.ofNat 32 (if high then (sByte s₀ i).toNat / 16 else (sByte s₀ i).toNat % 16) := by
  cases high
  · exact digitLow_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar hi et
  · exact digitHigh_ok (a := 1) ht.pre.scratch ht.saved (by decide) ht.pre.scalar hi et

theorem nibble_lt (b : Byte) (high : Bool) : (if high then b.toNat / 16 else b.toNat % 16) < 16 := by
  cases high
  · exact low_lt16 b
  · exact nib_lt16 b

theorem windowA_byte_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 64) (hesi : s.gpr .esi = BitVec.ofNat 32 i)
    (high : Bool) {a : EPoint dZ} (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa (windowA (if high then digitHigh 12 0 else digitLow 12 0)) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        ((16 : Nat) • a + (if high then (kByte s₀ i).toNat / 16 else (kByte s₀ i).toNat % 16) • Aa) :=
  windowWith_ok h (by decide) (by decide) (fun t ht => ht.ta) (nibble_lt _ high)
    (fun t ht et => digitK_ok hi high t ht (et.trans hesi)) hacc

theorem windowAB_byte_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 i)
    (high : Bool) {a : EPoint dZ} (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) a) :
    WP isa (windowAB (if high then digitHigh 12 0 else digitLow 12 0)
        (if high then digitHigh 8 32 else digitLow 8 32)) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        ((16 : Nat) • a + (if high then (kByte s₀ i).toNat / 16 else (kByte s₀ i).toNat % 16) • Aa +
          (if high then (sByte s₀ i).toNat / 16 else (sByte s₀ i).toNat % 16) • (-baseAff)) := by
  refine WP.seq (WP.mono (windowA_byte_ok h (by omega) hesi high hacc) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (digitS_ok hi high b wb (eb.trans hesi)) fun c ⟨kc, ec⟩ => ?_)
  have wc := wb.of_ikeep kc.ikeep (by rw [kc.mem])
  have rc : Rep (point (env c.mem (arg s₀ 3)) 0 1 2 3)
      ((16 : Nat) • a + (if high then (kByte s₀ i).toNat / 16 else (kByte s₀ i).toNat % 16) • Aa) := by
    rw [kc.mem]; exact rb
  refine WP.mono (addDigit_ok wc.ctx (by decide) (by decide) (nibble_lt _ high) ec wc.tb rc wc.d)
    fun t ⟨kt, et, rt, ht⟩ => ⟨wc.of_ikeep kt (ht 16 (by decide)), ?_, rt⟩
  rw [et, kc.gpr _ (by decide)]; exact eb

theorem esiDec_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} (h : WinCtx s₀ Aa R s)
    {i : Nat} (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun u => WinCtx s₀ Aa R u ∧
      u.gpr .esi = BitVec.ofNat 32 i ∧ u.mem = s.mem :=
  Wp.wp_subi fun u hu _ _ => WP.block_nil ⟨h.of_ikeep (IKeep.of_counter hu) (by rw [hu.mem]),
    by rw [hu.gpr, hesi, Wp.ofNat_pred (by omega), Nat.add_sub_cancel], hu.mem⟩

theorem test_zero (i : Nat) (hi : i < 2 ^ 32) :
    (BitVec.ofNat 32 i &&& BitVec.ofNat 32 i == 0) = decide (i = 0) := by
  rw [BitVec.and_self, Wp.ofNat_beq_zero hi]

theorem byteStepAB_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : i < 32) (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa (i + 1))) :
    WP isa byteStepAB s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i = 0)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa i) := by
  refine WP.seq (WP.mono (esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa (i + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (windowAB_byte_ok wu hi eu true ru) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (windowAB_byte_ok wb hi (eb.trans eu) false rb) fun c ⟨wc, ec, rc⟩ => ?_)
  refine Wp.wp_test fun t ht zt => WP.block_nil ⟨wc.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ec, eb, eu], ?_, ?_⟩
  · rw [zt, ec, eb, eu, test_zero i (by omega)]
  · rw [ht.mem]
    have e := window_step Aa (-baseAff) (verificationChallenge s₀) (verificationScalar s₀) i
      (kByte s₀ i) (sByte s₀ i) (kByte_val s₀ i) (sByte_val s₀ i)
    simp only [↓reduceIte, Bool.false_eq_true] at rc
    rw [wsum] at rc ⊢
    rw [← e]; exact rc

theorem byteStepA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {i : Nat} (hi : 32 ≤ i) (hi' : i < 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 (i + 1))
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa (i + 1))) :
    WP isa byteStepA s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 i ∧
      t.zf = some (decide (i = 32)) ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa i) := by
  refine WP.seq (WP.mono (esiDec_ok h hesi) fun u ⟨wu, eu, mu⟩ => ?_)
  have ru : Rep (point (env u.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa (i + 1)) := by rw [mu]; exact hacc
  refine WP.seq (WP.mono (windowA_byte_ok wu hi' eu true ru) fun b ⟨wb, eb, rb⟩ => ?_)
  refine WP.seq (WP.mono (windowA_byte_ok wb hi' (eb.trans eu) false rb) fun c ⟨wc, ec, rc⟩ => ?_)
  refine Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨wc.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ec, eb, eu], ?_, ?_⟩
  · rw [zt, ec, eb, eu, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]
  · rw [ht.mem]
    have hS := decodeLE_lt32 s₀.mem ((arg s₀ 1 + BitVec.ofNat 32 32).setWidth 64)
    have s0 : verificationScalar s₀ / 256 ^ i = 0 := high_zero hS hi
    have s1 : verificationScalar s₀ / 256 ^ (i + 1) = 0 := high_zero hS (by omega)
    have e := window_step Aa (-baseAff) (verificationChallenge s₀) (verificationScalar s₀) i
      (kByte s₀ i) 0 (kByte_val s₀ i) (by rw [s0]; rfl)
    have z : (0 : Byte).toNat = 0 := rfl
    simp only [z, Nat.zero_div, Nat.zero_mod, s1, s0, zero_smul, add_zero] at e
    simp only [↓reduceIte, Bool.false_eq_true] at rc
    rw [wsum] at rc ⊢
    simp only [s1, s0, zero_smul, add_zero] at rc ⊢
    rw [← e]; exact rc

/-! ## The loops -/

theorem loopAB_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 32)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa 32)) :
    WP isa (.loop byteStepAB .ne) s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa 0) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧
    t.gpr .esi = BitVec.ofNat 32 m ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa m)) ?_ 32 s
    ⟨h, by decide, by decide, hesi, hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (byteStepAB_ok wu (by omega) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false hi]; rfl, i, by omega,
      wt, by omega, by omega, et, rt⟩

theorem loopA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc1 : 32 < c) (hc2 : c ≤ 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa c)) :
    WP isa (.loop byteStepA .ne) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 32 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa 32) := by
  refine WP.loop (M := isa) (Inv := fun m t => WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧
    t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa (32 + m))) ?_ (c - 32) s
    ⟨h, by omega, by omega, by rw [hesi]; congr 1; omega, by rw [show 32 + (c - 32) = c by omega]; exact hacc⟩
  intro m u ⟨wu, hm0, hm, eu, ru⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (byteStepA_ok (i := 32 + i) wu (by omega) (by omega) eu ru) fun t ⟨wt, et, zt, rt⟩ => ?_
  by_cases hi : i = 0
  · subst hi
    exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, wt, et, rt⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, decide_eq_false (by omega)]; rfl, i, by omega,
      wt, by omega, by omega, et, rt⟩

theorem windowsA_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc1 : 32 ≤ c) (hc2 : c ≤ 64)
    (hesi : s.gpr .esi = BitVec.ofNat 32 c)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa c)) :
    WP isa windowsA s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 32 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa 32) := by
  have hcmp : WP isa (.block [.alu .cmp .esi (.imm 32)]) s fun t => WinCtx s₀ Aa R t ∧
      t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem ∧ t.zf = some (decide (c = 32)) :=
    Wp.wp_cmpi fun t ht _ zt => WP.block_nil ⟨h.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
      by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr], ht.mem,
      by rw [zt, hesi, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Wp.sub_beq (by omega) (by omega)]⟩
  refine WP.seq (WP.mono hcmp fun u ⟨wu, eu, mu, zu⟩ => ?_)
  refine WP.ite (!decide (c = 32)) (by show u.zf.map (!·) = _; rw [zu]; rfl) (fun hh => ?_) (fun hh => ?_)
  · have hne : c ≠ 32 := by simpa using hh
    exact loopA_ok wu (by omega) hc2 (eu.trans hesi) (by rw [mu]; exact hacc)
  · have heq : c = 32 := by simpa using hh
    subst heq
    exact WP.block_nil ⟨wu, eu.trans hesi, by rw [mu]; exact hacc⟩

/-! ## Skipping the leading zero bytes of `k` -/

theorem skipLoad_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) {c : Nat} (hc : 1 ≤ c) (hc' : c ≤ 64) (hesi : s.gpr .esi = BitVec.ofNat 32 c) :
    WP isa (.block skipLoad) s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
      t.gpr .edx = BitVec.ofNat 32 (c - 1) ∧ t.zf = some (decide ((kByte s₀ (c - 1)).toNat = 0)) ∧
      t.mem = s.mem := by
  have hp := h.pre
  have hs := h.saved
  refine Wp.wp_mov fun u₁ h₁ => Wp.wp_subi fun u₂ h₂ _ _ => ?_
  have e₂ : u₂.gpr .edx = BitVec.ofNat 32 (c - 1) := by
    rw [h₂.gpr, h₁.gpr, hesi]; exact Wp.ofNat_pred hc
  have hsp : u₂.gpr .esp = s₀.gpr .esp := by
    rw [h₂.other _ (by decide), h₁.other _ (by decide)]; exact hs.esp
  have hr₂ : u₂.rd ++ u₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hs.rd, hs.wr]
  refine Wp.wp_ldm hsp (by rw [hr₂]; exact hp.scratch.argIn (i := 2) (by decide)) fun u₃ h₃ => ?_
  have m₂ : u₂.mem = s.mem := by rw [h₂.mem, h₁.mem]
  have e₃ : u₃.gpr .eax = arg s₀ 2 := by
    rw [h₃.gpr, m₂, show (12 : Nat) = 4 + 4 * 2 from rfl]; exact hp.scratch.arg_same hs.frame (by decide)
  refine Wp.wp_add fun u₄ h₄ _ => ?_
  have e₄ : u₄.gpr .eax = arg s₀ 2 + BitVec.ofNat 32 (c - 1) := by
    rw [h₄.gpr, e₃, h₃.other .edx (by decide), e₂]
  have hA : addr (u₄.gpr .eax) 0 = addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1) := by
    rw [e₄]; simp only [addr]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 32 (c - 1))]
  have hr₄ : u₄.rd ++ u₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr, hr₂]
  refine scalar_ld8 hA (by rw [hr₄]; exact slice_read hp.challenge (by omega) (by decide))
    fun u₅ h₅ => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have hsl := hp.challenge
  have byte : s.mem (addr (arg s₀ 2 + BitVec.ofNat 32 0) (c - 1)) = kByte s₀ (c - 1) := by
    rw [kByte, bytesAt_getD _ _ _ _ (by omega), ← addr_eq (by have := hsl.fit; omega)]
    apply hs.frame
    intro r hr; rw [List.mem_singleton.mp hr]
    exact hsl.sep _ (slice_contains hsl (by omega) (by decide))
  have mt : t.mem = s.mem := by rw [ht.mem, h₅.mem, h₄.mem, h₃.mem, m₂]
  have k₅ : IKeep (arg s₀ 3) s t := ⟨by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide),
      h₃.other _ (by decide), h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide)],
    by rw [ht.rd, h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [ht.wr, h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [mt]; exact Frame.refl _ _⟩
  refine ⟨h.of_ikeep k₅ (by rw [mt]), ?_, ?_, ?_, mt⟩
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide),
      h₂.other _ (by decide), h₁.other _ (by decide), hesi]
  · rw [ht.gpr, h₅.other _ (by decide), h₄.other _ (by decide), h₃.other _ (by decide), e₂]
  · rw [zt, h₅.gpr, h₄.mem, h₃.mem, m₂, byte, BitVec.and_self]
    generalize kByte s₀ (c - 1) = b
    revert b; decide

/-- With `c` bytes of the scalars left. -/
def LoopAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (c : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 c ∧
    Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) (wsum s₀ Aa c)

/-- Skipping, with `32 + m` bytes of `k` left, all of them above zero. -/
def SkipAt (s₀ : State) (Aa : EPoint dZ) (R : Spec.Ed25519.Point) (m : Nat) (t : State) : Prop :=
  WinCtx s₀ Aa R t ∧ 0 < m ∧ m ≤ 32 ∧ t.gpr .esi = BitVec.ofNat 32 (32 + m) ∧
    verificationChallenge s₀ / 256 ^ (32 + m) = 0 ∧ Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0

/-- Whether the skipping goes on below `32 + m` bytes: the byte below is zero, and not the last
of `k` alone. -/
def skipOn (s₀ : State) (m : Nat) : Bool :=
  decide ((kByte s₀ (32 + m - 1)).toNat = 0) && decide (m ≠ 1)

/-- Where the skipping stops, if it does below `32 + m` bytes. -/
def skipEnd (s₀ : State) (m : Nat) : Nat :=
  if (kByte s₀ (32 + m - 1)).toNat = 0 then 32 + m - 1 else 32 + m

theorem wsum_zero {s₀ : State} {Aa : EPoint dZ} {c : Nat} (hc : 32 ≤ c)
    (hk : verificationChallenge s₀ / 256 ^ c = 0) : wsum s₀ Aa c = 0 := by
  rw [wsum, hk, high_zero (decodeLE_lt32 _ _) hc, zero_smul, zero_smul, add_zero]

theorem skipBody_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point} {m : Nat}
    (h : SkipAt s₀ Aa R m s) :
    WP isa skipBody s fun t => t.zf.map (!·) = some (skipOn s₀ m) ∧
      (skipOn s₀ m = false → 32 ≤ skipEnd s₀ m ∧ skipEnd s₀ m ≤ 64 ∧ LoopAt s₀ Aa R (skipEnd s₀ m) t) ∧
      (skipOn s₀ m = true → SkipAt s₀ Aa R (m - 1) t) := by
  obtain ⟨wu, hm0, hm, eu, ku, ru⟩ := h
  refine WP.seq (WP.mono (skipLoad_ok wu (by omega) (by omega) eu) fun v ⟨wv, ev, dv, zv, mv⟩ => ?_)
  have rv : Rep (point (env v.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [mv]; exact ru
  refine WP.ite (!decide ((kByte s₀ (32 + m - 1)).toNat = 0)) (by show v.zf.map (!·) = _; rw [zv]; rfl)
    (fun hh => ?_) (fun hh => ?_)
  · have hnz : (kByte s₀ (32 + m - 1)).toNat ≠ 0 := by simpa using hh
    have son : skipOn s₀ m = false := by simp only [skipOn, decide_eq_false hnz, Bool.false_and]
    have sen : skipEnd s₀ m = 32 + m := by simp only [skipEnd, hnz, ↓reduceIte]
    refine Wp.wp_cmp fun t ht _ zt => WP.block_nil ⟨?_, fun _ => ?_, fun h => absurd h (by rw [son]; decide)⟩
    · rw [zt, son]; simp
    · rw [sen]
      refine ⟨by omega, by omega, wv.of_ikeep ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
        by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem]), by rw [ht.gpr, ev], ?_⟩
      rw [ht.mem, wsum_zero (by omega) ku]; exact rv
  · have hz : (kByte s₀ (32 + m - 1)).toNat = 0 := by simpa using hh
    have k' : verificationChallenge s₀ / 256 ^ (32 + m - 1) = 0 := by
      have := div_split (verificationChallenge s₀) (32 + m - 1)
      rw [show 32 + m - 1 + 1 = 32 + m by omega, ku, ← kByte_val, hz] at this
      exact this
    have son : skipOn s₀ m = decide (m ≠ 1) := by
      simp only [skipOn, decide_eq_true hz, Bool.true_and]
    have sen : skipEnd s₀ m = 32 + m - 1 := by simp only [skipEnd, hz, ↓reduceIte]
    refine Wp.wp_mov fun w hw => Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
    have ww : WinCtx s₀ Aa R t := (wv.of_ikeep (IKeep.of_counter hw) (by rw [hw.mem])).of_ikeep
      ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr, by rw [ht.mem]; exact Frame.refl _ _⟩ (by rw [ht.mem])
    have et : t.gpr .esi = BitVec.ofNat 32 (32 + m - 1) := by rw [ht.gpr, hw.gpr, dv]
    have rt : Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by rw [ht.mem, hw.mem]; exact rv
    have zt' : t.zf = some (decide (32 + m - 1 = 32)) := by
      rw [zt, hw.gpr, dv, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
        Wp.sub_beq (by omega) (by omega)]
    refine ⟨?_, fun hf => ?_, fun hn => ?_⟩
    · rw [zt', son]
      by_cases h1 : m = 1
      · subst h1; rfl
      · rw [decide_eq_false (show ¬(32 + m - 1 = 32) by omega), decide_eq_true h1]; rfl
    · have h1 : m = 1 := by
        rw [son] at hf
        by_contra hne
        rw [decide_eq_true hne] at hf
        cases hf
      subst h1
      rw [sen]
      exact ⟨by decide, by decide, ww, et, by rw [wsum_zero (le_refl _) k']; exact rt⟩
    · have h1 : m ≠ 1 := by
        rw [son] at hn
        exact of_decide_eq_true hn
      exact ⟨ww, by omega, by omega, by rw [et]; congr 1; omega,
        by rw [show 32 + (m - 1) = 32 + m - 1 by omega]; exact k', rt⟩

theorem skipZero_ok {s₀ s : State} {Aa : EPoint dZ} {R : Spec.Ed25519.Point}
    (h : WinCtx s₀ Aa R s) (hesi : s.gpr .esi = BitVec.ofNat 32 64)
    (hacc : Rep (point (env s.mem (arg s₀ 3)) 0 1 2 3) 0) :
    WP isa skipZero s fun t => ∃ c, 32 ≤ c ∧ c ≤ 64 ∧ LoopAt s₀ Aa R c t := by
  have high_zero_64 : verificationChallenge s₀ / 256 ^ (32 + 32) = 0 := Nat.div_eq_of_lt (decodeLE_lt64 _ _)
  refine WP.loop (M := isa) (Inv := fun m t => SkipAt s₀ Aa R m t) ?_ 32 s
    ⟨h, by decide, by decide, hesi, high_zero_64, hacc⟩
  intro m u hu
  have hm0 := hu.2.1
  refine WP.mono (skipBody_ok hu) fun t ⟨zt, ft, tt⟩ => ?_
  cases hs : skipOn s₀ m
  · exact .inl ⟨by show t.zf.map (!·) = _; rw [zt, hs], skipEnd s₀ m, ft hs⟩
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt, hs], m - 1, by omega, tt hs⟩

/-! ## The whole multiplication -/

theorem Saved.frame2 {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s) (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (hk : ScalarKeep s t) {o n o' n' : Nat} (hf : Frame [sub x o n, sub x o' n'] s.mem t.mem)
    (h1 : 16 ≤ o) (h2 : o + n ≤ 8192) (h3 : 16 ≤ o') (h4 : o' + n' ≤ 8192) (h5 : o < 8192)
    (h6 : o' < 8192) : Saved s₀ x t := by
  apply h.of_frame hk hf
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [scR_eq]
    · exact sub_sub hx (Nat.zero_le _) h2 h5
    · exact sub_sub hx (Nat.zero_le _) h4 h6
  · intro p hp r hr
    have := savedSlots_bound p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj (by omega) (by omega) (Or.inl (by omega))
    · exact sub_disj (by omega) (by omega) (Or.inl (by omega))

theorem windowPrep_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R) :
    WP isa windowPrep s fun t => WinCtx s₀ Aa R t ∧ t.gpr .esi = BitVec.ofNat 32 64 ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3) 0 := by
  have hfit := hp.scratch.fit
  have hc := hs.ctx hfit hp.scratch.wr
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hc) fun a ⟨ka, ea⟩ => ?_)
  have sa := hs.ikeep hfit (IKeep.of_field ka)
  have ca := ka.ctx hc
  have tpa : ∀ o, 928 ≤ o → o + 128 ≤ 8192 → tablePoint a.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o :=
    fun o h1 h2 => tablePoint_frame hfit ka.frame (by decide) h2 (Or.inr h1)
  refine WP.seq (WP.mono (aTable_ok ca hA (by rw [tpa 7680 (by decide) (by decide)]; exact ha)
    (by rw [ea]; rfl)) fun b hb => ?_)
  have sb := sa.frame2 hfit hb.keep hb.frame (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine WP.seq (WP.mono (bTable_ok hb.ctx) fun c ⟨kc, fc, tc, dc⟩ => ?_)
  have sc := sb.frame2 hfit kc fc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have cc := sc.ctx hfit hp.scratch.wr
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ cc) fun d ⟨kd, ed⟩ => ?_
  refine Wp.wp_movi fun e he => WP.block_nil ?_
  have ke : IKeep (arg s₀ 3) c e := (IKeep.of_field kd).trans (IKeep.of_counter he)
  have de : env e.mem (arg s₀ 3) 16 = env c.mem (arg s₀ 3) 16 := by rw [he.mem, ed]; rfl
  refine ⟨⟨hp, sc.ikeep hfit ke, de.trans (dc.trans hb.d), fun j hj => ?_, fun j hj => ?_, ?_⟩, he.gpr, ?_⟩
  · rw [tablePoint_frame hfit ke.frame (by decide) (by omega) (Or.inr (by omega)),
      tablePoint_frame2 fc hfit (by decide) (by decide) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hb.table j hj
  · rw [tablePoint_frame hfit ke.frame (by decide) (by omega) (Or.inr (by omega))]
    exact tc j hj
  · rw [tablePoint_frame hfit ke.frame (by decide) (by decide) (Or.inr (by decide)),
      tablePoint_frame2 fc hfit (by decide) (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)),
      tablePoint_frame2 hb.frame hfit (by decide) (by decide) (by decide) (Or.inr (by decide))
        (Or.inr (by decide)), tpa 7808 (by decide) (by decide)]
    exact hr
  · rw [he.mem, ed, constPoint_eval]; exact identity_rep

theorem windowMultiply_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s)
    {A R : Spec.Ed25519.Point} {Aa : EPoint dZ} (hA : Rep A Aa)
    (ha : tablePoint s.mem (arg s₀ 3) 7680 = A) (hr : tablePoint s.mem (arg s₀ 3) 7808 = R) :
    WP isa windowMultiply s fun t => WinCtx s₀ Aa R t ∧
      Rep (point (env t.mem (arg s₀ 3)) 0 1 2 3)
        (verificationChallenge s₀ • Aa + verificationScalar s₀ • (-baseAff)) := by
  refine WP.seq (WP.mono (windowPrep_ok hp hs hA ha hr) fun e ⟨we, ee, re⟩ => ?_)
  refine WP.seq (WP.mono (skipZero_ok we ee re) fun f ⟨c', hc1, hc2, wf, ef, rf⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok wf hc1 hc2 ef rf) fun g ⟨wg, eg, rg⟩ => ?_)
  refine WP.mono (loopAB_ok wg eg rg) fun t ⟨wt, rt⟩ => ⟨wt, ?_⟩
  simpa only [wsum, pow_zero, Nat.div_one] using rt

end VG.Proof.Ed25519.X86
