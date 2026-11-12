module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoop
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtNorm
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.QDiv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root

`firstX` (the first digit, from the normalized number's top two words),
`finishX` (the root shifted back, and whether the remainder is zero), and
the square root as a whole.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (isqrt)

/-! ## The first digit -/

/-- The first digit's setup: `X`'s top two words into `(r8, r9)`, `r10`, `r11`, `r13` zero, `rcx = 64`. -/
theorem firstHd_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) (hW : 6 ≤ W) :
    WP isa (.block (ws ++ base sqZ .rbx ++ ([.mov .r8 (.mem (ix .rbx .r12 (-40))), .mov .r9 (.mem (ix .rbx .r12 (-48))),
      .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0), .mov32 .r13 (.imm 0), .mov32 .rcx (.imm 64)] : List Instr))) s
      fun t => t.gpr .r8 = word s.mem B (slot W sqZ + 8 * (W - 5)) ∧
        t.gpr .r9 = word s.mem B (slot W sqZ + 8 * (W - 6)) ∧ t.gpr .r10 = 0 ∧ t.gpr .r11 = 0 ∧ t.gpr .r13 = 0 ∧
        t.gpr .rcx = BitVec.ofNat 64 64 ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .r8, .r10, .r11, .r13, .rcx] s t := by
  have hn := hw.scr.nowrap
  have sj := hw.sl (j := sqZ) (by decide)
  have hw2 := hw.w2
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := hw.scr.congr (k₁.trans k₂).2.2
  have h12' : s₂.gpr .r12 = BitVec.ofNat 64 W := (k₂.gpr (by decide)).trans h12
  have a5 := addrI (d := -40) (k := W - 5) hbx h12' (by omega)
  have a6 := addrI (d := -48) (k := W - 6) hbx h12' (by omega)
  refine WP.mono (WP.keep [.r8, .r9, .r10, .r11, .r13, .rcx] (Q := fun t =>
      t.gpr .r8 = word s.mem B (slot W sqZ + 8 * (W - 5)) ∧ t.gpr .r9 = word s.mem B (slot W sqZ + 8 * (W - 6)) ∧
      t.gpr .r10 = 0 ∧ t.gpr .r11 = 0 ∧ t.gpr .r13 = 0 ∧ t.gpr .rcx = BitVec.ofNat 64 64 ∧ t.mem = s₂.mem) (by
    xrun [State.ea, ix, a5, a6, hs₂.ld (d := slot W sqZ + 8 * (W - 5)) (by simp only [sqZ] at sj ⊢; omega),
      hs₂.ld (d := slot W sqZ + 8 * (W - 6)) (by simp only [sqZ] at sj ⊢; omega), m₂, m₁]
    all_goals first | rfl | decide) rfl) fun t ⟨⟨a1, a2, a3, a4, a5', a6', m₃⟩, k₃⟩ => ?_
  exact ⟨a1, a2, a3, a4, a5', a6', by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The first digit's stores: the remainder `(r11, r13)` in place of `X`'s top two
words, `D`'s words `h - 1` and `h` from `2 r10`, and `r10` into `S`'s word 2. -/
theorem firstSt_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h1 : 1 ≤ h) :
    WP isa (.block (ws ++ base sqZ .rbx ++ ([.store (ix .rbx .r12 (-40)) .r11, .store (ix .rbx .r12 (-48)) .r13] :
      List Instr) ++ base sqD .rsi ++ hOf ++ ([.mov .rax (.reg .r10), .alu .add .rax (.reg .rax),
      .store (ix .rsi .r12 (-8)) .rax, .mov .rax (.reg .r10), .shift .shr .rax 63, .store (ix .rsi .r12) .rax] :
      List Instr) ++ base sqS .rsi ++ ([.store { base := .rsi, disp := 16 } .r10] : List Instr))) s fun t =>
      t.mem = ((((s.mem.writeW (off B (slot W sqZ + 8 * (W - 5))) (s.gpr .r11)).writeW
        (off B (slot W sqZ + 8 * (W - 6))) (s.gpr .r13)).writeW (off B (slot W sqD + 8 * (h - 1)))
          (s.gpr .r10 + s.gpr .r10)).writeW (off B (slot W sqD + 8 * h)) (s.gpr .r10 >>> 63)).writeW
            (off B (slot W sqS + 16)) (s.gpr .r10) ∧
      Keep [.r12, .r9, .rbx, .rsi, .rax] s t := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have slS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqZ (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans hw.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hw.scr.congr k12.2.2
  have h12' : s₂.gpr .r12 = BitVec.ofNat 64 W := (k₂.gpr (by decide)).trans h12
  have a5 := addrI (d := -40) (k := W - 5) hbx h12' (by omega)
  have a6 := addrI (d := -48) (k := W - 6) hbx h12' (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = (s.mem.writeW (off B (slot W sqZ + 8 * (W - 5))) (s.gpr .r11)).writeW
      (off B (slot W sqZ + 8 * (W - 6))) (s.gpr .r13)) (by
    xrun [State.ea, ix, a5, a6, hs₂.st (d := slot W sqZ + 8 * (W - 5)) (by omega),
      hs₂.st (d := slot W sqZ + 8 * (W - 6)) (by omega), m₂, m₁, (k12.gpr (by decide) : s₂.gpr .r11 = _),
      (k12.gpr (by decide) : s₂.gpr .r13 = _)]) rfl) fun s₃ ⟨m₃, k₃⟩ => ?_
  have k13 := k12.trans k₃
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqD (r := .rsi) (by decide) ((k13.gpr (by decide)).trans hw.rdi)
    ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9))) fun s₄ ⟨hsi, m₄, k₄⟩ => ?_
  have k14 := k13.trans k₄
  have hs₄ := hw.scr.congr k14.2.2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 h ∧ t.mem = s₄.mem)
    (by unfold hOf; xrun [((k₃.trans k₄).gpr (by decide) : s₄.gpr .r12 = _), h12', hOf_val (W := W) (by omega) (by omega),
      show W / 2 - 2 = h by omega]) rfl) fun s₅ ⟨⟨h12'', m₅⟩, k₅⟩ => ?_
  have k15 := k14.trans k₅
  have hsi' : s₅.gpr .rsi = off B (slot W sqD) := (k₅.gpr (by decide)).trans hsi
  have d1 := addrI (d := -8) (k := h - 1) hsi' h12'' (by omega)
  have d0 := addrI (d := 0) (k := h) hsi' h12'' (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s₅.mem.writeW (off B (slot W sqD + 8 * (h - 1)))
      (s.gpr .r10 + s.gpr .r10)).writeW (off B (slot W sqD + 8 * h)) (s.gpr .r10 >>> 63)) (by
    have hs₅ := hw.scr.congr k15.2.2
    have shv : (1 ≤ 63 ∧ 63 ≤ 63) = True := eq_true ⟨by decide, by decide⟩
    xrun [State.ea, ix, d1, d0, shv, hs₅.st (d := slot W sqD + 8 * (h - 1)) (by omega),
      hs₅.st (d := slot W sqD + 8 * h) (by omega), (k15.gpr (by decide) : s₅.gpr .r10 = _)]) rfl)
    fun s₆ ⟨m₆, k₆⟩ => ?_
  have k16 := k15.trans k₆
  rw [WP.block_append_iff]
  refine WP.mono (base_ok sqS (r := .rsi) (by decide) ((k16.gpr (by decide)).trans hw.rdi)
    (((k₃.trans (k₄.trans (k₅.trans k₆))).gpr (by decide)).trans ((k₂.gpr (by decide)).trans h9)))
    fun s₇ ⟨hsi7, m₇, k₇⟩ => ?_
  have k17 := k16.trans k₇
  have hs₇ := hw.scr.congr k17.2.2
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₇.mem.writeW (off B (slot W sqS + 16)) (s.gpr .r10)) (by
    have a16 : s₇.gpr .rsi + BitVec.ofInt 64 16 = off B (slot W sqS + 16) := by
      rw [hsi7, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, off_addN]
    xrun [State.ea, a16, hs₇.st (d := slot W sqS + 16) (by omega), (k17.gpr (by decide) : s₇.gpr .r10 = _)]) rfl)
    fun t ⟨m₈, k₈⟩ => ?_
  exact ⟨by rw [m₈, m₇, m₆, m₅, m₄, m₃], (k17.trans k₈).mono (by simp)⟩

/-- The reciprocal's setup: `r10 = r8 = [sqS]`, `r12 = 3`. -/
theorem firstRcp_ok {s : State} {B : Addr} {Z W : Nat} (hw : Ws s B Z W) :
    WP isa (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) s fun t =>
      t.gpr .r10 = off B (slot W sqS) ∧ t.gpr .r8 = off B (slot W sqS) ∧ t.gpr .r12 = BitVec.ofNat 64 3 ∧
        t.mem = s.mem ∧ Keep [.r12, .r9, .r10, .r8] s t := by
  rw [show ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr) =
    ws ++ ((base sqS .r10 ++ base sqS .r8) ++ ([.mov32 .r12 (.imm 3)] : List Instr)) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono hw.ws_ok fun t₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok sqS sqS (r₁ := .r10) (r₂ := .r8) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun t₂ ⟨h10, h8, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 3 ∧ t.mem = t₂.mem)
    (by xrun) rfl) fun t ⟨⟨h12', m₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans h10, (k₃.gpr (by decide)).trans h8, h12', by rw [m₃, m₂, m₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The first digit's numbers, generic over the word `β`. -/
theorem first_arith {H β T : Nat} (hlo : H * H ≤ T) (hhi : T < β * β) :
    H ≤ isqrt T ∧ isqrt T < β ∧ T - isqrt T * isqrt T ≤ 2 * isqrt T := by
  obtain ⟨lo, hi⟩ := VG.Proof.Rsa.RecoverDet.isqrt_spec T
  generalize isqrt T = q at lo hi
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.le_of_not_lt fun h => ?_
    have := Nat.mul_self_le_mul_self (show q + 1 ≤ H by omega)
    omega
  · refine Nat.lt_of_not_le fun h => ?_
    have := Nat.mul_self_le_mul_self h
    omega
  · have : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by grind
    omega

/-- `firstX`'s program, in memory: the arrays `sqD`, `sqS`, `sqU` cleared, then
the first digit `r10` of `T` (`X`'s top two words) with its remainder
`(r11, r13)` stored, and `S`'s reciprocal word. -/
theorem firstA_ok {s : State} {B : Addr} {Z W h T : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h1 : 1 ≤ h)
    (hT : (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat * 2 ^ 64 + (word s.mem B (slot W sqZ + 8 * (W - 6))).toNat = T)
    (hTl : 2 ^ 126 ≤ T) :
    WP isa (seqs (firstX.take 5)) s fun t => Ws t B Z W ∧ FrmP B (SqLP W) s.mem t.mem ∧ Keep mmRegs s t ∧
      2 ^ 63 ≤ (word t.mem B (slot W sqS + 8 * (3 - 1))).toNat := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have slS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have slU : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have hsCt : 8 * sCt = 200 := rfl
  have hsU : 8 * sU = 208 := rfl
  have hT128 : T < 2 ^ 128 := by
    have h5 := (word s.mem B (slot W sqZ + 8 * (W - 5))).isLt
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h5, h6]
  obtain ⟨sq1, sq2, sq3⟩ := first_arith (H := 2 ^ 63) (β := 2 ^ 64) (T := T) (by rw [← Nat.pow_add]; exact hTl)
    (by rw [← Nat.pow_add]; exact hT128)
  have e8 : T / 2 ^ 64 = (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat := by
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h6]
  have e9 : T % 2 ^ 64 = (word s.mem B (slot W sqZ + 8 * (W - 6))).toNat := by
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h6]
  clear hTl
  simp only [firstX, List.take, seqs]
  refine WP.seq (WP.mono (zeroA_ok hw (j := sqD) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := hw.congrO o1 (by omega_arith) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := sqS) (by decide)) fun t₂ ⟨_, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by omega_arith) k2 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := sqU) (by decide)) fun t₃ ⟨_, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by omega_arith) k3 (by simp)
  have zw : ∀ d, slot W sqZ ≤ d → d + 8 ≤ slot W sqZ + 8 * (W + 2) → word t₃.mem B d = word s.mem B d :=
    fun d h1 h2 => by rw [o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
  have zD : wv t₃.mem B (slot W sqD) (W + 2) = 0 := by
    rw [o3.wv (by omega_arith) (by omega_arith), o2.wv (by omega_arith) (by omega_arith), z1]
  have F₃ : FrmP B (SqLP W) s.mem t₃.mem := by
    have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → SqLP W y) →
        FrmP B (SqLP W) m m' := fun ho hP => FrmP.of_out ho hP
    exact ((fr o1 fun y h1 h2 => by unfold SqLP; omega_arith).trans (fr o2 fun y h1 h2 => by unfold SqLP; omega_arith)).trans
      (fr o3 fun y h1 h2 => by unfold SqLP; omega_arith)
  -- The first digit.
  refine WP.seq (WP.seq (WP.mono (firstHd_ok h₃ (by omega_arith)) fun t₄ ⟨h8, h9, h10, h11, h13, hcx, m₄, k₄⟩ => ?_))
  have h8' : t₄.gpr .r8 = BitVec.ofNat 64 (T / 2 ^ 64) := by
    rw [h8, zw _ (by omega_arith) (by omega_arith), e8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h9' : t₄.gpr .r9 = BitVec.ofNat 64 (T % 2 ^ 64) := by
    rw [h9, zw _ (by omega_arith) (by omega_arith), e9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (isq_ok hT128 (isqInv0 (t₀ := t₄) hT128 h10 h11 h13 h8' h9' hcx rfl (Keep.refl _ _)))
    fun t₅ ⟨i10, i11, i13, _, _, _, m₅, k₅⟩ => ?_
  rw [show 64 - 64 = 0 from rfl, Nat.pow_zero, Nat.div_one] at i10 i11 i13
  have h₄ : Ws t₅ B Z W := h₃.congrP (P := fun _ => False) (fun _ _ => by rw [m₅, m₄])
    (fun _ f => f.elim) (k₄.trans k₅) (by simp)
  -- The stores.
  refine WP.mono (firstSt_ok h₄ hwh h1) fun t₆ ⟨m₆, k₆⟩ => ?_
  rw [i10, i11, i13, m₅, m₄] at m₆
  have FP₆ : FrmP B (SqLP W) t₃.mem t₆.mem := by
    intro x hx
    unfold SqLP at hx
    rw [m₆, writeW_outside _ B _ (d := slot W sqS + 16) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqD + 8 * h) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqD + 8 * (h - 1)) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 6)) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 5)) (by omega_arith) x (by omega_arith)]
  refine ⟨h₄.congrP (by rw [m₅, m₄]; exact FP₆) (fun y hy => by unfold DOk; unfold SqLP at hy; omega) k₆ (by decide),
    F₃.trans FP₆, ((((((k1.trans k2).trans k3).trans k₄).trans k₅).trans k₆).mono
      (by simp [mmRegs])), ?_⟩
  rw [m₆, show slot W sqS + 8 * (3 - 1) = slot W sqS + 16 from rfl, word_writeW_self, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt sq2]
  exact sq1

theorem firstM_ok {s : State} {B : Addr} {Z W h T : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h1 : 1 ≤ h)
    (hT : (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat * 2 ^ 64 + (word s.mem B (slot W sqZ + 8 * (W - 6))).toNat = T)
    (hTl : 2 ^ 126 ≤ T) :
    WP isa (seqs firstX) s fun t => ∃ m₃ : Mem,
      wv m₃ B (slot W sqD) (W + 2) = 0 ∧ FrmP B (SqLP W) s.mem m₃ ∧
      (∀ d, slot W sqZ ≤ d → d + 8 ≤ slot W sqZ + 8 * (W + 2) → word m₃ B d = word s.mem B d) ∧
      t.mem = (((((m₃.writeW (off B (slot W sqZ + 8 * (W - 5))) (BitVec.ofNat 64 ((T - isqrt T * isqrt T) / 2 ^ 64))).writeW
        (off B (slot W sqZ + 8 * (W - 6))) (BitVec.ofNat 64 ((T - isqrt T * isqrt T) % 2 ^ 64))).writeW
          (off B (slot W sqD + 8 * (h - 1))) (BitVec.ofNat 64 (isqrt T) + BitVec.ofNat 64 (isqrt T))).writeW
            (off B (slot W sqD + 8 * h)) (BitVec.ofNat 64 (isqrt T) >>> 63)).writeW
              (off B (slot W sqS + 16)) (BitVec.ofNat 64 (isqrt T))).writeW (off B (slot W sqS))
                (BitVec.ofNat 64 ((2 ^ 128 - 1) / isqrt T - 2 ^ 64)) ∧
      Keep mmRegs s t ∧ Ws t B Z W := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have slS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have slU : slot W sqU = 256 + 5 * (8 * (W + 2)) := rfl
  have hsCt : 8 * sCt = 200 := rfl
  have hsU : 8 * sU = 208 := rfl
  have hT128 : T < 2 ^ 128 := by
    have h5 := (word s.mem B (slot W sqZ + 8 * (W - 5))).isLt
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h5, h6]
  obtain ⟨sq1, sq2, sq3⟩ := first_arith (H := 2 ^ 63) (β := 2 ^ 64) (T := T) (by rw [← Nat.pow_add]; exact hTl)
    (by rw [← Nat.pow_add]; exact hT128)
  have e8 : T / 2 ^ 64 = (word s.mem B (slot W sqZ + 8 * (W - 5))).toNat := by
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h6]
  have e9 : T % 2 ^ 64 = (word s.mem B (slot W sqZ + 8 * (W - 6))).toNat := by
    have h6 := (word s.mem B (slot W sqZ + 8 * (W - 6))).isLt
    omega_using [hT, h6]
  clear hTl
  simp only [firstX, seqs]
  refine WP.seq (WP.mono (zeroA_ok hw (j := sqD) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := hw.congrO o1 (by omega_arith) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := sqS) (by decide)) fun t₂ ⟨_, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by omega_arith) k2 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₂ (j := sqU) (by decide)) fun t₃ ⟨_, o3, k3⟩ => ?_)
  have h₃ := h₂.congrO o3 (by omega_arith) k3 (by simp)
  have zw : ∀ d, slot W sqZ ≤ d → d + 8 ≤ slot W sqZ + 8 * (W + 2) → word t₃.mem B d = word s.mem B d :=
    fun d h1 h2 => by rw [o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]
  have zD : wv t₃.mem B (slot W sqD) (W + 2) = 0 := by
    rw [o3.wv (by omega_arith) (by omega_arith), o2.wv (by omega_arith) (by omega_arith), z1]
  have F₃ : FrmP B (SqLP W) s.mem t₃.mem := by
    have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → SqLP W y) →
        FrmP B (SqLP W) m m' := fun ho hP => FrmP.of_out ho hP
    exact ((fr o1 fun y h1 h2 => by unfold SqLP; omega_arith).trans (fr o2 fun y h1 h2 => by unfold SqLP; omega_arith)).trans
      (fr o3 fun y h1 h2 => by unfold SqLP; omega_arith)
  -- The first digit.
  refine WP.seq (WP.seq (WP.mono (firstHd_ok h₃ (by omega_arith)) fun t₄ ⟨h8, h9, h10, h11, h13, hcx, m₄, k₄⟩ => ?_))
  have h8' : t₄.gpr .r8 = BitVec.ofNat 64 (T / 2 ^ 64) := by
    rw [h8, zw _ (by omega_arith) (by omega_arith), e8, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have h9' : t₄.gpr .r9 = BitVec.ofNat 64 (T % 2 ^ 64) := by
    rw [h9, zw _ (by omega_arith) (by omega_arith), e9, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (isq_ok hT128 (isqInv0 (t₀ := t₄) hT128 h10 h11 h13 h8' h9' hcx rfl (Keep.refl _ _)))
    fun t₅ ⟨i10, i11, i13, _, _, _, m₅, k₅⟩ => ?_
  rw [show 64 - 64 = 0 from rfl, Nat.pow_zero, Nat.div_one] at i10 i11 i13
  have h₄ : Ws t₅ B Z W := h₃.congrP (P := fun _ => False) (fun _ _ => by rw [m₅, m₄])
    (fun _ f => f.elim) (k₄.trans k₅) (by simp)
  -- The stores.
  refine WP.seq (WP.mono (firstSt_ok h₄ hwh h1) fun t₆ ⟨m₆, k₆⟩ => ?_)
  rw [i10, i11, i13, m₅, m₄] at m₆
  have FP₆ : FrmP B (SqLP W) t₃.mem t₆.mem := by
    intro x hx
    unfold SqLP at hx
    rw [m₆, writeW_outside _ B _ (d := slot W sqS + 16) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqD + 8 * h) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqD + 8 * (h - 1)) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 6)) (by omega_arith) x (by omega_arith),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 5)) (by omega_arith) x (by omega_arith)]
  have h₆ := h₄.congrP (by rw [m₅, m₄]; exact FP₆) (fun y hy => by unfold DOk; unfold SqLP at hy; omega) k₆ (by decide)
  -- The reciprocal.
  refine WP.seq (WP.mono (firstRcp_ok h₆) fun t₇ ⟨r10, r8, r12, m₇, k₇⟩ => ?_)
  have hs₇ := h₆.scr.congr k₇.2.2
  have top : word t₇.mem B (slot W sqS + 8 * (3 - 1)) = BitVec.ofNat 64 (isqrt T) := by
    rw [m₇, m₆, show slot W sqS + 8 * (3 - 1) = slot W sqS + 16 from rfl, word_writeW_self]
  refine WP.mono (R2w.recip_ok hs₇ r10 r12 r8 (by decide) (by omega_arith) (by omega_arith)
    (by rw [top, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sq2]; exact sq1)) fun t ⟨m₈, k₈⟩ => ?_
  rw [top, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sq2, m₇, m₆] at m₈
  refine ⟨t₃.mem, zD, F₃, zw, m₈, ?_, ?_⟩
  · exact (((((((k1.trans k2).trans k3).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).mono (by simp [mmRegs])
  · refine h₆.congrP (P := fun y => slot W sqS ≤ y ∧ y < slot W sqS + 8) (by
      intro x hx
      have hx' : ofs B x < slot W sqS ∨ slot W sqS + 8 ≤ ofs B x := by
        rcases Nat.lt_or_ge (ofs B x) (slot W sqS) with h | h
        · exact .inl h
        · exact .inr (Nat.le_of_not_lt fun h' => hx ⟨h, h'⟩)
      rw [m₈, writeW_outside _ B _ (d := slot W sqS) (by omega_arith) x hx', ← m₆])
      (fun y hy => by unfold DOk; omega) (k₇.trans k₈) (by decide)

/-- The top pair `T` of `X`'s `2 h` words, from its two top words. -/
theorem top_pair {m : Mem} {B : Addr} {d W h X : Nat} (hwh : W = 2 * h + 4) (h1 : 1 ≤ h) (hX : wv m B d W = X)
    (hXh : X < 2 ^ (64 * (2 * h))) :
    (word m B (d + 8 * (W - 5))).toNat * 2 ^ 64 + (word m B (d + 8 * (W - 6))).toNat = X / 2 ^ (64 * (2 * (h - 1))) := by
  have e5 := word_of_wv m B d W (q := W - 5) (by omega)
  have e6 := word_of_wv m B d W (q := W - 6) (by omega)
  rw [hX] at e5 e6
  have pP : 2 ^ (64 * (W - 5)) = 2 ^ (64 * (2 * (h - 1))) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [show 64 * (W - 6) = 64 * (2 * (h - 1)) by omega] at e6
  rw [pP, ← Nat.div_div_eq_div_mul] at e5
  have hT : X / 2 ^ (64 * (2 * (h - 1))) < 2 ^ 64 * 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hXh (Nat.pow_le_pow_right (by decide) (by omega))
  generalize X / 2 ^ (64 * (2 * (h - 1))) = T at e5 e6 hT ⊢
  have : T / 2 ^ 64 < 2 ^ 64 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hT
  rw [e5, e6, Nat.mod_eq_of_lt this]
  exact Nat.div_add_mod' _ _

/-- The top pair's lower bound: `2^126` for a normalized `X`. -/
theorem top_pair_lo {X h : Nat} (h1 : 1 ≤ h) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X) :
    2 ^ 126 ≤ X / 2 ^ (64 * (2 * (h - 1))) := by
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
  refine Nat.le_trans (Nat.le_of_eq ?_) hXt
  rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega

/-- `sCt := h - 1`. -/
theorem ctX_ok {s : State} {B : Addr} {Z W h : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h1 : 1 ≤ h) :
    WP isa (.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (h - 1)) ∧ Keep [.r12, .r9] s t := by
  have hw2 := hw.w2
  have h256 := hw.h256
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  have hs₁ := hw.scr.congr k₁.2.2
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (h - 1))) (by
    simp only [hOf, List.cons_append, List.nil_append]
    xrun [h12, hOf_val (W := W) (by omega) (by omega), show W / 2 - 2 = h by omega, State.ea, hdr,
      (k₁.gpr (by decide) : s₁.gpr .rdi = _), hw.rdi, hdrOff, hs₁.st (d := 8 * sCt) (by unfold sCt sFn; omega), m₁,
      sx_ofNat (show 1 < 2 ^ 31 by decide), ofNat64_pred (show 1 ≤ h by omega) (by omega)]) rfl)
    fun t ⟨m₂, k₂⟩ => ⟨m₂, (k₁.trans k₂).mono (by simp)⟩

/-- `firstX` and the count: the loop's invariant at `h - 1`, from the normalized `X`. -/
theorem sqInit_ok {s : State} {B : Addr} {Z W h X : Nat} (hw : Ws s B Z W) (hwh : W = 2 * h + 4) (h2 : 2 ≤ h)
    (hX : wv s.mem B (slot W sqZ) W = X) (hXt : 2 ^ 62 * 2 ^ (64 * (2 * h - 1)) ≤ X) (hXh : X < 2 ^ (64 * (2 * h))) :
    WP isa (seqs (firstX ++ ([.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] :
      List (Prog isa))))
      s fun t => SqI t B Z W h X (h - 1) t ∧ FrmP B (SqLP W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  have hw2 := hw.w2
  have slZ : slot W sqZ = 256 + 7 * (8 * (W + 2)) := rfl
  have slD : slot W sqD = 256 + 3 * (8 * (W + 2)) := rfl
  have slS : slot W sqS = 256 + 1 * (8 * (W + 2)) := rfl
  have hsCt : 8 * sCt = 200 := rfl
  have hsU : 8 * sU = 208 := rfl
  have hT := top_pair (m := s.mem) (B := B) (d := slot W sqZ) hwh (by omega) hX hXh
  have hTl := top_pair_lo (by omega) hXt
  refine wp_seqs_append (by simp [firstX]) (by simp) (WP.mono (firstM_ok hw hwh (by omega) hT hTl)
    fun t₁ ⟨m₃, zD, F₃, zw, m₁, k₁, h₁⟩ => ?_)
  simp only [seqs]
  refine WP.mono (ctX_ok h₁ hwh (by omega)) fun t ⟨m₂, k₂⟩ => ?_
  generalize hTd : X / 2 ^ (64 * (2 * (h - 1))) = T at hT hTl m₁
  have hTβ : T < 2 ^ 64 * 2 ^ 64 := by
    rw [← hTd, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hXh (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨sq1, sq2, sq3⟩ := first_arith (H := 2 ^ 63) (β := 2 ^ 64) (T := T) (by rw [← Nat.pow_add]; exact hTl) hTβ
  generalize hs0 : isqrt T = s0 at m₁ sq1 sq2 sq3
  -- What changed after `m₃`.
  have FP : FrmP B (fun y => (slot W sqZ + 8 * (W - 6) ≤ y ∧ y < slot W sqZ + 8 * (W - 4)) ∨
      (slot W sqD + 8 * (h - 1) ≤ y ∧ y < slot W sqD + 8 * (h + 1)) ∨ (slot W sqS ≤ y ∧ y < slot W sqS + 8) ∨
      (slot W sqS + 16 ≤ y ∧ y < slot W sqS + 24) ∨ (200 ≤ y ∧ y < 208)) m₃ t.mem := by
    intro x hx
    rw [m₂, writeW_outside _ B _ (d := 8 * sCt) (by omega) x (by omega), m₁,
      writeW_outside _ B _ (d := slot W sqS) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqS + 16) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqD + 8 * h) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqD + 8 * (h - 1)) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 6)) (by omega) x (by omega),
      writeW_outside _ B _ (d := slot W sqZ + 8 * (W - 5)) (by omega) x (by omega)]
  -- The words written.
  have hrem : T - s0 * s0 < 2 ^ 64 * 2 ^ 64 := by omega
  have wZ6 : (word t.mem B (slot W sqZ + 8 * (W - 6))).toNat = (T - s0 * s0) % 2 ^ 64 := by
    rw [m₂, word_wW (d := 8 * sCt) _ (by omega) (by omega) (by omega), m₁,
      word_wW (d := slot W sqS) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqS + 16) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqD + 8 * h) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqD + 8 * (h - 1)) _ (by omega) (by omega) (by omega), word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_mod]
  have wZ5 : (word t.mem B (slot W sqZ + 8 * (W - 5))).toNat = (T - s0 * s0) / 2 ^ 64 := by
    rw [m₂, word_wW (d := 8 * sCt) _ (by omega) (by omega) (by omega), m₁,
      word_wW (d := slot W sqS) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqS + 16) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqD + 8 * h) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqD + 8 * (h - 1)) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqZ + 8 * (W - 6)) _ (by omega) (by omega) (by omega), word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (by decide)).mpr hrem)]
  have wD0 : (word t.mem B (slot W sqD + 8 * (h - 1))).toNat = (s0 + s0) % 2 ^ 64 := by
    rw [m₂, word_wW (d := 8 * sCt) _ (by omega) (by omega) (by omega), m₁,
      word_wW (d := slot W sqS) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqS + 16) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqD + 8 * h) _ (by omega) (by omega) (by omega), word_writeW_self,
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sq2]
  have wD1 : (word t.mem B (slot W sqD + 8 * h)).toNat = s0 / 2 ^ 63 := by
    rw [m₂, word_wW (d := 8 * sCt) _ (by omega) (by omega) (by omega), m₁,
      word_wW (d := slot W sqS) _ (by omega) (by omega) (by omega),
      word_wW (d := slot W sqS + 16) _ (by omega) (by omega) (by omega), word_writeW_self,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sq2, Nat.shiftRight_eq_div_pow]
  have hv : (2 ^ 128 - 1) / s0 - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / s0 < 2 ^ 65 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  have wS : (word t.mem B (slot W sqS)).toNat = (2 ^ 128 - 1) / s0 - 2 ^ 64 := by
    rw [m₂, word_wW (d := 8 * sCt) _ (by omega) (by omega) (by omega), m₁, word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  -- `X`'s top pair, the remainder.
  have hZ0 : wv m₃ B (slot W sqZ) W = X % 2 ^ (64 * (2 * (h - 1))) + 2 ^ (64 * (2 * (h - 1))) * T := by
    rw [wv_congr (fun i hi => zw _ (by omega) (by omega)), hX, ← hTd]; exact (Nat.mod_add_div _ _).symm
  have hR' : wv t.mem B (slot W sqZ + 8 * (2 * (h - 1))) 2 = T - s0 * s0 := by
    have e := wv_two t.mem B (slot W sqZ + 8 * (2 * (h - 1))) 0
    rw [show slot W sqZ + 8 * (2 * (h - 1)) = slot W sqZ + 8 * (W - 6) by omega,
      show slot W sqZ + 8 * (W - 6) + 8 = slot W sqZ + 8 * (W - 5) by omega, wZ6, wZ5] at e
    rw [show slot W sqZ + 8 * (2 * (h - 1)) = slot W sqZ + 8 * (W - 6) by omega, e]
    simp only [wv, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_add_div _ _
  have hZt := wv_replace (m := m₃) (m' := t.mem) (d := slot W sqZ) (k := 2 * (h - 1)) (L := 2) (N := W) (by omega)
    hZ0 (Nat.mod_lt _ (Nat.two_pow_pos _)) (show T < 2 ^ (64 * 2) by rw [show 64 * 2 = 64 + 64 from rfl, Nat.pow_add]; exact hTβ)
    (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) hR'
  -- `D = 2 s₀ β^(h - 1)`.
  have hD0 : wv m₃ B (slot W sqD) W = 0 + 2 ^ (64 * (h - 1)) * 0 := by
    rw [← wv_mod_low m₃ B _ (show W ≤ W + 2 by omega), zD]; rfl
  have hDR' : wv t.mem B (slot W sqD + 8 * (h - 1)) 2 = 2 * s0 := by
    have e := wv_two t.mem B (slot W sqD + 8 * (h - 1)) 0
    rw [show slot W sqD + 8 * (h - 1) + 8 = slot W sqD + 8 * h by omega, wD0, wD1] at e
    rw [e]
    simp only [wv, Nat.mul_zero, Nat.add_zero]
    omega
  have hDt := wv_replace (m := m₃) (m' := t.mem) (d := slot W sqD) (k := h - 1) (L := 2) (N := W) (by omega)
    hD0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) (FP.wv_eq (fun y h1 h2 hy => by omega) (by omega)) hDR'
  have hAp : Ap X (h - 1) = T := hTd
  refine ⟨⟨h₁.congrW m₂ (by unfold DOk; simp only [sCt, sFn]; omega) (by decide) k₂ (by simp), by rw [m₂, word_writeW_self],
    ?_, ?_, ?_, FrmP.refl _ _ _, Keep.refl _ _, ?_⟩, F₃.trans (FP.mono fun y hy => by unfold SqLP; omega),
    (k₁.trans k₂).mono (by simp [mmRegs])⟩
  · rw [hZt, hAp, hs0, Nat.mul_comm (2 ^ _)]
  · rw [hDt, hAp, hs0, Nat.zero_add, Nat.mul_comm (2 ^ _)]
  · rw [wS, hAp, hs0]
  · rw [FP.word_eq (fun y h1 h2 hy => by omega) (by omega)]
    exact (wv_eq_zero_iff _ _ _ _).mp zD W (by omega)

end VG.Proof.Rsa.X86_64.Rd
