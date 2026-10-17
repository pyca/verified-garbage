module

import VerifiedGarbage.Proof.AesGcm.AArch64.J0
public import VerifiedGarbage.Proof.AesGcm.AArch64.Tag

/-!
# AES-GCM on AArch64: checking a received tag (`tagLenOk`, `cmpSeg`, `verRet`), moving tags

Untrusted: everything here is checked by Lean. `tagLenOk` leaves 1 in `x9`
iff §5.2.1.2 allows a tag of `x28` bytes, 0 if not (`tagLenOk_ok`);
`cmpSeg` pads the `x28` bytes of the received tag at `W` and of the computed
one at `W + 112` with zeros, and leaves 0 in `x10` if they are equal, 1 if
not (`cmpSeg_ok`); `verRet` returns 1 or 0 (`verRet_ok`). `tagIn` copies the
received tag into `W` (`tagIn_ok`), and `tagOut` the computed one out of it
(`tagOut_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## The length -/

theorem tlTest_ok (s : State) (k : Nat) (hk : k < 4096) {t b : Nat} (h28 : s.gpr .x28 = BitVec.ofNat 64 t)
    (ht : t < 2 ^ 64) (h9 : s.gpr .x9 = BitVec.ofNat 64 b) :
    WP isa (tlTest k) s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (if t = k then 1 else b) ∧ Regs [.x9, .x10] s s' := by
  obtain ⟨s₁, run₁, x10₁, r₁⟩ : ∃ s₁, runBlock isa [.subImm .x .x10 .x28 k] s = some s₁ ∧
      s₁.gpr .x10 = BitVec.ofNat 64 t - BitVec.ofNat 64 k ∧ Regs [.x10] s s₁ := by
    refine ⟨_, by arun [hk], ?_⟩
    exact ⟨by simp [gpr_write, h28], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have ev : isa.eval (.zero .x .x10) s₁ = some (decide (t = k)) := by
    show some (s₁.read .x .x10 == 0) = _
    rw [State.read, x10₁, BitVec.setWidth_eq, Offset.ofNat_sub_ofNat_beq ht (by omega)]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, WP.ite (decide (t = k)) ev (fun h => ?_) (fun h => ?_)⟩)
  · have h' : t = k := by simpa using h
    exact WP.run ⟨_, by arun [], rfl⟩ fun s' hs' => by
      subst hs'
      exact ⟨by simp [gpr_write, h'], (r₁.comp (rs' := [.x9]) ⟨by others_tac, by rfl, by rfl, by rfl, by rfl⟩).mono (rs' := [.x9, .x10])⟩
  · have h' : t ≠ k := by simpa using h
    exact WP.block_nil ⟨by simp [r₁.others .x9 (by decide), h9, h'], r₁.mono⟩

theorem tl_chain {t : Nat} (ht : t < 2 ^ 64) :
    (if t = 16 then 1 else if t = 15 then 1 else if t = 14 then 1 else if t = 13 then 1 else
      if t = 12 then 1 else if t = 8 then 1 else if t = 4 then 1 else 0) =
      if Spec.Gcm.tagLenOk t then 1 else 0 := by
  rcases Nat.lt_or_ge t 17 with h | h
  · have e : ∀ t < 17, (if t = 16 then 1 else if t = 15 then 1 else if t = 14 then 1 else if t = 13 then 1 else
        if t = 12 then 1 else if t = 8 then 1 else if t = 4 then 1 else 0) =
        if Spec.Gcm.tagLenOk t then 1 else 0 := by decide
    exact e t h
  · simp [Spec.Gcm.tagLenOk, show t ≠ 16 by omega, show t ≠ 15 by omega, show t ≠ 14 by omega,
      show t ≠ 13 by omega, show t ≠ 12 by omega, show t ≠ 8 by omega, show t ≠ 4 by omega,
      show ¬ t ≤ 16 by omega]

/-- `tagLenOk`: `x9` is 1 iff the tag length is allowed. -/
theorem tagLenOk_ok (s : State) {t : Nat} (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.gpr .x9 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0) ∧
      Regs [.x9, .x10] s s' := by
  obtain ⟨s₁, run₁, x9₁, r₁⟩ : ∃ s₁, runBlock isa [imm .x9 0] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 0 ∧ Regs [.x9] s s₁ := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write], ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  have e28 : ∀ s' : State, Regs [.x9, .x10] s s' → s'.gpr .x28 = BitVec.ofNat 64 t :=
    fun s' r => by rw [r.others _ (by decide), h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have r₁' : Regs [.x9, .x10] s s₁ := r₁.mono
  refine WP.seq (WP.mono (tlTest_ok s₁ 4 (by decide) (e28 _ r₁') ht x9₁) fun s₂ ⟨x9₂, r₂⟩ => ?_)
  have r₂' := r₁'.trans r₂
  refine WP.seq (WP.mono (tlTest_ok s₂ 8 (by decide) (e28 _ r₂') ht x9₂) fun s₃ ⟨x9₃, r₃⟩ => ?_)
  have r₃' := r₂'.trans r₃
  refine WP.seq (WP.mono (tlTest_ok s₃ 12 (by decide) (e28 _ r₃') ht x9₃) fun s₄ ⟨x9₄, r₄⟩ => ?_)
  have r₄' := r₃'.trans r₄
  refine WP.seq (WP.mono (tlTest_ok s₄ 13 (by decide) (e28 _ r₄') ht x9₄) fun s₅ ⟨x9₅, r₅⟩ => ?_)
  have r₅' := r₄'.trans r₅
  refine WP.seq (WP.mono (tlTest_ok s₅ 14 (by decide) (e28 _ r₅') ht x9₅) fun s₆ ⟨x9₆, r₆⟩ => ?_)
  have r₆' := r₅'.trans r₆
  refine WP.seq (WP.mono (tlTest_ok s₆ 15 (by decide) (e28 _ r₆') ht x9₆) fun s₇ ⟨x9₇, r₇⟩ => ?_)
  have r₇' := r₆'.trans r₇
  refine WP.mono (tlTest_ok s₇ 16 (by decide) (e28 _ r₇') ht x9₇) fun s₈ ⟨x9₈, r₈⟩ =>
    ⟨by rw [x9₈, tl_chain ht], r₇'.trans r₈⟩

/-! ## Padded tags -/

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self, BitVec.or_self]; rfl

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at hz
  have e := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

/-- The carry of adding all ones: whether a word is not 0. -/
theorem carry_ne (d : BitVec 64) :
    decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + (false : Bool).toNat) = !decide (d = 0) := by
  have : (0 - 1 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide
  rw [this]
  by_cases h : d = 0
  · subst h; decide
  · have : d.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    simp only [h, decide_false, Bool.not_false, Bool.toNat_false, Nat.add_zero, decide_eq_true_iff]
    omega

theorem carry_val (d : BitVec 64) :
    (0 : BitVec 64) + 0 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ d.toNat + (0 - 1 : BitVec 64).toNat + false.toNat)).toNat =
      BitVec.ofNat 64 (if d = 0 then 0 else 1) := by
  rw [carry_ne]
  by_cases h : d = 0
  · subst h; rfl
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `cmpSeg`: 0 in `x10` iff the first `t` bytes of the tag at `W + 112` are
those at `W`. -/
theorem cmpSeg_ok {k : Reg → BitVec 64} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s) {t : Nat}
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) :
    WP isa cmpSeg s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t then 0 else 1) ∧
      Env Ctx St W SP s' ∧ Kept k s' ∧ s'.gpr .x28 = BitVec.ofNat 64 t ∧
      Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  have w (d : Nat) (h : d + 8 ≤ 2560) := he.perm.wW h
  obtain ⟨s₁, run₁, hm₁, x11₁, x12₁, x13₁, og₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [imm .x9 0, .str .x .x9 .x19 vO,
      .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO, .str .x .x9 .x19 (rO + 8), ptr .x11 .x19 rO, mov .x12 .x19,
      mov .x13 .x28] s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 264)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 280)
          (0 : BitVec 64) ∧
      s₁.gpr .x11 = W + BitVec.ofNat 64 272 ∧ s₁.gpr .x12 = W ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x9, .x11, .x12, .x13] s s₁ ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [he.x19, w 256 (by decide), w 264 (by decide), w 272 (by decide), w 280 (by decide)], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, he.x19]
    · simp [gpr_write, he.x19, BitVec.add_zero]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq ?_
  have he₁ : Env Ctx St W SP s₁ := he.keep (fun r hr => og₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁
  have dW : (⟨W, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 272, 16⟩ := by
    simpa using L.w_w (a := 0) (n := t) (d := 272) (k := 16) (.inl (by omega)) (by omega) (by decide)
  have lp : LoopPre s₁ W (W + BitVec.ofNat 64 272) t :=
    ⟨by omega, covers_left (by simpa using he₁.perm.wC (d := 0) (n := t) (by omega)),
      he₁.perm.wC (by omega), dW.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyB_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ?_
  have he₂ : Env Ctx St W SP s₂ := he₁.keep (fun r hr => og₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₂ rd₂ wr₂
  have x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 t := by
    rw [og₂ _ (by decide), og₁ _ (by decide), h28]
  refine WP.seq ?_
  obtain ⟨s₃, run₃, hm₃, x11₃, x12₃, x13₃, og₃, sp₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa [ptr .x11 .x19 vO,
      ptr .x12 .x19 uO, mov .x13 .x28] s₂ = some s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x11 = W + BitVec.ofNat 64 256 ∧ s₃.gpr .x12 = W + BitVec.ofNat 64 112 ∧
      s₃.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x11, .x12, .x13] s₂ s₃ ∧ s₃.sp = s₂.sp ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by arun [he₂.x19], ?_⟩
    refine ⟨rfl, ?_, ?_, ?_, by others_tac, rfl, rfl, rfl⟩
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, he₂.x19]
    · simp [gpr_write, x28₂]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have he₃ : Env Ctx St W SP s₃ := he₂.keep (fun r hr => og₃ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₃ rd₃ wr₃
  have dU : (⟨W + BitVec.ofNat 64 112, t⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩ :=
    L.w_w (.inl (by omega)) (by omega) (by decide)
  have lp₃ : LoopPre s₃ (W + BitVec.ofNat 64 112) (W + BitVec.ofNat 64 256) t :=
    ⟨by omega, covers_left (he₃.perm.wC (by omega)), he₃.perm.wC (by omega), dU.sub_right (Region.sub_prefix h16)⟩
  refine WP.seq (WP.mono (copyB_ok s₃ x12₃ x11₃ x13₃ lp₃) fun s₄ ⟨hm₄, og₄, sp₄, rd₄, wr₄⟩ => ?_)
  have he₄ : Env Ctx St W SP s₄ := he₃.keep (fun r hr => og₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₄ rd₄ wr₄
  have r (d : Nat) (h : d + 8 ≤ 2560) := he₄.perm.wR h
  obtain ⟨s₅, run₅, x10₅, og₅, sp₅, m₅, rd₅, wr₅⟩ : ∃ s₅, runBlock isa [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO,
      .logic .eor .x .x9 .x9 .x10, .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8),
      .logic .eor .x .x10 .x10 .x11, .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1,
      .adds .x .x9 .x9 .x12, .adcs .x .x10 .x11 .x11] s₄ = some s₅ ∧
      s₅.gpr .x10 = BitVec.ofNat 64 (if (s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 272) 64) ||| (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^
        s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0 then 0 else 1) ∧
      Others [.x9, .x10, .x11, .x12] s₄ s₅ ∧ s₅.sp = s₄.sp ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr := by
    refine ⟨_, by arun [he₄.x19, r 256 (by decide), r 264 (by decide), r 272 (by decide), r 280 (by decide),
      gpr_addWithCarry, c_addWithCarry, mem_addWithCarry, rd_addWithCarry, wr_addWithCarry, sp_addWithCarry,
      c_write], ?_⟩
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
        show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
      exact carry_val _
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, gpr_addWithCarry, hr]
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have e8 (a : Nat) : W + BitVec.ofNat 64 (a + 8) = W + BitVec.ofNat 64 a + BitVec.ofNat 64 8 :=
    (add_ofNat_assoc W a 8).symm
  have hm₁' : s₁.mem = (((s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272)
        (0 : BitVec 64)).writeW (W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [hm₁, ← e8, ← e8]
  have fa := Proof.Cmac.frame_store2 (m := s.mem) (W + BitVec.ofNat 64 256) 0 0
  have fb := Proof.Cmac.frame_store2 (m := (s.mem.writeW (W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) (W + BitVec.ofNat 64 272) 0 0
  have sR (d n : Nat) (h₁ : 256 ≤ d) (h₂ : d + n ≤ 288) :
      ∃ r' ∈ [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r' :=
    ⟨_, List.mem_singleton_self _, Offset.sub _ (by omega) (by omega)⟩
  have f₁ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₁.mem := by
    rw [hm₁']
    refine (fa.sub fun r hr => ?_).trans (fb.sub fun r hr => ?_) <;>
      (simp only [List.mem_singleton] at hr; subst hr)
    · exact sR 256 16 (by decide) (by decide)
    · exact sR 272 16 (by decide) (by decide)
  have z₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 272) 16 = zeros 16 := by
    rw [hm₁', Proof.Cmac.bytesAt_store2]; rfl
  have z₀ : bytesAt s₁.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [hm₁', bytesAt_frame fb (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), Proof.Cmac.bytesAt_store2]; rfl
  have f₂ : Frame [⟨W + BitVec.ofNat 64 272, t⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₄ : Frame [⟨W + BitVec.ofNat 64 256, t⟩] s₂.mem s₄.mem := by
    rw [hm₄, hm₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have f₁₂ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 272 t (by decide) (by omega))
  have f₁₄ : Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s₄.mem :=
    f₁₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sR 256 t (by decide) (by omega))
  have hA : bytesAt s₁.mem W t = bytesAt s.mem W t :=
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using L.w_w (a := 0) (n := t) (d := 256) (k := 32) (.inl (by omega)) (by omega) (by decide)) (by omega)
  have hB : bytesAt s₂.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem (W + BitVec.ofNat 64 112) t :=
    bytesAt_frame f₁₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact L.w_w (.inl (by omega)) (by omega) (by decide)) (by omega)
  have p₁ : bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s.mem W t ++ zeros (16 - t) := by
    rw [hm₂, pad_bytes z₁ _ (by rw [length_bytesAt]; omega), length_bytesAt, hA]
  have z₀' : bytesAt s₂.mem (W + BitVec.ofNat 64 256) 16 = zeros 16 := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by omega))
      (by decide), z₀]
  have p₀ : bytesAt s₄.mem (W + BitVec.ofNat 64 256) 16 = bytesAt s.mem (W + BitVec.ofNat 64 112) t ++ zeros (16 - t) := by
    rw [hm₄, hm₃, pad_bytes z₀' _ (by rw [length_bytesAt]; omega), length_bytesAt, hB]
  have q₁ : bytesAt s₄.mem (W + BitVec.ofNat 64 272) 16 = bytesAt s₂.mem (W + BitVec.ofNat 64 272) 16 :=
    bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by decide) (by omega))
      (by decide)
  have key : ((s₄.mem.readW (W + BitVec.ofNat 64 256) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 272) 64) |||
      (s₄.mem.readW (W + BitVec.ofNat 64 264) 64 ^^^ s₄.mem.readW (W + BitVec.ofNat 64 280) 64) = 0) ↔
      bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t := by
    rw [show (264 : Nat) = 256 + 8 from rfl, show (280 : Nat) = 272 + 8 from rfl, e8 256, e8 272, words_eq, p₀, q₁, p₁]
    exact ⟨List.append_cancel_right, fun h => by rw [h]⟩
  have og : Others [.x9, .x11, .x12, .x13, .x14, .x15, .x10] s s₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h9, h11, h12, h13, h14, h15, h10⟩ := hr
    have hl : r ∉ loopRegs := by simp [loopRegs, h11, h12, h13, h14, h15]
    rw [og₅ r (by simp [h9, h10, h11, h12]), og₄ r hl, og₃ r (by simp [h11, h12, h13]), og₂ r hl,
      og₁ r (by simp [h9, h11, h12, h13])]
  refine ⟨by rw [x10₅]; simp only [key], he₄.keep (fun r hr => og₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₅ rd₅ wr₅, hk.of_others og, by rw [og _ (by decide), h28], ?_⟩
  rw [m₅]; exact f₁₄

end

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W)
include L

/-- `cmp`: `cmpSeg`, or for 16-byte tags `cmp16`, which compares them where they are. -/
theorem cmp_ok {k : Reg → BitVec 64} {s : State} (he : Env Ctx St W SP s) (hk : Kept k s) {t : Nat}
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) :
    WP isa cmp s fun s' =>
      s'.gpr .x10 = BitVec.ofNat 64 (if bytesAt s.mem (W + BitVec.ofNat 64 112) t = bytesAt s.mem W t then 0 else 1) ∧
      Env Ctx St W SP s' ∧ Kept k s' ∧ s'.gpr .x28 = BitVec.ofNat 64 t ∧
      Frame [⟨W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem := by
  obtain ⟨s₀, run₀, x9₀, og₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [.lsr .x .x9 .x28 4] s = some s₀ ∧
      s₀.gpr .x9 = BitVec.ofNat 64 (t / 2 ^ 4) ∧ Others [.x9] s s₀ ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧
      s₀.rd = s.rd ∧ s₀.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h28, lsr_ofNat t 4 (by omega)], by others_tac, rfl, rfl, rfl, rfl⟩
  have he₀ : Env Ctx St W SP s₀ := he.keep (fun r hr => og₀ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide)) sp₀ rd₀ wr₀
  have hk₀ : Kept k s₀ := hk.of_others og₀
  have x28₀ : s₀.gpr .x28 = BitVec.ofNat 64 t := by rw [og₀ _ (by decide), h28]
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  refine WP.ite (decide (t / 2 ^ 4 = 0)) (eval_zero x9₀ (by omega)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (cmpSeg_ok L he₀ hk₀ x28₀ h16) fun s' ⟨x10, e, k', x28', f⟩ =>
      ⟨by rw [x10, m₀], e, k', x28', by rw [← m₀]; exact f⟩
  · have e : t = 16 := by have := of_decide_eq_false hf; omega
    subst e
    have r (d : Nat) (h : d + 8 ≤ 2560) := he₀.perm.wR h
    obtain ⟨s₁, run₁, x10₁, og₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa cmp16 s₀ = some s₁ ∧
        s₁.gpr .x10 = BitVec.ofNat 64 (if (s₀.mem.readW (W + BitVec.ofNat 64 112) 64 ^^^
          s₀.mem.readW (W + BitVec.ofNat 64 0) 64) ||| (s₀.mem.readW (W + BitVec.ofNat 64 120) 64 ^^^
          s₀.mem.readW (W + BitVec.ofNat 64 8) 64) = 0 then 0 else 1) ∧
        Others [.x9, .x10, .x11, .x12] s₀ s₁ ∧ s₁.sp = s₀.sp ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧
        s₁.wr = s₀.wr := by
      have q₀ := r 112 (by decide)
      have q₁ := r 0 (by decide)
      have q₂ := r 120 (by decide)
      have q₃ := r 8 (by decide)
      refine ⟨_, by arun [cmp16, he₀.x19, q₀, q₁, q₂, q₃, gpr_addWithCarry, c_addWithCarry, mem_addWithCarry,
        rd_addWithCarry, wr_addWithCarry, sp_addWithCarry, c_write], ?_⟩
      refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      · simp only [gpr_addWithCarry, gpr_write, Mem.readW, BitVec.setWidth_eq, ite_true, Size.bits, Nat.reduceAdd,
          show (BitVec.setWidth 64 0#16 <<< (16 * 0) : BitVec 64) = 0 from rfl, Nat.reduceDiv, Nat.reduceMul]
        exact carry_val _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [gpr_write, gpr_addWithCarry, hr]
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have key : ((s₀.mem.readW (W + BitVec.ofNat 64 112) 64 ^^^ s₀.mem.readW (W + BitVec.ofNat 64 0) 64) |||
        (s₀.mem.readW (W + BitVec.ofNat 64 120) 64 ^^^ s₀.mem.readW (W + BitVec.ofNat 64 8) 64) = 0) ↔
        bytesAt s.mem (W + BitVec.ofNat 64 112) 16 = bytesAt s.mem W 16 := by
      rw [show (120 : Nat) = 112 + 8 from rfl, ← add_ofNat_assoc W 112 8, BitVec.add_zero,
        show W + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 by rw [BitVec.add_zero],
        BitVec.add_zero, words_eq, m₀]
    have og : Others [.x9, .x10, .x11, .x12] s s₁ := fun r hr => by
      rw [og₁ r hr, og₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.1)]
    refine ⟨by rw [x10₁]; simp only [key], he₀.keep (fun r hr => og₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) sp₁ rd₁ wr₁, hk.of_others og, by rw [og _ (by decide), h28], ?_⟩
    rw [m₁, m₀]; exact Frame.refl _ _

end

/-- `verRet`: 1 if the tags are equal (`x10` is 0), 0 if not. -/
theorem verRet_ok {s : State} {b : Bool} (h10 : s.gpr .x10 = BitVec.ofNat 64 (if b then 0 else 1)) :
    WP isa (.block verRet) s fun s' => s'.gpr .x0 = BitVec.ofNat 64 (if b then 1 else 0) ∧ Regs [.x0] s s' := by
  refine WP.run ⟨_, by simp only [verRet]; arun [], rfl⟩ fun s' hs' => ?_
  subst hs'
  refine ⟨?_, ⟨by others_tac, rfl, rfl, rfl, rfl⟩⟩
  simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, h10]
  cases b <;> decide

/-- `tagIn` one byte at a time: the received tag, the `t` bytes at `Tg`, copied to `W`. -/
theorem tagInB_ok {s : State} {W Tg : Addr} {t : Nat} (h19 : s.gpr .x19 = W) (h12 : s.gpr .x12 = Tg)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) (hr : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨W, 2560⟩] s.wr) (hd : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa (.seq (.block [mov .x11 .x19, mov .x13 .x28]) copyB) s fun s' => bytesAt s'.mem W t = bytesAt s.mem Tg t ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      Others loopRegs s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, og₁, m₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x11 .x19, mov .x13 .x28] s =
      some s₁ ∧ s₁.gpr .x11 = W ∧ s₁.gpr .x12 = Tg ∧ s₁.gpr .x13 = BitVec.ofNat 64 t ∧
      Others [.x11, .x13] s s₁ ∧ s₁.mem = s.mem ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, h19]
    · simp [gpr_write, h12]
    · simp [gpr_write, h28]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have lp : LoopPre s₁ Tg W t :=
    ⟨by omega, by rw [rd₁, wr₁]; exact hr, covers_prefix (by rw [wr₁]; exact hw) (by omega),
      hd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyB_ok s₁ x12₁ x11₁ x13₁ lp) fun s₂ ⟨hm₂, og₂, sp₂, rd₂, wr₂⟩ => ⟨?_, ?_, ?_, by rw [sp₂, sp₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · have := bytesAt_writeBytes_self s₁.mem W (bytesAt s₁.mem Tg t) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at this
    rw [hm₂, this, m₁]
  · rw [hm₂, ← m₁]
    exact (writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩
  · intro r hr
    rw [og₂ r hr, og₁ r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with rfl | rfl <;> simp)]

theorem exec_ldrq' {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.load, hin,
    Option.map_some]

theorem exec_strq' {t : VReg} {n : Reg} {off : Nat} {s : State} (ho : off % 16 = 0)
    (ho' : off < 4096 * 16) (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, ho, ho', and_self, ite_true, Option.bind_some, State.store, hout]

/-- `tagIn`: the received tag, the `t` bytes at `Tg`, copied to `W`. -/
theorem tagIn_ok {s : State} {W Tg : Addr} {t : Nat} (h19 : s.gpr .x19 = W) (h12 : s.gpr .x12 = Tg)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 t) (h16 : t ≤ 16) (hr : Covers [⟨Tg, t⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨W, 2560⟩] s.wr) (hd : (⟨Tg, t⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa tagIn s fun s' => bytesAt s'.mem W t = bytesAt s.mem Tg t ∧ Frame [⟨W, 16⟩] s.mem s'.mem ∧
      Others loopRegs s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, run₀, x13₀, og₀, m₀, sp₀, rd₀, wr₀⟩ : ∃ s₀, runBlock isa [.lsr .x .x13 .x28 4] s = some s₀ ∧
      s₀.gpr .x13 = BitVec.ofNat 64 (t / 2 ^ 4) ∧ Others [.x13] s s₀ ∧ s₀.mem = s.mem ∧ s₀.sp = s.sp ∧
      s₀.rd = s.rd ∧ s₀.wr = s.wr := by
    refine ⟨_, by arun [], ?_⟩
    exact ⟨by simp [gpr_write, h28, lsr_ofNat t 4 (by omega)], by others_tac, rfl, rfl, rfl, rfl⟩
  have og₀' : Others loopRegs s s₀ := fun r hr => og₀ r (by
    simp only [List.mem_singleton]; rintro rfl; exact hr (by decide))
  unfold tagIn
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  refine WP.ite (decide (t / 2 ^ 4 = 0)) (eval_zero x13₀ (by omega)) (fun _ => ?_) (fun hf => ?_)
  · refine WP.mono (tagInB_ok (by rw [og₀ _ (by decide), h19]) (by rw [og₀ _ (by decide), h12])
      (by rw [og₀ _ (by decide), h28]) h16 (by rw [rd₀, wr₀]; exact hr) (by rw [wr₀]; exact hw) hd)
      fun s' ⟨b, f, o, sp, rd, wr⟩ => ⟨by rw [b, m₀], by rw [← m₀]; exact f,
        fun r hr => by rw [o r hr, og₀' r hr], by rw [sp, sp₀], by rw [rd, rd₀], by rw [wr, wr₀]⟩
  · have e : t = 16 := by have := of_decide_eq_false hf; omega
    subst e
    have i₁ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x12 + BitVec.ofNat 64 0) 16 := by
      rw [og₀ _ (by decide), h12, rd₀, wr₀, BitVec.add_zero]
      exact hr Tg 16 ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    have i₂ : InRegions (s₀.setV .v0 (s₀.mem.read (s₀.gpr .x12 + BitVec.ofNat 64 0) 16)).wr
        ((s₀.setV .v0 (s₀.mem.read (s₀.gpr .x12 + BitVec.ofNat 64 0) 16)).gpr .x19 + BitVec.ofNat 64 0) 16 := by
      show InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 0) 16
      rw [og₀ _ (by decide), h19, wr₀, BitVec.add_zero]
      exact covers_prefix (n := 16) hw (by decide) W 16 ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_ldrq' (by decide) (by decide) i₁, ?_⟩
    refine WP.block_cons_iff.mpr ⟨_, exec_strq' (by decide) (by decide) i₂, WP.block_nil ?_⟩
    have hx12 : s₀.gpr .x12 = Tg := by rw [og₀ _ (by decide), h12]
    have hx19 : s₀.gpr .x19 = W := by rw [og₀ _ (by decide), h19]
    simp only [RegUpd.mem_setV, RegUpd.gpr_setV, RegUpd.v_setV_self, hx12, hx19, BitVec.add_zero]
    refine ⟨?_, ?_, fun r hr => og₀' r hr, sp₀, rd₀, wr₀⟩
    · have := bytesAt_writeBytes_self s₀.mem W (bytesAt s₀.mem Tg 16) (by rw [length_bytesAt]; decide)
      rw [length_bytesAt] at this
      rw [write_read_bytes, this, m₀]
    · rw [write_read_bytes, ← m₀]
      exact writeBytes_frame' _ (length_bytesAt _ _ _)

/-- `tagOut`: the tag at `W` copied to the 16 bytes at `Tg`. -/
theorem tagOut_ok {s : State} {W Tg : Addr} (h19 : s.gpr .x19 = W) (h28 : s.gpr .x28 = Tg)
    (hr : Covers [⟨W, 2560⟩] (s.rd ++ s.wr)) (hw : Covers [⟨Tg, 16⟩] s.wr)
    (hd : (⟨Tg, 16⟩ : Region).Disjoint ⟨W, 16⟩) :
    WP isa (.block tagOut) s fun s' => bytesAt s'.mem Tg 16 = bytesAt s.mem W 16 ∧
      Frame [⟨Tg, 16⟩] s.mem s'.mem ∧ Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := in_off hr (show 0 + 8 ≤ 2560 by decide) (by decide)
  have r₂ := in_off hr (show 8 + 8 ≤ 2560 by decide) (by decide)
  have w₁ := in_off hw (show 0 + 8 ≤ 16 by decide) (by decide)
  have w₂ := in_off hw (show 8 + 8 ≤ 16 by decide) (by decide)
  have hd' : (⟨Tg, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 8, 8⟩ :=
    hd.sub_left (Region.sub_prefix (by decide)) |>.sub_right (Offset.sub_base _ (by decide))
  obtain ⟨s', run, hm, og, sp', rd', wr'⟩ : ∃ s', runBlock isa tagOut s = some s' ∧
      s'.mem = (s.mem.writeW Tg (s.mem.readW W 64)).writeW (Tg + BitVec.ofNat 64 8)
        ((s.mem.writeW Tg (s.mem.readW W 64)).readW (W + BitVec.ofNat 64 8) 64) ∧
      Others [.x9] s s' ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    refine ⟨_, by simp only [tagOut]; arun [h19, h28, r₁, r₂, w₁, w₂], ?_⟩
    refine ⟨?_, by others_tac, rfl, rfl, rfl⟩
    simp only [mem_write, Mem.writeW, Mem.readW, BitVec.setWidth_eq, BitVec.add_zero, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceAdd, gpr_write, ite_true, ite_false, reduceCtorEq, h19, h28]
  refine WP.of_runBlock ⟨s', run, ?_, ?_, og, sp', rd', wr'⟩
  · rw [hm, bytesAt_copy2 _ hd']
  · rw [hm]; exact Proof.Cmac.frame_store2 _ _ _

end VG.Proof.AesGcm.AArch64
