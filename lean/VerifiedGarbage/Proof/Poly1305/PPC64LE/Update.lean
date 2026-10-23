module

public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Buffer
public import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Poly1305.BlocksScratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Buffer
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Poly1305.Stream
meta import VerifiedGarbage.Proof.Poly1305.BlocksScratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Blocks
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
meta import VerifiedGarbage.Proof.Poly1305.PPC64LE.Save
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Save

/-!
# Poly1305 on PPC64LE: `update`

As on AArch64 (radix `2²⁶`), between `save` and `restore`: the code after
`save` is proved from the state `save` leaves, which agrees with the state on
entry everywhere but in the working space.
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.Poly1305.PPC64LE
open VG.Proof.Poly1305.Radix26
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : Addr := s₀.gpr .r5
abbrev dl : Nat := (s₀.gpr .r6).toNat
abbrev dR : Region := ⟨dp s₀, dl s₀⟩
/-- The number of bytes buffered. -/
abbrev kb : Nat := (s₀.gpr .r4).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (off (st s₀) 56) (kb s₀)
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : sR (st s₀) ∈ s₀.wr
  st_d : (sR (st s₀)).Disjoint (dR s₀)

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem x3_eq (s₀ : State) : s₀.gpr .r6 = BitVec.ofNat 64 (dl s₀) := by simp

/-! ## Invariants -/

/-- What holds throughout. -/
structure UCommon (s₀ : State) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r21 : s.gpr .r21 = s₀.gpr .r21
  mask : s.gpr .r20 = M26
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [wR (st s₀)] s₀.mem s.mem
  coefs : Coefs s.mem (st s₀) (Rn s₀)

/-- The accumulator in `r7`–`r11` is that of the message on entry followed by
the whole blocks `X`. -/
def Acc (s₀ : State) (X : List Byte) (s : State) : Prop :=
  A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) X % P ∧ Bounds s

/-- Before any data is consumed. -/
structure Pre1 (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  r5 : s.gpr .r5 = dp s₀
  r6 : s.gpr .r6 = s₀.gpr .r6
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s

/-- The buffer and the first `c` bytes of data are absorbed, a whole number
of blocks, and the rest of the data is at `r5`. -/
structure Cons (s₀ : State) (c : Nat) (s : State) : Prop extends UCommon s₀ s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  r5 : s.gpr .r5 = dp s₀ + BitVec.ofNat 64 c
  r6 : s.gpr .r6 = BitVec.ofNat 64 (dl s₀ - c)
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s

/-- As `Cons`, with the rest of the data at `r4`. -/
structure ConsB (s₀ : State) (c : Nat) (s : State) : Prop extends UCommon s₀ s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  r4 : s.gpr .r4 = dp s₀ + BitVec.ofNat 64 c
  r6 : s.gpr .r6 = BitVec.ofNat 64 (dl s₀ - c)
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s

/-- The buffer and the data are the whole blocks `X`, absorbed, followed by
`Y`, in the buffer. -/
structure Done (s₀ : State) (s : State) : Prop extends UCommon s₀ s where
  done : ∃ X Y : List Byte, Acc s₀ X s ∧ X.length % 16 = 0 ∧ Y.length < 16 ∧
    Bf s₀ ++ Dt s₀ (dl s₀) = X ++ Y ∧ bytesAt s.mem (off (st s₀) 56) Y.length = Y

theorem UCommon.of_regs {s₀ s s' : State} (h : UCommon s₀ s)
    (hg : ∀ r ∈ [Reg.r3, .r20, .r21], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : UCommon s₀ s' where
  r3 := by rw [hg _ (by simp)]; exact h.r3
  r21 := by rw [hg _ (by simp)]; exact h.r21
  mask := by rw [hg _ (by simp)]; exact h.mask
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  frame := by rw [hm]; exact h.frame
  coefs := by rw [hm]; exact h.coefs

/-- Writing the buffer keeps what holds throughout. -/
theorem UCommon.of_buf {s₀ s s' : State} (h : UCommon s₀ s)
    (hg : ∀ r ∈ [Reg.r3, .r20, .r21], s'.gpr r = s.gpr r)
    (hm : Frame [bfR (st s₀)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : UCommon s₀ s' where
  r3 := by rw [hg _ (by simp)]; exact h.r3
  r21 := by rw [hg _ (by simp)]; exact h.r21
  mask := by rw [hg _ (by simp)]; exact h.mask
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  frame := h.frame.trans (hm.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨wR (st s₀), List.mem_singleton_self _, bfR_sub_wR _⟩)
  coefs := h.coefs.frame hm

theorem Acc.of_regs {s₀ s s' : State} {X : List Byte} (h : Acc s₀ X s)
    (hg : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) : Acc s₀ X s' := by
  intro hA
  obtain ⟨h1, h2⟩ := h hA
  obtain ⟨e, b⟩ := bounds_eq hg
  exact ⟨by rw [e]; exact h1, b h2⟩

/-- The registers `r` other than those of `l` are kept, so those of `l'`. -/
theorem keep_of {s s' : State} {l : List Reg} (h : ∀ r, r ∉ l → s'.gpr r = s.gpr r) {l' : List Reg}
    (hl : (l'.all fun r => !l.contains r) = true := by decide) : ∀ r ∈ l', s'.gpr r = s.gpr r :=
  fun r hr => h r (by
    have := List.all_eq_true.mp hl r hr
    simpa using this)

/-- Bytes of data read from memory the code has written only in the working space. -/
theorem UPre.data {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {i : Nat}
    (hi : i < dl s₀) : m (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := dR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.st_d.symm.sub_right (sub_sR _ (by decide))) (show dl s₀ ≤ 2 ^ 64 by have := dl_lt s₀; omega_using [this]) hi

/-- The source of a copy from the data. -/
theorem UPre.srcOk {s₀ : State} (hp : UPre s₀) {s : State} (hc : UCommon s₀ s) {c n : Nat}
    (h : c + n ≤ dl s₀) : SrcOk s s₀.mem (dp s₀ + BitVec.ofNat 64 c) n := by
  intro i hi
  have e : dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (c + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine ⟨⟨dR s₀, by rw [hc.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    contains_off (by omega_using [h, hi]) (by have := dl_lt s₀; omega_using [h, hi, this])⟩, fun hb => ?_, hp.data hc.frame (by omega_using [h, hi])⟩
  rw [hc.r3] at hb
  exact hp.st_d _ (sub_sR _ (by decide) _ hb) (contains_off (by omega_using [h, hi]) (by have := dl_lt s₀; omega_using [h, hi, this]))

theorem UCommon.in_st {s₀ : State} (hp : UPre s₀) {s : State} (h : UCommon s₀ s) :
    sR (s.gpr .r3) ∈ s.wr := by
  rw [h.wr, h.r3]; exact hp.wr

/-- A state that differs from `s` only in the registers `r4`–`r6`, `r12`, `r14`–`r19` and `r0`. -/
def Temps (s s' : State) : Prop :=
  (∀ r ∈ [Reg.r3, .r7, .r8, .r9, .r10, .r11, .r20, .r21], s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
    s'.rd = s.rd ∧ s'.wr = s.wr

theorem Temps.ucommon {s₀ s s' : State} (h : UCommon s₀ s) (ht : Temps s s') : UCommon s₀ s' :=
  h.of_regs (fun r hr => ht.1 r (by revert hr; decide +revert)) ht.2.1 ht.2.2.1 ht.2.2.2

theorem Temps.acc {s₀ s s' : State} {X : List Byte} (h : Acc s₀ X s) (ht : Temps s s') : Acc s₀ X s' :=
  h.of_regs fun r hr => ht.1 r (by revert hr; decide +revert)

theorem Temps.done {s₀ s s' : State} (h : Done s₀ s) (ht : Temps s s') : Done s₀ s' := by
  obtain ⟨X, Y, a, b, c, d, e⟩ := h.done
  exact { Temps.ucommon h.toUCommon ht with done := ⟨X, Y, Temps.acc a ht, b, c, d, by rw [ht.2.1]; exact e⟩ }

/-! ## Prologue -/

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (setup ++ ([.li .r12 15, .logic .and .r12 .r4 .r12] : List Instr))) s₀ (Pre1 s₀) := by
  refine WP.block_append (WP.mono (setup_ok s₀ hp.wr) fun s₁ h₁ => ?_)
  refine wp_li (by decide) fun s₂ u₂ => wp_and fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → s₃.gpr r = s₁.gpr r := fun r h => by rw [u₃.other r h, u₂.other r h]
  have hm₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
  have c : UCommon s₀ s₃ :=
    { r3 := by rw [g _ (by decide), h₁.gpr .r3 (by decide)]
      r21 := by rw [g _ (by decide), h₁.gpr .r21 (by decide)]
      mask := by rw [g _ (by decide), h₁.mask]
      rd := by rw [u₃.rd, u₂.rd, h₁.rd]
      wr := by rw [u₃.wr, u₂.wr, h₁.wr]
      frame := by
        rw [hm₃]
        exact h₁.frame.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨wR (st s₀), List.mem_singleton_self _, cR_sub_wR _⟩
      coefs := by rw [hm₃]; exact h₁.coefs }
  refine { c with
    r5 := by rw [g _ (by decide), h₁.gpr .r5 (by decide)]
    r6 := by rw [g _ (by decide), h₁.gpr .r6 (by decide)]
    r12 := by rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, h₁.gpr .r4 (by decide), and15]
    buf := ?_
    acc := fun hA => ?_ }
  · rw [hm₃]
    have := kb_lt s₀
    refine bytesAt_frame h₁.frame (fun r hr => ?_) (by omega_using [this])
    simp only [List.mem_singleton] at hr; subst hr
    exact buf_disjoint_cR _ (by omega_using [this])
  · obtain ⟨e, b⟩ := h₁.acc hA
    obtain ⟨e', b'⟩ := bounds_eq (s := s₁) (s' := s₃) (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    exact ⟨by rw [e', e, Poly1305.absorbAll_nil], b' b⟩

/-- Nothing buffered: nothing of the data is consumed yet. -/
theorem Pre1.cons {s₀ s : State} (h : Pre1 s₀ s) (hk : kb s₀ = 0) : Cons s₀ 0 s :=
  { h.toUCommon with
    c_le := Nat.zero_le _, whole := by rw [hk]
    r5 := by rw [h.r5, add_ofNat_zero]
    r6 := by rw [h.r6, x3_eq, Nat.sub_zero]
    acc := by
      have e : Bf s₀ ++ Dt s₀ 0 = [] := by simp only [Bf, Dt, hk]; rfl
      rw [e]; exact h.acc }

/-! ## Filling the buffer -/

/-- The sign of `a - b`, for `a, b < 2⁶³`. -/
theorem sign_sub {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 == 0) = decide (b ≤ a) := by
  have e : ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63).toNat = if b ≤ a then 0 else 1 := by
    rw [lsr_toNat, BitVec.toNat_sub, toNat_ofNat_lt (by omega_using [hb]), toNat_ofNat_lt (by omega_using [ha])]
    split <;> omega
  by_cases h : b ≤ a
  · simp only [h, decide_true]
    simp only [h, ↓reduceIte] at e
    simpa using BitVec.eq_of_toNat_eq (y := 0) (by rw [e]; rfl)
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h0
    simp only [h, ↓reduceIte, h0] at e
    exact absurd e (by decide)

/-- After the count: `n = min(16 - kb, dl)` bytes to copy. -/
structure Counted (s₀ : State) (n : Nat) (s : State) : Prop extends UCommon s₀ s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  r4 : s.gpr .r4 = dp s₀
  r6 : s.gpr .r6 = BitVec.ofNat 64 (dl s₀ - n)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀ + n)
  r14 : s.gpr .r14 = BitVec.ofNat 64 n
  r15 : s.gpr .r15 = st s₀ + BitVec.ofNat 64 (kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s

theorem Pre1.temps {s₀ s s' : State} (h : Pre1 s₀ s) (ht : Temps s s')
    (hx2 : s'.gpr .r5 = s.gpr .r5) (hx3 : s'.gpr .r6 = s.gpr .r6) (hx9 : s'.gpr .r12 = s.gpr .r12) :
    Pre1 s₀ s' :=
  { Temps.ucommon h.toUCommon ht with
    r5 := hx2.trans h.r5, r6 := hx3.trans h.r6, r12 := hx9.trans h.r12, buf := by rw [ht.2.1]; exact h.buf
    acc := Temps.acc h.acc ht }

theorem count_ok {s₀ : State} {s : State} (h : Pre1 s₀ s) :
    WP isa count s (Counted s₀ (min (16 - kb s₀) (dl s₀))) := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have hx10 : s₃.gpr .r14 = BitVec.ofNat 64 (16 - kb s₀) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.r12,
      sub_ofNat (by omega_using [hkl])]
  have hx11 : (s₃.gpr .r15 == 0) = decide (dl s₀ < 16) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r6]
    have e : (s₀.gpr .r6).toNat = dl s₀ := rfl
    by_cases hd : dl s₀ < 16
    · simp only [hd, decide_true]
      exact beq_iff_eq.mpr (BitVec.eq_of_toNat_eq (by rw [lsr_toNat]; simp; omega_using [hd]))
    · simp only [hd, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [lsr_toNat] at this
      simp at this; omega_using [hdl, e, hd, this]
  have ht₃ : Temps s s₃ := ⟨fun r hr => by
    rw [u₃.other r (by revert hr; decide +revert), u₂.other r (by revert hr; decide +revert),
      u₁.other r (by revert hr; decide +revert)], by rw [u₃.mem, u₂.mem, u₁.mem],
    by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  have hP₃ : Pre1 s₀ s₃ := h.temps ht₃ (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)])
  -- `x10 = n`.
  refine WP.seq (WP.mono (Q := fun s₄ : State => Pre1 s₀ s₄ ∧
      s₄.gpr .r14 = BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀))) ?_ fun s₄ ⟨hP₄, hx10₄⟩ => ?_)
  · refine WP.ite (decide (dl s₀ < 16)) (by rw [eval_zero, hx11]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_sub fun s₄ u₄ => wp_lsr (by decide) fun s₅ u₅ => WP.block_nil ?_)
      have ht₅ : Temps s₃ s₅ := ⟨fun r hr => by
        rw [u₅.other r (by revert hr; decide +revert), u₄.other r (by revert hr; decide +revert)],
        by rw [u₅.mem, u₄.mem], by rw [u₅.rd, u₄.rd], by rw [u₅.wr, u₄.wr]⟩
      have hP₅ : Pre1 s₀ s₅ := hP₃.temps ht₅ (by rw [u₅.other _ (by decide), u₄.other _ (by decide)])
        (by rw [u₅.other _ (by decide), u₄.other _ (by decide)])
        (by rw [u₅.other _ (by decide), u₄.other _ (by decide)])
      have hx12 : (s₅.gpr .r16 == 0) = decide (16 - kb s₀ ≤ dl s₀) := by
        rw [u₅.gpr, u₄.gpr, hP₃.r6, x3_eq, hx10]
        exact sign_sub (by omega_using [hdl, hb]) (by omega_using [hkl])
      have hx10₅ : s₅.gpr .r14 = s₃.gpr .r14 := by rw [u₅.other _ (by decide), u₄.other _ (by decide)]
      refine WP.ite (decide (16 - kb s₀ ≤ dl s₀)) (by rw [eval_zero, hx12]) (fun hc => ?_) (fun hc => ?_)
      · simp only [decide_eq_true_eq] at hc
        exact WP.block_nil ⟨hP₅, by rw [hx10₅, hx10, Nat.min_eq_left hc]⟩
      · simp only [decide_eq_false_iff_not, Nat.not_le] at hc
        refine wp_addi (by decide) (by decide) fun s₆ u₆ => WP.block_nil ⟨hP₅.temps ⟨fun r hr => u₆.other r
          (by revert hr; decide +revert), u₆.mem, u₆.rd, u₆.wr⟩ (u₆.other _ (by decide))
          (u₆.other _ (by decide)) (u₆.other _ (by decide)), ?_⟩
        rw [u₆.gpr, hP₅.r6, x3_eq, add_ofNat_zero, Nat.min_eq_right (by omega_using [hc])]
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      exact WP.block_nil ⟨hP₃, by rw [hx10, Nat.min_eq_left (by omega_using [hkl, hdl, hb])]⟩
  · refine wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => wp_add fun s₇ u₇ => wp_addi (by decide) (by decide)
      fun s₈ u₈ => WP.block_nil ?_
    have ht : Temps s₄ s₈ := ⟨fun r hr => by
      rw [u₈.other r (by revert hr; decide +revert), u₇.other r (by revert hr; decide +revert),
        u₆.other r (by revert hr; decide +revert), u₅.other r (by revert hr; decide +revert)],
      by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem], by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd],
      by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr]⟩
    have hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
    have hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
      have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega_using [hkl, this]
    refine { Temps.ucommon hP₄.toUCommon ht with
      n_le := hn, n_le' := hn'
      r4 := by rw [u₈.gpr, u₇.other .r5 (by decide), u₆.other .r5 (by decide), u₅.other .r5 (by decide),
        hP₄.r5, add_ofNat_zero]
      r6 := by rw [u₈.other .r6 (by decide), u₇.other .r6 (by decide), u₆.other .r6 (by decide), u₅.gpr,
        hP₄.r6, x3_eq, hx10₄, sub_ofNat hn]
      r12 := by rw [u₈.other .r12 (by decide), u₇.gpr, u₆.other .r12 (by decide), u₆.other .r14 (by decide),
        u₅.other .r12 (by decide), u₅.other .r14 (by decide), hP₄.r12, hx10₄, ← BitVec.ofNat_add]
      r14 := by rw [u₈.other .r14 (by decide), u₇.other .r14 (by decide), u₆.other .r14 (by decide),
        u₅.other .r14 (by decide), hx10₄]
      r15 := by rw [u₈.other .r15 (by decide), u₇.other .r15 (by decide), u₆.gpr, u₅.other .r3 (by decide),
        u₅.other .r12 (by decide), hP₄.r3, hP₄.r12]
      buf := by rw [ht.2.1]; exact hP₄.buf
      acc := Temps.acc hP₄.acc ht }

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (n : Nat) (s : State) : Prop extends UCommon s₀ s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  r4 : s.gpr .r4 = dp s₀ + BitVec.ofNat 64 n
  r6 : s.gpr .r6 = BitVec.ofNat 64 (dl s₀ - n)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (kb s₀ + n)
  buf : bytesAt s.mem (off (st s₀) 56) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n
  acc : Acc s₀ [] s

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {s : State} {n : Nat} (h : Counted s₀ n s) :
    WP isa (.ite (.zero .d .r14) (.block []) copyIn) s (Filled s₀ n) := by
  have hdl := dl_lt s₀
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.r14, ofNat_beq_zero (by have := h.n_le; omega_using [hdl, this])])
    (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil { h.toUCommon with
      n_le := h.n_le, n_le' := h.n_le', r4 := by rw [h.r4, add_ofNat_zero], r6 := h.r6, r12 := h.r12
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt]
      acc := h.acc }
  · simp only [decide_eq_false_iff_not] at h0
    have hsrc := hp.srcOk h.toUCommon (c := 0) (n := n) (by have := h.n_le; omega_using [this])
    refine WP.mono (copy_ok (j0 := kb s₀) h.n_le' (by omega_using [h0]) (h.toUCommon.in_st hp) hsrc
      (by rw [h.r4, add_ofNat_zero]) (by rw [h.r15, h.r3]) h.r14) fun s' hc => ?_
    have hU : UCommon s₀ s' := h.toUCommon.of_buf (keep_of (l := [.r4, .r14, .r15, .r16])
        (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
                        exact hc.keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2))
      (by rw [← h.r3]; exact hc.frame h.n_le') hc.rd hc.wr
    have hk : ∀ r, r ∉ [Reg.r4, .r14, .r15, .r16] → s'.gpr r = s.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hc.keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    refine { hU with
      n_le := h.n_le, n_le' := h.n_le', r4 := by rw [hc.r4, add_ofNat_zero]
      r6 := by rw [hk _ (by decide), h.r6]
      r12 := by rw [hk _ (by decide), h.r12]
      buf := ?_
      acc := h.acc.of_regs (keep_of hk) }
    have hb := hc.buf h.n_le'
    rw [h.r3, h.buf] at hb
    rw [hb]
    simp [Dt]

theorem temps_of {s s' : State} (h : ∀ r ∈ [Reg.r3, .r7, .r8, .r9, .r10, .r11, .r20, .r21], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Temps s s' :=
  ⟨h, hm, hrd, hwr⟩

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Pre1 s₀ s) :
    WP isa fill s fun s' => (∃ c, Cons s₀ c s') ∨ (Done s₀ s' ∧ s'.gpr .r6 = 0) := by
  have hkl := kb_lt s₀
  have hdl := dl_lt s₀
  refine WP.seq (WP.mono (count_ok h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (wp_addi (by decide) (by decide) fun s₃ u₃ => wp_subi (by decide) (by decide) fun s₄ u₄ => WP.block_nil ?_)
  have hn := h₂.n_le; have hn' := h₂.n_le'
  have ht : Temps s₂ s₄ := temps_of (fun r hr => by
      rw [u₄.other r (by revert hr; decide +revert), u₃.other r (by revert hr; decide +revert)])
    (by rw [u₄.mem, u₃.mem]) (by rw [u₄.rd, u₃.rd]) (by rw [u₄.wr, u₃.wr])
  have hU : UCommon s₀ s₄ := Temps.ucommon h₂.toUCommon ht
  have hx2 : s₄.gpr .r5 = dp s₀ + BitVec.ofNat 64 (min (16 - kb s₀) (dl s₀)) := by
    rw [u₄.other _ (by decide), u₃.gpr, h₂.r4, add_ofNat_zero]
  have hx3 : s₄.gpr .r6 = BitVec.ofNat 64 (dl s₀ - min (16 - kb s₀) (dl s₀)) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), h₂.r6]
  have hx12 : (s₄.gpr .r16 == 0) = decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16) := by
    rw [u₄.gpr, u₃.other _ (by decide), h₂.r12]
    exact sub_beq (by omega_using [hn']) (by decide)
  have hacc : Acc s₀ [] s₄ := Temps.acc h₂.acc ht
  have hbuf : bytesAt s₄.mem (off (st s₀) 56) (kb s₀ + min (16 - kb s₀) (dl s₀)) =
      Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)) := by rw [ht.2.1]; exact h₂.buf
  have hl : (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀))).length = kb s₀ + min (16 - kb s₀) (dl s₀) := by
    simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16)) (by rw [eval_zero, hx12])
    (fun hf => ?_) (fun hf => ?_)
  · simp only [decide_eq_true_eq] at hf
    refine WP.mono (absorbBuf_ok s₄ true (Rk_lt s₀.mem (st s₀)) hU.mask (by rw [hU.r3]; exact hU.coefs)
      (hU.in_st hp)) fun s' ⟨ha, k⟩ => .inl ⟨min (16 - kb s₀) (dl s₀), ?_⟩
    refine { hU.of_regs (keep_of k.1) k.2.1 k.2.2.1 k.2.2.2 with
      c_le := hn, whole := by rw [hf]
      r5 := by rw [k.gpr' (r := .r5)]; exact hx2
      r6 := by rw [k.gpr' (r := .r6)]; exact hx3
      acc := fun hA => ?_ }
    obtain ⟨hv, hb⟩ := hacc hA
    obtain ⟨hv', hb'⟩ := ha hb
    refine ⟨?_, hb'⟩
    have e : leNum (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)) ++ [0x01]) =
        leNum (Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀))) + 2 ^ 128 * true.toNat := by
      rw [Poly1305.leNum_append, hl, hf]; rfl
    rw [Poly1305.absorbAll_nil] at hv
    have hbuf16 := hbuf
    rw [hf] at hbuf16
    rw [hv', hU.r3, hbuf16, mod_step hv, Poly1305.absorbAll_block (by omega_using [hl, hf]) (by omega_using [hl, hf]), e]
  · simp only [decide_eq_false_iff_not] at hf
    have hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega_using [hkl, hn, hn', hl, hf]
    refine WP.block_nil (.inr ⟨{ hU with
      done := ⟨[], Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)), hacc, rfl, by omega_using [hn', hl, hf], ?_, ?_⟩ }, ?_⟩)
    · rw [hnd, List.nil_append]
    · rw [hl]; exact hbuf
    · rw [hx3, hnd, Nat.sub_self]; rfl

/-! ## Whole blocks of data -/

/-- The data's words, as numbers: its bytes from `dp + c`. -/
theorem data_value {s₀ : State} (hp : UPre s₀) {m : Mem} (hf : Frame [wR (st s₀)] s₀.mem m) {c : Nat}
    (hc : c + 16 ≤ dl s₀) :
    w64 m (dp s₀ + BitVec.ofNat 64 c) 0 + 2 ^ 64 * w64 m (dp s₀ + BitVec.ofNat 64 c) 8 +
        2 ^ 128 * true.toNat =
      leNum (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 ++ [0x01]) := by
  have hdl := dl_lt s₀
  have hw : ∀ d : Nat, d + 8 ≤ 16 → m.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 d) 64 =
      s₀.mem.readW (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 d) 64 := by
    intro d hd
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    refine hf.readW (r := dR s₀) (contains_off (n := 64 / 8) (by omega_using [hc, hd]) (by omega_using [hc, hdl, hd])) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    exact hp.st_d.symm.sub_right (sub_sR _ (by decide))
  simp only [w64]
  rw [hw 0 (by decide), hw 8 (by decide), Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

/-- One whole block of data. -/
theorem whole_step {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : ConsB s₀ c s)
    (hc : 16 ≤ dl s₀ - c) :
    WP isa (.block (absorb true ++ ([.addi .r4 .r4 16, .subi .r6 .r6 16, .lsr .d .r5 .r6 4] : List Instr))) s
      fun s' => ConsB s₀ (c + 16) s' ∧ s'.gpr .r5 = BitVec.ofNat 64 ((dl s₀ - (c + 16)) / 16) := by
  have hdl := dl_lt s₀
  have hin : ∀ d : Nat, d + 8 ≤ 16 →
      InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [h.rd, h.r4, hp.rd, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega_using [hc, hd]) (by omega_using [hc, hdl, hd])⟩
  refine WP.block_append (WP.mono (absorb_ok s true (Rk_lt s₀.mem (st s₀)) h.mask (by rw [h.r3]; exact h.coefs)
    (coefIn_of (h.toUCommon.in_st hp)) (hin 0 (by decide)) (hin (0 + 8) (by decide))) fun s₁ ⟨ha, k₁⟩ => ?_)
  refine wp_addi (by decide) (by decide) fun s₂ u₂ => wp_subi (by decide) (by decide) fun s₃ u₃ =>
    wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_
  have ht : Temps s₁ s₄ := temps_of (fun r hr => by
      rw [u₄.other r (by revert hr; decide +revert), u₃.other r (by revert hr; decide +revert),
        u₂.other r (by revert hr; decide +revert)])
    (by rw [u₄.mem, u₃.mem, u₂.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr])
  have hU₁ : UCommon s₀ s₁ := h.toUCommon.of_regs (keep_of k₁.1) k₁.2.1 k₁.2.2.1 k₁.2.2.2
  have hx3 : s₄.gpr .r6 = BitVec.ofNat 64 (dl s₀ - (c + 16)) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), k₁.gpr' (r := .r6), h.r6,
      sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  refine ⟨{ Temps.ucommon hU₁ ht with
    c_le := by omega_using [hc]
    whole := by have := h.whole; omega_using [this]
    r4 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, k₁.gpr' (r := .r4), h.r4,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    r6 := hx3
    acc := fun hA => ?_ }, ?_⟩
  · obtain ⟨hv, hb⟩ := h.acc hA
    obtain ⟨hv', hb'⟩ := ha hb
    obtain ⟨e, b⟩ := bounds_eq (s := s₁) (s' := s₄) (fun r hr => ht.1 r (by revert hr; decide +revert))
    refine ⟨?_, b hb'⟩
    have h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
      simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact h.whole
    have hb1 : 0 < (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length := by
      rw [Poly1305.length_bytesAt]; omega_using []
    have hb2 : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16).length ≤ 16 := by
      rw [Poly1305.length_bytesAt]
    rw [e, hv', h.r4, data_value hp h.frame (by omega_using [hc]), mod_step hv,
      show Dt s₀ (c + 16) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 16 from
        Poly1305.bytesAt_add _ _ _ _, ← List.append_assoc, Poly1305.absorbAll_append h16,
      Poly1305.absorbAll_block hb1 hb2]
  · apply BitVec.eq_of_toNat_eq
    rw [u₄.gpr, lsr_toNat, u₃.gpr, u₂.other _ (by decide), k₁.gpr' (r := .r6), h.r6, sub_ofNat (by omega_using [hc]),
      toNat_ofNat_lt (by omega_using [hdl]), toNat_ofNat_lt (by omega_using [hdl]), Nat.sub_sub]

/-- The loop over the whole blocks of data. -/
theorem whole_loop {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : ConsB s₀ c s)
    (hc : 16 ≤ dl s₀ - c) :
    WP isa (.loop (.block (absorb true ++ ([.addi .r4 .r4 16, .subi .r6 .r6 16,
      .lsr .d .r5 .r6 4] : List Instr))) (.nonzero .d .r5)) s fun s' => ∃ c', ConsB s₀ c' s' ∧ dl s₀ - c' < 16 := by
  have hdl := dl_lt s₀
  refine WP.loop (M := isa) (fun k s => ∃ c, k = dl s₀ - c ∧ ConsB s₀ c s ∧ 16 ≤ dl s₀ - c) ?_ _ s
    ⟨c, rfl, h, hc⟩
  rintro k s ⟨c, rfl, h, hc⟩
  refine WP.mono (whole_step hp h hc) fun s' ⟨h', hx2⟩ => ?_
  have hev : isa.eval (.nonzero .d .r5) s' = some (!decide ((dl s₀ - (c + 16)) / 16 = 0)) := by
    rw [eval_nonzero, hx2, show (BitVec.ofNat 64 ((dl s₀ - (c + 16)) / 16) != 0) =
      !(BitVec.ofNat 64 ((dl s₀ - (c + 16)) / 16) == 0) from rfl, ofNat_beq_zero (by omega_using [hdl])]
  by_cases hl : dl s₀ - (c + 16) < 16
  · exact .inl ⟨by rw [hev]; simp; omega_using [hl], c + 16, h', hl⟩
  · exact .inr ⟨by rw [hev]; simp; omega_using [hl], _, by omega_using [hl], c + 16, rfl, h', by omega_using [hl]⟩

theorem whole_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, Cons s₀ c s) ∨ (Done s₀ s ∧ s.gpr .r6 = 0)) :
    WP isa whole s fun s' => (∃ c, ConsB s₀ c s' ∧ dl s₀ - c < 16) ∨ (Done s₀ s' ∧ s'.gpr .r6 = 0) := by
  have hdl := dl_lt s₀
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have ht : Temps s s₂ := temps_of (fun r hr => by
      rw [u₂.other r (by revert hr; decide +revert), u₁.other r (by revert hr; decide +revert)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  have hx3 : s₂.gpr .r6 = s.gpr .r6 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have hx2 : s₂.gpr .r5 = s.gpr .r6 >>> 4 := by rw [u₂.gpr, u₁.other _ (by decide)]
  rcases h with ⟨c, hc⟩ | ⟨hd, hz⟩
  · have hb : ConsB s₀ c s₂ := { Temps.ucommon hc.toUCommon ht with
      c_le := hc.c_le, whole := hc.whole
      r4 := by rw [u₂.other _ (by decide), u₁.gpr, hc.r5, add_ofNat_zero]
      r6 := hx3.trans hc.r6, acc := Temps.acc hc.acc ht }
    have hq : s₂.gpr .r5 = BitVec.ofNat 64 ((dl s₀ - c) / 16) := by
      apply BitVec.eq_of_toNat_eq
      rw [hx2, lsr_toNat, hc.r6, toNat_ofNat_lt (by omega_using [hdl]), toNat_ofNat_lt (by omega_using [hdl])]
    refine WP.ite (decide (dl s₀ - c < 16)) (by
      rw [eval_zero, hq, ofNat_beq_zero (by omega_using [hdl])]; simp only [Option.some.injEq, decide_eq_decide]; omega_using [])
      (fun hl => ?_) (fun hl => ?_)
    · simp only [decide_eq_true_eq] at hl
      exact WP.block_nil (.inl ⟨c, hb, hl⟩)
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hl
      exact WP.mono (whole_loop hp hb hl) fun s' h' => .inl h'
  · have hq : s₂.gpr .r5 = 0 := by rw [hx2, hz]; rfl
    refine WP.ite true (by rw [eval_zero, hq]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    exact WP.block_nil (.inr ⟨Temps.done hd ht, hx3.trans hz⟩)

/-! ## The rest of the data -/

theorem rest_ok {s₀ : State} (hp : UPre s₀) {s : State}
    (h : (∃ c, ConsB s₀ c s ∧ dl s₀ - c < 16) ∨ (Done s₀ s ∧ s.gpr .r6 = 0)) :
    WP isa rest s (Done s₀) := by
  have hdl := dl_lt s₀
  rcases h with ⟨c, hc, hlt⟩ | ⟨hd, hz⟩
  · refine WP.ite (decide (dl s₀ - c = 0)) (by rw [eval_zero, hc.r6, ofNat_beq_zero (by omega_using [hlt])])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hcd : c = dl s₀ := by have := hc.c_le; omega_using [hb, this]
      refine WP.block_nil { hc.toUCommon with
        done := ⟨Bf s₀ ++ Dt s₀ c, [], hc.acc, ?_, by simp, by rw [hcd, List.append_nil], rfl⟩ }
      simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact hc.whole
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.seq (wp_addi (by decide) (by decide) fun s₂ u₂ => wp_addi (by decide) (by decide) fun s₃ u₃ => WP.block_nil ?_)
      have ht : Temps s s₃ := temps_of (fun r hr => by
          rw [u₃.other r (by revert hr; decide +revert), u₂.other r (by revert hr; decide +revert)])
        (by rw [u₃.mem, u₂.mem]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
      have hU₃ : UCommon s₀ s₃ := Temps.ucommon hc.toUCommon ht
      have hsrc := hp.srcOk hU₃ (c := c) (n := dl s₀ - c) (by omega_using [hlt, hb])
      refine WP.mono (copy_ok (j0 := 0) (by omega_using [hlt]) (by omega_using [hlt, hb]) (hU₃.in_st hp) hsrc
        (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact hc.r4)
        (by rw [u₃.gpr, u₃.other .r3 (by decide)])
        (by rw [u₃.other _ (by decide), u₂.gpr, hc.r6, add_ofNat_zero])) fun s' hcp => ?_
      have hk : ∀ r, r ∉ [Reg.r4, .r14, .r15, .r16] → s'.gpr r = s₃.gpr r := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact hcp.keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
      have hU' : UCommon s₀ s' := hU₃.of_buf (keep_of hk) (by rw [← hU₃.r3]; exact hcp.frame (by omega_using [hlt]))
        hcp.rd hcp.wr
      have hY : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c)).length = dl s₀ - c :=
        Poly1305.length_bytesAt _ _ _
      refine { hU' with
        done := ⟨Bf s₀ ++ Dt s₀ c, bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (dl s₀ - c),
          (Temps.acc hc.acc ht).of_regs (keep_of hk), ?_, by omega_using [hlt, hY], ?_, ?_⟩ }
      · simp only [List.length_append, Bf, Dt, Poly1305.length_bytesAt]; exact hc.whole
      · rw [List.append_assoc, show Dt s₀ (dl s₀) = Dt s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c)
          (dl s₀ - c) by rw [Dt, Dt, ← Poly1305.bytesAt_add]; congr 1; omega_using [hlt, hb, hY]]
      · have hb' := hcp.buf (by omega_using [hlt, hY])
        rw [hU₃.r3, Nat.zero_add] at hb'
        rw [hY, hb']
        rfl
  · refine WP.ite true (by rw [eval_zero, hz]; rfl) (fun _ => WP.block_nil hd) (fun h => absurd h (by decide))

/-! ## Epilogue -/

theorem storeHm_buf (m : Mem) (st : Addr) (w0 w1 w2 : BitVec 64) {n : Nat} (hn : n ≤ 16) :
    bytesAt (storeHm m st w0 w1 w2) (off st 56) n = bytesAt m (off st 56) n := by
  have hf : Frame [hR st] m (storeHm m st w0 w1 w2) := by
    have c : ∀ d, d + 8 ≤ 24 → (hR st).Contains (off st d) (64 / 8) := fun d hd => hR_contains st hd
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
      (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hn])
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base st (by decide) (by omega_using [hn])

theorem uepilogue_ok {s₀ : State} (hp : UPre s₀) {s : State} (hd : Done s₀ s) :
    WP isa (.block (reduce ++ pack ++ storeH)) s fun s' => Proof.Poly1305.updatePPC64LE.post s₀ s' ∧
      s'.gpr .r21 = s₀.gpr .r21 ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [hR (st s₀), wR (st s₀)] s₀.mem s'.mem := by
  refine WP.block_append (WP.block_append (WP.mono (reduce_ok s hd.mask) fun s₁ ⟨hr, k₁⟩ =>
    WP.mono (pack_ok s₁) fun s₂ ⟨hp₂, k₂⟩ => ?_))
  have x0₂ : s₂.gpr .r3 = st s₀ := by rw [k₂.gpr', k₁.gpr', hd.r3]
  refine WP.mono (storeH_ok s₂ (by rw [k₂.2.2.2, k₁.2.2.2, hd.wr, x0₂]; exact hp.wr))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_
  have mem₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  rw [x0₂, mem₂] at m₃
  have hf : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₃.mem := by
    rw [m₃]; exact storeHm_frame (hd.frame.mono (by simp)) _ _ _
  refine ⟨?_, by rw [g₃, k₂.gpr', k₁.gpr', hd.r21], by rw [rd₃, k₂.2.2.1, k₁.2.2.1, hd.rd],
    by rw [wr₃, k₂.2.2.2, k₁.2.2.2, hd.wr], hf⟩
  intro key msg hbuf hcnt
  obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
  have hk : kb s₀ = (W ++ B).length % 16 := hcnt
  have hBf : Bf s₀ = B := by rw [Bf, hk, off_56]; exact hBb
  obtain ⟨X, Y, hacc, hX, hY, hXY, hbufY⟩ := hd.done
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := hacc hA
  obtain ⟨hN, n0, n1, n2, n3, -⟩ := hr hb
  obtain ⟨w0, w1, w2⟩ := hp₂ n0 n1 n2 n3
  have hlen := hrep.1
  change Buffered s₃.mem (st s₀) key (W ++ B ++ Dt s₀ (dl s₀))
  rw [List.append_assoc, ← hBf, hXY, ← List.append_assoc]
  refine Buffered.of ⟨?_, ?_, ?_⟩ hY ?_
  · rw [List.length_append]; omega_using [hX, hlen]
  · rw [← off_24, key_frame hf]; exact repr_key hrep
  · rw [m₃, storeHm_acc, ← repr_key hrep, clamp_key, Poly1305.accumulate_append hlen, repr_acc hrep]
    have hV : val5 (v s₁ .r7) (v s₁ .r8) (v s₁ .r9) (v s₁ .r10) (v s₁ .r11) =
        Poly1305.absorbAll (Rn s₀) (A0 s₀) X := by
      rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
    change v s₂ .r18 + 2 ^ 64 * v s₂ .r19 + 2 ^ 128 * v s₂ .r0 = _
    rw [w0, w1, w2, words_val, hV]
  · rw [← off_56, m₃, storeHm_buf _ _ _ _ _ (by omega_using [hY]), hbufY]

/-! ## The whole function -/

/-- `update`'s precondition, from its contract's. -/
structure UPre₀ (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [sR (st s₀), savR (s₀.gpr .r7)]
  st_d : (sR (st s₀)).Disjoint (dR s₀)
  st_scr : (sR (st s₀)).Disjoint (savR (s₀.gpr .r7))
  d_scr : (dR s₀).Disjoint (savR (s₀.gpr .r7))

theorem UPre₀.of (s₀ : State) (h : Proof.Poly1305.updatePPC64LE.pre s₀) : UPre₀ s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem update_correct {s₀ : State} (hp₀ : UPre₀ s₀) :
    WP isa update s₀ fun s' => (∀ i < 8, s'.gpr (saved i) = s₀.gpr (saved i)) ∧
      Proof.Poly1305.updatePPC64LE.post s₀ s' := by
  have hsv := save_ok s₀ (w := .r7) (by decide)
    (by rw [hp₀.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  refine WP.seq (WP.block_append (WP.block_append (WP.mono hsv fun s₁ hs₁ => ?_)))
  have hg : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], s₁.gpr r = s₀.gpr r := fun r hr =>
    hs₁.gpr r (by revert r; decide)
  have hp : UPre s₁ := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [dR, dp, dl, hs₁.rd, hg .r5 (by decide), hg .r6 (by decide)]; exact hp₀.rd
    · rw [hs₁.wr, hp₀.wr, show st s₁ = s₀.gpr .r3 from hg .r3 (by decide)]; exact List.mem_cons_self
    · simp only [dR, dp, dl, st, hg .r3 (by decide), hg .r5 (by decide), hg .r6 (by decide)]
      exact hp₀.st_d
  refine WP.mono (WP.block_append_iff.mp (uprologue_ok hp)) fun s₂ h₂ => WP.mono h₂ fun s₃ h₃ => ?_
  refine WP.seq (WP.mono (Q := fun s : State => (∃ c, Cons s₁ c s) ∨ (Done s₁ s ∧ s.gpr .r6 = 0)) ?_
    fun s₄ h₄ => ?_)
  · refine WP.ite (decide (kb s₁ = 0))
      (by rw [eval_zero, h₃.r12, ofNat_beq_zero (by have := kb_lt s₁; omega_using [this])]) (fun h => ?_)
      (fun _ => fill_ok hp h₃)
    simp only [decide_eq_true_eq] at h
    exact WP.block_nil (.inl ⟨0, h₃.cons h⟩)
  refine WP.seq (WP.mono (whole_ok hp h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (rest_ok hp h₅) fun s₆ h₆ => ?_)
  refine WP.block_append (WP.mono (uepilogue_ok hp h₆) fun s₇ ⟨hpost, r21₇, rd₇, wr₇, hf₇⟩ => ?_)
  have hst : st s₁ = s₀.gpr .r3 := hg .r3 (by decide)
  have hdj : ∀ r ∈ [hR (st s₁), wR (st s₁)], (savR (s₀.gpr .r7)).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₀.st_scr.symm.sub_right (by rw [hst]; exact hR_sub_sR _)
    · exact hp₀.st_scr.symm.sub_right (by rw [hst]; exact sub_sR _ (by decide))
  have hsav : ∀ i < 8, s₇.mem.readW (off (s₀.gpr .r7) (8 * i)) 64 = s₀.gpr (saved i) := by
    intro i hi
    rw [hf₇.readW (r := savR (s₀.gpr .r7)) (w := 64) (sav_contains _ hi) hdj (by decide)]
    exact hs₁.saved i hi
  refine WP.mono (restore_ok s₇ (w := s₀.gpr .r7) (v := fun i => s₀.gpr (saved i))
    (by rw [r21₇, hs₁.r21])
    (by rw [wr₇, hs₁.wr, hp₀.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self) hsav)
    fun s' ⟨hr, _, hm', _, _⟩ => ⟨hr, fun key msg hbuf hcnt => ?_⟩
  have hb₁ : Buffered s₁.mem (s₁.gpr .r3) key msg := by
    rw [hg .r3 (by decide)]
    refine Proof.Poly1305.buffered_congr (fun i hi => ?_) hbuf
    refine hs₁.frame.bytes (R := sR (s₀.gpr .r3)) (fun r hr => ?_) (show (128 : Nat) ≤ 2 ^ 64 by decide) hi
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp₀.st_scr
  have h := hpost key msg hb₁ (by rw [hg .r4 (by decide)]; exact hcnt)
  have hbl : bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat =
      bytesAt s₀.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat := by
    rw [hg .r5 (by decide), hg .r6 (by decide)]
    refine Proof.Poly1305.bytesAt_congr' fun i hi => hs₁.frame.bytes (R := dR s₀) (fun r hr => ?_)
      (Nat.le_of_lt (dl_lt s₀)) hi
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp₀.d_scr
  rw [hg .r3 (by decide), hbl] at h
  rw [hm']
  exact h

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 128⟩]

theorem update_untouched : Untouched update keepRegs :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem update_verified : Verified PPC64LE.target update Proof.Poly1305.updatePPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ⟨updateSat, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩⟩
  · obtain ⟨t, s', he, hr, h⟩ := update_correct (UPre₀.of s hs)
    refine ⟨t, s', he, ⟨fun r hr' => ?_, Exec.sp he,
      Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
    rcases preserved_cases r hr' with ⟨i, hi, rfl⟩ | hk'
    · exact hr i hi
    · exact Exec.gpr (update_untouched r hk') he
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Poly1305.PPC64LE
