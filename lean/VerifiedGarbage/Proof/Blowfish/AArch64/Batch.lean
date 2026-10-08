import VerifiedGarbage.Proof.Blowfish.AArch64.Cipher
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A batch of sixteen blocks

`loadBatch_run`: the sixteen blocks at `x4` into `A` (xL) and `B` (xR), as
big-endian words. `storeBatch_run`: xL from `B` and xR from `A` back, as
blocks.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Blowfish.AArch64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.AArch64.Tbl (VOnly)

def ioRegs : List VReg := [.v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27]

/-- Word `w` of a reversed 16-byte load: the big-endian word at `4 w`, which
is half `w % 2` of block `w / 2`. -/
theorem vword_rev_read (m : Mem) (a : Addr) {w : Nat} (hw : w < 4) :
    vword (VRevOp.eval .rev32b (m.read a 16)) w =
      decodeWord (blockAt m (a + BitVec.ofNat 64 (8 * (w / 2)))) (4 * (w % 2)) := by
  refine word_ext fun b hb => ?_
  rw [← vbyte_word _ hb, vbyte_rev32b _ (by omega), vbyte_read16 _ _ (by omega), decodeWord_byte _ _ hb,
    blockAt_getD _ _ (by omega), Offset.add_add,
    show 4 * ((4 * w + b) / 4) + (3 - (4 * w + b) % 4) = 8 * (w / 2) + (4 * (w % 2) + (3 - b)) by omega]

theorem ldrq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (t.rd ++ t.wr) (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.ldrq d n off] t = some t' ∧
      t'.v d = t.mem.read (t.gpr n + BitVec.ofNat 64 off) 16 ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, exec_ldrq ho h, runStep_some, runBlock_nil], v_setV_self _ _ _,
    VOnly.setV _ (by simp) _⟩

theorem vop_run {t : State} (op : VOp) (d : VReg) (x : BitVec 128) (h : exec (.vop op) t = some (t.setV d x)) :
    ∃ t', runBlock isa [.vop op] t = some t' ∧ t'.v d = x ∧ VOnly [d] t t' :=
  ⟨_, by rw [runBlock_cons, h, runStep_some, runBlock_nil], v_setV_self _ _ _, VOnly.setV _ (by simp) _⟩

/-- Chaining two steps that each change one register. -/
theorem cat_run {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ :=
  VG.AArch64.Tbl.runBlock_cat_some h₁ h₂

theorem ab_ne : ∀ k < 4, aReg k ≠ .v20 ∧ aReg k ≠ .v21 ∧ bReg k ≠ .v20 ∧ bReg k ≠ .v21 ∧ aReg k ≠ bReg k := by
  decide

/-- Blocks `4 k`…`4 k + 3` into word `k` of `A` and `B`. -/
theorem loadPair_run {s : State} {k : Nat} (hk : k < 4)
    (hR : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (loadPair .x4 k) s = some s' ∧
      (∀ l < 4, vword (s'.v (aReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 0) ∧
      (∀ l < 4, vword (s'.v (bReg k)) l =
        decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * (4 * k + l)))) 4) ∧
      VOnly [.v20, .v21, aReg k, bReg k] s s' := by
  have ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := ldrq_run (t := s) .v20 .x4 (off := 32 * k) (by omega)
    (by have := hR 0 (by decide); simpa using this)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := ldrq_run (t := s₁) .v21 .x4 (off := 32 * k + 16) (by omega)
    (by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hR 1 (by decide))
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  obtain ⟨s₅, r₅, v₅, o₅⟩ := vop_run (t := s₄) (.perm .uzp1 .s4 (aReg k) .v20 .v21) (aReg k) _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₆, r₆, v₆, o₆⟩ := vop_run (t := s₅) (.perm .uzp2 .s4 (bReg k) .v20 .v21) (bReg k) _
    (exec_vperm _ _ _ _ _ _)
  -- the two reversed loads
  have m₁ : s₁.mem = s.mem := o₁.mem
  have g₁ : s₁.gpr = s.gpr := o₁.gpr
  have w20 : s₄.v .v20 = VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k)) 16) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  have w21 : s₄.v .v21 =
      VRevOp.eval .rev32b (s.mem.read (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16)) 16) := by
    rw [v₄, o₃.2 _ (by simp), v₂, m₁, g₁]
  have w20' : s₅.v .v20 = s₄.v .v20 := o₅.2 _ (by simp; exact ne.1.symm)
  have w21' : s₅.v .v21 = s₄.v .v21 := o₅.2 _ (by simp; exact ne.2.1.symm)
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), ?_, ?_, ?_⟩
  · intro l hl
    rw [o₆.2 _ (by simp; exact ne.2.2.2.2), v₅, vword_uzp1 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega), Offset.add_add, show 32 * k + 8 * (2 * l / 2) = 8 * (4 * k + l) by omega,
        show 4 * (2 * l % 2) = 0 by omega]
    · rw [vword_rev_read _ _ (by omega), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l - 4) / 2) = 8 * (4 * k + l) by omega,
        show 4 * ((2 * l - 4) % 2) = 0 by omega]
  · intro l hl
    rw [v₆, w20', w21', vword_uzp2 _ _ hl, w20, w21]
    split
    · rw [vword_rev_read _ _ (by omega), Offset.add_add,
        show 32 * k + 8 * ((2 * l + 1) / 2) = 8 * (4 * k + l) by omega,
        show 4 * ((2 * l + 1) % 2) = 4 by omega]
    · rw [vword_rev_read _ _ (by omega), Offset.add_add,
        show 32 * k + 16 + 8 * ((2 * l + 1 - 4) / 2) = 8 * (4 * k + l) by omega,
        show 4 * ((2 * l + 1 - 4) % 2) = 4 by omega]
  · exact (((((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans (VOnly.mono o₃ (by simp))).trans
      (VOnly.mono o₄ (by simp))).trans (VOnly.mono o₅ (by simp))).trans (VOnly.mono o₆ (by simp))

theorem loadPair_eq : (List.range 4).flatMap (loadPair .x4) =
    loadPair .x4 0 ++ (loadPair .x4 1 ++ (loadPair .x4 2 ++ (loadPair .x4 3 ++ []))) := rfl

/-- The sixteen blocks at `x4` into `A` (xL) and `B` (xR). -/
theorem loadBatch_run {s : State}
    (hR : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (loadBatch .x4) s = some s' ∧
      (∀ n < 16, lane s'.v aReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 0) ∧
      (∀ n < 16, lane s'.v bReg n = decodeWord (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n))) 4) ∧
      VOnly (.v20 :: .v21 :: halfRegs) s s' := by
  have hR' : ∀ {t : State}, VOnly (.v20 :: .v21 :: halfRegs) s t → ∀ k < 4, ∀ j < 2,
      InRegions (t.rd ++ t.wr) (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.rd, ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega]
    exact hR _ (by omega)
  have sub : ∀ k < 4, ∀ r ∈ [VReg.v20, .v21, aReg k, bReg k], r ∈ VReg.v20 :: .v21 :: halfRegs := by decide
  obtain ⟨s₀, r₀, a₀, b₀, o₀⟩ := loadPair_run (s := s) (by decide : 0 < 4) (hR' (VOnly.refl _ _) 0 (by decide))
  have p₀ := VOnly.mono o₀ (sub 0 (by decide))
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadPair_run (s := s₀) (by decide : 1 < 4) (hR' p₀ 1 (by decide))
  have p₁ := p₀.trans (VOnly.mono o₁ (sub 1 (by decide)))
  obtain ⟨s₂, r₂, a₂, b₂, o₂⟩ := loadPair_run (s := s₁) (by decide : 2 < 4) (hR' p₁ 2 (by decide))
  have p₂ := p₁.trans (VOnly.mono o₂ (sub 2 (by decide)))
  obtain ⟨s₃, r₃, a₃, b₃, o₃⟩ := loadPair_run (s := s₂) (by decide : 3 < 4) (hR' p₂ 3 (by decide))
  have p₃ := p₂.trans (VOnly.mono o₃ (sub 3 (by decide)))
  refine ⟨s₃, by rw [loadBatch, loadPair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    ?_, ?_, p₃⟩
  all_goals
    intro n hn
    have m₀ := o₀.mem; have m₁ := o₁.mem; have m₂ := o₂.mem
    have g₀ := o₀.gpr; have g₁ := o₁.gpr; have g₂ := o₂.gpr
    have pres : ∀ k < 4, ∀ k' < 4, k ≠ k' → aReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] ∧
        bReg k ∉ [VReg.v20, .v21, aReg k', bReg k'] := by decide
    simp only [lane]
    rcases (by omega : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3) with h | h | h | h <;> rw [h]
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).1, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).1, a₀ _ (by omega)]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).1, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).1, a₁ _ (by omega), m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).1, a₂ _ (by omega), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [a₃ _ (by omega), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 0) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [o₃.2 _ (pres 0 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 0 (by decide) 2 (by decide) (by decide)).2, o₁.2 _ (pres 0 (by decide) 1 (by decide) (by decide)).2, b₀ _ (by omega)]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [o₃.2 _ (pres 1 (by decide) 3 (by decide) (by decide)).2, o₂.2 _ (pres 1 (by decide) 2 (by decide) (by decide)).2, b₁ _ (by omega), m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [o₃.2 _ (pres 2 (by decide) 3 (by decide) (by decide)).2, b₂ _ (by omega), m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega))))
  · rw [b₃ _ (by omega), m₂, g₂, m₁, g₁, m₀, g₀]
    exact congrArg (decodeWord · 4) (congrArg _ (congrArg _ (congrArg _ (by omega))))

/-! ## Storing -/

/-- Byte `j` (< 128) of the sixteen blocks whose halves are the words of `A`
and `B` (xL in `B`, xR in `A`). -/
def outByte (v : VReg → BitVec 128) (j : Nat) : Byte :=
  (encodeBlock (lane v bReg (j / 8)) (lane v aReg (j / 8))).getD (j % 8) 0

theorem write16_byte (m : Mem) (p : Addr) (x : BitVec 128) {o j : Nat} (ho : o + 16 ≤ 128) (hj : j < 128) :
    m.write (p + BitVec.ofNat 64 o) 16 x (p + BitVec.ofNat 64 j) =
      if o ≤ j ∧ j < o + 16 then vbyte x (j - o) else m (p + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.sub_toNat' p (show o < 2 ^ 64 by omega) (show j < 2 ^ 64 by omega)]
  by_cases h : o ≤ j
  · simp only [h, ite_true, true_and]
    by_cases h' : j < o + 16
    · simp only [show j - o < 16 by omega, h', ite_true]; rfl
    · simp only [show ¬ j - o < 16 by omega, h', ite_false]
  · simp only [h, ite_false, false_and]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- What `rev32 (zip1/zip2 .4s B A)` holds: byte `e` of it is byte `e % 8` of
block `2 o + e / 8` of the four in words `k` of `A` and `B`. -/
theorem stored_byte (Bk Ak : BitVec 128) {o e : Nat} (ho : o < 2) (he : e < 16) :
    vbyte (VRevOp.eval .rev32b (VPermOp.eval (if o = 0 then .zip1 else .zip2) .s4 Bk Ak)) e =
      (encodeBlock (vword Bk (2 * o + e / 8)) (vword Ak (2 * o + e / 8))).getD (e % 8) 0 := by
  rw [vbyte_rev32b _ he, vbyte_word _ (by omega), encodeBlock_getD _ _ (by omega)]
  have hw : (e / 4) / 2 = e / 8 := by omega
  rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), vword_zip1 _ _ (by omega), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega, show 2 * 0 + e / 8 = e / 8 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega, show 2 * 0 + e / 8 = e / 8 by omega]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), vword_zip2 _ _ (by omega), hw]
    by_cases h : e % 8 < 4
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h),
        show 3 - e % 4 = 3 - e % 8 by omega, show 2 * 1 + e / 8 = 2 + e / 8 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h),
        show 3 - e % 4 = 7 - e % 8 by omega, show 2 * 1 + e / 8 = 2 + e / 8 by omega]

/-- Only the memory and the vector registers `vs` change. -/
structure MOnly (vs : List VReg) (s s' : State) : Prop where
  eq : s' = { s with v := s'.v, mem := s'.mem }
  v : ∀ r, r ∉ vs → s'.v r = s.v r

theorem MOnly.trans {vs : List VReg} {a b c : State} (h₁ : MOnly vs a b) (h₂ : MOnly vs b c) : MOnly vs a c := by
  refine ⟨?_, fun r hr => (h₂.v r hr).trans (h₁.v r hr)⟩
  rw [h₂.eq, h₁.eq]

theorem MOnly.ofV {vs : List VReg} {a b : State} (h : VOnly vs a b) : MOnly vs a b :=
  ⟨by rw [h.1], h.2⟩

theorem MOnly.gpr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.gpr = a.gpr := by rw [h.eq]
theorem MOnly.rd {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.rd = a.rd := by rw [h.eq]
theorem MOnly.wr {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.wr = a.wr := by rw [h.eq]
theorem MOnly.sp {vs : List VReg} {a b : State} (h : MOnly vs a b) : b.sp = a.sp := by rw [h.eq]

theorem strq_run {t : State} (d : VReg) (n : Reg) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions t.wr (t.gpr n + BitVec.ofNat 64 off) 16) :
    ∃ t', runBlock isa [.strq d n off] t = some t' ∧
      t'.mem = t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) ∧ MOnly [] t t' :=
  ⟨{ t with mem := t.mem.write (t.gpr n + BitVec.ofNat 64 off) 16 (t.v d) },
    by rw [runBlock_cons, exec_strq ho h, runStep_some, runBlock_nil], rfl, ⟨rfl, fun _ _ => rfl⟩⟩

theorem storePair_run {s : State} {k : Nat} (hk : k < 4)
    (hW : ∀ j < 2, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16) :
    ∃ s', runBlock isa (storePair .x4 k) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) =
        if 32 * k ≤ j ∧ j < 32 * k + 32 then outByte s.v j else s.mem (s.gpr .x4 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  have ne := ab_ne k hk
  obtain ⟨s₁, r₁, v₁, o₁⟩ := vop_run (t := s) (.perm .zip1 .s4 .v20 (bReg k) (aReg k)) .v20 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₂, r₂, v₂, o₂⟩ := vop_run (t := s₁) (.perm .zip2 .s4 .v21 (bReg k) (aReg k)) .v21 _
    (exec_vperm _ _ _ _ _ _)
  obtain ⟨s₃, r₃, v₃, o₃⟩ := vop_run (t := s₂) (.rev .rev32b .v20 .v20) .v20 _ (exec_rev32b _ _ _)
  obtain ⟨s₄, r₄, v₄, o₄⟩ := vop_run (t := s₃) (.rev .rev32b .v21 .v21) .v21 _ (exec_rev32b _ _ _)
  have o₁₄ : VOnly [.v20, .v21] s s₄ := (((VOnly.mono o₁ (by simp)).trans (VOnly.mono o₂ (by simp))).trans
    (VOnly.mono o₃ (by simp))).trans (VOnly.mono o₄ (by simp))
  obtain ⟨s₅, r₅, m₅, o₅⟩ := strq_run (t := s₄) .v20 .x4 (off := 32 * k) (by omega)
    (by rw [o₁₄.wr, o₁₄.gpr]; simpa using hW 0 (by decide))
  obtain ⟨s₆, r₆, m₆, o₆⟩ := strq_run (t := s₅) .v21 .x4 (off := 32 * k + 16) (by omega)
    (by rw [o₅.wr, o₅.gpr, o₁₄.wr, o₁₄.gpr]; exact hW 1 (by decide))
  -- the values stored
  have x20 : s₄.v .v20 = VRevOp.eval .rev32b (VPermOp.eval .zip1 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₄.2 _ (by simp), v₃, o₂.2 _ (by simp), v₁]
  have x21 : s₅.v .v21 = VRevOp.eval .rev32b (VPermOp.eval .zip2 .s4 (s.v (bReg k)) (s.v (aReg k))) := by
    rw [o₅.v _ (by simp), v₄, o₃.2 _ (by simp), v₂, o₁.2 _ (by simp; exact ne.2.2.1),
      o₁.2 _ (by simp; exact ne.1)]
  have g₄' : s₄.gpr = s.gpr := o₁₄.gpr
  have g₅' : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄']
  have fr : Frame [⟨s.gpr .x4, 128⟩] s.mem s₆.mem := by
    rw [m₆, m₅, g₅', g₄', o₁₄.mem]
    exact ((Frame.refl _ _).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega) (by omega))).write (List.mem_singleton.mpr rfl) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨s₆, cat_run r₁ (cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ r₆)))), fun j hj => ?_, fr,
    (MOnly.ofV o₁₄).trans (o₅.trans o₆ |>.trans ⟨rfl, fun _ _ => rfl⟩ |> fun h => ⟨h.eq, fun r _ => h.v r (by simp)⟩)⟩
  have g₄ : s₄.gpr = s.gpr := o₁₄.gpr
  have g₅ : s₅.gpr = s.gpr := by rw [o₅.gpr, g₄]
  rw [m₆, g₅, show s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) = s.gpr .x4 + BitVec.ofNat 64 (32 * k + 16) from rfl,
    write16_byte _ _ _ (by omega) hj, m₅, g₄, write16_byte _ _ _ (by omega) hj, o₁₄.mem, x21, x20]
  have lane_k : ∀ (R : Nat → VReg) (e : Nat), e < 16 → ∀ o < 2,
      vword (s.v (R k)) (2 * o + e / 8) = lane s.v R (4 * k + (2 * o + e / 8)) := by
    intro R e he o ho
    simp only [lane]
    rw [show (4 * k + (2 * o + e / 8)) / 4 = k by omega, show (4 * k + (2 * o + e / 8)) % 4 = 2 * o + e / 8 by omega]
  by_cases h₂ : 32 * k + 16 ≤ j ∧ j < 32 * k + 16 + 16
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h₂), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      show VPermOp.zip2 = (if 1 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega),
      lane_k bReg _ (by omega) 1 (by decide), lane_k aReg _ (by omega) 1 (by decide), outByte,
      show 4 * k + (2 * 1 + (j - (32 * k + 16)) / 8) = j / 8 by omega,
      show (j - (32 * k + 16)) % 8 = j % 8 by omega]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h₂)]
    by_cases h₁ : 32 * k ≤ j ∧ j < 32 * k + 16
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h₁), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        show VPermOp.zip1 = (if 0 = 0 then .zip1 else .zip2) from rfl, stored_byte _ _ (by decide) (by omega),
        lane_k bReg _ (by omega) 0 (by decide), lane_k aReg _ (by omega) 0 (by decide), outByte,
        show 4 * k + (2 * 0 + (j - 32 * k) / 8) = j / 8 by omega,
        show (j - 32 * k) % 8 = j % 8 by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h₁), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem storePair_eq : (List.range 4).flatMap (storePair .x4) =
    storePair .x4 0 ++ (storePair .x4 1 ++ (storePair .x4 2 ++ (storePair .x4 3 ++ []))) := rfl

theorem outByte_congr {v v' : VReg → BitVec 128} (h : ∀ r ∈ halfRegs, v' r = v r) (j : Nat) :
    outByte v' j = outByte v j := by
  have ha : ∀ n, lane v' aReg n = lane v aReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, aReg, halfRegs])]
  have hb : ∀ n, lane v' bReg n = lane v bReg n := fun n => by
    simp only [lane]; rw [h _ (by
      rcases (by omega : n / 4 = 0 ∨ n / 4 = 1 ∨ n / 4 = 2 ∨ n / 4 = 3 ∨ 4 ≤ n / 4) with e | e | e | e | e <;>
        simp [e, bReg, halfRegs])]
  simp only [outByte, ha, hb]

/-- The halves of the sixteen blocks back to the 128 bytes at `x4`. -/
theorem storeBatch_run {s : State}
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    ∃ s', runBlock isa (storeBatch .x4) s = some s' ∧
      (∀ j < 128, s'.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j) ∧
      Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem ∧ MOnly [.v20, .v21] s s' := by
  have hW' : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ k < 4, ∀ j < 2,
      InRegions t.wr (t.gpr .x4 + BitVec.ofNat 64 (32 * k + 16 * j)) 16 := by
    intro t ht k hk j hj
    rw [ht.wr, ht.gpr, show 32 * k + 16 * j = 16 * (2 * k + j) by omega]
    exact hW _ (by omega)
  have hh : ∀ {t : State}, MOnly [.v20, .v21] s t → ∀ r ∈ halfRegs, t.v r = s.v r := fun ht r hr =>
    ht.v r (by revert r; decide)
  obtain ⟨s₀, r₀, m₀, f₀, o₀⟩ := storePair_run (s := s) (by decide : 0 < 4) (hW' ⟨rfl, fun _ _ => rfl⟩ 0 (by decide))
  obtain ⟨s₁, r₁, m₁, f₁, o₁⟩ := storePair_run (s := s₀) (by decide : 1 < 4) (hW' o₀ 1 (by decide))
  have p₁ := o₀.trans o₁
  obtain ⟨s₂, r₂, m₂, f₂, o₂⟩ := storePair_run (s := s₁) (by decide : 2 < 4) (hW' p₁ 2 (by decide))
  have p₂ := p₁.trans o₂
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storePair_run (s := s₂) (by decide : 3 < 4) (hW' p₂ 3 (by decide))
  have p₃ := p₂.trans o₃
  have g₀ := o₀.gpr; have g₁ := p₁.gpr; have g₂ := p₂.gpr
  have b₀ := outByte_congr (hh o₀); have b₁ := outByte_congr (hh p₁); have b₂ := outByte_congr (hh p₂)
  have mem : ∀ j < 128, s₃.mem (s.gpr .x4 + BitVec.ofNat 64 j) = outByte s.v j := by
    intro j hj
    have e₃ := m₃ j hj; have e₂ := m₂ j hj; have e₁ := m₁ j hj; have e₀ := m₀ j hj
    rw [g₂] at e₃; rw [g₁] at e₂; rw [g₀] at e₁
    rw [e₃, b₂]
    split
    · rfl
    · rw [e₂, b₁]; split
      · rfl
      · rw [e₁, b₀]; split
        · rfl
        · rw [e₀]; split
          · rfl
          · omega
  refine ⟨s₃, by rw [storeBatch, storePair_eq]; exact cat_run r₀ (cat_run r₁ (cat_run r₂ (cat_run r₃ runBlock_nil))),
    mem, ?_, p₃⟩
  rw [g₂] at f₃; rw [g₁] at f₂; rw [g₀] at f₁
  exact f₀.trans (f₁.trans (f₂.trans f₃))

/-! ## The batch -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (order up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

structure BatchPost (up : Bool) (s s' : State) : Prop where
  out : ∀ n < 16, blockAt s'.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)) =
    blockOut (scheduleAt s.mem (s.gpr .x0)) up (blockAt s.mem (s.gpr .x4 + BitVec.ofNat 64 (8 * n)))
  gpr : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr .x4, 128⟩] s.mem s'.mem
  v : ∀ r, r ∉ roundRegs → s'.v r = s.v r

theorem io_sub : ∀ r ∈ (VReg.v20 :: .v21 :: halfRegs), r ∈ roundRegs := by decide

theorem batch_ok (up : Bool) {s : State} (hS : SchedIn s .x0) (hc : Consts s)
    (hW : ∀ k < 8, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (batch up) s (BatchPost up s) := by
  let K := scheduleAt s.mem (s.gpr .x0)
  obtain ⟨s₁, r₁, a₁, b₁, o₁⟩ := loadBatch_run (s := s) fun k hk => by
    obtain ⟨r, hr, hc'⟩ := hW k hk; exact ⟨r, List.mem_append_right _ hr, hc'⟩
  rw [batch]
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, r₁, ?_⟩
  have hS₁ : SchedIn s₁ .x0 := fun off n h => by rw [o₁.rd, o₁.wr, o₁.gpr]; exact hS off n h
  have hc₁ : Consts s₁ :=
    ⟨fun e he => by rw [o₁.2 _ (by decide)]; exact hc.1 e he, fun e he => by rw [o₁.2 _ (by decide)]; exact hc.2 e he⟩
  apply WP.seq
  refine WP.mono (cipher_run hS₁ hc₁ (by decide) up) ?_
  intro s₂ ⟨hl, o₂⟩
  have hW₂ : ∀ k < 8, InRegions s₂.wr (s₂.gpr .x4 + BitVec.ofNat 64 (16 * k)) 16 := fun k hk => by
    rw [o₂.wr, o₂.g _ (by simp), o₁.wr, o₁.gpr]; exact hW k hk
  obtain ⟨s₃, r₃, m₃, f₃, o₃⟩ := storeBatch_run hW₂
  refine WP.of_runBlock ⟨s₃, r₃, ?_⟩
  have g₂ : s₂.gpr .x4 = s.gpr .x4 := by rw [o₂.g _ (by simp), o₁.gpr]
  have K₁ : scheduleAt s₁.mem (s₁.gpr .x0) = K := by rw [o₁.mem, o₁.gpr]
  refine ⟨fun n hn => ?_, fun r h5 h6 h7 => ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · refine blockAt_eq _ _ _ fun i hi => ?_
    rw [← g₂, Offset.add_add, m₃ _ (by omega), outByte, show (8 * n + i) / 8 = n by omega,
      show (8 * n + i) % 8 = i by omega, (hl n hn).1, (hl n hn).2, K₁, a₁ n hn, b₁ n hn, ← blockOut_eq, g₂]
  · rw [o₃.gpr, o₂.g _ (by simp; exact ⟨h5, h6, h7⟩), o₁.gpr]
  · rw [o₃.rd, o₂.rd, o₁.rd]
  · rw [o₃.wr, o₂.wr, o₁.wr]
  · rw [o₃.sp, o₂.sp, o₁.1]
  · rw [g₂] at f₃; rw [← o₁.mem, ← o₂.mem]; exact f₃
  · have n20 : r ∉ [VReg.v20, .v21] := fun h => hr (io_sub _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; rcases h with h | h <;> simp [h]))
    rw [o₃.v _ n20, o₂.v _ hr, o₁.2 _ (fun h => hr (io_sub _ h))]

end VG.Proof.Blowfish.AArch64
