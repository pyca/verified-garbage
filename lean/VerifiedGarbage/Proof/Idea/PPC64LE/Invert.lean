module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Ecb
public import VerifiedGarbage.Proof.Idea.Inverse
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Idea.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Idea.Inverse
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.PPC64LE.Lit

/-!
# IDEA decryption subkeys on PPC64LE

Each decryption subkey is a copy, the negation or the inverse of an
encryption subkey (`invertKey_getD`, `Impl.Idea.invOp`), computed into
`r12` (`invWord_ok`; the inverse by a loop of fifteen steps of
`t := (t ⊙ t) ⊙ a`, `invLoop_ok`), placed in its 16 bits of `r8`
(`invPlace`), and stored a doubleword at a time (`invQuad_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.r5, .r6, .r7, .r9, .r11, .r12]

theorem loadKey_ok (z : Spec.Idea.Schedule) (r : Reg) {k : Nat} (hk : k < 52) (t : State)
    (hz : KeyOk z t) :
    WP isa (.block (loadKey r k)) t fun t' => (t'.gpr r).setWidth 16 = z.getD k 0 ∧
      t'.mem = t.mem ∧ Keep [r] t t' := by
  refine WP.mono (WP.keep (c := .block (loadKey r k)) [r] (Q := fun t' =>
      (t'.gpr r).setWidth 16 = z.getD k 0 ∧ t'.mem = t.mem) ?_
    (by unfold loadKey; split <;> simp [writesOnly, Code.allInstrs_eq, instrs, dstOf]) rfl)
    fun t' ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold loadKey
  split
  · rename_i h
    have k₁ := hz.low k h
    irun [k₁.1, show 2 * k < 32768 by omega, lo16, k₁.2]
  · rename_i h
    have k₁ := hz.low 50 (by decide)
    simp only [Nat.reduceMul] at k₁
    have hk51 : k = 51 := by omega
    subst hk51
    irun [k₁.1, hi16, hz.last]

theorem invStep_ok (t : State) (h0 : t.gpr .r0 = 65535) :
    WP isa (.block invStep) t fun t' =>
      t'.gpr .r7 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .r7).setWidth 16) ((t.gpr .r7).setWidth 16))
        ((t.gpr .r6).setWidth 16)).setWidth 64 ∧
      t'.gpr .r5 = t.gpr .r5 - 1#64 ∧ t'.mem = t.mem ∧ Keep [.r5, .r7, .r11, .r12] t t' := by
  simp only [invStep, List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [mov .r11 .r7, mov .r12 .r7]) t fun u =>
      u.gpr .r11 = t.gpr .r7 ∧ u.gpr .r12 = t.gpr .r7 ∧ u.mem = t.mem ∧ Keep [.r11, .r12] t u := by
    refine WP.mono (WP.keep [.r11, .r12] (Q := fun u =>
      u.gpr .r11 = t.gpr .r7 ∧ u.gpr .r12 = t.gpr .r7 ∧ u.mem = t.mem) ?_ (by decide) rfl)
      fun u ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    irun [BitVec.or_self]
  refine WP.mono h1 fun u ⟨u11, u12, um, ue⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep u ((ue.gpr (by decide)).trans h0)) fun v ⟨v12, vm, ve⟩ => ?_
  rw [WP.block_append_iff]
  have h3 : WP isa (.block [mov .r11 .r12, mov .r12 .r6]) v fun w =>
      w.gpr .r11 = v.gpr .r12 ∧ w.gpr .r12 = v.gpr .r6 ∧ w.mem = v.mem ∧ Keep [.r11, .r12] v w := by
    refine WP.mono (WP.keep [.r11, .r12] (Q := fun w =>
      w.gpr .r11 = v.gpr .r12 ∧ w.gpr .r12 = v.gpr .r6 ∧ w.mem = v.mem) ?_ (by decide) rfl)
      fun w ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    irun [BitVec.or_self]
  refine WP.mono h3 fun w ⟨w11, w12, wm, we⟩ => ?_
  have e₃ : Keep [.r11, .r12] t w := ((ue.trans ve).trans we).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep w ((e₃.gpr (by decide)).trans h0)) fun x ⟨x12, xm, xe⟩ => ?_
  have h5 : WP isa (.block [mov .r7 .r12, .subi .r5 .r5 1]) x fun y =>
      y.gpr .r7 = x.gpr .r12 ∧ y.gpr .r5 = x.gpr .r5 - 1#64 ∧ y.mem = x.mem ∧ Keep [.r5, .r7] x y := by
    refine WP.mono (WP.keep [.r5, .r7] (Q := fun y =>
      y.gpr .r7 = x.gpr .r12 ∧ y.gpr .r5 = x.gpr .r5 - 1#64 ∧ y.mem = x.mem) ?_ (by decide) rfl)
      fun y ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
    unfold mov
    irun [BitVec.or_self]
  refine WP.mono h5 fun y ⟨y7, y5, ym, ye⟩ => ?_
  refine ⟨?_, ?_, by rw [ym, xm, wm, vm, um], ((e₃.trans xe).trans ye).mono (by decide)⟩
  · rw [y7, x12, w11, w12, v12, u11, u12, setWidth_setWidth16, ve.gpr (by decide), ue.gpr (by decide)]
  · rw [y5, xe.gpr (by decide), e₃.gpr (by decide)]

/-- `c` steps remain: `r7` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  r5 : t.gpr .r5 = BitVec.ofNat 64 c
  r6 : (t.gpr .r6).setWidth 16 = a
  r7 : (t.gpr .r7).setWidth 16 = chain a (15 - c)
  mask : t.gpr .r0 = 65535
  mem : t.mem = t₀.mem
  keep : Keep [.r5, .r7, .r11, .r12] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) (.nonzero .d .r5)) t (fun t' =>
      t'.gpr .r7 = (Spec.Idea.inv a).setWidth 64 ∧ t'.mem = t₀.mem ∧
      Keep [.r5, .r7, .r11, .r12] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  refine WP.mono (invStep_ok t hi.mask) fun t' ⟨r7', r5', m', e'⟩ => ?_
  have hv : t'.gpr .r7 = (chain a (15 - c + 1)).setWidth 64 := by
    rw [r7', hi.r7, hi.r6]; rfl
  have hc : t.gpr .r5 - 1#64 = BitVec.ofNat 64 (c - 1) := by
    rw [hi.r5]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have keep' : Keep [.r5, .r7, .r11, .r12] t₀ t' := (hi.keep.trans e').mono (by decide)
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨?_, ?_, m'.trans hi.mem, keep'⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, r5', hc]; rfl
    · rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨?_, c - 1, by omega, by omega, by omega, r5'.trans hc, ?_, ?_, ?_, m'.trans hi.mem, keep'⟩
    · simp only [eval, State.read, BitVec.setWidth_eq, r5', hc, Option.some.injEq]
      have h : (BitVec.ofNat 64 (c - 1) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, toNat_zero] at this
        omega
      rw [bne, h]; rfl
    · rw [e'.gpr (by decide)]; exact hi.r6
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega]
    · rw [e'.gpr (by decide)]; exact hi.mask

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .r12 = ((Spec.Idea.invertKey z).getD n 0).setWidth 64 ∧ t'.mem = t.mem ∧
      Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    rw [WP.block_append_iff]
    refine WP.mono (loadKey_ok z .r12 hk t hz) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
    have h2 : WP isa (.block [.logic .and .r12 .r12 .r0]) t₁ fun t₂ =>
        t₂.gpr .r12 = t₁.gpr .r12 &&& 65535 ∧ t₂.mem = t₁.mem ∧ Keep [.r12] t₁ t₂ := by
      refine WP.mono (WP.keep [.r12] (Q := fun t₂ =>
        t₂.gpr .r12 = t₁.gpr .r12 &&& 65535 ∧ t₂.mem = t₁.mem) ?_ (by decide) rfl)
        fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      irun [(e₁.gpr (by decide)).trans hz.mask]
    refine WP.mono h2 fun t₂ ⟨v₂, m₂, e₂⟩ => ⟨?_, m₂.trans m₁, (e₁.trans e₂).mono (by decide)⟩
    rw [v₂, mask_setWidth, v₁]; rfl
  | neg =>
    rw [WP.block_append_iff]
    refine WP.mono (loadKey_ok z .r9 hk t hz) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
    have h2 : WP isa (.block [.li .r12 0, .sub .r12 .r12 .r9, .logic .and .r12 .r12 .r0]) t₁
        fun t₂ => t₂.gpr .r12 = (0 - t₁.gpr .r9) &&& 65535 ∧ t₂.mem = t₁.mem ∧ Keep [.r12] t₁ t₂ := by
      refine WP.mono (WP.keep [.r12] (Q := fun t₂ =>
        t₂.gpr .r12 = (0 - t₁.gpr .r9) &&& 65535 ∧ t₂.mem = t₁.mem) ?_ (by decide) rfl)
        fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      irun [(e₁.gpr (by decide)).trans hz.mask]
    refine WP.mono h2 fun t₂ ⟨v₂, m₂, e₂⟩ => ⟨?_, m₂.trans m₁, (e₁.trans e₂).mono (by decide)⟩
    rw [v₂, neg_mask, v₁]; rfl
  | inv =>
    apply WP.seq
    rw [WP.block_append_iff]
    refine WP.mono (loadKey_ok z .r6 hk t hz) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
    have h2 : WP isa (.block [mov .r7 .r6, .li .r5 15]) t₁ fun t₂ =>
        t₂.gpr .r6 = t₁.gpr .r6 ∧ t₂.gpr .r7 = t₁.gpr .r6 ∧ t₂.gpr .r5 = 15 ∧ t₂.mem = t₁.mem ∧
        Keep [.r5, .r7] t₁ t₂ := by
      refine WP.mono (WP.keep [.r5, .r7] (Q := fun t₂ =>
        t₂.gpr .r6 = t₁.gpr .r6 ∧ t₂.gpr .r7 = t₁.gpr .r6 ∧ t₂.gpr .r5 = 15 ∧ t₂.mem = t₁.mem) ?_
        (by decide) rfl) fun u ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩
      unfold mov
      irun [BitVec.or_self]
    refine WP.mono h2 fun t₂ ⟨r6₂, r7₂, r5₂, m₂, e₂⟩ => ?_
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ 15 t₂ ⟨by decide, by decide, r5₂, by rw [r6₂, v₁],
      by rw [r7₂, v₁]; rfl, (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hz.mask),
      rfl, Keep.refl _ _⟩) fun t₃ ⟨r7₃, m₃, e₃⟩ => ?_
    have h4 : WP isa (.block [mov .r12 .r7]) t₃ fun t₄ => t₄.gpr .r12 = t₃.gpr .r7 ∧
        t₄.mem = t₃.mem ∧ Keep [.r12] t₃ t₄ := by
      refine WP.mono (WP.keep [.r12] (Q := fun t₄ => t₄.gpr .r12 = t₃.gpr .r7 ∧ t₄.mem = t₃.mem) ?_
        (by decide) rfl) fun u ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
      unfold mov
      irun [BitVec.or_self]
    refine WP.mono h4 fun t₄ ⟨v₄, m₄, e₄⟩ => ⟨?_, by rw [m₄, m₃, m₂, m₁],
      (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
    rw [v₄, r7₃]; rfl

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `r8` holds the first `i` decryption subkeys of doubleword `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 64, (t.gpr .r8).getLsbD p =
    if p < 16 * i then (dk z (4 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_ok (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 4) (t : State)
    (hr12 : t.gpr .r12 = (dk z (4 * q + i)).setWidth 64) (hacc : i = 0 ∨ Acc z q i t) :
    WP isa (.block (invPlace (4 * q + i))) t fun t' => Acc z q (i + 1) t' ∧ t'.mem = t.mem ∧
      Keep [.r8, .r12] t t' := by
  refine WP.mono (WP.keep (c := .block (invPlace (4 * q + i))) [.r8, .r12] (Q := fun t' =>
      Acc z q (i + 1) t' ∧ t'.mem = t.mem) ?_
    (by unfold invPlace; split <;> simp [writesOnly, Code.allInstrs_eq, instrs, dstOf, mov]) rfl)
    fun t' ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold invPlace
  split
  · rename_i h
    have hi0 : i = 0 := by omega
    subst hi0
    unfold mov
    irun [BitVec.or_self, hr12, Acc]
    intro p hp
    rw [BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and, Nat.add_zero]
    by_cases hp16 : p < 16
    · rw [ite_eq_left (by omega), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
    · rw [ite_eq_right (by omega)]; exact BitVec.getLsbD_of_ge _ _ (by omega)
  · rename_i h
    have hi0 : i ≠ 0 := by omega
    have hacc' := hacc.resolve_left hi0
    have hm : (4 * q + i) % 4 = i := by omega
    rw [hm]
    irun [show 16 * i < 64 by omega, hr12, Acc]
    intro p hp
    rw [BitVec.getLsbD_or, hacc' p hp, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h1 : p < 16 * i
    · simp [h1, show p < 16 * (i + 1) by omega]
    · by_cases h2 : p < 16 * (i + 1)
      · simp [h1, h2, hp, show p - 16 * i < 64 by omega, show 4 * q + p / 16 = 4 * q + i by omega,
          show p % 16 = p - 16 * i by omega]
      · simp only [h1, h2, ↓reduceIte, Bool.false_or]
        rw [BitVec.getLsbD_of_ge (dk z (4 * q + i)) _ (by omega)]
        simp

/-- The registers computing a doubleword of decryption subkeys writes. -/
abbrev quadWrites : List Reg := [.r5, .r6, .r7, .r8, .r9, .r11, .r12]

theorem quadWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 13) (hi : i < 4) (t : State)
    (hz : KeyOk z t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → t'.mem = t.mem → Keep quadWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega) t hz) fun t₁ ⟨v₁, m₁, e₁⟩ => ?_
  apply WP.seq
  have hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.gpr (by decide)]; exact h p hp
  exact WP.mono (invPlace_ok z q i hi t₁ v₁ hacc₁) fun t₂ ⟨a₂, m₂, e₂⟩ =>
    hrest t₂ a₂ (m₂.trans m₁) ((e₁.trans e₂).mono (by decide))

/-- What `vg_idea_invert_key` needs of its state: the encryption subkeys (104
bytes at `r3`) readable, the decryption subkeys (104 bytes at `r4`) writable,
apart. -/
structure InvPre (s : State) : Prop where
  sched : ⟨s.gpr .r3, 104⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .r4, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .r3, 104⟩ : Region).Disjoint ⟨s.gpr .r4, 104⟩

/-- After `q` doublewords of decryption subkeys, from the state `s₀` after the
mask is set. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  keep : Keep (quadWrites ++ [.r8]) s₀ t
  frame : Frame [⟨s₀.gpr .r4, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .r4 + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (dk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .r3)) (4 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (h0 : s₀.gpr .r0 = 65535)
    (hi : QInv s₀ q t) (hq : q ≤ 13) : KeyOk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .r3)) t := by
  have h3 : t.gpr .r3 = s₀.gpr .r3 := hi.keep.gpr (by decide)
  have h := keyOk_of t (by rw [h3, hi.keep.2.1, hi.keep.2.2]; exact hp.sched)
    ((hi.keep.gpr (by decide)).trans h0)
  rwa [h3, scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega))) (by decide))] at h

theorem invQuad_ok (s₀ : State) (hp : InvPre s₀) (h0 : s₀.gpr .r0 = 65535) (q : Nat) (hq : q < 13)
    (t : State) (hi : QInv s₀ q t) : WP isa (invQuad q) t (QInv s₀ (q + 1)) := by
  have hz := hi.keyOk hp h0 (by omega)
  simp only [invQuad, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons, List.foldr_nil]
  refine quadWord_ok _ q 0 hq (by decide) t hz (Or.inl rfl) fun t₁ a₁ m₁ e₁ => ?_
  have hz₁ := hz.keep e₁ m₁ (by decide) (by decide)
  refine quadWord_ok _ q 1 hq (by decide) t₁ hz₁ (Or.inr a₁) fun t₂ a₂ m₂ e₂ => ?_
  have hz₂ := hz₁.keep e₂ m₂ (by decide) (by decide)
  refine quadWord_ok _ q 2 hq (by decide) t₂ hz₂ (Or.inr a₂) fun t₃ a₃ m₃ e₃ => ?_
  have hz₃ := hz₂.keep e₃ m₃ (by decide) (by decide)
  refine quadWord_ok _ q 3 hq (by decide) t₃ hz₃ (Or.inr a₃) fun t₄ a₄ m₄ e₄ => ?_
  have e : Keep quadWrites t t₄ := (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)
  have m : t₄.mem = t.mem := m₄.trans (m₃.trans (m₂.trans m₁))
  have hr4 : t₄.gpr .r4 = s₀.gpr .r4 := (e.gpr (by decide)).trans (hi.keep.gpr (by decide))
  have hw : InRegions t₄.wr (t₄.gpr .r4 + BitVec.ofNat 64 (8 * q)) 8 := by
    rw [hr4, e.2.2, hi.keep.2.2]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  have hk₄ : Keep (quadWrites ++ [.r8]) s₀ t₄ := (hi.keep.trans e).mono (by decide)
  irun [hw, show 8 * q < 32768 by omega, show (8 * q) % 4 = 0 by omega]
  refine ⟨hk₄, ?_, ?_⟩
  · rw [m, hr4]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · intro i hiq p hp64
    rw [m, hr4]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self64, a₄ p hp64, ite_eq_left (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words i (by omega) p hp64

/-- Doublewords `q … q + n - 1`. -/
def quads (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invQuad q) rest) (.block [])

theorem quads_ok (s₀ : State) (hp : InvPre s₀) (h0 : s₀.gpr .r0 = 65535) :
    ∀ n q, q + n = 13 → ∀ t, QInv s₀ q t → WP isa (quads q n) t (QInv s₀ 13)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [quads, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invQuad_ok s₀ hp h0 q (by omega) t hi) fun t₁ h₁ =>
      quads_ok s₀ hp h0 n (q + 1) (by omega) t₁ h₁

theorem invertKey_eq : invertKey = .seq (.block setMask) (quads 0 13) := rfl

/-- `vg_idea_invert_key` on PPC64LE. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 104⟩
    let out : Region := ⟨s.gpr .r4, 104⟩
    s.rd = [sched] ∧ s.wr = [out] ∧ sched.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .r4) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (s.gpr .r3))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

/-- The registers `invertKey` writes: all volatile. -/
abbrev invertWrites : List Reg := [.r0, .r5, .r6, .r7, .r8, .r9, .r11, .r12]

theorem invert_wp (s : State) (hs : invertContract.pre s) :
    WP isa invertKey s (invertContract.post s) := by
  obtain ⟨hrd, hwr, hsep⟩ := hs
  rw [invertKey_eq]
  apply WP.seq
  have h1 : WP isa (.block setMask) s fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem ∧
      Keep [.r0] s t := by
    refine WP.mono (WP.keep [.r0] (Q := fun t => t.gpr .r0 = 65535 ∧ t.mem = s.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold setMask
    irun
    rfl
  refine WP.mono h1 fun s₁ ⟨h0₁, m₁, e₁⟩ => ?_
  have hp : InvPre s₁ := ⟨by rw [e₁.gpr (by decide), e₁.2.1, e₁.2.2, hrd]; simp,
    by rw [e₁.gpr (by decide), e₁.2.2, hwr]; simp,
    by rw [e₁.gpr (by decide), e₁.gpr (by decide)]; exact hsep⟩
  refine WP.mono (quads_ok s₁ hp h0₁ 13 0 rfl s₁ ⟨Keep.refl _ _, Frame.refl _ _,
    fun i hi => absurd hi (by omega)⟩) fun s' hi => ?_
  show Spec.Idea.scheduleAt s'.mem (s.gpr .r4) = _
  rw [← e₁.gpr (show Reg.r4 ∉ [Reg.r0] by decide), ← e₁.gpr (show Reg.r3 ∉ [Reg.r0] by decide),
    ← m₁]
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega) _ (by omega),
    show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega,
    show (16 * (n % 4) + b) % 16 = b by omega]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨tr, s', he, ⟨hp, hk⟩⟩ :=
    WP.keep invertWrites (invert_wp s hs) (by lit_decide) (by lit_decide)
  exact ⟨tr, s', he, abiPreserved_of_keep he hk (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hp⟩

theorem invert_ct : ConstantTime isa invertContract.pre invertContract.pub invertKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1
  · exact h.2.1

def invertSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩]

theorem invertKey_verified : Verified target invertKey (Spec.Idea.invertKeyContract abi) :=
  Verified.of_correct invert_correct invert_ct (by
    sig_implies [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, abi,
      argRegs, invertContract] [invertSat] using invertSat)

end VG.Proof.Idea.PPC64LE
