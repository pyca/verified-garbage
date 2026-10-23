module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA public-key operation on PPC64LE: the output

`output_ok`: array 4's `k` bytes, most significant first, masked, to `out`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

theorem mask_byte (x : BitVec 8) (b : Bool) :
    ((x.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) =
      if b then x else 0 := by
  cases b
  · simp
  · simp only [ite_true, show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 from rfl,
      BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := x.isLt
    omega

theorem read1_setWidth (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  show (m.read (a + 1) 0 ++ m a).toNat % 2 ^ 64 = (m a).toNat % 2 ^ 64
  rw [BitVec.toNat_append]
  simp [Mem.read]

/-- `output`, the mask of `b` in `r26`: `out`'s (`r27`) byte `i` is array 4's
byte `k - 1 - i` if `b`, else 0; `r3` is 1 if `b`, else 0. -/
theorem output_ok {s : State} {B O : Addr} {Z w k : Nat} {b : Bool} (hs : Scr s B Z) (ho : Scr s O k)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (h27 : s.gpr .r27 = off O 0)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hZ : slot w 8 ≤ Z)
    (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa output s fun t =>
      ((∀ i < k, t.mem (off O i) = if b then s.mem (off B (slot w 4 + (k - 1 - i))) else 0) ∧
        Outside O 0 k s.mem t.mem ∧ t.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0)) ∧
      Keep [.r0, .r3, .r15, .r16, .r17] s t := by
  have hnw := hs.nowrap
  have hno := ho.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e4 := e 4; have e8 := e 8
  unfold output
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok (rd := .r15) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a15, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15, .r16, .r17] (Q := fun s₂ => s₂.gpr .r15 = off B (slot w 4 + (k - 1)) ∧
    s₂.gpr .r16 = off O 0 ∧ s₂.gpr .r17 = BitVec.ofNat 64 k ∧ s₂.mem = s₁.mem)
    (by prun [a15, (k1.gpr .r28 (by decide)).trans h28, (k1.gpr .r27 (by decide)).trans h27, off_add,
        BitVec.add_zero]
        rw [off_sub1 _ (by omega)]; congr 2; omega) (by decide)) fun s₂ ⟨⟨b15, b16, b17, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have h26' : s₂.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) :=
    (k12.gpr _ (by decide)).trans h26
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r15 = off B (slot w 4 + (k - 1) - j) ∧ t.gpr .r16 = off O j ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = if b then s.mem (off B (slot w 4 + (k - 1 - i))) else 0) ∧
      Keep [.r0, .r15, .r16, .r17] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.lbz .r0 .r15 0, .logic .and .r0 .r0 .r26,
      .stb .r0 .r16 0, .addi .r16 .r16 1, .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := k) (by omega) (by omega) Inv (fun j hj t ⟨t15, t16, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b15]; rfl, b16, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega),
      k12.mono⟩ b17) fun t ⟨_, _, tout, tb, tk⟩ => ?_)
  · have hrd : InRegions (t.rd ++ t.wr) (off B (slot w 4 + (k - 1) - j)) 1 := by
      rw [tk.rd, tk.wr]; exact hs.ld (show slot w 4 + (k - 1) - j + 1 ≤ Z by have := slot_le (w := w) (j := 4) (by decide); omega)
    have hst : WP isa (.block [.lbz .r0 .r15 0, .logic .and .r0 .r0 .r26, .stb .r0 .r16 0, .addi .r16 .r16 1,
        .subi .r15 .r15 1, .subi .r17 .r17 1]) t fun t' => t' = ((({ ((t.write .r0
          ((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64)).write .r0
          ((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)))) with
          mem := t.mem.write (off O j) 1 (((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
            (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) } :
            State).write .r16 (off O (j + 1))).write .r15
              (off B (slot w 4 + (k - 1) - j) - BitVec.ofNat 64 1)).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
      prun [t15, t16, (tk.gpr .r26 (by decide)).trans h26, exec_lbz' (show Reg.r15 ≠ .r0 by decide)
        (show 0 < 2 ^ 15 by decide), exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
        (ho.congr tk.wr).st (d := j) (n := 1) (by omega)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem O (d := j) (((t.mem.read (off B (slot w 4 + (k - 1) - j)) 1).setWidth 64 &&&
      (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0))).setWidth 8) (by omega)
    have harr : t.mem (off B (slot w 4 + (k - 1) - j)) = s.mem (off B (slot w 4 + (k - 1) - j)) := by
      refine tout _ (Or.inr ?_)
      by_contra hc
      have := hsep (off B (slot w 4 + (k - 1) - j)) (by omega)
      rw [show ofs B (off B (slot w 4 + (k - 1) - j)) = slot w 4 + (k - 1) - j from
        Mem.sub_ofNat_toNat B (by have := slot_le (w := w) (j := 4) (by decide); omega)] at this
      have := slot_le (w := w) (j := 4) (by decide)
      omega
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub1 _ (by have := slot_le (w := w) (j := 4) (by decide); unfold slot hdrBytes at *; omega),
        show slot w 4 + (k - 1) - j - 1 = slot w 4 + (k - 1) - (j + 1) by omega]
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega)).trans (hw1.mono (by omega) (by omega))
    · intro i hi
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hw1 _ (by rw [ofs_off0 O (by omega)]; omega)]; exact tb i hi
      · rw [write1_self, read1_setWidth, show slot w 4 + (k - 1 - i) = slot w 4 + (k - 1) - i by omega, ← harr]
        exact mask_byte _ b
    · exact tk.trans' ((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.mem _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
  · refine WP.mono (WP.keep [.r3] (Q := fun t' => t'.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0) ∧
      t'.mem = t.mem) ?_ (by decide)) fun t' ⟨⟨a3, tm⟩, k5⟩ => ⟨⟨by rw [tm]; exact tb, by rw [tm]; exact tout, a3⟩,
        (tk.trans k5).mono⟩
    prun [(tk.gpr .r26 (by decide)).trans h26]
    cases b <;> decide

end VG.Proof.Bignum.PPC64LE.Pub
