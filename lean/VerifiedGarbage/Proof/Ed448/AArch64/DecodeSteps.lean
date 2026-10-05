import VerifiedGarbage.Proof.Ed448.AArch64.Window.Checks
import VerifiedGarbage.Proof.Ed448.AArch64.VerifySign
import VerifiedGarbage.Proof.Ed448.AArch64.DecodeOps
import VerifiedGarbage.Proof.X448.AArch64.Fast.Chain

/-!
# Ed448 verification's equation on AArch64: decoding's blocks

Untrusted: everything here is checked by Lean. What decoding writes
(`DFrame`), and its blocks around the register-resident field operations: `y`
read with the sign bit kept at `SIGN` and 1 written into slot 10 (`head_ok`),
the sign bit read back (`signLoad_ok`), and the check of `x = 0` for `x` below
`2^118` (`zeroSignF_ok`). The slots stay below the products' operand bound
(`BEnv`), which a check keeps (`bnd_check`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 ofs workRegs FieldMem store_ok)
open VG.Proof.X448.AArch64.Weak (E IKeep)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-! ## What decoding writes -/

/-- What decoding writes: the sign bit at `SIGN` (beyond the saved `x19` and `x20`), the slots,
the coefficients of the register-resident products and `CAN`. -/
def DFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 16 ∨ 2880 ≤ ofs base x) → (ofs base x < ACC ∨ ACC + 1152 ≤ ofs base x) →
    (ofs base x < CAN ∨ CAN + 128 ≤ ofs base x) → m' x = m x

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := fun x a b c => (h₂ x a b c).trans (h₁ x a b c)

theorem DFrame.of_outside2 {base : Addr} {m m' : Mem} {n : Nat} (hn : n ≤ 2816)
    (h : Outside2 base 64 n ACC 1152 m m') : DFrame base m m' := fun x a b _ => h x (by omega) b

theorem DFrame.of_outside {base : Addr} {m m' : Mem} {o n : Nat} (h : Outside base o n m m')
    (ho : 16 ≤ o ∧ o + n ≤ 2880) : DFrame base m m' := fun x a _ _ => h x (by omega)

theorem DFrame.whole {base : Addr} {m m' : Mem} (h : DFrame base m m') : Outside base 0 8192 m m' :=
  fun x hx => h x (by omega) (by simp only [ACC]; omega) (by simp only [CAN]; omega)

theorem DFrame.word {base : Addr} {m m' : Mem} (h : DFrame base m m') {d : Nat}
    (h1 : d + 8 ≤ 16 ∨ 2880 ≤ d) (h2 : d + 8 ≤ ACC ∨ ACC + 1152 ≤ d) (h3 : d + 8 ≤ CAN ∨ CAN + 128 ≤ d)
    (hd : d + 8 ≤ 8192) : word m' base d = word m base d :=
  Mem.readW_congr fun i hi => h _ (by
      simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)

theorem cframe_dframe {base : Addr} {m m' : Mem} (h : CFrame base m m') : DFrame base m m' :=
  fun x h1 h2 h3 => h x (by simp only [X2, slot] at *; omega) h3 (by simp only [ACC] at *; omega)

theorem fkeep_dframe {base : Addr} {s t : State} (h : FKeep base s t) : DFrame base s.mem t.mem :=
  DFrame.of_outside2 (Nat.le_refl _) h.mem

theorem ikeep_dframe {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Fast.IKeep base s t) :
    DFrame base s.mem t.mem :=
  DFrame.of_outside2 (Nat.le_refl _) h.mem

/-! ## Bounds -/

theorem weakB_ib {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.Curve448.AArch64.Bounded m base o) :
    Bnd Ib m base o := fun i hi => Nat.lt_trans (h i hi) (by decide)

theorem benv_of_weak {m : Mem} {base : Addr} (h : VG.Proof.X448.AArch64.Weak.BoundedEnv m base) : BEnv m base :=
  fun i => weakB_ib (h i)

/-- `BEnv` after a check: the slots but `X2` are unchanged, and `X2` holds 28-bit limbs. -/
theorem bnd_check {base : Addr} {m m' : Mem} (hb : BEnv m base) (h : CFrame base m m')
    (h2 : VG.Proof.X448.AArch64.Bounded m' base X2) : BEnv m' base := by
  intro i j hj
  by_cases hi : i = 1
  · subst hi; exact weakB_ib (bounded_of_legacy h2) j hj
  · rw [show limbs m' base (slot i.val) j = _ from h.limbs hi (by omega)]
    exact hb i j hj

theorem lt118 {m : Mem} {base : Addr} (hb : BEnv m base) (i : Fin 22) :
    ∀ j < 8, limbs m base (slot i.val) j < 2 ^ 118 := fun j hj => Nat.lt_trans (hb i j hj) (by decide)

/-! ## The blocks -/

/-- `y`, its checks and the sign bit (kept at `SIGN`), and 1 in slot 10. -/
theorem head_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {rp : Reg}
    {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (yo : Fin 22) (hy10 : yo ≠ 10)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block (decodeY rp yo.val ++ [st .x17 SIGN] ++ Impl.X448.AArch64.Base.constSlot (slot 10) 1)) s
      fun t =>
      E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      word t.mem base SIGN = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ i : Fin 22, i ≠ yo → i ≠ 10 → E t.mem base i = E s.mem base i) ∧ E t.mem base 10 = 1 ∧
      BEnv t.mem base ∧ Bnd Mb t.mem base (slot (10 : Fin 22).val) ∧
      Keeps [.x4, .x5, .x6, .x7, .x17, .x20] s t ∧ DFrame base s.mem t.mem := by
  have hy := yo.isLt
  have hsep : slot yo.val + 128 ≤ slot 10 ∨ slot 10 + 128 ≤ slot yo.val := by
    have := VG.Proof.X448.AArch64.Weak.slot_sep hy10; simpa using this
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (decodeY_ok hs hp hrp yo hr hfar) fun a ⟨ya, sa, ca, ea, ba, ka, oa⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [show ([st .x17 SIGN] ++ Impl.X448.AArch64.Base.constSlot (slot 10) 1 : List Instr) =
    [st .x17 SIGN] ++ Impl.X448.AArch64.Base.constSlot (slot 10) 1 from rfl, WP.block_append_iff]
  refine WP.mono (store_ok hsa (d := SIGN) (by decide) (by decide) .x17) fun b ⟨mb, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  have ob : Outside base SIGN 8 a.mem b.mem := by
    rw [mb]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Base.constSlot_ok hsb (o := slot 10) (by decide) (by decide) 1)
    fun t ⟨wt, ot, kt⟩ => ?_
  -- Slots other than 10 keep their limbs from `a`.
  have lab : ∀ i : Fin 22, i ≠ 10 → ∀ j < 8, limbs t.mem base (slot i.val) j = limbs a.mem base (slot i.val) j :=
    fun i hi j hj => by
      have := i.isLt
      have hs10 : slot i.val + 128 ≤ slot 10 ∨ slot 10 + 64 ≤ slot i.val := by
        have := VG.Proof.X448.AArch64.Weak.slot_sep hi; simp only [slot] at *; omega
      rw [ot.limbs hs10 (by simp only [slot]; omega) (by omega),
        ob.limbs (Or.inr (by simp only [SIGN, slot]; omega)) (by simp only [slot]; omega) (by omega)]
  have Eab : ∀ i : Fin 22, i ≠ 10 → E t.mem base i = E a.mem base i := fun i hi =>
    congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (lab i hi))
  have w10 : ∀ j < 8, limbs t.mem base (slot 10) j < 2 ^ 56 := fun j hj => by
    change (word t.mem base (slot 10 + 8 * j)).toNat < _
    rw [wt j hj]; exact VG.Proof.X448.AArch64.Base.limb_lt _ _
  refine ⟨by rw [Eab yo hy10]; exact ya, ?_, ?_, fun i hi h10 => by rw [Eab i h10, ea i hi], ?_, ?_,
    fun j hj => Nat.lt_trans (w10 j hj) (by decide), ?_, ?_⟩
  · rw [ot.word (Or.inl (by simp only [SIGN, slot]; omega)) (by decide), mb,
      VG.Proof.X448.AArch64.word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
    exact sa
  · obtain ⟨c, hc, h20⟩ := ca
    exact ⟨c, hc, by rw [kt.1 _ (by decide), kb.1 _ (by simp), h20]⟩
  · exact VG.Proof.X448.AArch64.Base.F_of_words wt
  · intro i j hj
    by_cases h10 : i = 10
    · subst h10; exact Nat.lt_trans (w10 j hj) (by decide)
    · rw [lab i h10 j hj]
      by_cases hiy : i = yo
      · subst hiy; exact Nat.lt_trans (ba j hj) (by decide)
      · rw [oa.limbs (by have := VG.Proof.X448.AArch64.Weak.slot_sep hiy; have := i.isLt; simp only [slot] at *; omega)
          (by have := i.isLt; simp only [slot]; omega) (by omega)]
        exact hb i j hj
  · exact (ka.trans (kb.mono (by simp))).trans (kt.mono (by decide))
  · exact ((DFrame.of_outside oa (by simp only [slot]; omega)).trans
      (fun x h1 _ _ => ob x (by simp only [SIGN]; omega))).trans
      (DFrame.of_outside ot (by simp only [slot]; omega))

/-- The sign bit read back into `x17`. -/
theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [ld .x17 SIGN]) s fun t =>
      t.gpr .x17 = word s.mem base SIGN ∧ t.mem = s.mem ∧ Keeps [.x17] s t := by
  have hr := hs.read (d := 16) (n := 8) (by decide)
  show WP isa (.block [ld .x17 16]) s fun t => t.gpr .x17 = word s.mem base 16 ∧ t.mem = s.mem ∧ Keeps [.x17] s t
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load, Nat.reduceMod,
    Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq, hs.x3, hr, RegUpd.gpr_write, RegUpd.mem_write,
    ite_true, Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- `zeroSign xo`, for `x` below `2^118`: `x20 |= c`, `c = 0` exactly when `x ≠ 0` or the sign bit is 0,
and the parity of `x` in `X2`'s first limb. -/
theorem zeroSignF_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (xo : Fin 22)
    (hxo : xo ≠ 1) {sb : Nat} (hsb : sb < 2) (h17 : s.gpr .x17 = BitVec.ofNat 64 sb) :
    WP isa (.block (zeroSign xo.val)) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ ¬ (E s.mem base xo = 0 ∧ sb = 1)) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      VG.Proof.X448.AArch64.limbs t.mem base X2 0 % 2 = (E s.mem base xo).val % 2 ∧
      CKeep base s t ∧ BEnv t.mem base := by
  rw [zeroSign]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (canonF_ok hs xo hxo (lt118 hb xo)) fun u ⟨bu, fu, mu, ku⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (orWords_ok hsu) fun v ⟨v5, vm, vk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok v) fun w ⟨w5, wm, wk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and17_ok w) fun x ⟨x5, xm, xk⟩ => ?_
  refine WP.mono (orBad_ok x) fun t ⟨t20, tm, tk⟩ => ?_
  have tmem : t.mem = u.mem := by rw [tm, xm, wm, vm]
  have x17 : w.gpr .x17 = BitVec.ofNat 64 sb := by
    rw [wk.1 _ (by decide), vk.1 _ (by decide), ku.1 _ (by decide)]; exact h17
  have hz : v.gpr .x5 = 0 ↔ E s.mem base xo = 0 := by
    rw [v5]
    constructor
    · intro h
      apply Fin.ext
      rw [← fu, Fin.val_zero]
      exact valN_zero_iff.mpr fun j hj => by
        have := congrArg BitVec.toNat (h j hj)
        exact this
    · intro h j hj
      have h0 : VG.Proof.X448.AArch64.fe u.mem base X2 = 0 := by rw [fu, h, Fin.val_zero]
      apply BitVec.eq_of_toNat_eq
      exact valN_zero_iff.mp h0 j hj
  refine ⟨⟨x.gpr .x5, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [x5, w5, x17]
    have := zeroSign_val (decide (v.gpr .x5 = 0)) hsb
    simp only [decide_eq_true_eq] at this
    rw [this, hz]
  · rw [t20, xk.1 _ (by decide), wk.1 _ (by decide), vk.1 _ (by decide), ku.1 _ (by decide)]
  · rw [tmem, ← fu]
    exact (valN_mod_two _).symm
  · refine CKeep.of_keeps (rs := [.x4, .x5, .x6, .x7, .x20] ++ workRegs)
      ((ku.mono (by decide)).trans ((((vk.mono (by decide)).trans (wk.mono (by decide))).trans
        (xk.mono (by decide))).trans (tk.mono (by decide)))) (by decide) ?_
    rw [tmem]; exact CFrame.of_field mu
  · rw [tmem]
    exact bnd_check hb (CFrame.of_field mu) bu

end VG.Proof.Ed448.AArch64
