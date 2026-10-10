import VerifiedGarbage.Proof.Ed448.AArch64.Window.Table
import VerifiedGarbage.Proof.Curve448.AArch64.Copy
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters

/-!
# Ed448 verification on AArch64: the table's first entries

Untrusted: everything here is checked by Lean. `tabInit`, after the decodings
(every slot's limbs below the products' operand bound `Ib`): `R` (slots 8–9) copied to `RX`
and `RY`, zero in slot 19 and 1 in slot 20, entry 0 the neutral point, `P =
(x, y, 1)` from slots 6–7 in slots 3–5 and 6–8 and as entry 1, and the counter
at 2 (`tabInit_ok`): `TInv` for entry 2. Only the slots, `RX`, `RY` and the
first two entries change (`IFrame`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot limb)
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt constSlot_ok F_of_words bnd_of_words limb_lt)
open VG.Spec.Ed448 (Point)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

/-- What `tabInit` keeps: everything but the slots, `RX`, and `RY` with the first two entries. -/
def IFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 64 ∨ 2880 ≤ ofs base x) → (ofs base x < RX ∨ RX + 128 ≤ ofs base x) →
    (ofs base x < RY ∨ TAB + 384 ≤ ofs base x) → m' x = m x

theorem IFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : IFrame base m₁ m₂) (h₂ : IFrame base m₂ m₃) :
    IFrame base m₁ m₃ := fun x a b c => (h₂ x a b c).trans (h₁ x a b c)

theorem IFrame.of_outside {base : Addr} {m m' : Mem} {o n : Nat} (h : Outside base o n m m')
    (hr : (64 ≤ o ∧ o + n ≤ 2880) ∨ (RX ≤ o ∧ o + n ≤ RX + 128) ∨ (RY ≤ o ∧ o + n ≤ TAB + 384)) :
    IFrame base m m' := fun x a b c => h x (by simp only [RX, RY, CAN, TAB] at hr a b c; omega)

theorem IFrame.refl (base : Addr) (m : Mem) : IFrame base m m := fun _ _ _ _ => rfl

/-! ## The steps -/

/-- A copy between slots or from a slot to `RX` or `RY`. -/
theorem copyS_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : o + 128 ≤ 8192)
    (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hsep : o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (Impl.Curve448.AArch64.copy o a)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = limbs s.mem base a i) ∧ Outside base o 128 s.mem t.mem ∧
      Keeps VG.Proof.X448.AArch64.clob s t :=
  VG.Proof.Curve448.AArch64.copy_ok hs ho ha ho8 ha8 (Or.inr hsep)

theorem FV_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i) :
    FV m' base o' = FV m base o := congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

/-- The point `(x, y, 1)` of slots 6–7 (`-A`, once decoded). -/
def slotPt (m : Mem) (base : Addr) : Point := ⟨EV m base 6, EV m base 7, 1⟩

/-- The state after `tabInit`, from the state `s` before it. -/
structure IOut (s : State) (base : Addr) (t : State) : Prop where
  inv : TInv t base (slotPt s.mem base) 2 t
  one : EV t.mem base 20 = 1
  rx : ∀ i < 8, limbs t.mem base RX i = limbs s.mem base (slot 8) i
  ry : ∀ i < 8, limbs t.mem base RY i = limbs s.mem base (slot 9) i
  chk : t.gpr .x20 = s.gpr .x20
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : IFrame base s.mem t.mem

/-! ## The copies and constants -/

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-- A word kept by a step that wrote only `[o, o + n)`. -/
theorem kw {base : Addr} {m m' : Mem} {o n : Nat} (h : Outside base o n m m') {d : Nat} (hd : d + 8 ≤ o ∨ o + n ≤ d)
    (hd' : d + 8 ≤ 8192) : word m' base d = word m base d := h.word hd hd'

/-- The first part of `tabInit`: everything but the first entry's store. -/
def tabPre : List Instr :=
  Impl.Curve448.AArch64.copy RX (slot 8) ++ Impl.Curve448.AArch64.copy RY (slot 9) ++
  constSlot (slot 19) 0 ++ constSlot (slot 20) 1 ++
  constSlot TAB 0 ++ constSlot (TAB + 64) 1 ++ constSlot (TAB + 128) 1 ++
  Impl.Curve448.AArch64.copy (slot 3) (slot 6) ++ Impl.Curve448.AArch64.copy (slot 4) (slot 7) ++ constSlot (slot 5) 1 ++
  constSlot (slot 8) 1

theorem tabInit_eq : tabInit = tabPre ++ (([.movz .x .x19 1 0] : List Instr) ++ (tabStore ++ ([.movz .x .x19 2 0] : List Instr))) := by
  simp only [tabInit, tabPre, List.append_assoc]

/-- Memory unchanged within `[lo, hi)` of the working space. -/
def KeepIn (base : Addr) (lo hi : Nat) (m m' : Mem) : Prop :=
  ∀ x, lo ≤ ofs base x → ofs base x < hi → m' x = m x

theorem KeepIn.trans {base : Addr} {lo hi : Nat} {m₁ m₂ m₃ : Mem} (h₁ : KeepIn base lo hi m₁ m₂)
    (h₂ : KeepIn base lo hi m₂ m₃) : KeepIn base lo hi m₁ m₃ := fun x a b => (h₂ x a b).trans (h₁ x a b)

theorem KeepIn.of_outside {base : Addr} {lo hi o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hd : hi ≤ o ∨ o + n ≤ lo) : KeepIn base lo hi m m' := fun x a b => h x (by omega)

theorem KeepIn.word {base : Addr} {lo hi : Nat} {m m' : Mem} (h : KeepIn base lo hi m m') {d : Nat}
    (hl : lo ≤ d) (hh : d + 8 ≤ hi) (hd : d + 8 ≤ 8192) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi' => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem KeepIn.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : KeepIn base o (o + 64) m m') (ho : o + 64 ≤ 8192)
    {i : Nat} (hi : i < 8) : limbs m' base o i = limbs m base o i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega) (by omega))

/-- What `tabPre` leaves. -/
structure PreOut (s : State) (base : Addr) (t : State) : Prop where
  rx : ∀ i < 8, limbs t.mem base RX i = limbs s.mem base (slot 8) i
  ry : ∀ i < 8, limbs t.mem base RY i = limbs s.mem base (slot 9) i
  z19 : ∀ w < 8, word t.mem base (slot 19 + 8 * w) = limb 0 w
  o20 : ∀ w < 8, word t.mem base (slot 20 + 8 * w) = limb 1 w
  t0 : ∀ w < 8, word t.mem base (TAB + 8 * w) = limb 0 w
  t1 : ∀ w < 8, word t.mem base (TAB + 64 + 8 * w) = limb 1 w
  t2 : ∀ w < 8, word t.mem base (TAB + 128 + 8 * w) = limb 1 w
  s3 : ∀ i < 8, limbs t.mem base (slot 3) i = limbs s.mem base (slot 6) i
  s4 : ∀ i < 8, limbs t.mem base (slot 4) i = limbs s.mem base (slot 7) i
  s5 : ∀ w < 8, word t.mem base (slot 5 + 8 * w) = limb 1 w
  s8 : ∀ w < 8, word t.mem base (slot 8 + 8 * w) = limb 1 w
  keep : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ slot 3 ∨ slot 5 + 64 ≤ d) → (d + 8 ≤ slot 8 ∨ slot 8 + 64 ≤ d) →
    (d + 8 ≤ slot 19 ∨ slot 20 + 64 ≤ d) →
    (d + 8 ≤ RX ∨ RX + 128 ≤ d) → (d + 8 ≤ RY ∨ TAB + 192 ≤ d) → word t.mem base d = word s.mem base d
  mem : IFrame base s.mem t.mem
  regs : Keeps (.x4 :: VG.Proof.X448.AArch64.clob) s t

theorem tabPre_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block tabPre) s (PreOut s base) := by
  simp only [tabPre, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok hs (o := RX) (a := slot 8) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u1 ⟨v1, o1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok h1 (o := RY) (a := slot 9) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u2 ⟨v2, o2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h2 (o := slot 19) (by decide) (by decide) 0) fun u3 ⟨v3, o3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h3 (o := slot 20) (by decide) (by decide) 1) fun u4 ⟨v4, o4, k4⟩ => ?_
  have h4 := h3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h4 (o := TAB) (by decide) (by decide) 0) fun u5 ⟨v5, o5, k5⟩ => ?_
  have h5 := h4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h5 (o := TAB + 64) (by decide) (by decide) 1) fun u6 ⟨v6, o6, k6⟩ => ?_
  have h6 := h5.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h6 (o := TAB + 128) (by decide) (by decide) 1) fun u7 ⟨v7, o7, k7⟩ => ?_
  have h7 := h6.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok h7 (o := slot 3) (a := slot 6) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u8 ⟨v8, o8, k8⟩ => ?_
  have h8 := h7.of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copyS_ok h8 (o := slot 4) (a := slot 7) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u9 ⟨v9, o9, k9⟩ => ?_
  have h9 := h8.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constSlot_ok h9 (o := slot 5) (by decide) (by decide) 1) fun u10 ⟨v10, o10, k10⟩ => ?_
  have h10 := h9.of_keeps k10 (by decide)
  refine WP.mono (constSlot_ok h10 (o := slot 8) (by decide) (by decide) 1) fun u ⟨v11, o11, k11⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
    fun w hw => ?_, fun i hi => ?_, fun i hi => ?_, fun w hw => ?_, fun w hw => ?_, fun d hd a b c e f => ?_, ?_,
    ?_⟩
  · have k : KeepIn base RX (RX + 64) u1.mem u.mem := ((((((((((KeepIn.of_outside o2 (by decide)).trans (KeepIn.of_outside o3 (by decide))).trans (KeepIn.of_outside o4 (by decide))).trans (KeepIn.of_outside o5 (by decide))).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.limbs (by decide) hi]; exact v1 i hi
  · have k : KeepIn base RY (RY + 64) u2.mem u.mem := (((((((((KeepIn.of_outside o3 (by decide)).trans (KeepIn.of_outside o4 (by decide))).trans (KeepIn.of_outside o5 (by decide))).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    have k1 : KeepIn base (slot 9) (slot 9 + 64) s.mem u1.mem := (KeepIn.of_outside o1 (by decide))
    rw [k.limbs (by decide) hi, v2 i hi, k1.limbs (by decide) hi]
  · have k : KeepIn base (slot 19) (slot 19 + 64) u3.mem u.mem := ((((((((KeepIn.of_outside o4 (by decide)).trans (KeepIn.of_outside o5 (by decide))).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.word (by omega) (by omega) (by simp only [slot]; omega)]; exact v3 w hw
  · have k : KeepIn base (slot 20) (slot 20 + 64) u4.mem u.mem := (((((((KeepIn.of_outside o5 (by decide)).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.word (by omega) (by omega) (by simp only [slot]; omega)]; exact v4 w hw
  · have k : KeepIn base (TAB) (TAB + 64) u5.mem u.mem := ((((((KeepIn.of_outside o6 (by decide)).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.word (by omega) (by omega) (by simp only [TAB]; omega)]; exact v5 w hw
  · have k : KeepIn base (TAB + 64) (TAB + 64 + 64) u6.mem u.mem := (((((KeepIn.of_outside o7 (by decide)).trans (KeepIn.of_outside o8 (by decide))).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.word (by omega) (by omega) (by simp only [TAB]; omega)]; exact v6 w hw
  · have k : KeepIn base (TAB + 128) (TAB + 128 + 64) u7.mem u.mem := ((((KeepIn.of_outside o8 (by decide)).trans (KeepIn.of_outside o9 (by decide))).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    rw [k.word (by omega) (by omega) (by simp only [TAB]; omega)]; exact v7 w hw
  · have k : KeepIn base (slot 3) (slot 3 + 64) u8.mem u.mem := (((KeepIn.of_outside o9 (by decide)).trans (KeepIn.of_outside o10 (by decide))).trans (KeepIn.of_outside o11 (by decide)))
    have k' : KeepIn base (slot 6) (slot 6 + 64) s.mem u7.mem := (((((((KeepIn.of_outside o1 (by decide)).trans (KeepIn.of_outside o2 (by decide))).trans (KeepIn.of_outside o3 (by decide))).trans (KeepIn.of_outside o4 (by decide))).trans (KeepIn.of_outside o5 (by decide))).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide)))
    rw [k.limbs (by decide) hi, v8 i hi, k'.limbs (by decide) hi]
  · have k : KeepIn base (slot 4) (slot 4 + 64) u9.mem u.mem := ((KeepIn.of_outside o10 (by decide)).trans (KeepIn.of_outside o11 (by decide)))
    have k' : KeepIn base (slot 7) (slot 7 + 64) s.mem u8.mem := ((((((((KeepIn.of_outside o1 (by decide)).trans (KeepIn.of_outside o2 (by decide))).trans (KeepIn.of_outside o3 (by decide))).trans (KeepIn.of_outside o4 (by decide))).trans (KeepIn.of_outside o5 (by decide))).trans (KeepIn.of_outside o6 (by decide))).trans (KeepIn.of_outside o7 (by decide))).trans (KeepIn.of_outside o8 (by decide)))
    rw [k.limbs (by decide) hi, v9 i hi, k'.limbs (by decide) hi]
  · have k : KeepIn base (slot 5) (slot 5 + 64) u10.mem u.mem := (KeepIn.of_outside o11 (by decide))
    rw [k.word (by omega) (by omega) (by simp only [slot]; omega)]; exact v10 w hw
  · exact v11 w hw
  · rw [kw o11 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o10 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o9 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o8 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o7 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o6 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o5 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o4 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o3 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o2 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd, kw o1 (by simp only [slot, RX, RY, CAN, TAB] at *; omega) hd]
  · exact (((((((((((IFrame.of_outside o1 (by decide)).trans (IFrame.of_outside o2 (by decide))).trans (IFrame.of_outside o3 (by decide))).trans (IFrame.of_outside o4 (by decide))).trans (IFrame.of_outside o5 (by decide))).trans (IFrame.of_outside o6 (by decide))).trans (IFrame.of_outside o7 (by decide))).trans (IFrame.of_outside o8 (by decide))).trans (IFrame.of_outside o9 (by decide))).trans (IFrame.of_outside o10 (by decide))).trans (IFrame.of_outside o11 (by decide)))
  · exact (((((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))).trans (k10.mono (by decide))).trans (k11.mono (by decide)))

/-! ## `tabInit` -/

/-- A slot equal limb by limb to a bounded slot is bounded. -/
theorem ib_of_limbs {m m' : Mem} {base : Addr} {o o' : Nat} (h : ∀ i < 8, limbs m' base o' i = limbs m base o i)
    (hb : Bnd Ib m base o) : Bnd Ib m' base o' := fun i hi => by rw [h i hi]; exact hb i hi

theorem tabInit_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : BEnv s.mem base) :
    WP isa (.block tabInit) s (IOut s base) := by
  rw [tabInit_eq, WP.block_append_iff]
  refine WP.mono (tabPre_ok hs) fun u P => ?_
  have hu : Scr u base := hs.of_keeps P.regs (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok u 1 (by decide))
    fun u1 ⟨c1, g1, m1, rd1, wr1⟩ => ?_
  have hu1 : Scr u1 base := ⟨(g1 _ (by decide)).trans hu.x3, (g1 _ (by decide)).trans hu.mask,
    wr1 ▸ hu.wr, hu.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (tabStore_ok hu1 (e := 1) (by decide) c1) fun u2 ⟨w2, o2, k2⟩ => ?_
  have hu2 : Scr u2 base := hu1.of_keeps k2 (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok u2 2 (by decide))
    fun t ⟨ct, gt, mt, rdt, wrt⟩ => ?_
  have ht : Scr t base := ⟨(gt _ (by decide)).trans hu2.x3, (gt _ (by decide)).trans hu2.mask,
    wrt ▸ hu2.wr, hu2.nowrap⟩
  -- The memory from `u` to `t`: entry 1 alone changes.
  have hmut : Outside base (TAB + 192 * 1) 192 u.mem t.mem := by rw [mt, ← m1]; exact o2
  have wut : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ TAB + 192 ∨ TAB + 384 ≤ d) → word t.mem base d = word u.mem base d :=
    fun d hd hr => hmut.word (by simpa using hr) hd
  have lut : ∀ o, o + 64 ≤ TAB + 192 ∨ TAB + 384 ≤ o → o + 64 ≤ 8192 → ∀ i < 8,
      limbs t.mem base o i = limbs u.mem base o i :=
    fun o ho ho' i hi => congrArg BitVec.toNat (wut _ (by omega) (by omega))
  -- Every slot of `t`, below `Ib`.
  have slotKeep : ∀ i : Index, i.val ≠ 3 → i.val ≠ 4 → i.val ≠ 5 → i.val ≠ 8 → i.val ≠ 19 → i.val ≠ 20 →
      ∀ j < 8, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j :=
    fun i h3 h4 h5 h8 h19 h20 j hj => by
      have := i.isLt
      rw [lut _ (by simp only [slot, TAB]; omega) (by simp only [slot]; omega) j hj]
      exact congrArg BitVec.toNat (P.keep _ (by simp only [slot]; omega) (by simp only [slot]; omega)
        (by simp only [slot]; omega) (by simp only [slot]; omega) (by simp only [slot, RX]; omega)
        (by simp only [slot, RY, CAN]; omega))
  have wslot : ∀ (o : Nat) (v : Spec.X448.Fe), o + 64 ≤ TAB + 192 → (∀ w < 8, word u.mem base (o + 8 * w) = limb v w) →
      ∀ w < 8, word t.mem base (o + 8 * w) = limb v w := fun o v ho h w hw => by
    rw [wut _ (by simp only [TAB] at ho; omega) (by omega)]; exact h w hw
  have z19 := wslot _ _ (by decide) P.z19
  have o20 := wslot _ _ (by decide) P.o20
  have s5 := wslot _ _ (by decide) P.s5
  have s8 := wslot _ _ (by decide) P.s8
  have l3 : ∀ i < 8, limbs t.mem base (slot 3) i = limbs s.mem base (slot 6) i := fun i hi => by
    rw [lut _ (by decide) (by decide) i hi]; exact P.s3 i hi
  have l4 : ∀ i < 8, limbs t.mem base (slot 4) i = limbs s.mem base (slot 7) i := fun i hi => by
    rw [lut _ (by decide) (by decide) i hi]; exact P.s4 i hi
  have b6 := hb 6
  have b7 := hb 7
  have benv : BEnv t.mem base := by
    intro i
    by_cases h6 : i.val ≠ 3 ∧ i.val ≠ 4 ∧ i.val ≠ 5 ∧ i.val ≠ 8 ∧ i.val ≠ 19 ∧ i.val ≠ 20
    · exact ib_of_limbs (fun j hj => slotKeep i h6.1 h6.2.1 h6.2.2.1 h6.2.2.2.1 h6.2.2.2.2.1 h6.2.2.2.2.2 j hj)
        (hb i)
    · have hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 8 ∨ i = 19 ∨ i = 20 := by
        rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at h6 ⊢; omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ib_of_limbs l3 b6
      · exact ib_of_limbs l4 b7
      · exact bnd_of_words s5
      · exact bnd_of_words s8
      · exact bnd_of_words z19
      · exact bnd_of_words o20
  have hP : pt (EV u.mem base) 3 4 5 = slotPt s.mem base := by
    show (⟨FV u.mem base (slot 3), FV u.mem base (slot 4), FV u.mem base (slot 5)⟩ : Point) =
      ⟨FV s.mem base (slot 6), FV s.mem base (slot 7), 1⟩
    rw [FV_of_limbs P.s3, FV_of_limbs P.s4, F_of_words P.s5]
  have hP3 : pt (EV t.mem base) 3 4 5 = slotPt s.mem base := by
    show (⟨FV t.mem base (slot 3), FV t.mem base (slot 4), FV t.mem base (slot 5)⟩ : Point) =
      ⟨FV s.mem base (slot 6), FV s.mem base (slot 7), 1⟩
    rw [FV_of_limbs l3, FV_of_limbs l4, F_of_words s5]
  have hP6 : pt (EV t.mem base) 6 7 8 = slotPt s.mem base := by
    show (⟨FV t.mem base (slot 6), FV t.mem base (slot 7), FV t.mem base (slot 8)⟩ : Point) =
      ⟨FV s.mem base (slot 6), FV s.mem base (slot 7), 1⟩
    have l6 : ∀ j < 8, limbs t.mem base (slot 6) j = limbs s.mem base (slot 6) j :=
      slotKeep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have l7 : ∀ j < 8, limbs t.mem base (slot 7) j = limbs s.mem base (slot 7) j :=
      slotKeep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [FV_of_limbs l6, FV_of_limbs l7, F_of_words s8]
  have e1 : TPt t.mem base 1 = slotPt s.mem base := by
    rw [show t.mem = u2.mem from mt, tabStore_pt w2, show pt (EV u1.mem base) 3 4 5 = pt (EV u.mem base) 3 4 5 by rw [m1],
      hP]
  have e0 : TPt t.mem base 0 = ⟨0, 1, 1⟩ := by
    have hw : ∀ (c : Nat) (v : Spec.X448.Fe), c < 3 → (∀ w < 8, word u.mem base (TAB + 64 * c + 8 * w) = limb v w) →
        FV t.mem base (TAB + 192 * 0 + 64 * c) = v := fun c v hc h =>
      F_of_words fun w hw => by
        rw [wut _ (by simp only [TAB]; omega) (by simp only [TAB]; omega), show TAB + 192 * 0 + 64 * c + 8 * w =
          TAB + 64 * c + 8 * w by omega]
        exact h w hw
    simp only [TPt]
    rw [show TAB + 192 * 0 = TAB + 192 * 0 + 64 * 0 by rfl, hw 0 0 (by decide) (fun w hw => by rw [show TAB + 64 * 0 + 8 * w = TAB + 8 * w by omega]; exact P.t0 w hw),
      show TAB + 192 * 0 + 64 = TAB + 192 * 0 + 64 * 1 by rfl, hw 1 1 (by decide) P.t1,
      show TAB + 192 * 0 + 128 = TAB + 192 * 0 + 64 * 2 by rfl, hw 2 1 (by decide) P.t2]
  refine ⟨⟨⟨by decide, by decide⟩, ht, benv, fun w hw => ?_, ct, by rw [hP3]; rfl, hP6, rfl,
      fun e he => ?_, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩,
    F_of_words o20, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · show (word t.mem base (slot 19 + 8 * w)).toNat = 0
    rw [z19 w hw, limb_zero]; rfl
  · rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · refine ⟨e0, fun w hw => ?_⟩
      rw [tw, wut _ (by simp only [TAB]; omega) (by simp only [TAB]; omega)]
      have hw' : w = 8 * (w / 8) + w % 8 := by omega
      rcases (show w / 8 = 0 ∨ w / 8 = 1 ∨ w / 8 = 2 by omega) with h | h | h <;> rw [h] at hw'
      · rw [show TAB + 192 * 0 + 8 * w = TAB + 8 * (w % 8) by omega, P.t0 _ (by omega)]
        exact Nat.lt_trans (limb_lt _ _) (by decide)
      · rw [show TAB + 192 * 0 + 8 * w = TAB + 64 + 8 * (w % 8) by omega, P.t1 _ (by omega)]
        exact Nat.lt_trans (limb_lt _ _) (by decide)
      · rw [show TAB + 192 * 0 + 8 * w = TAB + 128 + 8 * (w % 8) by omega, P.t2 _ (by omega)]
        exact Nat.lt_trans (limb_lt _ _) (by decide)
    · refine ⟨e1, ?_⟩
      rw [show t.mem = u2.mem from mt]
      intro w hw
      rw [tw, w2 w hw, src, m1]
      have h0 : Bnd Ib u.mem base (slot 3) := ib_of_limbs P.s3 b6
      have h1 : Bnd Ib u.mem base (slot 4) := ib_of_limbs P.s4 b7
      have h2 : Bnd Ib u.mem base (slot 5) := bnd_of_words P.s5
      rcases (show w / 8 = 0 ∨ w / 8 = 1 ∨ w / 8 = 2 by omega) with h | h | h <;> rw [h]
      · exact h0 _ (Nat.mod_lt _ (by decide))
      · exact h1 _ (Nat.mod_lt _ (by decide))
      · exact h2 _ (Nat.mod_lt _ (by decide))
  · rw [lut _ (by simp only [RX, TAB]; omega) (by decide) i hi]; exact P.rx i hi
  · rw [lut _ (by simp only [RY, CAN, TAB]; omega) (by decide) i hi]; exact P.ry i hi
  · rw [gt _ (by decide), k2.1 _ (by decide), g1 _ (by decide), P.regs.1 _ (by decide)]
  · rw [rdt, k2.2.1, rd1, P.regs.2.1]
  · rw [wrt, k2.2.2, wr1, P.regs.2.2]
  · exact P.mem.trans (IFrame.of_outside hmut (by decide))

end VG.Proof.Ed448.AArch64.Window
