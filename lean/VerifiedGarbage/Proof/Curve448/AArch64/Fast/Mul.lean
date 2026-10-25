module

public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Loop
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Finish
public import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Prelude
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Columns
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block

/-!
# Multiplication

Untrusted: everything here is checked by Lean. `mul o a b` writes the
limbs `out r` of the reduced schoolbook coefficients `r` of `[a] * [b]` to
`o`, for operand limbs below `Ib`.
-/

@[expose] public section

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix pair rows reduced)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 writeW_outside limbs FieldMem ofs)

/-- The registers every field operation may write. -/
def clob : List Reg :=
  [.x0, .x2, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

def kakb (rb : Reg) (b : Nat) : List Instr :=
  (List.range 4).flatMap (fun i =>
    [.add .x Mul.R.p0 (Mul.A i) (Mul.A (i + 4)), st Mul.R.p0 (KA + 8 * i),
      .ldr .x Mul.R.t rb (b + 8 * i), .ldr .x Mul.R.p1 rb (b + 32 + 8 * i),
      .add .x Mul.R.t Mul.R.t Mul.R.p1, st Mul.R.t (KB + 8 * i)])

theorem mulAt_split (ra : Reg) (a : Nat) (rb : Reg) (b : Nat) (ro : Reg) (o : Nat) :
    mulAt ra a rb b ro o = loadA ra a ++ consts ++ kakb rb b ++
      columns Mul.R rb b Mul.L Mul.H Mul.column ro o ++ finish ro o :=
  rfl

theorem kakb_ok {s : State} {base : Addr} (hs : Scr s base) {rb : Reg} {D b : Nat}
    (hp : PtrOk s base rb D b) (hb : b + 64 ≤ ACC) (hrb : rb ∉ [Reg.x10, .x11, .x13]) :
    WP isa (.block (kakb rb D)) s fun t =>
      (∀ i < 4, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
      (∀ i < 4, word t.mem base (KB + 8 * i) =
        word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
      Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (KA + 8 * i) = s.gpr (Mul.A i) + s.gpr (Mul.A (i + 4))) ∧
    (∀ i < n, word t.mem base (KB + 8 * i) =
      word s.mem base (b + 8 * i) + word s.mem base (b + 32 + 8 * i)) ∧
    Outside base KA 64 s.mem t.mem ∧ Keeps [.x10, .x11, .x13] s t
  refine wp_range_flatMap (M := isa) (N := 4) inv (fun n t hn ⟨ta, tb, tO, tk⟩ => ?_) 4 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  have treg : ∀ i < 8, t.gpr (Mul.A i) = s.gpr (Mul.A i) := fun i hi => tk.1 _ (A_ne i hi)
  have tw : ∀ d, d + 8 ≤ KA → word t.mem base d = word s.mem base d := fun d hd =>
    tO.word (Or.inl hd) (by omega_arith)
  refine WP.mono (kakbStep_ok ts (hp.of_keeps tk hrb) hb hrb hn) fun u ⟨ua, ub, uo, uk, uw⟩ => ?_
  refine ⟨fun i hi => ?_, fun i hi => ?_, tO.trans uo, tk.trans uk⟩
  · by_cases h : i = n
    · subst h; rw [ua, treg i (by omega_arith), treg (i + 4) (by omega_arith)]
    · rw [uw _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact ta i (by omega_arith)
  · by_cases h : i = n
    · subst h; rw [ub, tw _ (by omega_arith), tw _ (by omega_arith)]
    · rw [uw _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact tb i (by omega_arith)

theorem mul_good : Good Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_colRegs : ColRegs Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide
theorem mul_ops : ∀ d < 4, (Mul.column d).all
    (opOk (writes Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) [Mul.L, Mul.H, Mul.X, Mul.Y]) = true := by
  decide

theorem A_consts : ∀ i < 8, Mul.A i ∉ [MASK, ZERO] := by decide

theorem A_colWrites : ∀ i < 8, Mul.A i ∉ colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y] := by decide

/-- The product's limbs, from the operands' limbs. -/
abbrev prodOut (f g : Nat → Nat) : Nat → Nat := out (reduced (rows f g 8))

theorem fits_of {f g : Nat → Nat} (hf : ∀ i < 8, f i < Ib) (hg : ∀ i < 8, g i < Ib) :
    Fits (reduced (rows f g 8)) :=
  fits fun k _ => reduced_le (fun i hi => Nat.le_sub_one_of_lt (hf i hi))
    (fun i hi => Nat.le_sub_one_of_lt (hg i hi)) k

theorem stage_limbs {base : Addr} {o : Nat} {r : Nat → Nat} {s t : State} (hi : ColInv base o r s t 4) :
    ∀ i < 8, (word t.mem base (o + 8 * i)).toNat =
      (if i < 4 then chainLimb r 0 i else chainLimb r 4 (i - 4)) := by
  intro i hi'
  by_cases h : i < 4
  · rw [ite_eq_left h]; exact hi.lo i h
  · rw [ite_eq_right h, show i = 4 + (i - 4) by omega_arith]
    rw [hi.hi (i - 4) (by omega_arith)]; simp

theorem finVal_out (r : Nat → Nat) :
    ∀ i < 8, finVal (fun i => if i < 4 then chainLimb r 0 i else chainLimb r 4 (i - 4))
      (chain r 0 4) (chain r 4 4) i = out r i := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_arith
  all_goals simp only [finVal, out]; rfl

theorem aRegs_clob : ∀ r ∈ aRegs, r ∈ clob := by decide
theorem consts_clob : ∀ r ∈ [MASK, ZERO], r ∈ clob := by decide
theorem kakb_clob : ∀ r ∈ [Reg.x10, .x11, .x13], r ∈ clob := by decide
theorem colWrites_clob : ∀ r ∈ colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y], r ∈ clob := by decide
theorem finish_clob : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], r ∈ clob := by decide

/-- **A product** of operands each addressed by a register plus a displacement (`PtrOk`), at
offsets `a`, `b` and `o` of the working space below the coefficients: the result's limbs, and
only the result's 64 bytes and the operand sums' 64 bytes (`KA`) written. The pointers of `b` and
`o` are not among the registers the product writes, nor `a`'s among those the operand loads write. -/
theorem mulAt_ok {s : State} {base : Addr} (hs : Scr s base) {ra rb ro : Reg} {da db od a b o : Nat}
    (hpa : PtrOk s base ra da a) (hpb : PtrOk s base rb db b) (hpo : PtrOk s base ro od o)
    (hra : ra ∉ aRegs) (hrb : rb ∉ clob) (hro : ro ∉ clob)
    (ho : o + 64 ≤ ACC) (hb : b + 64 ≤ ACC) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (.block (mulAt ra da rb db ro od)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      Outside2 base o 64 KA 64 s.mem t.mem ∧ Keeps clob s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  have hKB : KB = 3616 := rfl
  let f := limbs s.mem base a
  let g := limbs s.mem base b
  have nclob : ∀ {r : Reg} {rs : List Reg}, r ∉ clob → (∀ q ∈ rs, q ∈ clob) → r ∉ rs :=
    fun hr hs h => hr (hs _ h)
  rw [mulAt_split, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadA_ok hs hpa hra) fun t1 ⟨a1, m1, k1⟩ => ?_
  have s1 : Scr t1 base := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok t1) fun t2 ⟨mk2, z2, m2, k2⟩ => ?_
  have s2 : Scr t2 base := s1.of_keeps k2 (by decide)
  have pb2 : PtrOk t2 base rb db b :=
    (hpb.of_keeps k1 (nclob hrb aRegs_clob)).of_keeps k2 (nclob hrb consts_clob)
  have po2 : PtrOk t2 base ro od o :=
    (hpo.of_keeps k1 (nclob hro aRegs_clob)).of_keeps k2 (nclob hro consts_clob)
  rw [WP.block_append_iff]
  refine WP.mono (kakb_ok s2 pb2 hb (nclob hrb kakb_clob)) fun t3 ⟨ka3, kb3, o3, k3⟩ => ?_
  have s3 : Scr t3 base := s2.of_keeps k3 (by decide)
  have pb3 : PtrOk t3 base rb db b := pb2.of_keeps k3 (nclob hrb kakb_clob)
  have po3 : PtrOk t3 base ro od o := po2.of_keeps k3 (nclob hro kakb_clob)
  have A3 : ∀ i < 8, (t3.gpr (Mul.A i)).toNat = f i := by
    intro i hi
    rw [k3.1 _ (A_ne i hi), k2.1 _ (A_consts i hi), a1 i hi]
  have g3 : ∀ j < 8, word t3.mem base (b + 8 * j) = word s.mem base (b + 8 * j) := by
    intro j hj
    rw [o3.word (Or.inl (by omega_arith)) (by omega_arith), m2, m1]
  have sumlt : ∀ x y : BitVec 64, x.toNat < Ib → y.toNat < Ib → (x + y).toNat = x.toNat + y.toNat :=
    fun x y hx hy => by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [Ib] at hx hy; omega_arith)]
  have hfit := fits_of fa fb
  let P := fun (t : State) =>
    (∀ i < 8, t.gpr (Mul.A i) = t3.gpr (Mul.A i)) ∧
    (∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 64 ≤ d) → word t.mem base d = word t3.mem base d)
  have hP : ∀ t u, P t → Keeps (colWrites Mul.R [Mul.L, Mul.H, Mul.X, Mul.Y]) t u →
      Outside base o 64 t.mem u.mem → P u := by
    intro t u ⟨pa, pm⟩ k o
    exact ⟨fun i hi => (k.1 _ (A_colWrites i hi)).trans (pa i hi),
      fun d hd hd' => (o.word hd' hd).trans (pm d hd hd')⟩
  have hsem : ∀ d < 4, ∀ t, P t → ∀ e,
      sem (srcVal t base b) e (Mul.column d) Mul.L = reduced (rows f g 8) d ∧
      sem (srcVal t base b) e (Mul.column d) Mul.H = reduced (rows f g 8) (d + 4) := by
    intro d hd t ⟨pa, pm⟩ e
    have va : ∀ i < 8, srcVal t base b (.reg (Mul.A i)) = f i := fun i hi => by
      simp only [srcVal]; rw [pa i hi, A3 i hi]
    have vb : ∀ j < 8, srcVal t base b (.arg j) = g j := fun j hj => by
      simp only [srcVal]; rw [pm _ (by omega_arith) (by omega_arith), g3 j hj]
    refine mulCol_ok f g (srcVal t base b) ?_ ?_ ?_ e hd
    · intro i j hi hj
      change ((srcVal t base b (.reg (Mul.A i)) : Nat) : Int) * (srcVal t base b (.arg j) : Nat) = _
      rw [va i (by omega_arith), vb j (by omega_arith)]
    · intro i j hi hj
      change ((srcVal t base b (.reg (Mul.A (i + 4))) : Nat) : Int) *
        (srcVal t base b (.arg (j + 4)) : Nat) = _
      rw [va _ (by omega_arith), vb _ (by omega_arith)]
    · intro i j hi hj
      change ((word t.mem base (KA + 8 * i)).toNat : Int) * ((word t.mem base (KB + 8 * j)).toNat : Int) = _
      have e1 : ∀ i < 8, (t2.gpr (Mul.A i)).toNat = f i := fun i hi => by
        rw [k2.1 _ (A_consts i hi), a1 i hi]
      rw [pm _ (by omega_arith) (by omega_arith), pm _ (by omega_arith) (by omega_arith), ka3 i hi, kb3 j hj,
        m2, m1]
      have x1 := sumlt (t2.gpr (Mul.A i)) (t2.gpr (Mul.A (i + 4)))
        (by rw [e1 i (by omega_arith)]; exact fa i (by omega_arith)) (by rw [e1 (i + 4) (by omega_arith)]; exact fa _ (by omega_arith))
      have gb : word s.mem base (b + 32 + 8 * j) = word s.mem base (b + 8 * (j + 4)) := by
        rw [show b + 32 + 8 * j = b + 8 * (j + 4) by omega_arith]
      have x2 := sumlt (word s.mem base (b + 8 * j)) (word s.mem base (b + 32 + 8 * j))
        (fb j (by omega_arith)) (by rw [gb]; exact fb _ (by omega_arith))
      rw [x1, x2, e1 i (by omega_arith), e1 (i + 4) (by omega_arith), gb]
      push_cast
      rfl
  rw [WP.block_append_iff]
  refine WP.mono (columns_ok mul_good mul_colRegs (by decide) (by decide) (by decide)
    (nclob hrb colWrites_clob) (nclob hro colWrites_clob) hfit mul_ops P hP hsem s3 pb3 po3
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    (by rw [k3.1 _ (by decide)]; exact mk2) (by rw [k3.1 _ (by decide)]; exact z2))
    fun t4 ⟨p4, i4, k4⟩ => ?_
  have hcl := i4.cl (by decide)
  have hch := i4.ch (by decide)
  have lb : ∀ j < 8, (if j < 4 then chainLimb (reduced (rows f g 8)) 0 j
      else chainLimb (reduced (rows f g 8)) 4 (j - 4)) < radix := fun j _ => by
    split <;> exact Nat.mod_lt _ (by decide)
  refine WP.mono (finish_ok i4.scr (po3.of_keeps k4 (nclob hro colWrites_clob))
    (nclob hro finish_clob) i4.mask (stage_limbs i4) lb hcl hch hfit.c₀ hfit.c₄)
    fun t5 ⟨v5, o5, k5⟩ => ⟨fun i hi => by rw [v5 i hi, finVal_out _ i hi], ?_, ?_⟩
  · intro x h1 h2
    simp only [ofs] at h1 h2
    rw [o5 x (by simp only [ofs]; omega_arith), i4.out x (by simp only [ofs]; omega_arith),
      o3 x (by simp only [ofs]; omega_arith), m2, m1]
  · refine (k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans (k5.mono ?_))))
    all_goals intro r hr; revert r; decide

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : o + 64 ≤ ACC) (ho8 : o % 8 = 0) (ha : a + 64 ≤ ACC) (ha8 : a % 8 = 0)
    (hb : b + 64 ≤ ACC) (hb8 : b % 8 = 0) (hob : o + 64 ≤ b ∨ b + 64 ≤ o)
    (fa : ∀ i < 8, limbs s.mem base a i < Ib) (fb : ∀ i < 8, limbs s.mem base b i < Ib) :
    WP isa (.block (mul o a b)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = prodOut (limbs s.mem base a) (limbs s.mem base b) i) ∧
      FieldMem base o s.mem t.mem ∧ Keeps clob s t := by
  have hA : ACC = 3584 := rfl
  have hKA : KA = 3584 := rfl
  refine WP.mono (mulAt_ok hs (PtrOk.x3 hs ha8 (by omega_arith)) (PtrOk.x3 hs hb8 (by omega_arith))
    (PtrOk.x3 hs ho8 (by omega_arith)) (by decide) (by decide) (by decide) ho hb hob fa fb)
    fun t ⟨tv, tm, tk⟩ => ⟨tv, fun x h1 h2 => tm x (by omega_arith) (by omega_arith), tk⟩

end VG.Proof.Curve448.AArch64.Fast
