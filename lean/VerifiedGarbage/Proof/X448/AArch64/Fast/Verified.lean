import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Field
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.Curve448.AArch64.Square
import VerifiedGarbage.Impl.X448.AArch64.Fast
import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Mul2
import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.X448.AArch64.Fast.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Env`. -/
section

/-!
# X448 on AArch64: the working space as field-element slots

Untrusted: everything here is checked by Lean. Each field operation updates
the slots it writes. Every slot's limbs stay below `Ib`; products leave
reduced limbs (below `Mb`), which sums and differences need of their
operands.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot)
open VG.Proof.X448.AArch64.Weak (Index Env slot_bound slot_aligned slot_sep opMul opAdd opSub
  opA24 opCopy opSwap)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (toFe)

abbrev fclob := VG.Proof.Curve448.AArch64.Fast.clob

/-- Limbs below `n`. -/
def Bnd (n : Nat) (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 8, limbs m base o i < n

/-- Every slot's limbs are below `Ib`. -/
def BEnv (m : Mem) (base : Addr) : Prop := ∀ i : Index, VG.Proof.X448.AArch64.Fast.Bnd Ib m base (slot i.val)

/-- What a field operation preserves: registers outside `clob`, and memory
outside the field slots and the coefficient area. -/
structure FKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps VG.Proof.X448.AArch64.Fast.fclob s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem FKeep.refl (base : Addr) (s : State) : VG.Proof.X448.AArch64.Fast.FKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem FKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.AArch64.Fast.FKeep base s t) (h' : VG.Proof.X448.AArch64.Fast.FKeep base t u) :
    VG.Proof.X448.AArch64.Fast.FKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem FKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Fast.FKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

/-- Slots other than `os` keep their limbs. -/
def Same (base : Addr) (os : List Index) (m m' : Mem) : Prop :=
  ∀ i : Index, i ∉ os → ∀ j < 8, limbs m' base (slot i.val) j = limbs m base (slot i.val) j

theorem Same.bnd {base : Addr} {os : List Index} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.Same base os m m') {n : Nat}
    {i : Index} (hi : i ∉ os) (hb : VG.Proof.X448.AArch64.Fast.Bnd n m base (slot i.val)) : VG.Proof.X448.AArch64.Fast.Bnd n m' base (slot i.val) :=
  fun j hj => by rw [h i hi j hj]; exact hb j hj

theorem Same.env {base : Addr} {os : List Index} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.Same base os m m') {i : Index}
    (hi : i ∉ os) : VG.Proof.X448.AArch64.Weak.E m' base i = VG.Proof.X448.AArch64.Weak.E m base i :=
  congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr (h i hi))

theorem slot_lt (i : Index) : slot i.val + 128 ≤ ACC := slot_bound i

theorem slot_64 (i : Index) : slot i.val + 64 ≤ ACC := by have := slot_bound i; omega

theorem slot_mem (i : Index) : slot i.val + 128 ≤ 8192 := by
  have := slot_bound i; have : ACC = 3584 := rfl; omega

theorem slot_sep64 {i j : Index} (h : i ≠ j) : slot i.val + 64 ≤ slot j.val ∨ slot j.val + 64 ≤ slot i.val := by
  have := slot_sep h; omega

/-- Byte frame of an operation writing slot `o`'s first 64 bytes and the coefficient area. -/
theorem fieldMem_same {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    VG.Proof.X448.AArch64.Fast.Same base [o] m m' := by
  intro i hi j hj
  have hne : i ≠ o := fun e => hi (by simp [e])
  exact h.limbs (slot_sep hne) (slot_bound i) (by omega : j < 16)

theorem fieldMem_outside2 {base : Addr} {o : Index} {m m' : Mem} (h : FieldMem base (slot o.val) m m') :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp hq
  apply h p _ (hq.imp_right fun h => Nat.le_trans (Nat.add_le_add_left (by decide : 512 ≤ 1152) _) h)
  have := o.isLt
  simp only [slot]
  omega

theorem slot_inj {i j : Index} (h : slot i.val = slot j.val) : i = j := by
  apply Fin.ext; simp only [slot] at h; omega

theorem env_update {base : Addr} {s t : State} {o : Index} (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    (hm : FieldMem base (slot o.val) s.mem t.mem) (ho : VG.Proof.X448.AArch64.Fast.Bnd Ib t.mem base (slot o.val)) :
    VG.Proof.X448.AArch64.Fast.BEnv t.mem base := by
  intro i
  by_cases h : i = o
  · subst h; exact ho
  · exact (VG.Proof.X448.AArch64.Fast.fieldMem_same hm).bnd (by simp [h]) (hb i)

theorem fmulE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b) :
    WP isa (.block (Impl.X448.AArch64.Fast.fmul (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot o.val) ∧
      VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
  have post : ∀ t : State, (∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val)) i) → FieldMem base (slot o.val) s.mem t.mem → Keeps VG.Proof.X448.AArch64.Fast.fclob s t →
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot o.val) ∧
      VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧ VG.Proof.X448.AArch64.Weak.E t.mem base = opMul o a b (VG.Proof.X448.AArch64.Weak.E s.mem base) := by
    intro t tv tm tk
    have bo : VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot o.val) := fun i hi => by
      rw [tv i hi]; exact VG.Proof.Curve448.AArch64.Fast.prod_bound (hb a) (hb b) i hi
    refine ⟨⟨tk, VG.Proof.X448.AArch64.Fast.fieldMem_outside2 tm⟩, VG.Proof.X448.AArch64.Fast.env_update hb tm (fun i hi =>
      Nat.lt_of_lt_of_le (bo i hi) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib), bo, VG.Proof.X448.AArch64.Fast.fieldMem_same tm, ?_⟩
    rw [VG.Proof.X448.AArch64.Weak.E_update tm]
    simp only [opMul]
    refine congrArg (Function.update _ o) ?_
    change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ * VG.Proof.X448.toFe _
    rw [show VG.Proof.X448.Wide.valN (limbs t.mem base (slot o.val)) 8 =
      VG.Proof.X448.Wide.valN (VG.Proof.Curve448.AArch64.Fast.prodOut (limbs s.mem base (slot a.val))
        (limbs s.mem base (slot b.val))) 8 from VG.Proof.X448.Wide.valN_congr tv]
    exact VG.Proof.Curve448.AArch64.Fast.prod_val _ _
  simp only [Impl.X448.AArch64.Fast.fmul]
  split
  · rename_i h
    have hab := VG.Proof.X448.AArch64.Fast.slot_inj h
    subst hab
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.sqr_ok hs (VG.Proof.X448.AArch64.Fast.slot_64 o) (slot_aligned o) (VG.Proof.X448.AArch64.Fast.slot_64 a)
      (slot_aligned a) (hb a)) fun t ⟨tv, tm, tk⟩ => post t tv tm tk
  · rename_i h
    have hob' : o ≠ b := hob.resolve_left fun e => h (e ▸ rfl)
    exact WP.mono (VG.Proof.Curve448.AArch64.Fast.mul_ok hs (VG.Proof.X448.AArch64.Fast.slot_64 o) (slot_aligned o) (VG.Proof.X448.AArch64.Fast.slot_64 a)
      (slot_aligned a) (VG.Proof.X448.AArch64.Fast.slot_64 b) (slot_aligned b) (VG.Proof.X448.AArch64.Fast.slot_sep64 hob') (hb a) (hb b))
      fun t ⟨tv, tm, tk⟩ => post t tv tm tk

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

open VG.Proof.Curve448.AArch64.Fast (Away)

theorem away_same {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) : VG.Proof.X448.AArch64.Fast.Same base os m m' := by
  intro i hi j hj
  change (word m' base (slot i.val + 8 * j)).toNat = (word m base (slot i.val + 8 * j)).toNat
  rw [VG.Proof.Curve448.AArch64.Fast.away_word h (by have := VG.Proof.X448.AArch64.Fast.slot_mem i; omega) (fun o ho => by
    simp only [List.mem_map] at ho
    obtain ⟨k, hk, rfl⟩ := ho
    have := slot_sep (show i ≠ k from fun e => hi (e ▸ hk))
    omega)]

theorem away_outside2 {base : Addr} {os : List Index} {m m' : Mem}
    (h : ∀ x, Away base (os.map fun i => slot i.val) 64 x → m' x = m x) :
    Outside2 base 64 2816 ACC 1152 m m' := by
  intro p hp _
  apply h p
  intro o ho
  simp only [List.mem_map] at ho
  obtain ⟨k, -, rfl⟩ := ho
  have := k.isLt
  simp only [slot]
  omega

theorem away_fieldMem {base : Addr} {o : Index} {m m' : Mem}
    (h : ∀ x, Away base [slot o.val] 64 x → m' x = m x) : FieldMem base (slot o.val) m m' :=
  fun x hx _ => h x fun o' ho' => by simp at ho'; subst ho'; omega

theorem bnd_word {m : Mem} {base : Addr} {n : Nat} {o : Nat} (h : VG.Proof.X448.AArch64.Fast.Bnd n m base o) {i : Nat} (hi : i < 8) :
    (word m base (o + 8 * i)).toNat < n := h i hi

theorem subE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) {o a b : Index}
    (ha : VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot a.val)) (hb' : VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧ EV t.mem base = opSub o a b (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.sub_ok hs (by have := VG.Proof.X448.AArch64.Fast.slot_mem o; omega)
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem a; omega) (by have := VG.Proof.X448.AArch64.Fast.slot_mem b; omega) (slot_aligned o) (slot_aligned a)
    (slot_aligned b) (VG.Proof.X448.AArch64.Fast.slot_sep64 hoa) (VG.Proof.X448.AArch64.Fast.slot_sep64 hob)) fun t ⟨tv, tm, tk⟩ => ?_
  have tl : ∀ i < 8, limbs t.mem base (slot o.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i := by
    intro i hi
    change (word t.mem base (slot o.val + 8 * i)).toNat = _
    rw [tv i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have fm := VG.Proof.X448.AArch64.Fast.away_fieldMem tm
  refine ⟨⟨tk.mono (by decide), VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩, VG.Proof.X448.AArch64.Fast.env_update hb fm (fun i hi => by
    rw [tl i hi]; exact VG.Proof.Curve448.AArch64.Fast.diff_bound ha i hi), VG.Proof.X448.AArch64.Fast.fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  simp only [opSub]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.toFe _ = VG.Proof.X448.toFe _ - VG.Proof.X448.toFe _
  rw [VG.Proof.X448.Wide.valN_congr tl]
  exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'

theorem bnd_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat} {n : Nat}
    (h : ∀ i < 8, limbs m base o i = f i) (hf : ∀ i < 8, f i < n) : VG.Proof.X448.AArch64.Fast.Bnd n m base o :=
  fun i hi => by rw [h i hi]; exact hf i hi

theorem fe_of_limbs {m : Mem} {base : Addr} {o : Nat} {f : Nat → Nat}
    (h : ∀ i < 8, limbs m base o i = f i) :
    VG.Proof.X448.AArch64.Weak.F m base o = VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN f 8) :=
  congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr h)

theorem addSubE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) {o₁ o₂ a b : Index}
    (ha : VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot a.val)) (hb' : VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot b.val)) (h12 : o₁ ≠ o₂)
    (h1a : o₁ ≠ a) (h1b : o₁ ≠ b) (h2a : o₂ ≠ a) (h2b : o₂ ≠ b) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.addSub (slot o₁.val) (slot o₂.val) (slot a.val)
        (slot b.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Same base [o₁, o₂] s.mem t.mem ∧
      EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a + EV s.mem base b))
        o₂ (EV s.mem base a - EV s.mem base b) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.addSub_ok hs (by have := VG.Proof.X448.AArch64.Fast.slot_mem o₁; omega)
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem o₂; omega) (by have := VG.Proof.X448.AArch64.Fast.slot_mem a; omega) (by have := VG.Proof.X448.AArch64.Fast.slot_mem b; omega)
    (slot_aligned o₁) (slot_aligned o₂) (slot_aligned a) (slot_aligned b) (VG.Proof.X448.AArch64.Fast.slot_sep64 h12)
    (VG.Proof.X448.AArch64.Fast.slot_sep64 h1a) (VG.Proof.X448.AArch64.Fast.slot_sep64 h1b) (VG.Proof.X448.AArch64.Fast.slot_sep64 h2a) (VG.Proof.X448.AArch64.Fast.slot_sep64 h2b)) fun t ⟨t1, t2, tm, tk⟩ => ?_
  have l1 : ∀ i < 8, limbs t.mem base (slot o₁.val) i =
      limbs s.mem base (slot a.val) i + limbs s.mem base (slot b.val) i := fun i hi => by
    change (word t.mem base (slot o₁.val + 8 * i)).toNat = _
    rw [t1 i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (ha i hi) (hb' i hi)]
  have l2 : ∀ i < 8, limbs t.mem base (slot o₂.val) i =
      VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot a.val)) (limbs s.mem base (slot b.val)) i :=
    fun i hi => by
      change (word t.mem base (slot o₂.val + 8 * i)).toNat = _
      rw [t2 i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (ha i hi) (hb' i hi)]; rfl
  have sm : VG.Proof.X448.AArch64.Fast.Same base [o₁, o₂] s.mem t.mem := VG.Proof.X448.AArch64.Fast.away_same (os := [o₁, o₂]) tm
  refine ⟨⟨tk.mono (by decide), VG.Proof.X448.AArch64.Fast.away_outside2 (os := [o₁, o₂]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e1 : i = o₁
    · subst e1; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs l1 (VG.Proof.Curve448.AArch64.Fast.sum_bound ha hb')
    · by_cases e2 : i = o₂
      · subst e2; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs l2 (VG.Proof.Curve448.AArch64.Fast.diff_bound ha)
      · exact sm.bnd (by simp [e1, e2]) (hb i)
  · funext i
    simp only [Function.update_apply]
    by_cases e2 : i = o₂
    · subst e2
      rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
      rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs l2]
      exact VG.Proof.Curve448.AArch64.Fast.diff_val hb'
    · rw [ite_eq_right e2]
      by_cases e1 : i = o₁
      · subst e1
        rw [ite_eq_left rfl]
        change VG.Proof.X448.AArch64.Weak.F t.mem base (slot i.val) = _
        rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs l1]
        exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
      · rw [ite_eq_right e1]; exact sm.env (by simp [e1, e2])

theorem smallE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) {o a e : Index}
    (ha : VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot a.val)) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.small (slot o.val) (slot a.val) (slot e.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a + Spec.X448.a24 * EV s.mem base e) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.small_ok hs (by have := VG.Proof.X448.AArch64.Fast.slot_mem o; omega)
    (by have := VG.Proof.X448.AArch64.Fast.slot_mem a; omega) (by have := VG.Proof.X448.AArch64.Fast.slot_mem e; omega) (slot_aligned o) (slot_aligned a)
    (slot_aligned e) ha (hb e)) fun t ⟨tv, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output (tm.mono (Nat.le_refl _) (by omega))
  refine ⟨⟨tk.mono (by decide), VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩, VG.Proof.X448.AArch64.Fast.env_update hb fm
    (VG.Proof.X448.AArch64.Fast.bnd_of_limbs tv (VG.Proof.Curve448.AArch64.Fast.small_bound ha (hb e))), VG.Proof.X448.AArch64.Fast.fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm]
  refine congrArg (Function.update _ o) ?_
  change VG.Proof.X448.AArch64.Weak.F t.mem base (slot o.val) = _
  rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs tv]
  exact VG.Proof.Curve448.AArch64.Fast.smallF _ _

/-- Slot `i` of the swapped coordinates (`x₂, z₂, x₃, z₃` are slots 1–4). -/
def swp (sw : Bool) (i : Index) : Index := if sw then (if i = 1 then 3 else if i = 3 then 1 else
  if i = 2 then 4 else if i = 4 then 2 else i) else i

/-- The butterfly's result on the field slots. -/
def bflyEnv (sw : Bool) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := fun i =>
  if i = 5 then e (VG.Proof.X448.AArch64.Fast.swp sw 1) + e (VG.Proof.X448.AArch64.Fast.swp sw 2) else if i = 6 then e (VG.Proof.X448.AArch64.Fast.swp sw 1) - e (VG.Proof.X448.AArch64.Fast.swp sw 2)
  else if i = 7 then e (VG.Proof.X448.AArch64.Fast.swp sw 3) + e (VG.Proof.X448.AArch64.Fast.swp sw 4) else if i = 8 then e (VG.Proof.X448.AArch64.Fast.swp sw 3) - e (VG.Proof.X448.AArch64.Fast.swp sw 4)
  else e i

theorem sel_slot (m : Mem) (base : Addr) (sw : Bool) (p q : Index) (i : Nat) :
    VG.Proof.Curve448.AArch64.Fast.sel sw (word m base (slot p.val + 8 * i)) (word m base (slot q.val + 8 * i)) =
      word m base (slot (if sw then q else p).val + 8 * i) := by
  cases sw <;> rfl

theorem bflyE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    (hM : ∀ i : Index, i.val ∈ [1, 2, 3, 4] → VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot i.val))
    {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.Fast.butterfly X2 Z2 X3 Z3 A B C D)) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Same base [5, 6, 7, 8] s.mem t.mem ∧
      EV t.mem base = VG.Proof.X448.AArch64.Fast.bflyEnv sw (EV s.mem base) := by
  have hX2 : X2 = slot (1 : Index).val := rfl
  have hZ2 : Z2 = slot (2 : Index).val := rfl
  have hX3 : X3 = slot (3 : Index).val := rfl
  have hZ3 : Z3 = slot (4 : Index).val := rfl
  have hA : A = slot (5 : Index).val := rfl
  have hB : B = slot (6 : Index).val := rfl
  have hC : C = slot (7 : Index).val := rfl
  have hD : D = slot (8 : Index).val := rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Fast.butterfly_ok hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hm) fun t ⟨tv, tm, tk⟩ => ?_
  have sw1 : ∀ p q : Index, p.val ∈ [1, 2, 3, 4] → q.val ∈ [1, 2, 3, 4] →
      VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot (if sw then q else p).val) := fun p q hp hq => by
    cases sw
    · exact hM p hp
    · exact hM q hq
  have val : ∀ (o : Nat) (k : Index) (p q : Index), o = slot k.val →
      (∀ i < 8, word t.mem base (o + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        word s.mem base (slot q.val + 8 * i)) → VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot p.val) → VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i = limbs s.mem base (slot p.val) i + limbs s.mem base (slot q.val) i) :=
    fun o k p q ho h hp hq i hi => by
      subst ho
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.sum_word _ _ (hp i hi) (hq i hi)]
  have dif : ∀ (k : Index) (p q : Index),
      (∀ i < 8, word t.mem base (slot k.val + 8 * i) = word s.mem base (slot p.val + 8 * i) +
        VG.Proof.Curve448.AArch64.Fast.twoPW i - word s.mem base (slot q.val + 8 * i)) →
      VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot p.val) → VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot q.val) →
      (∀ i < 8, limbs t.mem base (slot k.val) i =
        VG.Proof.Curve448.AArch64.Fast.diffN (limbs s.mem base (slot p.val)) (limbs s.mem base (slot q.val)) i) :=
    fun k p q h hp hq i hi => by
      change (word t.mem base (slot k.val + 8 * i)).toNat = _
      rw [h i hi, VG.Proof.Curve448.AArch64.Fast.diff_word _ _ i (hp i hi) (hq i hi)]; rfl
  let x2 := VG.Proof.X448.AArch64.Fast.swp sw 1; let z2 := VG.Proof.X448.AArch64.Fast.swp sw 2; let x3 := VG.Proof.X448.AArch64.Fast.swp sw 3; let z3 := VG.Proof.X448.AArch64.Fast.swp sw 4
  have ex2 : (if sw then (3 : Index) else 1) = x2 := by cases sw <;> rfl
  have ez2 : (if sw then (4 : Index) else 2) = z2 := by cases sw <;> rfl
  have ex3 : (if sw then (1 : Index) else 3) = x3 := by cases sw <;> rfl
  have ez3 : (if sw then (2 : Index) else 4) = z3 := by cases sw <;> rfl
  have mx2 := sw1 1 3 (by decide) (by decide); rw [ex2] at mx2
  have mz2 := sw1 2 4 (by decide) (by decide); rw [ez2] at mz2
  have mx3 := sw1 3 1 (by decide) (by decide); rw [ex3] at mx3
  have mz3 := sw1 4 2 (by decide) (by decide); rw [ez3] at mz3
  have wA : ∀ i < 8, word t.mem base (slot (5 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hA, tv A (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, ite_true, hX2, hX3, hZ2, hZ3, VG.Proof.X448.AArch64.Fast.sel_slot, ex2, ez2]
  have wB : ∀ i < 8, word t.mem base (slot (6 : Index).val + 8 * i) =
      word s.mem base (slot x2.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z2.val + 8 * i) := fun i hi => by
    rw [← hB, tv B (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show B ≠ A by decide, ite_true, ite_false, hX2, hX3,
      hZ2, hZ3, VG.Proof.X448.AArch64.Fast.sel_slot, ex2, ez2]
  have wC : ∀ i < 8, word t.mem base (slot (7 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hC, tv C (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show C ≠ A by decide, show C ≠ B by decide, ite_true,
      ite_false, hX2, hX3, hZ2, hZ3, VG.Proof.X448.AArch64.Fast.sel_slot, ex3, ez3]
  have wD : ∀ i < 8, word t.mem base (slot (8 : Index).val + 8 * i) =
      word s.mem base (slot x3.val + 8 * i) + VG.Proof.Curve448.AArch64.Fast.twoPW i -
        word s.mem base (slot z3.val + 8 * i) := fun i hi => by
    rw [← hD, tv D (by simp) i hi]
    simp only [VG.Proof.Curve448.AArch64.Fast.bflyV, show D ≠ A by decide, show D ≠ B by decide,
      show D ≠ C by decide, ite_false, hX2, hX3, hZ2, hZ3, VG.Proof.X448.AArch64.Fast.sel_slot, ex3, ez3]
  have lA := val _ 5 x2 z2 rfl wA mx2 mz2
  have lB := dif 6 x2 z2 wB mx2 mz2
  have lC := val _ 7 x3 z3 rfl wC mx3 mz3
  have lD := dif 8 x3 z3 wD mx3 mz3
  have sm : VG.Proof.X448.AArch64.Fast.Same base [5, 6, 7, 8] s.mem t.mem := VG.Proof.X448.AArch64.Fast.away_same (os := [5, 6, 7, 8]) tm
  refine ⟨⟨tk.mono (by decide), VG.Proof.X448.AArch64.Fast.away_outside2 (os := [5, 6, 7, 8]) tm⟩, fun i => ?_, sm, ?_⟩
  · by_cases e5 : i = 5
    · subst e5; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs lA (VG.Proof.Curve448.AArch64.Fast.sum_bound mx2 mz2)
    by_cases e6 : i = 6
    · subst e6; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs lB (VG.Proof.Curve448.AArch64.Fast.diff_bound mx2)
    by_cases e7 : i = 7
    · subst e7; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs lC (VG.Proof.Curve448.AArch64.Fast.sum_bound mx3 mz3)
    by_cases e8 : i = 8
    · subst e8; exact VG.Proof.X448.AArch64.Fast.bnd_of_limbs lD (VG.Proof.Curve448.AArch64.Fast.diff_bound mx3)
    exact sm.bnd (by simp [e5, e6, e7, e8]) (hb i)
  · funext i
    simp only [VG.Proof.X448.AArch64.Fast.bflyEnv]
    by_cases e5 : i = 5
    · subst e5; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((5 : Index) : Nat)) = _
      rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs lA]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e5]
    by_cases e6 : i = 6
    · subst e6; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((6 : Index) : Nat)) = _
      rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs lB]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz2
    rw [ite_eq_right e6]
    by_cases e7 : i = 7
    · subst e7; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((7 : Index) : Nat)) = _
      rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs lC]; exact VG.Proof.Curve448.AArch64.Fast.sum_val _ _
    rw [ite_eq_right e7]
    by_cases e8 : i = 8
    · subst e8; rw [ite_eq_left rfl]
      change VG.Proof.X448.AArch64.Weak.F t.mem base (slot ((8 : Index) : Nat)) = _
      rw [VG.Proof.X448.AArch64.Fast.fe_of_limbs lD]; exact VG.Proof.Curve448.AArch64.Fast.diff_val mz3
    rw [ite_eq_right e8]
    exact sm.env (by simp [e5, e6, e7, e8])

theorem copyE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) (o a : Index) :
    WP isa (.block (Impl.Curve448.AArch64.copy (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ (∀ j < 8, limbs t.mem base (slot o.val) j = limbs s.mem base (slot a.val) j) ∧
      VG.Proof.X448.AArch64.Fast.Same base [o] s.mem t.mem ∧ EV t.mem base = opCopy o a (EV s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 128 ≤ slot a.val ∨ slot a.val + 128 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (slot_sep h)
  refine WP.mono (VG.Proof.Curve448.AArch64.copy_ok hs (VG.Proof.X448.AArch64.Fast.slot_mem o) (VG.Proof.X448.AArch64.Fast.slot_mem a) (slot_aligned o)
    (slot_aligned a) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have fm : FieldMem base (slot o.val) s.mem t.mem := VG.Proof.X448.AArch64.FieldMem.output tm
  refine ⟨⟨tk.mono (by decide), VG.Proof.X448.AArch64.Fast.fieldMem_outside2 fm⟩, VG.Proof.X448.AArch64.Fast.env_update hb fm (fun i hi => by
    rw [tf i hi]; exact hb a i hi), tf, VG.Proof.X448.AArch64.Fast.fieldMem_same fm, ?_⟩
  rw [VG.Proof.X448.AArch64.Weak.E_update fm, opCopy]
  refine congrArg (Function.update _ o) ?_
  exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr tf)

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.NeonEnv`. -/
section

/-!
# X448 on AArch64: two products in AdvSIMD, on slots

Untrusted: everything here is checked by Lean. `mul2` updates two slots as
two field operations would, and writes nothing but the two slots and the
vector working space, which `FKeep` allows.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs ofs ofs_off)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.Curve448.AArch64.Neon (NA mul2)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem mul2_word {m m' : Mem} {base : Addr} {o₁ o₂ : Nat}
    (hF : ∀ x, (ofs base x < o₁ ∨ o₁ + 64 ≤ ofs base x) → (ofs base x < o₂ ∨ o₂ + 64 ≤ ofs base x) →
      (ofs base x < NA ∨ NA + 640 ≤ ofs base x) → m' x = m x) {d : Nat}
    (h1 : d + 8 ≤ o₁ ∨ o₁ + 64 ≤ d) (h2 : d + 8 ≤ o₂ ∨ o₂ + 64 ≤ d) (h3 : d + 8 ≤ NA) :
    word m' base d = word m base d := by
  have hNA : NA = 4096 := rfl
  exact (Mem.readW_congr fun i hi => (hF _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega) (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem slot_neon (i : Index) : slot i.val % 16 = 0 ∧ slot i.val + 64 ≤ NA := by
  have := i.isLt; have hNA : NA = 4096 := rfl; simp only [slot]; omega

theorem mul2E {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) (o₁ a₁ b₁ o₂ a₂ b₂ : Index)
    (h12 : o₁ ≠ o₂) :
    WP isa (.block (mul2 (slot o₁.val) (slot a₁.val) (slot b₁.val) (slot o₂.val) (slot a₂.val) (slot b₂.val))) s
      fun t => VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot o₁.val) ∧
        VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot o₂.val) ∧ VG.Proof.X448.AArch64.Fast.Same base [o₁, o₂] s.mem t.mem ∧
        EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a₁ * EV s.mem base b₁))
          o₂ (EV s.mem base a₂ * EV s.mem base b₂) := by
  have hNA : NA = 4096 := rfl
  have hACC : ACC = 3584 := rfl
  refine WP.mono (VG.Proof.Curve448.AArch64.Neon.mul2_ok hs (VG.Proof.X448.AArch64.Fast.slot_neon a₁) (VG.Proof.X448.AArch64.Fast.slot_neon b₁) (VG.Proof.X448.AArch64.Fast.slot_neon a₂)
    (VG.Proof.X448.AArch64.Fast.slot_neon b₂) (VG.Proof.X448.AArch64.Fast.slot_neon o₁) (VG.Proof.X448.AArch64.Fast.slot_neon o₂) (VG.Proof.X448.AArch64.Fast.slot_sep64 h12) (hb a₁) (hb b₁) (hb a₂) (hb b₂))
    fun t ⟨m1, m2, v1, v2, fr, g, r, w⟩ => ?_
  have same : VG.Proof.X448.AArch64.Fast.Same base [o₁, o₂] s.mem t.mem := fun i hi j hj => by
    have n1 : i ≠ o₁ := fun e => hi (by simp [e])
    have n2 : i ≠ o₂ := fun e => hi (by simp [e])
    have := VG.Proof.X448.AArch64.Fast.slot_sep64 n1; have := VG.Proof.X448.AArch64.Fast.slot_sep64 n2; have := (VG.Proof.X448.AArch64.Fast.slot_neon i).2
    exact congrArg BitVec.toNat (VG.Proof.X448.AArch64.Fast.mul2_word fr (by omega) (by omega) (by omega))
  refine ⟨⟨⟨fun r _ => congrFun g r, r, w⟩, fun p hp hq => fr p ?_ ?_ ?_⟩, fun i => ?_, m1, m2, same, ?_⟩
  · have := o₁.isLt; simp only [slot]; omega
  · have := o₂.isLt; simp only [slot]; omega
  · omega
  · by_cases e1 : i = o₁
    · subst e1; exact fun j hj => Nat.lt_of_lt_of_le (m1 j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib
    by_cases e2 : i = o₂
    · subst e2; exact fun j hj => Nat.lt_of_lt_of_le (m2 j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib
    exact same.bnd (by simp [e1, e2]) (hb i)
  · funext i
    simp only [Function.update_apply]
    by_cases e2 : i = o₂
    · rw [ite_eq_left e2]; subst e2; exact v2
    rw [ite_eq_right e2]
    by_cases e1 : i = o₁
    · rw [ite_eq_left e1]; subst e1; exact v1
    rw [ite_eq_right e1]
    exact same.env (by simp [e1, e2])

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.StepOps`. -/
section

/-!
# X448 on AArch64: the field operations of a ladder step

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot)
open VG.Proof.X448.AArch64.Weak (Index Env opMul)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The slots after the step's operations (slots as in `Impl/X448/AArch64/Common.lean`), in the
order `Impl/X448/AArch64/Fast.lean` computes them. -/
def stepOpsEnv (e : Env) : Env :=
  let e := Function.update e 9 (e 5 * e 5)
  let e := Function.update e 10 (e 6 * e 6)
  let e := Function.update e 1 (e 9 * e 10)
  let e := Function.update e 11 (e 9 - e 10)
  let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
  let e := Function.update (Function.update e 12 (e 8 * e 5)) 13 (e 7 * e 6)
  let e := Function.update (Function.update e 14 (e 12 + e 13)) 15 (e 12 - e 13)
  let e := Function.update e 15 (e 15 * e 15)
  let e := Function.update e 4 (e 0 * e 15)
  Function.update (Function.update e 2 (e 11 * e 16)) 3 (e 14 * e 14)

/-- What the step's operations keep. -/
def Post (base : Addr) (s t : State) : Prop :=
  FKeep base s t ∧ BEnv t.mem base

theorem Same.append {base : Addr} {l₁ l₂ : List Index} {m₁ m₂ m₃ : Mem} (h : Same base l₁ m₁ m₂)
    (h' : Same base l₂ m₂ m₃) : Same base (l₁ ++ l₂) m₁ m₃ := fun i hi j hj => by
  rw [h' i (fun e => hi (List.mem_append_right _ e)) j hj, h i (fun e => hi (List.mem_append_left _ e)) j hj]

theorem mulOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) (o a b : Index)
    (hob : a = b ∨ o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Bnd Mb t.mem base (slot o.val) →
      Same base [o] s.mem t.mem → EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a * EV s.mem base b) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.mul (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q := by
  refine WP.seq (WP.mono (fmulE hs hb o a b hob) fun t ⟨tk, tb, tm, ts, te⟩ => h t tk tb tm ts ?_)
  rw [te]; rfl

theorem addSubOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o₁ o₂ a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (h12 : o₁ ≠ o₂)
    (h1a : o₁ ≠ a) (h1b : o₁ ≠ b) (h2a : o₂ ≠ a) (h2b : o₂ ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o₁, o₂] s.mem t.mem →
      EV t.mem base = Function.update (Function.update (EV s.mem base) o₁ (EV s.mem base a + EV s.mem base b))
        o₂ (EV s.mem base a - EV s.mem base b) → WP isa (ops rest) t Q) :
    WP isa (ops (.addSub (slot o₁.val) (slot o₂.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (addSubE hs hb ha hb' h12 h1a h1b h2a h2b) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem subOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a b : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) (hb' : Bnd Mb s.mem base (slot b.val)) (hoa : o ≠ a) (hob : o ≠ b)
    {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a - EV s.mem base b) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.sub (slot o.val) (slot a.val) (slot b.val) :: rest)) s Q :=
  WP.seq (WP.mono (subE hs hb ha hb' hoa hob) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem smallOp {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) {o a e : Index}
    (ha : Bnd Mb s.mem base (slot a.val)) {rest : List Impl.X448.AArch64.Fast.Op} {Q : State → Prop}
    (h : ∀ t, FKeep base s t → BEnv t.mem base → Same base [o] s.mem t.mem →
      EV t.mem base = Function.update (EV s.mem base) o (EV s.mem base a + Spec.X448.a24 * EV s.mem base e) →
      WP isa (ops rest) t Q) :
    WP isa (ops (.small (slot o.val) (slot a.val) (slot e.val) :: rest)) s Q :=
  WP.seq (WP.mono (smallE hs hb ha) fun t ⟨tk, tb, ts, te⟩ => h t tk tb ts te)

theorem ops_append (l₁ l₂ : List Impl.X448.AArch64.Fast.Op) {s : State} {Q : State → Prop}
    (h : WP isa (ops l₁) s fun t => WP isa (ops l₂) t Q) : WP isa (ops (l₁ ++ l₂)) s Q := by
  induction l₁ generalizing s with
  | nil => exact (WP.block_nil_iff.mp h)
  | cons o os ih =>
    rw [ops, WP.seq_iff] at h
    exact WP.seq (WP.mono h fun t ht => ih ht)

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Weave`. -/
section

/-!
# X448 on AArch64: interleaved code

Untrusted: everything here is checked by Lean. `weave a b` is a merge of
`a` and `b`, so for independent blocks it runs as `a` and then `b`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.AArch64.Interleave
open VG.Impl.X448.AArch64.Fast (weave weaveGo codeOf ops)

theorem weaveGo_merge (n m : Nat) : ∀ f i j (a b : List Instr), Merge (weaveGo n m f i j a b) a b
  | 0, _, _, a, b => Merge.append a b
  | _ + 1, _, _, [], b => Merge.nil_left b
  | _ + 1, _, _, x :: a, [] => Merge.nil_right (x :: a)
  | f + 1, i, j, x :: a, y :: b => by
    rw [weaveGo]
    split
    · exact .left (VG.Proof.X448.AArch64.Fast.weaveGo_merge n m f _ _ _ _)
    · exact .right (VG.Proof.X448.AArch64.Fast.weaveGo_merge n m f _ _ _ _)

theorem weave_merge (a b : List Instr) : Merge (VG.Impl.X448.AArch64.Fast.weave a b) a b := VG.Proof.X448.AArch64.Fast.weaveGo_merge _ _ _ _ _ _ _

/-- Independent blocks, interleaved, run as the first and then the second. -/
theorem WP.weave {a b : List Instr}
    (hind : ((blockFp a).bind fun A => (blockFp b).map fun B => A.indep B) = some true) {s : State}
    {Q : State → Prop} (h : WP isa (.block a) s fun t => WP isa (.block b) t Q) : WP isa (.block (VG.Impl.X448.AArch64.Fast.weave a b)) s Q :=
  WP.merge (VG.Proof.X448.AArch64.Fast.weave_merge a b) (indeps_of_check hind) (WP.block_append_iff.mpr h)

theorem block_codeOf {l : List Impl.X448.AArch64.Fast.Op} {s : State} {Q : State → Prop}
    (h : WP isa (ops l) s Q) : WP isa (.block (codeOf l)) s Q := by
  induction l generalizing s with
  | nil => exact h
  | cons o os ih =>
    rw [ops, WP.seq_iff] at h
    exact WP.block_append_iff.mpr (WP.mono h fun t ht => ih ht)

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Phases`. -/
section

/-!
# X448 on AArch64: the ladder step's field operations

Untrusted: everything here is checked by Lean. Each half of the step runs
two products in AdvSIMD interleaved with scalar operations; the two streams
are independent (checked by evaluating their footprints), so they run as the
scalar operations and then the vector products.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64 (Scr)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Impl.X448.AArch64.Fast (ops codeOf weave stepA stepB)
open VG.Impl.Curve448.AArch64.Neon (mul2)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- The scalar half of `stepA`. -/
theorem opsA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [9, 10, 1, 11, 16] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (1 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 9 (e 5 * e 5)
        let e := Function.update e 10 (e 6 * e 6)
        let e := Function.update e 1 (e 9 * e 10)
        let e := Function.update e 11 (e 9 - e 10)
        Function.update e 16 (e 9 + Spec.X448.a24 * e 11) := by
  refine mulOp hs hb 9 5 5 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  have hs1 := k1.scr hs
  refine mulOp hs1 b1 10 6 6 (by decide) fun t2 k2 b2 m2 s2 e2 => ?_
  have hs2 := k2.scr hs1
  have m9 : Bnd Mb t2.mem base (slot (9 : Index).val) := s2.bnd (by decide) m1
  refine mulOp hs2 b2 1 9 10 (by decide) fun t3 k3 b3 m3 s3 e3 => ?_
  have hs3 := k3.scr hs2
  refine subOp (o := 11) (a := 9) (b := 10) hs3 b3 (s3.bnd (by decide) m9) (s3.bnd (by decide) m2)
    (by decide) (by decide) fun t4 k4 b4 s4 e4 => ?_
  have hs4 := k4.scr hs3
  refine smallOp (o := 16) (a := 9) (e := 11) hs4 b4 (s4.bnd (by decide) (s3.bnd (by decide) m9))
    fun t5 k5 b5 s5 e5 => ?_
  refine WP.block_nil ⟨k1.trans (k2.trans (k3.trans (k4.trans k5))), b5,
    (((s1.append s2).append s3).append s4).append s5, s5.bnd (by decide) (s4.bnd (by decide) m3), ?_⟩
  rw [e5, e4, e3, e2, e1]

theorem stepA_eq : stepA = weave (codeOf [.mul (slot (9 : Index).val) (slot (5 : Index).val) (slot (5 : Index).val),
      .mul (slot (10 : Index).val) (slot (6 : Index).val) (slot (6 : Index).val),
      .mul (slot (1 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .sub (slot (11 : Index).val) (slot (9 : Index).val) (slot (10 : Index).val),
      .small (slot (16 : Index).val) (slot (9 : Index).val) (slot (11 : Index).val)])
    (mul2 (slot (12 : Index).val) (slot (8 : Index).val) (slot (5 : Index).val) (slot (13 : Index).val)
      (slot (7 : Index).val) (slot (6 : Index).val)) := rfl

theorem stepA_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block stepA) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([9, 10, 1, 11, 16] ++ [12, 13]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (1 : Index).val) ∧ Bnd Mb t.mem base (slot (12 : Index).val) ∧
      Bnd Mb t.mem base (slot (13 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 9 (e 5 * e 5)
        let e := Function.update e 10 (e 6 * e 6)
        let e := Function.update e 1 (e 9 * e 10)
        let e := Function.update e 11 (e 9 - e 10)
        let e := Function.update e 16 (e 9 + Spec.X448.a24 * e 11)
        Function.update (Function.update e 12 (e 8 * e 5)) 13 (e 7 * e 6) := by
  rw [stepA_eq]
  refine WP.weave (by decide +kernel) (WP.mono (block_codeOf (opsA_ok hs hb)) fun t ⟨tk, tb, ts, t1, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 12 8 5 13 7 6 (by decide)) fun u ⟨uk, ub, u12, u13, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, us.bnd (by decide) t1, u12, u13, ?_⟩
  rw [ue, te]

/-- The scalar half of `stepB`. -/
theorem opsB_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (ops [.mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val)]) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [15, 4] s.mem t.mem ∧
      Bnd Mb t.mem base (slot (4 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 15 (e 15 * e 15)
        Function.update e 4 (e 0 * e 15) := by
  refine mulOp hs hb 15 15 15 (by decide) fun t1 k1 b1 m1 s1 e1 => ?_
  refine mulOp (k1.scr hs) b1 4 0 15 (by decide) fun t2 k2 b2 m2 s2 e2 => ?_
  refine WP.block_nil ⟨k1.trans k2, b2, s1.append s2, m2, ?_⟩
  rw [e2, e1]

theorem stepB_eq : stepB = weave (codeOf [.mul (slot (15 : Index).val) (slot (15 : Index).val) (slot (15 : Index).val),
      .mul (slot (4 : Index).val) (slot (0 : Index).val) (slot (15 : Index).val)])
    (mul2 (slot (2 : Index).val) (slot (11 : Index).val) (slot (16 : Index).val) (slot (3 : Index).val)
      (slot (14 : Index).val) (slot (14 : Index).val)) := rfl

theorem stepB_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base) :
    WP isa (.block stepB) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base ([15, 4] ++ [2, 3]) s.mem t.mem ∧
      Bnd Mb t.mem base (slot (2 : Index).val) ∧ Bnd Mb t.mem base (slot (3 : Index).val) ∧
      Bnd Mb t.mem base (slot (4 : Index).val) ∧
      EV t.mem base =
        let e := EV s.mem base
        let e := Function.update e 15 (e 15 * e 15)
        let e := Function.update e 4 (e 0 * e 15)
        Function.update (Function.update e 2 (e 11 * e 16)) 3 (e 14 * e 14) := by
  rw [stepB_eq]
  refine WP.weave (by decide +kernel) (WP.mono (block_codeOf (opsB_ok hs hb)) fun t ⟨tk, tb, ts, t4, te⟩ => ?_)
  refine WP.mono (mul2E (tk.scr hs) tb 2 11 16 3 14 14 (by decide)) fun u ⟨uk, ub, u2, u3, us, ue⟩ =>
    ⟨tk.trans uk, ub, ts.append us, u2, u3, us.bnd (by decide) t4, ?_⟩
  rw [ue, te]

/-- The step's field operations, after `A, B, C, D`. -/
def stepOpsCode : Prog isa :=
  .seq (.block stepA) <| .seq (ops [.addSub (slot (14 : Index).val) (slot (15 : Index).val) (slot (12 : Index).val)
    (slot (13 : Index).val)]) (.block stepB)

theorem stepOps_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hX1 : Bnd Mb s.mem base (slot (0 : Index).val)) :
    WP isa stepOpsCode s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ (∀ i : Index, i.val ∈ [0, 1, 2, 3, 4] → Bnd Mb t.mem base (slot i.val)) ∧
      EV t.mem base = stepOpsEnv (EV s.mem base) := by
  refine WP.seq (WP.mono (stepA_ok hs hb) fun t ⟨tk, tb, ts, t1, t12, t13, te⟩ => ?_)
  have ht := tk.scr hs
  refine WP.seq (addSubOp (o₁ := 14) (o₂ := 15) (a := 12) (b := 13) ht tb t12 t13
    (by decide) (by decide) (by decide) (by decide) (by decide) fun u uk ub us ue => WP.block_nil ?_)
  refine WP.mono (stepB_ok (uk.scr ht) ub) fun v ⟨vk, vb, vs, v2, v3, v4, ve⟩ =>
    ⟨tk.trans (uk.trans vk), vb, fun i hi => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h
    · rw [show i = 0 from Fin.ext h]
      exact vs.bnd (by decide) (us.bnd (by decide) (ts.bnd (by decide) hX1))
    · rw [show i = 1 from Fin.ext h]; exact vs.bnd (by decide) (us.bnd (by decide) t1)
    · rw [show i = 2 from Fin.ext h]; exact v2
    · rw [show i = 3 from Fin.ext h]; exact v3
    · rw [show i = 4 from Fin.ext h]; exact v4
  · rw [ve, ue, te]; rfl

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Iter`. -/
section

/-!
# X448 on AArch64: the Montgomery ladder's iterations

Untrusted: everything here is checked by Lean. Each iteration consumes one
scalar bit and updates the five ladder slots according to `ladderStep`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask writeW_outside)
open VG.Proof.X448.AArch64.Weak (Index Env cswap_fst cswap_snd counter_zero ofs_off')
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (ladderAfter ladderStep_eq ladderAfter_step bit bit_le ladderAfter_swap_le)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def stepEnvF (sw : Bool) (e : VG.Proof.X448.AArch64.Env) : VG.Proof.X448.AArch64.Env := VG.Proof.X448.AArch64.Fast.stepOpsEnv (VG.Proof.X448.AArch64.Fast.bflyEnv sw e)

theorem stepEnvF_eval (e : VG.Proof.X448.AArch64.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.AArch64.Fast.stepEnvF (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.AArch64.Fast.stepEnvF (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.AArch64.Fast.stepEnvF (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.AArch64.Fast.stepEnvF (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.AArch64.Fast.stepEnvF (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [VG.Proof.X448.ladderStep_eq]
  cases hsw : decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)
  all_goals
    simp (config := {decide := true}) only [VG.Proof.X448.AArch64.Fast.stepEnvF, VG.Proof.X448.AArch64.Fast.stepOpsEnv, VG.Proof.X448.AArch64.Fast.bflyEnv, VG.Proof.X448.AArch64.Fast.swp, Function.update_apply,
      VG.Proof.X448.AArch64.Weak.cswap_fst, VG.Proof.X448.AArch64.Weak.cswap_snd, hsw, h0, h1, h2, h3, h4, ite_true, ite_false, Bool.false_eq_true]

/-- The ladder's loop invariant. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  env : VG.Proof.X448.AArch64.Fast.BEnv s.mem base
  red : ∀ i : Index, i.val ∈ [0, 1, 2, 3, 4] → VG.Proof.X448.AArch64.Fast.Bnd Mb s.mem base (slot i.val)
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.Fast.fclob) s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 n
  mem : Outside2 base 16 2864 ACC 1152 s₀.mem s.mem
  x1 : EV s.mem base 0 = u
  x2 : EV s.mem base 1 = (VG.Proof.X448.ladderAfter k u n).x2
  z2 : EV s.mem base 2 = (VG.Proof.X448.ladderAfter k u n).z2
  x3 : EV s.mem base 3 = (VG.Proof.X448.ladderAfter k u n).x3
  z3 : EV s.mem base 4 = (VG.Proof.X448.ladderAfter k u n).z3
  swap : word s.mem base SWAP = BitVec.ofNat 64 (VG.Proof.X448.ladderAfter k u n).swap

theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s (n + 1)) :
    WP isa Impl.X448.AArch64.Fast.step s fun t => VG.Proof.X448.AArch64.Fast.LInv base k u s₀ t n ∧ (t.gpr .x19 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [Impl.X448.AArch64.Fast.step, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.stepPre_ok hs hn hi.x19 (by have := VG.Proof.X448.bit_le k n; omega)
    (by have := VG.Proof.X448.ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.x3, (g₁ _ (by decide)).trans hs.mask, wr₁ ▸ hs.wr,
    hs.nowrap⟩
  have out₁ : Outside base SWAP 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : Index, ∀ j < 8, limbs s₁.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.AArch64.Weak.slot_bound i) (by decide)) (by omega)
  have same₁ : VG.Proof.X448.AArch64.Fast.Same base [] s.mem s₁.mem := fun i _ j hj => l₁ i j hj
  have e₁ : EV s₁.mem base = EV s.mem base := funext fun i => same₁.env (by simp)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.bflyE hs₁ (fun i => same₁.bnd (by simp) (hi.env i))
    (fun i hi' => same₁.bnd (by simp) (hi.red i (by simp at hi' ⊢; omega))) c₁) fun s₂ ⟨k₂, b₂, sm₂, e₂⟩ => ?_
  have hs₂ := k₂.scr hs₁
  have r₂ : VG.Proof.X448.AArch64.Fast.Bnd Mb s₂.mem base (slot (0 : Index).val) :=
    sm₂.bnd (by decide) (same₁.bnd (by simp) (hi.red 0 (by decide)))
  refine WP.mono (VG.Proof.X448.AArch64.Fast.stepOps_ok hs₂ b₂ r₂) fun s₃ ⟨k₃, b₃, r₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃' : s₃.gpr .x19 = BitVec.ofNat 64 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := VG.Proof.X448.AArch64.Fast.stepEnvF_eval (EV s.mem base) (VG.Proof.X448.ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : EV s₃.mem base = VG.Proof.X448.AArch64.Fast.stepEnvF (decide ((VG.Proof.X448.ladderAfter k u (n + 1)).swap ^^^ VG.Proof.X448.bit k n = 1))
      (EV s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← VG.Proof.X448.ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, b₃, r₃, ?_, b₃', ?_, vals.1, vals.2.1, vals.2.2.1, vals.2.2.2.1, vals.2.2.2.2, ?_⟩,
    VG.Proof.X448.AArch64.Weak.counter_zero (by omega) b₃'⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ VG.Proof.X448.AArch64.Fast.fclob := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.x19, .x4, .x5, .x6, .x11] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => hr (by subst r; decide), fun h => hwork (by subst r; decide),
        fun h => hwork (by subst r; decide), fun h => hwork (by subst r; decide),
        fun h => hwork (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, VG.Proof.X448.ladderAfter_step k u hn]
    exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Ladder`. -/
section

/-!
# X448 on AArch64: all 448 ladder iterations, and the final swap

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok opSwap swapMask_ok)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (bit)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s n →
      WP isa (.loop Impl.X448.AArch64.Fast.step (.nonzero .x .x19)) s fun s' => VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := Impl.X448.AArch64.Fast.step) (c := .nonzero .x .x19)
    (Q := fun s' => VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.AArch64.Fast.step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .x19 = BitVec.ofNat 64 448 → (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s' 448) :
    WP isa Impl.X448.AArch64.Fast.ladder s fun s' => VG.Proof.X448.AArch64.Fast.LInv base k u s₀ s' 0 :=
  WP.seq (WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.AArch64.Fast.loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = VG.Proof.X448.AArch64.mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      (∀ j < 8, limbs t.mem base (slot x.val) j = if sw then limbs s.mem base (slot y.val) j
        else limbs s.mem base (slot x.val) j) ∧
      (∀ j < 8, limbs t.mem base (slot y.val) j = if sw then limbs s.mem base (slot x.val) j
        else limbs s.mem base (slot y.val) j) ∧
      VG.Proof.X448.AArch64.Fast.Same base [x, y] s.mem t.mem ∧ EV t.mem base = opSwap x y sw (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound x)
    (VG.Proof.X448.AArch64.Weak.slot_bound y) (VG.Proof.X448.AArch64.Weak.slot_aligned x)
    (VG.Proof.X448.AArch64.Weak.slot_aligned y) (VG.Proof.X448.AArch64.Weak.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have sm : VG.Proof.X448.AArch64.Fast.Same base [x, y] s.mem t.mem := by
    intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have ex := VG.Proof.X448.AArch64.Weak.slot_sep hi.1
    have ey := VG.Proof.X448.AArch64.Weak.slot_sep hi.2
    have hi' := VG.Proof.X448.AArch64.Weak.slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi'; omega)]
  have fx : EV t.mem base x = if sw then EV s.mem base y else EV s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact tx
  have fy : EV t.mem base y = if sw then EV s.mem base x else EV s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, fun i => ?_, tk.1 _ (by decide), tx, ty, sm, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · by_cases hix : i = x
    · subst i; intro j hj; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; intro j hj; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · exact sm.bnd (by simp [hix, hiy]) (hb i)
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact sm.env (by simp [hix, hiy])

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block Impl.X448.AArch64.Weak.lastSwap) s fun t => VG.Proof.X448.AArch64.Fast.FKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧
      EV t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (EV s.mem base)) := by
  rw [Impl.X448.AArch64.Weak.lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : VG.Proof.X448.AArch64.Fast.FKeep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  have ts := kt.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Fast.cswapE ts (tm ▸ hb) 1 3 (by decide) tc) fun u ⟨ku, bu, cu, _, _, _, eu⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Fast.cswapE (ku.scr ts) bu 2 4 (by decide) (cu.trans tc)) fun v ⟨kv, bv, _, _, _, _, ev⟩ =>
    ⟨kt.trans (ku.trans kv), bv, by rw [ev, eu, tm]⟩

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Inv`. -/
section

/-!
# X448 on AArch64: inversion

Untrusted: everything here is checked by Lean. The addition chain of
`Impl/X448/AArch64/Weak.lean`, with the faster field operations.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok decCounter_ok opMul opCopy opSqn opMul_update
  FieldOp applyOps invEnv)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x19 :: VG.Proof.X448.AArch64.Fast.fclob) s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem IKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.AArch64.Fast.IKeep base s t) (h' : VG.Proof.X448.AArch64.Fast.IKeep base t u) :
    VG.Proof.X448.AArch64.Fast.IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Fast.IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem FKeep.ikeep {base : Addr} {s t : State} (h : VG.Proof.X448.AArch64.Fast.FKeep base s t) : VG.Proof.X448.AArch64.Fast.IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : VG.Proof.X448.AArch64.Fast.IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env) : Prop :=
  ∀ s, Scr s base → VG.Proof.X448.AArch64.Fast.BEnv s.mem base → WP isa code s fun t =>
    VG.Proof.X448.AArch64.Fast.IKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ EV t.mem base = f (EV s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.AArch64.Env → VG.Proof.X448.AArch64.Env}
    (h₁ : VG.Proof.X448.AArch64.Fast.ISpec base c₁ f) (h₂ : VG.Proof.X448.AArch64.Fast.ISpec base c₂ g) :
    VG.Proof.X448.AArch64.Fast.ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

/-- The inversion's operations: products and copies. -/
def fimpl : VG.Proof.X448.AArch64.Weak.FieldOp → Impl.X448.AArch64.Fast.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .copy o a => .copy (slot o.val) (slot a.val)
  | _ => .copy 0 0

def MulCopy : VG.Proof.X448.AArch64.Weak.FieldOp → Prop
  | .mul o a b => a = b ∨ o ≠ b
  | .copy .. => True
  | _ => False

theorem opsI (base : Addr) (xs : List VG.Proof.X448.AArch64.Weak.FieldOp) (hx : ∀ x ∈ xs, VG.Proof.X448.AArch64.Fast.MulCopy x) :
    VG.Proof.X448.AArch64.Fast.ISpec base (Impl.X448.AArch64.Fast.ops (xs.map VG.Proof.X448.AArch64.Fast.fimpl)) (VG.Proof.X448.AArch64.Weak.applyOps xs) := by
  induction xs with
  | nil => exact fun s _ hb => WP.block_nil ⟨⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩, hb, rfl⟩
  | cons x xs ih =>
    intro s hs hb
    have ih' := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    refine WP.seq ?_
    cases x with
    | mul o a b =>
      refine WP.mono (VG.Proof.X448.AArch64.Fast.fmulE hs hb o a b (hx _ List.mem_cons_self)) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | copy o a =>
      refine WP.mono (VG.Proof.X448.AArch64.Fast.copyE hs hb o a) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | _ => exact absurd (hx _ List.mem_cons_self) (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])

theorem sqnI (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    VG.Proof.X448.AArch64.Fast.ISpec base (Impl.X448.AArch64.Fast.sqn (slot o.val) n) (VG.Proof.X448.AArch64.Weak.opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.AArch64.Fast.sqn, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : VG.Proof.X448.AArch64.Fast.IKeep base s t := VG.Proof.X448.AArch64.Fast.counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ VG.Proof.X448.AArch64.Fast.IKeep base s u ∧ VG.Proof.X448.AArch64.Fast.BEnv u.mem base ∧
    u.gpr .x19 = BitVec.ofNat 64 m ∧
    EV u.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.block_append_iff]
    have hsq : Impl.Curve448.AArch64.Fast.sqr (slot o.val) (slot o.val) =
        Impl.X448.AArch64.Fast.fmul (slot o.val) (slot o.val) (slot o.val) := by
      simp only [Impl.X448.AArch64.Fast.fmul, ite_true]
    rw [hsq]
    refine WP.mono (VG.Proof.X448.AArch64.Fast.fmulE (ku.scr hs) bu o o o (Or.inl rfl)) fun v ⟨kv, bv, _, _, ev⟩ => ?_
    have cv : v.gpr .x19 = BitVec.ofNat 64 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : VG.Proof.X448.AArch64.Fast.IKeep base s w := ku.trans (kv.ikeep.trans (VG.Proof.X448.AArch64.Fast.counter_keep wg wm wr ww))
    have bw : VG.Proof.X448.AArch64.Fast.BEnv w.mem base := wm ▸ bv
    have ew : EV w.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m)) := by
      rw [wm, ev, eu]
      simp only [VG.Proof.X448.AArch64.opMul, Function.update_self, Function.update_idem]
      rw [← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, State.read, BitVec.setWidth_eq, bne, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

theorem invert_spec (base : Addr) : VG.Proof.X448.AArch64.Fast.ISpec base Impl.X448.AArch64.Fast.invert VG.Proof.X448.AArch64.Weak.invEnv := by
  have h : VG.Proof.X448.AArch64.Fast.ISpec base _ _ :=
    (VG.Proof.X448.AArch64.Fast.opsI base [.copy 14 2] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 14 14 2, .copy 15 14] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 15 15 14, .copy 16 15] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 16 16 15, .copy 17 16] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 17 17 16, .copy 18 17] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 18 18 17, .copy 19 18] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 19 19 18, .copy 20 19] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 19] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 19] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 17] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 16] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 15] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 14, .copy 21 20] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 21 21 2] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy])).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Fast.opsI base [.mul 20 20 2, .mul 21 21 20] (by simp [VG.Proof.X448.AArch64.Fast.MulCopy]))
  exact h

theorem invert_ok {s : State} {base : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base) :
    WP isa Impl.X448.AArch64.Fast.invert s fun t =>
      VG.Proof.X448.AArch64.Fast.IKeep base s t ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ EV t.mem base = VG.Proof.X448.AArch64.Weak.invEnv (EV s.mem base) :=
  VG.Proof.X448.AArch64.Fast.invert_spec base s hs hb

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.VSave`. -/
section

/-!
# X448 on AArch64: saving `v8`–`v15`

Untrusted: everything here is checked by Lean. The AdvSIMD products use
every vector register, so the function saves `v8`–`v15` (whose low halves
are callee-saved) at `VSAVE`, past everything else it writes, and restores
them last.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ACC)
open VG.Impl.X448.AArch64.Fast (VSAVE vsave vrestore)
open VG.Impl.Curve448.AArch64.Neon (V ldq stq)
open VG.Proof.Curve448.AArch64.Neon (exec_ldq exec_stq off_add st_outside read16_write scr_of setMem setMem_mem V_ne)
open VG.Proof.X448.AArch64 (Scr off Outside Outside2 FieldMem ofs)
open VG.Proof.X448.AArch64.Weak (ofs_off')

theorem _root_.VG.Proof.X448.AArch64.Outside.read16 {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') {d : Nat} (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 8192) :
    m'.read (off base d) 16 = m.read (off base d) 16 :=
  (Mem.read_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

/-- The low halves of `v8`–`v15` of `v`, saved in the working space. -/
def SavedV (base : Addr) (v : VReg → BitVec 128) (m : Mem) : Prop :=
  ∀ k < 8, (m.read (off base (VSAVE + 16 * k)) 16).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64

theorem SavedV.frame {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedV base v m)
    (he : ∀ d, VSAVE ≤ d → d < VSAVE + 128 → m' (off base d) = m (off base d)) : VG.Proof.X448.AArch64.Fast.SavedV base v m' := by
  intro k hk
  rw [← h k hk, Mem.read_congr fun i hi => ?_]
  have hV : VSAVE = 4736 := rfl
  rw [off_add]
  exact he _ (by omega) (by omega)

theorem SavedV.outside2 {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedV base v m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ VSAVE) (hy : y + ny ≤ VSAVE) :
    VG.Proof.X448.AArch64.Fast.SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)

theorem SavedV.outside {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedV base v m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ VSAVE ∨ VSAVE + 128 ≤ o) : VG.Proof.X448.AArch64.Fast.SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by simp only [VSAVE] at h2; omega)]; omega)

theorem SavedV.field {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedV base v m)
    {o : Nat} (ho : FieldMem base o m m') (hx : o + 128 ≤ VSAVE) : VG.Proof.X448.AArch64.Fast.SavedV base v m' := by
  have hA : ACC = 3584 := rfl
  have hV : VSAVE = 4736 := rfl
  exact h.frame fun d h1 h2 => ho _ (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.Weak.ofs_off' base (by omega)]; omega)

/-- Away from the output: `hfar` as `output_word` takes it. -/
theorem SavedV.output {base p : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedV base v m)
    {n : Nat} (ho : Outside p 0 n m m') (hn : n ≤ 56) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    VG.Proof.X448.AArch64.Fast.SavedV base v m' :=
  h.frame fun d h1 h2 => ho _ (Or.inr (Nat.le_trans (by omega) (hfar d (by simp only [VSAVE] at h2; omega))))

theorem vsave_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vsave) s fun t =>
      VG.Proof.X448.AArch64.Fast.SavedV base s.v t.mem ∧ Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vsave = (List.range 8).flatMap fun k => [stq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vsave]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (VSAVE + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tvv, tr, tw⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, _, tr, tw⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tr, tw⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega)).mono (by omega) (by omega)),
      tg, tvv, tr, tw⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [((st_outside t.mem base (t.v (V (8 + n))) (d := VSAVE + 16 * n) (by omega))).read16 (by omega)
      (by omega)]
    exact tv k (by omega)

theorem vrestore_ok {s : State} {base : Addr} (hs : Scr s base) {v : VReg → BitVec 128}
    (hsv : VG.Proof.X448.AArch64.Fast.SavedV base v s.mem) :
    WP isa (.block vrestore) s fun t =>
      (∀ k < 8, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hV : VSAVE = 4736 := rfl
  have e : vrestore = (List.range 8).flatMap fun k => [ldq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vrestore]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  have ts : Scr t base := scr_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]; exact hsv k hn
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
    exact tv k (by omega)

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Setup`. -/
section

/-!
# X448 on AArch64: setup, saving `x21`–`x28` and `v8`–`v15`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS ACC)
open VG.Impl.X448.AArch64.Fast (SAVE VSAVE saved save restore vsave)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib stw_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `x21`–`x28` saved in the working space. -/
def SavedX (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ k < 8, word m base (SAVE + 8 * k) = g (saved k)

theorem SavedX.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedX base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ SAVE) (hy : SAVE + 64 ≤ y) :
    VG.Proof.X448.AArch64.Fast.SavedX base g m' := fun k hk =>
  (ho.word (Or.inr (by omega)) (Or.inl (by omega)) (by simp only [SAVE]; omega)).trans (h k hk)

theorem SavedX.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.AArch64.Fast.SavedX base g m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ SAVE ∨ SAVE + 64 ≤ o) :
    VG.Proof.X448.AArch64.Fast.SavedX base g m' := fun k hk =>
  (ho.word (by omega) (by simp only [SAVE]; omega)).trans (h k hk)

theorem saved_ne : ∀ k < 8, saved k ≠ .x3 ∧ saved k ≠ .x12 := by decide

theorem save_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block save) s fun t =>
      VG.Proof.X448.AArch64.Fast.SavedX base s.gpr t.mem ∧ Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have e : save = (List.range 8).flatMap fun k => [st (saved k) (SAVE + 8 * k)] := by
    simp only [save]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, word t.mem base (SAVE + 8 * k) = s.gpr (saved k)) ∧
    Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl⟩
  have ts : Scr t base := ⟨by rw [tg]; exact hs.x3, by rw [tg]; exact hs.mask, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (stw_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uw, uO, ug, ur, uwr⟩ => ⟨fun k hk => ?_,
      tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr, uwr.trans tw⟩
  rw [uw _ (by simp only [SAVE]; omega) (by omega)]
  by_cases h : k = n
  · subst h; rw [ite_eq_left rfl, tg]
  · rw [ite_eq_right (by omega)]; exact tv k (by omega)

theorem saved_not_setup : ∀ k < 8, saved k ∉ VG.Proof.X448.AArch64.Weak.setupRegs := by decide

theorem weak_bnd {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.Curve448.AArch64.Bounded m base o) :
    VG.Proof.X448.AArch64.Fast.Bnd Mb m base o := fun i hi => Nat.lt_of_lt_of_le (h i hi) (by decide)

theorem setup0_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block (Impl.X448.AArch64.Weak.setup ++ save)) s fun t =>
      Scr t base ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ (∀ i : Index, VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot i.val)) ∧
      t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧ VG.Proof.X448.AArch64.Fast.SavedX base s.gpr t.mem ∧
      EV t.mem base 0 = VG.Proof.X448.toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      EV t.mem base 1 = 1 ∧ EV t.mem base 2 = 0 ∧
      EV t.mem base 3 = EV t.mem base 0 ∧ EV t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setup_ok hc hw hn hp hr hd)
    fun u ⟨us, ub, ux, uk, um, uv, u0, u1, u2, u3, u4, uw⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Fast.save_ok us) fun t ⟨tv, tO, tg, tr, tw⟩ => ?_
  have sl : ∀ i : Index, ∀ j < 8, limbs t.mem base (slot i.val) j = limbs u.mem base (slot i.val) j := by
    intro i j hj
    have hi := i.isLt
    have hS : SAVE = 2880 := rfl
    exact tO.limbs (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega) (by omega)
  have sm : VG.Proof.X448.AArch64.Fast.Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  have red : ∀ i : Index, VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot i.val) := fun i => sm.bnd (by simp) (VG.Proof.X448.AArch64.Fast.weak_bnd (ub i))
  have ug : ∀ r, t.gpr r = u.gpr r := fun r => by rw [tg]
  refine ⟨⟨(ug _).trans us.x3, (ug _).trans us.mask, tw ▸ us.wr, us.nowrap⟩,
    fun i j hj => Nat.lt_of_lt_of_le (red i j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib, red, (ug _).trans ux,
    ⟨fun r hr => (ug r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    um.trans ?_, uv.outside tO (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact tO x (by simp only [SAVE]; omega)
  · intro k hk; rw [tv k hk, uk.1 _ (VG.Proof.X448.AArch64.Fast.saved_not_setup k hk)]
  · rw [sm.env (by simp)]; exact u0
  · rw [sm.env (by simp)]; exact u1
  · rw [sm.env (by simp)]; exact u2
  · rw [sm.env (by simp), sm.env (by simp)]; exact u3
  · rw [sm.env (by simp)]; exact u4
  · rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block Impl.X448.AArch64.Fast.setup) s fun t =>
      Scr t base ∧ VG.Proof.X448.AArch64.Fast.BEnv t.mem base ∧ (∀ i : Index, VG.Proof.X448.AArch64.Fast.Bnd Mb t.mem base (slot i.val)) ∧
      t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧ VG.Proof.X448.AArch64.Fast.SavedX base s.gpr t.mem ∧
      EV t.mem base 0 = VG.Proof.X448.toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      EV t.mem base 1 = 1 ∧ EV t.mem base 2 = 0 ∧
      EV t.mem base 3 = EV t.mem base 0 ∧ EV t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 ∧
      VG.Proof.X448.AArch64.Fast.SavedV base s.v t.mem := by
  have hV : VSAVE = 4736 := rfl
  rw [Impl.X448.AArch64.Fast.setup, WP.block_append_iff]
  refine WP.mono (WP.preservedV (VG.Proof.X448.AArch64.Fast.setup0_ok hc hw hn hp hr hd) (by lit_decide))
    fun u ⟨⟨us, ub, red, ux, uk, uo, sv, svx, u0, u1, u2, u3, u4, uw⟩, uv⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.Fast.vsave_ok us) fun t ⟨tv, tO, tg, tr, tw⟩ => ?_
  have sl : ∀ i : Index, ∀ j < 8, limbs t.mem base (slot i.val) j = limbs u.mem base (slot i.val) j := by
    intro i j hj
    have hi := i.isLt
    exact tO.limbs (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega) (by omega)
  have sm : VG.Proof.X448.AArch64.Fast.Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  refine ⟨VG.Proof.Curve448.AArch64.Neon.scr_of us tg tw, fun i => sm.bnd (by simp) (ub i), fun i => sm.bnd (by simp) (red i), tg ▸ ux,
    ⟨fun r hr => (congrFun tg r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    uo.trans fun x hx => tO x (by omega), sv.outside tO (by decide), svx.outside tO (by decide),
    by rw [sm.env (by simp)]; exact u0, by rw [sm.env (by simp)]; exact u1, by rw [sm.env (by simp)]; exact u2,
    by rw [sm.env (by simp), sm.env (by simp)]; exact u3, by rw [sm.env (by simp)]; exact u4,
    by rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw, fun k hk => ?_⟩
  rw [tv k hk]
  exact uv _ (by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Finish`. -/
section

/-!
# X448 on AArch64: the result, and restoring the callee-saved registers

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X2 T7 SWAP BITS ACC)
open VG.Impl.X448.AArch64.Fast (SAVE VSAVE saved save restore)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved Op freeze_ok
  output_ok output_word restore_ok)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib ld_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem restoreX_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : VG.Proof.X448.AArch64.Fast.SavedX base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t := by
  have e : restore = (List.range 8).flatMap fun k => [ld (saved k) (SAVE + 8 * k)] := by
    simp only [restore]; rfl
  rw [e]
  have sinj : ∀ k < 8, ∀ j < 8, j ≠ k → saved j ≠ saved k := by decide
  have smem : ∀ k < 8, saved k ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide
  let inv := fun n (t : State) =>
    (∀ k < n, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (ld_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uv, um, uk⟩ => ⟨fun k hk => ?_, um.trans tm, tk.trans (uk.mono ?_)⟩
  · by_cases h : k = n
    · subst h; rw [uv, tm]; exact hsv k hn
    · rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sinj n hn k (by omega) h)]
      exact tv k (by omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [hr]; exact smem n hn

def finishRegs : List Reg := .x19 :: .x20 :: VG.Proof.X448.AArch64.Fast.fclob

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : VG.Proof.X448.AArch64.Fast.BEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : VG.Proof.X448.AArch64.Saved base g s.mem)
    (svx : VG.Proof.X448.AArch64.Fast.SavedX base g s.mem) {gv : VReg → BitVec 128} (svV : VG.Proof.X448.AArch64.Fast.SavedV base gv s.mem) :
    WP isa Impl.X448.AArch64.Fast.finish s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      Keeps VG.Proof.X448.AArch64.Fast.finishRegs s t ∧ Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (EV s.mem base 1 * EV s.mem base 21) := by
  rw [Impl.X448.AArch64.Fast.finish]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Fast.fmulE hs hb 1 1 21 (by decide)) fun u ⟨uk, ub, um, us, ue⟩ => ?_
  have us₀ := uk.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' us₀ (o := X2) (by decide) (by decide)
    (fun i hi => Nat.lt_trans (um i hi) (by decide))) fun u' ⟨ck, cb, cv⟩ => ?_
  have uv : VG.Proof.X448.AArch64.F u'.mem base X2 = EV s.mem base 1 * EV s.mem base 21 := by
    rw [cv]
    change EV u.mem base 1 = _
    rw [ue]; simp only [VG.Proof.X448.AArch64.opMul, Function.update_self]
  have us := us₀.of_keeps ck.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us cb) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs vb ((vk.1 _ (by decide)).trans ((ck.1.1 _ (by decide)).trans
    ((uk.regs.1 _ (by decide)).trans hp)))
    (by intro j hj; rw [vk.2.2, ck.1.2.2, uk.regs.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := ((sv.outside2 uk.mem (by decide) (by decide)).field ck.2 (by decide)).field vm (by decide)
  have svw : VG.Proof.X448.AArch64.Saved base g w.mem :=
    ⟨(output_word wm (by decide) (by decide) hfar).trans svv.1,
      (output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  have sxv : VG.Proof.X448.AArch64.Fast.SavedX base g v.mem := by
    intro k hk
    have hS : SAVE = 2880 := rfl
    rw [vm.word (Or.inr (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)) (by simp only [ACC]; omega),
      ck.2.word (Or.inr (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)) (by simp only [ACC]; omega),
      uk.mem.word (Or.inr (by omega)) (Or.inl (by simp only [ACC]; omega)) (by omega)]
    exact svx k hk
  have sxw : VG.Proof.X448.AArch64.Fast.SavedX base g w.mem := fun k hk =>
    (output_word wm (by decide) (by simp only [SAVE]; omega) hfar).trans (sxv k hk)
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  have tsx : VG.Proof.X448.AArch64.Fast.SavedX base g t.mem := by rw [tm]; exact sxw
  have ts := ws.of_keeps tk (by decide)
  have hV : VSAVE = 4736 := rfl
  have vsw : VG.Proof.X448.AArch64.Fast.SavedV base gv w.mem :=
    ((((svV.outside2 uk.mem (by decide) (by decide)).field ck.2 (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)).field
      vm (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)).output wm (by decide) hfar)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Fast.restoreX_ok ts tsx) fun z ⟨zv, zm, zk⟩ => ?_
  have zs := ts.of_keeps zk (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Fast.vrestore_ok zs (v := gv) (by rw [zm, tm]; exact vsw)) fun z' ⟨zvv, zm', zg', zr', zw'⟩ => ?_
  have zk' : Keeps [] z z' := ⟨fun r _ => congrFun zg' r, zr', zw'⟩
  refine ⟨(zg' ▸ zk.1 _ (by decide)).trans tb, (zg' ▸ zk.1 _ (by decide)).trans tr, fun k hk => zg' ▸ zv k hk, zvv,
    (uk.regs.mono ?_).trans ((ck.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans
      ((tk.mono ?_).trans ((zk.mono ?_).trans (zk'.mono ?_)))))), ?_, ?_⟩
  all_goals try (intro r hr; revert r; decide)
  · rw [zm', zm, tm]
    exact ((((uk.mem.whole (by decide) (by decide)).trans ((ck.2.whole (by decide)).trans
      (vm.whole (by decide)))).frame.mono (by simp)).trans (wm.frame.mono (by simp)))
  · rw [zm', zm, tm, wv, vv, VG.Proof.X448.encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Main`. -/
section

/-!
# X448 on AArch64: the whole function, with register-resident field arithmetic

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64 VG.Proof.X448
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved Pre far
  far_output bytesAt_outside pointR scalarR outR scR bits_ok moveOutput_ok bitRegs)
open VG.Proof.X448.AArch64.Weak (Index Env E_outside cswap_fst invEnv invEnv_x2 invEnv_eval opSwap)
open VG.Impl.X448.AArch64.Fast (saved)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.X448.AArch64.Fast.x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      Proof.X448.x448AArch64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .x3 = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .x2) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x2) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off (s₀.gpr .x1) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [Impl.X448.AArch64.Fast.x448]
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, b₁, r₁, savedOut₁, k₁, o₁, sv₁, svx₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁, svV₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (off (s₀.gpr .x1) j) 1 := fun j hj =>
    ⟨scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (bits_ok hs₁ (k₁.1 _ (by decide)) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : Keeps bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  refine WP.seq (WP.mono (moveOutput_ok s₂) fun s₃ ⟨out₃, m₃, k₃⟩ => ?_)
  have k03 := k₁.then (k₂.then k₃)
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  have sv₃ : VG.Proof.X448.AArch64.Saved base s₀.gpr s₃.mem := by rw [m₃]; exact sv₁.outside o₂ (by decide)
  have svx₃ : VG.Proof.X448.AArch64.Fast.SavedX base s₀.gpr s₃.mem := by
    rw [m₃]; exact svx₁.outside o₂ (by simp only [BITS, Impl.X448.AArch64.Fast.SAVE]; omega)
  have svV₃ : VG.Proof.X448.AArch64.Fast.SavedV base s₀.v s₃.mem := by
    rw [m₃]; exact svV₁.outside o₂ (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)
  have l₃ : ∀ i : Index, ∀ j < 8, limbs s₃.mem base (slot i.val) j = limbs s₁.mem base (slot i.val) j := by
    intro i j hj
    rw [m₃]
    exact o₂.limbs (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) (by omega)
  have e₃ : ∀ i : Index, EV s₃.mem base i = EV s₁.mem base i := fun i =>
    congrArg toFe (VG.Proof.X448.Wide.valN_congr (l₃ i))
  have b₃ : VG.Proof.X448.AArch64.Fast.BEnv s₃.mem base := fun i j hj => by rw [l₃ i j hj]; exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.ladder_ok (s₀ := s₃) (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
    (fun t ht => by rw [m₃, bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨(hg _ (by decide)).trans hs₃.x3, (hg _ (by decide)).trans hs₃.mask, hw ▸ hs₃.wr, hn⟩, hm ▸ b₃,
      fun i _ j hj => by rw [hm, l₃ i j hj]; exact r₁ i j hj,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₃ 0, x1₁], by rw [hm, e₃ 1, x2₁]; rfl,
      by rw [hm, e₃ 2, z2₁]; rfl, by rw [hm, e₃ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₃ 4, z3₁]; rfl,
      by rw [hm, m₃, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.lastSwap_ok L.scr L.env
    (by have := VG.Proof.X448.ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .x1) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .x2) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.AArch64.Fast.invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k36 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have svx₆ := ((svx₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have svV₆ := ((svV₃.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .x1 = s₀.gpr .x0 :=
    (k36.1 _ (by decide)).trans (out₃.trans ((g₂ _ (by decide)).trans savedOut₁))
  have k06 := k03.then k36
  have hw₆ : ∀ j < 56, InRegions s₆.wr (off (s₀.gpr .x0) j) 1 := fun j hj =>
    ⟨outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.X448.AArch64.Fast.finish_ok (k₆.scr hs₅) b₆ out₆ hw₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆ svx₆ svV₆) fun s' ⟨rb, x20, rx, rv, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rb
    · exact x20
    · exact rx 0 (by decide)
    · exact rx 1 (by decide)
    · exact rx 2 (by decide)
    · exact rx 3 (by decide)
    · exact rx 4 (by decide)
    · exact rx 5 (by decide)
    · exact rx 6 (by decide)
    · exact rx 7 (by decide)
    · exact kall.1 _ (by decide)
  · simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rv 0 (by decide)
    · exact rv 1 (by decide)
    · exact rv 2 (by decide)
    · exact rv 3 (by decide)
    · exact rv 4 (by decide)
    · exact rv 5 (by decide)
    · exact rv 6 (by decide)
    · exact rv 7 (by decide)
  · change Spec.X448.bytesAt s'.mem (s₀.gpr .x0) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.AArch64.Weak.invEnv_x2, VG.Proof.X448.AArch64.Weak.invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.AArch64.Fast

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Fast.Verified`. -/
section

/-!
# X448 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), satisfiability, and the shared
contract of `Spec/`.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Proof.X448.AArch64 (Pre)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448AArch64.pre s) :
    ∃ t s', Exec isa Impl.X448.AArch64.Fast.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448AArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.X448.AArch64.Fast.correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he, h.2.1⟩, h.2.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448AArch64.pre Proof.X448.x448AArch64.pub
    Impl.X448.AArch64.Fast.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448_verified :
    Verified AArch64.target Impl.X448.AArch64.Fast.x448 (Spec.X448.x448Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.X448.AArch64.Fast.x448_ok VG.Proof.X448.AArch64.Fast.x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, AArch64.abi, AArch64.argRegs,
      Proof.X448.x448AArch64] [satState] using VG.Proof.X448.AArch64.Fast.satState)

end VG.Proof.X448.AArch64.Fast

end
