module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
public import VerifiedGarbage.Proof.Ed25519.AArch64.Sub

/-!
# Field programs: which slots hold small values

Untrusted: everything here is checked by Lean. Addition and subtraction with one
fold of the carry (`fieldAdd1`, `fieldSub1`) need operands stored below
`2²⁵⁵ + 2¹³⁶`, not just below `2²⁵⁶`. Products and squares are stored below
that, and so are constants; `fieldCode_okS` tracks the slots a field program
leaves small (`smallAfterOps`), so that a caller can tell by `decide`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519

/-- The slots `S` hold values below `2²⁵⁵ + 2¹³⁶`. -/
def Small (m : Mem) (base : Addr) (S : Slot → Bool) : Prop :=
  ∀ i, S i = true → fe m base (offset i) < 2 ^ 255 + 2 ^ 136

theorem Small.none (m : Mem) (base : Addr) : Small m base fun _ => false := fun _ h => nomatch h

/-- Writing slot `o` alone, small if `b`. -/
theorem Small.update {base : Addr} {m m' : Mem} {S : Slot → Bool} {o : Slot} (h : Outside base (offset o) 32 m m')
    (hS : Small m base S) (b : Bool) (hb : b = true → fe m' base (offset o) < 2 ^ 255 + 2 ^ 136) :
    Small m' base fun i => if i = o then b else S i := by
  intro i hi
  by_cases ho : i = o
  · subst ho
    simp only [ite_true] at hi
    exact hb hi
  · simp only [ho, ite_false] at hi
    have hne : i.val ≠ o.val := fun h => ho (Fin.ext h)
    rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
    exact hS i hi

theorem Small.mono {base : Addr} {m : Mem} {S S' : Slot → Bool} (h : ∀ i, S i = true → S' i = true)
    (hS : Small m base S') : Small m base S := fun i hi => hS i (h i hi)

/-- Writing memory outside the slots. -/
theorem Small.frame {base : Addr} {m m' : Mem} {S : Slot → Bool} {o n : Nat} (h : Outside base o n m m')
    (ho : 64 + 32 * 22 ≤ o) (hS : Small m base S) : Small m' base S := by
  intro i hi
  have := i.isLt
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
  exact hS i hi

/-- The slots small after `op`, if `S` were before it: a product, a square, a constant,
or a copy of a small slot. -/
def smallAfter (op : FieldOp) (S : Slot → Bool) : Slot → Bool :=
  match op with
  | .copy o a => fun i => if i = o then S a else S i
  | .const o _ | .mul o _ _ | .sqr o _ => fun i => if i = o then true else S i
  | .add o _ _ | .sub o _ _ => fun i => if i = o then false else S i

def smallAfterOps (ops : List FieldOp) (S : Slot → Bool) : Slot → Bool :=
  ops.foldl (fun S op => smallAfter op S) S

theorem fieldOp_okS {s : State} {base : Addr} (hs : Scr s base large) (op : FieldOp) {S : Slot → Bool}
    (hS : Small s.mem base S) :
    WP isa (.block op.code) s fun t => Keep base s t ∧ env t.mem base = evalOp op (env s.mem base) ∧
      Small t.mem base (smallAfter op S) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have hP : VG.Spec.X25519.P < 2 ^ 255 + 2 ^ 136 := by simp only [VG.Spec.X25519.P]; omega
  cases op with
  | copy o a =>
    refine WP.mono (copyField_opB hs o a) fun t ⟨h, e⟩ => ?_
    refine ⟨op_keep h, by rw [env_update o h.mem]; simp only [F]; rw [e]; rfl, ?_⟩
    exact hS.update h.mem (S a) fun ha => by rw [e]; exact hS a ha
  | const o v =>
    refine WP.mono (constField_opB hs o v) fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl,
      hS.update h.mem true fun _ => by rw [r]; exact Nat.lt_trans v.isLt hP⟩
  | mul o a b =>
    refine WP.mono (mul_okB hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
      (slot_rangeWith (large := large) b)) fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem true fun _ => by omega⟩
  | sqr o a =>
    refine WP.mono (sqr_okB hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a))
      fun t ⟨h, e, r⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem true fun _ => by omega⟩
  | add o a b =>
    refine WP.mono (add_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
      (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩
  | sub o a b =>
    refine WP.mono (sub_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
      (slot_rangeWith (large := large) b)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩

/-- `fieldCode_ok`, with the slots the program leaves small. -/
theorem fieldCode_okS (ops : List FieldOp) {s : State} {base : Addr} (hs : Scr s base large)
    {S : Slot → Bool} (hS : Small s.mem base S) :
    WP isa (.block (fieldCode ops)) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps ops (env s.mem base) ∧ Small t.mem base (smallAfterOps ops S) := by
  induction ops generalizing s S with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, hS⟩
  | cons op ops ih =>
    rw [fieldCode, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOp_okS hs op hS) fun t ⟨ht, et, st⟩ => ?_
    refine WP.mono (ih (ht.scr hs) st) fun u ⟨hu, eu, su⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl, su⟩

/-- `fieldAdd1` on small slots. -/
theorem add1Slot_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) {S : Slot → Bool}
    (hS : Small s.mem base S) (ha : S a = true) (hb : S b = true) :
    WP isa (.block (fieldAdd1 (offset o) (offset a) (offset b))) s fun t =>
      Keep base s t ∧ env t.mem base = evalOp (.add o a b) (env s.mem base) ∧
      Small t.mem base (fun i => if i = o then false else S i) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have := hS a ha
  have := hS b hb
  refine WP.mono (add1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
    (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
  exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩

/-- `fieldSub1` from a small slot. -/
theorem sub1Slot_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) {S : Slot → Bool}
    (hS : Small s.mem base S) (hb : S b = true) :
    WP isa (.block (fieldSub1 (offset o) (offset a) (offset b))) s fun t =>
      Keep base s t ∧ env t.mem base = evalOp (.sub o a b) (env s.mem base) ∧
      Small t.mem base (fun i => if i = o then false else S i) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have := hS b hb
  refine WP.mono (sub1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
    (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
  exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩

end VG.Proof.Ed25519.AArch64
