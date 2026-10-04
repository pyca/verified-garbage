import VerifiedGarbage.Proof.Ed448.VerifyFormulas
import VerifiedGarbage.Proof.X448.X86.Square
import VerifiedGarbage.Impl.Ed448.X86.VerifyEquation

/-!
# Ed448 verification's equation on x86 (32-bit): field programs

A list of field operations on the slots (`FOp`, `Impl/Ed448/Formulas.lean`)
runs as X448's field arithmetic on x86 (`field_ok`): the slots become the
operations' evaluation (`evalOps`, whose values for the doubling, the
addition and the steps of decoding are in `Proof/Ed448/VerifyFormulas.lean`).
`VKeep` is what the checks and decoding may change: the field operations'
registers, the counter `esi`, and the working space from `BAD` to the slots'
end and from X448's `ACC`.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (idx fopValid evalOp evalOps pt)
open VG.Impl.X448.X86 (slot X2 ACC sc)

/-! ## Reading the working space -/

theorem rd_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 8192) :
    readSrc s (.mem (sc d)) = some (word s.mem base d) := by
  simp only [readSrc, hs.ea (d := d) (by omega), State.load32, hs.read (d := d) (n := 4) hd, ite_true]

/-! ## Field programs -/

theorem slot_idx {n : Nat} (h : n < 22) : slot n = slot (idx n).val := by
  simp only [idx, Nat.mod_eq_of_lt h]

theorem fop_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (op : FOp)
    (hv : fopValid op) :
    WP isa (toOp op).code s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = evalOp op (E s.mem base) := by
  cases op with
  | mul o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact mulE hs hb _ _ _
  | sqr o a =>
    obtain ⟨h1, h2⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, slot_idx h1, slot_idx h2]
    exact mulE hs hb _ _ _
  | add o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact addE hs hb _ _ _
  | sub o a b =>
    obtain ⟨h1, h2, h3⟩ := hv
    simp only [toOp, Impl.X448.X86.Op.code, slot_idx h1, slot_idx h2, slot_idx h3]
    exact subE hs hb _ _ _

theorem field_ok (l : List FOp) (hv : ∀ op ∈ l, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa (field l) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = evalOps l (E s.mem base) := by
  induction l generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op l ih =>
    change WP isa (.seq (toOp op).code (field l)) s _
    rw [WP.seq_iff]
    refine WP.mono (fop_ok hs hb op (hv op List.mem_cons_self)) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (fun o h => hv o (List.mem_cons_of_mem _ h)) (tk.scr hs) tb)
      fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]; rfl⟩

/-- A field program, then more code. -/
theorem field_seq (l : List FOp) (hv : ∀ op ∈ l, fopValid op) {s : State} {base : Addr}
    (hs : Scr s base) (hb : BoundedEnv s.mem base) {c : Prog isa} {Q : State → Prop}
    (k : ∀ t, Keep base s t → BoundedEnv t.mem base → E t.mem base = evalOps l (E s.mem base) →
      WP isa c t Q) :
    WP isa (.seq (field l) c) s Q :=
  WP.seq (WP.mono (field_ok l hv hs hb) fun t ⟨kt, bt, et⟩ => k t kt bt et)

/-! ## The frame -/

/-- What the checks and decoding may change. -/
structure VKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.esi :: workRegs) s t
  mem : Outside2 base 16 2864 ACC 512 s.mem t.mem

theorem VKeep.refl (base : Addr) (s : State) : VKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem VKeep.trans {base : Addr} {s t u : State} (h : VKeep base s t) (h' : VKeep base t u) :
    VKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem VKeep.scr {base : Addr} {s t : State} (h : VKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Outside2.widen {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    Outside2 base 16 2864 ACC 512 m m' :=
  fun p h1 h2 => h p (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]) h2

theorem IKeep.toV {base : Addr} {s t : State} (h : IKeep base s t) : VKeep base s t :=
  ⟨h.regs, Outside2.widen h.mem⟩

theorem Keep.toV {base : Addr} {s t : State} (h : Keep base s t) : VKeep base s t := IKeep.toV h.ikeep

theorem slot_range (i : Index) : 64 ≤ slot i.val ∧ slot i.val + 112 ≤ 2880 := by
  have := i.isLt
  simp only [slot]
  omega

theorem outV {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : 16 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 16 2864 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmV {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 16 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 16 2864 ACC 512 m m' := fun p hp hq => h p (by omega) hq

/-- The point in slots `i`, `j`, `k`, from equal slots. -/
theorem pt_congr' {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

end VG.Proof.Ed448.X86
