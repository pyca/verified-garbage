import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide

/-!
# Ed25519 field programs with sums and differences folded once

`fieldCodeL` folds the carry of each sum, and the borrow of each difference,
once (`addL`, `subL`), which is correct when one operand of the sum, or the
subtrahend of the difference, is at most `2p`. Every product is
(`mulBnd_ok`, `mulXBnd_ok`), so a program's sums and differences meet this if
those operands are products, or slots bounded before it runs.

Which slots are bounded is tracked by `bndStep` through a program (a product's
result is, every other result is forgotten), and `bndOk` checks each sum and
difference against it; for a given program both are evaluated by `decide`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F fe)

variable {fld : Arith} [EdArith fld]

/-- Two postconditions of the same code (which runs deterministically). -/
theorem wp_and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- Slot `i` holds at most `2p`. -/
def Bnd (m : Mem) (base : Addr) (i : Slot) : Prop :=
  fe m base (offset i) ≤ 2 * Spec.X25519.P

/-- The accumulator's `X`, `Y` and `Z` (slots 0–2) are at most `2p`, as the comb's
additions need (`pointAddAffine`). -/
def AccBnd (m : Mem) (base : Addr) : Prop := ∀ i : Slot, i.val < 3 → Bnd m base i

/-- The slot an operation writes. -/
def _root_.VG.Impl.Ed25519.X86_64.FieldOp.out : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ | .mul2 o _ _
  | .sqr2 o _ => o

/-- The operation's result is at most `2p`: a product, or a constant. -/
def _root_.VG.Impl.Ed25519.X86_64.FieldOp.bnd : FieldOp → Bool
  | .mul .. | .sqr .. | .const .. => true
  | _ => false

/-- The slots bounded after `op`, if `B` were before it. -/
def bndStep (op : FieldOp) (B : Slot → Bool) : Slot → Bool := Function.update B op.out op.bnd

/-- `op`'s operands are bounded as `codeB lazy` needs. -/
def opOk (lazy : Bool) (op : FieldOp) (B : Slot → Bool) : Bool :=
  match lazy, op with
  | true, .add _ a b => B a || B b
  | true, .sub _ _ b => B b
  | _, _ => true

/-- Every operation of `ops` has its operands bounded as `codeB lazy` needs, from the
slots `B` bounded at the start. -/
def bndOk (lazy : Bool) : List FieldOp → (Slot → Bool) → Bool
  | [], _ => true
  | op :: ops, B => opOk lazy op B && bndOk lazy ops (bndStep op B)

/-- The slots bounded after `ops`. -/
def bndOut : List FieldOp → (Slot → Bool) → Slot → Bool
  | [], B => B
  | op :: ops, B => bndOut ops (bndStep op B)

theorem bndOk_false (ops : List FieldOp) (B : Slot → Bool) : bndOk false ops B = true := by
  induction ops generalizing B with
  | nil => rfl
  | cons op ops ih => simp only [bndOk, opOk, Bool.true_and, ih]

omit [EdArith fld] in
theorem codeB_false (op : FieldOp) : op.codeB fld false = op.code fld := by
  cases op <;> rfl

omit [EdArith fld] in
theorem fieldCode_eq_codeB (ops : List FieldOp) :
    fieldCode fld ops = ops.flatMap (FieldOp.codeB fld false) :=
  congrArg (List.flatMap · ops) (funext fun op => (codeB_false op).symm)

/-- A product of `fld` is at most `2p`. -/
theorem EdArith.mulBnd {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Proof.X25519.X86_64.Slot o) (ha : Proof.X25519.X86_64.Slot a)
    (hb : Proof.X25519.X86_64.Slot b) :
    WP isa (.block (fld.mul o a b)) s fun t => Op base o s t ∧
      F t.mem base o = F s.mem base a * F s.mem base b ∧ fe t.mem base o ≤ 2 * Spec.X25519.P := by
  rcases EdArith.known (fld := fld) with rfl | rfl
  · exact Proof.X25519.X86_64.mulBnd_ok hs ho ha hb
  · exact Proof.X25519.X86_64.mulXBnd_ok hs ho ha hb

/-- A square of `fld` is at most `2p`. -/
theorem EdArith.sqrBnd {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Proof.X25519.X86_64.Slot o) (ha : Proof.X25519.X86_64.Slot a) :
    WP isa (.block (fld.sqr o a)) s fun t => Op base o s t ∧
      F t.mem base o = F s.mem base a * F s.mem base a ∧ fe t.mem base o ≤ 2 * Spec.X25519.P := by
  rcases EdArith.known (fld := fld) with rfl | rfl
  · exact Proof.X25519.X86_64.sqrBnd_ok hs ho ha
  · exact Proof.X25519.X86_64.sqrXBnd_ok hs ho ha

/-- The bounds after an operation into `op.out`: the other slots keep theirs. -/
theorem bnd_after {op : FieldOp} {B : Slot → Bool} {base : Addr} {s t : State}
    (h : Op base (offset op.out) s t) (hB : ∀ i, B i = true → Bnd s.mem base i)
    (hp : op.bnd = true → Bnd t.mem base op.out) :
    ∀ i, bndStep op B i = true → Bnd t.mem base i := by
  intro i hi
  by_cases e : i = op.out
  · subst e
    rw [bndStep, Function.update_self] at hi
    exact hp hi
  · rw [bndStep, Function.update_of_ne e] at hi
    have hne : i.val ≠ op.out.val := fun h' => e (Fin.ext h')
    unfold Bnd
    rw [h.mem.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]
    exact hB i hi

theorem fieldOpB_ok {s : State} {base : Addr} (hs : Scr s base) (lazy : Bool) (op : FieldOp)
    {B : Slot → Bool} (hok : opOk lazy op B = true) (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (op.codeB fld lazy)) s fun t => Keep base s t ∧
      env t.mem base = evalOp op (env s.mem base) ∧ ∀ i, bndStep op B i = true → Bnd t.mem base i := by
  cases op with
  | mul o a b =>
    refine WP.mono (EdArith.mulBnd (fld := fld) hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e, hb⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => hb⟩
  | sqr o a =>
    refine WP.mono (EdArith.sqrBnd (fld := fld) hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e, hb⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => hb⟩
  | add o a b =>
    cases lazy with
    | false =>
      refine WP.mono (Proof.X25519.X86_64.add_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
    | true =>
      have hab : Bnd s.mem base a ∨ Bnd s.mem base b := by
        simp only [opOk, Bool.or_eq_true] at hok
        exact hok.imp (hB a) (hB b)
      refine WP.mono (Proof.X25519.X86_64.addL_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega) hab) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | sub o a b =>
    cases lazy with
    | false =>
      refine WP.mono (Proof.X25519.X86_64.sub_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
    | true =>
      refine WP.mono (Proof.X25519.X86_64.subL_ok hs
        (by simp only [offset]; omega) (by simp only [offset]; omega)
        (by simp only [offset]; omega) (hB b hok)) fun t ⟨h, e⟩ => ?_
      exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | copy o a =>
    refine WP.mono (copyField_op hs o a) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | const o v =>
    refine WP.mono (constField_op hs o v) fun t ⟨h, e, r⟩ => ?_
    refine ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB fun _ => ?_⟩
    show fe t.mem base (offset o) ≤ _
    rw [r]; have := v.isLt; omega
  | mul2 o a b =>
    refine WP.mono ((EdArith.ok (fld := fld)).mul2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)
      (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩
  | sqr2 o a =>
    refine WP.mono ((EdArith.ok (fld := fld)).sqr2 hs
      (by simp only [offset]; omega) (by simp only [offset]; omega)) fun t ⟨h, e⟩ => ?_
    exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, bnd_after h hB (fun e => by simp [FieldOp.bnd] at e)⟩

theorem fieldCodeB_ok (lazy : Bool) (ops : List FieldOp) {s : State} {base : Addr}
    (hs : Scr s base) {B : Slot → Bool} (hok : bndOk lazy ops B = true)
    (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (ops.flatMap (FieldOp.codeB fld lazy))) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ i, bndOut ops B i = true → Bnd t.mem base i := by
  induction ops generalizing s B with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl, hB⟩
  | cons op ops ih =>
    simp only [bndOk, Bool.and_eq_true] at hok
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fieldOpB_ok hs lazy op hok.1 hB) fun t ⟨ht, et, bt⟩ => ?_
    refine WP.mono (ih (ht.scr hs) hok.2 bt) fun u ⟨hu, eu, bu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl, bu⟩

/-- `field_lift`, with bounds before and after. -/
theorem field_liftB {s : State} {base : Addr} (hs : Scratch s base) (code : List Instr)
    (f : Env → Env) (Pre Post : Mem → Prop) (hpre : Pre s.mem)
    (correct : ∀ t, Scr t base → Pre t.mem → WP isa (.block code) t fun u =>
      Keep base t u ∧ env u.mem base = f (env t.mem base) ∧ Post u.mem) :
    WP isa (.block code) s fun t => Keep base s t ∧ env t.mem base = f (env s.mem base) ∧
      Post t.mem := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hk, hv, hp⟩ := correct narrow hn hpre
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, ⟨hk.gpr, rfl, rfl, hk.mem⟩, hv, hp⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

theorem fieldCodeBWide_ok (lazy : Bool) (ops : List FieldOp) {s : State} {base : Addr}
    (hs : Scratch s base) {B : Slot → Bool} (hok : bndOk lazy ops B = true)
    (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (ops.flatMap (FieldOp.codeB fld lazy))) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ i, bndOut ops B i = true → Bnd t.mem base i :=
  field_liftB hs _ (evalOps ops) (fun m => ∀ i, B i = true → Bnd m base i)
    (fun m => ∀ i, bndOut ops B i = true → Bnd m base i) hB
    (fun _ h hp => fieldCodeB_ok lazy ops h hok hp)

/-- After `ops`, the slots it last wrote with products or constants, among `0`–`2`,
are bounded (`bndOut ops (fun _ => false)` names them), whatever was before. -/
theorem fieldCodeWide_acc (ops : List FieldOp) {s : State} {base : Addr} (hs : Scratch s base)
    (h : ∀ i : Slot, i.val < 3 → bndOut ops (fun _ => false) i = true) :
    WP isa (.block (fieldCode fld ops)) s fun t => AccBnd t.mem base := by
  rw [fieldCode_eq_codeB]
  exact WP.mono (fieldCodeBWide_ok false ops hs (B := fun _ => false) (bndOk_false ops _) nofun)
    fun _ ⟨_, _, hb⟩ i hi => hb i (h i hi)

/-- `ops` keeps the bounds of slots `0`–`2` if it writes none of them, or writes them
with products or constants. -/
theorem fieldCodeWide_accKeep (ops : List FieldOp) {s : State} {base : Addr} (hs : Scratch s base)
    (hb : AccBnd s.mem base)
    (h : ∀ i : Slot, i.val < 3 → bndOut ops (fun i => decide (i.val < 3)) i = true) :
    WP isa (.block (fieldCode fld ops)) s fun t => AccBnd t.mem base := by
  rw [fieldCode_eq_codeB]
  exact WP.mono (fieldCodeBWide_ok false ops hs (bndOk_false ops _)
    fun i hi => hb i (of_decide_eq_true hi)) fun _ ⟨_, _, hb'⟩ i hi => hb' i (h i hi)

end VG.Proof.Ed25519.X86_64
