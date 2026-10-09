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

/-- The accumulator's `X`, `Y` and `Z` (slots 0–2) are at most `2p`, as the comb's
additions need (`pointAddAffine`). -/
def AccBnd (m : Mem) (base : Addr) : Prop := ∀ i : Slot, i.val < 3 → Bnd m base i

/-- Every operation of `ops` has its operands bounded as `codeB lazy` needs, from the
slots `B` bounded at the start. -/
def bndOk (lazy : Bool) : List FieldOp → (Slot → Bool) → Bool
  | [], _ => true
  | op :: ops, B => opOk lazy op B && bndOk lazy ops (bndStep op B)

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

/-- `fieldCode`, lifted to the wide scratch, with bounds before and after. -/
theorem fieldCodeFromWide_ok (ops : List FieldOp) {s : State} {base : Addr} (hs : Scratch s base)
    {B : Slot → Bool} (hB : ∀ i, B i = true → Bnd s.mem base i) :
    WP isa (.block (fieldCodeFrom fld B ops)) s fun t => Keep base s t ∧
      env t.mem base = evalOps ops (env s.mem base) ∧
      ∀ i, bndOut ops B i = true → Bnd t.mem base i :=
  field_liftB hs _ (evalOps ops) (fun m => ∀ i, B i = true → Bnd m base i)
    (fun m => ∀ i, bndOut ops B i = true → Bnd m base i) hB
    (fun _ h hp => fieldCodeFrom_ok ops h hp)

/-- After `ops`, the slots it last wrote with products or constants, among `0`–`2`,
are bounded (`bndOut ops (fun _ => false)` names them), whatever was before. -/
theorem fieldCodeWide_acc (ops : List FieldOp) {s : State} {base : Addr} (hs : Scratch s base)
    (h : ∀ i : Slot, i.val < 3 → bndOut ops (fun _ => false) i = true) :
    WP isa (.block (fieldCode fld ops)) s fun t => AccBnd t.mem base :=
  WP.mono (fieldCodeFromWide_ok ops hs (B := fun _ => false) nofun)
    fun _ ⟨_, _, hb⟩ i hi => hb i (h i hi)

/-- `ops` keeps the bounds of slots `0`–`2` if it writes none of them, or writes them
with products or constants. -/
theorem fieldCodeWide_accKeep (ops : List FieldOp) {s : State} {base : Addr} (hs : Scratch s base)
    (hb : AccBnd s.mem base)
    (h : ∀ i : Slot, i.val < 3 → bndOut ops (fun i => decide (i.val < 3)) i = true)
    (hs' : fieldCode fld ops = fieldCodeFrom fld (fun i => decide (i.val < 3)) ops) :
    WP isa (.block (fieldCode fld ops)) s fun t => AccBnd t.mem base := by
  rw [hs']
  exact WP.mono (fieldCodeFromWide_ok ops hs fun i hi => hb i (of_decide_eq_true hi))
    fun _ ⟨_, _, hb'⟩ i hi => hb' i (h i hi)

end VG.Proof.Ed25519.X86_64
