module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Calls of functions that call, as inlined code (x86-64)

`Code.InlineOk` (`CallInline.lean`) lets code call only functions that call
nothing. This file allows one level more: a function the code calls may
itself call functions that call nothing (`Code.CalleeOk`), as a function
whose additions are calls of another does. `Code.inlineD c` is `c` with each
call replaced by the code it calls, with that code's own calls inlined
(`Code.inline`). Code whose proofs say that memory changes only where they
name (and nothing of the 16 bytes below `rsp`, `hole2`, which no buffer
overlaps) is proved for its inlined form; this file moves the proof to `c`:

* a run of `c.inlineD` gives a run of `c`, whose final state is that of
  `c.inlineD` but for the 16 bytes below `rsp` and the unknowns the calls
  consume (`Exec.uninlineD`);
* the run's leakage is a function of the inlined run's (`liftTD`), so `c` is
  constant time if `c.inlineD` is (`ConstantTime.of_inlineD`).

Inside a call, `rsp` is 8 lower than in the inlined run, and inside its
calls 16: the function's run is `Exec.uninline`'s from 8 below, of the code
it calls with its own calls inlined, run first with the return address in
place (`Exec.F`).
-/

@[expose] public section

namespace VG

/-- `c` with each call replaced by the code it calls, that code's calls
inlined. -/
def Code.inlineD {I C : Type} : Code I C → Code I C
  | .block l => .block l
  | .seq a b => .seq a.inlineD b.inlineD
  | .ite c t e => .ite c t.inlineD e.inlineD
  | .loop b c => .loop b.inlineD c
  | .call _ b => b.inline
  | .frame i b j => .frame i b.inlineD j
  | .icall i n b nx => .icall i n b nx

end VG

namespace VG.X86_64

/-! ## The code a call may run -/

/-- Code a function called by inlined code may have: instructions that
neither read nor write `rsp`, no frames, and calls of functions that call
nothing and have only such instructions. Only the kernel evaluates it. -/
noncomputable def _root_.VG.Code.CalleeOk : Prog isa → Bool
  | .block l => KList.all l Instr.rspFree
  | .seq a b => a.CalleeOk && b.CalleeOk
  | .ite _ t e => t.CalleeOk && e.CalleeOk
  | .loop b _ => b.CalleeOk
  | .call _ b => b.noCalls && b.allInstrs Instr.rspFree
  | .frame .. => false
  | .icall .. => false

/-- Code whose calls can be inlined, their own calls too: no instruction
outside a call writes `rsp`, there are no frames, and each function called
is `CalleeOk`. Only the kernel evaluates it. -/
noncomputable def _root_.VG.Code.InlineOkD : Prog isa → Bool
  | .block l => KList.all l fun i => !Taint.clobbers i .rsp
  | .seq a b => a.InlineOkD && b.InlineOkD
  | .ite _ t e => t.InlineOkD && e.InlineOkD
  | .loop b _ => b.InlineOkD
  | .call _ b => b.CalleeOk
  | .frame .. => false
  | .icall .. => false

/-- A function a call may run can itself be inlined. -/
theorem _root_.VG.Code.inlineOk_of_calleeOk {c : Prog isa} (h : c.CalleeOk = true) : c.InlineOk = true := by
  induction c with
  | block l =>
    simp only [Code.CalleeOk, KList.all_eq, List.all_eq_true] at h
    simp only [Code.InlineOk, KList.all_eq, List.all_eq_true, Bool.not_eq_true']
    exact fun i hi => Instr.clobbers_rsp_of_rspFree (h i hi)
  | seq a b iha ihb =>
    simp only [Code.CalleeOk, Bool.and_eq_true] at h
    simp only [Code.InlineOk, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [Code.CalleeOk, Bool.and_eq_true] at h
    simp only [Code.InlineOk, Bool.and_eq_true]
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih =>
    simp only [Code.CalleeOk] at h
    exact ih h
  | call _ b _ => exact h
  | frame => simp only [Code.CalleeOk, Bool.false_eq_true] at h
  | icall => simp only [Code.CalleeOk, Bool.false_eq_true] at h

/-- Every instruction of such a function inlined neither reads nor writes `rsp`. -/
theorem _root_.VG.Code.rspFree_inline_of_calleeOk {c : Prog isa} (h : c.CalleeOk = true) :
    ∀ i ∈ instrs c.inline, i.rspFree = true := by
  induction c with
  | block l =>
    simp only [Code.CalleeOk, KList.all_eq, List.all_eq_true] at h
    exact h
  | seq a b iha ihb =>
    simp only [Code.CalleeOk, Bool.and_eq_true] at h
    simp only [Code.inline, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.CalleeOk, Bool.and_eq_true] at h
    simp only [Code.inline, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih =>
    simp only [Code.CalleeOk] at h
    exact ih h
  | call _ b _ =>
    simp only [Code.CalleeOk, Bool.and_eq_true, Code.allInstrs_eq, List.all_eq_true] at h
    exact h.2
  | frame => simp only [Code.CalleeOk, Bool.false_eq_true] at h
  | icall => simp only [Code.CalleeOk, Bool.false_eq_true] at h

/-- Code with calls of functions that call nothing is `InlineOkD`. -/
theorem _root_.VG.Code.calleeOk_of_leaf {c : Prog isa} (hn : c.noCalls = true)
    (hr : c.allInstrs Instr.rspFree = true) : c.CalleeOk = true := by
  induction c with
  | block l =>
    simp only [Code.allInstrs_eq, instrs, List.all_eq_true] at hr
    simp only [Code.CalleeOk, KList.all_eq, List.all_eq_true]
    exact hr
  | seq a b iha ihb =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    simp only [Code.allInstrs_eq, instrs, List.all_append, Bool.and_eq_true] at hr
    simp only [Code.CalleeOk, Bool.and_eq_true]
    exact ⟨iha hn.1 (by rw [Code.allInstrs_eq]; exact hr.1), ihb hn.2 (by rw [Code.allInstrs_eq]; exact hr.2)⟩
  | ite _ t e iht ihe =>
    simp only [Code.noCalls, Bool.and_eq_true] at hn
    simp only [Code.allInstrs_eq, instrs, List.all_append, Bool.and_eq_true] at hr
    simp only [Code.CalleeOk, Bool.and_eq_true]
    exact ⟨iht hn.1 (by rw [Code.allInstrs_eq]; exact hr.1), ihe hn.2 (by rw [Code.allInstrs_eq]; exact hr.2)⟩
  | loop b _ ih =>
    simp only [Code.noCalls] at hn
    exact ih hn hr
  | call => simp only [Code.noCalls, Bool.false_eq_true] at hn
  | frame => simp only [Code.noCalls, Bool.false_eq_true] at hn
  | icall => simp only [Code.noCalls, Bool.false_eq_true] at hn

/-- `InlineOk` code is `InlineOkD`, and its two inlined forms are one. -/
theorem _root_.VG.Code.inlineOkD_of_inlineOk {c : Prog isa} (h : c.InlineOk = true) :
    c.InlineOkD = true ∧ c.inlineD = c.inline := by
  induction c with
  | block _ => exact ⟨h, rfl⟩
  | seq a b iha ihb =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    obtain ⟨a1, a2⟩ := iha h.1
    obtain ⟨b1, b2⟩ := ihb h.2
    exact ⟨by simp only [Code.InlineOkD, a1, b1, Bool.and_self], by simp only [Code.inlineD, Code.inline, a2, b2]⟩
  | ite _ t e iht ihe =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    obtain ⟨t1, t2⟩ := iht h.1
    obtain ⟨e1, e2⟩ := ihe h.2
    exact ⟨by simp only [Code.InlineOkD, t1, e1, Bool.and_self], by simp only [Code.inlineD, Code.inline, t2, e2]⟩
  | loop b _ ih =>
    simp only [Code.InlineOk] at h
    obtain ⟨b1, b2⟩ := ih h
    exact ⟨b1, by simp only [Code.inlineD, Code.inline, b2]⟩
  | call _ b _ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    exact ⟨Code.calleeOk_of_leaf h.1 h.2, by simp only [Code.inlineD, Code.inline, Code.inline_of_noCalls h.1]⟩
  | frame => simp only [Code.InlineOk, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOk, Bool.false_eq_true] at h

/-- Inlined code whose calls' calls call none calls none. -/
theorem _root_.VG.Code.noCalls_inlineD {c : Prog isa} (h : c.InlineOkD = true) : c.inlineD.noCalls = true := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at h
    simp only [Code.inlineD, Code.noCalls, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at h
    simp only [Code.inlineD, Code.noCalls, Bool.and_eq_true]
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih =>
    simp only [Code.InlineOkD] at h
    simp only [Code.inlineD, Code.noCalls]
    exact ih h
  | call _ b _ =>
    simp only [Code.InlineOkD] at h
    exact Code.noCalls_inline (Code.inlineOk_of_calleeOk h)
  | frame => simp only [Code.InlineOkD, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOkD, Bool.false_eq_true] at h

/-- No instruction of inlined code writes `rsp`. -/
theorem _root_.VG.Code.clobbers_rsp_of_inlineOkD {c : Prog isa} (h : c.InlineOkD = true) :
    ∀ i ∈ instrs c.inlineD, Taint.clobbers i .rsp = false := by
  induction c with
  | block l =>
    simp only [Code.InlineOkD, KList.all_eq, List.all_eq_true, Bool.not_eq_true'] at h
    exact h
  | seq a b iha ihb =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at h
    simp only [Code.inlineD, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at h
    simp only [Code.inlineD, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih =>
    simp only [Code.InlineOkD] at h
    exact ih h
  | call _ b _ =>
    simp only [Code.InlineOkD] at h
    exact fun i hi => Instr.clobbers_rsp_of_rspFree (Code.rspFree_inline_of_calleeOk h i hi)
  | frame => simp only [Code.InlineOkD, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOkD, Bool.false_eq_true] at h

/-! ## The two return addresses -/

theorem sub_sub_add (x y z : BitVec 64) : x - (y - z) = x - y + z := by
  rw [BitVec.sub_eq_add_neg x (y - z), BitVec.neg_sub, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]

/-- The return addresses a call from `sp`, and a call from that call, store. -/
def hole2 (sp : Addr) : Region := ⟨sp - 16, 16⟩

theorem hole2_contains {sp x : Addr} : (hole2 sp).Contains x 1 ↔ (x - (sp - 16)).toNat < 16 := by
  simp only [hole2, Region.Contains]; omega_arith

/-- The upper 8 bytes of `hole2 sp` are the hole of a call from `sp`. -/
theorem hole2_of_hole {sp x : Addr} (h : (hole sp).Contains x 1) : (hole2 sp).Contains x 1 := by
  rw [hole_contains] at h
  rw [hole2_contains]
  have e : x - (sp - 16) = (x - (sp - 8)) + 8 := by
    rw [show sp - 16 = (sp - 8) - 8 from by rw [BitVec.sub_sub]; rfl]
    exact sub_sub_add _ _ _
  rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  omega_arith

/-- The lower 8 bytes of `hole2 sp` are the hole of a call from `sp - 8`. -/
theorem hole2_of_hole8 {sp x : Addr} (h : (hole (sp - 8)).Contains x 1) : (hole2 sp).Contains x 1 := by
  rw [hole_contains] at h
  rw [hole2_contains, show sp - 16 = (sp - 8) - 8 from by rw [BitVec.sub_sub]; rfl]
  omega_arith

/-- A byte of `hole2 sp` is in one of the two holes. -/
theorem hole_or_hole8 {sp x : Addr} (h : (hole2 sp).Contains x 1) :
    (hole sp).Contains x 1 ∨ (hole (sp - 8)).Contains x 1 := by
  rw [hole2_contains] at h
  rw [hole_contains, hole_contains]
  by_cases h8 : (x - (sp - 16)).toNat < 8
  · right; rw [show sp - 16 = (sp - 8) - 8 from by rw [BitVec.sub_sub]; rfl] at h8; exact h8
  · left
    have e : x - (sp - 16) = (x - (sp - 8)) + 8 := by
      rw [show sp - 16 = (sp - 8) - 8 from by rw [BitVec.sub_sub]; rfl]
      exact sub_sub_add _ _ _
    rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl] at h h8
    omega_arith

theorem Clear.of_hole2 {sp : Addr} {s : State} (h : Clear (hole2 sp) s) : Clear (hole sp) s :=
  fun r hr a ha hb => h r hr a ha (hole2_of_hole hb)

theorem Clear.of_hole2_8 {sp : Addr} {s : State} (h : Clear (hole2 sp) s) : Clear (hole (sp - 8)) s :=
  fun r hr a ha hb => h r hr a ha (hole2_of_hole8 hb)

theorem overlay_hole2_writeW (sp : Addr) (hv m : Mem) (v : BitVec 64) :
    (overlay (hole2 sp) hv m).writeW (sp - 8) v = overlay (hole2 sp) (hv.writeW (sp - 8) v) m := by
  funext x
  simp only [Mem.writeW, Mem.write, overlay]
  split
  · rename_i hx
    have : (hole2 sp).Contains x 1 := hole2_of_hole (by rw [hole_contains]; exact hx)
    simp only [this, ite_true]
  · rfl

/-- Patching the hole of a call from `sp - 8` over a patch of the hole of a
call from `sp` patches `hole2 sp`. -/
theorem overlay_hole8_hole (sp : Addr) (hv hv' m : Mem) :
    overlay (hole (sp - 8)) hv' (overlay (hole sp) hv m) =
      overlay (hole2 sp) (overlay (hole (sp - 8)) hv' hv) m := by
  funext x
  simp only [overlay]
  by_cases h8 : (hole (sp - 8)).Contains x 1
  · simp only [h8, ite_true, hole2_of_hole8 h8]
  · by_cases h0 : (hole sp).Contains x 1
    · simp only [h8, h0, ite_true, ite_false, hole2_of_hole h0]
    · have h2 : ¬ (hole2 sp).Contains x 1 := fun h => (hole_or_hole8 h).elim h0 h8
      simp only [h8, h0, h2, ite_false]

theorem State.patch_setRsp (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) (x : BitVec 64) :
    (s.setReg .rsp x).patch H hv u = (s.patch H hv u).setReg .rsp x := rfl

theorem State.patch_patch (H H' : Region) (hv hv' : Mem) (u u' : Nat → BitVec 64) (s : State) :
    (s.patch H hv u).patch H' hv' u' = { s with mem := overlay H' hv' (overlay H hv s.mem), unknowns := u' } :=
  rfl

/-! ## The leakage -/

/-- The leakage of a run of `c`, from that of `c.inlineD` (a prefix of
`t`): each call adds the address of its return address `h` before and after
the leakage of the code it calls, which `liftT` gives from that code's
inlined leakage with its calls' return address `h₂`. With `f` steps of
fuel; with the remainder of `t`. -/
def liftTD (h h₂ : Addr) : Nat → Prog isa → List Leak → Option (List Leak × List Leak)
  | 0, _, _ => none
  | _ + 1, .block l, t => if blockLen l ≤ t.length then some (t.take (blockLen l), t.drop (blockLen l)) else none
  | f + 1, .seq a b, t => (liftTD h h₂ f a t).bind fun (p : List Leak × List Leak) =>
      (liftTD h h₂ f b p.2).map fun (q : List Leak × List Leak) => (p.1 ++ q.1, q.2)
  | f + 1, .ite _ th _, .branch true :: t =>
      (liftTD h h₂ f th t).map fun (p : List Leak × List Leak) => (.branch true :: p.1, p.2)
  | f + 1, .ite _ _ el, .branch false :: t =>
      (liftTD h h₂ f el t).map fun (p : List Leak × List Leak) => (.branch false :: p.1, p.2)
  | _ + 1, .ite .., _ => none
  | f + 1, .loop b c, t => (liftTD h h₂ f b t).bind fun (p : List Leak × List Leak) => match p.2 with
      | .branch false :: r => some (p.1 ++ [.branch false], r)
      | .branch true :: r => (liftTD h h₂ f (.loop b c) r).map fun (q : List Leak × List Leak) =>
          (p.1 ++ .branch true :: q.1, q.2)
      | _ => none
  | f + 1, .call _ b, t => (liftT h₂ f b t).map fun (p : List Leak × List Leak) => (.addr h :: (p.1 ++ [.addr h]), p.2)
  | _ + 1, .frame .., _ => none
  | _ + 1, .icall .., _ => none

/-- `ta` is the leakage `liftTD` gives for `t`, with enough fuel, whatever follows. -/
def LiftsD (h h₂ : Addr) (c : Prog isa) (ta t : List Leak) : Prop :=
  ∃ N, ∀ f, N ≤ f → ∀ r, liftTD h h₂ f c (t ++ r) = some (ta, r)

theorem LiftsD.unique {h h₂ : Addr} {c : Prog isa} {ta₁ ta₂ t : List Leak} (h₁ : LiftsD h h₂ c ta₁ t)
    (h₂' : LiftsD h h₂ c ta₂ t) : ta₁ = ta₂ := by
  obtain ⟨N₁, l₁⟩ := h₁
  obtain ⟨N₂, l₂⟩ := h₂'
  have := (l₁ (max N₁ N₂) (by omega_arith) []).symm.trans (l₂ (max N₁ N₂) (by omega_arith) [])
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

theorem Exec.liftsD_self (h h₂ : Addr) {c : Prog isa} (hc : c.noCalls = true) {s s' : State} {t : List Leak}
    (e : Exec isa c s t s') : LiftsD h h₂ c t t := by
  induction e with
  | block e =>
    refine ⟨1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    have hl := execBlock_length e
    simp only [liftTD, List.length_append, hl, Nat.le_add_right, ite_true, List.take_left', List.drop_left']
  | @seq c₁ c₂ _ _ _ t₁ t₂ _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N₁, h₁⟩ := ih₁ hc.1
    obtain ⟨N₂, h₂⟩ := ih₂ hc.2
    refine ⟨max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, h₁ f (by omega_arith) (t₂ ++ r), Option.bind_some,
      h₂ f (by omega_arith) r, Option.map_some]
  | @iteT _ _ _ _ _ t _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N, h₁⟩ := ih hc.1
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.cons_append, h₁ f (by omega_arith) r, Option.map_some]
  | @iteF _ _ _ _ _ t _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N, h₁⟩ := ih hc.2
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.cons_append, h₁ f (by omega_arith) r, Option.map_some]
  | @loopExit _ _ _ _ t _ _ ih =>
    obtain ⟨N, h₁⟩ := ih hc
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, List.cons_append, List.nil_append, h₁ f (by omega_arith), Option.bind_some]
  | @loopNext _ _ _ _ _ t t' _ _ _ ih₁ ih₂ =>
    obtain ⟨N₁, h₁⟩ := ih₁ hc
    obtain ⟨N₂, h₂⟩ := ih₂ hc
    refine ⟨max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, List.cons_append, h₁ f (by omega_arith), Option.bind_some]
    rw [h₂ f (by omega_arith) r]; rfl
  | call => simp [Code.noCalls] at hc
  | frame => simp [Code.noCalls] at hc
  | icall | icallNext => simp [Code.noCalls] at hc

/-- `Lifts` gives `liftT`'s leakage with enough fuel. -/
theorem Lifts.fuel {h : Addr} {c : Prog isa} {ta t : List Leak} (hl : Lifts h c ta t) :
    ∃ N, ∀ f, N ≤ f → ∀ r, liftT h f c (t ++ r) = some (ta, r) := hl

/-! ## Calls as inlined code -/

theorem loop_uninlineD {body : Prog isa} {k : Cond} {sp : Addr}
    (ih : ∀ {b b' : State} {t : List Leak}, Exec isa body.inlineD b t b' → Clear (hole2 sp) b → b.gpr .rsp = sp →
      ∀ (hv : Mem) (u : Nat → BitVec 64), ∃ hv' u' ta,
        Exec isa body (b.patch (hole2 sp) hv u) ta (b'.patch (hole2 sp) hv' u') ∧ b'.gpr .rsp = sp ∧
          LiftsD (sp - 8) (sp - 16) body ta t)
    {b b' : State} {t : List Leak} (h : Exec isa (.loop body.inlineD k) b t b') (hb : Clear (hole2 sp) b)
    (hsp : b.gpr .rsp = sp) (hv : Mem) (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa (.loop body k) (b.patch (hole2 sp) hv u) ta (b'.patch (hole2 sp) hv' u') ∧
      b'.gpr .rsp = sp ∧ LiftsD (sp - 8) (sp - 16) (.loop body k) ta t := by
  generalize e : (Code.loop body.inlineD k : Prog isa) = L at h
  induction h generalizing hv u with
  | block | seq | iteT | iteF | call | frame | icall | icallNext => cases e
  | @loopExit body' k' s s' t h₁ hk _ =>
    cases e
    obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih h₁ hb hsp hv u
    refine ⟨hv', u', ta ++ [.branch false], .loopExit ha ((eval_patch _).trans hk), hs', N + 1,
      fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, List.cons_append, List.nil_append, hl f (by omega_arith), Option.bind_some]
  | @loopNext body' k' s s₁ s' t t' h₁ hk _ _ ih₂ =>
    cases e
    obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ⟨N₁, hl₁⟩⟩ := ih h₁ hb hsp hv u
    obtain ⟨hv', u', ta₂, ha₂, hs', ⟨N₂, hl₂⟩⟩ := ih₂ (hb.of_exec h₁) hs₁ hv₁ u₁ rfl
    refine ⟨hv', u', ta₁ ++ .branch true :: ta₂, .loopNext ha₁ ((eval_patch _).trans hk) ha₂, hs',
      max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, List.cons_append, hl₁ f (by omega_arith), Option.bind_some]
    rw [hl₂ f (by omega_arith) r]; rfl

/-- A run of `c.inlineD` gives one of `c`, from the same state but for the
16 bytes below `rsp` and the unknowns, to the same state but for those,
with the leakage `liftTD` gives. -/
theorem Exec.uninlineD {c : Prog isa} (hc : c.InlineOkD = true) {sp : Addr} {b b' : State} {t : List Leak}
    (h : Exec isa c.inlineD b t b') (hb : Clear (hole2 sp) b) (hsp : b.gpr .rsp = sp) (hv : Mem)
    (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa c (b.patch (hole2 sp) hv u) ta (b'.patch (hole2 sp) hv' u') ∧ b'.gpr .rsp = sp ∧
      LiftsD (sp - 8) (sp - 16) c ta t := by
  induction c generalizing b b' t hv u with
  | icall => simp only [Code.InlineOkD, Bool.false_eq_true] at hc
  | block l =>
    simp only [Code.inlineD] at h
    simp only [Code.InlineOkD, KList.all_eq, List.all_eq_true, Bool.not_eq_true'] at hc
    refine ⟨hv, u, t, Exec.F (H := hole2 sp) rfl (fun i _ s hs => ⟨exec_patch hs i, addrs_patch i⟩)
      (fun k _ => eval_patch k) h hb, ?_, Exec.liftsD_self _ _ rfl h⟩
    rw [Exec.gpr (c := .block l) (fun i hi => hc i hi) h, hsp]
  | seq a c ih₁ ih₂ =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at hc
    simp only [Code.inlineD] at h
    obtain ⟨t₁, t₂, s₁, h₁, h₂, rfl⟩ := Exec.seq_inv h
    obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ⟨N₁, hl₁⟩⟩ := ih₁ hc.1 h₁ hb hsp hv u
    obtain ⟨hv', u', ta₂, ha₂, hs', ⟨N₂, hl₂⟩⟩ := ih₂ hc.2 h₂ (hb.of_exec h₁) hs₁ hv₁ u₁
    refine ⟨hv', u', ta₁ ++ ta₂, .seq ha₁ ha₂, hs', max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, List.append_assoc, hl₁ f (by omega_arith), Option.bind_some, hl₂ f (by omega_arith) r,
      Option.map_some]
  | ite k th el ih₁ ih₂ =>
    simp only [Code.InlineOkD, Bool.and_eq_true] at hc
    simp only [Code.inlineD] at h
    rcases Exec.ite_inv h with ⟨t, rfl, hk, h₁⟩ | ⟨t, rfl, hk, h₁⟩
    · obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih₁ hc.1 h₁ hb hsp hv u
      refine ⟨hv', u', .branch true :: ta, .iteT ((eval_patch _).trans hk) ha, hs', N + 1, fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftTD, List.cons_append, hl f (by omega_arith) r, Option.map_some]
    · obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih₂ hc.2 h₁ hb hsp hv u
      refine ⟨hv', u', .branch false :: ta, .iteF ((eval_patch _).trans hk) ha, hs', N + 1,
        fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftTD, List.cons_append, hl f (by omega_arith) r, Option.map_some]
  | loop body k ih =>
    simp only [Code.InlineOkD] at hc
    simp only [Code.inlineD] at h
    exact loop_uninlineD (fun h₁ hb₁ hsp₁ hv₁ u₁ => ih hc h₁ hb₁ hsp₁ hv₁ u₁) h hb hsp hv u
  | call n body _ =>
    simp only [Code.InlineOkD] at hc
    simp only [Code.inlineD] at h
    have hn := Code.noCalls_inline (Code.inlineOk_of_calleeOk hc)
    have hr' := Code.rspFree_inline_of_calleeOk hc
    have hrsp : b'.gpr .rsp = sp := by
      rw [Exec.gpr (fun i hi => Instr.clobbers_rsp_of_rspFree (hr' i hi)) h, hsp]
    -- After the call: `rsp` 8 lower and the return address in the hole.
    let hv₁ : Mem := hv.writeW (sp - 8) (u 0)
    let u₁ : Nat → BitVec 64 := fun n => u (n + 1)
    let F : State → State := fun s => (s.patch (hole sp) hv₁ u₁).setReg .rsp (sp - 8)
    have hcall : isa.call (b.patch (hole2 sp) hv u) = some ((b.patch (hole2 sp) hv₁ u₁).setReg .rsp (sp - 8)) := by
      simp only [isa, call, State.patch_gpr, hsp, hv₁, u₁]
      congr 1
      simp only [State.patch, State.setReg, ← overlay_hole2_writeW]
    -- The code it calls, inlined, runs with the return address in place.
    have hF : Exec isa body.inline (F b) t (F b') :=
      Exec.F (H := hole sp) hn (fun i hi s hs => ⟨by
          have hi' := hr' i hi
          simp only [F]; rw [exec_setRsp hi', exec_patch hs, Option.map_map]; rfl,
        by simp only [F]; rw [addrs_setRsp (hr' i hi), addrs_patch]⟩)
        (fun k s => by simp only [F]; rw [eval_setRsp, eval_patch]) h hb.of_hole2
    have hF0 : (F b).gpr .rsp = sp - 8 := by simp [F, State.setReg]
    have hFc : Clear (hole (sp - 8)) (F b) := hb.of_hole2_8
    -- The code it calls, from 8 below.
    obtain ⟨hv₂, u₂, ta, hbody, hrsp₂, hl⟩ :=
      Exec.uninline (Code.inlineOk_of_calleeOk hc) hF hFc hF0 hv₁ u₁
    have hentry : (F b).patch (hole (sp - 8)) hv₁ u₁ = (b.patch (hole2 sp) hv₁ u₁).setReg .rsp (sp - 8) := by
      simp only [F, ← State.patch_setRsp, State.patch_patch]
      simp only [State.patch, State.setReg, overlay_hole8_hole]
      congr 2
      funext x
      simp only [overlay]
      split <;> rfl
    rw [hentry] at hbody
    have g₂ : ((F b').patch (hole (sp - 8)) hv₂ u₂).gpr .rsp = sp - 8 := by
      simp [F, State.setReg]
    have m₂ : ((F b').patch (hole (sp - 8)) hv₂ u₂).mem.readW (sp - 8) 64 = hv₁.readW (sp - 8) 64 := by
      simp only [F, State.patch, State.setReg]
      rw [overlay_readW (by decide) fun x hx hh => ?_]
      · exact overlay_hole_readW sp hv₁ b'.mem
      · rw [hole_contains] at hh
        have : (x - (sp - 8 - 8)).toNat = (x - (sp - 8)).toNat + 8 := by
          have e : x - (sp - 8 - 8) = (x - (sp - 8)) + 8 := by
            exact sub_sub_add _ _ _
          rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
          omega_arith
        omega_arith
    have m₁ : ((b.patch (hole2 sp) hv₁ u₁).setReg .rsp (sp - 8)).mem.readW (sp - 8) 64 = hv₁.readW (sp - 8) 64 := by
      simp only [State.patch, State.setReg]
      exact Mem.readW_congr fun i hi => by
        have : (hole2 sp).Contains (sp - 8 + BitVec.ofNat 64 i) 1 := hole2_of_hole (by
          rw [hole_contains, Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
        simp only [overlay, this, ite_true]
    let hv' : Mem := overlay (hole (sp - 8)) hv₂ hv₁
    have hret : isa.ret ((b.patch (hole2 sp) hv₁ u₁).setReg .rsp (sp - 8)) ((F b').patch (hole (sp - 8)) hv₂ u₂) =
        some (b'.patch (hole2 sp) hv' u₂) := by
      have g₁ : ((b.patch (hole2 sp) hv₁ u₁).setReg .rsp (sp - 8)).gpr .rsp = sp - 8 := by
        simp [State.setReg]
      simp only [isa, ret, g₁, g₂, m₁, m₂, and_self, ite_true, Option.some.injEq, BitVec.sub_add_cancel]
      simp only [F, ← State.patch_setRsp, State.patch_patch, hv']
      simp only [State.patch, State.setReg, overlay_hole8_hole]
      rw [← hrsp]
      congr 1
      funext r
      split <;> simp_all
    refine ⟨hv', u₂, _, .call hcall hbody hret, hrsp, ?_⟩
    obtain ⟨N, hl'⟩ := hl
    rw [show sp - 8 - 8 = sp - 16 from by rw [BitVec.sub_sub]; rfl] at hl'
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTD, hl' f (by omega_arith) r, Option.map_some, State.patch_gpr, hsp, g₂, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append]
  | frame => simp [Code.InlineOkD] at hc

/-- A run of `c.inlineD` from `s` gives one of `c` from `s`. -/
theorem Exec.of_inlineD {c : Prog isa} (hc : c.InlineOkD = true) {s s' : State} {t : List Leak}
    (h : Exec isa c.inlineD s t s') (hs : Clear (hole2 (s.gpr .rsp)) s) :
    ∃ hv u ta, Exec isa c s ta (s'.patch (hole2 (s.gpr .rsp)) hv u) ∧ s'.gpr .rsp = s.gpr .rsp ∧
      LiftsD (s.gpr .rsp - 8) (s.gpr .rsp - 16) c ta t := by
  obtain ⟨hv, u, ta, he, hr, hl⟩ := Exec.uninlineD hc h hs rfl s.mem s.unknowns
  rw [State.patch_self] at he
  exact ⟨hv, u, ta, he, hr, hl⟩

/-- `c` is constant time if `c.inlineD` is, and runs from every state its
precondition allows. -/
theorem ConstantTime.of_inlineD {c : Prog isa} (hc : c.InlineOkD = true) {P : State → Prop}
    {Pub : State → State → Prop} (hrun : ∀ s, P s → ∃ t s', Exec isa c.inlineD s t s')
    (hclear : ∀ s, P s → Clear (hole2 (s.gpr .rsp)) s)
    (hpub : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa P Pub c.inlineD) : ConstantTime isa P Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨tb₁, b₁, f₁⟩ := hrun s₁ p₁
  obtain ⟨tb₂, b₂, f₂⟩ := hrun s₂ p₂
  obtain ⟨_, _, ta₁, a₁, _, l₁⟩ := Exec.of_inlineD hc f₁ (hclear s₁ p₁)
  obtain ⟨_, _, ta₂, a₂, _, l₂⟩ := Exec.of_inlineD hc f₂ (hclear s₂ p₂)
  obtain ⟨rfl, -⟩ := Exec.det e₁ a₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ a₂
  have ht := hct s₁ s₂ tb₁ tb₂ b₁ b₂ p₁ p₂ hp f₁ f₂
  subst ht
  rw [hpub s₁ s₂ p₁ p₂ hp] at l₁
  exact l₁.unique l₂

/-- The calling convention's obligations hold of the run of `c` if they do of `c.inlineD`'s. -/
theorem abiPreserved_patch2 {s b : State} (hv : Mem) (u : Nat → BitVec 64) (h : abiPreserved s b) :
    abiPreserved s (b.patch (hole2 (s.gpr .rsp)) hv u) := by
  refine ⟨h.1, ?_, h.2.2⟩
  rw [State.patch_readW (by decide) fun x hx hh => ?_]
  · exact h.2.1
  · rcases hole_or_hole8 hh with hh | hh
    · exact not_hole_of_above hx hh
    · rw [hole_contains] at hh
      have e : x - (s.gpr .rsp - 8 - 8) = (x - s.gpr .rsp) + 16 := by
        rw [BitVec.sub_sub, sub_sub_add]; rfl
      rw [e, BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl] at hh
      omega_arith

/-! ## Contracts -/

/-- `k`, with no buffer on the 16 bytes below `rsp`: what a caller of code
whose calls call must also give it. -/
def _root_.VG.Contract.clear2 (k : Contract isa) : Contract isa :=
  { k with pre := fun s => k.pre s ∧ Clear (hole2 (s.gpr .rsp)) s }

/-- A contract built by `Sig.contract` with `stack` at least 16 keeps every
buffer and argument area away from the 16 bytes below `rsp`. -/
theorem Sig.clear2_of_pre {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract abi pre post wa 16 leak).pre s) : Clear (hole2 (s.gpr .rsp)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨_, hrd, hwr, _, hres, _⟩ := h
    intro r hr
    have hh : (hole2 (s.gpr .rsp)) ∈ abi.reserved 16 s := by
      simp [abi, stackBelow, hole2]
    rcases List.mem_append.mp hr with hr | hr
    · rw [show s.rd = abi.rd s from rfl, hrd] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm
    · rw [show s.wr = abi.wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

/-- Correctness of `c` from that of `c.inlineD`, for a postcondition that
does not read the 16 bytes below `rsp`. -/
theorem ok_of_inlineD {c : Prog isa} (hc : c.InlineOkD = true) {k : Contract isa}
    (hcor : ∀ s, k.pre s → ∃ t s', Exec isa c.inlineD s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hpost : ∀ s b hv u, k.pre s → Clear (hole2 (s.gpr .rsp)) s → k.post s b →
      k.post s (b.patch (hole2 (s.gpr .rsp)) hv u)) :
    ∀ s, k.clear2.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s' := by
  intro s ⟨hs, hcl⟩
  obtain ⟨t, b, he, ha, hp⟩ := hcor s hs
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inlineD hc he hcl
  exact ⟨ta, _, ha', abiPreserved_patch2 hv u ha, hpost s b hv u hs hcl hp⟩

/-- Constant time of `c` from that of `c.inlineD`, for a relation that fixes `rsp`. -/
theorem ct_of_inlineD {c : Prog isa} (hc : c.InlineOkD = true) {k : Contract isa}
    (hrun : ∀ s, k.pre s → ∃ t s', Exec isa c.inlineD s t s')
    (hrsp : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa k.pre k.pub c.inlineD) : ConstantTime isa k.clear2.pre k.pub c :=
  ConstantTime.of_inlineD hc (fun s h => hrun s h.1) (fun _ h => h.2) (fun _ _ _ _ h => hrsp _ _ h)
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => hct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

/-- `c` is verified against `k` if `c.inlineD` is correct and constant time
against a contract `k₀` that `k` implies, `k₀`'s postcondition does not read
the 16 bytes below `rsp`, and `k` keeps every buffer away from them. -/
theorem Verified.of_inlineD {c : Prog isa} (hc : c.InlineOkD = true) {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inlineD s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inlineD) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (hole2 (s.gpr .rsp)) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (hole2 (s.gpr .rsp)) hv u))
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp) : Verified target c k := by
  refine ⟨fun s hs => ?_, ?_, himp.sat⟩
  · obtain ⟨t, b, he, ha, hp⟩ := hcor s (himp.pre s hs)
    obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inlineD hc he (hclear s hs)
    exact ⟨ta, _, ha', abiPreserved_patch2 hv u ha, himp.post s _ hs (hpost s b hv u hs hp)⟩
  · refine ConstantTime.of_inlineD hc (fun s hs => ?_) hclear hrsp fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      hct s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂
    obtain ⟨t, b, he, -, -⟩ := hcor s (himp.pre s hs)
    exact ⟨t, b, he⟩

end VG.X86_64
