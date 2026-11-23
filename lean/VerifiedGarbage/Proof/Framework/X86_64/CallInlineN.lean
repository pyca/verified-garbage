module

public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Calls at any depth, as inlined code (x86-64)

`Code.InlineOk` (`CallInline.lean`) lets code call only functions that call
nothing. Here a function the code calls may call functions in turn, to any
depth `d` (`Code.InlineOkN d`): `Code.inlineAll c` is `c` with every call,
at every depth, replaced by the code it calls. Code whose proofs say that
memory changes only where they name (and nothing of the `8 d` bytes below
`rsp`, `holeN`, where the calls' return addresses go, which no buffer
overlaps) is proved for its inlined form; this file moves the proof to `c`:

* a run of `c.inlineAll` gives a run of `c`, whose final state is that of
  `c.inlineAll` but for the `8 d` bytes below `rsp` and the unknowns the calls
  consume (`Exec.of_inlineAll`);
* the run's leakage is a function of the inlined run's (`liftTN`), so `c` is
  constant time if `c.inlineAll` is (`ConstantTime.of_inlineAll`).

Inside `k` calls, `rsp` is `8 k` lower than in the inlined run (`NestState`), and
the return address of the `k`-th is in the `k`-th 8 bytes below the entry's
`rsp`. The code a call runs neither reads nor writes `rsp`
(`Instr.rspFree`), so it runs there as in the inlined run; the calls it makes
write only the return addresses below its own (`RetsKept`), so its return
address is where its call stored it when it returns (`Exec.uninlineN`).
One level of calls is the case `d = 1` (`inlineOkN_of_inlineOk`).

At its top level, `c` may also call a function indirectly, by `callm` of a
slot `[rsp + disp]` (`Code.icall` of one function, `icallSlot`), where
`(disp, n)` is one of `slots` (`Code.InlineOkNS`): inlined, that is the code of
`n`. The run of `c` calls `n` if the slot holds its address, and no region
`c` may write overlaps the slot (`SlotsOk`), which inlined code then keeps. The
call's leakage adds the slot's address and `n`'s (`liftTN`'s `F`), so `c` is
constant time if two runs agree on the addresses of the slots' functions
(`ConstantTime.of_inlineAllS`). With no slots, the theorems are those above.
-/

@[expose] public section

namespace VG

/-- `c` with every call, at every depth, replaced by the code it calls. -/
def Code.inlineAll {I C : Type} : Code I C → Code I C
  | .block l => .block l
  | .seq a b => .seq a.inlineAll b.inlineAll
  | .ite c t e => .ite c t.inlineAll e.inlineAll
  | .loop b c => .loop b.inlineAll c
  | .call _ b => b.inlineAll
  | .frame i b j => .frame i b.inlineAll j
  | .icall i n b nx => match nx with
    | .block [] => b.inlineAll
    | nx => .icall i n b nx

end VG

namespace VG.X86_64

/-! ## The code that can be inlined -/

/-- An indirect call by `i` of `n` is one through `[rsp + disp]` for a slot
`(disp, n)` of `slots`. -/
def icallSlot (slots : List (Int × String)) (i : Instr) (n : String) : Bool :=
  match i with
  | .callm m => m.base == .rsp && m.index.isNone && slots.contains (m.disp, n)
  | _ => false

theorem icallSlot_spec {slots : List (Int × String)} {i : Instr} {n : String} (h : icallSlot slots i n = true) :
    ∃ m, i = .callm m ∧ m.base = .rsp ∧ m.index = none ∧ (m.disp, n) ∈ slots := by
  unfold icallSlot at h
  split at h
  · rename_i m
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, List.contains_iff_mem] at h
    exact ⟨m, rfl, h.1.1, h.1.2, h.2⟩
  · exact absurd h (by simp)

/-- Code whose calls can be inlined, with calls nested at most `d` deep: no
instruction writes `rsp` (and inside a call, `inner`, none reads it either),
there are no frames, and the code each call runs calls at most `d - 1`
deep. An indirect call of one function at the top level is one through a
slot of `slots` (`icallSlot`), whose function's code calls at most `d - 1`
deep. Only the kernel evaluates it. -/
noncomputable def _root_.VG.Code.OkN (slots : List (Int × String)) : Nat → Bool → Prog isa → Bool
  | _, inner, .block l => KList.all l fun i => if inner then i.rspFree else !Taint.clobbers i .rsp
  | d, inner, .seq a b => a.OkN slots d inner && b.OkN slots d inner
  | d, inner, .ite _ t e => t.OkN slots d inner && e.OkN slots d inner
  | d, inner, .loop b _ => b.OkN slots d inner
  | 0, _, .call .. => false
  | d + 1, _, .call _ b => b.OkN slots d true
  | _, _, .frame .. => false
  | d + 1, false, .icall i n b (.block []) => icallSlot slots i n && b.OkN slots d true
  | _, _, .icall .. => false

/-- Code whose calls can be inlined, nested at most `d` deep. -/
noncomputable abbrev _root_.VG.Code.InlineOkN (d : Nat) (c : Prog isa) : Bool := c.OkN [] d false

/-- Code whose calls can be inlined, nested at most `d` deep, with
indirect calls through the slots `slots` at its top level. -/
noncomputable abbrev _root_.VG.Code.InlineOkNS (slots : List (Int × String)) (d : Nat) (c : Prog isa) : Bool :=
  c.OkN slots d false

theorem _root_.VG.Code.OkN_icall {slots : List (Int × String)} {d : Nat} {inner : Bool} {i : Instr} {n : String}
    {b nx : Prog isa} (h : (Code.icall i n b nx : Prog isa).OkN slots d inner = true) :
    ∃ d' m, d = d' + 1 ∧ inner = false ∧ nx = .block [] ∧ i = .callm m ∧ m.base = .rsp ∧ m.index = none ∧
      (m.disp, n) ∈ slots ∧ b.OkN slots d' true = true := by
  rcases d with _ | d' <;> cases inner <;> rcases nx with ⟨_ | ⟨_, _⟩⟩ | _ | _ | _ | _ | _ | _ <;>
    simp [Code.OkN] at h
  obtain ⟨m, rfl, hb, hx, hs⟩ := icallSlot_spec h.1
  exact ⟨d', m, rfl, rfl, rfl, rfl, hb, hx, hs, h.2⟩

/-- Inlined code calls nothing. -/
theorem _root_.VG.Code.noCalls_inlineAll {slots : List (Int × String)} {c : Prog isa} {d : Nat} {inner : Bool}
    (h : c.OkN slots d inner = true) :
    c.inlineAll.noCalls = true := by
  induction c generalizing d inner with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.OkN, Bool.and_eq_true] at h
    simp only [Code.inlineAll, Code.noCalls, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [Code.OkN, Bool.and_eq_true] at h
    simp only [Code.inlineAll, Code.noCalls, Bool.and_eq_true]
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih =>
    simp only [Code.OkN] at h
    simp only [Code.inlineAll, Code.noCalls]
    exact ih h
  | call _ b ih =>
    cases d with
    | zero => simp only [Code.OkN, Bool.false_eq_true] at h
    | succ d => exact ih h
  | frame => cases d <;> simp only [Code.OkN, Bool.false_eq_true] at h
  | icall _ _ b _ ih =>
    obtain ⟨_, _, rfl, rfl, rfl, rfl, -, -, -, hb⟩ := Code.OkN_icall h
    exact ih hb

/-- Every instruction of the code a call runs, inlined, neither reads nor
writes `rsp`; and no instruction of any inlined code writes it. -/
theorem _root_.VG.Code.rsp_inlineAll {slots : List (Int × String)} {c : Prog isa} {d : Nat} {inner : Bool}
    (h : c.OkN slots d inner = true) :
    ∀ i ∈ instrs c.inlineAll, (inner = true → i.rspFree = true) ∧ Taint.clobbers i .rsp = false := by
  induction c generalizing d inner with
  | block l =>
    simp only [Code.OkN, KList.all_eq, List.all_eq_true] at h
    intro i hi
    have := h i hi
    cases inner
    · simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true'] at this
      exact ⟨fun h => absurd h (by decide), this⟩
    · simp only [ite_true] at this
      exact ⟨fun _ => this, Instr.clobbers_rsp_of_rspFree this⟩
  | seq a b iha ihb =>
    simp only [Code.OkN, Bool.and_eq_true] at h
    simp only [Code.inlineAll, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.OkN, Bool.and_eq_true] at h
    simp only [Code.inlineAll, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih =>
    simp only [Code.OkN] at h
    exact ih h
  | call _ b ih =>
    cases d with
    | zero => simp only [Code.OkN, Bool.false_eq_true] at h
    | succ d =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih h i hi
      exact ⟨fun _ => h1 rfl, h2⟩
  | frame => cases d <;> simp only [Code.OkN, Bool.false_eq_true] at h
  | icall _ _ b _ ih =>
    obtain ⟨_, _, rfl, rfl, rfl, rfl, -, -, -, hb⟩ := Code.OkN_icall h
    intro i hi
    obtain ⟨h1, h2⟩ := ih hb i hi
    exact ⟨fun _ => h1 rfl, h2⟩

/-- Code with only calls of functions that call nothing (`InlineOk`) can be
inlined with calls one deep, and its two inlined forms are one. -/
theorem _root_.VG.Code.inlineOkN_of_inlineOk {c : Prog isa} (h : c.InlineOk = true) :
    c.InlineOkN 1 = true ∧ c.inlineAll = c.inline := by
  have leaf : ∀ {b : Prog isa}, b.noCalls = true → b.allInstrs Instr.rspFree = true →
      b.OkN [] 0 true = true ∧ b.inlineAll = b := by
    intro b
    induction b with
    | block l =>
      intro _ hr
      simp only [Code.allInstrs_eq, instrs, List.all_eq_true] at hr
      simp only [Code.OkN, KList.all_eq, List.all_eq_true, ite_true]
      exact ⟨hr, rfl⟩
    | seq a b iha ihb =>
      intro hn hr
      simp only [Code.noCalls, Bool.and_eq_true] at hn
      simp only [Code.allInstrs_eq, instrs, List.all_append, Bool.and_eq_true] at hr
      obtain ⟨a1, a2⟩ := iha hn.1 (by rw [Code.allInstrs_eq]; exact hr.1)
      obtain ⟨b1, b2⟩ := ihb hn.2 (by rw [Code.allInstrs_eq]; exact hr.2)
      exact ⟨by simp only [Code.OkN, a1, b1, Bool.and_self], by simp only [Code.inlineAll, a2, b2]⟩
    | ite _ t e iht ihe =>
      intro hn hr
      simp only [Code.noCalls, Bool.and_eq_true] at hn
      simp only [Code.allInstrs_eq, instrs, List.all_append, Bool.and_eq_true] at hr
      obtain ⟨t1, t2⟩ := iht hn.1 (by rw [Code.allInstrs_eq]; exact hr.1)
      obtain ⟨e1, e2⟩ := ihe hn.2 (by rw [Code.allInstrs_eq]; exact hr.2)
      exact ⟨by simp only [Code.OkN, t1, e1, Bool.and_self], by simp only [Code.inlineAll, t2, e2]⟩
    | loop b _ ih =>
      intro hn hr
      simp only [Code.noCalls] at hn
      obtain ⟨b1, b2⟩ := ih hn hr
      exact ⟨b1, by simp only [Code.inlineAll, b2]⟩
    | call => intro hn; simp only [Code.noCalls, Bool.false_eq_true] at hn
    | frame => intro hn; simp only [Code.noCalls, Bool.false_eq_true] at hn
    | icall => intro hn; simp only [Code.noCalls, Bool.false_eq_true] at hn
  induction c with
  | block _ => exact ⟨h, rfl⟩
  | seq a b iha ihb =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    obtain ⟨a1, a2⟩ := iha h.1
    obtain ⟨b1, b2⟩ := ihb h.2
    exact ⟨by simp only [Code.InlineOkN, Code.OkN] at a1 b1 ⊢; simp only [a1, b1, Bool.and_self],
      by simp only [Code.inlineAll, Code.inline, a2, b2]⟩
  | ite _ t e iht ihe =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    obtain ⟨t1, t2⟩ := iht h.1
    obtain ⟨e1, e2⟩ := ihe h.2
    exact ⟨by simp only [Code.InlineOkN, Code.OkN] at t1 e1 ⊢; simp only [t1, e1, Bool.and_self],
      by simp only [Code.inlineAll, Code.inline, t2, e2]⟩
  | loop b _ ih =>
    simp only [Code.InlineOk] at h
    obtain ⟨b1, b2⟩ := ih h
    exact ⟨b1, by simp only [Code.inlineAll, Code.inline, b2]⟩
  | call _ b _ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    obtain ⟨l1, l2⟩ := leaf h.1 h.2
    exact ⟨l1, by simp only [Code.inlineAll, Code.inline, l2]⟩
  | frame => simp only [Code.InlineOk, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOk, Bool.false_eq_true] at h

/-! ## The return addresses -/

/-- The `n` return addresses below `sp`: the `k`-th call's is the `k`-th
8 bytes below it. -/
def holeN (sp : Addr) (n : Nat) : Region := ⟨sp - BitVec.ofNat 64 (8 * n), 8 * n⟩

/-- Where the `k`-th nested call stores its return address. -/
abbrev retSlot (sp : Addr) (k : Nat) : Addr := sp - BitVec.ofNat 64 (8 * k)

theorem sub_sub_sub_cancel (sp a b : BitVec 64) : (sp - a) - (sp - b) = b - a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub]
  have := sp.isLt; have := a.isLt; have := b.isLt
  omega_arith

theorem toNat_ofNat_sub {a b : Nat} (h : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b - BitVec.ofNat 64 a).toNat = b - a := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem retSlot_succ (sp : Addr) (k : Nat) : retSlot sp k - 8 = retSlot sp (k + 1) := by
  simp only [retSlot, BitVec.sub_sub]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
  omega_arith

theorem retSlot_succ_add (sp : Addr) (k : Nat) : retSlot sp (k + 1) + 8 = retSlot sp k := by
  rw [← retSlot_succ, BitVec.sub_add_cancel]

theorem retSlot_zero (sp : Addr) : retSlot sp 0 = sp := by
  simp only [retSlot, Nat.mul_zero]; exact BitVec.sub_zero _

/-- The offset of a byte in `holeN sp D`, from its base. -/
abbrev offN (sp : Addr) (D : Nat) (x : Addr) : Nat := (x - (sp - BitVec.ofNat 64 (8 * D))).toNat

theorem offN_slotAt {sp : Addr} {D k : Nat} (hk : k ≤ D) (hD : 8 * D < 2 ^ 64) :
    offN sp D (retSlot sp k) = 8 * D - 8 * k := by
  simp only [offN, retSlot, sub_sub_sub_cancel]
  exact toNat_ofNat_sub (by omega_arith) hD

/-- A byte `i` bytes into a slot is that many past the slot's offset. -/
theorem offN_slot_add {sp : Addr} {D k : Nat} (hk : k ≤ D) (hD : 8 * D < 2 ^ 64) {x : Addr}
    (hx : (x - retSlot sp k).toNat < 8) (hk1 : 1 ≤ k) :
    offN sp D x = (8 * D - 8 * k) + (x - retSlot sp k).toNat := by
  have e : x - (sp - BitVec.ofNat 64 (8 * D)) = (x - retSlot sp k) + (retSlot sp k - (sp - BitVec.ofNat 64 (8 * D))) :=
    (Offset.sub_add_sub_cancel _ _ _).symm
  have h₂ := offN_slotAt (sp := sp) hk hD
  simp only [offN] at h₂ ⊢
  rw [e, BitVec.toNat_add, h₂]
  omega_arith

theorem holeN_contains {sp : Addr} {D : Nat} {x : Addr} : (holeN sp D).Contains x 1 ↔ offN sp D x < 8 * D := by
  simp only [holeN, Region.Contains, offN]; omega_arith

/-- What a run of code inside `k` calls leaves of the return addresses:
the bytes of the `k` calls' and those above, as they were. -/
def RetsKept (sp : Addr) (D k : Nat) (hv hv' : Mem) : Prop :=
  ∀ x, 8 * D - 8 * k ≤ offN sp D x → hv' x = hv x

theorem RetsKept.refl (sp : Addr) (D k : Nat) (hv : Mem) : RetsKept sp D k hv hv := fun _ _ => rfl

theorem RetsKept.trans {sp : Addr} {D k : Nat} {a b c : Mem} (h₁ : RetsKept sp D k a b) (h₂ : RetsKept sp D k b c) :
    RetsKept sp D k a c := fun x hx => (h₂ x hx).trans (h₁ x hx)

/-- The state of the real run inside `k` calls: the inlined run's, with the
return addresses from `hv`, the unknowns `u`, and `rsp` `8 k` lower. -/
def NestState (sp : Addr) (D k : Nat) (hv : Mem) (u : Nat → BitVec 64) (s : State) : State :=
  (s.patch (holeN sp D) hv u).setReg .rsp (retSlot sp k)

theorem NestState_zero {sp : Addr} {D : Nat} {hv : Mem} {u : Nat → BitVec 64} {s : State} (h : s.gpr .rsp = sp) :
    NestState sp D 0 hv u s = s.patch (holeN sp D) hv u := by
  simp only [NestState, retSlot_zero]
  rw [← h]
  exact setReg_self _ _

theorem NestState_rsp (sp : Addr) (D k : Nat) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (NestState sp D k hv u s).gpr .rsp = retSlot sp k := by
  simp [NestState, State.setReg]

theorem NestState_mem (sp : Addr) (D k : Nat) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (NestState sp D k hv u s).mem = overlay (holeN sp D) hv s.mem := rfl

/-- The 8 bytes of the `k`-th slot are in the hole. -/
theorem slot_in_hole {sp : Addr} {D k : Nat} (hk : 1 ≤ k) (hkD : k ≤ D) (hD : 8 * D < 2 ^ 64) {x : Addr}
    (hx : (x - retSlot sp k).toNat < 8) : (holeN sp D).Contains x 1 := by
  rw [holeN_contains, offN_slot_add hkD hD hx hk]
  omega_arith

theorem overlay_slot_writeW {sp : Addr} {D k : Nat} (hk : 1 ≤ k) (hkD : k ≤ D) (hD : 8 * D < 2 ^ 64)
    (hv m : Mem) (v : BitVec 64) :
    (overlay (holeN sp D) hv m).writeW (retSlot sp k) v = overlay (holeN sp D) (hv.writeW (retSlot sp k) v) m := by
  funext x
  simp only [Mem.writeW, Mem.write, overlay]
  split
  · rename_i hx
    simp only [slot_in_hole hk hkD hD hx, ite_true]
  · rename_i hx
    split <;> [simp only; rfl]

theorem overlay_slot_readW {sp : Addr} {D k : Nat} (hk : 1 ≤ k) (hkD : k ≤ D) (hD : 8 * D < 2 ^ 64)
    (hv m : Mem) : (overlay (holeN sp D) hv m).readW (retSlot sp k) 64 = hv.readW (retSlot sp k) 64 :=
  Mem.readW_congr fun i hi => by
    have : (holeN sp D).Contains (retSlot sp k + BitVec.ofNat 64 i) 1 :=
      slot_in_hole hk hkD hD (by rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith)
    simp only [overlay, this, ite_true]

/-- A run that keeps the bytes of the `k`-th slot keeps the value read there. -/
theorem RetsKept.readW {sp : Addr} {D k : Nat} {hv hv' : Mem} (h : RetsKept sp D k hv hv') (hk : 1 ≤ k) (hkD : k ≤ D)
    (hD : 8 * D < 2 ^ 64) : hv'.readW (retSlot sp k) 64 = hv.readW (retSlot sp k) 64 :=
  Mem.readW_congr fun i hi => h _ (by
    rw [offN_slot_add hkD hD (by rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith) hk]
    omega_arith)

/-- Storing the `k + 1`-th return address keeps the bytes of the `k`-th
slot and those above. -/
theorem RetsKept.writeW {sp : Addr} {D k : Nat} (hkD : k + 1 ≤ D) (hD : 8 * D < 2 ^ 64) (hv : Mem) (v : BitVec 64) :
    RetsKept sp D k hv (hv.writeW (retSlot sp (k + 1)) v) := by
  intro x hx
  simp only [Mem.writeW, Mem.write]
  rw [ite_eq_right]
  intro hlt
  have := offN_slot_add (sp := sp) hkD hD hlt (by omega_arith)
  omega_arith

/-- The bytes a run inside `k + 1` calls keeps include those a run inside `k` keeps. -/
theorem RetsKept.succ {sp : Addr} {D k : Nat} {hv hv' : Mem} (h : RetsKept sp D (k + 1) hv hv') : RetsKept sp D k hv hv' :=
  fun x hx => h x (by omega_arith)

/-! ## The leakage -/

/-- The address an indirect call by `i` reads its target from, inside `k`
calls: for `callm [rsp + disp]`, `rsp + disp`. -/
def icallLeak (sp : Addr) (k : Nat) (i : Instr) : List Leak :=
  match i with
  | .callm m => [.addr (retSlot sp k + BitVec.ofInt 64 m.disp)]
  | _ => []

/-- The leakage of a run of `c` inside `k` calls, from that of `c.inlineAll`
(a prefix of `t`): each call adds the address of its return address
(`retSlot sp (k + 1)`) before and after the leakage of the code it calls,
inside `k + 1` calls; an indirect call of one function also the address it
reads (`icallLeak`) and the function's, from `F`. With `f` steps of fuel;
with the remainder of `t`. -/
def liftTN (sp : Addr) (F : String → Addr) : Nat → Nat → Prog isa → List Leak → Option (List Leak × List Leak)
  | _, 0, _, _ => none
  | _, _ + 1, .block l, t => if blockLen l ≤ t.length then some (t.take (blockLen l), t.drop (blockLen l)) else none
  | k, f + 1, .seq a b, t => (liftTN sp F k f a t).bind fun (p : List Leak × List Leak) =>
      (liftTN sp F k f b p.2).map fun (q : List Leak × List Leak) => (p.1 ++ q.1, q.2)
  | k, f + 1, .ite _ th _, .branch true :: t =>
      (liftTN sp F k f th t).map fun (p : List Leak × List Leak) => (.branch true :: p.1, p.2)
  | k, f + 1, .ite _ _ el, .branch false :: t =>
      (liftTN sp F k f el t).map fun (p : List Leak × List Leak) => (.branch false :: p.1, p.2)
  | _, _ + 1, .ite .., _ => none
  | k, f + 1, .loop b c, t => (liftTN sp F k f b t).bind fun (p : List Leak × List Leak) => match p.2 with
      | .branch false :: r => some (p.1 ++ [.branch false], r)
      | .branch true :: r => (liftTN sp F k f (.loop b c) r).map fun (q : List Leak × List Leak) =>
          (p.1 ++ .branch true :: q.1, q.2)
      | _ => none
  | k, f + 1, .call _ b, t => (liftTN sp F (k + 1) f b t).map fun (p : List Leak × List Leak) =>
      (.addr (retSlot sp (k + 1)) :: (p.1 ++ [.addr (retSlot sp (k + 1))]), p.2)
  | _, _ + 1, .frame .., _ => none
  | k, f + 1, .icall i n b (.block []), t => (liftTN sp F (k + 1) f b t).map fun (p : List Leak × List Leak) =>
      (icallLeak sp k i ++ .addr (F n) :: .addr (retSlot sp (k + 1)) :: (p.1 ++ [.addr (retSlot sp (k + 1))]), p.2)
  | _, _ + 1, .icall .., _ => none

/-- `ta` is the leakage `liftTN` gives for `t`, with enough fuel, whatever follows. -/
def LiftsN (sp : Addr) (F : String → Addr) (k : Nat) (c : Prog isa) (ta t : List Leak) : Prop :=
  ∃ N, ∀ f, N ≤ f → ∀ r, liftTN sp F k f c (t ++ r) = some (ta, r)

theorem LiftsN.unique {sp : Addr} {F : String → Addr} {k : Nat} {c : Prog isa} {ta₁ ta₂ t : List Leak}
    (h₁ : LiftsN sp F k c ta₁ t) (h₂ : LiftsN sp F k c ta₂ t) : ta₁ = ta₂ := by
  obtain ⟨N₁, l₁⟩ := h₁
  obtain ⟨N₂, l₂⟩ := h₂
  have := (l₁ (max N₁ N₂) (by omega_arith) []).symm.trans (l₂ (max N₁ N₂) (by omega_arith) [])
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

/-- The leakage of a block lifts to itself. -/
theorem Exec.liftsN_block {sp : Addr} {F : String → Addr} {k : Nat} {l : List Instr} {s s' : State}
    {t : List Leak} (h : Exec isa (.block l) s t s') : LiftsN sp F k (.block l) t t := by
  generalize e : (Code.block l : Prog isa) = c at h
  induction h with
  | seq | iteT | iteF | loopExit | loopNext | call | frame | icall | icallNext => cases e
  | block h =>
    cases e
    refine ⟨1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    have hl := execBlock_length h
    simp only [liftTN, List.length_append, hl, Nat.le_add_right, ite_true, List.take_left', List.drop_left']

/-! ## The slots of indirect calls -/

/-- Each slot `(disp, n)` of `slots`: the 8 bytes at `sp + disp` hold the
address of `n` and may be read, and no region `s` may write overlaps them. -/
def SlotsOk (slots : List (Int × String)) (sp : Addr) (s : State) : Prop :=
  ∀ p ∈ slots, s.load64 (sp + BitVec.ofInt 64 p.1) = some (s.syms p.2) ∧
    ∀ r ∈ s.wr, (⟨sp + BitVec.ofInt 64 p.1, 8⟩ : Region).Disjoint r

theorem SlotsOk.nil (sp : Addr) (s : State) : SlotsOk [] sp s := fun _ h => absurd h List.not_mem_nil

/-- Code that calls nothing keeps the slots, which it may not write. -/
theorem SlotsOk.of_exec {slots : List (Int × String)} {sp : Addr} {c : Prog isa} (hn : c.noCalls = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hs : SlotsOk slots sp s) : SlotsOk slots sp s' := by
  obtain ⟨hrd, hwr, hf⟩ := Exec.regions h hn
  intro p hp
  obtain ⟨hl, hd⟩ := hs p hp
  refine ⟨?_, by rw [hwr]; exact hd⟩
  simp only [State.load64] at hl ⊢
  rw [hrd, hwr, Exec.syms h]
  split at hl
  · rename_i hin
    simp only [hin, ite_true]
    rw [hf.readW (w := 64) (Region.contains_self _ 8) hd (by decide)]
    exact hl
  · cases hl

/-! ## Calls as inlined code -/

/-- The run of a loop of inlined code, from its body's. -/
theorem loop_uninlineN {slots : List (Int × String)} {body : Prog isa} {kc : Cond} {sp : Addr} {F : String → Addr}
    {D k : Nat} (hn : body.inlineAll.noCalls = true)
    (ih : ∀ {b b' : State} {t : List Leak}, Exec isa body.inlineAll b t b' → Clear (holeN sp D) b →
      b.gpr .rsp = sp → SlotsOk slots sp b → b.syms = F → ∀ (hv : Mem) (u : Nat → BitVec 64), ∃ hv' u' ta,
        Exec isa body (NestState sp D k hv u b) ta (NestState sp D k hv' u' b') ∧ b'.gpr .rsp = sp ∧
          RetsKept sp D k hv hv' ∧ LiftsN sp F k body ta t)
    {b b' : State} {t : List Leak} (h : Exec isa (.loop body.inlineAll kc) b t b') (hb : Clear (holeN sp D) b)
    (hsp : b.gpr .rsp = sp) (hslot : SlotsOk slots sp b) (hF : b.syms = F) (hv : Mem) (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa (.loop body kc) (NestState sp D k hv u b) ta (NestState sp D k hv' u' b') ∧
      b'.gpr .rsp = sp ∧ RetsKept sp D k hv hv' ∧ LiftsN sp F k (.loop body kc) ta t := by
  generalize e : (Code.loop body.inlineAll kc : Prog isa) = L at h
  induction h generalizing hv u with
  | block | seq | iteT | iteF | call | frame | icall | icallNext => cases e
  | @loopExit body' k' s s' t h₁ hk _ =>
    cases e
    obtain ⟨hv', u', ta, ha, hs', ag, ⟨N, hl⟩⟩ := ih h₁ hb hsp hslot hF hv u
    refine ⟨hv', u', ta ++ [.branch false],
      .loopExit ha (by simp only [NestState]; rw [eval_setRsp, eval_patch]; exact hk), hs', ag, N + 1,
      fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTN, List.append_assoc, List.cons_append, List.nil_append, hl f (by omega_arith), Option.bind_some]
  | @loopNext body' k' s s₁ s' t t' h₁ hk _ _ ih₂ =>
    cases e
    obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ag₁, ⟨N₁, hl₁⟩⟩ := ih h₁ hb hsp hslot hF hv u
    obtain ⟨hv', u', ta₂, ha₂, hs', ag₂, ⟨N₂, hl₂⟩⟩ :=
      ih₂ (hb.of_exec h₁) hs₁ (hslot.of_exec hn h₁) ((Exec.syms h₁).trans hF) hv₁ u₁ rfl
    refine ⟨hv', u', ta₁ ++ .branch true :: ta₂,
      .loopNext ha₁ (by simp only [NestState]; rw [eval_setRsp, eval_patch]; exact hk) ha₂, hs', ag₁.trans ag₂,
      max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTN, List.append_assoc, List.cons_append, hl₁ f (by omega_arith), Option.bind_some]
    rw [hl₂ f (by omega_arith) r]; rfl

/-- A run of `c.inlineAll` inside `k` calls (of the `D` the hole has room
for) gives one of `c` from the real state (`NestState`), to the real state of its
end, which keeps the return addresses of the `k` calls (`RetsKept`), with the
leakage `liftTN` gives. -/
theorem Exec.uninlineN {slots : List (Int × String)} {c : Prog isa} {d : Nat} {inner : Bool}
    (hc : c.OkN slots d inner = true) {D k : Nat} (hkD : k + d ≤ D) (hD : 8 * D < 2 ^ 64)
    (hin : inner = false → k = 0) {sp : Addr} {F : String → Addr} {b b' : State} {t : List Leak}
    (h : Exec isa c.inlineAll b t b') (hb : Clear (holeN sp D) b) (hsp : b.gpr .rsp = sp)
    (hslot : SlotsOk slots sp b) (hF : b.syms = F) (hv : Mem) (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa c (NestState sp D k hv u b) ta (NestState sp D k hv' u' b') ∧ b'.gpr .rsp = sp ∧
      RetsKept sp D k hv hv' ∧ LiftsN sp F k c ta t := by
  induction c generalizing d inner k b b' t hv u with
  | icall i n body nx ih =>
    obtain ⟨d, m, rfl, rfl, rfl, rfl, hbase, hidx, hmem, hc⟩ := Code.OkN_icall hc
    obtain rfl := hin rfl
    simp only [Code.inlineAll] at h
    -- The call reads the address of `n` from its slot, outside the hole.
    obtain ⟨hl, -⟩ := hslot _ hmem
    have hea : (NestState sp D 0 hv u b).ea m = sp + BitVec.ofInt 64 m.disp := by
      simp only [State.ea, hidx, hbase, NestState_rsp, retSlot_zero]
    have hi : isa.icall (.callm m) (NestState sp D 0 hv u b) = some (isa.fnAddr (NestState sp D 0 hv u b) n) := by
      simp only [State.load64] at hl
      split at hl
      · rename_i hin'
        have hin'' : InRegions ((NestState sp D 0 hv u b).rd ++ (NestState sp D 0 hv u b).wr)
            (sp + BitVec.ofInt 64 m.disp) 8 := hin'
        show (NestState sp D 0 hv u b).load64 _ = some ((NestState sp D 0 hv u b).syms n)
        simp only [hea, State.load64, hin'', ite_true, NestState_mem]
        rw [overlay_readW (w := 64) (by decide) fun x hx => Clear.miss hb (fun _ h => h) hin' (x := x) hx]
        exact hl
      · cases hl
    let hv₁ : Mem := hv.writeW (retSlot sp 1) (u 0)
    let u₁ : Nat → BitVec 64 := fun n => u (n + 1)
    have hcall : isa.call (NestState sp D 0 hv u b) = some (NestState sp D 1 hv₁ u₁ b) := by
      simp only [isa, call, NestState_rsp, retSlot_succ]
      congr 1
      simp only [NestState, State.patch, State.setReg, hv₁, u₁,
        overlay_slot_writeW (k := 1) (by omega_arith) (by omega_arith) hD]
      congr 1
      funext r
      split <;> rfl
    obtain ⟨hv₂, u₂, ta, hbody, hrsp, ag, hl'⟩ :=
      ih hc (k := 1) (by omega_arith) (fun h => absurd h (by decide)) h hb hsp hslot hF hv₁ u₁
    have hret : isa.ret (NestState sp D 1 hv₁ u₁ b) (NestState sp D 1 hv₂ u₂ b') =
        some (NestState sp D 0 hv₂ u₂ b') := by
      have m' : (NestState sp D 1 hv₂ u₂ b').mem.readW (retSlot sp 1) 64 =
          (NestState sp D 1 hv₁ u₁ b).mem.readW (retSlot sp 1) 64 := by
        rw [NestState_mem, NestState_mem, overlay_slot_readW (by omega_arith) (by omega_arith) hD,
          overlay_slot_readW (by omega_arith) (by omega_arith) hD,
          ag.readW (by omega_arith) (by omega_arith) hD]
      simp only [isa, ret, NestState_rsp, m', and_self, ite_true, Option.some.injEq, retSlot_succ_add]
      simp only [NestState, setReg_setReg]
    refine ⟨hv₂, u₂, _, .icall hi hcall hbody hret, hrsp,
      (RetsKept.writeW (by omega_arith) hD hv (u 0)).trans ag.succ, ?_⟩
    obtain ⟨N, hl''⟩ := hl'
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    have hsy : (NestState sp D 0 hv u b).syms = F := hF
    show _ = some ((isa.addrs (.callm m) (NestState sp D 0 hv u b)).map Leak.addr ++
      Leak.addr ((NestState sp D 0 hv u b).syms n) :: _, r)
    have h1 : sp - 8 = retSlot sp 1 := by rw [← retSlot_succ, retSlot_zero]
    simp only [liftTN, icallLeak, hl'' f (by omega_arith) r, Option.map_some, NestState_rsp, addrs, hea,
      retSlot_zero, hsy, List.map_cons, List.map_nil, List.cons_append, List.nil_append, Nat.zero_add, h1]
  | frame => cases d <;> simp only [Code.OkN, Bool.false_eq_true] at hc
  | block l =>
    simp only [Code.inlineAll] at h
    have hr := Code.rsp_inlineAll hc
    simp only [Code.inlineAll] at hr
    have hrsp : b'.gpr .rsp = sp := by
      rw [Exec.gpr (c := .block l) (fun i hi => (hr i hi).2) h, hsp]
    have hlift : LiftsN sp F k (.block l) t t := Exec.liftsN_block h
    cases inner with
    | false =>
      obtain rfl := hin rfl
      refine ⟨hv, u, t, ?_, hrsp, RetsKept.refl _ _ _ _, hlift⟩
      rw [NestState_zero hsp, NestState_zero hrsp]
      exact Exec.F (H := holeN sp D) rfl (fun i _ s hs => ⟨exec_patch hs i, addrs_patch i⟩)
        (fun k _ => eval_patch k) h hb
    | true =>
      refine ⟨hv, u, t, Exec.F (H := holeN sp D) rfl (fun i hi s hs => ⟨?_, ?_⟩)
        (fun k s => by simp only [NestState]; rw [eval_setRsp, eval_patch]) h hb, hrsp, RetsKept.refl _ _ _ _, hlift⟩
      · have hi' := (hr i hi).1 rfl
        simp only [NestState]; rw [exec_setRsp hi', exec_patch hs, Option.map_map]; rfl
      · simp only [NestState]; rw [addrs_setRsp ((hr i hi).1 rfl), addrs_patch]
  | seq a c ih₁ ih₂ =>
    simp only [Code.OkN, Bool.and_eq_true] at hc
    simp only [Code.inlineAll] at h
    obtain ⟨t₁, t₂, s₁, h₁, h₂, rfl⟩ := Exec.seq_inv h
    obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ag₁, ⟨N₁, hl₁⟩⟩ := ih₁ hc.1 hkD hin h₁ hb hsp hslot hF hv u
    obtain ⟨hv', u', ta₂, ha₂, hs', ag₂, ⟨N₂, hl₂⟩⟩ := ih₂ hc.2 hkD hin h₂ (hb.of_exec h₁) hs₁
      (hslot.of_exec (Code.noCalls_inlineAll hc.1) h₁) ((Exec.syms h₁).trans hF) hv₁ u₁
    refine ⟨hv', u', ta₁ ++ ta₂, .seq ha₁ ha₂, hs', ag₁.trans ag₂, max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTN, List.append_assoc, hl₁ f (by omega_arith), Option.bind_some, hl₂ f (by omega_arith) r,
      Option.map_some]
  | ite kc th el ih₁ ih₂ =>
    simp only [Code.OkN, Bool.and_eq_true] at hc
    simp only [Code.inlineAll] at h
    have hev : eval kc (NestState sp D k hv u b) = eval kc b := by
      simp only [NestState]; rw [eval_setRsp, eval_patch]
    rcases Exec.ite_inv h with ⟨t, rfl, hk, h₁⟩ | ⟨t, rfl, hk, h₁⟩
    · obtain ⟨hv', u', ta, ha, hs', ag, ⟨N, hl⟩⟩ := ih₁ hc.1 hkD hin h₁ hb hsp hslot hF hv u
      refine ⟨hv', u', .branch true :: ta, .iteT (hev.trans hk) ha, hs', ag, N + 1, fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftTN, List.cons_append, hl f (by omega_arith) r, Option.map_some]
    · obtain ⟨hv', u', ta, ha, hs', ag, ⟨N, hl⟩⟩ := ih₂ hc.2 hkD hin h₁ hb hsp hslot hF hv u
      refine ⟨hv', u', .branch false :: ta, .iteF (hev.trans hk) ha, hs', ag, N + 1, fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftTN, List.cons_append, hl f (by omega_arith) r, Option.map_some]
  | loop body kc ih =>
    simp only [Code.OkN] at hc
    simp only [Code.inlineAll] at h
    exact loop_uninlineN (Code.noCalls_inlineAll hc)
      (fun h₁ hb₁ hsp₁ hs₁ hF₁ hv₁ u₁ => ih hc hkD hin h₁ hb₁ hsp₁ hs₁ hF₁ hv₁ u₁) h hb hsp hslot hF hv u
  | call n body ih =>
    cases d with
    | zero => simp only [Code.OkN, Bool.false_eq_true] at hc
    | succ d =>
    simp only [Code.OkN] at hc
    simp only [Code.inlineAll] at h
    -- The call stores the return address in the `k + 1`-th slot.
    let hv₁ : Mem := hv.writeW (retSlot sp (k + 1)) (u 0)
    let u₁ : Nat → BitVec 64 := fun n => u (n + 1)
    have hcall : isa.call (NestState sp D k hv u b) = some (NestState sp D (k + 1) hv₁ u₁ b) := by
      simp only [isa, call, NestState_rsp, retSlot_succ]
      congr 1
      simp only [NestState, State.patch, State.setReg, hv₁, u₁,
        overlay_slot_writeW (k := k + 1) (by omega_arith) (by omega_arith) hD]
      congr 1
      funext r
      split <;> rfl
    -- The code it calls, inside `k + 1` calls.
    obtain ⟨hv₂, u₂, ta, hbody, hrsp, ag, hl⟩ :=
      ih hc (k := k + 1) (by omega_arith) (fun h => absurd h (by decide)) h hb hsp hslot hF hv₁ u₁
    have hret : isa.ret (NestState sp D (k + 1) hv₁ u₁ b) (NestState sp D (k + 1) hv₂ u₂ b') =
        some (NestState sp D k hv₂ u₂ b') := by
      have m : (NestState sp D (k + 1) hv₂ u₂ b').mem.readW (retSlot sp (k + 1)) 64 =
          (NestState sp D (k + 1) hv₁ u₁ b).mem.readW (retSlot sp (k + 1)) 64 := by
        rw [NestState_mem, NestState_mem, overlay_slot_readW (by omega_arith) (by omega_arith) hD,
          overlay_slot_readW (by omega_arith) (by omega_arith) hD,
          ag.readW (by omega_arith) (by omega_arith) hD]
      simp only [isa, ret, NestState_rsp, m, and_self, ite_true, Option.some.injEq, retSlot_succ_add]
      simp only [NestState, setReg_setReg]
    refine ⟨hv₂, u₂, _, .call hcall hbody hret, hrsp,
      (RetsKept.writeW (by omega_arith) hD hv (u 0)).trans ag.succ, ?_⟩
    obtain ⟨N, hl'⟩ := hl
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftTN, hl' f (by omega_arith) r, Option.map_some, NestState_rsp, retSlot_succ, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append]

/-- `liftTN` reads `F` only at the functions of the slots. -/
theorem liftTN_congr {slots : List (Int × String)} {sp : Addr} {F₁ F₂ : String → Addr}
    (hF : ∀ p ∈ slots, F₁ p.2 = F₂ p.2) :
    ∀ {f k : Nat} {c : Prog isa} {d : Nat} {inner : Bool} {t : List Leak}, c.OkN slots d inner = true →
      liftTN sp F₁ k f c t = liftTN sp F₂ k f c t := by
  intro f
  induction f with
  | zero => intro k c d inner t _; rfl
  | succ f ih =>
    intro k c d inner t hc
    cases c with
    | block l => rfl
    | seq a b =>
      simp only [Code.OkN, Bool.and_eq_true] at hc
      simp only [liftTN, ih hc.1]
      congr 1
      funext p
      rw [ih hc.2]
    | ite cd th el =>
      simp only [Code.OkN, Bool.and_eq_true] at hc
      rcases t with _ | ⟨_ | ⟨_ | _⟩, t⟩ <;> simp only [liftTN, ih hc.1, ih hc.2]
    | loop b cd =>
      have hb := hc
      simp only [Code.OkN] at hb
      simp only [liftTN, ih hb]
      congr 1
      funext p
      split <;> simp only [ih hc]
    | call n b =>
      cases d with
      | zero => simp only [Code.OkN, Bool.false_eq_true] at hc
      | succ d => simp only [Code.OkN] at hc; simp only [liftTN, ih hc]
    | frame => cases d <;> simp only [Code.OkN, Bool.false_eq_true] at hc
    | icall i n b nx =>
      obtain ⟨d, m, rfl, rfl, rfl, rfl, -, -, hmem, hb⟩ := Code.OkN_icall hc
      simp only [liftTN, ih hb, hF _ hmem]

theorem LiftsN.congr {slots : List (Int × String)} {sp : Addr} {F₁ F₂ : String → Addr}
    (hF : ∀ p ∈ slots, F₁ p.2 = F₂ p.2) {k : Nat} {c : Prog isa} {d : Nat} {inner : Bool}
    (hc : c.OkN slots d inner = true) {ta t : List Leak} (h : LiftsN sp F₂ k c ta t) : LiftsN sp F₁ k c ta t := by
  obtain ⟨N, hl⟩ := h
  exact ⟨N, fun f hf r => (liftTN_congr hF hc).trans (hl f hf r)⟩

/-- A run of `c.inlineAll` from `s`, whose slots hold their functions'
addresses, gives one of `c` from `s`, to the same state but for the `8 d`
bytes below `rsp` and the unknowns. -/
theorem Exec.of_inlineAllS {slots : List (Int × String)} {c : Prog isa} {d : Nat} (hc : c.InlineOkNS slots d = true)
    (hD : 8 * d < 2 ^ 64) {s s' : State} {t : List Leak} (h : Exec isa c.inlineAll s t s')
    (hs : Clear (holeN (s.gpr .rsp) d) s) (hslot : SlotsOk slots (s.gpr .rsp) s) :
    ∃ hv u ta, Exec isa c s ta (s'.patch (holeN (s.gpr .rsp) d) hv u) ∧ s'.gpr .rsp = s.gpr .rsp ∧
      LiftsN (s.gpr .rsp) s.syms 0 c ta t := by
  obtain ⟨hv, u, ta, he, hr, -, hl⟩ :=
    Exec.uninlineN hc (k := 0) (by omega_arith) hD (fun _ => rfl) h hs rfl hslot rfl s.mem s.unknowns
  rw [NestState_zero rfl, State.patch_self, NestState_zero hr] at he
  exact ⟨hv, u, ta, he, hr, hl⟩

/-- A run of `c.inlineAll` from `s` gives one of `c` from `s`, to the same
state but for the `8 d` bytes below `rsp` and the unknowns. -/
theorem Exec.of_inlineAll {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {s s' : State} {t : List Leak} (h : Exec isa c.inlineAll s t s') (hs : Clear (holeN (s.gpr .rsp) d) s) :
    ∃ hv u ta, Exec isa c s ta (s'.patch (holeN (s.gpr .rsp) d) hv u) ∧ s'.gpr .rsp = s.gpr .rsp ∧
      LiftsN (s.gpr .rsp) s.syms 0 c ta t :=
  Exec.of_inlineAllS hc hD h hs (SlotsOk.nil _ _)

/-- `c` is constant time if `c.inlineAll` is, runs from every state its
precondition allows, with its slots holding their functions' addresses, and
two runs agree on those addresses. -/
theorem ConstantTime.of_inlineAllS {slots : List (Int × String)} {c : Prog isa} {d : Nat}
    (hc : c.InlineOkNS slots d = true) (hD : 8 * d < 2 ^ 64)
    {P : State → Prop} {Pub : State → State → Prop} (hrun : ∀ s, P s → ∃ t s', Exec isa c.inlineAll s t s')
    (hclear : ∀ s, P s → Clear (holeN (s.gpr .rsp) d) s) (hslot : ∀ s, P s → SlotsOk slots (s.gpr .rsp) s)
    (hpub : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hsyms : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ → ∀ p ∈ slots, s₁.syms p.2 = s₂.syms p.2)
    (hct : ConstantTime isa P Pub c.inlineAll) : ConstantTime isa P Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨tb₁, b₁, f₁⟩ := hrun s₁ p₁
  obtain ⟨tb₂, b₂, f₂⟩ := hrun s₂ p₂
  obtain ⟨_, _, ta₁, a₁, _, l₁⟩ := Exec.of_inlineAllS hc hD f₁ (hclear s₁ p₁) (hslot s₁ p₁)
  obtain ⟨_, _, ta₂, a₂, _, l₂⟩ := Exec.of_inlineAllS hc hD f₂ (hclear s₂ p₂) (hslot s₂ p₂)
  obtain ⟨rfl, -⟩ := Exec.det e₁ a₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ a₂
  have ht := hct s₁ s₂ tb₁ tb₂ b₁ b₂ p₁ p₂ hp f₁ f₂
  subst ht
  rw [hpub s₁ s₂ p₁ p₂ hp] at l₁
  exact l₁.unique (l₂.congr (hsyms s₁ s₂ p₁ p₂ hp) hc)

/-- `c` is constant time if `c.inlineAll` is, and runs from every state its
precondition allows. -/
theorem ConstantTime.of_inlineAll {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {P : State → Prop} {Pub : State → State → Prop} (hrun : ∀ s, P s → ∃ t s', Exec isa c.inlineAll s t s')
    (hclear : ∀ s, P s → Clear (holeN (s.gpr .rsp) d) s)
    (hpub : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa P Pub c.inlineAll) : ConstantTime isa P Pub c :=
  ConstantTime.of_inlineAllS hc hD hrun hclear (fun s _ => SlotsOk.nil _ s) hpub
    (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) hct

/-- The calling convention's obligations hold of the run of `c` if they do
of `c.inlineAll`'s: the return address above `rsp` is not in the hole. -/
theorem abiPreserved_patchN {s b : State} {d : Nat} (hD : 8 * d < 2 ^ 64) (hv : Mem) (u : Nat → BitVec 64)
    (h : abiPreserved s b) : abiPreserved s (b.patch (holeN (s.gpr .rsp) d) hv u) := by
  refine ⟨h.1, ?_, h.2.2⟩
  rw [State.patch_readW (by decide) fun x hx hh => ?_]
  · exact h.2.1
  · rw [holeN_contains] at hh
    have e : x - (s.gpr .rsp - BitVec.ofNat 64 (8 * d)) = (x - s.gpr .rsp) + BitVec.ofNat 64 (8 * d) :=
      Offset.sub_sub_eq _ _ _
    simp only [offN] at hh
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hD] at hh
    have := (x - s.gpr .rsp).isLt
    omega_arith

/-! ## Contracts -/

/-- `k`, with no buffer on the `8 d` bytes below `rsp`: what a caller of code
whose calls call, `d` deep, must also give it. -/
def _root_.VG.Contract.clearN (d : Nat) (k : Contract isa) : Contract isa :=
  { k with pre := fun s => k.pre s ∧ Clear (holeN (s.gpr .rsp) d) s }

/-- A contract built by `Sig.contract` with `stack` at least `8 d` keeps
every buffer and argument area away from the `8 d` bytes below `rsp`. -/
theorem Sig.clearN_of_pre {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
    {wa : Bool} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {s : State} {d : Nat}
    (h : (sig.contract abi pre post wa (8 * (d + 1)) leak).pre s) : Clear (holeN (s.gpr .rsp) (d + 1)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨_, hrd, hwr, _, hres, _⟩ := h
    intro r hr
    have hh : (holeN (s.gpr .rsp) (d + 1)) ∈ abi.reserved (8 * (d + 1)) s := by
      show _ ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (8 * (d + 1)))
      refine List.mem_cons_of_mem _ ?_
      unfold holeN
      rw [show 8 * (d + 1) = (8 * d + 7) + 1 from by omega_arith]
      exact List.mem_singleton_self _
    rcases List.mem_append.mp hr with hr | hr
    · rw [show s.rd = abi.rd s from rfl, hrd] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm
    · rw [show s.wr = abi.wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

/-- Correctness of `c` from that of `c.inlineAll`, for a postcondition that
does not read the `8 d` bytes below `rsp`. -/
theorem ok_of_inlineAll {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {k : Contract isa}
    (hcor : ∀ s, k.pre s → ∃ t s', Exec isa c.inlineAll s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hpost : ∀ s b hv u, k.pre s → Clear (holeN (s.gpr .rsp) d) s → k.post s b →
      k.post s (b.patch (holeN (s.gpr .rsp) d) hv u)) :
    ∀ s, (k.clearN d).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s' := by
  intro s ⟨hs, hcl⟩
  obtain ⟨t, b, he, ha, hp⟩ := hcor s hs
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inlineAll hc hD he hcl
  exact ⟨ta, _, ha', abiPreserved_patchN hD hv u ha, hpost s b hv u hs hcl hp⟩

/-- Constant time of `c` from that of `c.inlineAll`, for a relation that fixes `rsp`. -/
theorem ct_of_inlineAll {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {k : Contract isa} (hrun : ∀ s, k.pre s → ∃ t s', Exec isa c.inlineAll s t s')
    (hrsp : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa k.pre k.pub c.inlineAll) : ConstantTime isa (k.clearN d).pre k.pub c :=
  ConstantTime.of_inlineAll hc hD (fun s h => hrun s h.1) (fun _ h => h.2) (fun _ _ _ _ h => hrsp _ _ h)
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => hct s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1 hp e₁ e₂

/-- `c` is verified against `k` if `c.inlineAll` is correct and constant time
against a contract `k₀` that `k` implies, `k₀`'s postcondition does not read
the `8 d` bytes below `rsp`, `k` keeps every buffer away from them, and its
precondition gives the slots their functions' addresses, on which two runs
`k` relates agree. -/
theorem Verified.of_inlineAllS {slots : List (Int × String)} {c : Prog isa} {d : Nat}
    (hc : c.InlineOkNS slots d = true) (hD : 8 * d < 2 ^ 64) {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inlineAll s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inlineAll) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (holeN (s.gpr .rsp) d) s)
    (hslot : ∀ s, k.pre s → SlotsOk slots (s.gpr .rsp) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (holeN (s.gpr .rsp) d) hv u))
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hsyms : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → ∀ p ∈ slots, s₁.syms p.2 = s₂.syms p.2) :
    Verified target c k := by
  refine ⟨fun s hs => ?_, ?_, himp.sat⟩
  · obtain ⟨t, b, he, ha, hp⟩ := hcor s (himp.pre s hs)
    obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inlineAllS hc hD he (hclear s hs) (hslot s hs)
    exact ⟨ta, _, ha', abiPreserved_patchN hD hv u ha, himp.post s _ hs (hpost s b hv u hs hp)⟩
  · refine ConstantTime.of_inlineAllS hc hD (fun s hs => ?_) hclear hslot hrsp hsyms
      fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
        hct s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂
    obtain ⟨t, b, he, -, -⟩ := hcor s (himp.pre s hs)
    exact ⟨t, b, he⟩

/-- `c` is verified against `k` if `c.inlineAll` is correct and constant time
against a contract `k₀` that `k` implies, `k₀`'s postcondition does not read
the `8 d` bytes below `rsp`, and `k` keeps every buffer away from them. -/
theorem Verified.of_inlineAll {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inlineAll s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inlineAll) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (holeN (s.gpr .rsp) d) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (holeN (s.gpr .rsp) d) hv u))
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp) : Verified target c k :=
  Verified.of_inlineAllS hc hD hcor hct himp hclear (fun s _ => SlotsOk.nil _ s) hpost hrsp
    (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil)

/-- `Verified.of_inlineAll`, with constant time checked on `c` itself (taint
tracking follows the calls). -/
theorem Verified.of_inlineAll_ct {c : Prog isa} {d : Nat} (hc : c.InlineOkN d = true) (hD : 8 * d < 2 ^ 64)
    {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inlineAll s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (holeN (s.gpr .rsp) d) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (holeN (s.gpr .rsp) d) hv u)) :
    Verified target c k := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    hct s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂, himp.sat⟩
  obtain ⟨t, b, he, ha, hp⟩ := hcor s (himp.pre s hs)
  obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inlineAll hc hD he (hclear s hs)
  exact ⟨ta, _, ha', abiPreserved_patchN hD hv u ha, himp.post s _ hs (hpost s b hv u hs hp)⟩

/-- `Sig.clearN_of_pre`, under the calling convention with static tables. -/
theorem Sig.clearN_of_pre_consts {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {s : State} {d : Nat}
    (h : (sig.contract (abi.withConsts (c :: cs)) pre post wa (8 * (d + 1)) leak).pre s) :
    Clear (holeN (s.gpr .rsp) (d + 1)) s := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · obtain ⟨hwf, hrd, hwr, _, hres, _⟩ := h
    have hh : holeN (s.gpr .rsp) (d + 1) ∈ (abi.withConsts (c :: cs)).reserved (8 * (d + 1)) s := by
      show _ ∈ (⟨s.gpr .rsp, 8⟩ :: stackBelow (s.gpr .rsp) (8 * (d + 1)))
      refine List.mem_cons_of_mem _ ?_
      unfold holeN
      rw [show 8 * (d + 1) = (8 * d + 7) + 1 from by omega_arith]
      exact List.mem_singleton_self _
    obtain ⟨-, hdrop, -, hct, -⟩ := hwf
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [← List.take_append_drop (s.rd.length - (c :: cs).length) s.rd] at hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [show s.rd.take (s.rd.length - (c :: cs).length) = (abi.withConsts (c :: cs)).rd s from rfl,
          hrd] at hr
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
        exact (hres _ hh a (List.mem_filter.mp ha).1).symm
      · rw [show s.rd = abi.rd s from rfl, hdrop] at hr
        exact (hct r hr).2.2 _ hh
    · rw [show s.wr = (abi.withConsts (c :: cs)).wr s from rfl, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact (hres _ hh a (List.mem_filter.mp ha).1).symm

theorem abi_wf0_16 (ws : List Nat) (s : State) (h : abi.wf ws 16 s) : abi.wf ws 0 s := by
  simp only [abi] at h ⊢
  split at h
  · rename_i hl; simp only [hl, ite_true]
  · rename_i hl; simp only [hl, ite_false]; exact ⟨trivial, h.2⟩

/-- A contract with 16 bytes of stack asks more than the same with none. -/
theorem Sig.pre_stack0_16 {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract (abi.withConsts (c :: cs)) pre post wa 16 leak).pre s) :
    (sig.contract (abi.withConsts (c :: cs)) pre post wa 0 leak).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨⟨hw, hdrop, hheld, hct, hal⟩, hrd, hwr, hpw, hres, hb, hp⟩ := h
    have hsub : ∀ r ∈ (abi.withConsts (c :: cs)).reserved 0 s, r ∈ (abi.withConsts (c :: cs)).reserved 16 s := by
      intro r hr; simp only [abi, Abi.withConsts, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact .inl hr
    refine ⟨⟨?_, hdrop, hheld, fun t ht => ⟨(hct t ht).1, (hct t ht).2.1, fun r hr => (hct t ht).2.2 r (hsub r hr)⟩, hal⟩,
      hrd, hwr, hpw, fun r hr => hres r (hsub r hr), hb, hp⟩
    exact abi_wf0_16 _ s hw

/-- A contract that implies the one with no stack implies the one with 16
bytes of stack, if that one can be met. -/
theorem _root_.VG.Contract.Implies.stack16 {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    {sig : Sig} {pre : Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → Prop)}
    {post : sig.Post (abi.withConsts (c :: cs)).ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words (abi.withConsts (c :: cs)).ptrBits) (Mem → List Nat))} {k₀ : Contract isa}
    (h : k₀.Implies (sig.contract (abi.withConsts (c :: cs)) pre post wa 0 leak))
    (hsat : ∃ s, (sig.contract (abi.withConsts (c :: cs)) pre post wa 16 leak).pre s) :
    k₀.Implies (sig.contract (abi.withConsts (c :: cs)) pre post wa 16 leak) :=
  ⟨fun s hs => h.pre s (Sig.pre_stack0_16 hs), fun s s' hs hp => h.post s s' (Sig.pre_stack0_16 hs) hp,
    fun s₁ s₂ h₁ h₂ hp => h.pub s₁ s₂ (Sig.pre_stack0_16 h₁) (Sig.pre_stack0_16 h₂) hp, hsat⟩

/-- The code each call of a function calls, inlined, and every instruction
of it: no instruction of the inlined code writes `rsp`. -/
theorem _root_.VG.Code.clobbers_rsp_of_inlineOkN {c : Prog isa} {d : Nat} (h : c.InlineOkN d = true) :
    ∀ i ∈ instrs c.inlineAll, Taint.clobbers i .rsp = false :=
  fun i hi => (Code.rsp_inlineAll h i hi).2

/-- Inlining at every depth keeps only instructions of the code and the
functions it calls: a check of every instruction of `c` holds of its
inlined form. -/
theorem _root_.VG.Code.allInstrs_inlineAll {I C : Type} {p : I → Bool} :
    ∀ {c : Code I C}, c.allInstrs p = true → c.inlineAll.allInstrs p = true
  | .block _, h => h
  | .seq a b, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [Code.inlineAll, Code.allInstrs, Bool.and_eq_true]
    exact ⟨Code.allInstrs_inlineAll h.1, Code.allInstrs_inlineAll h.2⟩
  | .ite _ t e, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [Code.inlineAll, Code.allInstrs, Bool.and_eq_true]
    exact ⟨Code.allInstrs_inlineAll h.1, Code.allInstrs_inlineAll h.2⟩
  | .loop b _, h => by
    simp only [Code.allInstrs] at h
    simp only [Code.inlineAll, Code.allInstrs]
    exact Code.allInstrs_inlineAll h
  | .call _ b, h => by
    simp only [Code.allInstrs] at h
    simp only [Code.inlineAll]
    exact Code.allInstrs_inlineAll h
  | .frame _ b _, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [Code.inlineAll, Code.allInstrs, Bool.and_eq_true]
    exact ⟨⟨h.1.1, Code.allInstrs_inlineAll h.1.2⟩, h.2⟩
  | .icall _ _ b nx, h => by
    simp only [Code.allInstrs, Bool.and_eq_true] at h
    simp only [Code.inlineAll]
    split
    · exact Code.allInstrs_inlineAll h.1.2
    · simp only [Code.allInstrs, Bool.and_eq_true]; exact h

/-- The 8 bytes below `rsp` are among the 16 below it. -/
theorem hole_sub_holeN2 (sp : Addr) : Region.Sub (hole sp) (holeN sp 2) := by
  have e₁ : hole sp = ⟨(sp - BitVec.ofNat 64 16) + BitVec.ofNat 64 8, 8⟩ := by
    show (⟨sp - 8, 8⟩ : Region) = _
    congr 1; bv_omega
  have e₂ : holeN sp 2 = ⟨sp - BitVec.ofNat 64 16, 16⟩ := rfl
  rw [e₁, e₂]
  exact Offset.sub_base _ (by omega_arith)

/-- What keeps clear of the 16 bytes below `rsp` keeps clear of the 8 below
it: a function whose calls nest one deep, for a caller that allows two. -/
theorem Clear.hole_of_holeN2 {sp : Addr} {s : State} (h : Clear (holeN sp 2) s) : Clear (hole sp) s :=
  fun r hr => (h r hr).sub_right (hole_sub_holeN2 sp)

end VG.X86_64
