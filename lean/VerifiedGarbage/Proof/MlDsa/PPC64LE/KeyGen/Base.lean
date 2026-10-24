module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.KeyGen.Frag
public import VerifiedGarbage.Proof.MlKem.PPC64LE.HashCT
public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE: the primitives, and calling them

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Base.lean`). Key generation and
verification are proven for any implementations of the primitives they call
that are verified against their contracts with at most `S` bytes of stack,
and whose frames use at most `S` bytes (`Callee`).

A call is the moves of its arguments (`glue`, which computes `glueSt`), then
the call (`callV`): from the callee's precondition on entry, it changes only
the callee's writable buffers and the stack below the stack pointer (`Kept`,
as ML-KEM's), and the callee's postcondition holds. Two runs of a call leak
the same if the callee's preconditions hold and its public data agree
(`callV_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Impl.MlDsa.PPC64LE.Arith (loadImm)

/-! ## The primitives -/

/-- Code `c` verified against the contract `k stk` of some stack `stk ≤ S`,
whose frames use at most `S` bytes of stack. -/
structure Callee (c : Prog isa) (k : Nat → Contract isa) (S : Nat) : Prop where
  verified : ∃ stk, stk ≤ S ∧ Verified PPC64LE.target c (k stk)
  stack : sdepth c ≤ S

/-! ## Moves -/

theorem write_write (s : State) (d : Reg) (x y : BitVec 64) : (s.write d x).write d y = s.write d y := by
  simp only [State.write]
  congr 1
  funext r
  split <;> rfl

theorem loadImm_ok (d : Reg) {v : Nat} (hv : v < 2 ^ 31) (s : State) :
    WP isa (.block (loadImm d v)) s (· = s.write d (BitVec.ofNat 64 v)) := by
  refine WP.cons exec_lis (WP.cons exec_ori (wp_nil ?_))
  rw [gpr_write_self, write_write, VG.Proof.MlDsa.PPC64LE.Arith.loadImm_val hv]

/-- The value of an argument. -/
def argVal (s : State) : Arg → BitVec 64
  | .ptr p => s.gpr p.1 + BitVec.ofNat 64 p.2
  | .imm v => BitVec.ofNat 64 v

/-- An argument whose pointer, if any, is in a callee-saved register of the
layout, and whose offset or value is below `2³¹`. -/
def argOk : Arg → Bool
  | .ptr p => (p.1 == .r28 || p.1 == .r29 || p.1 == .r30 || p.1 == .r31) && decide (p.2 < 2 ^ 31)
  | .imm v => decide (v < 2 ^ 31)

theorem arg_ok (d : Reg) {a : Arg} (ha : argOk a = true) (h : ∀ p : Ptr, a = .ptr p → p.1 ≠ d) (s : State) :
    WP isa (.block (a.instrs d)) s (· = s.write d (argVal s a)) := by
  cases a with
  | ptr p =>
    have hb := h p rfl
    simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at ha
    rw [Arg.instrs, WP.block_append_iff]
    refine WP.mono (loadImm_ok d ha.2 s) fun s1 e => ?_
    subst e
    refine WP.cons exec_add (wp_nil ?_)
    rw [gpr_write_self, gpr_write_of_ne _ _ (fun e => hb e), write_write]
    simp only [argVal, BitVec.add_comm]
  | imm v =>
    simp only [argOk, decide_eq_true_eq] at ha
    exact loadImm_ok d ha s

/-- The state after the moves of the arguments `as`. -/
def glueSt (s : State) : List (Reg × Arg) → State
  | [] => s
  | (d, a) :: as => glueSt (s.write d (argVal s a)) as

/-- An argument register. -/
def argReg (r : Reg) : Bool :=
  r == .r3 || r == .r4 || r == .r5 || r == .r6 || r == .r7 || r == .r8 || r == .r9 || r == .r10

/-- The moves of arguments into `r3`–`r10`, of pointers in `r28`–`r31`. -/
def glueOk (as : List (Reg × Arg)) : Bool := as.all fun x => argReg x.1 && argOk x.2

theorem argOk_ne {d : Reg} (hd : argReg d = true) {a : Arg} (ha : argOk a = true) :
    ∀ p : Ptr, a = .ptr p → p.1 ≠ d := by
  intro p e he
  subst e he
  simp only [argOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ha
  simp only [argReg, Bool.or_eq_true, beq_iff_eq] at hd
  rcases ha.1 with ((h | h) | h) | h <;> rw [h] at hd <;> simp at hd

theorem glue_ok : ∀ {as : List (Reg × Arg)}, glueOk as = true → ∀ s, WP isa (.block (glue as)) s (· = glueSt s as)
  | [], _, s => WP.block_nil rfl
  | (d, a) :: as, h, s => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨⟨hd, ha⟩, hs⟩ := h
    rw [glue, WP.block_append_iff]
    refine WP.mono (arg_ok d ha (argOk_ne hd ha) s) fun s1 e1 => ?_
    subst e1
    exact glue_ok (as := as) hs _

theorem glueSt_mem (s : State) : ∀ as, (glueSt s as).mem = s.mem
  | [] => rfl
  | _ :: as => glueSt_mem _ as
theorem glueSt_rd (s : State) : ∀ as, (glueSt s as).rd = s.rd
  | [] => rfl
  | _ :: as => glueSt_rd _ as
theorem glueSt_wr (s : State) : ∀ as, (glueSt s as).wr = s.wr
  | [] => rfl
  | _ :: as => glueSt_wr _ as
theorem glueSt_sp (s : State) : ∀ as, (glueSt s as).sp = s.sp
  | [] => rfl
  | _ :: as => glueSt_sp _ as
theorem glueSt_lr (s : State) : ∀ as, (glueSt s as).lr = s.lr
  | [] => rfl
  | _ :: as => glueSt_lr _ as

/-- The registers the moves do not write. -/
theorem glueSt_gpr {r : Reg} (hr : argReg r = false) :
    ∀ (s : State) {as : List (Reg × Arg)}, glueOk as = true → (glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at h
    rw [glueSt, glueSt_gpr hr _ (as := as) h.2, gpr_write_of_ne]
    intro e; subst e
    rw [h.1.1] at hr; exact Bool.noConfusion hr

theorem glueSt_pres (s : State) {as : List (Reg × Arg)} (h : glueOk as = true) :
    ∀ r ∈ preserved, (glueSt s as).gpr r = s.gpr r := fun r hr =>
  glueSt_gpr (by revert r; decide) s h

theorem glue_noMem : ∀ as : List (Reg × Arg), (glue as).all noMem = true
  | [] => rfl
  | (d, a) :: as => by
    rw [glue, List.all_append, glue_noMem as, Bool.and_true]
    cases a <;> rfl

/-- The registers the moves of `as` do not write. -/
theorem glueSt_gpr' {r : Reg} : ∀ (s : State) {as : List (Reg × Arg)}, r ∉ as.map Prod.fst →
    (glueSt s as).gpr r = s.gpr r
  | s, [], _ => rfl
  | s, (d, a) :: as, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [glueSt, glueSt_gpr' _ h.2, gpr_write_of_ne _ _ h.1]

/-- An argument's register holds its value after the moves. -/
theorem glueSt_arg (s : State) {d : Reg} {a : Arg} :
    ∀ {as : List (Reg × Arg)}, glueOk as = true → (as.map Prod.fst).Nodup → (d, a) ∈ as →
      (glueSt s as).gpr d = argVal s a
  | [], _, _, hm => absurd hm List.not_mem_nil
  | (d', a') :: as, hg, hn, hm => by
    simp only [glueOk, List.all_cons, Bool.and_eq_true] at hg
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [glueSt]
    rcases List.mem_cons.mp hm with e | hm
    · rw [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rw [glueSt_gpr' _ hn.1, gpr_write_self]
    · rw [glueSt_arg _ hg.2 hn.2 hm]
      have ha : argOk a = true := by
        have := List.all_eq_true.mp hg.2 _ hm
        simp only [Bool.and_eq_true] at this; exact this.2
      cases a with
      | imm v => rfl
      | ptr q =>
        simp only [argVal]
        rw [gpr_write_of_ne]
        intro e
        exact argOk_ne hg.1.1 ha q rfl e

/-! ## Calls -/

/-- The state a callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State := s.callEntry.withRegions rd wr

/-- A call, after the moves of its arguments. -/
theorem callV {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c < 2 ^ 64)
    {as : List (Reg × Arg)} (hg : glueOk as = true) {s : State} {rd wr : List Region}
    (hpre : k.pre (view (glueSt s as) rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept (wr ++ [below s.sp (sdepth c)]) s s' →
      k.post (view (glueSt s as) rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (callAt name c as) s Q := by
  refine WP.seq (WP.mono (glue_ok hg s) fun s1 e => ?_)
  subst e
  refine WP.callAny hv hpre (by rw [glueSt_rd, glueSt_wr]; exact hc) (by rw [glueSt_wr]; exact hw)
    (fun s' hrd hwr hsp hf hcs hp => hQ s' ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩ hp) hd
  · rw [hcs r hr, glueSt_pres s hg r hr]
  · rw [hsp, glueSt_sp]
  · rw [hrd, glueSt_rd]
  · rw [hwr, glueSt_wr]
  · rw [glueSt_mem, glueSt_sp] at hf; exact hf

/-! ## Two runs of a call -/

/-- The preconditions and public data of a callee in two runs, from the states
`a` and `b` it starts from, with the regions `rd` and `wr`. -/
def CallRel (k : Contract isa) (rd wr : List Region) (x y a b : State) : Prop :=
  k.pre (a.callEntry.withRegions rd wr) ∧ k.pre (b.callEntry.withRegions rd wr) ∧
    k.pub (a.callEntry.withRegions rd wr) (b.callEntry.withRegions rd wr) ∧
    Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧ Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr

/-- Two runs of a call leak the same, if the callee's preconditions hold and
its public data agree. -/
theorem callV_tr {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × Arg)} (hg : glueOk as = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∃ rd wr, CallRel k rd wr x y (glueSt x as) (glueSt y as)) :
    RelCT isa P (callAt name c as) fun _ _ => True := by
  unfold callAt
  refine RelCT.seq (RelCT.wpDep (F := fun x x1 => x1 = glueSt x as) (relct_noMem (glue_noMem as))
    fun x y _ => ⟨glue_ok hg x, glue_ok hg y⟩) ?_
  refine RelCT.mono (P := fun (a b : State) => ∃ rw : List Region × List Region, ∃ x y : State,
      CallRel k rw.1 rw.2 x y a b ∧ x.rd = a.rd ∧ x.wr = a.wr ∧ y.rd = b.rd ∧ y.wr = b.wr)
    (RelCT.exists_ fun (rw : List Region × List Region) => RelCT.call hv hct rw.1 rw.2
      fun a b ⟨x, y, h, e1, e2, e3, e4⟩ => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
        exact ⟨h1, h2, h3, by rwa [← e1, ← e2], by rwa [← e2], by rwa [← e3, ← e4], by rwa [← e4]⟩) ?_
    fun _ _ h => h
  rintro a b ⟨-, x, y, hp, rfl, rfl⟩
  obtain ⟨rd, wr, h⟩ := hP x y hp
  exact ⟨(rd, wr), x, y, h, (glueSt_rd x as).symm, (glueSt_wr x as).symm, (glueSt_rd y as).symm,
    (glueSt_wr y as).symm⟩

end VG.Proof.MlDsa.PPC64LE.KeyGen
