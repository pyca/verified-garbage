import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# Registers kept through SSE registers

`Exec.gpr` keeps a register that no instruction writes. Code may also write
a register it has copied into an SSE register (`movq xmm, r64`) and copy it
back (`movq r64, xmm`), as a function that needs every general-purpose
register does with the callee-saved ones. `keeps r c` follows, through `c`,
whether `r` holds its value from the start (`Abs.ok`), and which SSE
registers hold it in their low quadword (`Abs.xs`); `Exec.gpr_keeps` shows
that `r` ends with its value if `keeps r c`. Any write to the vector
registers but `movq xmm, r64` forgets the SSE registers.
-/

namespace VG.X86_64.KeepReg

/-- What is known of a register's value `v`: whether the register holds it,
and the SSE registers whose low quadword is `v`. -/
structure Abs where
  ok : Bool
  xs : RegSet XReg

/-- Whether an instruction may write a vector register. -/
def writesVec : Instr → Bool
  | .movdquLoad .. | .xop _ | .vop _ | .vmovdquLoad .. | .vbroadcasti128 .. | .vbinLoad .. | .zop _
  | .vmovdqu32Load .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpmadd52Load ..
  | .eop _ | .evLoad .. | .evMadd52Load .. => true
  | _ => false

/-- What is known of `r` after an instruction. -/
def step (r : Reg) (a : Abs) : Instr → Abs
  | .xop (.movq x q) => { a with xs := bif a.ok && q == r then a.xs.insert x else a.xs.erase x }
  | .movqR d x => bif d == r then { a with ok := a.xs.mem x } else a
  | i => { ok := a.ok && !Taint.clobbers i r, xs := bif writesVec i then .empty else a.xs }

/-- `a` says no more than `b`. -/
def le (a b : Abs) : Bool := (!a.ok || b.ok) && a.xs.subset b.xs

/-- What both say. -/
def meet (a b : Abs) : Abs := ⟨a.ok && b.ok, a.xs.inter b.xs⟩

/-- `is.foldl (step r) ⟨ok, ⟨xs⟩⟩`, for the kernel: it looks at what is
known before each instruction, so that it computes each step's value before
the next (the fold would leave a term as deep as the block, too deep for the
kernel in a long one). -/
def run (r : Reg) (is : List Instr) : Bool → Nat → Abs :=
  List.rec (fun ok xs => ⟨ok, ⟨xs⟩⟩)
    (fun i _ ih ok xs =>
      let g := fun a : Abs => ih a.ok a.xs.bits
      bif ok then (bif Nat.beq xs 0 then g (step r ⟨true, ⟨0⟩⟩ i) else g (step r ⟨true, ⟨xs⟩⟩ i))
      else (bif Nat.beq xs 0 then g (step r ⟨false, ⟨0⟩⟩ i) else g (step r ⟨false, ⟨xs⟩⟩ i))) is

theorem run_eq (r : Reg) : ∀ (is : List Instr) (a : Abs), run r is a.ok a.xs.bits = is.foldl (step r) a
  | [], _ => rfl
  | i :: is, ⟨ok, ⟨xs⟩⟩ => by
    have e : ∀ b : Abs, run r is b.ok b.xs.bits = is.foldl (step r) b := run_eq r is
    show (bif ok then (bif Nat.beq xs 0 then run r is (step r ⟨true, ⟨0⟩⟩ i).ok (step r ⟨true, ⟨0⟩⟩ i).xs.bits
        else run r is (step r ⟨true, ⟨xs⟩⟩ i).ok (step r ⟨true, ⟨xs⟩⟩ i).xs.bits)
      else (bif Nat.beq xs 0 then run r is (step r ⟨false, ⟨0⟩⟩ i).ok (step r ⟨false, ⟨0⟩⟩ i).xs.bits
        else run r is (step r ⟨false, ⟨xs⟩⟩ i).ok (step r ⟨false, ⟨xs⟩⟩ i).xs.bits)) = _
    rw [List.foldl_cons]
    cases ok <;> cases h : Nat.beq xs 0 <;> simp only [Bool.cond_true, Bool.cond_false, e] <;>
      rw [Nat.eq_of_beq_eq_true h]

/-- What is known of `r` after `c`, from `a`; a loop's body must keep what
is known on entry. Calls and frames are not followed. -/
def check (r : Reg) : Prog isa → Abs → Option Abs
  | .block is, a => some (run r is a.ok a.xs.bits)
  | .seq c d, a => (check r c a).bind (check r d)
  | .ite _ c d, a => (check r c a).bind fun x => (check r d a).map (meet x)
  | .loop b _, a => (check r b a).bind fun x => bif le a x then some a else none
  | .call .., _ => none
  | .frame .., _ => none

/-- `r` ends `c` with the value it starts with. -/
def keeps (r : Reg) (c : Prog isa) : Bool :=
  match check r c ⟨true, .empty⟩ with
  | some a => a.ok
  | none => false

/-! ## Soundness -/

/-- What `a` says of `r` and `v` holds in `s`. -/
def Holds (r : Reg) (v : BitVec 64) (a : Abs) (s : State) : Prop :=
  (a.ok = true → s.gpr r = v) ∧ ∀ x ∈ a.xs, (s.xmm x).extractLsb' 0 64 = v

theorem Holds.mono {r : Reg} {v : BitVec 64} {a b : Abs} {s : State} (hle : le a b = true)
    (h : Holds r v b s) : Holds r v a s := by
  simp only [KeepReg.le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
  refine ⟨fun ho => h.1 (hle.1.resolve_left (by rw [ho]; decide)), fun x hx => h.2 x ?_⟩
  exact RegSet.mem_of_subset hle.2 hx

theorem Holds.meet_left {r : Reg} {v : BitVec 64} {a b : Abs} {s : State} (h : Holds r v a s) :
    Holds r v (meet a b) s :=
  ⟨fun ho => h.1 (by simp only [meet, Bool.and_eq_true] at ho; exact ho.1),
    fun x hx => h.2 x (RegSet.mem_inter.mp hx).1⟩

theorem Holds.meet_right {r : Reg} {v : BitVec 64} {a b : Abs} {s : State} (h : Holds r v b s) :
    Holds r v (meet a b) s :=
  ⟨fun ho => h.1 (by simp only [meet, Bool.and_eq_true] at ho; exact ho.2),
    fun x hx => h.2 x (RegSet.mem_inter.mp hx).2⟩

/-- An instruction that writes no vector register keeps the SSE registers. -/
theorem exec_xmm {i : Instr} (hw : writesVec i = false) {s s' : State} (h : exec i s = some s') :
    s'.xmm = s.xmm := by
  cases hd : Taint.dstOf i with
  | some d => exact (Taint.exec_nonstore_xmm hd h).2.2.2.1
  | none =>
    cases i <;> simp only [Taint.dstOf, reduceCtorEq, writesVec, Bool.true_eq_false] at hd hw
    all_goals first
      | (simp only [exec, reduceCtorEq] at h; done)
      | (simp only [exec, Option.some.injEq] at h; subst h; rfl)
      | (simp only [exec, State.store64, State.store32, State.store8, State.store128, State.store512,
          State.store256] at h
         split at h <;> cases h; rfl)
      | (rename_i len _ _; cases len <;>
          (simp only [exec, State.store128, State.store256] at h; split at h <;> cases h; rfl))
      | (simp only [exec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
         split at h <;> cases h; rfl)
      | (simp only [exec, execMulx] at h; split at h
         · cases h
         · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl)

/-- What is known after an instruction other than `movq`. -/
theorem other_holds {r : Reg} {v : BitVec 64} {a : Abs} {i : Instr} {s s' : State}
    (h : exec i s = some s') (ha : Holds r v a s) :
    Holds r v ⟨a.ok && !Taint.clobbers i r, bif writesVec i then .empty else a.xs⟩ s' := by
  refine ⟨fun ho => ?_, fun y hy => ?_⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at ho
    exact (exec_gpr ho.2 h).trans (ha.1 ho.1)
  · cases hw : writesVec i
    · simp only [hw, Bool.cond_false] at hy; rw [exec_xmm hw h]; exact ha.2 y hy
    · simp only [hw, Bool.cond_true] at hy; exact absurd hy (RegSet.not_mem_empty y)

theorem step_holds {r : Reg} {v : BitVec 64} {a : Abs} {i : Instr} {s s' : State}
    (h : exec i s = some s') (ha : Holds r v a s) : Holds r v (step r a i) s' := by
  cases i
  case xop op =>
    cases op
    case movq x q =>
      simp only [exec, XOp.exec, Option.some.injEq] at h
      subst h
      simp only [step]
      refine ⟨fun ho => ha.1 ho, fun y hy => ?_⟩
      simp only [State.setXmm]
      cases e : (a.ok && q == r)
      · simp only [e, Bool.cond_false] at hy
        obtain ⟨hne, hy⟩ := RegSet.mem_erase.mp hy
        simp only [hne, ite_false]; exact ha.2 y hy
      · simp only [e, Bool.cond_true] at hy
        simp only [Bool.and_eq_true, beq_iff_eq] at e
        by_cases hyx : y = x
        · subst hyx; obtain ⟨ho, rfl⟩ := e
          simp only [ite_true]; rw [← ha.1 ho]
          ext k hk; simp only [BitVec.getElem_extractLsb']; rw [BitVec.getLsbD_append]; simp [hk]
        · simp only [hyx, ite_false]
          exact ha.2 y ((RegSet.mem_insert.mp hy).resolve_left hyx)
    all_goals exact other_holds h ha
  case movqR d x =>
    simp only [exec, Option.some.injEq] at h
    subst h
    simp only [step]
    by_cases hd : d = r
    · subst hd
      simp only [beq_self_eq_true, Bool.cond_true]
      refine ⟨fun ho => ?_, fun y hy => ha.2 y hy⟩
      simp only [State.setReg, ite_true]
      exact ha.2 x ho
    · have hd' : (d == r) = false := by simpa using hd
      simp only [hd', Bool.cond_false]
      refine ⟨fun ho => ?_, fun y hy => ha.2 y hy⟩
      simp only [State.setReg, Ne.symm hd, ite_false]
      exact ha.1 ho
  all_goals exact other_holds h ha

theorem execBlock_holds {r : Reg} {v : BitVec 64} :
    ∀ {is : List Instr} {a : Abs} {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) →
      Holds r v a s → Holds r v (is.foldl (step r) a) s'
  | [], _, s, s', t, h, ha => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ha
  | i :: is, a, s, s', t, h, ha => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact execBlock_holds (is := is) (a := step r a i) (t := p.2) (by rw [hp]) (step_holds h₁ ha)

theorem Exec.holds {r : Reg} {v : BitVec 64} {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : ∀ {a b : Abs}, check r c a = some b → Holds r v a s → Holds r v b s' := by
  induction h with
  | block he =>
    intro a b hc ha
    simp only [check, Option.some.injEq, run_eq] at hc
    subst hc
    exact execBlock_holds he ha
  | seq _ _ ih₁ ih₂ =>
    intro a b hc ha
    simp only [check, Option.bind_eq_some_iff] at hc
    obtain ⟨m, hm, hb⟩ := hc
    exact ih₂ hb (ih₁ hm ha)
  | iteT _ _ ih =>
    intro a b hc ha
    simp only [check, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨x, hx, y, -, rfl⟩ := hc
    exact (ih hx ha).meet_left
  | iteF _ _ ih =>
    intro a b hc ha
    simp only [check, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨x, -, y, hy, rfl⟩ := hc
    exact (ih hy ha).meet_right
  | loopExit _ _ ih =>
    intro a b hc ha
    simp only [check, Option.bind_eq_some_iff] at hc
    obtain ⟨x, hx, hb⟩ := hc
    cases hle : le a x
    · simp only [hle, Bool.cond_false, reduceCtorEq] at hb
    · simp only [hle, Bool.cond_true, Option.some.injEq] at hb
      subst hb
      exact (ih hx ha).mono hle
  | loopNext _ _ _ ih₁ ih₂ =>
    intro a b hc ha
    have hc' := hc
    simp only [check, Option.bind_eq_some_iff] at hc
    obtain ⟨x, hx, hb⟩ := hc
    cases hle : le a x
    · simp only [hle, Bool.cond_false, reduceCtorEq] at hb
    · exact ih₂ hc' ((ih₁ hx ha).mono hle)
  | call =>
    intro a b hc
    simp only [check, reduceCtorEq] at hc
  | frame =>
    intro a b hc
    simp only [check, reduceCtorEq] at hc

/-- A register that `keeps` follows through `c` ends with its value. -/
theorem _root_.VG.X86_64.Exec.gpr_keeps {c : Prog isa} {r : Reg} (hk : keeps r c = true) {s s' : State}
    {t : List Leak} (h : Exec isa c s t s') : s'.gpr r = s.gpr r := by
  unfold keeps at hk
  split at hk
  · rename_i a ha
    exact (Exec.holds (v := s.gpr r) h ha ⟨fun _ => rfl, fun x hx => absurd hx (RegSet.not_mem_empty x)⟩).1 hk
  · cases hk

end VG.X86_64.KeepReg
