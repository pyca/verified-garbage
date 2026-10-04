import VerifiedGarbage.Proof.Framework.X86_64.LaneSse

/-!
# x86-64: VEX.128 blocks as SSE blocks on the lower lanes

A `VEX.128` instruction does to the lower 128-bit lane of the vector
registers what an SSE instruction does to the SSE registers (`VBinOp.sse`),
and clears the upper lane of its destination. For a block of them
(`lane0Block`), what it leaves in the lower lanes, with the general-purpose
registers, memory and flags, is what the corresponding SSE block leaves from
`s.proj 0` (`WP.lane0`), so that proofs about SSE code hold of the `VEX.128`
code that does the same with three operands.
-/

namespace VG.X86_64

/-- The SSE instructions that do to the lower lane what a `VEX.128`
instruction does, if it is one: `vop d, a, b` is `movdqa d, a` then
`op d, b` (just `op d, b` if `a` is `d`; not if only `b` is). -/
def lane0V : VOp → Option (List Instr)
  | .vbin op .l128 d a b =>
    if a = d then some [.xop (.bin op.sse d b)]
    else if b = d then none else some [.xop (.bin .movdqa d a), .xop (.bin op.sse d b)]
  | .vshift op .l128 d a n =>
    if a = d then some [.xop (.shift op d n)] else some [.xop (.bin .movdqa d a), .xop (.shift op d n)]
  | .vpclmulqdq .l128 d a b n =>
    if a = d then some [.xop (.pclmulqdq d b n)]
    else if b = d then none else some [.xop (.bin .movdqa d a), .xop (.pclmulqdq d b n)]
  | .vpshufd .l128 d a o => some [.xop (.pshufd d a o)]
  | .vmovdqa .l128 d a => some [.xop (.bin .movdqa d a)]
  | .vmovq d r => some [.xop (.movq d r)]
  | _ => none

@[inherit_doc lane0V]
def lane0 : Instr → Option (List Instr)
  | .vop o => lane0V o
  | .vmovdquLoad .l128 d m => some [.movdquLoad d m]
  | .vmovdquStore .l128 m r => some [.movdquStore m r]
  | .movImm64 d v => some [.movImm64 d v]
  | _ => none

/-- The SSE block of a block of `VEX.128` instructions. -/
def lane0Block : List Instr → Option (List Instr)
  | [] => some []
  | i :: is => match lane0 i, lane0Block is with
    | some a, some b => some (a ++ b)
    | _, _ => none

theorem proj_setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    (s.setV .l128 d lo hi).proj 0 = (s.proj 0).setXmm d lo := by
  cases s
  simp only [State.proj, State.setV, State.setXmm, State.lane, State.mk.injEq, and_true, true_and]
  funext r
  by_cases h : r = d <;> simp [h]

theorem proj_lane0 (s : State) (r : XReg) : (s.proj 0).xmm r = s.xmm r := by
  simp [State.lane]

theorem proj_ea (s : State) (m : MemOp) : (s.proj 0).ea m = s.ea m := rfl

theorem proj_setReg (s : State) (d : Reg) (v : BitVec 64) : (s.setReg d v).proj 0 = (s.proj 0).setReg d v := by
  cases s; rfl

theorem proj_setMem (s : State) (a : Addr) (v : BitVec 128) :
    ({ s with mem := s.mem.writeW a v } : State).proj 0 = { s.proj 0 with mem := (s.proj 0).mem.writeW a v } := by
  cases s; rfl

/-- `vop d, a, b` from `movdqa d, a` and `op d, b`, on the lower lane. -/
theorem two_ops {s : State} {d a b : XReg} (hb : b ≠ d) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    ((s.proj 0).setXmm d (s.lane a 0)).setXmm d (f (((s.proj 0).setXmm d (s.lane a 0)).xmm d)
      (((s.proj 0).setXmm d (s.lane a 0)).xmm b)) = (s.proj 0).setXmm d (f (s.lane a 0) (s.lane b 0)) := by
  rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hb, setXmm_setXmm, State.proj_xmm]

theorem lane0_ok {i : Instr} {ss : List Instr} (h : lane0 i = some ss) (s : State) :
    (exec i s).map (·.proj 0) = runBlock isa ss (s.proj 0) := by
  cases i
  all_goals try (simp only [lane0, reduceCtorEq] at h)
  case movImm64 d v =>
    cases h; simp [runBlock, exec, isa, proj_setReg]
  case vmovdquLoad len d m =>
    cases len
    · simp only [Option.some.injEq] at h; subst h
      simp only [exec, runBlock, isa, State.load128, State.proj_rd, State.proj_wr, State.proj_mem, proj_ea]
      by_cases hin : InRegions (s.rd ++ s.wr) (s.ea m) 16 <;> simp [hin, proj_setV128]
    · simp at h
  case vmovdquStore len m r =>
    cases len
    · simp only [Option.some.injEq] at h; subst h
      simp only [exec, runBlock, isa, State.store128, State.proj_wr, proj_ea, proj_lane0]
      by_cases hin : InRegions s.wr (s.ea m) 16
      · simp only [hin, ite_true, Option.map_some, Option.bind_some]
        cases s; rfl
      · simp [hin]
    · simp at h
  case vop o =>
    cases o
    all_goals try (simp only [lane0V, reduceCtorEq] at h; done)
    case vbin op len d a b =>
      cases len
      · simp only [lane0V] at h
        simp only [exec, VOp.exec, Option.map_some, proj_setV128]
        split at h
        · subst_vars; cases h
          simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm]
        · split at h
          · cases h
          · rename_i h1 h2; cases h
            simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm, eval_movdqa]
            rw [two_ops h2 op.sse.eval]
      · simp [lane0V] at h
    case vpclmulqdq len d a b n =>
      cases len
      · simp only [lane0V] at h
        simp only [exec, VOp.exec, Option.map_some, proj_setV128]
        split at h
        · subst_vars; cases h
          simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm]
        · split at h
          · cases h
          · rename_i h1 h2; cases h
            simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm, eval_movdqa]
            rw [two_ops h2 (fun x y => pclmul x y n)]
      · simp [lane0V] at h
    case vshift op len d a n =>
      cases len
      · simp only [lane0V] at h
        simp only [exec, VOp.exec, Option.map_some, proj_setV128]
        split at h
        · subst_vars; cases h
          simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm]
        · cases h
          simp only [runBlock, isa, exec, XOp.exec, Option.bind_some, State.proj_xmm, eval_movdqa]
          rw [RegUpd.xmm_setXmm_self, setXmm_setXmm]
      · simp [lane0V] at h
    case vpshufd len d a o =>
      cases len
      · simp only [lane0V, Option.some.injEq] at h; subst h
        simp only [exec, VOp.exec, Option.map_some, proj_setV128, runBlock, isa, XOp.exec,
          Option.bind_some, State.proj_xmm]
      · simp [lane0V] at h
    case vmovdqa len d a =>
      cases len
      · simp only [lane0V, Option.some.injEq] at h; subst h
        simp only [exec, VOp.exec, Option.map_some, proj_setV128, runBlock, isa, XOp.exec,
          Option.bind_some, State.proj_xmm, eval_movdqa]
      · simp [lane0V] at h
    case vmovq d r =>
      simp only [lane0V, Option.some.injEq] at h; subst h
      simp only [exec, VOp.exec, Option.map_some, proj_setV128, runBlock, isa, XOp.exec,
        Option.bind_some, State.proj_gpr]

theorem lane0Block_ok {vs ss : List Instr} (h : lane0Block vs = some ss) (s : State) :
    (runBlock isa vs s).map (·.proj 0) = runBlock isa ss (s.proj 0) := by
  induction vs generalizing ss s with
  | nil =>
    simp only [lane0Block, Option.some.injEq] at h; subst h
    rfl
  | cons i is ih =>
    simp only [lane0Block] at h
    split at h
    · rename_i a b ha hb
      cases h
      rw [runBlock_append, ← lane0_ok ha s]
      show ((exec i s).bind (runBlock isa is)).map _ = _
      cases exec i s with
      | none => rfl
      | some s₁ => exact ih hb s₁
    · cases h

/-- The vector register a `VEX.128` instruction of `lane0` writes, if any. -/
def vdst : Instr → Option XReg
  | .vop (.vbin _ _ d _ _) | .vop (.vpclmulqdq _ d _ _ _) | .vop (.vshift _ _ d _ _)
  | .vop (.vpshufd _ d _ _) | .vop (.vmovdqa _ d _) | .vop (.vmovq d _) | .vmovdquLoad _ d _ => some d
  | _ => none

/-- An instruction of `lane0` keeps the upper lanes of the registers it does
not write. -/
theorem lane0_hi {i : Instr} {ss : List Instr} (h : lane0 i = some ss) {s s' : State}
    (e : exec i s = some s') (r : XReg) (hr : vdst i ≠ some r) : s'.ymmHi r = s.ymmHi r := by
  cases i
  all_goals try (simp only [lane0, reduceCtorEq] at h)
  case movImm64 d v => cases e; rfl
  case vmovdquLoad len d m =>
    have hrd : r ≠ d := fun h => hr (by rw [h]; rfl)
    cases len
    · simp only [exec, Option.map_eq_some_iff] at e
      obtain ⟨v, -, rfl⟩ := e
      simp [State.setV, hrd]
    · simp at h
  case vmovdquStore len m r' =>
    cases len
    · simp only [exec, State.store128] at e
      split at e
      · cases e; rfl
      · cases e
    · simp at h
  case vop o =>
    simp only [exec, Option.some.injEq] at e
    subst e
    cases o <;> simp only [vdst, ne_eq, Option.some.injEq] at hr
    all_goals first
      | (simp [VOp.exec, State.setV, Ne.symm hr]; done)
      | (simp [lane0V] at h; done)
      | skip

theorem lane0Block_hi {vs ss : List Instr} (h : lane0Block vs = some ss) {s s' : State}
    (e : runBlock isa vs s = some s') (r : XReg) (hr : r ∉ vs.filterMap vdst) : s'.ymmHi r = s.ymmHi r := by
  induction vs generalizing ss s with
  | nil => cases e; rfl
  | cons i is ih =>
    simp only [lane0Block] at h
    split at h
    · rename_i a b ha hb
      cases h
      have e₀ : (exec i s).bind (runBlock isa is) = some s' := e
      cases e₁ : exec i s with
      | none => rw [e₁] at e₀; cases e₀
      | some s₁ =>
        rw [e₁, Option.bind_some] at e₀
        have hr' : vdst i ≠ some r ∧ r ∉ is.filterMap vdst := by
          constructor
          · intro hv; exact hr (by simp [hv])
          · intro hm; exact hr (by cases hv : vdst i <;> simp [hv] at hm ⊢ <;> simp_all)
        rw [ih hb e₀ hr'.2, lane0_hi ha e₁ r hr'.1]
    · cases h

/-- Whether an instruction of `lane0` leaves the general-purpose registers
alone: all but `movImm64`. -/
def noGpr : Instr → Bool
  | .movImm64 .. => false
  | _ => true

theorem lane0_gpr {i : Instr} {ss : List Instr} (h : lane0 i = some ss) (hn : noGpr i = true) {s s' : State}
    (e : exec i s = some s') : s'.gpr = s.gpr := by
  cases i
  all_goals try (simp only [lane0, reduceCtorEq] at h)
  case movImm64 => simp [noGpr] at hn
  case vmovdquLoad len d m =>
    cases len
    · simp only [exec, Option.map_eq_some_iff] at e
      obtain ⟨v, -, rfl⟩ := e
      simp
    · simp at h
  case vmovdquStore len m r' =>
    cases len
    · simp only [exec, State.store128] at e
      split at e
      · cases e; rfl
      · cases e
    · simp at h
  case vop o =>
    simp only [exec, Option.some.injEq] at e
    subst e
    exact VOp.exec_gpr o s

theorem lane0Block_gpr {vs ss : List Instr} (h : lane0Block vs = some ss) (hn : vs.all noGpr = true)
    {s s' : State} (e : runBlock isa vs s = some s') : s'.gpr = s.gpr := by
  induction vs generalizing ss s with
  | nil => cases e; rfl
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hn
    simp only [lane0Block] at h
    split at h
    · rename_i a b ha hb
      cases h
      have e₀ : (exec i s).bind (runBlock isa is) = some s' := e
      cases e₁ : exec i s with
      | none => rw [e₁] at e₀; cases e₀
      | some s₁ =>
        rw [e₁, Option.bind_some] at e₀
        rw [ih hb hn.2 e₀, lane0_gpr ha hn.1 e₁]
    · cases h

/-- A block of `VEX.128` instructions does to the lower lanes what its SSE
block does to the SSE registers, and keeps the upper lanes of the registers
it does not write. -/
theorem WP.lane0 {vs ss : List Instr} (h : lane0Block vs = some ss) {s : State} {Q : State → Prop}
    (hq : WP isa (.block ss) (s.proj 0) Q) :
    WP isa (.block vs) s fun s' => Q (s'.proj 0) ∧ (∀ r, r ∉ vs.filterMap vdst → s'.lane r 1 = s.lane r 1) ∧
      (vs.all noGpr = true → s'.gpr = s.gpr) := by
  obtain ⟨t, et, qt⟩ := WP.runBlock_of hq
  have e := lane0Block_ok h s
  rw [et] at e
  cases e' : runBlock isa vs s with
  | none => rw [e'] at e; cases e
  | some s' =>
    rw [e'] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact WP.of_runBlock ⟨s', e', e ▸ qt, fun r hr => by
      simp only [State.lane, Nat.one_ne_zero, ite_false]; exact lane0Block_hi h e' r hr,
      fun hn => lane0Block_gpr h hn e'⟩

end VG.X86_64
