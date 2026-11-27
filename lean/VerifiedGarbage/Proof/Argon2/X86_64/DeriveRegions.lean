module

import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.Argon2.X86_64.Parameters
public import VerifiedGarbage.Proof.Argon2.X86_64.Divide
public import VerifiedGarbage.Proof.Argon2.X86_64.Memory
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.X86_64.DivideCT
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Impl.Argon2.X86_64.Derive
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Argon2.X86_64.DeriveNormalize`, which this module and modules that import it used -/

section

/-! Normalize u32 stack arguments without assuming anything about their upper bits. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Impl.Argon2.X86_64.Derive

structure Normalized (s t : State) (d : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d)
    (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem normalize_ok (s : State) (d : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block (normalize d)) s (Normalized s · d) := by
  apply WP.of_runBlock
  simp only [normalize, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    read, write, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem Normalized.word {s t : State} {d : Nat} (h : Normalized s t d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64) := by
  rw [h.regs .rbp (by decide), h.mem, Mem.readW_writeW_self64]

theorem Normalized.frame {s t : State} {d : Nat} (h : Normalized s t d) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem Normalized.other_word {s t : State} {d : Nat} (h : Normalized s t d)
    (e : Nat) (separate : e + 8 ≤ d ∨ d + 8 ≤ e) (ed : e + 8 < 2 ^ 64) (dd : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide), h.mem]
  exact Mem.readW_writeW_sep (Offset.sep _ separate (Nat.le_of_lt ed) (Nat.le_of_lt dd)) (by decide)

end VG.Proof.Argon2.X86_64.Derive

end

end

/-! ### `Argon2.X86_64.DeriveSaved`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.DeriveFrame`, which this module and modules that import it used -/

section

/-! Compose the nested saved-register frames and the 272-byte local allocation. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def frameStart (s : State) : List Reg → State
  | [] => pushed (List.replicate 34 .rax) s
  | r :: rs => frameStart (pushed [r] s) rs

def frameEnd (s : State) : List Reg → State
  | [] => popped .rax 34 s
  | r :: rs => popped r 1 (frameEnd s rs)

theorem frameEnd_metadata (s t : State) (rs : List Reg)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (wr : t.wr = (frameStart s rs).wr) :
    (frameEnd t rs).gpr .rsp = s.gpr .rsp ∧ (frameEnd t rs).wr = s.wr := by
  induction rs generalizing s with
  | nil =>
    constructor
    · rw [frameEnd, popped_rsp, sp, frameStart, pushed_rsp]
      simp only [List.length_replicate, Nat.reduceMul, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, wr, frameStart, pushed_wr]; rfl
  | cons r rs ih =>
    obtain ⟨innerSp, innerWr⟩ := ih (pushed [r] s) sp wr
    constructor
    · rw [frameEnd, popped_rsp, innerSp, pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one, BitVec.sub_add_cancel]
    · rw [frameEnd, popped_wr, innerWr, pushed_wr]; rfl

theorem frameEnd_mem (s : State) (rs : List Reg) : (frameEnd s rs).mem = s.mem := by
  induction rs with
  | nil => exact popped_mem ..
  | cons r rs ih => exact (popped_mem ..).trans ih

/-- The nested frames, whose bytes, `272 + 8 * rs.length` below `rsp`, each hold
whatever they hold once released. -/
theorem frame_ok (s : State) (rs : List Reg) (body : Prog isa) (Q : State → Prop)
    (notSp : .rsp ∉ rs) (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (run : WP isa body (frameStart s rs) fun t =>
      t.gpr .rsp = (frameStart s rs).gpr .rsp ∧ t.wr = (frameStart s rs).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (272 + 8 * rs.length), 272 + 8 * rs.length⟩] t.mem m →
        Q { frameEnd t rs with mem := m, unknowns := u }) :
    WP isa (Impl.Argon2.X86_64.Derive.frame body rs) s Q := by
  induction rs generalizing s Q with
  | nil =>
    exact WP.frame (by decide) (by decide) (by decide) (by simpa using space) run
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have pushedBound : ((pushed [r] s).gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      exact toNat_sub_ofNat (by simp only [List.length_cons] at space; omega_using [space])
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushedBound]; simp only [List.length_cons] at space; omega_using [space]
    have hp : (pushed [r] s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8 := by
      rw [pushed_rsp]; rfl
    have hlt := (s.gpr .rsp).isLt
    simp only [List.length_cons] at space
    apply WP.frame (by simp) (by simpa using notSp.1) (Ne.symm notSp.1)
      (by simp only [List.length_singleton, Nat.mul_one]; omega_using [space])
    apply ih (pushed [r] s) (fun t => t.gpr .rsp = (pushed [r] s).gpr .rsp ∧
      t.wr = (pushed [r] s).wr ∧ ∀ m u,
        Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (8 * [r].length), 8 * [r].length⟩] t.mem m →
        Q { popped r [r].length t with mem := m, unknowns := u }) notSp.2 innerSpace
    apply run.mono
    rintro t ⟨sp, wr, result⟩
    obtain ⟨endSp, endWr⟩ := frameEnd_metadata (pushed [r] s) t rs sp wr
    refine ⟨sp, wr, fun m₁ u₁ fm₁ => ⟨endSp, endWr, fun m₂ u₂ fm₂ => ?_⟩⟩
    replace fm₂ : Frame [⟨s.gpr .rsp - BitVec.ofNat 64 8, 8⟩] m₁ m₂ := fm₂
    have slot : ∀ i < 1, m₁.readW ((frameEnd t rs).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 =
        (frameEnd t rs).mem.readW ((frameEnd t rs).gpr .rsp + BitVec.ofNat 64 (8 * i)) 64 := by
      intro i hi
      simp only [Nat.lt_one_iff] at hi; subst hi
      rw [frameEnd_mem, endSp, Nat.mul_zero, BitVec.add_zero]
      refine fm₁.readW (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact Offset.base_disjoint_below _ (by omega_using [space, hlt])
    show Q { popped r 1 { frameEnd t rs with mem := m₁, unknowns := u₁ } with mem := m₂, unknowns := u₂ }
    rw [popped_withMem slot]
    refine result m₂ u₂ ((fm₁.sub ?_).trans (fm₂.sub ?_))
    · intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hp, BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Offset.sub_below _ (by simp only [List.length_cons]; omega_using [])
        (by simp only [List.length_cons]; omega_using [])
    · intro r' hr'
      simp only [List.mem_singleton] at hr'; subst hr'
      exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ (by simp only [List.length_cons]; omega_using [])
        (by simp only [List.length_cons]; omega_using [])⟩

end VG.Proof.Argon2.X86_64.Derive

end

end

/-! Merged from `Proof.Argon2.X86_64.DeriveFrameState`. -/

@[expose] public section

section
/-! Exact stack depth and memory modified by the entry-point prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_sp (s : State) (rs : List Reg) :
    (frameStart s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (272 + 8 * rs.length) := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_rsp]; rfl
  | cons r rs ih =>
    rw [frameStart, ih, pushed_rsp]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp - BitVec.ofNat 64 n) (by omega_using [])

theorem frameStart_reg (s : State) (rs : List Reg) (r : Reg) (notSp : r ≠ .rsp) :
    (frameStart s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact pushed_gpr _ _ notSp
  | cons x xs ih => exact (ih (pushed [x] s)).trans (pushed_gpr _ _ notSp)

theorem frameStart_rd (s : State) (rs : List Reg) : (frameStart s rs).rd = s.rd := by
  induction rs generalizing s with
  | nil => exact pushed_rd ..
  | cons r rs ih => exact (ih (pushed [r] s)).trans (pushed_rd ..)

theorem frameStart_frame (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [below (s.gpr .rsp) (272 + 8 * rs.length)] s.mem (frameStart s rs).mem := by
  induction rs generalizing s with
  | nil =>
    exact (pushRegs_mem s (List.replicate 34 .rax) (by decide) (by simpa using space)).1
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega_using [space]
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega_using [space]
    have outer := (pushRegs_mem s [r] (by simpa using notSp.1)
      (by simpa using enough)).1
    have inner := ih (pushed [r] s) notSp.2 innerSpace
    apply (outer.sub ?_).trans (inner.sub ?_)
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub_below (s.gpr .rsp) (by simp only [List.length_cons, List.length_nil]; omega_using [])
        (by simp only [List.length_singleton, Nat.mul_one]; omega_using [])
    · intro region hr
      simp only [List.mem_singleton] at hr; subst region
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [pushed_rsp]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one, below]
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + (272 + 8 * rs.length) = 272 + 8 * (rs.length + 1) by omega_using []]
      exact Region.sub_prefix (by omega_using [])

end VG.Proof.Argon2.X86_64.Derive
end

/-! The nested prologue stores every callee-saved register at its exact ABI slot. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_word (s : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat) (j : Nat) (bound : j < rs.length) :
    (frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s j with
  | nil => exact absurd bound (Nat.not_lt_zero _)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have enough : 8 ≤ (s.gpr .rsp).toNat := by simp only [List.length_cons] at space; omega_using [space]
    have innerSpace : 272 + 8 * rs.length ≤ ((pushed [r] s).gpr .rsp).toNat := by
      rw [pushed_rsp]
      simp only [List.length_singleton, Nat.mul_one]
      rw [toNat_sub_ofNat enough]
      simp only [List.length_cons] at space; omega_using [space]
    cases j with
    | zero =>
      have stored := (pushRegs_mem s [r] (by simpa using notSp.1)
        (by simpa using enough)).2 0 (by simp)
      have inner := frameStart_frame (pushed [r] s) rs notSp.2 innerSpace
      have unchanged : (frameStart (pushed [r] s) rs).mem.readW ((pushed [r] s).gpr .rsp) 64 =
          (pushed [r] s).mem.readW ((pushed [r] s).gpr .rsp) 64 := inner.readW
        (r := ⟨(pushed [r] s).gpr .rsp, 8⟩) (Region.contains_self _ _) (by
          intro region hr
          simp only [List.mem_singleton] at hr; subst region
          apply Offset.base_disjoint_below
          have limit := (s.gpr .rsp).isLt
          simp only [List.length_cons] at space; omega_using [space]) (by decide)
      rw [pushed_rsp] at unchanged
      simp only [List.length_singleton, Nat.mul_one] at unchanged
      exact unchanged.trans stored
    | succ j =>
      have word := ih (pushed [r] s) notSp.2 innerSpace j (by simpa using bound)
      rw [pushed_rsp, pushed_gpr _ _ (fun h => notSp.2 (h ▸ List.getElem_mem _))] at word
      simp only [List.length_singleton, Nat.mul_one] at word
      rw [BitVec.sub_sub, ← BitVec.ofNat_add,
        show 8 + 8 * (j + 1) = 8 * (j + 1 + 1) by omega_using []] at word
      exact word

end VG.Proof.Argon2.X86_64.Derive

end

end

/-! ### `Argon2.X86_64.DeriveAbi`, which this module and modules that import it used -/

section

/-! Decode the reviewed System V contract without requiring normalized upper bits. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def abiWord (s : State) (d : Nat) : Addr := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64
def abiParams (s : State) : Spec.Argon2.Params := Spec.Argon2.params
  ((s.gpr .rdi).setWidth 32).toNat ((s.gpr .r9).setWidth 32).toNat
  ((abiWord s 8).setWidth 32).toNat ((abiWord s 16).setWidth 32).toNat (abiWord s 96).toNat

def abiInputs (s : State) : List Region :=
  [⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩,
    ⟨abiWord s 32, (abiWord s 40).toNat⟩, ⟨abiWord s 48, (abiWord s 56).toNat⟩]
def abiMatrix (s : State) : Region := ⟨abiWord s 64, (abiWord s 72).toNat * 1024⟩
def abiWork (s : State) : Region := ⟨abiWord s 80, 16384⟩
def abiOutput (s : State) : Region := ⟨abiWord s 88, (abiWord s 96).toNat⟩
def abiArguments (s : State) : Region := ⟨s.gpr .rsp + BitVec.ofNat 64 8, 96⟩
def abiBuffers (s : State) : List (Region × Bool) :=
  (abiInputs s).map (·, false) ++ [(abiMatrix s, true), (abiWork s, true), (abiOutput s, true)]

structure AbiEnvironment (s : State) : Prop where
  stack : 344 ≤ (s.gpr .rsp).toNat
  wrap : (s.gpr .rsp).toNat + 104 ≤ 2 ^ 64
  rd : s.rd = abiInputs s ++ [abiArguments s]
  wr : s.wr = [abiMatrix s, abiWork s, abiOutput s]
  pairs : (abiBuffers s ++ [(abiArguments s, false)]).Pairwise
    (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  reserved : ∀ r ∈ [⟨s.gpr .rsp, 8⟩, below (s.gpr .rsp) 344],
    ∀ b ∈ abiBuffers s ++ [(abiArguments s, false)], r.Disjoint b.1
  bounds : ∀ b ∈ abiBuffers s, b.1.base.toNat + b.1.len ≤ 2 ^ 64
  kind : ((s.gpr .rdi).setWidth 32).toNat ≤ 2
  valid : Spec.Argon2.valid (abiParams s) (s.gpr .rdx).toNat (s.gpr .r8).toNat
    (abiWord s 40).toNat (abiWord s 56).toNat
  threads : 1 ≤ ((abiWord s 24).setWidth 32).toNat ∧ ((abiWord s 24).setWidth 32).toNat < 2 ^ 24
  blocks : (abiWord s 72).toNat = (abiParams s).blocks

theorem abi_environment (s : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    AbiEnvironment s := by
  sig_pre [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [abiInputs, abiArguments, abiMatrix, abiWork, abiOutput, abiBuffers,
    abiWord, abiParams, below]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

end VG.Proof.Argon2.X86_64.Derive

end

end

/-! ### `Argon2.X86_64.Parameters`, which this module and modules that import it used -/

section

/-! Merged from `Proof.Argon2.X86_64.ParametersSteps`. -/

@[expose] public section

section
/-! Public frame loads and fixed arithmetic for the RFC's rounded memory dimensions. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64

theorem args_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8) :
    WP isa (.block Impl.Argon2.X86_64.Parameters.args) s fun t =>
      t.gpr .rdi = s.mem.readW (off (s.gpr .rbp) 176) 64 ∧
      t.gpr .rsi = (s.mem.readW (off (s.gpr .rbp) 184) 64) * 4 ∧ Divide.Keeps [.rdi, .rsi] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.args, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.load64, ea_at, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, memoryRead, lanesRead, reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    all_goals rfl

theorem finish_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.Parameters.finish) s fun t =>
    t.gpr .r13 = s.gpr .r9 * 4 ∧ Divide.Keeps [.r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Parameters.finish, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_⟩
  · simp only [show (4 : Addr) = 2#64 + 2#64 from rfl, BitVec.mul_add, BitVec.mul_two]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

end VG.Proof.Argon2.X86_64.Parameters
end

/-! Exact rounded lane length using the verified fixed-time divider. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  memoryRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 176) 8
  lanesRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 184) 8
  memoryWord : s.mem.readW (off (s.gpr .rbp) 176) 64 = BitVec.ofNat 64 p.memory
  lanesWord : s.mem.readW (off (s.gpr .rbp) 184) 64 = BitVec.ofNat 64 p.lanes
  positive : 0 < p.lanes
  memoryBound : p.memory < 2 ^ 32
  lanesBound : p.lanes < 2 ^ 24

def changed : List Reg := [.rdi, .rsi] ++ Divide.changed ++ [.r13]

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.X86_64.Parameters.code s fun t =>
      t.gpr .r13 = BitVec.ofNat 64 p.laneLen ∧ Divide.Keeps changed s t := by
  unfold Impl.Argon2.X86_64.Parameters.code
  refine WP.seq ((args_ok s h.memoryRead h.lanesRead).mono ?_)
  rintro a ⟨memory, lanes, ka⟩
  have divisor : a.gpr .rsi = BitVec.ofNat 64 (4 * p.lanes) := by
    rw [lanes, h.lanesWord, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have n : (a.gpr .rdi).toNat = p.memory := by
    rw [memory, h.memoryWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h.memoryBound (by decide))]
  have bound : 4 * p.lanes < 2 ^ 32 := by have lanesBound := h.lanesBound; omega_using [lanesBound]
  have d : (a.gpr .rsi).toNat = 4 * p.lanes := by
    rw [divisor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bound (by decide))]
  refine WP.seq ((Divide.code_ok a (by rw [n]; exact h.memoryBound)
    (by rw [d]; have positive := h.positive; omega_using [positive]) (by rw [d]; exact bound)).mono ?_)
  rintro b ⟨quotient, _, kb⟩
  rw [n, d] at quotient
  have word : b.gpr .r9 = BitVec.ofNat 64 (p.memory / (4 * p.lanes)) := by
    rw [← quotient]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine (finish_ok b).mono ?_
  rintro t ⟨value, kt⟩
  refine ⟨?_, (ka.mono (by simp [changed])).trans
    ((kb.mono (by
      intro r hr
      simp only [changed, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (Or.inr hr))).trans (kt.mono (by simp [changed])))⟩
  rw [value, word, show (4 : Addr) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul,
    Nat.mul_comm, ← Proof.Argon2.laneLen_eq p h.positive]

end VG.Proof.Argon2.X86_64.Parameters

end

end

/-! Merged from `Proof.Argon2.X86_64.DeriveStore`. -/

@[expose] public section

section
/-! Save each incoming argument with one short symbolic execution. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Stored (s t : State) (d : Nat) (r : Reg) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 d) (s.gpr r)
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem store_ok (s : State) (d : Nat) (r : Reg)
    (write : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store (Impl.Argon2.X86_64.at_ .rbp d) r]) s (Stored s · d r) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    State.ea, Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast, write,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Stored.word {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.gpr r := by
  rw [h.regs, h.mem, Mem.readW_writeW_self64]

theorem Stored.frame {s t : State} {d : Nat} {r : Reg} (h : Stored s t d r) :
    Frame [⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveStores`. -/
section
/-! Compose argument stores without re-executing a growing symbolic memory state. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def saveMemory (s : State) (args : List (Nat × Reg)) : Mem :=
  args.foldl (fun m arg => m.writeW (s.gpr .rbp + BitVec.ofNat 64 arg.1) (s.gpr arg.2)) s.mem

structure Saved (s t : State) (args : List (Nat × Reg)) : Prop where
  mem : t.mem = saveMemory s args
  regs : t.gpr = s.gpr
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (args.map fun arg => (⟨s.gpr .rbp + BitVec.ofNat 64 arg.1, 8⟩ : Region)) s.mem t.mem

theorem Saved.other_word {s t : State} {args : List (Nat × Reg)} (h : Saved s t args)
    (e : Nat) (bound : e + 8 ≤ 2 ^ 64)
    (separate : ∀ arg ∈ args, e + 8 ≤ arg.1 ∨ arg.1 + 8 ≤ e)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨arg, member, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate arg member) bound (bounds arg member)

theorem stores_values_ok (args : List (Nat × Reg)) (s : State)
    (write : ∀ arg ∈ args, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 arg.1) 8)
    (separate : args.Pairwise fun a b => a.1 + 8 ≤ b.1 ∨ b.1 + 8 ≤ a.1)
    (bounds : ∀ arg ∈ args, arg.1 + 8 ≤ 2 ^ 64) :
    WP isa (.block (args.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2)) s fun t =>
      Saved s t args ∧ ∀ arg ∈ args, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = s.gpr arg.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  | cons arg args ih =>
    obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
    rw [List.map_cons]
    change WP isa (.block (([.store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2] : List Instr) ++ _)) s _
    rw [WP.block_append_iff]
    refine (store_ok s arg.1 arg.2 (write arg (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t (fun a ha => by rw [ht.wr, ht.regs]; exact write a (List.mem_cons_of_mem arg ha))
      tailSep (fun a ha => bounds a (List.mem_cons_of_mem arg ha))).mono ?_
    rintro u ⟨hu, values⟩
    have saved : Saved s u (arg :: args) := by
      refine ⟨?_, hu.regs.trans ht.regs, hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
      · rw [hu.mem]; unfold saveMemory; rw [ht.regs, ht.mem, List.foldl_cons]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..
    refine ⟨saved, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hu.other_word a.1 (bounds a (List.mem_cons_self ..)) headSep
        (fun b hb => bounds b (List.mem_cons_of_mem a hb))]
      exact ht.word
    · rw [values a ha, ht.regs]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveSetup`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveScratch`. -/
section
/-! Load the caller-supplied hash workspace after saving incoming arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure ScratchLoaded (s t : State) : Prop where
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rbp + 248) 64
  regs : ∀ r, r ≠ .rbx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem scratch_ok (s : State) (read : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 248) 8) :
    WP isa (.block [.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))]) s (ScratchLoaded s) := by
  have ea : s.ea (Impl.Argon2.X86_64.at_ .rbp 248) = s.gpr .rbp + 248 := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea, read,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact RegUpd.gpr_setReg_self ..
  · intro r hr
    exact RegUpd.gpr_setReg_of_ne _ _ hr

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveEntry`. -/
section
/-! Establish the local frame base and normalize register-passed u32 arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Entered (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  kind : t.gpr .rdi = ((s.gpr .rdi).setWidth 32).setWidth 64
  passes : t.gpr .r9 = ((s.gpr .r9).setWidth 32).setWidth 64
  regs : ∀ r, r ≠ .rbp → r ≠ .rdi → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem entry_ok (s : State) :
    WP isa (.block [.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)]) s (Entered s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hb hd h9
  simp only [RegUpd.gpr_setReg, hb, hd, h9, ite_false]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Save the register arguments into the local derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def arguments : List (Nat × Reg) :=
  [(72, .r9), (80, .r8), (88, .rcx), (96, .rdx), (104, .rsi), (112, .rdi)]

def argumentValue (s : State) (r : Reg) : Addr :=
  if r = .rdi ∨ r = .r9 then ((s.gpr r).setWidth 32).setWidth 64 else s.gpr r

theorem Entered.argument {s t : State} (h : Entered s t) (r : Reg) (bp : r ≠ .rbp) :
    t.gpr r = argumentValue s r := by
  unfold argumentValue
  by_cases di : r = .rdi
  · subst r; rw [ite_eq_left (Or.inl rfl)]; exact h.kind
  · by_cases nine : r = .r9
    · subst r; rw [ite_eq_left (Or.inr rfl)]; exact h.passes
    · rw [ite_eq_right (by simp only [di, nine, or_self, not_false_eq_true])]
      exact h.regs r bp di nine

structure SetupDone (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame [⟨s.gpr .rsp, 120⟩] s.mem t.mem

theorem setup_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8) :
    WP isa (.block Impl.Argon2.X86_64.Derive.setup) s (SetupDone s) := by
  change WP isa (.block (([.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)] : List Instr) ++
    (arguments.map fun arg => .store (Impl.Argon2.X86_64.at_ .rbp arg.1) arg.2) ++
    ([.mov .rbx (.mem (Impl.Argon2.X86_64.at_ .rbp 248))] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine (entry_ok s).mono ?_
  intro a entered
  rw [WP.block_append_iff]
  have write : ∀ arg ∈ arguments, InRegions a.wr (a.gpr .rbp + BitVec.ofNat 64 arg.1) 8 := by
    intro arg ha
    rw [entered.wr, entered.bp]
    apply frameWrite
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (bounds arg ha) (by have := bounds arg ha; omega_using [this])⟩
  refine (stores_values_ok arguments a write (by decide) (by decide)).mono ?_
  rintro b ⟨saved, values⟩
  have bp : b.gpr .rbp = s.gpr .rsp := by rw [saved.regs, entered.bp]
  have scratchWord : b.mem.readW (b.gpr .rbp + 248) 64 = s.mem.readW (s.gpr .rsp + 248) 64 := by
    have kept := saved.other_word 248 (by decide) (by decide) (by decide)
    change b.mem.readW (b.gpr .rbp + 248) 64 = a.mem.readW (a.gpr .rbp + 248) 64 at kept
    rw [kept, entered.bp, entered.mem]
  refine (scratch_ok b (by rw [saved.rd, saved.wr, bp, entered.rd, entered.wr]; exact read)).mono ?_
  intro t loaded
  refine ⟨(loaded.regs .rbp (by decide)).trans bp, ?_, loaded.scratch.trans scratchWord, ?_, ?_,
    loaded.rd.trans (saved.rd.trans entered.rd), loaded.wr.trans (saved.wr.trans entered.wr),
    loaded.mxcsr.trans (saved.mxcsr.trans entered.mxcsr), ?_⟩
  · rw [loaded.regs .rsp (by decide), saved.regs]
    exact entered.regs .rsp (by decide) (by decide) (by decide)
  · intro arg ha
    rw [loaded.mem, loaded.regs .rbp (by decide), values arg ha]
    have notBp : ∀ arg ∈ arguments, arg.2 ≠ .rbp := by decide
    exact entered.argument arg.2 (notBp arg ha)
  · intro r hr hb hx
    have other : ∀ r ∈ calleeSaved, r ≠ .rdi ∧ r ≠ .r9 := by decide
    rw [loaded.regs r hx, saved.regs]
    exact entered.regs r hb (other r hr).1 (other r hr).2
  · rw [loaded.mem, ← entered.mem]
    have frame := saved.frame
    rw [entered.bp] at frame
    apply frame.sub
    intro region hr
    obtain ⟨arg, ha, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ arg ∈ arguments, arg.1 + 8 ≤ 120 := by decide
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (bounds arg ha)⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrologue`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrivatePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DerivePrepare`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveNormalizeArgs`. -/
section
/-! Normalize distinct stack slots while retaining every other frame word. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedWord (s : State) (d : Nat) : Addr :=
  (((s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)

structure NormalizedArgs (s t : State) (ds : List Nat) : Prop where
  values : ∀ d ∈ ds, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = normalizedWord s d
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (ds.map fun d => (⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ : Region)) s.mem t.mem

theorem NormalizedArgs.other_word {s t : State} {ds : List Nat} (h : NormalizedArgs s t ds)
    (e : Nat) (bound : e + 8 < 2 ^ 64)
    (separate : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 e) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 e) 64 := by
  rw [h.regs .rbp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 e, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate d hd) (Nat.le_of_lt bound) (Nat.le_of_lt (bounds d hd))

theorem normalizeArgs_ok (ds : List Nat) (s : State)
    (read : ∀ d ∈ ds, InRegions (s.rd ++ s.wr) (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ ds, InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 d) 8)
    (separate : ds.Pairwise fun d e => d + 8 ≤ e ∨ e + 8 ≤ d)
    (bounds : ∀ d ∈ ds, d + 8 < 2 ^ 64) :
    WP isa (Impl.Argon2.X86_64.Derive.normalizeArgs ds) s (NormalizedArgs s · ds) := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine (normalize_ok s d (read d (by simp)) (write d (by simp))).mono ?_
      intro t ht
      exact ⟨fun e he => by simp only [List.mem_singleton] at he; subst e; exact ht.word,
        ht.regs, ht.rd, ht.wr, ht.mxcsr, ht.frame⟩
    | cons e ds =>
      obtain ⟨headSep, tailSep⟩ := List.pairwise_cons.mp separate
      refine WP.seq ((normalize_ok s d (read d (List.mem_cons_self ..))
        (write d (List.mem_cons_self ..))).mono ?_)
      intro t ht
      refine (ih t
        (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rbp (by decide)]; exact read x (List.mem_cons_of_mem d hx))
        (fun x hx => by rw [ht.wr, ht.regs .rbp (by decide)]; exact write x (List.mem_cons_of_mem d hx))
        tailSep (fun x hx => bounds x (List.mem_cons_of_mem d hx))).mono ?_
      intro u hu
      refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
        hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hu.other_word x (bounds x (List.mem_cons_self ..)) headSep
            (fun a ha => bounds a (List.mem_cons_of_mem x ha))]
          exact ht.word
        · rw [hu.values x hx]
          unfold normalizedWord
          have sep : x + 8 ≤ d ∨ d + 8 ≤ x := (headSep x hx).symm
          rw [ht.other_word x sep (bounds x (List.mem_cons_of_mem d hx)) (bounds d (List.mem_cons_self ..))]
      · apply (ht.frame.mono ?_).trans
        · have frame := hu.frame
          rw [ht.regs .rbp (by decide)] at frame
          exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
        · intro region hr
          simp only [List.mem_singleton] at hr; subst region
          exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
end

/-! Complete ABI preparation retains the inputs and exposes normalized public arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def normalizedOffsets : List Nat := [176, 184, 192]

def prepareWrites (s : State) : List Region :=
  ⟨s.gpr .rsp, 120⟩ :: normalizedOffsets.map fun d => ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩

theorem SetupDone.other_word {s t : State} (h : SetupDone s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  simp only [List.mem_singleton] at hr; subst region
  simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
    (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)

structure Prepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 248) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  normalized : ∀ d ∈ normalizedOffsets, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
    (((s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64).setWidth 32).setWidth 64)
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (prepareWrites s) s.mem t.mem

theorem Prepared.other_word {s t : State} (h : Prepared s t) (d : Nat)
    (afterFrame : 120 ≤ d) (bound : d + 8 < 2 ^ 64)
    (separate : ∀ e ∈ normalizedOffsets, d + 8 ≤ e ∨ e + 8 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.bp]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [BitVec.add_zero] using Offset.disjoint (s.gpr .rsp) (d := d) (n := 8) (e := 0) (k := 120)
      (Or.inr afterFrame) (Nat.le_of_lt bound) (by decide)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have bounds : ∀ e ∈ normalizedOffsets, e + 8 ≤ 2 ^ 64 := by decide
    exact Offset.disjoint _ (separate e he) (Nat.le_of_lt bound) (bounds e he)

theorem prepareLocal_ok (s : State) (frameWrite : Covers [⟨s.gpr .rsp, 120⟩] s.wr)
    (read : ∀ d ∈ 248 :: normalizedOffsets, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 d) 8)
    (write : ∀ d ∈ normalizedOffsets, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepareLocal s (Prepared s) := by
  unfold Impl.Argon2.X86_64.Derive.prepareLocal
  have scratchRead : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 248) 8 := read 248 (List.mem_cons_self ..)
  refine WP.seq ((setup_ok s frameWrite scratchRead).mono ?_)
  intro a setup
  refine (normalizeArgs_ok normalizedOffsets a
    (fun d hd => by rw [setup.rd, setup.wr, setup.bp]; exact read d (List.mem_cons_of_mem _ hd))
    (fun d hd => by rw [setup.wr, setup.bp]; exact write d hd) (by decide) (by decide)).mono ?_
  intro t normalized
  refine ⟨(normalized.regs .rbp (by decide)).trans setup.bp,
    (normalized.regs .rsp (by decide)).trans setup.sp,
    (normalized.regs .rbx (by decide)).trans setup.scratch, ?_, ?_, ?_,
    normalized.rd.trans setup.rd, normalized.wr.trans setup.wr, normalized.mxcsr.trans setup.mxcsr, ?_⟩
  · intro arg ha
    have bound : ∀ arg ∈ arguments, arg.1 + 8 < 2 ^ 64 := by decide
    have separate : ∀ arg ∈ arguments, ∀ d ∈ normalizedOffsets, arg.1 + 8 ≤ d ∨ d + 8 ≤ arg.1 := by decide
    rw [normalized.other_word arg.1 (bound arg ha) (separate arg ha) (by decide)]
    exact setup.values arg ha
  · intro d hd
    rw [normalized.values d hd]
    unfold normalizedWord
    have afterFrame : ∀ d ∈ normalizedOffsets, 120 ≤ d := by decide
    have bound : ∀ d ∈ normalizedOffsets, d + 8 < 2 ^ 64 := by decide
    rw [setup.other_word d (afterFrame d hd) (bound d hd)]
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (normalized.regs r (notAx r hr)).trans (setup.regs r hr hb hx)
  · apply (setup.frame.mono (by
      intro region hr
      simp only [List.mem_singleton] at hr
      subst region
      exact List.mem_cons_self ..)).trans
    have frame := normalized.frame
    rw [setup.bp] at frame
    exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArgs`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveCopyArg`. -/
section
/-! Copy a read-only caller argument into the private derivation frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def copySource (j : Nat) : Nat := 328 + 8 * j
def copyDestination (j : Nat) : Nat := 176 + 8 * j

structure CopiedArg (s t : State) (j : Nat) : Prop where
  mem : t.mem = s.mem.writeW (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j))
    (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64)
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem copyArg_ok (s : State) (j : Nat)
    (read : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8)
    (write : InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.Derive.copyArg j)) s (CopiedArg s · j) := by
  change InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (328 + 8 * j)) 8 at read
  change InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (176 + 8 * j)) 8 at write
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.Derive.copyArg, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.load64, State.store64, readSrc, State.ea, Impl.Argon2.X86_64.at_,
    BitVec.ofInt_natCast, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, read, write, reduceCtorEq,
    ite_true, ite_false, Option.some.injEq, Option.map_some, exists_eq_left']
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro r hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem CopiedArg.frame {s t : State} {j : Nat} (h : CopiedArg s t j) :
    Frame [⟨s.gpr .rsp + BitVec.ofNat 64 (copyDestination j), 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem CopiedArg.word {s t : State} {j : Nat} (h : CopiedArg s t j) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 64 =
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 := by
  rw [h.regs .rsp (by decide), h.mem, Mem.readW_writeW_self64]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Copy all stack arguments without modifying their caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure CopiedArgs (s t : State) (js : List Nat) : Prop where
  values : ∀ j ∈ js, t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 64 =
    s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64
  regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr
  frame : Frame (js.map fun j => (⟨s.gpr .rsp + BitVec.ofNat 64 (copyDestination j), 8⟩ : Region)) s.mem t.mem

theorem CopiedArgs.other_word {s t : State} {js : List Nat} (h : CopiedArgs s t js)
    (d : Nat) (bound : d + 8 ≤ 2 ^ 64)
    (separate : ∀ j ∈ js, d + 8 ≤ copyDestination j ∨ copyDestination j + 8 ≤ d)
    (bounds : ∀ j ∈ js, copyDestination j + 8 ≤ 2 ^ 64) :
    t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 d) 64 := by
  rw [h.regs .rsp (by decide)]
  apply h.frame.readW (r := ⟨s.gpr .rsp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro region hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact Offset.disjoint _ (separate j hj) bound (bounds j hj)

theorem copyArgs_ok (js : List Nat) (s : State) (bounds : ∀ j ∈ js, j < 12)
    (distinct : js.Nodup)
    (read : ∀ j ∈ js, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8)
    (write : ∀ j ∈ js, InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 (copyDestination j)) 8) :
    WP isa (.block (js.flatMap Impl.Argon2.X86_64.Derive.copyArg)) s (CopiedArgs s · js) := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons j js ih =>
    have nodup := List.nodup_cons.mp distinct
    have jBound := bounds j (List.mem_cons_self ..)
    have tailBounds : ∀ x ∈ js, x < 12 := fun x hx => bounds x (List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine (copyArg_ok s j (read j (List.mem_cons_self ..)) (write j (List.mem_cons_self ..))).mono ?_
    intro t ht
    refine (ih t tailBounds nodup.2
      (fun x hx => by rw [ht.rd, ht.wr, ht.regs .rsp (by decide)]; exact read x (List.mem_cons_of_mem _ hx))
      (fun x hx => by rw [ht.wr, ht.regs .rsp (by decide)]; exact write x (List.mem_cons_of_mem _ hx))).mono ?_
    intro u hu
    refine ⟨?_, fun r hr => (hu.regs r hr).trans (ht.regs r hr),
      hu.rd.trans ht.rd, hu.wr.trans ht.wr, hu.mxcsr.trans ht.mxcsr, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hu.other_word (copyDestination x) (by unfold copyDestination; omega_using [jBound]) (by
          intro y hy
          have ne : y ≠ x := fun eq => nodup.1 (eq ▸ hy)
          unfold copyDestination; omega_using [ne]) (by
          intro y hy; have := tailBounds y hy; unfold copyDestination; omega_using [this])]
        exact ht.word
      · rw [hu.values x hx, ht.regs .rsp (by decide), ht.mem]
        apply Mem.readW_writeW_sep ?_ (by decide)
        have xBound := tailBounds x hx
        exact Offset.sep _ (Or.inr (by unfold copyDestination copySource; omega_using [jBound]))
          (by unfold copySource; omega_using [xBound]) (by unfold copyDestination; omega_using [jBound])
    · apply (ht.frame.mono ?_).trans
      · have frame := hu.frame
        rw [ht.regs .rsp (by decide)] at frame
        exact frame.mono (fun _ h => List.mem_cons_of_mem _ h)
      · intro region hr
        simp only [List.mem_singleton] at hr; subst region
        exact List.mem_cons_self ..

end VG.Proof.Argon2.X86_64.Derive
end

/-! Prepare private copies of every ABI argument, preserving caller-owned storage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def privateWrites (s : State) : List Region := [⟨s.gpr .rsp, 120⟩, ⟨s.gpr .rsp + 176, 96⟩]

structure PrivatePrepared (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  sp : t.gpr .rsp = s.gpr .rsp
  scratch : t.gpr .rbx = s.mem.readW (s.gpr .rsp + 400) 64
  values : ∀ arg ∈ arguments, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2
  stackWords : ∀ j < 12, t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (copyDestination j)) 64 =
    let w := s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 64
    if j < 3 then (w.setWidth 32).setWidth 64 else w
  regs : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .rbx → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (privateWrites s) s.mem t.mem

theorem private_prepare_ok (s : State) (locals : Covers [⟨s.gpr .rsp, 272⟩] s.wr)
    (read : ∀ j < 12, InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (copySource j)) 8) :
    WP isa Impl.Argon2.X86_64.Derive.prepare s (PrivatePrepared s) := by
  have localWord : ∀ d, d + 8 ≤ 272 → InRegions s.wr (s.gpr .rsp + BitVec.ofNat 64 d) 8 := by
    intro d hd
    exact locals _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega_using [hd])⟩
  unfold Impl.Argon2.X86_64.Derive.prepare Impl.Argon2.X86_64.Derive.copyArgs
  refine WP.seq ((copyArgs_ok (List.range 12) s
    (fun _ h => List.mem_range.mp h) List.nodup_range (fun j h => read j (List.mem_range.mp h))
    (fun j h => localWord _ (by have := List.mem_range.mp h; unfold copyDestination; omega_using [this]))).mono ?_)
  intro a copied
  have sp := copied.regs .rsp (by decide)
  refine (prepareLocal_ok a (by
    intro p n h
    rw [copied.wr]
    rw [sp] at h
    apply locals p n
    exact Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, 0, (BitVec.add_zero _).symm, show 0 + 120 ≤ 272 by decide⟩) p n h)
    (by
      intro d hd
      rw [copied.rd, copied.wr, sp]
      have bound : ∀ d ∈ 248 :: normalizedOffsets, d + 8 ≤ 272 := by decide
      obtain ⟨region, member, contains⟩ := localWord d (bound d hd)
      exact ⟨region, List.mem_append_right _ member, contains⟩)
    (by
      intro d hd; rw [copied.wr, sp]
      have bound : ∀ d ∈ normalizedOffsets, d + 8 ≤ 272 := by decide
      exact localWord d (bound d hd))).mono ?_
  intro t prepared
  refine ⟨prepared.bp.trans sp, prepared.sp.trans sp, ?_, ?_, ?_, ?_,
    prepared.rd.trans copied.rd, prepared.wr.trans copied.wr, ?_⟩
  · have word := copied.values 9 (by decide)
    change a.mem.readW (a.gpr .rsp + 248) 64 = s.mem.readW (s.gpr .rsp + 400) 64 at word
    exact prepared.scratch.trans word
  · intro arg ha
    rw [prepared.values arg ha]
    unfold argumentValue
    have notAx : ∀ arg ∈ arguments, arg.2 ≠ .rax := by decide
    rw [copied.regs arg.2 (notAx arg ha)]
  · intro j hj
    by_cases small : j < 3
    · have slot : ∀ j < 3, copyDestination j ∈ normalizedOffsets := by decide
      rw [prepared.normalized _ (slot j small), copied.values j (List.mem_range.mpr hj), ite_eq_left small]
    · rw [ite_eq_right small, prepared.other_word _ (by unfold copyDestination; omega_using [])
        (by unfold copyDestination; omega_using [hj]) (by
          intro d hd
          have upper : ∀ d ∈ normalizedOffsets, d + 8 ≤ 200 := by decide
          have := upper d hd; unfold copyDestination; omega_using [small, this])]
      exact copied.values j (List.mem_range.mpr hj)
  · intro r hr hb hx
    have notAx : ∀ r ∈ calleeSaved, r ≠ .rax := by decide
    exact (prepared.regs r hr hb hx).trans (copied.regs r (notAx r hr))
  · apply (copied.frame.sub ?_).trans (prepared.frame.sub ?_)
    · intro region hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hj
      refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      unfold copyDestination
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact Offset.sub_base _ (by omega_using [bound])
    · intro region hr
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [sp]; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
        rw [sp]
        have bounds : ∀ d ∈ normalizedOffsets, 176 ≤ d ∧ d + 8 ≤ 272 := by decide
        obtain ⟨lo, hi⟩ := bounds d hd
        refine ⟨⟨s.gpr .rsp + 176, 96⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [show d = 176 + (d - 176) by omega_using [lo], BitVec.ofNat_add, ← BitVec.add_assoc]
        exact Offset.sub_base _ (by omega_using [hi])

end VG.Proof.Argon2.X86_64.Derive
end

/-! Private frame permissions and caller argument values after the ABI prologue. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def prologueState (s : State) : State := frameStart s Impl.Argon2.X86_64.Derive.saved

theorem prologue_sp (s : State) : (prologueState s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 :=
  frameStart_sp s _

theorem frameStart_locals (s : State) (rs : List Reg) :
    (⟨(frameStart s rs).gpr .rsp, 272⟩ : Region) ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_wr, pushed_rsp]; exact List.mem_cons_self ..
  | cons r rs ih => exact ih (pushed [r] s)

theorem prologue_locals (s : State) : Covers [⟨(prologueState s).gpr .rsp, 272⟩] (prologueState s).wr := by
  intro p n ⟨region, member, contains⟩
  simp only [List.mem_singleton] at member; subst region
  exact ⟨_, frameStart_locals s _, contains⟩

theorem prologue_source (s : State) (j : Nat) :
    (prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j) =
      s.gpr .rsp + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [prologue_sp]
  unfold copySource
  rw [show 328 + 8 * j = 320 + 8 * (j + 1) by omega_using [],
    BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem prologue_reads {s : State} (h : AbiEnvironment s) :
    ∀ j < 12, InRegions ((prologueState s).rd ++ (prologueState s).wr)
      ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 8 := by
  intro j hj
  rw [prologue_source]
  refine ⟨abiArguments s, List.mem_append_left _ ?_, ?_⟩
  · change abiArguments s ∈ (frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [frameStart_rd, h.rd]; exact List.mem_append_right _ (List.mem_singleton_self _)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem prologue_word {s : State} (h : AbiEnvironment s) (j : Nat) (hj : j < 12) :
    (prologueState s).mem.readW ((prologueState s).gpr .rsp + BitVec.ofNat 64 (copySource j)) 64 =
      abiWord s (8 * (j + 1)) := by
  rw [prologue_source]
  have frame := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega_using [space])
  apply frame.readW (r := abiArguments s) ?_ ?_ (by decide)
  · unfold abiArguments
    rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · intro region hr
    simp only [List.mem_singleton] at hr; subst region
    unfold abiArguments
    exact Offset.disjoint_below _ (by decide)

theorem prologue_prepare (s : State) (h : AbiEnvironment s) :
    WP isa Impl.Argon2.X86_64.Derive.prepare (prologueState s) (PrivatePrepared (prologueState s)) :=
  private_prepare_ok _ (prologue_locals s) (prologue_reads h)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveMetadata`. -/
section
/-! The private frame contains the exact arguments decoded by the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_stack_word {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (j : Nat) (hj : j < 12) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 (copyDestination j)) 64 =
      let word := abiWord s (8 * (j + 1))
      if j < 3 then (word.setWidth 32).setWidth 64 else word := by
  rw [prepared.stackWords j hj, prologue_word h j hj]

theorem private_argument_word {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (arg : Nat × Reg) (member : arg ∈ arguments) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 arg.1) 64 = argumentValue s arg.2 := by
  rw [prepared.values arg member]
  unfold argumentValue
  have notSp : ∀ arg ∈ arguments, arg.2 ≠ .rsp := by decide
  unfold prologueState
  rw [frameStart_reg s _ arg.2 (notSp arg member)]

theorem private_local_write {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) : InRegions t.wr (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  rw [prepared.wr, prepared.bp]
  apply prologue_locals s
  exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega_using [bound])⟩

theorem private_local_read {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (d n : Nat) (bound : d + n ≤ 272) :
    InRegions (t.rd ++ t.wr) (t.gpr .rbp + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := private_local_write prepared d n bound
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem private_parameters {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Parameters.Ready (abiParams s) t := by
  refine ⟨private_local_read prepared 176 8 (by decide), private_local_read prepared 184 8 (by decide),
    ?_, ?_, h.valid.1, h.valid.2.2.2.2.2.1, h.valid.2.1⟩
  · have word := private_stack_word h prepared 0 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      (((abiWord s 8).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 176) 64 =
      BitVec.ofNat 64 ((abiWord s 8).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 1 (by decide)
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      (((abiWord s 16).setWidth 32).setWidth 64) at word
    change t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 184) 64 =
      BitVec.ofNat 64 ((abiWord s 16).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]

end VG.Proof.Argon2.X86_64.Derive
end

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => rw [frameStart, pushed_wr]; exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; rw [pushed_wr]; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .rbp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.bp.trans (prologue_sp s)

theorem private_sp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 320 := prepared.sp.trans (prologue_sp s)

theorem private_frame_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Region.Sub ⟨t.gpr .rbp, 272⟩ (below (s.gpr .rsp) 344) := by
  rw [private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : Region.Sub (below (t.gpr .rsp) n) (below (s.gpr .rsp) 344) := by
  rw [private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega_using [bound]) (by omega_using [bound])

theorem private_frame_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (⟨t.gpr .rbp, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) (n : Nat) (bound : n ≤ 24) :
    (below (t.gpr .rsp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 24) : (⟨t.gpr .rbp, 272⟩ : Region).Disjoint (below (t.gpr .rsp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega_using [bound])

theorem private_work_member {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : abiWork s ∈ t.wr := by
  apply private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.X86_64.Derive
