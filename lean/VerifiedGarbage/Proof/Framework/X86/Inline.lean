import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Mmx

/-!
# Inlining verified code (x86, 32-bit)

The inlining theory (`Proof/Framework/Inline.lean`) for x86 states
(`regionModel`): running code from a state that permits more memory gives
the same result (`Exec.widen`), code never writes outside the regions its
state permits (`Exec.regions`), and `WP.inline` combines the two with the
correctness part of the inlined function's `Verified` proof.
-/

namespace VG.X86

/-- `s`, permitted to read `rd` and write `wr` instead. -/
def State.withRegions (s : State) (rd wr : List Region) : State := { s with rd := rd, wr := wr }

theorem State.withRegions_syms (s : State) (rd wr : List Region) :
    (s.withRegions rd wr).syms = s.syms := rfl

@[simp] theorem State.withRegions_gpr (s : State) (rd wr) : (s.withRegions rd wr).gpr = s.gpr := rfl
@[simp] theorem State.withRegions_mem (s : State) (rd wr) : (s.withRegions rd wr).mem = s.mem := rfl
@[simp] theorem State.withRegions_rd (s : State) (rd wr) : (s.withRegions rd wr).rd = rd := rfl
@[simp] theorem State.withRegions_wr (s : State) (rd wr) : (s.withRegions rd wr).wr = wr := rfl
@[simp] theorem State.withRegions_cf (s : State) (rd wr) : (s.withRegions rd wr).cf = s.cf := rfl
@[simp] theorem State.withRegions_zf (s : State) (rd wr) : (s.withRegions rd wr).zf = s.zf := rfl
@[simp] theorem State.withRegions_mmx (s : State) (rd wr) : (s.withRegions rd wr).mmx = s.mmx := rfl
@[simp] theorem State.withRegions_ea (s : State) (rd wr) (m : MemOp) :
    (s.withRegions rd wr).ea m = s.ea m := rfl
@[simp] theorem State.withRegions_self (s : State) : s.withRegions s.rd s.wr = s := rfl
@[simp] theorem State.withRegions_withRegions (s : State) (rd wr rd' wr') :
    (s.withRegions rd wr).withRegions rd' wr' = s.withRegions rd' wr' := rfl

@[simp] theorem arg_withRegions (s : State) (rd wr) (i : Nat) :
    arg (s.withRegions rd wr) i = arg s i := rfl
@[simp] theorem argAddr_withRegions (s : State) (rd wr) (i : Nat) :
    argAddr (s.withRegions rd wr) i = argAddr s i := rfl

/-- The register an instruction may write, if it writes exactly one (see `Taint.clobbers`). -/
abbrev dstOf : Instr → Option Reg := Taint.dst

section
variable {s s' : State} {rd wr : List Region}

theorem readSrc_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v) : readSrc (s.withRegions rd wr) src = some v := by
  cases src with
  | reg _ | imm _ => exact h
  | mem m =>
    simp only [readSrc, State.load32] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_ea,
      hc _ _ hi, ite_true]
    exact h

theorem MSrc.read_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : MSrc} {v : BitVec 64}
    (h : src.read s = some v) : src.read (s.withRegions rd wr) = some v := by
  cases src with
  | reg _ => exact h
  | mem m =>
    simp only [MSrc.read] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_ea,
      hc _ _ hi, ite_true]
    exact h

theorem MOp.exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {op : MOp} (h : op.exec s = some s') :
    op.exec (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases op with
  | bin o d src | movq d src =>
    simp only [MOp.exec] at h ⊢
    split at h <;> [rename_i hm; cases h]
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [State.withRegions_mmx, hm, ite_true, MSrc.read_widen hc hv, Option.map_some]
    rfl
  | _ =>
    simp only [MOp.exec] at h ⊢
    split at h <;> [rename_i hm; cases h]
    cases h
    simp only [State.withRegions_mmx, hm, ite_true]
    rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | mov d src =>
    simp only [exec, Option.map_eq_some_iff] at h ⊢
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨v, readSrc_widen hc hv, rfl⟩
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, out, ho, rfl⟩ := h
    refine ⟨b, readSrc_widen hc hb, out, ho, ?_⟩
    split <;> rfl
  | shift op d n =>
    simp only [exec, execShift] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    cases op <;> simp only [Option.some.injEq] at h ⊢ <;> subst h <;> rfl
  | bswap d =>
    simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | movzx8 d m =>
    simp only [exec, State.load8, Option.map_eq_some_iff] at h ⊢
    split at h <;> [rename_i hi; simp at h]
    obtain ⟨v, hv, rfl⟩ := h
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_ea,
      hc _ _ hi, ite_true]
    exact ⟨v, hv, rfl⟩
  | store m r | store8 m r =>
    simp only [exec, State.store32, State.store8] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    simp only [State.withRegions_wr, State.withRegions_gpr, State.withRegions_ea, hw _ _ hi, ite_true]
    rfl
  | mul r => simp only [exec, Option.some.injEq] at h ⊢; subst h; rfl
  | xop op =>
    simp only [exec, Option.some.injEq] at h ⊢; subst h
    cases op <;> rfl
  | movdquLoad d m =>
    simp only [exec, State.load128, Option.map_eq_some_iff] at h ⊢
    split at h <;> [rename_i hi; simp at h]
    obtain ⟨v, hv, rfl⟩ := h
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_ea,
      hc _ _ hi, ite_true]
    exact ⟨v, hv, rfl⟩
  | movdquStore m r =>
    simp only [exec, State.store128] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    simp only [State.withRegions_wr, State.withRegions_ea, hw _ _ hi, ite_true]
    rfl
  | movqLoad d m =>
    simp only [exec, State.load64, Option.map_eq_some_iff] at h ⊢
    split at h <;> [rename_i hi; simp at h]
    obtain ⟨v, hv, rfl⟩ := h
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_ea,
      hc _ _ hi, ite_true]
    exact ⟨v, hv, rfl⟩
  | movqStore m r =>
    simp only [exec, State.store64] at h ⊢
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    simp only [State.withRegions_wr, State.withRegions_ea, hw _ _ hi, ite_true]
    rfl
  | mop op => exact MOp.exec_widen hc h
  | mmxStore m r =>
    simp only [exec, State.store64] at h ⊢
    split at h <;> [rename_i hm; cases h]
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    simp only [State.withRegions_mmx, State.withRegions_wr, State.withRegions_ea, hm, hw _ _ hi, ite_true]
    rfl
  | symPush _ _ | push _ | pop _ _ | alloc _ | free _ | mmxEnter | emms => simp only [exec, reduceCtorEq] at h

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> (try cases ‹MOp›) <;> (try cases ‹MSrc›) <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  cases i with
  | store m r | store8 m r =>
    simp only [exec, State.store32, State.store8] at h
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, (Frame.refl _ _).writeW hr _ hc⟩
  | mov d src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split <;> exact ⟨rfl, rfl, Frame.refl _ _⟩
  | shift op d n =>
    simp only [exec, execShift] at h
    split at h <;> [skip; cases h]
    cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> exact ⟨rfl, rfl, Frame.refl _ _⟩
  | bswap d =>
    simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | movzx8 d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | mul r => simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h
    cases op <;> exact ⟨rfl, rfl, Frame.refl _ _⟩
  | movdquLoad d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | movdquStore m r =>
    simp only [exec, State.store128] at h
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, (Frame.refl _ _).writeW hr _ hc⟩
  | movqLoad d m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | movqStore m r =>
    simp only [exec, State.store64] at h
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, (Frame.refl _ _).writeW hr _ hc⟩
  | mop op =>
    simp only [exec] at h
    rw [MOp.exec_eq h]; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | mmxStore m r =>
    simp only [exec, State.store64] at h
    split at h <;> [skip; cases h]
    split at h <;> [rename_i hi; cases h]
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, hr, hc⟩ := hi
    exact ⟨rfl, rfl, (Frame.refl _ _).writeW hr _ hc⟩
  | symPush _ _ | push _ | pop _ _ | alloc _ | free _ | mmxEnter | emms => simp only [exec, reduceCtorEq] at h

theorem exec_gpr {i : Instr} {r : Reg} (hi : Taint.clobbers i r = false) (h : exec i s = some s') :
    s'.gpr r = s.gpr r := by
  cases hd : Taint.dst i with
  | some d => exact (Taint.exec_dst hd h).2.2 r fun e => Taint.dst_ne_of_clobbers hi (e ▸ hd)
  | none =>
    cases i with
    | store m r' | store8 m r' =>
      simp only [exec, State.store32, State.store8] at h
      split at h <;> [skip; cases h]
      simp only [Option.some.injEq] at h
      subst h; rfl
    | mul q =>
      simp only [Taint.clobbers, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
      simp only [exec, Option.some.injEq] at h; subst h
      exact Taint.execMul_gpr q s hi.1 hi.2
    | xop op =>
      simp only [exec, Option.some.injEq] at h; subst h
      cases op <;> rfl
    | movdquLoad d m =>
      simp only [exec, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
    | movdquStore m r' =>
      simp only [exec, State.store128] at h
      split at h <;> [skip; cases h]
      simp only [Option.some.injEq] at h
      subst h; rfl
    | movqLoad d m =>
      simp only [exec, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
    | movqStore m r' =>
      simp only [exec, State.store64] at h
      split at h <;> [skip; cases h]
      simp only [Option.some.injEq] at h
      subst h; rfl
    | mop op =>
      simp only [exec] at h
      rw [MOp.exec_eq h]
    | mmxStore m r' =>
      simp only [exec, State.store64] at h
      split at h <;> [skip; cases h]
      split at h <;> [skip; cases h]
      simp only [Option.some.injEq] at h
      subst h; rfl
    | symPush _ _ | push _ | pop _ _ | alloc _ | free _ | mmxEnter | emms => simp only [exec, reduceCtorEq] at h
    | _ => simp [Taint.dst] at hd

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

theorem call_gpr {s s' : State} (h : isa.call s = some s') (r : Reg) :
    s'.gpr r = if r = .esp then s.gpr .esp - 4 else s.gpr r := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_gpr {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') (r : Reg) :
    s₂.gpr .esp = s₁.gpr .esp ∧ s'.gpr r = if r = .esp then s₂.gpr .esp + 4 else s₂.gpr r := by
  simp only [isa, ret] at h; split at h <;> cases h; rename_i hc; exact ⟨hc.1, rfl⟩

theorem pushRegs_withRegions (s : State) (rs : List Reg) (rd wr : List Region) :
    pushRegs (s.withRegions rd wr) rs = (pushRegs s rs).withRegions rd wr := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    exact ih { s.setReg .esp (s.gpr .esp - 4) with
      mem := s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr x) }

theorem popReg_withRegions (s : State) (d : Reg) (k : Nat) (rd wr : List Region) :
    popReg (s.withRegions rd wr) d k = (popReg s d k).withRegions rd wr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    exact ih ((s.setReg d (s.mem.readW ((s.gpr .esp).setWidth 64) 32)).setReg .esp (s.gpr .esp + 4))

/-- A frame's push adds its region at the head of `wr`, and changes no
register but `esp` and the destination of a static-address push. -/
theorem push_eq {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ k, s₁.rd = s.rd ∧ s₁.wr = ⟨(s₁.gpr .esp).setWidth 64, 4 * k⟩ :: s.wr ∧
      (∀ r, r ≠ .esp → dstOf i ≠ some r → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * k) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case mmxEnter =>
    split at h <;> cases h
    exact ⟨0, rfl, rfl, fun _ _ _ => rfl, by simp⟩
  case push rs =>
    split at h <;> cases h
    obtain ⟨h₁, -, h₃, h₄⟩ := pushRegs_eq s rs
    exact ⟨rs.length, h₁, by rw [h₃], fun r hr _ => h₄ r hr, h₃⟩
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    have e : 4 * (bytes / 4) = bytes := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2.2.1)
    refine ⟨bytes / 4, rfl, ?_, fun r hr _ => ?_, ?_⟩
    · simp only [State.setReg, ite_true, e]
    · simp only [State.setReg, hr, ite_false]
    · simp only [State.setReg, ite_true, e]

  case symPush d name =>
    split at h <;> cases h
    rename_i hc
    have he : Reg.esp ≠ d := hc.1.symm
    refine ⟨1, rfl, ?_, fun r hr hd => ?_, ?_⟩
    · simp only [State.setReg, he, ↓reduceIte]
    · have hd' : r ≠ d := fun e => hd (by simp [dstOf, Taint.dst, e])
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, hd', ↓reduceIte]
    · simp only [State.setReg, he, ↓reduceIte]; rfl

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register and `esp`. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, r ≠ .esp → dstOf j ≠ some r → s'.gpr r = s₂.gpr r) ∧ s₂.gpr .esp = s₁.gpr .esp ∧
      ∃ k, s₁.wr.head? = some ⟨(s₁.gpr .esp).setWidth 64, 4 * k⟩ ∧
        s'.gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 (4 * k) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case emms =>
    split at h <;> cases h
    rename_i hc
    exact ⟨hc.2.2.1, rfl, rfl, fun _ _ _ => rfl, hc.2.1, 0, hc.2.2.2, by simp⟩
  case pop d k =>
    split at h <;> cases h
    rename_i hc
    obtain ⟨h₁, -, h₃, h₄⟩ := popReg_eq s₂ d k
    refine ⟨hc.2.2.2.1, h₁, rfl, fun r hr hd => h₄ r hr ?_, hc.2.2.1, k, hc.2.2.2.2, h₃⟩
    intro e; exact hd (by simp [dstOf, Taint.dst, e])
  case free bytes =>
    split at h <;> cases h
    rename_i hc
    have e : 4 * (bytes / 4) = bytes := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2.2.1)
    refine ⟨hc.2.2.2.2.1, rfl, rfl, fun r hr _ => ?_, hc.2.2.2.1, bytes / 4,
      by rw [e]; exact hc.2.2.2.2.2, ?_⟩
    · simp only [State.setReg, hr, ite_false]
    · simp only [State.setReg, ite_true, e]

theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ ∀ rd wr,
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case mmxEnter =>
    split at h <;> cases h
    rename_i hm
    refine ⟨_, rfl, rfl, fun rd wr => ?_⟩
    simp only [isa, push, State.withRegions_mmx, hm]
    rfl
  case push rs =>
    split at h <;> cases h
    rename_i hc
    refine ⟨_, (pushRegs_eq s rs).1, rfl, fun rd wr => ?_⟩
    simp only [isa, push, State.withRegions_gpr, ne_eq, hc.1, hc.2.1, hc.2.2, not_false_eq_true,
      and_self, ite_true, pushRegs_withRegions]
    rfl
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    refine ⟨_, rfl, rfl, fun rd wr => ?_⟩
    simp only [isa, push, State.withRegions_gpr, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, and_self, ite_true]
    rfl

  case symPush d name =>
    split at h <;> cases h
    rename_i hc
    refine ⟨_, rfl, rfl, fun rd wr => ?_⟩
    simp only [isa, push]
    split
    · rfl
    · rename_i hn; exact (hn hc).elim

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case emms =>
    split at h <;> cases h
    rename_i hc
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, State.withRegions_mmx, hw, hc.1,
      hc.2.1, hc.2.2.2, and_self, ite_true]
    rfl
  case pop =>
    split at h <;> cases h
    rename_i hc
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, ne_eq, hw, hc.1, hc.2.1,
      hc.2.2.1, hc.2.2.2.2, and_self, ite_true, not_false_eq_true, popReg_withRegions]
    rfl
  case free =>
    split at h <;> cases h
    rename_i hc
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, hw, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2.2, and_self, ite_true]
    rfl

/-- A call and its return restore every register, `esp` included. -/
theorem call_ret_gpr {s s₁ s₂ s' : State} (hc : isa.call s = some s₁) (hr : isa.ret s₁ s₂ = some s')
    {r : Reg} (hb : s₂.gpr r = s₁.gpr r) : s'.gpr r = s.gpr r := by
  obtain ⟨hsp, h'⟩ := ret_gpr hr r
  rw [h']
  by_cases hrs : r = .esp
  · subst hrs
    rw [ite_eq_left rfl, hsp, call_gpr hc, ite_eq_left rfl]
    exact BitVec.sub_add_cancel _ _
  · simp only [hrs, ite_false, hb, call_gpr hc]

/-- A frame restores registers written by neither its push nor its pop. -/
theorem frame_gpr {i j : Instr} {s s₁ s₂ s' : State} {r : Reg} (hi : Taint.clobbers i r = false) (hj : Taint.clobbers j r = false)
    (hp : isa.push i s = some s₁) (hq : isa.pop j s₁ s₂ = some s') (hb : s₂.gpr r = s₁.gpr r) :
    s'.gpr r = s.gpr r := by
  obtain ⟨k, -, w₁, g₁, e₁⟩ := push_eq hp
  obtain ⟨-, -, -, g₂, e₂, k', h₃, e₃⟩ := pop_eq hq
  by_cases hrs : r = .esp
  · subst hrs
    rw [w₁] at h₃
    simp only [List.head?_cons, Option.some.injEq, Region.mk.injEq] at h₃
    have : k = k' := by omega
    subst this
    rw [e₃, hb, e₁, BitVec.sub_add_cancel]
  · rw [g₂ r hrs (Taint.dst_ne_of_clobbers hj), hb, g₁ r hrs (Taint.dst_ne_of_clobbers hi)]

/-- The permissions of x86 states, for the inlining theory
(`Proof/Framework/Inline.lean`). -/
def regionModel : RegionModel isa where
  rd := State.rd
  wr := State.wr
  mem := State.mem
  withRegions := State.withRegions
  rd_with _ _ _ := rfl
  wr_with _ _ _ := rfl
  mem_with _ _ _ := rfl
  with_self _ := rfl
  with_with _ _ _ _ _ := rfl
  exec_regions := exec_regions
  exec_widen hc hw h := exec_widen hc hw h
  addrs_with := addrs_withRegions
  eval_with := eval_withRegions
  callAddrs_with _ _ _ := rfl
  retAddrs_with _ _ _ := rfl
  call_widen h := by
    simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  ret_widen h := by
    simp only [isa, ret] at h; split at h <;> cases h; rename_i hc
    exact ⟨rfl, rfl, fun _ _ => (ite_eq_left hc).trans rfl⟩
  push_widen := push_widen
  pop_widen h := ⟨(pop_eq h).1, (pop_eq h).2.1, (pop_eq h).2.2.1, fun _ _ hw => pop_widen h _ hw⟩

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem :=
  regionModel.execBlock_regions h

/-- The permissions never change. -/
theorem Exec.rdwr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr :=
  regionModel.rdwr h

/-- Code without calls or frames changes memory only within the regions it
may write (a call also stores its return address, and a frame's push its
registers, below the stack pointer). -/
theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noCalls = true) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem :=
  regionModel.regions h (Code.noFrames_of_noCalls hn) (.inl hn)

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) :=
  regionModel.widen h hc hw

/-- A register that no instruction writes keeps its value. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.gpr r = s.gpr r := by
  induction h with
  | block h => exact execBlock_keep (fun s : State => s.gpr r) (fun hi he => exec_gpr hi he) hc h
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)),
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi))]
  | iteT _ _ ih => exact ih (fun i hi => hc i (List.mem_append_left _ hi))
  | iteF _ _ ih => exact ih (fun i hi => hc i (List.mem_append_right _ hi))
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | call hp _ hq ih => exact call_ret_gpr hp hq (ih hc)
  | frame hp _ hq ih =>
    exact frame_gpr (hc _ (by simp [instrs])) (hc _ (by simp [instrs])) hp hq
      (ih (fun i hi => hc i (by simp [instrs, hi])))

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

/-- Running code proven on narrower permissions: if, from `s` with its
permissions narrowed to `rd` and `wr`, the code terminates in a state
satisfying `P`, then from `s` it terminates in a state that has the
permissions of `s`, differs from it in memory only within `wr`, and, narrowed
likewise, satisfies `P`. -/
theorem WP.narrow {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → Frame wr s.mem s'.mem → P (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q :=
  regionModel.wp_narrow h hc hw (Code.noFrames_of_noCalls hn) (.inl hn)
    fun _ _ _ hr hw hf hp => hQ _ hr hw hf hp

/-- Inlining verified code: from a state `s` in which the code's precondition
holds once its permissions are narrowed to `rd` and `wr`, the code
terminates in a state satisfying its postcondition and calling-convention
obligations (both on the narrowed states), which has the permissions of `s`,
differs from it in memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q :=
  regionModel.wp_narrow (hv _ hpre) hc hw (Code.noFrames_of_noCalls hn) (.inl hn)
    fun _ _ he hr hw hf hp => hQ _ hr hw hp.1 hf (fun _ h => Exec.gpr h he) hp.2

/-- Widening writable regions: code verified against `k` is verified against
a contract `k'` whose states permit writing regions that extend (same bases,
at least as long) the ones `k` permits (`wr s`), reading the same ones, if
`k'` asks nothing more. The code runs as it does from the narrowed state,
with the same trace and result. -/
theorem Verified.widen {c : Prog isa} {k k' : Contract isa} (h : Verified target c k)
    (wr : State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (s.withRegions s.rd (wr s)))
    (hwr : ∀ s, k'.pre s → List.Forall₂ Region.Prefix (wr s) s.wr)
    (hpost : ∀ s s', k'.pre s →
      k.post (s.withRegions s.rd (wr s)) (s'.withRegions s.rd (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (s₁.withRegions s₁.rd (wr s₁)) (s₂.withRegions s₂.rd (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified target c k' :=
  regionModel.verified_widen (T := target) (fun _ _ _ _ h => h) h wr hpre hwr hpost hpub hsat

/-- `Verified.widen`, narrowing the readable regions too: `k` may read
`rd s` and write `wr s`, which the regions of `k'` cover (a region `k'` lets
the code write may be only read under `k`). -/
theorem Verified.narrowTo {c : Prog isa} {k k' : Contract isa} (h : Verified target c k)
    (rd wr : State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (s.withRegions (rd s) (wr s)))
    (hc : ∀ s, k'.pre s → Covers (rd s ++ wr s) (s.rd ++ s.wr))
    (hw : ∀ s, k'.pre s → Covers (wr s) s.wr)
    (hpost : ∀ s s', k'.pre s →
      k.post (s.withRegions (rd s) (wr s)) (s'.withRegions (rd s) (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (s₁.withRegions (rd s₁) (wr s₁)) (s₂.withRegions (rd s₂) (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified target c k' :=
  regionModel.verified_narrowTo (T := target) (fun _ _ _ _ h => h) h rd wr hpre hc hw hpost hpub
    hsat

end VG.X86
