module

import VerifiedGarbage.Proof.Idea.KeyBits32
public import VerifiedGarbage.Proof.Framework.X86.Linear
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.KeyLit32
import VerifiedGarbage.Proof.Idea.KeyBits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Idea.X86.Lit
public import VerifiedGarbage.Impl.Idea.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Idea.KeyBits32
meta import VerifiedGarbage.Proof.Framework.X86.Linear
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Spec.Idea.Contract
meta import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.KeyBits
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Idea.X86.Lit
meta import VerifiedGarbage.Impl.Idea.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Idea.Memory32
import VerifiedGarbage.Proof.Idea.Arith32
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Idea
import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Idea.Memory32
meta import VerifiedGarbage.Proof.Idea.Arith32
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Idea.Memory
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Spec.Idea
meta import VerifiedGarbage.Proof.Framework.X86.Reduce

/-! ### `Idea.X86.Round`, which this module and modules that import it used -/

section

/-! ### `Idea.X86.Mul`, which this module and modules that import it used -/

section

/-!
# IDEA on x86 (32-bit): ⊙ without branches

`mul_run`: `mulCode src` leaves `eax ⊙ src` (of their low 16 bits) in
`edx`, and changes nothing but `eax`, `edx` and the flags, if `src` reads
the same value once `eax` has changed. The arithmetic is
`Proof.Idea.prep32_toNat` and `Proof.Idea.reduce32`.
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-- What a block keeps: every register but `written`, memory and regions. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.mem, h.rd, h.wr⟩

/-- `Keep.mono` for literal lists, by evaluation. -/
theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : (rs.all fun r => rs'.contains r) = true) : Keep rs' s s' :=
  h.mono fun r hr => by
    have := List.all_eq_true.mp hs r hr
    simpa using this

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil, Option.bind_some]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem run_append {a b : List Instr} {s s₁ s₂ : State}
    (h₁ : runBlock isa a s = some s₁) (h₂ : runBlock isa b s₁ = some s₂) :
    runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁, Option.bind_some, h₂]

tactic_template "keep_tac" : tactic => `(tactic| (
                   refine ⟨fun q hq => ?_, rfl, rfl, rfl⟩
                   simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
                   simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hq, ite_false]))

/-- A source that reads `v` from any state agreeing with `s` but on `eax`. -/
def SrcOk (s : State) (src : Src) (v : BitVec 32) : Prop :=
  ∀ t : State, t.mem = s.mem → t.rd = s.rd → t.wr = s.wr → (∀ r, r ≠ .eax → t.gpr r = s.gpr r) →
    readSrc t src = some v

theorem mul_run (src : Src) (v : BitVec 32) (s : State) (hsrc : SrcOk s src v) :
    ∃ s', runBlock isa (mulCode src) s = some s' ∧
      s'.gpr .edx = (Spec.Idea.mul ((s.gpr .eax).setWidth 16) (v.setWidth 16)).setWidth 32 ∧
      Keep [.eax, .edx] s s' := by
  have hm : (65535 : BitVec 32).toNat = 65535 := rfl
  -- The first operand's residue.
  obtain ⟨s₁, h₁, v₁, e₁⟩ : ∃ s₁, runBlock isa [.alu .sub .eax (.imm 1), .alu .and .eax (.imm 0xffff),
      .alu .add .eax (.imm 1)] s = some s₁ ∧ s₁.gpr .eax = ((s.gpr .eax - 1) &&& 65535) + 1 ∧
      Keep [.eax] s s₁ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg, ↓reduceIte, Option.some.injEq, exists_eq_left', true_and]
    keep_tac
  have hv : readSrc s₁ src = some v := hsrc s₁ e₁.mem e₁.rd e₁.wr fun r hr => e₁.reg r (by simpa using hr)
  refine ⟨_, run_append (a := [_, _, _]) h₁ (by
    rw [runBlock_cons, show exec (.mov .edx src) s₁ = some (s₁.setReg .edx v) by simp [reduceExec, hv],
      runStep_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execShift, execMul,
      readSrc, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
      ↓reduceIte, reduceCtorEq, Nat.reduceLeDiff, and_self, Option.map_some]
    rfl), ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg, ↓reduceIte]
    have hA := prep32_toNat (s.gpr .eax) 65535 hm
    have hB := prep32_toNat v 65535 hm
    have hp₀ := Nat.mul_le_mul (residue_pos ((s.gpr .eax).setWidth 16)) (residue_pos (v.setWidth 16))
    have hp := Nat.mul_le_mul (residue_le ((s.gpr .eax).setWidth 16)) (residue_le (v.setWidth 16))
    rw [mul32_toNat]
    refine reduce32 _ hp₀ (Nat.le_trans hp (by decide)) _ 65535 1 ?_ hm rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, v₁, hA, hB]
    show (2 ^ 32 - 1 + _ % 2 ^ 32) % 2 ^ 32 = _
    have := Nat.le_trans hp (show 2 ^ 16 * 2 ^ 16 ≤ 2 ^ 32 by decide)
    have := Nat.le_trans (show 1 ≤ 1 * 1 by decide) hp₀
    omega_using [hp₀, hp]
  · refine e₁.weaken (rs' := [.eax, .edx]) (by decide) |>.trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]

end VG.Proof.Idea.X86

end

end

/-!
# IDEA on x86 (32-bit): a round

`round_run`: round `j` of the code (`roundWith j b c`) maps the state words
in `ebx`, `b`, `c`, `ebp` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the copy of the schedule at `esi`
(`KeyOk`) when they are used, and leaves the new middle words in `c` and
`b`. It writes `eax`, `edx` and `t₀`'s slot, which follows the subkeys
(`KeepT`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-! ## Single instructions -/

/-- The value an ALU instruction writes. -/
def aluF : AluOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add => (· + ·)
  | .sub => (· - ·)
  | .and => (· &&& ·)
  | .or => (· ||| ·)
  | .xor => (· ^^^ ·)
  | _ => fun a _ => a

theorem alu_run (op : AluOp) (hop : op = .add ∨ op = .sub ∨ op = .and ∨ op = .or ∨ op = .xor)
    (d : Reg) (src : Src) (v : BitVec 32) (s : State) (hv : readSrc s src = some v) :
    ∃ s', runBlock isa [.alu op d src] s = some s' ∧ s'.gpr d = aluF op (s.gpr d) v ∧
      Keep [d] s s' := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execAlu, hv, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, aluF, true_and] <;>
  keep_tac

theorem mov_run (d : Reg) (src : Src) (v : BitVec 32) (s : State) (hv : readSrc s src = some v) :
    ∃ s', runBlock isa [.mov d src] s = some s' ∧ s'.gpr d = v ∧ Keep [d] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, hv, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  keep_tac

/-! ## The subkeys -/

/-- The scratch buffer at `esi` (`4 * slots` bytes or more: a mode keeps its
own after them): its first 104 bytes hold the subkeys `z`, then `t₀`'s slot;
all writable, not wrapping around. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  wr : ∃ n, slots ≤ n ∧ (s.gpr .esi).toNat + 4 * n ≤ 2 ^ 32 ∧ ⟨(s.gpr .esi).setWidth 64, 4 * n⟩ ∈ s.wr
  fit : (s.gpr .esi).toNat + 4 * slots ≤ 2 ^ 32
  sched : Spec.Idea.scheduleAt s.mem ((s.gpr .esi).setWidth 64) = z

/-- A scratch buffer of exactly `slots` slots. -/
theorem KeyOk.exact {z : Spec.Idea.Schedule} {s : State} (hr : ⟨(s.gpr .esi).setWidth 64, 4 * slots⟩ ∈ s.wr)
    (hf : (s.gpr .esi).toNat + 4 * slots ≤ 2 ^ 32)
    (hs : Spec.Idea.scheduleAt s.mem ((s.gpr .esi).setWidth 64) = z) : KeyOk z s :=
  ⟨⟨slots, Nat.le_refl _, hf, hr⟩, hf, hs⟩

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hesi : .esi ∉ rs) : KeyOk z s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hk.wr, hk.reg .esi hesi]; exact h.wr
  · rw [hk.reg .esi hesi]; exact h.fit
  · rw [hk.mem, hk.reg .esi hesi]; exact h.sched

theorem KeyOk.slot {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {d : Nat} (hd : d + 4 ≤ 4 * slots) :
    InRegions s.wr (addr (s.gpr .esi) d) 4 := by
  obtain ⟨n, hn, hf, hr⟩ := h.wr
  rw [addr_eq (by have := h.fit; simp only [slots] at *; omega_using [hd, this])]
  exact ⟨_, hr, Offset.contains_base _ (by omega_using [hd, hn]) (by omega_using [hd, hn, hf])⟩

/-- Subkey `k`, read at its offset. -/
theorem KeyOk.src {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {k : Nat} (hk : k < 52) :
    SrcOk s (.mem (at_ .esi (2 * k))) (s.mem.readW (addr (s.gpr .esi) (2 * k)) 32) ∧
      (s.mem.readW (addr (s.gpr .esi) (2 * k)) 32).setWidth 16 = z.getD k 0 := by
  refine ⟨fun t hm hrd hwr hg => ?_, ?_⟩
  · have hin := h.slot (d := 2 * k) (by simp only [slots]; omega_using [hk])
    simp only [readSrc, State.ea, State.load32, at_, hg .esi (by decide), hrd, hwr, hm]
    exact ite_eq_left (by rw [← addr]; exact ⟨_, List.mem_append_right _ hin.choose_spec.1, hin.choose_spec.2⟩)
  · rw [addr_eq (by have := h.fit; simp only [slots] at *; omega_using [hk, this]), subkey_lo32 _ _ hk, h.sched]

theorem mulKey_run (z : Spec.Idea.Schedule) (k : Nat) (hk : k < 52) (s : State) (h : KeyOk z s) :
    ∃ s', runBlock isa (mulKey k) s = some s' ∧
      s'.gpr .edx = (Spec.Idea.mul ((s.gpr .eax).setWidth 16) (z.getD k 0)).setWidth 32 ∧
      Keep [.eax, .edx] s s' := by
  obtain ⟨hs, hv⟩ := h.src hk
  obtain ⟨s', h', v', e'⟩ := mul_run _ _ s hs
  exact ⟨s', h', by rw [v', hv], e'⟩

theorem addKey_run (z : Spec.Idea.Schedule) (r : Reg) (k : Nat) (hk : k < 52) (s : State) (h : KeyOk z s) :
    ∃ s', runBlock isa (addKey r k) s = some s' ∧
      s'.gpr r = ((s.gpr r).setWidth 16 + z.getD k 0).setWidth 32 ∧ Keep [r] s s' := by
  obtain ⟨hs, hv⟩ := h.src hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := alu_run .add (by simp) r _ _ s (hs s rfl rfl rfl fun _ _ => rfl)
  obtain ⟨s₂, h₂, v₂, e₂⟩ := alu_run .and (by simp) r (.imm 0xffff) 0xffff s₁ rfl
  refine ⟨s₂, run_append h₁ h₂, ?_, e₁.trans e₂⟩
  rw [v₂, v₁]
  simp only [aluF]
  rw [mask32_setWidth, ← hv]
  congr 1
  rw [BitVec.setWidth_add _ _ (by decide)]

/-! ## A round -/

/-- The state words are in `ebx`, `b`, `c`, `ebp`, zero-extended. -/
structure Holds (x : Spec.Idea.State) (b c : Reg) (s : State) : Prop where
  ebx : s.gpr .ebx = (x.getD 0 0).setWidth 32
  b : s.gpr b = (x.getD 1 0).setWidth 32
  c : s.gpr c = (x.getD 2 0).setWidth 32
  ebp : s.gpr .ebp = (x.getD 3 0).setWidth 32

/-- What a round keeps: every register but `written` (never `esi`), the
regions, and the memory outside `t₀`'s slot. -/
structure KeepT (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem s'.mem

theorem Keep.toT {rs : List Reg} {s s' : State} (h : Keep rs s s') : KeepT rs s s' :=
  ⟨h.reg, h.rd, h.wr, by rw [h.mem]; exact Frame.refl _ _⟩

theorem KeepT.trans {rs : List Reg} {s s' s'' : State} (hesi : .esi ∉ rs)
    (h : KeepT rs s s') (h' : KeepT rs s' s'') : KeepT rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans (by rw [← h.reg .esi hesi]; exact h'.frame)⟩

theorem KeepT.mono {rs rs' : List Reg} {s s' : State} (h : KeepT rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : KeepT rs' s s' :=
  ⟨fun r hr => h.reg r fun hm => hr (hs r hm), h.rd, h.wr, h.frame⟩

theorem KeyOk.keepT {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : KeepT rs s s') (hesi : .esi ∉ rs) : KeyOk z s' := by
  obtain e := hk.reg .esi hesi
  refine ⟨by rw [hk.wr, e]; exact h.wr, by rw [e]; exact h.fit, ?_⟩
  rw [e, ← h.sched]
  refine scheduleAt_congr (frame_bytes hk.frame ?_ (by decide))
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  rw [addr_eq (by have := h.fit; simp only [t0Slot, slots] at *; omega_using [this])]
  exact Offset.base_disjoint _ (by decide) (by have := h.fit; simp only [t0Slot, slots] at *; omega_using [])

/-- The six subkeys of round `j`. -/
abbrev rk (z : Spec.Idea.Schedule) (j i : Nat) : Spec.Idea.Word := z.getD (6 * j + i) 0

/-- The written registers of a round. -/
abbrev roundWrites : List Reg := [.eax, .ebx, .ecx, .edx, .edi, .ebp]

theorem store_t0_run (z : Spec.Idea.Schedule) (s : State) (h : KeyOk z s) :
    ∃ s', runBlock isa [.store (at_ .esi t0Slot) .edx] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr .esi) t0Slot) (s.gpr .edx) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hin : InRegions s.wr (s.ea (at_ .esi t0Slot)) 4 := h.slot (d := t0Slot) (by decide)
  simp only [runBlock_cons, isa, exec, State.store32, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem round_run (j : Nat) (hj : j < 8) (b c : Reg)
    (hb : (b == .ecx && c == .edi || b == .edi && c == .ecx) = true)
    (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x b c s) (hk : KeyOk z s) :
    ∃ s', runBlock isa (roundWith j b c) s = some s' ∧
      Holds (Spec.Idea.round (rk z j 0) (rk z j 1) (rk z j 2) (rk z j 3) (rk z j 4) (rk z j 5) x)
        c b s' ∧
      KeepT roundWrites s s' := by
  obtain nb : ∀ r ∈ [Reg.eax, .ebx, .edx, .ebp, .esi], b ≠ r ∧ c ≠ r := by
    intro r hr
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain hbc : b ≠ c := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  obtain hsub : ∀ r ∈ [b, c], r ∈ roundWrites := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  obtain ⟨ba, ca⟩ := nb .eax (by simp)
  obtain ⟨bb, cb⟩ := nb .ebx (by simp)
  obtain ⟨bd, cd⟩ := nb .edx (by simp)
  obtain ⟨bp, cp⟩ := nb .ebp (by simp)
  obtain ⟨bs, cs⟩ := nb .esi (by simp)
  obtain hB : ∀ r ∈ [b], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
  obtain hC : ∀ r ∈ [c], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
  -- X₁ ⊙ Z₁
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ebx) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run z (6 * j) (by omega_using [hj]) s₁ (hk.keep e₁ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mov_run .ebx (.reg .edx) _ s₂ rfl
  -- X₄ ⊙ Z₄
  obtain e₀₃ : Keep [.eax, .ebx, .edx] s s₃ :=
    ((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax (.reg .ebp) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := mulKey_run z (6 * j + 3) (by omega_using [hj]) s₄
    ((hk.keep e₀₃ (by decide)).keep e₄ (by decide))
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .ebp (.reg .edx) _ s₅ rfl
  obtain e₀₆ : Keep [.eax, .ebx, .edx, .ebp] s s₆ :=
    (((e₀₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  obtain k₆ := hk.keep e₀₆ (by decide)
  -- X₂ ⊞ Z₂, X₃ ⊞ Z₃
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run z b (6 * j + 1) (by omega_using [hj]) s₆ k₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run z c (6 * j + 2) (by omega_using [hj]) s₇ (k₆.keep e₇ (by simpa using bs.symm))
  obtain e₆₈ : Keep [b, c] s₆ s₈ := (e₇.mono (by simp)).trans (e₈.mono (by simp))
  obtain k₈ := k₆.keep e₆₈ (by simp [bs.symm, cs.symm])
  -- t₀
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .eax (.reg .ebx) _ s₈ rfl
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := alu_run .xor (by simp) .eax (.reg c) _ s₉ rfl
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mulKey_run z (6 * j + 4) (by omega_using [hj]) s₁₀
    ((k₈.keep e₉ (by decide)).keep e₁₀ (by decide))
  obtain e₈₁₁ : Keep [.eax, .edx] s₈ s₁₁ :=
    ((e₉.weaken (by decide)).trans (e₁₀.weaken (by decide))).trans e₁₁
  obtain k₁₁ := k₈.keep e₈₁₁ (by decide)
  obtain ⟨s₁₂, h₁₂, m₁₂, g₁₂, rd₁₂, wr₁₂⟩ := store_t0_run z s₁₁ k₁₁
  obtain e₁₂ : KeepT [] s₁₁ s₁₂ := ⟨fun r _ => by rw [g₁₂], rd₁₂, wr₁₂, by
    rw [m₁₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  obtain k₁₂ := k₁₁.keepT e₁₂ (by simp)
  -- t₁
  obtain ⟨s₁₃, h₁₃, v₁₃, e₁₃⟩ := mov_run .eax (.reg b) _ s₁₂ rfl
  obtain ⟨s₁₄, h₁₄, v₁₄, e₁₄⟩ := alu_run .xor (by simp) .eax (.reg .ebp) _ s₁₃ rfl
  obtain ⟨s₁₅, h₁₅, v₁₅, e₁₅⟩ := alu_run .add (by simp) .eax (.reg .edx) _ s₁₄ rfl
  obtain e₁₂₁₅ : Keep [.eax] s₁₂ s₁₅ := (e₁₃.trans e₁₄).trans e₁₅
  obtain ⟨s₁₆, h₁₆, v₁₆, e₁₆⟩ := mulKey_run z (6 * j + 5) (by omega_using [hj]) s₁₅ (k₁₂.keep e₁₂₁₅ (by decide))
  -- The outputs.
  obtain ht0 : readSrc s₁₆ (.mem (at_ .esi t0Slot)) = some (s₁₁.gpr .edx) := by
    obtain hin := k₁₁.slot (d := t0Slot) (by decide)
    obtain esi₁₆ : s₁₆.gpr .esi = s₁₁.gpr .esi := by
      rw [e₁₆.reg .esi (by decide), e₁₂₁₅.reg .esi (by decide), g₁₂]
    obtain mem₁₆ : s₁₆.mem = s₁₂.mem := by rw [e₁₆.mem, e₁₂₁₅.mem]
    simp only [readSrc, State.ea, State.load32, at_, esi₁₆, mem₁₆, e₁₆.rd, e₁₆.wr, e₁₂₁₅.rd, e₁₂₁₅.wr,
      rd₁₂, wr₁₂, m₁₂]
    rw [← addr, Mem.readW_writeW_self32]
    exact ite_eq_left ⟨_, List.mem_append_right _ hin.choose_spec.1, hin.choose_spec.2⟩
  obtain ⟨s₁₇, h₁₇, v₁₇, e₁₇⟩ := mov_run .eax _ _ s₁₆ ht0
  obtain ⟨s₁₈, h₁₈, v₁₈, e₁₈⟩ := alu_run .add (by simp) .eax (.reg .edx) _ s₁₇ rfl
  obtain ⟨s₁₉, h₁₉, v₁₉, e₁₉⟩ := alu_run .and (by simp) .eax (.imm 0xffff) 0xffff s₁₈ rfl
  obtain ⟨s₂₀, h₂₀, v₂₀, e₂₀⟩ := alu_run .xor (by simp) .ebx (.reg .edx) _ s₁₉ rfl
  obtain ⟨s₂₁, h₂₁, v₂₁, e₂₁⟩ := alu_run .xor (by simp) c (.reg .edx) _ s₂₀ rfl
  obtain ⟨s₂₂, h₂₂, v₂₂, e₂₂⟩ := alu_run .xor (by simp) b (.reg .eax) _ s₂₁ rfl
  obtain ⟨s₂₃, h₂₃, v₂₃, e₂₃⟩ := alu_run .xor (by simp) .ebp (.reg .eax) _ s₂₂ rfl
  simp only [aluF] at v₁₀ v₁₄ v₁₅ v₁₈ v₁₉ v₂₀ v₂₁ v₂₂ v₂₃
  obtain k1219 : Keep [.eax, .edx] s₁₂ s₁₉ :=
    (((e₁₂₁₅.weaken (by decide)).trans e₁₆).trans (e₁₇.weaken (by decide))).trans
      ((e₁₈.weaken (by decide)).trans (e₁₉.weaken (by decide)))
  refine ⟨s₂₃, ?_, ?_, ?_⟩
  · simp only [roundWith, mulKey, addKey]
    obtain m₁ : runBlock isa ([.mov .eax (.reg .ebx), .alu .xor .eax (.reg c)] : List Instr) s₈ = some s₁₀ :=
      run_append h₉ h₁₀
    obtain m₂ : runBlock isa ([.store (at_ .esi t0Slot) .edx, .mov .eax (.reg b), .alu .xor .eax (.reg .ebp),
        .alu .add .eax (.reg .edx)] : List Instr) s₁₁ = some s₁₅ :=
      run_append h₁₂ (run_append h₁₃ (run_append h₁₄ h₁₅))
    obtain m₃ : runBlock isa ([.mov .eax (.mem (at_ .esi t0Slot)), .alu .add .eax (.reg .edx),
        .alu .and .eax (.imm 0xffff), .alu .xor .ebx (.reg .edx), .alu .xor c (.reg .edx),
        .alu .xor b (.reg .eax), .alu .xor .ebp (.reg .eax)] : List Instr) s₁₆ = some s₂₃ :=
      run_append h₁₇ (run_append h₁₈ (run_append h₁₉ (run_append h₂₀ (run_append h₂₁
        (run_append h₂₂ h₂₃)))))
    exact run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆)
      h₇) h₈) m₁) h₁₁) m₂) h₁₆) m₃
  · -- The values, from the last write back.
    obtain a : s₈.gpr .ebx = (Spec.Idea.mul (x.getD 0 0) (rk z j 0)).setWidth 32 := by
      rw [e₆₈.reg .ebx (by simp [bb.symm, cb.symm]), e₆.reg .ebx (by decide), e₅.reg .ebx (by decide),
        e₄.reg .ebx (by decide), v₃, v₂, v₁, hx.ebx, setWidth_setWidth16_32]
      rfl
    obtain d : s₈.gpr .ebp = (Spec.Idea.mul (x.getD 3 0) (rk z j 3)).setWidth 32 := by
      rw [e₆₈.reg .ebp (by simp [bp.symm, cp.symm]), v₆, v₅, v₄, e₀₃.reg .ebp (by decide), hx.ebp,
        setWidth_setWidth16_32]
    obtain bv : s₈.gpr b = (x.getD 1 0 + rk z j 1).setWidth 32 := by
      rw [e₈.reg b (by simpa using hbc), v₇, e₀₆.reg b (by simp [ba, bb, bd, bp]), hx.b,
        setWidth_setWidth16_32]
    obtain cv : s₈.gpr c = (x.getD 2 0 + rk z j 2).setWidth 32 := by
      rw [v₈, e₇.reg c (by simpa using Ne.symm hbc), e₀₆.reg c (by simp [ca, cb, cd, cp]), hx.c,
        setWidth_setWidth16_32]
    obtain t₀ : s₁₁.gpr .edx = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4)).setWidth 32 := by
      rw [v₁₁, v₁₀, v₉, e₉.reg c (by simpa using ca), a, cv, xor_setWidth32, setWidth_setWidth16_32]
    obtain hconst : ∀ r, r ∉ [Reg.eax, .edx] → s₁₉.gpr r = s₈.gpr r := fun r h =>
      (k1219.reg r h).trans ((congrFun g₁₂ r).trans (e₈₁₁.reg r h))
    obtain t₁ : s₁₆.gpr .edx = (Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₆, v₁₅, v₁₄, v₁₃, e₁₄.reg .edx (by decide), e₁₃.reg .edx (by decide),
        e₁₃.reg .ebp (by decide), g₁₂, e₈₁₁.reg b (by simp [ba, bd]), e₈₁₁.reg .ebp (by decide), bv, d, t₀,
        xor_setWidth32, add_setWidth32]
    obtain t₂ : s₁₉.gpr .eax = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4) + Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₉, v₁₈, v₁₇, e₁₇.reg .edx (by decide), t₀, t₁, add_mask32, setWidth_setWidth16_32]
    obtain edx₁₉ : s₁₉.gpr .edx = s₁₆.gpr .edx := by
      rw [e₁₉.reg .edx (by decide), e₁₈.reg .edx (by decide), e₁₇.reg .edx (by decide)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e₂₃.reg .ebx (by decide), e₂₂.reg .ebx (by simpa using bb.symm), e₂₁.reg .ebx (by simpa using cb.symm),
        v₂₀, hconst .ebx (by decide), a, edx₁₉, t₁, xor_setWidth32]
      rfl
    · rw [e₂₃.reg c (by simpa using cp), e₂₂.reg c (by simpa using Ne.symm hbc), v₂₁,
        e₂₀.reg c (by simpa using cb), e₂₀.reg .edx (by decide), hconst c (by simp [ca, cd]), cv, edx₁₉, t₁,
        xor_setWidth32]
      rfl
    · rw [e₂₃.reg b (by simpa using bp), v₂₂, e₂₁.reg b (by simpa using hbc), e₂₀.reg b (by simpa using bb),
        e₂₁.reg .eax (by simpa using ca.symm), e₂₀.reg .eax (by decide), hconst b (by simp [ba, bd]), bv, t₂,
        xor_setWidth32]
      rfl
    · rw [v₂₃, e₂₂.reg .ebp (by simpa using bp.symm), e₂₁.reg .ebp (by simpa using cp.symm),
        e₂₀.reg .ebp (by decide), e₂₂.reg .eax (by simpa using ba.symm), e₂₁.reg .eax (by simpa using ca.symm),
        e₂₀.reg .eax (by decide), hconst .ebp (by decide), d, t₂, xor_setWidth32]
      rfl
  · refine KeepT.trans (by decide) ((e₀₆.weaken (by decide)).toT.trans (by decide) ((e₆₈.mono fun r hr => ?_).toT)) ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hB _ (by simp)
      · exact hC _ (by simp)
    refine KeepT.trans (by decide) (e₈₁₁.weaken (by decide)).toT (KeepT.trans (by decide)
      (e₁₂.mono (by simp)) ?_)
    refine KeepT.trans (by decide) (k1219.weaken (by decide)).toT ?_
    exact (((e₂₀.weaken (by decide)).trans (e₂₁.mono hC)).trans ((e₂₂.mono hB).trans
      (e₂₃.weaken (by decide)))).toT

end VG.Proof.Idea.X86

end

end

/-!
# IDEA key expansion on x86 (32-bit)

The schedule's 26 words (two subkeys each) are fixed bit permutations of the
key's four 32-bit words, built in place: the whole of `expandBody` is
checked by one evaluation over the lane domain (`expand_check`,
`Straight.linear_ok`), with the key's words (at `eax`) as external words and
the schedule's (at `ecx`) as slots: bit `p` of schedule word `w` is the key
bit `expandSrc32 w p`, and every subkey bit is then the key bit
`Spec.Idea.expandKey` takes (`expandKey_getLsbD`).
-/

@[expose] public section

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Idea.X86 VG.Impl.Idea

/-- The key's four words at `eax`, the schedule's 26 at `ecx`. -/
def eCfg : Cfg := { base := .ecx, slots := 26, ext := .eax, exts := 4 }

/-- Bit `p` of word `w`: atom `32 j + t`, bit `t` of key word `j`. -/
def eG (w p : Nat) : List Nat := [32 * (expandSrc32 w p).1 + (expandSrc32 w p).2]

theorem expand_check :
    check (lanes 32 7) eCfg (linExt 0) expandBody (linEnv [])
      (linPost 26 7 ((List.range 26).map fun w => (w, eG w))) = true := by
  lit_decide

/-- `vg_idea_expand_key` on x86: the key (16 bytes) readable, the schedule
(104 bytes) writable, apart from each other, the arguments and the return
address, none wrapping around. -/
def expandContract : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 104⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched] ∧ key.Disjoint sched ∧ args.Disjoint sched ∧
      ret.Disjoint sched ∧ (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 104 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' := Spec.Idea.scheduleAt s'.mem ((arg s 1).setWidth 64) =
    Spec.Idea.expandKey (Spec.Idea.keyAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

theorem arg_src {s : State} {i n : Nat} (hi : 4 * i + 4 ≤ n) (h : ⟨argAddr s 0, n⟩ ∈ s.rd)
    (hf : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) :
    readSrc s (.mem (argOp i)) = some (arg s i) := by
  simp only [readSrc, State.load32, arg]
  refine ite_eq_left ⟨_, List.mem_append_left _ h, ?_⟩
  show Region.Contains _ (addr (s.gpr .esp) (4 + 4 * i)) 4
  simp only [argAddr]
  rw [show ((s.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 : Addr) = addr (s.gpr .esp) 4 from rfl,
    addr_eq (by omega_using [hi, hf]), addr_eq (by omega_using [hi, hf])]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [hf])

theorem expand_correct (s : State) (hs : expandContract.pre s) :
    WP isa expandKey s (fun s' => abiPreserved s s' ∧ expandContract.post s s') := by
  obtain ⟨hrd, hwr, dKS, dAS, dRS, fitK, fitS, fitSp⟩ := hs
  have hargs : ⟨argAddr s 0, 8⟩ ∈ s.rd := by rw [hrd]; simp
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (arg_src (i := 0) (by decide) hargs (by omega_using [fitSp]))
  have hargs₁ : ⟨argAddr s₁ 0, 8⟩ ∈ s₁.rd := by
    rw [e₁.rd]; simp only [argAddr, e₁.reg .esp (by decide)]; exact hargs
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .ecx _ _ s₁ (arg_src (i := 1) (by decide) hargs₁
    (by rw [e₁.reg .esp (by decide)]; omega_using [fitSp]))
  have a1 : arg s₁ 1 = arg s 1 := by simp only [arg, argAddr, e₁.mem, e₁.reg .esp (by decide)]
  have ecx₂ : s₂.gpr .ecx = arg s 1 := v₂.trans a1
  have eax₂ : s₂.gpr .eax = arg s 0 := (e₂.reg .eax (by decide)).trans v₁
  have e₀₂ : Keep [.eax, .ecx] s s₂ := (e₁.weaken (by decide)).trans (e₂.weaken (by decide))
  have hok : Ok eCfg s₂ := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
    · show InRegions s₂.wr (addr (s₂.gpr .ecx) (4 * k)) 4
      rw [e₀₂.wr, hwr, ecx₂, addr_eq (by simp only [eCfg] at hk; omega_using [fitS, hk])]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by simp only [eCfg] at hk; omega_using [hk])
        (by simp only [eCfg] at hk; omega_using [hk])⟩
    · show InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) (4 * k)) 4
      simp only [eCfg] at hk
      rw [e₀₂.rd, hrd, eax₂, addr_eq (by omega_using [fitK, hk])]
      exact ⟨⟨(arg s 0).setWidth 64, 16⟩, by simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
    · show (s₂.gpr .ecx).toNat + 4 * 26 ≤ 2 ^ 32
      rw [ecx₂]; omega_using [fitS]
    · simp only [eCfg] at hk hj
      show Mem.Sep (addr (s₂.gpr .ecx) (4 * k)) 4 (addr (s₂.gpr .eax) (4 * j)) 4
      rw [ecx₂, eax₂, addr_eq (by omega_using [fitS, hk]), addr_eq (by omega_using [fitK, hj])]
      exact fun x h₁ h₂ => dKS x (Region.Contains.byte (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])) h₂)
        (Region.Contains.byte (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])) h₁)
  obtain ⟨s', hs', hout, hrd', hwr', hoth, hfr⟩ := linear_ok expand_check hok
    (fun i => s₂.mem.readW (wordAddr (s₂.gpr .eax) i) 32)
    (fun r i h => by simp at h) (fun j hj => by
      have hj' : j < 4 := hj
      refine ⟨by omega_using [hj'], ?_⟩
      simp only [Nat.zero_add]
      rfl)
  refine WP.of_runBlock ⟨s', ?_, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · exact run_append (a := [_, _]) (run_append h₁ h₂) hs'
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hk : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp, .esp], (expandBody.all fun i => i.dst != some r) = true := by
      lit_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (hoth _ (hk _ (by simp))).trans (e₀₂.reg _ (by decide))
  · rw [← e₀₂.mem]
    refine hfr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, eCfg, ecx₂]
    exact dRS
  · show Spec.Idea.scheduleAt s'.mem _ = _
    apply Vector.ext
    intro n hn
    rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have hw := hout (n / 2) (eG (n / 2)) (List.mem_map.mpr ⟨n / 2, List.mem_range.mpr (by omega_using [hn]), rfl⟩)
      (16 * (n % 2) + b) (by omega_using [hb])
    rw [scheduleAt_getLsbD32 _ _ hn hb, ← addr_eq (by omega_using [fitS, hn]), ← ecx₂]
    show (s'.mem.readW (wordAddr (s₂.gpr eCfg.base) (n / 2)) 32).getLsbD _ = _
    rw [hw]
    have src := keyLoc32_spec (keyBit_lt (2 * (n / 2) + (16 * (n % 2) + b) / 16) ((16 * (n % 2) + b) % 16))
    simp only [eG, xorBits_cons, xorBits_nil, Bool.xor_false]
    rw [bitOf_word _ _ _ (by simpa [expandSrc32] using src.2.1), expandKey_getLsbD _ hn hb]
    simp only [expandSrc32] at src ⊢
    rw [show 2 * (n / 2) + (16 * (n % 2) + b) / 16 = n by omega_using [hb], show (16 * (n % 2) + b) % 16 = b by omega_using [hb]]
      at src ⊢
    rw [wordAddr, eax₂, addr_eq (by omega_using [fitK, src]), readW32_getLsbD _ _ src.2.1, Offset.add_ofNat_add_ofNat,
      src.2.2.1, src.2.2.2, keyValue_getLsbD _ (keyBit_lt _ _), keyAt_getD _ _ (by omega_using []), e₀₂.mem]

def keyTaint : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem keyTaint_wf {s : State} (h : expandContract.pre s) : VG.X86.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, ao, ro, _, _, spfit⟩ := h
  refine Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨spfit, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [keyTaint, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact Taint.frame_disjoint (n := 8) (by omega_using [spfit]) ro ao

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : expandContract.pre s₁) (h₂ : expandContract.pre s₂)
    (hp : expandContract.pub s₁ s₂) : VG.X86.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, expandContract.pre s → (s.gpr .esp).toNat + 12 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [keyTaint] at hk
    rw [show Taint.depth keyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [Taint.argByte_eq (fit _ h₁) h4 hk, Taint.argByte_eq (fit _ h₂) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

theorem expandKey_constantTime : ConstantTime isa expandContract.pre expandContract.pub expandKey :=
  VG.Taint.constantTime (A := taint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def keySatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 104⟩]

theorem expandKey_verified : Verified target expandKey (Spec.Idea.expandKeyContract abi) := by
  refine Verified.of_correct expand_correct expandKey_constantTime ?_
  sig_implies [Spec.Idea.expandKeyContract, Spec.Idea.expandKeySig, Spec.Idea.expandKeyPost, abi, argSlots,
    argVal, argBytes, expandContract] [keySatState, arg, argAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Idea.X86
