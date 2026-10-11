import VerifiedGarbage.Proof.Idea.X86.Mul
import VerifiedGarbage.Proof.Idea.Memory32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# IDEA on x86 (32-bit): a round

`round_run`: round `j` of the code (`roundWith j b c`) maps the state words
in `ebx`, `b`, `c`, `ebp` (`Holds`) to `Spec.Idea.round` of them under
subkeys `6j … 6j + 5`, read from the copy of the schedule at `esi`
(`KeyOk`) when they are used, and leaves the new middle words in `c` and
`b`. It writes `eax`, `edx` and `t₀`'s slot, which follows the subkeys
(`KeepT`).
-/

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

/-- The scratch buffer at `esi` (`4 * slots` bytes): its first 104 bytes
hold the subkeys `z`, then `t₀`'s slot; all writable, not wrapping around. -/
structure KeyOk (z : Spec.Idea.Schedule) (s : State) : Prop where
  wr : ⟨(s.gpr .esi).setWidth 64, 4 * slots⟩ ∈ s.wr
  fit : (s.gpr .esi).toNat + 4 * slots ≤ 2 ^ 32
  sched : Spec.Idea.scheduleAt s.mem ((s.gpr .esi).setWidth 64) = z

theorem KeyOk.keep {z : Spec.Idea.Schedule} {rs : List Reg} {s s' : State} (h : KeyOk z s)
    (hk : Keep rs s s') (hesi : .esi ∉ rs) : KeyOk z s' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hk.wr, hk.reg .esi hesi]; exact h.wr
  · rw [hk.reg .esi hesi]; exact h.fit
  · rw [hk.mem, hk.reg .esi hesi]; exact h.sched

theorem KeyOk.slot {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {d : Nat} (hd : d + 4 ≤ 4 * slots) :
    InRegions s.wr (addr (s.gpr .esi) d) 4 := by
  rw [addr_eq (by have := h.fit; simp only [slots] at *; omega)]
  exact ⟨_, h.wr, Offset.contains_base _ hd (by simp only [slots] at *; omega)⟩

/-- Subkey `k`, read at its offset. -/
theorem KeyOk.src {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {k : Nat} (hk : k < 52) :
    SrcOk s (.mem (at_ .esi (2 * k))) (s.mem.readW (addr (s.gpr .esi) (2 * k)) 32) ∧
      (s.mem.readW (addr (s.gpr .esi) (2 * k)) 32).setWidth 16 = z.getD k 0 := by
  refine ⟨fun t hm hrd hwr hg => ?_, ?_⟩
  · have hin := h.slot (d := 2 * k) (by simp only [slots]; omega)
    simp only [readSrc, State.ea, State.load32, at_, hg .esi (by decide), hrd, hwr, hm]
    exact ite_eq_left (by rw [← addr]; exact ⟨_, List.mem_append_right _ hin.choose_spec.1, hin.choose_spec.2⟩)
  · rw [addr_eq (by have := h.fit; simp only [slots] at *; omega), subkey_lo32 _ _ hk, h.sched]

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
  have e := hk.reg .esi hesi
  refine ⟨by rw [hk.wr, e]; exact h.wr, by rw [e]; exact h.fit, ?_⟩
  rw [e, ← h.sched]
  refine scheduleAt_congr (frame_bytes hk.frame ?_ (by decide))
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  rw [addr_eq (by have := h.fit; simp only [t0Slot, slots] at *; omega)]
  exact Offset.base_disjoint _ (by decide) (by have := h.fit; simp only [t0Slot, slots] at *; omega)

/-- The six subkeys of round `j`. -/
abbrev rk (z : Spec.Idea.Schedule) (j i : Nat) : Spec.Idea.Word := z.getD (6 * j + i) 0

/-- The written registers of a round. -/
abbrev roundWrites : List Reg := [.eax, .ebx, .ecx, .edx, .edi, .ebp]

theorem store_t0_run (z : Spec.Idea.Schedule) (s : State) (h : KeyOk z s) :
    ∃ s', runBlock isa [.store (at_ .esi t0Slot) .edx] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr .esi) t0Slot) (s.gpr .edx) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions s.wr (s.ea (at_ .esi t0Slot)) 4 := h.slot (d := t0Slot) (by decide)
  simp only [runBlock_cons, isa, exec, State.store32, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem round_run (j : Nat) (hj : j < 8) (b c : Reg)
    (hb : (b == .ecx && c == .edi || b == .edi && c == .ecx) = true)
    (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x b c s) (hk : KeyOk z s) :
    ∃ s', runBlock isa (roundWith j b c) s = some s' ∧
      Holds (Spec.Idea.round (rk z j 0) (rk z j 1) (rk z j 2) (rk z j 3) (rk z j 4) (rk z j 5) x)
        c b s' ∧
      KeepT roundWrites s s' := by
  have nb : ∀ r ∈ [Reg.eax, .ebx, .edx, .ebp, .esi], b ≠ r ∧ c ≠ r := by
    intro r hr
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have hbc : b ≠ c := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  have hsub : ∀ r ∈ [b, c], r ∈ roundWrites := by
    rcases Bool.or_eq_true _ _ |>.mp hb with h | h <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> decide
  obtain ⟨ba, ca⟩ := nb .eax (by simp)
  obtain ⟨bb, cb⟩ := nb .ebx (by simp)
  obtain ⟨bd, cd⟩ := nb .edx (by simp)
  obtain ⟨bp, cp⟩ := nb .ebp (by simp)
  obtain ⟨bs, cs⟩ := nb .esi (by simp)
  have hB : ∀ r ∈ [b], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
  have hC : ∀ r ∈ [c], r ∈ roundWrites := fun r hr => hsub r (by simp at hr; simp [hr])
  -- X₁ ⊙ Z₁
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ebx) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run z (6 * j) (by omega) s₁ (hk.keep e₁ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mov_run .ebx (.reg .edx) _ s₂ rfl
  -- X₄ ⊙ Z₄
  have e₀₃ : Keep [.eax, .ebx, .edx] s s₃ :=
    ((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax (.reg .ebp) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := mulKey_run z (6 * j + 3) (by omega) s₄
    ((hk.keep e₀₃ (by decide)).keep e₄ (by decide))
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .ebp (.reg .edx) _ s₅ rfl
  have e₀₆ : Keep [.eax, .ebx, .edx, .ebp] s s₆ :=
    (((e₀₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  have k₆ := hk.keep e₀₆ (by decide)
  -- X₂ ⊞ Z₂, X₃ ⊞ Z₃
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run z b (6 * j + 1) (by omega) s₆ k₆
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run z c (6 * j + 2) (by omega) s₇ (k₆.keep e₇ (by simpa using bs.symm))
  have e₆₈ : Keep [b, c] s₆ s₈ := (e₇.mono (by simp)).trans (e₈.mono (by simp))
  have k₈ := k₆.keep e₆₈ (by simp [bs.symm, cs.symm])
  -- t₀
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .eax (.reg .ebx) _ s₈ rfl
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := alu_run .xor (by simp) .eax (.reg c) _ s₉ rfl
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := mulKey_run z (6 * j + 4) (by omega) s₁₀
    ((k₈.keep e₉ (by decide)).keep e₁₀ (by decide))
  have e₈₁₁ : Keep [.eax, .edx] s₈ s₁₁ :=
    ((e₉.weaken (by decide)).trans (e₁₀.weaken (by decide))).trans e₁₁
  have k₁₁ := k₈.keep e₈₁₁ (by decide)
  obtain ⟨s₁₂, h₁₂, m₁₂, g₁₂, rd₁₂, wr₁₂⟩ := store_t0_run z s₁₁ k₁₁
  have e₁₂ : KeepT [] s₁₁ s₁₂ := ⟨fun r _ => by rw [g₁₂], rd₁₂, wr₁₂, by
    rw [m₁₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  have k₁₂ := k₁₁.keepT e₁₂ (by simp)
  -- t₁
  obtain ⟨s₁₃, h₁₃, v₁₃, e₁₃⟩ := mov_run .eax (.reg b) _ s₁₂ rfl
  obtain ⟨s₁₄, h₁₄, v₁₄, e₁₄⟩ := alu_run .xor (by simp) .eax (.reg .ebp) _ s₁₃ rfl
  obtain ⟨s₁₅, h₁₅, v₁₅, e₁₅⟩ := alu_run .add (by simp) .eax (.reg .edx) _ s₁₄ rfl
  have e₁₂₁₅ : Keep [.eax] s₁₂ s₁₅ := (e₁₃.trans e₁₄).trans e₁₅
  obtain ⟨s₁₆, h₁₆, v₁₆, e₁₆⟩ := mulKey_run z (6 * j + 5) (by omega) s₁₅ (k₁₂.keep e₁₂₁₅ (by decide))
  -- The outputs.
  have ht0 : readSrc s₁₆ (.mem (at_ .esi t0Slot)) = some (s₁₁.gpr .edx) := by
    have hin := k₁₁.slot (d := t0Slot) (by decide)
    have esi₁₆ : s₁₆.gpr .esi = s₁₁.gpr .esi := by
      rw [e₁₆.reg .esi (by decide), e₁₂₁₅.reg .esi (by decide), g₁₂]
    have mem₁₆ : s₁₆.mem = s₁₂.mem := by rw [e₁₆.mem, e₁₂₁₅.mem]
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
  have k1219 : Keep [.eax, .edx] s₁₂ s₁₉ :=
    (((e₁₂₁₅.weaken (by decide)).trans e₁₆).trans (e₁₇.weaken (by decide))).trans
      ((e₁₈.weaken (by decide)).trans (e₁₉.weaken (by decide)))
  refine ⟨s₂₃, ?_, ?_, ?_⟩
  · simp only [roundWith, mulKey, addKey]
    have m₁ : runBlock isa ([.mov .eax (.reg .ebx), .alu .xor .eax (.reg c)] : List Instr) s₈ = some s₁₀ :=
      run_append h₉ h₁₀
    have m₂ : runBlock isa ([.store (at_ .esi t0Slot) .edx, .mov .eax (.reg b), .alu .xor .eax (.reg .ebp),
        .alu .add .eax (.reg .edx)] : List Instr) s₁₁ = some s₁₅ :=
      run_append h₁₂ (run_append h₁₃ (run_append h₁₄ h₁₅))
    have m₃ : runBlock isa ([.mov .eax (.mem (at_ .esi t0Slot)), .alu .add .eax (.reg .edx),
        .alu .and .eax (.imm 0xffff), .alu .xor .ebx (.reg .edx), .alu .xor c (.reg .edx),
        .alu .xor b (.reg .eax), .alu .xor .ebp (.reg .eax)] : List Instr) s₁₆ = some s₂₃ :=
      run_append h₁₇ (run_append h₁₈ (run_append h₁₉ (run_append h₂₀ (run_append h₂₁
        (run_append h₂₂ h₂₃)))))
    exact run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆)
      h₇) h₈) m₁) h₁₁) m₂) h₁₆) m₃
  · -- The values, from the last write back.
    have a : s₈.gpr .ebx = (Spec.Idea.mul (x.getD 0 0) (rk z j 0)).setWidth 32 := by
      rw [e₆₈.reg .ebx (by simp [bb.symm, cb.symm]), e₆.reg .ebx (by decide), e₅.reg .ebx (by decide),
        e₄.reg .ebx (by decide), v₃, v₂, v₁, hx.ebx, setWidth_setWidth16_32]
      rfl
    have d : s₈.gpr .ebp = (Spec.Idea.mul (x.getD 3 0) (rk z j 3)).setWidth 32 := by
      rw [e₆₈.reg .ebp (by simp [bp.symm, cp.symm]), v₆, v₅, v₄, e₀₃.reg .ebp (by decide), hx.ebp,
        setWidth_setWidth16_32]
    have bv : s₈.gpr b = (x.getD 1 0 + rk z j 1).setWidth 32 := by
      rw [e₈.reg b (by simpa using hbc), v₇, e₀₆.reg b (by simp [ba, bb, bd, bp]), hx.b,
        setWidth_setWidth16_32]
    have cv : s₈.gpr c = (x.getD 2 0 + rk z j 2).setWidth 32 := by
      rw [v₈, e₇.reg c (by simpa using Ne.symm hbc), e₀₆.reg c (by simp [ca, cb, cd, cp]), hx.c,
        setWidth_setWidth16_32]
    have t₀ : s₁₁.gpr .edx = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4)).setWidth 32 := by
      rw [v₁₁, v₁₀, v₉, e₉.reg c (by simpa using ca), a, cv, xor_setWidth32, setWidth_setWidth16_32]
    have hconst : ∀ r, r ∉ [Reg.eax, .edx] → s₁₉.gpr r = s₈.gpr r := fun r h =>
      (k1219.reg r h).trans ((congrFun g₁₂ r).trans (e₈₁₁.reg r h))
    have t₁ : s₁₆.gpr .edx = (Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₆, v₁₅, v₁₄, v₁₃, e₁₄.reg .edx (by decide), e₁₃.reg .edx (by decide),
        e₁₃.reg .ebp (by decide), g₁₂, e₈₁₁.reg b (by simp [ba, bd]), e₈₁₁.reg .ebp (by decide), bv, d, t₀,
        xor_setWidth32, add_setWidth32]
    have t₂ : s₁₉.gpr .eax = (Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^
        (x.getD 2 0 + rk z j 2)) (rk z j 4) + Spec.Idea.mul (((x.getD 1 0 + rk z j 1) ^^^
        Spec.Idea.mul (x.getD 3 0) (rk z j 3)) +
        Spec.Idea.mul (Spec.Idea.mul (x.getD 0 0) (rk z j 0) ^^^ (x.getD 2 0 + rk z j 2)) (rk z j 4))
        (rk z j 5)).setWidth 32 := by
      rw [v₁₉, v₁₈, v₁₇, e₁₇.reg .edx (by decide), t₀, t₁, add_mask32, setWidth_setWidth16_32]
    have edx₁₉ : s₁₉.gpr .edx = s₁₆.gpr .edx := by
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
