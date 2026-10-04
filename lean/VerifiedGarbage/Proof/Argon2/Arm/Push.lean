import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RelCT

/-!
# Argon2 on ARMv7: calls in frames of their stack arguments

A call whose stack arguments are pushed in a frame of their own (`push
{rs}`, the call, `ldr t, [sp], #n`): the callee finds word `i` of the frame
as its stack argument `i` (`pushed_arg`); `frameCall_ok` runs such a frame
around a call of verified code that may have frames of its own (`WP.callF`),
which changes memory only in what the callee may write and the `k` bytes
below the stack pointer (`After`); `frameCall_rel` relates two runs of one.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Arm.FrameStack

/-- The `n` bytes below `sp`. -/
abbrev stkR (sp : BitVec 32) (n : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 n, n⟩

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Word `i` a push stored. -/
theorem storeWords_readW (m : Mem) (a : BitVec 32) (vs : List (BitVec 32)) (h : a.toNat + 4 * vs.length < 2 ^ 32)
    {i : Nat} (hi : i < vs.length) :
    (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i] := by
  induction vs generalizing m a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons v vs ih =>
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 := by omega
    have e4 : (a + 4).toNat = a.toNat + 4 := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 4) (by omega), Nat.mod_eq_of_lt h4]
    cases i with
    | zero =>
      have hf := storeWords_frame vs (m.writeW (State.addr a) v) (a + 4) (by rw [e4]; omega)
      rw [show a + BitVec.ofNat 32 (4 * 0) = a by simp, hf.readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr
          rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_add h4]
          exact Offset.base_disjoint _ (Nat.le_refl 4) (by omega))
        (by decide), Mem.readW_writeW_self32]
      rfl
    | succ j =>
      rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
        rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 2; omega]
      exact ih _ _ (by rw [e4]; omega) (by omega)

/-- Stack argument `i` of a callee entered after `push {rs}`: the register `rs[i]`. -/
theorem pushed_arg {rs : List Reg} {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {i : Nat} (hi : i < rs.length)
    {rd wr : List Region} :
    stackArg ((pushed rs s).callEntry.withRegions rd wr) i = s.gpr rs[i] := by
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp, State.callEntry_mem,
    State.callEntry_sp, pushed]
  rw [storeWords_readW _ _ _ (by rw [List.length_map, sub_toNat' h]; have := s.sp.isLt; omega)
    (by simpa using hi)]
  simp

/-- Stack argument `i` agrees in two runs whose pushed register `rs[i]` does. -/
theorem pushed_arg_eq {rs : List Reg} {s₁ s₂ : State} (h₁ : 4 * rs.length ≤ s₁.sp.toNat)
    (h₂ : 4 * rs.length ≤ s₂.sp.toNat) {i : Nat} (hi : i < rs.length) (hr : s₁.gpr rs[i] = s₂.gpr rs[i])
    {rd wr rd' wr' : List Region} :
    stackArg ((pushed rs s₁).callEntry.withRegions rd wr) i =
      stackArg ((pushed rs s₂).callEntry.withRegions rd' wr') i := by
  rw [pushed_arg h₁ hi, pushed_arg h₂ hi, hr]

theorem pushed_argAddr {rs : List Reg} {s : State} (h : 4 * rs.length ≤ s.sp.toNat) {rd wr : List Region} :
    stackArgAddr ((pushed rs s).callEntry.withRegions rd wr) 0 =
      State.addr s.sp - BitVec.ofNat 64 (4 * rs.length) := by
  simp only [stackArgAddr, State.withRegions_sp, State.callEntry_sp, pushed_sp, Nat.mul_zero]
  rw [BitVec.add_zero, addr_sub' h]

theorem pushed_sp_toNat {rs : List Reg} {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    (pushed rs s).sp.toNat = s.sp.toNat - 4 * rs.length := by
  rw [pushed_sp, sub_toNat' h]

/-- The frame's words are below the stack pointer. -/
theorem pushed_stk {rs : List Reg} {s : State} (h : 4 * rs.length ≤ s.sp.toNat) :
    Frame [stkR s.sp (4 * rs.length)] s.mem (pushed rs s).mem := by
  have := pushed_frameA (rs := rs) (s := s) h
  simpa [belowA, addr_sub' h] using this

/-- What a framed call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the `k` bytes
below the stack pointer. -/
structure After (k : Nat) (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [stkR s.sp k]) s.mem s'.mem

theorem stkR_inner {sp : BitVec 32} {a k b : Nat} (h : a + k ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (stkR (sp - BitVec.ofNat 32 k) a) (stkR sp b) := by
  have := belowA_inner (sp := sp) (a := a) (b := b) (k := k) h hb
  simp only [belowA] at this
  rwa [addr_sub' (x := sp - BitVec.ofNat 32 k) (k := a) (by rw [sub_toNat' (by omega)]; omega),
    addr_sub' (x := sp) (k := b) hb] at this

theorem stkR_sub {sp : BitVec 32} {a b : Nat} (h : a ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (stkR sp a) (stkR sp b) := by
  have := stkR_inner (sp := sp) (a := a) (k := 0) (b := b) (by omega) hb
  simpa using this

/-- A frame of the words `rs`, popped into `t`, around a call of verified code
whose frames use at most `armStack c` bytes: the callee runs from the state
after the push, and the frame leaves `After`. -/
theorem frameCall_ok {rs : List Reg} {t : Reg} (hrs : regList rs = true) (ht : t ∉ preserved)
    (hlt : 4 * rs.length < 256) {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {K : Nat} (hst : 4 * rs.length + armStack c ≤ K) {s : State} (hK : K ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed rs s).callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) ((pushed rs s).rd ++ (pushed rs s).wr))
    (hw : Covers wr (pushed rs s).wr) {Q : State → Prop}
    (hQ : ∀ s₂ : State, After K s wr (popped t (4 * rs.length) s₂) →
      k.post ((pushed rs s).callEntry.withRegions rd wr) (s₂.withRegions rd wr) →
      Q (popped t (4 * rs.length) s₂)) :
    WP isa (.frame (.push rs) (.call n c) (.pop t (4 * rs.length))) s Q := by
  have hn : 4 * rs.length ≤ s.sp.toNat := by omega
  refine WP.frame (rs := rs) (r := t) hrs hn hlt ?_
  refine WP.callF hv hpre hc hw (by rw [pushed_sp, sub_toNat' hn]; omega)
    fun s₂ hrd hwr hsp hf hcs hpost => ?_
  refine hQ s₂ ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩ hpost
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ t := fun e => ht (e ▸ hr)
    rw [popped_gpr this, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    refine Frame.trans (Frame.sub (pushed_stk hn) fun r hr => ?_) (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), stkR_sub (by omega) hK⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        have := stkR_inner (sp := s.sp) (a := armStack c) (k := 4 * rs.length) (b := K) (by omega) hK
        simpa [belowA, pushed_sp, addr_sub' (x := s.sp - BitVec.ofNat 32 (4 * rs.length)) (k := armStack c)
          (by rw [sub_toNat' hn]; omega)] using this

theorem push_eq {rs : List Reg} {s a : State} (hrs : regList rs = true) (h : isa.push (.push rs) s = some a) :
    a = pushed rs s := by
  rw [push_pushed hrs (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- Two runs of such a frame leak the same, if their stack pointers are the
same and the callee's preconditions and public data hold. -/
theorem frameCall_rel {rs : List Reg} {t : Reg} {m : Nat} (hrs : regList rs = true) {n : String} {c : Prog isa}
    {k : Contract isa} (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧
      k.pre ((pushed rs s₁).callEntry.withRegions rd wr) ∧
      k.pre ((pushed rs s₂).callEntry.withRegions rd wr) ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) ((pushed rs s₁).rd ++ (pushed rs s₁).wr) ∧ Covers wr (pushed rs s₁).wr ∧
      Covers (rd ++ wr) ((pushed rs s₂).rd ++ (pushed rs s₂).wr) ∧ Covers wr (pushed rs s₂).wr) :
    RelCT isa P (.frame (.push rs) (.call n c) (.pop t m)) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => (h s₁ s₂ hp).1) (RelCT.call hv hct rd wr fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_)
  rw [push_eq hrs pa, push_eq hrs pb]
  exact (h s₁ s₂ hp).2

end VG.Proof.Argon2.Arm
