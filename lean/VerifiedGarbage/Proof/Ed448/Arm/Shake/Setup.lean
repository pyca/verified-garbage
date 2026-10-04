import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup

/-!
# Ed448 on ARMv7: setting up a call's arguments

`Whole.Ctx.setup` (`Proof/Ed25519/Arm/Whole/Setup.lean`), for values that
may also read the caller's stack arguments beyond the six that `wrap 6`
saves, where the caller put them: `.caller j d`, for `10 ≤ j < n`, reads
the word at `E + 248 + 4 j` (`Slot n`). The set-up also leaves every
register but `r0`, `r12` and the destinations alone (`Ctx.setup`), so that
an argument can be moved into its register before it, and writes only the
words of its stack arguments.
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.ARGS Whole.value Whole.SetupStep Whole.SetupStep.refl
  Whole.StackStep Whole.StackStep.refl Whole.setArg_ok)

/-- The saved words a value may read, below `n`: the six arguments `wrap 6`
saves, and the caller's stack arguments from the third (`248 + 4 * 10 = 288`). -/
abbrev Slot (n j : Nat) : Prop := j < n ∧ (j < 6 ∨ 10 ≤ j)

def valid (n : Nat) : Value → Prop
  | .const k => k < 65536
  | .frame d => d < 256
  | .caller j d => Slot n j ∧ d < 256

/-- The words up to `n` fit below `2^32`, with at least the six saved ones. -/
abbrev Fits (E : BitVec 32) (n : Nat) : Prop := 6 ≤ n ∧ n ≤ 16 ∧ E.toNat + 248 + 4 * n ≤ 2 ^ 32

variable {n : Nat}

theorem setArg_ok {s : State} {E : BitVec 32} {r : Reg} {v : Value}
    (he : s.sp = E) (hE : Fits E n) (hv : valid n v)
    (hr : ∀ j d, v = .caller j d → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (setArg r v)) s fun t => Whole.SetupStep [r] s t ∧ t.gpr r = Whole.value E s.mem v := by
  cases v with
  | const k => exact Whole.setArg_ok he (by omega) hv (fun _ _ h => by cases h)
  | frame d => exact Whole.setArg_ok he (by omega) hv (fun _ _ h => by cases h)
  | caller j d =>
    obtain ⟨hj, hd⟩ := hv
    have hj' : j < 16 := by omega
    have ha : 248 + 4 * j < 4096 := by omega
    have he' : State.addr (E + BitVec.ofNat 32 (248 + 4 * j)) =
        State.addr E + BitVec.ofNat 64 (248 + 4 * j) := addr_add (by omega)
    have enc : encodable (BitVec.ofNat 32 d) = true := by
      apply List.any_eq_true.mpr
      refine ⟨0, by decide, ?_⟩
      simp only [Nat.mul_zero, BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.zero_mod, Nat.sub_zero,
        BitVec.shiftLeft_zero, BitVec.ushiftRight_eq_zero (Nat.le_refl 32), BitVec.or_zero,
        BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
    have hr' := hr j d rfl
    apply WP.of_runBlock
    simp only [setArg, Whole.value, runBlock_cons, runStep_some, runBlock_nil, exec,
      ha, ite_true, he, he', State.load32, hr', Option.map_some, Op2.eval, enc,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, True.intro⟩
    intro q hq
    have hqr : q ≠ r := by simpa using hq
    rw [RegUpd.gpr_setReg_of_ne _ _ hqr, RegUpd.gpr_setReg_of_ne _ _ hqr]

theorem setupRegs_ok {s : State} {E : BitVec 32} {args : List (Reg × Value)}
    (he : s.sp = E) (hE : Fits E n) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid n p.2)
    (hr : ∀ j, Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (args.flatMap fun (r, v) => setArg r v)) s fun t =>
      Whole.SetupStep (args.map Prod.fst) s t ∧ ∀ p ∈ args, t.gpr p.1 = Whole.value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨Whole.SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r, v) List.mem_cons_self
    refine WP.mono (setArg_ok he hE hv0 ?_) fun u ⟨hu, hval⟩ => ?_
    · intro j d h
      subst v
      exact hr j hv0.1
    refine WP.mono (ih (hu.sp.trans he) hn.2
      (fun p hp => hv p (List.mem_cons_of_mem _ hp)) ?_) fun t ⟨ht, hvals⟩ => ?_
    · intro j hj
      rw [hu.rd, hu.wr]
      exact hr j hj
    refine ⟨hu.trans ht, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (ht.regs r hn.1).trans hval
    · rw [hvals p hp, hu.mem]

/-- Values read only the saved words, beyond the outgoing stack slots. -/
theorem value_frame {E : BitVec 32} {m m' : Mem}
    (hE : Fits E n) (hf : Frame [⟨State.addr E, 24⟩] m m') {v : Value} (hv : valid n v) :
    Whole.value E m' v = Whole.value E m v := by
  cases v with
  | const k => rfl
  | frame d => rfl
  | caller j d =>
    obtain ⟨hj, _⟩ := hv
    unfold Whole.value
    apply congrArg (· + BitVec.ofNat 32 d)
    refine hf.readW (r := ⟨State.addr E + BitVec.ofNat 64 (248 + 4 * j), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (d := 248 + 4 * j) (by omega) (by omega)

theorem putArg_ok {s : State} {E : BitVec 32} {j : Nat} {v : Value}
    (he : s.sp = E) (hE : Fits E n) (hj : j < 6) (hv : valid n v)
    (hr : ∀ i, Slot n i → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * i)) 4)
    (hw : InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (putArg j v)) s fun t => Whole.StackStep E s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (4 * j)) (Whole.value E s.mem v) := by
  rw [putArg, WP.block_append_iff]
  refine WP.mono (setArg_ok he hE hv ?_) fun u ⟨hu, hval⟩ => ?_
  · intro i d h
    subst v
    exact hr i hv.1
  have hoff : 4 * j < 256 := by omega
  have ha : State.addr (E + BitVec.ofNat 32 (4 * j)) = State.addr E + BitVec.ofNat 64 (4 * j) :=
    addr_add (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hoff, ite_true,
    State.store32, Nat.reduceLT, RegUpd.gpr_setReg, RegUpd.wr_setReg, reduceCtorEq,
    ite_false, BitVec.add_zero, hu.sp, he, ha, hu.wr, hw, RegUpd.mem_setReg, hu.mem,
    hval, Option.some.injEq, exists_eq_left']
  refine ⟨⟨hu.rd, rfl, hu.sp, ?_, ?_⟩, True.intro⟩
  · intro r h0 h12
    rw [RegUpd.gpr_setReg_of_ne _ _ h12]
    exact hu.regs r (by simpa using h0)
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))

structure StackReady (E : BitVec 32) (s : State) (start : Nat) (vs : List Value) (t : State) : Prop where
  step : Whole.StackStep E s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * vs.length⟩] s.mem t.mem
  words : ∀ j (hj : j < vs.length),
    t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = Whole.value E s.mem (vs[j]'hj)

theorem setupStack_ok {E : BitVec 32} (hE : Fits E n)
    {s : State} {start : Nat} {vs : List Value}
    (he : s.sp = E) (hs : start + vs.length ≤ 6)
    (hv : ∀ v ∈ vs, valid n v)
    (hr : ∀ j, Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4)
    (hw : ∀ j < 6, InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (setupStack start vs)) s (StackReady E s start vs) := by
  induction vs generalizing s start with
  | nil => exact WP.block_nil ⟨.refl _ _, Frame.refl _ _, fun j hj => by simp at hj⟩
  | cons v vs ih =>
    rw [setupStack, WP.block_append_iff]
    have hj : start < 6 := by simp only [List.length_cons] at hs; omega
    refine WP.mono (putArg_ok he hE hj (hv v List.mem_cons_self) hr (hw start hj)) fun u ⟨hu, hmem⟩ => ?_
    refine WP.mono (ih (hu.sp.trans he) (by simp only [List.length_cons] at hs; omega)
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))
      (by intro j hj; rw [hu.rd, hu.wr]; exact hr j hj)
      (by intro j hj; rw [hu.wr]; exact hw j hj)) fun t ht => ?_
    refine ⟨hu.trans ht.step, ?_, ?_⟩
    · have first : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * (v :: vs).length⟩] s.mem u.mem := by
        rw [hmem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_cons]; omega)
      refine first.trans (Frame.sub ht.frame ?_)
      intro r hr
      rw [List.mem_singleton.mp hr]
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub _ (by omega) (by simp only [List.length_cons]; omega)
    · intro j hj'
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [ht.frame.readW (r := ⟨State.addr E + BitVec.ofNat 64 (4 * start), 4⟩)
          (Region.contains_self _ _) (by
            intro r hr
            rw [List.mem_singleton.mp hr]
            exact Offset.disjoint _ (by omega) (by omega) (by simp only [List.length_cons] at hs; omega)) (by decide)]
        rw [hmem, Mem.readW_writeW_self32]
      | succ j =>
        have hj : j < vs.length := by simpa using hj'
        have hw' := ht.words j hj
        rw [value_frame hE hu.frame (hv vs[j] (List.mem_cons_of_mem _ (List.getElem_mem hj)))] at hw'
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using hw'

/-- A call's arguments set up, from a frame whose readable regions hold the
saved words (`hr`). -/
theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : State} (hc : Whole.Ctx E g m₀ rd wr s)
    (hE : Fits E n)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, valid n p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, valid n v)
    (hr : ∀ j, Slot n j → InRegions rd (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (setup args stack)) s fun t => Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E, 4 * stack.length⟩] s.mem t.mem ∧
      (∀ p ∈ args, t.gpr p.1 = Whole.value E s.mem p.2) ∧
      (∀ j (hj : j < stack.length), stackArg t j = Whole.value E s.mem (stack[j]'hj)) ∧
      (∀ r, r ∉ args.map Prod.fst → r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r) := by
  have read : ∀ j, Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    intro j hj
    obtain ⟨R, hR, hcon⟩ := hr j hj
    rw [hc.rd]
    exact ⟨R, List.mem_append_left _ hR, hcon⟩
  have write : ∀ j < 6, InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4 := by
    intro j hj
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  rw [Impl.Ed25519.Arm.Whole.setup, WP.block_append_iff]
  refine WP.mono (setupStack_ok hE hc.sp (by simpa using hs) hvs read write) fun u hu => ?_
  refine WP.mono (setupRegs_ok (hu.step.sp.trans hc.sp) hE hn hv
    (by intro j hj; rw [hu.step.rd, hu.step.wr]; exact read j hj)) fun t ⟨ht, hvals⟩ => ?_
  have hcu : Whole.Ctx E g m₀ rd wr u := by
    refine hc.of_frame hu.step.rd hu.step.wr hu.step.sp ?_ hu.step.frame ?_
    · intro r hr _
      exact hu.step.regs r (by intro h; subst r; exact (by decide : Reg.r0 ∉ preserved) hr)
        (by intro h; subst r; exact (by decide : Reg.r12 ∉ preserved) hr)
    · intro R hR
      rw [List.mem_singleton.mp hR]
      exact .inl (Region.sub_prefix (by decide))
  have hct : Whole.Ctx E g m₀ rd wr t := by
    refine hcu.regs ht.rd ht.wr ht.sp ?_ ht.mem
    intro r hpres _
    apply ht.regs
    intro hm
    obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
    exact hregs p hp (heq ▸ hpres)
  have hf : Frame [⟨State.addr E, 4 * stack.length⟩] s.mem t.mem := by
    rw [ht.mem]
    simpa only [Nat.mul_zero, BitVec.add_zero] using hu.frame
  refine ⟨hct, hf, ?_, ?_, ?_⟩
  · intro p hp
    rw [hvals p hp, value_frame hE hu.step.frame (hv p hp)]
  · intro j hj
    have hsp : t.sp = E := ht.sp.trans (hu.step.sp.trans hc.sp)
    have ha : State.addr (E + BitVec.ofNat 32 (4 * j)) = State.addr E + BitVec.ofNat 64 (4 * j) :=
      addr_add (by omega)
    simp only [stackArg, stackArgAddr, hsp, ha, ht.mem]
    simpa only [Nat.zero_add] using hu.words j hj
  · intro r ha h0 h12
    exact (ht.regs r ha).trans (hu.step.regs r h0 h12)

end VG.Proof.Ed448.Arm.Shake
