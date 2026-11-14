module

public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Ed448.Contract

/-! ### `Ed448.Arm.Shake.Setup`, which only this module used -/

section

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

@[expose] public section

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
    have ha : 248 + 4 * j < 4096 := by omega_using [hj']
    have he' : State.addr (E + BitVec.ofNat 32 (248 + 4 * j)) =
        State.addr E + BitVec.ofNat 64 (248 + 4 * j) := addr_add (by omega)
    have enc : encodable (BitVec.ofNat 32 d) = true := by
      apply List.any_eq_true.mpr
      refine ⟨0, by decide, ?_⟩
      simp only [Nat.mul_zero, BitVec.rotateLeft, BitVec.rotateLeftAux, Nat.zero_mod, Nat.sub_zero,
        BitVec.shiftLeft_zero, BitVec.ushiftRight_eq_zero (Nat.le_refl 32), BitVec.or_zero,
        BitVec.toNat_ofNat, decide_eq_true_eq]
      omega_using [hd]
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
    exact Offset.disjoint_base _ (d := 248 + 4 * j) (by omega_using []) (by omega)

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
  have hoff : 4 * j < 256 := by omega_using [hj]
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
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))

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
    have hj : start < 6 := by simp only [List.length_cons] at hs; omega_using [hs]
    refine WP.mono (putArg_ok he hE hj (hv v List.mem_cons_self) hr (hw start hj)) fun u ⟨hu, hmem⟩ => ?_
    refine WP.mono (ih (hu.sp.trans he) (by simp only [List.length_cons] at hs; omega_using [hs])
      (fun v hv' => hv v (List.mem_cons_of_mem _ hv'))
      (by intro j hj; rw [hu.rd, hu.wr]; exact hr j hj)
      (by intro j hj; rw [hu.wr]; exact hw j hj)) fun t ht => ?_
    refine ⟨hu.trans ht.step, ?_, ?_⟩
    · have first : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * (v :: vs).length⟩] s.mem u.mem := by
        rw [hmem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_cons]; omega_using [])
      refine first.trans (Frame.sub ht.frame ?_)
      intro r hr
      rw [List.mem_singleton.mp hr]
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      exact Offset.sub _ (by omega_using []) (by simp only [List.length_cons]; omega_using [])
    · intro j hj'
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        rw [ht.frame.readW (r := ⟨State.addr E + BitVec.ofNat 64 (4 * start), 4⟩)
          (Region.contains_self _ _) (by
            intro r hr
            rw [List.mem_singleton.mp hr]
            exact Offset.disjoint _ (by omega_using []) (by omega_using [hs]) (by simp only [List.length_cons] at hs; omega_using [hs])) (by decide)]
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
    exact hc.writable_frame (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
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

end

end


/-!
# Ed448 on ARMv7: what a complete operation's calls need of its layout

A complete operation runs in Ed25519's frame on this target
(`Proof/Ed25519/Arm/Whole`): `Whole.Ctx E g m₀ ins outs` holds between the
frame's entry and its exit, `E` the frame's base, `ins` the regions it reads
(its inputs, the saved arguments and the caller's stack arguments) and
`outs` those it may write besides the frame. `Kit` is what the calls need of
them: the saved words below `n` (`Slot n`) in the inputs, `scratch` an
output outside the stack, and the inputs outside everything written. `Args`
gives the saved words' values (`val`), and `setup_ok` sets a call's
arguments from them.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.value Whole.Within)

abbrev STK (E : BitVec 32) : Region := ⟨State.addr E, 280⟩
abbrev SCR (scr : BitVec 32) : Region := ⟨State.addr scr, 8192⟩

structure Kit (E scr : BitVec 32) (n : Nat) (ins outs : List Region) : Prop where
  fits : Fits E n
  nc : scr.toNat + 8192 ≤ 2 ^ 32
  so : SCR scr ∈ outs
  kc : (STK E).Disjoint (SCR scr)
  io : ∀ r ∈ ins, ∀ R ∈ outs ++ [Whole.FR E], r.Disjoint R
  slot : ∀ j, Slot n j → ∃ R ∈ ins, R.Contains (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4

/-- The saved words, and the caller's stack arguments, below `n`. -/
def Args (E : BitVec 32) (n : Nat) (val : Nat → BitVec 32) (m : Mem) : Prop :=
  ∀ j, Slot n j → m.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 = val j

def argVal (E : BitVec 32) (val : Nat → BitVec 32) : Value → BitVec 32
  | .const k => BitVec.ofNat 32 k
  | .frame d => E + BitVec.ofNat 32 d
  | .caller j d => val j + BitVec.ofNat 32 d

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

theorem top : E.toNat + 272 ≤ 2 ^ 32 := by have := hk.fits; omega

theorem frame_addr {d : Nat} (hd : d < 272) :
    State.addr (E + BitVec.ofNat 32 d) = State.addr E + BitVec.ofNat 64 d :=
  addr_add (by have := hk.top; omega_using [hd, this])

theorem frame_fit {d k : Nat} (hd : d + k ≤ 248) : (E + BitVec.ofNat 32 d).toNat + k ≤ 2 ^ 32 := by
  have ht := hk.top
  rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd])]; omega_using [hd, ht]),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hd])]
  omega_using [hd, ht]

/-- A region of the frame, and the stack, are outside `scratch`. -/
theorem stack_scr {d k : Nat} (hd : d + k ≤ 280) :
    (⟨State.addr E + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (SCR scr) :=
  hk.kc.sub_left (Offset.sub_base _ hd)

/-- The inputs, as they were. -/
theorem input_bytes (hc : Whole.Ctx E g m₀ ins outs t) {r : Region} (hr : r ∈ ins)
    {D : Region} (hw : Whole.Within D r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem D.base D.len = Spec.Ed448.bytesAt m₀ D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := D) (fun R hR => (hk.io r hr R hR).sub_left hw.sub) hn (List.mem_range.mp hi)

theorem arg_word (hc : Whole.Ctx E g m₀ ins outs t) {j : Nat} (hj : Slot n j) :
    t.mem.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  obtain ⟨R, hR, hcon⟩ := hk.slot j hj
  exact hc.frame.readW (r := R) hcon (hk.io R hR) (by decide)

theorem value_eq (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {v : Value} (hv : valid n v) : Whole.value E t.mem v = argVal E val v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, argVal]
    rw [hk.arg_word hc hv.1, ha j hv.1]

/-- A call's arguments set up: the set-up writes only the words of its stack
arguments, from `E`. -/
theorem setup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid n v) :
    WP isa (.block (setup args stk)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨State.addr E, 4 * stk.length⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = argVal E val p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = argVal E val (stk[j]'hj)) ∧
      (∀ r, r ∉ args.map Prod.fst → r ≠ .r0 → r ≠ .r12 → u.gpr r = t.gpr r) := by
  refine WP.mono (Ctx.setup hc hk.fits hn hv hs hvs
    (fun j hj => let ⟨R, hR, hcon⟩ := hk.slot j hj; ⟨R, hR, hcon⟩) hr)
    fun u ⟨hu, hm, hregs, hstk, hk'⟩ => ⟨hu, hm, ?_, ?_, hk'⟩
  · intro p hp
    rw [hregs p hp, hk.value_eq hc ha (hv p hp)]
  · intro j hj
    rw [hstk j hj, hk.value_eq hc ha (hvs _ (List.getElem_mem hj))]

end Kit

/-- Bytes outside the regions a step may write, through it. -/
theorem frame_bytes {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {D : Region}
    (hd : ∀ r ∈ ws, D.Disjoint r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

/-- Bytes outside a set-up's stack arguments, through it. -/
theorem bytes_setup {m m' : Mem} {k : Nat} (hm : Frame [⟨State.addr E, k⟩] m m') {D : Region}
    (hd : (⟨State.addr E, k⟩ : Region).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hm.bytes (R := D) ?_ hn (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact hd.symm

/-- A region of the frame at `d ≥ k`, outside the first `k` bytes. -/
theorem frame_out {k d l : Nat} (hd : k ≤ d) (hl : d + l ≤ 248) :
    (⟨State.addr E, k⟩ : Region).Disjoint ⟨State.addr E + BitVec.ofNat 64 d, l⟩ :=
  Offset.base_disjoint _ hd (by omega_using [hl])

end VG.Proof.Ed448.Arm.Shake
