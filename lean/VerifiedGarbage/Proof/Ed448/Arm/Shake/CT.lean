import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
import VerifiedGarbage.Impl.Ed448.Arm.Shake
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Shake.Setup`. -/
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
  | .caller j d => VG.Proof.Ed448.Arm.Shake.Slot n j ∧ d < 256

/-- The words up to `n` fit below `2^32`, with at least the six saved ones. -/
abbrev Fits (E : BitVec 32) (n : Nat) : Prop := 6 ≤ n ∧ n ≤ 16 ∧ E.toNat + 248 + 4 * n ≤ 2 ^ 32

variable {n : Nat}

theorem setArg_ok {s : VG.Arm.State} {E : BitVec 32} {r : Reg} {v : Value}
    (he : s.sp = E) (hE : VG.Proof.Ed448.Arm.Shake.Fits E n) (hv : VG.Proof.Ed448.Arm.Shake.valid n v)
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

theorem setupRegs_ok {s : VG.Arm.State} {E : BitVec 32} {args : List (Reg × Value)}
    (he : s.sp = E) (hE : VG.Proof.Ed448.Arm.Shake.Fits E n) (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid n p.2)
    (hr : ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4) :
    WP isa (.block (args.flatMap fun (r, v) => setArg r v)) s fun t =>
      Whole.SetupStep (args.map Prod.fst) s t ∧ ∀ p ∈ args, t.gpr p.1 = Whole.value E s.mem p.2 := by
  induction args generalizing s with
  | nil => exact WP.block_nil ⟨Whole.SetupStep.refl s, fun _ h => by cases h⟩
  | cons p ps ih =>
    obtain ⟨r, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [List.flatMap_cons, WP.block_append_iff]
    have hv0 := hv (r, v) List.mem_cons_self
    refine WP.mono (VG.Proof.Ed448.Arm.Shake.setArg_ok he hE hv0 ?_) fun u ⟨hu, hval⟩ => ?_
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
    (hE : VG.Proof.Ed448.Arm.Shake.Fits E n) (hf : Frame [⟨State.addr E, 24⟩] m m') {v : Value} (hv : VG.Proof.Ed448.Arm.Shake.valid n v) :
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

theorem putArg_ok {s : VG.Arm.State} {E : BitVec 32} {j : Nat} {v : Value}
    (he : s.sp = E) (hE : VG.Proof.Ed448.Arm.Shake.Fits E n) (hj : j < 6) (hv : VG.Proof.Ed448.Arm.Shake.valid n v)
    (hr : ∀ i, VG.Proof.Ed448.Arm.Shake.Slot n i → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * i)) 4)
    (hw : InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (putArg j v)) s fun t => Whole.StackStep E s t ∧
      t.mem = s.mem.writeW (State.addr E + BitVec.ofNat 64 (4 * j)) (Whole.value E s.mem v) := by
  rw [putArg, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.Shake.setArg_ok he hE hv ?_) fun u ⟨hu, hval⟩ => ?_
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

structure StackReady (E : BitVec 32) (s : VG.Arm.State) (start : Nat) (vs : List Value) (t : VG.Arm.State) : Prop where
  step : Whole.StackStep E s t
  frame : Frame [⟨State.addr E + BitVec.ofNat 64 (4 * start), 4 * vs.length⟩] s.mem t.mem
  words : ∀ j (hj : j < vs.length),
    t.mem.readW (State.addr E + BitVec.ofNat 64 (4 * (start + j))) 32 = Whole.value E s.mem (vs[j]'hj)

theorem setupStack_ok {E : BitVec 32} (hE : VG.Proof.Ed448.Arm.Shake.Fits E n)
    {s : VG.Arm.State} {start : Nat} {vs : List Value}
    (he : s.sp = E) (hs : start + vs.length ≤ 6)
    (hv : ∀ v ∈ vs, VG.Proof.Ed448.Arm.Shake.valid n v)
    (hr : ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4)
    (hw : ∀ j < 6, InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (setupStack start vs)) s (VG.Proof.Ed448.Arm.Shake.StackReady E s start vs) := by
  induction vs generalizing s start with
  | nil => exact WP.block_nil ⟨.refl _ _, Frame.refl _ _, fun j hj => by simp at hj⟩
  | cons v vs ih =>
    rw [setupStack, WP.block_append_iff]
    have hj : start < 6 := by simp only [List.length_cons] at hs; omega
    refine WP.mono (VG.Proof.Ed448.Arm.Shake.putArg_ok he hE hj (hv v List.mem_cons_self) hr (hw start hj)) fun u ⟨hu, hmem⟩ => ?_
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
        rw [VG.Proof.Ed448.Arm.Shake.value_frame hE hu.frame (hv vs[j] (List.mem_cons_of_mem _ (List.getElem_mem hj)))] at hw'
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using hw'

/-- A call's arguments set up, from a frame whose readable regions hold the
saved words (`hr`). -/
theorem Ctx.setup {E : BitVec 32} {g : Reg → BitVec 32}
    {m₀ : Mem} {rd wr : List Region} {s : VG.Arm.State} (hc : Whole.Ctx E g m₀ rd wr s)
    (hE : VG.Proof.Ed448.Arm.Shake.Fits E n)
    {args : List (Reg × Value)} {stack : List Value}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid n p.2)
    (hs : stack.length ≤ 6) (hvs : ∀ v ∈ stack, VG.Proof.Ed448.Arm.Shake.valid n v)
    (hr : ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → InRegions rd (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4)
    (hregs : ∀ p ∈ args, p.1 ∉ preserved) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stack)) s fun t => Whole.Ctx E g m₀ rd wr t ∧
      Frame [⟨State.addr E, 4 * stack.length⟩] s.mem t.mem ∧
      (∀ p ∈ args, t.gpr p.1 = Whole.value E s.mem p.2) ∧
      (∀ j (hj : j < stack.length), stackArg t j = Whole.value E s.mem (stack[j]'hj)) ∧
      (∀ r, r ∉ args.map Prod.fst → r ≠ .r0 → r ≠ .r12 → t.gpr r = s.gpr r) := by
  have read : ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → InRegions (s.rd ++ s.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    intro j hj
    obtain ⟨R, hR, hcon⟩ := hr j hj
    rw [hc.rd]
    exact ⟨R, List.mem_append_left _ hR, hcon⟩
  have write : ∀ j < 6, InRegions s.wr (State.addr E + BitVec.ofNat 64 (4 * j)) 4 := by
    intro j hj
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  rw [Impl.Ed25519.Arm.Whole.setup, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.Shake.setupStack_ok hE hc.sp (by simpa using hs) hvs read write) fun u hu => ?_
  refine WP.mono (VG.Proof.Ed448.Arm.Shake.setupRegs_ok (hu.step.sp.trans hc.sp) hE hn hv
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
    rw [hvals p hp, VG.Proof.Ed448.Arm.Shake.value_frame hE hu.step.frame (hv p hp)]
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

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Shake.Layout`. -/
section

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

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.value Whole.Within)

abbrev STK (E : BitVec 32) : Region := ⟨State.addr E, 280⟩
abbrev SCR (scr : BitVec 32) : Region := ⟨State.addr scr, 8192⟩

structure Kit (E scr : BitVec 32) (n : Nat) (ins outs : List Region) : Prop where
  fits : VG.Proof.Ed448.Arm.Shake.Fits E n
  nc : scr.toNat + 8192 ≤ 2 ^ 32
  so : VG.Proof.Ed448.Arm.Shake.SCR scr ∈ outs
  kc : (VG.Proof.Ed448.Arm.Shake.STK E).Disjoint (VG.Proof.Ed448.Arm.Shake.SCR scr)
  io : ∀ r ∈ ins, ∀ R ∈ outs ++ [Whole.FR E], r.Disjoint R
  slot : ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → ∃ R ∈ ins, R.Contains (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4

/-- The saved words, and the caller's stack arguments, below `n`. -/
def Args (E : BitVec 32) (n : Nat) (val : Nat → BitVec 32) (m : Mem) : Prop :=
  ∀ j, VG.Proof.Ed448.Arm.Shake.Slot n j → m.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 = val j

def argVal (E : BitVec 32) (val : Nat → BitVec 32) : Value → BitVec 32
  | .const k => BitVec.ofNat 32 k
  | .frame d => E + BitVec.ofNat 32 d
  | .caller j d => val j + BitVec.ofNat 32 d

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

namespace Kit

variable (hk : VG.Proof.Ed448.Arm.Shake.Kit E scr n ins outs)
include hk

theorem top : E.toNat + 272 ≤ 2 ^ 32 := by have := hk.fits; omega

theorem frame_addr {d : Nat} (hd : d < 272) :
    State.addr (E + BitVec.ofNat 32 d) = State.addr E + BitVec.ofNat 64 d :=
  addr_add (by have := hk.top; omega)

theorem frame_fit {d k : Nat} (hd : d + k ≤ 248) : (E + BitVec.ofNat 32 d).toNat + k ≤ 2 ^ 32 := by
  have ht := hk.top
  rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A region of the frame, and the stack, are outside `scratch`. -/
theorem stack_scr {d k : Nat} (hd : d + k ≤ 280) :
    (⟨State.addr E + BitVec.ofNat 64 d, k⟩ : Region).Disjoint (VG.Proof.Ed448.Arm.Shake.SCR scr) :=
  hk.kc.sub_left (Offset.sub_base _ hd)

/-- The inputs, as they were. -/
theorem input_bytes (hc : Whole.Ctx E g m₀ ins outs t) {r : Region} (hr : r ∈ ins)
    {D : Region} (hw : Whole.Within D r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem D.base D.len = Spec.Ed448.bytesAt m₀ D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := D) (fun R hR => (hk.io r hr R hR).sub_left hw.sub) hn (List.mem_range.mp hi)

theorem arg_word (hc : Whole.Ctx E g m₀ ins outs t) {j : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot n j) :
    t.mem.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  obtain ⟨R, hR, hcon⟩ := hk.slot j hj
  exact hc.frame.readW (r := R) hcon (hk.io R hR) (by decide)

theorem value_eq (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀)
    {v : Value} (hv : VG.Proof.Ed448.Arm.Shake.valid n v) : Whole.value E t.mem v = VG.Proof.Ed448.Arm.Shake.argVal E val v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, VG.Proof.Ed448.Arm.Shake.argVal]
    rw [hk.arg_word hc hv.1, ha j hv.1]

/-- A call's arguments set up: the set-up writes only the words of its stack
arguments, from `E`. -/
theorem setup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, VG.Proof.Ed448.Arm.Shake.valid n v) :
    WP isa (.block (VG.Impl.Ed25519.Arm.Whole.setup args stk)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨State.addr E, 4 * stk.length⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed448.Arm.Shake.argVal E val p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = VG.Proof.Ed448.Arm.Shake.argVal E val (stk[j]'hj)) ∧
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
  Offset.base_disjoint _ hd (by omega)

end VG.Proof.Ed448.Arm.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Shake.Sponge`. -/
section

/-!
# Ed448 on ARMv7: the calls of the sponge functions

The Keccak state zeroed (`Kit.zero_ok`), and each call of a sponge function
through `Whole.call_ok` with its own contract (`Proof.Sha3.absorbArm`,
`padArm`, `squeezeArm`), from its set-up (`Kit.first_abs`, `Kit.next_abs`,
`Kit.pad_step`, `Kit.sqz_step`), for any layout (`Kit`) with `scratch` in
the saved word `sc` (`ScrAt`). An absorption reads its data from the frame,
an input or an output (`DataOk`); each after the first starts at the
position the previous one returned in `r0`. Each step states the regions it
may write: the outgoing stack arguments (`kArgs E 8`), the state and the
working space (`kWr scr`), and the squeezed output.
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.X25519.Arm (Upd wp_mov op2_reg)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.Ctx Whole.call_ok)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t u : State}

/-- `scratch` is the saved word `sc`. -/
structure ScrAt (n : Nat) (val : Nat → BitVec 32) (sc : Nat) (scr : BitVec 32) : Prop where
  slot : VG.Proof.Ed448.Arm.Shake.Slot n sc
  val : val sc = scr

/-! ## The regions -/

/-- The state and the sponge functions' working space. -/
def kWr (scr : BitVec 32) : List Region :=
  [⟨State.addr scr, 200⟩, ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩]

/-- The outgoing stack arguments. -/
abbrev kArgs (E : BitVec 32) (k : Nat) : Region := ⟨State.addr E, k⟩

theorem kWr_sub (scr : BitVec 32) : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Whole.Within r (VG.Proof.Ed448.Arm.Shake.SCR scr) := by
  intro r hr
  simp only [VG.Proof.Ed448.Arm.Shake.kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, rfl, by change 208 + 640 ≤ 8192; decide⟩

theorem state_scratch (scr : BitVec 32) : (⟨State.addr scr, 200⟩ : Region).Disjoint
    ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩ := Offset.base_disjoint _ (by decide) (by decide)

/-- Data an absorption may read: in the frame, or in an input or an output. -/
def DataOk (E : BitVec 32) (ins outs : List Region) (D : Region) : Prop :=
  Whole.Within D (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within D R

theorem covers_of {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R) :
    Covers rs (ins ++ Whole.FR E :: outs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with hf | ⟨R, hR, hw⟩
  · exact ⟨Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hw⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem args_within (E : BitVec 32) {k : Nat} (hk : k ≤ 248) : Whole.Within (VG.Proof.Ed448.Arm.Shake.kArgs E k) (Whole.FR E) :=
  ⟨0, (BitVec.add_zero _).symm, by change 0 + k ≤ 248; omega⟩

theorem frame_within (E : BitVec 32) {d k : Nat} (hd : d + k ≤ 248) :
    Whole.Within ⟨State.addr E + BitVec.ofNat 64 d, k⟩ (Whole.FR E) := ⟨d, rfl, hd⟩

/-! ## The state, through a step outside it -/

theorem state_frame {ws : List Region} {m m' : Mem} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨State.addr scr, 200⟩ : Region).Disjoint r) :
    stateAt m' (State.addr scr) = stateAt m (State.addr scr) :=
  Proof.Sha3.stateAt_congr fun _ hj => hm.bytes (R := ⟨State.addr scr, 200⟩) hd
    (by change 200 ≤ 2 ^ 64; decide) hj

theorem repr_frame' {ws : List Region} {m m' : Mem} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨State.addr scr, 200⟩ : Region).Disjoint r) {msg : List Byte}
    (h : Spec.Sha3.Repr m (State.addr scr) 136 msg) : Spec.Sha3.Repr m' (State.addr scr) 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [VG.Proof.Ed448.Arm.Shake.state_frame hm hd]; exact h

/-- An absorption's set-up writes its two stack arguments. -/
theorem args_two (len : Value) (sc : Nat) : 4 * [len, Value.caller sc KSCR].length = 8 := rfl

theorem valid_const {k : Nat} (h : k < 65536) : VG.Proof.Ed448.Arm.Shake.valid n (.const k) := h
theorem valid_frame {d : Nat} (h : d < 256) : VG.Proof.Ed448.Arm.Shake.valid n (.frame d) := h

theorem ScrAt.valid {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) {d : Nat} (hd : d < 256) : VG.Proof.Ed448.Arm.Shake.valid n (.caller sc d) :=
  ⟨hsc.slot, hd⟩

/-- What an absorption reads, and what a squeeze writes. -/
def absRd (E : BitVec 32) (D : Region) : List Region := [D, VG.Proof.Ed448.Arm.Shake.kArgs E 8]

def sqzWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨State.addr scr, 200⟩, ⟨State.addr E + BitVec.ofNat 64 d, 114⟩,
    ⟨State.addr scr + BitVec.ofNat 64 KSCR, 640⟩]

namespace Kit

variable (hk : VG.Proof.Ed448.Arm.Shake.Kit E scr n ins outs)
include hk

theorem scr_addr : State.addr (scr + BitVec.ofNat 32 KSCR) = State.addr scr + BitVec.ofNat 64 KSCR :=
  addr_add (by have := hk.nc; simp only [KSCR]; omega)

theorem scr_fit : (scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hk.nc
  rw [BitVec.toNat_add_of_lt (by change scr.toNat + 208 < 2 ^ 32; omega)]
  change scr.toNat + 208 + 640 ≤ 2 ^ 32
  omega

theorem kWr_writes : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R :=
  fun r hr => .inr ⟨VG.Proof.Ed448.Arm.Shake.SCR scr, hk.so, VG.Proof.Ed448.Arm.Shake.kWr_sub scr r hr⟩

theorem kWr_covered : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, ∃ R ∈ ins ++ outs, Whole.Within r R :=
  fun r hr => ⟨VG.Proof.Ed448.Arm.Shake.SCR scr, List.mem_append_right _ hk.so, VG.Proof.Ed448.Arm.Shake.kWr_sub scr r hr⟩

theorem args_scr {k : Nat} (hk' : k ≤ 280) : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, (VG.Proof.Ed448.Arm.Shake.kArgs E k).Disjoint r :=
  fun r hr => (hk.kc.sub_left (Region.sub_prefix hk')).sub_right (VG.Proof.Ed448.Arm.Shake.kWr_sub scr r hr).sub

/-- A region of the frame is outside the state and the working space. -/
theorem frame_kWr {d l : Nat} (hd : d + l ≤ 280) :
    ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr E + BitVec.ofNat 64 d, l⟩ r :=
  fun r hr => (hk.stack_scr hd).sub_right (VG.Proof.Ed448.Arm.Shake.kWr_sub scr r hr).sub

/-- Data in an input is outside the state, the working space and the
outgoing stack arguments. -/
theorem data_input {D R : Region} (hR : R ∈ ins) (hw : Whole.Within D R) :
    (∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, D.Disjoint r) ∧ (VG.Proof.Ed448.Arm.Shake.kArgs E 8).Disjoint D := by
  have ho := hk.io R hR
  refine ⟨fun r hr => ((ho (VG.Proof.Ed448.Arm.Shake.SCR scr) (List.mem_append_left _ hk.so)).sub_left hw.sub).sub_right
    (VG.Proof.Ed448.Arm.Shake.kWr_sub scr r hr).sub, ?_⟩
  exact ((ho (Whole.FR E) (by simp)).sub_left hw.sub).symm.sub_left (Region.sub_prefix (by decide))

/-- The state is outside the frame's first `k` bytes. -/
theorem state_args {k : Nat} (hk' : k ≤ 280) : ∀ r ∈ [VG.Proof.Ed448.Arm.Shake.kArgs E k], (⟨State.addr scr, 200⟩ : Region).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (hk.args_scr hk' _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr])).symm

/-! ## The state, zeroed -/

theorem zeroStores_step (hu : Whole.Ctx E g m₀ ins outs t) (h0 : t.gpr .r0 = scr) (h1 : t.gpr .r1 = 0) :
    WP isa (.block Impl.Ed448.Arm.PublicKey.zeroStores) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      stateAt v.mem (State.addr scr) = Spec.Sha3.zero ∧ Frame [⟨State.addr scr, 200⟩] t.mem v.mem := by
  have hw : ∀ k < 50, InRegions t.wr (State.addr (t.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk'
    rw [hu.wr, h0]; exact ⟨VG.Proof.Ed448.Arm.Shake.SCR scr, List.mem_cons_of_mem _ hk.so, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (PublicKey.zeroStores_ok h1 (by rw [h0]; have := hk.nc; omega) hw) fun v hv => ⟨?_, ?_, ?_⟩
  · refine hu.of_frame hv.rd hv.wr hv.sp (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
    intro r hr
    rw [List.mem_singleton.mp hr, h0]
    exact .inr ⟨VG.Proof.Ed448.Arm.Shake.SCR scr, hk.so, Region.sub_prefix (by decide)⟩
  · have := hv.zero
    rw [h0] at this
    exact PublicKey.stateAt_zero this
  · have f2 := hv.frame
    rw [h0] at f2
    exact f2

theorem zero_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hs : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) :
    WP isa (zeroState sc) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (State.addr scr) = Spec.Sha3.zero ∧ Frame [⟨State.addr scr, 200⟩] t.mem u.mem := by
  unfold zeroState zeroArgs
  refine WP.seq (WP.mono (hk.setup_ok hc ha (args := [(.r0, .caller sc 0), (.r1, .const 0)]) (stk := [])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hs.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hv, _⟩ => ?_)
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 0) (by simp)
  simp only [VG.Proof.Ed448.Arm.Shake.argVal, hs.val, BitVec.add_zero] at h0 h1
  refine WP.mono (hk.zeroStores_step hu h0 h1) fun v ⟨hv, hz, f2⟩ => ⟨hv, hz, ?_⟩
  refine (Frame.sub hm fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans f2
  rw [List.mem_singleton.mp hr]
  intro x hx
  simp only [Region.Contains, List.length_nil, Nat.mul_zero] at hx
  omega

/-! ## `absorb` -/

theorem abs_pre {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr P, N.toNat⟩ r) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (he : t.sp = E) (h0 : t.gpr .r0 = scr) (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : t.gpr .r3 = P) (a0 : stackArg t 0 = N) (a1 : stackArg t 1 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbArm.pre (t.callEntry.withRegions (VG.Proof.Ed448.Arm.Shake.absRd E ⟨State.addr P, N.toNat⟩) (VG.Proof.Ed448.Arm.Shake.kWr scr)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (VG.Proof.Ed448.Arm.Shake.absRd E ⟨State.addr P, N.toNat⟩) (VG.Proof.Ed448.Arm.Shake.kWr scr)) j =
      stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (VG.Proof.Ed448.Arm.Shake.absRd E ⟨State.addr P, N.toNat⟩) (VG.Proof.Ed448.Arm.Shake.kWr scr)) 0 =
      State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.absorbArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, hk.scr_addr]
  have wa := hk.args_scr (k := 8) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, VG.Proof.Ed448.Arm.Shake.state_scratch scr, hs _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]), hs _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]),
    wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]), wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]), by have := hk.nc; omega, hfit, hk.scr_fit,
    by have := hk.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem abs_covers {D : Region} (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs D) :
    Covers (VG.Proof.Ed448.Arm.Shake.absRd E D ++ VG.Proof.Ed448.Arm.Shake.kWr scr) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.Arm.Shake.covers_of fun r hr => ?_
  simp only [VG.Proof.Ed448.Arm.Shake.absRd, List.cons_append, List.nil_append, List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · exact hcov
  · exact .inl (VG.Proof.Ed448.Arm.Shake.args_within E (by decide))
  · exact .inr (hk.kWr_covered r hr)

theorem absorb_call (hc : Whole.Ctx E g m₀ ins outs u) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr P, N.toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr P, N.toNat⟩ r) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : u.gpr .r0 = scr) (h1 : u.gpr .r1 = 136) (h2 : u.gpr .r2 = BitVec.ofNat 32 pos)
    (h3 : u.gpr .r3 = P) (a0 : stackArg u 0 = N) (a1 : stackArg u 1 = scr + BitVec.ofNat 32 KSCR) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb) u fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.Arm.Shake.kWr scr) u.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr u.mem (State.addr scr) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (State.addr scr) 136 (msg ++ Spec.Ed448.bytesAt u.mem (State.addr P) N.toNat)) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((pos + N.toNat) % 136) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 PublicKey.absorb_noFrames
    (hk.abs_pre hp hs hfit hc.sp h0 h1 h2 h3 a0 a1) (hk.abs_covers hcov) hk.kWr_writes
    fun v hv hf hpost => ⟨hv, hf, ?_, ?_⟩
  · have hp1 := hpost.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      stackArg_withRegions] at hp1
    rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hpn] at hp1
    exact hp1
  · have hp2 := hpost.2
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), stackArg_withRegions] at hp2
    rw [h1, h2, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hpn] at hp2
    apply BitVec.eq_of_toNat_eq
    rw [hp2, show BitVec.toNat (136 : BitVec 32) = 136 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (pos + N.toNat) % 136) (b := 2 ^ 32)
        (by have := Nat.mod_lt (pos + N.toNat) (by decide : 136 > 0); omega)]

/-- The first absorption, from position 0 of an empty state. -/
theorem first_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩ r)
    (h8 : (VG.Proof.Ed448.Arm.Shake.kArgs E 8).Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hfit : (VG.Proof.Ed448.Arm.Shake.argVal E val src).toNat + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136
        (Spec.Ed448.bytesAt t.mem (State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src)) (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat % 136) := by
  unfold absorb firstArgs callWith
  refine WP.seq (WP.mono (hk.setup_ok hc ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, src)])
    (stk := [len, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), vs, fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, _⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.Shake.args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h2 := hv (.r2, .const 0) (by simp)
  have h3 := hv (.r3, src) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 a1
  simp only [List.getElem_cons_zero] at a0
  have hbytes := VG.Proof.Ed448.Arm.Shake.bytes_setup hm h8 (by change (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 64; have := (VG.Proof.Ed448.Arm.Shake.argVal E val len).isLt; omega)
  refine WP.mono (hk.absorb_call hu (pos := 0) (by decide) hcov hs hfit h0 h1 h2 h3 a0 a1)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, ?_, ?_, by rw [h0v, Nat.zero_add]⟩
  · exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hrv := hrv [] (VG.Proof.Ed448.Arm.Shake.repr_frame' hm (hk.state_args (by decide)) hr) rfl
    simp only at hbytes
    rw [List.nil_append, hbytes] at hrv
    exact hrv

/-- An absorption at the position the previous one returned. -/
theorem next_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩ r)
    (h8 : (VG.Proof.Ed448.Arm.Shake.kArgs E 8).Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hfit : (VG.Proof.Ed448.Arm.Shake.argVal E val src).toNat + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136
        (msg ++ Spec.Ed448.bytesAt t.mem (State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src)) (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg.length + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat) % 136) := by
  unfold absorb nextArgs callWith
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Whole.Ctx E g m₀ ins outs s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (hk.setup_ok hc1 ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r3, src)]) (stk := [len, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), vs, fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, hk'⟩ => ?_
  rw [VG.Proof.Ed448.Arm.Shake.args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h3 := hv (.r3, src) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 a1
  simp only [List.getElem_cons_zero] at a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk' .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  have hrd : Spec.Sha3.Repr u.mem (State.addr scr) 136 msg := VG.Proof.Ed448.Arm.Shake.repr_frame' hm (hk.state_args (by decide)) (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  have hbytes := VG.Proof.Ed448.Arm.Shake.bytes_setup hm h8 (by change (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 64; have := (VG.Proof.Ed448.Arm.Shake.argVal E val len).isLt; omega)
  refine WP.mono (hk.absorb_call hu (Nat.mod_lt _ (by decide)) hcov hs hfit h0 h1 h2 h3 a0 a1)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, ?_, ?_, ?_⟩
  · rw [v1.mem] at hm
    exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hrv := hrv msg hrd rfl
    simp only at hbytes
    rw [hbytes, v1.mem] at hrv
    exact hrv
  · rw [h0v, Nat.mod_add_mod]

/-- The first absorption, of `N` bytes at `P`. -/
theorem firstAt (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.Arm.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr P, N⟩) (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr P, N⟩ r)
    (h8 : (VG.Proof.Ed448.Arm.Shake.kArgs E 8).Disjoint ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136 (Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 (N % 136) := by
  have h := hk.first_abs hc ha hsc vs vl (by rw [hP, hN]; exact hcov) (by rw [hP, hN]; exact hs)
    (by rw [hP, hN]; exact h8) (by rw [hP, hN]; exact hfit) hr
  rw [hP, hN] at h
  exact h

/-- An absorption of `N` bytes at `P`, at the position the previous one returned. -/
theorem nextAt (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.Arm.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr P, N⟩) (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr P, N⟩ r)
    (h8 : (VG.Proof.Ed448.Arm.Shake.kArgs E 8).Disjoint ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr scr) 136 (msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N).length % 136) := by
  have h := hk.next_abs hc ha hsc vs vl (by rw [hP, hN]; exact hcov) (by rw [hP, hN]; exact hs)
    (by rw [hP, hN]; exact h8) (by rw [hP, hN]; exact hfit) hr hpos
  rw [hP, hN] at h
  refine WP.mono h fun v ⟨hv, hf, hrv, h0⟩ => ⟨hv, hf, hrv, ?_⟩
  rw [h0]
  simp [Spec.Ed448.bytesAt]

/-! ## `pad` -/

theorem pad_pre {pos : Nat} (hp : pos < 136) (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = BitVec.ofNat 32 pos) (a0 : stackArg t 0 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.padArm.pre (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 4] (VG.Proof.Ed448.Arm.Shake.kWr scr)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 4] (VG.Proof.Ed448.Arm.Shake.kWr scr)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 4] (VG.Proof.Ed448.Arm.Shake.kWr scr)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.padArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, a0, he, hk.scr_addr]
  have wa := hk.args_scr (k := 4) (by decide)
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨rfl, rfl, VG.Proof.Ed448.Arm.Shake.state_scratch scr, wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]), wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]),
    by have := hk.nc; omega, hk.scr_fit, by have := hk.top; omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem pad_covers : Covers ([VG.Proof.Ed448.Arm.Shake.kArgs E 4] ++ VG.Proof.Ed448.Arm.Shake.kWr scr) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.Arm.Shake.covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.Arm.Shake.args_within E (by decide))
  · exact .inr (hk.kWr_covered r hr)

theorem pad_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (pad sc) t fun v => Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.kWr scr) t.mem v.mem ∧
      stateAt v.mem (State.addr scr) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold pad callWith padArgs
  refine WP.seq ?_
  refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
  have hc1 : Whole.Ctx E g m₀ ins outs s1 := hc.regs v1.rd v1.wr v1.sp
    (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
  refine WP.mono (hk.setup_ok hc1 ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)]) (stk := [.caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), fun _ h => nomatch h⟩) (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, hk'⟩ => ?_
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h3 := hv (.r3, .const 0x1f) (by simp)
  have a0 := st 0 (by simp)
  simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, List.getElem_cons_zero, BitVec.add_zero] at h0 h1 h3 a0
  have h2 : u.gpr .r2 = BitVec.ofNat 32 (msg.length % 136) := by
    rw [hk' .r2 (by simp) (by decide) (by decide), v1.gpr, hpos]
  have hrd : Spec.Sha3.Repr u.mem (State.addr scr) 136 msg := VG.Proof.Ed448.Arm.Shake.repr_frame' hm (hk.state_args (by simp)) (by
    unfold Spec.Sha3.Repr at hr ⊢; rw [v1.mem]; exact hr)
  have hpn : (BitVec.ofNat 32 (msg.length % 136)).toNat = msg.length % 136 := by
    rw [BitVec.toNat_ofNat]; have := Nat.mod_lt msg.length (by decide : 136 > 0); omega
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
    (hk.pad_pre (Nat.mod_lt _ (by decide)) hu.sp h0 h1 h2 a0) hk.pad_covers hk.kWr_writes
    fun v hv hf hp => ⟨hv, ?_, ?_⟩
  · rw [v1.mem] at hm
    refine (Frame.sub hm fun r hr => ⟨VG.Proof.Ed448.Arm.Shake.kArgs E 8, List.mem_cons_self, ?_⟩).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    rw [List.mem_singleton.mp hr]
    exact Region.sub_prefix (by simp)
  · simp only [Proof.Sha3.padArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs)] at hp
    rw [h0, h1, h2, h3, hpn] at hp
    exact hp msg hrd rfl

/-! ## `squeeze` -/

theorem sqz_pre {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (h1 : t.gpr .r1 = 136) (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = E + BitVec.ofNat 32 d)
    (a0 : stackArg t 0 = 114) (a1 : stackArg t 1 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.squeezeArm.pre (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 8] (VG.Proof.Ed448.Arm.Shake.sqzWr E scr d)) := by
  have sa (j : Nat) : stackArg (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 8] (VG.Proof.Ed448.Arm.Shake.sqzWr E scr d)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Shake.kArgs E 8] (VG.Proof.Ed448.Arm.Shake.sqzWr E scr d)) 0 = State.addr t.sp := by
    simp [stackArgAddr, State.withRegions_sp, State.callEntry_sp]
  simp only [Proof.Sha3.squeezeArm, sa, spa, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), State.withRegions_sp, State.callEntry_sp]
  rw [h0, h1, h2, h3, a0, a1, he, hk.scr_addr, hk.frame_addr (by omega)]
  have wa := hk.args_scr (k := 8) (by decide)
  have so := hk.frame_kWr (d := d) (l := 114) (by omega)
  have ht := hk.top
  refine ⟨rfl, rfl, (so _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr])).symm, VG.Proof.Ed448.Arm.Shake.state_scratch scr, so _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]),
    wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]), Offset.base_disjoint _ h8 (by omega), wa _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr]),
    by have := hk.nc; omega, hk.frame_fit hd, hk.scr_fit, by omega, by decide, by decide⟩

theorem sqz_writes {d : Nat} (hd : d + 114 ≤ 248) :
    ∀ r ∈ VG.Proof.Ed448.Arm.Shake.sqzWr E scr d, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  simp only [VG.Proof.Ed448.Arm.Shake.sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.kWr_writes _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr])
  · exact .inl (VG.Proof.Ed448.Arm.Shake.frame_within E hd)
  · exact hk.kWr_writes _ (by simp [VG.Proof.Ed448.Arm.Shake.kWr])

theorem sqz_covers {d : Nat} (hd : d + 114 ≤ 248) :
    Covers ([VG.Proof.Ed448.Arm.Shake.kArgs E 8] ++ VG.Proof.Ed448.Arm.Shake.sqzWr E scr d) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.Arm.Shake.covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.Arm.Shake.args_within E (by decide))
  · rcases hk.sqz_writes hd r hr with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, h⟩

theorem sqz_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    WP isa (squeeze sc d) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.Arm.Shake.kArgs E 8 :: VG.Proof.Ed448.Arm.Shake.sqzWr E scr d) t.mem v.mem ∧
      Spec.Ed448.bytesAt v.mem (State.addr E + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (State.addr scr)) 0 114 := by
  unfold squeeze callWith sqzArgs
  refine WP.seq (WP.mono (hk.setup_ok hc ha
    (args := [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame d)])
    (stk := [.const 114, .caller sc KSCR])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_frame (by omega), fun _ h => nomatch h⟩) (by simp [preserved])
    (by simp) (by simp only [List.forall_mem_cons]; exact ⟨VG.Proof.Ed448.Arm.Shake.valid_const (by decide), hsc.valid (by decide), fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hv, st, _⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.Shake.args_two] at hm
  have h0 := hv (.r0, .caller sc 0) (by simp)
  have h1 := hv (.r1, .const 136) (by simp)
  have h2 := hv (.r2, .const 0) (by simp)
  have h3 := hv (.r3, .frame d) (by simp)
  have a0 := st 0 (by simp)
  have a1 := st 1 (by simp)
  simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at h0 h1 h2 h3 a0 a1
  refine Whole.call_ok hu Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
    (hk.sqz_pre h8 hd hu.sp h0 h1 h2 h3 a0 a1) (hk.sqz_covers hd) (hk.sqz_writes hd)
    fun v hv hf hp => ⟨hv, ?_, ?_⟩
  · exact (hm.mono fun r hr => by simp at hr ⊢; exact .inl hr).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  · have hp1 := hp.1
    simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      stackArg_withRegions] at hp1
    rw [h0, h1, h2, h3, show stackArg u.callEntry 0 = stackArg u 0 from rfl, a0, hk.frame_addr (by omega),
      VG.Proof.Ed448.Arm.Shake.state_frame hm (hk.state_args (by decide))] at hp1
    exact hp1

end Kit

end VG.Proof.Ed448.Arm.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Shake.Header`. -/
section

/-!
# Ed448 on ARMv7: the header of `dom4`

`Kit.hdr_ok`: the block `hdrAt j off` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the
first ten bytes of `dom4(0, context)`, in the frame at `off`, `ctxlen` the
saved word `j` (`hdr_bytes`: three little-endian words, the last
`ctxlen · 2^8`), and writes nothing else.
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.X25519.Arm (Upd wp_mov wp_movw wp_str op2_lsl)
open VG.Proof.Ed25519.Arm (Whole.FR Whole.Ctx)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_addSp {d : Reg} {n : Nat} (hn : n < 256)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' d (s.sp + BitVec.ofNat 32 n) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d n :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (by simp only [exec, hn, ite_true]) (k _ (Upd.setReg _ _ _))

theorem wp_ldrSp {r : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.X25519.Arm.Upd s s' r (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp r off :: is)) s Q := by
  subst ha
  exact VG.Proof.X25519.Arm.WP.cons (s' := s.setReg r (s.mem.readW _ 32))
    (by simp only [exec, ho, ite_true, State.load32, hin, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (c : BitVec 32) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat]

theorem bytes4 (m : Mem) (p : Addr) : Spec.Ed448.bytesAt m p 4 = Proof.X25519.leBytes 4 (m.readW p 32).toNat := by
  rw [Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_leBytes]; simp [Mem.readW]

/-- The bytes of the three words of the header. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c : BitVec 32) (hc : c.toNat < 256) :
    Spec.Ed448.bytesAt (((m.writeW (p + BitVec.ofNat 64 8) (c <<< 8)).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32) p 10 =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat] := by
  generalize hM : ((m.writeW (p + BitVec.ofNat 64 8) (c <<< 8)).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32 = M
  have s84 : Mem.Sep (p + BitVec.ofNat 64 8) 4 (p + BitVec.ofNat 64 4) 4 := Offset.sep p (by omega) (by omega) (by omega)
  have s80 : Mem.Sep (p + BitVec.ofNat 64 8) 4 p 4 := by
    have := Offset.sep p (d := 8) (n := 4) (e := 0) (k := 4) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have s04 : Mem.Sep p 4 (p + BitVec.ofNat 64 4) 4 := by
    have := Offset.sep p (d := 0) (n := 4) (e := 4) (k := 4) (by omega) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have h0 : M.readW p 32 = 0x45676953#32 := by
    rw [← hM, Mem.readW_writeW_sep s04 (by decide), Mem.readW_writeW_self32]
  have h1 : M.readW (p + BitVec.ofNat 64 4) 32 = 0x38343464#32 := by
    rw [← hM, Mem.readW_writeW_self32]
  have h2 : M.readW (p + BitVec.ofNat 64 8) 32 = c <<< 8 := by
    rw [← hM, Mem.readW_writeW_sep s84 (by decide), Mem.readW_writeW_sep s80 (by decide),
      Mem.readW_writeW_self32]
  have hw : (c <<< 8).toNat = c.toNat * 256 := by
    rw [VG.Proof.X25519.Arm.toNat_shl]; omega
  have e10 : Spec.Ed448.bytesAt M p 10 = Spec.Ed448.bytesAt M p 4 ++
      (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 4) 4 ++ (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 8) 4).take 2) := by
    have a := Proof.X25519.bytesAt_add M p 4 6
    have b := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 4) 4 2
    have b' := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 8) 2 2
    have l := Proof.X25519.length_bytesAt M (p + BitVec.ofNat 64 8) 2
    rw [Offset.add_add] at b b'
    simp only [Proof.Ed448.bytesAt_eq]
    rw [a, show (6 : Nat) = 4 + 2 from rfl, b, show (4 : Nat) = 2 + 2 from rfl, b', List.take_left' l]
  rw [e10, VG.Proof.Ed448.Arm.Shake.bytes4, VG.Proof.Ed448.Arm.Shake.bytes4, VG.Proof.Ed448.Arm.Shake.bytes4, h0, h1, h2, hw]
  have e1 : Proof.X25519.leBytes 4 (0x45676953#32).toNat ++ Proof.X25519.leBytes 4 (0x38343464#32).toNat =
      "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) := by decide
  rw [← List.append_assoc, e1]
  refine congrArg (List.append _) ?_
  simp only [Proof.X25519.leBytes_succ, List.take_succ_cons, List.take_zero]
  have e2 : BitVec.ofNat 8 (c.toNat * 256) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, show (0 : BitVec 8).toNat = 0 from rfl]; omega
  have e3 : c.toNat * 256 / 256 = c.toNat := by omega
  rw [e2, e3]
  rfl

theorem hdr_len (c : BitVec 32) : (VG.Proof.Ed448.Arm.Shake.hdrBytes c).length = 10 := by simp [VG.Proof.Ed448.Arm.Shake.hdrBytes]

/-- The input of a hash, as the specification puts it together. -/
theorem dom4_eq (c : BitVec 32) (ctx x : List Byte) (hc : ctx.length = c.toNat) :
    Spec.Ed448.dom4 0 ctx ++ x = VG.Proof.Ed448.Arm.Shake.hdrBytes c ++ ctx ++ x := by
  simp [Spec.Ed448.dom4, VG.Proof.Ed448.Arm.Shake.hdrBytes, hc]

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.hdr_ok (hk : VG.Proof.Ed448.Arm.Shake.Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₀)
    {j off : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot n j) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 248) :
    WP isa (.block (hdrAt j off)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨State.addr E + BitVec.ofNat 64 off, 12⟩] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr E + BitVec.ofNat 64 off) 10 = VG.Proof.Ed448.Arm.Shake.hdrBytes (val j) := by
  have hsp := hc.sp
  have ht := hk.top
  have hf := hk.fits
  have hjn := hj.1
  have hoff : (BitVec.ofNat 32 off).toNat = off := by rw [BitVec.toNat_ofNat]; omega
  have hEo : (E + BitVec.ofNat 32 off).toNat = E.toNat + off := by
    rw [BitVec.toNat_add_of_lt (by rw [hoff]; omega), hoff]
  have ea : ∀ k ≤ 8, State.addr (E + BitVec.ofNat 32 off + BitVec.ofNat 32 k) =
      State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k hk => by
    rw [addr_add (by rw [hEo]; omega), addr_add (by omega)]
  have hw : ∀ k ≤ 8, InRegions t.wr (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 :=
    fun k hk => by
      rw [Offset.add_add]
      exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have h256 : State.addr (t.sp + BitVec.ofNat 32 (248 + 4 * j)) = State.addr E + BitVec.ofNat 64 (248 + 4 * j) := by
    rw [hsp, addr_add (by omega)]
  obtain ⟨R, hR, hcon⟩ := hk.slot j hj
  have hin : InRegions (t.rd ++ t.wr) (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
    rw [hc.rd]; exact ⟨R, List.mem_append_left _ hR, hcon⟩
  have hv : t.mem.readW (State.addr E + BitVec.ofNat 64 (248 + 4 * j)) 32 = val j := by
    rw [hk.arg_word hc hj, ha j hj]
  have e0 : State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 0 = State.addr E + BitVec.ofNat 64 off :=
    BitVec.add_zero _
  unfold hdrAt
  refine VG.Proof.Ed448.Arm.Shake.wp_ldrSp (by omega) h256 hin fun s1 v1 => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun s2 v2 => ?_
  refine VG.Proof.Ed448.Arm.Shake.wp_addSp (by omega) fun s3 v3 => ?_
  have r12 : ∀ s' : State, s'.gpr .r12 = s3.gpr .r12 → s'.gpr .r12 = E + BitVec.ofNat 32 off := fun s' h => by
    rw [h, v3.gpr, v2.sp, v1.sp, hsp]
  refine VG.Proof.X25519.Arm.wp_str (a := State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 8) (by decide) (by rw [r12 s3 rfl]; exact ea 8 (by omega)) (by rw [v3.wr, v2.wr, v1.wr]; exact hw 8 (by omega))
    fun s4 v4 => ?_
  refine VG.Proof.X25519.Arm.wp_movw fun s5 v5 => ?_
  refine VG.Proof.Ed448.Arm.Shake.wp_movt fun s6 v6 => ?_
  refine VG.Proof.X25519.Arm.wp_str (a := State.addr E + BitVec.ofNat 64 off) (by decide) (by rw [r12 s6 (by rw [v6.other _ (by decide), v5.other _ (by decide), v4.gpr])]; exact (ea 0 (by omega)).trans e0)
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ← e0]; exact hw 0 (by omega)) fun s7 v7 => ?_
  refine VG.Proof.X25519.Arm.wp_movw fun s8 v8 => ?_
  refine VG.Proof.Ed448.Arm.Shake.wp_movt fun s9 v9 => ?_
  refine VG.Proof.X25519.Arm.wp_str (a := State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 4) (by decide) (by
      rw [r12 s9 (by rw [v9.other _ (by decide), v8.other _ (by decide), v7.gpr, v6.other _ (by decide),
        v5.other _ (by decide), v4.gpr])]; exact ea 4 (by omega))
    (by rw [v9.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hw 4 (by omega)) fun u vu => ?_
  apply WP.block_nil
  have w0 : s2.gpr .r0 = val j <<< 8 := by rw [v2.gpr, v1.gpr, hv]
  have w1 : s6.gpr .r0 = 0x45676953#32 := by rw [v6.gpr, v5.gpr]; decide
  have w2 : s9.gpr .r0 = 0x38343464#32 := by rw [v9.gpr, v8.gpr]; decide
  have hm : u.mem = ((t.mem.writeW (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 8) (val j <<< 8)).writeW
      (State.addr E + BitVec.ofNat 64 off) 0x45676953#32).writeW
      (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 4) 0x38343464#32 := by
    rw [vu.mem, v9.mem, v8.mem, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, w2, w1,
      v3.other _ (by decide), w0]
  have hfr : Frame [⟨State.addr E + BitVec.ofNat 64 off, 12⟩] t.mem u.mem := by
    rw [hm]
    have c : ∀ k ≤ 8, (⟨State.addr E + BitVec.ofNat 64 off, 12⟩ : Region).Contains
        (State.addr E + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 := fun k hk =>
      Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 8 (by omega))).writeW
      (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
    have h := c 0 (by omega)
    rw [e0] at h
    exact h
  refine ⟨?_, hfr, by rw [hm]; exact VG.Proof.Ed448.Arm.Shake.hdr_bytes _ _ _ hcl⟩
  refine hc.of_frame (by rw [vu.rd, v9.rd, v8.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd])
    (by rw [vu.wr, v9.wr, v8.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr])
    (by rw [vu.sp, v9.sp, v8.sp, v7.sp, v6.sp, v5.sp, v4.sp, v3.sp, v2.sp, v1.sp]) ?_ hfr ?_
  · intro r hr _
    have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
    rw [vu.gpr, v9.other r h0, v8.other r h0, v7.gpr, v6.other r h0, v5.other r h0, v4.gpr,
      v3.other r h12, v2.other r h0, v1.other r h0]
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by omega))
end VG.Proof.Ed448.Arm.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Shake.CT`. -/
section

/-!
# Ed448 on ARMv7: the calls of the sponge functions in constant time

As Ed25519's complete operations on this target: two runs from the same
pointers, lengths and `sp` set up the same arguments for every call
(`setup_ct`, `next_setup_ct`), each callee is constant time under its own
contract (`call_ct`), and the blocks between the calls address memory only
through `sp`, `r12` and `scratch` (`hdr_ct`, `zero_ct`). The positions the
absorptions return, which the next ones start from, depend only on the
lengths (`absorb_ct`).
-/

namespace VG.Proof.Ed448.Arm.Shake

open VG VG.Arm VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.rel_wp Whole.setup_ct Whole.callEx Whole.CallReady
  Whole.block_cons_ct Whole.block_nil_ct Whole.step_sp_ct Whole.Within Whole.Ctx Whole.call_ok)
open VG.Proof.X25519.Arm (wp_mov op2_reg)

/-! ## Relational frame -/

/-- Both runs in the frame, and `P` of each. -/
abbrev Two (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Whole.Ctx E g₁ m₁ ins outs a ∧ P a) ∧ (Whole.Ctx E g₂ m₂ ins outs b ∧ P b)

/-- A call's arguments, in registers and on the stack. -/
def Slots (E : BitVec 32) (val : Nat → BitVec 32) (args : List (Reg × Value)) (stk : List Value) (s : State) :=
  (∀ p ∈ args, s.gpr p.1 = VG.Proof.Ed448.Arm.Shake.argVal E val p.2) ∧ ∀ j (hj : j < stk.length), stackArg s j = VG.Proof.Ed448.Arm.Shake.argVal E val (stk[j]'hj)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

/-- Instructions that address memory only through `r12`, and leave it alone. -/
theorem r12_ct (is : List Instr) (hd : ∀ i ∈ is, dstOf i ≠ some .r12)
    (ha : ∀ i ∈ is, ∀ a b : State, a.gpr .r12 = b.gpr .r12 → addrs i a = addrs i b) :
    RelCT isa (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) (.block is)
      (fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) := by
  induction is with
  | nil => exact Whole.block_nil_ct
  | cons i is ih =>
    refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ⟨ha i List.mem_cons_self a b hp.2,
      (exec_sp ea).trans (hp.1.trans (exec_sp eb).symm), ?_⟩)
      (ih (fun j hj => hd j (List.mem_cons_of_mem _ hj)) (fun j hj => ha j (List.mem_cons_of_mem _ hj)))
    rw [exec_gpr (hd i List.mem_cons_self) ea, exec_gpr (hd i List.mem_cons_self) eb, hp.2]

def hdrTail : List Instr :=
  [.str .r0 .r12 8, .movw .r0 0x6953, .movt .r0 0x4567, .str .r0 .r12 0,
    .movw .r0 0x3464, .movt .r0 0x3834, .str .r0 .r12 4]

/-- The header's block addresses memory only through `sp` and `r12 = sp + off`. -/
theorem hdr_sp_ct (j off : Nat) (ho : off < 256) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (hdrAt j off)) (fun a b => a.sp = b.sp) := by
  have tail : RelCT isa (fun a b => a.sp = b.sp) (.block (.addSp .r12 off :: VG.Proof.Ed448.Arm.Shake.hdrTail))
      (fun a b => a.sp = b.sp) := by
    refine Whole.block_cons_ct (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12)
      (fun a b a' b' hp ea eb => ?_) ((VG.Proof.Ed448.Arm.Shake.r12_ct VG.Proof.Ed448.Arm.Shake.hdrTail (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
    · simp only [exec, ho, ite_true, Option.some.injEq] at ea eb
      subst a' b'
      exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 off) hp⟩
    · intro i hi a b h
      simp only [VG.Proof.Ed448.Arm.Shake.hdrTail, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]
  exact Whole.step_sp_ct (fun _ _ h => by simp only [addrs, h]) (Whole.step_sp_ct (fun _ _ _ => rfl) tail)

namespace Kit

variable (hk : VG.Proof.Ed448.Arm.Shake.Kit E scr n ins outs)
include hk

theorem setup_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, VG.Proof.Ed448.Arm.Shake.valid n v) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (VG.Impl.Ed25519.Arm.Whole.setup args stk))
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val args stk)) := by
  refine Whole.rel_wp ((Whole.setup_ct args stk).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (hk.setup_ok hc ha hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (hk.setup_ok hc hb hn hv hr hs hvs) fun _ ⟨hc, _, hg, ht, _⟩ => ⟨hc, hg, ht⟩

/-- A set-up after the position the previous call returned is moved into `r2`. -/
theorem next_setup_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) (P : Nat)
    (args : List (Reg × Value)) (stk : List Value)
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid n p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, VG.Proof.Ed448.Arm.Shake.valid n v) (h2 : Reg.r2 ∉ args.map Prod.fst) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P)
      (.block (.mov .r2 (.reg .r0) :: VG.Impl.Ed25519.Arm.Whole.setup args stk))
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val ((.r2, .const P) :: args) stk)) := by
  have side : ∀ (g : Reg → BitVec 32) (m : Mem), VG.Proof.Ed448.Arm.Shake.Args E n val m → ∀ t, Whole.Ctx E g m ins outs t →
      t.gpr .r0 = BitVec.ofNat 32 P → WP isa (.block (.mov .r2 (.reg .r0) :: VG.Impl.Ed25519.Arm.Whole.setup args stk)) t
        fun u => Whole.Ctx E g m ins outs u ∧ VG.Proof.Ed448.Arm.Shake.Slots E val ((.r2, .const P) :: args) stk u := by
    intro g m ha t hc h0
    refine wp_mov (op2_reg _ _) fun s1 v1 => ?_
    have hc1 : Whole.Ctx E g m ins outs s1 := hc.regs v1.rd v1.wr v1.sp
      (fun r hr _ => v1.other r (by rintro rfl; simp [preserved] at hr)) v1.mem
    refine WP.mono (hk.setup_ok hc1 ha hn hv hr hs hvs) fun u ⟨hu, _, hg, ht, hk'⟩ => ⟨hu, ?_, ht⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hk' .r2 h2 (by decide) (by decide), v1.gpr, h0]; rfl
    · exact hg p hp
  refine Whole.rel_wp ((Whole.step_sp_ct (fun _ _ _ => rfl) (Whole.setup_ct args stk)).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, h0⟩; exact side _ _ ha t hc h0
  · intro t ⟨hc, h0⟩; exact side _ _ hb t hc h0

omit hk in
theorem call_ct {args : List (Reg × Value)} {stk : List Value} {k : Contract isa} {c : Prog isa}
    {name : String} {Q : State → Prop}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (ready : ∀ t, t.sp = E → VG.Proof.Ed448.Arm.Shake.Slots E val args stk t → Whole.CallReady k E ins outs t)
    (kp : ∀ (a b : State) ar aw br bw, a.sp = b.sp →
      (∀ p ∈ args, a.callEntry.gpr p.1 = b.callEntry.gpr p.1) →
      (∀ j < stk.length, stackArg a j = stackArg b j) →
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    (hq : ∀ (g : Reg → BitVec 32) (m : Mem) (t : State), Whole.Ctx E g m ins outs t → VG.Proof.Ed448.Arm.Shake.Slots E val args stk t →
      WP isa (.call name c) t fun u => Whole.Ctx E g m ins outs u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val args stk)) (.call name c)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ Q) := by
  refine Whole.rel_wp ?_ ?_ ?_
  · refine (Whole.callEx correct ct fun a b h => ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial)
    let ra := ready a h.1.1.sp h.1.2
    let rb := ready b h.2.1.sp h.2.2
    obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
    obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
    refine ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
      kp a b _ _ _ _ (h.1.1.sp.trans h.2.1.sp.symm) ?_ ?_, ca, wa, cb, wb⟩
    · intro p hp
      rw [State.callEntry_gpr _ (hl p hp), State.callEntry_gpr _ (hl p hp), h.1.2.1 p hp, h.2.2.1 p hp]
    · intro j hj
      exact (h.1.2.2 j hj).trans (h.2.2.2 j hj).symm
  · intro t ⟨hc, hs⟩; exact hq _ _ t hc hs
  · intro t ⟨hc, hs⟩; exact hq _ _ t hc hs

/-! ## The sponge functions -/

/-- An absorption, from arguments that depend only on the layout. -/
theorem absorb_ct {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) {args : List (Reg × Value)} {vpos vsrc vlen : Value}
    {pos : Nat} (hp : pos < 136) (m0 : (.r0, .caller sc 0) ∈ args) (m1 : (.r1, .const 136) ∈ args)
    (m2 : (.r2, vpos) ∈ args) (m3 : (.r3, vsrc) ∈ args) (hl : ∀ p ∈ args, p.1 ∉ linkRegs)
    (epos : VG.Proof.Ed448.Arm.Shake.argVal E val vpos = BitVec.ofNat 32 pos)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val vsrc), (VG.Proof.Ed448.Arm.Shake.argVal E val vlen).toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val vsrc), (VG.Proof.Ed448.Arm.Shake.argVal E val vlen).toNat⟩ r)
    (hfit : (VG.Proof.Ed448.Arm.Shake.argVal E val vsrc).toNat + (VG.Proof.Ed448.Arm.Shake.argVal E val vlen).toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val args [vlen, .caller sc KSCR]))
      (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.Arm.Stream.absorb)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((pos + (VG.Proof.Ed448.Arm.Shake.argVal E val vlen).toNat) % 136)) := by
  have get : ∀ t, VG.Proof.Ed448.Arm.Shake.Slots E val args [vlen, .caller sc KSCR] t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 pos ∧ t.gpr .r3 = VG.Proof.Ed448.Arm.Shake.argVal E val vsrc ∧ stackArg t 0 = VG.Proof.Ed448.Arm.Shake.argVal E val vlen ∧
      stackArg t 1 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    refine ⟨?_, hs.1 _ m1, (hs.1 _ m2).trans epos, hs.1 _ m3, hs.2 0 (by simp), ?_⟩
    · have h := hs.1 _ m0
      simpa only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, BitVec.add_zero] using h
    · have h := hs.2 1 (by simp)
      simpa only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, List.getElem_cons_succ, List.getElem_cons_zero] using h
  apply VG.Proof.Ed448.Arm.Shake.Kit.call_ct Proof.Sha3.Arm.Stream.Absorb.absorb_verified.1 Proof.Sha3.Arm.Stream.Absorb.absorb_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h;
      ⟨VG.Proof.Ed448.Arm.Shake.absRd E ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val vsrc), (VG.Proof.Ed448.Arm.Shake.argVal E val vlen).toNat⟩, VG.Proof.Ed448.Arm.Shake.kWr scr,
        hk.abs_pre hp hs hfit he h0 h1 h2 h3 a0 a1, hk.abs_covers hcov, hk.kWr_writes⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg _ m0, hg _ m1, hg _ m2, hg _ m3, ht 0 (by simp), ht 1 (by simp)⟩
  · exact hl
  · intro g m t hc hsl
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hsl
    exact WP.mono (hk.absorb_call hc hp hcov hs hfit h0 h1 h2 h3 a0 a1) fun _ ⟨hu, _, _, hr⟩ => ⟨hu, hr⟩

def padValues (sc P : Nat) : List (Reg × Value) :=
  [(.r2, .const P), (.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)]

theorem pad_ct {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) {P : Nat} (hp : P < 136) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val (VG.Proof.Ed448.Arm.Shake.Kit.padValues sc P) [.caller sc KSCR]))
      (.call Spec.Sha3.padScratchApi.name Impl.Sha3.Arm.Stream.pad) (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, VG.Proof.Ed448.Arm.Shake.Slots E val (VG.Proof.Ed448.Arm.Shake.Kit.padValues sc P) [.caller sc KSCR] t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = BitVec.ofNat 32 P ∧ stackArg t 0 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, .caller sc 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues])
    have a0 := hs.2 0 (by simp)
    simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, BitVec.add_zero, List.getElem_cons_zero] at h0 a0
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]), hs.1 (.r2, .const P) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]), a0⟩
  apply VG.Proof.Ed448.Arm.Shake.Kit.call_ct Proof.Sha3.Arm.Stream.Pad.pad_verified.1 Proof.Sha3.Arm.Stream.Pad.pad_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, a0⟩ := get t h; ⟨[VG.Proof.Ed448.Arm.Shake.kArgs E 4], VG.Proof.Ed448.Arm.Shake.kWr scr, hk.pad_pre hp he h0 h1 h2 a0,
      hk.pad_covers, hk.kWr_writes⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller sc 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]), hg (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]),
      hg (.r2, .const P) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]), hg (.r3, .const 0x1f) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues]), ht 0 (by simp)⟩
  · simp [VG.Proof.Ed448.Arm.Shake.Kit.padValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, a0⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Pad.pad_verified.1 PublicKey.pad_noFrames
      (hk.pad_pre hp hc.sp h0 h1 h2 a0) hk.pad_covers hk.kWr_writes fun v hv _ _ => ⟨hv, trivial⟩

def sqzValues (sc d : Nat) : List (Reg × Value) :=
  [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame d)]
def sqzStack (sc : Nat) : List Value := [.const 114, .caller sc KSCR]

theorem sqz_ct {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val (VG.Proof.Ed448.Arm.Shake.Kit.sqzValues sc d) (VG.Proof.Ed448.Arm.Shake.Kit.sqzStack sc)))
      (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.Arm.Stream.squeeze)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have get : ∀ t, VG.Proof.Ed448.Arm.Shake.Slots E val (VG.Proof.Ed448.Arm.Shake.Kit.sqzValues sc d) (VG.Proof.Ed448.Arm.Shake.Kit.sqzStack sc) t → t.gpr .r0 = scr ∧ t.gpr .r1 = 136 ∧
      t.gpr .r2 = 0 ∧ t.gpr .r3 = E + BitVec.ofNat 32 d ∧ stackArg t 0 = 114 ∧
      stackArg t 1 = scr + BitVec.ofNat 32 KSCR := by
    intro t hs
    have h0 := hs.1 (.r0, .caller sc 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues])
    have a0 := hs.2 0 (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack])
    have a1 := hs.2 1 (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack])
    simp only [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack, VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, BitVec.add_zero, List.getElem_cons_zero,
      List.getElem_cons_succ] at h0 a0 a1
    exact ⟨h0, hs.1 (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]), hs.1 (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]),
      hs.1 (.r3, .frame d) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]), a0, a1⟩
  apply VG.Proof.Ed448.Arm.Shake.Kit.call_ct Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.2.1
    (fun t he h => let ⟨h0, h1, h2, h3, a0, a1⟩ := get t h; ⟨[VG.Proof.Ed448.Arm.Shake.kArgs E 8], VG.Proof.Ed448.Arm.Shake.sqzWr E scr d,
      hk.sqz_pre h8 hd he h0 h1 h2 h3 a0 a1, hk.sqz_covers hd, hk.sqz_writes hd⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller sc 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]), hg (.r1, .const 136) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]),
      hg (.r2, .const 0) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]), hg (.r3, .frame d) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues]),
      ht 0 (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack]), ht 1 (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack])⟩
  · simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues, linkRegs]
  · intro g m t hc hs
    obtain ⟨h0, h1, h2, h3, a0, a1⟩ := get t hs
    refine Whole.call_ok hc Proof.Sha3.Arm.Stream.Squeeze.squeeze_verified.1 PublicKey.squeeze_noFrames
      (hk.sqz_pre h8 hd hc.sp h0 h1 h2 h3 a0 a1) (hk.sqz_covers hd) (hk.sqz_writes hd) fun v hv _ _ => ⟨hv, trivial⟩

/-! ## The blocks -/

theorem zero_ct {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.Arm.Shake.Slots E val [(.r0, .caller sc 0), (.r1, .const 0)] []))
      (.block Impl.Ed448.Arm.PublicKey.zeroStores) (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  have r0 : ∀ {s : State}, VG.Proof.Ed448.Arm.Shake.Slots E val [(.r0, .caller sc 0), (.r1, .const 0)] [] s → s.gpr .r0 = scr ∧ s.gpr .r1 = 0 :=
    fun hs => by
      have h0 := hs.1 (.r0, .caller sc 0) (by simp)
      have h1 := hs.1 (.r1, .const 0) (by simp)
      simp only [VG.Proof.Ed448.Arm.Shake.argVal, hsc.val, BitVec.add_zero] at h0 h1
      exact ⟨h0, h1⟩
  refine Whole.rel_wp ((PublicKey.stores_ct (List.range 50)).mono
    (fun _ _ h => (r0 h.1.2).1.trans (r0 h.2.2).1.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, hs⟩
    exact WP.mono (hk.zeroStores_step hc (r0 hs).1 (r0 hs).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, hs⟩
    exact WP.mono (hk.zeroStores_step hc (r0 hs).1 (r0 hs).2) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- The state zeroed. -/
theorem zeroState_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (zeroState sc)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.setup_ct ha hb [(.r0, .caller sc 0), (.r1, .const 0)] [] (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp) (by simp)).seq (hk.zero_ct hsc)

theorem hdr_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {j off : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot n j)
    (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 248) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt j off))
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => Spec.Ed448.bytesAt s.mem (State.addr E + BitVec.ofNat 64 off) 10 =
        VG.Proof.Ed448.Arm.Shake.hdrBytes (val j)) := by
  have hf := hk.fits
  have hj' := hj.1
  refine Whole.rel_wp ((VG.Proof.Ed448.Arm.Shake.hdr_sp_ct j off (by omega)).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (hk.hdr_ok hc ha hj hcl ho) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩
  · intro t ⟨hc, _⟩; exact WP.mono (hk.hdr_ok hc hb hj hcl ho) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

/-- An absorption at the position the previous one returned. -/
theorem next_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    (P : Nat) (hP : P < 136) {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩ r)
    (hfit : (VG.Proof.Ed448.Arm.Shake.argVal E val src).toNat + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs sc src len))
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat) % 136)) :=
  (hk.next_setup_ct ha hb P [(.r0, .caller sc 0), (.r1, .const 136), (.r3, src)] [len, .caller sc KSCR] (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), vs, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩) (by simp)).seq
    (hk.absorb_ct hsc hP (vpos := .const P) (by simp) (by simp) (by simp) (by simp) (by simp [linkRegs]) rfl
      hcov hs hfit)

/-- The first absorption, from position 0. -/
theorem first_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : VG.Proof.Ed448.Arm.Shake.valid n src) (vl : VG.Proof.Ed448.Arm.Shake.valid n len)
    (hcov : VG.Proof.Ed448.Arm.Shake.DataOk E ins outs ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩)
    (hs : ∀ r ∈ VG.Proof.Ed448.Arm.Shake.kWr scr, Region.Disjoint ⟨State.addr (VG.Proof.Ed448.Arm.Shake.argVal E val src), (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat⟩ r)
    (hfit : (VG.Proof.Ed448.Arm.Shake.argVal E val src).toNat + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs sc src len))
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((0 + (VG.Proof.Ed448.Arm.Shake.argVal E val len).toNat) % 136)) :=
  (hk.setup_ct ha hb [(.r0, .caller sc 0), (.r1, .const 136), (.r2, .const 0), (.r3, src)] [len, .caller sc KSCR]
    (by simp)
    (by simp only [List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), vs, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨vl, hsc.valid (by decide), fun _ h => nomatch h⟩)).seq
    (hk.absorb_ct hsc (pos := 0) (vpos := .const 0) (by decide) (by simp) (by simp) (by simp) (by simp)
      (by simp [linkRegs]) rfl hcov hs hfit)

/-- The padding, at the position the last absorption returned. -/
theorem padStep_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    (P : Nat) (hP : P < 136) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (pad sc)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.next_setup_ct ha hb P [(.r0, .caller sc 0), (.r1, .const 136), (.r3, .const 0x1f)] [.caller sc KSCR]
    (by simp)
    (by simp only [List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by simp)
    (by simp only [List.forall_mem_cons]; exact ⟨hsc.valid (by decide), fun _ h => nomatch h⟩) (by simp)).seq
    (hk.pad_ct hsc hP)

/-- 114 bytes squeezed into the frame at `d`. -/
theorem sqzStep_ct (ha : VG.Proof.Ed448.Arm.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.Arm.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.Arm.Shake.ScrAt n val sc scr)
    {d : Nat} (h8 : 8 ≤ d) (hd : d + 114 ≤ 248) :
    RelCT isa (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (squeeze sc d)
      (VG.Proof.Ed448.Arm.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  (hk.setup_ct ha hb (VG.Proof.Ed448.Arm.Shake.Kit.sqzValues sc d) (VG.Proof.Ed448.Arm.Shake.Kit.sqzStack sc) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues])
    (by simp only [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues, List.forall_mem_cons]
        exact ⟨hsc.valid (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_const (by decide), VG.Proof.Ed448.Arm.Shake.valid_frame (by omega),
          fun _ h => nomatch h⟩)
    (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzValues, preserved]) (by simp [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack])
    (by simp only [VG.Proof.Ed448.Arm.Shake.Kit.sqzStack, List.forall_mem_cons]
        exact ⟨VG.Proof.Ed448.Arm.Shake.valid_const (by decide), hsc.valid (by decide), fun _ h => nomatch h⟩)).seq
    (hk.sqz_ct hsc h8 hd)

end Kit

end VG.Proof.Ed448.Arm.Shake

end
