import VerifiedGarbage.Proof.Ed448.Arm.Shake.Setup
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Spec.Ed448.Contract

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
  addr_add (by have := hk.top; omega)

theorem frame_fit {d k : Nat} (hd : d + k ≤ 248) : (E + BitVec.ofNat 32 d).toNat + k ≤ 2 ^ 32 := by
  have ht := hk.top
  rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

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
  Offset.base_disjoint _ hd (by omega)

end VG.Proof.Ed448.Arm.Shake
