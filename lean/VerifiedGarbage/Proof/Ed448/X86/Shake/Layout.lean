import VerifiedGarbage.Proof.Ed25519.X86.Whole.Setup
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 on x86 (32-bit): what a complete operation's calls need of its layout

A complete operation runs in Ed25519's frame on this target
(`Proof/Ed25519/X86/Whole`): `Whole.Ctx E g m₀ ins outs` holds between the
frame's push and its pop, `E` the frame's base (the pushed `esp`), `ins`
the regions it reads (its inputs and the caller's arguments, at `E + 260`)
and `outs` those it may write besides the frame. `Kit` is what the calls
need of them: the caller's argument words below `n` in the inputs,
`scratch` an output, the outputs outside the stack, and the inputs outside
everything written. `Args` gives the argument words' values (`val`), and
`Kit.setup_ok` sets a call's outgoing arguments from them.

`fr E d l` is the frame's `l` bytes at `d`; `Lo E` the 48 bytes around `E`
that a call writes besides its own buffers (the outgoing arguments, its
return address and its stack).
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR Whole.STK Whole.Within Whole.value Whole.valid Whole.slots
  Whole.SetupStep Whole.frame_sub Whole.call_arg)

abbrev SCR (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 8192⟩
abbrev fr (E : BitVec 32) (d l : Nat) : Region := ⟨E.setWidth 64 + BitVec.ofNat 64 d, l⟩
abbrev Lo (E : BitVec 32) : Region := ⟨E.setWidth 64 - 24, 48⟩

structure Kit (E scr : BitVec 32) (n : Nat) (ins outs : List Region) : Prop where
  below : 24 ≤ E.toNat
  fit : E.toNat + 260 + 4 * n ≤ 2 ^ 32
  nc : scr.toNat + 8192 ≤ 2 ^ 32
  so : SCR scr ∈ outs
  ko : ∀ R ∈ outs, (Whole.STK E).Disjoint R
  io : ∀ r ∈ ins, ∀ R ∈ outs ++ [Whole.STK E], r.Disjoint R
  slot : ∀ i < n, ∃ R ∈ ins, R.Contains (addr E (260 + 4 * i)) 4

/-- The caller's argument words below `n`. -/
def Args (E : BitVec 32) (n : Nat) (val : Nat → BitVec 32) (m : Mem) : Prop :=
  ∀ i < n, m.readW (addr E (260 + 4 * i)) 32 = val i

def argVal (E : BitVec 32) (val : Nat → BitVec 32) : Value → BitVec 32
  | .const k => BitVec.ofNat 32 k
  | .frame d => E + BitVec.ofNat 32 d
  | .caller i d => val i + BitVec.ofNat 32 d

theorem frame_sub_stk (E : BitVec 32) {d l : Nat} (h : d + l ≤ 256) : Region.Sub (fr E d l) (Whole.STK E) :=
  fun p hp => Whole.frame_sub E p (Offset.sub_base _ h p hp)

theorem lo_sub (E : BitVec 32) : Region.Sub (Lo E) (Whole.STK E) := Region.sub_prefix (by decide)

theorem lo_base (E : BitVec 32) (d : Nat) :
    E.setWidth 64 - 24 + BitVec.ofNat 64 (24 + d) = E.setWidth 64 + BitVec.ofNat 64 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
    BitVec.sub_add_cancel]

/-- A region of the frame at `d ≥ 24` is outside `Lo E`. -/
theorem lo_fr (E : BitVec 32) {d l : Nat} (hd : 24 ≤ d) (hl : d + l ≤ 256) : (Lo E).Disjoint (fr E d l) := by
  have h := Offset.base_disjoint (E.setWidth 64 - 24) (k := 48) (e := 24 + d) (n := l) (by omega) (by omega)
  rwa [lo_base] at h

/-- The outgoing arguments are in `Lo E`. -/
theorem args_lo (E : BitVec 32) {k : Nat} (hk : k ≤ 24) : Region.Sub ⟨E.setWidth 64, k⟩ (Lo E) := by
  have h := Offset.sub_base (E.setWidth 64 - 24) (d := 24 + 0) (n := k) (k := 48) (by omega)
  rwa [lo_base, BitVec.add_zero] at h

/-- What a call writes below `E` is in `Lo E`. -/
theorem below_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) : Region.Sub (below E 24) (Lo E) := by
  have e : (below E 24) = ⟨E.setWidth 64 - BitVec.ofNat 64 24, 24⟩ := by
    simp only [below, Taint.sub_setWidth hE]
  rw [e]
  exact Region.sub_prefix (by decide)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

namespace Kit

variable (hk : Kit E scr n ins outs)
include hk

theorem frame : E.toNat + 256 ≤ 2 ^ 32 := by have := hk.fit; omega

theorem fr_addr {d : Nat} (hd : d < 256) : (E + BitVec.ofNat 32 d).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hk.frame; omega)

theorem fr_fit {d l : Nat} (hd : d + l ≤ 256) : (E + BitVec.ofNat 32 d).toNat + l ≤ 2 ^ 32 := by
  have := hk.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := E.toNat + d) (by omega)]
  omega

theorem scr_stk : (Whole.STK E).Disjoint (SCR scr) := hk.ko _ hk.so

theorem lo_scr : (Lo E).Disjoint (SCR scr) := hk.scr_stk.sub_left (lo_sub E)

/-- A callee entered from `esp = E` has 20 bytes of stack below its return address, in the
stack below the frame. -/
theorem callee_room : 20 ≤ (E - 4).toNat := by
  have := hk.below
  rw [BitVec.toNat_sub_of_le (by change (4 : BitVec 32).toNat ≤ E.toNat; simp; omega)]
  simp; omega

theorem callee_lo : Region.Sub ⟨(E - 4).setWidth 64 - 20#64, 20⟩ (Lo E) := by
  have h4 : 4 ≤ E.toNat := by have := hk.below; omega
  have e : (E - 4).setWidth 64 - 20#64 = E.setWidth 64 - 24 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.Taint.sub_setWidth h4, BitVec.sub_sub]
    rfl
  rw [e]
  exact Region.sub_prefix (by decide)

theorem callee_stk : ∀ R ∈ outs, Region.Disjoint ⟨(E - 4).setWidth 64 - 20#64, 20⟩ R := fun R hR =>
  ((hk.ko R hR).sub_left (lo_sub E)).sub_left hk.callee_lo

theorem callee_in : ∀ r ∈ ins, Region.Disjoint ⟨(E - 4).setWidth 64 - 20#64, 20⟩ r := fun r hr =>
  ((hk.io r hr _ (List.mem_append_right _ (List.mem_singleton_self _))).symm.sub_left (lo_sub E)).sub_left
    hk.callee_lo

theorem fr_scr {d l : Nat} (h : d + l ≤ 256) : (fr E d l).Disjoint (SCR scr) :=
  hk.scr_stk.sub_left (frame_sub_stk E h)

/-- The inputs, as they were. -/
theorem input_bytes (hc : Whole.Ctx E g m₀ ins outs t) {r : Region} (hr : r ∈ ins)
    {D : Region} (hw : Whole.Within D r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem D.base D.len = Spec.Ed448.bytesAt m₀ D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := D) (fun R hR => (hk.io r hr R hR).sub_left hw.sub) hn (List.mem_range.mp hi)

theorem arg_word (hc : Whole.Ctx E g m₀ ins outs t) {i : Nat} (hi : i < n) :
    t.mem.readW (addr E (260 + 4 * i)) 32 = m₀.readW (addr E (260 + 4 * i)) 32 := by
  obtain ⟨R, hR, hcon⟩ := hk.slot i hi
  exact hc.frame.readW (r := R) hcon (hk.io R hR) (by decide)

theorem value_eq (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {v : Value} (hv : Whole.valid n v) : Whole.value E t.mem v = argVal E val v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller i d =>
    simp only [Whole.value, argVal]
    rw [hk.arg_word hc hv, ha i hv]

theorem readable (hc : Whole.Ctx E g m₀ ins outs t) :
    ∀ i < n, InRegions (t.rd ++ t.wr) (addr E (260 + 4 * i)) 4 := fun i hi => by
  obtain ⟨R, hR, hcon⟩ := hk.slot i hi
  rw [hc.rd]
  exact ⟨R, List.mem_append_left _ hR, hcon⟩

/-- A call's outgoing arguments set up: the set-up writes only them, and
leaves every register but `eax` alone. -/
theorem setup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : Args E n val m₀)
    {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid n v) :
    WP isa (.block (setup 0 vs)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧
      (∀ j (hj : j < vs.length), Whole.slots E u j = argVal E val (vs[j]'hj)) ∧
      (∀ r, r ≠ .eax → u.gpr r = t.gpr r) := by
  refine WP.mono (VG.Proof.Ed25519.X86.Whole.setup_ok (n := n) hc.esp (by have := hk.fit; omega)
    (hk.readable hc) (by rw [hc.wr]; exact List.mem_cons_self) (by omega) hv)
    fun u ⟨hu, hft, hvals⟩ => ?_
  have hf24 : Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem :=
    hft.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        simpa only [Nat.mul_zero, BitVec.add_zero] using Region.sub_prefix (by omega)⟩
  have hcu : Whole.Ctx E g m₀ ins outs u := by
    refine hc.of_frame hu.rd hu.wr hu.esp ?_ hf24 ?_
    · intro r hr _
      apply hu.regs
      rintro rfl
      simp [calleeSaved] at hr
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Region.sub_prefix (by decide))
  refine ⟨hcu, hf24, fun j hj => ?_, hu.regs⟩
  have e := hvals j hj
  simp only [Nat.zero_add] at e
  rw [addr_eq (by have := hk.frame; omega)] at e
  rw [Whole.slots, e]
  have := hk.value_eq hc ha (hv _ (List.getElem_mem hj))
  rw [VG.Proof.Ed25519.X86.Whole.value_congr (n := n) (by have := hk.fit; omega) (hv _ (List.getElem_mem hj))
    (Frame.refl _ _)] at this
  exact this

/-- A call's argument, from the outgoing slots. -/
theorem call_arg (hc : Whole.Ctx E g m₀ ins outs t) {j : Nat} (hj : j < 6) :
    arg t.callEntry j = Whole.slots E t j :=
  Whole.call_arg hc.esp hk.below hk.frame (by omega)

end Kit

/-- Bytes outside the regions a step may write, through it. -/
theorem frame_bytes {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {D : Region}
    (hd : ∀ r ∈ ws, D.Disjoint r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

end VG.Proof.Ed448.X86.Shake
