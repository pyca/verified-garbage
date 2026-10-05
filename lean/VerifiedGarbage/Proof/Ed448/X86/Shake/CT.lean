import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Scratch
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Impl.Ed448.X86.Shake
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.PruneBytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.OffsetBelow

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.Layout`. -/
section

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
  so : VG.Proof.Ed448.X86.Shake.SCR scr ∈ outs
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

theorem frame_sub_stk (E : BitVec 32) {d l : Nat} (h : d + l ≤ 256) : Region.Sub (VG.Proof.Ed448.X86.Shake.fr E d l) (Whole.STK E) :=
  fun p hp => Whole.frame_sub E p (Offset.sub_base _ h p hp)

theorem lo_sub (E : BitVec 32) : Region.Sub (VG.Proof.Ed448.X86.Shake.Lo E) (Whole.STK E) := Region.sub_prefix (by decide)

theorem lo_base (E : BitVec 32) (d : Nat) :
    E.setWidth 64 - 24 + BitVec.ofNat 64 (24 + d) = E.setWidth 64 + BitVec.ofNat 64 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (24 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
    BitVec.sub_add_cancel]

/-- A region of the frame at `d ≥ 24` is outside `Lo E`. -/
theorem lo_fr (E : BitVec 32) {d l : Nat} (hd : 24 ≤ d) (hl : d + l ≤ 256) : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint (VG.Proof.Ed448.X86.Shake.fr E d l) := by
  have h := Offset.base_disjoint (E.setWidth 64 - 24) (k := 48) (e := 24 + d) (n := l) (by omega) (by omega)
  rwa [VG.Proof.Ed448.X86.Shake.lo_base] at h

/-- The outgoing arguments are in `Lo E`. -/
theorem args_lo (E : BitVec 32) {k : Nat} (hk : k ≤ 24) : Region.Sub ⟨E.setWidth 64, k⟩ (VG.Proof.Ed448.X86.Shake.Lo E) := by
  have h := Offset.sub_base (E.setWidth 64 - 24) (d := 24 + 0) (n := k) (k := 48) (by omega)
  rwa [VG.Proof.Ed448.X86.Shake.lo_base, BitVec.add_zero] at h

/-- What a call writes below `E` is in `Lo E`. -/
theorem below_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) : Region.Sub (below E 24) (VG.Proof.Ed448.X86.Shake.Lo E) := by
  have e : (below E 24) = ⟨E.setWidth 64 - BitVec.ofNat 64 24, 24⟩ := by
    simp only [below, Taint.sub_setWidth hE]
  rw [e]
  exact Region.sub_prefix (by decide)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

namespace Kit

variable (hk : VG.Proof.Ed448.X86.Shake.Kit E scr n ins outs)
include hk

theorem frame : E.toNat + 256 ≤ 2 ^ 32 := by have := hk.fit; omega

theorem fr_addr {d : Nat} (hd : d < 256) : (E + BitVec.ofNat 32 d).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hk.frame; omega)

theorem fr_fit {d l : Nat} (hd : d + l ≤ 256) : (E + BitVec.ofNat 32 d).toNat + l ≤ 2 ^ 32 := by
  have := hk.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := E.toNat + d) (by omega)]
  omega

theorem scr_stk : (Whole.STK E).Disjoint (VG.Proof.Ed448.X86.Shake.SCR scr) := hk.ko _ hk.so

theorem lo_scr : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint (VG.Proof.Ed448.X86.Shake.SCR scr) := hk.scr_stk.sub_left (VG.Proof.Ed448.X86.Shake.lo_sub E)

theorem fr_scr {d l : Nat} (h : d + l ≤ 256) : (VG.Proof.Ed448.X86.Shake.fr E d l).Disjoint (VG.Proof.Ed448.X86.Shake.SCR scr) :=
  hk.scr_stk.sub_left (VG.Proof.Ed448.X86.Shake.frame_sub_stk E h)

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

theorem value_eq (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀)
    {v : Value} (hv : Whole.valid n v) : Whole.value E t.mem v = VG.Proof.Ed448.X86.Shake.argVal E val v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller i d =>
    simp only [Whole.value, VG.Proof.Ed448.X86.Shake.argVal]
    rw [hk.arg_word hc hv, ha i hv]

theorem readable (hc : Whole.Ctx E g m₀ ins outs t) :
    ∀ i < n, InRegions (t.rd ++ t.wr) (addr E (260 + 4 * i)) 4 := fun i hi => by
  obtain ⟨R, hR, hcon⟩ := hk.slot i hi
  rw [hc.rd]
  exact ⟨R, List.mem_append_left _ hR, hcon⟩

/-- A call's outgoing arguments set up: the set-up writes only them, and
leaves every register but `eax` alone. -/
theorem setup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀)
    {vs : List Value} (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid n v) :
    WP isa (.block (VG.Impl.Ed25519.X86.Whole.setup 0 vs)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧
      (∀ j (hj : j < vs.length), Whole.slots E u j = VG.Proof.Ed448.X86.Shake.argVal E val (vs[j]'hj)) ∧
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge`. -/
section

/-!
# Ed448 on x86 (32-bit): the calls of the sponge functions

The Keccak state zeroed (`Kit.zero_ok`), and each call of a sponge function
through `Whole.call_ok` with its own contract (`Proof.Sha3.absorbX86`,
`padX86`, `squeezeX86`), from its set-up (`Kit.first_abs`, `Kit.next_abs`,
`Kit.pad_step`, `Kit.sqz_step`), for any layout (`Kit`) with `scratch` the
caller's argument `sc` (`ScrAt`). An absorption reads its data from the
frame, an input or an output (`DataOk`) outside what the calls write
(`Away`); each after the first starts at the position the previous one
returned in `eax`. Each step states the regions it may write: `Lo E` (the
outgoing arguments, and the return address and stack of its call), the
state and the working space (`kWr scr`), and the squeezed output.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (Value setup at_)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.X86 (Whole.CallReady Whole.Ctx Whole.FR Whole.STK Whole.Within Whole.valid Whole.slots Whole.call_ok
  Whole.callEntry_frame Whole.arg_base)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t u : State}

/-- `scratch` is the caller's argument `sc`. -/
structure ScrAt (n : Nat) (val : Nat → BitVec 32) (sc : Nat) (scr : BitVec 32) : Prop where
  lt : sc < n
  val : val sc = scr

theorem ScrAt.valid {sc : Nat} (h : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr) (d : Nat) : Whole.valid n (.caller sc d) := h.lt

theorem absorb_stack : stackUse Impl.Sha3.X86.Stream.absorb = 12 := by decide +kernel
theorem pad_stack : stackUse Impl.Sha3.X86.Stream.pad = 12 := by decide +kernel
theorem squeeze_stack : stackUse Impl.Sha3.X86.Stream.squeeze = 12 := by decide +kernel

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem nosp_ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) :=
  VG.Proof.Ed448.X86.Shake.nosp_seq (a := a) (b := b) ha hb

/-- The calls of the permutation do not write `esp`, from the permutation's
own `permute_nosp`, rather than by evaluating its code again. -/
theorem permuteCall_nosp (st scr : Reg) : NoSp (Impl.Sha3.X86.Stream.permuteCall st scr) := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · rfl
  rcases List.mem_append.mp hi with hi | hi
  · exact Proof.Sha3.X86.permute_nosp i hi
  · rw [List.mem_singleton.mp hi]; rfl

theorem next_nosp : NoSp Impl.Sha3.X86.Stream.next :=
  VG.Proof.Ed448.X86.Shake.nosp_ite (VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.permuteCall_nosp _ _)) (NoSp.of_all (by decide +kernel))

theorem absorb_nosp : NoSp Impl.Sha3.X86.Stream.absorb :=
  VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.nosp_seq (VG.Proof.Ed448.X86.Shake.nosp_ite (NoSp.of_all (by decide +kernel))
    (VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.nosp_seq VG.Proof.Ed448.X86.Shake.next_nosp (NoSp.of_all (by decide +kernel)))))
    (NoSp.of_all (by decide +kernel)))

theorem pad_nosp : NoSp Impl.Sha3.X86.Stream.pad :=
  VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.nosp_seq (VG.Proof.Ed448.X86.Shake.permuteCall_nosp _ _) (NoSp.of_all (by decide +kernel)))

theorem squeeze_nosp : NoSp Impl.Sha3.X86.Stream.squeeze :=
  VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.nosp_seq (VG.Proof.Ed448.X86.Shake.nosp_ite (NoSp.of_all (by decide +kernel))
    (VG.Proof.Ed448.X86.Shake.nosp_seq (NoSp.of_all (by decide +kernel)) (VG.Proof.Ed448.X86.Shake.nosp_seq VG.Proof.Ed448.X86.Shake.next_nosp (NoSp.of_all (by decide +kernel)))))
    (NoSp.of_all (by decide +kernel)))

theorem absorb_nosp' {args : List Instr} (h : NoSp (.block args)) : NoSp (absorb args) :=
  VG.Proof.Ed448.X86.Shake.nosp_seq h VG.Proof.Ed448.X86.Shake.absorb_nosp

theorem pad_nosp' {sc : Nat} (h : NoSp (.block (padArgs sc))) : NoSp (pad sc) :=
  VG.Proof.Ed448.X86.Shake.nosp_seq h VG.Proof.Ed448.X86.Shake.pad_nosp

theorem squeeze_nosp' {sc d : Nat} (h : NoSp (.block (sqzArgs sc d))) : NoSp (squeeze sc d) :=
  VG.Proof.Ed448.X86.Shake.nosp_seq h VG.Proof.Ed448.X86.Shake.squeeze_nosp

/-! ## The regions -/

/-- The state and the sponge functions' working space. -/
def kWr (scr : BitVec 32) : List Region :=
  [⟨scr.setWidth 64, 200⟩, ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩]

theorem kWr_state (scr : BitVec 32) : (⟨scr.setWidth 64, 200⟩ : Region) ∈ VG.Proof.Ed448.X86.Shake.kWr scr := List.mem_cons_self
theorem kWr_scratch (scr : BitVec 32) : (⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩ : Region) ∈ VG.Proof.Ed448.X86.Shake.kWr scr :=
  List.mem_cons_of_mem _ List.mem_cons_self

/-- Data an absorption may read: in the frame, or in an input or an output. -/
def DataOk (E : BitVec 32) (ins outs : List Region) (D : Region) : Prop :=
  Whole.Within D (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within D R

/-- Outside what a call of a sponge function writes but its squeezed output. -/
structure Away (E scr : BitVec 32) (D : Region) : Prop where
  lo : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint D
  kwr : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, D.Disjoint r

theorem lo_off (E : BitVec 32) {d : Nat} (hd : d ≤ 24) :
    E.setWidth 64 - BitVec.ofNat 64 d = E.setWidth 64 - 24 + BitVec.ofNat 64 (24 - d) :=
  Offset.sub_ofNat_eq _ hd

/-- A call's return address and the 12 bytes below it, from `E`. -/
theorem ret_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) :
    Region.Sub ⟨(E - 4).setWidth 64, 4⟩ (VG.Proof.Ed448.X86.Shake.Lo E) := by
  have e : (E - 4).setWidth 64 = E.setWidth 64 - 24 + BitVec.ofNat 64 20 := by
    rw [show (E - 4) = E - BitVec.ofNat 32 4 from rfl, Taint.sub_setWidth (by omega), VG.Proof.Ed448.X86.Shake.lo_off E (by decide)]
  rw [e]
  exact Offset.sub_base _ (by decide)

theorem stk_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) :
    Region.Sub ⟨(E - 4).setWidth 64 - 12, 12⟩ (VG.Proof.Ed448.X86.Shake.Lo E) := by
  have e : (E - 4).setWidth 64 - 12 = E.setWidth 64 - 24 + BitVec.ofNat 64 8 := by
    rw [show (E - 4) = E - BitVec.ofNat 32 4 from rfl, Taint.sub_setWidth (by omega),
      show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, BitVec.sub_sub, ← BitVec.ofNat_add,
      VG.Proof.Ed448.X86.Shake.lo_off E (by decide)]
  rw [e]
  exact Offset.sub_base _ (by decide)

theorem below4_lo {E : BitVec 32} (hE : 24 ≤ E.toNat) : Region.Sub (below E 4) (VG.Proof.Ed448.X86.Shake.Lo E) :=
  fun p hp => VG.Proof.Ed448.X86.Shake.below_lo hE p (below_sub (by decide) hE p hp)

theorem covers_of {E : BitVec 32} {rs : List Region}
    (h : ∀ r ∈ rs, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R) :
    Covers rs (ins ++ Whole.FR E :: outs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases h r hr with hf | ⟨R, hR, hw⟩
  · exact ⟨Whole.FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · refine ⟨R, ?_, hw⟩
    rcases List.mem_append.mp hR with hi | ho
    · exact List.mem_append_left _ hi
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)

theorem args_within (E : BitVec 32) {k : Nat} (hk : k ≤ 256) : Whole.Within ⟨E.setWidth 64, k⟩ (Whole.FR E) :=
  ⟨0, (BitVec.add_zero _).symm, by change 0 + k ≤ 256; omega⟩

theorem frame_within (E : BitVec 32) {d l : Nat} (hd : d + l ≤ 256) : Whole.Within (VG.Proof.Ed448.X86.Shake.fr E d l) (Whole.FR E) :=
  ⟨d, rfl, hd⟩

/-- The state, through a step outside it. -/
theorem state_frame {ws : List Region} {m m' : Mem} {p : Addr} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨p, 200⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p :=
  Proof.Sha3.stateAt_congr fun _ hj => hm.bytes (R := ⟨p, 200⟩) hd (by change 200 ≤ 2 ^ 64; decide) hj

theorem repr_frame {ws : List Region} {m m' : Mem} {p : Addr} (hm : Frame ws m m')
    (hd : ∀ r ∈ ws, (⟨p, 200⟩ : Region).Disjoint r) {msg : List Byte}
    (h : Spec.Sha3.Repr m p 136 msg) : Spec.Sha3.Repr m' p 136 msg := by
  unfold Spec.Sha3.Repr at h ⊢
  rw [VG.Proof.Ed448.X86.Shake.state_frame hm hd]; exact h

/-- After zeroing the first `k` words of the state at `eax`. -/
structure ZInv (scr : BitVec 32) (s₁ : State) (k : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨scr.setWidth 64, 200⟩] s₁.mem s.mem
  zero : ∀ j < k, s.mem.readW (scr.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem stateAt_zero {m : Mem} (h : ∀ j < 50, m.readW (scr.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = 0) :
    stateAt m (scr.setWidth 64) = Spec.Sha3.zero := by
  refine Eq.trans (Proof.Sha3.stateAt_congr (m := fun _ => 0) fun j hj => ?_) ?_
  · have e := Mem.readW_byte m (scr.setWidth 64 + BitVec.ofNat 64 (4 * (j / 4))) (i := j % 4) (by omega)
    rw [Offset.add_add, show 4 * (j / 4) + j % 4 = j by omega, h (j / 4) (by omega)] at e
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp
  · apply Vector.ext
    intro i hi
    simp [stateAt, Spec.Sha3.zero, Mem.readW, Mem.read]

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    Spec.Sha3.squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [Spec.Sha3.squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  rw [VG.Proof.Ed448.X86.Shake.squeezeFrom_zero]; rfl

theorem length_sbytes (m : Mem) (p : Addr) (k : Nat) : (Spec.Sha3.bytesAt m p k).length = k := by
  simp [Spec.Sha3.bytesAt]

theorem argVal_const (k : Nat) : VG.Proof.Ed448.X86.Shake.argVal E val (.const k) = BitVec.ofNat 32 k := rfl
theorem argVal_frame (d : Nat) : VG.Proof.Ed448.X86.Shake.argVal E val (.frame d) = E + BitVec.ofNat 32 d := rfl
theorem argVal_caller (i d : Nat) : VG.Proof.Ed448.X86.Shake.argVal E val (.caller i d) = val i + BitVec.ofNat 32 d := rfl

/-- Bytes outside the regions a step may write, through it. -/
theorem sframe_bytes {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {D : Region}
    (hd : ∀ r ∈ ws, D.Disjoint r) (hn : D.len ≤ 2 ^ 64) :
    Spec.Sha3.bytesAt m' D.base D.len = Spec.Sha3.bytesAt m D.base D.len := by
  unfold Spec.Sha3.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

/-- The outgoing arguments of an absorption. -/
structure AbsSlots (E scr : BitVec 32) (pos : Nat) (P N : BitVec 32) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 pos
  a3 : Whole.slots E s 3 = P
  a4 : Whole.slots E s 4 = N
  a5 : Whole.slots E s 5 = scr + BitVec.ofNat 32 KSCR

/-- The outgoing arguments of the padding. -/
structure PadSlots (E scr : BitVec 32) (pos : Nat) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 pos
  a3 : Whole.slots E s 3 = BitVec.ofNat 32 0x1f
  a4 : Whole.slots E s 4 = scr + BitVec.ofNat 32 KSCR

/-- The outgoing arguments of a squeeze into the frame at `d`. -/
structure SqzSlots (E scr : BitVec 32) (d : Nat) (s : State) : Prop where
  a0 : Whole.slots E s 0 = scr
  a1 : Whole.slots E s 1 = 136
  a2 : Whole.slots E s 2 = BitVec.ofNat 32 0
  a3 : Whole.slots E s 3 = E + BitVec.ofNat 32 d
  a4 : Whole.slots E s 4 = BitVec.ofNat 32 114
  a5 : Whole.slots E s 5 = scr + BitVec.ofNat 32 KSCR

namespace Kit

variable (hk : VG.Proof.Ed448.X86.Shake.Kit E scr n ins outs)
include hk

theorem scr_addr : (scr + BitVec.ofNat 32 KSCR).setWidth 64 = scr.setWidth 64 + BitVec.ofNat 64 KSCR :=
  addr_eq (by have := hk.nc; simp only [KSCR]; omega)

theorem scr_fit : (scr + BitVec.ofNat 32 KSCR).toNat + 640 ≤ 2 ^ 32 := by
  have := hk.nc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := KSCR) (by simp only [KSCR]; omega),
    Nat.mod_eq_of_lt (by simp only [KSCR]; omega)]
  simp only [KSCR]; omega

theorem kWr_sub : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, Whole.Within r (VG.Proof.Ed448.X86.Shake.SCR scr) := by
  intro r hr
  simp only [VG.Proof.Ed448.X86.Shake.kWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨0, (BitVec.add_zero _).symm, by change 0 + 200 ≤ 8192; decide⟩
  · exact ⟨KSCR, hk.scr_addr, by change 208 + 640 ≤ 8192; decide⟩

theorem state_scratch : (⟨scr.setWidth 64, 200⟩ : Region).Disjoint
    ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩ := by
  rw [hk.scr_addr]; exact Offset.base_disjoint _ (by decide) (by decide)

theorem kWr_writes : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R :=
  fun r hr => .inr ⟨VG.Proof.Ed448.X86.Shake.SCR scr, hk.so, hk.kWr_sub r hr⟩

theorem kWr_covered : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ ins ++ outs, Whole.Within r R :=
  fun r hr => .inr ⟨VG.Proof.Ed448.X86.Shake.SCR scr, List.mem_append_right _ hk.so, hk.kWr_sub r hr⟩

/-- `Lo E` is outside the state and the working space. -/
theorem lo_kWr : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint r :=
  fun r hr => hk.lo_scr.sub_right (hk.kWr_sub r hr).sub

theorem away_fr {d l : Nat} (h24 : 24 ≤ d) (hd : d + l ≤ 256) : VG.Proof.Ed448.X86.Shake.Away E scr (VG.Proof.Ed448.X86.Shake.fr E d l) :=
  ⟨VG.Proof.Ed448.X86.Shake.lo_fr E h24 hd, fun r hr => (hk.fr_scr hd).sub_right (hk.kWr_sub r hr).sub⟩

theorem away_input {R D : Region} (hR : R ∈ ins) (hw : Whole.Within D R) : VG.Proof.Ed448.X86.Shake.Away E scr D :=
  ⟨((hk.io R hR (Whole.STK E) (by simp)).sub_left hw.sub).symm.sub_left (VG.Proof.Ed448.X86.Shake.lo_sub E),
    fun r hr => ((hk.io R hR (VG.Proof.Ed448.X86.Shake.SCR scr) (List.mem_append_left _ hk.so)).sub_left hw.sub).sub_right
      (hk.kWr_sub r hr).sub⟩

theorem away_output {R D : Region} (hR : R ∈ outs) (hRs : R.Disjoint (VG.Proof.Ed448.X86.Shake.SCR scr)) (hw : Whole.Within D R) :
    VG.Proof.Ed448.X86.Shake.Away E scr D :=
  ⟨((hk.ko R hR).sub_right hw.sub).sub_left (VG.Proof.Ed448.X86.Shake.lo_sub E),
    fun r hr => (hRs.sub_left hw.sub).sub_right (hk.kWr_sub r hr).sub⟩

/-! ## The state, zeroed -/

theorem zeroStores_ok {s₁ : State} (h0 : s₁.gpr .eax = scr) (h2 : s₁.gpr .edx = 0)
    (hwr : ∀ k < 50, InRegions s₁.wr (scr.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block zeroStores) s₁ (VG.Proof.Ed448.X86.Shake.ZInv scr s₁ 50) := by
  rw [zeroStores, List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa) (VG.Proof.Ed448.X86.Shake.ZInv scr s₁) (fun k s hk' h => ?_) 50 (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have ea : addr scr (4 * k) = scr.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    addr_eq (by have := hk.nc; omega)
  have hb : s.gpr .eax = scr := by rw [h.gpr, h0]
  refine wp_stm hb (by rw [ea, h.wr]; exact hwr k hk') fun s' m => WP.block_nil
    ⟨by rw [m.gpr, h.gpr], by rw [m.rd, h.rd], by rw [m.wr, h.wr], ?_, fun j hj => ?_⟩
  · rw [m.mem, ea]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [m.mem, ea, h.gpr, h2]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.zero j (by omega)

/-- `scratch` into `eax`, `0` into `edx`. -/
theorem zeroArgs_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr) :
    WP isa (.block (zeroArgs sc)) t fun u => Whole.Ctx E g m₀ ins outs u ∧ u.gpr .eax = scr ∧
      u.gpr .edx = 0 ∧ u.mem = t.mem := by
  unfold zeroArgs
  refine wp_ldm (b := .esp) hc.esp (hk.readable hc sc hsc.lt) fun s1 v1 => wp_movi fun s2 v2 => WP.block_nil ?_
  refine ⟨hc.of_frame (by rw [v2.rd, v1.rd]) (by rw [v2.wr, v1.wr])
      (by rw [v2.other _ (by decide), v1.other _ (by decide)]) ?_ (ws := [])
      (by rw [v2.mem, v1.mem]; exact Frame.refl _ _) (fun _ h => nomatch h), ?_, v2.gpr, by rw [v2.mem, v1.mem]⟩
  · intro r hr _
    have h0 : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    have h2 : r ≠ .edx := by rintro rfl; simp [calleeSaved] at hr
    rw [v2.other r h2, v1.other r h0]
  · rw [v2.other _ (by decide), v1.gpr, hk.arg_word hc hsc.lt, ha sc hsc.lt, hsc.val]

/-- The stores, from `scratch` in `eax` and `0` in `edx`. -/
theorem zeroStores_step {s : State} (hc : Whole.Ctx E g m₀ ins outs s) (h0 : s.gpr .eax = scr)
    (h2 : s.gpr .edx = 0) :
    WP isa (.block zeroStores) s fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (scr.setWidth 64) = Spec.Sha3.zero ∧ Frame [⟨scr.setWidth 64, 200⟩] s.mem u.mem := by
  have hw : ∀ k < 50, InRegions s.wr (scr.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk'
    rw [hc.wr]
    exact ⟨VG.Proof.Ed448.X86.Shake.SCR scr, List.mem_cons_of_mem _ hk.so, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (hk.zeroStores_ok h0 h2 hw) fun v hv => ⟨?_, VG.Proof.Ed448.X86.Shake.stateAt_zero hv.zero, hv.frame⟩
  refine hc.of_frame hv.rd hv.wr (by rw [hv.gpr]) (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨VG.Proof.Ed448.X86.Shake.SCR scr, hk.so, Region.sub_prefix (by decide)⟩

theorem zero_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr) :
    WP isa (zeroState sc) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      stateAt u.mem (scr.setWidth 64) = Spec.Sha3.zero ∧ Frame [⟨scr.setWidth 64, 200⟩] t.mem u.mem := by
  unfold zeroState
  rw [WP.block_append_iff]
  refine WP.mono (hk.zeroArgs_ok hc ha hsc) fun u ⟨hu, h0, h2, hm⟩ => ?_
  refine WP.mono (hk.zeroStores_step hu h0 h2) fun v ⟨hv, hz, hf⟩ => ⟨hv, hz, ?_⟩
  rw [← hm]; exact hf

/-! ## The calls' common facts -/

theorem esp4 : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by have := hk.below; omega)

/-- The return address and the callee's stack are outside the regions `D`
that `Lo E` is outside. -/
theorem ret_disj {D : Region} (h : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint D) : Region.Disjoint ⟨(E - 4).setWidth 64, 4⟩ D :=
  h.sub_left (VG.Proof.Ed448.X86.Shake.ret_lo hk.below)

theorem stk_disj {D : Region} (h : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint D) : Region.Disjoint ⟨(E - 4).setWidth 64 - 12, 12⟩ D :=
  h.sub_left (VG.Proof.Ed448.X86.Shake.stk_lo hk.below)

omit hk in
theorem args_disj {D : Region} {k : Nat} (hk' : k ≤ 24) (h : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint D) :
    Region.Disjoint ⟨E.setWidth 64, k⟩ D :=
  h.sub_left (VG.Proof.Ed448.X86.Shake.args_lo E hk')

/-- Bytes outside `Lo E`, as the callee sees them. -/
theorem entry_bytes (hc : Whole.Ctx E g m₀ ins outs t) {D : Region} (h : (VG.Proof.Ed448.X86.Shake.Lo E).Disjoint D) (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.callEntry.mem D.base D.len = Spec.Ed448.bytesAt t.mem D.base D.len := by
  refine VG.Proof.Ed448.X86.Shake.frame_bytes (Whole.callEntry_frame t) (fun r hr => ?_) hn
  rw [List.mem_singleton.mp hr, hc.esp]
  exact (h.sub_left (VG.Proof.Ed448.X86.Shake.below4_lo hk.below)).symm

theorem entry_repr (hc : Whole.Ctx E g m₀ ins outs t) {msg : List Byte}
    (h : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg) : Spec.Sha3.Repr t.callEntry.mem (scr.setWidth 64) 136 msg :=
  VG.Proof.Ed448.X86.Shake.repr_frame (Whole.callEntry_frame t) (fun r hr => by
    rw [List.mem_singleton.mp hr, hc.esp]
    exact ((hk.lo_kWr _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)).sub_left (VG.Proof.Ed448.X86.Shake.below4_lo hk.below)).symm) h

/-! ## `absorb` -/

def absRd (D : Region) : List Region := [D]
def absWr (E scr : BitVec 32) : List Region := VG.Proof.Ed448.X86.Shake.kWr scr ++ [⟨E.setWidth 64, 24⟩]

theorem abs_pre (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N.toNat⟩) (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : arg t.callEntry 0 = scr) (h1 : arg t.callEntry 1 = 136) (h2 : arg t.callEntry 2 = BitVec.ofNat 32 pos)
    (h3 : arg t.callEntry 3 = P) (h4 : arg t.callEntry 4 = N) (h5 : arg t.callEntry 5 = scr + BitVec.ofNat 32 KSCR) :
    Proof.Sha3.absorbX86.pre (t.callEntry.withRegions (VG.Proof.Ed448.X86.Shake.Kit.absRd ⟨P.setWidth 64, N.toNat⟩) (VG.Proof.Ed448.X86.Shake.Kit.absWr E scr)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  simp only [Proof.Sha3.absorbX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, h0, h1, h2, h3, h4, h5, ab, VG.Proof.Ed448.X86.Shake.Kit.absRd, VG.Proof.Ed448.X86.Shake.Kit.absWr, VG.Proof.Ed448.X86.Shake.kWr,
    List.cons_append, List.nil_append]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨trivial, trivial, hk.state_scratch, hd.kwr _ (VG.Proof.Ed448.X86.Shake.kWr_state scr), hd.kwr _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr),
    VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) hd.lo,
    VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.ret_disj hd.lo, hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.stk_disj hd.lo, hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    by have := hk.nc; omega, hfit, hk.scr_fit, by omega, by omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem abs_covers {D : Region} (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs D) :
    Covers (VG.Proof.Ed448.X86.Shake.Kit.absRd D ++ VG.Proof.Ed448.X86.Shake.Kit.absWr E scr) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.X86.Shake.covers_of fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]; exact hcov
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_covered r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_within E (by decide))

theorem abs_writes : ∀ r ∈ VG.Proof.Ed448.X86.Shake.Kit.absWr E scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_writes r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_within E (by decide))

/-- What a call writes, in `Lo E` and the regions it may write. -/
theorem call_frame {ws : List Region} {m m' : Mem} (hf : Frame (ws ++ [VG.X86.below E 24]) m m')
    (hw : ∀ r ∈ ws, Region.Sub r (VG.Proof.Ed448.X86.Shake.Lo E) ∨ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr) : Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) m m' := by
  refine Frame.sub hf fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with h | h
    · exact ⟨VG.Proof.Ed448.X86.Shake.Lo E, List.mem_cons_self, h⟩
    · exact ⟨r, List.mem_cons_of_mem _ h, fun _ h => h⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨VG.Proof.Ed448.X86.Shake.Lo E, List.mem_cons_self, VG.Proof.Ed448.X86.Shake.below_lo hk.below⟩

omit hk in
theorem absWr_lo : ∀ r ∈ VG.Proof.Ed448.X86.Shake.Kit.absWr E scr, Region.Sub r (VG.Proof.Ed448.X86.Shake.Lo E) ∨ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_lo E (by decide))

theorem absorb_call (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32)
    (h0 : arg t.callEntry 0 = scr) (h1 : arg t.callEntry 1 = 136) (h2 : arg t.callEntry 2 = BitVec.ofNat 32 pos)
    (h3 : arg t.callEntry 3 = P) (h4 : arg t.callEntry 4 = N) (h5 : arg t.callEntry 5 = scr + BitVec.ofNat 32 KSCR) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat)) ∧
      v.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Absorb.absorb_verified.1 VG.Proof.Ed448.X86.Shake.absorb_nosp
    (by rw [VG.Proof.Ed448.X86.Shake.absorb_stack]; decide) (hk.abs_pre hc hp hd hfit h0 h1 h2 h3 h4 h5) (hk.abs_covers hcov)
    hk.abs_writes fun v hv hf _ ⟨s₂, hm, hg, hpost⟩ => ⟨hv, hk.call_frame hf VG.Proof.Ed448.X86.Shake.Kit.absWr_lo, ?_, ?_⟩
  · intro msg hr hpos
    have h := hpost.1 msg (by
      simp only [State.withRegions_mem, arg_withRegions, h0, h1]
      exact hk.entry_repr hc hr) (by simp only [arg_withRegions, h1, h2, hpn]; exact hpos)
    simp only [State.withRegions_mem, arg_withRegions, h0, h1, h3, h4] at h
    have e : Spec.Sha3.bytesAt t.callEntry.mem (P.setWidth 64) N.toNat =
        Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat :=
      hk.entry_bytes hc (D := ⟨P.setWidth 64, N.toNat⟩) hd.lo (by change N.toNat ≤ 2 ^ 64; have := N.isLt; omega)
    rw [hm, e] at h
    exact h
  · have h := hpost.2
    simp only [arg_withRegions, h1, h2, h4, hpn] at h
    rw [← hg .eax (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [h, show BitVec.toNat (136 : BitVec 32) = 136 from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (pos + N.toNat) % 136) (b := 2 ^ 32)
        (by have := Nat.mod_lt (pos + N.toNat) (by decide : 136 > 0); omega)]

/-! ## Set-ups -/

/-- The state is outside the outgoing arguments. -/
theorem state_args : ∀ r ∈ [(⟨E.setWidth 64, 24⟩ : Region)], (⟨scr.setWidth 64, 200⟩ : Region).Disjoint r :=
  fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ((hk.lo_kWr _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)).sub_left (VG.Proof.Ed448.X86.Shake.args_lo E (by decide))).symm

omit hk in
theorem args_frame {m m' : Mem} (h : Frame [⟨E.setWidth 64, 24⟩] m m') : Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) m m' :=
  h.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨VG.Proof.Ed448.X86.Shake.Lo E, List.mem_cons_self, VG.Proof.Ed448.X86.Shake.args_lo E (by decide)⟩

omit hk in
theorem data_args {D : Region} (hd : VG.Proof.Ed448.X86.Shake.Away E scr D) : ∀ r ∈ [(⟨E.setWidth 64, 24⟩ : Region)], D.Disjoint r :=
  fun r hr => by rw [List.mem_singleton.mp hr]; exact (hd.lo.sub_left (VG.Proof.Ed448.X86.Shake.args_lo E (by decide))).symm

/-- `mov [esp + 8], edx`: the third outgoing argument. -/
theorem store2_ok (hc : Whole.Ctx E g m₀ ins outs t) :
    WP isa (.block [.store (VG.Impl.Ed25519.X86.Whole.at_ 8) .edx]) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ Whole.slots E u 2 = t.gpr .edx ∧
      (∀ j < 6, j ≠ 2 → Whole.slots E u j = Whole.slots E t j) ∧ u.gpr = t.gpr := by
  have hf := hk.frame
  have ea : addr E 8 = E.setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega)
  refine wp_stm (b := .esp) (o := 8) hc.esp ?_ fun u m => WP.block_nil ?_
  · rw [ea, hc.wr]; exact ⟨Whole.FR E, List.mem_cons_self, Offset.contains_base _ (by decide) (by decide)⟩
  have hfr : Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem := by
    rw [m.mem, ea]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨hc.of_frame m.rd m.wr (by rw [m.gpr]) (fun r _ _ => by rw [m.gpr]) hfr
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (Region.sub_prefix (by decide))), hfr, ?_,
    fun j hj h2 => ?_, m.gpr⟩
  · show u.mem.readW (E.setWidth 64 + BitVec.ofNat 64 8) 32 = _
    rw [m.mem, ea]; exact Mem.readW_writeW_self32 _ _ _
  · show u.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = t.mem.readW _ 32
    rw [m.mem, ea, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]

omit hk in
/-- `mov edx, eax`. -/
theorem keep_ok (hc : Whole.Ctx E g m₀ ins outs t) {is : List Instr} {Q : State → Prop}
    (k : ∀ s, Whole.Ctx E g m₀ ins outs s → s.mem = t.mem → s.gpr .edx = t.gpr .eax →
      (∀ r, r ≠ .edx → s.gpr r = t.gpr r) → WP isa (.block is) s Q) :
    WP isa (.block (.mov .edx (.reg .eax) :: is)) t Q :=
  wp_mov fun s v => k s (hc.of_frame v.rd v.wr (v.other _ (by decide))
    (fun r hr _ => v.other r (by rintro rfl; simp [calleeSaved] at hr)) (ws := [])
    (by rw [v.mem]; exact Frame.refl _ _) (fun _ h => nomatch h)) v.mem v.gpr v.other

/-- A call's outgoing argument `j`, from its slot. -/
theorem slot_arg (hc : Whole.Ctx E g m₀ ins outs t) {j : Nat} (hj : j < 6) {v : BitVec 32}
    (h : Whole.slots E t j = v) : arg t.callEntry j = v :=
  (hk.call_arg hc hj).trans h

/-- `mov edx, eax`, a set-up, and `mov [esp + 8], edx`: a call's arguments,
the third the position the previous call returned. -/
theorem nsetup_ok (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {vs : List Value}
    (hn : vs.length ≤ 6) (hv : ∀ v ∈ vs, Whole.valid n v) {pos : Nat} (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (.mov .edx (.reg .eax) :: VG.Impl.Ed25519.X86.Whole.setup 0 vs ++ ([.store (VG.Impl.Ed25519.X86.Whole.at_ 8) .edx] : List Instr))) t fun w =>
      Whole.Ctx E g m₀ ins outs w ∧ Frame [⟨E.setWidth 64, 24⟩] t.mem w.mem ∧
      Whole.slots E w 2 = BitVec.ofNat 32 pos ∧
      ∀ j (hj : j < vs.length), j ≠ 2 → Whole.slots E w j = VG.Proof.Ed448.X86.Shake.argVal E val (vs[j]'hj) := by
  rw [WP.block_append_iff]
  refine VG.Proof.Ed448.X86.Shake.Kit.keep_ok hc fun s1 hc1 m1 e1 _ => ?_
  refine WP.mono (hk.setup_ok hc1 ha hn hv) fun u ⟨hu, hm, hs, hreg⟩ => ?_
  refine WP.mono (hk.store2_ok hu) fun w ⟨hw, hm2, h2, hs', _⟩ =>
    ⟨hw, by rw [m1] at hm; exact hm.trans hm2, by rw [h2, hreg .edx (by decide), e1, hpos],
      fun j hj h => (hs' j (by omega) h).trans (hs j hj)⟩

/-! ## Absorptions -/

/-- An absorption's arguments, from position 0. -/
theorem first_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) :
    WP isa (.block (firstArgs sc src len)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ VG.Proof.Ed448.X86.Shake.AbsSlots E scr 0 (VG.Proof.Ed448.X86.Shake.argVal E val src) (VG.Proof.Ed448.X86.Shake.argVal E val len) u := by
  unfold firstArgs
  refine WP.mono (hk.setup_ok hc ha (by simp) ?_) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, vs, vl, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp)
  have a1 := hs 1 (by simp)
  have a2 := hs 2 (by simp)
  have a3 := hs 3 (by simp)
  have a4 := hs 4 (by simp)
  have a5 := hs 5 (by simp)
  simp only [VG.Proof.Ed448.X86.Shake.argVal_const, VG.Proof.Ed448.X86.Shake.argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  exact ⟨a0, a1, a2, a3, a4, a5⟩

/-- An absorption's arguments, from the position the previous one returned. -/
theorem next_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {pos : Nat}
    (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (nextArgs sc src len)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos (VG.Proof.Ed448.X86.Shake.argVal E val src) (VG.Proof.Ed448.X86.Shake.argVal E val len) u := by
  unfold nextArgs
  refine WP.mono (hk.nsetup_ok hc ha (by simp) ?_ hpos) fun u ⟨hu, hm, h2, hs⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, vs, vl, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp) (by decide)
  have a1 := hs 1 (by simp) (by decide)
  have a3 := hs 3 (by simp) (by decide)
  have a4 := hs 4 (by simp) (by decide)
  have a5 := hs 5 (by simp) (by decide)
  simp only [VG.Proof.Ed448.X86.Shake.argVal_const, VG.Proof.Ed448.X86.Shake.argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a3 a4 a5
  exact ⟨a0, a1, h2, a3, a4, a5⟩

/-- An absorption's call, from its arguments. -/
theorem absorb_slots (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos P N t)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) :
    WP isa (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N.toNat)) ∧
      v.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136) :=
  hk.absorb_call hc hp hcov hd hfit (hk.slot_arg hc (by decide) hs.a0) (hk.slot_arg hc (by decide) hs.a1)
    (hk.slot_arg hc (by decide) hs.a2) (hk.slot_arg hc (by decide) hs.a3) (hk.slot_arg hc (by decide) hs.a4)
    (hk.slot_arg hc (by decide) hs.a5)

/-- What an absorption's call needs, for its constant time. -/
def abs_ready (hc : Whole.Ctx E g m₀ ins outs t) {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hs : VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos P N t)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) : Whole.CallReady Proof.Sha3.absorbX86 E ins outs t :=
  ⟨VG.Proof.Ed448.X86.Shake.Kit.absRd ⟨P.setWidth 64, N.toNat⟩, VG.Proof.Ed448.X86.Shake.Kit.absWr E scr,
    hk.abs_pre hc hp hd hfit (hk.slot_arg hc (by decide) hs.a0) (hk.slot_arg hc (by decide) hs.a1)
      (hk.slot_arg hc (by decide) hs.a2) (hk.slot_arg hc (by decide) hs.a3) (hk.slot_arg hc (by decide) hs.a4)
      (hk.slot_arg hc (by decide) hs.a5), hk.abs_covers hcov, hk.abs_writes⟩

/-- The first absorption, of `N` bytes at `P`, from position 0 of an empty state. -/
theorem first_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.X86.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 []) :
    WP isa (absorb (firstArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (Spec.Sha3.bytesAt t.mem (P.setWidth 64) N) ∧
      v.gpr .eax = BitVec.ofNat 32 (N % 136) := by
  unfold absorb callWith
  refine WP.seq (WP.mono (hk.first_setup hc ha hsc vs vl) fun u ⟨hu, hm, hs⟩ => ?_)
  subst hP hN
  have hrd := VG.Proof.Ed448.X86.Shake.repr_frame hm hk.state_args hr
  refine WP.mono (hk.absorb_slots hu (by decide) hs hcov hd hfit)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, (VG.Proof.Ed448.X86.Shake.Kit.args_frame hm).trans hf, ?_, by rw [h0v, Nat.zero_add]⟩
  have e := VG.Proof.Ed448.X86.Shake.sframe_bytes (D := ⟨(VG.Proof.Ed448.X86.Shake.argVal E val src).setWidth 64, (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat⟩) hm (VG.Proof.Ed448.X86.Shake.Kit.data_args hd)
    (by change (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat ≤ 2 ^ 64; omega)
  have h := hrv [] hrd rfl
  rw [List.nil_append, e] at h
  exact h

/-- An absorption of `N` bytes at `P`, at the position the previous one
returned. -/
theorem next_abs (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.X86.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg)
    (hpos : t.gpr .eax = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs sc src len)) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (scr.setWidth 64) 136 (msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N) ∧
      v.gpr .eax = BitVec.ofNat 32 ((msg ++ Spec.Sha3.bytesAt t.mem (P.setWidth 64) N).length % 136) := by
  unfold absorb callWith
  refine WP.seq (WP.mono (hk.next_setup hc ha hsc vs vl hpos) fun u ⟨hu, hm, hs⟩ => ?_)
  subst hP hN
  have hrd := VG.Proof.Ed448.X86.Shake.repr_frame hm hk.state_args hr
  have e := VG.Proof.Ed448.X86.Shake.sframe_bytes (D := ⟨(VG.Proof.Ed448.X86.Shake.argVal E val src).setWidth 64, (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat⟩) hm (VG.Proof.Ed448.X86.Shake.Kit.data_args hd)
    (by change (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat ≤ 2 ^ 64; omega)
  refine WP.mono (hk.absorb_slots hu (Nat.mod_lt _ (by decide)) hs hcov hd hfit)
    fun v ⟨hv, hf, hrv, h0v⟩ => ⟨hv, (VG.Proof.Ed448.X86.Shake.Kit.args_frame hm).trans hf, ?_, ?_⟩
  · have h := hrv msg hrd rfl
    rw [e] at h
    exact h
  · rw [h0v, Nat.mod_add_mod, List.length_append]
    simp only [Spec.Sha3.bytesAt, List.length_map, List.length_range]

/-! ## `pad` -/

def padWr (E scr : BitVec 32) : List Region := VG.Proof.Ed448.X86.Shake.kWr scr ++ [⟨E.setWidth 64, 20⟩]

theorem pad_pre (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : VG.Proof.Ed448.X86.Shake.PadSlots E scr pos t) :
    Proof.Sha3.padX86.pre (t.callEntry.withRegions [] (VG.Proof.Ed448.X86.Shake.Kit.padWr E scr)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  simp only [Proof.Sha3.padX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, hk.slot_arg hc (by decide) hs.a0,
    hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a4,
    ab, VG.Proof.Ed448.X86.Shake.Kit.padWr, VG.Proof.Ed448.X86.Shake.kWr, List.cons_append, List.nil_append]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨trivial, trivial, hk.state_scratch,
    VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    by have := hk.nc; omega, hk.scr_fit, by omega, by omega, by decide, ?_⟩
  rw [hpn]; exact hp

theorem pad_covers : Covers ([] ++ VG.Proof.Ed448.X86.Shake.Kit.padWr E scr) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.X86.Shake.covers_of fun r hr => ?_
  rcases List.mem_append.mp (List.nil_append _ ▸ hr) with hr | hr
  · exact hk.kWr_covered r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_within E (by decide))

theorem pad_writes : ∀ r ∈ VG.Proof.Ed448.X86.Shake.Kit.padWr E scr, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hk.kWr_writes r hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_within E (by decide))

omit hk in
theorem padWr_lo : ∀ r ∈ VG.Proof.Ed448.X86.Shake.Kit.padWr E scr, Region.Sub r (VG.Proof.Ed448.X86.Shake.Lo E) ∨ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr hr
  · rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.Ed448.X86.Shake.args_lo E (by decide))

/-- The padding's arguments, at the position the last absorption returned. -/
theorem pad_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {pos : Nat} (hpos : t.gpr .eax = BitVec.ofNat 32 pos) :
    WP isa (.block (padArgs sc)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ VG.Proof.Ed448.X86.Shake.PadSlots E scr pos u := by
  unfold padArgs
  refine WP.mono (hk.nsetup_ok hc ha (by simp) ?_ hpos) fun u ⟨hu, hm, h2, hs⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, trivial, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp) (by decide)
  have a1 := hs 1 (by simp) (by decide)
  have a3 := hs 3 (by simp) (by decide)
  have a4 := hs 4 (by simp) (by decide)
  simp only [VG.Proof.Ed448.X86.Shake.argVal_const, VG.Proof.Ed448.X86.Shake.argVal_caller, hsc.val, List.getElem_cons_zero, List.getElem_cons_succ,
    BitVec.add_zero] at a0 a1 a3 a4
  exact ⟨a0, a1, h2, a3, a4⟩

theorem pad_call (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : VG.Proof.Ed448.X86.Shake.PadSlots E scr pos t) :
    WP isa (.call Spec.Sha3.padScratchApi.name Impl.Sha3.X86.Stream.pad) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      ∀ msg, Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg → pos = msg.length % 136 →
        stateAt v.mem (scr.setWidth 64) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  have hpn : (BitVec.ofNat 32 pos).toNat = pos := by rw [BitVec.toNat_ofNat]; omega
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Pad.pad_verified.1 VG.Proof.Ed448.X86.Shake.pad_nosp
    (by rw [VG.Proof.Ed448.X86.Shake.pad_stack]; decide) (hk.pad_pre hc hp hs) hk.pad_covers
    hk.pad_writes fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, hk.call_frame hf VG.Proof.Ed448.X86.Shake.Kit.padWr_lo, fun msg hr hpos => ?_⟩
  simp only [Proof.Sha3.padX86, State.withRegions_mem, arg_withRegions, hm₂] at hpost
  rw [hk.slot_arg hc (by decide) hs.a0, hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2,
    hk.slot_arg hc (by decide) hs.a3, hpn] at hpost
  exact hpost msg (hk.entry_repr hc hr) hpos

def pad_ready (hc : Whole.Ctx E g m₀ ins outs t) {pos : Nat} (hp : pos < 136) (hs : VG.Proof.Ed448.X86.Shake.PadSlots E scr pos t) :
    Whole.CallReady Proof.Sha3.padX86 E ins outs t :=
  ⟨[], VG.Proof.Ed448.X86.Shake.Kit.padWr E scr, hk.pad_pre hc hp hs, hk.pad_covers, hk.pad_writes⟩

theorem pad_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (scr.setWidth 64) 136 msg)
    (hpos : t.gpr .eax = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (pad sc) t fun v => Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      stateAt v.mem (scr.setWidth 64) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  unfold pad callWith
  refine WP.seq (WP.mono (hk.pad_setup hc ha hsc hpos) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (hk.pad_call hu (Nat.mod_lt _ (by decide)) hs) fun v ⟨hv, hf, hp⟩ =>
    ⟨hv, (VG.Proof.Ed448.X86.Shake.Kit.args_frame hm).trans hf, hp msg (VG.Proof.Ed448.X86.Shake.repr_frame hm hk.state_args hr) rfl⟩

/-! ## `squeeze` -/

def sqzWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨scr.setWidth 64, 200⟩, VG.Proof.Ed448.X86.Shake.fr E d 114, ⟨(scr + BitVec.ofNat 32 KSCR).setWidth 64, 640⟩, ⟨E.setWidth 64, 24⟩]

theorem sqz_pre (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : VG.Proof.Ed448.X86.Shake.SqzSlots E scr d t) :
    Proof.Sha3.squeezeX86.pre (t.callEntry.withRegions [] (VG.Proof.Ed448.X86.Shake.Kit.sqzWr E scr d)) := by
  have ab : ∀ rd wr, argAddr (t.callEntry.withRegions rd wr) 0 = E.setWidth 64 :=
    Whole.arg_base hc.esp
  have fa := hk.fr_addr (d := d) (by omega)
  simp only [Proof.Sha3.squeezeX86, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, hk.slot_arg hc (by decide) hs.a0,
    hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a3,
    hk.slot_arg hc (by decide) hs.a4, hk.slot_arg hc (by decide) hs.a5, ab, VG.Proof.Ed448.X86.Shake.Kit.sqzWr, fa]
  have lk := hk.lo_kWr
  have e4 := hk.esp4
  have hb := hk.below
  have hf := hk.frame
  have so : ∀ r ∈ VG.Proof.Ed448.X86.Shake.kWr scr, (VG.Proof.Ed448.X86.Shake.fr E d 114).Disjoint r := fun r hr => (hk.fr_scr hd).sub_right (hk.kWr_sub r hr).sub
  have lo := VG.Proof.Ed448.X86.Shake.lo_fr E h24 hd
  refine ⟨trivial, rfl, (so _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)).symm, hk.state_scratch, so _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr),
    VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), Offset.base_disjoint _ h24 (by omega),
    VG.Proof.Ed448.X86.Shake.Kit.args_disj (by decide) (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.ret_disj lo, hk.ret_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), hk.stk_disj lo, hk.stk_disj (lk _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)),
    by have := hk.nc; omega, hk.fr_fit hd, hk.scr_fit, by omega, by omega, by decide, by decide⟩

theorem sqz_writes {d : Nat} (hd : d + 114 ≤ 256) :
    ∀ r ∈ VG.Proof.Ed448.X86.Shake.Kit.sqzWr E scr d, Whole.Within r (Whole.FR E) ∨ ∃ R ∈ outs, Whole.Within r R := by
  intro r hr
  simp only [VG.Proof.Ed448.X86.Shake.Kit.sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hk.kWr_writes _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)
  · exact .inl (VG.Proof.Ed448.X86.Shake.frame_within E hd)
  · exact hk.kWr_writes _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)
  · exact .inl (VG.Proof.Ed448.X86.Shake.args_within E (by decide))

theorem sqz_covers {d : Nat} (hd : d + 114 ≤ 256) :
    Covers ([] ++ VG.Proof.Ed448.X86.Shake.Kit.sqzWr E scr d) (ins ++ Whole.FR E :: outs) := by
  refine VG.Proof.Ed448.X86.Shake.covers_of fun r hr => ?_
  rw [List.nil_append] at hr
  rcases hk.sqz_writes hd r hr with h | ⟨R, hR, h⟩
  · exact .inl h
  · exact .inr ⟨R, List.mem_append_right _ hR, h⟩

theorem sqz_setup (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    (d : Nat) :
    WP isa (.block (sqzArgs sc d)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [⟨E.setWidth 64, 24⟩] t.mem u.mem ∧ VG.Proof.Ed448.X86.Shake.SqzSlots E scr d u := by
  unfold sqzArgs
  refine WP.mono (hk.setup_ok hc ha (by simp) ?_) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  · simp only [List.forall_mem_cons]
    exact ⟨hsc.valid 0, trivial, trivial, trivial, trivial, hsc.valid KSCR, fun _ h => nomatch h⟩
  have a0 := hs 0 (by simp)
  have a1 := hs 1 (by simp)
  have a2 := hs 2 (by simp)
  have a3 := hs 3 (by simp)
  have a4 := hs 4 (by simp)
  have a5 := hs 5 (by simp)
  simp only [VG.Proof.Ed448.X86.Shake.argVal_const, VG.Proof.Ed448.X86.Shake.argVal_frame, VG.Proof.Ed448.X86.Shake.argVal_caller, hsc.val, List.getElem_cons_zero,
    List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2 a3 a4 a5
  exact ⟨a0, a1, a2, a3, a4, a5⟩

theorem sqz_call (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : VG.Proof.Ed448.X86.Shake.SqzSlots E scr d t) :
    WP isa (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.X86.Stream.squeeze) t fun v =>
      Whole.Ctx E g m₀ ins outs v ∧ Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.fr E d 114 :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.bytesAt v.mem (E.setWidth 64 + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (scr.setWidth 64)) 0 114 := by
  have hst : stateAt t.callEntry.mem (scr.setWidth 64) = stateAt t.mem (scr.setWidth 64) :=
    VG.Proof.Ed448.X86.Shake.state_frame (Whole.callEntry_frame t) (fun r hr => by
      rw [List.mem_singleton.mp hr, hc.esp]
      exact ((hk.lo_kWr _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)).sub_left (VG.Proof.Ed448.X86.Shake.below4_lo hk.below)).symm)
  refine Whole.call_ok hc hk.below Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1 VG.Proof.Ed448.X86.Shake.squeeze_nosp
    (by rw [VG.Proof.Ed448.X86.Shake.squeeze_stack]; decide) (hk.sqz_pre hc h24 hd hs) (hk.sqz_covers hd)
    (hk.sqz_writes hd) fun v hv hf _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, ?_, ?_⟩
  · refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [VG.Proof.Ed448.X86.Shake.Kit.sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (VG.Proof.Ed448.X86.Shake.kWr_state scr)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (VG.Proof.Ed448.X86.Shake.kWr_scratch scr)), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self, VG.Proof.Ed448.X86.Shake.args_lo E (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨VG.Proof.Ed448.X86.Shake.Lo E, List.mem_cons_self, VG.Proof.Ed448.X86.Shake.below_lo hk.below⟩
  · have h := hpost.1
    simp only [State.withRegions_mem, arg_withRegions, hm₂, hk.slot_arg hc (by decide) hs.a0,
      hk.slot_arg hc (by decide) hs.a1, hk.slot_arg hc (by decide) hs.a2, hk.slot_arg hc (by decide) hs.a3,
      hk.slot_arg hc (by decide) hs.a4, hk.fr_addr (d := d) (by omega), hst] at h
    exact h

def sqz_ready (hc : Whole.Ctx E g m₀ ins outs t) {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256)
    (hs : VG.Proof.Ed448.X86.Shake.SqzSlots E scr d t) : Whole.CallReady Proof.Sha3.squeezeX86 E ins outs t :=
  ⟨[], VG.Proof.Ed448.X86.Shake.Kit.sqzWr E scr d, hk.sqz_pre hc h24 hd hs, hk.sqz_covers hd, hk.sqz_writes hd⟩

theorem sqz_step (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
    {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) :
    WP isa (squeeze sc d) t fun v => Whole.Ctx E g m₀ ins outs v ∧
      Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.fr E d 114 :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem v.mem ∧
      Spec.Sha3.bytesAt v.mem (E.setWidth 64 + BitVec.ofNat 64 d) 114 =
        Spec.Sha3.squeezeFrom 136 (stateAt t.mem (scr.setWidth 64)) 0 114 := by
  unfold squeeze callWith
  refine WP.seq (WP.mono (hk.sqz_setup hc ha hsc d) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (hk.sqz_call hu h24 hd hs) fun v ⟨hv, hf, hb⟩ => ⟨hv, ?_, ?_⟩
  · have h1 : Frame (VG.Proof.Ed448.X86.Shake.Lo E :: VG.Proof.Ed448.X86.Shake.fr E d 114 :: VG.Proof.Ed448.X86.Shake.kWr scr) t.mem u.mem := hm.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨VG.Proof.Ed448.X86.Shake.Lo E, List.mem_cons_self, VG.Proof.Ed448.X86.Shake.args_lo E (by decide)⟩
    exact h1.trans hf
  · rw [hb, VG.Proof.Ed448.X86.Shake.state_frame hm hk.state_args]

end Kit

end VG.Proof.Ed448.X86.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.Header`. -/
section

/-!
# Ed448 on x86 (32-bit): the header of `dom4`

`Kit.hdr_ok`: the block `hdrAt j off` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the
first ten bytes of `dom4(0, context)`, in the frame at `off`, `ctxlen` the
caller's argument `j` (below 256): three little-endian words, the last
`ctxlen · 2^8`, by eight doublings (`hdr_bytes`). It writes nothing else.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (at_)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR)

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (c : BitVec 32) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 c.toNat]

theorem bytes4 (m : Mem) (p : Addr) : Spec.Ed448.bytesAt m p 4 = Proof.X25519.leBytes 4 (m.readW p 32).toNat := by
  rw [Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_leBytes]; simp [Mem.readW]

/-- The bytes of the three words of the header, the last `w = ctxlen · 2^8`. -/
theorem hdr_bytes (m : Mem) (p : Addr) (c w : BitVec 32) (hw : w.toNat = c.toNat * 256) :
    Spec.Ed448.bytesAt (((m.writeW (p + BitVec.ofNat 64 8) w).writeW p 0x45676953#32).writeW
      (p + BitVec.ofNat 64 4) 0x38343464#32) p 10 = VG.Proof.Ed448.X86.Shake.hdrBytes c := by
  generalize hM : ((m.writeW (p + BitVec.ofNat 64 8) w).writeW p 0x45676953#32).writeW
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
  have h2 : M.readW (p + BitVec.ofNat 64 8) 32 = w := by
    rw [← hM, Mem.readW_writeW_sep s84 (by decide), Mem.readW_writeW_sep s80 (by decide),
      Mem.readW_writeW_self32]
  have e10 : Spec.Ed448.bytesAt M p 10 = Spec.Ed448.bytesAt M p 4 ++
      (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 4) 4 ++ (Spec.Ed448.bytesAt M (p + BitVec.ofNat 64 8) 4).take 2) := by
    have a := Proof.X25519.bytesAt_add M p 4 6
    have b := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 4) 4 2
    have b' := Proof.X25519.bytesAt_add M (p + BitVec.ofNat 64 8) 2 2
    have l := Proof.X25519.length_bytesAt M (p + BitVec.ofNat 64 8) 2
    rw [Offset.add_add] at b b'
    simp only [Proof.Ed448.bytesAt_eq]
    rw [a, show (6 : Nat) = 4 + 2 from rfl, b, show (4 : Nat) = 2 + 2 from rfl, b', List.take_left' l]
  rw [e10, VG.Proof.Ed448.X86.Shake.bytes4, VG.Proof.Ed448.X86.Shake.bytes4, VG.Proof.Ed448.X86.Shake.bytes4, h0, h1, h2, hw]
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

theorem hdr_len (c : BitVec 32) : (VG.Proof.Ed448.X86.Shake.hdrBytes c).length = 10 := by simp [VG.Proof.Ed448.X86.Shake.hdrBytes]

/-- The input of a hash, as the specification puts it together. -/
theorem dom4_eq (c : BitVec 32) (ctx x : List Byte) (hc : ctx.length = c.toNat) :
    Spec.Ed448.dom4 0 ctx ++ x = VG.Proof.Ed448.X86.Shake.hdrBytes c ++ ctx ++ x := by
  simp [Spec.Ed448.dom4, VG.Proof.Ed448.X86.Shake.hdrBytes, hc]

/-- `k` doublings of `eax`. -/
theorem dbl_ok {s : State} : ∀ k, WP isa (.block (List.replicate k (.alu .add .eax (.reg .eax)))) s fun u =>
    u.gpr .eax = BitVec.ofNat 32 (2 ^ k * (s.gpr .eax).toNat) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
      u.wr = s.wr ∧ ∀ r, r ≠ .eax → u.gpr r = s.gpr r
  | 0 => WP.block_nil ⟨by simp, rfl, rfl, rfl, fun _ _ => rfl⟩
  | k + 1 => by
    rw [List.replicate_succ', WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.X86.Shake.dbl_ok k) fun u ⟨h0, hm, hrd, hwr, ho⟩ => wp_add fun s' v _ => WP.block_nil
      ⟨?_, v.mem.trans hm, v.rd.trans hrd, v.wr.trans hwr, fun r hr => (v.other r hr).trans (ho r hr)⟩
    rw [v.gpr, h0, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.two_mul]

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.hdr_ok (hk : VG.Proof.Ed448.X86.Shake.Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₀)
    {j off : Nat} (hj : j < n) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 256) :
    WP isa (.block (hdrAt j off)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [VG.Proof.Ed448.X86.Shake.fr E off 12] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (E.setWidth 64 + BitVec.ofNat 64 off) 10 = VG.Proof.Ed448.X86.Shake.hdrBytes (val j) ∧
      ∀ r, r ≠ .eax → u.gpr r = t.gpr r := by
  have hf := hk.frame
  have ea : ∀ k ≤ 8, addr E (off + k) = E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k := fun k hk' => by
    rw [addr_eq (by omega), Offset.add_add]
  have hw : ∀ k ≤ 8, InRegions t.wr (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 := fun k hk' => by
    rw [Offset.add_add]
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have e0 : E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 0 = E.setWidth 64 + BitVec.ofNat 64 off :=
    BitVec.add_zero _
  unfold hdrAt
  rw [List.singleton_append, List.cons_append]
  refine VG.X86.Wp.wp_ldm (b := .esp) hc.esp (hk.readable hc j hj) fun s1 v1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.X86.Shake.dbl_ok 8) fun s2 ⟨h2, m2, rd2, wr2, o2⟩ => ?_
  have esp2 : s2.gpr .esp = E := by rw [o2 _ (by decide), v1.other _ (by decide), hc.esp]
  have hwr2 : s2.wr = t.wr := by rw [wr2, v1.wr]
  refine VG.X86.Wp.wp_stm (b := .esp) (o := off + 8) esp2 (by rw [ea 8 (by omega), hwr2]; exact hw 8 (by omega))
    fun s3 v3 => wp_movi fun s4 v4 => ?_
  refine VG.X86.Wp.wp_stm (b := .esp) (o := off) (by rw [v4.other _ (by decide), v3.gpr, esp2])
    (by rw [v4.wr, v3.wr, hwr2, ← Nat.add_zero off, ea 0 (by omega)]; exact hw 0 (by omega))
    fun s5 v5 => wp_movi fun s6 v6 => ?_
  refine VG.X86.Wp.wp_stm (b := .esp) (o := off + 4)
    (by rw [v6.other _ (by decide), v5.gpr, v4.other _ (by decide), v3.gpr, esp2])
    (by rw [v6.wr, v5.wr, v4.wr, v3.wr, hwr2, ea 4 (by omega)]; exact hw 4 (by omega))
    fun u vu => WP.block_nil ?_
  have w0 : s2.gpr .eax = BitVec.ofNat 32 (2 ^ 8 * (val j).toNat) := by
    rw [h2, v1.gpr, hk.arg_word hc hj, ha j hj]
  have hm : u.mem = ((t.mem.writeW (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 8)
      (BitVec.ofNat 32 (2 ^ 8 * (val j).toNat))).writeW
      (E.setWidth 64 + BitVec.ofNat 64 off) 0x45676953#32).writeW
      (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 4) 0x38343464#32 := by
    rw [vu.mem, v6.gpr, v6.mem, v5.mem, v4.gpr, v4.mem, v3.mem, w0, m2, v1.mem, ea 8 (by omega), ea 4 (by omega),
      ← Nat.add_zero off, ea 0 (by omega), e0]
    rfl
  have hfr : Frame [VG.Proof.Ed448.X86.Shake.fr E off 12] t.mem u.mem := by
    rw [hm]
    have c : ∀ k ≤ 8, (VG.Proof.Ed448.X86.Shake.fr E off 12).Contains (E.setWidth 64 + BitVec.ofNat 64 off + BitVec.ofNat 64 k) 4 :=
      fun k hk' => Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 8 (by omega))).writeW
      (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ (c 4 (by omega))
    have h := c 0 (by omega)
    rw [e0] at h
    exact h
  have gp : ∀ r, r ≠ .eax → u.gpr r = t.gpr r := fun r hr => by
    rw [vu.gpr, v6.other r hr, v5.gpr, v4.other r hr, v3.gpr, o2 r hr, v1.other r hr]
  refine ⟨?_, hfr, ?_, gp⟩
  · refine hc.of_frame (by rw [vu.rd, v6.rd, v5.rd, v4.rd, v3.rd, rd2, v1.rd])
      (by rw [vu.wr, v6.wr, v5.wr, v4.wr, v3.wr, hwr2]) (gp _ (by decide))
      (fun r hr _ => gp r (by rintro rfl; simp [calleeSaved] at hr)) hfr ?_
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ ho)
  · rw [hm]
    refine VG.Proof.Ed448.X86.Shake.hdr_bytes _ _ _ _ ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

end VG.Proof.Ed448.X86.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.Prune`. -/
section

/-!
# Ed448 on x86 (32-bit): pruning a hash in place

`Kit.prune_ok`: the block `pruneAt q` clears bits 0–1 of the frame's byte
`q`, sets bit 7 of byte `q + 55` and clears byte `q + 56`, through `eax`;
the 57 bytes at `q` are then `Spec.Ed448.prune` of the 114 there before
(`pruned_value`, by `Proof.Ed448.prune_bytes`). It writes nothing else.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.X86.Wp VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (at_)
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR)
open VG.WriteBytes (writeW8_apply)

/-! ## The bytes -/

theorem bytesAt_split (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = m q :: (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 ++
      [m (q + BitVec.ofNat 64 55), m (q + BitVec.ofNat 64 56)]) := by
  have b1 : Spec.X25519.bytesAt m q 1 = [m q] := by
    simp [Spec.X25519.bytesAt]
  have b2 : ∀ p : Addr, Spec.X25519.bytesAt m p 2 = [m p, m (p + BitVec.ofNat 64 1)] := fun p => by
    simp [Spec.X25519.bytesAt, List.range_succ]
  rw [Proof.Ed448.bytesAt_eq, show 57 = 1 + (54 + 2) from rfl, VG.Proof.X25519.bytesAt_add,
    VG.Proof.X25519.bytesAt_add, b1, b2, Offset.add_add, Offset.add_add]
  rfl

theorem decodeLE_split (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) = (m q).toNat + 256 *
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) + 2 ^ 432 *
        ((m (q + BitVec.ofNat 64 55)).toNat + 256 * (m (q + BitVec.ofNat 64 56)).toNat)) := by
  rw [VG.Proof.Ed448.X86.Shake.bytesAt_split, Spec.Ed448.decodeLE, Proof.Ed448.decodeLE_append]
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  rw [hl, show (256 : Nat) ^ 54 = 2 ^ 432 by decide +kernel]
  simp only [Spec.Ed448.decodeLE, Nat.mul_zero, Nat.add_zero]

theorem bytesAt_take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem pruned_value {m : Mem} {q : Addr} :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt (((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8)) q 57) =
      (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) &&& (2 ^ 448 - 4)) ||| 2 ^ 447 := by
  have ne : ∀ i j, i < 57 → j < 57 → i ≠ j → q + BitVec.ofNat 64 i ≠ q + BitVec.ofNat 64 j :=
    fun i j hi hj h => Offset.add_ofNat_ne q (by omega) (by omega) h
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  have ne0 : ∀ j, 0 < j → j < 57 → q + BitVec.ofNat 64 j ≠ q := fun j h1 h2 e =>
    ne j 0 h2 (by omega) (by omega) (e.trans z.symm)
  generalize hm' : ((m.writeW q (BitVec.ofNat 8 ((m q).toNat &&& 252))).writeW
        (q + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
          (q + BitVec.ofNat 64 56) (0 : BitVec 8) = m'
  have mid : Spec.Ed448.bytesAt m' (q + BitVec.ofNat 64 1) 54 = Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54 := by
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← hm', Offset.add_add, VG.WriteBytes.writeW8_apply, ite_eq_right (ne (1 + i) 56 (by omega) (by omega) (by omega)),
      VG.WriteBytes.writeW8_apply, ite_eq_right (ne (1 + i) 55 (by omega) (by omega) (by omega)), VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne0 (1 + i) (by omega) (by omega))]
  have e0 : m' q = BitVec.ofNat 8 ((m q).toNat &&& 252) := by
    rw [← hm', VG.WriteBytes.writeW8_apply, ite_eq_right (ne0 56 (by omega) (by omega)).symm,
      VG.WriteBytes.writeW8_apply, ite_eq_right (ne0 55 (by omega) (by omega)).symm,
      VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
  have e55 : m' (q + BitVec.ofNat 64 55) = BitVec.ofNat 8 ((m (q + BitVec.ofNat 64 55)).toNat ||| 128) := by
    rw [← hm', VG.WriteBytes.writeW8_apply, ite_eq_right (ne 55 56 (by omega) (by omega) (by omega)),
      VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
  have e56 : m' (q + BitVec.ofNat 64 56) = BitVec.ofNat 8 0 := by
    rw [← hm', VG.WriteBytes.writeW8_apply, ite_eq_left rfl]; rfl
  rw [VG.Proof.Ed448.X86.Shake.decodeLE_split, VG.Proof.Ed448.X86.Shake.decodeLE_split, mid, e0, e55, e56]
  have h0 := (m q).isLt
  have h55 := (m (q + BitVec.ofNat 64 55)).isLt
  have hl : (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54).length = 54 := by simp [Spec.Ed448.bytesAt]
  have hM' := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54)
  rw [hl] at hM'
  have hM : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (q + BitVec.ofNat 64 1) 54) < 2 ^ 432 :=
    Nat.lt_of_lt_of_le hM' (Nat.le_of_eq (by decide +kernel))
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left h0),
    Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 8) h55 (by decide))]
  exact (Proof.Ed448.prune_bytes (b56 := (m (q + BitVec.ofNat 64 56)).toNat) h0 hM h55).symm

/-! ## The instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_ldb {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, State.load8, ea_mk, hb, hin]) (k _ (Upd.setReg _ _ _))

/-- `mov BYTE PTR [b + o], r` -/
theorem wp_stb {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

theorem wp_ori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem and_fc : ∀ x : BitVec 8, (x.setWidth 32 &&& 0xfc#32).setWidth 8 = BitVec.ofNat 8 (x.toNat &&& 252) := by
  decide

theorem or_80 : ∀ x : BitVec 8, (x.setWidth 32 ||| 0x80#32).setWidth 8 = BitVec.ofNat 8 (x.toNat ||| 128) := by
  decide

variable {E scr : BitVec 32} {n : Nat} {ins outs : List Region} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem Kit.prune_ok (hk : VG.Proof.Ed448.X86.Shake.Kit E scr n ins outs) (hc : Whole.Ctx E g m₀ ins outs t) {q : Nat}
    (hq : q + 57 ≤ 256) :
    WP isa (.block (pruneAt q)) t fun u => Whole.Ctx E g m₀ ins outs u ∧
      Frame [VG.Proof.Ed448.X86.Shake.fr E q 57] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (E.setWidth 64 + BitVec.ofNat 64 q) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (E.setWidth 64 + BitVec.ofNat 64 q) 114) ∧
      ∀ r, r ≠ .eax → u.gpr r = t.gpr r := by
  have hf := hk.frame
  have ea : ∀ k < 57, addr E (q + k) = E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k := fun k hk' => by
    rw [addr_eq (by omega), Offset.add_add]
  have hw : ∀ k < 57, InRegions t.wr (E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 := fun k hk' => by
    rw [Offset.add_add]
    exact hc.writable_frame (Offset.contains_base _ (by omega) (by omega))
  have hr : ∀ k < 57, InRegions (t.rd ++ t.wr) (E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 k) 1 :=
    fun k hk' => by
      obtain ⟨R, hR, hcon⟩ := hw k hk'
      exact ⟨R, List.mem_append_right _ hR, hcon⟩
  have e0 : addr E q = E.setWidth 64 + BitVec.ofNat 64 q := by
    rw [← Nat.add_zero q, ea 0 (by omega), Nat.add_zero, BitVec.add_zero]
  have z : E.setWidth 64 + BitVec.ofNat 64 q + BitVec.ofNat 64 0 = E.setWidth 64 + BitVec.ofNat 64 q :=
    BitVec.add_zero _
  generalize hP : E.setWidth 64 + BitVec.ofNat 64 q = P at ea hw hr e0 z
  unfold pruneAt
  simp only [VG.Impl.Ed25519.X86.Whole.at_]
  refine VG.Proof.Ed448.X86.Shake.wp_ldb (b := .esp) hc.esp (by rw [e0, ← z]; exact hr 0 (by omega)) fun s1 v1 => ?_
  refine wp_andi fun s2 v2 => ?_
  refine VG.Proof.Ed448.X86.Shake.wp_stb (b := .esp) (by rw [v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v2.wr, v1.wr, e0, ← z]; exact hw 0 (by omega)) fun s3 v3 => ?_
  refine VG.Proof.Ed448.X86.Shake.wp_ldb (b := .esp) (by rw [v3.gpr, v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr, ea 55 (by omega)]; exact hr 55 (by omega)) fun s4 v4 => ?_
  refine VG.Proof.Ed448.X86.Shake.wp_ori fun s5 v5 => ?_
  refine VG.Proof.Ed448.X86.Shake.wp_stb (b := .esp) (by rw [v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
                               v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ea 55 (by omega)]; exact hw 55 (by omega)) fun s6 v6 => ?_
  refine wp_movi fun s7 v7 => ?_
  refine VG.Proof.Ed448.X86.Shake.wp_stb (b := .esp) (by rw [v7.other _ (by decide), v6.gpr, v5.other _ (by decide), v4.other _ (by decide),
                               v3.gpr, v2.other _ (by decide), v1.other _ (by decide), hc.esp])
    (by rw [v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr, ea 56 (by omega)]; exact hw 56 (by omega))
    fun u vu => WP.block_nil ?_
  have ne55 : P + BitVec.ofNat 64 55 ≠ P := fun e =>
    Offset.add_ofNat_ne P (a := 55) (b := 0) (by omega) (by omega) (by omega) (e.trans z.symm)
  have al : ∀ s : State, s.gpr Reg8.al.reg = s.gpr .eax := fun _ => rfl
  have r2 : s2.gpr .eax = (t.mem P).setWidth 32 &&& 0xfc#32 := by rw [v2.gpr, v1.gpr, e0]; rfl
  have m3 : s3.mem = t.mem.writeW P (BitVec.ofNat 8 ((t.mem P).toNat &&& 252)) := by
    rw [v3.mem, v2.mem, v1.mem, e0, al, r2, ← VG.Proof.Ed448.X86.Shake.and_fc]
  have r5 : s5.gpr .eax = (t.mem (P + BitVec.ofNat 64 55)).setWidth 32 ||| 0x80#32 := by
    rw [v5.gpr, v4.gpr, ea 55 (by omega), m3, VG.WriteBytes.writeW8_apply, ite_eq_right ne55]; rfl
  have hm : u.mem = ((t.mem.writeW P (BitVec.ofNat 8 ((t.mem P).toNat &&& 252))).writeW
      (P + BitVec.ofNat 64 55) (BitVec.ofNat 8 ((t.mem (P + BitVec.ofNat 64 55)).toNat ||| 128))).writeW
        (P + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [vu.mem, v7.mem, v6.mem, v5.mem, v4.mem, m3, al, al, v7.gpr, r5, VG.Proof.Ed448.X86.Shake.or_80, ea 55 (by omega),
      ea 56 (by omega)]
    rfl
  have hfr : Frame [VG.Proof.Ed448.X86.Shake.fr E q 57] t.mem u.mem := by
    rw [hm]
    have c : ∀ k < 57, (VG.Proof.Ed448.X86.Shake.fr E q 57).Contains (P + BitVec.ofNat 64 k) 1 := fun k hk' => by
      rw [← hP]; exact Offset.contains_base _ (by omega) (by omega)
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (c 55 (by omega))).writeW (List.mem_singleton_self _) _ (c 56 (by omega))
    have h := c 0 (by omega)
    rw [z] at h
    exact h
  have gp : ∀ r, r ≠ .eax → u.gpr r = t.gpr r := fun r hr => by
    rw [vu.gpr, v7.other r hr, v6.gpr, v5.other r hr, v4.other r hr, v3.gpr, v2.other r hr, v1.other r hr]
  refine ⟨?_, hfr, ?_, gp⟩
  · refine hc.of_frame (by rw [vu.rd, v7.rd, v6.rd, v5.rd, v4.rd, v3.rd, v2.rd, v1.rd])
      (by rw [vu.wr, v7.wr, v6.wr, v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]) (gp _ (by decide))
      (fun r hr _ => gp r (by rintro rfl; simp [calleeSaved] at hr)) hfr ?_
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hq)
  · rw [hm, VG.Proof.Ed448.X86.Shake.pruned_value]
    unfold Spec.Ed448.prune
    rw [VG.Proof.Ed448.X86.Shake.bytesAt_take57]

end VG.Proof.Ed448.X86.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.CT`. -/
section

/-!
# Ed448 on x86 (32-bit): the calls of the sponge functions in constant time

As Ed25519's complete operations on this target: the blocks between the
calls address memory only through `esp` (`block_ct`, given the taint check
of each block, which its operation discharges with `taint_decide`), two runs
from the same pointers, lengths and `esp` set up the same arguments for
every call (`AbsSlots`, …), and each callee is constant time under its own
contract (`call_ct`). The positions the absorptions return, which the next
ones start from, depend only on the lengths.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86 VG.Impl.Ed448.X86.Shake
open VG.Impl.Ed25519.X86.Whole (Value setup at_)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.X86 (Whole.CallReady Whole.Ctx Whole.FR Whole.valid Whole.slots Whole.rel_wp
  Whole.callEx Whole.block_rel)

/-- Both runs in the frame, and `P` of each. -/
abbrev Two (E : BitVec 32) (ins outs : List Region) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem)
    (P : State → Prop) (a b : State) :=
  (Whole.Ctx E g₁ m₁ ins outs a ∧ P a) ∧ (Whole.Ctx E g₂ m₂ ins outs b ∧ P b)

variable {E scr : BitVec 32} {n : Nat} {val : Nat → BitVec 32} {ins outs : List Region}
  {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem two_esp {P : State → Prop} {a b : State} (h : VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ P a b) :
    a.gpr .esp = b.gpr .esp := h.1.1.esp.trans h.2.1.esp.symm

/-- A block that addresses memory only through `esp`, with what it does in each run. -/
theorem block_ct {is : List Instr} {P Q : State → Prop} {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block is) hint).isSome = true)
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ P) (.block is) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ Q) :=
  Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ P a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ P b)
    (Whole.block_rel (fun _ _ h => VG.Proof.Ed448.X86.Shake.two_esp h) ht) (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)

/-- A block that addresses memory only through the registers `rs`, equal in
both runs. -/
theorem regs_block_ct {is : List Instr} {P Q : State → Prop} {rs : List Reg}
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr rs) (.block is) hint).isSome = true)
    (he : ∀ a b, VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ P a b → ∀ r ∈ rs, a.gpr r = b.gpr r)
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → P t →
      WP isa (.block is) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ P) (.block is) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ Q) :=
  Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ P a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ P b)
    (RelCT.taint (A := taint) (τr rs) (fun a b h => agree_regs (he a b h)) ht)
    (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)

/-- A call whose arguments (`R`) are the same in both runs, with what it does in each. -/
theorem call_ct {k : Contract isa} {c : Prog isa} {name : String} {R Q : State → Prop}
    (correct : ∀ s, k.pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (ready : ∀ (g : Reg → BitVec 32) (m : Mem) (t : State), Whole.Ctx E g m ins outs t → R t →
      Whole.CallReady k E ins outs t)
    (kp : ∀ a b : State, a.gpr .esp = E → b.gpr .esp = E → R a → R b → ∀ ar aw br bw,
      k.pub (a.callEntry.withRegions ar aw) (b.callEntry.withRegions br bw))
    (h₁ : ∀ t, Whole.Ctx E g₁ m₁ ins outs t → R t →
      WP isa (.call name c) t fun u => Whole.Ctx E g₁ m₁ ins outs u ∧ Q u)
    (h₂ : ∀ t, Whole.Ctx E g₂ m₂ ins outs t → R t →
      WP isa (.call name c) t fun u => Whole.Ctx E g₂ m₂ ins outs u ∧ Q u) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ R) (.call name c) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ Q) := by
  refine Whole.rel_wp (F := fun a => Whole.Ctx E g₁ m₁ ins outs a ∧ R a)
    (F' := fun b => Whole.Ctx E g₂ m₂ ins outs b ∧ R b) ?_ (fun t h => h₁ t h.1 h.2) (fun t h => h₂ t h.1 h.2)
  refine Whole.callEx correct ct fun a b h => ?_
  let ra := ready _ _ a h.1.1 h.1.2
  let rb := ready _ _ b h.2.1 h.2.2
  obtain ⟨ca, wa⟩ := ra.covers_state h.1.1
  obtain ⟨cb, wb⟩ := rb.covers_state h.2.1
  exact ⟨ra.reads, ra.writes, rb.reads, rb.writes, ra.pre, rb.pre,
    kp a b h.1.1.esp h.2.1.esp h.1.2 h.2.2 _ _ _ _, ca, wa, cb, wb, VG.Proof.Ed448.X86.Shake.two_esp h⟩

theorem entry_esp {a b : State} (ea : a.gpr .esp = E) (eb : b.gpr .esp = E) (ar aw br bw : List Region) :
    (a.callEntry.withRegions ar aw).gpr .esp = (b.callEntry.withRegions br bw).gpr .esp := by
  simp only [State.withRegions_gpr, State.callEntry_esp, ea, eb]

theorem AbsSlots.eq {pos : Nat} {P N : BitVec 32} {a b : State} (ha : VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos P N a)
    (hb : VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos P N b) : ∀ i < 6, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm, ha.a5.trans hb.a5.symm]

theorem PadSlots.eq {pos : Nat} {a b : State} (ha : VG.Proof.Ed448.X86.Shake.PadSlots E scr pos a) (hb : VG.Proof.Ed448.X86.Shake.PadSlots E scr pos b) :
    ∀ i < 5, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm]

theorem SqzSlots.eq {d : Nat} {a b : State} (ha : VG.Proof.Ed448.X86.Shake.SqzSlots E scr d a) (hb : VG.Proof.Ed448.X86.Shake.SqzSlots E scr d b) :
    ∀ i < 6, Whole.slots E a i = Whole.slots E b i := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm, ha.a3.trans hb.a3.symm,
    ha.a4.trans hb.a4.symm, ha.a5.trans hb.a5.symm]

namespace Kit

variable (hk : VG.Proof.Ed448.X86.Shake.Kit E scr n ins outs)
include hk

/-- The arguments of two calls, from equal slots. -/
theorem args_eq {a b : State} (ea : a.gpr .esp = E) (eb : b.gpr .esp = E) {k : Nat} (hk6 : k ≤ 6)
    (h : ∀ i < k, Whole.slots E a i = Whole.slots E b i) (ar aw br bw : List Region) :
    ∀ i < k, arg (a.callEntry.withRegions ar aw) i = arg (b.callEntry.withRegions br bw) i := by
  intro i hi
  rw [arg_withRegions, arg_withRegions, VG.Proof.Ed25519.X86.Whole.call_arg ea hk.below hk.frame (by omega),
    VG.Proof.Ed25519.X86.Whole.call_arg eb hk.below hk.frame (by omega)]
  exact h i hi

/-! ## The calls -/

theorem abs_ct {P N : BitVec 32} {pos : Nat} (hp : pos < 136)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N.toNat⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N.toNat⟩)
    (hfit : P.toNat + N.toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.X86.Shake.AbsSlots E scr pos P N))
      (.call Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb)
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 ((pos + N.toNat) % 136)) :=
  VG.Proof.Ed448.X86.Shake.call_ct Proof.Sha3.X86.Stream.Absorb.absorb_verified.1 Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1
    (fun _ _ _ hc hs => hk.abs_ready hc hp hs hcov hd hfit)
    (fun a b ea eb ha hb ar aw br bw => ⟨VG.Proof.Ed448.X86.Shake.entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.absorb_slots hc hp hs hcov hd hfit) fun _ ⟨hv, _, _, he⟩ => ⟨hv, he⟩)
    (fun _ hc hs => WP.mono (hk.absorb_slots hc hp hs hcov hd hfit) fun _ ⟨hv, _, _, he⟩ => ⟨hv, he⟩)

theorem pad_ct {pos : Nat} (hp : pos < 136) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.X86.Shake.PadSlots E scr pos))
      (.call Spec.Sha3.padScratchApi.name Impl.Sha3.X86.Stream.pad) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  VG.Proof.Ed448.X86.Shake.call_ct Proof.Sha3.X86.Stream.Pad.pad_verified.1 Proof.Sha3.X86.Stream.Pad.pad_verified.2.1
    (fun _ _ _ hc hs => hk.pad_ready hc hp hs)
    (fun a b ea eb ha hb ar aw br bw => ⟨VG.Proof.Ed448.X86.Shake.entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.pad_call hc hp hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)
    (fun _ hc hs => WP.mono (hk.pad_call hc hp hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)

theorem sqz_ct {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ (VG.Proof.Ed448.X86.Shake.SqzSlots E scr d))
      (.call Spec.Sha3.squeezeScratchApi.name Impl.Sha3.X86.Stream.squeeze)
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  VG.Proof.Ed448.X86.Shake.call_ct Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1 Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1
    (fun _ _ _ hc hs => hk.sqz_ready hc h24 hd hs)
    (fun a b ea eb ha hb ar aw br bw => ⟨VG.Proof.Ed448.X86.Shake.entry_esp ea eb ar aw br bw,
      hk.args_eq ea eb (by decide) (ha.eq hb) ar aw br bw⟩)
    (fun _ hc hs => WP.mono (hk.sqz_call hc h24 hd hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)
    (fun _ hc hs => WP.mono (hk.sqz_call hc h24 hd hs) fun _ ⟨hv, _⟩ => ⟨hv, trivial⟩)

/-! ## The sponge's steps -/

variable (ha : VG.Proof.Ed448.X86.Shake.Args E n val m₁) (hb : VG.Proof.Ed448.X86.Shake.Args E n val m₂) {sc : Nat} (hsc : VG.Proof.Ed448.X86.Shake.ScrAt n val sc scr)
include ha hb hsc

/-- The state zeroed: `scratch`, the same in both runs, loaded into `eax`,
then the stores through it. -/
theorem zero_ct {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (zeroArgs sc)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (zeroState sc) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) := by
  unfold zeroState
  refine RelCT.block_append (RelCT.seq (R := VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = scr ∧ s.gpr .edx = 0)
    (VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc _ => WP.mono (hk.zeroArgs_ok hc ha hsc) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun _ hc _ => WP.mono (hk.zeroArgs_ok hc hb hsc) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)) ?_)
  refine VG.Proof.Ed448.X86.Shake.regs_block_ct (rs := [.esp, .eax]) (by taint_decide) (fun a b h r hr => ?_)
    (fun _ hc h => WP.mono (hk.zeroStores_step hc h.1 h.2) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc h => WP.mono (hk.zeroStores_step hc h.1 h.2) fun _ h => ⟨h.1, trivial⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.Ed448.X86.Shake.two_esp h
  · exact h.1.2.1.trans h.2.2.1.symm

/-- The first absorption, from position 0. -/
theorem first_ct {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.X86.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (firstArgs sc src len)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs sc src len))
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 (N % 136)) := by
  subst hP hN
  refine RelCT.seq (VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc _ => WP.mono (hk.first_setup hc ha hsc vs vl) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc _ => WP.mono (hk.first_setup hc hb hsc vs vl) fun _ h => ⟨h.1, h.2.2⟩)) ?_
  have h := hk.abs_ct (g₁ := g₁) (g₂ := g₂) (m₁ := m₁) (m₂ := m₂) (by decide : 0 < 136) hcov hd hfit
  rwa [Nat.zero_add] at h

/-- An absorption at the position `pos` the previous one returned. -/
theorem next_ct {src len : Value} (vs : Whole.valid n src) (vl : Whole.valid n len) {P : BitVec 32} {N : Nat}
    (hP : VG.Proof.Ed448.X86.Shake.argVal E val src = P) (hN : (VG.Proof.Ed448.X86.Shake.argVal E val len).toNat = N)
    (hcov : VG.Proof.Ed448.X86.Shake.DataOk E ins outs ⟨P.setWidth 64, N⟩) (hd : VG.Proof.Ed448.X86.Shake.Away E scr ⟨P.setWidth 64, N⟩)
    (hfit : P.toNat + N ≤ 2 ^ 32) {pos : Nat} (hp : pos < 136) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (nextArgs sc src len)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 pos) (absorb (nextArgs sc src len))
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 ((pos + N) % 136)) := by
  subst hP hN
  exact RelCT.seq (VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc h0 => WP.mono (hk.next_setup hc ha hsc vs vl h0) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc h0 => WP.mono (hk.next_setup hc hb hsc vs vl h0) fun _ h => ⟨h.1, h.2.2⟩))
    (hk.abs_ct hp hcov hd hfit)

/-- The padding, at the position `pos` the last absorption returned. -/
theorem padStep_ct {pos : Nat} (hp : pos < 136) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (padArgs sc)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun s => s.gpr .eax = BitVec.ofNat 32 pos) (pad sc)
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  RelCT.seq (VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc h0 => WP.mono (hk.pad_setup hc ha hsc h0) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc h0 => WP.mono (hk.pad_setup hc hb hsc h0) fun _ h => ⟨h.1, h.2.2⟩)) (hk.pad_ct hp)

/-- 114 bytes squeezed into the frame at `d`. -/
theorem sqzStep_ct {d : Nat} (h24 : 24 ≤ d) (hd : d + 114 ≤ 256) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (sqzArgs sc d)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (squeeze sc d) (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  RelCT.seq (VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc _ => WP.mono (hk.sqz_setup hc ha hsc d) fun _ h => ⟨h.1, h.2.2⟩)
    (fun _ hc _ => WP.mono (hk.sqz_setup hc hb hsc d) fun _ h => ⟨h.1, h.2.2⟩)) (hk.sqz_ct h24 hd)

omit hsc in
/-- The header of `dom4` in the frame at `off`. -/
theorem hdr_ct {j off : Nat} (hj : j < n) (hcl : (val j).toNat < 256) (ho : off + 12 ≤ 256)
    {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (hdrAt j off)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt j off))
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc _ => WP.mono (hk.hdr_ok hc ha hj hcl ho) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc _ => WP.mono (hk.hdr_ok hc hb hj hcl ho) fun _ h => ⟨h.1, trivial⟩)

omit ha hb hsc in
/-- The hash at `q` pruned in place. -/
theorem prune_ct {q : Nat} (hq : q + 57 ≤ 256) {hint : VG.Taint.Hint VG.X86.Taint.T}
    (ht : (taint.check (τr [.esp]) (.block (pruneAt q)) hint).isSome = true) :
    RelCT isa (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) (.block (pruneAt q))
      (VG.Proof.Ed448.X86.Shake.Two E ins outs g₁ g₂ m₁ m₂ fun _ => True) :=
  VG.Proof.Ed448.X86.Shake.block_ct ht (fun _ hc _ => WP.mono (hk.prune_ok hc hq) fun _ h => ⟨h.1, trivial⟩)
    (fun _ hc _ => WP.mono (hk.prune_ok hc hq) fun _ h => ⟨h.1, trivial⟩)

end Kit

end VG.Proof.Ed448.X86.Shake

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.X86.Shake.Entry`. -/
section

/-!
# Ed448 on x86 (32-bit): a complete operation's frame, from its caller

A complete operation pushes 64 words (`Impl/Ed25519/X86/PublicKey.lean`'s
frame): `base s` is `esp` after the push, the caller's `n` argument words
(`ARGS s n`) are at `base s + 260`, and the stack the operation uses is the
280 bytes below its return address (`stack_eq`). `push_ctx`: after the push,
`Whole.Ctx` holds of the regions the operation reads and writes; `kit`: the
layout facts the calls need (`Kit`), from its precondition's;
`pop_abi`: after the pop, the callee-saved registers and the return address
are as they were.
-/

namespace VG.Proof.Ed448.X86.Shake

open VG VG.X86
open VG.Proof.Ed25519.X86 (Whole.Ctx Whole.FR Whole.STK Whole.Within)

/-- The frame's base: `esp` after the push of 64 words. -/
abbrev base (s : State) : BitVec 32 := s.gpr .esp - BitVec.ofNat 32 256

/-- The caller's `n` argument words. -/
abbrev ARGS (s : State) (n : Nat) : Region := ⟨argAddr s 0, 4 * n⟩

/-- The return address. -/
abbrev RET (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

theorem whole (r : Region) : Whole.Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

variable {s : State} {n : Nat}

theorem arg_address (s : State) (j : Nat) : addr (VG.Proof.Ed448.X86.Shake.base s) (260 + 4 * j) = argAddr s j := by
  simp only [addr, VG.Proof.Ed448.X86.Shake.base, argAddr]
  rw [show 260 + 4 * j = 256 + (4 + 4 * j) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem args_val (s : State) (n : Nat) : VG.Proof.Ed448.X86.Shake.Args (VG.Proof.Ed448.X86.Shake.base s) n (arg s) s.mem := fun i _ => by
  rw [VG.Proof.Ed448.X86.Shake.arg_address]; rfl

theorem stack_eq (hb : 280 ≤ (s.gpr .esp).toNat) : Whole.STK (VG.Proof.Ed448.X86.Shake.base s) = below (s.gpr .esp) 280 := by
  simp only [Whole.STK, below, VG.Proof.Ed448.X86.Shake.base]
  rw [Taint.sub_setWidth (by omega : 256 ≤ (s.gpr .esp).toNat),
    Taint.sub_setWidth hb, BitVec.sub_sub]
  rfl

theorem base_toNat (hb : 280 ≤ (s.gpr .esp).toNat) : (VG.Proof.Ed448.X86.Shake.base s).toNat = (s.gpr .esp).toNat - 256 :=
  sub_toNat (by omega)

theorem argAddr64 (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {j : Nat} (hj : j < n) :
    argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) :=
  addr_eq (by omega)

theorem args_stack (hb : 280 ≤ (s.gpr .esp).toNat) (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hn : 0 < n) :
    (VG.Proof.Ed448.X86.Shake.ARGS s n).Disjoint (below (s.gpr .esp) 280) := by
  change Region.Disjoint ⟨argAddr s 0, 4 * n⟩ ⟨((s.gpr .esp) - BitVec.ofNat 32 280).setWidth 64, 280⟩
  rw [VG.Proof.Ed448.X86.Shake.argAddr64 ha hn, Taint.sub_setWidth hb]
  exact (Offset.disjoint_below_above _ (m := 280) (a := 4 + 4 * 0) (l := 4 * n) (by omega)).symm

theorem args_contains (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) {j : Nat} (hj : j < n) :
    (VG.Proof.Ed448.X86.Shake.ARGS s n).Contains (argAddr s j) 4 := by
  change (⟨argAddr s 0, 4 * n⟩ : Region).Contains _ _
  rw [VG.Proof.Ed448.X86.Shake.argAddr64 ha (by omega), VG.Proof.Ed448.X86.Shake.argAddr64 ha hj]
  exact Offset.contains _ (by omega) (by omega) (by omega)

/-- The layout facts the calls need, from the precondition's. -/
theorem kit {sc : Nat} {ins outs : List Region} (hb : 280 ≤ (s.gpr .esp).toNat)
    (ha : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32) (hnc : (arg s sc).toNat + 8192 ≤ 2 ^ 32)
    (so : VG.Proof.Ed448.X86.Shake.SCR (arg s sc) ∈ outs) (ko : ∀ R ∈ outs, (below (s.gpr .esp) 280).Disjoint R)
    (io : ∀ r ∈ ins, ∀ R ∈ outs, r.Disjoint R) (is : ∀ r ∈ ins, r.Disjoint (below (s.gpr .esp) 280))
    (hargs : VG.Proof.Ed448.X86.Shake.ARGS s n ∈ ins) : VG.Proof.Ed448.X86.Shake.Kit (VG.Proof.Ed448.X86.Shake.base s) (arg s sc) n ins outs := by
  have hE := VG.Proof.Ed448.X86.Shake.base_toNat hb
  refine ⟨by omega, by omega, hnc, so, fun R hR => VG.Proof.Ed448.X86.Shake.stack_eq hb ▸ ko R hR, fun r hr R hR => ?_,
    fun i hi => ⟨VG.Proof.Ed448.X86.Shake.ARGS s n, hargs, by rw [VG.Proof.Ed448.X86.Shake.arg_address]; exact VG.Proof.Ed448.X86.Shake.args_contains ha hi⟩⟩
  rcases List.mem_append.mp hR with hR | hR
  · exact io r hr R hR
  · rw [List.mem_singleton.mp hR, VG.Proof.Ed448.X86.Shake.stack_eq hb]; exact is r hr

/-- After the push, the frame's invariant holds of the regions the operation
reads (`ins`) and writes (`outs`). -/
theorem push_ctx {ins outs : List Region} (hrd : s.rd = ins) (hwr : s.wr = outs)
    (hb : 280 ≤ (s.gpr .esp).toNat) :
    Whole.Ctx (VG.Proof.Ed448.X86.Shake.base s) s.gpr s.mem ins outs (pushed (List.replicate 64 .eax) s) := by
  have hf := pushed_frame (s := s) (rs := List.replicate 64 .eax) (by simp)
    (by simp only [List.length_replicate]; omega)
  refine ⟨(pushed_rd _ _).trans hrd, ?_, ?_, fun r _ hn => pushed_gpr _ _ hn, ?_⟩
  · rw [pushed_wr, hwr]
    simp only [List.length_replicate]
  · rw [pushed_esp, List.length_replicate]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨Whole.STK (VG.Proof.Ed448.X86.Shake.base s), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
    rw [VG.Proof.Ed448.X86.Shake.stack_eq hb]
    exact below_sub (by simp) hb

/-- After the pop, the callee-saved registers and the return address. -/
theorem pop_abi {ins outs : List Region} {u : State} {q : Reg} (hq : q ∉ calleeSaved)
    (hb : 280 ≤ (s.gpr .esp).toNat)
    (hu : Whole.Ctx (VG.Proof.Ed448.X86.Shake.base s) s.gpr s.mem ins outs u) (hret : ∀ R ∈ outs, (VG.Proof.Ed448.X86.Shake.RET s).Disjoint R) :
    abiPreserved s (popped q (List.replicate 64 Reg.eax).length u) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; exact hq hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := VG.Proof.Ed448.X86.Shake.RET s) (Region.contains_self _ _) ?_ (by decide)
    intro R hR
    rcases List.mem_append.mp hR with hR | hR
    · exact hret R hR
    · rw [List.mem_singleton.mp hR, VG.Proof.Ed448.X86.Shake.stack_eq hb]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hb]
      exact (Offset.below_disjoint _ (by decide)).symm

/-- `abiPreserved` from a state that differs from the entry state only in
registers that are not callee-saved. -/
theorem abi_of {s' u : State} (hs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem)
    (h : abiPreserved s' u) : abiPreserved s u := by
  have he := hs .esp (by simp [calleeSaved])
  refine ⟨fun r hr => (h.1 r hr).trans (hs r hr), ?_⟩
  have := h.2
  rw [he, hm] at this
  exact this

end VG.Proof.Ed448.X86.Shake

end
