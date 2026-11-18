module

public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Verified
import VerifiedGarbage.Proof.MlDsa.X86.PreparedKey
public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintBase
public import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint
meta import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintBase
meta import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/-! ### `MlDsa.X86.Pack.HintUnpackEnd`, which only this module used -/

section

/-! ### `MlDsa.X86.Pack.HintUnpackMain`, which only this module used -/

section

/-! ### `MlDsa.X86.Pack.HintUnpackLoop`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86.Pack.HintUnpack`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the setup

The code follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Pack/Hint.lean`) step by step: after `i` polynomials the spec's state is `PS
s₀ i`, `eax` is its index, or 256 once a check has failed (`idxOf`), and while
no check has failed the words of `h` are its hint (`SR`).

Every register the code branches on or addresses memory with is a function
of the entry state `s₀` through the input `y`, which two runs with the same
public data and leak agree on (`Pub`).

This file: the contract's facts (`Pre`, `Pub`), what holds throughout the
body (`Base`: `h` and the argument slots of `len` and `hlen`, which the
code uses for the count of polynomials left and the address of the next
bound, are all it changes), zeroing `h`, and the setup of the loops.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

namespace Up

section
variable (s₀ : State)
/-- `len`, `hlen`, `k`. -/
abbrev yL : Nat := (arg s₀ 1).toNat
abbrev hL : Nat := (arg s₀ 4).toNat
abbrev K : Nat := yL s₀ - ω s₀
/-- `h`, and the argument slot `i`. -/
abbrev hR : Region := ⟨wA s₀, hL s₀ * 4⟩
abbrev slot (i : Nat) : Region := ⟨argAddr s₀ i, 4⟩
/-- What the body changes. -/
abbrev W : List Region := [hR s₀, slot s₀ 1, slot s₀ 4]
/-- The input. -/
abbrev Y : Array Byte := (bytesAt s₀.mem (rA s₀) (yL s₀)).toArray
abbrev yb (t : Nat) : Nat := ((Y s₀).getD t 0).toNat
/-- The spec's state after `i` polynomials. -/
abbrev PS (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (ω s₀) (Y s₀)) (List.range i) (Array.replicate (K s₀) noHint, 0)
/-- The bound of polynomial `i`. -/
abbrev bnd (i : Nat) : Nat := yb s₀ (ω s₀ + i)
end

/-- The index of a state of the spec, or 256 for a failed check. -/
def idxOf : Option (Array (Vector Bool n) × Nat) → Nat
  | none => 256
  | some st => st.2

/-- Unless a check failed, the words of `h` are the hint, and the index is at
most `ω`. -/
def SR (s₀ : State) (o : Option (Array (Vector Bool n) × Nat)) (m : Mem) : Prop :=
  ∀ st, o = some st → st.2 ≤ ω s₀ ∧ HArr m (wA s₀) (K s₀) st.1

theorem SR.none (s₀ : State) (m : Mem) : SR s₀ none m := fun _ h => nomatch h

theorem SR.congr {s₀ : State} {o : Option (Array (Vector Bool n) × Nat)} {m m' : Mem} (h : SR s₀ o m)
    (hm : ∀ t < 256 * K s₀, coeffAt m' (wA s₀) t = coeffAt m (wA s₀) t) : SR s₀ o m' :=
  fun st e => ⟨(h st e).1, harr_congr (h st e).2 hm⟩

structure Pre (s₀ : State) : Prop extends Lay s₀ (yL s₀) (hL s₀ * 4) where
  par : (ω s₀, K s₀) ∈ hintParams
  le : ω s₀ ≤ yL s₀
  hlen : hL s₀ = 256 * K s₀

theorem Pre.of {s₀ : State} (h : (hintBitUnpackContract X86.abi 16).pre s₀) : Pre s₀ := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18⟩

theorem Pre.facts {s₀ : State} (hp : Pre s₀) :
    4 ≤ K s₀ ∧ K s₀ ≤ 8 ∧ ω s₀ ≤ 80 ∧ ω s₀ + K s₀ = yL s₀ ∧ hL s₀ = 256 * K s₀ := by
  have := mem_hintParams hp.par
  have := hp.le
  have := hp.hlen
  have e : K s₀ = yL s₀ - ω s₀ := rfl
  omega_arith

/-- The public data: `esp`, the arguments and the input. -/
structure Pub (s₀ s₀' : State) : Prop where
  e0 : E0 s₀ = E0 s₀'
  a0 : arg s₀ 0 = arg s₀' 0
  a1 : arg s₀ 1 = arg s₀' 1
  a2 : arg s₀ 2 = arg s₀' 2
  a3 : arg s₀ 3 = arg s₀' 3
  a4 : arg s₀ 4 = arg s₀' 4
  y : Y s₀ = Y s₀'

theorem Pub.of {s₀ s₀' : State} (h : (hintBitUnpackContract X86.abi 16).pub s₀ s₀') : Pub s₀ s₀' := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e, hl, a0, a1, a2, a3, a4⟩ := h
  exact ⟨e, a0, a1, a2, a3, a4, congrArg List.toArray (map_toNat_inj hl)⟩

theorem Pub.eK {s₀ s₀' : State} (h : Pub s₀ s₀') : K s₀ = K s₀' := by
  show (arg s₀ 1).toNat - (arg s₀ 2).toNat = (arg s₀' 1).toNat - (arg s₀' 2).toNat; rw [h.a1, h.a2]
theorem Pub.eω {s₀ s₀' : State} (h : Pub s₀ s₀') : ω s₀ = ω s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [h.a2]
theorem Pub.eyb {s₀ s₀' : State} (h : Pub s₀ s₀') (t : Nat) : yb s₀ t = yb s₀' t := by
  show ((Y s₀).getD t 0).toNat = ((Y s₀').getD t 0).toNat; rw [h.y]
theorem Pub.ePS {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : PS s₀ i = PS s₀' i := by
  show optFold (huPoly (ω s₀) (Y s₀)) (List.range i) (Array.replicate (K s₀) noHint, 0) =
    optFold (huPoly (ω s₀') (Y s₀')) (List.range i) (Array.replicate (K s₀') noHint, 0)
  rw [h.y, h.eω, h.eK]
theorem Pub.ebnd {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : bnd s₀ i = bnd s₀' i := by
  show yb s₀ (ω s₀ + i) = yb s₀' (ω s₀' + i); rw [h.eω, h.eyb]

/-! ## Regions -/

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.sp'; unfold E0 at this; omega_arith)

theorem slot_disj {i j : Nat} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) : (slot s₀ i).Disjoint (slot s₀ j) := by
  rw [slot, slot, hp.argAddr_eq hi, hp.argAddr_eq hj]
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem slot_sub {i : Nat} (hi : i < 5) : Region.Sub (slot s₀ i) (gR s₀) :=
  sub_of_contains (arg_contains (n := 5) hi hp.sp')

theorem h_slot {i : Nat} (hi : i < 5) : (hR s₀).Disjoint (slot s₀ i) := hp.w_g.sub_right (hp.slot_sub hi)

/-- The slots of `y`, `ω` and `h` are apart from `W`. -/
theorem slotW {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : ∀ r ∈ W s₀, (slot s₀ i).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.h_slot hi).symm
  · exact hp.slot_disj hi (by omega_arith) h1
  · exact hp.slot_disj hi (by omega_arith) h4

theorem yW : ∀ r ∈ W s₀, (⟨rA s₀, yL s₀⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.r_w
  · exact hp.r_g.sub_right (hp.slot_sub (by omega_arith))
  · exact hp.r_g.sub_right (hp.slot_sub (by omega_arith))

theorem hW : ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have st := hp.stk_eq
  rcases hr with rfl | rfl | rfl
  · exact ⟨st ▸ hp.stk_w, hp.ret_w⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega_arith)), hp.ret_g.sub_right (hp.slot_sub (by omega_arith))⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega_arith)), hp.ret_g.sub_right (hp.slot_sub (by omega_arith))⟩

/-- A word of `h` is apart from the slots. -/
theorem coeff_slot {t j : Nat} (ht : t < 256 * K s₀) (hj : j < 5) :
    Mem.Sep (coeffAddr (wA s₀) t) 4 (argAddr s₀ j) (32 / 8) := by
  have := hp.facts
  have hc : (hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  exact (hp.h_slot hj).sep hc (Region.contains_self _ _)

theorem slot_coeff {t j : Nat} (ht : t < 256 * K s₀) (hj : j < 5) :
    Mem.Sep (argAddr s₀ j) 4 (coeffAddr (wA s₀) t) (32 / 8) := by
  have := hp.facts
  have hc : (hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega_arith) (by omega_arith)
  exact (hp.h_slot hj).symm.sep (Region.contains_self _ _) hc

theorem coeff_frame {m : Mem} {j : Nat} (hj : j < 5) (v : BitVec 32) :
    ∀ t < 256 * K s₀, coeffAt (m.writeW (argAddr s₀ j) v) (wA s₀) t = coeffAt m (wA s₀) t :=
  fun t ht => Mem.readW_writeW_sep (hp.coeff_slot ht hj) (by decide)

end Pre

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (W s₀) (P0 s₀).mem s.mem

theorem Base.keep {s₀ s s' : State} (h : Base s₀ s) {rs : List Reg} (k : Keep rs s s') (hsp : Reg.esp ∉ rs)
    (hm : Frame (W s₀) s.mem s'.mem) : Base s₀ s' :=
  ⟨(k.gpr hsp).trans h.esp, k.2.1.trans h.rd, k.2.2.trans h.wr, h.frame.trans hm⟩

namespace Base
variable {s₀ s : State} (hp : Pre s₀) (h : Base s₀ s)
include hp h

theorem argw {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [h.frame.readW (Region.contains_self _ _) (hp.slotW hi h1 h4) (by decide)]
  exact hp.P0_argw hi

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := hp.argIn h.rd h.wr hi

theorem argOut {i : Nat} (hi : i < 5) : InRegions s.wr (argAddr s₀ i) 4 := hp.argOut h.wr hi

/-- A byte of `y`. -/
theorem ybyte {t : Nat} (ht : t < yL s₀) : s.mem (rA s₀ + BitVec.ofNat 64 t) = (Y s₀).getD t 0 := by
  rw [hp.r_keep h.frame hp.yW ht, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]

theorem inY {t : Nat} (ht : t < yL s₀) : InRegions (s.rd ++ s.wr) (rA s₀ + BitVec.ofNat 64 t) 1 := by
  have := hp.r_fit
  rw [h.rd, h.wr, pushed_rd, hp.rd]
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem inH {t : Nat} (ht : t < 256 * K s₀) : InRegions s.wr (coeffAddr (wA s₀) t) 4 := by
  have := hp.facts
  have := hp.w_fit
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨hR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

end Base

theorem frame_slot {s₀ : State} {m : Mem} {j : Nat} (hj : j = 1 ∨ j = 4) (v : BitVec 32) :
    Frame (W s₀) m (m.writeW (argAddr s₀ j) v) := by
  rcases hj with rfl | rfl
  · exact (Frame.refl _ _).writeW (r := slot s₀ 1) (by simp) _ (Region.contains_self _ _)
  · exact (Frame.refl _ _).writeW (r := slot s₀ 4) (by simp) _ (Region.contains_self _ _)

theorem frame_coeff {s₀ : State} (hp : Pre s₀) {m : Mem} {t : Nat} (ht : t < 256 * K s₀) (v : BitVec 32) :
    Frame (W s₀) m (m.writeW (coeffAddr (wA s₀) t) v) := by
  have := hp.facts
  exact (Frame.refl _ _).writeW (r := hR s₀) (by simp) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- A word of `h`. -/
theorem hAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 256 * K s₀) :
    addr (arg s₀ 3 + BitVec.ofNat 32 (4 * t)) 0 = coeffAddr (wA s₀) t := by
  have := hp.facts; have := hp.w_fit; rw [addr_add (by omega_arith), Nat.add_zero]

/-- A byte of `y`. -/
theorem yAddr {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < yL s₀) :
    addr (arg s₀ 0 + BitVec.ofNat 32 t) 0 = rA s₀ + BitVec.ofNat 64 t := by
  have := hp.r_fit; rw [addr_add (by omega_arith), Nat.add_zero]

theorem yb_lt (s₀ : State) (t : Nat) : yb s₀ t < 256 := ((Y s₀).getD t 0).isLt

/-! ## Zeroing `h` -/

/-- After `t` words. -/
structure ZI (s₀ : State) (t : Nat) (s : State) : Prop extends Base s₀ s where
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (4 * t)
  edx : s.gpr .edx = BitVec.ofNat 32 (hL s₀ - t)
  eax : s.gpr .eax = 0
  zero : ∀ u < t, coeffAt s.mem (wA s₀) u = 0
  len : s.mem.readW (argAddr s₀ 1) 32 = arg s₀ 1

theorem zinit_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (ZI · 0) (.block hbuZeroInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by native_taint_decide)
  · subst e
    have b₀ : Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a3 : addr ((P0 s₀).gpr .esp) 32 = argAddr s₀ 3 := argEa rfl 3
    have a4 : addr ((P0 s₀).gpr .esp) 36 = argAddr s₀ 4 := argEa rfl 4
    have i3 := b₀.argIn hp (i := 3) (by omega_arith)
    have i4 := b₀.argIn hp (i := 4) (by omega_arith)
    have v3 := hp.P0_argw (i := 3) (by omega_arith)
    have v4 := hp.P0_argw (i := 4) (by omega_arith)
    have hb : WP isa (.block hbuZeroInit) (P0 s₀) fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edx = arg s₀ 4 ∧
        s'.gpr .eax = 0 ∧ s'.mem = (P0 s₀).mem := by
      hrun [hbuZeroInit, a3, a4, i3, i4, v3, v4]
    refine (WP.keep [.ecx, .edx, .eax] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨b₀.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e1]; simp, by rw [e2]; simp, e3,
        fun u hu => absurd hu (Nat.not_lt_zero _), by rw [m]; exact hp.P0_argw (by omega_arith)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.e0]

theorem zstep {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < hL s₀) {s : State} (h : ZI s₀ t s) :
    WP isa (.block hbuZeroBody) s fun s' => ZI s₀ (t + 1) s' ∧ isa.eval .ne s' = some (decide (t + 1 < hL s₀)) := by
  have hf := hp.facts
  have ht' : t < 256 * K s₀ := by omega_arith
  have ea : addr (s.gpr .ecx) 0 = coeffAddr (wA s₀) t := by rw [h.ecx]; exact hAddr hp ht'
  have hin := h.inH hp ht'
  have hb : WP isa (.block hbuZeroBody) s fun s' => s'.gpr .ecx = s.gpr .ecx + 4 ∧ s'.gpr .edx = s.gpr .edx - 1 ∧
      s'.zf = some (s.gpr .edx - 1 == 0) ∧ s'.mem = s.mem.writeW (coeffAddr (wA s₀) t) (s.gpr .eax) := by
    hrun [hbuZeroBody, ea, hin]
  refine (WP.keep [.ecx, .edx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ => ?_
  refine ⟨⟨h.keep k (by decide) (by rw [m]; exact frame_coeff hp ht' _), by rw [e1, h.ecx, add_four']; congr 2,
    by rw [e2, h.edx]; exact cnt_next ht, by rw [k.gpr (by decide), h.eax], fun u hu => ?_,
    by rw [m, Mem.readW_writeW_sep (hp.slot_coeff ht' (j := 1) (by omega_arith)) (by decide), h.len]⟩,
    eval_ne_cnt ht (by omega_arith) (by rw [z, h.edx])⟩
  rw [m, h.eax]
  by_cases e : u = t
  · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
  · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
      ← coeffAt_eq, h.zero u (by omega_arith)]

theorem zloop_piece : Piece Pre Pub (ZI · 0) (fun s₀ s => ZI s₀ (hL s₀) s) (.loop (.block hbuZeroBody) .ne) :=
  countLoopN (fun t s₀ s => ZI s₀ t s) hL (fun s₀ hp => by have := hp.facts; omega_arith)
    (fun _ _ _ _ hq => by simp only [hL, hq.a4]) [.ecx] (fun t s₀ s hp h ht => zstep hp ht h)
    (fun t s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ecx, h'.ecx, hq.a3]) (by native_taint_decide)

/-! ## The state of the loops -/

/-- The registers and slots of polynomial `i`. -/
structure Ptr (s₀ : State) (i : Nat) (s : State) : Prop extends Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  esi : s.gpr .esi = 1
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (1024 * i)
  cnt : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (K s₀ - i)
  ptr : s.mem.readW (argAddr s₀ 4) 32 = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i)

/-- `Ptr`, after a block that writes only the registers `rs` (not those of
`Ptr`) and not memory. -/
theorem Ptr.keep {s₀ s s' : State} {i : Nat} (h : Ptr s₀ i s) {rs : List Reg} (k : Keep rs s s')
    (hrs : ∀ r ∈ rs, r = .eax ∨ r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) : Ptr s₀ i s' := by
  have g : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a b c d =>
    k.gpr fun hr => by rcases hrs r hr with e | e | e | e <;> contradiction
  exact ⟨h.toBase.keep k (fun hr => by rcases hrs _ hr with e | e | e | e <;> cases e)
      (by rw [hm]; exact Frame.refl _ _),
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ecx], by rw [hm, h.cnt], by rw [hm, h.ptr]⟩

/-- Before polynomial `i` (or after it, with the spec's state `o`). -/
structure OM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends Ptr s₀ i s where
  eax : s.gpr .eax = BitVec.ofNat 32 (idxOf o)
  sr : SR s₀ o s.mem

theorem setup_piece : Piece Pre Pub (fun s₀ s => ZI s₀ (hL s₀) s) (fun s₀ s => OM s₀ 0 (PS s₀ 0) s)
    (.block hbuSetup) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · have a0 : addr (s.gpr .esp) 20 = argAddr s₀ 0 := argEa h.esp 0
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have a3 : addr (s.gpr .esp) 32 = argAddr s₀ 3 := argEa h.esp 3
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i0 := h.argIn hp (i := 0) (by omega_arith)
    have i1 := h.argIn hp (i := 1) (by omega_arith)
    have i2 := h.argIn hp (i := 2) (by omega_arith)
    have i3 := h.argIn hp (i := 3) (by omega_arith)
    have o1 := h.argOut hp (i := 1) (by omega_arith)
    have o4 := h.argOut hp (i := 4) (by omega_arith)
    have v0 := h.argw hp (i := 0) (by omega_arith) (by omega_arith) (by omega_arith)
    have v2 := h.argw hp (i := 2) (by omega_arith) (by omega_arith) (by omega_arith)
    have v3 := h.argw hp (i := 3) (by omega_arith) (by omega_arith) (by omega_arith)
    have v1 := h.len
    have hb : WP isa (.block hbuSetup) s fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edi = arg s₀ 0 ∧
        s'.gpr .esi = 1 ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (arg s₀ 1 - arg s₀ 2)).writeW (argAddr s₀ 4) (arg s₀ 0 + arg s₀ 2) := by
      hrun [hbuSetup, a0, a1, a2, a3, a4, i0, i1, i2, i3, o1, o4, v0, v1, v2, v3]
    have hf := hp.facts
    have l1 := (arg s₀ 1).isLt
    have l2 := (arg s₀ 2).isLt
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega_arith) (by omega_arith) (by omega_arith)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    refine (WP.keep [.ecx, .edi, .edx, .esi] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨⟨h.keep k (by decide) (by rw [m]; exact (frame_slot (.inl rfl) _).trans (frame_slot (.inr rfl) _)),
        e2, e3, by rw [e1]; simp, ?_, ?_⟩, by rw [k.gpr (by decide), h.eax]; rfl, ?_⟩
    · rw [m, Mem.readW_writeW_sep s14 (by decide), Mem.readW_writeW_self32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [K, yL, ω] at hf ⊢
      omega_arith
    · rw [m, Mem.readW_writeW_self32]; simp
    · rintro st e
      simp only [PS, List.range_zero, optFold, Option.some.injEq] at e
      subst e
      refine ⟨Nat.zero_le _, harr_zero fun t ht => ?_⟩
      rw [m, hp.coeff_frame (by omega_arith) _ t ht, hp.coeff_frame (by omega_arith) _ t ht]
      exact h.zero t (by omega_arith)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the coefficients of a polynomial

Once the bound `y[ω + i]` of polynomial `i` has passed its checks, the code
sets the coefficients `y[index]` up to it (`coefs_piece`), following `huStep`
from the spec's state `cur s₀ i` before the polynomial: after `t` of them the
spec's state is `G s₀ i t`, and `eax` its index (or 256 once a check fails,
which ends the loop).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state before polynomial `i`, if no check failed. -/
def cur (s₀ : State) (i : Nat) : Array (Vector Bool n) × Nat := (PS s₀ i).getD (#[], 0)

/-- Its index. -/
abbrev fst (s₀ : State) (i : Nat) : Nat := (cur s₀ i).2

/-- ... and after `t` of the coefficients of polynomial `i`. -/
def G (s₀ : State) (i t : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huStep (Y s₀) i (fst s₀ i)) (List.range t) (cur s₀ i)

theorem Pub.ecur {s₀ s₀' : State} (h : Pub s₀ s₀') (i : Nat) : cur s₀ i = cur s₀' i := by
  unfold cur; rw [h.ePS]

theorem Pub.eG {s₀ s₀' : State} (h : Pub s₀ s₀') (i t : Nat) : G s₀ i t = G s₀' i t := by
  show optFold (huStep (Y s₀) i (cur s₀ i).2) (List.range t) (cur s₀ i) =
    optFold (huStep (Y s₀') i (cur s₀' i).2) (List.range t) (cur s₀' i)
  rw [h.ecur, h.y]

theorem G_succ (s₀ : State) (i t : Nat) :
    G s₀ i (t + 1) = (G s₀ i t).bind fun st => huStep (Y s₀) i (fst s₀ i) st t :=
  optFold_range_succ _ _ _

theorem G_idx (s₀ : State) (i : Nat) : ∀ {t : Nat} {st : Array (Vector Bool n) × Nat}, G s₀ i t = some st →
    st.2 = fst s₀ i + t
  | 0, st, h => by simp only [G, List.range_zero, optFold, Option.some.injEq] at h; subst h; rfl
  | t + 1, st, h => by
    rw [G_succ] at h
    cases e : G s₀ i t with
    | none => rw [e] at h; cases h
    | some st' =>
      rw [e, Option.bind_some] at h
      rw [huStep_idx h, G_idx s₀ i e]; omega_arith

theorem idxOf_G {s₀ : State} {i t : Nat} (h : idxOf (G s₀ i t) < 256) : ∃ st, G s₀ i t = some st ∧
    idxOf (G s₀ i t) = fst s₀ i + t := by
  cases e : G s₀ i t with
  | none => rw [e] at h; exact absurd h (by decide)
  | some st => exact ⟨st, rfl, G_idx s₀ i e⟩

theorem PS_succ (s₀ : State) (i : Nat) :
    PS s₀ (i + 1) = (PS s₀ i).bind fun st => huPoly (ω s₀) (Y s₀) st i :=
  optFold_range_succ _ _ _

theorem bnd_lt (s₀ : State) (i : Nat) : bnd s₀ i < 256 := yb_lt _ _

/-- A bound less than the index fails. -/
theorem PS_fail₁ {s₀ : State} {i : Nat} (h : bnd s₀ i < idxOf (PS s₀ i)) : PS s₀ (i + 1) = none := by
  rw [PS_succ]
  cases e : PS s₀ i with
  | none => rfl
  | some st =>
    rw [e] at h
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inl h) _ _

/-- A bound greater than `ω` fails. -/
theorem PS_fail₂ {s₀ : State} {i : Nat} (h : bnd s₀ i > ω s₀) : PS s₀ (i + 1) = none := by
  rw [PS_succ]
  cases e : PS s₀ i with
  | none => rfl
  | some st =>
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inr h) _ _

/-- Otherwise the coefficients follow. -/
theorem PS_ok {s₀ : State} {i : Nat} (h₁ : ¬ bnd s₀ i < idxOf (PS s₀ i)) (h₂ : ¬ bnd s₀ i > ω s₀) :
    PS s₀ i = some (cur s₀ i) ∧ fst s₀ i ≤ bnd s₀ i ∧ PS s₀ (i + 1) = G s₀ i (bnd s₀ i - fst s₀ i) := by
  cases e : PS s₀ i with
  | none => rw [e] at h₁; exact absurd (bnd_lt s₀ i) h₁
  | some st =>
    have ec : cur s₀ i = st := by unfold cur; rw [e]; rfl
    have ef : fst s₀ i = st.2 := by show (cur s₀ i).2 = _; rw [ec]
    have eb : bnd s₀ i = ((Y s₀).getD (ω s₀ + i) 0).toNat := rfl
    rw [e] at h₁
    simp only [idxOf] at h₁
    refine ⟨by rw [ec], by omega_arith, ?_⟩
    rw [PS_succ, e, Option.bind_some, huPoly, ite_neg' (by omega_arith), G]
    show _ = optFold (huStep (Y s₀) i (cur s₀ i).2) (List.range (bnd s₀ i - (cur s₀ i).2)) (cur s₀ i)
    rw [ec]

/-! ## The state within a polynomial -/

/-- Within polynomial `i`, whose bound passed its checks, with the spec's
state `o`. -/
structure IM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends Ptr s₀ i s where
  ebx : s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)
  eax : s.gpr .eax = BitVec.ofNat 32 (idxOf o)
  sr : SR s₀ o s.mem
  hi : i < K s₀
  some : PS s₀ i = some (cur s₀ i)
  fb : fst s₀ i ≤ bnd s₀ i
  bw : bnd s₀ i ≤ ω s₀

/-- `IM`, after a block that writes only `edx`, `ebp` and the flags. -/
theorem IM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : IM s₀ i o s)
    (k : Keep [.edx, .ebp] s s') (hm : s'.mem = s.mem) : IM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp) hm,
    by rw [k.gpr (by decide), h.ebx], by rw [k.gpr (by decide), h.eax], by rw [hm]; exact h.sr, h.hi, h.some,
    h.fb, h.bw⟩

theorem idx_lt_yL {s₀ : State} (hp : Pre s₀) {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} {s : State}
    (h : IM s₀ i o s) {t : Nat} (ht : t < bnd s₀ i) : t < yL s₀ := by
  have := hp.facts; have := h.bw; omega_arith

/-- The `SR` of `G`, from that of the state before. -/
theorem SR_G {s₀ : State} {i t : Nat} {m : Mem} (hfb : fst s₀ i + t ≤ bnd s₀ i) (hbw : bnd s₀ i ≤ ω s₀)
    (h : ∀ st, G s₀ i t = some st → HArr m (wA s₀) (K s₀) st.1) : SR s₀ (G s₀ i t) m :=
  fun st e => ⟨by rw [G_idx s₀ i e]; omega_arith, h st e⟩

/-! ## Setting a coefficient -/

/-- `ebp ← 4b + ecx`, the word of coefficient `b` of polynomial `i`. -/
theorem setAddr {x : BitVec 32} {i b : Nat} (hx : x.toNat + 1024 * i + 4 * b + 4 ≤ 2 ^ 32) :
    addr (BitVec.ofNat 32 b + BitVec.ofNat 32 b + (BitVec.ofNat 32 b + BitVec.ofNat 32 b) +
      (x + BitVec.ofNat 32 (1024 * i))) 0 = x.setWidth 64 + BitVec.ofNat 64 (4 * (256 * i + b)) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm, BitVec.add_assoc, ofNat_add_ofNat,
    addr_add (by omega_arith)]
  congr 2; omega_arith

theorem set_wp {s₀ s : State} (hp : Pre s₀) {i b : Nat} (h : Ptr s₀ i s) (hi : i < K s₀) (hb : b < 256)
    (hebp : s.gpr .ebp = BitVec.ofNat 32 b) :
    WP isa (.block hbuSet) s fun s' => (s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) ∧ Keep [.ebp, .eax] s s' := by
  have hf := hp.facts
  have hw := hp.w_fit
  have ht : 256 * i + b < 256 * K s₀ := by omega_arith
  have ea : addr (s.gpr .ebp + s.gpr .ebp + (s.gpr .ebp + s.gpr .ebp) + s.gpr .ecx) 0 =
      coeffAddr (wA s₀) (256 * i + b) := by
    rw [hebp, h.ecx]; exact setAddr (by omega_arith)
  have hin := h.inH hp ht
  refine WP.keep _ ?_ (by decide)
  hrun [hbuSet, ea, hin, h.esi]

/-- After setting coefficient `b` of polynomial `i`. -/
theorem sr_set {s₀ : State} (hp : Pre s₀) {i b : Nat} (hi : i < K s₀) (hb : b < 256) {m : Mem}
    {hA : Array (Vector Bool n)} (hh : HArr m (wA s₀) (K s₀) hA) :
    HArr (m.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) (wA s₀) (K s₀) (huSet i b hA) := by
  have := hp.facts
  exact harr_set (by omega_arith) hh hi hb

/-- The frame of the write. -/
theorem ptr_set {s₀ s s' : State} (hp : Pre s₀) {i b : Nat} (h : Ptr s₀ i s) (hi : i < K s₀) (hb : b < 256)
    (k : Keep [.ebp, .eax] s s') (hm : s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) :
    Ptr s₀ i s' := by
  have hf := hp.facts
  have ht : 256 * i + b < 256 * K s₀ := by omega_arith
  have g : ∀ r, r ≠ .eax → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a c =>
    k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun hh => hh.elim c a)
  exact ⟨h.toBase.keep k (by decide) (by rw [hm]; exact frame_coeff hp ht _),
    by rw [g _ (by decide) (by decide), h.edi], by rw [g _ (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide), h.ecx],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega_arith)) (by decide), h.cnt],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega_arith)) (by decide), h.ptr]⟩

theorem idxOf_le {s₀ : State} (hp : Pre s₀) {o : Option (Array (Vector Bool n) × Nat)} {m : Mem}
    (h : SR s₀ o m) : idxOf o ≤ 256 := by
  cases o with
  | none => exact Nat.le_refl _
  | some st => have := (h st rfl).1; have := hp.facts; show st.2 ≤ 256; omega_arith

theorem G_next {s₀ : State} {i t : Nat} {st : Array (Vector Bool n) × Nat} (e : G s₀ i t = some st) :
    G s₀ i (t + 1) = if st.2 > fst s₀ i ∧ yb s₀ (st.2 - 1) ≥ yb s₀ st.2 then none
      else some (huSet i (yb s₀ st.2) st.1, st.2 + 1) := by
  rw [G_succ, e]; rfl

theorem G_one (s₀ : State) (i : Nat) :
    G s₀ i 1 = some (huSet i (yb s₀ (fst s₀ i)) (cur s₀ i).1, fst s₀ i + 1) := by
  rw [G_next (t := 0) rfl, ite_neg' (fun h => Nat.lt_irrefl _ h.1)]

/-- `cmp eax, ebx`: whether the index is below the bound. -/
theorem cmp_piece (i : Nat) (o : State → Option (Array (Vector Bool n) × Nat)) (X : State → Prop) :
    Piece Pre Pub (fun s₀ s => IM s₀ i (o s₀) s ∧ X s₀)
      (fun s₀ s => (IM s₀ i (o s₀) s ∧ X s₀) ∧ isa.eval .b s = some (decide (idxOf (o s₀) < bnd s₀ i)))
      (.block [.alu .cmp .eax (.reg .ebx)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by native_taint_decide)
  have hb : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .eax).toNat < (s.gpr .ebx).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
        s'.mem = s.mem := by hrun
  have hl := idxOf_le hp h.sr
  have hb' := bnd_lt s₀ i
  refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k⟩ =>
    ⟨⟨h.keep ⟨fun r _ => (k.drop ea).gpr (by simp), k.2⟩ m, hx⟩, ?_⟩
  show s'.cf = _
  rw [c, h.eax, h.ebx, toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]

/-- The first coefficient: `ebp = y[index]`. -/
theorem first_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i)
    (fun s₀ s => (IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i)))
    (.block hbuFirst) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp ⟨h, hl⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by native_taint_decide)
  · have hy := idx_lt_yL hp h hl
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i) := by
      rw [h.edi, h.eax]; exact yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block hbuFirst) s fun s' => s'.gpr .ebp = BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i) 0) ∧
        s'.mem = s.mem := by
      hrun [hbuFirst, ea, hin, hv]
    exact (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ => ⟨⟨h.keep k m, hl⟩, by rw [e, byte32]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.edi, h'.edi, hq.a0]
    · rw [h.eax, h'.eax, hq.eG]

/-- The first coefficient set, and whether the index is below the bound. -/
theorem set1_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (IM s₀ i (G s₀ i 0) s ∧ fst s₀ i < bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i)))
    (fun s₀ s => IM s₀ i (G s₀ i 1) s ∧ isa.eval .b s = some (decide (fst s₀ i + 1 < bnd s₀ i)))
    (.block (hbuSet ++ ([.alu .cmp .eax (.reg .ebx)] : List Instr))) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨h, hl⟩, he⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨h, _⟩, he⟩ ⟨⟨h', _⟩, he'⟩ r hr => ?_) (by native_taint_decide)
  · have hb' := bnd_lt s₀ i
    have hbw := h.bw
    have hf := hp.facts
    refine WP.block_append ((set_wp hp h.toPtr h.hi (yb_lt s₀ _) he).mono fun s₁ ⟨⟨e1, m1⟩, k1⟩ => ?_)
    have hc : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s₁ fun s' =>
        s'.cf = some (decide ((s₁.gpr .eax).toNat < (s₁.gpr .ebx).toNat)) ∧ s'.gpr .eax = s₁.gpr .eax ∧
          s'.mem = s₁.mem := by hrun
    refine (WP.keep [.eax] hc (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨(ptr_set hp h.toPtr h.hi (yb_lt s₀ _) k1 m1).keep k (fun r hr => by simp at hr) m, ?_, ?_, ?_, h.hi,
      h.some, h.fb, h.bw⟩, ?_⟩
    · rw [k.gpr (by simp), k1.gpr (by decide), h.ebx]
    · rw [k.gpr (by simp), e1, h.eax, G_one]; simp only [idxOf]; rw [ofNat_add_one]; rfl
    · rw [m, m1]
      refine SR_G (t := 1) (by omega_arith) hbw fun st e => ?_
      rw [G_one, Option.some.injEq] at e
      subst e
      obtain ⟨-, hh⟩ := h.sr (cur s₀ i) (by rw [G]; rfl)
      exact sr_set hp h.hi (yb_lt s₀ _) hh
    · show s'.cf = _
      rw [c, e1, h.eax, k1.gpr (by decide), h.ebx]
      simp only [G, List.range_zero, optFold, idxOf]
      have : fst s₀ i = (cur s₀ i).2 := rfl
      rw [ofNat_add_one, toNat_ofNat32 (by omega_arith), toNat_ofNat32 (by omega_arith)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (yb s₀ (cur s₀ i).2) = BitVec.ofNat 32 (yb s₀' (cur s₀' i).2)
      rw [hq.ecur, hq.eyb]
    · rw [h.ecx, h'.ecx, hq.a3]

/-! ## The coefficients after the first -/

/-- Before iteration `k` of the loop: `k + 1` coefficients set, and the
index below the bound. -/
def NI (i k : Nat) (s₀ s : State) : Prop :=
  IM s₀ i (G s₀ i (k + 1)) s ∧ idxOf (G s₀ i (k + 1)) = fst s₀ i + k + 1 ∧ fst s₀ i + k + 1 < bnd s₀ i

/-- `ebp = y[index]`, and whether `y[index - 1] < y[index]`. -/
theorem loads_piece (i k : Nat) : Piece Pre Pub (NI i k)
    (fun s₀ s => (NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1))))
    (.block hbuLoads) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · obtain ⟨hI, hx, hl⟩ := h
    have hy := idx_lt_yL hp hI hl
    have hax : s.gpr .eax = BitVec.ofNat 32 (fst s₀ i + k + 1) := by rw [hI.eax, hx]
    have ea1 : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i + k + 1) := by
      rw [hI.edi, hax]; exact yAddr hp hy
    have ea2 : addr (s.gpr .edi + s.gpr .eax - 1) 0 = rA s₀ + BitVec.ofNat 64 (fst s₀ i + k) := by
      rw [hI.edi, hax, add_sub_one' _ (by omega_arith)]; exact yAddr hp (by omega_arith)
    have i1 := hI.inY hp hy
    have i2 := hI.inY hp (t := fst s₀ i + k) (by omega_arith)
    have v1 := hI.ybyte hp hy
    have v2 := hI.ybyte hp (t := fst s₀ i + k) (by omega_arith)
    have hb : WP isa (.block hbuLoads) s fun s' =>
        s'.gpr .ebp = BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k + 1) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k) 0)).toNat <
          (BitVec.setWidth 32 ((Y s₀).getD (fst s₀ i + k + 1) 0)).toNat)) ∧ s'.mem = s.mem := by
      hrun [hbuLoads, ea1, ea2, i1, i2, v1, v2]
    refine (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k'⟩ =>
      ⟨⟨⟨hI.keep k' m, hx, hl⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, toNat_setWidth32_8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.1.eax, h'.1.eax, hq.eG]

theorem G_some {s₀ : State} {i k : Nat} (h : idxOf (G s₀ i (k + 1)) = fst s₀ i + k + 1) (hl : fst s₀ i + k + 1 < 256) :
    ∃ st, G s₀ i (k + 1) = some st ∧ st.2 = fst s₀ i + k + 1 := by
  obtain ⟨st, e, -⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 1) (by omega_arith)
  exact ⟨st, e, by rw [e] at h; exact h⟩

/-- A coefficient greater than the previous one: set it. -/
theorem set2_piece (i k : Nat) : Piece Pre Pub
    (fun s₀ s => ((NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)))) ∧
      decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)) = true)
    (fun s₀ s => IM s₀ i (G s₀ i (k + 2)) s ∧ fst s₀ i + k + 1 < bnd s₀ i) (.block hbuSet) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨hn, he⟩, _⟩, _⟩ ⟨⟨⟨hn', he'⟩, _⟩, _⟩ r hr => ?_) (by native_taint_decide)
  · have hlt := of_decide_eq_true hb
    have hb' := bnd_lt s₀ i
    obtain ⟨st, e, est⟩ := G_some hx (by omega_arith)
    have hG : G s₀ i (k + 2) = some (huSet i (yb s₀ (fst s₀ i + k + 1)) st.1, fst s₀ i + k + 1 + 1) := by
      rw [G_next e, est, ite_neg' (fun h => by
        rw [show fst s₀ i + k + 1 - 1 = fst s₀ i + k by omega_arith] at h; omega_arith)]
    refine (set_wp hp hI.toPtr hI.hi (yb_lt s₀ _) he).mono fun s' ⟨⟨e1, m1⟩, k1⟩ =>
      ⟨⟨ptr_set hp hI.toPtr hI.hi (yb_lt s₀ _) k1 m1, by rw [k1.gpr (by decide), hI.ebx], ?_, ?_, hI.hi, hI.some,
        hI.fb, hI.bw⟩, hl⟩
    · rw [e1, hI.eax, hx, hG]; simp only [idxOf]; rw [ofNat_add_one]
    · rw [m1]
      refine SR_G (t := k + 2) (by omega_arith) hI.bw fun st' e' => ?_
      rw [hG, Option.some.injEq] at e'
      subst e'
      exact sr_set hp hI.hi (yb_lt s₀ _) (hI.sr st e).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (yb s₀ ((cur s₀ i).2 + k + 1)) = BitVec.ofNat 32 (yb s₀' ((cur s₀' i).2 + k + 1))
      rw [hq.ecur, hq.eyb]
    · rw [hn.1.ecx, hn'.1.ecx, hq.a3]

/-- A coefficient not greater than the previous one: fail. -/
theorem fail2_piece (i k : Nat) : Piece Pre Pub
    (fun s₀ s => ((NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (yb s₀ (fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)))) ∧
      decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1)) = false)
    (fun s₀ s => IM s₀ i (G s₀ i (k + 2)) s ∧ fst s₀ i + k + 1 < bnd s₀ i) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)
  have hge := of_decide_eq_false hb
  have hb' := bnd_lt s₀ i
  obtain ⟨st, e, est⟩ := G_some hx (by omega_arith)
  have hG : G s₀ i (k + 2) = none := by
    rw [G_next e, est, ite_pos' ⟨by omega_arith, by rw [show fst s₀ i + k + 1 - 1 = fst s₀ i + k by omega_arith]; omega_arith⟩]
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨⟨hI.toPtr.keep k' (fun r hr => by simp at hr; simp [hr]) m, by rw [k'.gpr (by decide), hI.ebx],
      by rw [e1, hG]; rfl, by rw [hG]; exact SR.none _ _, hI.hi, hI.some, hI.fb, hI.bw⟩, hl⟩

theorem loop_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 1) s ∧ fst s₀ i + 1 < bnd s₀ i)
    (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) (.loop hbuNext .b) := by
  refine (loopC (NI i) (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) (fun s₀ => bnd s₀ i)
    (fun k s₀ => decide (idxOf (G s₀ i (k + 2)) < bnd s₀ i)) (fun k s₀ _ hc => ?_)
    (fun k s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) fun k => ?_).mono
    (fun s₀ s _ ⟨h, hl⟩ => ⟨h, by rw [G_one]; rfl, hl⟩) fun _ _ _ h => h
  · have hc := of_decide_eq_true hc
    have := bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega_arith)
    omega_arith
  refine Piece.seq (loads_piece i k) (Piece.seq (Piece.ite
    (fun s₀ => decide (yb s₀ (fst s₀ i + k) < yb s₀ (fst s₀ i + k + 1))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by simp only [fst, hq.ecur, hq.eyb]) (set2_piece i k) (fail2_piece i k))
    ((cmp_piece i (fun s₀ => G s₀ i (k + 2)) (fun s₀ => fst s₀ i + k + 1 < bnd s₀ i)).mono (fun _ _ _ h => h)
      fun s₀ s _ ⟨⟨h, hl⟩, hc⟩ => ⟨hc, fun hc' => ?_, fun hc' => ?_⟩))
  · have hc' := of_decide_eq_true hc'
    have := bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega_arith)
    exact ⟨h, by omega_arith, by omega_arith⟩
  · have hc' := of_decide_eq_false hc'
    cases e : G s₀ i (k + 2) with
    | none =>
      have : G s₀ i (bnd s₀ i - fst s₀ i) = none := optFold_range_none _ (show k + 2 ≤ _ by omega_arith) e
      rw [this]; rw [e] at h; exact h
    | some st =>
      have hx := G_idx s₀ i e
      rw [e] at hc'
      simp only [idxOf] at hc'
      rw [show bnd s₀ i - fst s₀ i = k + 2 by omega_arith]; exact h

/-- The coefficients of polynomial `i`. -/
theorem coefs_piece (i : Nat) : Piece Pre Pub (fun s₀ s => IM s₀ i (G s₀ i 0) s)
    (fun s₀ s => IM s₀ i (G s₀ i (bnd s₀ i - fst s₀ i)) s) hbuCoefs := by
  have e0 : ∀ s₀, idxOf (G s₀ i 0) = fst s₀ i := fun _ => rfl
  refine Piece.seq ((cmp_piece i (fun s₀ => G s₀ i 0) (fun _ => True)).mono (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ h => h) (Piece.ite (fun s₀ => decide (idxOf (G s₀ i 0) < bnd s₀ i)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) ?_ ?_)
  · refine Piece.seq ((first_piece i).mono (fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, by
      have := of_decide_eq_true hb; rw [e0] at this; exact this⟩) fun _ _ _ h => h) ?_
    refine Piece.seq (addX (set1_piece i) fun _ _ _ h => h.1.2) (Piece.ite
      (fun s₀ => decide (fst s₀ i + 1 < bnd s₀ i)) (fun _ _ _ h => h.1.2)
      (fun s₀ s₀' _ _ hq => by simp only [fst, hq.ecur, hq.ebnd]) ?_ ?_)
    · exact (loop_piece i).mono (fun _ _ _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h
    · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, hl⟩, hb⟩ => by
        have := of_decide_eq_false hb
        rw [show bnd s₀ i - fst s₀ i = 1 by omega_arith]; exact h
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => by
      have := of_decide_eq_false hb
      rw [e0] at this
      have := h.fb
      rw [show bnd s₀ i - fst s₀ i = 0 by omega_arith]; exact h

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`

The polynomials (`poly_piece`: the bound `y[ω + i]`, its two checks, and the
coefficients of `HintUnpackLoop.lean`), the bytes from the index up to `ω`
(`trail_piece`), and the return value (`ret_piece`), which is 1 iff no check
failed; `hintBitUnpack_eq` (`Pack/Hint.lean`) gives the contract.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

namespace Up

/-- `OM`, after a block that writes only the registers `rs` (among `ebx`,
`edx` and `ebp`) and not memory. -/
theorem OM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : OM s₀ i o s)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ rs, r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) :
    OM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by rcases hrs r hr with e | e | e <;> simp [e]) hm,
    by rw [k.gpr (fun hr => by rcases hrs _ hr with e | e | e <;> cases e), h.eax], by rw [hm]; exact h.sr⟩

/-! ## A polynomial -/

theorem q1_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ i) s ∧ i < K s₀)
    (fun s₀ s => (OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (.block [.mov .edx (.mem (at_ .esp 36))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by native_taint_decide)
  · have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i4 := h.argIn hp (i := 4) (by omega_arith)
    have hb : WP isa (.block [.mov .edx (.mem (at_ .esp 36))]) s fun s' =>
        s'.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) ∧ s'.mem = s.mem := by
      hrun [a4, i4, h.ptr]
    exact (WP.keep [.edx] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨⟨h.keep k (by simp) m, hi⟩, e⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem q2_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (fun s₀ s => ((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i))))
    (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) := by
  refine Piece.taint [.edx] (fun s₀ s hp ⟨⟨h, hi⟩, hd⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨_, hd⟩ ⟨_, hd'⟩ r hr => ?_) (by native_taint_decide)
  · have hf := hp.facts
    have hy : ω s₀ + i < yL s₀ := by omega_arith
    have ea : addr (s.gpr .edx) 0 = rA s₀ + BitVec.ofNat 64 (ω s₀ + i) := by rw [hd]; exact yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) s fun s' =>
        s'.gpr .ebx = BitVec.setWidth 32 ((Y s₀).getD (ω s₀ + i) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((Y s₀).getD (ω s₀ + i) 0)).toNat < (s.gpr .eax).toNat)) ∧
        s'.mem = s.mem := by
      hrun [ea, hin, hv]
    have hl := idxOf_le hp h.sr
    refine (WP.keep [.ebx] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k⟩ =>
      ⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, h.eax, toNat_ofNat32 (by omega_arith)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [hd, hd', hq.a0, hq.eω]

theorem fail1_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i)))) ∧ decide (bnd s₀ i < idxOf (PS s₀ i)) = true)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)
  have e := PS_fail₁ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem q3_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      isa.eval .b s = some (decide (bnd s₀ i < idxOf (PS s₀ i)))) ∧ decide (bnd s₀ i < idxOf (PS s₀ i)) = false)
    (fun s₀ s => (((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i)))
    (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨⟨⟨⟨h, hi⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨h', _⟩, _⟩, _⟩, _⟩ r hr => ?_) (by native_taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega_arith)
    have v2 := h.argw hp (i := 2) (by omega_arith) (by omega_arith) (by omega_arith)
    have hb' : WP isa (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) s fun s' =>
        s'.cf = some (decide ((arg s₀ 2).toNat < (s.gpr .ebx).toNat)) ∧ s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have := bnd_lt s₀ i
    refine (WP.keep [.edx] hb' (by decide)).mono fun s' ⟨⟨c, m⟩, k⟩ =>
      ⟨⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [k.gpr (by decide), he]⟩, of_decide_eq_false hb⟩, ?_⟩
    show s'.cf = _
    rw [c, he, toNat_ofNat32 (by omega_arith)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem fail2_poly_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => ((((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i))) ∧
      decide (ω s₀ < bnd s₀ i) = true)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)
  have e := PS_fail₂ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem coefs_poly_piece (i : Nat) : Piece Pre Pub
    (fun s₀ s => ((((OM s₀ i (PS s₀ i) s ∧ i < K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (bnd s₀ i)) ∧
      ¬ bnd s₀ i < idxOf (PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < bnd s₀ i))) ∧
      decide (ω s₀ < bnd s₀ i) = false)
    (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s) hbuCoefs :=
  (coefs_piece i).mono (fun s₀ s _ ⟨⟨⟨⟨⟨h, hi⟩, he⟩, h1⟩, _⟩, hb⟩ => by
      have h2 := of_decide_eq_false hb
      obtain ⟨e1, e2, -⟩ := PS_ok h1 h2
      have eG : G s₀ i 0 = PS s₀ i := by rw [e1]; rfl
      exact ⟨h.toPtr, he, by rw [eG]; exact h.eax, by rw [eG]; exact h.sr, hi, e1, e2, by omega_arith⟩)
    fun s₀ s _ h => by
      obtain ⟨-, -, e3⟩ := PS_ok (s₀ := s₀) (i := i) (by rw [h.some]; exact Nat.not_lt.mpr h.fb)
        (Nat.not_lt.mpr h.bw)
      exact ⟨h.toPtr, by rw [e3]; exact h.eax, by rw [e3]; exact h.sr⟩

theorem end_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ (i + 1)) s ∧ i < K s₀)
    (fun s₀ s => OM s₀ (i + 1) (PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀)))
    (.block hbuPolyEnd) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by native_taint_decide)
  · have hf := hp.facts
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i1 := h.argIn hp (i := 1) (by omega_arith)
    have i4 := h.argIn hp (i := 4) (by omega_arith)
    have o1 := h.argOut hp (i := 1) (by omega_arith)
    have o4 := h.argOut hp (i := 4) (by omega_arith)
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega_arith) (by omega_arith) (by omega_arith)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have s41 : Mem.Sep (argAddr s₀ 4) (32 / 8) (argAddr s₀ 1) (32 / 8) :=
      (hp.slot_disj (i := 4) (j := 1) (by omega_arith) (by omega_arith) (by omega_arith)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have r1 : ∀ v : BitVec 32, (s.mem.writeW (argAddr s₀ 4) v).readW (argAddr s₀ 1) 32 =
        BitVec.ofNat 32 (K s₀ - i) := fun v => by rw [Mem.readW_writeW_sep s14 (by decide), h.cnt]
    have hb : WP isa (.block hbuPolyEnd) s fun s' => s'.gpr .ecx = s.gpr .ecx + 1024 ∧
        s'.zf = some (BitVec.ofNat 32 (K s₀ - i) - 1 == 0) ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 4) (arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) + 1)).writeW (argAddr s₀ 1)
          (BitVec.ofNat 32 (K s₀ - i) - 1) := by
      hrun [hbuPolyEnd, a1, a4, i1, i4, o1, o4, h.ptr, r1]
    refine (WP.keep [.edx, .ecx] hb (by decide)).mono fun s' ⟨⟨e1, z, m⟩, k⟩ => ⟨⟨⟨h.toBase.keep k (by decide)
      (by rw [m]; exact (frame_slot (.inr rfl) _).trans (frame_slot (.inl rfl) _)),
      by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.esi], by rw [e1, h.ecx, add_1024']; congr 2,
      ?_, ?_⟩, by rw [k.gpr (by decide), h.eax], ?_⟩, eval_ne_cnt hi (by omega_arith) z⟩
    · rw [m, Mem.readW_writeW_self32]; exact cnt_next hi
    · rw [m, Mem.readW_writeW_sep s41 (by decide), Mem.readW_writeW_self32, add_one']; rfl
    · rw [m]
      exact h.sr.congr fun t ht => by rw [hp.coeff_frame (by omega_arith) _ t ht, hp.coeff_frame (by omega_arith) _ t ht]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem poly_piece (i : Nat) : Piece Pre Pub (fun s₀ s => OM s₀ i (PS s₀ i) s ∧ i < K s₀)
    (fun s₀ s => OM s₀ (i + 1) (PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < K s₀)))
    (.seq hbuPoly (.block hbuPolyEnd)) := by
  refine Piece.seq (addX (X := fun s₀ => i < K s₀) ?_ fun _ _ _ h => h.2) ((end_piece i).mono (fun _ _ _ h => h)
    fun _ _ _ h => h)
  refine Piece.seq (q1_piece i) (Piece.seq (q2_piece i) (Piece.ite
    (fun s₀ => decide (bnd s₀ i < idxOf (PS s₀ i))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.ePS]) (fail1_piece i) (Piece.seq (q3_piece i) (Piece.ite
      (fun s₀ => decide (ω s₀ < bnd s₀ i)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.eω]) (fail2_poly_piece i) (coefs_poly_piece i)))))

theorem polys_piece : Piece Pre Pub (fun s₀ s => OM s₀ 0 (PS s₀ 0) s) (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s)
    (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) :=
  loopN (fun i s₀ s => OM s₀ i (PS s₀ i) s) K (fun s₀ hp => by have := hp.facts; omega_arith)
    (fun _ _ _ _ hq => hq.eK) poly_piece

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the end

After the polynomials, the bytes from the index up to `ω` must be zero
(`trail_piece`; the spec's `huTrail`): the index ends at `ω`, or 256 if a
check failed (`fin`); the return value is 1 iff it is at most `ω`
(`ret_piece`). Then the whole function (`piece`) and its contract
(`hintBitUnpack_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state after the polynomials, if no check failed. -/
def cK (s₀ : State) : Array (Vector Bool n) × Nat := (PS s₀ (K s₀)).getD (#[], 0)

/-- Its index. -/
abbrev i₀ (s₀ : State) : Nat := (cK s₀).2

/-- The checks of the first `k` bytes from the index. -/
def TF (s₀ : State) (k : Nat) : Option Unit := optFold (huTrail (Y s₀)) (List.range' (i₀ s₀) k) ()

/-- The result of the spec: the hint, if no check fails. -/
def TS (s₀ : State) : Option (Array (Vector Bool n) × Nat) :=
  (PS s₀ (K s₀)).bind fun st => (optFold (huTrail (Y s₀)) (List.range' st.2 (ω s₀ - st.2)) ()).map fun _ => st

/-- The index at the end: `ω`, or 256 if a check failed. -/
def fin (s₀ : State) : Nat := match TS s₀ with
  | none => 256
  | some _ => ω s₀

/-- The index after byte `k`: 256 if it is not zero. -/
def tr (s₀ : State) (k : Nat) : Nat := if (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0 then 256 else i₀ s₀ + k + 1

theorem Pub.ecK {s₀ s₀' : State} (h : Pub s₀ s₀') : cK s₀ = cK s₀' := by
  unfold cK; rw [h.ePS, h.eK]

theorem Pub.etr {s₀ s₀' : State} (h : Pub s₀ s₀') (k : Nat) : tr s₀ k = tr s₀' k := by
  unfold tr; simp only [i₀, h.ecK, h.y]

/-- What the end keeps. -/
structure TB (s₀ s : State) : Prop extends Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  sr : SR s₀ (PS s₀ (K s₀)) s.mem

theorem TB.keep {s₀ s s' : State} (h : TB s₀ s) {rs : List Reg} (k : Keep rs s s') (hrs : Reg.esp ∉ rs)
    (hdi : Reg.edi ∉ rs) (hm : s'.mem = s.mem) : TB s₀ s' :=
  ⟨h.toBase.keep k hrs (by rw [hm]; exact Frame.refl _ _), by rw [k.gpr hdi, h.edi], by rw [hm]; exact h.sr⟩

/-- Before byte `k` from the index. -/
def TI (k : Nat) (s₀ s : State) : Prop :=
  TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (i₀ s₀ + k) ∧ PS s₀ (K s₀) = some (cK s₀) ∧ i₀ s₀ + k < ω s₀ ∧
    TF s₀ k = some ()

/-- After byte `k`, before the comparison. -/
def TM (k : Nat) (s₀ s : State) : Prop :=
  TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (tr s₀ k) ∧ PS s₀ (K s₀) = some (cK s₀) ∧ i₀ s₀ + k < ω s₀ ∧
    TF s₀ k = some ()

/-- At the end. -/
def TFin (s₀ s : State) : Prop := TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (fin s₀)

theorem TS_some {s₀ : State} (e : PS s₀ (K s₀) = some (cK s₀)) (ht : TF s₀ (ω s₀ - i₀ s₀) = some ()) :
    fin s₀ = ω s₀ := by
  unfold fin TS; rw [e, Option.bind_some]
  unfold TF at ht
  rw [ht]; rfl

theorem TS_none {s₀ : State} (e : PS s₀ (K s₀) = some (cK s₀)) (ht : TF s₀ (ω s₀ - i₀ s₀) = none) :
    fin s₀ = 256 := by
  unfold fin TS; rw [e, Option.bind_some]
  unfold TF at ht
  rw [ht]; rfl

/-! ## The trailing bytes -/

theorem t0_piece : Piece Pre Pub (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s)
    (fun s₀ s => (TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (idxOf (PS s₀ (K s₀)))) ∧
      isa.eval .b s = some (decide (idxOf (PS s₀ (K s₀)) < ω s₀)))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega_using [])
    have v2 := h.argw hp (i := 2) (by omega_using []) (by omega_using []) (by omega_using [])
    have hb : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hl := idxOf_le hp h.sr
    refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨⟨h.toBase.keep k (by simp) (by rw [m]; exact Frame.refl _ _), by rw [k.gpr (by simp), h.edi],
      by rw [m]; exact h.sr⟩, by rw [ea, h.eax]⟩, ?_⟩
    show s'.cf = _
    rw [c, h.eax, toNat_ofNat32 (by omega_using [hl])]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem ne_zero_byte (b : Byte) : (!(BitVec.setWidth 32 b - 0 == 0)) = decide (b ≠ 0) := by
  rw [sub_zero', byte32]
  by_cases hb : b = 0
  · subst hb; rfl
  · have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
    rw [ofNat_beq_zero (by have := b.isLt; omega_using [])]
    simpa [this] using hb

theorem load_piece (k : Nat) : Piece Pre Pub (TI k)
    (fun s₀ s => TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0)))
    (.block hbuTrailLoad) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by native_taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have hf := hp.facts
    have hy : i₀ s₀ + k < yL s₀ := by omega_using [hl, hf]
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (i₀ s₀ + k) := by
      rw [hb.edi, hax]; exact yAddr hp hy
    have hin := hb.inY hp hy
    have hv := hb.ybyte hp hy
    have hbk : WP isa (.block hbuTrailLoad) s fun s' =>
        s'.zf = some (BitVec.setWidth 32 ((Y s₀).getD (i₀ s₀ + k) 0) - 0 == 0) ∧ s'.mem = s.mem := by
      hrun [hbuTrailLoad, ea, hin, hv]
    refine (WP.keep [.edx] hbk (by decide)).mono fun s' ⟨⟨z, m⟩, k'⟩ =>
      ⟨⟨hb.keep k' (by simp) (by simp) m, by rw [k'.gpr (by simp), hax], e, hl, ht⟩, ?_⟩
    show s'.zf.map (!·) = _
    rw [z, Option.map_some, ne_zero_byte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.2.1, h'.2.1]; simp only [i₀, hq.ecK]

theorem tfail_piece (k : Nat) : Piece Pre Pub
    (fun s₀ s => (TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0) = true) (TM k) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, _, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, tr, ite_pos' (of_decide_eq_true hc)]; rfl, e, hl, ht⟩

theorem tinc_piece (k : Nat) : Piece Pre Pub
    (fun s₀ s => (TI k s₀ s ∧ isa.eval .ne s = some (decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0) = false) (TM k) (.block [.alu .add .eax (.imm 1)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, hax, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by native_taint_decide)
  have hbk : WP isa (.block [.alu .add .eax (.imm 1)]) s fun s' => s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem := by hrun
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, hax, tr, ite_neg' (of_decide_eq_false hc), ofNat_add_one],
      e, hl, ht⟩

/-- `cmp eax, ω`, after byte `k`. -/
theorem tcmp_piece (k : Nat) : Piece Pre Pub (TM k)
    (fun s₀ s => isa.eval .b s = some (decide (tr s₀ k < ω s₀)) ∧ (decide (tr s₀ k < ω s₀) = true → TI (k + 1) s₀ s) ∧
      (decide (tr s₀ k < ω s₀) = false → TFin s₀ s))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega_using [])
    have v2 := hb.argw hp (i := 2) (by omega_using []) (by omega_using []) (by omega_using [])
    have hbk : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hf := hp.facts
    have htr : tr s₀ k ≤ 256 := by unfold tr; split <;> omega_arith
    refine (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have kk := k'.drop ea
    have hb' := hb.keep kk (by simp) (by simp) m
    have hax' : s'.gpr .eax = BitVec.ofNat 32 (tr s₀ k) := by rw [ea, hax]
    refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
    · show s'.cf = _
      rw [c, hax, toNat_ofNat32 (by omega_using [htr])]
    · -- The byte is zero, and the index still below `ω`.
      have hc := of_decide_eq_true hc
      have hz : ¬ (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0 := fun h => by rw [tr, ite_pos' h] at hc; omega_using [hf, hc]
      have htk : tr s₀ k = i₀ s₀ + k + 1 := by rw [tr, ite_neg' hz]
      refine ⟨hb', by rw [hax', htk]; rfl, e, by omega_using [hc, htk], ?_⟩
      unfold TF at ht ⊢
      rw [optFold_range'_succ, ht, Option.bind_some]
      exact ite_neg' hz _ _
    · have hc := of_decide_eq_false hc
      refine ⟨hb', ?_⟩
      rw [hax']
      by_cases hz : (Y s₀).getD (i₀ s₀ + k) 0 ≠ 0
      · rw [tr, ite_pos' hz, TS_none e]
        have h1 : TF s₀ (k + 1) = none := by
          unfold TF at ht ⊢
          rw [optFold_range'_succ, ht, Option.bind_some]
          exact ite_pos' hz _ _
        unfold TF at h1 ⊢
        exact optFold_range'_none _ _ (show k + 1 ≤ ω s₀ - i₀ s₀ by omega_using [hl]) h1
      · have htk : tr s₀ k = i₀ s₀ + k + 1 := by rw [tr, ite_neg' hz]
        rw [htk] at hc ⊢
        rw [TS_some e, show i₀ s₀ + k + 1 = ω s₀ by omega_using [hl, hc]]
        rw [show ω s₀ - i₀ s₀ = k + 1 by omega_using [hl, hc]]
        unfold TF at ht ⊢
        rw [optFold_range'_succ, ht, Option.bind_some]
        exact ite_neg' hz _ _
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

theorem tloop_piece : Piece Pre Pub (TI 0) TFin (.loop (.seq (.block hbuTrailLoad)
    (.seq (.ite .ne hbuFail (.block [.alu .add .eax (.imm 1)])) (.block [.alu .cmp .eax (.mem (at_ .esp 28))]))) .b) :=
  loopC TI TFin (fun s₀ => ω s₀ - i₀ s₀) (fun k s₀ => decide (tr s₀ k < ω s₀))
    (fun k s₀ hp hc => by
      have hf := hp.facts
      have hc := of_decide_eq_true hc
      show k + 1 < ω s₀ - i₀ s₀
      unfold tr at hc
      split at hc <;> omega_arith)
    (fun k s₀ s₀' _ _ hq => by rw [hq.etr, hq.eω])
    fun k => Piece.seq (load_piece k) (Piece.seq (Piece.ite
      (fun s₀ => decide ((Y s₀).getD (i₀ s₀ + k) 0 ≠ 0)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by simp only [i₀, hq.ecK, hq.y]) (tfail_piece k) (tinc_piece k)) (tcmp_piece k))

theorem trail_piece : Piece Pre Pub (fun s₀ s => OM s₀ (K s₀) (PS s₀ (K s₀)) s) TFin hbuTrail := by
  refine Piece.seq t0_piece (Piece.ite (fun s₀ => decide (idxOf (PS s₀ (K s₀)) < ω s₀)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ePS, hq.eK, hq.eω]) ?_ ?_)
  · refine tloop_piece.mono (fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ?_) fun _ _ _ h => h
    have hc := of_decide_eq_true hc
    have hf := hp.facts
    cases e : PS s₀ (K s₀) with
    | none => rw [e] at hc; simp only [idxOf] at hc; omega
    | some st =>
      have ec : cK s₀ = st := by unfold cK; rw [e]; rfl
      rw [e] at hc hax
      refine ⟨hb, by rw [hax, Nat.add_zero]; simp only [idxOf, i₀, ec], by rw [ec]; exact e, ?_, rfl⟩
      simp only [idxOf] at hc
      simp only [i₀, ec]; omega_using [hc]
  · refine nil_piece fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ⟨hb, ?_⟩
    have hc := of_decide_eq_false hc
    rw [hax]
    cases e : PS s₀ (K s₀) with
    | none => unfold fin TS; rw [e]; rfl
    | some st =>
      have ec : cK s₀ = st := by unfold cK; rw [e]; rfl
      have hle := (hb.sr st e).1
      rw [e] at hc
      simp only [idxOf] at hc ⊢
      rw [TS_some (by rw [e, ec]) (by rw [show ω s₀ - i₀ s₀ = 0 by simp only [i₀, ec]; omega_using [hc]]; rfl)]
      congr 1; omega_using [hc, hle]

/-! ## The return value -/

/-- 1 if no check failed. -/
def res (s₀ : State) : BitVec 32 := match TS s₀ with
  | none => 0
  | some _ => 1

theorem ret_piece : Piece Pre Pub TFin (fun s₀ s => TB s₀ s ∧ s.gpr .eax = res s₀) (.block hbuRet) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨hb, hax⟩ => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega_using [])
    have v2 := hb.argw hp (i := 2) (by omega_using []) (by omega_using []) (by omega_using [])
    have hbk : WP isa (.block hbuRet) s fun s' =>
        s'.gpr .eax = 1 - 0 - (BitVec.ofBool (decide ((arg s₀ 2).toNat < (s.gpr .eax).toNat))).setWidth 32 ∧
          s'.mem = s.mem := by
      hrun [hbuRet, a2, i2, v2]
    have hf := hp.facts
    refine (WP.keep [.edx, .eax] hbk (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨hb.keep k (by simp) (by simp) m, ?_⟩
    rw [e, hax]
    cases hT : TS s₀ with
    | none =>
      have e1 : fin s₀ = 256 := by unfold fin; rw [hT]
      have e2 : res s₀ = 0 := by unfold res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega_using []), decide_eq_true (show (arg s₀ 2).toNat < 256 by simp only [ω] at hf; omega_using [hf])]
      rfl
    | some _ =>
      have e1 : fin s₀ = ω s₀ := by unfold fin; rw [hT]
      have e2 : res s₀ = 1 := by unfold res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega_using [hf]), decide_eq_false (Nat.lt_irrefl _)]
      rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

/-! ## The function -/

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ TB s₀ s ∧ s.gpr .eax = res s₀)
    (.seq (.block hbuZeroInit) (.seq (.loop (.block hbuZeroBody) .ne)
      (.seq (.block hbuSetup) (.seq (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) (.seq hbuTrail (.block hbuRet)))))) :=
  (Piece.seq zinit_piece <| Piece.seq zloop_piece <| Piece.seq setup_piece <| Piece.seq polys_piece <|
    Piece.seq trail_piece ret_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => TB s₀ s ∧ s.gpr .eax = res s₀) s₀ s') Impl.MlDsa.X86.Pack.hintBitUnpack :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.e0) body_piece

/-- The spec, as the result. -/
theorem hintBitUnpack_TS (s₀ : State) :
    hintBitUnpack (ω s₀) (K s₀) (bytesAt s₀.mem (rA s₀) (yL s₀)) = (TS s₀).map (·.1.toList) := by
  rw [hintBitUnpack_eq]
  change (match PS s₀ (K s₀) with
    | none => none
    | some (h, idx) => Option.map (fun _ => h.toList) (optFold (huTrail (Y s₀)) (List.range' idx (ω s₀ - idx)) ())) = _
  unfold TS
  cases PS s₀ (K s₀) with
  | none => rfl
  | some st =>
    obtain ⟨hA, idx⟩ := st
    simp only [Option.bind_some]
    cases optFold (huTrail (Y s₀)) (List.range' idx (ω s₀ - idx)) () <;> rfl

theorem TS_PS {s₀ : State} {st : Array (Vector Bool n) × Nat} (h : TS s₀ = some st) : PS s₀ (K s₀) = some st := by
  unfold TS at h
  cases e : PS s₀ (K s₀) with
  | none => rw [e] at h; cases h
  | some st' =>
    rw [e, Option.bind_some] at h
    cases e' : optFold (huTrail (Y s₀)) (List.range' st'.2 (ω s₀ - st'.2)) () with
    | none => rw [e'] at h; cases h
    | some _ => rw [e'] at h; cases h; rfl

end Up

/-- Memory with the arguments `0`, `84`, `80`, `0x1000` and `1024` at `0x5004`. -/
def unpackSatMem : Mem := fun a =>
  if a = 0x5008 then 84 else if a = 0x500c then 80 else if a = 0x5011 then 0x10 else if a = 0x5015 then 4 else 0

theorem hintBitUnpack_verified :
    Verified X86.target Impl.MlDsa.X86.Pack.hintBitUnpack (hintBitUnpackContract X86.abi 16) := by
  refine Piece.verified ((Up.piece.pre_mono (fun _ h => Up.Pre.of h)
    fun _ _ _ _ hq => Up.Pub.of hq).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨hb, hax⟩, hm, hax'⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := Up.Pre.of h₀
    obtain kH := Proof.MlKem.X86.leaf_keep (r := Up.hR s₀) hm (hp.hW _ List.mem_cons_self).1
      (by dsimp only; have := hp.w_fit; omega_arith)
    rw [setWidth_append32, hax', hax]
    show match hintBitUnpack (ω s₀) (Up.K s₀) (bytesAt s₀.mem (rA s₀) (Up.yL s₀)) with
      | some hint => Up.res s₀ = 1 ∧ HintIs s'.mem (wA s₀) (Up.K s₀) hint
      | none => Up.res s₀ = 0
    rw [Up.hintBitUnpack_TS]
    unfold Up.res
    cases e : Up.TS s₀ with
    | none => rfl
    | some st =>
      exact ⟨rfl, VG.Proof.MlDsa.Verify.hintIs_congr (fun i hi => kH i (by dsimp only; have := hp.hlen; omega_arith))
        (harr_hintIs (hb.sr st (Up.TS_PS e)).2)⟩
  · refine ⟨satState unpackSatMem [⟨0, 84⟩] [⟨0x1000, 4096⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlDsa.X86.Pack.Hint

end

end

/-!
# ML-DSA verification on x86 (32-bit), with this library's primitives

The x86 primitives (`Impl.MlDsa.X86.Verify.prims`) are verified against their
contracts, use at most 56 bytes of stack and write `esp` only by frames and
calls (`prims_ok`), so `vg_mldsa{44,65,87}_verify_core` meet theirs
(`verifyCore44_verified`, …), whose precondition a run of
`vg_mldsa*_prepare_verifying_key` satisfies (`PreparedKey.verify_core_sat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify (prims verify)

theorem prims_ok : PrimsOk prims where
  ntt := ⟨⟨15, by decide, Arith.NttFwd.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  invNtt := ⟨⟨15, by decide, Arith.NttInvP.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  mul := ⟨⟨15, by decide, Arith.mul_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  mulAdd := ⟨⟨15, by decide, Arith.mulAdd_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  sub := ⟨⟨15, by decide, Arith.sub_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  rejNtt := ⟨⟨55, by decide, Sample.RejNtt.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  ball := ⟨⟨55, by decide, Sample.Ball.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  useHint := ⟨⟨15, by decide, Round.useHint_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  simpleBitPack := ⟨⟨15, by decide, Pack.SimpleBitPack.verified⟩, by lit_decide,
    NoSp.of_all (by lit_decide)⟩
  bitUnpack := ⟨⟨15, by decide, Pack.Unpack.BU.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  unpackT1 := ⟨⟨15, by decide, Pack.Unpack.T1.verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩
  hintUnpack := ⟨⟨15, by decide, Pack.Hint.hintBitUnpack_verified⟩, by lit_decide,
    NoSp.of_all (by lit_decide)⟩
  normLt := ⟨⟨15, by decide, Round.normLt_verified⟩, by lit_decide, NoSp.of_all (by lit_decide)⟩

/-- `vg_mldsa{44,65,87}_verify_core` never write `esp`. -/
theorem verify_nosp (p : Spec.MlDsa.Params) : NoSp (verify prims p) := KeyGen.NoSp.leaf (body_nosp prims_ok p)

theorem verifyCore44_verified :
    Verified X86.target (verify prims Spec.MlDsa.mlDsa44) (verifyCoreContract Spec.MlDsa.mlDsa44 X86.abi 96) :=
  verify_verified prims_ok _ (.inl rfl) (PreparedKey.verify_core_sat prims_ok (.inl rfl))

theorem verifyCore65_verified :
    Verified X86.target (verify prims Spec.MlDsa.mlDsa65) (verifyCoreContract Spec.MlDsa.mlDsa65 X86.abi 96) :=
  verify_verified prims_ok _ (.inr (.inl rfl)) (PreparedKey.verify_core_sat prims_ok (.inr (.inl rfl)))

theorem verifyCore87_verified :
    Verified X86.target (verify prims Spec.MlDsa.mlDsa87) (verifyCoreContract Spec.MlDsa.mlDsa87 X86.abi 96) :=
  verify_verified prims_ok _ (.inr (.inr rfl)) (PreparedKey.verify_core_sat prims_ok (.inr (.inr rfl)))

end VG.Proof.MlDsa.X86.Verify
