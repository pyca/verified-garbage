import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Hint

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpack`. -/
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

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

namespace Up

section
variable (s₀ : State)
/-- `len`, `hlen`, `k`. -/
abbrev yL : Nat := (arg s₀ 1).toNat
abbrev hL : Nat := (arg s₀ 4).toNat
abbrev K : Nat := VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ - ω s₀
/-- `h`, and the argument slot `i`. -/
abbrev hR : Region := ⟨wA s₀, VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀ * 4⟩
abbrev slot (i : Nat) : Region := ⟨argAddr s₀ i, 4⟩
/-- What the body changes. -/
abbrev W : List Region := [VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀, VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ 1, VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ 4]
/-- The input. -/
abbrev Y : Array Byte := (bytesAt s₀.mem (rA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀)).toArray
abbrev yb (t : Nat) : Nat := ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD t 0).toNat
/-- The spec's state after `i` polynomials. -/
abbrev PS (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range i) (Array.replicate (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) noHint, 0)
/-- The bound of polynomial `i`. -/
abbrev bnd (i : Nat) : Nat := VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (ω s₀ + i)
end

/-- The index of a state of the spec, or 256 for a failed check. -/
def idxOf : Option (Array (Vector Bool n) × Nat) → Nat
  | none => 256
  | some st => st.2

/-- Unless a check failed, the words of `h` are the hint, and the index is at
most `ω`. -/
def SR (s₀ : State) (o : Option (Array (Vector Bool n) × Nat)) (m : Mem) : Prop :=
  ∀ st, o = some st → st.2 ≤ ω s₀ ∧ HArr m (wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) st.1

theorem SR.none (s₀ : State) (m : Mem) : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ none m := fun _ h => nomatch h

theorem SR.congr {s₀ : State} {o : Option (Array (Vector Bool n) × Nat)} {m m' : Mem} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ o m)
    (hm : ∀ t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀, coeffAt m' (wA s₀) t = coeffAt m (wA s₀) t) : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ o m' :=
  fun st e => ⟨(h st e).1, harr_congr (h st e).2 hm⟩

structure Pre (s₀ : State) : Prop extends Lay s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀ * 4) where
  par : (ω s₀, VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∈ hintParams
  le : ω s₀ ≤ VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀
  hlen : VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀ = 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀

theorem Pre.of {s₀ : State} (h : (hintBitUnpackContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀ := by
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18⟩

theorem Pre.facts {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) :
    4 ≤ VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ ≤ 8 ∧ ω s₀ ≤ 80 ∧ ω s₀ + VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀ = 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ := by
  have := mem_hintParams hp.par
  have := hp.le
  have := hp.hlen
  have e : VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ - ω s₀ := rfl
  omega

/-- The public data: `esp`, the arguments and the input. -/
structure Pub (s₀ s₀' : State) : Prop where
  e0 : E0 s₀ = E0 s₀'
  a0 : arg s₀ 0 = arg s₀' 0
  a1 : arg s₀ 1 = arg s₀' 1
  a2 : arg s₀ 2 = arg s₀' 2
  a3 : arg s₀ 3 = arg s₀' 3
  a4 : arg s₀ 4 = arg s₀' 4
  y : VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀'

theorem Pub.of {s₀ s₀' : State} (h : (hintBitUnpackContract X86.abi 16).pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀' := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e, hl, a0, a1, a2, a3, a4⟩ := h
  exact ⟨e, a0, a1, a2, a3, a4, congrArg List.toArray (map_toNat_inj hl)⟩

theorem Pub.eK {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀' := by
  show (arg s₀ 1).toNat - (arg s₀ 2).toNat = (arg s₀' 1).toNat - (arg s₀' 2).toNat; rw [h.a1, h.a2]
theorem Pub.eω {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') : ω s₀ = ω s₀' := by
  show (arg s₀ 2).toNat = (arg s₀' 2).toNat; rw [h.a2]
theorem Pub.eyb {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (t : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ t = VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀' t := by
  show ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD t 0).toNat = ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀').getD t 0).toNat; rw [h.y]
theorem Pub.ePS {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (i : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i = VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀' i := by
  show optFold (huPoly (ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range i) (Array.replicate (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) noHint, 0) =
    optFold (huPoly (ω s₀') (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀')) (List.range i) (Array.replicate (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀') noHint, 0)
  rw [h.y, h.eω, h.eK]
theorem Pub.ebnd {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (i : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i = VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀' i := by
  show VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (ω s₀ + i) = VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀' (ω s₀' + i); rw [h.eω, h.eyb]

/-! ## Regions -/

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀)
include hp

theorem argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = (E0 s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  ea_off (by have := hp.sp'; unfold E0 at this; omega)

theorem slot_disj {i j : Nat} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) : (VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ i).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ j) := by
  rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.slot, VG.Proof.MlDsa.X86.Pack.Hint.Up.slot, hp.argAddr_eq hi, hp.argAddr_eq hj]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem slot_sub {i : Nat} (hi : i < 5) : Region.Sub (VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ i) (gR s₀) :=
  sub_of_contains (arg_contains (n := 5) hi hp.sp')

theorem h_slot {i : Nat} (hi : i < 5) : (VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ i) := hp.w_g.sub_right (hp.slot_sub hi)

/-- The slots of `y`, `ω` and `h` are apart from `W`. -/
theorem slotW {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : ∀ r ∈ VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀, (VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ i).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.h_slot hi).symm
  · exact hp.slot_disj hi (by omega) h1
  · exact hp.slot_disj hi (by omega) h4

theorem yW : ∀ r ∈ VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀, (⟨rA s₀, VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.r_w
  · exact hp.r_g.sub_right (hp.slot_sub (by omega))
  · exact hp.r_g.sub_right (hp.slot_sub (by omega))

theorem hW : ∀ r ∈ VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have st := hp.stk_eq
  rcases hr with rfl | rfl | rfl
  · exact ⟨st ▸ hp.stk_w, hp.ret_w⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega)), hp.ret_g.sub_right (hp.slot_sub (by omega))⟩
  · exact ⟨(st ▸ hp.stk_g).sub_right (hp.slot_sub (by omega)), hp.ret_g.sub_right (hp.slot_sub (by omega))⟩

/-- A word of `h` is apart from the slots. -/
theorem coeff_slot {t j : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (hj : j < 5) :
    Mem.Sep (coeffAddr (wA s₀) t) 4 (argAddr s₀ j) (32 / 8) := by
  have := hp.facts
  have hc : (VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega) (by omega)
  exact (hp.h_slot hj).sep hc (Region.contains_self _ _)

theorem slot_coeff {t j : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (hj : j < 5) :
    Mem.Sep (argAddr s₀ j) 4 (coeffAddr (wA s₀) t) (32 / 8) := by
  have := hp.facts
  have hc : (VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀).Contains (coeffAddr (wA s₀) t) 4 := Offset.contains_base _ (by omega) (by omega)
  exact (hp.h_slot hj).symm.sep (Region.contains_self _ _) hc

theorem coeff_frame {m : Mem} {j : Nat} (hj : j < 5) (v : BitVec 32) :
    ∀ t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀, coeffAt (m.writeW (argAddr s₀ j) v) (wA s₀) t = coeffAt m (wA s₀) t :=
  fun t ht => Mem.readW_writeW_sep (hp.coeff_slot ht hj) (by decide)

end Pre

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀) (P0 s₀).mem s.mem

theorem Base.keep {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s) {rs : List Reg} (k : Keep rs s s') (hsp : Reg.esp ∉ rs)
    (hm : Frame (VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀) s.mem s'.mem) : VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s' :=
  ⟨(k.gpr hsp).trans h.esp, k.2.1.trans h.rd, k.2.2.trans h.wr, h.frame.trans hm⟩

namespace Base
variable {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s)
include hp h

theorem argw {i : Nat} (hi : i < 5) (h1 : i ≠ 1) (h4 : i ≠ 4) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  rw [h.frame.readW (Region.contains_self _ _) (hp.slotW hi h1 h4) (by decide)]
  exact hp.P0_argw hi

theorem argIn {i : Nat} (hi : i < 5) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := hp.argIn h.rd h.wr hi

theorem argOut {i : Nat} (hi : i < 5) : InRegions s.wr (argAddr s₀ i) 4 := hp.argOut h.wr hi

/-- A byte of `y`. -/
theorem ybyte {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀) : s.mem (rA s₀ + BitVec.ofNat 64 t) = (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD t 0 := by
  rw [hp.r_keep h.frame hp.yW ht, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]

theorem inY {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀) : InRegions (s.rd ++ s.wr) (rA s₀ + BitVec.ofNat 64 t) 1 := by
  have := hp.r_fit
  rw [h.rd, h.wr, pushed_rd, hp.rd]
  exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩

theorem inH {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) : InRegions s.wr (coeffAddr (wA s₀) t) 4 := by
  have := hp.facts
  have := hp.w_fit
  rw [h.wr, P0_wr, hp.wr]
  exact ⟨VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩

end Base

theorem frame_slot {s₀ : State} {m : Mem} {j : Nat} (hj : j = 1 ∨ j = 4) (v : BitVec 32) :
    Frame (VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀) m (m.writeW (argAddr s₀ j) v) := by
  rcases hj with rfl | rfl
  · exact (Frame.refl _ _).writeW (r := VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ 1) (by simp) _ (Region.contains_self _ _)
  · exact (Frame.refl _ _).writeW (r := VG.Proof.MlDsa.X86.Pack.Hint.Up.slot s₀ 4) (by simp) _ (Region.contains_self _ _)

theorem frame_coeff {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {m : Mem} {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (v : BitVec 32) :
    Frame (VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀) m (m.writeW (coeffAddr (wA s₀) t) v) := by
  have := hp.facts
  exact (Frame.refl _ _).writeW (r := VG.Proof.MlDsa.X86.Pack.Hint.Up.hR s₀) (by simp) _ (Offset.contains_base _ (by omega) (by omega))

/-- A word of `h`. -/
theorem hAddr {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {t : Nat} (ht : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) :
    addr (arg s₀ 3 + BitVec.ofNat 32 (4 * t)) 0 = coeffAddr (wA s₀) t := by
  have := hp.facts; have := hp.w_fit; rw [addr_add (by omega), Nat.add_zero]

/-- A byte of `y`. -/
theorem yAddr {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀) :
    addr (arg s₀ 0 + BitVec.ofNat 32 t) 0 = rA s₀ + BitVec.ofNat 64 t := by
  have := hp.r_fit; rw [addr_add (by omega), Nat.add_zero]

theorem yb_lt (s₀ : State) (t : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ t < 256 := ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD t 0).isLt

/-! ## Zeroing `h` -/

/-- After `t` words. -/
structure ZI (s₀ : State) (t : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s where
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (4 * t)
  edx : s.gpr .edx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀ - t)
  eax : s.gpr .eax = 0
  zero : ∀ u < t, coeffAt s.mem (wA s₀) u = 0
  len : s.mem.readW (argAddr s₀ 1) 32 = arg s₀ 1

theorem zinit_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI · 0) (.block hbuZeroInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_) (by taint_decide)
  · subst e
    have b₀ : VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a3 : addr ((P0 s₀).gpr .esp) 32 = argAddr s₀ 3 := argEa rfl 3
    have a4 : addr ((P0 s₀).gpr .esp) 36 = argAddr s₀ 4 := argEa rfl 4
    have i3 := b₀.argIn hp (i := 3) (by omega)
    have i4 := b₀.argIn hp (i := 4) (by omega)
    have v3 := hp.P0_argw (i := 3) (by omega)
    have v4 := hp.P0_argw (i := 4) (by omega)
    have hb : WP isa (.block hbuZeroInit) (P0 s₀) fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edx = arg s₀ 4 ∧
        s'.gpr .eax = 0 ∧ s'.mem = (P0 s₀).mem := by
      hrun [hbuZeroInit, a3, a4, i3, i4, v3, v4]
    refine (WP.keep [.ecx, .edx, .eax] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨b₀.keep k (by decide) (by rw [m]; exact Frame.refl _ _), by rw [e1]; simp, by rw [e2]; simp, e3,
        fun u hu => absurd hu (Nat.not_lt_zero _), by rw [m]; exact hp.P0_argw (by omega)⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.e0]

theorem zstep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀) {s : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI s₀ t s) :
    WP isa (.block hbuZeroBody) s fun s' => VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI s₀ (t + 1) s' ∧ isa.eval .ne s' = some (decide (t + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀)) := by
  have hf := hp.facts
  have ht' : t < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ := by omega
  have ea : addr (s.gpr .ecx) 0 = coeffAddr (wA s₀) t := by rw [h.ecx]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.hAddr hp ht'
  have hin := h.inH hp ht'
  have hb : WP isa (.block hbuZeroBody) s fun s' => s'.gpr .ecx = s.gpr .ecx + 4 ∧ s'.gpr .edx = s.gpr .edx - 1 ∧
      s'.zf = some (s.gpr .edx - 1 == 0) ∧ s'.mem = s.mem.writeW (coeffAddr (wA s₀) t) (s.gpr .eax) := by
    hrun [hbuZeroBody, ea, hin]
  refine (WP.keep [.ecx, .edx] hb (by decide)).mono fun s' ⟨⟨e1, e2, z, m⟩, k⟩ => ?_
  refine ⟨⟨h.keep k (by decide) (by rw [m]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_coeff hp ht' _), by rw [e1, h.ecx, add_four']; congr 2,
    by rw [e2, h.edx]; exact cnt_next ht, by rw [k.gpr (by decide), h.eax], fun u hu => ?_,
    by rw [m, Mem.readW_writeW_sep (hp.slot_coeff ht' (j := 1) (by omega)) (by decide), h.len]⟩,
    eval_ne_cnt ht (by omega) (by rw [z, h.edx])⟩
  rw [m, h.eax]
  by_cases e : u = t
  · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32]
  · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      ← coeffAt_eq, h.zero u (by omega)]

theorem zloop_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI · 0) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀) s) (.loop (.block hbuZeroBody) .ne) :=
  countLoopN (fun t s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI s₀ t s) VG.Proof.MlDsa.X86.Pack.Hint.Up.hL (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.hL, hq.a4]) [.ecx] (fun t s₀ s hp h ht => VG.Proof.MlDsa.X86.Pack.Hint.Up.zstep hp ht h)
    (fun t s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ecx, h'.ecx, hq.a3]) (by taint_decide)

/-! ## The state of the loops -/

/-- The registers and slots of polynomial `i`. -/
structure Ptr (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  esi : s.gpr .esi = 1
  ecx : s.gpr .ecx = arg s₀ 3 + BitVec.ofNat 32 (1024 * i)
  cnt : s.mem.readW (argAddr s₀ 1) 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ - i)
  ptr : s.mem.readW (argAddr s₀ 4) 32 = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i)

/-- `Ptr`, after a block that writes only the registers `rs` (not those of
`Ptr`) and not memory. -/
theorem Ptr.keep {s₀ s s' : State} {i : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s) {rs : List Reg} (k : Keep rs s s')
    (hrs : ∀ r ∈ rs, r = .eax ∨ r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) : VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s' := by
  have g : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .edx → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a b c d =>
    k.gpr fun hr => by rcases hrs r hr with e | e | e | e <;> contradiction
  exact ⟨h.toBase.keep k (fun hr => by rcases hrs _ hr with e | e | e | e <;> cases e)
      (by rw [hm]; exact Frame.refl _ _),
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.edi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), h.ecx], by rw [hm, h.cnt], by rw [hm, h.ptr]⟩

/-- Before polynomial `i` (or after it, with the spec's state `o`). -/
structure OM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s where
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf o)
  sr : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ o s.mem

theorem setup_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.ZI s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.hL s₀) s) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ 0 (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ 0) s)
    (.block hbuSetup) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a0 : addr (s.gpr .esp) 20 = argAddr s₀ 0 := argEa h.esp 0
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have a3 : addr (s.gpr .esp) 32 = argAddr s₀ 3 := argEa h.esp 3
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i0 := h.argIn hp (i := 0) (by omega)
    have i1 := h.argIn hp (i := 1) (by omega)
    have i2 := h.argIn hp (i := 2) (by omega)
    have i3 := h.argIn hp (i := 3) (by omega)
    have o1 := h.argOut hp (i := 1) (by omega)
    have o4 := h.argOut hp (i := 4) (by omega)
    have v0 := h.argw hp (i := 0) (by omega) (by omega) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have v3 := h.argw hp (i := 3) (by omega) (by omega) (by omega)
    have v1 := h.len
    have hb : WP isa (.block hbuSetup) s fun s' => s'.gpr .ecx = arg s₀ 3 ∧ s'.gpr .edi = arg s₀ 0 ∧
        s'.gpr .esi = 1 ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 1) (arg s₀ 1 - arg s₀ 2)).writeW (argAddr s₀ 4) (arg s₀ 0 + arg s₀ 2) := by
      hrun [hbuSetup, a0, a1, a2, a3, a4, i0, i1, i2, i3, o1, o4, v0, v1, v2, v3]
    have hf := hp.facts
    have l1 := (arg s₀ 1).isLt
    have l2 := (arg s₀ 2).isLt
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    refine (WP.keep [.ecx, .edi, .edx, .esi] hb (by decide)).mono fun s' ⟨⟨e1, e2, e3, m⟩, k⟩ =>
      ⟨⟨h.keep k (by decide) (by rw [m]; exact (VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_slot (.inl rfl) _).trans (VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_slot (.inr rfl) _)),
        e2, e3, by rw [e1]; simp, ?_, ?_⟩, by rw [k.gpr (by decide), h.eax]; rfl, ?_⟩
    · rw [m, Mem.readW_writeW_sep s14 (by decide), Mem.readW_writeW_self32]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.K, VG.Proof.MlDsa.X86.Pack.Hint.Up.yL, ω] at hf ⊢
      omega
    · rw [m, Mem.readW_writeW_self32]; simp
    · rintro st e
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.PS, List.range_zero, optFold, Option.some.injEq] at e
      subst e
      refine ⟨Nat.zero_le _, harr_zero fun t ht => ?_⟩
      rw [m, hp.coeff_frame (by omega) _ t ht, hp.coeff_frame (by omega) _ t ht]
      exact h.zero t (by omega)
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackLoop`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the coefficients of a polynomial

Once the bound `y[ω + i]` of polynomial `i` has passed its checks, the code
sets the coefficients `y[index]` up to it (`coefs_piece`), following `huStep`
from the spec's state `cur s₀ i` before the polynomial: after `t` of them the
spec's state is `G s₀ i t`, and `eax` its index (or 256 once a check fails,
which ends the loop).
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state before polynomial `i`, if no check failed. -/
def cur (s₀ : State) (i : Nat) : Array (Vector Bool n) × Nat := (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i).getD (#[], 0)

/-- Its index. -/
abbrev fst (s₀ : State) (i : Nat) : Nat := (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2

/-- ... and after `t` of the coefficients of polynomial `i`. -/
def G (s₀ : State) (i t : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huStep (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀) i (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)) (List.range t) (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i)

theorem Pub.ecur {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (i : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i = VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀' i := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.cur; rw [h.ePS]

theorem Pub.eG {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (i t : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t = VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀' i t := by
  show optFold (huStep (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀) i (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2) (List.range t) (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i) =
    optFold (huStep (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀') i (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀' i).2) (List.range t) (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀' i)
  rw [h.ecur, h.y]

theorem G_succ (s₀ : State) (i t : Nat) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (t + 1) = (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t).bind fun st => huStep (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀) i (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i) st t :=
  optFold_range_succ _ _ _

theorem G_idx (s₀ : State) (i : Nat) : ∀ {t : Nat} {st : Array (Vector Bool n) × Nat}, VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t = some st →
    st.2 = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + t
  | 0, st, h => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.G, List.range_zero, optFold, Option.some.injEq] at h; subst h; rfl
  | t + 1, st, h => by
    rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_succ] at h
    cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t with
    | none => rw [e] at h; cases h
    | some st' =>
      rw [e, Option.bind_some] at h
      rw [huStep_idx h, VG.Proof.MlDsa.X86.Pack.Hint.Up.G_idx s₀ i e]; omega

theorem idxOf_G {s₀ : State} {i t : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t) < 256) : ∃ st, VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t = some st ∧
    VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t) = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + t := by
  cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t with
  | none => rw [e] at h; exact absurd h (by decide)
  | some st => exact ⟨st, rfl, VG.Proof.MlDsa.X86.Pack.Hint.Up.G_idx s₀ i e⟩

theorem PS_succ (s₀ : State) (i : Nat) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1) = (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i).bind fun st => huPoly (ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀) st i :=
  optFold_range_succ _ _ _

theorem bnd_lt (s₀ : State) (i : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < 256 := VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt _ _

/-- A bound less than the index fails. -/
theorem PS_fail₁ {s₀ : State} {i : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1) = none := by
  rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_succ]
  cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i with
  | none => rfl
  | some st =>
    rw [e] at h
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inl h) _ _

/-- A bound greater than `ω` fails. -/
theorem PS_fail₂ {s₀ : State} {i : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i > ω s₀) : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1) = none := by
  rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_succ]
  cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i with
  | none => rfl
  | some st =>
    simp only [Option.bind_some, huPoly]
    exact ite_pos' (.inr h) _ _

/-- Otherwise the coefficients follow. -/
theorem PS_ok {s₀ : State} {i : Nat} (h₁ : ¬ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) (h₂ : ¬ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i > ω s₀) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i ≤ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1) = VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i) := by
  cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i with
  | none => rw [e] at h₁; exact absurd (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i) h₁
  | some st =>
    have ec : VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i = st := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.cur; rw [e]; rfl
    have ef : VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i = st.2 := by show (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2 = _; rw [ec]
    have eb : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i = ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (ω s₀ + i) 0).toNat := rfl
    rw [e] at h₁
    simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf] at h₁
    refine ⟨by rw [ec], by omega, ?_⟩
    rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_succ, e, Option.bind_some, huPoly, ite_neg' (by omega), VG.Proof.MlDsa.X86.Pack.Hint.Up.G]
    show _ = optFold (huStep (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀) i (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2) (List.range (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2)) (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i)
    rw [ec]

/-! ## The state within a polynomial -/

/-- Within polynomial `i`, whose bound passed its checks, with the spec's
state `o`. -/
structure IM (s₀ : State) (i : Nat) (o : Option (Array (Vector Bool n) × Nat)) (s : State) : Prop
    extends VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s where
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf o)
  sr : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ o s.mem
  hi : i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀
  some : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i)
  fb : VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i ≤ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i
  bw : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i ≤ ω s₀

/-- `IM`, after a block that writes only `edx`, `ebp` and the flags. -/
theorem IM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i o s)
    (k : Keep [.edx, .ebp] s s') (hm : s'.mem = s.mem) : VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp) hm,
    by rw [k.gpr (by decide), h.ebx], by rw [k.gpr (by decide), h.eax], by rw [hm]; exact h.sr, h.hi, h.some,
    h.fb, h.bw⟩

theorem idx_lt_yL {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} {s : State}
    (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i o s) {t : Nat} (ht : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) : t < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ := by
  have := hp.facts; have := h.bw; omega

/-- The `SR` of `G`, from that of the state before. -/
theorem SR_G {s₀ : State} {i t : Nat} {m : Mem} (hfb : VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + t ≤ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) (hbw : VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i ≤ ω s₀)
    (h : ∀ st, VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t = some st → HArr m (wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) st.1) : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t) m :=
  fun st e => ⟨by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_idx s₀ i e]; omega, h st e⟩

/-! ## Setting a coefficient -/

/-- `ebp ← 4b + ecx`, the word of coefficient `b` of polynomial `i`. -/
theorem setAddr {x : BitVec 32} {i b : Nat} (hx : x.toNat + 1024 * i + 4 * b + 4 ≤ 2 ^ 32) :
    addr (BitVec.ofNat 32 b + BitVec.ofNat 32 b + (BitVec.ofNat 32 b + BitVec.ofNat 32 b) +
      (x + BitVec.ofNat 32 (1024 * i))) 0 = x.setWidth 64 + BitVec.ofNat 64 (4 * (256 * i + b)) := by
  rw [ofNat_add_ofNat, ofNat_add_ofNat, BitVec.add_comm, BitVec.add_assoc, ofNat_add_ofNat,
    addr_add (by omega)]
  congr 2; omega

theorem set_wp {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {i b : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s) (hi : i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (hb : b < 256)
    (hebp : s.gpr .ebp = BitVec.ofNat 32 b) :
    WP isa (.block hbuSet) s fun s' => (s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) ∧ Keep [.ebp, .eax] s s' := by
  have hf := hp.facts
  have hw := hp.w_fit
  have ht : 256 * i + b < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ := by omega
  have ea : addr (s.gpr .ebp + s.gpr .ebp + (s.gpr .ebp + s.gpr .ebp) + s.gpr .ecx) 0 =
      coeffAddr (wA s₀) (256 * i + b) := by
    rw [hebp, h.ecx]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.setAddr (by omega)
  have hin := h.inH hp ht
  refine WP.keep _ ?_ (by decide)
  hrun [hbuSet, ea, hin, h.esi]

/-- After setting coefficient `b` of polynomial `i`. -/
theorem sr_set {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {i b : Nat} (hi : i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (hb : b < 256) {m : Mem}
    {hA : Array (Vector Bool n)} (hh : HArr m (wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) hA) :
    HArr (m.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) (wA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (huSet i b hA) := by
  have := hp.facts
  exact harr_set (by omega) hh hi hb

/-- The frame of the write. -/
theorem ptr_set {s₀ s s' : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {i b : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s) (hi : i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (hb : b < 256)
    (k : Keep [.ebp, .eax] s s') (hm : s'.mem = s.mem.writeW (coeffAddr (wA s₀) (256 * i + b)) (1 : BitVec 32)) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.Ptr s₀ i s' := by
  have hf := hp.facts
  have ht : 256 * i + b < 256 * VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ := by omega
  have g : ∀ r, r ≠ .eax → r ≠ .ebp → s'.gpr r = s.gpr r := fun r a c =>
    k.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun hh => hh.elim c a)
  exact ⟨h.toBase.keep k (by decide) (by rw [hm]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_coeff hp ht _),
    by rw [g _ (by decide) (by decide), h.edi], by rw [g _ (by decide) (by decide), h.esi],
    by rw [g _ (by decide) (by decide), h.ecx],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega)) (by decide), h.cnt],
    by rw [hm, Mem.readW_writeW_sep (hp.slot_coeff ht (by omega)) (by decide), h.ptr]⟩

theorem idxOf_le {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre s₀) {o : Option (Array (Vector Bool n) × Nat)} {m : Mem}
    (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ o m) : VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf o ≤ 256 := by
  cases o with
  | none => exact Nat.le_refl _
  | some st => have := (h st rfl).1; have := hp.facts; show st.2 ≤ 256; omega

theorem G_next {s₀ : State} {i t : Nat} {st : Array (Vector Bool n) × Nat} (e : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i t = some st) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (t + 1) = if st.2 > VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (st.2 - 1) ≥ VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ st.2 then none
      else some (huSet i (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ st.2) st.1, st.2 + 1) := by
  rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_succ, e]; rfl

theorem G_one (s₀ : State) (i : Nat) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 1 = some (huSet i (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)) (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).1, VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + 1) := by
  rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_next (t := 0) rfl, ite_neg' (fun h => Nat.lt_irrefl _ h.1)]

/-- `cmp eax, ebx`: whether the index is below the bound. -/
theorem cmp_piece (i : Nat) (o : State → Option (Array (Vector Bool n) × Nat)) (X : State → Prop) :
    Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (o s₀) s ∧ X s₀)
      (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (o s₀) s ∧ X s₀) ∧ isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (o s₀) < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)))
      (.block [.alu .cmp .eax (.reg .ebx)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hb : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .eax).toNat < (s.gpr .ebx).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
        s'.mem = s.mem := by hrun
  have hl := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_le hp h.sr
  have hb' := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
  refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k⟩ =>
    ⟨⟨h.keep ⟨fun r _ => (k.drop ea).gpr (by simp), k.2⟩ m, hx⟩, ?_⟩
  show s'.cf = _
  rw [c, h.eax, h.ebx, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]

/-- The first coefficient: `ebp = y[index]`. -/
theorem first_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)))
    (.block hbuFirst) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp ⟨h, hl⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_) (by taint_decide)
  · have hy := VG.Proof.MlDsa.X86.Pack.Hint.Up.idx_lt_yL hp h hl
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i) := by
      rw [h.edi, h.eax]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block hbuFirst) s fun s' => s'.gpr .ebp = BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i) 0) ∧
        s'.mem = s.mem := by
      hrun [hbuFirst, ea, hin, hv]
    exact (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ => ⟨⟨h.keep k m, hl⟩, by rw [e, byte32]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.edi, h'.edi, hq.a0]
    · rw [h.eax, h'.eax, hq.eG]

/-- The first coefficient set, and whether the index is below the bound. -/
theorem set1_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) ∧ s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)))
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 1) s ∧ isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)))
    (.block (hbuSet ++ ([.alu .cmp .eax (.reg .ebx)] : List Instr))) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨h, hl⟩, he⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨h, _⟩, he⟩ ⟨⟨h', _⟩, he'⟩ r hr => ?_) (by taint_decide)
  · have hb' := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
    have hbw := h.bw
    have hf := hp.facts
    refine WP.block_append ((VG.Proof.MlDsa.X86.Pack.Hint.Up.set_wp hp h.toPtr h.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) he).mono fun s₁ ⟨⟨e1, m1⟩, k1⟩ => ?_)
    have hc : WP isa (.block [.alu .cmp .eax (.reg .ebx)]) s₁ fun s' =>
        s'.cf = some (decide ((s₁.gpr .eax).toNat < (s₁.gpr .ebx).toNat)) ∧ s'.gpr .eax = s₁.gpr .eax ∧
          s'.mem = s₁.mem := by hrun
    refine (WP.keep [.eax] hc (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨(VG.Proof.MlDsa.X86.Pack.Hint.Up.ptr_set hp h.toPtr h.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) k1 m1).keep k (fun r hr => by simp at hr) m, ?_, ?_, ?_, h.hi,
      h.some, h.fb, h.bw⟩, ?_⟩
    · rw [k.gpr (by simp), k1.gpr (by decide), h.ebx]
    · rw [k.gpr (by simp), e1, h.eax, VG.Proof.MlDsa.X86.Pack.Hint.Up.G_one]; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf]; rw [ofNat_add_one]; rfl
    · rw [m, m1]
      refine VG.Proof.MlDsa.X86.Pack.Hint.Up.SR_G (t := 1) (by omega) hbw fun st e => ?_
      rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_one, Option.some.injEq] at e
      subst e
      obtain ⟨-, hh⟩ := h.sr (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i) (by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G]; rfl)
      exact VG.Proof.MlDsa.X86.Pack.Hint.Up.sr_set hp h.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) hh
    · show s'.cf = _
      rw [c, e1, h.eax, k1.gpr (by decide), h.ebx]
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.G, List.range_zero, optFold, VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf]
      have : VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i = (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2 := rfl
      rw [ofNat_add_one, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2) = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀' (VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀' i).2)
      rw [hq.ecur, hq.eyb]
    · rw [h.ecx, h'.ecx, hq.a3]

/-! ## The coefficients after the first -/

/-- Before iteration `k` of the loop: `k + 1` coefficients set, and the
index below the bound. -/
def NI (i k : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 1)) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 1)) = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i

/-- `ebp = y[index]`, and whether `y[index - 1] < y[index]`. -/
theorem loads_piece (i k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Up.NI i k)
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1))))
    (.block hbuLoads) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · obtain ⟨hI, hx, hl⟩ := h
    have hy := VG.Proof.MlDsa.X86.Pack.Hint.Up.idx_lt_yL hp hI hl
    have hax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1) := by rw [hI.eax, hx]
    have ea1 : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1) := by
      rw [hI.edi, hax]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.yAddr hp hy
    have ea2 : addr (s.gpr .edi + s.gpr .eax - 1) 0 = rA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) := by
      rw [hI.edi, hax, add_sub_one' _ (by omega)]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.yAddr hp (by omega)
    have i1 := hI.inY hp hy
    have i2 := hI.inY hp (t := VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) (by omega)
    have v1 := hI.ybyte hp hy
    have v2 := hI.ybyte hp (t := VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) (by omega)
    have hb : WP isa (.block hbuLoads) s fun s' =>
        s'.gpr .ebp = BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) 0)).toNat <
          (BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1) 0)).toNat)) ∧ s'.mem = s.mem := by
      hrun [hbuLoads, ea1, ea2, i1, i2, v1, v2]
    refine (WP.keep [.edx, .ebp] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k'⟩ =>
      ⟨⟨⟨hI.keep k' m, hx, hl⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, toNat_setWidth32_8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.1.eax, h'.1.eax, hq.eG]

theorem G_some {s₀ : State} {i k : Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 1)) = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1) (hl : VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 < 256) :
    ∃ st, VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 1) = some st ∧ st.2 = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 := by
  obtain ⟨st, e, -⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_G (s₀ := s₀) (i := i) (t := k + 1) (by omega)
  exact ⟨st, e, by rw [e] at h; exact h⟩

/-- A coefficient greater than the previous one: set it. -/
theorem set2_piece (i k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Hint.Up.NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1)))) ∧
      decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1)) = true)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2)) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) (.block hbuSet) := by
  refine Piece.taint [.ebp, .ecx] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨hn, he⟩, _⟩, _⟩ ⟨⟨⟨hn', he'⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have hlt := of_decide_eq_true hb
    have hb' := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
    obtain ⟨st, e, est⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.G_some hx (by omega)
    have hG : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2) = some (huSet i (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1)) st.1, VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 + 1) := by
      rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_next e, est, ite_neg' (fun h => by
        rw [show VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 - 1 = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k by omega] at h; omega)]
    refine (VG.Proof.MlDsa.X86.Pack.Hint.Up.set_wp hp hI.toPtr hI.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) he).mono fun s' ⟨⟨e1, m1⟩, k1⟩ =>
      ⟨⟨VG.Proof.MlDsa.X86.Pack.Hint.Up.ptr_set hp hI.toPtr hI.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) k1 m1, by rw [k1.gpr (by decide), hI.ebx], ?_, ?_, hI.hi, hI.some,
        hI.fb, hI.bw⟩, hl⟩
    · rw [e1, hI.eax, hx, hG]; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf]; rw [ofNat_add_one]
    · rw [m1]
      refine VG.Proof.MlDsa.X86.Pack.Hint.Up.SR_G (t := k + 2) (by omega) hI.bw fun st' e' => ?_
      rw [hG, Option.some.injEq] at e'
      subst e'
      exact VG.Proof.MlDsa.X86.Pack.Hint.Up.sr_set hp hI.hi (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb_lt s₀ _) (hI.sr st e).2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [he, he']
      show BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ ((VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀ i).2 + k + 1)) = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀' ((VG.Proof.MlDsa.X86.Pack.Hint.Up.cur s₀' i).2 + k + 1))
      rw [hq.ecur, hq.eyb]
    · rw [hn.1.ecx, hn'.1.ecx, hq.a3]

/-- A coefficient not greater than the previous one: fail. -/
theorem fail2_piece (i k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Hint.Up.NI i k s₀ s ∧ s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1))) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1)))) ∧
      decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1)) = false)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2)) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨hI, hx, hl⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hge := of_decide_eq_false hb
  have hb' := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
  obtain ⟨st, e, est⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.G_some hx (by omega)
  have hG : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2) = none := by
    rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_next e, est, ite_pos' ⟨by omega, by rw [show VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 - 1 = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k by omega]; omega⟩]
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨⟨hI.toPtr.keep k' (fun r hr => by simp at hr; simp [hr]) m, by rw [k'.gpr (by decide), hI.ebx],
      by rw [e1, hG]; rfl, by rw [hG]; exact SR.none _ _, hI.hi, hI.some, hI.fb, hI.bw⟩, hl⟩

theorem loop_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 1) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)) s) (.loop hbuNext .b) := by
  refine (loopC (VG.Proof.MlDsa.X86.Pack.Hint.Up.NI i) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)) s) (fun s₀ => VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)
    (fun k s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2)) < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) (fun k s₀ _ hc => ?_)
    (fun k s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) fun k => ?_).mono
    (fun s₀ s _ ⟨h, hl⟩ => ⟨h, by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.G_one]; rfl, hl⟩) fun _ _ _ h => h
  · have hc := of_decide_eq_true hc
    have := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega)
    omega
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Up.loads_piece i k) (Piece.seq (Piece.ite
    (fun s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k) < VG.Proof.MlDsa.X86.Pack.Hint.Up.yb s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.fst, hq.ecur, hq.eyb]) (VG.Proof.MlDsa.X86.Pack.Hint.Up.set2_piece i k) (VG.Proof.MlDsa.X86.Pack.Hint.Up.fail2_piece i k))
    ((VG.Proof.MlDsa.X86.Pack.Hint.Up.cmp_piece i (fun s₀ => VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2)) (fun s₀ => VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + k + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)).mono (fun _ _ _ h => h)
      fun s₀ s _ ⟨⟨h, hl⟩, hc⟩ => ⟨hc, fun hc' => ?_, fun hc' => ?_⟩))
  · have hc' := of_decide_eq_true hc'
    have := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
    obtain ⟨st, e, hx⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_G (s₀ := s₀) (i := i) (t := k + 2) (by omega)
    exact ⟨h, by omega, by omega⟩
  · have hc' := of_decide_eq_false hc'
    cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (k + 2) with
    | none =>
      have : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i) = none := optFold_range_none _ (show k + 2 ≤ _ by omega) e
      rw [this]; rw [e] at h; exact h
    | some st =>
      have hx := VG.Proof.MlDsa.X86.Pack.Hint.Up.G_idx s₀ i e
      rw [e] at hc'
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf] at hc'
      rw [show VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i = k + 2 by omega]; exact h

/-- The coefficients of polynomial `i`. -/
theorem coefs_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) s)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.IM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i)) s) hbuCoefs := by
  have e0 : ∀ s₀, VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) = VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i := fun _ => rfl
  refine Piece.seq ((VG.Proof.MlDsa.X86.Pack.Hint.Up.cmp_piece i (fun s₀ => VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) (fun _ => True)).mono (fun _ _ _ h => ⟨h, trivial⟩)
    fun _ _ _ h => h) (Piece.ite (fun s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0) < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.eG, hq.ebnd]) ?_ ?_)
  · refine Piece.seq ((VG.Proof.MlDsa.X86.Pack.Hint.Up.first_piece i).mono (fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, by
      have := of_decide_eq_true hb; rw [e0] at this; exact this⟩) fun _ _ _ h => h) ?_
    refine Piece.seq (addX (VG.Proof.MlDsa.X86.Pack.Hint.Up.set1_piece i) fun _ _ _ h => h.1.2) (Piece.ite
      (fun s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) (fun _ _ _ h => h.1.2)
      (fun s₀ s₀' _ _ hq => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.fst, hq.ecur, hq.ebnd]) ?_ ?_)
    · exact (VG.Proof.MlDsa.X86.Pack.Hint.Up.loop_piece i).mono (fun _ _ _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => ⟨h, of_decide_eq_true hb⟩) fun _ _ _ h => h
    · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, hl⟩, hb⟩ => by
        have := of_decide_eq_false hb
        rw [show VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i = 1 by omega]; exact h
  · exact nil_piece fun s₀ s _ ⟨⟨⟨h, _⟩, _⟩, hb⟩ => by
      have := of_decide_eq_false hb
      rw [e0] at this
      have := h.fb
      rw [show VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i - VG.Proof.MlDsa.X86.Pack.Hint.Up.fst s₀ i = 0 by omega]; exact h

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackMain`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`

The polynomials (`poly_piece`: the bound `y[ω + i]`, its two checks, and the
coefficients of `HintUnpackLoop.lean`), the bytes from the index up to `ω`
(`trail_piece`), and the return value (`ret_piece`), which is 1 iff no check
failed; `hintBitUnpack_eq` (`Pack/Hint.lean`) gives the contract.
-/

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
theorem OM.keep {s₀ s s' : State} {i : Nat} {o : Option (Array (Vector Bool n) × Nat)} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i o s)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ rs, r = .ebx ∨ r = .edx ∨ r = .ebp) (hm : s'.mem = s.mem) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i o s' :=
  ⟨h.toPtr.keep k (fun r hr => by rcases hrs r hr with e | e | e <;> simp [e]) hm,
    by rw [k.gpr (fun hr => by rcases hrs _ hr with e | e | e <;> cases e), h.eax], by rw [hm]; exact h.sr⟩

/-! ## A polynomial -/

theorem q1_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (.block [.mov .edx (.mem (at_ .esp 36))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i4 := h.argIn hp (i := 4) (by omega)
    have hb : WP isa (.block [.mov .edx (.mem (at_ .esp 36))]) s fun s' =>
        s'.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) ∧ s'.mem = s.mem := by
      hrun [a4, i4, h.ptr]
    exact (WP.keep [.edx] hb (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨⟨h.keep k (by simp) m, hi⟩, e⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem q2_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .edx = arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i))
    (fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i))))
    (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) := by
  refine Piece.taint [.edx] (fun s₀ s hp ⟨⟨h, hi⟩, hd⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨_, hd⟩ ⟨_, hd'⟩ r hr => ?_) (by taint_decide)
  · have hf := hp.facts
    have hy : ω s₀ + i < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ := by omega
    have ea : addr (s.gpr .edx) 0 = rA s₀ + BitVec.ofNat 64 (ω s₀ + i) := by rw [hd]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.yAddr hp hy
    have hin := h.inY hp hy
    have hv := h.ybyte hp hy
    have hb : WP isa (.block [.movzx8 .ebx (at_ .edx 0), .alu .cmp .ebx (.reg .eax)]) s fun s' =>
        s'.gpr .ebx = BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (ω s₀ + i) 0) ∧
        s'.cf = some (decide ((BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (ω s₀ + i) 0)).toNat < (s.gpr .eax).toNat)) ∧
        s'.mem = s.mem := by
      hrun [ea, hin, hv]
    have hl := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_le hp h.sr
    refine (WP.keep [.ebx] hb (by decide)).mono fun s' ⟨⟨e, c, m⟩, k⟩ =>
      ⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [e, byte32]⟩, ?_⟩
    show s'.cf = _
    rw [c, toNat_setWidth32_8, h.eax, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [hd, hd', hq.a0, hq.eω]

theorem fail1_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)))) ∧ decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) = true)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have e := VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_fail₁ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem q3_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)))) ∧ decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) = false)
    (fun s₀ s => (((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      ¬ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)))
    (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨⟨⟨⟨h, hi⟩, he⟩, _⟩, hb⟩ => ?_)
    (fun s₀ s₀' s s' _ _ hq ⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨h', _⟩, _⟩, _⟩, _⟩ r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hb' : WP isa (.block [.mov .edx (.mem (at_ .esp 28)), .alu .cmp .edx (.reg .ebx)]) s fun s' =>
        s'.cf = some (decide ((arg s₀ 2).toNat < (s.gpr .ebx).toNat)) ∧ s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have := VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd_lt s₀ i
    refine (WP.keep [.edx] hb' (by decide)).mono fun s' ⟨⟨c, m⟩, k⟩ =>
      ⟨⟨⟨⟨h.keep k (by simp) m, hi⟩, by rw [k.gpr (by decide), he]⟩, of_decide_eq_false hb⟩, ?_⟩
    show s'.cf = _
    rw [c, he, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem fail2_poly_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => ((((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      ¬ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i))) ∧
      decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) = true)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨⟨⟨h, _⟩, _⟩, _⟩, _⟩, hb⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have e := VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_fail₂ (of_decide_eq_true hb)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k⟩ =>
    ⟨h.toPtr.keep k (fun r hr => by simp at hr; simp [hr]) m, by rw [e1, e]; rfl, by rw [e]; exact SR.none _ _⟩

theorem coefs_poly_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => ((((VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ∧ s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) ∧
      ¬ VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i)) ∧ isa.eval .b s = some (decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i))) ∧
      decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i) = false)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s) hbuCoefs :=
  (VG.Proof.MlDsa.X86.Pack.Hint.Up.coefs_piece i).mono (fun s₀ s _ ⟨⟨⟨⟨⟨h, hi⟩, he⟩, h1⟩, _⟩, hb⟩ => by
      have h2 := of_decide_eq_false hb
      obtain ⟨e1, e2, -⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_ok h1 h2
      have eG : VG.Proof.MlDsa.X86.Pack.Hint.Up.G s₀ i 0 = VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i := by rw [e1]; rfl
      exact ⟨h.toPtr, he, by rw [eG]; exact h.eax, by rw [eG]; exact h.sr, hi, e1, e2, by omega⟩)
    fun s₀ s _ h => by
      obtain ⟨-, -, e3⟩ := VG.Proof.MlDsa.X86.Pack.Hint.Up.PS_ok (s₀ := s₀) (i := i) (by rw [h.some]; exact Nat.not_lt.mpr h.fb)
        (Nat.not_lt.mpr h.bw)
      exact ⟨h.toPtr, by rw [e3]; exact h.eax, by rw [e3]; exact h.sr⟩

theorem end_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ (i + 1) (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)))
    (.block hbuPolyEnd) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
    (by taint_decide)
  · have hf := hp.facts
    have a1 : addr (s.gpr .esp) 24 = argAddr s₀ 1 := argEa h.esp 1
    have a4 : addr (s.gpr .esp) 36 = argAddr s₀ 4 := argEa h.esp 4
    have i1 := h.argIn hp (i := 1) (by omega)
    have i4 := h.argIn hp (i := 4) (by omega)
    have o1 := h.argOut hp (i := 1) (by omega)
    have o4 := h.argOut hp (i := 4) (by omega)
    have s14 : Mem.Sep (argAddr s₀ 1) (32 / 8) (argAddr s₀ 4) (32 / 8) :=
      (hp.slot_disj (i := 1) (j := 4) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have s41 : Mem.Sep (argAddr s₀ 4) (32 / 8) (argAddr s₀ 1) (32 / 8) :=
      (hp.slot_disj (i := 4) (j := 1) (by omega) (by omega) (by omega)).sep (Region.contains_self _ _)
        (Region.contains_self _ _)
    have r1 : ∀ v : BitVec 32, (s.mem.writeW (argAddr s₀ 4) v).readW (argAddr s₀ 1) 32 =
        BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ - i) := fun v => by rw [Mem.readW_writeW_sep s14 (by decide), h.cnt]
    have hb : WP isa (.block hbuPolyEnd) s fun s' => s'.gpr .ecx = s.gpr .ecx + 1024 ∧
        s'.zf = some (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ - i) - 1 == 0) ∧
        s'.mem = (s.mem.writeW (argAddr s₀ 4) (arg s₀ 0 + BitVec.ofNat 32 (ω s₀ + i) + 1)).writeW (argAddr s₀ 1)
          (BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀ - i) - 1) := by
      hrun [hbuPolyEnd, a1, a4, i1, i4, o1, o4, h.ptr, r1]
    refine (WP.keep [.edx, .ecx] hb (by decide)).mono fun s' ⟨⟨e1, z, m⟩, k⟩ => ⟨⟨⟨h.toBase.keep k (by decide)
      (by rw [m]; exact (VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_slot (.inr rfl) _).trans (VG.Proof.MlDsa.X86.Pack.Hint.Up.frame_slot (.inl rfl) _)),
      by rw [k.gpr (by decide), h.edi], by rw [k.gpr (by decide), h.esi], by rw [e1, h.ecx, add_1024']; congr 2,
      ?_, ?_⟩, by rw [k.gpr (by decide), h.eax], ?_⟩, eval_ne_cnt hi (by omega) z⟩
    · rw [m, Mem.readW_writeW_self32]; exact cnt_next hi
    · rw [m, Mem.readW_writeW_sep s41 (by decide), Mem.readW_writeW_self32, add_one']; rfl
    · rw [m]
      exact h.sr.congr fun t ht => by rw [hp.coeff_frame (by omega) _ t ht, hp.coeff_frame (by omega) _ t ht]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem poly_piece (i : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s ∧ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ (i + 1) (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (i + 1)) s ∧ isa.eval .ne s = some (decide (i + 1 < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)))
    (.seq hbuPoly (.block hbuPolyEnd)) := by
  refine Piece.seq (addX (X := fun s₀ => i < VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) ?_ fun _ _ _ h => h.2) ((VG.Proof.MlDsa.X86.Pack.Hint.Up.end_piece i).mono (fun _ _ _ h => h)
    fun _ _ _ h => h)
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Up.q1_piece i) (Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Up.q2_piece i) (Piece.ite
    (fun s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i < VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i))) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.ePS]) (VG.Proof.MlDsa.X86.Pack.Hint.Up.fail1_piece i) (Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Up.q3_piece i) (Piece.ite
      (fun s₀ => decide (ω s₀ < VG.Proof.MlDsa.X86.Pack.Hint.Up.bnd s₀ i)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.ebnd, hq.eω]) (VG.Proof.MlDsa.X86.Pack.Hint.Up.fail2_poly_piece i) (VG.Proof.MlDsa.X86.Pack.Hint.Up.coefs_poly_piece i)))))

theorem polys_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ 0 (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ 0) s) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) s)
    (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) :=
  loopN (fun i s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ i (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ i) s) VG.Proof.MlDsa.X86.Pack.Hint.Up.K (fun s₀ hp => by have := hp.facts; omega)
    (fun _ _ _ _ hq => hq.eK) VG.Proof.MlDsa.X86.Pack.Hint.Up.poly_piece

end Up

end VG.Proof.MlDsa.X86.Pack.Hint

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.HintUnpackEnd`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_hint_bit_unpack`, the end

After the polynomials, the bytes from the index up to `ω` must be zero
(`trail_piece`; the spec's `huTrail`): the index ends at `ω`, or 256 if a
check failed (`fin`); the return value is 1 iff it is at most `ω`
(`ret_piece`). Then the whole function (`piece`) and its contract
(`hintBitUnpack_verified`).
-/

namespace VG.Proof.MlDsa.X86.Pack.Hint

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Impl.MlKem.X86 (at_ saveRegs)
open VG.Proof.MlKem.X86
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

namespace Up

/-- The spec's state after the polynomials, if no check failed. -/
def cK (s₀ : State) : Array (Vector Bool n) × Nat := (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)).getD (#[], 0)

/-- Its index. -/
abbrev i₀ (s₀ : State) : Nat := (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀).2

/-- The checks of the first `k` bytes from the index. -/
def TF (s₀ : State) (k : Nat) : Option Unit := optFold (huTrail (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range' (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀) k) ()

/-- The result of the spec: the hint, if no check fails. -/
def TS (s₀ : State) : Option (Array (Vector Bool n) × Nat) :=
  (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)).bind fun st => (optFold (huTrail (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range' st.2 (ω s₀ - st.2)) ()).map fun _ => st

/-- The index at the end: `ω`, or 256 if a check failed. -/
def fin (s₀ : State) : Nat := match VG.Proof.MlDsa.X86.Pack.Hint.Up.TS s₀ with
  | none => 256
  | some _ => ω s₀

/-- The index after byte `k`: 256 if it is not zero. -/
def tr (s₀ : State) (k : Nat) : Nat := if (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0 then 256 else VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k + 1

theorem Pub.ecK {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀' := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.cK; rw [h.ePS, h.eK]

theorem Pub.etr {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') (k : Nat) : VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k = VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀' k := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.tr; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, h.ecK, h.y]

theorem Pub.efin {s₀ s₀' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub s₀ s₀') : VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀ = VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀' := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin VG.Proof.MlDsa.X86.Pack.Hint.Up.TS; rw [h.eK, h.ePS, h.y, h.eω]

/-- What the end keeps. -/
structure TB (s₀ s : State) : Prop extends VG.Proof.MlDsa.X86.Pack.Hint.Up.Base s₀ s where
  edi : s.gpr .edi = arg s₀ 0
  sr : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) s.mem

theorem TB.keep {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s) {rs : List Reg} (k : Keep rs s s') (hrs : Reg.esp ∉ rs)
    (hdi : Reg.edi ∉ rs) (hm : s'.mem = s.mem) : VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s' :=
  ⟨h.toBase.keep k hrs (by rw [hm]; exact Frame.refl _ _), by rw [k.gpr hdi, h.edi], by rw [hm]; exact h.sr⟩

/-- Before byte `k` from the index. -/
def TI (k : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k < ω s₀ ∧
    VG.Proof.MlDsa.X86.Pack.Hint.Up.TF s₀ k = some ()

/-- After byte `k`, before the comparison. -/
def TM (k : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀) ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k < ω s₀ ∧
    VG.Proof.MlDsa.X86.Pack.Hint.Up.TF s₀ k = some ()

/-- At the end. -/
def TFin (s₀ s : State) : Prop := VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀)

theorem sr_le {s₀ : State} {m : Mem} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.SR s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) m) (e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀)) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ ≤ ω s₀ := (h _ e).1

theorem TS_some {s₀ : State} (e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀)) (ht : VG.Proof.MlDsa.X86.Pack.Hint.Up.TF s₀ (ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀) = some ()) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀ = ω s₀ := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin VG.Proof.MlDsa.X86.Pack.Hint.Up.TS; rw [e, Option.bind_some]
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at ht
  rw [ht]; rfl

theorem TS_none {s₀ : State} (e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some (VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀)) (ht : VG.Proof.MlDsa.X86.Pack.Hint.Up.TF s₀ (ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀) = none) :
    VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀ = 256 := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin VG.Proof.MlDsa.X86.Pack.Hint.Up.TS; rw [e, Option.bind_some]
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at ht
  rw [ht]; rfl

/-! ## The trailing bytes -/

theorem t0_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) s)
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)))) ∧
      isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) < ω s₀)))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa h.esp 2
    have i2 := h.argIn hp (i := 2) (by omega)
    have v2 := h.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hb : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hl := VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf_le hp h.sr
    refine (WP.keep [.eax] hb (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have k := k'.drop ea
    refine ⟨⟨⟨h.toBase.keep k (by simp) (by rw [m]; exact Frame.refl _ _), by rw [k.gpr (by simp), h.edi],
      by rw [m]; exact h.sr⟩, by rw [ea, h.eax]⟩, ?_⟩
    show s'.cf = _
    rw [c, h.eax, toNat_ofNat32 (by omega)]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, P0_esp, P0_esp, hq.e0]

theorem ne_zero_byte (b : Byte) : (!(BitVec.setWidth 32 b - 0 == 0)) = decide (b ≠ 0) := by
  rw [sub_zero', byte32]
  by_cases hb : b = 0
  · subst hb; rfl
  · have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq h)
    rw [ofNat_beq_zero (by have := b.isLt; omega)]
    simpa [this] using hb

theorem load_piece (k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Up.TI k)
    (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.TI k s₀ s ∧ isa.eval .ne s = some (decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0)))
    (.block hbuTrailLoad) := by
  refine Piece.taint [.edi, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have hf := hp.facts
    have hy : VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k < VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀ := by omega
    have ea : addr (s.gpr .edi + s.gpr .eax) 0 = rA s₀ + BitVec.ofNat 64 (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) := by
      rw [hb.edi, hax]; exact VG.Proof.MlDsa.X86.Pack.Hint.Up.yAddr hp hy
    have hin := hb.inY hp hy
    have hv := hb.ybyte hp hy
    have hbk : WP isa (.block hbuTrailLoad) s fun s' =>
        s'.zf = some (BitVec.setWidth 32 ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0) - 0 == 0) ∧ s'.mem = s.mem := by
      hrun [hbuTrailLoad, ea, hin, hv]
    refine (WP.keep [.edx] hbk (by decide)).mono fun s' ⟨⟨z, m⟩, k'⟩ =>
      ⟨⟨hb.keep k' (by simp) (by simp) m, by rw [k'.gpr (by simp), hax], e, hl, ht⟩, ?_⟩
    show s'.zf.map (!·) = _
    rw [z, Option.map_some, VG.Proof.MlDsa.X86.Pack.Hint.Up.ne_zero_byte]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.edi, h'.1.edi, hq.a0]
    · rw [h.2.1, h'.2.1]; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, hq.ecK]

theorem tfail_piece (k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.TI k s₀ s ∧ isa.eval .ne s = some (decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0) = true) (VG.Proof.MlDsa.X86.Pack.Hint.Up.TM k) hbuFail := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, _, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hbk : WP isa hbuFail s fun s' => s'.gpr .eax = 256 ∧ s'.mem = s.mem := by hrun [hbuFail]
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_pos' (of_decide_eq_true hc)]; rfl, e, hl, ht⟩

theorem tinc_piece (k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub
    (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Hint.Up.TI k s₀ s ∧ isa.eval .ne s = some (decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0))) ∧
      decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0) = false) (VG.Proof.MlDsa.X86.Pack.Hint.Up.TM k) (.block [.alu .add .eax (.imm 1)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨⟨⟨hb, hax, e, hl, ht⟩, _⟩, hc⟩ => ?_)
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  have hbk : WP isa (.block [.alu .add .eax (.imm 1)]) s fun s' => s'.gpr .eax = s.gpr .eax + 1 ∧
      s'.mem = s.mem := by hrun
  exact (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨e1, m⟩, k'⟩ =>
    ⟨hb.keep k' (by simp) (by simp) m, by rw [e1, hax, VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_neg' (of_decide_eq_false hc), ofNat_add_one],
      e, hl, ht⟩

/-- `cmp eax, ω`, after byte `k`. -/
theorem tcmp_piece (k : Nat) : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Up.TM k)
    (fun s₀ s => isa.eval .b s = some (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k < ω s₀)) ∧ (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k < ω s₀) = true → VG.Proof.MlDsa.X86.Pack.Hint.Up.TI (k + 1) s₀ s) ∧
      (decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k < ω s₀) = false → VG.Proof.MlDsa.X86.Pack.Hint.Up.TFin s₀ s))
    (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · obtain ⟨hb, hax, e, hl, ht⟩ := h
    have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega)
    have v2 := hb.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hbk : WP isa (.block [.alu .cmp .eax (.mem (at_ .esp 28))]) s fun s' =>
        s'.cf = some (decide ((s.gpr .eax).toNat < (arg s₀ 2).toNat)) ∧ s'.gpr .eax = s.gpr .eax ∧
          s'.mem = s.mem := by
      hrun [a2, i2, v2]
    have hf := hp.facts
    have htr : VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k ≤ 256 := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.tr; split <;> omega
    refine (WP.keep [.eax] hbk (by decide)).mono fun s' ⟨⟨c, ea, m⟩, k'⟩ => ?_
    have kk := k'.drop ea
    have hb' := hb.keep kk (by simp) (by simp) m
    have hax' : s'.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k) := by rw [ea, hax]
    refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
    · show s'.cf = _
      rw [c, hax, toNat_ofNat32 (by omega)]
    · -- The byte is zero, and the index still below `ω`.
      have hc := of_decide_eq_true hc
      have hz : ¬ (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0 := fun h => by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_pos' h] at hc; omega
      have htk : VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k = VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k + 1 := by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_neg' hz]
      refine ⟨hb', by rw [hax', htk]; rfl, e, by omega, ?_⟩
      unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at ht ⊢
      rw [optFold_range'_succ, ht, Option.bind_some]
      exact ite_neg' hz _ _
    · have hc := of_decide_eq_false hc
      refine ⟨hb', ?_⟩
      rw [hax']
      by_cases hz : (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0
      · rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_pos' hz, VG.Proof.MlDsa.X86.Pack.Hint.Up.TS_none e]
        have h1 : VG.Proof.MlDsa.X86.Pack.Hint.Up.TF s₀ (k + 1) = none := by
          unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at ht ⊢
          rw [optFold_range'_succ, ht, Option.bind_some]
          exact ite_pos' hz _ _
        unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at h1 ⊢
        exact optFold_range'_none _ _ (show k + 1 ≤ ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ by omega) h1
      · have htk : VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k = VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k + 1 := by rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.tr, ite_neg' hz]
        rw [htk] at hc ⊢
        rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.TS_some e, show VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k + 1 = ω s₀ by omega]
        rw [show ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ = k + 1 by omega]
        unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TF at ht ⊢
        rw [optFold_range'_succ, ht, Option.bind_some]
        exact ite_neg' hz _ _
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

theorem tloop_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (VG.Proof.MlDsa.X86.Pack.Hint.Up.TI 0) VG.Proof.MlDsa.X86.Pack.Hint.Up.TFin (.loop (.seq (.block hbuTrailLoad)
    (.seq (.ite .ne hbuFail (.block [.alu .add .eax (.imm 1)])) (.block [.alu .cmp .eax (.mem (at_ .esp 28))]))) .b) :=
  loopC VG.Proof.MlDsa.X86.Pack.Hint.Up.TI VG.Proof.MlDsa.X86.Pack.Hint.Up.TFin (fun s₀ => ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀) (fun k s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.tr s₀ k < ω s₀))
    (fun k s₀ hp hc => by
      have hf := hp.facts
      have hc := of_decide_eq_true hc
      show k + 1 < ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀
      unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.tr at hc
      split at hc <;> omega)
    (fun k s₀ s₀' _ _ hq => by rw [hq.etr, hq.eω])
    fun k => Piece.seq (VG.Proof.MlDsa.X86.Pack.Hint.Up.load_piece k) (Piece.seq (Piece.ite
      (fun s₀ => decide ((VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀).getD (VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ + k) 0 ≠ 0)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, hq.ecK, hq.y]) (VG.Proof.MlDsa.X86.Pack.Hint.Up.tfail_piece k) (VG.Proof.MlDsa.X86.Pack.Hint.Up.tinc_piece k)) (VG.Proof.MlDsa.X86.Pack.Hint.Up.tcmp_piece k))

theorem trail_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.OM s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) s) VG.Proof.MlDsa.X86.Pack.Hint.Up.TFin hbuTrail := by
  refine Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.t0_piece (Piece.ite (fun s₀ => decide (VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf (VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀)) < ω s₀)) (fun _ _ _ h => h.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.ePS, hq.eK, hq.eω]) ?_ ?_)
  · refine tloop_piece.mono (fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ?_) fun _ _ _ h => h
    have hc := of_decide_eq_true hc
    have hf := hp.facts
    cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) with
    | none => rw [e] at hc; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf] at hc; omega
    | some st =>
      have ec : VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀ = st := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.cK; rw [e]; rfl
      rw [e] at hc hax
      refine ⟨hb, by rw [hax, Nat.add_zero]; simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf, VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, ec], by rw [ec]; exact e, ?_, rfl⟩
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf] at hc
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, ec]; omega
  · refine nil_piece fun s₀ s hp ⟨⟨⟨hb, hax⟩, _⟩, hc⟩ => ⟨hb, ?_⟩
    have hc := of_decide_eq_false hc
    rw [hax]
    cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) with
    | none => unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin VG.Proof.MlDsa.X86.Pack.Hint.Up.TS; rw [e]; rfl
    | some st =>
      have ec : VG.Proof.MlDsa.X86.Pack.Hint.Up.cK s₀ = st := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.cK; rw [e]; rfl
      have hle := (hb.sr st e).1
      rw [e] at hc
      simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.idxOf] at hc ⊢
      rw [VG.Proof.MlDsa.X86.Pack.Hint.Up.TS_some (by rw [e, ec]) (by rw [show ω s₀ - VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀ s₀ = 0 by simp only [VG.Proof.MlDsa.X86.Pack.Hint.Up.i₀, ec]; omega]; rfl)]
      congr 1; omega

/-! ## The return value -/

/-- 1 if no check failed. -/
def res (s₀ : State) : BitVec 32 := match VG.Proof.MlDsa.X86.Pack.Hint.Up.TS s₀ with
  | none => 0
  | some _ => 1

theorem ret_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub VG.Proof.MlDsa.X86.Pack.Hint.Up.TFin (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = VG.Proof.MlDsa.X86.Pack.Hint.Up.res s₀) (.block hbuRet) := by
  refine Piece.taint [.esp] (fun s₀ s hp ⟨hb, hax⟩ => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by taint_decide)
  · have a2 : addr (s.gpr .esp) 28 = argAddr s₀ 2 := argEa hb.esp 2
    have i2 := hb.argIn hp (i := 2) (by omega)
    have v2 := hb.argw hp (i := 2) (by omega) (by omega) (by omega)
    have hbk : WP isa (.block hbuRet) s fun s' =>
        s'.gpr .eax = 1 - 0 - (BitVec.ofBool (decide ((arg s₀ 2).toNat < (s.gpr .eax).toNat))).setWidth 32 ∧
          s'.mem = s.mem := by
      hrun [hbuRet, a2, i2, v2]
    have hf := hp.facts
    refine (WP.keep [.edx, .eax] hbk (by decide)).mono fun s' ⟨⟨e, m⟩, k⟩ =>
      ⟨hb.keep k (by simp) (by simp) m, ?_⟩
    rw [e, hax]
    cases hT : VG.Proof.MlDsa.X86.Pack.Hint.Up.TS s₀ with
    | none =>
      have e1 : VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀ = 256 := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin; rw [hT]
      have e2 : VG.Proof.MlDsa.X86.Pack.Hint.Up.res s₀ = 0 := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega), decide_eq_true (show (arg s₀ 2).toNat < 256 by simp only [ω] at hf; omega)]
      rfl
    | some _ =>
      have e1 : VG.Proof.MlDsa.X86.Pack.Hint.Up.fin s₀ = ω s₀ := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.fin; rw [hT]
      have e2 : VG.Proof.MlDsa.X86.Pack.Hint.Up.res s₀ = 1 := by unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.res; rw [hT]
      rw [e1, e2, toNat_ofNat32 (by omega), decide_eq_false (Nat.lt_irrefl _)]
      rfl
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.1.esp, h'.1.esp, P0_esp, P0_esp, hq.e0]

/-! ## The function -/

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LeafEnd s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.W s₀) s ∧ VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = VG.Proof.MlDsa.X86.Pack.Hint.Up.res s₀)
    (.seq (.block hbuZeroInit) (.seq (.loop (.block hbuZeroBody) .ne)
      (.seq (.block hbuSetup) (.seq (.loop (.seq hbuPoly (.block hbuPolyEnd)) .ne) (.seq hbuTrail (.block hbuRet)))))) :=
  (Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.zinit_piece <| Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.zloop_piece <| Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.setup_piece <| Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.polys_piece <|
    Piece.seq VG.Proof.MlDsa.X86.Pack.Hint.Up.trail_piece VG.Proof.MlDsa.X86.Pack.Hint.Up.ret_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨⟨h.1.frame, h.1.esp, h.1.rd, h.1.wr⟩, h⟩

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.Hint.Up.Pre VG.Proof.MlDsa.X86.Pack.Hint.Up.Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => VG.Proof.MlDsa.X86.Pack.Hint.Up.TB s₀ s ∧ s.gpr .eax = VG.Proof.MlDsa.X86.Pack.Hint.Up.res s₀) s₀ s') Impl.MlDsa.X86.Pack.hintBitUnpack :=
  Piece.leaf VG.Proof.MlDsa.X86.Pack.Hint.Up.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.e0) VG.Proof.MlDsa.X86.Pack.Hint.Up.body_piece

/-- The spec, as the result. -/
theorem hintBitUnpack_TS (s₀ : State) :
    hintBitUnpack (ω s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) (bytesAt s₀.mem (rA s₀) (VG.Proof.MlDsa.X86.Pack.Hint.Up.yL s₀)) = (VG.Proof.MlDsa.X86.Pack.Hint.Up.TS s₀).map (·.1.toList) := by
  rw [hintBitUnpack_eq]
  change (match VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) with
    | none => none
    | some (h, idx) => Option.map (fun _ => h.toList) (optFold (huTrail (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range' idx (ω s₀ - idx)) ())) = _
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TS
  cases VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) with
  | none => rfl
  | some st =>
    obtain ⟨hA, idx⟩ := st
    simp only [Option.bind_some]
    cases optFold (huTrail (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range' idx (ω s₀ - idx)) () <;> rfl

theorem TS_PS {s₀ : State} {st : Array (Vector Bool n) × Nat} (h : VG.Proof.MlDsa.X86.Pack.Hint.Up.TS s₀ = some st) : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) = some st := by
  unfold VG.Proof.MlDsa.X86.Pack.Hint.Up.TS at h
  cases e : VG.Proof.MlDsa.X86.Pack.Hint.Up.PS s₀ (VG.Proof.MlDsa.X86.Pack.Hint.Up.K s₀) with
  | none => rw [e] at h; cases h
  | some st' =>
    rw [e, Option.bind_some] at h
    cases e' : optFold (huTrail (VG.Proof.MlDsa.X86.Pack.Hint.Up.Y s₀)) (List.range' st'.2 (ω s₀ - st'.2)) () with
    | none => rw [e'] at h; cases h
    | some _ => rw [e'] at h; cases h; rfl

end Up

/-- Memory with the arguments `0`, `84`, `80`, `0x1000` and `1024` at `0x5004`. -/
def unpackSatMem : Mem := fun a =>
  if a = 0x5008 then 84 else if a = 0x500c then 80 else if a = 0x5011 then 0x10 else if a = 0x5015 then 4 else 0

theorem hintBitUnpack_verified :
    Verified X86.target Impl.MlDsa.X86.Pack.hintBitUnpack (hintBitUnpackContract X86.abi 16) := by
  refine Piece.verified ((Up.piece.pre_mono (fun _ h => Up.Pre.of h)
    fun _ _ _ _ hq => Up.Pub.of hq).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, ⟨hb, hax⟩, hm, hax'⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax', hax, hm]
    show match hintBitUnpack (ω s₀) (Up.K s₀) (bytesAt s₀.mem (rA s₀) (Up.yL s₀)) with
      | some hint => Up.res s₀ = 1 ∧ HintIs s.mem (wA s₀) (Up.K s₀) hint
      | none => Up.res s₀ = 0
    rw [Up.hintBitUnpack_TS]
    unfold Up.res
    cases e : Up.TS s₀ with
    | none => rfl
    | some st => exact ⟨rfl, harr_hintIs (hb.sr st (Up.TS_PS e)).2⟩
  · refine ⟨satState VG.Proof.MlDsa.X86.Pack.Hint.unpackSatMem [⟨0, 84⟩] [⟨0x1000, 4096⟩, ⟨0x5004, 20⟩], ?_⟩
    sig_sat_check [hintBitUnpackContract, hintBitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlDsa.X86.Pack.Hint

end
