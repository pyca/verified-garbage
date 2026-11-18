module

import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import all Init.Data.Nat.Bitwise.Basic
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Encode
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Stream
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.Pack.Bits
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.Contract

/-! ### `MlDsa.PPC64LE.Pack.SimpleBitPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PPC64LE.Pack.Loop`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: the loops over the groups

As on 32-bit ARM (`Proof/MlDsa/Arm/Pack/BitPack.lean`): `packLoop_ok`, the loop
of `packBody` writes the packing of the values of the 256 coefficients at
`f`; `unpackLoop_ok`, the loop of `unpackBody` writes, for each field of the
bytes at `v`, `fin`'s coefficient of it. Both for any width and any `ld` or
`fin`, from the group lemmas of `Stream.lean`, and for any state that
permits the accesses: they change only the output and the registers of
`loopRegs`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa (bitsToBytes)
open VG.Proof.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz count_sub count_nz)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- The value of each coefficient is less than `2ᵈ`, and the groups tile the
polynomial and the output. -/
structure Shape (d c nb : Nat) : Prop where
  d1 : 1 ≤ d
  d20 : d ≤ 20
  dc : d * c = 8 * nb
  c0 : 0 < c
  c8 : c ≤ 8
  cN : c * (256 / c) = 256
  bN : nb * (256 / c) = 32 * d

theorem Shape.nb20 {d c nb : Nat} (h : Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega_arith

theorem Shape.nb0 {d c nb : Nat} (h : Shape d c nb) : 0 < nb := by
  have := Nat.mul_le_mul h.d1 h.c0; have := h.dc; omega_arith

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega_arith)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega_arith)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega_arith

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ptr_step (p : Addr) (i c : Nat) :
    p + BitVec.ofNat 64 (c * i) + BitVec.ofNat 64 c = p + BitVec.ofNat 64 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- `li r12, N`, the count of groups. -/
theorem liN_ok (N : Nat) (hN : N < 2 ^ 15) (s : State) :
    WP isa (.block [.li .r12 N]) s fun s' =>
      (s'.gpr .r12 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.r12] s s' := by
  refine WP.keep _ ?_ rfl rfl
  exact wp_li hN fun s₁ u₁ => wp_nil ⟨u₁.gpr, u₁.mem⟩

/-- The count after `i` of `N` groups, and whether the loop goes on. -/
theorem count_step {N i : Nat} (hi : i < N) (hN : N ≤ 256) {x : BitVec 64} (hx : x = BitVec.ofNat 64 (N - i)) :
    x - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) ∧
      (x - BitVec.ofNat 64 1 != 0) = decide (i + 1 ≠ N) := by
  rw [hx, count_sub hi]
  exact ⟨rfl, count_nz hi (by omega_arith)⟩

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {V : BitVec 32 → Nat} {R : State → Prop} (hld : LdOk ld V R) (hRs : Stable R)
  {d c nb : Nat} (hs : Shape d c nb) {pf po : Addr} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hRE : R sE) (hin : polyRegion pf ∈ rd ++ wr) (hout : (⟨po, 32 * d⟩ : Region) ∈ wr)
  (hsep : Region.Disjoint (polyRegion pf) ⟨po, 32 * d⟩)
  (hF : ∀ i < 256, V (coeffAt m₀ pf i) < 2 ^ d)
include hld hRs hs hRE hin hout hsep hF

/-- The values of the coefficients. -/
abbrev vals (V : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => V (coeffAt m f i)

omit hld hRs hs hRE hin hout hsep hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, V (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals V m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

omit hld hRs hs hRE hin hout hsep hF in
/-- After `i` groups. -/
structure PInv (V : BitVec 32 → Nat) (d c nb : Nat) (pf po : Addr) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = pf + BitVec.ofNat 64 (4 * c * i)
  r11 : s.gpr .r11 = po + BitVec.ofNat 64 (nb * i)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (256 / c - i)
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [⟨po, 32 * d⟩] m₀ s.mem
  done : ∀ k < nb * i, s.mem (po + BitVec.ofNat 64 k) = (bitsToBytes (fieldBits d (vals V m₀ pf)))[k]!
  keep : Keep loopRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv V d c nb pf po m₀ rd wr sE i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv V d c nb pf po m₀ rd wr sE (i + 1) s' ∧ (s'.gpr .r12 != 0) = decide (i + 1 ≠ 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ha : ∀ j, s.gpr .r10 + BitVec.ofNat 64 (4 * j) = coeffAddr pf (c * i + j) :=
    fun j => by rw [hI.r10, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .r11 + BitVec.ofNat 64 t = po + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [hI.r11, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32 = coeffAt m₀ pf (c * i + j) :=
    fun j hj => by
      rw [ha j]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega_arith)
  refine WP.mono (packBody_ok hld hRs hs.d20 hs.dc hs.c8 s (hRs sE s hRE hI.keep)
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains _ (by omega_arith)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (by
      rw [hI.r10, hI.r11]
      exact (hsep.sub_left (Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith))).sub_right
        (Offset.sub_base _ (by omega_arith)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega_arith)))
    fun s' ⟨hW, x', y', c', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r10]; exact ptr_step _ i (4 * c)
  · rw [y', hI.r11]; exact ptr_step _ i nb
  · rw [c']; exact (count_step hi hN hI.r12).1
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · refine hI.frame.trans (hW.1.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [hI.r11]; exact Offset.sub_base _ (by omega_arith)⟩
  · by_cases hk' : k < nb * i
    · -- Written before.
      rw [← hI.done k hk']
      refine hW.1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [hI.r11] at hc
      exact Offset.disjoint po (d := k) (n := 1) (e := nb * i) (k := nb) (by omega_arith) (by omega_arith)
        (by omega_arith) _ (Region.contains_self _ _) hc
    · -- Written by this group.
      have ht : k - nb * i < nb := by rw [Nat.mul_succ] at hk; omega_arith
      have := hW.2 (k - nb * i) ht
      rw [hb, show nb * i + (k - nb * i) = k by omega_arith] at this
      have e : k = nb * i + (k - nb * i) := by omega_arith
      rw [this]
      conv => rhs; rw [e]
      rw [pack_group (c := c) (by have := hs.d1; omega_arith) hs.dc (by simp) (vals_lt hF) ht (by omega_arith),
        take_drop_eq _ 0 (by simp; omega_arith)]
      refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * (k - nb * i)))) (List.map_congr_left fun j hj => ?_)
      have hj := List.mem_range.mp hj
      rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_arith)]
      rfl
  · rw [c']; exact (count_step hi hN hI.r12).2

theorem packLoop_ok {s : State} (h10 : s.gpr .r10 = pf) (h11 : s.gpr .r11 = po) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) (hE : Keep loopRegs sE s) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem po (32 * d) = bitsToBytes (fieldBits d (vals V m₀ pf)) ∧
        Frame [⟨po, 32 * d⟩] m₀ s'.mem ∧ Keep loopRegs sE s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega_arith) h0'
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  unfold packLoop
  refine WP.seq (WP.mono (liN_ok _ (by omega_arith) s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_nz (PInv V d c nb pf po m₀ rd wr sE) hN0
    (fun i hi s' hI => packStep hld hRs hs hRE hin hout hsep hF hi hI)
    (fun s' hI => ⟨bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk),
      hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), (hE.trans k₁).mono (by decide)⟩
  · rw [k₁.gpr (by decide), h10]; simp
  · rw [k₁.gpr (by decide), h11]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

/-! ## Unpacking -/

/-- The number whose bytes are the `32 d` bytes of the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (W : Nat → BitVec 32) (d c nb : Nat) (pv pp : Addr) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = pv + BitVec.ofNat 64 (nb * i)
  r11 : s.gpr .r11 = pp + BitVec.ofNat 64 (4 * c * i)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (256 / c - i)
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [polyRegion pp] m₀ s.mem
  done : ∀ k < c * i, coeffAt s.mem pp k = W (inNum m₀ pv d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep loopRegs sE s

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {R : State → Prop} {d c nb : Nat}
  (hfin : FinOk fin d W R) (hRs : Stable R) (hs : Shape d c nb) {pv pp : Addr} {m₀ : Mem}
  {rd wr : List Region} {sE : State} (hRE : R sE)
  (hin : (⟨pv, 32 * d⟩ : Region) ∈ rd ++ wr) (hout : polyRegion pp ∈ wr)
  (hsep : Region.Disjoint ⟨pv, 32 * d⟩ (polyRegion pp))
include hfin hRs hs hRE hin hout hsep

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : UInv W d c nb pv pp m₀ rd wr sE i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv W d c nb pv pp m₀ rd wr sE (i + 1) s' ∧ (s'.gpr .r12 != 0) = decide (i + 1 ≠ 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ha : ∀ j, s.gpr .r11 + BitVec.ofNat 64 (4 * j) = coeffAddr pp (c * i + j) :=
    fun j => by rw [hI.r11, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .r10 + BitVec.ofNat 64 t = pv + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [hI.r10, off_add]
  have hsub : Region.Sub ⟨s.gpr .r11, 4 * c⟩ (polyRegion pp) := by
    rw [hI.r11]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith)
  refine WP.mono (unpackBody_ok hfin hRs hs.d1 hs.d20 hs.dc hs.c8 s (hRs sE s hRE hI.keep)
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains _ (by omega_arith)))
    (by rw [hI.r10]; exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hsub))
    fun s' ⟨hw, hf, x', p', c', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_),
      fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r10]; exact ptr_step _ i nb
  · rw [p', hI.r11]; exact ptr_step _ i (4 * c)
  · rw [c']; exact (count_step hi hN hI.r12).1
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  · -- The bytes of the group, on entry.
    have hB : (List.range nb).map (fun t => (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat) =
        (((bytesAt m₀ pv (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
      rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega_arith)]
      refine List.map_congr_left fun t ht => ?_
      have ht := List.mem_range.mp ht
      rw [getD_map_toNat, bytesAt_getD _ _ (by omega_arith), hb]
      refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    have hlt : ∀ a ∈ (bytesAt m₀ pv (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
    by_cases hk' : k < c * i
    · -- Written before.
      rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
      refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [hI.r11]
      exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega_arith) (by omega_arith) (by rw [Nat.mul_assoc]; omega_arith)
    · -- Written by this group.
      have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega_arith
      have := hw (k - c * i) hj
      rw [ha, show c * i + (k - c * i) = k by omega_arith, hB, digits_group hs.dc hlt hj,
        show c * i + (k - c * i) = k by omega_arith] at this
      rw [coeffAt_eq, this]
  · rw [c']; exact (count_step hi hN hI.r12).2

theorem unpackLoop_ok {s : State} (h10 : s.gpr .r10 = pv) (h11 : s.gpr .r11 = pp) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) (hE : Keep loopRegs sE s) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem pp k = W (inNum m₀ pv d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion pp] m₀ s'.mem ∧ Keep loopRegs sE s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega_arith) h0'
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  unfold unpackLoop
  refine WP.seq (WP.mono (liN_ok _ (by omega_arith) s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_nz (UInv W d c nb pv pp m₀ rd wr sE) hN0
    (fun i hi s' hI => unpackStep hfin hRs hs hRE hin hout hsep hi hI)
    (fun s' hI => ⟨fun k hk => hI.done k (by rw [hs.cN]; exact hk), hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), (hE.trans k₁).mono (by decide)⟩
  · rw [k₁.gpr (by decide), h10]; simp
  · rw [k₁.gpr (by decide), h11]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.PPC64LE.Pack

end

end

/-! ### `MlDsa.PPC64LE.Pack.Contracts`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Proof/MlDsa/Contract.lean`) requires, spelled out for PPC64LE (`SbpPre`, `BpPre`,
`BuPre`, `T1Pre`, from `pre_of`). A `u32` argument is the low 32 bits of its
register (`lo`): the ABI leaves the others unspecified, and the contracts
make only those public. So the branch of `sel` on a width compares the low
32 bits (`sel_ok`), and is constant time from states that agree on them
(`sel_ct`), a fact the taint analysis, which tracks whole registers, cannot
see; the loops it chooses between are constant time by the taint analysis
(`leaf_ct`). `abi_of` derives what the calling convention preserves from the
instructions alone.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack

/-- The `u32` argument in register `r`: its low 32 bits. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-! ## The preconditions -/

/-- `vg_mldsa_simple_bit_pack(f = r3, b = r4, out = r5, len = r6)`. -/
structure SbpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .r3)]
  wr : s.wr = [⟨s.gpr .r5, (s.gpr .r6).toNat⟩]
  disj : (polyRegion (s.gpr .r3)).Disjoint ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  fitF : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
  b : lo s .r4 ∈ simpleBitPackBounds
  len : (s.gpr .r6).toNat = 32 * bitlen (lo s .r4)
  le : ∀ i < n, (coeffAt s.mem (s.gpr .r3) i).toNat ≤ lo s .r4

theorem SbpPre.of {s : State} (h : (simpleBitPackContract PPC64LE.abi).pre s) : SbpPre s := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- `vg_mldsa_bit_pack(f = r3, a = r4, b = r5, out = r6, len = r7)`. -/
structure BpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (s.gpr .r3)]
  wr : s.wr = [⟨s.gpr .r6, (s.gpr .r7).toNat⟩]
  disj : (polyRegion (s.gpr .r3)).Disjoint ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
  fitF : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 64
  fitO : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  ab : (lo s .r4, lo s .r5) ∈ bitPackParams
  len : (s.gpr .r7).toNat = 32 * bitlen (lo s .r4 + lo s .r5)
  red : Reduced s.mem (s.gpr .r3)
  bnd : ∀ i < n, -(lo s .r4 : Int) ≤ modPm (coeffAt s.mem (s.gpr .r3) i).toNat q ∧
    modPm (coeffAt s.mem (s.gpr .r3) i).toNat q ≤ lo s .r5

theorem BpPre.of {s : State} (h : (bitPackContract PPC64LE.abi).pre s) : BpPre s := by
  sig_pre [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- `vg_mldsa_bit_unpack(v = r3, len = r4, a = r5, b = r6, f = r7)`. -/
structure BuPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [polyRegion (s.gpr .r7)]
  disj : Region.Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat⟩ (polyRegion (s.gpr .r7))
  fitV : (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64
  fitP : (s.gpr .r7).toNat + 1024 ≤ 2 ^ 64
  ab : (lo s .r5, lo s .r6) ∈ bitPackParams
  len : (s.gpr .r4).toNat = 32 * bitlen (lo s .r5 + lo s .r6)

theorem BuPre.of {s : State} (h : (bitUnpackContract PPC64LE.abi).pre s) : BuPre s := by
  sig_pre [bitUnpackContract, bitUnpackSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `vg_mldsa_unpack_t1(v = r3, f = r4)`. -/
structure T1Pre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 320⟩]
  wr : s.wr = [polyRegion (s.gpr .r4)]
  disj : Region.Disjoint ⟨s.gpr .r3, 320⟩ (polyRegion (s.gpr .r4))
  fitV : (s.gpr .r3).toNat + 320 ≤ 2 ^ 64
  fitP : (s.gpr .r4).toNat + 1024 ≤ 2 ^ 64

theorem T1Pre.of {s : State} (h : (unpackT1Contract PPC64LE.abi).pre s) : T1Pre s := by
  sig_pre [unpackT1Contract, unpackT1Sig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-! ## Constants -/

/-- The value `loadB r B` leaves in `r`. -/
def loadBVal (B : Nat) : BitVec 64 :=
  if B < 2 ^ 15 then BitVec.ofNat 64 B else ((BitVec.ofNat 16 (B / 2 ^ 16)) ++ (0 : BitVec 16)).signExtend 64

theorem loadB_ok (r : Reg) {B : Nat} (hB : loadBVal B = BitVec.ofNat 64 B) (s : State) :
    WP isa (.block (loadB r B)) s fun s' =>
      (s'.gpr r = BitVec.ofNat 64 B ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  unfold loadB
  by_cases h : B < 2 ^ 15
  · simp only [h, ↓reduceIte]
    refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, dstOf]) rfl
    exact wp_li h fun s₁ u₁ => wp_nil ⟨u₁.gpr, u₁.mem⟩
  · simp only [h, ↓reduceIte]
    refine WP.keep _ ?_ (by simp [writesOnly, Code.allInstrs, dstOf]) rfl
    refine WP.cons exec_lis (wp_nil ⟨?_, rfl⟩)
    rw [← hB]
    simp [loadBVal, h, State.write]

/-- The pointers of the loops from the arguments `a` and `b`. -/
theorem mov2_ok {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb10 : b ≠ .r10) (s : State) :
    WP isa (.block [VG.Impl.Sha3.PPC64LE.Stream.mov .r10 a, VG.Impl.Sha3.PPC64LE.Stream.mov .r11 b]) s
      fun s' => (s'.gpr .r10 = s.gpr a ∧ s'.gpr .r11 = s.gpr b ∧ s'.mem = s.mem) ∧ Keep [.r10, .r11] s s' := by
  refine WP.keep _ ?_ rfl rfl
  refine wp_addi ha (by decide) fun s₁ u₁ => wp_addi hb (by decide) fun s₂ u₂ => wp_nil ⟨?_, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr]; exact BitVec.add_zero _
  · rw [u₂.gpr, u₁.other _ hb10]; exact BitVec.add_zero _
  · rw [u₂.mem, u₁.mem]

/-- As `mov2_ok`, then `q` in `r7`. -/
theorem mov2Q_ok {a b : Reg} (ha : a ≠ .r0) (hb : b ≠ .r0) (hb10 : b ≠ .r10) (s : State) :
    WP isa (.block ([VG.Impl.Sha3.PPC64LE.Stream.mov .r10 a, VG.Impl.Sha3.PPC64LE.Stream.mov .r11 b] ++ loadQ)) s
      fun s' => (s'.gpr .r10 = s.gpr a ∧ s'.gpr .r11 = s.gpr b ∧ s'.gpr .r7 = BitVec.ofNat 64 q ∧
        s'.mem = s.mem) ∧ Keep [.r10, .r11, .r7] s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (mov2_ok ha hb hb10 s) fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_
  unfold loadQ
  refine wp_lis fun s₂ u₂ => wp_ori fun s₃ u₃ => wp_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g10]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g11]
  · rw [u₃.gpr, u₂.gpr]; decide
  · rw [u₃.mem, u₂.mem, m₁]
  · exact ((k₁.trans (upd_keep u₂)).trans (upd_keep u₃)).mono (by decide)

/-! ## Branching on a width -/

/-- What the block of `sel` keeps. -/
def Same (s s' : State) : Prop := Keep [.r9] s s' ∧ s'.mem = s.mem

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨(h₁.1.trans h₂.1).mono (by decide), h₂.2.trans h₁.2⟩

theorem lo_sub_beq (x : BitVec 64) {v : Nat} (hv : v < 2 ^ 32) :
    ((x - BitVec.ofNat 64 v).setWidth 32 == 0) = decide ((x.setWidth 32).toNat = v) := by
  have e : (BitVec.ofNat 64 v).setWidth 32 = BitVec.ofNat 32 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hv] : v < 2 ^ 64)]
  rw [lo32_sub, e]
  generalize x.setWidth 32 = a
  by_cases h : a.toNat = v
  · have : a = BitVec.ofNat 32 v :=
      BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv])
    rw [decide_eq_true h, this, BitVec.sub_self]
    rfl
  · have : a - BitVec.ofNat 32 v ≠ 0 := by
      intro e'
      apply h
      bv_omega
    rw [decide_eq_false h]
    exact beq_eq_false_iff_ne.mpr this

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  change VG.PPC64LE.eval (.zero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

/-- The block of `sel`: `r9` = `r - v`. -/
theorem selBlk_ok (r : Reg) (hr : r ≠ .r9) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v) (s : State) :
    WP isa (.block (loadB .r9 v ++ ([.sub .r9 r .r9] : List Instr))) s fun s' =>
      s'.gpr .r9 = s.gpr r - BitVec.ofNat 64 v ∧ Same s s' := by
  rw [WP.block_append_iff]
  refine WP.mono (loadB_ok .r9 hl s) fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ => wp_sub fun s₂ u₂ => wp_nil ⟨?_, ?_, ?_⟩
  · rw [u₂.gpr, g₁, k₁.gpr (by simpa using hr)]
  · exact (k₁.trans (upd_keep u₂)).mono (by decide)
  · rw [u₂.mem, m₁]

theorem sel_ok (r : Reg) (hr : r ≠ .r9) (v : Nat) (hv : v < 2 ^ 32) (hl : loadBVal v = BitVec.ofNat 64 v)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → lo s r = v → WP isa p s' Q)
    (hn : ∀ s', Same s s' → lo s r ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (selBlk_ok r hr hl s) fun s' ⟨g, hs⟩ => ?_)
  refine WP.ite (M := isa) (decide (lo s r = v)) (by rw [eval_zero_w, g, lo_sub_beq _ hv])
    (fun h => hp s' hs (of_decide_eq_true h)) (fun h => hn s' hs (of_decide_eq_false h))

/-! ## Constant time -/

/-- An instruction that accesses no memory. -/
def noMem : Instr → Bool
  | .load .. | .store .. | .lbz .. | .stb .. | .loadRev .. | .storeRev .. | .push _ | .pop _
  | .alloc _ | .lxvd2x .. | .lxvd2xTbl .. | .stxvd2x .. | .dcbz .. => false
  | _ => true

theorem addrs_noMem {i : Instr} (h : noMem i = true) (s : State) : VG.PPC64LE.addrs i s = [] := by
  cases i <;> first | rfl | simp [noMem] at h

theorem execBlock_noMem : ∀ {is : List Instr}, is.all noMem = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → t = []
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | i :: is, hm, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    simp only [execBlock] at h
    split at h
    · cases h
    · obtain ⟨⟨s'', t'⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      cases h₂
      rw [addrs_noMem hm.1 s]
      simpa using execBlock_noMem hm.2 h₁

/-- A block that accesses no memory leaks nothing. -/
theorem relct_noMem {P : State → State → Prop} {is : List Instr} (h : is.all noMem = true) :
    RelCT isa P (.block is) fun _ _ => True := fun _ _ _ _ _ _ _ e₁ e₂ => by
  rw [Exec.block_iff] at e₁ e₂
  rw [execBlock_noMem h e₁, execBlock_noMem h e₂]; exact ⟨rfl, trivial⟩

theorem WP.withSp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp :=
  let ⟨t, s', he, hq⟩ := h
  ⟨t, s', he, hq, Exec.sp he⟩

/-- Two runs that agree on the stack pointer, the pointers of the loops and
the `u32` argument in `r`. -/
def Agr (r : Reg) (a b : State) : Prop :=
  a.sp = b.sp ∧ a.gpr .r10 = b.gpr .r10 ∧ a.gpr .r11 = b.gpr .r11 ∧ lo a r = lo b r

theorem sel_ct {r : Reg} (hr : r ≠ .r9) {v : Nat} (hl : loadBVal v = BitVec.ofNat 64 v)
    {p e : Prog isa} {Q : State → State → Prop} (hp : RelCT isa (Agr r) p Q) (he : RelCT isa (Agr r) e Q) :
    RelCT isa (Agr r) (sel r v p e) Q := by
  unfold sel
  have hb := (relct_noMem (P := Agr r) (is := loadB .r9 v ++ ([.sub .r9 r .r9] : List Instr))
    (by unfold loadB; split <;> rfl)).wpDep
    (F := fun (σ s' : State) => (s'.gpr .r9 = σ.gpr r - BitVec.ofNat 64 v ∧ Same σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (selBlk_ok r hr hl a), WP.withSp (selBlk_ok r hr hl b)⟩
  refine RelCT.seq (R := fun a b => Agr r a b ∧ isa.eval (.zero .w .r9) a = isa.eval (.zero .w .r9) b)
    (hb.mono (fun _ _ h => h) fun a' b' ⟨_, σ₁, σ₂, hσ, ⟨⟨g₁, k₁, _⟩, p₁⟩, ⟨⟨g₂, k₂, _⟩, p₂⟩⟩ =>
      ⟨⟨by rw [p₁, p₂, hσ.1], by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.1],
        by rw [k₁.gpr (by decide), k₂.gpr (by decide), hσ.2.2.1],
        by simp only [lo]; rw [k₁.gpr (by simpa using hr), k₂.gpr (by simpa using hr)]; exact hσ.2.2.2⟩,
      by
        rw [eval_zero_w, eval_zero_w, g₁, g₂, lo32_sub, lo32_sub]
        have : (σ₁.gpr r).setWidth 32 = (σ₂.gpr r).setWidth 32 := BitVec.eq_of_toNat_eq hσ.2.2.2
        rw [this]⟩)
    (RelCT.ite (fun _ _ h => h.2) (hp.mono (fun _ _ h => h.1.1) fun _ _ h => h)
      (he.mono (fun _ _ h => h.1.1) fun _ _ h => h))

/-- A branch of `sel`, constant time by the taint analysis with the pointers
of the loops public. -/
theorem leaf_ct {r : Reg} {c : Prog isa} {hc : VG.Taint.Hint VG.PPC64LE.taint.T}
    (h : (VG.PPC64LE.taint.check (Taint.ofRegs [.r10, .r11]) c hc).isSome = true) :
    RelCT isa (Agr r) c fun _ _ => True :=
  RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r10, .r11]) (fun a b h => ⟨h.1, fun x hx => by
    rw [Taint.mem_ofRegs] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [h.2.1, h.2.2.1]⟩) h

/-! ## The calling convention -/

/-- Code without calls that writes no register the calling convention
preserves, nor the link register, preserves what it must. -/
theorem abi_of {c : Prog isa}
    (hp : (instrs c).all (fun i => preserved.all fun r => dstOf i != some r) = true) (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi h => ?_) he (.inl hn), Exec.sp he, Exec.lr he hn hl⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hp i hi) r hr
  rw [h] at this
  simp at this

end VG.Proof.MlDsa.PPC64LE.Pack

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases. Constant time: the branch on the width by `sel_ct`, and each
loop by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE (toNat_setWidth64)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat fun _ => True := fun j s _ hj hin => by
  refine WP.keep _ ?_ rfl rfl
  unfold sbpLd
  exact wp_lwz (by decide) hj rfl hin fun s₁ u₁ => wp_nil ⟨by rw [u₁.gpr, toNat_setWidth64], u₁.mem⟩

theorem true_stable : Stable fun _ => True := fun _ _ _ _ => trivial

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem sbp_wp {s₀ : State} (hp : SbpPre s₀) :
    WP isa Impl.MlDsa.PPC64LE.Pack.simpleBitPack s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat =
        simpleBitPack (natPolyAt s₀.mem (s₀.gpr .r3)) (lo s₀ .r4) := by
  unfold Impl.MlDsa.PPC64LE.Pack.simpleBitPack
  refine WP.seq (WP.mono (mov2_ok (a := .r3) (b := .r5) (by decide) (by decide) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_)
  have e4 : lo s₁ .r4 = lo s₀ .r4 := by simp only [lo]; rw [k₁.gpr (by decide)]
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (lo s₀ .r4) = d → ∀ s : State, Same s₁ s →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        bytesAt s'.mem (s₀.gpr .r5) (s₀.gpr .r6).toNat =
          simpleBitPack (natPolyAt s₀.mem (s₀.gpr .r3)) (lo s₀ .r4) := by
    intro d c nb hs hd s hS
    have hlen := hp.len
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok true_stable hs (pf := s₀.gpr .r3) (po := s₀.gpr .r5) (m₀ := s₀.mem)
      (rd := s₀.rd) (wr := s₀.wr) (sE := s) trivial
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hp.disj)
      (fun i hi => by rw [← hd]; exact lt_bitlen (hp.le i hi))
      (by rw [hS.1.gpr (by decide), g10]) (by rw [hS.1.gpr (by decide), g11])
      (by rw [hS.1.2.1, k₁.2.1]) (by rw [hS.1.2.2, k₁.2.2]) (by rw [hS.2, m₁]) (Keep.refl _ _))
      fun s' ⟨hB, _, _⟩ => ?_
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  refine sel_ok .r4 (by decide) 15 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n15 => ?_)
  · rw [e4] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) (by rw [e]; decide) s₂ h₂
  rw [e4] at n15
  refine sel_ok .r4 (by decide) 43 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n43 => ?_)
  · rw [show lo s₂ .r4 = lo s₀ .r4 by simp only [lo]; rw [h₂.1.gpr (by decide)]; exact e4] at e
    exact go (d := 6) (c := 4) (nb := 3) (by constructor <;> decide) (by rw [e]; decide) s₃ (h₂.trans h₃)
  · rw [show lo s₂ .r4 = lo s₀ .r4 by simp only [lo]; rw [h₂.1.gpr (by decide)]; exact e4] at n43
    have e : lo s₀ .r4 = 1023 := by
      have hb := hp.b
      simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
      omega_using [n15, n43, hb]
    exact go (d := 10) (c := 4) (nb := 5) (by constructor <;> decide) (by rw [e]; decide) s₃ (h₂.trans h₃)

theorem simpleBitPack_ct :
    ConstantTime isa (simpleBitPackContract PPC64LE.abi).pre (simpleBitPackContract PPC64LE.abi).pub
      Impl.MlDsa.PPC64LE.Pack.simpleBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.PPC64LE.Pack.simpleBitPack
  refine RelCT.seq (R := Agr .r4) (((relct_noMem (by rfl)).wpDep
    (F := fun (σ s' : State) => ((s'.gpr .r10 = σ.gpr .r3 ∧ s'.gpr .r11 = σ.gpr .r5 ∧ s'.mem = σ.mem) ∧
      Keep [.r10, .r11] σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (mov2_ok (by decide) (by decide) (by decide) a),
      WP.withSp (mov2_ok (by decide) (by decide) (by decide) b)⟩).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, ⟨⟨⟨g₁, h₁, _⟩, k₁⟩, p₁⟩, ⟨⟨⟨g₂, h₂, _⟩, k₂⟩, p₂⟩⟩ => by
      sig_pub [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, e3, e4, e5, -⟩ := hpub
      refine ⟨by rw [p₁, p₂, hsp], by rw [g₁, g₂, e3], by rw [h₁, h₂, e5], ?_⟩
      simp only [lo]; rw [k₁.gpr (by decide), k₂.gpr (by decide), e4]) ?_
  exact sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
    (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide)) (leaf_ct (by taint_decide)))

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp [coeffAt, Mem.readW, Mem.read]

/-- A state satisfying the precondition. -/
def sbpSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 15 | .r5 => 0x2000 | .r6 => 128 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

example : ∃ pre post leak, simpleBitPackContract PPC64LE.abi =
    simpleBitPackSig.contract PPC64LE.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem simpleBitPack_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.simpleBitPack (simpleBitPackContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, simpleBitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := sbp_wp (SbpPre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpost
  · refine ⟨sbpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [simpleBitPackContract, simpleBitPackSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
        | (simp only [simpleBitPackBounds, t1Max_eq]; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Pack

end

end

/-!
# ML-DSA on PPC64LE: `vg_mldsa_bit_pack`

The value of a coefficient `x` is `b - x`, plus `q` if that is negative (`bm`,
as `bMinus` computes it, with `b` in `r4` and `q` in `r7`), which is
`b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`). The loop is proven
once for every width (`packLoop_ok`), and the function by its five cases.
Constant time: the branch on the width by `sel_ct`, and each loop by the
taint analysis.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.PPC64LE (toNat_setWidth64)
open VG.Proof.MlDsa.Pack

/-! ## `b - x` modulo `q` -/

/-- `b - x`, plus `q` if it is negative, as `bMinus` computes it in 64 bits. -/
def bm (b x : BitVec 64) : BitVec 64 := b - x + ((b - x) >>> 63) * BitVec.ofNat 64 q

theorem bm_toNat {b x : BitVec 64} (hb : b.toNat ≤ 2 ^ 19) (hx : x.toNat < q) :
    (bm b x).toNat = (b.toNat + q - x.toNat) % q := by
  rw [q_eq] at hx ⊢
  unfold bm
  rw [q_eq]
  by_cases h : x.toNat ≤ b.toNat
  · have e : (b - x) >>> 63 = 0#64 := by bv_omega
    rw [e, Nat.mod_eq_sub_mod (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [hb])]
    bv_omega
  · have e : (b - x) >>> 63 = 1#64 := by bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega_using [h])]
    bv_omega

/-- `b = B` in `r4` and `q` in `r7`. -/
def RB (B : Nat) (s : State) : Prop := s.gpr .r4 = BitVec.ofNat 64 B ∧ s.gpr .r7 = BitVec.ofNat 64 q

theorem RB_stable (B : Nat) : Stable (RB B) := fun _ _ h k =>
  ⟨by rw [k.gpr (by decide), h.1], by rw [k.gpr (by decide), h.2]⟩

/-- `r9 ← b - r9` modulo `q`, from a state of `RB B`. -/
theorem bMinus_ok {B : Nat} {s : State} (hR : RB B s) :
    WP isa (.block bMinus) s fun s' =>
      (s'.gpr .r9 = bm (BitVec.ofNat 64 B) (s.gpr .r9) ∧ s'.mem = s.mem) ∧ Keep [.r0, .r9] s s' := by
  refine WP.keep _ ?_ rfl
  unfold bMinus addQNeg
  refine wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => wp_mul fun s₄ u₄ => wp_add fun s₅ u₅ =>
    wp_nil ⟨?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]⟩
  rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other .r9 (by decide), u₃.other .r7 (by decide),
    u₂.gpr, u₂.other .r7 (by decide), hR.1, hR.2]
  rfl

/-- The value `bpLd` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (bm (BitVec.ofNat 64 B) (w.setWidth 64)).toNat

theorem bpLd_ok (B : Nat) : LdOk bpLd (bpVal B) (RB B) := fun j s hR hj hin => by
  unfold bpLd
  refine wp_lwz (by decide) hj rfl hin fun s₁ u₁ => ?_
  have hR₁ : RB B s₁ := ⟨by rw [u₁.other _ (by decide), hR.1], by rw [u₁.other _ (by decide), hR.2]⟩
  refine WP.mono (bMinus_ok hR₁) fun s₂ ⟨⟨g₂, m₂⟩, k₂⟩ => ⟨⟨by rw [g₂, u₁.gpr], by rw [m₂, u₁.mem]⟩,
    ((upd_keep u₁).trans k₂).mono (by decide)⟩

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ 2 ^ 19)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega_using [hb]
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, bm_toNat (by omega_using [hb, hbq]) (by rw [toNat_setWidth64]; exact hx), hbq, toNat_setWidth64,
    sub_modPm hx (by rw [q_eq]; omega_using [hb]) (hle i hi)]

/-! ## The function -/

/-- What `bitPack` leaves. -/
def BpPost (s₀ s' : State) : Prop :=
  bytesAt s'.mem (s₀.gpr .r6) (s₀.gpr .r7).toNat =
    bitPack ((polyAt s₀.mem (s₀.gpr .r3)).map fun c => modPm c.val q) (lo s₀ .r4) (lo s₀ .r5)

theorem bp_wp {s₀ : State} (hp : BpPre s₀) : WP isa Impl.MlDsa.PPC64LE.Pack.bitPack s₀ (BpPost s₀) := by
  unfold Impl.MlDsa.PPC64LE.Pack.bitPack
  refine WP.seq (WP.mono (mov2Q_ok (a := .r3) (b := .r6) (by decide) (by decide) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, g7, m₁⟩, k₁⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have go : ∀ {d c nb B : Nat}, Shape d c nb → lo s₀ .r5 = B → B ≤ 2 ^ 19 →
      loadBVal B = BitVec.ofNat 64 B → bitlen (lo s₀ .r4 + B) = d → ∀ s : State, Same s₁ s →
      WP isa (withB B (packLoop bpLd d c nb)) s (BpPost s₀) := by
    intro d c nb B hs hB hB19 hBl hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have hBq : (BitVec.ofNat 64 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega_using [hB19]
    refine WP.seq (WP.mono (loadB_ok .r4 hBl s) fun s₂ ⟨⟨g4, m₂⟩, k₂⟩ => ?_)
    refine WP.mono (packLoop_ok (bpLd_ok B) (RB_stable B) hs (pf := s₀.gpr .r3) (po := s₀.gpr .r6)
      (m₀ := s₀.mem) (rd := s₀.rd) (wr := s₀.wr) (sE := s₂)
      ⟨g4, by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g7]⟩
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _)
      (by rw [← hlen]; exact hp.disj) (fun i hi => ?_)
      (by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g10]) (by rw [k₂.gpr (by decide), hS.1.gpr (by decide), g11])
      (by rw [k₂.2.1, hS.1.2.1, k₁.2.1]) (by rw [k₂.2.2, hS.1.2.2, k₁.2.2]) (by rw [m₂, hS.2, m₁])
      (Keep.refl _ _))
      fun s₃ ⟨hbytes, _, _⟩ => ?_
    · obtain ⟨h₁, h₂⟩ := hp.bnd i hi
      rw [hB] at h₂
      have hx := hp.red i hi
      rw [bpVal, bm_toNat (by omega_using [hB19, hBq]) (by rw [toNat_setWidth64]; exact hx), hBq, toNat_setWidth64,
        ← sub_modPm hx (by rw [q_eq]; omega_using [hB19]) h₂, ← hd, ← hB]
      exact lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · rw [BpPost, hlen, hbytes, bitPack_eq, ← hB, ← hd, hB,
        bitPack_vals hp.red hB19 (fun i hi => by rw [← hB]; exact (hp.bnd i hi).2)]
  refine sel_ok .r5 (by decide) 2 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n2 => ?_)
  · have e5 : lo s₁ .r5 = lo s₀ .r5 := by simp only [lo]; rw [k₁.gpr (by decide)]
    rw [e5] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 2 by omega_using [ab, e]]; decide) s₂ h₂
  have e5 : ∀ s, Same s₁ s → lo s .r5 = lo s₀ .r5 := fun s h => by
    simp only [lo]; rw [h.1.gpr (by decide), k₁.gpr (by decide)]
  rw [e5 s₁ ⟨Keep.refl _ _, rfl⟩] at n2
  refine sel_ok .r5 (by decide) 4 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n4 => ?_)
  · rw [e5 s₂ h₂] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 4 by omega_using [ab, e]]; decide) s₃ (h₂.trans h₃)
  rw [e5 s₂ h₂] at n4
  refine sel_ok .r5 (by decide) 4096 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4096 => ?_)
  · rw [e5 s₃ (h₂.trans h₃)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 4095 by omega_using [ab, e]]; decide) s₄ ((h₂.trans h₃).trans h₄)
  rw [e5 s₃ (h₂.trans h₃)] at n4096
  refine sel_ok .r5 (by decide) 131072 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n17 => ?_)
  · rw [e5 s₄ ((h₂.trans h₃).trans h₄)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 131071 by omega_using [ab, e]]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)
  · rw [e5 s₄ ((h₂.trans h₃).trans h₄)] at n17
    have e : lo s₀ .r5 = 524288 := by omega_using [ab, n2, n4, n4096, n17]
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show lo s₀ .r4 = 524287 by omega_using [ab, n2, n4, n4096, n17]]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)

/-! ## Constant time -/

theorem bitPack_ct :
    ConstantTime isa (bitPackContract PPC64LE.abi).pre (bitPackContract PPC64LE.abi).pub
      Impl.MlDsa.PPC64LE.Pack.bitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.PPC64LE.Pack.bitPack
  refine RelCT.seq (R := Agr .r5) (((relct_noMem (by rfl)).wpDep
    (F := fun (σ s' : State) => ((s'.gpr .r10 = σ.gpr .r3 ∧ s'.gpr .r11 = σ.gpr .r6 ∧
      s'.gpr .r7 = BitVec.ofNat 64 q ∧ s'.mem = σ.mem) ∧ Keep [.r10, .r11, .r7] σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) a),
      WP.withSp (mov2Q_ok (by decide) (by decide) (by decide) b)⟩).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, ⟨⟨⟨g₁, h₁, _⟩, k₁⟩, p₁⟩, ⟨⟨⟨g₂, h₂, _⟩, k₂⟩, p₂⟩⟩ => by
      sig_pub [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
      obtain ⟨hsp, e3, -, e5, e6, -⟩ := hpub
      refine ⟨by rw [p₁, p₂, hsp], by rw [g₁, g₂, e3], by rw [h₁, h₂, e6], ?_⟩
      simp only [lo]; rw [k₁.gpr (by decide), k₂.gpr (by decide), e5]) ?_
  exact sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
    (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
      (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
        (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide)) (leaf_ct (by taint_decide)))))

/-! ## `Verified` -/

/-- A state satisfying the precondition. -/
def bpSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 2 | .r5 => 2 | .r6 => 0x2000 | .r7 => 96 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

example : ∃ pre post leak, bitPackContract PPC64LE.abi =
    bitPackSig.contract PPC64LE.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem bitPack_verified :
    Verified PPC64LE.target Impl.MlDsa.PPC64LE.Pack.bitPack (bitPackContract PPC64LE.abi) := by
  refine ⟨fun s hs => ?_, bitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := bp_wp (BpPre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
    sig_post [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
    exact hpost
  · refine ⟨bpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitPackContract, bitPackSig, PPC64LE.abi, PPC64LE.argRegs]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | (unfold Reduced; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.PPC64LE.Pack
