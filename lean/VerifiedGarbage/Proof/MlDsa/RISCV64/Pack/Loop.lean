module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on RISC-V: the loops over the groups

As on 32-bit ARM (`Proof/MlDsa/Arm/Pack/Loop.lean`): `packLoop_ok`, the loop
of `packBody` writes the packing of the values of the 256 coefficients at
`f`; `unpackLoop_ok`, the loop of `unpackBody` writes, for each field of the
bytes at `v`, `fin`'s coefficient of it. Both for any width and any `ld` or
`fin`, from the group lemmas of `Stream.lean`, and for any state that
permits the accesses: they change only the output and the registers of
`loopRegs`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz)
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
theorem liN_ok (N : Nat) (hN : N < 2048) (s : State) :
    WP isa (.block [.li .t2 N]) s fun s' =>
      (s'.gpr .t2 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.t2] s s' := by
  refine WP.keep _ ?_ rfl rfl
  exact Steps.wp_li hN fun s₁ u₁ => WP.block_nil ⟨u₁.gpr, u₁.mem⟩

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
  a7 : s.gpr .a7 = pf + BitVec.ofNat 64 (4 * c * i)
  t1 : s.gpr .t1 = po + BitVec.ofNat 64 (nb * i)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (256 / c - i)
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [⟨po, 32 * d⟩] m₀ s.mem
  done : ∀ k < nb * i, s.mem (po + BitVec.ofNat 64 k) = (bitsToBytes (fieldBits d (vals V m₀ pf)))[k]!
  keep : Keep loopRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv V d c nb pf po m₀ rd wr sE i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv V d c nb pf po m₀ rd wr sE (i + 1) s' ∧ (s'.gpr .t2 != 0) = decide (i + 1 ≠ 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ha : ∀ j, s.gpr .a7 + BitVec.ofNat 64 (4 * j) = coeffAddr pf (c * i + j) :=
    fun j => by rw [hI.a7, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .t1 + BitVec.ofNat 64 t = po + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [hI.t1, off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32 = coeffAt m₀ pf (c * i + j) :=
    fun j hj => by
      rw [ha j]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega_arith)
  refine WP.mono (packBody_ok hld hRs hs.d20 hs.dc hs.c8 s (hRs sE s hRE hI.keep)
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains _ (by omega_arith)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (by
      rw [hI.a7, hI.t1]
      exact (hsep.sub_left (Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith))).sub_right
        (Offset.sub_base _ (by omega_arith)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega_arith)))
    fun s' ⟨hW, x', y', c', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.a7]; exact ptr_step _ i (4 * c)
  · rw [y', hI.t1]; exact ptr_step _ i nb
  · rw [c']; exact (count_step hi hN hI.t2).1
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · refine hI.frame.trans (hW.1.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [hI.t1]; exact Offset.sub_base _ (by omega_arith)⟩
  · by_cases hk' : k < nb * i
    · -- Written before.
      rw [← hI.done k hk']
      refine hW.1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [hI.t1] at hc
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
  · rw [c']; exact (count_step hi hN hI.t2).2

theorem packLoop_ok {s : State} (h10 : s.gpr .a7 = pf) (h11 : s.gpr .t1 = po) (hrd : s.rd = rd)
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
  a7 : s.gpr .a7 = pv + BitVec.ofNat 64 (nb * i)
  t1 : s.gpr .t1 = pp + BitVec.ofNat 64 (4 * c * i)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (256 / c - i)
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
      UInv W d c nb pv pp m₀ rd wr sE (i + 1) s' ∧ (s'.gpr .t2 != 0) = decide (i + 1 ≠ 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ha : ∀ j, s.gpr .t1 + BitVec.ofNat 64 (4 * j) = coeffAddr pp (c * i + j) :=
    fun j => by rw [hI.t1, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .a7 + BitVec.ofNat 64 t = pv + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [hI.a7, off_add]
  have hsub : Region.Sub ⟨s.gpr .t1, 4 * c⟩ (polyRegion pp) := by
    rw [hI.t1]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith)
  refine WP.mono (unpackBody_ok hfin hRs hs.d1 hs.d20 hs.dc hs.c8 s (hRs sE s hRE hI.keep)
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains _ (by omega_arith)))
    (by rw [hI.a7]; exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hsub))
    fun s' ⟨hw, hf, x', p', c', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_),
      fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.a7]; exact ptr_step _ i nb
  · rw [p', hI.t1]; exact ptr_step _ i (4 * c)
  · rw [c']; exact (count_step hi hN hI.t2).1
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  · -- The bytes of the group, on entry.
    have hB : (List.range nb).map (fun t => (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat) =
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
      rw [hI.t1]
      exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega_arith) (by omega_arith) (by rw [Nat.mul_assoc]; omega_arith)
    · -- Written by this group.
      have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega_arith
      have := hw (k - c * i) hj
      rw [ha, show c * i + (k - c * i) = k by omega_arith, hB, digits_group hs.dc hlt hj,
        show c * i + (k - c * i) = k by omega_arith] at this
      rw [coeffAt_eq, this]
  · rw [c']; exact (count_step hi hN hI.t2).2

theorem unpackLoop_ok {s : State} (h10 : s.gpr .a7 = pv) (h11 : s.gpr .t1 = pp) (hrd : s.rd = rd)
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

end VG.Proof.MlDsa.RISCV64.Pack
