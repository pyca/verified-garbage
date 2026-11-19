module

public import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.Ed448.Arm.BaseEncode
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.X448.Arm.Save
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Arm.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Ed448.Arm.BaseBits`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on ARMv7: the scalar's bits

All 57 bytes of the scalar expanded into bytes `BITS + t` holding bit `t`, as
X448's `bits` expands its 56 (without its clamping): byte `t` is bit `t` of
the scalar (`baseBits_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem baseBitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (baseBitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.r2] s t := by
  unfold baseBitJ
  refine VG.Proof.X25519.Arm.wp_mov (bitShift_eval s hj) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have ea : State.addr (u.gpr .r7 + BitVec.ofNat 32 (BITS + j)) = off base (BITS + (8 * i + j)) := by
    rw [hu.other .r7 (by decide), ht.other .r7 (by decide), hp,
      BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [BITS]; omega_using [hi, hj])]
    congr 1; omega_using []
  have wr := hs.write (d := BITS + (8 * i + j)) (n := 1) (by simp only [BITS]; omega_using [hi, hj])
  refine VG.Proof.X25519.Arm.wp_strb (by simp only [BITS]; omega_using [hj]) ea
    (by rw [hu.wr, ht.wr]; exact wr) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ ((t.gpr .r2 &&& (1 : BitVec 32)).setWidth 8) = _
    rw [ht.gpr, ha, bit_byte b j hj]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

/-- Expanding eight bits preserves each byte already written. -/
theorem baseByteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap baseBitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r2] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (baseBitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (baseBitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega_using [hi, hn, hj]) (by simp only [BITS]; omega_using [hi, hn])]
        omega_using []
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega_using [hj, he])
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega_using [hi, hn]) (by omega_using [hn, hx])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def baseBitHead : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0, .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def baseBitTail : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 57)]

def baseBitRegs : List Reg := [.r3, .r2, .r11, .r7]

theorem baseBitHead_ok {s : State} {k : Addr} (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block baseBitHead) s fun t =>
      t.gpr .r3 = (s.mem (off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r7] s t := by
  unfold baseBitHead
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => ?_
  have ea : State.addr (t.gpr .r7 + BitVec.ofNat 32 0) = off k i := by
    rw [ht.gpr]; change State.addr (s.gpr .r1 + s.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [BitVec.add_zero, hb, addr_add (by omega_using [hfit, hi]), hk]
  refine VG.Proof.X25519.Arm.wp_ldrb (by decide) ea (by rw [ht.rd, ht.wr]; exact hkr) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun v hv =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hv.other .r3 (by decide), hu.gpr, ht.mem]
  · rw [hv.gpr, hv.other .r0 (by decide)]
    change u.gpr .r0 + u.gpr .r11 <<< 3 = _
    rw [hu.other .r11 (by decide), ht.other .r11 (by decide), hb]
    apply congrArg (u.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  · exact hv.mem.trans (hu.mem.trans ht.mem)
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest (by decide))))

theorem baseBitTail_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .r11 = BitVec.ofNat 32 i) :
    WP isa (.block baseBitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.r11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (57 : BitVec 32)) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  unfold baseBitTail
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu hz =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.gpr]; change s.gpr .r11 + BitVec.ofNat 32 1 = _
    rw [hb, ← BitVec.ofNat_add]
  · rw [hz, ht.gpr]; change ((s.gpr .r11 + 1 - 57) == 0) = _
    rw [hb]; exact check i hi
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem baseBitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block baseBitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧ Keeps baseBitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (baseBitHead ++ (List.range 8).flatMap baseBitJ ++ baseBitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (baseBitHead_ok hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (baseByteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (baseBitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The bits loop's invariant, after `i` bytes. -/
structure BitsInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  r1 : State.addr (s.gpr .r1) = k
  fit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ baseBitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem baseBitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → BitsInv base k s₀ s i →
      WP isa (.loop (.block baseBitsBody) .ne) s fun s' => BitsInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block baseBitsBody) (c := .ne)
    (Q := fun s' => BitsInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ BitsInv base k s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (baseBitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega_using [this])
  have inv : BitsInv base k s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.r1),
      (by rw [g' _ (by decide)]; exact hb.fit), b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega_using []) (by omega_using [hi])),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega_using [hi, ht])]; omega_using [h]), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega_using [ht])
      rw [show 8 * i + (t - 8 * i) = t by omega_using [h], hbyte] at e
      rw [e, show t / 8 = i by omega_using [ht, h], show t % 8 = t - 8 * i by omega_using [ht, h]]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [h] : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega_using [hi], i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega_using [hi, h]
    exact .inl ⟨rfl, inv⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- Bit `t` of the scalar is bit `t % 8` of its byte `t / 8`. -/
theorem scalar_bit (m : Mem) (p : Addr) {t : Nat} (ht : t < 456) :
    ((m (p + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1 =
      (decodeLE (bytesAt m p 57) >>> t) &&& 1 := by
  rw [Proof.Ed448.decodeLE_eq, Proof.X25519.leNum_bit, bytesAt_getD m p (by omega_using [ht])]

/-- `baseBits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`. -/
theorem baseBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa baseBits s fun s' =>
      (∀ r, r ∉ baseBitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> t) &&& 1) := by
  unfold baseBits
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => BitsInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : Keeps baseBitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (baseBitsLoop_ok hkr hkd 0 s₁ (by omega_using []) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega_using [ht]), scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm

end

end

/-!
# Ed448 base-point multiplication on ARMv7: the whole function

`vg_ed448_scalar_base(out = r0, scalar = r1, scratch = r2)` computes the
encoding of the comb over the scalar's bits (`scalarBase_comb`): the
entry, the scalar's bits, the loop (`R` ends as `comb k 114`), the
inversion of `Z` and the encoding. Every write is in the working space but
the result's, so the scalar is read unchanged; the callee-saved registers are
restored from the working space, and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (comb)
open VG.Impl.X448.Arm (slot BITS ACC saved)
open VG.Spec.Ed448 (bytesAt decodeLE)

variable {fv : Bool}

/-- The precondition of `vg_ed448_scalar_base`, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 57⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  scalar_ws : (⟨State.addr (s.gpr .r1), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 57 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far_ws {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_using [hi])
    (by omega_using [hi, hn])) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega_using [h]

theorem baseEntry_eq : baseEntry =
    ([.mov .r3 (.reg .r2)] : List Instr) ++ setupHead ++ initSlots := rfl

theorem scalarBase_comb {s : State} (h : BasePre s) :
    WP isa (scalarBase fv) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      bytesAt t.mem (State.addr (s.gpr .r0)) 57 =
        Spec.Ed448.encodePoint (comb (decodeLE (bytesAt s.mem (State.addr (s.gpr .r1)) 57)) 114) := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r2) = b := ⟨_, rfl⟩
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, ← hbase]; simp
  have kd : ∀ j < 57, 8192 ≤ ofs base (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) :=
    fun j hj => far_ws (hbase ▸ h.scalar_ws) hj (by decide)
  have kr : ∀ j < 57, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1) + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨State.addr (s.gpr .r1), 57⟩, by rw [h.rd]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  unfold scalarBase
  rw [baseEntry_eq, List.append_assoc, List.singleton_append]
  -- The entry.
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => ?_)
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok (s := u) (base := base) (by rw [hu.gpr, hbase])
    (by rw [hu.wr]; exact hw₀) (by rw [hu.gpr]; exact h.f2)) fun v ⟨hsv, rv, rl, svv, ov, kv⟩ => ?_
  refine WP.mono (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw : Scr w base := hsv.of_keeps kw (by decide)
  have kuw : Keeps [.r3, .r8, .r10, .r0, .r6, .r4] s w :=
    (rest_keeps (hu.rest (by decide))).trans ((kv.mono (by decide)).trans (kw.mono (by decide)))
  have r1w : w.gpr .r1 = s.gpr .r1 := kuw.1 _ (by decide)
  have r12w : w.gpr .r8 = s.gpr .r0 := by
    rw [kw.1 _ (by decide), rv, hu.other _ (by decide)]
  have r10w : w.gpr .r10 = s.gpr .lr := by
    rw [kw.1 _ (by decide), rl, hu.other _ (by decide)]
  have mw : ∀ x, 8192 ≤ ofs base x → w.mem x = s.mem x := fun x hx => by
    rw [ow x (Or.inr (by omega_using [hx])), ov x (Or.inr (by omega_using [hx])), hu.mem]
  have bw : bytesAt w.mem (State.addr (s.gpr .r1)) 57 = bytesAt s.mem (State.addr (s.gpr .r1)) 57 := by
    unfold bytesAt; exact List.map_congr_left fun j hj => mw _ (kd j (List.mem_range.mp hj))
  have sn : ∀ i < 8, saved[i]! ≠ .r3 := by decide
  have svw : Saved base s.gpr w.mem := by
    intro i hi
    rw [ow.word (by omega_using [hi]) (by omega_using [hi]), svv i hi]
    exact hu.other _ (sn i hi)
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok (k := State.addr (s.gpr .r1)) hsw (by rw [r1w])
    (by rw [r1w]; exact h.f1) (by rw [kuw.2.1, kuw.2.2]; exact kr) kd)
    fun x ⟨gx, rdx, wrx, ox, bitsx⟩ => ?_)
  have kx : Keeps baseBitRegs w x := ⟨gx, rdx, wrx⟩
  have hsx : Scr x base := hsw.of_keeps kx (by decide)
  have ex : ∀ i : Index, E x.mem base i = Proof.X448.toFe (initVal i.val) := by
    intro i
    rw [← initSlots_E lw i]
    simp only [E, F]
    rw [ox.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using [])]
  have bx : BoundedEnv x.mem base := by
    intro i j hj
    rw [ox.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []) hj]
    exact initSlots_bounded lw i j hj
  rw [bw] at bitsx
  -- The loop.
  refine WP.seq (WP.mono (combLoop_ok (s₀ := x) (s := x) bitsx (fun s' h1 h2 h3 h4 h5 => ?_))
    fun y hy => ?_)
  · have k' : Keeps (.r11 :: workRegs) x s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hsx.of_keeps k' (by decide), h3 ▸ bx, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [h3]; simp only [pt, ex]
      rw [show ((0 : Index) : Nat) = 0 from rfl, show ((1 : Index) : Nat) = 1 from rfl,
        show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
        show initVal 1 = Spec.Ed448.identity.Y.val from rfl,
        show initVal 2 = Spec.Ed448.identity.Z.val from rfl, Proof.X448.toFe_self,
        Proof.X448.toFe_self, Proof.X448.toFe_self]
      rfl
    · rw [h3, ex, show ((10 : Index) : Nat) = 10 from rfl,
        show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self]
      rfl
    · rw [h3, ex]; exact Proof.X448.toFe_self _
  -- The encoding.
  have r12y : y.gpr .r8 = s.gpr .r0 := by
    rw [hy.regs.1 _ (by decide), gx _ (by decide), r12w]
  have r10y : y.gpr .r10 = s.gpr .lr := by
    rw [hy.regs.1 _ (by decide), gx _ (by decide), r10w]
  have wry : y.wr = s.wr := by rw [hy.regs.2.2, wrx, kuw.2.2]
  have svy : Saved base s.gpr y.mem :=
    (svw.outside ox (by decide)).outside2 hy.mem (by decide) (by decide)
  refine WP.mono (baseEncode_ok hy.scr hy.bounded (q := State.addr (s.gpr .r0)) (by rw [r12y])
    (by rw [r12y]; exact h.f0) (by rw [wry, h.wr]; simp) (hbase ▸ h.out_ws) svy)
    fun t ⟨bt, rt, _, lt, _⟩ => ?_
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt 0 (by decide)
    · exact rt 1 (by decide)
    · exact rt 2 (by decide)
    · exact rt 3 (by decide)
    · exact rt 4 (by decide)
    · exact rt 5 (by decide)
    · exact rt 6 (by decide)
    · exact rt 7 (by decide)
    · exact lt.trans r10y
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint hy.r
