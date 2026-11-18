module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlKem.Arm.Common
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.MlKem.Arm.Add
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Stream
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Stream
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlDsa.Pack.Bits

/-! ### `MlDsa.Arm.Pack.SimpleBitPack`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.Pack.Loop`, which this module and modules that import it used -/

section

/-! ### `MlDsa.Arm.Pack.Stream`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: streaming fields through `r3`

The group bodies of `Impl/MlDsa/Arm/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`), as on
x86-64:

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator `r3` is a slice of the number throughout
(`Proof/MlDsa/Pack/Stream.lean`), of at most `d + 7 ≤ 27` bits.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Proof.MlKem.Arm (byte_writeW8 contains_off setWidth8 setWidth32_toNat)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

/-! ## Registers kept -/

/-- `s'` has the registers of `s` but for `rs`, and its regions and stack pointer. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => (dsts i).all rs.contains

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  obtain he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  exact ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi =>
    clobbers_eq_false_of_contains (List.all_eq_true.mp hc i hi) hr) he', r, w, p⟩

/-! ## Instructions -/

/-- `r3 ← r3 + r12 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh ≤ 31) (s : State)
    (hs : (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32) :
    WP isa (.block [shiftAdd sh]) s fun s' =>
      ((s'.gpr .r3).toNat = (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ite_true]
    run_block [and_true]
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · simp only [shiftAdd, h, ite_false]
    run_block [show 1 ≤ sh by omega_arith, hsh, and_true]
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 4096) (s : State)
    (hout : InRegions s.wr (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) (BitVec.ofNat 8 (s.gpr .r3).toNat) ∧
        (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ 8) ∧ Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  unfold packByte
  run_block [ht, hout, and_true]
  exact ⟨by rw [setWidth8], by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩

/-- The first `n` bytes of the group of `nb` bytes at `o` are `V 0, …, V (n - 1)`,
and memory is `m₀`'s outside the group. -/
def GOut (m₀ m : Mem) (o : Addr) (nb n : Nat) (V : Nat → Byte) : Prop :=
  Frame [⟨o, nb⟩] m₀ m ∧ ∀ t < n, m (o + BitVec.ofNat 64 t) = V t

/-- The bytes `k, …, k + nf - 1` of the group from the accumulator `X`,
whose byte `u` is byte `k + u` of the group. -/
theorem flush_ok {k nf nb : Nat} {m₀ : Mem} {o : Addr} {y : BitVec 32} {V : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V (k + u)) (hk : k + nf ≤ nb) (hnb : nb < 4096)
    (s : State) (h2 : s.gpr .r2 = y) (ho : ∀ t < nb, State.addr (y + BitVec.ofNat 32 t) = o + BitVec.ofNat 64 t)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hw : GOut m₀ s.mem o nb k V) (hr : (s.gpr .r3).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      GOut m₀ s'.mem o nb (k + nf) V ∧ (s'.gpr .r3).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r3] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r3] s s' ∧
    (s'.gpr .r3).toNat = X / 2 ^ (8 * u) ∧ GOut m₀ s'.mem o nb (k + u) V)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  obtain h2' : s'.gpr .r2 = y := (hkp.gpr (by decide)).trans h2
  obtain ea : State.addr (s'.gpr .r2 + BitVec.ofNat 32 (k + u)) = o + BitVec.ofNat 64 (k + u) := by
    rw [h2']; exact ho _ (by omega_arith)
  refine WP.mono (packByte_ok (by omega_arith) s' (by rw [ea, hkp.2.2.1]; exact hout _ (by omega_arith)))
    fun s'' ⟨⟨hm, h3⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_, ?_⟩
  · rw [h3, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ea]
    exact hw'.1.writeW (List.mem_singleton_self _) _ (contains_off (by omega_arith) (by omega_arith))
  · intro t ht
    rw [hm, ea, byte_writeW8 _ _ (by omega_arith) (by omega_arith)]
    by_cases e : t = k + u
    · rw [ite_eq_left e, hr', hX u hu, e]
    · rw [ite_eq_right e]; exact hw'.2 t (by omega_arith)

/-- `ld j` loads into `r12` the value `V` of the word at `r0 + 4j`, and
writes only `r4` and `r12`. -/
def LdOk (ld : Nat → List Instr) (V : BitVec 32 → Nat) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .r12).toNat = V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) ∧
        s'.mem = s.mem) ∧ Keep [.r4, .r12] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r3`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d j nb G : Nat}
    (hd : d ≤ 20) (hj : j < 8) (hnb : nb < 4096) (hjn : d * (j + 1) / 8 ≤ nb) {m₀ : Mem} {o : Addr}
    {y : BitVec 32} (s : State) (h2 : s.gpr .r2 = y)
    (ho : ∀ t < nb, State.addr (y + BitVec.ofNat 32 t) = o + BitVec.ofNat 64 t)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4)
    (hv : V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hw : GOut m₀ s.mem o nb (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      GOut m₀ s'.mem o nb (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.r3, .r4, .r12] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s (by omega_arith) hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  obtain hx : (s₁.gpr .r12).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  obtain hr₁ : (s₁.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  obtain hacc := pack_acc_lt G d j
  obtain hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  obtain hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega_arith) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega_arith))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  obtain hX : (s₂.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  obtain h2₂ : s₂.gpr .r2 = y := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h2]
  obtain hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
  obtain hsum : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega_arith
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (V := bytesOf G) _
    (fun u hu => ?_) (by omega_arith) hnb s₂ h2₂ ho (by rw [k₂.2.2.1, k₁.2.2.1]; exact hout)
    (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨by rwa [hsum] at hw₃, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega_arith
      omega_arith)]
  · rw [hr₃, pack_shift, hsum]

theorem zero_ok (s : State) :
    WP isa (.block [.mov .r3 (.imm 0)]) s fun s' => ((s'.gpr .r3).toNat = 0 ∧ s'.mem = s.mem) ∧ Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

theorem packTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * c))), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 nb)),
      .subs .r1 .r1 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧ s'.mem = s.mem) ∧
        Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r2`. -/
theorem packBody_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State)
    (hx : (s.gpr .r0).toNat + 4 * c ≤ 2 ^ 32) (hy : (s.gpr .r2).toNat + nb ≤ 2 ^ 32)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 t) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), 4 * c⟩ ⟨State.addr (s.gpr .r2), nb⟩)
    (hF : ∀ j < c, V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb nb (bytesOf (digits d ((List.range c).map fun j =>
          V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hG : digits d ((List.range c).map fun j =>
    V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)) = G
  obtain hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d =
      V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  obtain ea : ∀ j < c, State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega_arith)
  obtain ho : ∀ t < nb, State.addr (s.gpr .r2 + BitVec.ofNat 32 t) = State.addr (s.gpr .r2) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega_arith)
  obtain hnb : nb ≤ 20 := by have := Nat.mul_le_mul hd hc; omega_arith
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  obtain x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  obtain y₁ : s₁.gpr .r2 = s.gpr .r2 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r3, .r4, .r12] s₁ s' ∧
      GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, ⟨by rw [m₁]; exact Frame.refl _ _, fun t ht => absurd ht (by simp)⟩,
      by rw [z₁, Nat.mul_zero, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]⟩)
    fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    obtain yj : s'.gpr .r2 = s.gpr .r2 := (hk.gpr (by decide)).trans y₁
    obtain hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); omega_arith
    obtain hA : State.addr (s'.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
        State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := by rw [xj]; exact ea j hj
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd (by omega_arith) (by omega_arith) hj8 s' yj ho
      (by rw [hk.2.2.1, k₁.2.2.1]; exact hout) (by rw [hA, hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin j hj)
      ?_ hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [hA, hdig j hj]
    refine congrArg V (hw.1.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_left (Offset.sub_base _ (by omega_arith))
  · have hc8 : d * c / 8 = nb := by omega_arith
    rw [hc8] at hw₂
    refine WP.mono (packTail_ok e₁ e₂ s₂) fun s₃ ⟨⟨x₃, y₃, c₃, z₃, m₃⟩, k₃⟩ =>
      ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [y₃, k₂.gpr (by decide), y₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]

/-! ## Unpacking -/

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j ≤ 31) (ht : t < 4096) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 t)) 1)
    (hs : (s.gpr .r3).toNat + (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat * 2 ^ (8 * t - d * j) <
      2 ^ 32) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .r3).toNat =
          (s.gpr .r3).toNat + (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.r3, .r12] s s' := by
  rw [show unpackByte d j t = ([.ldrb .r12 .r0 t] : List Instr) ++ [shiftAdd (8 * t - d * j)] from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun s' => s'.gpr .r12 =
    (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).setWidth 32 ∧ s'.mem = s.mem)
    (by run_block [ht, hin, and_true]) rfl) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  obtain hax : (s₁.gpr .r12).toNat = (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat := by
    rw [ax₁, setWidth32_toNat]
  refine WP.mono (shiftAdd_ok hsh s₁ (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` (at `x`) into the accumulator, which
holds bits `d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} {x : BitVec 32} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk' : k + nl ≤ 4096) (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (k + u))) 1)
    (hb : ∀ u < nl, (s.mem (State.addr (x + BitVec.ofNat 32 (k + u)))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.r3, .r12] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r3, .r12] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  obtain x' : s'.gpr .r0 = x := (hkp.gpr (by decide)).trans h0
  obtain hacc := unpack_acc_lt H (k + u) (d * j)
  obtain hbu := hb u hu
  rw [← hm, ← x'] at hbu
  obtain hbl : (s'.mem (State.addr (s'.gpr .r0 + BitVec.ofNat 32 (k + u)))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  obtain hsh : 8 * (k + u) - d * j ≤ 19 := by omega_arith
  obtain hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok (by omega_arith) (by omega_arith) s' (by rw [hkp.2.1, hkp.2.2.1, x']; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega_arith
      omega_arith))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega_arith), Nat.add_assoc]

/-- The low `d` bits of `r3` into `r12`, and `r3` shifted right by `d`. -/
theorem extract_ok {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block (extract d)) s fun s' =>
      ((s'.gpr .r12).toNat = (s.gpr .r3).toNat % 2 ^ d ∧ (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ d ∧
        s'.mem = s.mem) ∧ Keep [.r3, .r12] s s' := by
  refine WP.keep _ ?_ rfl
  unfold extract
  run_block [show 1 ≤ 32 - d by omega_arith, show 32 - d ≤ 31 by omega_arith, hd1, show d ≤ 31 by omega_arith, and_true]
  refine ⟨?_, by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 2 ^ 32 = 2 ^ d * 2 ^ (32 - d) by rw [← Nat.pow_add]; congr 1; omega_arith, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `r12` to
`r1 + 4j`, and writes only `r4` and `r12`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 →
    (s.gpr .r12).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (s.gpr .r12).toNat) ∧
        Keep [.r4, .r12] s s'

/-- Field `j`: the bytes it needs into `r3`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (hj : j < 8) {x : BitVec 32} (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 t)) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (State.addr (x + BitVec.ofNat 32 t))).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r3).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.r3, .r4, .r12] s s' := by
  obtain hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  obtain hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega_arith)
  obtain hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega_arith
  obtain hn8 : need d (j + 1) ≤ 20 := by unfold need; have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega_arith); omega_arith
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega_arith) (by rw [hn']; unfold need; omega_arith) (by omega_arith) s h0 (fun u hu => hin _ (by omega_arith))
    (fun u hu => hb _ (by omega_arith)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (extract_ok hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  obtain hv : (s₂.gpr .r12).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega_arith)]
  obtain p₂ : s₂.gpr .r1 = s.gpr .r1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by omega_arith) (by rw [k₂.2.2.1, k₁.2.2.1, p₂]; exact hout)
      (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, p₂, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, r₁, unpack_shift]

theorem unpackTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 nb) = true)
    (e₂ : encodable (BitVec.ofNat 32 (4 * c)) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 nb)), .dp .add .r1 .r1 (.imm (BitVec.ofNat 32 (4 * c))),
      .subs .r2 .r2 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 nb ∧ s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem) ∧
        Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `r0`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8)
    (e₁ : encodable (BitVec.ofNat 32 nb) = true) (e₂ : encodable (BitVec.ofNat 32 (4 * c)) = true) (s : State)
    (hx : (s.gpr .r0).toNat + nb ≤ 2 ^ 32) (hp : (s.gpr .r1).toNat + 4 * c ≤ 2 ^ 32)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), nb⟩ ⟨State.addr (s.gpr .r1), 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨State.addr (s.gpr .r1), 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 nb ∧ s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧
        Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t =>
    (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) = H
  obtain ea : ∀ t < nb, State.addr (s.gpr .r0 + BitVec.ofNat 32 t) = State.addr (s.gpr .r0) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega_arith)
  obtain ep : ∀ j < c, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega_arith)
  obtain hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  obtain hneed : need d c = nb := by unfold need; omega_arith
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  obtain x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  obtain p₁ : s₁.gpr .r1 = s.gpr .r1 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r3, .r4, .r12] s₁ s' ∧
      Frame [⟨State.addr (s.gpr .r1), 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j')) 32 =
        W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    obtain pj : s'.gpr .r1 = s.gpr .r1 := (hk.gpr (by decide)).trans p₁
    obtain hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) (by omega_arith) s' xj
      (fun t ht => by rw [ea t (by omega_arith), hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin t (by omega_arith))
      (fun t ht => by
        rw [ea t (by omega_arith), hbyte t (by omega_arith)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      (by rw [pj, ep j hj, hk.2.2.1, k₁.2.2.1]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', pj, ep j hj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [m'', pj, ep j hj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hw j' (by omega_arith)]
  · refine WP.mono (unpackTail_ok e₁ e₂ s₂)
      fun s₃ ⟨⟨x₃, p₃, c₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [p₃, k₂.gpr (by decide), p₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.Arm.Pack

end

end


/-!
# ML-DSA on 32-bit ARM: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`, and for any
state that permits the accesses: they change only the output, the registers of
`packRegs` or `unpackRegs` and the flags.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa (bitsToBytes)
open VG.Proof.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- The value of each coefficient is less than `2ᵈ`, the groups tile the
polynomial and the output, and the immediates of the loop are encodable. -/
structure Shape (d c nb : Nat) : Prop where
  d1 : 1 ≤ d
  d20 : d ≤ 20
  dc : d * c = 8 * nb
  c0 : 0 < c
  c8 : c ≤ 8
  cN : c * (256 / c) = 256
  bN : nb * (256 / c) = 32 * d
  e4c : encodable (BitVec.ofNat 32 (4 * c)) = true
  enb : encodable (BitVec.ofNat 32 nb) = true
  eN : encodable (BitVec.ofNat 32 (256 / c)) = true

theorem Shape.nb20 {d c nb : Nat} (h : Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega_arith

theorem Shape.nb0 {d c nb : Nat} (h : Shape d c nb) : 0 < nb := by
  have := Nat.mul_le_mul h.d1 h.c0; have := h.dc; omega_arith

theorem Shape.group {d c nb : Nat} (h : Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  obtain h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega_arith)
  obtain h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega_arith)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega_arith

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ptr_step (p : BitVec 32) (i c : Nat) :
    p + BitVec.ofNat 32 (c * i) + BitVec.ofNat 32 c = p + BitVec.ofNat 32 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

theorem ptr_toNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) : (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt h]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The registers a loop writes. -/
abbrev packRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12]
abbrev unpackRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r12]

/-- `mov r, #N`. -/
theorem movN_ok (r : Reg) (N : Nat) (hN : encodable (BitVec.ofNat 32 N) = true) (s : State) :
    WP isa (.block [.mov r (.imm (BitVec.ofNat 32 N))]) s fun s' =>
      (s'.gpr r = BitVec.ofNat 32 N ∧ s'.mem = s.mem) ∧ Keep [r] s s' := by
  refine WP.keep _ ?_ (by (cases r <;> rfl))
  run_block [hN, and_true]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : LdOk ld V) {d c nb : Nat} (hs : Shape d c nb)
  {pf po : BitVec 32} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hin : polyRegion (State.addr pf) ∈ rd ++ wr) (hout : (⟨State.addr po, 32 * d⟩ : Region) ∈ wr)
  (hsep : Region.Disjoint (polyRegion (State.addr pf)) ⟨State.addr po, 32 * d⟩)
  (fitF : pf.toNat + 1024 ≤ 2 ^ 32) (fitO : po.toNat + 32 * d ≤ 2 ^ 32)
  (hF : ∀ i < 256, V (coeffAt m₀ (State.addr pf) i) < 2 ^ d)
include hld hs hin hout hsep fitF fitO hF

/-- The values of the coefficients. -/
abbrev vals (V : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => V (coeffAt m f i)

omit hld hs hin hout hsep fitF fitO hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, V (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ vals V m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

omit hld hs hin hout hsep fitF fitO hF in
/-- After `i` groups. -/
structure PInv (V : BitVec 32 → Nat) (d c nb : Nat) (pf po : BitVec 32) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pf + BitVec.ofNat 32 (4 * c * i)
  r2 : s.gpr .r2 = po + BitVec.ofNat 32 (nb * i)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (1 * (256 / c - i))
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [⟨State.addr po, 32 * d⟩] m₀ s.mem
  done : ∀ k < nb * i, s.mem (State.addr po + BitVec.ofNat 64 k) =
    (bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))))[k]!
  keep : Keep packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : PInv V d c nb pf po m₀ rd wr sE i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      PInv V d c nb pf po m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  obtain hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  obtain ex : State.addr (s.gpr .r0) = State.addr pf + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r0]; exact addr_add (by rw [Nat.mul_assoc]; omega_arith)
  obtain ey : State.addr (s.gpr .r2) = State.addr po + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r2]; exact addr_add (by omega_arith)
  obtain ha : ∀ j, State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pf) (c * i + j) :=
    fun j => by rw [ex, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  obtain hb : ∀ t, State.addr (s.gpr .r2) + BitVec.ofNat 64 t = State.addr po + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ey, off_add]
  -- The words of the group are those on entry.
  obtain hw : ∀ j < c, s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 =
      coeffAt m₀ (State.addr pf) (c * i + j) :=
    fun j hj => by
      rw [ha j]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega_arith)
  refine WP.mono (packBody_ok hld hs.d20 hs.dc hs.c8 hs.e4c hs.enb s
    (by rw [hI.r0, ptr_toNat (by rw [Nat.mul_assoc]; omega_arith)]; rw [Nat.mul_assoc]; omega_arith)
    (by rw [hI.r2, ptr_toNat (by omega_arith)]; omega_arith)
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact inRegions_of hin (coeff_contains _ (by omega_arith)))
    (fun t ht => by rw [hb, hI.wr]; exact inRegions_of hout (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (by
      rw [ex, ey]
      exact (hsep.sub_left (Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith))).sub_right
        (Offset.sub_base _ (by omega_arith)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega_arith)))
    fun s' ⟨hW, x', y', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact ptr_step _ i (4 * c)
  · rw [y', hI.r2]; exact ptr_step _ i nb
  · rw [c', hI.r1]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · refine hI.frame.trans (hW.1.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [ey]; exact Offset.sub_base _ (by omega_arith)⟩
  · have hE : (bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))))[k]! = _ := rfl
    by_cases hk' : k < nb * i
    · -- Written before.
      rw [← hI.done k hk']
      refine hW.1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [ey] at hc
      exact Offset.disjoint (State.addr po) (d := k) (n := 1) (e := nb * i) (k := nb) (by omega_arith) (by omega_arith)
        (by omega_arith) _ (Region.contains_self _ _) hc
    · -- Written by this group.
      obtain ht : k - nb * i < nb := by rw [Nat.mul_succ] at hk; omega_arith
      have := hW.2 (k - nb * i) ht
      rw [hb, show nb * i + (k - nb * i) = k by omega_arith] at this
      obtain e : k = nb * i + (k - nb * i) := by omega_arith
      rw [this]
      conv => rhs; rw [e]
      rw [pack_group (c := c) (by have := hs.d1; omega_arith) hs.dc (by simp) (vals_lt hF) ht (by omega_arith),
        take_drop_eq _ 0 (by simp; omega_arith)]
      refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * (k - nb * i)))) (List.map_congr_left fun j hj => ?_)
      obtain hj := List.mem_range.mp hj
      rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega_arith)]
      rfl
  · rw [z', hI.r1]; exact count_z (k := 1) hi (by decide) (by omega_arith)

theorem packLoop_ok {s : State} (h0 : s.gpr .r0 = pf) (h2 : s.gpr .r2 = po) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem (State.addr po) (32 * d) = bitsToBytes (fieldBits d (vals V m₀ (State.addr pf))) ∧
        Frame [⟨State.addr po, 32 * d⟩] m₀ s'.mem ∧ Keep packRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  obtain hN0 : 0 < 256 / c := Nat.div_pos (by omega_arith) h0'
  unfold packLoop
  refine WP.seq (WP.mono (movN_ok .r1 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (PInv V d c nb pf po m₀ rd wr s) hN0
    (fun i hi s' hI => packStep hld hs hin hout hsep fitF fitO hF hi hI)
    (fun s' hI => ⟨bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk),
      hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), k₁.mono (by decide)⟩
  · rw [k₁.gpr (by decide), h0]; simp
  · rw [k₁.gpr (by decide), h2]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2.1, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

/-! ## Unpacking -/

/-- The number whose bytes are the `32 d` bytes of the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (W : Nat → BitVec 32) (d c nb : Nat) (pv pp : BitVec 32) (m₀ : Mem) (rd wr : List Region)
    (sE : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pv + BitVec.ofNat 32 (nb * i)
  r1 : s.gpr .r1 = pp + BitVec.ofNat 32 (4 * c * i)
  r2 : s.gpr .r2 = BitVec.ofNat 32 (1 * (256 / c - i))
  rd : s.rd = rd
  wr : s.wr = wr
  frame : Frame [polyRegion (State.addr pp)] m₀ s.mem
  done : ∀ k < c * i, coeffAt s.mem (State.addr pp) k = W (inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep unpackRegs sE s

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : FinOk fin d W)
  (hs : Shape d c nb) {pv pp : BitVec 32} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hin : (⟨State.addr pv, 32 * d⟩ : Region) ∈ rd ++ wr) (hout : polyRegion (State.addr pp) ∈ wr)
  (hsep : Region.Disjoint ⟨State.addr pv, 32 * d⟩ (polyRegion (State.addr pp)))
  (fitV : pv.toNat + 32 * d ≤ 2 ^ 32) (fitP : pp.toNat + 1024 ≤ 2 ^ 32)
include hfin hs hin hout hsep fitV fitP

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : UInv W d c nb pv pp m₀ rd wr sE i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      UInv W d c nb pv pp m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  obtain hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  obtain ex : State.addr (s.gpr .r0) = State.addr pv + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r0]; exact addr_add (by omega_arith)
  obtain ep : State.addr (s.gpr .r1) = State.addr pp + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r1]; exact addr_add (by rw [Nat.mul_assoc]; omega_arith)
  obtain ha : ∀ j, State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pp) (c * i + j) :=
    fun j => by rw [ep, off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  obtain hb : ∀ t, State.addr (s.gpr .r0) + BitVec.ofNat 64 t = State.addr pv + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ex, off_add]
  obtain hsub : Region.Sub ⟨State.addr (s.gpr .r1), 4 * c⟩ (polyRegion (State.addr pp)) := by
    rw [ep]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega_arith)
  refine WP.mono (unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 hs.enb hs.e4c s
    (by rw [hI.r0, ptr_toNat (by omega_arith)]; omega_arith)
    (by rw [hI.r1, ptr_toNat (by rw [Nat.mul_assoc]; omega_arith)]; rw [Nat.mul_assoc]; omega_arith)
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact inRegions_of hin (Offset.contains_base _ (by omega_arith) (by omega_arith)))
    (fun j hj => by rw [ha, hI.wr]; exact inRegions_of hout (coeff_contains _ (by omega_arith)))
    (by rw [ex]; exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right hsub))
    fun s' ⟨hw, hf, x', p', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_),
      fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact ptr_step _ i nb
  · rw [p', hI.r1]; exact ptr_step _ i (4 * c)
  · rw [c', hI.r2]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  · -- The bytes of the group, on entry.
    obtain hB : (List.range nb).map (fun t => (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) =
        (((bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
      rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega_arith)]
      refine List.map_congr_left fun t ht => ?_
      obtain ht := List.mem_range.mp ht
      rw [getD_map_toNat, bytesAt_getD _ _ (by omega_arith), hb]
      refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    obtain hlt : ∀ a ∈ (bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
    by_cases hk' : k < c * i
    · -- Written before.
      rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
      refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [ep]
      exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega_arith) (by omega_arith) (by rw [Nat.mul_assoc]; omega_arith)
    · -- Written by this group.
      obtain hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega_arith
      have := hw (k - c * i) hj
      rw [ha, show c * i + (k - c * i) = k by omega_arith, hB, digits_group hs.dc hlt hj,
        show c * i + (k - c * i) = k by omega_arith] at this
      rw [coeffAt_eq, this]
  · rw [z', hI.r2]; exact count_z (k := 1) hi (by decide) (by omega_arith)

theorem unpackLoop_ok {s : State} (h0 : s.gpr .r0 = pv) (h1 : s.gpr .r1 = pp) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem (State.addr pp) k = W (inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion (State.addr pp)] m₀ s'.mem ∧ Keep unpackRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  obtain hN0 : 0 < 256 / c := Nat.div_pos (by omega_arith) h0'
  unfold unpackLoop
  refine WP.seq (WP.mono (movN_ok .r2 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (UInv W d c nb pv pp m₀ rd wr s) hN0
    (fun i hi s' hI => unpackStep hfin hs hin hout hsep fitV fitP hi hI)
    (fun s' hI => ⟨fun k hk => hI.done k (by rw [hs.cN]; exact hk), hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega_arith), k₁.mono (by decide)⟩
  · rw [k₁.gpr (by decide), h0]; simp
  · rw [k₁.gpr (by decide), h1]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2.1, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.Arm.Pack

end

end

/-! ### `MlDsa.Arm.Pack.Contracts`, which this module and modules that import it used -/

section

/-!
# ML-DSA on 32-bit ARM: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Proof/MlDsa/Contract.lean`) requires, spelled out for 32-bit ARM (`SbpPre`,
`BpPre`, `BuPre`, `T1Pre`, from `pre_of`); the branch of `sel` on a width
(`sel_ok`); and the frame of `bitPack` and `bitUnpack`, which saves `r4` in
the 4 bytes below the stack pointer that their contracts reserve
(`pushed4_mem`, `popped4`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.Arm (cmp_z)
open VG.Proof.MlDsa.Pack

/-! ## The preconditions -/

/-- `vg_mldsa_simple_bit_pack(f = r0, b = r1, out = r2, len = r3)`. -/
structure SbpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (State.addr (s.gpr .r0))]
  wr : s.wr = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩]
  disj : (polyRegion (State.addr (s.gpr .r0))).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  fitF : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  fitO : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  b : (s.gpr .r1).toNat ∈ simpleBitPackBounds
  len : (s.gpr .r3).toNat = 32 * bitlen (s.gpr .r1).toNat
  le : ∀ i < n, (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat ≤ (s.gpr .r1).toNat

theorem SbpPre.of {s : State} (h : (simpleBitPackContract Arm.abi).pre s) : SbpPre s := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The 4 bytes below the stack pointer. -/
abbrev below4 (s : State) : Region := ⟨State.addr s.sp - 4, 4⟩

/-- `vg_mldsa_bit_pack(f = r0, a = r1, b = r2, out = r3, len = [sp])`. -/
structure BpPre (s : State) : Prop where
  sp4 : 4 ≤ s.sp.toNat
  rd : s.rd = [polyRegion (State.addr (s.gpr .r0)), ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩]
  disj : (polyRegion (State.addr (s.gpr .r0))).Disjoint ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  bF : (below4 s).Disjoint (polyRegion (State.addr (s.gpr .r0)))
  bO : (below4 s).Disjoint ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  fitF : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  fitO : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  ab : ((s.gpr .r1).toNat, (s.gpr .r2).toNat) ∈ bitPackParams
  len : (stackArg s 0).toNat = 32 * bitlen ((s.gpr .r1).toNat + (s.gpr .r2).toNat)
  red : Reduced s.mem (State.addr (s.gpr .r0))
  bnd : ∀ i < n, -((s.gpr .r1).toNat : Int) ≤ modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ∧
    modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ≤ (s.gpr .r2).toNat

theorem BpPre.of {s : State} (h : (bitPackContract Arm.abi 4).pre s) : BpPre s := by
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, -, h5, h6, -, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- `vg_mldsa_bit_unpack(v = r0, len = r1, a = r2, b = r3, f = [sp])`. -/
structure BuPre (s : State) : Prop where
  sp4 : 4 ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [polyRegion (State.addr (stackArg s 0))]
  disj : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (polyRegion (State.addr (stackArg s 0)))
  bV : (below4 s).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  bP : (below4 s).Disjoint (polyRegion (State.addr (stackArg s 0)))
  fitV : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fitP : (stackArg s 0).toNat + 1024 ≤ 2 ^ 32
  ab : ((s.gpr .r2).toNat, (s.gpr .r3).toNat) ∈ bitPackParams
  len : (s.gpr .r1).toNat = 32 * bitlen ((s.gpr .r2).toNat + (s.gpr .r3).toNat)

theorem BuPre.of {s : State} (h : (bitUnpackContract Arm.abi 4).pre s) : BuPre s := by
  sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, -, h5, h6, -, h7, h8, h9, h10⟩ := h
  exact ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h10⟩

/-- `vg_mldsa_unpack_t1(v = r0, f = r1)`. -/
structure T1Pre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 320⟩]
  wr : s.wr = [polyRegion (State.addr (s.gpr .r1))]
  disj : Region.Disjoint ⟨State.addr (s.gpr .r0), 320⟩ (polyRegion (State.addr (s.gpr .r1)))
  fitV : (s.gpr .r0).toNat + 320 ≤ 2 ^ 32
  fitP : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32

theorem T1Pre.of {s : State} (h : (unpackT1Contract Arm.abi).pre s) : T1Pre s := by
  sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-! ## Branching on a width -/

/-- The same registers, memory, regions and stack pointer. -/
def Same (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem cmp_ok (r : Reg) (v : Nat) (he : encodable (BitVec.ofNat 32 v) = true) (s : State) :
    WP isa (.block [.cmp r (.imm (BitVec.ofNat 32 v))]) s fun s' =>
      s'.z = (s.gpr r - BitVec.ofNat 32 v == 0) ∧ Same s s' := by
  run_block [he, Same, and_true]

theorem sel_ok (r : Reg) (v : Nat) (hv : v < 2 ^ 32) (he : encodable (BitVec.ofNat 32 v) = true)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → (s.gpr r).toNat = v → WP isa p s' Q)
    (hn : ∀ s', Same s s' → (s.gpr r).toNat ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (cmp_ok r v he s) fun s' ⟨z, hs⟩ => ?_)
  refine WP.ite (M := isa) (decide ((s.gpr r).toNat = v)) (by
    show some s'.z = _
    rw [z, cmp_z _ _ hv]) (fun h => hp s' hs (of_decide_eq_true h)) (fun h => hn s' hs (of_decide_eq_false h))

/-! ## The frame of `r4` -/

theorem addr_sub {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 n) = State.addr sp - BitVec.ofNat 64 n := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := n) (by omega_using [h]), Nat.mod_eq_of_lt (a := n) (by omega_using [h]),
    Nat.mod_eq_of_lt (a := sp.toNat) (by omega_using [])]
  omega_using [h]

theorem pushed4_sp (s : State) : (pushed [.r4] s).sp = s.sp - 4 := rfl

theorem pushed4_mem {s : State} (hsp : 4 ≤ s.sp.toNat) :
    (pushed [.r4] s).mem = s.mem.writeW (State.addr s.sp - 4) (s.gpr .r4) := by
  show s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 4)) (s.gpr .r4) = _
  rw [addr_sub hsp]; rfl

theorem pushed4_frame {s : State} (hsp : 4 ≤ s.sp.toNat) : Frame [below4 s] s.mem (pushed [.r4] s).mem := by
  rw [pushed4_mem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []

/-- What the pop of the frame restores: `r4`, from the frame, which the body
left as the push wrote it, and the stack pointer. -/
theorem popped4 {s s₂ : State} (hsp : 4 ≤ s.sp.toNat) (h₂ : s₂.sp = s.sp - 4)
    (hr4 : s₂.mem.readW (State.addr s.sp - 4) 32 = s.gpr .r4) :
    (popped .r4 4 s₂).gpr .r4 = s.gpr .r4 ∧ (popped .r4 4 s₂).sp = s.sp := by
  refine ⟨?_, ?_⟩
  · show (s₂.setReg .r4 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r4 = _
    rw [RegUpd.gpr_setReg_self, h₂, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_sub hsp]
    exact hr4
  · rw [popped_sp, h₂]; exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat := fun j s hj hin => by
  refine WP.keep _ ?_ rfl
  unfold sbpLd
  run_block [hj, hin, and_true]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

/-- The registers `s'` has as `s` (for the ABI). -/
theorem keep_of_same {rs : List Reg} {s₀ s s' : State} (hs : Same s₀ s) (hk : Keep rs s s') : Keep rs s₀ s' :=
  ⟨fun r hr => by rw [hk.1 r hr, hs.1], hk.2.1.trans hs.2.2.1, hk.2.2.1.trans hs.2.2.2.1, hk.2.2.2.trans hs.2.2.2.2⟩

theorem sbp_wp {s₀ : State} (hp : SbpPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.simpleBitPack s₀ fun s' =>
      bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
        simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ Keep packRegs s₀ s' := by
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (s₀.gpr .r1).toNat = d → ∀ s : State, Same s₀ s →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
          simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ Keep packRegs s₀ s' := by
    intro d c nb hs hd s hS
    have hlen := hp.len
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok hs (pf := s₀.gpr .r0) (po := s₀.gpr .r2) (m₀ := s₀.mem) (rd := s₀.rd)
      (wr := s₀.wr) (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hp.disj) hp.fitF
      (by rw [← hlen]; exact hp.fitO) (fun i hi => by rw [← hd]; exact lt_bitlen (hp.le i hi))
      (by rw [hS.1]) (by rw [hS.1]) hS.2.2.1 hS.2.2.2.1 hS.2.1)
      fun s' ⟨hB, _, hk⟩ => ⟨?_, keep_of_same hS hk⟩
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.Arm.Pack.simpleBitPack
  refine sel_ok .r1 15 (by decide) (by decide) _ _ s₀ (fun s₁ h₁ e => ?_) (fun s₁ h₁ n15 => ?_)
  · exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) (by rw [e]; decide) s₁ h₁
  refine sel_ok .r1 43 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n43 => ?_)
  · rw [h₁.1] at e
    exact go (d := 6) (c := 4) (nb := 3) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩
  · rw [h₁.1] at n43
    have e : (s₀.gpr .r1).toNat = 1023 := by
      have hb := hp.b
      simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
      omega_using [n15, n43, hb]
    exact go (d := 10) (c := 4) (nb := 5) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩

/-- `simpleBitPack` writes no register the ABI preserves. -/
theorem sbp_preserves : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.MlDsa.Arm.Pack.simpleBitPack, clobbers i r = false := by
  have h : (instrs Impl.MlDsa.Arm.Pack.simpleBitPack).all
      (fun i => preserved.all fun r => !clobbers i r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp [coeffAt, Mem.readW, Mem.read]

/-- A state satisfying the precondition. -/
def sbpSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 15 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

example : ∃ pre post leak, simpleBitPackContract Arm.abi =
    simpleBitPackSig.contract Arm.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem simpleBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.simpleBitPack (simpleBitPackContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Proof.MlKem.Arm.Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · have hp := SbpPre.of hs
    obtain ⟨t, s', he, hpost, hk⟩ := sbp_wp hp
    refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (sbp_preserves r hr) he, hk.2.2.2⟩, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hpost
  · sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨sbpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
        | (simp only [simpleBitPackBounds, t1Max_eq]; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.Arm.Pack

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_bit_pack`

The value of a coefficient `x` is `b - x`, plus `q` if that is negative (`bm`,
as `bMinus` computes it), which is `b - (x mod± q)` for a reduced `x`
(`Pack/Arith.lean`). The loop is proven once for every width (`packLoop_ok`),
and the function by its five cases, in its frame, which saves `r4` in the 4
bytes below the stack pointer. Constant time: the frame leaks only addresses
computed from the stack pointer, and the taint analysis proves its body
constant time (`RelCT.frame`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

/-! ## `b - x` modulo `q` -/

/-- `b - x`, plus `q` if it is negative, as `bMinus` computes it in 32 bits:
`m = (b - x) >> 31`, then `b - x + m + (m << 23) - (m << 13)`. -/
def bm (b x : BitVec 32) : BitVec 32 :=
  b - x + ((b - x) >>> 31) + (((b - x) >>> 31) <<< 23) - (((b - x) >>> 31) <<< 13)

theorem bm_toNat {b x : BitVec 32} (hb : b.toNat ≤ 2 ^ 19) (hx : x.toNat < q) :
    (bm b x).toNat = (b.toNat + q - x.toNat) % q := by
  rw [q_eq] at hx ⊢
  unfold bm
  by_cases h : x.toNat ≤ b.toNat
  · have e : (b - x) >>> 31 = 0#32 := by bv_omega
    rw [e, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    bv_omega
  · have e : (b - x) >>> 31 = 1#32 := by bv_omega
    rw [e, Nat.mod_eq_of_lt (by omega_arith)]
    bv_omega

/-- The value `bpLd B` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (bm (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok {B : Nat} (hB : encodable (BitVec.ofNat 32 B) = true) : LdOk (bpLd B) (bpVal B) :=
  fun j s hj hin => by
    refine WP.keep _ ?_ rfl
    unfold bpLd bMinus addQNeg
    run_block [hj, hin, hB, bm, bpVal, and_true]

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ 2 ^ 19)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      vals (bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega_arith
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [bpVal, bm_toNat (by omega_arith) hx, hbq, sub_modPm hx (by rw [q_eq]; omega_arith) (hle i hi)]

/-! ## The function -/

theorem Same.trans {a b c : State} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem bpPro_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .r2), .mov .r2 (.reg .r3)]) s fun s' =>
      (s'.gpr .r12 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r3 ∧ s'.mem = s.mem) ∧ Keep [.r12, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

/-- What `bitPack` leaves. -/
def BpPost (s₀ s' : State) : Prop :=
  bytesAt s'.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat =
    bitPack ((polyAt s₀.mem (State.addr (s₀.gpr .r0))).map fun c => modPm c.val q) (s₀.gpr .r1).toNat
      (s₀.gpr .r2).toNat ∧ abiPreserved s₀ s'

theorem bp_wp {s₀ : State} (hp : BpPre s₀) : WP isa Impl.MlDsa.Arm.Pack.bitPack s₀ (BpPost s₀) := by
  have hsp := hp.sp4
  have hbF : ∀ r ∈ [below4 s₀], (polyRegion (State.addr (s₀.gpr .r0))).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.bF.symm
  have hco : ∀ i < 256, coeffAt (pushed [.r4] s₀).mem (State.addr (s₀.gpr .r0)) i =
      coeffAt s₀.mem (State.addr (s₀.gpr .r0)) i := fun i hi => coeffAt_frame (pushed4_frame hsp) hbF hi
  unfold Impl.MlDsa.Arm.Pack.bitPack
  refine WP.frame (rs := [.r4]) (r := .r4) rfl (by simpa using hsp) (by decide) ?_
  refine WP.seq (WP.mono (bpPro_ok _) fun s₁ ⟨⟨g12, g2, gm⟩, k₁⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have go : ∀ {d c nb B : Nat}, Shape d c nb → (s₀.gpr .r2).toNat = B → B ≤ 2 ^ 19 →
      encodable (BitVec.ofNat 32 B) = true → bitlen ((s₀.gpr .r1).toNat + B) = d → ∀ s : State, Same s₁ s →
      WP isa (packLoop (bpLd B) d c nb) s fun s₂ => ∀ m u,
        Frame [⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)), 4 * [Reg.r4].length⟩] s₂.mem m →
          BpPost s₀ { popped .r4 (4 * [Reg.r4].length) s₂ with mem := m, unknowns := u } := by
    intro d c nb B hs hB hB19 hBe hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega_arith
    refine WP.mono (packLoop_ok (bpLd_ok hBe) hs (pf := s₀.gpr .r0) (po := s₀.gpr .r3)
      (m₀ := (pushed [.r4] s₀).mem) (rd := s₀.rd) (wr := (pushed [.r4] s₀).wr)
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_self ..))
      (by rw [pushed_wr, hp.wr, hlen]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (by rw [← hlen]; exact hp.disj) hp.fitF (by rw [← hlen]; exact hp.fitO) (fun i hi => ?_)
      (by rw [hS.1, k₁.gpr (by decide), pushed_gpr]) (by rw [hS.1, g2, pushed_gpr])
      (by rw [hS.2.2.1, k₁.2.1, pushed_rd]) (by rw [hS.2.2.2.1, k₁.2.2.1]) (by rw [hS.2.1, gm]))
      fun s₂ ⟨hbytes, hf, hk⟩ mL uL hfl => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
    · obtain ⟨h₁, h₂⟩ := hp.bnd i hi
      rw [hB] at h₂
      have hx := hp.red i hi
      rw [hco i hi, bpVal, bm_toNat (by omega_arith) hx, hBq, ← sub_modPm hx (by rw [q_eq]; omega_arith) h₂, ← hd, ← hB]
      exact lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · have e4 : State.addr (s₀.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)) = State.addr s₀.sp - 4 := addr_sub hsp
      rw [e4] at hfl
      dsimp only
      rw [Proof.MlKem.bytesAt_frame (rs := [below4 s₀]) hfl (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.bO.symm)
        (by have := (stackArg s₀ 0).isLt; omega_arith)]
      rw [hlen, hbytes, bitPack_eq, ← hB, ← hd, hB]
      rw [bitPack_vals hp.red hB19 (fun i hi => by rw [← hB]; exact (hp.bnd i hi).2)]
      refine congrArg (fun L => bitsToBytes (fieldBits _ L)) (List.map_congr_left fun i hi => ?_)
      rw [hco i (List.mem_range.mp hi)]
    · -- The registers: `r4` from the frame, the others kept.
      have hsp₂ : s₂.sp = s₀.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₁.2.2.2, pushed4_sp]
      dsimp only
      by_cases h4 : r = .r4
      · subst h4
        refine (popped4 hsp hsp₂ ?_).1
        rw [hf.readW (r := below4 s₀) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← hlen]; exact hp.bO) (by decide),
          pushed4_mem hsp, Mem.readW_writeW_self32]
      · have hr' : r ∉ packRegs ++ [.r12, .r2] := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h4 | decide
        rw [popped_gpr h4, hk.gpr (fun h => hr' (List.mem_append_left _ h)), hS.1,
          k₁.gpr (fun h => hr' (List.mem_append_right _ h)), pushed_gpr]
    · have hsp₂ : s₂.sp = s₀.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₁.2.2.2, pushed4_sp]
      dsimp only
      rw [popped_sp, hsp₂]; exact BitVec.sub_add_cancel _ _
  have e12 : ∀ s, Same s₁ s → (s.gpr .r12).toNat = (s₀.gpr .r2).toNat := fun s h => by
    rw [h.1, g12, pushed_gpr]
  refine sel_ok .r12 2 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n2 => ?_)
  · rw [e12 s₁ ⟨rfl, rfl, rfl, rfl, rfl⟩] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 2 by omega_arith]; decide) s₂ h₂
  rw [e12 s₁ ⟨rfl, rfl, rfl, rfl, rfl⟩] at n2
  refine sel_ok .r12 4 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n4 => ?_)
  · rw [e12 s₂ h₂] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 4 by omega_arith]; decide) s₃ (h₂.trans h₃)
  rw [e12 s₂ h₂] at n4
  refine sel_ok .r12 4096 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4096 => ?_)
  · rw [e12 s₃ (h₂.trans h₃)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 4095 by omega_arith]; decide) s₄ ((h₂.trans h₃).trans h₄)
  rw [e12 s₃ (h₂.trans h₃)] at n4096
  refine sel_ok .r12 131072 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n17 => ?_)
  · rw [e12 s₄ ((h₂.trans h₃).trans h₄)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 131071 by omega_arith]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)
  · rw [e12 s₄ ((h₂.trans h₃).trans h₄)] at n17
    have e : (s₀.gpr .r2).toNat = 524288 := by omega_arith
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r1).toNat = 524287 by omega_arith]; decide) s₅ (((h₂.trans h₃).trans h₄).trans h₅)

/-! ## Constant time -/

theorem push_eq {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) : a = pushed rs s := by
  simp only [isa, push] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A frame `push {r4}; body; pop r4` is constant time if its body is, by
the taint analysis with `rs` public, from states that agree on `rs` and
the stack pointer. -/
theorem frame4_ct {body : Prog isa} (rs : List Reg) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) body hc).isSome = true) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) (hr : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa P (.frame (.push [.r4]) body (.pop .r4 4)) fun _ _ => True :=
  RelCT.frame hsp (RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b ⟨x₁, x₂, hx, pa, pb⟩ => by
      rw [push_eq pa, push_eq pb]
      exact Taint.agree_ofRegs fun r h' => by rw [pushed_gpr, pushed_gpr]; exact hr _ _ hx r h') h)

theorem bitPack_ct :
    ConstantTime isa (bitPackContract Arm.abi 4).pre (bitPackContract Arm.abi 4).pub Impl.MlDsa.Arm.Pack.bitPack := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ hpub e₁ e₂
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
  obtain ⟨hsp, h0, h1, h2, h3, -⟩ := hpub
  exact (frame4_ct [.r0, .r1, .r2, .r3] (by native_taint_decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) (fun a b h r hr => by
      rw [h.1, h.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying the precondition: `len` = 96 on the stack. -/
def bpSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 2 | .r2 => 2 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4000 then 96 else 0
  rd := [⟨0x1000, 1024⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 96⟩]

example : ∃ pre post leak, bitPackContract Arm.abi 4 =
    bitPackSig.contract Arm.target.abi pre post true 4 leak := ⟨_, _, _, rfl⟩

theorem bitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.bitPack (bitPackContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, bitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hb, habi⟩ := bp_wp (BpPre.of hs)
    refine ⟨t, s', he, habi, ?_⟩
    sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hb
  · refine ⟨bpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | (unfold Reduced; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.Arm.Pack
