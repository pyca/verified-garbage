import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Encode
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.Stream`. -/
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

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Proof.MlKem.Arm (byte_writeW8 contains_off setWidth8 setWidth32_toNat)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

/-! ## Registers kept -/

/-- `s'` has the registers of `s` but for `rs`, and its regions and stack pointer. -/
def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Pack.Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlDsa.Arm.Pack.Keep rs s₁ s₂) (h₂ : VG.Proof.MlDsa.Arm.Pack.Keep rs' s₂ s₃) :
    VG.Proof.MlDsa.Arm.Pack.Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.MlDsa.Arm.Pack.Keep rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.MlDsa.Arm.Pack.Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : VG.Proof.MlDsa.Arm.Pack.Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => match dstOf i with
    | some r => rs.contains r
    | none => true

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : VG.Proof.MlDsa.Arm.Pack.writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ VG.Proof.MlDsa.Arm.Pack.Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  refine ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi e => hr ?_) he', r, w, p⟩
  have := List.all_eq_true.mp hc i hi
  simp only [e, List.contains_iff_mem] at this
  exact this

/-! ## Instructions -/

/-- `r3 ← r3 + r12 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh ≤ 31) (s : State)
    (hs : (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32) :
    WP isa (.block [shiftAdd sh]) s fun s' =>
      ((s'.gpr .r3).toNat = (s.gpr .r3).toNat + (s.gpr .r12).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ite_true]
    run_block [and_true]
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · simp only [shiftAdd, h, ite_false]
    run_block [show 1 ≤ sh by omega, hsh, and_true]
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show (s.gpr .r12).toNat * 2 ^ sh < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 4096) (s : State)
    (hout : InRegions s.wr (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (State.addr (s.gpr .r2 + BitVec.ofNat 32 t)) (BitVec.ofNat 8 (s.gpr .r3).toNat) ∧
        (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ 8) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3] s s' := by
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
    (hw : VG.Proof.MlDsa.Arm.Pack.GOut m₀ s.mem o nb k V) (hr : (s.gpr .r3).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.GOut m₀ s'.mem o nb (k + nf) V ∧ (s'.gpr .r3).toNat = X / 2 ^ (8 * nf) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => VG.Proof.MlDsa.Arm.Pack.Keep [.r3] s s' ∧
    (s'.gpr .r3).toNat = X / 2 ^ (8 * u) ∧ VG.Proof.MlDsa.Arm.Pack.GOut m₀ s'.mem o nb (k + u) V)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h2' : s'.gpr .r2 = y := (hkp.gpr (by decide)).trans h2
  have ea : State.addr (s'.gpr .r2 + BitVec.ofNat 32 (k + u)) = o + BitVec.ofNat 64 (k + u) := by
    rw [h2']; exact ho _ (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.packByte_ok (by omega) s' (by rw [ea, hkp.2.2.1]; exact hout _ (by omega)))
    fun s'' ⟨⟨hm, h3⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_, ?_⟩
  · rw [h3, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ea]
    exact hw'.1.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))
  · intro t ht
    rw [hm, ea, byte_writeW8 _ _ (by omega) (by omega)]
    by_cases e : t = k + u
    · rw [ite_eq_left e, hr', hX u hu, e]
    · rw [ite_eq_right e]; exact hw'.2 t (by omega)

/-- `ld j` loads into `r12` the value `V` of the word at `r0 + 4j`, and
writes only `r4` and `r12`. -/
def LdOk (ld : Nat → List Instr) (V : BitVec 32 → Nat) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .r12).toNat = V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) ∧
        s'.mem = s.mem) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r4, .r12] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r3`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.Arm.Pack.LdOk ld V) {d j nb G : Nat}
    (hd : d ≤ 20) (hj : j < 8) (hnb : nb < 4096) (hjn : d * (j + 1) / 8 ≤ nb) {m₀ : Mem} {o : Addr}
    {y : BitVec 32} (s : State) (h2 : s.gpr .r2 = y)
    (ho : ∀ t < nb, State.addr (y + BitVec.ofNat 32 t) = o + BitVec.ofNat 64 t)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 4)
    (hv : V (s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j))) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hw : VG.Proof.MlDsa.Arm.Pack.GOut m₀ s.mem o nb (d * j / 8) (VG.Proof.MlDsa.Arm.Pack.bytesOf G))
    (hr : (s.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.GOut m₀ s'.mem o nb (d * (j + 1) / 8) (VG.Proof.MlDsa.Arm.Pack.bytesOf G) ∧
        (s'.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r4, .r12] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s (by omega) hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .r12).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.shiftAdd_ok (sh := d * j % 8) (by omega) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hX : (s₂.gpr .r3).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h2₂ : s₂.gpr .r2 = y := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h2]
  have hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
  have hsum : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (V := VG.Proof.MlDsa.Arm.Pack.bytesOf G) _
    (fun u hu => ?_) (by omega) hnb s₂ h2₂ ho (by rw [k₂.2.2.1, k₁.2.2.1]; exact hout)
    (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨by rwa [hsum] at hw₃, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [hr₃, pack_shift, hsum]

theorem zero_ok (s : State) :
    WP isa (.block [.mov .r3 (.imm 0)]) s fun s' => ((s'.gpr .r3).toNat = 0 ∧ s'.mem = s.mem) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

theorem packTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * c))), .dp .add .r2 .r2 (.imm (BitVec.ofNat 32 nb)),
      .subs .r1 .r1 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧ s'.mem = s.mem) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r2`. -/
theorem packBody_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.Arm.Pack.LdOk ld V) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (e₁ : encodable (BitVec.ofNat 32 (4 * c)) = true)
    (e₂ : encodable (BitVec.ofNat 32 nb) = true) (s : State)
    (hx : (s.gpr .r0).toNat + 4 * c ≤ 2 ^ 32) (hy : (s.gpr .r2).toNat + nb ≤ 2 ^ 32)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 t) 1)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), 4 * c⟩ ⟨State.addr (s.gpr .r2), nb⟩)
    (hF : ∀ j < c, V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb nb (VG.Proof.MlDsa.Arm.Pack.bytesOf (digits d ((List.range c).map fun j =>
          V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 nb ∧
        s'.gpr .r1 = s.gpr .r1 - 1 ∧ s'.z = (s.gpr .r1 - 1 == 0) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hG : digits d ((List.range c).map fun j =>
    V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d =
      V (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  have ea : ∀ j < c, State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega)
  have ho : ∀ t < nb, State.addr (s.gpr .r2 + BitVec.ofNat 32 t) = State.addr (s.gpr .r2) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega)
  have hnb : nb ≤ 20 := by have := Nat.mul_le_mul hd hc; omega
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  have y₁ : s₁.gpr .r2 = s.gpr .r2 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r4, .r12] s₁ s' ∧
      VG.Proof.MlDsa.Arm.Pack.GOut s.mem s'.mem (State.addr (s.gpr .r2)) nb (d * j / 8) (VG.Proof.MlDsa.Arm.Pack.bytesOf G) ∧
      (s'.gpr .r3).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, ⟨by rw [m₁]; exact Frame.refl _ _, fun t ht => absurd ht (by simp)⟩,
      by rw [z₁, Nat.mul_zero, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]⟩)
    fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    have yj : s'.gpr .r2 = s.gpr .r2 := (hk.gpr (by decide)).trans y₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    have hA : State.addr (s'.gpr .r0 + BitVec.ofNat 32 (4 * j)) =
        State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) := by rw [xj]; exact ea j hj
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.packCoef_ok hld (G := G) (m₀ := s.mem) hd (by omega) (by omega) hj8 s' yj ho
      (by rw [hk.2.2.1, k₁.2.2.1]; exact hout) (by rw [hA, hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin j hj)
      ?_ hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [hA, hdig j hj]
    refine congrArg V (hw.1.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_left (Offset.sub_base _ (by omega))
  · have hc8 : d * c / 8 = nb := by omega
    rw [hc8] at hw₂
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.packTail_ok e₁ e₂ s₂) fun s₃ ⟨⟨x₃, y₃, c₃, z₃, m₃⟩, k₃⟩ =>
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
        s'.mem = s.mem) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r12] s s' := by
  rw [show unpackByte d j t = ([.ldrb .r12 .r0 t] : List Instr) ++ [shiftAdd (8 * t - d * j)] from rfl,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun s' => s'.gpr .r12 =
    (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).setWidth 32 ∧ s'.mem = s.mem)
    (by run_block [ht, hin, and_true]) rfl) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hax : (s₁.gpr .r12).toNat = (s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 t))).toNat := by
    rw [ax₁, setWidth32_toNat]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.shiftAdd_ok hsh s₁ (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` (at `x`) into the accumulator, which
holds bits `d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} {x : BitVec 32} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk' : k + nl ≤ 4096) (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (k + u))) 1)
    (hb : ∀ u < nl, (s.mem (State.addr (x + BitVec.ofNat 32 (k + u)))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r12] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r12] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r3).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have x' : s'.gpr .r0 = x := (hkp.gpr (by decide)).trans h0
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← x'] at hbu
  have hbl : (s'.mem (State.addr (s'.gpr .r0 + BitVec.ofNat 32 (k + u)))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.unpackByte_ok (by omega) (by omega) s' (by rw [hkp.2.1, hkp.2.2.1, x']; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- The low `d` bits of `r3` into `r12`, and `r3` shifted right by `d`. -/
theorem extract_ok {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block (extract d)) s fun s' =>
      ((s'.gpr .r12).toNat = (s.gpr .r3).toNat % 2 ^ d ∧ (s'.gpr .r3).toNat = (s.gpr .r3).toNat / 2 ^ d ∧
        s'.mem = s.mem) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r12] s s' := by
  refine WP.keep _ ?_ rfl
  unfold extract
  run_block [show 1 ≤ 32 - d by omega, show 32 - d ≤ 31 by omega, hd1, show d ≤ 31 by omega, and_true]
  refine ⟨?_, by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]⟩
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 2 ^ 32 = 2 ^ d * 2 ^ (32 - d) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `r12` to
`r1 + 4j`, and writes only `r4` and `r12`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, 4 * j < 4096 → InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4 →
    (s.gpr .r12).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (s.gpr .r12).toNat) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r4, .r12] s s'

/-- Field `j`: the bytes it needs into `r3`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.Arm.Pack.FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (hj : j < 8) {x : BitVec 32} (s : State) (h0 : s.gpr .r0 = x)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 t)) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (State.addr (x + BitVec.ofNat 32 t))).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) 4)
    (hr : (s.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j))) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r3).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r4, .r12] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  have hn8 : need d (j + 1) ≤ 20 := by unfold need; have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) (by omega) s h0 (fun u hu => hin _ (by omega))
    (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.extract_ok hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .r12).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have p₂ : s₂.gpr .r1 = s.gpr .r1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by omega) (by rw [k₂.2.2.1, k₁.2.2.1, p₂]; exact hout)
      (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, p₂, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, r₁, unpack_shift]

theorem unpackTail_ok {c nb : Nat} (e₁ : encodable (BitVec.ofNat 32 nb) = true)
    (e₂ : encodable (BitVec.ofNat 32 (4 * c)) = true) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 nb)), .dp .add .r1 .r1 (.imm (BitVec.ofNat 32 (4 * c))),
      .subs .r2 .r2 (.imm 1)]) s fun s' =>
      (s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 nb ∧ s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem) ∧
        VG.Proof.MlDsa.Arm.Pack.Keep [.r0, .r1, .r2] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [e₁, e₂, and_true]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `r0`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.Arm.Pack.FinOk fin d W)
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
        VG.Proof.MlDsa.Arm.Pack.Keep [.r0, .r1, .r2, .r3, .r4, .r12] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t =>
    (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) = H
  have ea : ∀ t < nb, State.addr (s.gpr .r0 + BitVec.ofNat 32 t) = State.addr (s.gpr .r0) + BitVec.ofNat 64 t :=
    fun t ht => addr_add (by omega)
  have ep : ∀ j < c, State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * j)) =
      State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) := fun j hj => addr_add (by omega)
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r0 = s.gpr .r0 := k₁.gpr (by decide)
  have p₁ : s₁.gpr .r1 = s.gpr .r1 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => VG.Proof.MlDsa.Arm.Pack.Keep [.r3, .r4, .r12] s₁ s' ∧
      Frame [⟨State.addr (s.gpr .r1), 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j')) 32 =
        W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r3).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r0 = s.gpr .r0 := (hk.gpr (by decide)).trans x₁
    have pj : s'.gpr .r1 = s.gpr .r1 := (hk.gpr (by decide)).trans p₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.unpackCoef_ok hfin hd1 hd (H := H) (by omega) s' xj
      (fun t ht => by rw [ea t (by omega), hk.2.1, hk.2.2.1, k₁.2.1, k₁.2.2.1]; exact hin t (by omega))
      (fun t ht => by
        rw [ea t (by omega), hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep _ (Offset.contains_base _ (by omega) (by omega)))
      (by rw [pj, ep j hj, hk.2.2.1, k₁.2.2.1]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', pj, ep j hj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', pj, ep j hj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (VG.Proof.MlDsa.Arm.Pack.unpackTail_ok e₁ e₂ s₂)
      fun s₃ ⟨⟨x₃, p₃, c₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [p₃, k₂.gpr (by decide), p₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.Arm.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.Loop`. -/
section

/-!
# ML-DSA on 32-bit ARM: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`, and for any
state that permits the accesses: they change only the output, the registers of
`packRegs` or `unpackRegs` and the flags.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
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

theorem Shape.nb20 {d c nb : Nat} (h : VG.Proof.MlDsa.Arm.Pack.Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.nb0 {d c nb : Nat} (h : VG.Proof.MlDsa.Arm.Pack.Shape d c nb) : 0 < nb := by
  have := Nat.mul_le_mul h.d1 h.c0; have := h.dc; omega

theorem Shape.group {d c nb : Nat} (h : VG.Proof.MlDsa.Arm.Pack.Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ptr_step (p : BitVec 32) (i c : Nat) :
    p + BitVec.ofNat 32 (c * i) + BitVec.ofNat 32 c = p + BitVec.ofNat 32 (c * (i + 1)) := by
  rw [BitVec.add_assoc, Nat.mul_succ, BitVec.ofNat_add]

theorem ptr_toNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) : (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

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
      (s'.gpr r = BitVec.ofNat 32 N ∧ s'.mem = s.mem) ∧ VG.Proof.MlDsa.Arm.Pack.Keep [r] s s' := by
  refine WP.keep _ ?_ (by simp [VG.Proof.MlDsa.Arm.Pack.writesOnly, dstOf])
  run_block [hN, and_true]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {V : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.Arm.Pack.LdOk ld V) {d c nb : Nat} (hs : VG.Proof.MlDsa.Arm.Pack.Shape d c nb)
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
    ∀ a ∈ VG.Proof.MlDsa.Arm.Pack.vals V m f, a < 2 ^ d := fun a ha => by
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
    (bitsToBytes (fieldBits d (VG.Proof.MlDsa.Arm.Pack.vals V m₀ (State.addr pf))))[k]!
  keep : VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlDsa.Arm.Pack.PInv V d c nb pf po m₀ rd wr sE i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.PInv V d c nb pf po m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ex : State.addr (s.gpr .r0) = State.addr pf + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r0]; exact addr_add (by rw [Nat.mul_assoc]; omega)
  have ey : State.addr (s.gpr .r2) = State.addr po + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r2]; exact addr_add (by omega)
  have ha : ∀ j, State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pf) (c * i + j) :=
    fun j => by rw [ex, VG.Proof.MlDsa.Arm.Pack.off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, State.addr (s.gpr .r2) + BitVec.ofNat 64 t = State.addr po + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ey, VG.Proof.MlDsa.Arm.Pack.off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 =
      coeffAt m₀ (State.addr pf) (c * i + j) :=
    fun j hj => by
      rw [ha j]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.packBody_ok hld hs.d20 hs.dc hs.c8 hs.e4c hs.enb s
    (by rw [hI.r0, VG.Proof.MlDsa.Arm.Pack.ptr_toNat (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (by rw [hI.r2, VG.Proof.MlDsa.Arm.Pack.ptr_toNat (by omega)]; omega)
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact VG.Proof.MlDsa.Arm.Pack.inRegions_of hin (coeff_contains _ (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact VG.Proof.MlDsa.Arm.Pack.inRegions_of hout (Offset.contains_base _ (by omega) (by omega)))
    (by
      rw [ex, ey]
      exact (hsep.sub_left (Offset.sub_base _ (by rw [Nat.mul_assoc]; omega))).sub_right
        (Offset.sub_base _ (by omega)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega)))
    fun s' ⟨hW, x', y', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact VG.Proof.MlDsa.Arm.Pack.ptr_step _ i (4 * c)
  · rw [y', hI.r2]; exact VG.Proof.MlDsa.Arm.Pack.ptr_step _ i nb
  · rw [c', hI.r1]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · refine hI.frame.trans (hW.1.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [ey]; exact Offset.sub_base _ (by omega)⟩
  · have hE : (bitsToBytes (fieldBits d (VG.Proof.MlDsa.Arm.Pack.vals V m₀ (State.addr pf))))[k]! = _ := rfl
    by_cases hk' : k < nb * i
    · -- Written before.
      rw [← hI.done k hk']
      refine hW.1 _ fun r hr hc => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [ey] at hc
      exact Offset.disjoint (State.addr po) (d := k) (n := 1) (e := nb * i) (k := nb) (by omega) (by omega)
        (by omega) _ (Region.contains_self _ _) hc
    · -- Written by this group.
      have ht : k - nb * i < nb := by rw [Nat.mul_succ] at hk; omega
      have := hW.2 (k - nb * i) ht
      rw [hb, show nb * i + (k - nb * i) = k by omega] at this
      have e : k = nb * i + (k - nb * i) := by omega
      rw [this]
      conv => rhs; rw [e]
      rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (VG.Proof.MlDsa.Arm.Pack.vals_lt hF) ht (by omega),
        take_drop_eq _ 0 (by simp; omega)]
      refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * (k - nb * i)))) (List.map_congr_left fun j hj => ?_)
      have hj := List.mem_range.mp hj
      rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      rfl
  · rw [z', hI.r1]; exact count_z (k := 1) hi (by decide) (by omega)

theorem packLoop_ok {s : State} (h0 : s.gpr .r0 = pf) (h2 : s.gpr .r2 = po) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem (State.addr po) (32 * d) = bitsToBytes (fieldBits d (VG.Proof.MlDsa.Arm.Pack.vals V m₀ (State.addr pf))) ∧
        Frame [⟨State.addr po, 32 * d⟩] m₀ s'.mem ∧ VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.packRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega) h0'
  unfold packLoop
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.movN_ok .r1 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Pack.PInv V d c nb pf po m₀ rd wr s) hN0
    (fun i hi s' hI => VG.Proof.MlDsa.Arm.Pack.packStep hld hs hin hout hsep fitF fitO hF hi hI)
    (fun s' hI => ⟨bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk),
      hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₁.mono (by decide)⟩
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
  done : ∀ k < c * i, coeffAt s.mem (State.addr pp) k = W (VG.Proof.MlDsa.Arm.Pack.inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)
  keep : VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.unpackRegs sE s

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : VG.Proof.MlDsa.Arm.Pack.FinOk fin d W)
  (hs : VG.Proof.MlDsa.Arm.Pack.Shape d c nb) {pv pp : BitVec 32} {m₀ : Mem} {rd wr : List Region} {sE : State}
  (hin : (⟨State.addr pv, 32 * d⟩ : Region) ∈ rd ++ wr) (hout : polyRegion (State.addr pp) ∈ wr)
  (hsep : Region.Disjoint ⟨State.addr pv, 32 * d⟩ (polyRegion (State.addr pp)))
  (fitV : pv.toNat + 32 * d ≤ 2 ^ 32) (fitP : pp.toNat + 1024 ≤ 2 ^ 32)
include hfin hs hin hout hsep fitV fitP

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlDsa.Arm.Pack.UInv W d c nb pv pp m₀ rd wr sE i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      VG.Proof.MlDsa.Arm.Pack.UInv W d c nb pv pp m₀ rd wr sE (i + 1) s' ∧ s'.z = decide (i + 1 = 256 / c) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have hc8 := hs.c8
  have hc0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have ex : State.addr (s.gpr .r0) = State.addr pv + BitVec.ofNat 64 (nb * i) := by
    rw [hI.r0]; exact addr_add (by omega)
  have ep : State.addr (s.gpr .r1) = State.addr pp + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.r1]; exact addr_add (by rw [Nat.mul_assoc]; omega)
  have ha : ∀ j, State.addr (s.gpr .r1) + BitVec.ofNat 64 (4 * j) = coeffAddr (State.addr pp) (c * i + j) :=
    fun j => by rw [ep, VG.Proof.MlDsa.Arm.Pack.off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, State.addr (s.gpr .r0) + BitVec.ofNat 64 t = State.addr pv + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ex, VG.Proof.MlDsa.Arm.Pack.off_add]
  have hsub : Region.Sub ⟨State.addr (s.gpr .r1), 4 * c⟩ (polyRegion (State.addr pp)) := by
    rw [ep]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (VG.Proof.MlDsa.Arm.Pack.unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 hs.enb hs.e4c s
    (by rw [hI.r0, VG.Proof.MlDsa.Arm.Pack.ptr_toNat (by omega)]; omega)
    (by rw [hI.r1, VG.Proof.MlDsa.Arm.Pack.ptr_toNat (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact VG.Proof.MlDsa.Arm.Pack.inRegions_of hin (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact VG.Proof.MlDsa.Arm.Pack.inRegions_of hout (coeff_contains _ (by omega)))
    (by rw [ex]; exact (hsep.sub_left (Offset.sub_base _ (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, x', p', c', z', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_),
      fun k hk => ?_, (hI.keep.trans k').mono (by decide)⟩, ?_⟩
  · rw [x', hI.r0]; exact VG.Proof.MlDsa.Arm.Pack.ptr_step _ i nb
  · rw [p', hI.r1]; exact VG.Proof.MlDsa.Arm.Pack.ptr_step _ i (4 * c)
  · rw [c', hI.r2]; exact count_sub (k := 1) hi
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2.1, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  · -- The bytes of the group, on entry.
    have hB : (List.range nb).map (fun t => (s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 t)).toNat) =
        (((bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
      rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
      refine List.map_congr_left fun t ht => ?_
      have ht := List.mem_range.mp ht
      rw [VG.Proof.MlDsa.Arm.Pack.getD_map_toNat, bytesAt_getD _ _ (by omega), hb]
      refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base _ (by omega) (by omega))
    have hlt : ∀ a ∈ (bytesAt m₀ (State.addr pv) (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
    by_cases hk' : k < c * i
    · -- Written before.
      rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
      refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [ep]
      exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
    · -- Written by this group.
      have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
      have := hw (k - c * i) hj
      rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
        show c * i + (k - c * i) = k by omega] at this
      rw [coeffAt_eq, this]
  · rw [z', hI.r2]; exact count_z (k := 1) hi (by decide) (by omega)

theorem unpackLoop_ok {s : State} (h0 : s.gpr .r0 = pv) (h1 : s.gpr .r1 = pp) (hrd : s.rd = rd)
    (hwr : s.wr = wr) (hm : s.mem = m₀) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem (State.addr pp) k = W (VG.Proof.MlDsa.Arm.Pack.inNum m₀ (State.addr pv) d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion (State.addr pp)] m₀ s'.mem ∧ VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.unpackRegs s s' := by
  have h0' := hs.c0
  have hc8 := hs.c8
  have hN0 : 0 < 256 / c := Nat.div_pos (by omega) h0'
  unfold unpackLoop
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.movN_ok .r2 _ hs.eN s) fun s₁ ⟨⟨r₁, m₁⟩, k₁⟩ => ?_)
  refine wp_loop_ne (VG.Proof.MlDsa.Arm.Pack.UInv W d c nb pv pp m₀ rd wr s) hN0
    (fun i hi s' hI => VG.Proof.MlDsa.Arm.Pack.unpackStep hfin hs hin hout hsep fitV fitP hi hI)
    (fun s' hI => ⟨fun k hk => hI.done k (by rw [hs.cN]; exact hk), hI.frame, hI.keep⟩)
    ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₁.mono (by decide)⟩
  · rw [k₁.gpr (by decide), h0]; simp
  · rw [k₁.gpr (by decide), h1]; simp
  · rw [r₁]; simp
  · rw [k₁.2.1, hrd]
  · rw [k₁.2.2.1, hwr]
  · rw [m₁, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.Arm.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.Contracts`. -/
section

/-!
# ML-DSA on 32-bit ARM: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Spec/MlDsa/Poly.lean`) requires, spelled out for 32-bit ARM (`SbpPre`,
`BpPre`, `BuPre`, `T1Pre`, from `pre_of`); the branch of `sel` on a width
(`sel_ok`); and the frame of `bitPack` and `bitUnpack`, which saves `r4` in
the 4 bytes below the stack pointer that their contracts reserve
(`pushed4_mem`, `popped4`).
-/

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

theorem SbpPre.of {s : State} (h : (simpleBitPackContract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Pack.SbpPre s := by
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
  bF : (VG.Proof.MlDsa.Arm.Pack.below4 s).Disjoint (polyRegion (State.addr (s.gpr .r0)))
  bO : (VG.Proof.MlDsa.Arm.Pack.below4 s).Disjoint ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  fitF : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  fitO : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  ab : ((s.gpr .r1).toNat, (s.gpr .r2).toNat) ∈ bitPackParams
  len : (stackArg s 0).toNat = 32 * bitlen ((s.gpr .r1).toNat + (s.gpr .r2).toNat)
  red : Reduced s.mem (State.addr (s.gpr .r0))
  bnd : ∀ i < n, -((s.gpr .r1).toNat : Int) ≤ modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ∧
    modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ≤ (s.gpr .r2).toNat

theorem BpPre.of {s : State} (h : (bitPackContract Arm.abi 4).pre s) : VG.Proof.MlDsa.Arm.Pack.BpPre s := by
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, -, h5, h6, -, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- `vg_mldsa_bit_unpack(v = r0, len = r1, a = r2, b = r3, f = [sp])`. -/
structure BuPre (s : State) : Prop where
  sp4 : 4 ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [polyRegion (State.addr (stackArg s 0))]
  disj : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (polyRegion (State.addr (stackArg s 0)))
  bV : (VG.Proof.MlDsa.Arm.Pack.below4 s).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  bP : (VG.Proof.MlDsa.Arm.Pack.below4 s).Disjoint (polyRegion (State.addr (stackArg s 0)))
  fitV : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fitP : (stackArg s 0).toNat + 1024 ≤ 2 ^ 32
  ab : ((s.gpr .r2).toNat, (s.gpr .r3).toNat) ∈ bitPackParams
  len : (s.gpr .r1).toNat = 32 * bitlen ((s.gpr .r2).toNat + (s.gpr .r3).toNat)

theorem BuPre.of {s : State} (h : (bitUnpackContract Arm.abi 4).pre s) : VG.Proof.MlDsa.Arm.Pack.BuPre s := by
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

theorem T1Pre.of {s : State} (h : (unpackT1Contract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Pack.T1Pre s := by
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
      s'.z = (s.gpr r - BitVec.ofNat 32 v == 0) ∧ VG.Proof.MlDsa.Arm.Pack.Same s s' := by
  run_block [he, VG.Proof.MlDsa.Arm.Pack.Same, and_true]

theorem sel_ok (r : Reg) (v : Nat) (hv : v < 2 ^ 32) (he : encodable (BitVec.ofNat 32 v) = true)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', VG.Proof.MlDsa.Arm.Pack.Same s s' → (s.gpr r).toNat = v → WP isa p s' Q)
    (hn : ∀ s', VG.Proof.MlDsa.Arm.Pack.Same s s' → (s.gpr r).toNat ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Pack.cmp_ok r v he s) fun s' ⟨z, hs⟩ => ?_)
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
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.mod_eq_of_lt (a := sp.toNat) (by omega)]
  omega

theorem pushed4_sp (s : State) : (pushed [.r4] s).sp = s.sp - 4 := rfl

theorem pushed4_mem {s : State} (hsp : 4 ≤ s.sp.toNat) :
    (pushed [.r4] s).mem = s.mem.writeW (State.addr s.sp - 4) (s.gpr .r4) := by
  show s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 4)) (s.gpr .r4) = _
  rw [VG.Proof.MlDsa.Arm.Pack.addr_sub hsp]; rfl

theorem pushed4_frame {s : State} (hsp : 4 ≤ s.sp.toNat) : Frame [VG.Proof.MlDsa.Arm.Pack.below4 s] s.mem (pushed [.r4] s).mem := by
  rw [VG.Proof.MlDsa.Arm.Pack.pushed4_mem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- What the pop of the frame restores: `r4`, from the frame, which the body
left as the push wrote it, and the stack pointer. -/
theorem popped4 {s s₂ : State} (hsp : 4 ≤ s.sp.toNat) (h₂ : s₂.sp = s.sp - 4)
    (hr4 : s₂.mem.readW (State.addr s.sp - 4) 32 = s.gpr .r4) :
    (popped .r4 4 s₂).gpr .r4 = s.gpr .r4 ∧ (popped .r4 4 s₂).sp = s.sp := by
  refine ⟨?_, ?_⟩
  · show (s₂.setReg .r4 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r4 = _
    rw [RegUpd.gpr_setReg_self, h₂, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.Arm.Pack.addr_sub hsp]
    exact hr4
  · rw [popped_sp, h₂]; exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : VG.Proof.MlDsa.Arm.Pack.LdOk sbpLd BitVec.toNat := fun j s hj hin => by
  refine WP.keep _ ?_ rfl
  unfold sbpLd
  run_block [hj, hin, and_true]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

/-- The registers `s'` has as `s` (for the ABI). -/
theorem keep_of_same {rs : List Reg} {s₀ s s' : State} (hs : VG.Proof.MlDsa.Arm.Pack.Same s₀ s) (hk : VG.Proof.MlDsa.Arm.Pack.Keep rs s s') : VG.Proof.MlDsa.Arm.Pack.Keep rs s₀ s' :=
  ⟨fun r hr => by rw [hk.1 r hr, hs.1], hk.2.1.trans hs.2.2.1, hk.2.2.1.trans hs.2.2.2.1, hk.2.2.2.trans hs.2.2.2.2⟩

theorem sbp_wp {s₀ : State} (hp : VG.Proof.MlDsa.Arm.Pack.SbpPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.simpleBitPack s₀ fun s' =>
      bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
        simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.packRegs s₀ s' := by
  have go : ∀ {d c nb : Nat}, VG.Proof.MlDsa.Arm.Pack.Shape d c nb → bitlen (s₀.gpr .r1).toNat = d → ∀ s : State, VG.Proof.MlDsa.Arm.Pack.Same s₀ s →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
          simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ VG.Proof.MlDsa.Arm.Pack.Keep VG.Proof.MlDsa.Arm.Pack.packRegs s₀ s' := by
    intro d c nb hs hd s hS
    have hlen := hp.len
    rw [hd] at hlen
    refine WP.mono (VG.Proof.MlDsa.Arm.Pack.packLoop_ok VG.Proof.MlDsa.Arm.Pack.sbpLd_ok hs (pf := s₀.gpr .r0) (po := s₀.gpr .r2) (m₀ := s₀.mem) (rd := s₀.rd)
      (wr := s₀.wr) (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hp.disj) hp.fitF
      (by rw [← hlen]; exact hp.fitO) (fun i hi => by rw [← hd]; exact VG.Proof.MlDsa.Arm.Pack.lt_bitlen (hp.le i hi))
      (by rw [hS.1]) (by rw [hS.1]) hS.2.2.1 hS.2.2.2.1 hS.2.1)
      fun s' ⟨hB, _, hk⟩ => ⟨?_, VG.Proof.MlDsa.Arm.Pack.keep_of_same hS hk⟩
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.Arm.Pack.simpleBitPack
  refine VG.Proof.MlDsa.Arm.Pack.sel_ok .r1 15 (by decide) (by decide) _ _ s₀ (fun s₁ h₁ e => ?_) (fun s₁ h₁ n15 => ?_)
  · exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) (by rw [e]; decide) s₁ h₁
  refine VG.Proof.MlDsa.Arm.Pack.sel_ok .r1 43 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n43 => ?_)
  · rw [h₁.1] at e
    exact go (d := 6) (c := 4) (nb := 3) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩
  · rw [h₁.1] at n43
    have e : (s₀.gpr .r1).toNat = 1023 := by
      have hb := hp.b
      simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    exact go (d := 10) (c := 4) (nb := 5) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩

/-- `simpleBitPack` writes no register the ABI preserves. -/
theorem sbp_preserves : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.MlDsa.Arm.Pack.simpleBitPack, dstOf i ≠ some r := by
  have h : (instrs Impl.MlDsa.Arm.Pack.simpleBitPack).all
      (fun i => preserved.all fun r => dstOf i != some r) = true := by
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
    simpleBitPackApi.sig.contract Arm.target.abi pre post simpleBitPackApi.writeArgs 0 leak := ⟨_, _, _, rfl⟩

theorem simpleBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.simpleBitPack (simpleBitPackContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Proof.MlKem.Arm.Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := SbpPre.of hs
    obtain ⟨t, s', he, hpost, hk⟩ := VG.Proof.MlDsa.Arm.Pack.sbp_wp hp
    refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (VG.Proof.MlDsa.Arm.Pack.sbp_preserves r hr) he, hk.2.2.2⟩, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hpost
  · sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlDsa.Arm.Pack.sbpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | exact fun i _ => by rw [VG.Proof.MlDsa.Arm.Pack.coeffAt_zero]; exact Nat.zero_le _
        | (simp only [simpleBitPackBounds, t1Max_eq]; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.Arm.Pack

end
