module

public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Impl.MlDsa.RISCV64.Pack.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.RISCV64.Bytes

/-!
# ML-DSA on RISC-V: streaming fields through `a5`

The group bodies of `Impl/MlDsa/RISCV64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`), as on
PPC64LE (`Proof/MlDsa/PPC64LE/Pack/Stream.lean`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator `a5` is a slice of the number throughout
(`Proof/MlDsa/Pack/Stream.lean`), of at most `d + 7 ≤ 27` bits. `ld` and
`fin` may read registers the loops keep (`a1` and `a4`, say), so they are
proven for the states satisfying a predicate `R` of their choice.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.RISCV64.Steps (Upd Mupd)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlKem.RISCV64 (byte_writeW8 setWidth_zero_append)
open VG.Proof.MlDsa.Pack

theorem upd_keep {s s' : State} {d : Reg} {v : BitVec 64} (h : Upd s s' d v) : Keep [d] s s' :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ List.mem_singleton_self _), h.rd, h.wr⟩

/-- A byte of a doubleword, as `stb` stores it. -/
theorem setWidth8_ofNat (v : BitVec 64) : v.setWidth 8 = BitVec.ofNat 8 v.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte zero-extended, as `lbz` loads it. -/
theorem setWidth64_toNat (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)

/-- `r8 ← r8 + r9 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State)
    (hs : (s.gpr .a5).toNat + (s.gpr .a6).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .a5).toNat = (s.gpr .a5).toNat + (s.gpr .a6).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.a5, .a6] s s' := by
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ↓reduceIte]
    refine WP.keep _ ?_ rfl rfl
    refine Steps.wp_add fun s₁ u₁ => WP.block_nil ⟨?_, u₁.mem⟩
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt hs]
  · simp only [shiftAdd, h, ↓reduceIte]
    refine WP.keep _ ?_ rfl rfl
    refine Steps.wp_sll hsh fun s₁ u₁ => Steps.wp_add fun s₂ u₂ => WP.block_nil ⟨?_, by rw [u₂.mem, u₁.mem]⟩
    have h9 : (s.gpr .a6).toNat * 2 ^ sh < 2 ^ 64 := by omega_arith
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt h9, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 2048) (s : State)
    (hout : InRegions s.wr (s.gpr .t1 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .t1 + BitVec.ofNat 64 t) (BitVec.ofNat 8 (s.gpr .a5).toNat) ∧
        (s'.gpr .a5).toNat = (s.gpr .a5).toNat / 2 ^ 8) ∧ Keep [.a5] s s' := by
  refine WP.keep _ ?_ rfl rfl
  unfold packByte
  refine Steps.wp_sb ht rfl hout fun s₁ m₁ => Steps.wp_srl (by decide) fun s₂ u₂ => WP.block_nil ⟨?_, ?_⟩
  · rw [u₂.mem, m₁.mem, setWidth8_ofNat]
  · rw [u₂.gpr, m₁.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The first `n` bytes of the group of `nb` bytes at `o` are `V 0, …, V (n - 1)`,
and memory is `m₀`'s outside the group. -/
def GOut (m₀ m : Mem) (o : Addr) (nb n : Nat) (V : Nat → Byte) : Prop :=
  Frame [⟨o, nb⟩] m₀ m ∧ ∀ t < n, m (o + BitVec.ofNat 64 t) = V t

/-- The bytes `k, …, k + nf - 1` of the group from the accumulator `X`,
whose byte `u` is byte `k + u` of the group. -/
theorem flush_ok {k nf nb : Nat} {m₀ : Mem} {o : Addr} {V : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V (k + u)) (hk : k + nf ≤ nb) (hnb : nb < 2048)
    (s : State) (h11 : s.gpr .t1 = o) (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hw : GOut m₀ s.mem o nb k V) (hr : (s.gpr .a5).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      GOut m₀ s'.mem o nb (k + nf) V ∧ (s'.gpr .a5).toNat = X / 2 ^ (8 * nf) ∧ Keep [.a5] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.a5] s s' ∧
    (s'.gpr .a5).toNat = X / 2 ^ (8 * u) ∧ GOut m₀ s'.mem o nb (k + u) V)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h11' : s'.gpr .t1 = o := (hkp.gpr (by decide)).trans h11
  refine WP.mono (packByte_ok (by omega_arith) s' (by rw [h11', hkp.2.2]; exact hout _ (by omega_arith)))
    fun s'' ⟨⟨hm, h3⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_, ?_⟩
  · rw [h3, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h11']
    exact hw'.1.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · intro t ht
    rw [hm, h11', byte_writeW8 _ _ (by omega_arith) (by omega_arith)]
    by_cases e : t = k + u
    · rw [ite_eq_left e, hr', hX u hu, e]
    · rw [ite_eq_right e]; exact hw'.2 t (by omega_arith)

/-- `ld j` loads into `a6` the value `V` of the word at `r10 + 4j`, from a
state satisfying `R`, and writes only `t0` and `a6`. -/
def LdOk (ld : Nat → List Instr) (V : BitVec 32 → Nat) (R : State → Prop) : Prop :=
  ∀ j s, R s → 4 * j < 2048 → InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .a6).toNat = V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.t0, .a6] s s'

/-- The registers the loops write. -/
abbrev loopRegs : List Reg := [.t0, .a5, .a6, .a7, .t1, .t2]

/-- `R` holds of every state with the registers but `loopRegs` of one it
holds of. -/
def Stable (R : State → Prop) : Prop := ∀ s s', R s → Keep loopRegs s s' → R s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `a5`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} {R : State → Prop} (hld : LdOk ld V R)
    {d j nb G : Nat} (hd : d ≤ 20) (hj : j < 8) (hnb : nb < 2048) (hjn : d * (j + 1) / 8 ≤ nb) {m₀ : Mem}
    {o : Addr} (s : State) (hR : R s) (h11 : s.gpr .t1 = o)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hw : GOut m₀ s.mem o nb (d * j / 8) (bytesOf G))
    (hr : (s.gpr .a5).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      GOut m₀ s'.mem o nb (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .a5).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.t0, .a5, .a6] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hR (by omega_arith) hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .a6).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .a5).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by
    rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega_arith) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega_arith))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hX : (s₂.gpr .a5).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h11₂ : s₂.gpr .t1 = o := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h11]
  have hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
  have hsum : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega_arith
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (V := bytesOf G) _
    (fun u hu => ?_) (by omega_arith) hnb s₂ h11₂ (by rw [k₂.2.2, k₁.2.2]; exact hout)
    (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨by rwa [hsum] at hw₃, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega_arith
      omega_arith)]
  · rw [hr₃, pack_shift, hsum]

theorem zero_ok (s : State) :
    WP isa (.block [.li .a5 0]) s fun s' => ((s'.gpr .a5).toNat = 0 ∧ s'.mem = s.mem) ∧ Keep [.a5] s s' := by
  refine WP.keep _ ?_ rfl
  exact Steps.wp_li (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr]; rfl, u₁.mem⟩

theorem tail_ok {a b : Nat} (ha : a < 2048) (hb : b < 2048) (s : State) :
    WP isa (.block [.addi .a7 .a7 a, .addi .t1 .t1 b, .addi .t2 .t2 (-1)]) s fun s' =>
      (s'.gpr .a7 = s.gpr .a7 + BitVec.ofNat 64 a ∧ s'.gpr .t1 = s.gpr .t1 + BitVec.ofNat 64 b ∧
        s'.gpr .t2 = s.gpr .t2 - BitVec.ofNat 64 1 ∧ s'.mem = s.mem) ∧
        Keep [.a7, .t1, .t2] s s' := by
  refine WP.keep _ ?_ rfl rfl
  refine Steps.wp_addi ha fun s₁ u₁ => Steps.wp_addi hb fun s₂ u₂ =>
    Steps.wp_subi (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `t1`. -/
theorem packBody_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} {R : State → Prop} (hld : LdOk ld V R)
    (hRs : Stable R) {d c nb : Nat} (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State) (hR : R s)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .t1 + BitVec.ofNat 64 t) 1)
    (hsep : Region.Disjoint ⟨s.gpr .a7, 4 * c⟩ ⟨s.gpr .t1, nb⟩)
    (hF : ∀ j < c, V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      GOut s.mem s'.mem (s.gpr .t1) nb nb (bytesOf (digits d ((List.range c).map fun j =>
          V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .a7 = s.gpr .a7 + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .t1 = s.gpr .t1 + BitVec.ofNat 64 nb ∧
        s'.gpr .t2 = s.gpr .t2 - BitVec.ofNat 64 1 ∧ Keep loopRegs s s' := by
  generalize hG : digits d ((List.range c).map fun j =>
    V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = V (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  have hnb : nb ≤ 20 := by have := Nat.mul_le_mul hd hc; omega_arith
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .a7 = s.gpr .a7 := k₁.gpr (by decide)
  have y₁ : s₁.gpr .t1 = s.gpr .t1 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.t0, .a5, .a6] s₁ s' ∧
      GOut s.mem s'.mem (s.gpr .t1) nb (d * j / 8) (bytesOf G) ∧
      (s'.gpr .a5).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, ⟨by rw [m₁]; exact Frame.refl _ _, fun t ht => absurd ht (by simp)⟩,
      by rw [z₁, Nat.mul_zero, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]⟩)
    fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .a7 = s.gpr .a7 := (hk.gpr (by decide)).trans x₁
    have yj : s'.gpr .t1 = s.gpr .t1 := (hk.gpr (by decide)).trans y₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); omega_arith
    have hRj : R s' := hRs s s' hR ((k₁.trans hk).mono (by decide))
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd (by omega_arith) (by omega_arith) hj8 s' hRj yj
      (by rw [hk.2.2, k₁.2.2]; exact hout) (by rw [xj, hk.2.1, hk.2.2, k₁.2.1, k₁.2.2]; exact hin j hj)
      ?_ hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [xj, hdig j hj]
    refine congrArg V (hw.1.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide))
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep.sub_left (Offset.sub_base _ (by omega_arith))
  · have hc8 : d * c / 8 = nb := by omega_arith
    rw [hc8] at hw₂
    refine WP.mono (tail_ok (by omega_arith) (by omega_arith) s₂) fun s₃ ⟨⟨x₃, y₃, c₃, m₃⟩, k₃⟩ =>
      ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [y₃, k₂.gpr (by decide), y₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]

/-! ## Unpacking -/

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j < 64) (ht : t < 2048) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .a5).toNat + (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .a5).toNat =
          (s.gpr .a5).toNat + (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.a5, .a6] s s' := by
  unfold unpackByte
  refine Steps.wp_lbu ht rfl hin fun s₁ u₁ => ?_
  have hax : (s₁.gpr .a6).toNat = (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat := by
    rw [u₁.gpr, setWidth64_toNat]
  refine WP.mono (shiftAdd_ok hsh s₁ (by rw [hax, u₁.other _ (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, u₁.other _ (by decide)], by rw [m₂, u₁.mem]⟩,
      ((upd_keep u₁).trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` (at `x`) into the accumulator, which
holds bits `d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} {x : Addr} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk' : k + nl ≤ 2048) (s : State) (h10 : s.gpr .a7 = x)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (x + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .a5).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .a5).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.a5, .a6] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.a5, .a6] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .a5).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have x' : s'.gpr .a7 = x := (hkp.gpr (by decide)).trans h10
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← x'] at hbu
  have hbl : (s'.mem (s'.gpr .a7 + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega_arith
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (unpackByte_ok (by omega_arith) (by omega_arith) s' (by rw [hkp.2.1, hkp.2.2, x']; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega_arith
      omega_arith))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega_arith), Nat.add_assoc]

/-- The low `d` bits of `a5` into `a6`, and `a5` shifted right by `d`. -/
theorem extract_ok {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block (extract d)) s fun s' =>
      ((s'.gpr .a6).toNat = (s.gpr .a5).toNat % 2 ^ d ∧ (s'.gpr .a5).toNat = (s.gpr .a5).toNat / 2 ^ d ∧
        s'.mem = s.mem) ∧ Keep [.a5, .a6] s s' := by
  refine WP.keep _ ?_ rfl rfl
  unfold extract
  refine Steps.wp_sll (by omega_arith) fun s₁ u₁ => Steps.wp_srl (by omega_arith) fun s₂ u₂ => Steps.wp_srl (by omega_arith) fun s₃ u₃ =>
    WP.block_nil ⟨?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      show 2 ^ 64 = 2 ^ d * 2 ^ (64 - d) by rw [← Nat.pow_add]; congr 1; omega_arith, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `a6` to
`r11 + 4j`, from a state satisfying `R`, and writes only `t0` and `a6`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) (R : State → Prop) : Prop :=
  ∀ j s, R s → 4 * j < 2048 → InRegions s.wr (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) 4 →
    (s.gpr .a6).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) (W (s.gpr .a6).toNat) ∧
        Keep [.t0, .a6] s s'

/-- Field `j`: the bytes it needs into `a5`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {R : State → Prop}
    (hfin : FinOk fin d W R) (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (hj : j < 8) {x : Addr} (s : State)
    (hRs : ∀ s', Keep [.a5, .a6] s s' → R s') (h10 : s.gpr .a7 = x)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (x + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) 4)
    (hr : (s.gpr .a5).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .a5).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.t0, .a5, .a6] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega_arith)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega_arith
  have hn8 : need d (j + 1) ≤ 20 := by
    unfold need; have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega_arith); omega_arith
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega_arith) (by rw [hn']; unfold need; omega_arith) (by omega_arith) s h10 (fun u hu => hin _ (by omega_arith))
    (fun u hu => hb _ (by omega_arith)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (extract_ok hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .a6).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega_arith)]
  have p₂ : s₂.gpr .t1 = s.gpr .t1 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (hRs s₂ ((k₁.trans k₂).mono (by decide))) (by omega_arith)
      (by rw [k₂.2.2, k₁.2.2, p₂]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, p₂, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `a7`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {R : State → Prop}
    (hfin : FinOk fin d W R) (hRs : Stable R) {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb)
    (hc : c ≤ 8) (s : State) (hR : R s)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .a7, nb⟩ ⟨s.gpr .t1, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .t1 + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨s.gpr .t1, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .a7 = s.gpr .a7 + BitVec.ofNat 64 nb ∧ s'.gpr .t1 = s.gpr .t1 + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .t2 = s.gpr .t2 - BitVec.ofNat 64 1 ∧ Keep loopRegs s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (s.gpr .a7 + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega_arith
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .a7 = s.gpr .a7 := k₁.gpr (by decide)
  have p₁ : s₁.gpr .t1 = s.gpr .t1 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.t0, .a5, .a6] s₁ s' ∧
      Frame [⟨s.gpr .t1, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .t1 + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .a5).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .a7 = s.gpr .a7 := (hk.gpr (by decide)).trans x₁
    have pj : s'.gpr .t1 = s.gpr .t1 := (hk.gpr (by decide)).trans p₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    have hk₁ : Keep loopRegs s s' := (k₁.trans hk).mono (by decide)
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) (by omega_arith) s'
      (fun s'' h'' => hRs s s'' hR ((hk₁.trans h'').mono (by decide))) xj
      (fun t ht => by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2]; exact hin t (by omega_arith))
      (fun t ht => by
        rw [hbyte t (by omega_arith)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep _ (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      (by rw [pj, hk.2.2, k₁.2.2]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', pj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [m'', pj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hw j' (by omega_arith)]
  · refine WP.mono (tail_ok (by omega_arith) (by omega_arith) s₂)
      fun s₃ ⟨⟨x₃, p₃, c₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [x₃, k₂.gpr (by decide), x₁]
    · rw [p₃, k₂.gpr (by decide), p₁]
    · rw [c₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.RISCV64.Pack
