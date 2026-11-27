module

import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
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
meta import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
public import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.Pack.Bits
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.Contract
public import VerifiedGarbage.Proof.MlKem.Bits
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes
meta import VerifiedGarbage.Proof.MlKem.Bits
meta import VerifiedGarbage.Impl.MlDsa.PPC64LE.Pack.Stream
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Bytes

/-! ### `MlDsa.PPC64LE.Pack.Stream`, which this module and modules that import it used -/

section

/-!
# ML-DSA on PPC64LE: streaming fields through `r8`

The group bodies of `Impl/MlDsa/PPC64LE/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`), as on
32-bit ARM (`Proof/MlDsa/Arm/Pack/Stream.lean`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator `r8` is a slice of the number throughout
(`Proof/MlDsa/Pack/Stream.lean`), of at most `d + 7 ≤ 27` bits. `ld` and
`fin` may read registers the loops keep (`r4` and `r7`, say), so they are
proven for the states satisfying a predicate `R` of their choice.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Pack

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.Pack
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlKem.PPC64LE (byte_writeW8 setWidth_zero_append)
open VG.Proof.MlDsa.Pack

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha]
  simp only [Mem.read]
  rw [setWidth_zero_append]

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_lis {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d ((imm ++ (0 : BitVec 16)).signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lis d imm :: is)) s Q :=
  WP.cons exec_lis (k _ (Upd.write _ _ _))

theorem wp_ori {d n : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (s.gpr n ||| imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ori d n imm :: is)) s Q :=
  WP.cons exec_ori (k _ (Upd.write _ _ _))

end

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
    (hs : (s.gpr .r8).toNat + (s.gpr .r9).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .r8).toNat = (s.gpr .r8).toNat + (s.gpr .r9).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.r8, .r9] s s' := by
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ↓reduceIte]
    refine WP.keep _ ?_ rfl rfl
    refine wp_add fun s₁ u₁ => wp_nil ⟨?_, u₁.mem⟩
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    rw [u₁.gpr, BitVec.toNat_add, Nat.mod_eq_of_lt hs]
  · simp only [shiftAdd, h, ↓reduceIte]
    refine WP.keep _ ?_ rfl rfl
    refine wp_lsl hsh fun s₁ u₁ => wp_add fun s₂ u₂ => wp_nil ⟨?_, by rw [u₂.mem, u₁.mem]⟩
    have h9 : (s.gpr .r9).toNat * 2 ^ sh < 2 ^ 64 := by omega_arith
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt h9, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 2 ^ 15) (s : State)
    (hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 t) (BitVec.ofNat 8 (s.gpr .r8).toNat) ∧
        (s'.gpr .r8).toNat = (s.gpr .r8).toNat / 2 ^ 8) ∧ Keep [.r8] s s' := by
  refine WP.keep _ ?_ rfl rfl
  unfold packByte
  refine wp_stb (by decide) ht rfl hout fun s₁ m₁ => wp_lsr (by decide) fun s₂ u₂ => wp_nil ⟨?_, ?_⟩
  · rw [u₂.mem, m₁.mem, setWidth8_ofNat]
  · rw [u₂.gpr, m₁.gpr, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The first `n` bytes of the group of `nb` bytes at `o` are `V 0, …, V (n - 1)`,
and memory is `m₀`'s outside the group. -/
def GOut (m₀ m : Mem) (o : Addr) (nb n : Nat) (V : Nat → Byte) : Prop :=
  Frame [⟨o, nb⟩] m₀ m ∧ ∀ t < n, m (o + BitVec.ofNat 64 t) = V t

/-- The bytes `k, …, k + nf - 1` of the group from the accumulator `X`,
whose byte `u` is byte `k + u` of the group. -/
theorem flush_ok {k nf nb : Nat} {m₀ : Mem} {o : Addr} {V : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V (k + u)) (hk : k + nf ≤ nb) (hnb : nb < 2 ^ 15)
    (s : State) (h11 : s.gpr .r11 = o) (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hw : GOut m₀ s.mem o nb k V) (hr : (s.gpr .r8).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      GOut m₀ s'.mem o nb (k + nf) V ∧ (s'.gpr .r8).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r8] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r8] s s' ∧
    (s'.gpr .r8).toNat = X / 2 ^ (8 * u) ∧ GOut m₀ s'.mem o nb (k + u) V)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h11' : s'.gpr .r11 = o := (hkp.gpr (by decide)).trans h11
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

/-- `ld j` loads into `r9` the value `V` of the word at `r10 + 4j`, from a
state satisfying `R`, and writes only `r0` and `r9`. -/
def LdOk (ld : Nat → List Instr) (V : BitVec 32 → Nat) (R : State → Prop) : Prop :=
  ∀ j s, R s → 4 * j < 2 ^ 15 → InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .r9).toNat = V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.r0, .r9] s s'

/-- The registers the loops write. -/
abbrev loopRegs : List Reg := [.r0, .r8, .r9, .r10, .r11, .r12]

/-- `R` holds of every state with the registers but `loopRegs` of one it
holds of. -/
def Stable (R : State → Prop) : Prop := ∀ s s', R s → Keep loopRegs s s' → R s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r8`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} {R : State → Prop} (hld : LdOk ld V R)
    {d j nb G : Nat} (hd : d ≤ 20) (hj : j < 8) (hnb : nb < 2 ^ 15) (hjn : d * (j + 1) / 8 ≤ nb) {m₀ : Mem}
    {o : Addr} (s : State) (hR : R s) (h11 : s.gpr .r11 = o)
    (hout : ∀ t < nb, InRegions s.wr (o + BitVec.ofNat 64 t) 1)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hw : GOut m₀ s.mem o nb (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r8).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      GOut m₀ s'.mem o nb (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r8).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.r0, .r8, .r9] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hR (by omega_arith) hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .r9).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r8).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by
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
  have hX : (s₂.gpr .r8).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h11₂ : s₂.gpr .r11 = o := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h11]
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
    WP isa (.block [.li .r8 0]) s fun s' => ((s'.gpr .r8).toNat = 0 ∧ s'.mem = s.mem) ∧ Keep [.r8] s s' := by
  refine WP.keep _ ?_ rfl
  exact wp_li (by decide) fun s₁ u₁ => wp_nil ⟨by rw [u₁.gpr]; rfl, u₁.mem⟩

theorem tail_ok {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) (s : State) :
    WP isa (.block [.addi .r10 .r10 a, .addi .r11 .r11 b, .subi .r12 .r12 1]) s fun s' =>
      (s'.gpr .r10 = s.gpr .r10 + BitVec.ofNat 64 a ∧ s'.gpr .r11 = s.gpr .r11 + BitVec.ofNat 64 b ∧
        s'.gpr .r12 = s.gpr .r12 - BitVec.ofNat 64 1 ∧ s'.mem = s.mem) ∧
        Keep [.r10, .r11, .r12] s s' := by
  refine WP.keep _ ?_ rfl rfl
  refine wp_addi (by decide) ha fun s₁ u₁ => wp_addi (by decide) hb fun s₂ u₂ =>
    wp_subi (by decide) (by decide) fun s₃ u₃ => wp_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₃.mem, u₂.mem, u₁.mem]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r11`. -/
theorem packBody_ok {ld : Nat → List Instr} {V : BitVec 32 → Nat} {R : State → Prop} (hld : LdOk ld V R)
    (hRs : Stable R) {d c nb : Nat} (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State) (hR : R s)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 t) 1)
    (hsep : Region.Disjoint ⟨s.gpr .r10, 4 * c⟩ ⟨s.gpr .r11, nb⟩)
    (hF : ∀ j < c, V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      GOut s.mem s'.mem (s.gpr .r11) nb nb (bytesOf (digits d ((List.range c).map fun j =>
          V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .r10 = s.gpr .r10 + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r11 = s.gpr .r11 + BitVec.ofNat 64 nb ∧
        s'.gpr .r12 = s.gpr .r12 - BitVec.ofNat 64 1 ∧ Keep loopRegs s s' := by
  generalize hG : digits d ((List.range c).map fun j =>
    V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = V (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  have hnb : nb ≤ 20 := by have := Nat.mul_le_mul hd hc; omega_arith
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr (by decide)
  have y₁ : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r0, .r8, .r9] s₁ s' ∧
      GOut s.mem s'.mem (s.gpr .r11) nb (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r8).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, ⟨by rw [m₁]; exact Frame.refl _ _, fun t ht => absurd ht (by simp)⟩,
      by rw [z₁, Nat.mul_zero, Nat.zero_div, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]⟩)
    fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r10 = s.gpr .r10 := (hk.gpr (by decide)).trans x₁
    have yj : s'.gpr .r11 = s.gpr .r11 := (hk.gpr (by decide)).trans y₁
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

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j < 64) (ht : t < 2 ^ 15) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .r8).toNat + (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .r8).toNat =
          (s.gpr .r8).toNat + (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.r8, .r9] s s' := by
  unfold unpackByte
  refine wp_lbz (by decide) ht rfl hin fun s₁ u₁ => ?_
  have hax : (s₁.gpr .r9).toNat = (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat := by
    rw [u₁.gpr, setWidth64_toNat]
  refine WP.mono (shiftAdd_ok hsh s₁ (by rw [hax, u₁.other _ (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, u₁.other _ (by decide)], by rw [m₂, u₁.mem]⟩,
      ((upd_keep u₁).trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` (at `x`) into the accumulator, which
holds bits `d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} {x : Addr} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk' : k + nl ≤ 2 ^ 15) (s : State) (h10 : s.gpr .r10 = x)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (x + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r8).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r8).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.r8, .r9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r8, .r9] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r8).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have x' : s'.gpr .r10 = x := (hkp.gpr (by decide)).trans h10
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← x'] at hbu
  have hbl : (s'.mem (s'.gpr .r10 + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
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

/-- The low `d` bits of `r8` into `r9`, and `r8` shifted right by `d`. -/
theorem extract_ok {d : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block (extract d)) s fun s' =>
      ((s'.gpr .r9).toNat = (s.gpr .r8).toNat % 2 ^ d ∧ (s'.gpr .r8).toNat = (s.gpr .r8).toNat / 2 ^ d ∧
        s'.mem = s.mem) ∧ Keep [.r8, .r9] s s' := by
  refine WP.keep _ ?_ rfl rfl
  unfold extract
  refine wp_lsl (by omega_arith) fun s₁ u₁ => wp_lsr (by omega_arith) fun s₂ u₂ => wp_lsr (by omega_arith) fun s₃ u₃ =>
    wp_nil ⟨?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      show 2 ^ 64 = 2 ^ d * 2 ^ (64 - d) by rw [← Nat.pow_add]; congr 1; omega_arith, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `r9` to
`r11 + 4j`, from a state satisfying `R`, and writes only `r0` and `r9`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) (R : State → Prop) : Prop :=
  ∀ j s, R s → 4 * j < 2 ^ 15 → InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) 4 →
    (s.gpr .r9).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) (W (s.gpr .r9).toNat) ∧
        Keep [.r0, .r9] s s'

/-- Field `j`: the bytes it needs into `r8`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {R : State → Prop}
    (hfin : FinOk fin d W R) (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (hj : j < 8) {x : Addr} (s : State)
    (hRs : ∀ s', Keep [.r8, .r9] s s' → R s') (h10 : s.gpr .r10 = x)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (x + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) 4)
    (hr : (s.gpr .r8).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r8).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.r0, .r8, .r9] s s' := by
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
  have hv : (s₂.gpr .r9).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega_arith)]
  have p₂ : s₂.gpr .r11 = s.gpr .r11 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (hRs s₂ ((k₁.trans k₂).mono (by decide))) (by omega_arith)
      (by rw [k₂.2.2, k₁.2.2, p₂]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, p₂, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `r10`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {R : State → Prop}
    (hfin : FinOk fin d W R) (hRs : Stable R) {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb)
    (hc : c ≤ 8) (s : State) (hR : R s)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨s.gpr .r10, nb⟩ ⟨s.gpr .r11, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨s.gpr .r11, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .r10 = s.gpr .r10 + BitVec.ofNat 64 nb ∧ s'.gpr .r11 = s.gpr .r11 + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .r12 = s.gpr .r12 - BitVec.ofNat 64 1 ∧ Keep loopRegs s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (s.gpr .r10 + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega_arith
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have x₁ : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr (by decide)
  have p₁ : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.r0, .r8, .r9] s₁ s' ∧
      Frame [⟨s.gpr .r11, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .r11 + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r8).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have xj : s'.gpr .r10 = s.gpr .r10 := (hk.gpr (by decide)).trans x₁
    have pj : s'.gpr .r11 = s.gpr .r11 := (hk.gpr (by decide)).trans p₁
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

end VG.Proof.MlDsa.PPC64LE.Pack

end

end

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
