import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Hint
import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.Framework.RelCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Stream`. -/
section

/-!
# ML-DSA on AArch64: streaming fields through `x9`

The group bodies of `Impl/MlDsa/AArch64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients, which the
  caller says are bytes `gb, …, gb + nb - 1` of the output (`BytesUpTo`);
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's, which the caller says is
  coefficient `gc + j` of the output (`CoeffsUpTo`).

The accumulator is a slice of the number throughout (`Pack/Stream.lean`).
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_lsl wp_lsr wp_and wp_strb wp_ldrb wp_nil wp_movz wp_addImm
  wp_subImm toNat_add_n toNat_lsl_n toNat_lsr toNat_and_mask toNat_byte toNat_imm setWidth8_of_toNat BytesUpTo
  BytesUpTo.write ptr_add ptr_zero)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

/-- `x9 ← x9 + x10 · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State)
    (hs : (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      (s'.gpr .x9).toNat = (s.gpr .x9).toNat + (s.gpr .x10).toNat * 2 ^ sh ∧ Only [.x9, .x10] s s' := by
  by_cases h : sh = 0
  · subst h
    simp only [shiftAdd, ↓reduceIte, List.nil_append]
    refine VG.Proof.MlKem.AArch64.wp_add fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ⟨?_, h₁.mono⟩
    rw [Nat.pow_zero, Nat.mul_one] at hs ⊢
    rw [e₁, toNat_add_n hs]
  · simp only [shiftAdd, h, ↓reduceIte, List.singleton_append]
    have hx : (s.gpr .x10).toNat * 2 ^ sh < 2 ^ 64 := by omega
    refine wp_lsl hsh fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_add fun s₂ h₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ⟨?_, (h₁.trans h₂).mono⟩
    have v₁ : (s₁.gpr .x10).toNat = (s.gpr .x10).toNat * 2 ^ sh := by rw [e₁, toNat_lsl_n hx]
    rw [e₂, h₁.get .x9, toNat_add_n (by rw [v₁]; omega), v₁]

/-! ## Packing -/

theorem packByte_ok {t : Nat} (ht : t < 4096) (s : State)
    (hout : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 t) ((s.gpr .x9).setWidth 8) ∧
        s'.gpr .x9 = s.gpr .x9 >>> 8 ∧ Keep [.x9] s s' :=
  VG.Proof.MlKem.AArch64.wp_strb ht rfl hout fun s₁ h₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₂ h₂ e₂ =>
    VG.Proof.MlKem.AArch64.wp_nil ⟨by rw [h₂.mem, h₁.mem], by rw [e₂, h₁.gpr], (h₁.keep.trans h₂.keep).mono⟩

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- The bytes `k, …, k + nf - 1` of the group at `x2 = o + gb` from the
accumulator `X`, whose byte `u` is byte `gb + k + u` of the output. -/
theorem flush_ok {gb k nf N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = L (gb + k + u)) (hN : gb + k + nf ≤ N)
    (hN64 : N < 2 ^ 64) (hk : k + nf ≤ 4096) (s : State) (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb)
    (hR : (⟨o, N⟩ : Region) ∈ s.wr) (hw : BytesUpTo s.mem o N (gb + k) L old)
    (hf : VG.Frame [⟨o, N⟩] m₀ s.mem) (hr : (s.gpr .x9).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      BytesUpTo s'.mem o N (gb + k + nf) L old ∧ VG.Frame [⟨o, N⟩] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = X / 2 ^ (8 * nf) ∧ Keep [.x9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.x9] s s' ∧
    (s'.gpr .x9).toNat = X / 2 ^ (8 * u) ∧ BytesUpTo s'.mem o N (gb + k + u) L old ∧
      VG.Frame [⟨o, N⟩] m₀ s'.mem)
    (fun u s' hu ⟨hkp, hr', hw', hf'⟩ => ?_) nf (Nat.le_refl _) s
    ⟨Keep.refl _ _, by rw [hr, Nat.mul_zero, Nat.pow_zero, Nat.div_one], hw, hf⟩)
    fun s' ⟨hkp, hr', hw', hf'⟩ => ⟨hw', hf', hr', hkp⟩
  have ha : s'.gpr .x2 + BitVec.ofNat 64 (k + u) = o + BitVec.ofNat 64 (gb + k + u) := by
    rw [hkp.get .x2, h2, ptr_add, Nat.add_assoc]
  have hc : (⟨o, N⟩ : Region).Contains (o + BitVec.ofNat 64 (gb + k + u)) 1 :=
    Offset.contains_base o (by omega) (by omega)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.packByte_ok (by omega) s' (by rw [ha, hkp.wr]; exact ⟨_, hR, hc⟩))
    fun s'' ⟨hm, h9, hk'⟩ => ⟨(hkp.trans hk').mono, ?_, ?_, ?_⟩
  · rw [h9, toNat_lsr, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ha, show gb + k + (u + 1) = gb + k + u + 1 by omega]
    exact hw'.write (by omega) (by omega) (by rw [setWidth8_of_toNat hr', hX u hu])
  · rw [hm, ha]
    exact hf'.writeW (List.mem_singleton_self _) _ hc

/-- `ld j` loads into `x10` the value `F` of the word at `x0 + 4j`, and
writes only `x10` and `x14`, when `x12` and `x13` hold `K12` and `K13`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) (K12 K13 : BitVec 64) : Prop :=
  ∀ j s, s.gpr .x12 = K12 → s.gpr .x13 = K13 → 4 * j < 16384 →
    InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      (s'.gpr .x10).toNat = F (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) ∧ Only [.x10, .x14] s s'

/-- Field `j`: its value, digit `j` of `G`, into `x9`, then the bytes it
completes, bytes `gb + ⌊dj/8⌋, …` of the output. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64}
    (hld : VG.Proof.MlDsa.AArch64.Pack.LdOk ld F K12 K13) {d j G gb N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem}
    (hd : d ≤ 20) (hj : j < 8) (hN : gb + d * (j + 1) / 8 ≤ N) (hN64 : N < 2 ^ 64)
    (hL : ∀ t < d * (j + 1) / 8, L (gb + t) = VG.Proof.MlDsa.AArch64.Pack.bytesOf G t) (s : State) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb) (hR : (⟨o, N⟩ : Region) ∈ s.wr)
    (hw : BytesUpTo s.mem o N (gb + d * j / 8) L old) (hf : VG.Frame [⟨o, N⟩] m₀ s.mem)
    (hr : (s.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      BytesUpTo s'.mem o N (gb + d * (j + 1) / 8) L old ∧ VG.Frame [⟨o, N⟩] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.x9, .x10, .x14] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s h12 h13 (by omega) hin) fun s₁ ⟨ax₁, o₁⟩ => ?_
  have hx : (s₁.gpr .x10).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [o₁.get .x9, hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.shiftAdd_ok (sh := d * j % 8) (by omega) s₁ (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega)) fun s₂ ⟨r₂, o₂⟩ => ?_
  have hX : (s₂.gpr .x9).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have hle : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
  have hn' : d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 := by omega
  have h8 : d * (j + 1) ≤ 160 := by have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.flush_ok (gb := gb) (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (N := N) (L := L)
      (old := old) (m₀ := m₀) _ (fun u hu => ?_) (by omega) hN64 (by omega) s₂
      (by rw [o₂.get .x2, o₁.get .x2, h2]) (by rw [o₂.wr, o₁.wr]; exact hR)
      (by rw [o₂.mem, o₁.mem]; exact hw) (by rw [o₂.mem, o₁.mem]; exact hf) hX)
    fun s₃ ⟨hw₃, hf₃, hr₃, k₃⟩ => ⟨?_, hf₃, ?_, ((o₁.keep.trans o₂.keep).trans k₃).mono⟩
  · rw [Nat.add_assoc, hL _ (by omega)]
    refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by omega)]
  · rwa [Nat.add_assoc, hn'] at hw₃
  · rw [hr₃, pack_shift, hn']

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values `V` of its `c` coefficients, stored at `x2 = o + gb`: bytes
`gb, …, gb + nb - 1` of the output, whose other bytes `m₀` had. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64}
    (hld : VG.Proof.MlDsa.AArch64.Pack.LdOk ld F K12 K13) {d c nb gb N : Nat} {o : Addr} {L old : Nat → Byte} {m₀ : Mem}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hN : gb + nb ≤ N) (hN64 : N < 2 ^ 64)
    {V : Nat → Nat} (hV : ∀ j < c, V j < 2 ^ d)
    (hL : ∀ t < nb, L (gb + t) = VG.Proof.MlDsa.AArch64.Pack.bytesOf (digits d ((List.range c).map V)) t) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 4)
    (hv : ∀ j < c, ∀ m, VG.Frame [⟨o, N⟩] m₀ m → F (m.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32) = V j)
    (h2 : s.gpr .x2 = o + BitVec.ofNat 64 gb) (hR : (⟨o, N⟩ : Region) ∈ s.wr)
    (hw : BytesUpTo s.mem o N gb L old) (hf : VG.Frame [⟨o, N⟩] m₀ s.mem) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      BytesUpTo s'.mem o N (gb + nb) L old ∧ VG.Frame [⟨o, N⟩] m₀ s'.mem ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 nb ∧
        s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧ Keep [.x0, .x2, .x9, .x10, .x11, .x14] s s' := by
  generalize hG : digits d ((List.range c).map V) = G at hL
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = V j := fun j hj => by rw [← hG]; exact digits_range_get hV hj
  have hdc8 : d * c / 8 = nb := by omega
  have := Nat.mul_le_mul hd hc
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.x9, .x10, .x14] s₁ s' ∧
      BytesUpTo s'.mem o N (gb + d * j / 8) L old ∧ VG.Frame [⟨o, N⟩] m₀ s'.mem ∧
      (s'.gpr .x9).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw', hf', hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [o₁.mem, Nat.mul_zero, Nat.zero_div, Nat.add_zero]; exact hw, by rw [o₁.mem]; exact hf,
      by rw [e₁, toNat_imm, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, hf₂, _⟩ => ?_
  · have hx0 : s'.gpr .x0 = s.gpr .x0 := by rw [hk.get .x0, o₁.get .x0]
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      rw [← hdc8]; exact Nat.div_le_div_right (Nat.mul_le_mul_left d hj)
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.packCoef_ok hld (G := G) (N := N) (L := L) (old := old) (m₀ := m₀) hd (by omega)
      (by omega) hN64 (fun t ht => hL t (by omega)) s' (by rw [hk.get .x12, o₁.get .x12, h12])
      (by rw [hk.get .x13, o₁.get .x13, h13]) (by rw [hk.rd, hk.wr, o₁.rd, o₁.wr, hx0]; exact hin j hj)
      (by rw [hx0, hv j hj _ hf', hdig j hj]) (by rw [hk.get .x2, o₁.get .x2, h2])
      (by rw [hk.wr, o₁.wr]; exact hR) hw' hf' hr)
      fun s'' ⟨hw'', hf'', hr', hk'⟩ => ⟨(hk.trans hk').mono, hw'', hf'', hr'⟩
  · rw [hdc8] at hw₂
    refine VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₄ o₄ e₄ =>
      VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hw₂
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hf₂
    · rw [o₅.get .x0, o₄.get .x0, e₃, k₂.get .x0, o₁.get .x0]
    · rw [o₅.get .x2, e₄, o₃.get .x2, k₂.get .x2, o₁.get .x2]
    · rw [e₅, o₄.get .x11, o₃.get .x11, k₂.get .x11, o₁.get .x11]
    · exact ((((o₁.keep.trans k₂).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono

/-! ## Unpacking -/

theorem unpackByte_ok {d j t : Nat} (hsh : 8 * t - d * j ≤ 56) (ht : t < 4096) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .x9).toNat + (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      (s'.gpr .x9).toNat =
          (s.gpr .x9).toNat + (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        Only [.x9, .x10] s s' := by
  unfold unpackByte
  rw [List.singleton_append]
  refine VG.Proof.MlKem.AArch64.wp_ldrb ht rfl hin fun s₁ o₁ e₁ => ?_
  have hax : (s₁.gpr .x10).toNat = (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat := by rw [e₁, toNat_byte]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.shiftAdd_ok (by omega) s₁ (by rw [hax, o₁.get .x9]; exact hs))
    fun s₂ ⟨r₂, o₂⟩ => ⟨by rw [r₂, hax, o₁.get .x9], (o₁.trans o₂).mono⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (hk4 : k + nl ≤ 4096) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (s.gpr .x0 + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .x9).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .x9).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ Only [.x9, .x10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Only [.x9, .x10] s s' ∧
    (s'.gpr .x9).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Only.refl _ _, hr⟩)
    fun s' ⟨hkp, hr'⟩ => ⟨hr', hkp⟩
  have di : s'.gpr .x0 = s.gpr .x0 := hkp.get .x0
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hkp.mem, ← di] at hbu
  have hbl : (s'.mem (s'.gpr .x0 + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.unpackByte_ok (by omega) (by omega) s' (by rw [hkp.rd, hkp.wr, di]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨r'', k''⟩ => ⟨(hkp.trans k'').mono, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `x10` to
`x4 + 4j`, and writes only `x10` and `x14`, when `x12` and `x13` hold `K12`
and `K13`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) (K12 K13 : BitVec 64) : Prop :=
  ∀ j s, s.gpr .x12 = K12 → s.gpr .x13 = K13 → 4 * j < 16384 →
    InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .x10).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x4 + BitVec.ofNat 64 (4 * j)) (W (s.gpr .x10).toNat) ∧ Keep [.x10, .x14] s s'

theorem extract_ok {d : Nat} (hd : d < 64) (s : State) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1) :
    WP isa (.block [.logic .and .x .x10 .x9 .x15, .lsr .x .x9 .x9 d]) s fun s' =>
      (s'.gpr .x10).toNat = (s.gpr .x9).toNat % 2 ^ d ∧ s'.gpr .x9 = s.gpr .x9 >>> d ∧ Only [.x9, .x10] s s' :=
  VG.Proof.MlKem.AArch64.wp_and fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr hd fun s₂ o₂ e₂ =>
    VG.Proof.MlKem.AArch64.wp_nil ⟨by rw [o₂.get .x10, e₁, toNat_and_mask _ _ h15], by rw [e₂, o₁.get .x9], (o₁.trans o₂).mono⟩

/-- Field `j`: the bytes it needs into `x9`, then its value, digit `j` of
`H`, stored by `fin` as coefficient `gc + j` of the output at `p`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {K12 K13 : BitVec 64}
    (hfin : VG.Proof.MlDsa.AArch64.Pack.FinOk fin d W K12 K13) (hd : d ≤ 20) {H j gc : Nat} {p : Addr} {Wf old : Nat → BitVec 32}
    {m₀ : Mem} (hj : j < 8) (hgc : gc + j < 256) (hW : Wf (gc + j) = W (H / 2 ^ (d * j) % 2 ^ d)) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (s.gpr .x0 + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (h4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * gc)) (hP : polyRegion p ∈ s.wr)
    (hw : CoeffsUpTo s.mem p (gc + j) Wf old) (hf : VG.Frame [polyRegion p] m₀ s.mem)
    (hr : (s.gpr .x9).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      CoeffsUpTo s'.mem p (gc + j + 1) Wf old ∧ VG.Frame [polyRegion p] m₀ s'.mem ∧
        (s'.gpr .x9).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧
        Keep [.x9, .x10, .x14] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  have h8 : d * (j + 1) ≤ 160 := by have := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega); omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) (by rw [hn']; unfold need; omega) s
    (fun u hu => hin _ (by omega)) (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, o₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.extract_ok (by omega) s₁ (by rw [o₁.get .x15, h15])) fun s₂ ⟨ax₂, r₂, o₂⟩ => ?_
  have hv : (s₂.gpr .x10).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have hx4 : s₂.gpr .x4 = s.gpr .x4 := by rw [o₂.get .x4, o₁.get .x4]
  have ha : s₂.gpr .x4 + BitVec.ofNat 64 (4 * j) = coeffAddr p (gc + j) := by
    rw [hx4, h4, ptr_add, ← Nat.mul_add]
  have hc : (polyRegion p).Contains (coeffAddr p (gc + j)) 4 := coeff_contains p hgc
  refine WP.mono (hfin j s₂ (by rw [o₂.get .x12, o₁.get .x12, h12]) (by rw [o₂.get .x13, o₁.get .x13, h13])
      (by omega) (by rw [ha, o₂.wr, o₁.wr]; exact ⟨_, hP, hc⟩) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨?_, ?_, ?_, ((o₁.keep.trans o₂.keep).trans k₃).mono⟩
  · rw [m₃, ha, o₂.mem, o₁.mem]
    exact hw.write hgc (by rw [hv, hW])
  · rw [m₃, ha, o₂.mem, o₁.mem]
    exact hf.writeW (List.mem_singleton_self _) _ hc
  · rw [k₃.get .x9, r₂, toNat_lsr, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes `B` at `x0`: coefficient
`gc + j` of the output at `x4 = p + 4 gc`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} {K12 K13 : BitVec 64}
    (hfin : VG.Proof.MlDsa.AArch64.Pack.FinOk fin d W K12 K13) {c nb gc : Nat} {p : Addr} {Wf old : Nat → BitVec 32} {m₀ : Mem}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hgc : gc + c ≤ 256) {B : Nat → Nat}
    (hW : ∀ j < c, Wf (gc + j) = W (digits 8 ((List.range nb).map B) / 2 ^ (d * j) % 2 ^ d)) (s : State)
    (h12 : s.gpr .x12 = K12) (h13 : s.gpr .x13 = K13) (h15 : (s.gpr .x15).toNat = 2 ^ d - 1)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < nb, ∀ m, VG.Frame [polyRegion p] m₀ m → (m (s.gpr .x0 + BitVec.ofNat 64 t)).toNat = B t)
    (h4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * gc)) (hP : polyRegion p ∈ s.wr)
    (hw : CoeffsUpTo s.mem p gc Wf old) (hf : VG.Frame [polyRegion p] m₀ s.mem) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      CoeffsUpTo s'.mem p (gc + c) Wf old ∧ VG.Frame [polyRegion p] m₀ s'.mem ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 nb ∧ s'.gpr .x4 = s.gpr .x4 + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1 ∧ Keep [.x0, .x4, .x9, .x10, .x11, .x14] s s' := by
  generalize hH : digits 8 ((List.range nb).map B) = H at hW
  have hB : ∀ t < nb, B t < 2 ^ 8 := fun t ht => by
    rw [← hb t ht s.mem hf]; exact BitVec.isLt _
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = B t :=
    fun t ht => by rw [← hH]; exact digits_range_get hB ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.x9, .x10, .x14] s₁ s' ∧
      CoeffsUpTo s'.mem p (gc + j) Wf old ∧ VG.Frame [polyRegion p] m₀ s'.mem ∧
      (s'.gpr .x9).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hw', hf', hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [o₁.mem, Nat.add_zero]; exact hw, by rw [o₁.mem]; exact hf,
      by rw [e₁, toNat_imm]; simp [need, Nat.mod_one]⟩) fun s₂ ⟨k₂, hw₂, hf₂, _⟩ => ?_
  · have hx0 : s'.gpr .x0 = s.gpr .x0 := by rw [hk.get .x0, o₁.get .x0]
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.unpackCoef_ok hfin hd (H := H) (m₀ := m₀) (by omega) (by omega) (hW j hj) s'
      (by rw [hk.get .x12, o₁.get .x12, h12]) (by rw [hk.get .x13, o₁.get .x13, h13])
      (by rw [hk.get .x15, o₁.get .x15, h15])
      (fun t ht => by rw [hk.rd, hk.wr, o₁.rd, o₁.wr, hx0]; exact hin t (by omega))
      (fun t ht => by rw [hx0, hb t (by omega) _ hf', hbyte t (by omega)])
      (by rw [hk.get .x4, o₁.get .x4, h4]) (by rw [hk.wr, o₁.wr]; exact hP) hw' hf' hr)
      fun s'' ⟨hw'', hf'', hr', hk'⟩ => ⟨(hk.trans hk').mono, hw'', hf'', hr'⟩
  · refine VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_addImm (by omega) fun s₄ o₄ e₄ =>
      VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hw₂
    · rw [o₅.mem, o₄.mem, o₃.mem]; exact hf₂
    · rw [o₅.get .x0, o₄.get .x0, e₃, k₂.get .x0, o₁.get .x0]
    · rw [o₅.get .x4, e₄, o₃.get .x4, k₂.get .x4, o₁.get .x4]
    · rw [e₅, o₄.get .x11, o₃.get .x11, k₂.get .x11, o₁.get .x11]
    · exact ((((o₁.keep.trans k₂).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop`. -/
section

/-!
# ML-DSA on AArch64: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_movImm toNat_imm toNat_sub_n toNat_ofNat_lt BytesUpTo
  BytesUpTo.zero BytesUpTo.eq ptr_add ptr_zero ptr_next count_loop)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD)
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

theorem Shape.nb20 {d c nb : Nat} (h : VG.Proof.MlDsa.AArch64.Pack.Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.group {d c nb : Nat} (h : VG.Proof.MlDsa.AArch64.Pack.Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem Shape.G {d c nb : Nat} (h : VG.Proof.MlDsa.AArch64.Pack.Shape d c nb) : 0 < 256 / c ∧ 256 / c ≤ 256 :=
  ⟨Nat.div_pos (by have := h.c8; omega) h.c0, Nat.div_le_self _ _⟩

/-- The registers the loops write. -/
abbrev packRegs : List Reg := [.x0, .x2, .x9, .x10, .x11, .x14]
abbrev unpackRegs : List Reg := [.x0, .x4, .x9, .x10, .x11, .x14, .x15]

/-- A counter set to `n < 2¹⁶` with `movz`. -/
theorem movz_toNat {n : Nat} (h : n < 2 ^ 16) : ((BitVec.ofNat 16 n).setWidth 64).toNat = n := by
  rw [toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The counter after one more group. -/
theorem count_step {x : BitVec 64} {N g : Nat} (h : x.toNat = N - g) (hg : g < N) :
    (x - BitVec.ofNat 64 1).toNat = N - (g + 1) := by
  rw [toNat_sub_n (by rw [h, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by decide)]; omega), h, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by decide)]
  omega

/-! ## Packing -/

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

theorem vals_lt {F : BitVec 32 → Nat} {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ VG.Proof.MlDsa.AArch64.Pack.vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

theorem vals_getD (F : BitVec 32 → Nat) (m : Mem) (f : Addr) {i : Nat} (hi : i < 256) :
    (VG.Proof.MlDsa.AArch64.Pack.vals F m f).getD i 0 = F (coeffAt m f i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} {K12 K13 : BitVec 64} (hld : VG.Proof.MlDsa.AArch64.Pack.LdOk ld F K12 K13)
  {d c nb : Nat} (hs : VG.Proof.MlDsa.AArch64.Pack.Shape d c nb) {f o : Addr} {s₀ sE : State} (hin : polyRegion f ∈ s₀.rd ++ s₀.wr)
  (hout : (⟨o, 32 * d⟩ : Region) ∈ s₀.wr) (hsep : Region.Disjoint (polyRegion f) ⟨o, 32 * d⟩)
  (hF : ∀ i < 256, F (coeffAt s₀.mem f i) < 2 ^ d)
include hld hs hin hout hsep hF

/-- After `g` groups. -/
structure PInv (g : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = f + BitVec.ofNat 64 (4 * c * g)
  x2 : s.gpr .x2 = o + BitVec.ofNat 64 (nb * g)
  x11 : (s.gpr .x11).toNat = 256 / c - g
  x12 : s.gpr .x12 = K12
  x13 : s.gpr .x13 = K13
  out : BytesUpTo s.mem o (32 * d) (nb * g) (fun k => (bitsToBytes (fieldBits d (VG.Proof.MlDsa.AArch64.Pack.vals F s₀.mem f)))[k]!)
    fun k => s₀.mem (o + BitVec.ofNat 64 k)
  frame : VG.Frame [⟨o, 32 * d⟩] s₀.mem s.mem
  keep : Keep VG.Proof.MlDsa.AArch64.Pack.packRegs sE s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem packStep {g : Nat} (hg : g < 256 / c) {s : State}
    (hI : VG.Proof.MlDsa.AArch64.Pack.PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀)
      (sE := sE) g s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Pack.PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀)
        (sE := sE) (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / c) := by
  obtain ⟨hcg, hbg⟩ := hs.group hg
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j, s.gpr .x0 + BitVec.ofNat 64 (4 * j) = coeffAddr f (c * g + j) := fun j => by
    rw [hI.x0, ptr_add, coeffAddr, Nat.mul_add, Nat.mul_assoc]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.packBody_ok hld (gb := nb * g) (N := 32 * d) (o := o) (m₀ := s₀.mem)
    (V := fun j => F (coeffAt s₀.mem f (c * g + j))) hs.d20 hs.dc hs.c8 hbg (by omega)
    (fun j hj => hF _ (by omega)) (fun t ht => ?_) s hI.x12 hI.x13
    (fun j hj => by rw [ha j, hI.rd, hI.wr]; exact ⟨_, hin, coeff_contains f (by omega)⟩)
    (fun j hj m hm => by
      rw [ha j, ← coeffAt_eq]
      exact congrArg F (coeffAt_frame hm (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by omega)))
    hI.x2 (by rw [hI.wr]; exact hout) hI.out hI.frame)
    fun s' ⟨hw', hf', x0', x2', x11', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hf', (hI.keep.trans k').mono, ?_, ?_⟩, ?_⟩
  · -- The bytes of the group.
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (VG.Proof.MlDsa.AArch64.Pack.vals_lt hF) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    exact VG.Proof.MlDsa.AArch64.Pack.vals_getD F s₀.mem f (by have := List.mem_range.mp hj; omega)
  · rw [x0', hI.x0, ptr_add, Nat.mul_succ]
  · rw [x2', hI.x2, ptr_next]
  · rw [x11']; exact VG.Proof.MlDsa.AArch64.Pack.count_step hI.x11 hg
  · rw [k'.get .x12, hI.x12]
  · rw [k'.get .x13, hI.x13]
  · rw [Nat.mul_succ]; exact hw'
  · rw [k'.rd, hI.rd]
  · rw [k'.wr, hI.wr]
  · rw [x11', VG.Proof.MlDsa.AArch64.Pack.count_step hI.x11 hg]; omega

theorem packLoop_ok {s : State} (h0 : s.gpr .x0 = f) (h2 : s.gpr .x2 = o) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem o (32 * d) = bitsToBytes (fieldBits d (VG.Proof.MlDsa.AArch64.Pack.vals F s₀.mem f)) ∧
        VG.Frame [⟨o, 32 * d⟩] s₀.mem s'.mem ∧ Keep VG.Proof.MlDsa.AArch64.Pack.packRegs s s' := by
  obtain ⟨hG0, hG⟩ := hs.G
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  refine WP.mono (count_loop hG0
    (VG.Proof.MlDsa.AArch64.Pack.PInv (F := F) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (f := f) (o := o) (s₀ := s₀) (sE := s))
    (fun g hg s hI => VG.Proof.MlDsa.AArch64.Pack.packStep hld hs hin hout hsep hF hg hI) ?_)
    fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  · refine ⟨by rw [o₁.get .x0, h0, Nat.mul_zero, ptr_zero], by rw [o₁.get .x2, h2, Nat.mul_zero, ptr_zero],
      by rw [e₁, VG.Proof.MlDsa.AArch64.Pack.movz_toNat (by omega), Nat.sub_zero], by rw [o₁.get .x12, h12], by rw [o₁.get .x13, h13],
      ?_, by rw [o₁.mem, hm]; exact Frame.refl _ _, o₁.keep.mono, by rw [o₁.rd, hrd], by rw [o₁.wr, hwr]⟩
    rw [o₁.mem, hm, Nat.mul_zero]; exact BytesUpTo.zero _
  · have hB : nb * (256 / c) = 32 * d := hs.bN
    have hout' := hI.out
    rw [hB] at hout'
    exact hout'.eq (pack_length d _ (by simp)) fun _ _ => rfl

end

/-! ## Unpacking -/

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {K12 K13 : BitVec 64} {d c nb : Nat}
  (hfin : VG.Proof.MlDsa.AArch64.Pack.FinOk fin d W K12 K13) (hs : VG.Proof.MlDsa.AArch64.Pack.Shape d c nb) {v p : Addr} {s₀ sE : State}
  (hin : (⟨v, 32 * d⟩ : Region) ∈ s₀.rd ++ s₀.wr) (hout : polyRegion p ∈ s₀.wr)
  (hsep : Region.Disjoint ⟨v, 32 * d⟩ (polyRegion p))
include hfin hs hin hout hsep

/-- After `g` groups. -/
structure UInv (g : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = v + BitVec.ofNat 64 (nb * g)
  x4 : s.gpr .x4 = p + BitVec.ofNat 64 (4 * (c * g))
  x11 : (s.gpr .x11).toNat = 256 / c - g
  x12 : s.gpr .x12 = K12
  x13 : s.gpr .x13 = K13
  x15 : (s.gpr .x15).toNat = 2 ^ d - 1
  out : CoeffsUpTo s.mem p (c * g) (fun k => W (VG.Proof.MlDsa.AArch64.Pack.inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d))
    fun k => coeffAt s₀.mem p k
  frame : VG.Frame [polyRegion p] s₀.mem s.mem
  keep : Keep VG.Proof.MlDsa.AArch64.Pack.unpackRegs sE s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem unpackStep {g : Nat} (hg : g < 256 / c) {s : State}
    (hI : VG.Proof.MlDsa.AArch64.Pack.UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀)
      (sE := sE) g s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Pack.UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀)
        (sE := sE) (g + 1) s' ∧ ((s'.gpr .x11).toNat ≠ 0 ↔ g + 1 ≠ 256 / c) := by
  obtain ⟨hcg, hbg⟩ := hs.group hg
  have hnb := hs.nb20
  have hd20 := hs.d20
  have hb : ∀ t, s.gpr .x0 + BitVec.ofNat 64 t = v + BitVec.ofNat 64 (nb * g + t) := fun t => by
    rw [hI.x0, ptr_add]
  have hlt : ∀ a ∈ (bytesAt s₀.mem v (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.unpackBody_ok hfin (gc := c * g) (p := p) (m₀ := s₀.mem)
    (B := fun t => (s₀.mem (v + BitVec.ofNat 64 (nb * g + t))).toNat) hs.d20 hs.dc hs.c8 hcg
    (fun j hj => ?_) s hI.x12 hI.x13 hI.x15
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact ⟨_, hin, Offset.contains_base v (by omega) (by omega)⟩)
    (fun t ht m hm => by
      rw [hb]
      refine congrArg BitVec.toNat (hm _ fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep _ (Offset.contains_base v (by omega) (by omega)))
    hI.x4 (by rw [hI.wr]; exact hout) hI.out hI.frame)
    fun s' ⟨hw', hf', x0', x4', x11', k'⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hf', (hI.keep.trans k').mono, ?_, ?_⟩, ?_⟩
  · -- The coefficients of the group.
    have e := digits_group (g := g) hs.dc hlt hj
    rw [take_drop_eq _ 0 (by rw [List.length_map, Spec.Sha3.bytesAt, List.length_map, List.length_range]; omega)]
      at e
    have hB : ((List.range nb).map fun t => ((bytesAt s₀.mem v (32 * d)).map (·.toNat)).getD (nb * g + t) 0) =
        (List.range nb).map fun t => (s₀.mem (v + BitVec.ofNat 64 (nb * g + t))).toNat :=
      List.map_congr_left fun t ht => by
        rw [VG.Proof.MlDsa.AArch64.Pack.getD_map_toNat, bytesAt_getD _ _ (by have := List.mem_range.mp ht; omega)]
    rw [hB] at e
    rw [e]
  · rw [x0', hI.x0, ptr_next]
  · rw [x4', hI.x4, ptr_add, Nat.mul_succ, Nat.mul_add]
  · rw [x11']; exact VG.Proof.MlDsa.AArch64.Pack.count_step hI.x11 hg
  · rw [k'.get .x12, hI.x12]
  · rw [k'.get .x13, hI.x13]
  · rw [k'.get .x15, hI.x15]
  · rw [Nat.mul_succ]; exact hw'
  · rw [k'.rd, hI.rd]
  · rw [k'.wr, hI.wr]
  · rw [x11', VG.Proof.MlDsa.AArch64.Pack.count_step hI.x11 hg]; omega

theorem unpackLoop_ok {s : State} (h0 : s.gpr .x0 = v) (h4 : s.gpr .x4 = p) (h12 : s.gpr .x12 = K12)
    (h13 : s.gpr .x13 = K13) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem p k = W (VG.Proof.MlDsa.AArch64.Pack.inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)) ∧
        VG.Frame [polyRegion p] s₀.mem s'.mem ∧ Keep VG.Proof.MlDsa.AArch64.Pack.unpackRegs s s' := by
  obtain ⟨hG0, hG⟩ := hs.G
  have hd20 := hs.d20
  have hp : 2 ^ d - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hd20; omega
  refine WP.seq ?_
  rw [← List.append_nil [Instr.movz .x .x11 _ 0]]
  refine wp_movImm fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_movz fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  refine WP.mono (count_loop hG0
    (VG.Proof.MlDsa.AArch64.Pack.UInv (W := W) (K12 := K12) (K13 := K13) (d := d) (c := c) (nb := nb) (v := v) (p := p) (s₀ := s₀) (sE := s))
    (fun g hg s hI => VG.Proof.MlDsa.AArch64.Pack.unpackStep hfin hs hin hout hsep hg hI) ?_)
    fun s' hI => ⟨fun k hk => ?_, hI.frame, hI.keep⟩
  · have k₂ := o₁.trans o₂
    refine ⟨by rw [k₂.get .x0, h0, Nat.mul_zero, ptr_zero],
      by rw [k₂.get .x4, h4, Nat.mul_zero, Nat.mul_zero, ptr_zero],
      by rw [e₂, VG.Proof.MlDsa.AArch64.Pack.movz_toNat (by omega), Nat.sub_zero], by rw [k₂.get .x12, h12], by rw [k₂.get .x13, h13],
      by rw [o₂.get .x15, e₁, VG.Proof.MlKem.AArch64.toNat_ofNat_lt hp], ?_, by rw [k₂.mem, hm]; exact Frame.refl _ _, k₂.keep.mono,
      by rw [k₂.rd, hrd], by rw [k₂.wr, hwr]⟩
    rw [k₂.mem, hm, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · have hout' := hI.out
    rw [hs.cN] at hout'
    exact hout'.all hk

end

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts`. -/
section

/-!
# ML-DSA on AArch64: the contracts of the encodings, for the proofs

For each packing function, a contract with the facts of its shared contract
(`Spec/MlDsa/Poly.lean`) spelled out for AArch64: the arguments in their
registers, the permitted regions, their disjointness, and the postcondition.
The proofs are written against these, and `Verified.of_correct` moves them to
the shared contracts, which imply them. Also: `sel_ok`, the branch of `sel` on
a length.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Only wp_subImm wp_nil eval_zero eq_zero_iff)
open VG.Proof.MlDsa.Pack

/-- The 32-bit argument in `r`. -/
abbrev wArg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_simple_bit_pack(f = x0, b = w1, out = x2, len = x3)`. -/
def simpleBitPackK : Contract isa where
  pre s :=
    s.rd = [polyRegion (s.gpr .x0)] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧ VG.Proof.MlDsa.AArch64.Pack.wArg s .x1 ∈ simpleBitPackBounds ∧
    (s.gpr .x3).toNat = 32 * bitlen (VG.Proof.MlDsa.AArch64.Pack.wArg s .x1) ∧ ∀ i < n, (coeffAt s.mem (s.gpr .x0) i).toNat ≤ VG.Proof.MlDsa.AArch64.Pack.wArg s .x1
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    simpleBitPack (natPolyAt s.mem (s.gpr .x0)) (VG.Proof.MlDsa.AArch64.Pack.wArg s .x1)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_bit_pack(f = x0, a = w1, b = w2, out = x3, len = x4)`. -/
def bitPackK : Contract isa where
  pre s :=
    s.rd = [polyRegion (s.gpr .x0)] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧ (VG.Proof.MlDsa.AArch64.Pack.wArg s .x1, VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ∈ bitPackParams ∧
    (s.gpr .x4).toNat = 32 * bitlen (VG.Proof.MlDsa.AArch64.Pack.wArg s .x1 + VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ∧ Reduced s.mem (s.gpr .x0) ∧
    ∀ i < n, -(VG.Proof.MlDsa.AArch64.Pack.wArg s .x1 : Int) ≤ modPm (coeffAt s.mem (s.gpr .x0) i).toNat q ∧
      modPm (coeffAt s.mem (s.gpr .x0) i).toNat q ≤ VG.Proof.MlDsa.AArch64.Pack.wArg s .x2
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
    bitPack ((polyAt s.mem (s.gpr .x0)).map fun c => modPm c.val q) (VG.Proof.MlDsa.AArch64.Pack.wArg s .x1) (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_bit_unpack(v = x0, len = x1, a = w2, b = w3, f = x4)`. -/
def bitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [polyRegion (s.gpr .x4)] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ (polyRegion (s.gpr .x4)) ∧
    (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2, VG.Proof.MlDsa.AArch64.Pack.wArg s .x3) ∈ bitPackParams ∧ (s.gpr .x1).toNat = 32 * bitlen (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2 + VG.Proof.MlDsa.AArch64.Pack.wArg s .x3)
  post s s' := PolyIs s'.mem (s.gpr .x4)
    (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) (VG.Proof.MlDsa.AArch64.Pack.wArg s .x3)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_unpack_t1(v = x0, f = x1)`. -/
def unpackT1K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 320⟩] ∧ s.wr = [polyRegion (s.gpr .x1)] ∧
    Region.Disjoint ⟨s.gpr .x0, 320⟩ (polyRegion (s.gpr .x1))
  post s s' := PolyIs s'.mem (s.gpr .x1)
    ((simpleBitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-! ## Branching on a length -/

/-- `sel r v p e` runs `p` if `r = v`, else `e`, after writing `x9`. -/
theorem sel_ok {r : Reg} {v : Nat} (hv : v < 4096) {p e : Prog isa} {s : State} {Q : State → Prop}
    (hp : ∀ s', Only [.x9] s s' → (s.gpr r).toNat = v → WP isa p s' Q)
    (he : ∀ s', Only [.x9] s s' → (s.gpr r).toNat ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_subImm hv fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have hr := (s.gpr r).isLt
  have hz : isa.eval (.zero .x .x9) s₁ = some (decide ((s.gpr r).toNat = v)) := by
    rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, e₁, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v) (by omega)]
    congr 1
    apply decide_eq_decide.mpr
    omega
  refine WP.ite _ hz (fun h => hp s₁ o₁ (of_decide_eq_true h)) (fun h => he s₁ o₁ (of_decide_eq_false h))

/-- The arguments of `BitPack` and `BitUnpack`, by the length. -/
theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_pack`

The code follows the fold form of `HintBitPack` (`Pack/Hint.lean`) step by
step: the bytes of `y` are the array of the spec, and `x5` its index, which
stays below `ω` because it counts the 1s before the current coefficient
(`hpIdx_lt`).

Constant time but for the hint: once `y` is zeroed, the two runs agree on
all the memory the function may access (the hint, which the contract lets
it leak, and `y`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_ldrw wp_strb wp_addImm wp_subImm wp_movz wp_mov
  wp_nil eval_nonzero ne_zero_iff toNat_readW32 toNat_ofNat_lt toNat_imm setWidth8_of_toNat ptr_add ptr_zero
  count_loop abi_of agree_of)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_getD bytesAt_eq bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_pack(h = x0, hlen = x1, omega = w2, y = x3, len = x4)`. -/
def hintBitPackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat * 4⟩] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 4⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
    (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2, (s.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ∈ hintParams ∧ VG.Proof.MlDsa.AArch64.Pack.wArg s .x2 ≤ (s.gpr .x4).toNat ∧
    (s.gpr .x1).toNat = 256 * ((s.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ∧
    hintOnes (hintAt s.mem (s.gpr .x0) ((s.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2)) ≤ VG.Proof.MlDsa.AArch64.Pack.wArg s .x2
  post s s' := bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
    hintBitPack (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ((s.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2)
      (hintAt s.mem (s.gpr .x0) ((s.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    (List.range (s₁.gpr .x1).toNat).map (fun i => (coeffAt s₁.mem (s₁.gpr .x0) i).toNat) =
      (List.range (s₂.gpr .x1).toNat).map (fun i => (coeffAt s₂.mem (s₂.gpr .x0) i).toNat)

/-- `x + 1`, of a number. -/
theorem ofNat_succ64 (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 1 = BitVec.ofNat 64 (x + 1) := by
  rw [BitVec.ofNat_add_ofNat]

/-- The low byte of a register holding a number. -/
theorem lowByte (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]

/-- `k = hlen / 256` and `ω = len - k`, from the lengths. -/
theorem lsr8_toNat (x : BitVec 64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : hintBitPackK.pre s₀)

/-- The arguments. -/
abbrev hω (s₀ : State) : Nat := VG.Proof.MlDsa.AArch64.Pack.wArg s₀ .x2
abbrev hk (s₀ : State) : Nat := (s₀.gpr .x4).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s₀ .x2
abbrev hLen (s₀ : State) : Nat := (s₀.gpr .x4).toNat
abbrev hH (s₀ : State) : List (Vector Bool n) := hintAt s₀.mem (s₀.gpr .x0) (VG.Proof.MlDsa.AArch64.Pack.hk s₀)
abbrev hR (s₀ : State) : Region := ⟨s₀.gpr .x0, (s₀.gpr .x1).toNat * 4⟩
abbrev yR (s₀ : State) : Region := ⟨s₀.gpr .x3, VG.Proof.MlDsa.AArch64.Pack.hLen s₀⟩

include hp in
theorem hp_facts : 4 ≤ VG.Proof.MlDsa.AArch64.Pack.hk s₀ ∧ VG.Proof.MlDsa.AArch64.Pack.hk s₀ ≤ 8 ∧ VG.Proof.MlDsa.AArch64.Pack.hω s₀ ≤ 80 ∧ VG.Proof.MlDsa.AArch64.Pack.hω s₀ + VG.Proof.MlDsa.AArch64.Pack.hk s₀ = VG.Proof.MlDsa.AArch64.Pack.hLen s₀ ∧
    (s₀.gpr .x1).toNat = 256 * VG.Proof.MlDsa.AArch64.Pack.hk s₀ := by
  have := mem_hintParams hp.2.2.2.1
  have := hp.2.2.2.2.1
  have := hp.2.2.2.2.2.1
  simp only [VG.Proof.MlDsa.AArch64.Pack.hk, VG.Proof.MlDsa.AArch64.Pack.hω, VG.Proof.MlDsa.AArch64.Pack.hLen] at *
  omega

/-! ## Zeroing `y` -/

/-- What `hbpInit` leaves. -/
def hbpInitPost (s₀ s : State) : Prop :=
  (∀ t < VG.Proof.MlDsa.AArch64.Pack.hLen s₀, s.mem (s₀.gpr .x3 + BitVec.ofNat 64 t) = 0) ∧ VG.Frame [VG.Proof.MlDsa.AArch64.Pack.yR s₀] s₀.mem s.mem ∧
    s.gpr .x0 = s₀.gpr .x0 ∧ s.gpr .x3 = s₀.gpr .x3 ∧ s.gpr .x2 = s₀.gpr .x4 - (s₀.gpr .x1 >>> 8) ∧
    s.gpr .x12 = s₀.gpr .x1 >>> 8 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp

include hp in
theorem hbpInit_ok : WP isa hbpInit s₀ (VG.Proof.MlDsa.AArch64.Pack.hbpInitPost s₀) := by
  obtain ⟨hk4, -, -, hsum, -⟩ := VG.Proof.MlDsa.AArch64.Pack.hp_facts hp
  have hwr := hp.2.1
  have hl : VG.Proof.MlDsa.AArch64.Pack.hLen s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  unfold hbpInit hbpPro
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_movz fun s₃ o₃ e₃ =>
    VG.Proof.MlKem.AArch64.wp_mov fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_mov fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  have x15 : s₅.gpr .x15 = 0 := by rw [o₅.get .x15, o₄.get .x15, e₃]; rfl
  refine WP.mono (count_loop (n := VG.Proof.MlDsa.AArch64.Pack.hLen s₀) (by omega) (fun t s => s.gpr .x9 = s₀.gpr .x3 + BitVec.ofNat 64 t ∧
      (s.gpr .x10).toNat = VG.Proof.MlDsa.AArch64.Pack.hLen s₀ - t ∧ Keep [.x9, .x10] s₅ s ∧ VG.Frame [VG.Proof.MlDsa.AArch64.Pack.yR s₀] s₀.mem s.mem ∧
      ∀ u < t, s.mem (s₀.gpr .x3 + BitVec.ofNat 64 u) = 0)
    (fun t ht s ⟨h9, h10, hk, hf, hz⟩ => ?_)
    ⟨by rw [o₅.get .x9, e₄, o₃.get .x3, o₂.get .x3, o₁.get .x3, ptr_zero],
      (by rw [e₅, o₄.get .x4, o₃.get .x4, o₂.get .x4, o₁.get .x4, Nat.sub_zero]), Keep.refl _ _, by rw [k₅.mem]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s ⟨_, _, hk, hf, hz⟩ => ⟨hz, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : (VG.Proof.MlDsa.AArch64.Pack.yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 t) 1 := Offset.contains_base _ (by omega) (by omega)
    refine VG.Proof.MlKem.AArch64.wp_strb (by decide) (by rw [h9, ptr_zero]) (by rw [hk.wr, k₅.wr, hwr]; exact ⟨_, .head _, hc⟩)
      fun s₁ h₁ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil
        ⟨⟨by rw [o₃.get .x9, e₂, h₁.gpr, h9, ptr_add], by rw [e₃, o₂.get .x10, h₁.gpr]; exact VG.Proof.MlDsa.AArch64.Pack.count_step h10 ht,
          ((hk.trans h₁.keep).trans (o₂.keep.trans o₃.keep)).mono, ?_, fun u hu => ?_⟩, ?_⟩
    · rw [o₃.mem, o₂.mem, h₁.mem]
      exact hf.writeW (List.mem_singleton_self _) _ hc
    · rw [o₃.mem, o₂.mem, h₁.mem, VG.WriteBytes.writeW8_apply]
      by_cases e : u = t
      · subst e; rw [ite_eq_left rfl, hk.get .x15, x15]; rfl
      · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) e)]; exact hz u (by omega)
    · rw [e₃, o₂.get .x10, h₁.gpr, VG.Proof.MlDsa.AArch64.Pack.count_step h10 ht]; omega
  · rw [hk.get .x0, k₅.get .x0]
  · rw [hk.get .x3, k₅.get .x3]
  · rw [hk.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, e₂, o₁.get .x4, e₁]
  · rw [hk.get .x12, o₅.get .x12, o₄.get .x12, o₃.get .x12, o₂.get .x12, e₁]
  · rw [hk.rd, k₅.rd]
  · rw [hk.wr, k₅.wr]
  · rw [hk.sp, k₅.sp]

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (VG.Proof.MlDsa.AArch64.Pack.hω s₀) (VG.Proof.MlDsa.AArch64.Pack.hH s₀)) (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + VG.Proof.MlDsa.AArch64.Pack.hk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((VG.Proof.MlDsa.AArch64.Pack.hH s₀).getD i noHint)) (VG.Proof.MlDsa.AArch64.Pack.hpS s₀ i)

theorem hpT_zero (s₀ : State) (i : Nat) : VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i 0 = VG.Proof.MlDsa.AArch64.Pack.hpS s₀ i := by
  simp only [VG.Proof.MlDsa.AArch64.Pack.hpT, List.range_zero, List.foldl_nil]


theorem hpS_idx (s₀ : State) (i : Nat) : (VG.Proof.MlDsa.AArch64.Pack.hpS s₀ i).2 = onesBefore (VG.Proof.MlDsa.AArch64.Pack.hH s₀) i 0 := by
  rw [VG.Proof.MlDsa.AArch64.Pack.hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2 = onesBefore (VG.Proof.MlDsa.AArch64.Pack.hH s₀) i j := by
  rw [VG.Proof.MlDsa.AArch64.Pack.hpT, hpSteps_idx, VG.Proof.MlDsa.AArch64.Pack.hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (s₀ : State) (i j : Nat) :
    VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i (j + 1) = hpStep ((VG.Proof.MlDsa.AArch64.Pack.hH s₀).getD i noHint) (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j) j := by
  rw [VG.Proof.MlDsa.AArch64.Pack.hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    VG.Proof.MlDsa.AArch64.Pack.hpS s₀ (i + 1) = ((VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i n).1.set! (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i) (BitVec.ofNat 8 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i n).2), (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i n).2) := by
  rw [VG.Proof.MlDsa.AArch64.Pack.hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i + j))
  x3 : s.gpr .x3 = s₀.gpr .x3
  x5 : s.gpr .x5 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2
  x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i)
  x7 : s.gpr .x7 = BitVec.ofNat 64 j
  x8 : (s.gpr .x8).toNat = 256 - j
  x12 : (s.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.hk s₀ - i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .x3) (VG.Proof.MlDsa.AArch64.Pack.hLen s₀) = (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).1.toList

/-- The end of a coefficient: the pointer, `j` and the count. -/
theorem coefTail_ok {i j : Nat} (hj : j < 256) {s : State}
    (x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i + j))) (x3 : s.gpr .x3 = s₀.gpr .x3)
    (x5 : s.gpr .x5 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i (j + 1)).2)
    (x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i)) (x7 : s.gpr .x7 = BitVec.ofNat 64 j)
    (x8 : (s.gpr .x8).toNat = 256 - j) (x12 : (s.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.hk s₀ - i) (rd : s.rd = s₀.rd)
    (wr : s.wr = s₀.wr) (sp : s.sp = s₀.sp) (frame : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.yR s₀] s₀.mem s.mem)
    (y : bytesAt s.mem (s₀.gpr .x3) (VG.Proof.MlDsa.AArch64.Pack.hLen s₀) = (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i (j + 1)).1.toList) :
    WP isa (.block [.addImm .x .x0 .x0 4, .addImm .x .x7 .x7 1, .subImm .x .x8 .x8 1]) s fun s' =>
      VG.Proof.MlDsa.AArch64.Pack.CInv s₀ i (j + 1) s' ∧ ((s'.gpr .x8).toNat ≠ 0 ↔ j + 1 ≠ 256) :=
  VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_subImm (by decide)
    fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil (by
      have k₃ := (o₁.trans o₂).trans o₃
      have c8 : (s₃.gpr .x8).toNat = 256 - (j + 1) := by
        rw [e₃, o₂.get .x8, o₁.get .x8]; exact VG.Proof.MlDsa.AArch64.Pack.count_step x8 hj
      refine ⟨⟨?_, by rw [k₃.get .x3, x3], by rw [k₃.get .x5, x5], by rw [k₃.get .x6, x6], ?_, c8,
        by rw [k₃.get .x12, x12], by rw [k₃.rd, rd], by rw [k₃.wr, wr], by rw [k₃.sp, sp],
        by rw [k₃.mem]; exact frame, by rw [k₃.mem]; exact y⟩, by rw [c8]; omega⟩
      · rw [o₃.get .x0, o₂.get .x0, e₁, x0, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
      · rw [o₃.get .x7, e₂, o₁.get .x7, x7, VG.Proof.MlDsa.AArch64.Pack.ofNat_succ64])

include hp in
/-- Coefficient `j` of polynomial `i`: if it is not 0, `y[index] ← j`. -/
theorem coef_ok {i j : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.hk s₀) (hj : j < 256) {s : State} (hI : VG.Proof.MlDsa.AArch64.Pack.CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => VG.Proof.MlDsa.AArch64.Pack.CInv s₀ i (j + 1) s' ∧ ((s'.gpr .x8).toNat ≠ 0 ↔ j + 1 ≠ 256) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := VG.Proof.MlDsa.AArch64.Pack.hp_facts hp
  obtain ⟨hrd, hwr, hsep, -, -, -, hones⟩ := hp
  have hones' : hintOnes (VG.Proof.MlDsa.AArch64.Pack.hH s₀) ≤ VG.Proof.MlDsa.AArch64.Pack.hω s₀ := hones
  have hpos : 256 * i + j < 256 * VG.Proof.MlDsa.AArch64.Pack.hk s₀ := by omega
  have hR' : (VG.Proof.MlDsa.AArch64.Pack.hR s₀).Contains (coeffAddr (s₀.gpr .x0) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have hw : s.mem.readW (coeffAddr (s₀.gpr .x0) (256 * i + j)) 32 = coeffAt s₀.mem (s₀.gpr .x0) (256 * i + j) :=
    hI.frame.readW hR' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by decide)
  have hbit := hintAt_get (m := s₀.mem) (p := s₀.gpr .x0) hi (show j < n from hj)
  have hT := VG.Proof.MlDsa.AArch64.Pack.hpT_succ s₀ i j
  have hidx := VG.Proof.MlDsa.AArch64.Pack.hpT_idx s₀ i j
  unfold hbpCoef
  refine WP.seq (wp_ldrw (a := coeffAddr (s₀.gpr .x0) (256 * i + j)) ⟨by decide, by decide⟩
    (by rw [hI.x0, ptr_zero]) (by rw [hI.rd, hI.wr, hrd]; exact ⟨_, .head _, hR'⟩) fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have hb : (s₁.gpr .x9 != 0) = ((VG.Proof.MlDsa.AArch64.Pack.hH s₀).getD i noHint)[j]! := by
    rw [hbit, ne_zero_iff, e₁, toNat_readW32, hw]
    exact decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl), fun h e => h (BitVec.eq_of_toNat_eq e)⟩
  refine WP.seq (WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₁ .x9) (fun h1 => ?_) (fun h0 => ?_))
  · -- A 1: `y[index] ← j`.
    rw [hb] at h1
    have hlt : (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2 < VG.Proof.MlDsa.AArch64.Pack.hLen s₀ := by
      have : onesBefore (VG.Proof.MlDsa.AArch64.Pack.hH s₀) i j < hintOnes (VG.Proof.MlDsa.AArch64.Pack.hH s₀) :=
        hpIdx_lt (hintAt_length s₀.mem (s₀.gpr .x0) _) hi (show j < n from hj) h1
      rw [hidx]; omega
    have hc : (VG.Proof.MlDsa.AArch64.Pack.yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    unfold hbpSet
    refine VG.Proof.MlKem.AArch64.wp_add fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_strb (by decide) (by rw [e₂, o₁.get .x3, o₁.get .x5, hI.x3, hI.x5, ptr_zero])
      (by rw [o₂.wr, o₁.wr, hI.wr, hwr]; exact ⟨_, .head _, hc⟩) fun s₃ h₃ =>
      VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_nil ?_
    have k₄ := ((o₁.keep.trans o₂.keep).trans h₃.keep).trans o₄.keep
    have m₄ : s₄.mem = s.mem.writeW (s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2) (BitVec.ofNat 8 j) := by
      rw [o₄.mem, h₃.mem, o₂.mem, o₁.mem, o₂.get .x7, o₁.get .x7, hI.x7, VG.Proof.MlDsa.AArch64.Pack.lowByte]
    have hT1 : VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i (j + 1) = ((VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).1.set! (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2 (BitVec.ofNat 8 j), (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j).2 + 1) := by
      rw [hT, hpStep, h1]; rfl
    refine VG.Proof.MlDsa.AArch64.Pack.coefTail_ok hj (by rw [k₄.get .x0, hI.x0]) (by rw [k₄.get .x3, hI.x3])
      (by rw [e₄, h₃.gpr, o₂.get .x5, o₁.get .x5, hI.x5, hT1, VG.Proof.MlDsa.AArch64.Pack.ofNat_succ64]) (by rw [k₄.get .x6, hI.x6])
      (by rw [k₄.get .x7, hI.x7]) (by rw [k₄.get .x8, hI.x8]) (by rw [k₄.get .x12, hI.x12]) (by rw [k₄.rd, hI.rd])
      (by rw [k₄.wr, hI.wr]) (by rw [k₄.sp, hI.sp]) ?_ ?_
    · rw [m₄]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
    · rw [m₄, bytesAt_writeW8 _ _ hlt (by omega), hI.y, hT1]
      simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · -- A 0.
    rw [hb] at h0
    have hT0 : VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i (j + 1) = VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i j := by rw [hT, hpStep, h0]; rfl
    refine WP.block_nil (VG.Proof.MlDsa.AArch64.Pack.coefTail_ok hj (by rw [o₁.get .x0, hI.x0]) (by rw [o₁.get .x3, hI.x3])
      (by rw [o₁.get .x5, hI.x5, hT0]) (by rw [o₁.get .x6, hI.x6]) (by rw [o₁.get .x7, hI.x7])
      (by rw [o₁.get .x8, hI.x8]) (by rw [o₁.get .x12, hI.x12]) (by rw [o₁.rd, hI.rd]) (by rw [o₁.wr, hI.wr])
      (by rw [o₁.sp, hI.sp]) (by rw [o₁.mem]; exact hI.frame) (by rw [o₁.mem, hI.y, hT0]))

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 (4 * (256 * i))
  x3 : s.gpr .x3 = s₀.gpr .x3
  x5 : s.gpr .x5 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hpS s₀ i).2
  x6 : s.gpr .x6 = s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i)
  x12 : (s.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.hk s₀ - i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.yR s₀] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .x3) (VG.Proof.MlDsa.AArch64.Pack.hLen s₀) = (VG.Proof.MlDsa.AArch64.Pack.hpS s₀ i).1.toList

include hp in
theorem poly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.hk s₀) {s : State} (hP : VG.Proof.MlDsa.AArch64.Pack.HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => VG.Proof.MlDsa.AArch64.Pack.HPInv s₀ (i + 1) s' ∧ ((s'.gpr .x12).toNat ≠ 0 ↔ i + 1 ≠ VG.Proof.MlDsa.AArch64.Pack.hk s₀) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := VG.Proof.MlDsa.AArch64.Pack.hp_facts hp
  have hwr := hp.2.1
  have hones : hintOnes (VG.Proof.MlDsa.AArch64.Pack.hH s₀) ≤ VG.Proof.MlDsa.AArch64.Pack.hω s₀ := hp.2.2.2.2.2.2
  unfold hbpPoly
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_movz fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₂ := o₁.trans o₂
  refine WP.seq (WP.mono (count_loop (n := 256) (by decide) (VG.Proof.MlDsa.AArch64.Pack.CInv s₀ i)
    (fun j hj s hI => VG.Proof.MlDsa.AArch64.Pack.coef_ok hp hi hj hI) (s := s₂) ⟨by rw [k₂.get .x0, hP.x0, Nat.add_zero], by rw [k₂.get .x3, hP.x3],
      by rw [k₂.get .x5, hP.x5, VG.Proof.MlDsa.AArch64.Pack.hpT_zero], by rw [k₂.get .x6, hP.x6], by rw [o₂.get .x7, e₁]; rfl,
      by rw [e₂, toNat_imm]; rfl, by rw [k₂.get .x12, hP.x12], by rw [k₂.rd, hP.rd], by rw [k₂.wr, hP.wr],
      by rw [k₂.sp, hP.sp], by rw [k₂.mem]; exact hP.frame, by rw [k₂.mem, hP.y, VG.Proof.MlDsa.AArch64.Pack.hpT_zero]⟩) fun s₃ hI => ?_)
  have hidx : (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i 256).2 < 2 ^ 8 := by
    have h1 : onesBefore (VG.Proof.MlDsa.AArch64.Pack.hH s₀) i 256 ≤ hintOnes (VG.Proof.MlDsa.AArch64.Pack.hH s₀) := onesBefore_n_le (hintAt_length _ _ _) hi
    rw [VG.Proof.MlDsa.AArch64.Pack.hpT_idx]; omega
  have hc : (VG.Proof.MlDsa.AArch64.Pack.yR s₀).Contains (s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i)) 1 := Offset.contains_base _ (by omega) (by omega)
  refine VG.Proof.MlKem.AArch64.wp_strb (by decide) (by rw [hI.x6, ptr_zero]) (by rw [hI.wr, hwr]; exact ⟨_, .head _, hc⟩)
    fun s₄ h₄ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₆ o₆ e₆ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₆ := (h₄.keep.trans o₅.keep).trans o₆.keep
  have c12 : (s₆.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.hk s₀ - (i + 1) := by
    rw [e₆, o₅.get .x12, h₄.gpr]; exact VG.Proof.MlDsa.AArch64.Pack.count_step hI.x12 hi
  have m₆ : s₆.mem = s₃.mem.writeW (s₀.gpr .x3 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + i)) (BitVec.ofNat 8 (VG.Proof.MlDsa.AArch64.Pack.hpT s₀ i 256).2) := by
    rw [o₆.mem, o₅.mem, h₄.mem, hI.x5, VG.Proof.MlDsa.AArch64.Pack.lowByte]
  refine ⟨⟨?_, by rw [k₆.get .x3, hI.x3], by rw [k₆.get .x5, hI.x5, VG.Proof.MlDsa.AArch64.Pack.hpS_succ], ?_, c12, by rw [k₆.rd, hI.rd],
    by rw [k₆.wr, hI.wr], by rw [k₆.sp, hI.sp], ?_, ?_⟩, by rw [c12]; omega⟩
  · rw [k₆.get .x0, hI.x0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [o₆.get .x6, e₅, h₄.gpr, hI.x6, ptr_add, Nat.add_assoc]
  · rw [m₆]; exact hI.frame.writeW (List.mem_singleton_self _) _ hc
  · rw [m₆, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, VG.Proof.MlDsa.AArch64.Pack.hpS_succ]
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

include hp in
theorem hbpMain_ok {s : State} (hI : VG.Proof.MlDsa.AArch64.Pack.hbpInitPost s₀ s) :
    WP isa hbpMain s fun s' => VG.Proof.MlDsa.AArch64.Pack.HPInv s₀ (VG.Proof.MlDsa.AArch64.Pack.hk s₀) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr1⟩ := VG.Proof.MlDsa.AArch64.Pack.hp_facts hp
  obtain ⟨hz, hf, h0, h3, h2, h12, hrd, hwr, hsp⟩ := hI
  have hl := (s₀.gpr .x4).isLt
  have e4 : VG.Proof.MlDsa.AArch64.Pack.hLen s₀ = (s₀.gpr .x4).toNat := rfl
  have hx12 : (s₀.gpr .x1 >>> 8).toNat = VG.Proof.MlDsa.AArch64.Pack.hk s₀ := by rw [VG.Proof.MlDsa.AArch64.Pack.lsr8_toNat, hr1]; omega
  have hx2 : s.gpr .x2 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.hω s₀) := by
    rw [h2]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hx12, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by omega)]
    omega
  unfold hbpMain
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_add fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₂ := o₁.trans o₂
  refine count_loop (n := VG.Proof.MlDsa.AArch64.Pack.hk s₀) (by omega) (VG.Proof.MlDsa.AArch64.Pack.HPInv s₀) (fun i hi s hP => VG.Proof.MlDsa.AArch64.Pack.poly_ok hp hi hP)
    ⟨by rw [k₂.get .x0, h0]; exact (ptr_zero _).symm, by rw [k₂.get .x3, h3],
      by rw [o₂.get .x5, e₁]; rfl, by rw [e₂, o₁.get .x3, o₁.get .x2, h3, hx2, Nat.add_zero],
      by rw [k₂.get .x12, h12, hx12]; rfl, by rw [k₂.rd, hrd], by rw [k₂.wr, hwr], by rw [k₂.sp, hsp],
      by rw [k₂.mem]; exact hf, ?_⟩
  rw [k₂.mem]
  show _ = (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.hω s₀ + VG.Proof.MlDsa.AArch64.Pack.hk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]
  exact bytesAt_eq (by simp) fun t ht => by rw [hz t ht]; simp

end

theorem hintBitPack_correct (s : State) (hs : hintBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.hintBitPack s t s' ∧ abiPreserved s s' ∧ hintBitPackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := WP.seq (c₁ := hbpInit) (c₂ := hbpMain)
    (WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbpInit_ok hs) fun _ h => VG.Proof.MlDsa.AArch64.Pack.hbpMain_ok hs h)
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hb.y.trans (hintBitPack_eq _ _ _).symm⟩

/-! ## Constant time -/

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x0, .x2, .x3, .x12]

theorem hintBitPack_ct :
    ConstantTime isa hintBitPackK.pre hintBitPackK.pub Impl.MlDsa.AArch64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := memTaint.Agree VG.Proof.MlDsa.AArch64.Pack.hbpTaint) ?_
    (RelCT.taint (A := memTaint) VG.Proof.MlDsa.AArch64.Pack.hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := VG.Proof.MlDsa.AArch64.Pack.hbpInitPost)
    (RelCT.taint (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x1, .x3, .x4])
      (fun _ _ ⟨_, _, h0, h1, h3, h4, hsp, _⟩ => agree_of hsp (by simp [h0, h1, h3, h4])) (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlDsa.AArch64.Pack.hbpInit_ok hx, VG.Proof.MlDsa.AArch64.Pack.hbpInit_ok hy⟩)) (fun _ _ h => h) fun x' y' ⟨_, x, y, ⟨hx, hy, hp⟩, fx, fy⟩ => ?_
  obtain ⟨hz₁, hf₁, a0, a3, a2, a12, rd₁, wr₁, sp₁⟩ := fx
  obtain ⟨hz₂, hf₂, b0, b3, b2, b12, rd₂, wr₂, sp₂⟩ := fy
  obtain ⟨p0, p1, p3, p4, psp, hleak⟩ := hp
  have hrd : x'.rd = y'.rd := by rw [rd₁, rd₂, hx.1, hy.1, p0, p1]
  have hwr : x'.wr = y'.wr := by rw [wr₁, wr₂, hx.2.1, hy.2.1, p3, p4]
  refine ⟨agree_of (by rw [sp₁, sp₂, psp]) fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a0, b0, p0]
    · rw [a2, b2, p4, p1]
    · rw [a3, b3, p3]
    · rw [a12, b12, p1]
  · rw [rd₁, wr₁, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      rw [hf₁ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'),
        hf₂ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [VG.Proof.MlDsa.AArch64.Pack.yR, VG.Proof.MlDsa.AArch64.Pack.hLen, ← p3, ← p4] at hc'
          exact hx.2.2.1 a hc hc')]
      exact bytes_of_words (by rw [← p0, ← p1] at hleak; exact hleak) hc
    · -- `y`: zeros.
      have hlt : (a - x.gpr .x3).toNat < (x.gpr .x4).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .x3 + BitVec.ofNat 64 (a - x.gpr .x3).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := hz₁ _ hlt
      have h₂ := hz₂ _ (show _ < (y.gpr .x4).toNat by rw [← p4]; exact hlt)
      rw [← p3, ← ea] at h₂
      rw [← ea] at h₁
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def hintBitPackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1024 | .x2 => 80 | .x3 => 0x3000 | .x4 => 84 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

theorem hintBitPack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.hintBitPack (hintBitPackContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.hintBitPack_correct VG.Proof.MlDsa.AArch64.Pack.hintBitPack_ct
    { pre := by sig_implies_pre [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitPackK, AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitPackK, AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitPackK, AArch64.abi, AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.hintBitPackSat, ?_⟩
        sig_pre [hintBitPackContract, hintBitPackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | (rw [hintOnes_zero]; exact Nat.zero_le _)
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpackPoly`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_unpack`, one polynomial

The code follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Pack/Hint.lean`) step by step: while no check has failed, the words of `h`
are the hint of the spec (`HArr`) and `x5` its index; once one has, `x5` is
256, which fails every later check (`SRel`). This file: the zeroing of `h`,
and a polynomial (`upoly_ok`): its bound, checked against the index and `ω`,
and its coefficients, each checked against the previous one plus one, which
`x11` holds (0 before the first: `prevV`).
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_lsl wp_ldrb wp_strw wp_addImm wp_subImm wp_movz
  wp_mov wp_orr wp_nil eval_nonzero ne_zero_iff toNat_byte toNat_ofNat_lt toNat_imm toNat_lsl_n ptr_add
  ptr_zero count_loop)
open VG.Proof.MlKem (bytesAt_getD bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_unpack(y = x0, len = x1, omega = w2, h = x3, hlen = x4) -> w0`. -/
def hintBitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat * 4⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 4⟩ ∧
    (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2, (s.gpr .x1).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ∈ hintParams ∧ VG.Proof.MlDsa.AArch64.Pack.wArg s .x2 ≤ (s.gpr .x1).toNat ∧
    (s.gpr .x4).toNat = 256 * ((s.gpr .x1).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2)
  post s s' :=
    match hintBitUnpack (VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) ((s.gpr .x1).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
    | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (s.gpr .x3) ((s.gpr .x1).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s .x2) hint
    | none => (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    leakBytes (bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat)

/-- The sign bit of `x - y`, tested by `cbnz`: `x < y`. -/
theorem nz_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    ((x - y) >>> 63 != 0) = decide (x.toNat < y.toNat) := by
  rw [ne_zero_iff, sub_lsr63 hx hy]
  by_cases h : x.toNat < y.toNat <;> simp [h]

/-- The sign bits of `x - y` and `z - w`, or'ed: `x < y` or `z < w`. -/
theorem nz_or {x y z w : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) (hz : z.toNat < 2 ^ 63)
    (hw : w.toNat < 2 ^ 63) :
    ((x - y ||| z - w) >>> 63 != 0) = decide (x.toNat < y.toNat ∨ z.toNat < w.toNat) := by
  rw [BitVec.ushiftRight_or_distrib, ne_zero_iff, BitVec.toNat_or, sub_lsr63 hx hy, sub_lsr63 hz hw]
  by_cases h₁ : x.toNat < y.toNat <;> by_cases h₂ : z.toNat < w.toNat <;> simp [h₁, h₂]

theorem toNat_ofNat_small {a : Nat} (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toNat = a :=
  VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by omega)

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-- The arguments. -/
abbrev uω (s₀ : State) : Nat := VG.Proof.MlDsa.AArch64.Pack.wArg s₀ .x2
abbrev uk (s₀ : State) : Nat := (s₀.gpr .x1).toNat - VG.Proof.MlDsa.AArch64.Pack.wArg s₀ .x2
abbrev uLen (s₀ : State) : Nat := (s₀.gpr .x1).toNat
abbrev uY (s₀ : State) : Array Byte := (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray
/-- The region of `h`. -/
abbrev uR (s₀ : State) : Region := ⟨s₀.gpr .x3, (s₀.gpr .x4).toNat * 4⟩

include hp in
theorem up_facts : 4 ≤ VG.Proof.MlDsa.AArch64.Pack.uk s₀ ∧ VG.Proof.MlDsa.AArch64.Pack.uk s₀ ≤ 8 ∧ VG.Proof.MlDsa.AArch64.Pack.uω s₀ ≤ 80 ∧ VG.Proof.MlDsa.AArch64.Pack.uω s₀ + VG.Proof.MlDsa.AArch64.Pack.uk s₀ = VG.Proof.MlDsa.AArch64.Pack.uLen s₀ ∧
    (s₀.gpr .x4).toNat = 256 * VG.Proof.MlDsa.AArch64.Pack.uk s₀ := by
  have := mem_hintParams hp.2.2.2.1
  have := hp.2.2.2.2.1
  have := hp.2.2.2.2.2
  simp only [VG.Proof.MlDsa.AArch64.Pack.uk, VG.Proof.MlDsa.AArch64.Pack.uω, VG.Proof.MlDsa.AArch64.Pack.uLen] at *
  omega

/-! ## Zeroing `h` -/

/-- What `hbuInit` leaves. -/
def hbuInitPost (s₀ s : State) : Prop :=
  (∀ t < (s₀.gpr .x4).toNat, coeffAt s.mem (s₀.gpr .x3) t = 0) ∧ VG.Frame [VG.Proof.MlDsa.AArch64.Pack.uR s₀] s₀.mem s.mem ∧
    s.gpr .x9 = s₀.gpr .x0 ∧ s.gpr .x3 = s₀.gpr .x3 ∧ s.gpr .x2 = s₀.gpr .x1 - (s₀.gpr .x4 >>> 8) ∧
    s.gpr .x12 = s₀.gpr .x4 >>> 8 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp

include hp in
theorem hbuInit_ok : WP isa hbuInit s₀ (VG.Proof.MlDsa.AArch64.Pack.hbuInitPost s₀) := by
  obtain ⟨hk4, hk8, -, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  have hwr := hp.2.1
  have hl := (s₀.gpr .x4).isLt
  unfold hbuInit hbuPro
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_movz fun s₃ o₃ e₃ =>
    VG.Proof.MlKem.AArch64.wp_mov fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_mov fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_mov fun s₆ o₆ e₆ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₆ := ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆
  have x15 : s₆.gpr .x15 = 0 := by rw [o₆.get .x15, o₅.get .x15, o₄.get .x15, e₃]; rfl
  refine WP.mono (count_loop (n := (s₀.gpr .x4).toNat) (by omega) (fun t s =>
      s.gpr .x10 = s₀.gpr .x3 + BitVec.ofNat 64 (4 * t) ∧
      (s.gpr .x8).toNat = (s₀.gpr .x4).toNat - t ∧ Keep [.x8, .x10] s₆ s ∧ VG.Frame [VG.Proof.MlDsa.AArch64.Pack.uR s₀] s₀.mem s.mem ∧
      ∀ u < t, coeffAt s.mem (s₀.gpr .x3) u = 0)
    (fun t ht s ⟨h10, h8, hk, hf, hz⟩ => ?_)
    ⟨by rw [o₆.get .x10, e₅, o₄.get .x3, o₃.get .x3, o₂.get .x3, o₁.get .x3, Nat.mul_zero, ptr_zero],
      (by rw [e₆, o₅.get .x4, o₄.get .x4, o₃.get .x4, o₂.get .x4, o₁.get .x4, Nat.sub_zero]), Keep.refl _ _,
      by rw [k₆.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s ⟨_, _, hk, hf, hz⟩ => ⟨hz, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : (VG.Proof.MlDsa.AArch64.Pack.uR s₀).Contains (coeffAddr (s₀.gpr .x3) t) 4 := Offset.contains_base _ (by omega) (by omega)
    refine wp_strw ⟨by decide, by decide⟩ (by rw [h10, ptr_zero]) (by rw [hk.wr, k₆.wr, hwr]; exact ⟨_, .head _, hc⟩)
      fun s₁ h₁ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil
        ⟨⟨by rw [o₃.get .x10, e₂, h₁.gpr, h10, ptr_add, show 4 * t + 4 = 4 * (t + 1) by omega],
          by rw [e₃, o₂.get .x8, h₁.gpr]; exact VG.Proof.MlDsa.AArch64.Pack.count_step h8 ht,
          ((hk.trans h₁.keep).trans (o₂.keep.trans o₃.keep)).mono, ?_, fun u hu => ?_⟩, ?_⟩
    · rw [o₃.mem, o₂.mem, h₁.mem]
      exact hf.writeW (List.mem_singleton_self _) _ hc
    · rw [o₃.mem, o₂.mem, h₁.mem, coeffAt_writeW _ _ (by omega) (by omega)]
      by_cases e : t = u
      · subst e; rw [ite_eq_left rfl, hk.get .x15, x15]; rfl
      · rw [ite_eq_right e]; exact hz u (by omega)
    · rw [e₃, o₂.get .x8, h₁.gpr, VG.Proof.MlDsa.AArch64.Pack.count_step h8 ht]; omega
  · rw [hk.get .x9, o₆.get .x9, o₅.get .x9, e₄, o₃.get .x0, o₂.get .x0, o₁.get .x0]
  · rw [hk.get .x3, k₆.get .x3]
  · rw [hk.get .x2, o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, e₂, o₁.get .x1, e₁]
  · rw [hk.get .x12, o₆.get .x12, o₅.get .x12, o₄.get .x12, o₃.get .x12, o₂.get .x12, e₁]
  · rw [hk.rd, k₆.rd]
  · rw [hk.wr, k₆.wr]
  · rw [hk.sp, k₆.sp]

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = VG.Proof.MlDsa.AArch64.Pack.uk s₀ ∧ ∀ i < VG.Proof.MlDsa.AArch64.Pack.uk s₀, ∀ j < 256,
    coeffAt m (s₀.gpr .x3) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `x5`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .x5 = BitVec.ofNat 64 idx ∧ idx ≤ VG.Proof.MlDsa.AArch64.Pack.uω s₀ ∧ VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s.mem hA
  | none, s => s.gpr .x5 = BitVec.ofNat 64 256

/-- What stays the same from the loops on. -/
structure UCom (s₀ : State) (s : State) : Prop where
  x9 : s.gpr .x9 = s₀.gpr .x0
  x2 : s.gpr .x2 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.uω s₀)
  x15 : s.gpr .x15 = BitVec.ofNat 64 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.uR s₀] s₀.mem s.mem

theorem UCom.of_keep {s₀ s s' : State} (h : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (hm : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.uR s₀] s.mem s'.mem) (h9 : Reg.x9 ∉ rs := by decide) (h2 : Reg.x2 ∉ rs := by decide)
    (h15 : Reg.x15 ∉ rs := by decide) : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' :=
  ⟨(hk.gpr _ h9).trans h.x9, (hk.gpr _ h2).trans h.x2, (hk.gpr _ h15).trans h.x15, hk.rd.trans h.rd,
    hk.wr.trans h.wr, hk.sp.trans h.sp, h.frame.trans hm⟩

theorem UCom.of_only {s₀ s s' : State} (h : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s) {rs : List Reg} (hk : Only rs s s')
    (h9 : Reg.x9 ∉ rs := by decide) (h2 : Reg.x2 ∉ rs := by decide) (h15 : Reg.x15 ∉ rs := by decide) :
    VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' :=
  h.of_keep hk.keep (by rw [hk.mem]; exact Frame.refl _ _) h9 h2 h15

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s
  x3 : s.gpr .x3 = s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i)
  x6 : s.gpr .x6 = s₀.gpr .x0 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i)
  x7 : s.gpr .x7 = BitVec.ofNat 64 bound
  x12 : (s.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.uk s₀ - i

theorem PCom.of_keep {s₀ s s' : State} {i bound : Nat} (h : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s) {rs : List Reg}
    (hk : Keep rs s s') (hm : VG.Frame [VG.Proof.MlDsa.AArch64.Pack.uR s₀] s.mem s'.mem)
    (hrs : ∀ r ∈ rs, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x15 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x12 := by decide) :
    VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' :=
  ⟨h.com.of_keep hk hm (fun h' => (hrs _ h').1 rfl) (fun h' => (hrs _ h').2.1 rfl)
      (fun h' => (hrs _ h').2.2.1 rfl),
    (hk.gpr _ fun h' => (hrs _ h').2.2.2.1 rfl).trans h.x3, (hk.gpr _ fun h' => (hrs _ h').2.2.2.2.1 rfl).trans h.x6,
    (hk.gpr _ fun h' => (hrs _ h').2.2.2.2.2.1 rfl).trans h.x7,
    by rw [hk.gpr _ fun h' => (hrs _ h').2.2.2.2.2.2 rfl]; exact h.x12⟩

theorem PCom.of_only {s₀ s s' : State} {i bound : Nat} (h : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s) {rs : List Reg}
    (hk : Only rs s s')
    (hrs : ∀ r ∈ rs, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x15 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x12 := by decide) :
    VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' :=
  h.of_keep hk.keep (by rw [hk.mem]; exact Frame.refl _ _) hrs

include hp in
theorem harr_set {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.AArch64.Pack.HArr s₀ m hA) {i b : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀)
    (hb : b < 256) :
    VG.Proof.MlDsa.AArch64.Pack.HArr s₀ (m.writeW (coeffAddr (s₀.gpr .x3) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

include hp in
theorem harr_zero {m : Mem} (hz : ∀ t < (s₀.gpr .x4).toNat, coeffAt m (s₀.gpr .x3) t = 0) :
    VG.Proof.MlDsa.AArch64.Pack.HArr s₀ m (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.uk s₀) noHint) := by
  obtain ⟨-, -, -, -, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

include hp in
/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s) {t : Nat} (ht : t < VG.Proof.MlDsa.AArch64.Pack.uLen s₀) :
    s.mem (s₀.gpr .x0 + BitVec.ofNat 64 t) = (VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD t 0 := by
  have hl := (s₀.gpr .x1).isLt
  have e1 : VG.Proof.MlDsa.AArch64.Pack.uLen s₀ = (s₀.gpr .x1).toNat := rfl
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.2.2.1 _ (Offset.contains_base _ (by omega) (by omega)) hc'

include hp in
/-- Loading `y[t]` at `x9 + x5`. -/
theorem yLoad_ok {r : Reg} {t : Nat} (ht : t < VG.Proof.MlDsa.AArch64.Pack.uLen s₀) {s : State} (hc : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 t) :
    WP isa (.block [.add .x .x13 .x9 .x5, .ldrb r .x13 0]) s fun s' =>
      s'.gpr r = BitVec.ofNat 64 ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD t 0).toNat ∧ Only [.x13, r] s s' := by
  have hl := (s₀.gpr .x1).isLt
  have e1 : VG.Proof.MlDsa.AArch64.Pack.uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hrd := hp.1
  refine VG.Proof.MlKem.AArch64.wp_add fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_ldrb (by decide) (by rw [e₁, hc.x9, h5, ptr_zero])
    (by rw [o₁.rd, o₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, .head _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ⟨?_, o₁.trans o₂⟩
  rw [e₂, o₁.mem, VG.Proof.MlDsa.AArch64.Pack.yByte hp hc ht]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD t 0).isLt; omega)]

/-! ## The coefficients of a polynomial -/

/-- The previous coefficient of the polynomial plus one, or 0 at its first. -/
def prevV (y : Array Byte) (first idx : Nat) : Nat := if first < idx then (y.getD (idx - 1) 0).toNat + 1 else 0

theorem huStep_eq (y : Array Byte) (i first : Nat) (hA : Array (Vector Bool n)) (idx x : Nat) :
    huStep y i first (hA, idx) x =
      if (y.getD idx 0).toNat < VG.Proof.MlDsa.AArch64.Pack.prevV y first idx then none
      else some (huSet i (y.getD idx 0).toNat hA, idx + 1) := by
  unfold huStep VG.Proof.MlDsa.AArch64.Pack.prevV
  by_cases h : first < idx
  · rw [ite_pos' h]
    by_cases h' : (y.getD (idx - 1) 0).toNat ≥ (y.getD idx 0).toNat
    · rw [ite_pos' ⟨h, h'⟩, ite_pos' (by omega)]
    · rw [ite_neg' (fun e => h' e.2), ite_neg' (by omega)]
  · rw [ite_neg' h, ite_neg' (fun e => h e.1), ite_neg' (Nat.not_lt_zero _)]

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

include hp in
/-- Setting coefficient `v` of polynomial `i`. -/
theorem set_ok {i bound idx v : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀) (hv : v < 256) {hA : Array (Vector Bool n)}
    {s : State} (hP : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 idx)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 v) (hh : VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s.mem hA) :
    WP isa (.block hbuSet) s fun s' =>
      VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' ∧ s'.gpr .x5 = BitVec.ofNat 64 (idx + 1) ∧ s'.gpr .x11 = BitVec.ofNat 64 (v + 1) ∧
        VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s'.mem (huSet i v hA) := by
  obtain ⟨hk4, hk8, -, -, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  have hwr := hp.2.1
  have ha : s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i) + BitVec.ofNat 64 v <<< 2 =
      coeffAddr (s₀.gpr .x3) (256 * i + v) := by
    rw [show BitVec.ofNat 64 v <<< 2 = BitVec.ofNat 64 (4 * v) by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_lsl_n (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega,
      ptr_add, coeffAddr, show 1024 * i + 4 * v = 4 * (256 * i + v) by omega]
  have hin : (VG.Proof.MlDsa.AArch64.Pack.uR s₀).Contains (coeffAddr (s₀.gpr .x3) (256 * i + v)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  unfold hbuSet
  refine wp_lsl (by decide) fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_add fun s₂ o₂ e₂ =>
    wp_strw ⟨by decide, by decide⟩ (by rw [e₂, o₁.get .x3, e₁, hP.x3, h10, ptr_zero, ha])
      (by rw [o₂.wr, o₁.wr, hP.com.wr, hwr]; exact ⟨_, .head _, hin⟩) fun s₃ h₃ =>
    VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₅ := (((o₁.keep.trans o₂.keep).trans h₃.keep).trans o₄.keep).trans o₅.keep
  have m₅ : s₅.mem = s.mem.writeW (coeffAddr (s₀.gpr .x3) (256 * i + v)) (1 : BitVec 32) := by
    rw [o₅.mem, o₄.mem, h₃.mem, o₂.mem, o₁.mem, o₂.get .x15, o₁.get .x15, hP.com.x15]; rfl
  refine ⟨hP.of_keep k₅ (by rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin),
    by rw [o₅.get .x5, e₄, h₃.gpr, o₂.get .x5, o₁.get .x5, h5, VG.Proof.MlDsa.AArch64.Pack.ofNat_succ64],
    by rw [e₅, o₄.get .x10, h₃.gpr, o₂.get .x10, o₁.get .x10, h10, VG.Proof.MlDsa.AArch64.Pack.ofNat_succ64], by rw [m₅]; exact VG.Proof.MlDsa.AArch64.Pack.harr_set hp hh hi hv⟩

/-- A failed check. -/
theorem fail_ok (s : State) :
    WP isa hbuFail s fun s' => s'.gpr .x5 = BitVec.ofNat 64 256 ∧ Only [.x5] s s' :=
  VG.Proof.MlKem.AArch64.wp_movz fun _ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_nil ⟨by rw [e₁]; rfl, o₁⟩

/-- `x10 ← 1` if `x5 < r`, else 0. -/
theorem cmp_ok {r : Reg} (s : State) (hr : (s.gpr r).toNat < 2 ^ 63) (h5 : (s.gpr .x5).toNat < 2 ^ 63) :
    WP isa (.block [.sub .x .x10 .x5 r, .lsr .x .x10 .x10 63]) s fun s' =>
      (s'.gpr .x10 != 0) = decide ((s.gpr .x5).toNat < (s.gpr r).toNat) ∧ Only [.x10] s s' :=
  VG.Proof.MlKem.AArch64.wp_sub fun _ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun _ o₂ e₂ =>
    VG.Proof.MlKem.AArch64.wp_nil ⟨by rw [e₂, e₁, VG.Proof.MlDsa.AArch64.Pack.nz_lt h5 hr], (o₁.trans o₂).mono⟩

include hp in
/-- Coefficient `idx` of polynomial `i`, checked against the previous one. -/
theorem ucoef_ok {i bound first idx : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀) (hfi : first ≤ idx) (hib : idx < bound) (hbω : bound ≤ VG.Proof.MlDsa.AArch64.Pack.uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 idx)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.prevV (VG.Proof.MlDsa.AArch64.Pack.uY s₀) first idx)) (hh : VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s.mem hA) :
    WP isa hbuCoef s fun s' => VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' ∧
      (match huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA, idx) 0 with
        | some (hA', idx') => s'.gpr .x5 = BitVec.ofNat 64 idx' ∧
          s'.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.prevV (VG.Proof.MlDsa.AArch64.Pack.uY s₀) first idx') ∧ VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s'.mem hA' ∧
          (s'.gpr .x10 != 0) = decide (idx' < bound)
        | none => s'.gpr .x5 = BitVec.ofNat 64 256 ∧ (s'.gpr .x10 != 0) = false) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  have hv := ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD idx 0).isLt
  have hpv : VG.Proof.MlDsa.AArch64.Pack.prevV (VG.Proof.MlDsa.AArch64.Pack.uY s₀) first idx ≤ 256 := by
    unfold VG.Proof.MlDsa.AArch64.Pack.prevV; split
    · have := ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (idx - 1) 0).isLt; omega
    · omega
  unfold hbuCoef
  rw [show ([.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0, .sub .x .x14 .x10 .x11, .lsr .x .x14 .x14 63] : List Instr) =
    [.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0] ++ [.sub .x .x14 .x10 .x11, .lsr .x .x14 .x14 63] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.yLoad_ok hp (r := .x10) (by omega) hP.com h5) fun s₁ ⟨h10₁, o₁⟩ =>
    VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₃ := (o₁.trans o₂).trans o₃
  have hP₃ : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s₃ := hP.of_only k₃
  have hc : (s₃.gpr .x14 != 0) = decide (((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD idx 0).toNat < VG.Proof.MlDsa.AArch64.Pack.prevV (VG.Proof.MlDsa.AArch64.Pack.uY s₀) first idx) := by
    rw [e₃, e₂, o₁.get .x11, h11, h10₁, VG.Proof.MlDsa.AArch64.Pack.nz_lt (by rw [VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
      (by rw [VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  refine WP.seq (WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₃ .x14) (fun hf => ?_) (fun hs => ?_))
  · -- Not above the previous one: fail.
    rw [hc] at hf
    have hn : huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA, idx) 0 = none := by rw [VG.Proof.MlDsa.AArch64.Pack.huStep_eq, ite_pos' (of_decide_eq_true hf)]
    rw [hn]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.fail_ok s₃) fun s₄ ⟨h5₄, o₄⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x7) s₄ (by rw [o₄.get .x7, hP₃.x7, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
      (by rw [h5₄, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by decide)]; decide)) fun s₅ ⟨c₅, o₅⟩ =>
      ⟨hP₃.of_only (o₄.trans o₅), by rw [o₅.get .x5, h5₄], ?_⟩
    rw [c₅, h5₄, o₄.get .x7, hP₃.x7, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by decide), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
    exact decide_eq_false (by omega)
  · -- Set it.
    rw [hc] at hs
    have hs' := of_decide_eq_false hs
    have hn : huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA, idx) 0 =
        some (huSet i ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD idx 0).toNat hA, idx + 1) := by rw [VG.Proof.MlDsa.AArch64.Pack.huStep_eq, ite_neg' hs']
    rw [hn]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.set_ok hp hi hv (idx := idx) (hA := hA) (hP := hP₃) (by rw [k₃.get .x5, h5]) (by rw [o₃.get .x10, o₂.get .x10, h10₁])
      (by rw [k₃.mem]; exact hh)) fun s₄ ⟨hP₄, h5₄, h11₄, hh₄⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x7) s₄ (by rw [hP₄.x7, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
      (by rw [h5₄, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)) fun s₅ ⟨c₅, o₅⟩ =>
      ⟨hP₄.of_only o₅, by rw [o₅.get .x5, h5₄], ?_, by rw [o₅.mem]; exact hh₄, ?_⟩
    · rw [o₅.get .x11, h11₄, VG.Proof.MlDsa.AArch64.Pack.prevV, ite_pos' (by omega), Nat.add_sub_cancel]
    · rw [c₅, h5₄, hP₄.x7, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .x5 = BitVec.ofNat 64 idx ∧ VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s.mem hA
  | none, s => s.gpr .x5 = BitVec.ofNat 64 256

include hp in
/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ VG.Proof.MlDsa.AArch64.Pack.uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 first)
    (hh : VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s.mem hA) :
    WP isa hbuCoefs s fun s' => VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' ∧
      VG.Proof.MlDsa.AArch64.Pack.SIn s₀ bound (optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first) (List.range (bound - first)) (hA, first)) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  unfold hbuCoefs
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₃ := (o₁.trans o₂).trans o₃
  have hP₃ : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s₃ := hP.of_only k₃
  have h5₃ : s₃.gpr .x5 = BitVec.ofNat 64 first := by rw [k₃.get .x5, h5]
  have hc : (s₃.gpr .x10 != 0) = decide (first < bound) := by
    rw [e₃, e₂, o₁.get .x5, o₁.get .x7, h5, hP.x7, VG.Proof.MlDsa.AArch64.Pack.nz_lt (by rw [VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
      (by rw [VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  refine WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₃ .x10) (fun hlt => ?_) (fun hge => ?_)
  · -- The coefficients, while the index is less than the bound.
    rw [hc] at hlt
    have hlt := of_decide_eq_true hlt
    refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧
        optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first) (List.range t) (hA, first) = some (hA', idx') ∧ idx' = first + t ∧
        idx' < bound ∧ VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i bound s' ∧ s'.gpr .x5 = BitVec.ofNat 64 idx' ∧
        s'.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.prevV (VG.Proof.MlDsa.AArch64.Pack.uY s₀) first idx') ∧ VG.Proof.MlDsa.AArch64.Pack.HArr s₀ s'.mem hA')
      (fun m s' ⟨t, hA', idx', hm, hF, hidx, hlt', hP', h5', h11', hh'⟩ => ?_) _ s₃
      ⟨0, hA, first, rfl, rfl, rfl, hlt, hP₃, h5₃, by rw [o₃.get .x11, o₂.get .x11, e₁]; unfold VG.Proof.MlDsa.AArch64.Pack.prevV; rw [ite_neg' (Nat.lt_irrefl _)]; rfl,
        by rw [k₃.mem]; exact hh⟩
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.ucoef_ok hp hi (by omega) hlt' hbω hP' h5' h11' hh') fun s'' ⟨hP'', hm''⟩ => ?_
    have hF1 : optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) =
        huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
    have hst : huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA', idx') t = huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA', idx') 0 := by
      rw [VG.Proof.MlDsa.AArch64.Pack.huStep_eq, VG.Proof.MlDsa.AArch64.Pack.huStep_eq]
    cases hs : huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first (hA', idx') 0 with
    | none =>
      rw [hs] at hm''
      obtain ⟨h5'', c''⟩ := hm''
      refine .inl ⟨by rw [VG.Proof.MlKem.AArch64.eval_nonzero, c''], hP'', ?_⟩
      have : optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) = none := by
        rw [hF1, hst]; exact hs
      rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
      exact h5''
    | some st =>
      rw [hs] at hm''
      obtain ⟨hA'', idx''⟩ := st
      obtain ⟨h5'', h11'', hh'', c''⟩ := hm''
      have hi'' : idx'' = idx' + 1 := VG.Proof.MlDsa.AArch64.Pack.huStep_idx hs
      have hF2 : optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) = some (hA'', idx'') := by
        rw [hF1, hst]; exact hs
      by_cases e : idx'' < bound
      · refine .inr ⟨by rw [VG.Proof.MlKem.AArch64.eval_nonzero, c'', decide_eq_true e], bound - idx'', by omega, t + 1, hA'', idx'', rfl,
          hF2, by omega, e, hP'', h5'', h11'', hh''⟩
      · refine .inl ⟨by rw [VG.Proof.MlKem.AArch64.eval_nonzero, c'', decide_eq_false e], hP'', ?_⟩
        rw [show bound - first = t + 1 by omega, hF2]
        exact ⟨by omega, h5'', hh''⟩
  · -- No coefficient.
    rw [hc] at hge
    have hge := of_decide_eq_false hge
    refine WP.block_nil ⟨hP₃, ?_⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, h5₃, by rw [k₃.mem]; exact hh⟩

/-! ## A polynomial -/

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (VG.Proof.MlDsa.AArch64.Pack.uω s₀) (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range i) (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s
  x3 : s.gpr .x3 = s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i)
  x6 : s.gpr .x6 = s₀.gpr .x0 + BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i)
  x12 : (s.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.uk s₀ - i
  st : VG.Proof.MlDsa.AArch64.Pack.SRel s₀ (VG.Proof.MlDsa.AArch64.Pack.huS s₀ i) s

include hp in
/-- Polynomial `i`: its checks and coefficients; after a failed check, fails again. -/
theorem upolyBody_ok {i : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀) {s : State} (hI : VG.Proof.MlDsa.AArch64.Pack.OInv s₀ i s) :
    WP isa hbuPoly s fun s' => VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' ∧ s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x6 ∧
      s'.gpr .x12 = s.gpr .x12 ∧ VG.Proof.MlDsa.AArch64.Pack.SRel s₀ (VG.Proof.MlDsa.AArch64.Pack.huS s₀ (i + 1)) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  have hl := (s₀.gpr .x1).isLt
  have e1 : VG.Proof.MlDsa.AArch64.Pack.uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hrd := hp.1
  have hsucc : VG.Proof.MlDsa.AArch64.Pack.huS s₀ (i + 1) = (VG.Proof.MlDsa.AArch64.Pack.huS s₀ i).bind fun st => huPoly (VG.Proof.MlDsa.AArch64.Pack.uω s₀) (VG.Proof.MlDsa.AArch64.Pack.uY s₀) st i := optFold_range_succ _ _ _
  unfold hbuPoly
  -- The bound.
  have hbl := ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).isLt
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_ldrb (by decide) (by rw [hI.x6, ptr_zero])
    (by rw [hI.com.rd, hI.com.wr, hrd]; exact ⟨_, .head _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_sub fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_sub fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_orr fun s₄ o₄ e₄ =>
      VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₅ o₅ e₅ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  have hc₅ : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s₅ := hI.com.of_only k₅
  have hb : s₁.gpr .x7 = BitVec.ofNat 64 ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat := by
    rw [e₁, VG.Proof.MlDsa.AArch64.Pack.yByte hp hI.com (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb2 : (s₁.gpr .x7).toNat = ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat := by rw [hb, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  have hx5 : (s.gpr .x5).toNat ≤ 256 := by
    have := hI.st
    revert this
    cases VG.Proof.MlDsa.AArch64.Pack.huS s₀ i with
    | none => intro h; rw [VG.Proof.MlDsa.AArch64.Pack.SRel] at h; rw [h, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by decide)]
    | some st => obtain ⟨hA, idx⟩ := st; intro ⟨h, h', _⟩; rw [h, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega
  have hω2 : (s₁.gpr .x2).toNat = VG.Proof.MlDsa.AArch64.Pack.uω s₀ := by rw [o₁.get .x2, hI.com.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  have hc : (s₅.gpr .x10 != 0) =
      decide (((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat < (s.gpr .x5).toNat ∨ VG.Proof.MlDsa.AArch64.Pack.uω s₀ < ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat) := by
    rw [e₅, e₄, o₃.get .x10, e₃, e₂, o₂.get .x7, o₁.get .x5, o₂.get .x2,
      VG.Proof.MlDsa.AArch64.Pack.nz_or (by omega) (by omega) (by omega) (by omega), hb2, hω2]
  have hkeep : ∀ {s' : State} {rs : List Reg}, Keep rs s₅ s' → Reg.x3 ∉ rs → Reg.x6 ∉ rs → Reg.x12 ∉ rs →
      s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x6 ∧ s'.gpr .x12 = s.gpr .x12 := fun hk h3 h6 h12 =>
    ⟨by rw [hk.gpr _ h3, k₅.get .x3], by rw [hk.gpr _ h6, k₅.get .x6], by rw [hk.gpr _ h12, k₅.get .x12]⟩
  refine WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₅ .x10) (fun hf => ?_) (fun hs => ?_)
  · -- A failed check, now or before.
    rw [hc] at hf
    have hf := of_decide_eq_true hf
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.fail_ok s₅) fun s₆ ⟨h5₆, o₆⟩ => ?_
    obtain ⟨k3, k6, k12⟩ := hkeep o₆.keep (by decide) (by decide) (by decide)
    refine ⟨hc₅.of_only o₆, k3, k6, k12, ?_⟩
    rw [hsucc]
    have := hI.st
    revert this
    cases VG.Proof.MlDsa.AArch64.Pack.huS s₀ i with
    | none => intro _; exact h5₆
    | some st =>
      obtain ⟨hA, idx⟩ := st
      intro ⟨h5, _, _⟩
      rw [h5, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)] at hf
      simp only [Option.bind_some, huPoly]
      rw [ite_pos' hf]
      exact h5₆
  · -- The coefficients.
    rw [hc] at hs
    have hs := of_decide_eq_false hs
    have hst := hI.st
    revert hst
    cases hS : VG.Proof.MlDsa.AArch64.Pack.huS s₀ i with
    | none =>
      intro h5
      rw [VG.Proof.MlDsa.AArch64.Pack.SRel] at h5
      rw [h5, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by decide)] at hs
      omega
    | some st =>
      obtain ⟨hA, idx⟩ := st
      intro ⟨h5, hidx, hh⟩
      rw [h5, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)] at hs
      have hP₅ : VG.Proof.MlDsa.AArch64.Pack.PCom s₀ i ((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat s₅ :=
        ⟨hc₅, by rw [k₅.get .x3, hI.x3], by rw [k₅.get .x6, hI.x6], by rw [o₅.get .x7, o₄.get .x7, o₃.get .x7,
          o₂.get .x7, hb], by rw [k₅.get .x12, hI.x12]⟩
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.coefs_ok hp hi (first := idx) (hA := hA) (by omega) (by omega) hP₅ (by rw [k₅.get .x5, h5])
        (by rw [k₅.mem]; exact hh)) fun s₆ ⟨hP₆, hin₆⟩ => ⟨hP₆.com, by rw [hP₆.x3, hI.x3], by rw [hP₆.x6, hI.x6],
          ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq; rw [hP₆.x12, hI.x12]
      · rw [hsucc, hS]
        simp only [Option.bind_some, huPoly]
        rw [ite_neg' hs]
        revert hin₆
        cases optFold (huStep (VG.Proof.MlDsa.AArch64.Pack.uY s₀) i idx) (List.range (((VG.Proof.MlDsa.AArch64.Pack.uY s₀).getD (VG.Proof.MlDsa.AArch64.Pack.uω s₀ + i) 0).toNat - idx)) (hA, idx) with
        | none => exact id
        | some st => obtain ⟨hA', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩

include hp in
/-- Polynomial `i`, and the pointers and count to the next. -/
theorem upoly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.AArch64.Pack.uk s₀) {s : State} (hI : VG.Proof.MlDsa.AArch64.Pack.OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.addImm .x .x6 .x6 1, .addImm .x .x3 .x3 1024, .subImm .x .x12 .x12 1])) s
      fun s' => VG.Proof.MlDsa.AArch64.Pack.OInv s₀ (i + 1) s' ∧ ((s'.gpr .x12).toNat ≠ 0 ↔ i + 1 ≠ VG.Proof.MlDsa.AArch64.Pack.uk s₀) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.upolyBody_ok hp hi hI) fun s₁ ⟨hc₁, h3, h6, h12, st₁⟩ => ?_)
  refine VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ =>
    VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₄ o₄ e₄ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₄ := (o₂.trans o₃).trans o₄
  have c12 : (s₄.gpr .x12).toNat = VG.Proof.MlDsa.AArch64.Pack.uk s₀ - (i + 1) := by
    rw [e₄, o₃.get .x12, o₂.get .x12, h12]; exact VG.Proof.MlDsa.AArch64.Pack.count_step hI.x12 hi
  refine ⟨⟨hc₁.of_only k₄, ?_, ?_, c12, ?_⟩, by rw [c12]; omega⟩
  · rw [o₄.get .x3, e₃, o₂.get .x3, h3, hI.x3, ptr_add, show 1024 * i + 1024 = 1024 * (i + 1) by omega]
  · rw [o₄.get .x6, o₃.get .x6, e₂, h6, hI.x6, ptr_add, Nat.add_assoc]
  · revert st₁
    cases VG.Proof.MlDsa.AArch64.Pack.huS s₀ (i + 1) with
    | none => exact fun h => by rw [VG.Proof.MlDsa.AArch64.Pack.SRel] at h ⊢; rw [k₄.get .x5, h]
    | some st => obtain ⟨hA, idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [k₄.get .x5, h1], h2, by rw [k₄.mem]; exact h3⟩

end

end VG.Proof.MlDsa.AArch64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_unpack`

The polynomials (`HintUnpackPoly.lean`), then the bytes from the index up to
`ω`, which must be zero, and the return value: 1 if no check failed (the index
is at most `ω`), 0 otherwise.

Constant time but for its input: once `h` is zeroed, the two runs agree on
all the memory the function may access (the input `y`, which the contract
lets it leak, and `h`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_addImm wp_movz wp_eor wp_nil eval_nonzero
  ne_zero_iff toNat_ofNat_lt ptr_add ptr_zero count_loop abi_of agree_of)
open VG.Proof.MlKem (bytesAt_getD bytesAt_length)
open VG.Proof.MlDsa.Pack

theorem nz_byte (b : Byte) : (BitVec.ofNat 64 b.toNat != 0) = decide (b ≠ 0) := by
  rw [ne_zero_iff, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by have := b.isLt; omega)]
  exact decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl), fun h e => h (BitVec.eq_of_toNat_eq e)⟩

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-! ## The bytes after the last index -/

include hp in
/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ VG.Proof.MlDsa.AArch64.Pack.uω s₀) {s : State} (hc : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx)) () with
        | some _ => s'.gpr .x5 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.uω s₀)
        | none => s'.gpr .x5 = BitVec.ofNat 64 256) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  have hω2 : (s.gpr .x2).toNat = VG.Proof.MlDsa.AArch64.Pack.uω s₀ := by rw [hc.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x2) s (by omega) (by rw [h5, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega))
    fun s₁ ⟨c₁, o₁⟩ => ?_)
  rw [h5, hω2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)] at c₁
  have hc₁ : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s₁ := hc.of_only o₁
  refine WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₁ .x10) (fun hlt => ?_) (fun hge => ?_)
  · rw [c₁] at hlt
    have hlt := of_decide_eq_true hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx - u ∧ idx + u < VG.Proof.MlDsa.AArch64.Pack.uω s₀ ∧
        optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx u) () = some () ∧ s'.gpr .x5 = BitVec.ofNat 64 (idx + u) ∧
        VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' ∧ s'.mem = s.mem)
      (fun m s' ⟨u, hm, hu, hF, h5', hc', hm'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [o₁.get .x5, h5]; rfl, hc₁, o₁.mem⟩
    unfold hbuTrailByte
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.yLoad_ok hp (r := .x10) (t := idx + u) (by omega) hc' h5') fun s₂ ⟨h10₂, o₂⟩ => ?_)
    have hc₂ : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s₂ := hc'.of_only o₂
    have hF1 : optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx (u + 1)) () = huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀) () (idx + u) := by
      rw [optFold_range'_succ, hF]; rfl
    refine WP.seq (WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₂ .x10) (fun hne => ?_) (fun heq => ?_))
    · -- A nonzero byte: fail.
      rw [h10₂, VG.Proof.MlDsa.AArch64.Pack.nz_byte] at hne
      have hne := of_decide_eq_true hne
      have hn : optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.fail_ok s₂) fun s₃ ⟨h5₃, o₃⟩ => ?_
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x2) s₃ (by rw [o₃.get .x2, hc₂.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
        (by rw [h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide)]; decide)) fun s₄ ⟨c₄, o₄⟩ => .inl ⟨?_, ?_⟩
      · rw [VG.Proof.MlKem.AArch64.eval_nonzero, c₄, h5₃, o₃.get .x2, hc₂.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
        exact congrArg some (decide_eq_false (by omega))
      · refine ⟨hc₂.of_only (o₃.trans o₄), by rw [o₄.mem, o₃.mem, o₂.mem, hm'], ?_⟩
        rw [hn]; rw [o₄.get .x5, h5₃]
    · -- A zero byte: next.
      rw [h10₂, VG.Proof.MlDsa.AArch64.Pack.nz_byte] at heq
      have heq := of_decide_eq_false heq
      have hF2 : optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' heq]
      refine VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil ?_
      have h5₃ : s₃.gpr .x5 = BitVec.ofNat 64 (idx + (u + 1)) := by
        rw [e₃, o₂.get .x5, h5', VG.Proof.MlDsa.AArch64.Pack.ofNat_succ64, Nat.add_assoc]
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x2) s₃ (by rw [o₃.get .x2, hc₂.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
        (by rw [h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)) fun s₄ ⟨c₄, o₄⟩ => ?_
      have hc₄ : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s₄ := hc₂.of_only (o₃.trans o₄)
      rw [h5₃, o₃.get .x2, hc₂.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)] at c₄
      have h5₄ : s₄.gpr .x5 = BitVec.ofNat 64 (idx + (u + 1)) := by rw [o₄.get .x5, h5₃]
      have hm₄ : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, hm']
      by_cases e : idx + (u + 1) < VG.Proof.MlDsa.AArch64.Pack.uω s₀
      · exact .inr ⟨by rw [VG.Proof.MlKem.AArch64.eval_nonzero, c₄, decide_eq_true e], _, by omega, u + 1, rfl, e, hF2, h5₄, hc₄, hm₄⟩
      · refine .inl ⟨by rw [VG.Proof.MlKem.AArch64.eval_nonzero, c₄, decide_eq_false e], hc₄, hm₄, ?_⟩
        rw [show VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx = u + 1 by omega, hF2]
        rw [h5₄, show idx + (u + 1) = VG.Proof.MlDsa.AArch64.Pack.uω s₀ by omega]
  · -- `idx = ω`: nothing.
    rw [c₁] at hge
    have hge := of_decide_eq_false hge
    refine WP.block_nil ⟨hc₁, o₁.mem, ?_⟩
    rw [show VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx = 0 by omega]
    simp only [List.range'_zero, optFold]
    rw [o₁.get .x5, h5, show idx = VG.Proof.MlDsa.AArch64.Pack.uω s₀ by omega]

include hp in
theorem trail_fail {s : State} (hc : VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s) (h5 : s.gpr .x5 = BitVec.ofNat 64 256) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x5 = BitVec.ofNat 64 256 := by
  obtain ⟨-, -, hω80, -, -⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.cmp_ok (r := .x2) s (by rw [hc.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega)
    (by rw [h5, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide)]; decide)) fun s₁ ⟨c₁, o₁⟩ => ?_)
  rw [h5, hc.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := VG.Proof.MlDsa.AArch64.Pack.uω s₀) (by omega), VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide)] at c₁
  refine WP.ite _ (VG.Proof.MlKem.AArch64.eval_nonzero s₁ .x10) (fun h => ?_) fun _ => WP.block_nil ⟨hc.of_only o₁, o₁.mem, by
    rw [o₁.get .x5, h5]⟩
  rw [c₁] at h
  exact absurd (of_decide_eq_true h) (by omega)

/-! ## The return value -/

theorem hbuRet_ok {s : State} (h15 : s.gpr .x15 = BitVec.ofNat 64 1) (h2 : (s.gpr .x2).toNat < 2 ^ 63)
    (h5 : (s.gpr .x5).toNat < 2 ^ 63) :
    WP isa (.block hbuRet) s fun s' =>
      (s'.gpr .x0).setWidth 32 = (if (s.gpr .x2).toNat < (s.gpr .x5).toNat then 0 else 1) ∧ s'.mem = s.mem := by
  unfold hbuRet
  refine VG.Proof.MlKem.AArch64.wp_sub fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_eor fun s₃ o₃ e₃ =>
    VG.Proof.MlKem.AArch64.wp_nil ⟨?_, by rw [o₃.mem, o₂.mem, o₁.mem]⟩
  have hb : s₂.gpr .x10 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < (s.gpr .x5).toNat then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [e₂, e₁, sub_lsr63 h2 h5, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by split <;> decide)]
  rw [e₃, hb, o₂.get .x15, o₁.get .x15, h15]
  split <;> rfl

/-! ## The function -/

include hp in
/-- The polynomials. -/
theorem hbuMain_ok {s : State} (hI : VG.Proof.MlDsa.AArch64.Pack.hbuInitPost s₀ s) :
    WP isa hbuMain s fun s' => VG.Proof.MlDsa.AArch64.Pack.OInv s₀ (VG.Proof.MlDsa.AArch64.Pack.uk s₀) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  obtain ⟨hz, hf, h9, h3, h2, h12, hrd, hwr, hsp⟩ := hI
  have hl := (s₀.gpr .x1).isLt
  have e1 : VG.Proof.MlDsa.AArch64.Pack.uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hx12 : (s₀.gpr .x4 >>> 8).toNat = VG.Proof.MlDsa.AArch64.Pack.uk s₀ := by rw [VG.Proof.MlDsa.AArch64.Pack.lsr8_toNat, hr4]; omega
  have hx2 : s.gpr .x2 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Pack.uω s₀) := by
    rw [h2]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hx12, VG.Proof.MlKem.AArch64.toNat_ofNat_lt (by omega)]
    omega
  unfold hbuMain
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_movz fun s₂ o₂ e₂ => VG.Proof.MlKem.AArch64.wp_add fun s₃ o₃ e₃ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  have k₃ := (o₁.trans o₂).trans o₃
  refine count_loop (n := VG.Proof.MlDsa.AArch64.Pack.uk s₀) (by omega) (VG.Proof.MlDsa.AArch64.Pack.OInv s₀) (fun i hi s hP => VG.Proof.MlDsa.AArch64.Pack.upoly_ok hp hi hP)
    ⟨⟨by rw [k₃.get .x9, h9], by rw [k₃.get .x2, hx2], by rw [o₃.get .x15, e₂]; rfl, by rw [k₃.rd, hrd],
      by rw [k₃.wr, hwr], by rw [k₃.sp, hsp], by rw [k₃.mem]; exact hf⟩,
      by rw [k₃.get .x3, h3]; exact (ptr_zero _).symm,
      by rw [e₃, o₂.get .x9, o₁.get .x9, o₂.get .x2, o₁.get .x2, h9, hx2, Nat.add_zero],
      by rw [k₃.get .x12, h12, hx12]; rfl,
      ⟨by rw [o₃.get .x5, o₂.get .x5, e₁]; rfl, Nat.zero_le _, by rw [k₃.mem]; exact VG.Proof.MlDsa.AArch64.Pack.harr_zero hp hz⟩⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.AArch64.Pack.HArr s₀ m hA) :
    HintIs m (s₀.gpr .x3) (VG.Proof.MlDsa.AArch64.Pack.uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

include hp in
theorem hbu_wp :
    WP isa Impl.MlDsa.AArch64.Pack.hintBitUnpack s₀ fun s' => hintBitUnpackK.post s₀ s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := VG.Proof.MlDsa.AArch64.Pack.up_facts hp
  unfold Impl.MlDsa.AArch64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbuInit_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbuMain_ok hp h₁) fun s₂ hI => ?_)
  -- The spec, as folds.
  show WP isa _ s₂ fun s' => match hintBitUnpack (VG.Proof.MlDsa.AArch64.Pack.uω s₀) (VG.Proof.MlDsa.AArch64.Pack.uk s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) with
    | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (s₀.gpr .x3) (VG.Proof.MlDsa.AArch64.Pack.uk s₀) hint
    | none => (s'.gpr .x0).setWidth 32 = 0
  rw [hintBitUnpack_eq]
  have hst := hI.st
  have hω2 : ∀ {s : State}, VG.Proof.MlDsa.AArch64.Pack.UCom s₀ s → (s.gpr .x2).toNat = VG.Proof.MlDsa.AArch64.Pack.uω s₀ := fun hc => by
    rw [hc.x2, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]
  cases hS : VG.Proof.MlDsa.AArch64.Pack.huS s₀ (VG.Proof.MlDsa.AArch64.Pack.uk s₀) with
  | none =>
    rw [hS] at hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.AArch64.Pack.uω s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray)
      (List.range (VG.Proof.MlDsa.AArch64.Pack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.uk s₀) noHint, 0) = none from hS]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.trail_fail hp hI.com hst) fun s₃ ⟨hc₃, m₃, h5₃⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide)]; decide))
      fun s₄ ⟨r₄, m₄⟩ => ?_
    show (s₄.gpr .x0).setWidth 32 = 0
    rw [r₄, hω2 hc₃, h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide), ite_pos' (by omega)]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hS] at hst
    obtain ⟨h5, hidx, hh⟩ := hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.AArch64.Pack.uω s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray)
      (List.range (VG.Proof.MlDsa.AArch64.Pack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.AArch64.Pack.uk s₀) noHint, 0) = some (hA, idx) from hS]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Pack.trail_ok hp hidx hI.com h5) fun s₃ ⟨hc₃, m₃, hr₃⟩ => ?_)
    dsimp only
    revert hr₃
    cases optFold (huTrail (VG.Proof.MlDsa.AArch64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.AArch64.Pack.uω s₀ - idx)) () with
    | none =>
      intro h5₃
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide)]; decide))
        fun s₄ ⟨r₄, m₄⟩ => ?_
      show (s₄.gpr .x0).setWidth 32 = 0
      rw [r₄, hω2 hc₃, h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (a := 256) (by decide), ite_pos' (by omega)]
    | some _ =>
      intro h5₃
      refine WP.mono (VG.Proof.MlDsa.AArch64.Pack.hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega)]; omega))
        fun s₄ ⟨r₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact VG.Proof.MlDsa.AArch64.Pack.harr_hintIs hh⟩
      rw [r₄, hω2 hc₃, h5₃, VG.Proof.MlDsa.AArch64.Pack.toNat_ofNat_small (by omega), ite_neg' (Nat.lt_irrefl _)]

end

theorem hintBitUnpack_correct (s : State) (hs : hintBitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.hintBitUnpack s t s' ∧ abiPreserved s s' ∧
      hintBitUnpackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := VG.Proof.MlDsa.AArch64.Pack.hbu_wp hs
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hb⟩

/-! ## Constant time -/

/-- The public registers of the loops: `y`, `ω`, `h` and `k`. -/
abbrev hbuTaint : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x9, .x2, .x3, .x12]

theorem hintBitUnpack_ct :
    ConstantTime isa hintBitUnpackK.pre hintBitUnpackK.pub Impl.MlDsa.AArch64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := memTaint.Agree VG.Proof.MlDsa.AArch64.Pack.hbuTaint) ?_
    (RelCT.taint (A := memTaint) VG.Proof.MlDsa.AArch64.Pack.hbuTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := VG.Proof.MlDsa.AArch64.Pack.hbuInitPost)
    (RelCT.taint (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x1, .x3, .x4])
      (fun _ _ ⟨_, _, h0, h1, h3, h4, hsp, _⟩ => agree_of hsp (by simp [h0, h1, h3, h4])) (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlDsa.AArch64.Pack.hbuInit_ok hx, VG.Proof.MlDsa.AArch64.Pack.hbuInit_ok hy⟩)) (fun _ _ h => h)
    fun x' y' ⟨_, x, y, ⟨hx, hy, hp⟩, fx, fy⟩ => ?_
  obtain ⟨hz₁, hf₁, a9, a3, a2, a12, rd₁, wr₁, sp₁⟩ := fx
  obtain ⟨hz₂, hf₂, b9, b3, b2, b12, rd₂, wr₂, sp₂⟩ := fy
  obtain ⟨p0, p1, p3, p4, psp, hleak⟩ := hp
  have hrd : x'.rd = y'.rd := by rw [rd₁, rd₂, hx.1, hy.1, p0, p1]
  have hwr : x'.wr = y'.wr := by rw [wr₁, wr₂, hx.2.1, hy.2.1, p3, p4]
  refine ⟨agree_of (by rw [sp₁, sp₂, psp]) fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a9, b9, p0]
    · rw [a2, b2, p1, p4]
    · rw [a3, b3, p3]
    · rw [a12, b12, p4]
  · rw [rd₁, wr₁, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      rw [hf₁ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'),
        hf₂ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [VG.Proof.MlDsa.AArch64.Pack.uR, ← p3, ← p4] at hc'
          exact hx.2.2.1 a hc hc')]
      have hlt : (a - x.gpr .x0).toNat < (x.gpr .x1).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .x0 + BitVec.ofNat 64 (a - x.gpr .x0).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hb : bytesAt x.mem (x.gpr .x0) (x.gpr .x1).toNat = bytesAt y.mem (x.gpr .x0) (x.gpr .x1).toNat := by
        have hl2 := hleak
        rw [← p0, ← p1] at hl2
        exact map_toNat_inj hl2
      have h₁ := congrArg (·.getD (a - x.gpr .x0).toNat 0) hb
      rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ hlt, ← ea] at h₁
      exact h₁
    · -- `h`: zeros.
      rw [byte_of_zero_words hz₁ hc, byte_of_zero_words hz₂ (by rw [← p3, ← p4]; exact hc)]

/-- A state satisfying the precondition. -/
def hintBitUnpackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 84 | .x2 => 80 | .x3 => 0x3000 | .x4 => 1024 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.hintBitUnpack (hintBitUnpackContract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.AArch64.Pack.hintBitUnpack_correct VG.Proof.MlDsa.AArch64.Pack.hintBitUnpack_ct
    { pre := by sig_implies_pre [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.AArch64.Pack.hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.AArch64.Pack.hintBitUnpackSat, ?_⟩
        sig_pre [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack

end
