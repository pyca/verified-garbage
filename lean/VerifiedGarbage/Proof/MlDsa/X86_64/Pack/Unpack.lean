import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Stream`. -/
section

/-!
# ML-DSA on x86-64: streaming fields through `r10`

The group bodies of `Impl/MlDsa/X86_64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator is a slice of the number throughout (`Pack/Stream.lean`).
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep Written Written.nil
  Written.snoc Written.congr Written.frame rotr_toNat shr_toNat b8_eq64 ifp ifn sx_ofNat r10zero_ok)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (VG.Impl.MlDsa.X86_64.Pack.at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.MlDsa.X86_64.Pack.at_]
  congr 1

/-- `r10 ← r10 + rax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State) (hx : (s.gpr .rax).toNat < 2 ^ (64 - sh))
    (hs : (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .r10).toNat = (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  by_cases h : sh = 0
  · subst h
    refine WP.keep _ ?_ (by decide)
    simp only [shiftAdd, ite_true, List.nil_append]
    xrun
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · refine WP.keep _ ?_ (by simp only [shiftAdd, h, ite_false]; rfl)
    simp only [shiftAdd, h, ite_false, List.singleton_append]
    xrun [show 1 ≤ 64 - sh by omega, show 64 - sh ≤ 63 by omega]
    rw [BitVec.toNat_add, rotr_toNat _ (by omega) hx, show 64 - (64 - sh) = sh by omega, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 t) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hout]

/-- The bytes `k, …, k + nf - 1` of the output from the accumulator `X`,
whose byte `u` is byte `k + u` of the output. -/
theorem flush_ok {k nf : Nat} {m₀ : Mem} {o : Addr} {V8 : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V8 (k + u)) (hk : k + nf < 2 ^ 64) (s : State)
    (h8 : s.gpr .r8 = o) (hout : ∀ u < nf, InRegions s.wr (o + BitVec.ofNat 64 (k + u)) 1)
    (hw : Written m₀ s.mem o k V8) (hr : (s.gpr .r10).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      Written m₀ s'.mem o (k + nf) V8 ∧ (s'.gpr .r10).toNat = X / 2 ^ (8 * nf) ∧ Keep [.r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.r10] s s' ∧
    (s'.gpr .r10).toNat = X / 2 ^ (8 * u) ∧ Written m₀ s'.mem o (k + u) V8)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h8' : s'.gpr .r8 = o := (hkp.gpr (by decide)).trans h8
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.packByte_ok (k + u) s' (by rw [hkp.2.2, h8']; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8']
    refine (hw'.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k + u
    · subst e; rw [ifp rfl, b8_eq64, hr', hX u hu]
    · rw [ifn e]

/-- `ld j` loads into `rax` the value `F` of the word at `rdi + 4j`, and
writes only `rax` and `r11`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) : Prop :=
  ∀ j s, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .rax).toNat = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r11] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

/-- Field `j`: its value, digit `j` of `G`, into `r10`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.X86_64.Pack.LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (s.gpr .r8) (d * j / 8) (VG.Proof.MlDsa.X86_64.Pack.bytesOf G))
    (hr : (s.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) (hj : d * (j + 1) < 2 ^ 32) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (s.gpr .r8) (d * (j + 1) / 8) (VG.Proof.MlDsa.X86_64.Pack.bytesOf G) ∧
        (s'.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.rax, .r10, .r11] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .rax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.shiftAdd_ok (sh := d * j % 8) (by omega) s₁
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))) (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hX : (s₂.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8 : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (o := s.gpr .r8)
    (V8 := VG.Proof.MlDsa.X86_64.Pack.bytesOf G) _ (fun u hu => ?_) (by omega) s₂ h8 (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
      omega] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
      omega]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r8`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.X86_64.Pack.LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 (4 * j), 4⟩ ⟨s.gpr .r8, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) nb (VG.Proof.MlDsa.X86_64.Pack.bytesOf (digits d ((List.range c).map fun j =>
          F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)))) ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 (4 * c) ∧ s'.gpr .r8 = s.gpr .r8 + BitVec.ofNat 64 nb ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rdi, .r8, .r10, .r11] s s' := by
  generalize hG : digits d ((List.range c).map fun j => F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = s.gpr .rdi := k₁.gpr (by decide)
  have r8₁ : s₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r10, .r11] s₁ s' ∧
      Written s.mem s'.mem (s.gpr .r8) (d * j / 8) (VG.Proof.MlDsa.X86_64.Pack.bytesOf G) ∧
      (s'.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have r8 : s'.gpr .r8 = s.gpr .r8 := (hk.gpr (by decide)).trans r8₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    have hj32 := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.packCoef_ok hld (G := G) (m₀ := s.mem) hd s' (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2, r8]; exact hout t (by omega)) (by rw [r8]; exact hw) hr (by omega))
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), by rw [← r8]; exact hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [di, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨s.gpr .r8, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega
    have := Nat.mul_le_mul hd hc
    rw [hc8] at hw₂
    refine WP.mono (Proof.MlKem.X86_64.CE.tail_ok c nb (by omega) (by omega) s₂)
      fun s₃ ⟨⟨di₃, r8₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [r8₃, k₂.gpr (by decide), r8₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

theorem unpackByte_ok (d j t : Nat) (hsh : 8 * t - d * j ≤ 56) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hs : (s.gpr .r10).toNat + (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 64) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .r10).toNat =
          (s.gpr .r10).toNat + (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .r10] s s' := by
  unfold unpackByte
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.gpr .rax = BitVec.setWidth 64 (s.mem (s.gpr .rdi +
    BitVec.ofNat 64 t)) ∧ s'.mem = s.mem) (by xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hin]) (by rfl)) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hb := (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).isLt
  have hax : (s₁.gpr .rax).toNat = (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat := by
    rw [ax₁, Proof.MlKem.X86_64.toNat_setWidth64_8]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.shiftAdd_ok (by omega) s₁ (by
      rw [hax]; exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (s.gpr .rdi + BitVec.ofNat 64 (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .r10).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .r10).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.rax, .r10] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.rax, .r10] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .r10).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have di : s'.gpr .rdi = s.gpr .rdi := hkp.gpr (by decide)
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← di] at hbu
  have hbl : (s'.mem (s'.gpr .rdi + BitVec.ofNat 64 (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.unpackByte_ok d j (k + u) (by omega) s' (by rw [hkp.2.1, hkp.2.2, di]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `rax` to
`rsi + 4j`, and writes only `rax` and `r11`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .rax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (s.gpr .rax).toNat) ∧ Keep [.rax, .r11] s s'

theorem extract_ok (d : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block [.mov .rax (.reg .r10), .alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1))),
      .shift .shr .r10 d]) s fun s' =>
      ((s'.gpr .rax).toNat = (s.gpr .r10).toNat % 2 ^ d ∧ s'.gpr .r10 = s.gpr .r10 >>> d ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [show 1 ≤ d by omega, show d ≤ 63 by omega]
  have hp : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- Field `j`: the bytes it needs into `r10`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.X86_64.Pack.FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (s : State)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4)
    (hr : (s.gpr .r10).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .r10).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧ Keep [.rax, .r10, .r11] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) s (fun u hu => hin _ (by omega))
    (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.extract_ok d hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .rax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have si : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, si]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, si, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, shr_toNat, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `rdi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.X86_64.Pack.FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) 1)
    (hout : ∀ j < c, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : ∀ t < nb, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 t, 1⟩ ⟨s.gpr .rsi, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 nb ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (4 * c) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        Keep [.rax, .rcx, .rsi, .rdi, .r10, .r11] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (r10zero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = s.gpr .rdi := k₁.gpr (by decide)
  have si₁ : s₁.gpr .rsi = s.gpr .rsi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r10, .r11] s₁ s' ∧
      Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .r10).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have si : s'.gpr .rsi = s.gpr .rsi := (hk.gpr (by decide)).trans si₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.unpackCoef_ok hfin hd1 hd (H := H) s'
      (fun t ht => by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin t (by omega))
      (fun t ht => by
        rw [di, hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t (by omega) _ (Region.contains_self _ _))
      (by rw [hk.2.2, k₁.2.2, si]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', si]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', si]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (Proof.MlKem.X86_64.DD.tail_ok c nb (by omega) (by omega) s₂)
      fun s₃ ⟨⟨di₃, si₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Loop`. -/
section

/-!
# ML-DSA on x86-64: the loops over the groups

`packLoop_ok`: the loop of `packBody` writes the packing of the values of the
256 coefficients at `f`; `unpackLoop_ok`: the loop of `unpackBody` writes, for
each field of the bytes at `v`, `fin`'s coefficient of it. Both for any width
and any `ld` or `fin`, from the group lemmas of `Stream.lean`.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr Written Written.step ptr_step
  wp_counted WP.keep)
open VG.Proof.MlKem (digits take_drop_eq bytesAt_getD bytesAt_eq! bytesAt_length bytes_map_take_drop)
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

theorem Shape.nb20 {d c nb : Nat} (h : VG.Proof.MlDsa.X86_64.Pack.Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.group {d c nb : Nat} (h : VG.Proof.MlDsa.X86_64.Pack.Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The registers a loop writes. -/
abbrev packRegs : List Reg := [.rax, .rcx, .rdi, .r8, .r10, .r11]
abbrev unpackRegs : List Reg := [.rax, .rcx, .rsi, .rdi, .r10, .r11]

/-! ## Packing -/

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.X86_64.Pack.LdOk ld F) {d c nb : Nat} (hs : VG.Proof.MlDsa.X86_64.Pack.Shape d c nb)
  {f o : Addr} {s₀ sE : State} (hin : polyRegion f ∈ s₀.rd ++ s₀.wr) (hout : (⟨o, 32 * d⟩ : Region) ∈ s₀.wr)
  (hsep : Region.Disjoint (polyRegion f) ⟨o, 32 * d⟩) (hF : ∀ i < 256, F (coeffAt s₀.mem f i) < 2 ^ d)
include hld hs hin hout hsep hF

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

omit hld hs hin hout hsep hF in
theorem vals_lt {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Pack.vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

/-- After `i` groups. -/
structure PInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = f + BitVec.ofNat 64 (4 * c * i)
  r8 : s.gpr .r8 = o + BitVec.ofNat 64 (nb * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨o, 32 * d⟩] s₀.mem s.mem
  done : ∀ k < nb * i, s.mem (o + BitVec.ofNat 64 k) = (bitsToBytes (fieldBits d (VG.Proof.MlDsa.X86_64.Pack.vals F s₀.mem f)))[k]!
  keep : Keep VG.Proof.MlDsa.X86_64.Pack.packRegs sE s

theorem packStep {i : Nat} (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlDsa.X86_64.Pack.PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      VG.Proof.MlDsa.X86_64.Pack.PInv (f := f) (o := o) (s₀ := s₀) (sE := sE) (F := F) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j < c, s.gpr .rdi + BitVec.ofNat 64 (4 * j) = coeffAddr f (c * i + j) := fun j _ => by
    rw [hI.rdi, VG.Proof.MlDsa.X86_64.Pack.off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .r8 + BitVec.ofNat 64 t = o + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.r8, VG.Proof.MlDsa.X86_64.Pack.off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32 = coeffAt s₀.mem f (c * i + j) :=
    fun j hj => by
      rw [ha j hj]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.packBody_ok hld hs.d20 hs.dc hs.c8 s
    (fun j hj => by rw [ha j hj, hI.rd, hI.wr]; exact VG.Proof.MlDsa.X86_64.Pack.inRegions_of hin (coeff_contains f (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact VG.Proof.MlDsa.X86_64.Pack.inRegions_of hout (Offset.contains_base o (by omega) (by omega)))
    (fun j hj => by
      rw [ha j hj, hI.r8]
      exact (hsep.sub_left (Offset.sub_base f (by omega))).sub_right (Offset.sub_base o (by omega)))
    (fun j hj => by rw [hw j hj]; exact hF _ (by omega)))
    fun s' ⟨hW, di', r8', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  have hW' : Written s.mem s'.mem (o + BitVec.ofNat 64 (nb * i)) nb
      fun t => (bitsToBytes (fieldBits d (VG.Proof.MlDsa.X86_64.Pack.vals F s₀.mem f)))[nb * i + t]! := by
    rw [← hI.r8]
    refine hW.congr fun t ht => ?_
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (VG.Proof.MlDsa.X86_64.Pack.vals_lt hF) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    have hj := List.mem_range.mp hj
    rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega),
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i (4 * c)
  · rw [r8', hI.r8]; exact ptr_step _ i nb
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]

theorem packLoop_ok {s : State} (hdi : s.gpr .rdi = f) (h8 : s.gpr .r8 = o) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (packLoop ld d c nb) s fun s' =>
      bytesAt s'.mem o (32 * d) = bitsToBytes (fieldBits d (VG.Proof.MlDsa.X86_64.Pack.vals F s₀.mem f)) ∧
        Frame [⟨o, 32 * d⟩] s₀.mem s'.mem ∧ Keep VG.Proof.MlDsa.X86_64.Pack.packRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega) hN0
    (VG.Proof.MlDsa.X86_64.Pack.PInv (f := f) (o := o) (s₀ := s₀) (sE := s) (F := F) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₂.mono (by decide)⟩)
    fun i hi s hI => VG.Proof.MlDsa.X86_64.Pack.packStep hld hs hin hout hsep hF hi hI)
    fun s' hI => ⟨?_, hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), h8]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _
  · exact bytesAt_eq! (pack_length d _ (by simp)) fun k hk => hI.done k (by rw [hs.bN]; exact hk)

end

/-! ## Unpacking -/

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} (hfin : VG.Proof.MlDsa.X86_64.Pack.FinOk fin d W)
  (hs : VG.Proof.MlDsa.X86_64.Pack.Shape d c nb) {v p : Addr} {s₀ sE : State} (hin : (⟨v, 32 * d⟩ : Region) ∈ s₀.rd ++ s₀.wr)
  (hout : polyRegion p ∈ s₀.wr) (hsep : Region.Disjoint ⟨v, 32 * d⟩ (polyRegion p))
include hfin hs hin hout hsep

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

/-- After `i` groups. -/
structure UInv (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = v + BitVec.ofNat 64 (nb * i)
  rsi : s.gpr .rsi = p + BitVec.ofNat 64 (4 * c * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [polyRegion p] s₀.mem s.mem
  done : ∀ k < c * i, coeffAt s.mem p k = W (VG.Proof.MlDsa.X86_64.Pack.inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)
  keep : Keep VG.Proof.MlDsa.X86_64.Pack.unpackRegs sE s

theorem unpackStep {i : Nat} (hi : i < 256 / c) {s : State}
    (hI : VG.Proof.MlDsa.X86_64.Pack.UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      VG.Proof.MlDsa.X86_64.Pack.UInv (v := v) (p := p) (s₀ := s₀) (sE := sE) (W := W) (d := d) (c := c) (nb := nb) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hnb := hs.nb20
  have hd20 := hs.d20
  have ha : ∀ j, s.gpr .rsi + BitVec.ofNat 64 (4 * j) = coeffAddr p (c * i + j) := fun j => by
    rw [hI.rsi, VG.Proof.MlDsa.X86_64.Pack.off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t, s.gpr .rdi + BitVec.ofNat 64 t = v + BitVec.ofNat 64 (nb * i + t) := fun t => by
    rw [hI.rdi, VG.Proof.MlDsa.X86_64.Pack.off_add]
  have hsub : Region.Sub ⟨s.gpr .rsi, 4 * c⟩ (polyRegion p) := by
    rw [hI.rsi]; exact Offset.sub_base p (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 s
    (fun t ht => by rw [hb, hI.rd, hI.wr]; exact VG.Proof.MlDsa.X86_64.Pack.inRegions_of hin (Offset.contains_base v (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact VG.Proof.MlDsa.X86_64.Pack.inRegions_of hout (coeff_contains p (by omega)))
    (fun t ht => by
      rw [hb]
      exact (hsep.sub_left (Offset.sub_base v (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, di', si', cx', z', k'⟩ => ⟨?_, cx', z'⟩
  -- The bytes of the group, on entry.
  have hB : (List.range nb).map (fun t => (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat) =
      (((bytesAt s₀.mem v (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
    rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    have ht := List.mem_range.mp ht
    rw [VG.Proof.MlDsa.X86_64.Pack.getD_map_toNat, bytesAt_getD _ _ (by omega), hb]
    refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsep _ (Offset.contains_base v (by omega) (by omega))
  have hlt : ∀ a ∈ (bytesAt s₀.mem v (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine ⟨?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_), fun k hk => ?_,
    (hI.keep.trans k').mono (by decide)⟩
  · rw [di', hI.rdi]; exact ptr_step _ i nb
  · rw [si', hI.rsi]; exact ptr_step _ i (4 * c)
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [hI.rsi]
    exact Offset.disjoint p (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
  · -- Written by this group.
    have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
    have := hw (k - c * i) hj
    rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
      show c * i + (k - c * i) = k by omega] at this
    rw [coeffAt_eq, this]

theorem unpackLoop_ok {s : State} (hdi : s.gpr .rdi = v) (hsi : s.gpr .rsi = p) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : s.mem = s₀.mem) :
    WP isa (unpackLoop fin d c nb) s fun s' =>
      (∀ k < 256, coeffAt s'.mem p k = W (VG.Proof.MlDsa.X86_64.Pack.inNum s₀.mem v d / 2 ^ (d * k) % 2 ^ d)) ∧
        Frame [polyRegion p] s₀.mem s'.mem ∧ Keep VG.Proof.MlDsa.X86_64.Pack.unpackRegs s s' := by
  have h0 := hs.c0
  have hN : 256 / c ≤ 256 := Nat.div_le_self _ _
  have hN0 : 0 < 256 / c := Nat.div_pos (by have := hs.c8; omega) h0
  refine WP.mono (wp_counted (N := 256 / c)
    (v := BitVec.ofNat 32 (256 / c)) (by rw [BitVec.toNat_ofNat]; omega) hN0
    (VG.Proof.MlDsa.X86_64.Pack.UInv (v := v) (p := p) (s₀ := s₀) (sE := s) (W := W) (d := d) (c := c) (nb := nb))
    (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_, fun k hk => absurd hk (by omega), k₂.mono (by decide)⟩)
    fun i hi s hI => VG.Proof.MlDsa.X86_64.Pack.unpackStep hfin hs hin hout hsep hi hI)
    fun s' hI => ⟨fun k hk' => hI.done k (by rw [hs.cN]; exact hk'), hI.frame, hI.keep⟩
  · rw [k₂.gpr (by decide), hdi]; simp
  · rw [k₂.gpr (by decide), hsi]; simp
  · rw [k₂.2.1, hrd]
  · rw [k₂.2.2, hwr]
  · rw [m₂, hm]; exact Frame.refl _ _

end

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Contracts`. -/
section

/-!
# ML-DSA on x86-64: the contracts of the encodings, for the proofs

For each function of this group, a contract with the facts of its shared
contract (`Spec/MlDsa/Poly.lean`) spelled out for x86-64: the arguments in
their registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and `Verified.of_correct`
moves them to the shared contracts, which imply them. Also: `sel_ok`, the
branch of `sel` on a 32-bit argument.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (retR pR dArg sub_beq_zero32)

/-- `vg_mldsa_simple_bit_pack(f = rdi, b = esi, out = rdx, len = rcx)`. -/
def simpleBitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ dArg s .rsi ∈ simpleBitPackBounds ∧
    (s.gpr .rcx).toNat = 32 * bitlen (dArg s .rsi) ∧ ∀ i < n, (coeffAt s.mem (s.gpr .rdi) i).toNat ≤ dArg s .rsi
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    simpleBitPack (natPolyAt s.mem (s.gpr .rdi)) (dArg s .rsi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_bit_pack(f = rdi, a = esi, b = edx, out = rcx, len = r8)`. -/
def bitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (dArg s .rsi, dArg s .rdx) ∈ bitPackParams ∧
    (s.gpr .r8).toNat = 32 * bitlen (dArg s .rsi + dArg s .rdx) ∧ Reduced s.mem (s.gpr .rdi) ∧
    ∀ i < n, -(dArg s .rsi : Int) ≤ modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ∧
      modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ≤ dArg s .rdx
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
    bitPack ((polyAt s.mem (s.gpr .rdi)).map fun c => modPm c.val q) (dArg s .rsi) (dArg s .rdx)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_bit_unpack(v = rdi, len = rsi, a = edx, b = ecx, f = r8)`. -/
def bitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .r8)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .r8)) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .r8)) ∧
    (dArg s .rdx, dArg s .rcx) ∈ bitPackParams ∧ (s.gpr .rsi).toNat = 32 * bitlen (dArg s .rdx + dArg s .rcx)
  post s s' := PolyIs s'.mem (s.gpr .r8)
    (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (dArg s .rdx) (dArg s .rcx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (s₁.gpr .rcx).setWidth 32 = (s₂.gpr .rcx).setWidth 32

/-- `vg_mldsa_unpack_t1(v = rdi, f = rsi)`. -/
def unpackT1K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 320⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 320⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 320⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi)
    ((simpleBitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Branching on a width -/

theorem cmp_ok (r : Reg) (k : BitVec 32) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm k)]) s fun s' =>
      s'.zf = some (BitVec.setWidth 32 (s.gpr r) - k == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun

/-- The same registers, memory and permissions. -/
def Same (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem sel_ok (r : Reg) (v : Nat) (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', VG.Proof.MlDsa.X86_64.Pack.Same s s' → (s.gpr r).setWidth 32 = BitVec.ofNat 32 v → WP isa p s' Q)
    (he : ∀ s', VG.Proof.MlDsa.X86_64.Pack.Same s s' → (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmp_ok r _ s) fun s' ⟨z, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e s' = _ from z) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact hp s' ⟨hg, hm, hrd, hwr⟩ h
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    exact he s' ⟨hg, hm, hrd, hwr⟩ h

/-- The low 32 bits of `r` are `v` if its argument is. -/
theorem lo_eq {s : State} {r : Reg} {v : Nat} (hv : v < 2 ^ 32) (h : dArg s r = v) :
    (s.gpr r).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; exact h

theorem lo_ne {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v) :
    dArg s r ≠ v := fun e => h (by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← e]; exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm)

theorem lo_of_eq {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 = BitVec.ofNat 32 v) :
    dArg s r = v % 2 ^ 32 := by
  unfold dArg; rw [h, BitVec.toNat_ofNat]

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of toNat_setWidth64 read_zero)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : VG.Proof.MlDsa.X86_64.Pack.LdOk sbpLd BitVec.toNat := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold sbpLd
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hin]
  rw [toNat_setWidth64]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem sbpPro_ok (s : State) :
    WP isa (.block [.mov32 .rsi (.reg .rsi), .mov .r8 (.reg .rdx)]) s fun s' =>
      (dArg s' .rsi = dArg s .rsi ∧ s'.gpr .r8 = s.gpr .rdx ∧ s'.mem = s.mem) ∧ Keep [.rsi, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

theorem sbp_wp {s₀ : State} (hp : simpleBitPackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.simpleBitPack s₀ fun s' =>
      simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hb, hlen, hle⟩ := hp
  have go : ∀ {d c nb : Nat}, VG.Proof.MlDsa.X86_64.Pack.Shape d c nb → bitlen (dArg s₀ .rsi) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rdx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        simpleBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rdx, (s₀.gpr .rcx).toNat⟩] s₀.mem s'.mem := by
    intro d c nb hs hd s h1 h2 h3 h4 h5
    rw [hd] at hlen
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.packLoop_ok VG.Proof.MlDsa.X86_64.Pack.sbpLd_ok hs (f := s₀.gpr .rdi) (o := s₀.gpr .rdx) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => by rw [← hd]; exact VG.Proof.MlDsa.X86_64.Pack.lt_bitlen (hle i hi)) h1 h2 h3 h4 h5)
      fun s' ⟨hB, hf, _⟩ => ⟨?_, by rw [hlen]; exact hf⟩
    show bytesAt s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat = simpleBitPack _ _
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.X86_64.Pack.simpleBitPack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.sbpPro_ok s₀) fun s₁ ⟨⟨si₁, r8₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rsi 15 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rsi = 15 := by rw [← si₁, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₂
      (by rw [g₂, di₁]) (by rw [g₂, r8₁]) (by rw [rd₂, k₁.2.1]) (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n15 : dArg s₀ .rsi ≠ 15 := by rw [← si₁]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₂ : dArg s₂ .rsi = dArg s₀ .rsi := by unfold dArg; rw [g₂]; exact si₁
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rsi 43 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rsi = 43 := by rw [← ds₂, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    exact go (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])
  · have n43 : dArg s₀ .rsi ≠ 43 := by rw [← ds₂]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
    have e : dArg s₀ .rsi = 1023 := by
      simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with e | e | e
      · exact e
      · exact absurd e n43
      · exact absurd e n15
    exact go (d := 10) (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by rw [e]; decide) s₃
      (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁]) (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2])
      (by rw [m₃, m₂, m₁])

theorem simpleBitPack_correct (s : State) (hs : simpleBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.simpleBitPack s t s' ∧ abiPreserved s s' ∧
      simpleBitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.simpleBitPack)
    [.rax, .rcx, .rsi, .rdi, .r8, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.sbp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem simpleBitPack_ct :
    ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub Impl.MlDsa.X86_64.Pack.simpleBitPack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rdx, .rcx, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, VG.Proof.MlKem.X86_64.read_zero]
  rfl

/-- A state satisfying the precondition. -/
def simpleBitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 15 | .rdx => 0x2000 | .rcx => 128 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

theorem simpleBitPack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.simpleBitPack (simpleBitPackContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.simpleBitPack_correct VG.Proof.MlDsa.X86_64.Pack.simpleBitPack_ct
    { pre := by sig_implies_pre [simpleBitPackContract, simpleBitPackSig, VG.Proof.MlDsa.X86_64.Pack.simpleBitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [simpleBitPackContract, simpleBitPackSig, VG.Proof.MlDsa.X86_64.Pack.simpleBitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract, simpleBitPackSig, VG.Proof.MlDsa.X86_64.Pack.simpleBitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.simpleBitPackSat, ?_⟩
        sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [VG.Proof.MlDsa.X86_64.Pack.coeffAt_zero]; exact Nat.zero_le _
          | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.BitPack`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_bit_pack`

The value of a coefficient `x` is `b - x`, plus `q` if that borrows
(`subModQ`), which is `b - (x mod± q)` for a reduced `x` (`Pack/Arith.lean`).
The loop is proven once for every width (`packLoop_ok`), and the function by
its five cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of toNat_setWidth64)
open VG.Proof.MlDsa.Pack

/-- `b - x`, plus `q` if it borrows, as the code computes it in 32 bits. -/
def subModQ (b x : BitVec 32) : BitVec 32 :=
  b - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm)

theorem subModQ_toNat {b x : BitVec 32} (hb : b.toNat < q) (hx : x.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Pack.subModQ b x).toNat = (b.toNat + q - x.toNat) % q := by
  have hq : q = 8380417 := rfl
  rw [hq] at hb hx ⊢
  unfold VG.Proof.MlDsa.X86_64.Pack.subModQ
  by_cases h : b.toNat < x.toNat
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 8380417#32 := by
      rw [decide_eq_true h]; decide
    rw [e, Nat.mod_eq_of_lt (by omega)]
    bv_omega
  · have e : (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm) = 0#32 := by
      rw [decide_eq_false h]; decide
    rw [e, show (b.toNat + 8380417 - x.toNat) % 8380417 = b.toNat - x.toNat by omega]
    bv_omega

/-- The value `bpLd B` loads of a word. -/
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (VG.Proof.MlDsa.X86_64.Pack.subModQ (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok (B : Nat) : VG.Proof.MlDsa.X86_64.Pack.LdOk (bpLd B) (VG.Proof.MlDsa.X86_64.Pack.bpVal B) := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold bpLd
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hin]
  rw [toNat_setWidth64]
  rfl

theorem bpPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov .r8 (.reg .rcx)]) s fun s' =>
      (dArg s' .rdx = dArg s .rdx ∧ s'.gpr .r8 = s.gpr .rcx ∧ s'.mem = s.mem) ∧ Keep [.rdx, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) = VG.Proof.MlDsa.X86_64.Pack.vals (VG.Proof.MlDsa.X86_64.Pack.bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; have : q = 8380417 := rfl; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [VG.Proof.MlDsa.X86_64.Pack.bpVal, VG.Proof.MlDsa.X86_64.Pack.subModQ_toNat (by omega) hx, hbq, sub_modPm hx hb (hle i hi)]

theorem bp_wp {s₀ : State} (hp : bitPackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.bitPack s₀ fun s' =>
      bitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hab, hlen, hred, hbnd⟩ := hp
  have go : ∀ {d c nb B : Nat}, VG.Proof.MlDsa.X86_64.Pack.Shape d c nb → dArg s₀ .rdx = B → B ≤ 2 ^ 19 →
      bitlen (dArg s₀ .rsi + B) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .r8 = s₀.gpr .rcx → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (packLoop (bpLd B) d c nb) s fun s' =>
        bitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
    intro d c nb B hs hB hB19 hd s h1 h2 h3 h4 h5
    rw [hB, hd] at hlen
    have hq : q = 8380417 := rfl
    have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.packLoop_ok (VG.Proof.MlDsa.X86_64.Pack.bpLd_ok B) hs (f := s₀.gpr .rdi) (o := s₀.gpr .rcx) (s₀ := s₀)
      (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep)
      (fun i hi => ?_) h1 h2 h3 h4 h5)
      fun s' ⟨hB', hf, _⟩ => ⟨?_, by rw [hlen]; exact hf⟩
    · obtain ⟨h₁, h₂⟩ := hbnd i hi
      rw [hB] at h₂
      have hx := hred i hi
      rw [VG.Proof.MlDsa.X86_64.Pack.bpVal, VG.Proof.MlDsa.X86_64.Pack.subModQ_toNat (by omega) hx, hBq, ← sub_modPm hx (by omega) h₂, ← hd, ← hB]
      exact VG.Proof.MlDsa.X86_64.Pack.lt_bitlen (sub_modPm_le h₁ (by rw [hB]; exact h₂))
    · show bytesAt s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat = bitPack _ _ _
      rw [hlen, hB', bitPack_eq, VG.Proof.MlDsa.X86_64.Pack.bitPack_vals hred (by omega) (fun i hi => (hbnd i hi).2),
        hB, hd]
  unfold Impl.MlDsa.X86_64.Pack.bitPack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.bpPro_ok s₀) fun s₁ ⟨⟨dx₁, r8₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have cases := VG.Proof.MlDsa.X86_64.Pack.mem_bitPackParams hab
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rdx 2 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rdx = 2 := by rw [← dx₁, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rsi = 2 := by omega
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₂ (by rw [g₂, di₁]) (by rw [g₂, r8₁]) (by rw [rd₂, k₁.2.1])
      (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n2 : dArg s₀ .rdx ≠ 2 := by rw [← dx₁]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₂ : dArg s₂ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₂]; exact dx₁
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rdx 4 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rdx = 4 := by rw [← ds₂, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rsi = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₃ (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, r8₁])
      (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2]) (by rw [m₃, m₂, m₁])
  have n4 : dArg s₀ .rdx ≠ 4 := by rw [← ds₂]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₃ : dArg s₃ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₃]; exact ds₂
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rdx 4096 _ _ s₃ (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_) (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_)
  · have e : dArg s₀ .rdx = 4096 := by rw [← ds₃, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rsi = 4095 := by omega
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₄ (by rw [g₄, g₃, g₂, di₁]) (by rw [g₄, g₃, g₂, r8₁])
      (by rw [rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₄, m₃, m₂, m₁])
  have n4096 : dArg s₀ .rdx ≠ 4096 := by rw [← ds₃]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₄ : dArg s₄ .rdx = dArg s₀ .rdx := by unfold dArg; rw [g₄]; exact ds₃
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rdx 131072 _ _ s₄ (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_) (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_)
  · have e : dArg s₀ .rdx = 131072 := by rw [← ds₄, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rsi = 131071 := by omega
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, r8₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])
  · have n131072 : dArg s₀ .rdx ≠ 131072 := by rw [← ds₄]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
    have e : dArg s₀ .rdx = 524288 := by omega
    have ea : dArg s₀ .rsi = 524287 := by omega
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, r8₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])

theorem bitPack_correct (s : State) (hs : bitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.bitPack s t s' ∧ abiPreserved s s' ∧ bitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.bitPack)
    [.rax, .rcx, .rdx, .rdi, .r8, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.bp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem bitPack_ct : ConstantTime isa bitPackK.pre bitPackK.pub Impl.MlDsa.X86_64.Pack.bitPack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rcx, .r8, .rsp] [.rsi, .rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.2.2.2.2.1, hp.2.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def bitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 2 | .rdx => 2 | .rcx => 0x2000 | .r8 => 96 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 96⟩]

theorem bitPack_verified : Verified X86_64.target Impl.MlDsa.X86_64.Pack.bitPack (bitPackContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.bitPack_correct VG.Proof.MlDsa.X86_64.Pack.bitPack_ct
    { pre := by sig_implies_pre [bitPackContract, bitPackSig, VG.Proof.MlDsa.X86_64.Pack.bitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [bitPackContract, bitPackSig, VG.Proof.MlDsa.X86_64.Pack.bitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [bitPackContract, bitPackSig, VG.Proof.MlDsa.X86_64.Pack.bitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.bitPackSat, ?_⟩
        sig_pre [bitPackContract, bitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | exact fun i _ => by rw [VG.Proof.MlDsa.X86_64.Pack.coeffAt_zero]; decide
          | (simp only [bitPackParams]; decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y`, plus `q` if that borrows
(`subModQ`), which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`. The
loop is proven once for every width (`unpackLoop_ok`), and
`vg_mldsa_bit_unpack` by its five cases.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of rotr_toNat)
open VG.Proof.MlDsa.Pack

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := VG.Proof.MlDsa.X86_64.Pack.subModQ (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok (B d : Nat) : VG.Proof.MlDsa.X86_64.Pack.FinOk (buFin B) d (VG.Proof.MlDsa.X86_64.Pack.buWord B) := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold buFin
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hout]
  rw [VG.Proof.MlDsa.X86_64.Pack.buWord, BitVec.ofNat_toNat]
  rfl

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 32 y).rotateRight 19

theorem t1Fin_ok : VG.Proof.MlDsa.X86_64.Pack.FinOk t1Fin 10 VG.Proof.MlDsa.X86_64.Pack.t1Word := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold t1Fin
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_at', hout]
  rw [VG.Proof.MlDsa.X86_64.Pack.t1Word, BitVec.ofNat_toNat]

theorem buPro_ok (s : State) :
    WP isa (.block [.mov32 .rcx (.reg .rcx), .mov .rsi (.reg .r8)]) s fun s' =>
      (dArg s' .rcx = dArg s .rcx ∧ s'.gpr .rsi = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rcx, .rsi] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

theorem bu_wp {s₀ : State} (hp : bitUnpackK.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.bitUnpack s₀ fun s' =>
      bitUnpackK.post s₀ s' ∧ Frame [pR (s₀.gpr .r8)] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -, hab, hlen⟩ := hp
  have go : ∀ {d c nb B : Nat}, VG.Proof.MlDsa.X86_64.Pack.Shape d c nb → dArg s₀ .rcx = B → B ≤ 2 ^ 19 →
      bitlen (dArg s₀ .rdx + B) = d → ∀ s : State,
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsi = s₀.gpr .r8 → s.rd = s₀.rd → s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (unpackLoop (buFin B) d c nb) s fun s' =>
        bitUnpackK.post s₀ s' ∧ Frame [pR (s₀.gpr .r8)] s₀.mem s'.mem := by
    intro d c nb B hs hB hB19 hd s h1 h2 h3 h4 h5
    rw [hB, hd] at hlen
    have hq : q = 8380417 := rfl
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.unpackLoop_ok (VG.Proof.MlDsa.X86_64.Pack.buFin_ok B d) hs (v := s₀.gpr .rdi) (p := s₀.gpr .r8) (s₀ := s₀)
      (by rw [hrd, hlen]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hwr]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hsep) h1 h2 h3 h4 h5)
      fun s' ⟨hc, hf, _⟩ => ⟨?_, hf⟩
    show PolyIs s'.mem (s₀.gpr .r8) (toRq (bitUnpack (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) _ _))
    refine polyIs_of_toNat fun i hi => ?_
    have hy := VG.Proof.MlDsa.X86_64.Pack.field_lt (VG.Proof.MlDsa.X86_64.Pack.inNum s₀.mem (s₀.gpr .rdi) d) d i hs.d20
    have hy' := hy
    unfold VG.Proof.MlDsa.X86_64.Pack.inNum at hy'
    rw [hc i hi, VG.Proof.MlDsa.X86_64.Pack.buWord, VG.Proof.MlDsa.X86_64.Pack.subModQ_toNat (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi,
      hlen, hB, hd, ofInt_sub (by omega)]
  unfold Impl.MlDsa.X86_64.Pack.bitUnpack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.buPro_ok s₀) fun s₁ ⟨⟨cx₁, si₁, m₁⟩, k₁⟩ => ?_)
  have di₁ : s₁.gpr .rdi = s₀.gpr .rdi := k₁.gpr (by decide)
  have cases := VG.Proof.MlDsa.X86_64.Pack.mem_bitPackParams hab
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rcx 2 _ _ s₁ (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_) (fun s₂ ⟨g₂, m₂, rd₂, wr₂⟩ h => ?_)
  · have e : dArg s₀ .rcx = 2 := by rw [← cx₁, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rdx = 2 := by omega
    exact go (d := 3) (c := 8) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₂ (by rw [g₂, di₁]) (by rw [g₂, si₁]) (by rw [rd₂, k₁.2.1])
      (by rw [wr₂, k₁.2.2]) (by rw [m₂, m₁])
  have n2 : dArg s₀ .rcx ≠ 2 := by rw [← cx₁]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₂ : dArg s₂ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₂]; exact cx₁
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rcx 4 _ _ s₂ (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_) (fun s₃ ⟨g₃, m₃, rd₃, wr₃⟩ h => ?_)
  · have e : dArg s₀ .rcx = 4 := by rw [← ds₂, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rdx = 4 := by omega
    exact go (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₃ (by rw [g₃, g₂, di₁]) (by rw [g₃, g₂, si₁])
      (by rw [rd₃, rd₂, k₁.2.1]) (by rw [wr₃, wr₂, k₁.2.2]) (by rw [m₃, m₂, m₁])
  have n4 : dArg s₀ .rcx ≠ 4 := by rw [← ds₂]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₃ : dArg s₃ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₃]; exact ds₂
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rcx 4096 _ _ s₃ (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_) (fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ h => ?_)
  · have e : dArg s₀ .rcx = 4096 := by rw [← ds₃, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rdx = 4095 := by omega
    exact go (d := 13) (c := 8) (nb := 13) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₄ (by rw [g₄, g₃, g₂, di₁]) (by rw [g₄, g₃, g₂, si₁])
      (by rw [rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₄, m₃, m₂, m₁])
  have n4096 : dArg s₀ .rcx ≠ 4096 := by rw [← ds₃]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
  have ds₄ : dArg s₄ .rcx = dArg s₀ .rcx := by unfold dArg; rw [g₄]; exact ds₃
  refine VG.Proof.MlDsa.X86_64.Pack.sel_ok .rcx 131072 _ _ s₄ (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_) (fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ h => ?_)
  · have e : dArg s₀ .rcx = 131072 := by rw [← ds₄, VG.Proof.MlDsa.X86_64.Pack.lo_of_eq h]
    have ea : dArg s₀ .rdx = 131071 := by omega
    exact go (d := 18) (c := 4) (nb := 9) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, si₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])
  · have n131072 : dArg s₀ .rcx ≠ 131072 := by rw [← ds₄]; exact VG.Proof.MlDsa.X86_64.Pack.lo_ne h
    have e : dArg s₀ .rcx = 524288 := by omega
    have ea : dArg s₀ .rdx = 524287 := by omega
    exact go (d := 20) (c := 2) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩ e
      (by decide) (by rw [ea]; decide) s₅ (by rw [g₅, g₄, g₃, g₂, di₁]) (by rw [g₅, g₄, g₃, g₂, si₁])
      (by rw [rd₅, rd₄, rd₃, rd₂, k₁.2.1]) (by rw [wr₅, wr₄, wr₃, wr₂, k₁.2.2]) (by rw [m₅, m₄, m₃, m₂, m₁])

theorem bitUnpack_correct (s : State) (hs : bitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.bitUnpack s t s' ∧ abiPreserved s s' ∧ bitUnpackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.bitUnpack)
    [.rax, .rcx, .rsi, .rdi, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.bu_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

theorem bitUnpack_ct : ConstantTime isa bitUnpackK.pre bitUnpackK.pub Impl.MlDsa.X86_64.Pack.bitUnpack :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .r8, .rsp] [.rdx, .rcx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1])
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [hp.2.2.2.2.1, hp.2.2.2.2.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def bitUnpackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 96 | .rdx => 2 | .rcx => 2 | .r8 => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 96⟩]
  wr := [⟨0x2000, 1024⟩]

theorem bitUnpack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.bitUnpack (bitUnpackContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.bitUnpack_correct VG.Proof.MlDsa.X86_64.Pack.bitUnpack_ct
    { pre := by sig_implies_pre [bitUnpackContract, bitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.bitUnpackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [bitUnpackContract, bitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.bitUnpackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [bitUnpackContract, bitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.bitUnpackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.bitUnpackSat, ?_⟩
        sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | (simp only [bitPackParams]; decide)
          | decide }

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : unpackT1K.pre s₀) :
    WP isa Impl.MlDsa.X86_64.Pack.unpackT1 s₀ fun s' =>
      unpackT1K.post s₀ s' ∧ Frame [pR (s₀.gpr .rsi)] s₀.mem s'.mem := by
  obtain ⟨hrd, hwr, hsep, -, -⟩ := hp
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.unpackLoop_ok VG.Proof.MlDsa.X86_64.Pack.t1Fin_ok (c := 4) (nb := 5) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
    (v := s₀.gpr .rdi) (p := s₀.gpr .rsi) (s₀ := s₀)
    (by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hwr]; exact List.mem_singleton_self _) hsep rfl rfl rfl rfl rfl) fun s' ⟨hc, hf, _⟩ => ⟨?_, hf⟩
  refine polyIs_of_toNat fun i hi => ?_
  have hy : VG.Proof.MlDsa.X86_64.Pack.inNum s₀.mem (s₀.gpr .rdi) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, VG.Proof.MlDsa.X86_64.Pack.t1Word, rotr_toNat _ (by decide) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), Vector.getElem_map, simpleBitUnpack_get _ _ hi,
    show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem unpackT1_correct (s : State) (hs : unpackT1K.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.unpackT1 s t s' ∧ abiPreserved s s' ∧ unpackT1K.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.unpackT1)
    [.rax, .rcx, .rsi, .rdi, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.t1_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2)), hb⟩

theorem unpackT1_ct : ConstantTime isa unpackT1K.pre unpackT1K.pub Impl.MlDsa.X86_64.Pack.unpackT1 :=
  VG.Taint.constantTime (A := taint) (regsLo [.rdi, .rsi, .rsp] [])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
      fun r hr => absurd hr List.not_mem_nil)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def unpackT1Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

theorem unpackT1_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.unpackT1 (unpackT1Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.unpackT1_correct VG.Proof.MlDsa.X86_64.Pack.unpackT1_ct
    { pre := by sig_implies_pre [unpackT1Contract, unpackT1Sig, VG.Proof.MlDsa.X86_64.Pack.unpackT1K, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [unpackT1Contract, unpackT1Sig, VG.Proof.MlDsa.X86_64.Pack.unpackT1K, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [unpackT1Contract, unpackT1Sig, VG.Proof.MlDsa.X86_64.Pack.unpackT1K, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.unpackT1Sat, ?_⟩
        sig_pre [unpackT1Contract, unpackT1Sig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack

end
