import VerifiedGarbage.Impl.MlDsa.X86.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Pack.Written
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Pack.Bits
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlDsa.X86.Pack.Encode
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Pack.Arith

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.Stream`. -/
section

/-!
# ML-DSA on x86 (32-bit): streaming fields through `ebx`

The group bodies of `Impl/MlDsa/X86/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`), as on
x86-64:

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

The accumulator is a slice of the number throughout (`Pack/Stream.lean`),
of at most `d + 7 ≤ 27` bits.
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlKem.X86 (rotr_small toNat_shr)
open VG.Proof.MlDsa.Pack

/-- `x + d` of a 32-bit `x`, where nothing wraps around. -/
theorem toNat_add_fit {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).toNat = x.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt h]

/-- `ebx ← ebx + eax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 32) (s : State) (hx : (s.gpr .eax).toNat < 2 ^ (32 - sh))
    (hs : (s.gpr .ebx).toNat + (s.gpr .eax).toNat * 2 ^ sh < 2 ^ 32) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .ebx).toNat = (s.gpr .ebx).toNat + (s.gpr .eax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.eax, .ebx] s s' := by
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
    xrun [show 1 ≤ 32 - sh by omega, show 32 - sh ≤ 31 by omega, and_self]
    rw [BitVec.toNat_add, rotr_small _ (by omega) (by omega) hx, show 32 - (32 - sh) = sh by omega,
      Nat.mod_eq_of_lt hs]

theorem ebxZero_ok (s : State) :
    WP isa (.block [.mov .ebx (.imm 0)]) s fun s' => (s'.gpr .ebx = 0 ∧ s'.mem = s.mem) ∧
      Keep [.ebx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- The end of a group: the pointers advanced, and the counter down. -/
theorem tail_ok (a b : Nat) (s : State) :
    WP isa (.block [.alu .add .esi (.imm (BitVec.ofNat 32 a)), .alu .add .edi (.imm (BitVec.ofNat 32 b)),
      .alu .sub .ecx (.imm 1)]) s fun s' =>
      (s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 a ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 b ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧ s'.mem = s.mem) ∧
      Keep [.esi, .edi, .ecx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (addr (s.gpr .edi) t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (addr (s.gpr .edi) t) (BitVec.setWidth 8 (s.gpr .ebx)) ∧
        s'.gpr .ebx = s.gpr .ebx >>> 8) ∧ Keep [.ebx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [hout]

/-- The bytes `k, …, k + nf - 1` of the output from the accumulator `X`,
whose byte `u` is byte `k + u` of the output. -/
theorem flush_ok {k nf : Nat} {m₀ : Mem} {E : BitVec 32} {V8 : Nat → Byte} (X : Nat)
    (hX : ∀ u < nf, BitVec.ofNat 8 (X / 2 ^ (8 * u)) = V8 (k + u)) (hk : E.toNat + (k + nf) ≤ 2 ^ 32)
    (s : State) (h8 : s.gpr .edi = E)
    (hout : ∀ u < nf, InRegions s.wr (E.setWidth 64 + BitVec.ofNat 64 (k + u)) 1)
    (hw : Written m₀ s.mem (E.setWidth 64) k V8) (hr : (s.gpr .ebx).toNat = X) :
    WP isa (.block ((List.range nf).flatMap fun u => packByte (k + u))) s fun s' =>
      Written m₀ s'.mem (E.setWidth 64) (k + nf) V8 ∧ (s'.gpr .ebx).toNat = X / 2 ^ (8 * nf) ∧
        Keep [.ebx] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.ebx] s s' ∧
    (s'.gpr .ebx).toNat = X / 2 ^ (8 * u) ∧ Written m₀ s'.mem (E.setWidth 64) (k + u) V8)
    (fun u s' hu ⟨hkp, hr', hw'⟩ => ?_) nf (Nat.le_refl _) s ⟨Keep.refl _ _, by simp [hr], hw⟩)
    fun s' ⟨hkp, hr', hw'⟩ => ⟨hw', hr', hkp⟩
  have h8' : s'.gpr .edi = E := (hkp.gpr (by decide)).trans h8
  have ha : addr (s'.gpr .edi) (k + u) = E.setWidth 64 + BitVec.ofNat 64 (k + u) := by
    rw [h8']; exact addr_of_fit (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.packByte_ok (k + u) s' (by rw [ha, hkp.2.2]; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, toNat_shr, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, ha]
    refine (hw'.snoc (by omega) _).congr fun t ht => ?_
    by_cases e : t = k + u
    · subst e; rw [ifp rfl, b8_eq, hr', hX u hu]
    · rw [ifn e]

/-- `ld j` loads into `eax` the value `F` of the word at `esi + 4j`, and
writes only `eax` and `edx`. -/
def LdOk (ld : Nat → List Instr) (F : BitVec 32 → Nat) : Prop :=
  ∀ j s, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4 →
    WP isa (.block (ld j)) s fun s' =>
      ((s'.gpr .eax).toNat = F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) ∧ s'.mem = s.mem) ∧
        Keep [.eax, .edx] s s'

/-- The bytes of `G`. -/
abbrev bytesOf (G : Nat) (t : Nat) : Byte := BitVec.ofNat 8 (G / 2 ^ (8 * t))

theorem div8_le_succ (d j : Nat) : d * j / 8 ≤ d * (j + 1) / 8 :=
  Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)

/-- Field `j`: its value, digit `j` of `G`, into `ebx`, then the bytes it
completes. -/
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.X86.Pack.LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} {E : BitVec 32} (s : State) (h8 : s.gpr .edi = E)
    (hfit : E.toNat + d * (j + 1) / 8 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4)
    (hv : F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (E.setWidth 64 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (E.setWidth 64) (d * j / 8) (VG.Proof.MlDsa.X86.Pack.bytesOf G))
    (hr : (s.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (E.setWidth 64) (d * (j + 1) / 8) (VG.Proof.MlDsa.X86.Pack.bytesOf G) ∧
        (s'.gpr .ebx).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.eax, .ebx, .edx] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .eax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by
    rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.shiftAdd_ok (sh := d * j % 8) (by omega) s₁
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))) (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hX : (s₂.gpr .ebx).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8₂ : s₂.gpr .edi = E := by rw [k₂.gpr (by decide), k₁.gpr (by decide), h8]
  have hle := VG.Proof.MlDsa.X86.Pack.div8_le_succ d j
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (E := E)
    (V8 := VG.Proof.MlDsa.X86.Pack.bytesOf G) _ (fun u hu => ?_) (by omega) s₂ h8₂ (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega
      omega)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by omega] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by omega]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `edi`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : VG.Proof.MlDsa.X86.Pack.LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (s : State)
    (hfit : (s.gpr .edi).toNat + nb ≤ 2 ^ 32)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨addr (s.gpr .esi) (4 * j), 4⟩ ⟨(s.gpr .edi).setWidth 64, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem ((s.gpr .edi).setWidth 64) nb (VG.Proof.MlDsa.X86.Pack.bytesOf (digits d ((List.range c).map fun j =>
          F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32)))) ∧
        s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (4 * c) ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 nb ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧
        Keep [.eax, .ecx, .edx, .ebx, .esi, .edi] s s' := by
  generalize hG : digits d ((List.range c).map fun j => F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32)) = G
  have hdig : ∀ j < c, G / 2 ^ (d * j) % 2 ^ d = F (s.mem.readW (addr (s.gpr .esi) (4 * j)) 32) :=
    fun j hj => by rw [← hG]; exact digits_range_get hF hj
  unfold packBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.ebxZero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have si₁ : s₁.gpr .esi = s.gpr .esi := k₁.gpr (by decide)
  have di₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.eax, .ebx, .edx] s₁ s' ∧
      Written s.mem s'.mem ((s.gpr .edi).setWidth 64) (d * j / 8) (VG.Proof.MlDsa.X86.Pack.bytesOf G) ∧
      (s'.gpr .ebx).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have si : s'.gpr .esi = s.gpr .esi := (hk.gpr (by decide)).trans si₁
    have di : s'.gpr .edi = s.gpr .edi := (hk.gpr (by decide)).trans di₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega); omega
    refine WP.mono (VG.Proof.MlDsa.X86.Pack.packCoef_ok hld (G := G) (m₀ := s.mem) hd s' di (by omega)
      (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, si]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2]; exact hout t (by omega)) hw hr)
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [si, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨(s.gpr .edi).setWidth 64, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega
    rw [hc8] at hw₂
    refine WP.mono (VG.Proof.MlDsa.X86.Pack.tail_ok (4 * c) nb s₂)
      fun s₃ ⟨⟨si₃, di₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

theorem unpackByte_ok (d j t : Nat) (hsh : 8 * t - d * j ≤ 24) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hs : (s.gpr .ebx).toNat + (s.mem (addr (s.gpr .esi) t)).toNat * 2 ^ (8 * t - d * j) < 2 ^ 32) :
    WP isa (.block (unpackByte d j t)) s fun s' =>
      ((s'.gpr .ebx).toNat =
          (s.gpr .ebx).toNat + (s.mem (addr (s.gpr .esi) t)).toNat * 2 ^ (8 * t - d * j) ∧
        s'.mem = s.mem) ∧ Keep [.eax, .ebx] s s' := by
  unfold unpackByte
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax] (Q := fun s' => s'.gpr .eax = BitVec.setWidth 32 (s.mem (addr (s.gpr .esi) t)) ∧
    s'.mem = s.mem) (by xrun [hin]) (by rfl)) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hb := (s.mem (addr (s.gpr .esi) t)).isLt
  have hax : (s₁.gpr .eax).toNat = (s.mem (addr (s.gpr .esi) t)).toNat := by
    rw [ax₁, toNat_setWidth32_8]
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.shiftAdd_ok (by omega) s₁ (by
      rw [hax]; exact Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    (by rw [hax, k₁.gpr (by decide)]; exact hs))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ⟨⟨by rw [r₂, hax, k₁.gpr (by decide)], by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by decide)⟩

/-- Bytes `k, …, k + nl - 1` of `H` into the accumulator, which holds bits
`d·j` to `8k` of `H`. -/
theorem loadBytes_ok {d j k nl : Nat} (H : Nat) (hd : d ≤ 20) (hdk : d * j ≤ 8 * k)
    (hk : 8 * (k + nl) ≤ d * j + d + 7) (s : State)
    (hin : ∀ u < nl, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (k + u)) 1)
    (hb : ∀ u < nl, (s.mem (addr (s.gpr .esi) (k + u))).toNat = H / 2 ^ (8 * (k + u)) % 2 ^ 8)
    (hr : (s.gpr .ebx).toNat = H % 2 ^ (8 * k) / 2 ^ (d * j)) :
    WP isa (.block ((List.range nl).flatMap fun u => unpackByte d j (k + u))) s fun s' =>
      (s'.gpr .ebx).toNat = H % 2 ^ (8 * (k + nl)) / 2 ^ (d * j) ∧ s'.mem = s.mem ∧ Keep [.eax, .ebx] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun u s' => Keep [.eax, .ebx] s s' ∧ s'.mem = s.mem ∧
    (s'.gpr .ebx).toNat = H % 2 ^ (8 * (k + u)) / 2 ^ (d * j))
    (fun u s' hu ⟨hkp, hm, hr'⟩ => ?_) nl (Nat.le_refl _) s ⟨Keep.refl _ _, rfl, hr⟩)
    fun s' ⟨hkp, hm, hr'⟩ => ⟨hr', hm, hkp⟩
  have si : s'.gpr .esi = s.gpr .esi := hkp.gpr (by decide)
  have hacc := unpack_acc_lt H (k + u) (d * j)
  have hbu := hb u hu
  rw [← hm, ← si] at hbu
  have hbl : (s'.mem (addr (s'.gpr .esi) (k + u))).toNat < 2 ^ 8 := by
    rw [hbu]; exact Nat.mod_lt _ (by decide)
  have hsh : 8 * (k + u) - d * j ≤ 19 := by omega
  have hp : 2 ^ (8 * (k + u) - d * j) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) hsh
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.unpackByte_ok d j (k + u) (by omega) s' (by rw [hkp.2.1, hkp.2.2, si]; exact hin u hu) (by
      rw [hr']
      have := Nat.mul_lt_mul_of_lt_of_le hbl (Nat.le_refl (2 ^ (8 * (k + u) - d * j))) (Nat.two_pow_pos _)
      have : 2 ^ (8 * (k + u) - d * j) * 2 ^ 8 ≤ 2 ^ 19 * 2 ^ 8 := Nat.mul_le_mul_right _ hp
      have : 2 ^ (8 * (k + u) - d * j) < 2 ^ 20 := by omega
      omega))
    fun s'' ⟨⟨r'', m''⟩, k''⟩ => ⟨(hkp.trans k'').mono (by decide), m''.trans hm, ?_⟩
  rw [r'', hr', hbu, unpack_add H (k + u) (d * j) (by omega), Nat.add_assoc]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `eax` to
`edi + 4j`, and writes only `eax` and `edx`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (addr (s.gpr .edi) (4 * j)) 4 → (s.gpr .eax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .edi) (4 * j)) (W (s.gpr .eax).toNat) ∧ Keep [.eax, .edx] s s'

theorem extract_ok (d : Nat) (hd1 : 1 ≤ d) (hd : d ≤ 20) (s : State) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ d - 1))),
      .shift .shr .ebx d]) s fun s' =>
      ((s'.gpr .eax).toNat = (s.gpr .ebx).toNat % 2 ^ d ∧ s'.gpr .ebx = s.gpr .ebx >>> d ∧ s'.mem = s.mem) ∧
        Keep [.eax, .ebx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [show 1 ≤ d by omega, show d ≤ 31 by omega, and_self]
  exact Proof.MlKem.X86.toNat_and_mask _ _ (by omega)

/-- Field `j`: the bytes it needs into `ebx`, then its value, digit `j`
of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.X86.Pack.FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {H j : Nat} (s : State)
    (hin : ∀ t < need d (j + 1), InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hb : ∀ t < need d (j + 1), (s.mem (addr (s.gpr .esi) t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (addr (s.gpr .edi) (4 * j)) 4)
    (hr : (s.gpr .ebx).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j)) :
    WP isa (.block (unpackCoef fin d j)) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .edi) (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        (s'.gpr .ebx).toNat = H % 2 ^ (8 * need d (j + 1)) / 2 ^ (d * (j + 1)) ∧
        Keep [.eax, .ebx, .edx] s s' := by
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hn : need d j ≤ need d (j + 1) := Nat.div_le_div_right (by omega)
  have hn' : need d j + (need d (j + 1) - need d j) = need d (j + 1) := by omega
  unfold unpackCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.loadBytes_ok (k := need d j) (nl := need d (j + 1) - need d j) H hd
    (by unfold need; omega) (by rw [hn']; unfold need; omega) s (fun u hu => hin _ (by omega))
    (fun u hu => hb _ (by omega)) hr) fun s₁ ⟨r₁, m₁, k₁⟩ => ?_
  rw [hn'] at r₁
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.extract_ok d hd1 hd s₁) fun s₂ ⟨⟨ax₂, r₂, m₂⟩, k₂⟩ => ?_
  have hv : (s₂.gpr .eax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, r₁, unpack_field H _ d j (by unfold need; omega)]
  have di : s₂.gpr .edi = s.gpr .edi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, di]; exact hout) (by rw [hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, di, hv, m₂, m₁], ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [k₃.gpr (by decide), r₂, toNat_shr, r₁, unpack_shift]

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `esi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : VG.Proof.MlDsa.X86.Pack.FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hfit : (s.gpr .edi).toNat + 4 * c ≤ 2 ^ 32)
    (hin : ∀ t < nb, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) t) 1)
    (hout : ∀ j < c, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : ∀ t < nb, Region.Disjoint ⟨addr (s.gpr .esi) t, 1⟩ ⟨(s.gpr .edi).setWidth 64, 4 * c⟩) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      (∀ j < c, s'.mem.readW ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 =
        W (digits 8 ((List.range nb).map fun t => (s.mem (addr (s.gpr .esi) t)).toNat) /
          2 ^ (d * j) % 2 ^ d)) ∧
        Frame [⟨(s.gpr .edi).setWidth 64, 4 * c⟩] s.mem s'.mem ∧
        s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 nb ∧ s'.gpr .edi = s.gpr .edi + BitVec.ofNat 32 (4 * c) ∧
        s'.gpr .ecx = s.gpr .ecx - 1 ∧ s'.zf = some (s.gpr .ecx - 1 == 0) ∧
        Keep [.eax, .ecx, .edx, .ebx, .esi, .edi] s s' := by
  generalize hH : digits 8 ((List.range nb).map fun t => (s.mem (addr (s.gpr .esi) t)).toNat) = H
  have hbyte : ∀ t < nb, H / 2 ^ (8 * t) % 2 ^ 8 = (s.mem (addr (s.gpr .esi) t)).toNat :=
    fun t ht => by rw [← hH]; exact digits_range_get (fun t _ => BitVec.isLt _) ht
  have hneed : need d c = nb := by unfold need; omega
  have := Nat.mul_le_mul hd hc
  generalize hP : (s.gpr .edi).setWidth 64 = P at hout hsep ⊢
  have ha : ∀ j < c, addr (s.gpr .edi) (4 * j) = P + BitVec.ofNat 64 (4 * j) := fun j hj => by
    rw [← hP]; exact addr_of_fit (by omega)
  unfold unpackBody
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.ebxZero_ok s) fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_
  have si₁ : s₁.gpr .esi = s.gpr .esi := k₁.gpr (by decide)
  have di₁ : s₁.gpr .edi = s.gpr .edi := k₁.gpr (by decide)
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.eax, .ebx, .edx] s₁ s' ∧
      Frame [⟨P, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (P + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)) ∧
      (s'.gpr .ebx).toNat = H % 2 ^ (8 * need d j) / 2 ^ (d * j))
    (fun j s' hj ⟨hk, hf, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      by simp only [z₁, need, Nat.mul_zero, Nat.zero_add, show 7 / 8 = 0 from rfl, Nat.pow_zero,
        Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hf₂, hw₂, _⟩ => ?_
  · have si : s'.gpr .esi = s.gpr .esi := (hk.gpr (by decide)).trans si₁
    have di : s'.gpr .edi = s.gpr .edi := (hk.gpr (by decide)).trans di₁
    have hnj : need d (j + 1) ≤ nb := by
      rw [← hneed]; exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left d hj) 7)
    refine WP.mono (VG.Proof.MlDsa.X86.Pack.unpackCoef_ok hfin hd1 hd (H := H) s'
      (fun t ht => by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, si]; exact hin t (by omega))
      (fun t ht => by
        rw [si, hbyte t (by omega)]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t (by omega) _ (Region.contains_self _ _))
      (by rw [hk.2.2, k₁.2.2, di, ha j hj]; exact hout j hj) hr)
      fun s'' ⟨m'', r'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_, r''⟩
    · rw [m'', di, ha j hj]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m'', di, ha j hj]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hw j' (by omega)]
  · refine WP.mono (VG.Proof.MlDsa.X86.Pack.tail_ok nb (4 * c) s₂)
      fun s₃ ⟨⟨si₃, di₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj]
    · rw [si₃, k₂.gpr (by decide), si₁]
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.Loop`. -/
section

/-!
# ML-DSA on x86 (32-bit): the loops over the groups, as pieces

In a leaf (whose frame's push leaves the state `P0 s₀`), once the input
pointer `iP s₀` is in `esi` and the output pointer `oP s₀` in `edi` (`Start`):

* `packLoop_piece`: the loop of `packBody` writes the packing of the values
  of the 256 coefficients at `iP s₀`;
* `unpackLoop_piece`: the loop of `unpackBody` writes, for each field of
  the bytes at `iP s₀`, `fin`'s coefficient of it.

Both for any width and any `ld` or `fin`, from the group lemmas of
`Stream.lean`, and constant time: every address depends only on `esp`,
`esi`, `edi` and `ecx`, which correctness determines from the public
pointers (`Piece.countLoop`, given the taint analysis of the loop body).
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.taint Piece.countLoop Piece.seq P0 E0 P0_esp LeafEnd ea_off addr_add
  cnt_next cnt_ne)
open VG.Spec.MlDsa (coeffAt bitsToBytes)
open VG.Spec.Sha3 (bytesAt)
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

theorem Shape.nb20 {d c nb : Nat} (h : VG.Proof.MlDsa.X86.Pack.Shape d c nb) : nb ≤ 20 := by
  have := Nat.mul_le_mul h.d20 h.c8; have := h.dc; omega

theorem Shape.nb0 {d c nb : Nat} (h : VG.Proof.MlDsa.X86.Pack.Shape d c nb) : 0 < nb := by
  have := h.d1; have := h.c0; have := h.dc
  have : 0 < d * c := Nat.mul_pos (by omega) (by omega)
  omega

theorem Shape.group {d c nb : Nat} (h : VG.Proof.MlDsa.X86.Pack.Shape d c nb) {i : Nat} (hi : i < 256 / c) :
    c * i + c ≤ 256 ∧ nb * i + nb ≤ 32 * d := by
  have h1 := Nat.mul_le_mul_left c (show i + 1 ≤ 256 / c by omega)
  have h2 := Nat.mul_le_mul_left nb (show i + 1 ≤ 256 / c by omega)
  rw [Nat.mul_succ] at h1 h2
  have := h.cN; have := h.bN
  omega

theorem Shape.N {d c nb : Nat} (h : VG.Proof.MlDsa.X86.Pack.Shape d c nb) : 0 < 256 / c ∧ 256 / c ≤ 256 :=
  ⟨Nat.div_pos (by have := h.c8; omega) h.c0, Nat.div_le_self _ _⟩

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem inRegions_of {rs : List Region} {r : Region} (hr : r ∈ rs) {a : Addr} {n : Nat} (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

theorem getD_map_toNat (B : List Byte) (k : Nat) : (B.map (·.toNat)).getD k 0 = (B.getD k 0).toNat := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]; cases B[k]? <;> rfl

/-- The loop condition after the counter counted down. -/
theorem ecx_ne {N i : Nat} (hi : i < N) (hN : N < 2 ^ 32) {s s' : State}
    (hc : s.gpr .ecx = BitVec.ofNat 32 (N - i)) (hz : s'.zf = some (s.gpr .ecx - 1 == 0)) :
    eval .ne s' = some (decide (i + 1 < N)) := by
  simp only [eval, hz, hc]; exact cnt_ne hi hN

section
variable (iP oP : State → BitVec 32)

/-- The input pointer, as an address. -/
abbrev iA (s₀ : State) : Addr := (iP s₀).setWidth 64
/-- The output pointer, as an address. -/
abbrev oA (s₀ : State) : Addr := (oP s₀).setWidth 64

/-- In a leaf, once its pointers are loaded. -/
structure Start (s₀ s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  esi : s.gpr .esi = iP s₀
  edi : s.gpr .edi = oP s₀

end

/-- The registers correctness determines in a loop. -/
abbrev loopRegs : List Reg := [.esp, .esi, .edi, .ecx]

/-! ## Packing -/

/-- The values of the coefficients. -/
abbrev vals (F : BitVec 32 → Nat) (m : Mem) (f : Addr) : List Nat := (List.range 256).map fun i => F (coeffAt m f i)

theorem vals_lt {F : BitVec 32 → Nat} {d : Nat} {m : Mem} {f : Addr} (hF : ∀ i < 256, F (coeffAt m f i) < 2 ^ d) :
    ∀ a ∈ VG.Proof.MlDsa.X86.Pack.vals F m f, a < 2 ^ d := fun a ha => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hF i (List.mem_range.mp hi)

section
variable (F : BitVec 32 → Nat) (d c nb : Nat) (iP oP : State → BitVec 32)

/-- The packing of the values of the coefficients at `iP s₀`. -/
abbrev packed (s₀ : State) : List Byte := bitsToBytes (fieldBits d (VG.Proof.MlDsa.X86.Pack.vals F (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀)))

/-- What the pack loop needs of the layout. -/
structure PackOk (s₀ : State) : Prop where
  inR : polyRegion (VG.Proof.MlDsa.X86.Pack.iA iP s₀) ∈ (P0 s₀).rd ++ (P0 s₀).wr
  outR : (⟨VG.Proof.MlDsa.X86.Pack.oA oP s₀, 32 * d⟩ : Region) ∈ (P0 s₀).wr
  sep : Region.Disjoint (polyRegion (VG.Proof.MlDsa.X86.Pack.iA iP s₀)) ⟨VG.Proof.MlDsa.X86.Pack.oA oP s₀, 32 * d⟩
  ifit : (iP s₀).toNat + 1024 ≤ 2 ^ 32
  ofit : (oP s₀).toNat + 32 * d ≤ 2 ^ 32
  lt : ∀ i < 256, F (coeffAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) i) < 2 ^ d

/-- After `i` groups. -/
structure PInv (s₀ : State) (i : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = iP s₀ + BitVec.ofNat 32 (4 * c * i)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (nb * i)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 / c - i)
  frame : Frame [⟨VG.Proof.MlDsa.X86.Pack.oA oP s₀, 32 * d⟩] (P0 s₀).mem s.mem
  done : ∀ k < nb * i, s.mem (VG.Proof.MlDsa.X86.Pack.oA oP s₀ + BitVec.ofNat 64 k) = (VG.Proof.MlDsa.X86.Pack.packed F d iP s₀)[k]!

end

section
variable {ld : Nat → List Instr} {F : BitVec 32 → Nat} {d c nb : Nat} {iP oP : State → BitVec 32}

theorem packStep (hld : VG.Proof.MlDsa.X86.Pack.LdOk ld F) (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) {s₀ : State} (hk : VG.Proof.MlDsa.X86.Pack.PackOk F d iP oP s₀) {i : Nat}
    (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlDsa.X86.Pack.PInv F d c nb iP oP s₀ i s) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      VG.Proof.MlDsa.X86.Pack.PInv F d c nb iP oP s₀ (i + 1) s' ∧ eval .ne s' = some (decide (i + 1 < 256 / c)) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hN := hs.N.2
  have hnb := hs.nb20
  have hnb0 := hs.nb0
  have hd20 := hs.d20
  have fi := hk.ifit
  have fo := hk.ofit
  have ha : ∀ j < c, addr (s.gpr .esi) (4 * j) = coeffAddr (VG.Proof.MlDsa.X86.Pack.iA iP s₀) (c * i + j) := fun j _ => by
    rw [hI.esi, addr_add (by rw [Nat.mul_assoc]; omega)]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have ho : (s.gpr .edi).setWidth 64 = VG.Proof.MlDsa.X86.Pack.oA oP s₀ + BitVec.ofNat 64 (nb * i) := by
    rw [hI.edi]; exact ea_off (by omega)
  have hb : ∀ t, (s.gpr .edi).setWidth 64 + BitVec.ofNat 64 t = VG.Proof.MlDsa.X86.Pack.oA oP s₀ + BitVec.ofNat 64 (nb * i + t) :=
    fun t => by rw [ho, VG.Proof.MlDsa.X86.Pack.off_add]
  -- The words of the group are those on entry.
  have hw : ∀ j < c, s.mem.readW (addr (s.gpr .esi) (4 * j)) 32 = coeffAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) (c * i + j) :=
    fun j hj => by
      rw [ha j hj]
      exact coeffAt_frame hI.frame (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hk.sep)
        (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.packBody_ok hld hs.d20 hs.dc s (by rw [hI.edi, VG.Proof.MlDsa.X86.Pack.toNat_add_fit (by omega)]; omega)
    (fun j hj => by rw [ha j hj, hI.rd, hI.wr]; exact VG.Proof.MlDsa.X86.Pack.inRegions_of hk.inR (coeff_contains _ (by omega)))
    (fun t ht => by rw [hb, hI.wr]; exact VG.Proof.MlDsa.X86.Pack.inRegions_of hk.outR (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by
      rw [ha j hj, ho]
      exact (hk.sep.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)))
    (fun j hj => by rw [hw j hj]; exact hk.lt _ (by omega)))
    fun s' ⟨hW, si', di', cx', z', k'⟩ => ⟨?_, VG.Proof.MlDsa.X86.Pack.ecx_ne hi (by omega) hI.ecx z'⟩
  have hW' : Written s.mem s'.mem (VG.Proof.MlDsa.X86.Pack.oA oP s₀ + BitVec.ofNat 64 (nb * i)) nb
      fun t => (VG.Proof.MlDsa.X86.Pack.packed F d iP s₀)[nb * i + t]! := by
    rw [← ho]
    refine hW.congr fun t ht => ?_
    rw [pack_group (c := c) (by have := hs.d1; omega) hs.dc (by simp) (VG.Proof.MlDsa.X86.Pack.vals_lt hk.lt) ht (by omega),
      take_drop_eq _ 0 (by simp; omega)]
    refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * t))) (List.map_congr_left fun j hj => ?_)
    have hj := List.mem_range.mp hj
    rw [hw j hj, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  obtain ⟨hf', hd'⟩ := Written.step hI.frame hI.done hW' hbi (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hf', fun k hk => hd' k (by rw [Nat.mul_succ] at hk; omega)⟩
  · rw [k'.gpr (by decide), hI.esp]
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · rw [si', hI.esi]; exact ptr_step _ i (4 * c)
  · rw [di', hI.edi]; exact ptr_step _ i nb
  · rw [cx', hI.ecx]; exact cnt_next hi

variable {Pre : State → Prop} {Pub : State → State → Prop} {X : State → Prop}

/-- All the groups: the bytes of the packing. -/
theorem packLoop_piece (hld : VG.Proof.MlDsa.X86.Pack.LdOk ld F) (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) (iP oP : State → BitVec 32)
    (hok : ∀ s₀, Pre s₀ → X s₀ → VG.Proof.MlDsa.X86.Pack.PackOk F d iP oP s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀' ∧ iP s₀ = iP s₀' ∧ oP s₀ = oP s₀')
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr VG.Proof.MlDsa.X86.Pack.loopRegs) (.block (packBody ld d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ X s₀)
      (fun s₀ s => (LeafEnd s₀ [⟨VG.Proof.MlDsa.X86.Pack.oA oP s₀, 32 * d⟩] s ∧ bytesAt s.mem (VG.Proof.MlDsa.X86.Pack.oA oP s₀) (32 * d) = VG.Proof.MlDsa.X86.Pack.packed F d iP s₀) ∧
        X s₀) (packLoop ld d c nb) := by
  have hN := hs.N
  refine (Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Pack.PInv F d c nb iP oP s₀ 0 s ∧ X s₀)
    (Piece.taint [] (fun s₀ s _ ⟨h, hx⟩ => ?wp) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht₁)
    (Piece.countLoop hN.1 (fun i s₀ s => VG.Proof.MlDsa.X86.Pack.PInv F d c nb iP oP s₀ i s ∧ X s₀) VG.Proof.MlDsa.X86.Pack.loopRegs
      (fun i hi s₀ s h₀ ⟨h, hx⟩ => (VG.Proof.MlDsa.X86.Pack.packStep hld hs (hok s₀ h₀ hx) hi h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hx⟩, e⟩)
      (fun i _ s₀ s₀' s s' h₀ h₀' hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?regs) ht₂)).mono (fun _ _ _ h => h) ?post
  case wp =>
    xrun
    refine ⟨⟨?_, h.rd, h.wr, ?_, ?_, ?_, by rw [setReg_mem, h.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩, hx⟩ <;>
    simp only [reduceCtorEq, ↓reduceIte, setReg_gpr, h.esp, h.esi, h.edi,
      Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
  case regs =>
    obtain ⟨e₀, e₁, e₂⟩ := hpub _ _ h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.esp, h'.esp, P0_esp, P0_esp, e₀]
    · rw [h.esi, h'.esi, e₁]
    · rw [h.edi, h'.edi, e₂]
    · rw [h.ecx, h'.ecx]
  case post =>
    intro s₀ s h₀ ⟨h, hx⟩
    refine ⟨⟨⟨h.frame, h.esp, h.rd, h.wr⟩, bytesAt_eq! (pack_length d _ (by simp)) fun k hk => h.done k ?_⟩, hx⟩
    rw [hs.bN]; exact hk

end

/-! ## Unpacking -/

/-- The number whose bytes are the input. -/
abbrev inNum (m : Mem) (v : Addr) (d : Nat) : Nat := digits 8 ((bytesAt m v (32 * d)).map (·.toNat))

section
variable (W : Nat → BitVec 32) (d c nb : Nat) (iP oP : State → BitVec 32)

/-- What the unpack loop needs of the layout. -/
structure UnpackOk (s₀ : State) : Prop where
  inR : (⟨VG.Proof.MlDsa.X86.Pack.iA iP s₀, 32 * d⟩ : Region) ∈ (P0 s₀).rd ++ (P0 s₀).wr
  outR : polyRegion (VG.Proof.MlDsa.X86.Pack.oA oP s₀) ∈ (P0 s₀).wr
  sep : Region.Disjoint ⟨VG.Proof.MlDsa.X86.Pack.iA iP s₀, 32 * d⟩ (polyRegion (VG.Proof.MlDsa.X86.Pack.oA oP s₀))
  ifit : (iP s₀).toNat + 32 * d ≤ 2 ^ 32
  ofit : (oP s₀).toNat + 1024 ≤ 2 ^ 32

/-- After `i` groups. -/
structure UInv (s₀ : State) (i : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = iP s₀ + BitVec.ofNat 32 (nb * i)
  edi : s.gpr .edi = oP s₀ + BitVec.ofNat 32 (4 * c * i)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 / c - i)
  frame : Frame [polyRegion (VG.Proof.MlDsa.X86.Pack.oA oP s₀)] (P0 s₀).mem s.mem
  done : ∀ k < c * i, coeffAt s.mem (VG.Proof.MlDsa.X86.Pack.oA oP s₀) k = W (VG.Proof.MlDsa.X86.Pack.inNum (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) d / 2 ^ (d * k) % 2 ^ d)

end

section
variable {fin : Nat → List Instr} {W : Nat → BitVec 32} {d c nb : Nat} {iP oP : State → BitVec 32}

theorem unpackStep (hfin : VG.Proof.MlDsa.X86.Pack.FinOk fin d W) (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) {s₀ : State} (hk : VG.Proof.MlDsa.X86.Pack.UnpackOk d iP oP s₀)
    {i : Nat} (hi : i < 256 / c) {s : State} (hI : VG.Proof.MlDsa.X86.Pack.UInv W d c nb iP oP s₀ i s) :
    WP isa (.block (unpackBody fin d c nb)) s fun s' =>
      VG.Proof.MlDsa.X86.Pack.UInv W d c nb iP oP s₀ (i + 1) s' ∧ eval .ne s' = some (decide (i + 1 < 256 / c)) := by
  obtain ⟨hci, hbi⟩ := hs.group hi
  have hN := hs.N.2
  have hnb := hs.nb20
  have hd20 := hs.d20
  have hc0 := hs.c0
  have fi := hk.ifit
  have fo := hk.ofit
  have ho : (s.gpr .edi).setWidth 64 = VG.Proof.MlDsa.X86.Pack.oA oP s₀ + BitVec.ofNat 64 (4 * c * i) := by
    rw [hI.edi]; exact ea_off (by rw [Nat.mul_assoc]; omega)
  have ha : ∀ j, (s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (4 * j) = coeffAddr (VG.Proof.MlDsa.X86.Pack.oA oP s₀) (c * i + j) :=
    fun j => by rw [ho, VG.Proof.MlDsa.X86.Pack.off_add]; congr 2; rw [Nat.mul_add, Nat.mul_assoc]
  have hb : ∀ t < nb, addr (s.gpr .esi) t = VG.Proof.MlDsa.X86.Pack.iA iP s₀ + BitVec.ofNat 64 (nb * i + t) := fun t ht => by
    rw [hI.esi]; exact addr_add (by omega)
  have hsub : Region.Sub ⟨(s.gpr .edi).setWidth 64, 4 * c⟩ (polyRegion (VG.Proof.MlDsa.X86.Pack.oA oP s₀)) := by
    rw [ho]; exact Offset.sub_base _ (by rw [Nat.mul_assoc]; omega)
  refine WP.mono (VG.Proof.MlDsa.X86.Pack.unpackBody_ok hfin hs.d1 hs.d20 hs.dc hs.c8 s
    (by rw [hI.edi, VG.Proof.MlDsa.X86.Pack.toNat_add_fit (by rw [Nat.mul_assoc]; omega)]; rw [Nat.mul_assoc]; omega)
    (fun t ht => by rw [hb t ht, hI.rd, hI.wr]; exact VG.Proof.MlDsa.X86.Pack.inRegions_of hk.inR (Offset.contains_base _ (by omega) (by omega)))
    (fun j hj => by rw [ha, hI.wr]; exact VG.Proof.MlDsa.X86.Pack.inRegions_of hk.outR (coeff_contains _ (by omega)))
    (fun t ht => by
      rw [hb t ht]
      exact (hk.sep.sub_left (Offset.sub_base _ (by omega))).sub_right hsub))
    fun s' ⟨hw, hf, si', di', cx', z', k'⟩ => ⟨?_, VG.Proof.MlDsa.X86.Pack.ecx_ne hi (by omega) hI.ecx z'⟩
  -- The bytes of the group, on entry.
  have hB : (List.range nb).map (fun t => (s.mem (addr (s.gpr .esi) t)).toNat) =
      (((bytesAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) (32 * d)).map (·.toNat)).drop (nb * i)).take nb := by
    rw [take_drop_eq _ 0 (by rw [List.length_map, bytesAt_length]; omega)]
    refine List.map_congr_left fun t ht => ?_
    have ht := List.mem_range.mp ht
    rw [VG.Proof.MlDsa.X86.Pack.getD_map_toNat, bytesAt_getD _ _ (by omega), hb t ht]
    refine congrArg BitVec.toNat (hI.frame _ fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact hk.sep _ (Offset.contains_base _ (by omega) (by omega))
  have hlt : ∀ a ∈ (bytesAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) (32 * d)).map (·.toNat), a < 2 ^ 8 := fun a ha => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha; exact x.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hI.frame.trans (hf.sub fun r hr => ?_), fun k hk => ?_⟩
  · rw [k'.gpr (by decide), hI.esp]
  · rw [k'.2.1, hI.rd]
  · rw [k'.2.2, hI.wr]
  · rw [si', hI.esi]; exact ptr_step _ i nb
  · rw [di', hI.edi]; exact ptr_step _ i (4 * c)
  · rw [cx', hI.ecx]; exact cnt_next hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩
  by_cases hk' : k < c * i
  · -- Written before.
    rw [← hI.done k hk', coeffAt_eq, coeffAt_eq]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [ho]
    exact Offset.disjoint _ (by rw [Nat.mul_assoc]; omega) (by omega) (by rw [Nat.mul_assoc]; omega)
  · -- Written by this group.
    have hj : k - c * i < c := by rw [Nat.mul_succ] at hk; omega
    have := hw (k - c * i) hj
    rw [ha, show c * i + (k - c * i) = k by omega, hB, digits_group hs.dc hlt hj,
      show c * i + (k - c * i) = k by omega] at this
    rw [coeffAt_eq, this]

variable {Pre : State → Prop} {Pub : State → State → Prop} {X : State → Prop}

/-- All the groups: `fin`'s coefficient of each field. -/
theorem unpackLoop_piece (hfin : VG.Proof.MlDsa.X86.Pack.FinOk fin d W) (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) (iP oP : State → BitVec 32)
    (hok : ∀ s₀, Pre s₀ → X s₀ → VG.Proof.MlDsa.X86.Pack.UnpackOk d iP oP s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀' ∧ iP s₀ = iP s₀' ∧ oP s₀ = oP s₀')
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr VG.Proof.MlDsa.X86.Pack.loopRegs) (.block (unpackBody fin d c nb)) h₂).isSome = true) :
    Piece Pre Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ X s₀)
      (fun s₀ s => (LeafEnd s₀ [polyRegion (VG.Proof.MlDsa.X86.Pack.oA oP s₀)] s ∧
        ∀ k < 256, coeffAt s.mem (VG.Proof.MlDsa.X86.Pack.oA oP s₀) k = W (VG.Proof.MlDsa.X86.Pack.inNum (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) d / 2 ^ (d * k) % 2 ^ d)) ∧
        X s₀) (unpackLoop fin d c nb) := by
  have hN := hs.N
  refine (Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Pack.UInv W d c nb iP oP s₀ 0 s ∧ X s₀)
    (Piece.taint [] (fun s₀ s _ ⟨h, hx⟩ => ?wp) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht₁)
    (Piece.countLoop hN.1 (fun i s₀ s => VG.Proof.MlDsa.X86.Pack.UInv W d c nb iP oP s₀ i s ∧ X s₀) VG.Proof.MlDsa.X86.Pack.loopRegs
      (fun i hi s₀ s h₀ ⟨h, hx⟩ => (VG.Proof.MlDsa.X86.Pack.unpackStep hfin hs (hok s₀ h₀ hx) hi h).mono fun _ ⟨h', e⟩ => ⟨⟨h', hx⟩, e⟩)
      (fun i _ s₀ s₀' s s' h₀ h₀' hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?regs) ht₂)).mono (fun _ _ _ h => h) ?post
  case wp =>
    xrun
    refine ⟨⟨?_, h.rd, h.wr, ?_, ?_, ?_, by rw [setReg_mem, h.mem]; exact Frame.refl _ _,
      fun k hk => absurd hk (by omega)⟩, hx⟩ <;>
    simp only [reduceCtorEq, ↓reduceIte, setReg_gpr, h.esp, h.esi, h.edi,
      Nat.mul_zero, BitVec.add_zero, Nat.sub_zero]
  case regs =>
    obtain ⟨e₀, e₁, e₂⟩ := hpub _ _ h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h.esp, h'.esp, P0_esp, P0_esp, e₀]
    · rw [h.esi, h'.esi, e₁]
    · rw [h.edi, h'.edi, e₂]
    · rw [h.ecx, h'.ecx]
  case post =>
    intro s₀ s h₀ ⟨h, hx⟩
    exact ⟨⟨⟨h.frame, h.esp, h.rd, h.wr⟩, fun k hk => h.done k (by rw [hs.cN]; exact hk)⟩, hx⟩

end

end VG.Proof.MlDsa.X86.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.Top`. -/
section

/-!
# ML-DSA on x86 (32-bit): the encodings' leaves, loading and branching

Each of the encodings is a leaf with one input and one output buffer, and its
arguments on the stack (`Lay`: what the shared contract says of them on x86).
After the leaf's push, it loads its input pointer (argument `i`) into `esi`,
its output pointer (argument `o`) into `edi`, and its width (argument `w`)
into `eax` (`ldArgs_piece`, `ldPtrs_piece`), and branches on the width
(`sel_piece`) to one of the loops of `Loop.lean`. The branches depend only on
the width, which is public.
-/

namespace VG.Proof.MlDsa.X86.Pack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.taint Piece.seq Piece.ite P0 E0 P0_esp P0_wr frameR retR LeafEnd
  P0_argAddr P0_argIn P0_arg saveRegs_len sub_beq_zero toNat_ofNat32)
open VG.Spec.MlDsa (coeffAt)
open VG.Impl.MlKem.X86 (saveRegs)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

section
variable (k : Nat) (iP oP : State → BitVec 32) (iL oL : State → Nat)

/-- The stack the leaf's frame uses, as the contract states it. -/
abbrev stkR (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
/-- The `k` arguments. -/
abbrev argR (s₀ : State) : Region := ⟨argAddr s₀ 0, 4 * k⟩
/-- The input buffer. -/
abbrev inR (s₀ : State) : Region := ⟨VG.Proof.MlDsa.X86.Pack.iA iP s₀, iL s₀⟩
/-- The output buffer. -/
abbrev outR (s₀ : State) : Region := ⟨VG.Proof.MlDsa.X86.Pack.oA oP s₀, oL s₀⟩

/-- A leaf of `k` arguments that reads the input buffer and writes the
output buffer, as the shared contracts lay them out on x86. -/
structure Lay (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 4 * k ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.MlDsa.X86.Pack.inR iP iL s₀]
  wr : s₀.wr = [VG.Proof.MlDsa.X86.Pack.outR oP oL s₀, VG.Proof.MlDsa.X86.Pack.argR k s₀]
  i_o : (VG.Proof.MlDsa.X86.Pack.inR iP iL s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.outR oP oL s₀)
  i_a : (VG.Proof.MlDsa.X86.Pack.inR iP iL s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.argR k s₀)
  o_a : (VG.Proof.MlDsa.X86.Pack.outR oP oL s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.argR k s₀)
  ret_i : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.inR iP iL s₀)
  ret_o : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.outR oP oL s₀)
  ret_a : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.argR k s₀)
  stk_i : (VG.Proof.MlDsa.X86.Pack.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.inR iP iL s₀)
  stk_o : (VG.Proof.MlDsa.X86.Pack.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.outR oP oL s₀)
  stk_a : (VG.Proof.MlDsa.X86.Pack.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Pack.argR k s₀)
  i_fit : (iP s₀).toNat + iL s₀ ≤ 2 ^ 32
  o_fit : (oP s₀).toNat + oL s₀ ≤ 2 ^ 32

end

namespace Lay

variable {k : Nat} {iP oP : State → BitVec 32} {iL oL : State → Nat} {s₀ : State}
  (hp : VG.Proof.MlDsa.X86.Pack.Lay k iP oP iL oL s₀)
include hp

theorem stk_eq : VG.Proof.MlDsa.X86.Pack.stkR s₀ = frameR s₀ := by
  simp only [VG.Proof.MlDsa.X86.Pack.stkR, frameR, below]; rw [Taint.sub_setWidth hp.sp]

theorem P0_rd : (P0 s₀).rd = [VG.Proof.MlDsa.X86.Pack.inR iP iL s₀] := by rw [pushed_rd, hp.rd]

theorem P0_wr' : (P0 s₀).wr = frameR s₀ :: [VG.Proof.MlDsa.X86.Pack.outR oP oL s₀, VG.Proof.MlDsa.X86.Pack.argR k s₀] := by rw [P0_wr, hp.wr]

theorem push_frame : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.sp)
  rwa [saveRegs_len] at hf

/-- The input buffer is as on entry after the push. -/
theorem in_frame : ∀ r ∈ [frameR s₀], (VG.Proof.MlDsa.X86.Pack.inR iP iL s₀).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]; rw [← hp.stk_eq]; exact hp.stk_i.symm

/-- The coefficients of an input polynomial after the push. -/
theorem coeff_keep (hL : iL s₀ = 1024) {i : Nat} (hi : i < 256) :
    coeffAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) i = coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) i :=
  coeffAt_frame hp.push_frame (fun r hr => by have := hp.in_frame r hr; rwa [VG.Proof.MlDsa.X86.Pack.inR, hL] at this) hi

/-- The input bytes after the push. -/
theorem bytes_keep {n : Nat} (hn : n ≤ iL s₀) : bytesAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) n = bytesAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA iP s₀) n :=
  Proof.MlKem.bytesAt_frame hp.push_frame (fun r hr => (hp.in_frame r hr).sub_left (Region.sub_prefix hn))
    (by have := hp.i_fit; omega)

/-- The leaf's frame and return address are apart from the output. -/
theorem leafW : ∀ r ∈ [VG.Proof.MlDsa.X86.Pack.outR oP oL s₀], (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  simp only [List.mem_singleton, forall_eq]; rw [← hp.stk_eq]; exact ⟨hp.stk_o, hp.ret_o⟩

theorem leafE : 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32 := ⟨hp.sp, by have := hp.sp'; omega⟩

/-- The input buffer, after the push. -/
theorem inR_mem : VG.Proof.MlDsa.X86.Pack.inR iP iL s₀ ∈ (P0 s₀).rd ++ (P0 s₀).wr := by rw [hp.P0_rd]; simp

/-- The output buffer, after the push. -/
theorem outR_mem : VG.Proof.MlDsa.X86.Pack.outR oP oL s₀ ∈ (P0 s₀).wr := by rw [hp.P0_wr']; simp

end Lay

/-! ## Loading the arguments -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {k i o w : Nat} {iL oL : State → Nat}

theorem ldArgs_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Lay k (arg · i) (arg · o) iL oL s₀) (hi : i < k) (ho : o < k)
    (hw : w < k) :
    WP isa (.block (ldArgs i o w)) (P0 s₀) fun s =>
      VG.Proof.MlDsa.X86.Pack.Start (arg · i) (arg · o) s₀ s ∧ s.gpr .eax = arg s₀ w := by
  have fit := hp.sp'
  have hin : VG.Proof.MlDsa.X86.Pack.argR k s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.wr]; simp
  have a₀ := P0_argAddr s₀ i
  have a₁ := P0_argAddr s₀ o
  have a₂ := P0_argAddr s₀ w
  have i₀ := P0_argIn hi fit hin
  have i₁ := P0_argIn ho fit hin
  have i₂ := P0_argIn hw fit hin
  have v₀ := P0_arg hp.sp hi fit hp.stk_a
  have v₁ := P0_arg hp.sp ho fit hp.stk_a
  have v₂ := P0_arg hp.sp hw fit hp.stk_a
  unfold ldArgs ldPtrs
  xrun [addr, List.cons_append, List.nil_append, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁, v₂]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ldPtrs_ok {s₀ : State} (hp : VG.Proof.MlDsa.X86.Pack.Lay k (arg · i) (arg · o) iL oL s₀) (hi : i < k) (ho : o < k) :
    WP isa (.block (ldPtrs i o)) (P0 s₀) fun s => VG.Proof.MlDsa.X86.Pack.Start (arg · i) (arg · o) s₀ s := by
  have fit := hp.sp'
  have hin : VG.Proof.MlDsa.X86.Pack.argR k s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.wr]; simp
  have a₀ := P0_argAddr s₀ i
  have a₁ := P0_argAddr s₀ o
  have i₀ := P0_argIn hi fit hin
  have i₁ := P0_argIn ho fit hin
  have v₀ := P0_arg hp.sp hi fit hp.stk_a
  have v₁ := P0_arg hp.sp ho fit hp.stk_a
  unfold ldPtrs
  xrun [addr, a₀, a₁, i₀, i₁, v₀, v₁]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pointers and the width, from the arguments. -/
theorem ldArgs_piece (hi : i < k) (ho : o < k) (hw : w < k)
    (hL : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Pack.Lay k (arg · i) (arg · o) iL oL s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr [.esp]) (.block (ldArgs i o w)) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀)
      (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Start (arg · i) (arg · o) s₀ s ∧ s.gpr .eax = arg s₀ w) ∧ True) (.block (ldArgs i o w)) :=
  Piece.taint [.esp] (fun s₀ s h₀ e => by
      subst e; exact (VG.Proof.MlDsa.X86.Pack.ldArgs_ok (hL s₀ h₀) hi ho hw).mono fun _ h => ⟨h, trivial⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e, e', P0_esp, P0_esp, hpub _ _ h₀ h₀' hq]) ht

/-- The pointers, from the arguments. -/
theorem ldPtrs_piece (hi : i < k) (ho : o < k)
    (hL : ∀ s₀, Pre s₀ → VG.Proof.MlDsa.X86.Pack.Lay k (arg · i) (arg · o) iL oL s₀)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr [.esp]) (.block (ldPtrs i o)) hc).isSome = true) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start (arg · i) (arg · o) s₀ s ∧ True)
      (.block (ldPtrs i o)) :=
  Piece.taint [.esp] (fun s₀ s h₀ e => by
      subst e; exact (VG.Proof.MlDsa.X86.Pack.ldPtrs_ok (hL s₀ h₀) hi ho).mono fun _ h => ⟨h, trivial⟩)
    (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e, e', P0_esp, P0_esp, hpub _ _ h₀ h₀' hq]) ht

end

/-! ## Branching on the width -/

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {iP oP : State → BitVec 32}

theorem Start.same {s₀ s s' : State} (h : VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s) (hg : s'.gpr = s.gpr) (hm : s'.mem = s.mem)
    (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s' :=
  ⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm, h.mem], by rw [hg, h.esi],
    by rw [hg, h.edi]⟩

theorem cmp_ok (v : Nat) (s : State) :
    WP isa (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.zf = some (s.gpr .eax - BitVec.ofNat 32 v == 0) := by
  xrun

/-- `sel v p e`: `p` if the width `w s₀` (in `eax`) is `v`, and `e` otherwise. -/
theorem sel_piece {X : State → Prop} {B : State → State → Prop} {p e : Prog isa} (w : State → BitVec 32)
    {v : Nat} (hv : v < 2 ^ 32) (hw : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → w s₀ = w s₀')
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))]) hc).isSome = true)
    (hp : Piece Pre Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ (X s₀ ∧ (w s₀).toNat = v)) B p)
    (he : Piece Pre Pub (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ (X s₀ ∧ (w s₀).toNat ≠ v)) B e) :
    Piece Pre Pub (fun s₀ s => (VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ X s₀) B (sel v p e) := by
  refine Piece.seq (B := fun s₀ s => ((VG.Proof.MlDsa.X86.Pack.Start iP oP s₀ s ∧ s.gpr .eax = w s₀) ∧ X s₀) ∧
      eval .e s = some (decide ((w s₀).toNat = v)))
    (Piece.taint [] (fun s₀ s _ ⟨⟨h, ha⟩, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht)
    (Piece.ite (fun s₀ => decide ((w s₀).toNat = v)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' h₀ h₀' hq => by rw [hw _ _ h₀ h₀' hq])
      (hp.mono (fun _ _ _ ⟨⟨⟨⟨h, _⟩, hx⟩, _⟩, e⟩ => ⟨h, hx, of_decide_eq_true e⟩) fun _ _ _ h => h)
      (he.mono (fun _ _ _ ⟨⟨⟨h, hx⟩, _⟩, e⟩ => ⟨h, hx, of_decide_eq_false e⟩) fun _ _ _ h => h))
  refine (VG.Proof.MlDsa.X86.Pack.cmp_ok v s).mono fun s' ⟨hg, hm, hr, hw', hz⟩ => ⟨⟨⟨h.same hg hm hr hw', by rw [hg, ha]⟩, hx⟩, ?_⟩
  simp only [eval, hz, ha, sub_beq_zero, toNat_ofNat32 hv]

end

end VG.Proof.MlDsa.X86.Pack

namespace VG.Proof.MlDsa.X86.Pack

open VG.Spec.MlDsa (coeffAt)

/-! ## Satisfiability -/

/-- A polynomial in memory that is zero below `0x5000` (where the witnesses
of satisfiability put their buffers, with their arguments above) is zero. -/
theorem coeffAt_low {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) {p : Addr}
    (hp : p.toNat + 1024 ≤ 0x5000) {i : Nat} (hi : i < 256) : coeffAt m p i = 0 := by
  rw [coeffAt, Mem.readW_congr (m' := fun _ => 0) fun j hj => hm _ ?_]
  · simp [Mem.readW, Mem.read]
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- The memory of a witness: `ws` at `0x5000 + a` for each `(a, ws)`, zero elsewhere. -/
theorem ite_low {a b : Addr} {x y : Byte} (ha : a.toNat < 0x5000) (hb : 0x5000 ≤ b.toNat) :
    (if a = b then x else y) = y :=
  ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by omega)

end VG.Proof.MlDsa.X86.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.SimpleBitPack`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_simple_bit_pack`

`simpleBitPack(f, b, out, len)` loads `f` into `esi`, `out` into `edi` and `b`
into `eax`, and branches on `b` (15, 43 or 1023) to the pack loop for its
width (`packLoop_piece`), whose value of a coefficient is the coefficient.
-/

namespace VG.Proof.MlDsa.X86.Pack.SimpleBitPack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack

theorem sbpLd_ok : VG.Proof.MlDsa.X86.Pack.LdOk sbpLd BitVec.toNat := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold sbpLd
  xrun [hin]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

section
variable (s₀ : State)
/-- The input pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 0)
/-- The output pointer `out`. -/
abbrev oP : State → BitVec 32 := (arg · 2)
/-- The length of the output. -/
abbrev oL : State → Nat := fun s₀ => (arg s₀ 3).toNat
/-- The bound `b`. -/
abbrev bN : Nat := (arg s₀ 1).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : VG.Proof.MlDsa.X86.Pack.Lay 4 VG.Proof.MlDsa.X86.Pack.SimpleBitPack.fP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP (fun _ => 1024) VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL s₀
  b_mem : VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN s₀ ∈ simpleBitPackBounds
  len_eq : (arg s₀ 3).toNat = 32 * bitlen (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN s₀)
  le : ∀ i < n, (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.SimpleBitPack.fP s₀) i).toNat ≤ VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN s₀

theorem Pre.of {s₀ : State} (h : (simpleBitPackContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre s₀ := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧ arg s₀ 3 = arg s₀' 3

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL s₀] s ∧
    bytesAt s.mem (VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP s₀) (arg s₀ 3).toNat = simpleBitPack (natPolyAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.SimpleBitPack.fP s₀)) (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN s₀)

/-- The loop for the width `d = bitlen v` of `b = v`. -/
theorem branch {d c nb v : Nat} (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) (hv : bitlen v = d) {X : State → Prop}
    (hX : ∀ s₀, VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre s₀ → X s₀ → VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN s₀ = v) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr VG.Proof.MlDsa.X86.Pack.loopRegs) (.block (packBody sbpLd d c nb)) h₂).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start VG.Proof.MlDsa.X86.Pack.SimpleBitPack.fP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP s₀ s ∧ X s₀) VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Fin (packLoop sbpLd d c nb) := by
  have hlen : ∀ s₀, VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre s₀ → X s₀ → (arg s₀ 3).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, hX s₀ h₀ hx, hv]
  refine (VG.Proof.MlDsa.X86.Pack.packLoop_piece VG.Proof.MlDsa.X86.Pack.SimpleBitPack.sbpLd_ok hs VG.Proof.MlDsa.X86.Pack.SimpleBitPack.fP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.1⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hb⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have ho : VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL s₀ = ⟨VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP s₀, 32 * d⟩ := by simp only [VG.Proof.MlDsa.X86.Pack.outR, VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL, hlen s₀ h₀ hx]
    refine ⟨hp.inR_mem, by rw [← ho]; exact hp.outR_mem, by rw [← ho]; exact hp.i_o, hp.i_fit,
      by have := hp.o_fit; rwa [VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL, hlen s₀ h₀ hx] at this, fun i hi => ?_⟩
    rw [hp.coeff_keep rfl hi, ← hv, ← hX s₀ h₀ hx]
    exact VG.Proof.MlDsa.X86.Pack.SimpleBitPack.lt_bitlen (h₀.le i hi)
  · have hp := h₀.lay
    have ho : VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL s₀ = ⟨VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP s₀, 32 * d⟩ := by simp only [VG.Proof.MlDsa.X86.Pack.outR, VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL, hlen s₀ h₀ hx]
    refine ⟨⟨by rw [ho]; exact he.frame, he.esp, he.rd, he.wr⟩, ?_⟩
    rw [hlen s₀ h₀ hx, hb, VG.Proof.MlDsa.X86.Pack.packed, simpleBitPack_eq, natPolyAt_toList, hX s₀ h₀ hx, hv]
    refine congrArg (fun L => bitsToBytes (fieldBits d L)) (List.map_congr_left fun i hi => ?_)
    rw [hp.coeff_keep rfl (List.mem_range.mp hi)]

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Fin
    (.seq (.block (ldArgs 0 2 1))
      (sel 15 (packLoop sbpLd 4 2 1) (sel 43 (packLoop sbpLd 6 4 3) (packLoop sbpLd 10 4 5)))) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.ldArgs_piece (k := 4) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 1) (by decide) (fun _ _ _ _ hq => hq.2.2.1) (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.branch (d := 4) (c := 2) (nb := 1) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun _ _ h => h.2) (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 1) (by decide) (fun _ _ _ _ hq => hq.2.2.1) (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.branch (d := 6) (c := 4) (nb := 3) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun _ _ h => h.2) (by taint_decide) (by taint_decide)) ?_
  refine (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.branch (d := 10) (c := 4) (nb := 5) (v := 1023) ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
      (by decide) (fun s₀ h₀ ⟨⟨_, h15⟩, h43⟩ => ?_) (by taint_decide) (by taint_decide)).mono
    (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h
  have := h₀.b_mem
  simp only [VG.Proof.MlDsa.X86.Pack.SimpleBitPack.bN, simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at this h15 h43 ⊢
  omega

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pre VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Pack.SimpleBitPack.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.simpleBitPack :=
  Piece.leaf (fun s₀ => [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oP VG.Proof.MlDsa.X86.Pack.SimpleBitPack.oL s₀]) (NoSp.of_all (by decide +kernel)) (fun _ h => h.lay.leafE)
    (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `15`, `0x400` and `128` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 15 else if a = 0x500d then 4 else if a = 0x5010 then 128 else 0

theorem verified :
    Verified X86.target Impl.MlDsa.X86.Pack.simpleBitPack (simpleBitPackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState VG.Proof.MlDsa.X86.Pack.SimpleBitPack.satMem [⟨0, 1024⟩] [⟨0x400, 128⟩, ⟨0x5004, 16⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 15 := by decide
    have a2 : arg st 2 = 0x400 := by decide
    have a3 : arg st 3 = 128 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [simpleBitPackBounds, t1Max_eq]; decide)
      | (intro i hi
         rw [VG.Proof.MlDsa.X86.Pack.coeffAt_low (fun a ha => by
           show VG.Proof.MlDsa.X86.Pack.SimpleBitPack.satMem a = 0
           rw [VG.Proof.MlDsa.X86.Pack.SimpleBitPack.satMem, VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x5008) (by decide), VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x500d) (by decide),
             VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x5010) (by decide)]) (by decide) hi]
         decide)
      | decide

end VG.Proof.MlDsa.X86.Pack.SimpleBitPack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.BitPack`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_bit_pack`

`bitPack(f, a, b, out, len)` loads `f` into `esi`, `out` into `edi` and `b`
into `eax`, and branches on `b` to the pack loop for its width
(`packLoop_piece`). The value of a coefficient `x` is `b - x`, plus `q` if
that borrows (`subModQ`), which is `b - (x mod± q)` for a reduced `x`
(`Pack/Arith.lean`).
-/

namespace VG.Proof.MlDsa.X86.Pack.BitPack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack
open VG.Proof.MlDsa.X86.Pack.SimpleBitPack (lt_bitlen)

/-- `b - x`, plus `q` if it borrows, as the code computes it. -/
def subModQ (b x : BitVec 32) : BitVec 32 :=
  b - x + (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (b.toNat < x.toNat))) &&& qImm)

theorem subModQ_toNat {b x : BitVec 32} (hb : b.toNat < q) (hx : x.toNat < q) :
    (VG.Proof.MlDsa.X86.Pack.BitPack.subModQ b x).toNat = (b.toNat + q - x.toNat) % q := by
  have hq : q = 8380417 := rfl
  rw [hq] at hb hx ⊢
  unfold VG.Proof.MlDsa.X86.Pack.BitPack.subModQ
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
abbrev bpVal (B : Nat) (w : BitVec 32) : Nat := (VG.Proof.MlDsa.X86.Pack.BitPack.subModQ (BitVec.ofNat 32 B) w).toNat

theorem bpLd_ok (B : Nat) : VG.Proof.MlDsa.X86.Pack.LdOk (bpLd B) (VG.Proof.MlDsa.X86.Pack.BitPack.bpVal B) := fun j s hin => by
  refine WP.keep _ ?_ (by rfl)
  unfold bpLd
  xrun [hin]
  rfl

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- The values the loop packs are those of `BitPack`. -/
theorem bitPack_vals {m : Mem} {f : Addr} (hr : Reduced m f) {b : Nat} (hb : b ≤ q / 2)
    (hle : ∀ i < n, modPm (coeffAt m f i).toNat q ≤ b) :
    ((polyAt m f).map fun c => modPm c.val q).toList.map (fun wi => ((b : Int) - wi).toNat) =
      VG.Proof.MlDsa.X86.Pack.vals (VG.Proof.MlDsa.X86.Pack.BitPack.bpVal b) m f := by
  have hbq : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; have : q = 8380417 := rfl; omega
  rw [Vector.toList_map, polyAt, toList_ofFn (fun i => Fin.ofNat q (coeffAt m f i).toNat), List.map_map,
    List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hx := hr i hi
  simp only [Function.comp_apply, Fin.val_ofNat, Nat.mod_eq_of_lt hx]
  rw [VG.Proof.MlDsa.X86.Pack.BitPack.bpVal, VG.Proof.MlDsa.X86.Pack.BitPack.subModQ_toNat (by omega) hx, hbq, sub_modPm hx hb (hle i hi)]

section
variable (s₀ : State)
/-- The input pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 0)
/-- The output pointer `out`. -/
abbrev oP : State → BitVec 32 := (arg · 3)
/-- The length of the output. -/
abbrev oL : State → Nat := fun s₀ => (arg s₀ 4).toNat
/-- `a`. -/
abbrev aN : Nat := (arg s₀ 1).toNat
/-- `b`. -/
abbrev bN : Nat := (arg s₀ 2).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : VG.Proof.MlDsa.X86.Pack.Lay 5 VG.Proof.MlDsa.X86.Pack.BitPack.fP VG.Proof.MlDsa.X86.Pack.BitPack.oP (fun _ => 1024) VG.Proof.MlDsa.X86.Pack.BitPack.oL s₀
  ab : (VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀, VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀) ∈ bitPackParams
  len_eq : (arg s₀ 4).toNat = 32 * bitlen (VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀ + VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀)
  red : Reduced s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.BitPack.fP s₀)
  bnd : ∀ i < n, -(VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀ : Int) ≤ modPm (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.BitPack.fP s₀) i).toNat q ∧
    modPm (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.BitPack.fP s₀) i).toNat q ≤ VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀

theorem Pre.of {s₀ : State} (h : (bitPackContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀ := by
  sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧
    arg s₀ 3 = arg s₀' 3 ∧ arg s₀ 4 = arg s₀' 4

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.BitPack.oP VG.Proof.MlDsa.X86.Pack.BitPack.oL s₀] s ∧
    bytesAt s.mem (VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.BitPack.oP s₀) (arg s₀ 4).toNat =
      bitPack ((polyAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.BitPack.fP s₀)).map fun c => modPm c.val q) (VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀) (VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀)

/-- The loop for `b = B`, of width `d = bitlen (a + b)`. -/
theorem branch {d c nb B : Nat} (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) (hB : B ≤ 2 ^ 19) {X : State → Prop}
    (hX : ∀ s₀, VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀ → X s₀ → VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀ = B ∧ bitlen (VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀ + B) = d) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr VG.Proof.MlDsa.X86.Pack.loopRegs) (.block (packBody (bpLd B) d c nb)) h₂).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Pack.BitPack.Pre VG.Proof.MlDsa.X86.Pack.BitPack.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start VG.Proof.MlDsa.X86.Pack.BitPack.fP VG.Proof.MlDsa.X86.Pack.BitPack.oP s₀ s ∧ X s₀) VG.Proof.MlDsa.X86.Pack.BitPack.Fin (packLoop (bpLd B) d c nb) := by
  have hq : q = 8380417 := rfl
  have hBq : (BitVec.ofNat 32 B).toNat = B := by rw [BitVec.toNat_ofNat]; omega
  have hlen : ∀ s₀, VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀ → X s₀ → (arg s₀ 4).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, (hX s₀ h₀ hx).1, (hX s₀ h₀ hx).2]
  refine (VG.Proof.MlDsa.X86.Pack.packLoop_piece (VG.Proof.MlDsa.X86.Pack.BitPack.bpLd_ok B) hs VG.Proof.MlDsa.X86.Pack.BitPack.fP VG.Proof.MlDsa.X86.Pack.BitPack.oP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.2.1⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hb⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have ho : VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.BitPack.oP VG.Proof.MlDsa.X86.Pack.BitPack.oL s₀ = ⟨VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.BitPack.oP s₀, 32 * d⟩ := by simp only [VG.Proof.MlDsa.X86.Pack.outR, VG.Proof.MlDsa.X86.Pack.BitPack.oL, hlen s₀ h₀ hx]
    refine ⟨hp.inR_mem, by rw [← ho]; exact hp.outR_mem, by rw [← ho]; exact hp.i_o, hp.i_fit,
      by have := hp.o_fit; rwa [VG.Proof.MlDsa.X86.Pack.BitPack.oL, hlen s₀ h₀ hx] at this, fun i hi => ?_⟩
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    obtain ⟨b₁, b₂⟩ := h₀.bnd i hi
    rw [e₁] at b₂
    have hxq := h₀.red i hi
    rw [hp.coeff_keep rfl hi, VG.Proof.MlDsa.X86.Pack.BitPack.bpVal, VG.Proof.MlDsa.X86.Pack.BitPack.subModQ_toNat (by omega) hxq, hBq, ← sub_modPm hxq (by omega) b₂, ← e₂]
    exact VG.Proof.MlDsa.X86.Pack.SimpleBitPack.lt_bitlen (sub_modPm_le b₁ b₂)
  · have hp := h₀.lay
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    have ho : VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.BitPack.oP VG.Proof.MlDsa.X86.Pack.BitPack.oL s₀ = ⟨VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.BitPack.oP s₀, 32 * d⟩ := by simp only [VG.Proof.MlDsa.X86.Pack.outR, VG.Proof.MlDsa.X86.Pack.BitPack.oL, hlen s₀ h₀ hx]
    refine ⟨⟨by rw [ho]; exact he.frame, he.esp, he.rd, he.wr⟩, ?_⟩
    rw [hlen s₀ h₀ hx, hb, VG.Proof.MlDsa.X86.Pack.packed, bitPack_eq, e₁, e₂,
      VG.Proof.MlDsa.X86.Pack.BitPack.bitPack_vals h₀.red (by omega) (fun i hi => by rw [← e₁]; exact (h₀.bnd i hi).2)]
    refine congrArg (fun L => bitsToBytes (fieldBits d L)) (List.map_congr_left fun i hi => ?_)
    rw [hp.coeff_keep rfl (List.mem_range.mp hi)]

/-- The shapes of the widths. -/
theorem sh3 : VG.Proof.MlDsa.X86.Pack.Shape 3 8 3 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh4 : VG.Proof.MlDsa.X86.Pack.Shape 4 2 1 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh13 : VG.Proof.MlDsa.X86.Pack.Shape 13 8 13 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh18 : VG.Proof.MlDsa.X86.Pack.Shape 18 4 9 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩
theorem sh20 : VG.Proof.MlDsa.X86.Pack.Shape 20 2 5 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩

/-- The branch for `b = B` is the one for `a = A`, of width `d'`. -/
theorem pick {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀) {A B d' : Nat} (hd : bitlen (A + B) = d') (e : (arg s₀ 2).toNat = B)
    (hA : ∀ a, (a = 2 ∧ B = 2) ∨ (a = 4 ∧ B = 4) ∨ (a = 4095 ∧ B = 4096) ∨ (a = 131071 ∧ B = 131072) ∨
      (a = 524287 ∧ B = 524288) → a = A) : VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀ = B ∧ bitlen (VG.Proof.MlDsa.X86.Pack.BitPack.aN s₀ + B) = d' := by
  have := VG.Proof.MlDsa.X86.Pack.BitPack.mem_bitPackParams h₀.ab
  rw [show VG.Proof.MlDsa.X86.Pack.BitPack.bN s₀ = B from e] at this
  rw [hA _ this]; exact ⟨e, hd⟩

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.BitPack.Pre VG.Proof.MlDsa.X86.Pack.BitPack.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Pack.BitPack.Fin
    (.seq (.block (ldArgs 0 3 2))
      (sel 2 (packLoop (bpLd 2) 3 8 3)
        (sel 4 (packLoop (bpLd 4) 4 2 1)
          (sel 4096 (packLoop (bpLd 4096) 13 8 13)
            (sel 131072 (packLoop (bpLd 131072) 18 4 9) (packLoop (bpLd 524288) 20 2 5)))))) := by
  have hw : ∀ s₀ s₀', VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀ → VG.Proof.MlDsa.X86.Pack.BitPack.Pre s₀' → VG.Proof.MlDsa.X86.Pack.BitPack.Pub s₀ s₀' → arg s₀ 2 = arg s₀' 2 := fun _ _ _ _ hq => hq.2.2.2.1
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.ldArgs_piece (k := 5) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.BitPack.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh3 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.BitPack.pick h₀ (A := 2) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.BitPack.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh4 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.BitPack.pick h₀ (A := 4) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.BitPack.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh13 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.BitPack.pick h₀ (A := 4095) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 2) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.BitPack.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh18 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.BitPack.pick h₀ (A := 131071) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine (VG.Proof.MlDsa.X86.Pack.BitPack.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh20 (B := 524288) (by decide) (fun s₀ h₀ ⟨⟨⟨⟨_, e₂⟩, e₄⟩, e₄₀⟩, e₁₃⟩ =>
      VG.Proof.MlDsa.X86.Pack.BitPack.pick h₀ (A := 524287) (by decide) (by have := VG.Proof.MlDsa.X86.Pack.BitPack.mem_bitPackParams h₀.ab; simp only [VG.Proof.MlDsa.X86.Pack.BitPack.aN, VG.Proof.MlDsa.X86.Pack.BitPack.bN] at this; omega)
        fun _ _ => by omega)
      (by taint_decide) (by taint_decide)).mono (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.BitPack.Pre VG.Proof.MlDsa.X86.Pack.BitPack.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Pack.BitPack.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.bitPack :=
  Piece.leaf (fun s₀ => [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.BitPack.oP VG.Proof.MlDsa.X86.Pack.BitPack.oL s₀]) (NoSp.of_all (by decide +kernel)) (fun _ h => h.lay.leafE)
    (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `2`, `2`, `0x400` and `96` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 2 else if a = 0x500c then 2 else if a = 0x5011 then 4 else if a = 0x5014 then 96 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.bitPack (bitPackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState VG.Proof.MlDsa.X86.Pack.BitPack.satMem [⟨0, 1024⟩] [⟨0x400, 96⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 2 := by decide
    have a2 : arg st 2 = 2 := by decide
    have a3 : arg st 3 = 0x400 := by decide
    have a4 : arg st 4 = 96 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    have hz : ∀ i < 256, coeffAt VG.Proof.MlDsa.X86.Pack.BitPack.satMem (BitVec.setWidth 64 (0 : BitVec 32)) i = 0 := fun i hi =>
      VG.Proof.MlDsa.X86.Pack.coeffAt_low (fun a ha => by
        show VG.Proof.MlDsa.X86.Pack.BitPack.satMem a = 0
        rw [VG.Proof.MlDsa.X86.Pack.BitPack.satMem, VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x5008) (by decide), VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x500c) (by decide),
          VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x5011) (by decide), VG.Proof.MlDsa.X86.Pack.ite_low ha (b := 0x5014) (by decide)]) (by decide) hi
    refine ⟨st, ?_⟩
    sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [bitPackParams]; decide)
      | exact fun i hi => by rw [hz i hi]; decide
      | decide

end VG.Proof.MlDsa.X86.Pack.BitPack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

`bitUnpack(v, len, a, b, f)` loads `v` into `esi`, `f` into `edi` and `b` into
`eax`, and branches on `b` to the unpack loop for its width
(`unpackLoop_piece`); `unpackT1(v, f)` is the loop for 10-bit fields. The
coefficient of a field `y` is `b - y`, plus `q` if that borrows (`subModQ`),
which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`.
-/

namespace VG.Proof.MlDsa.X86.Pack.Unpack

open VG VG.X86 VG.Impl.MlDsa.X86.Pack
open VG.Proof.MlKem.X86 (Piece Piece.seq Piece.leaf Piece.verified P0 E0 LeafEnd LeafPost satState rotr_small)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.X86.Pack
open VG.Proof.MlDsa.X86.Pack.BitPack (subModQ subModQ_toNat mem_bitPackParams sh3 sh4 sh13 sh18 sh20)

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := VG.Proof.MlDsa.X86.Pack.BitPack.subModQ (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok (B d : Nat) : VG.Proof.MlDsa.X86.Pack.FinOk (buFin B) d (VG.Proof.MlDsa.X86.Pack.Unpack.buWord B) := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold buFin
  xrun [hout]
  rw [VG.Proof.MlDsa.X86.Pack.Unpack.buWord, BitVec.ofNat_toNat]
  rfl

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := (BitVec.ofNat 32 y).rotateRight 19

theorem t1Fin_ok : VG.Proof.MlDsa.X86.Pack.FinOk t1Fin 10 VG.Proof.MlDsa.X86.Pack.Unpack.t1Word := fun j s hout _ => by
  refine WP.keep _ ?_ (by rfl)
  unfold t1Fin
  xrun [hout]
  rw [VG.Proof.MlDsa.X86.Pack.Unpack.t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## `vg_mldsa_bit_unpack` -/

namespace BU

section
variable (s₀ : State)
/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- Its length. -/
abbrev vL : State → Nat := fun s₀ => (arg s₀ 1).toNat
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 4)
/-- `a`. -/
abbrev aN : Nat := (arg s₀ 2).toNat
/-- `b`. -/
abbrev bN : Nat := (arg s₀ 3).toNat
end

structure Pre (s₀ : State) : Prop where
  lay : VG.Proof.MlDsa.X86.Pack.Lay 5 VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL (fun _ => 1024) s₀
  ab : (VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN s₀, VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀) ∈ bitPackParams
  len_eq : (arg s₀ 1).toNat = 32 * bitlen (VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN s₀ + VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀)

theorem Pre.of {s₀ : State} (h : (bitUnpackContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀ := by
  sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17⟩

def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2 ∧
    arg s₀ 3 = arg s₀' 3 ∧ arg s₀ 4 = arg s₀' 4

/-- The end of every branch. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP s₀) (toRq (bitUnpack (bytesAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP s₀) (arg s₀ 1).toNat) (VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN s₀) (VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀)))

/-- The loop for `b = B`, of width `d = bitlen (a + b)`. -/
theorem branch {d c nb B : Nat} (hs : VG.Proof.MlDsa.X86.Pack.Shape d c nb) (hB : B ≤ 2 ^ 19) {X : State → Prop}
    (hX : ∀ s₀, VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀ → X s₀ → VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀ = B ∧ bitlen (VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN s₀ + B) = d) {h₁ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.taint.check (τr []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 (256 / c)))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₂ : (VG.X86.taint.check (τr VG.Proof.MlDsa.X86.Pack.loopRegs) (.block (unpackBody (buFin B) d c nb)) h₂).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Pack.Start VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP s₀ s ∧ X s₀) VG.Proof.MlDsa.X86.Pack.Unpack.BU.Fin (unpackLoop (buFin B) d c nb) := by
  have hq : q = 8380417 := rfl
  have hlen : ∀ s₀, VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀ → X s₀ → (arg s₀ 1).toNat = 32 * d := fun s₀ h₀ hx => by
    rw [h₀.len_eq, (hX s₀ h₀ hx).1, (hX s₀ h₀ hx).2]
  refine (VG.Proof.MlDsa.X86.Pack.unpackLoop_piece (VG.Proof.MlDsa.X86.Pack.Unpack.buFin_ok B d) hs VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP (X := X) (fun s₀ h₀ hx => ?_)
    (fun _ _ _ _ hq => ⟨hq.1, hq.2.1, hq.2.2.2.2.2⟩) ht₁ ht₂).mono (fun _ _ _ h => h)
    (fun s₀ s h₀ ⟨⟨he, hc⟩, hx⟩ => ?_)
  · have hp := h₀.lay
    have hi : VG.Proof.MlDsa.X86.Pack.inR VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL s₀ = ⟨VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP s₀, 32 * d⟩ := by simp only [VG.Proof.MlDsa.X86.Pack.inR, VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL, hlen s₀ h₀ hx]
    exact ⟨by rw [← hi]; exact hp.inR_mem, hp.outR_mem, by rw [← hi]; exact hp.i_o,
      by have := hp.i_fit; rwa [VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL, hlen s₀ h₀ hx] at this, hp.o_fit⟩
  · have hp := h₀.lay
    obtain ⟨e₁, e₂⟩ := hX s₀ h₀ hx
    refine ⟨he, polyIs_of_toNat fun i hi => ?_⟩
    have hy := VG.Proof.MlDsa.X86.Pack.Unpack.field_lt (VG.Proof.MlDsa.X86.Pack.inNum (P0 s₀).mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.Unpack.BU.vP s₀) d) d i hs.d20
    have hy' := hy
    unfold VG.Proof.MlDsa.X86.Pack.inNum at hy'
    rw [hp.bytes_keep (by simp only [VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL]; rw [hlen s₀ h₀ hx])] at hy'
    rw [hc i hi, VG.Proof.MlDsa.X86.Pack.Unpack.buWord, VG.Proof.MlDsa.X86.Pack.BitPack.subModQ_toNat (by rw [BitVec.toNat_ofNat]; omega) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi,
      hlen s₀ h₀ hx, e₁, e₂, ofInt_sub (by omega), VG.Proof.MlDsa.X86.Pack.inNum, hp.bytes_keep (by simp only [VG.Proof.MlDsa.X86.Pack.Unpack.BU.vL]; rw [hlen s₀ h₀ hx])]

/-- The branch for `b = B` is the one for `a = A`, of width `d'`. -/
theorem pick {s₀ : State} (h₀ : VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀) {A B d' : Nat} (hd : bitlen (A + B) = d') (e : (arg s₀ 3).toNat = B)
    (hA : ∀ a, (a = 2 ∧ B = 2) ∨ (a = 4 ∧ B = 4) ∨ (a = 4095 ∧ B = 4096) ∨ (a = 131071 ∧ B = 131072) ∨
      (a = 524287 ∧ B = 524288) → a = A) : VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀ = B ∧ bitlen (VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN s₀ + B) = d' := by
  have := VG.Proof.MlDsa.X86.Pack.BitPack.mem_bitPackParams h₀.ab
  rw [show VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN s₀ = B from e] at this
  rw [hA _ this]; exact ⟨e, hd⟩

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Pack.Unpack.BU.Fin
    (.seq (.block (ldArgs 0 4 3))
      (sel 2 (unpackLoop (buFin 2) 3 8 3)
        (sel 4 (unpackLoop (buFin 4) 4 2 1)
          (sel 4096 (unpackLoop (buFin 4096) 13 8 13)
            (sel 131072 (unpackLoop (buFin 131072) 18 4 9) (unpackLoop (buFin 524288) 20 2 5)))))) := by
  have hw : ∀ s₀ s₀', VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀ → VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre s₀' → VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pub s₀ s₀' → arg s₀ 3 = arg s₀' 3 := fun _ _ _ _ hq => hq.2.2.2.2.1
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.ldArgs_piece (k := 5) (by decide) (by decide) (by decide) (fun _ h => h.lay)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.Unpack.BU.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh3 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.Unpack.BU.pick h₀ (A := 2) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.Unpack.BU.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh4 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.Unpack.BU.pick h₀ (A := 4) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.Unpack.BU.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh13 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.Unpack.BU.pick h₀ (A := 4095) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine VG.Proof.MlDsa.X86.Pack.sel_piece (arg · 3) (by decide) hw (by taint_decide)
    (VG.Proof.MlDsa.X86.Pack.Unpack.BU.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh18 (by decide) (fun s₀ h₀ ⟨_, e⟩ => VG.Proof.MlDsa.X86.Pack.Unpack.BU.pick h₀ (A := 131071) (by decide) e fun _ _ => by omega)
      (by taint_decide) (by taint_decide)) ?_
  refine (VG.Proof.MlDsa.X86.Pack.Unpack.BU.branch VG.Proof.MlDsa.X86.Pack.BitPack.sh20 (B := 524288) (by decide) (fun s₀ h₀ ⟨⟨⟨⟨_, e₂⟩, e₄⟩, e₄₀⟩, e₁₃⟩ =>
      VG.Proof.MlDsa.X86.Pack.Unpack.BU.pick h₀ (A := 524287) (by decide) (by have := VG.Proof.MlDsa.X86.Pack.BitPack.mem_bitPackParams h₀.ab; simp only [VG.Proof.MlDsa.X86.Pack.Unpack.BU.aN, VG.Proof.MlDsa.X86.Pack.Unpack.BU.bN] at this; omega)
        fun _ _ => by omega)
      (by taint_decide) (by taint_decide)).mono (fun _ _ _ ⟨⟨h, _⟩, hx⟩ => ⟨h, hx⟩) fun _ _ _ h => h

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pre VG.Proof.MlDsa.X86.Pack.Unpack.BU.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Pack.Unpack.BU.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.bitUnpack :=
  Piece.leaf (fun s₀ => [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.Unpack.BU.fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.lay.leafE) (fun _ h => h.lay.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0`, `96`, `2`, `2` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5008 then 96 else if a = 0x500c then 2 else if a = 0x5010 then 2 else if a = 0x5015 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.bitUnpack (bitUnpackContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · let st := satState VG.Proof.MlDsa.X86.Pack.Unpack.BU.satMem [⟨0, 96⟩] [⟨0x400, 1024⟩, ⟨0x5004, 20⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 96 := by decide
    have a2 : arg st 2 = 2 := by decide
    have a3 : arg st 3 = 2 := by decide
    have a4 : arg st 4 = 0x400 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e]
    and_intros
    all_goals first
      | rfl
      | exact Region.disjoint_of_sep (by decide)
      | (simp only [bitPackParams]; decide)
      | decide

end BU

/-! ## `vg_mldsa_unpack_t1` -/

namespace T1

/-- The input pointer `v`. -/
abbrev vP : State → BitVec 32 := (arg · 0)
/-- The output pointer `f`. -/
abbrev fP : State → BitVec 32 := (arg · 1)

abbrev Pre (s₀ : State) : Prop := VG.Proof.MlDsa.X86.Pack.Lay 2 VG.Proof.MlDsa.X86.Pack.Unpack.T1.vP VG.Proof.MlDsa.X86.Pack.Unpack.T1.fP (fun _ => 320) (fun _ => 1024) s₀

theorem Pre.of {s₀ : State} (h : (unpackT1Contract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Pack.Unpack.T1.Pre s₀ := by
  sig_pre [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The end of the loop. -/
def Fin (s₀ s : State) : Prop :=
  LeafEnd s₀ [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.Unpack.T1.fP (fun _ => 1024) s₀] s ∧
    PolyIs s.mem (VG.Proof.MlDsa.X86.Pack.oA VG.Proof.MlDsa.X86.Pack.Unpack.T1.fP s₀) ((simpleBitUnpack (bytesAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.Unpack.T1.vP s₀) 320) t1Max).map
      fun c => ofInt (c * 2 ^ d : Nat))

theorem sh10 : VG.Proof.MlDsa.X86.Pack.Shape 10 4 5 := ⟨by decide, by decide, rfl, by decide, by decide, rfl, rfl⟩

theorem body_piece : Piece VG.Proof.MlDsa.X86.Pack.Unpack.T1.Pre VG.Proof.MlDsa.X86.Pack.Unpack.T1.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Pack.Unpack.T1.Fin
    (.seq (.block (ldPtrs 0 1)) (unpackLoop t1Fin 10 4 5)) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Pack.ldPtrs_piece (k := 2) (by decide) (by decide) (fun _ h => h)
    (fun _ _ _ _ hq => hq.1) (by taint_decide)) ?_
  refine (VG.Proof.MlDsa.X86.Pack.unpackLoop_piece VG.Proof.MlDsa.X86.Pack.Unpack.t1Fin_ok VG.Proof.MlDsa.X86.Pack.Unpack.T1.sh10 VG.Proof.MlDsa.X86.Pack.Unpack.T1.vP VG.Proof.MlDsa.X86.Pack.Unpack.T1.fP (X := fun _ => True) (fun s₀ hp _ => ?_)
    (fun _ _ _ _ hq => hq) (by taint_decide) (by taint_decide)).mono (fun _ _ _ h => h)
    (fun s₀ s hp ⟨⟨he, hc⟩, _⟩ => ⟨he, polyIs_of_toNat fun i hi => ?_⟩)
  · exact ⟨hp.inR_mem, hp.outR_mem, hp.i_o, hp.i_fit, hp.o_fit⟩
  · rw [hc i hi, VG.Proof.MlDsa.X86.Pack.inNum, hp.bytes_keep (by decide)]
    have hy := Nat.mod_lt (Proof.MlKem.digits 8 ((bytesAt s₀.mem (VG.Proof.MlDsa.X86.Pack.iA VG.Proof.MlDsa.X86.Pack.Unpack.T1.vP s₀) 320).map (·.toNat)) / 2 ^ (10 * i))
      (show 2 ^ 10 > 0 by decide)
    rw [VG.Proof.MlDsa.X86.Pack.Unpack.t1Word, rotr_small _ (by decide) (by decide) (by rw [BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega), show 32 - 19 = 13 from rfl,
      Vector.getElem_map, simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

theorem piece : Piece VG.Proof.MlDsa.X86.Pack.Unpack.T1.Pre VG.Proof.MlDsa.X86.Pack.Unpack.T1.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Pack.Unpack.T1.Fin s₀) s₀ s')
    Impl.MlDsa.X86.Pack.unpackT1 :=
  Piece.leaf (fun s₀ => [VG.Proof.MlDsa.X86.Pack.outR VG.Proof.MlDsa.X86.Pack.Unpack.T1.fP (fun _ => 1024) s₀]) (NoSp.of_all (by decide +kernel))
    (fun _ h => h.leafE) (fun _ h => h.leafW) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.1, h⟩)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

theorem verified : Verified X86.target Impl.MlDsa.X86.Pack.unpackT1 (unpackT1Contract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => by
      sig_pub [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact hinv.2
  · refine ⟨satState VG.Proof.MlDsa.X86.Pack.Unpack.T1.satMem [⟨0, 320⟩] [⟨0x400, 1024⟩, ⟨0x5004, 8⟩], ?_⟩
    sig_sat_check [unpackT1Contract, unpackT1Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end T1

end VG.Proof.MlDsa.X86.Pack.Unpack

end
