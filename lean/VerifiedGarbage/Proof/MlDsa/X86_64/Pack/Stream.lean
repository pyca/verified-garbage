module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.Read

/-!
# ML-DSA on x86-64: streaming fields through `r10`

The group bodies of `Impl/MlDsa/X86_64/Pack/Stream.lean`, for any width `d`,
group of `c` fields and `nb` bytes, and any code `ld` that loads a field's
value (`LdOk`) or `fin` that stores a coefficient from it (`FinOk`):

* `packBody_ok`: the `nb` bytes stored are those of the number `G` whose
  base-`2ᵈ` digits are the values of the group's coefficients;
* `unpackBody_ok`: the word stored for field `j` is `fin`'s of digit `j` of
  the number whose bytes are the group's.

In packing, the accumulator is a slice of the number throughout
(`Pack/Stream.lean`); in unpacking, the load of a field is the slice of the
number at its bytes (`read_slice`), which holds the field (`ldOff_fit`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep Written Written.nil
  Written.snoc Written.congr Written.frame rotr_toNat shr_toNat b8_eq64 ifp ifn sx_ofNat r10zero_ok)
open VG.Proof.MlKem (digits ofNat8_eq)
open VG.Proof.MlDsa.Pack

theorem ea_at' (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  congr 1

/-- `r10 ← r10 + rax · 2^sh`. -/
theorem shiftAdd_ok {sh : Nat} (hsh : sh < 64) (s : State) (hx : (s.gpr .rax).toNat < 2 ^ (64 - sh))
    (hs : (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh < 2 ^ 64) :
    WP isa (.block (shiftAdd sh)) s fun s' =>
      ((s'.gpr .r10).toNat = (s.gpr .r10).toNat + (s.gpr .rax).toNat * 2 ^ sh ∧ s'.mem = s.mem) ∧
        Keep [.rax, .r10] s s' := by
  by_cases h : sh = 0
  · subst h
    refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
    simp only [shiftAdd, ite_true, List.nil_append]
    xrun
    rw [BitVec.toNat_add]
    simp only [Nat.pow_zero, Nat.mul_one] at hs ⊢
    exact Nat.mod_eq_of_lt hs
  · refine WP.keep _ ?_ (by simp only [shiftAdd, h, ite_false]; rfl)
    simp only [shiftAdd, h, ite_false, List.singleton_append]
    xrun [show 1 ≤ 64 - sh by omega_arith, show 64 - sh ≤ 63 by omega_arith]
    rw [BitVec.toNat_add, rotr_toNat _ (by omega_arith) hx, show 64 - (64 - sh) = sh by omega_arith, Nat.mod_eq_of_lt hs]

/-! ## Packing -/

theorem packByte_ok (t : Nat) (s : State) (hout : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1) :
    WP isa (.block (packByte t)) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofNat 64 t) (BitVec.setWidth 8 (s.gpr .r10)) ∧
        s'.gpr .r10 = s.gpr .r10 >>> 8) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by rfl)
  unfold packByte
  xrun [ea_at', hout]

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
  refine WP.mono (packByte_ok (k + u) s' (by rw [hkp.2.2, h8']; exact hout u hu))
    fun s'' ⟨⟨hm, h10⟩, hk'⟩ => ⟨(hkp.trans hk').mono (by decide), ?_, ?_⟩
  · rw [h10, shr_toNat, hr', Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  · rw [hm, h8']
    refine (hw'.snoc (by omega_arith) _).congr fun t ht => ?_
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
theorem packCoef_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d j G : Nat}
    (hd : d ≤ 20) {m₀ : Mem} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hv : F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) = G / 2 ^ (d * j) % 2 ^ d)
    (hout : ∀ t < d * (j + 1) / 8, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hw : Written m₀ s.mem (s.gpr .r8) (d * j / 8) (bytesOf G))
    (hr : (s.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))) (hj : d * (j + 1) < 2 ^ 32) :
    WP isa (.block (packCoef ld d j)) s fun s' =>
      Written m₀ s'.mem (s.gpr .r8) (d * (j + 1) / 8) (bytesOf G) ∧
        (s'.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * (j + 1) / 8)) ∧
        Keep [.rax, .r10, .r11] s s' := by
  unfold packCoef
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (hld j s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hx : (s₁.gpr .rax).toNat < 2 ^ d := by rw [ax₁, hv]; exact Nat.mod_lt _ (Nat.two_pow_pos d)
  have hr₁ : (s₁.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) := by rw [k₁.gpr (by decide), hr]
  have hacc := pack_acc_lt G d j
  have hpd : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  have hp8 : 2 ^ (d * j % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
  refine WP.mono (shiftAdd_ok (sh := d * j % 8) (by omega_arith) s₁
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega_arith))) (by
      rw [hr₁]
      have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_refl (2 ^ (d * j % 8))) (Nat.two_pow_pos _)
      have : 2 ^ d * 2 ^ (d * j % 8) ≤ 2 ^ 20 * 2 ^ 7 := Nat.mul_le_mul hpd hp8
      omega_arith))
    fun s₂ ⟨⟨r₂, m₂⟩, k₂⟩ => ?_
  have hjs : d * (j + 1) = d * j + d := Nat.mul_succ d j
  have hX : (s₂.gpr .r10).toNat = G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
    rw [r₂, hr₁, ax₁, hv, pack_add]
  have h8 : s₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (flush_ok (k := d * j / 8) (nf := d * (j + 1) / 8 - d * j / 8) (m₀ := m₀) (o := s.gpr .r8)
    (V8 := bytesOf G) _ (fun u hu => ?_) (by omega_arith) s₂ h8 (fun u hu => ?_) (by rw [m₂, m₁]; exact hw) hX)
    fun s₃ ⟨hw₃, hr₃, k₃⟩ => ⟨?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · refine ofNat8_eq ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, pack_byte G _ _ _ (by
      have : d * j / 8 + u < d * (j + 1) / 8 := by omega_arith
      omega_arith)]
  · rw [k₂.2.2, k₁.2.2]; exact hout _ (by omega_arith)
  · rwa [show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
      omega_arith] at hw₃
  · rw [hr₃, pack_shift, show d * j / 8 + (d * (j + 1) / 8 - d * j / 8) = d * (j + 1) / 8 by
      have : d * j / 8 ≤ d * (j + 1) / 8 := Nat.div_le_div_right (by rw [Nat.mul_succ]; omega_arith)
      omega_arith]

/-- A group: the `nb` bytes of the number whose base-`2ᵈ` digits are the
values of its `c` coefficients, stored at `r8`. -/
theorem packBody_ok {ld : Nat → List Instr} {F : BitVec 32 → Nat} (hld : LdOk ld F) {d c nb : Nat}
    (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (s : State)
    (hin : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 4)
    (hout : ∀ t < nb, InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 t) 1)
    (hsep : ∀ j < c, Region.Disjoint ⟨s.gpr .rdi + BitVec.ofNat 64 (4 * j), 4⟩ ⟨s.gpr .r8, nb⟩)
    (hF : ∀ j < c, F (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (4 * j)) 32) < 2 ^ d) :
    WP isa (.block (packBody ld d c nb)) s fun s' =>
      Written s.mem s'.mem (s.gpr .r8) nb (bytesOf (digits d ((List.range c).map fun j =>
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
      Written s.mem s'.mem (s.gpr .r8) (d * j / 8) (bytesOf G) ∧
      (s'.gpr .r10).toNat = G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)))
    (fun j s' hj ⟨hk, hw, hr⟩ => ?_) c (Nat.le_refl _) s₁
    ⟨Keep.refl _ _, by rw [m₁, Nat.mul_zero, Nat.zero_div]; exact Written.nil _ _ _,
      by rw [z₁, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl⟩) fun s₂ ⟨k₂, hw₂, _⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := (hk.gpr (by decide)).trans di₁
    have r8 : s'.gpr .r8 = s.gpr .r8 := (hk.gpr (by decide)).trans r8₁
    have hj8 : d * (j + 1) / 8 ≤ nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); omega_arith
    have hj32 := Nat.mul_le_mul hd (show j + 1 ≤ 8 by omega_arith)
    refine WP.mono (packCoef_ok hld (G := G) (m₀ := s.mem) hd s' (by rw [hk.2.1, hk.2.2, k₁.2.1, k₁.2.2, di]; exact hin j hj)
      ?_ (fun t ht => by rw [hk.2.2, k₁.2.2, r8]; exact hout t (by omega_arith)) (by rw [r8]; exact hw) hr (by omega_arith))
      fun s'' ⟨hw', hr', hk'⟩ => ⟨(hk.trans hk').mono (by decide), by rw [← r8]; exact hw', hr'⟩
    -- The word is the one on entry: the bytes written are elsewhere.
    rw [di, hdig j hj]
    congr 1
    refine (hw.frame (R := ⟨s.gpr .r8, nb⟩) ?_).readW (Region.contains_self _ _) ?_ (by decide)
    · have := Nat.mul_le_mul_left d (Nat.le_of_lt hj)
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hsep j hj
  · have hc8 : d * c / 8 = nb := by omega_arith
    have := Nat.mul_le_mul hd hc
    rw [hc8] at hw₂
    refine WP.mono (Proof.MlKem.X86_64.CE.tail_ok c nb (by omega_arith) (by omega_arith) s₂)
      fun s₃ ⟨⟨di₃, r8₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨by rw [m₃]; exact hw₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), di₁]
    · rw [r8₃, k₂.gpr (by decide), r8₁]
    · rw [cx₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)

/-! ## Unpacking -/

/-- `n` bytes at `a + o` that are bytes `o, …, o + n - 1` of `H`. -/
theorem read_slice (m : Mem) (a : Addr) (H : Nat) : ∀ (n o : Nat),
    (∀ u < n, (m (a + BitVec.ofNat 64 (o + u))).toNat = H / 2 ^ (8 * (o + u)) % 2 ^ 8) →
    (m.read (a + BitVec.ofNat 64 o) n).toNat = H / 2 ^ (8 * o) % 2 ^ (8 * n)
  | 0, o, _ => by simp only [Mem.read, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1, o, h => by
    have h0 : (m (a + BitVec.ofNat 64 o)).toNat = H / 2 ^ (8 * o) % 2 ^ 8 := by simpa using h 0 (by omega)
    rw [Proof.Mont.read_toNat_succ, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      read_slice m a H n (o + 1) (fun u hu => by rw [show o + 1 + u = o + (u + 1) by omega]; exact h (u + 1) (by omega)),
      show 8 * (n + 1) = 8 + 8 * n by omega, mod_two_pow_add, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * o + 8 = 8 * (o + 1) by omega, h0]

/-- `fin j` stores the coefficient `W x` of the field `x < 2ᵈ` in `rax` to
`rsi + 4j`, and writes only `rax` and `r11`. -/
def FinOk (fin : Nat → List Instr) (d : Nat) (W : Nat → BitVec 32) : Prop :=
  ∀ j s, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4 → (s.gpr .rax).toNat < 2 ^ d →
    WP isa (.block (fin j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (s.gpr .rax).toNat) ∧ Keep [.rax, .r11] s s'

/-- The load of a field: the `ldW nb` bytes at `rdi + o`, as a number. -/
theorem ldLoad_ok {d nb j : Nat} (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb)) :
    WP isa (.block (if 4 ≤ nb then [.mov32 .rax (.mem (at_ .rdi (ldOff d nb j)))]
      else [.movzx16 .rax (at_ .rdi (ldOff d nb j))])) s fun s' =>
      ((s'.gpr .rax).toNat = (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb)).toNat ∧
        s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  by_cases h : 4 ≤ nb
  · have hw : ldW nb = 4 := ifp h 4 2
    rw [hw] at hin ⊢
    simp only [h, ite_true]
    refine WP.keep _ ?_ (by rfl)
    xrun [ea_at', hin]
    have := (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) 4).isLt
    simp only [Mem.readW, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  · have hw : ldW nb = 2 := ifn h 4 2
    rw [hw] at hin ⊢
    simp only [h, ite_false]
    refine WP.keep _ ?_ (by rfl)
    xrun [ea_at', hin, State.load16]
    have := (s.mem.read (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) 2).isLt
    simp only [Mem.readW, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]

/-- The field from the loaded bytes: shifted right by `sh` and masked to `d`
bits. -/
theorem ldMask_ok (d sh : Nat) (hd : d ≤ 20) (hsh : sh < 32) (s : State)
    (hx : (s.gpr .rax).toNat < 2 ^ 32) :
    WP isa (.block ((if sh = 0 then [] else [.shift32 .shr .rax sh]) ++
      ([.alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ d - 1)))] : List Instr))) s fun s' =>
      ((s'.gpr .rax).toNat = (s.gpr .rax).toNat / 2 ^ sh % 2 ^ d ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  have hp : 2 ^ d ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hd
  by_cases h : sh = 0
  · subst h
    simp only [ite_true, List.nil_append]
    refine WP.keep _ ?_ (by rfl)
    xrun
    rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.pow_zero, Nat.div_one]
  · simp only [h, ite_false, List.singleton_append]
    refine WP.keep _ ?_ (by rfl)
    xrun [show 1 ≤ sh by omega_arith, show sh ≤ 31 by omega_arith]
    rw [Proof.MlKem.X86_64.toNat_setWidth64, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.and_two_pow_sub_one_eq_mod]
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]

/-- The shift and width of the load of field `j` fit it: it starts at or
after the load, and ends within it. -/
theorem ldOff_fit {d nb j : Nat} (hd : d ≤ 20) (hnb : 2 ≤ nb) (hsm : nb < 4 → d ≤ 9) (hj : d * j + d ≤ 8 * nb) :
    8 * ldOff d nb j ≤ d * j ∧ d * j - 8 * ldOff d nb j + d ≤ 8 * ldW nb ∧ ldOff d nb j + ldW nb ≤ nb := by
  unfold ldOff ldW
  split <;> omega

/-- Field `j`: its value, digit `j` of `H`, stored by `fin`. -/
theorem unpackCoef_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    (hd1 : 1 ≤ d) (hd : d ≤ 20) {nb H j : Nat} (hnb : 2 ≤ nb) (hsm : nb < 4 → d ≤ 9) (hj : d * j + d ≤ 8 * nb)
    (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (ldOff d nb j)) (ldW nb))
    (hb : ∀ t < nb, (s.mem (s.gpr .rdi + BitVec.ofNat 64 t)).toNat = H / 2 ^ (8 * t) % 2 ^ 8)
    (hout : InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) 4) :
    WP isa (.block (unpackCoef fin d nb j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofNat 64 (4 * j)) (W (H / 2 ^ (d * j) % 2 ^ d)) ∧
        Keep [.rax, .r11] s s' := by
  obtain ⟨ho, hsh, hon⟩ := ldOff_fit hd hnb hsm hj
  have hw4 : ldW nb ≤ 4 := by unfold ldW; split <;> omega
  unfold unpackCoef ldField
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldLoad_ok s hin) fun s₁ ⟨⟨ax₁, m₁⟩, k₁⟩ => ?_
  have hv : (s₁.gpr .rax).toNat = H / 2 ^ (8 * ldOff d nb j) % 2 ^ (8 * ldW nb) := by
    rw [ax₁, read_slice _ _ H _ _ fun u hu => hb _ (by omega_arith)]
  have hx : (s₁.gpr .rax).toNat < 2 ^ 32 := by
    rw [hv]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega_arith))
  refine WP.mono (ldMask_ok d _ hd (by omega_arith) s₁ hx) fun s₂ ⟨⟨ax₂, m₂⟩, k₂⟩ => ?_
  have hf : (s₂.gpr .rax).toNat = H / 2 ^ (d * j) % 2 ^ d := by
    rw [ax₂, hv, VG.Proof.MlKem.mod_pow_div_mod _ hsh, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      show 8 * ldOff d nb j + (d * j - 8 * ldOff d nb j) = d * j by omega_arith]
  have si : s₂.gpr .rsi = s.gpr .rsi := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  refine WP.mono (hfin j s₂ (by rw [k₂.2.2, k₁.2.2, si]; exact hout) (by rw [hf]; exact Nat.mod_lt _ (Nat.two_pow_pos d)))
    fun s₃ ⟨m₃, k₃⟩ => ⟨by rw [m₃, si, hf, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- A group: the word stored for field `j` is `W` of digit `j` of the
number whose bytes are the group's `nb` bytes at `rdi`. -/
theorem unpackBody_ok {fin : Nat → List Instr} {d : Nat} {W : Nat → BitVec 32} (hfin : FinOk fin d W)
    {c nb : Nat} (hd1 : 1 ≤ d) (hd : d ≤ 20) (hdc : d * c = 8 * nb) (hc : c ≤ 8) (hnb : 2 ≤ nb)
    (hsm : nb < 4 → d ≤ 9) (s : State)
    (hin : ∀ t n, t + n ≤ nb → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 t) n)
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
  have := Nat.mul_le_mul hd hc
  unfold unpackBody
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun j s' => Keep [.rax, .r11] s s' ∧
      Frame [⟨s.gpr .rsi, 4 * c⟩] s.mem s'.mem ∧
      (∀ j' < j, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (4 * j')) 32 = W (H / 2 ^ (d * j') % 2 ^ d)))
    (fun j s' hj ⟨hk, hf, hw⟩ => ?_) c (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s₂ ⟨k₂, hf₂, hw₂⟩ => ?_
  · have di : s'.gpr .rdi = s.gpr .rdi := hk.gpr (by decide)
    have si : s'.gpr .rsi = s.gpr .rsi := hk.gpr (by decide)
    have hj' : d * j + d ≤ 8 * nb := by
      have := Nat.mul_le_mul_left d (show j + 1 ≤ c by omega_arith); rw [Nat.mul_succ] at this; omega_arith
    obtain ⟨-, -, hon⟩ := ldOff_fit hd hnb hsm hj'
    refine WP.mono (unpackCoef_ok hfin hd1 hd (H := H) hnb hsm hj' s'
      (by rw [hk.2.1, hk.2.2, di]; exact hin _ _ hon)
      (fun t ht => by
        rw [di, hbyte t ht]
        refine congrArg BitVec.toNat (hf _ fun r hr => ?_)
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep t ht _ (Region.contains_self _ _))
      (by rw [hk.2.2, si]; exact hout j hj))
      fun s'' ⟨m'', hk'⟩ => ⟨(hk.trans hk').mono (by decide), ?_, fun j' hj' => ?_⟩
    · rw [m'', si]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [m'', si]
      by_cases e : j' = j
      · subst e; rw [Mem.readW_writeW_self32]
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hw j' (by omega_arith)]
  · refine WP.mono (Proof.MlKem.X86_64.DD.tail_ok c nb (by omega_arith) (by omega_arith) s₂)
      fun s₃ ⟨⟨di₃, si₃, cx₃, z₃, m₃⟩, k₃⟩ => ⟨fun j hj => ?_, by rw [m₃]; exact hf₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m₃, hw₂ j hj, ← hH]
    · rw [di₃, k₂.gpr (by decide)]
    · rw [si₃, k₂.gpr (by decide)]
    · rw [cx₃, k₂.gpr (by decide)]
    · rw [z₃, k₂.gpr (by decide)]
    · exact (k₂.trans k₃).mono (by decide)

end VG.Proof.MlDsa.X86_64.Pack
