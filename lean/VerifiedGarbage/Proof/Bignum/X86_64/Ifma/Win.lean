module
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Area
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Sel

import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Tab
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# RSA with AVX512_IFMA on x86-64, any size: a window of the exponentiations

`ExpSt`: the regions' moduli (`Ar`), the table
(`T_j ≡ x^j R`) and `Y ≡ x^E R` for each prime, `R = 2^(208 R)`. A window
(`window_ok`) copies each prime's digit `v` (a byte at `oD`, below `T = 2^w`)
to its quadword at `oV` (`ldD_ok`), reads `T_v` into `S` (`select_ok`),
squares `Y` `w` times (`sq_ok`) and multiplies it by `S` (`mulS_ok`):
`Y ≡ x^(T E + v) R`. It writes only `Y`, `S` and `V` of each region
(`OutW`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (mont_mul2 r15Dec_ok ea_at' ea_idx wp_seqs_app se_ofNat ofs_off0)
open VG.Proof.Bignum.X86_64 (ofNat_sub_beq)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The state of the exponentiations: `Y ≡ x^E R`. -/
structure ExpSt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E : Nat → Nat) : Prop where
  ar : Ar l m B M k
  tab : ∀ j < l.T, ∀ p < 2, Good l m B M (l.oTab + l.NB * j) p ∧
    (Q → val52 l m B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p)
  y : ∀ p < 2, Good l m B M l.oY p
  yv : Q → ∀ p < 2, val52 l m B (l.D * p + l.oY) % M p = x p ^ E p * 2 ^ (52 * l.S) % M p

/-- `m'` agrees with `m` but on `Y`, `S` and `V` of each region. -/
def OutW (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (B : Addr) (m m' : Mem) : Prop :=
  ∀ a, (∀ p < 2, (ofs B a < l.D * p + l.oY ∨ l.D * p + l.oY + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oS ∨ l.D * p + l.oS + l.NB ≤ ofs B a) ∧
    (ofs B a < l.D * p + l.oV ∨ l.D * p + l.oV + 8 ≤ ofs B a)) →
    m' a = m a

theorem OutW.refl (B : Addr) (m : Mem) : OutW l B m m := fun _ _ => rfl

theorem OutW.trans {B : Addr} {m₁ m₂ m₃ : Mem} (h₁ : OutW l B m₁ m₂) (h₂ : OutW l B m₂ m₃) : OutW l B m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem OutW.ofY {B : Addr} {m m' : Mem} (h : Out2 l B l.oY l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).1

theorem OutW.ofS {B : Addr} {m m' : Mem} (h : Out2 l B l.oS l.NB m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.1

theorem OutW.ofV {B : Addr} {m m' : Mem} (h : Out2 l B l.oV 8 m m') : OutW l B m m' :=
  fun a ha => h a fun p hp => (ha p hp).2.2

/-- The table after a write elsewhere. -/
theorem ExpSt.tab_of (hl : LayOk l) {m m' : Mem} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (h : ExpSt l m B M k x Q E) {o n : Nat} (hf : Out2 l B o n m m')
    (ho : o + n ≤ l.oTab ∨ l.oTab + l.T * l.NB ≤ o) (hoD : o + n ≤ l.D) :
    ∀ j < l.T, ∀ p < 2, Good l m' B M (l.oTab + l.NB * j) p ∧
      (Q → val52 l m' B (l.D * p + (l.oTab + l.NB * j)) % M p = x p ^ j * 2 ^ (52 * l.S) % M p) :=
  fun j hj p hp => by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hNj : l.NB * j + l.NB ≤ l.T * l.NB := tab_le hl hj
  have hc : l.oTab + l.NB * j + l.NB ≤ o ∨ o + n ≤ l.oTab + l.NB * j := by
    rcases ho with ho | ho
    · exact .inr (by omega_using [ho])
    · exact .inl (by omega_using [hNj, ho])
  have hcD : l.oTab + l.NB * j + l.NB ≤ l.D := by omega_using [o5, o10, hNj]
  obtain ⟨g, v⟩ := h.tab j hj p hp
  exact ⟨g.of_out2 hl hp hf hc hcD hoD, fun hq => by rw [hf.val hl hp hc hcD hoD]; exact v hq⟩

/-- `Y := Y² / R`: `x^E R` becomes `x^(2E) R`. -/
theorem sq_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) :
    WP isa (amm l l.oY l.oY l.oY) s fun s' => ExpSt l s'.mem B M k x Q (fun p => 2 * E p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10])
      (by omega_using [o2, o10]) h.y h.y)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact VG.Proof.Bignum.mont_sq (hR p hp) (h.yv hq p hp) (hv p hp).2

/-- `Y := Y S / R`: `x^E R` and `S ≡ x^v R` give `x^(E+v) R`. -/
theorem mulS_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (gs : ∀ p < 2, Good l s.mem B M l.oS p)
    (vs : Q → ∀ p < 2, val52 l s.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p) :
    WP isa (amm l l.oY l.oY l.oS) s fun s' => ExpSt l s'.mem B M k x Q (fun p => E p + v p) ∧
      Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  refine WP.mono (amm2_ok hl hB hs h.ar (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10])
      (by omega_using [o4, o10]) h.y gs)
    fun s' ⟨hv, hf, ar', hg, hrd, hwr, hx⟩ => ⟨⟨ar', h.tab_of hl hf (.inl (by omega_using [o2, o5])) (by omega_using [o2, o10]),
      fun p hp => (hv p hp).1, fun hq p hp => ?_⟩, hf, hg, hrd, hwr, hx⟩
  exact mont_mul2 (hR p hp) (h.yv hq p hp) (vs hq p hp) (hv p hp).2

theorem eaG' (t : State) (r : Reg) (d : Nat) : t.ea (at_ r d) = t.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- The byte that holds digit `i`: with windows of 4 bits, byte `i / 2` of
the padded exponent (two digits a byte); otherwise the digit's own, at `oD`. -/
def dAt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i : Nat) : Nat := if l.w = 4 then l.oE + i / 2 else l.oD + i

/-- Digit `i` from the byte `b` that holds it. -/
def nibOf (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (i b : Nat) : Nat :=
  if l.w = 4 then (if i % 2 = 0 then b / 16 else b % 16) else b

/-- Digit `i` of prime `p`'s exponent. -/
abbrev dig (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (B : Addr) (p i : Nat) : Nat :=
  nibOf l i (m (off B (l.D * p + dAt l i))).toNat

/-- The digits, for windows of more than 4 bits, end before `K1`. -/
theorem lay_oD (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (hw : l.w ≠ 4) : l.oE + l.P ≤ l.oD ∧ l.oD + l.ND ≤ l.oK1 := by
  simp only [Lay.oD, Lay.oK1, Lay.XE, hw, ite_false]; omega_using []

/-- The byte of each digit is in `[oE, oK1)`. -/
theorem lay_dAt (hl : LayOk l) {i : Nat} (hi : i < l.ND) : l.oE ≤ dAt l i ∧ dAt l i < l.oK1 := by
  unfold dAt
  split
  · rename_i hw
    rcases hl with rfl | rfl | rfl
    · have h1 : lay2048.oK1 = lay2048.oE + 128 := rfl
      have h2 : lay2048.ND = 256 := rfl
      omega_arith
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
  · rename_i hw
    have := lay_oD l hw
    omega_arith

/-- The padded exponent: `E ≤ P`, `P` in whole quadwords at most `XE` bytes. -/
theorem lay_P (hl : LayOk l) : l.E ≤ l.P ∧ l.P ≤ 8 * ((l.P + 7) / 8) ∧ 8 * ((l.P + 7) / 8) ≤ l.XE ∧
    l.oD = l.oE + (l.P + 31) / 32 * 32 ∧ l.oE + l.XE = l.oK1 ∧ 8 * ((l.P + 7) / 8) ≤ (l.P + 31) / 32 * 32 := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- The windows: `w` bits, 4 or 5. -/
theorem LayOk.w_bounds (hl : LayOk l) : 4 ≤ l.w ∧ l.w ≤ 5 := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- Digit `i` of prime `p` into its quadword `V`. -/
theorem ldD_ok (hw : l.w ≠ 4) {s : State} {B : Addr} {p i : Nat} (hp : p < 2) (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * l.D)) :
    WP isa (.block [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * p + l.oD : Nat) : Int) },
        .store (at_ .rbx (l.D * p + l.oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (s.mem (off B (l.D * p + l.oD + i))).toNat) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_oD l hw
  have hDp : l.D * p ≤ l.D := by rcases D_mul (l := l) hp with h | h <;> omega_using [h]
  have e : B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oD) = off B (l.D * p + l.oD + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i]
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i + BitVec.ofNat 64 (l.D * p + l.oD)) 1 := by
    rw [e]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * p + l.oD + i) (n := 1) (by omega_using [hi, d2, o7, o10, hDp])
      (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (l.D * p + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D * p + l.oV) (n := 8) (by omega_using [o8, o10, hDp]) (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (l.D * p + l.oV)) (BitVec.ofNat 64 (s.mem (off B (l.D * p + l.oD + i))).toNat) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx, eaG', hB, h13, hld, hst]
    rw [e, BitVec.ofNat_toNat]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem ea_idx8 (t : State) (d : Nat) :
    t.ea { base := .rbx, index := some .r8, disp := ((d : Nat) : Int) } =
      t.gpr .rbx + t.gpr .r8 + BitVec.ofNat 64 d := by
  simp only [State.ea, BitVec.mul_one]
  exact congrArg _ (BitVec.ofInt_natCast ..)

theorem ofNat_ushr1 {i : Nat} (hi : i < 2 ^ 64) : BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow, Nat.pow_one]

/-- `nibSel`'s value: the nibble of the byte `b` that digit `i` is. -/
theorem nib_val (hw : l.w = 4) (b : BitVec 8) (i : Nat) :
    (BitVec.setWidth 64 b &&& BitVec.signExtend 64 (15 : BitVec 32) ^^^
      (BitVec.setWidth 64 b >>> 4 ^^^ BitVec.setWidth 64 b &&& BitVec.signExtend 64 (15 : BitVec 32)) &&&
        ((BitVec.ofNat 64 i &&& 1) - 1)) = BitVec.ofNat 64 (nibOf l i b.toNat) := by
  have h15 : BitVec.signExtend 64 (15 : BitVec 32) = (15 : BitVec 64) := by decide
  have hb := b.isLt
  have hi : BitVec.ofNat 64 i &&& 1 = BitVec.ofNat 64 (i % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.and_one_is_mod]
    omega_arith
  rw [h15, hi]
  simp only [nibOf, hw, ite_true]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, show BitVec.ofNat 64 0 - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm (BitVec.setWidth 64 b &&& 15), BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp only [ite_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith
  · rw [h, show BitVec.ofNat 64 1 - 1 = 0#64 by decide, BitVec.and_zero, BitVec.xor_zero]
    simp only [Nat.one_ne_zero, ite_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega_arith

/-- With windows of 4 bits: both primes' digits `i`, nibbles of byte `i / 2`
of their padded exponents, into their quadwords `V`. -/
theorem digNib_ok (hl : LayOk l) (hw : l.w = 4) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨a1, a2⟩ := lay_dAt hl hi
  have hD := hl.D_bounds
  have hdA : dAt l i = l.oE + i / 2 := by simp only [dAt, hw, ite_true]
  have hn := hs.nowrap
  have hND : l.ND < 2 ^ 31 := by rcases hl with rfl | rfl | rfl <;> decide
  have hsh : BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) := ofNat_ushr1 (by omega_using [hi, hND])
  have e0 : B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 l.oE = off B (l.D * 0 + dAt l i) := by
    rw [hdA, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have e1 : B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D + l.oE) = off B (l.D * 1 + dAt l i) := by
    rw [hdA, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
  have r0 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 l.oE) 1 := by
    rw [e0]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * 0 + dAt l i) (n := 1) (by omega_using [a2, o7, o10, hD]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  have r1 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (i / 2) + BitVec.ofNat 64 (l.D + l.oE)) 1 := by
    rw [e1]
    obtain ⟨r, h, c⟩ := hs.region (d := l.D * 1 + dAt l i) (n := 1) (by omega_using [a2, o7, o10, hD]) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  have w0 : InRegions s.wr (B + BitVec.ofNat 64 l.oV) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.oV) (n := 8) (by omega_using [o8, o10, hD]) (by decide); ⟨_, h, c⟩
  have w1 : InRegions s.wr (B + BitVec.ofNat 64 (l.D + l.oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := l.D + l.oV) (n := 8) (by omega_using [o8, o10, hD]) (by decide); ⟨_, h, c⟩
  simp only [digLoad, hw, ite_true, nibSel, List.cons_append, List.nil_append]
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rdx, .rsi, .r8] (Q := fun s' =>
    s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧ s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx8, eaG', hB, h13, hsh, r0, r1, w0, w1]
    refine ⟨?_, rfl⟩
    have v0 : B + BitVec.ofNat 64 l.oV = off B (l.D * 0 + l.oV) := by rw [Nat.mul_zero, Nat.zero_add]
    have v1 : B + BitVec.ofNat 64 (l.D + l.oV) = off B (l.D * 1 + l.oV) := by rw [Nat.mul_one]
    rw [e0, e1, nib_val hw, nib_val hw, v0, v1]) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩

theorem Outside.limbG (hl : LayOk l) {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {c : Nat}
    (hc : c + l.NB ≤ o ∨ o + n ≤ c) (hc' : c + l.NB ≤ 2 ^ 64) {j : Nat} (hj : j < l.L) :
    limb l m' B c j = limb l m B c j := by
  have := off_lt hl hj
  show (word m' B _).toNat = (word m B _).toNat
  rw [h.word (by omega_using [hc, this]) (by omega_using [hc', this])]

/-- `S := T_v` for both primes. -/
theorem sel2_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (h : ExpSt l s.mem B M k x Q E)
    (hv : ∀ p < 2, nib l s.mem B p < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (select l 0 ++ select l 1))
      s fun s' => ExpSt l s'.mem B M k x Q E ∧
        (∀ p < 2, Good l s'.mem B M l.oS p ∧
          (Q → val52 l s'.mem B (l.D * p + l.oS) % M p = x p ^ nib l s.mem B p * 2 ^ (52 * l.S) % M p)) ∧
        (∀ p < 2, word s'.mem B (l.D * p + l.oV) = word s.mem B (l.D * p + l.oV)) ∧
        Out2 l B l.oS l.NB s.mem s'.mem ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  refine wp_seqs_app (by simp [select]) (by simp [select])
    (WP.mono (select_ok hl (p := 0) (by decide) hB hs (hv 0 (by decide))) fun s₁ ⟨l₁, o₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have hB₁ : s₁.gpr .rbx = B := by rw [g₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hB
  have v₁ : nib l s₁.mem B 1 = nib l s.mem B 1 := by
    unfold nib; rw [o₁.word (by omega_using [o4, o10]) (by omega_using [o8, o10, hn])]
  refine WP.mono (select_ok hl (p := 1) (by decide) hB₁ (hs.congr wr₁) (by rw [v₁]; exact hv 1 (by decide)))
    fun s₂ ⟨l₂, o₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  have f₁ : Out2 l B l.oS l.NB s.mem s₁.mem := Out2.of_outside (p := 0) (by decide) o₁
  have f₂ : Out2 l B l.oS l.NB s₁.mem s₂.mem := Out2.of_outside (p := 1) (by decide) o₂
  have ex₁ := h.tab_of hl f₁ (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10])
  -- entry 0 and entry 1
  have hv0 := hv 0 (by decide)
  have hv1 := hv 1 (by decide)
  have t0 := h.tab (nib l s.mem B 0) hv0 0 (by decide)
  have t1 := ex₁ (nib l s.mem B 1) hv1 1 (by decide)
  have L0 : ∀ q < l.L, limb l s₂.mem B (l.D * 0 + l.oS) q =
      limb l s.mem B (l.D * 0 + (l.oTab + l.NB * nib l s.mem B 0)) q := fun q hq => by
    rw [Outside.limbG hl o₂ (.inl (by omega_using [hD])) (by omega_using [o4, hD]) hq, l₁ q hq, Nat.add_assoc]
  have L1 : ∀ q < l.L, limb l s₂.mem B (l.D * 1 + l.oS) q =
      limb l s₁.mem B (l.D * 1 + (l.oTab + l.NB * nib l s.mem B 1)) q :=
    fun q hq => by rw [l₂ q hq, v₁, Nat.add_assoc]
  refine ⟨⟨?_, h.tab_of hl (f₁.trans f₂) (.inl (by omega_using [o4, o5])) (by omega_using [o4, o10]), fun p hp => ?_, fun hq p hp => ?_⟩,
    fun p hp => ?_, fun p hp => ?_, f₁.trans f₂, fun r r1 r2 r3 r4 => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁],
    by rw [x₂, x₁]⟩
  · exact (h.ar.of_out2 hl f₁ (by omega_using [o2, o4]) (by omega_using [o4, o10])).of_out2 hl f₂
      (by omega_using [o2, o4]) (by omega_using [o4, o10])
  · exact (h.y p hp).of_out2 hl hp (f₁.trans f₂) (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  · rw [(f₁.trans f₂).val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])]; exact h.yv hq p hp
  · rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
    · exact ⟨t0.1.of_limbs L0, fun hq => by rw [val52_of_limbs L0]; exact t0.2 hq⟩
    · exact ⟨t1.1.of_limbs L1, fun hq => by rw [val52_of_limbs L1]; exact t1.2 hq⟩
  · rw [(f₁.trans f₂).word_at hl hp (.inr (by omega_using [o4, o8])) (by omega_using [o8, o10]) (by omega_using [o4, o10])]
  · rw [g₂ r r1 r2 r3 r4, g₁ r r1 r2 r3 r4]

theorem amm_winSetup (b : Nat) : amm l l.oY l.oY b = .seq (.block (winSetup l b)) (ammMul l) := rfl

/-- The comparison of `r15` with 1. -/
theorem r15Cmp_ok {s : State} {n : Nat} (hn : n ≤ 6) (h15 : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r15 (.imm 1)]) s fun s' =>
      isa.eval .e s' = some (n == 1) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  let t := arithFlags s (s.gpr .r15 - (1 : BitVec 32).signExtend 64)
    (decide ((s.gpr .r15).toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s.gpr .r15) ((1 : BitVec 32).signExtend 64) (s.gpr .r15 - (1 : BitVec 32).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h15]
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | omega_arith | decide
  all_goals rfl

/-- The loop of a window with `n` multiplications left, from `s₀`. -/
structure MulInv (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (M k x : Nat → Nat)
    (Q : Prop) (E v : Nat → Nat) (n : Nat) (t : State) : Prop where
  r15 : t.gpr .r15 = BitVec.ofNat 64 n
  st : ExpSt l t.mem B M k x Q (fun p => E p * 2 ^ (l.w + 1 - n))
  gs : ∀ p < 2, Good l t.mem B M l.oS p ∧
    (Q → val52 l t.mem B (l.D * p + l.oS) % M p = x p ^ v p * 2 ^ (52 * l.S) % M p)
  frame : Out2 l B l.oY l.NB s₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

/-- The loop body of a window. -/
def mulBody (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : Prog isa :=
  .seq (.block [.alu .cmp .r15 (.imm 1)])
    (.seq (.ite .e (.block (winSetup l l.oS)) (.block (winSetup l l.oY)))
      (.seq (ammMul l) (.block [.alu .sub .r15 (.imm 1)])))

/-- The `w + 1` multiplications: `w` squarings, then `Y S`. `Y ≡ x^E R` and
`S ≡ x^v R` give `Y ≡ x^(T E + v) R`. -/
theorem mulLoop_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E v : Nat → Nat}
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : MulInv l s B M k x Q E v (l.w + 1) s) :
    WP isa (.loop (mulBody l) .ne) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + v p) ∧ Out2 l B l.oY l.NB s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hw := hl.w_bounds
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ l.w + 1 ∧ MulInv l s B M k x Q E v n t) ?_ (l.w + 1) s
    ⟨by omega_using [], Nat.le_refl _, h⟩
  intro n t ⟨h1, h5, hI⟩
  have hB' : t.gpr .rbx = B := by
    rw [hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact hB
  refine WP.seq (WP.mono (r15Cmp_ok (by omega_using [h5, hw.2]) hI.r15) fun t₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_)
  have hB₀ : t₀.gpr .rbx = B := by rw [g₀]; exact hB'
  have hs₀ : Scr t₀ B (2 * l.D) := hs.congr (by rw [wr₀, hI.wr])
  have st₀ : ExpSt l t₀.mem B M k x Q (fun p => E p * 2 ^ (l.w + 1 - n)) := by rw [m₀]; exact hI.st
  -- after the multiplication and the count
  have after : ∀ (t₁ : State) (E' : Nat → Nat), ExpSt l t₁.mem B M k x Q E' →
      Out2 l B l.oY l.NB t₀.mem t₁.mem →
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → t₁.gpr r = t₀.gpr r) → t₁.rd = t₀.rd → t₁.wr = t₀.wr → t₁.mxcsr = t₀.mxcsr →
      (n = 1 → E' = fun p => E p * l.T + v p) → (1 < n → E' = fun p => E p * 2 ^ (l.w + 1 - (n - 1))) →
      WP isa (.block [.alu .sub .r15 (.imm 1)]) t₁ fun t₂ =>
        (isa.eval .ne t₂ = some false ∧ (ExpSt l t₂.mem B M k x Q (fun p => E p * l.T + v p) ∧
          Out2 l B l.oY l.NB s.mem t₂.mem ∧
          (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
            r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r) ∧
          t₂.rd = s.rd ∧ t₂.wr = s.wr ∧ t₂.mxcsr = s.mxcsr)) ∨
        (isa.eval .ne t₂ = some true ∧ ∃ m < n, 1 ≤ m ∧ m ≤ l.w + 1 ∧ MulInv l s B M k x Q E v m t₂) := by
    intro t₁ E' st₁ f₁ g₁ rd₁ wr₁ x₁ hlast hmore
    have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 n := by
      rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), g₀]; exact hI.r15
    refine WP.mono (r15Dec_ok h1 (by omega_using [h5, hw.2]) r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₂⟩ => ?_
    have f₀₁ : Out2 l B l.oY l.NB t.mem t₁.mem := by rw [← m₀]; exact f₁
    have f₂ : Out2 l B l.oY l.NB s.mem t₂.mem := by rw [me₂]; exact hI.frame.trans f₀₁
    have g₂ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r12 → r ≠ .r15 → t₂.gpr r = s.gpr r := fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => by
      rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₀]
      exact hI.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    have rd₂ : t₂.rd = s.rd := by rw [k₂.2.1, rd₁, rd₀, hI.rd]
    have wr₂ : t₂.wr = s.wr := by rw [k₂.2.2, wr₁, wr₀, hI.wr]
    have xx₂ : t₂.mxcsr = s.mxcsr := by rw [x₂, x₁, x₀, hI.mxcsr]
    simp only [eval, z₂, Option.map_some]
    rcases Nat.eq_or_lt_of_le h1 with rfl | hn
    · refine .inl ⟨by simp, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      rw [me₂, ← hlast rfl]; exact st₁
    · refine .inr ⟨by simp only [decide_eq_false (show ¬ (n - 1 = 0) by omega_using [hn]),
        Bool.not_false], n - 1, by omega_using [hn], by omega_using [hn], by omega_using [h5],
        r15₂, ?_, ?_, f₂, g₂, rd₂, wr₂, xx₂⟩
      · rw [me₂, ← hmore hn]; exact st₁
      · intro p hp
        have hf : Out2 l B l.oY l.NB t.mem t₂.mem := by rw [me₂]; exact f₀₁
        obtain ⟨g, w⟩ := hI.gs p hp
        exact ⟨g.of_out2 hl hp hf (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10]),
          fun hq => by rw [hf.val hl hp (.inr (by omega_using [o2, o4])) (by omega_using [o4, o10]) (by omega_using [o2, o10])]; exact w hq⟩
  refine WP.seq ?_
  by_cases h1' : n = 1
  · subst n
    refine WP.ite true e₀ (fun _ => ?_) (fun h => Bool.noConfusion h)
    have hm := mulS_ok hl (v := v) hB₀ hs₀ hR st₀
      (fun p hp => by rw [m₀]; exact (hI.gs p hp).1) (fun hq p hp => by rw [m₀]; exact (hI.gs p hp).2 hq)
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun _ => ?_) (fun h => absurd h (by decide))
    funext p; simp only [Nat.add_sub_cancel, Lay.T]
  · refine WP.ite false (by rw [e₀]; simp [h1']) (fun h => Bool.noConfusion h) (fun _ => ?_)
    have hm := sq_ok hl hB₀ hs₀ hR st₀
    rw [amm_winSetup, WP.seq_iff] at hm
    refine WP.mono hm fun u hu => WP.seq (WP.mono hu fun t₁ ⟨st₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
    refine after t₁ _ st₁ f₁ g₁ rd₁ wr₁ x₁ (fun h => absurd h h1') (fun _ => ?_)
    funext p
    rw [show l.w + 1 - (n - 1) = (l.w + 1 - n) + 1 by omega_using [h1, h5, h1'], Nat.pow_succ]; grind

/-- The last window's setup: `S := Fin`, one multiplication. -/
def finCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List Instr :=
  copyN l l.oS l.oFin ++ [.mov32 .r15 (.imm 1)]

/-- A window's usual setup: the digits into `V`, `S := T_v`, `w + 1` multiplications. -/
def normCode (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) : List (Prog isa) :=
  ([.block (digLoad l)] : List (Prog isa)) ++ (select l 0 ++ select l 1) ++
    ([.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (l.w + 1)))]] : List (Prog isa))

theorem window_eq : VG.Impl.Bignum.X86_64.seqs (window l) =
    .seq (.seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))])
      (.ite .e (.block (finCode l)) (VG.Impl.Bignum.X86_64.seqs (normCode l)))) (.loop (mulBody l) .ne) := by
  simp only [window, normCode, finCode, List.append_assoc]; rfl

theorem ND_lt (hl : LayOk l) : l.ND < 2 ^ 31 := by
  rcases hl with rfl | rfl | rfl <;> decide

/-- The comparison of `r13` (digit `i`) with `ND`. -/
theorem r13Cmp_ok (hl : LayOk l) {s : State} {i : Nat} (hi : i ≤ l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 l.ND))]) s fun s' =>
      isa.eval .e s' = some (decide (i = l.ND)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have hE := ND_lt hl
  let t := arithFlags s (s.gpr .r13 - (BitVec.ofNat 32 l.ND).signExtend 64)
    (decide ((s.gpr .r13).toNat < ((BitVec.ofNat 32 l.ND).signExtend 64).toNat))
    (subOverflow (s.gpr .r13) ((BitVec.ofNat 32 l.ND).signExtend 64) (s.gpr .r13 - (BitVec.ofNat 32 l.ND).signExtend 64))
  refine WP.of_runBlock ⟨t, by rw [runBlock_cons]; rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t.zf = _
    simp only [t, VG.X86_64.RegUpd.zf_arithFlags, h13, se_ofNat hE]
    rw [ofNat_sub_beq (by omega_using [hi, hE]) (by omega_using [hE])]
  all_goals rfl

/-- A byte outside the bytes that changed. -/
theorem Outside.byteAt {B : Addr} {o n : Nat} {m m' : Mem} (h : Outside B o n m m') {d : Nat}
    (hd : d + 1 ≤ o ∨ o + n ≤ d) (hd' : d < 2 ^ 64) : m' (off B d) = m (off B d) :=
  h _ (by rw [ofs_off0 B hd']; omega_using [hd])

/-- With windows of more than 4 bits: both primes' digits `i`, bytes at `oD`,
into their quadwords `V`. -/
theorem digByte_ok (hw : l.w ≠ 4) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  obtain ⟨d1, d2⟩ := lay_oD l hw
  have hn := hs.nowrap
  have hdg : ∀ (m : Mem) p, dig l m B p i = (m (off B (l.D * p + l.oD + i))).toNat := fun m p => by
    simp only [dig, nibOf, dAt, hw, ite_false, Nat.add_assoc]
  rw [show digLoad l = ([.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 0 + l.oD : Nat) : Int) },
      .store (at_ .rbx (l.D * 0 + l.oV)) .rax] : List Instr) ++
      [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((l.D * 1 + l.oD : Nat) : Int) },
      .store (at_ .rbx (l.D * 1 + l.oV)) .rax] by simp only [digLoad, hw, ite_false]; rfl, WP.block_append_iff]
  refine WP.mono (ldD_ok hw (p := 0) (by decide) hi hB h13 hs) fun s₁ ⟨m₁, k₁, x₁⟩ => ?_
  have hB₁ : s₁.gpr .rbx = B := by rw [k₁.gpr (by decide)]; exact hB
  have h13₁ : s₁.gpr .r13 = BitVec.ofNat 64 i := by rw [k₁.gpr (by decide)]; exact h13
  refine WP.mono (ldD_ok hw (p := 1) (by decide) hi hB₁ h13₁ (hs.congr k₁.2.2)) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
  have o₁ : Outside B (l.D * 0 + l.oV) 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have dg₁ : s₁.mem (off B (l.D * 1 + l.oD + i)) = s.mem (off B (l.D * 1 + l.oD + i)) :=
    Outside.byteAt o₁ (by simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]; omega_using [o8, o10, d1, d2, o6, o7, hi])
      (by omega_using [hn, o10, d2, o7, hi])
  refine ⟨?_, (k₁.trans k₂).mono fun r hr => by simp at hr ⊢; rcases hr with rfl | rfl <;> simp, x₂.trans x₁⟩
  rw [m₂, dg₁, m₁, hdg, hdg]

/-- Both primes' digits `i` into their quadwords `V`. -/
theorem digLoad_ok (hl : LayOk l) {s : State} {B : Addr} {i : Nat} (hi : i < l.ND)
    (hB : s.gpr .rbx = B) (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * l.D)) :
    WP isa (.block (digLoad l)) s fun s' =>
      s'.mem = (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))).writeW
        (off B (l.D * 1 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 1 i)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rdx, .rsi, .r8] s s' ∧ s'.mxcsr = s.mxcsr := by
  by_cases hw : l.w = 4
  · exact digNib_ok hl hw hi hB h13 hs
  · exact digByte_ok hw hi hB h13 hs

/-- A window's usual setup and multiplications (digit `i < ND`): `Y ≡ x^E R`
becomes `x^(T E + v) R` for each prime's digit `v`, which `V` then holds. -/
theorem winNorm_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat} {i : Nat}
    (hi : i < l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i)
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (hd : ∀ p < 2, dig l s.mem B p i < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (normCode l)) s fun t => WP isa (.loop (mulBody l) .ne) t fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + dig l s.mem B p i) ∧
      (∀ p < 2, word s'.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l s.mem B p i)) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  have hD := hl.D_bounds
  have hn := hs.nowrap
  have hw := hl.w_bounds
  -- the digits into `V`
  rw [normCode, List.append_assoc]
  refine wp_seqs_app (by simp) (by simp [select]) ?_
  dsimp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.mono (digLoad_ok hl hi hB h13 hs) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
  have o₁ : Outside B (l.D * 0 + l.oV) 8 s.mem
      (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))) :=
    writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have o₂ : Outside B (l.D * 1 + l.oV) 8
      (s.mem.writeW (off B (l.D * 0 + l.oV)) (BitVec.ofNat 64 (dig l s.mem B 0 i))) s₂.mem := by
    rw [m₂]; exact writeW_outside _ B _ (by omega_using [o8, o10, hn])
  have f₂ : Out2 l B l.oV 8 s.mem s₂.mem :=
    (Out2.of_outside (p := 0) (by decide) o₁).trans (Out2.of_outside (p := 1) (by decide) o₂)
  have w₀ : word s₂.mem B (l.D * 0 + l.oV) = BitVec.ofNat 64 (dig l s.mem B 0 i) := by
    rw [o₂.word (by omega_using [o10]) (by omega_using [o8, o10, hn]), VG.Proof.Bignum.word_writeW_self]
  have w₁ : word s₂.mem B (l.D * 1 + l.oV) = BitVec.ofNat 64 (dig l s.mem B 1 i) := by
    rw [m₂, VG.Proof.Bignum.word_writeW_self]
  have wv : ∀ p < 2, word s₂.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l s.mem B p i) := fun p hp => by
    rcases (by omega_using [hp] : p = 0 ∨ p = 1) with rfl | rfl
    · exact w₀
    · exact w₁
  have nv : ∀ p < 2, nib l s₂.mem B p = dig l s.mem B p i := fun p hp => by
    unfold nib; rw [wv p hp, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hd p hp; have := hl.T_bounds; omega_arith)]
  have hB₂ : s₂.gpr .rbx = B := by rw [k₂.gpr (by decide)]; exact hB
  have hs₂ : Scr s₂ B (2 * l.D) := hs.congr k₂.2.2
  have st₂ : ExpSt l s₂.mem B M k x Q E :=
    ⟨h.ar.of_out2 hl f₂ (by omega_using [o2, o8]) (by omega_using [o8, o10]),
      h.tab_of hl f₂ (.inr (by omega_using [o5, o6, o7, o8])) (by omega_using [o8, o10]),
      fun p hp => (h.y p hp).of_out2 hl hp f₂ (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10])
        (by omega_using [o8, o10]),
      fun hq p hp => by
        rw [f₂.val hl hp (.inl (by omega_using [o2, o8])) (by omega_using [o2, o10]) (by omega_using [o8, o10])]
        exact h.yv hq p hp⟩
  -- the entries
  refine wp_seqs_app (by simp [select]) (by simp)
    (WP.mono (sel2_ok hl hB₂ hs₂ st₂ fun p hp => by rw [nv p hp]; exact hd p hp)
      fun s₃ ⟨st₃, gs₃, w₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_)
  have hB₃ : s₃.gpr .rbx = B := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide)]; exact hB₂
  have hs₃ : Scr s₃ B (2 * l.D) := hs₂.congr wr₃
  dsimp only [VG.Impl.Bignum.X86_64.seqs]
  rw [WP.block_cons_iff]
  refine ⟨s₃.setReg32 .r15 (BitVec.ofNat 32 (l.w + 1)), rfl, WP.block_nil ?_⟩
  let s₄ := s₃.setReg32 .r15 (BitVec.ofNat 32 (l.w + 1))
  have hB₄ : s₄.gpr .rbx = B := by
    change (s₃.setReg32 .r15 _).gpr .rbx = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hB₃
  have hI : MulInv l s₄ B M k x Q E (fun p => dig l s.mem B p i) (l.w + 1) s₄ := by
    refine ⟨?_, ?_, fun p hp => ?_, Out2.refl _ _ _ _, fun _ _ _ _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
    · change (s₃.setReg32 .r15 _).gpr .r15 = _
      rw [State.setReg32, RegUpd.gpr_setReg_self]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := l.w + 1) (b := 2 ^ 32) (by omega_using [hw.2]),
        Nat.mod_eq_of_lt (a := l.w + 1) (b := 2 ^ 64) (by omega_using [hw.2])]
    · rw [Nat.sub_self, Nat.pow_zero]; simp only [Nat.mul_one]; exact st₃
    · rw [← nv p hp]; exact gs₃ p hp
  refine WP.mono (mulLoop_ok hl hB₄ (hs₃.congr rfl) hR hI)
    fun s₆ ⟨st₆, f₆, g₆, rd₆, wr₆, x₆⟩ => ⟨st₆, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_,
      by rw [rd₆]; change s₃.rd = _; rw [rd₃, k₂.2.1],
      by rw [wr₆]; change s₃.wr = _; rw [wr₃, k₂.2.2],
      by rw [x₆]; change s₃.mxcsr = _; rw [x₃, x₂]⟩
  · rw [f₆.word_at hl hp (.inr (by omega_using [o2, o8])) (by omega_using [o8, o10]) (by omega_using [o2, o10])]
    change word s₃.mem B _ = _
    rw [w₃ p hp, wv p hp]
  · exact ((OutW.ofV f₂).trans (OutW.ofS f₃)).trans (OutW.ofY f₆)
  · rw [g₆ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10]
    change (s₃.setReg32 .r15 _).gpr r = _
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r10, g₃ r r1 r2 r3 r5, k₂.gpr (by simp [r1, r2, r3, r4, r5])]

/-- A window (digit `i < ND`): `Y ≡ x^E R` becomes `x^(T E + v) R` for each
prime's digit `v`, which `V` then holds. -/
theorem window_ok (hl : LayOk l) {s : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E : Nat → Nat} {i : Nat}
    (hi : i < l.ND) (h13 : s.gpr .r13 = BitVec.ofNat 64 i)
    (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * l.S)) (M p))
    (h : ExpSt l s.mem B M k x Q E) (hd : ∀ p < 2, dig l s.mem B p i < l.T) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      ExpSt l s'.mem B M k x Q (fun p => E p * l.T + dig l s.mem B p i) ∧
      (∀ p < 2, word s'.mem B (l.D * p + l.oV) = BitVec.ofNat 64 (dig l s.mem B p i)) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_of_lt hi) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite false (by rw [e₀]; simp only [decide_eq_false (Nat.ne_of_lt hi)]) (fun h => Bool.noConfusion h)
    (fun _ => ?_)
  have := winNorm_ok hl (s := s₀) hi (by rw [g₀]; exact h13) (by rw [g₀]; exact hB) (hs.congr wr₀) hR (m₀ ▸ h)
    (by rw [m₀]; exact hd)
  rw [m₀, g₀, rd₀, wr₀, x₀] at this
  exact this

/-- `S` holds `Fin` and `r15` 1, from `s₀`. -/
structure FinSet (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (s₀ : State) (B : Addr) (t : State) : Prop where
  s : ∀ p < 2, ∀ q < l.L, limb l t.mem B (l.D * p + l.oS) q = limb l s₀.mem B (l.D * p + l.oFin) q
  frame : Out2 l B l.oS l.NB s₀.mem t.mem
  r15 : t.gpr .r15 = BitVec.ofNat 64 1
  gpr : ∀ r, r ≠ .r15 → t.gpr r = s₀.gpr r
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  mxcsr : t.mxcsr = s₀.mxcsr

theorem finCode_ok (hl : LayOk l) {s : State} {B : Addr} (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D)) :
    WP isa (.block (finCode l)) s (FinSet l s B) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [finCode, WP.block_append_iff]
  refine WP.mono (copyN_ok hl hB hs (by omega_using [o4, o10]) (by omega_using [o9, o10])
    (.inr (by omega_using [o4, o9]))) fun s₁ ⟨l₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁.setReg32 .r15 1, rfl, WP.block_nil ⟨l₁, f₁, ?_, fun r r1 => ?_, rd₁, wr₁, x₁⟩⟩
  · rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
  · rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ r1, g₁]

/-- The last window (`r13 = ND`): `Y := Y Fin / R`. -/
theorem finWin_ok (hl : LayOk l) {s : State} {B : Addr} {M k : Nat → Nat}
    (h13 : s.gpr .r13 = BitVec.ofNat 64 l.ND) (hB : s.gpr .rbx = B) (hs : Scr s B (2 * l.D))
    (ar : Ar l s.mem B M k) (gy : ∀ p < 2, Good l s.mem B M l.oY p) (gf : ∀ p < 2, Good l s.mem B M l.oFin p) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (window l)) s fun s' =>
      (∀ p < 2, Good l s'.mem B M l.oY p ∧
        val52 l s'.mem B (l.D * p + l.oY) * 2 ^ (52 * l.S) % M p =
          val52 l s.mem B (l.D * p + l.oY) * val52 l s.mem B (l.D * p + l.oFin) % M p) ∧
      OutW l B s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
        r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := lay_offs l
  rw [window_eq]
  refine WP.seq (WP.seq (WP.mono (r13Cmp_ok hl (Nat.le_refl _) h13) fun s₀ ⟨e₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_))
  refine WP.ite true (by rw [e₀]; simp only [decide_true]) (fun _ => ?_) (fun h => Bool.noConfusion h)
  have hB₀ : s₀.gpr .rbx = B := by rw [g₀]; exact hB
  refine WP.mono (finCode_ok hl hB₀ (hs.congr wr₀)) fun u hu => ?_
  have hBu : u.gpr .rbx = B := by rw [hu.gpr _ (by decide)]; exact hB₀
  have hsu : Scr u B (2 * l.D) := hs.congr (by rw [hu.wr, wr₀])
  have fu : Out2 l B l.oS l.NB s.mem u.mem := by rw [← m₀]; exact hu.frame
  have gsu : ∀ p < 2, Good l u.mem B M l.oS p := fun p hp =>
    (gf p hp).of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  have vsu : ∀ p < 2, val52 l u.mem B (l.D * p + l.oS) = val52 l s.mem B (l.D * p + l.oFin) := fun p hp =>
    val52_of_limbs fun q hq => by rw [hu.s p hp q hq, m₀]
  have gyu : ∀ p < 2, Good l u.mem B M l.oY p := fun p hp =>
    (gy p hp).of_out2 hl hp fu (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  have vyu : ∀ p < 2, val52 l u.mem B (l.D * p + l.oY) = val52 l s.mem B (l.D * p + l.oY) := fun p hp =>
    fu.val hl hp (.inl (by omega_using [o2, o4])) (by omega_using [o2, o10]) (by omega_using [o4, o10])
  have aru : Ar l u.mem B M k := ar.of_out2 hl fu (by omega_using [o2, o4]) (by omega_using [o4, o10])
  refine WP.loop (M := isa) (fun n t => n = 1 ∧ t = u) ?_ 1 u ⟨rfl, rfl⟩
  intro n t ⟨hn, ht⟩
  subst hn ht
  refine WP.seq (WP.mono (r15Cmp_ok (by decide) hu.r15) fun t₀ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  refine WP.seq (WP.ite true (by rw [e₁]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h))
  have hm := amm2_ok hl (o := l.oY) (a := l.oY) (b := l.oS) (by rw [g₁]; exact hBu) (hsu.congr wr₁) (m₁ ▸ aru)
    (by omega_using [o2, o10]) (by omega_using []) (by omega_using [o2, o10]) (by omega_using [o4, o10])
    (fun p hp => m₁ ▸ gyu p hp) (fun p hp => m₁ ▸ gsu p hp)
  rw [amm_winSetup, WP.seq_iff] at hm
  refine WP.mono hm fun w hw => WP.seq (WP.mono hw fun t₁ ⟨v₁, f₁, ar₁, g₂, rd₂, wr₂, x₂⟩ => ?_)
  have r15₁ : t₁.gpr .r15 = BitVec.ofNat 64 1 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), g₁]; exact hu.r15
  refine WP.mono (r15Dec_ok (by decide) (by decide) r15₁) fun t₂ ⟨r15₂, z₂, k₂, me₂, x₃⟩ => ?_
  simp only [eval, z₂, Option.map_some]
  refine .inl ⟨by simp, fun p hp => ?_, ?_, fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 => ?_, ?_, ?_, ?_⟩
  · rw [me₂, ← vyu p hp, ← vsu p hp, ← m₁]; exact v₁ p hp
  · rw [me₂, ← m₀]
    exact (OutW.ofS hu.frame).trans (OutW.ofY (m₁ ▸ f₁))
  · rw [k₂.gpr (by simp [r10]), g₂ r r1 r2 r3 r4 r5 r6 r7 r8 r9, g₁, hu.gpr r r10, g₀]
  · rw [k₂.2.1, rd₂, rd₁, hu.rd, rd₀]
  · rw [k₂.2.2, wr₂, wr₁, hu.wr, wr₀]
  · rw [x₃, x₂, x₁, hu.mxcsr, x₀]

end VG.Proof.Bignum.X86_64.Ifma
