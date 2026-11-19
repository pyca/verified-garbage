module

public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16Avx2
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
meta import VerifiedGarbage.Proof.MlKem.Mem16
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMem
meta import VerifiedGarbage.Proof.MlKem.Kpke16Contract
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42

/-! ### `MlKem.X86_64.Cbd16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `vg_mlkem16_cbd2`

The nibbles are split as in `vg_mlkem_cbd2` (`Cbd.front_ok`, here with the
16-bit constants, `front_ok`); what the code computes of each byte in a word
is checked for each of the 256 bytes by the kernel (`cbd16_vals`), and the
words stored from the nibbles (`grp_ok`) are proven lane by lane.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Cbd16

open Cbd (cbdT cbdE nib eB word_lo word_hi word_psrlw m8V m9V m10V m11V m12V word_m Nibs)

/-! ## One byte -/

/-- `d + q` if the word `d` is negative, else `d`. -/
def cadd16 (d : BitVec 16) : BitVec 16 := d + (d.sshiftRight 15 &&& 3329#16)

/-- A coefficient from its word `w = v + 2`: `v mod q`. -/
def cbdFix16 (w : BitVec 16) : BitVec 16 := cadd16 (w - 2#16)

theorem cbd16_vals : ∀ v < 256,
    (cbdFix16 (nib 0 (cbdE (BitVec.ofNat 16 v)))).toNat = (cbdX v + 3329 - cbdY v) % 3329 ∧
    (cbdFix16 (nib 1 (cbdE (BitVec.ofNat 16 v)))).toNat = (cbdX (v / 16) + 3329 - cbdY (v / 16)) % 3329 := by
  decide +kernel

/-! ## The constants -/

/-- `2` in each word. -/
def twoW : BitVec 128 := 0x00020002000200020002000200020002#128
/-- `q` in each word. -/
def qW : BitVec 128 := 0x0D010D010D010D010D010D010D010D01#128

theorem word_twoW {i : Nat} (hi : i < 8) : word twoW i = 2#16 ∧ word qW i = 3329#16 := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The constants in their registers. -/
structure Consts (s : State) : Prop where
  m8 : s.xmm .xmm8 = m8V
  m9 : s.xmm .xmm9 = m9V
  m10 : s.xmm .xmm10 = m10V
  m11 : s.xmm .xmm11 = m11V
  m12 : s.xmm .xmm12 = m12V
  two : s.xmm .xmm13 = twoW
  q : s.xmm .xmm15 = qW

theorem consts_iff (s : State) : Consts s ↔ s.xmm .xmm8 = m8V ∧ s.xmm .xmm9 = m9V ∧ s.xmm .xmm10 = m10V ∧
    s.xmm .xmm11 = m11V ∧ s.xmm .xmm12 = m12V ∧ s.xmm .xmm13 = twoW ∧ s.xmm .xmm15 = qW :=
  ⟨fun h => ⟨h.m8, h.m9, h.m10, h.m11, h.m12, h.two, h.q⟩,
    fun ⟨h8, h9, h10, h11, h12, h13, h15⟩ => ⟨h8, h9, h10, h11, h12, h13, h15⟩⟩

/-! ## The nibbles -/

theorem front_ok {s : State} (hc : Consts s) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) :
    WP isa (.block cbdFront) s fun s' =>
      Consts s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ k < 8, word (s'.xmm .xmm4) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (k / 2))) ∧
        word (s'.xmm .xmm0) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (4 + k / 2))) ∧
        word (s'.xmm .xmm2) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (k / 2) + 1)) ∧
        word (s'.xmm .xmm1) k = nib (k % 2) (eB s.mem (s.gpr .rdi) (2 * (4 + k / 2) + 1)) := by
  simp only [cbdFront, cbdNib]
  vrunm [h1, eval_movdqa]
  refine ⟨⟨hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.q⟩, fun k hk => ?_⟩
  have hk2 : k / 2 < 8 := by bdd_omega
  have h42 : 4 + k / 2 < 8 := by bdd_omega
  obtain ⟨a8, a9, a10, a11, a12⟩ := word_m hk2
  obtain ⟨b8, b9, b10, b11, b12⟩ := word_m h42
  simp (disch := first | decide | omega_using [hk]) only [word_punpcklwd, word_punpckhwd, word_pand, word_paddw,
    word_psubw, word_psrlw, hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, a8, a9, a10, a11, a12, b8, b9,
    b10, b11, b12, show (1 : BitVec 8).toNat = 1 from rfl, show (2 : BitVec 8).toNat = 2 from rfl,
    show (4 : BitVec 8).toNat = 4 from rfl, show (8 : BitVec 8).toNat = 8 from rfl, word_lo _ _ hk2,
    word_lo _ _ h42, word_hi _ _ hk2, word_hi _ _ h42]
  simp only [nib, eB, cbdE, cbdT]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## Sixteen coefficients -/

/-- The word of lane `j` of store `k` of a group: of `A` (an even byte) when
`⌊j / 2⌋` is even, else of `B` (an odd byte). -/
def grpW (A B : BitVec 128) (k j : Nat) : BitVec 16 :=
  if j / 2 % 2 = 0 then word A (4 * k + 2 * (j / 4) + j % 2) else word B (4 * k + 2 * (j / 4) + j % 2)

/-- `cbd16Out` on a register holding `D`. -/
def outW (D : BitVec 128) : BitVec 128 :=
  XBinOp.eval .paddw (XBinOp.eval .psubw D twoW)
    (XBinOp.eval .pand (XShiftOp.eval .psraw (XBinOp.eval .psubw D twoW) 15) qW)

/-- Store `k` of a group. -/
def grpX (A B : BitVec 128) (k : Nat) : BitVec 128 :=
  outW (if k = 0 then XBinOp.eval .punpckldq A B else XBinOp.eval .punpckhdq A B)

theorem word_grpX (A B : BitVec 128) {k j : Nat} (hk : k < 2) (hj : j < 8) :
    word (grpX A B k) j = cbdFix16 (grpW A B k j) := by
  obtain ⟨t2, tq⟩ := word_twoW hj
  rcases (by bdd_omega : k = 0 ∨ k = 1) with rfl | rfl <;>
  · simp (disch := bdd_omega) only [grpX, outW, grpW, cbdFix16, cadd16, ↓reduceIte, word_paddw, word_psubw,
      word_pand, word_psraw, word_punpckldq, word_punpckhdq, t2, tq, Nat.reduceEqDiff,
      show min (15 : BitVec 8).toNat 16 = 15 from rfl, Nat.mul_zero, Nat.mul_one, Nat.zero_add]

/-- Memory after the stores of a group at `p`. -/
def wr2 (m : Mem) (p : Addr) (off : Nat) (X : Nat → BitVec 128) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 off) (X 0)).writeW (p + BitVec.ofNat 64 (off + 16)) (X 1)

theorem grp_ok {a b : XReg} {off : Nat}
    (hab : (a, b, off) = (.xmm4, .xmm2, 0) ∨ (a, b, off) = (.xmm0, .xmm1, 32)) {s : State} (hc : Consts s)
    (hw : ∀ k < 2, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (off + 16 * k)) 16) :
    WP isa (.block (cbd16Grp a b off)) s fun s' =>
      Consts s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (off = 0 → s'.xmm .xmm0 = s.xmm .xmm0 ∧ s'.xmm .xmm1 = s.xmm .xmm1) ∧
      s'.mem = wr2 s.mem (s.gpr .rsi) off (grpX (s.xmm a) (s.xmm b)) := by
  have w0 := hw 0 (by decide)
  have w1 := hw 1 (by decide)
  rcases hab with h | h <;> cases h <;>
  · simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, add_ofNat_zero] at w0 w1 ⊢
    simp only [cbd16Grp, cbd16Out, wr2, grpX, outW, ite_true, ite_false, Nat.reduceEqDiff]
    vrunm [w0, w1, eval_movdqa, consts_iff, hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.q, false_implies]

/-! ## Sixteen bytes -/

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide

theorem body_ok {s : State} (hc : Consts s) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16)
    (hw : ∀ k < 4, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (16 * k)) 16) :
    WP isa (.block cbd2_16Body) s fun s' => Consts s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rsi = s.gpr .rsi + 64 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rdi, .rsi, .rcx] s s' ∧
      ∃ A₀ B₀ A₁ B₁, Nibs s.mem (s.gpr .rdi) A₀ B₀ A₁ B₁ ∧
        s'.mem = wr2 (wr2 s.mem (s.gpr .rsi) 0 (grpX A₀ B₀)) (s.gpr .rsi) 32 (grpX A₁ B₁) := by
  unfold cbd2_16Body
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (front_ok hc h1) fun s₁ ⟨hc₁, m₁, g₁, rd₁, wr₁, hn⟩ => ?_
  have hw₁ : ∀ off, off = 0 ∨ off = 32 → ∀ k < 2, InRegions s₁.wr (s₁.gpr .rsi + BitVec.ofNat 64 (off + 16 * k)) 16 :=
    fun off ho k hk => by
      rw [wr₁, g₁, show off + 16 * k = 16 * (off / 16 + k) by bdd_omega]; exact hw _ (by bdd_omega)
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok (Or.inl rfl) hc₁ (hw₁ 0 (.inl rfl))) fun s₂ ⟨hc₂, g₂, rd₂, wr₂, x₂, m₂⟩ => ?_
  obtain ⟨x0, x1⟩ := x₂ rfl
  have hw₂ : ∀ k < 2, InRegions s₂.wr (s₂.gpr .rsi + BitVec.ofNat 64 (32 + 16 * k)) 16 := fun k hk => by
    rw [wr₂, g₂]; exact hw₁ 32 (.inr rfl) k hk
  rw [WP.block_append_iff]
  refine WP.mono (grp_ok (Or.inr rfl) hc₂ hw₂) fun s₃ ⟨hc₃, g₃, rd₃, wr₃, _, m₃⟩ => ?_
  vrunm [sx64, consts_iff, hc₃.m8, hc₃.m9, hc₃.m10, hc₃.m11, hc₃.m12, hc₃.two, hc₃.q, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.xmm_setReg, RegUpd.gpr_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.xmm_setFlags, RegUpd.gpr_setFlags]
  have hg : s₃.gpr = s.gpr := by rw [g₃, g₂, g₁]
  refine ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [hg], by rw [hg], by rw [hg], by rw [hg],
    ⟨fun r hr => ?_, ?_, ?_⟩, s₁.xmm .xmm4, s₁.xmm .xmm2, s₁.xmm .xmm0, s₁.xmm .xmm1,
    ⟨fun k hk => (hn k hk).1, fun k hk => (hn k hk).2.1, fun k hk => (hn k hk).2.2.1, fun k hk => (hn k hk).2.2.2⟩,
    by rw [m₃, m₂, m₁, g₂, g₁, x0, x1]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, hg]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, rd₃, rd₂, rd₁]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, wr₃, wr₂, wr₁]

/-! ## The coefficients -/

theorem coeffAtW_eq (m : Mem) (p : Addr) (i : Nat) : coeffAtW 16 m p i = wordAt m p i := rfl

/-- The coefficients a group writes: sixteen from `c₀ + off / 2`. -/
theorem wordAt_wr2 (m : Mem) (p : Addr) {c₀ off : Nat} (hoff : off = 0 ∨ off = 32) (hc : c₀ + off / 2 + 16 ≤ 256)
    (X : Nat → BitVec 128) {k : Nat} (hk : k < 256) :
    wordAt (wr2 m (wAddr p c₀) off X) p k =
      if c₀ + off / 2 ≤ k ∧ k < c₀ + off / 2 + 16 then
        word (X ((k - (c₀ + off / 2)) / 8)) ((k - (c₀ + off / 2)) % 8)
      else wordAt m p k := by
  have ha : ∀ d, 2 ∣ d → wAddr p c₀ + BitVec.ofNat 64 d = wAddr p (c₀ + d / 2) := fun d hd => by
    rw [show d = 2 * (d / 2) from (Nat.mul_div_cancel' hd).symm, wAddr_add, Nat.mul_div_cancel_left _ (by decide)]
  simp only [wr2]
  rw [ha off (by bdd_omega), ha (off + 16) (by bdd_omega),
    wordAt_write128 _ _ (by bdd_omega) _ hk, wordAt_write128 _ _ (by bdd_omega) _ hk]
  generalize hb : c₀ + off / 2 = b at *
  have e16 : (off + 16) / 2 = off / 2 + 8 := by bdd_omega
  rw [e16, ← Nat.add_assoc, hb]
  by_cases hin : b ≤ k ∧ k < b + 16
  · rw [ite_eq_left hin]
    obtain ⟨r, rfl, hr⟩ : ∃ r, k = b + r ∧ r < 16 := ⟨k - b, by omega_using [hin], by omega_using [hin]⟩
    simp only [Nat.add_le_add_iff_left, Nat.add_lt_add_iff_left, Nat.add_sub_cancel_left]
    rcases (by bdd_omega : r / 8 = 0 ∨ r / 8 = 1) with h | h <;>
      rw [h] <;> simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right] <;> congr 1 <;> bdd_omega
  · rw [ite_eq_right hin]
    simp (disch := bdd_omega) only [ite_eq_right]

/-- A coefficient from nibble `h` of byte `b` at `p`. -/
theorem nib_val (m : Mem) (p : Addr) {h : Nat} (hh : h < 2) (b : Nat) :
    (cbdFix16 (nib h (eB m p b))).toNat =
      (cbdX ((m (p + BitVec.ofNat 64 b)).toNat / 16 ^ h) + 3329 -
        cbdY ((m (p + BitVec.ofNat 64 b)).toNat / 16 ^ h)) % 3329 := by
  have hv := cbd16_vals _ (m (p + BitVec.ofNat 64 b)).isLt
  rw [BitVec.ofNat_toNat] at hv
  rcases (by bdd_omega : h = 0 ∨ h = 1) with rfl | rfl
  · rw [Nat.pow_zero, Nat.div_one]; exact hv.1
  · rw [Nat.pow_one]; exact hv.2

/-- The value of lane `j` of store `t` of group `g`: from nibble `j mod 2` of
byte `8 g + 4 t + ⌊j / 2⌋`. -/
theorem grp_val {m : Mem} {p : Addr} {A₀ B₀ A₁ B₁ : BitVec 128} (hn : Nibs m p A₀ B₀ A₁ B₁) {g t j : Nat}
    (hg : g < 2) (ht : t < 2) (hj : j < 8) :
    (cbdFix16 (grpW (if g = 0 then A₀ else A₁) (if g = 0 then B₀ else B₁) t j)).toNat =
      (cbdX ((m (p + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat / 16 ^ (j % 2)) + 3329 -
        cbdY ((m (p + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat / 16 ^ (j % 2))) % 3329 := by
  unfold grpW
  have e2 : (4 * t + 2 * (j / 4) + j % 2) % 2 = j % 2 := by bdd_omega
  by_cases hj2 : j / 2 % 2 = 0
  · rw [ite_eq_left hj2]
    rcases (by bdd_omega : g = 0 ∨ g = 1) with rfl | rfl
    · rw [ite_eq_left rfl, hn.a0 _ (by bdd_omega), e2,
        show 2 * ((4 * t + 2 * (j / 4) + j % 2) / 2) = 8 * 0 + 4 * t + j / 2 by bdd_omega]
      exact nib_val m p (by bdd_omega) _
    · rw [ite_eq_right (by decide), hn.a1 _ (by bdd_omega), e2,
        show 2 * (4 + (4 * t + 2 * (j / 4) + j % 2) / 2) = 8 * 1 + 4 * t + j / 2 by bdd_omega]
      exact nib_val m p (by bdd_omega) _
  · rw [ite_eq_right hj2]
    rcases (by bdd_omega : g = 0 ∨ g = 1) with rfl | rfl
    · rw [ite_eq_left rfl, hn.b0 _ (by bdd_omega), e2,
        show 2 * ((4 * t + 2 * (j / 4) + j % 2) / 2) + 1 = 8 * 0 + 4 * t + j / 2 by bdd_omega]
      exact nib_val m p (by bdd_omega) _
    · rw [ite_eq_right (by decide), hn.b1 _ (by bdd_omega), e2,
        show 2 * (4 + (4 * t + 2 * (j / 4) + j % 2) / 2) + 1 = 8 * 1 + 4 * t + j / 2 by bdd_omega]
      exact nib_val m p (by bdd_omega) _

/-! ## The loop -/

/-- The groups' stores lie in the polynomial. -/
theorem wr2_frame {m : Mem} {P : Addr} {c₀ off : Nat} (hoff : off = 0 ∨ off = 32) (hc : c₀ + off / 2 + 16 ≤ 256)
    (X : Nat → BitVec 128) : Frame [sR P] m (wr2 m (wAddr P c₀) off X) := by
  have ha : ∀ d, 2 ∣ d → wAddr P c₀ + BitVec.ofNat 64 d = wAddr P (c₀ + d / 2) := fun d hd => by
    rw [show d = 2 * (d / 2) from (Nat.mul_div_cancel' hd).symm, wAddr_add, Nat.mul_div_cancel_left _ (by decide)]
  simp only [wr2]
  rw [ha off (by bdd_omega), ha (off + 16) (by bdd_omega)]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sR_contains _ (by bdd_omega))).writeW
    (List.mem_singleton_self _) _ (sR_contains _ (by bdd_omega))

/-- `vg_mlkem16_cbd2(b = rdi, f = rsi)`. -/
def cbd2_16K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 128⟩] ∧ s.wr = [sR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 128⟩ (sR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 128⟩ ∧
    (retR s).Disjoint (sR (s.gpr .rsi))
  post s s' := PolyIsW 16 s'.mem (s.gpr .rsi) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 128))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

section
variable (s₀ : State)
abbrev bP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
/-- The value of coefficient `k`. -/
abbrev val (k : Nat) : Nat := ((samplePolyCBD 2 (bytesAt s₀.mem (bP s₀) 128))[k]!).val
end

/-- After `i` groups of sixteen bytes. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (16 * i)
  rsi : s.gpr .rsi = wAddr (fP s₀) (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : Consts s
  frame : Frame [sR (fP s₀)] s₀.mem s.mem
  coeff : ∀ k < 32 * i, (wordAt s.mem (fP s₀) k).toNat = val s₀ k

section
variable {s₀ : State} (hp : cbd2_16K.pre s₀)
include hp

/-- Coefficient `k` from its byte in the state `s`, read at `rdi`. -/
theorem val_eq {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) {g t j : Nat} (hg : g < 2) (ht : t < 2)
    (hj : j < 8) :
    (cbdX ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat / 16 ^ (j % 2)) + 3329 -
        cbdY ((s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat / 16 ^ (j % 2))) % 3329 =
      val s₀ (32 * i + 16 * g + 8 * t + j) := by
  have hb : s.mem (s.gpr .rdi + BitVec.ofNat 64 (8 * g + 4 * t + j / 2)) =
      (bytesAt s₀.mem (bP s₀) 128).getD ((32 * i + 16 * g + 8 * t + j) / 2) 0 := by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add, bytesAt_getD _ _ (by bdd_omega),
      show 16 * i + (8 * g + 4 * t + j / 2) = (32 * i + 16 * g + 8 * t + j) / 2 by bdd_omega]
    exact bytes_frame hI.frame (by simpa using hp.2.2.1) (by decide) _ (by bdd_omega)
  rw [val, samplePolyCBD2_val _ (by rw [n_eq]; omega_using [hi, hg, ht, hj]), nibble, q_eq, ← hb,
    show (32 * i + 16 * g + 8 * t + j) % 2 = j % 2 by bdd_omega]

theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block cbd2_16Body) s fun s' => Inv s₀ (i + 1) s' ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 128⟩, sR (fP s₀)] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [sR (fP s₀)] := by rw [hI.wr, hp.2.1]
  refine WP.mono (body_ok hI.c (by rw [hrd, hI.rdi]; exact ⟨⟨bP s₀, 128⟩, by simp, Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩)
    (fun k hk => by
      rw [hwr, hI.rsi, show 16 * k = 2 * (8 * k) by bdd_omega, wAddr_add]
      exact ⟨_, List.mem_singleton_self _, sR_contains _ (by bdd_omega)⟩))
    fun s' ⟨hc', rd', wr', di', si', cx', z', _, A₀, B₀, A₁, B₁, hn, hm⟩ => ⟨?_, cx', z'⟩
  refine ⟨?_, ?_, rd'.trans hI.rd, wr'.trans hI.wr, hc', ?_, fun k hk => ?_⟩
  · rw [di', hI.rdi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.mul_succ]
  · rw [si', hI.rsi, show (64 : BitVec 64) = BitVec.ofNat 64 (2 * 32) from rfl, wAddr_add, Nat.mul_succ]
  · rw [hm, hI.rsi]
    exact hI.frame.trans ((wr2_frame (.inl rfl) (by bdd_omega) _).trans (wr2_frame (.inr rfl) (by bdd_omega) _))
  · rw [hm, hI.rsi, wordAt_wr2 _ _ (.inr rfl) (by bdd_omega) _ (by bdd_omega),
      wordAt_wr2 _ _ (.inl rfl) (by bdd_omega) _ (by bdd_omega)]
    by_cases hlo : k < 32 * i
    · rw [ite_eq_right (by bdd_omega), ite_eq_right (by bdd_omega)]; exact hI.coeff k hlo
    · obtain ⟨g, hg, t, ht, j, hj, rfl⟩ : ∃ g < 2, ∃ t < 2, ∃ j < 8, k = 32 * i + 16 * g + 8 * t + j :=
        ⟨(k - 32 * i) / 16, by bdd_omega, (k - 32 * i) % 16 / 8, by bdd_omega, (k - 32 * i) % 8, by bdd_omega, by bdd_omega⟩
      have hv := grp_val hn hg ht hj
      rw [val_eq hp hi hI hg ht hj] at hv
      rcases (by bdd_omega : g = 0 ∨ g = 1) with rfl | rfl
      · rw [ite_eq_left rfl, ite_eq_left rfl] at hv
        rw [ite_eq_right (by bdd_omega), ite_eq_left (by bdd_omega),
          show (32 * i + 16 * 0 + 8 * t + j - (32 * i + 0 / 2)) / 8 = t by bdd_omega,
          show (32 * i + 16 * 0 + 8 * t + j - (32 * i + 0 / 2)) % 8 = j by bdd_omega, word_grpX _ _ ht hj, hv]
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hv
        rw [ite_eq_left (by bdd_omega),
          show (32 * i + 16 * 1 + 8 * t + j - (32 * i + 32 / 2)) / 8 = t by bdd_omega,
          show (32 * i + 16 * 1 + 8 * t + j - (32 * i + 32 / 2)) % 8 = j by bdd_omega, word_grpX _ _ ht hj, hv]

theorem correct : ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2_16 s₀ t s' ∧ abiPreserved s₀ s' ∧ cbd2_16K.post s₀ s' := by
  have hL : WP isa Impl.MlKem.X86_64.cbd2_16 s₀ (Inv s₀ 8) := by
    unfold Impl.MlKem.X86_64.cbd2_16
    refine WP.seq (WP.mono (Q := fun (s : State) => Consts s ∧ s.gpr .rcx = BitVec.ofNat 64 8 ∧
        s.mem = s₀.mem ∧ Keep [.rax, .rcx] s₀ s) (by
          simp only [cbd16Consts, bcast]
          vrunm [consts_iff]
          refine ⟨fun r hr => ?_, rfl, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setXmm, hr, ite_false]) fun s ⟨hc, hcx, hm0, k0⟩ => ?_)
    refine wp_countdown (cnt := .rcx) (N := 8) (by decide) (by decide) (Inv s₀)
      (fun i hi s hI _ => step hp hi hI) (fun _ h => h)
      ⟨?_, ?_, k0.2.1, k0.2.2, hc, by rw [hm0]; exact Frame.refl _ _, fun k hk => absurd hk (by bdd_omega)⟩ hcx
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
    · rw [k0.gpr (by decide)]; exact (BitVec.add_zero _).symm
  obtain ⟨t, s', he, hI, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rcx] hL (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hI.frame
    (by simpa using hp.2.2.2.2)), polyIsW_of_toNat fun k hk => ?_⟩
  rw [coeffAtW_eq]
  exact hI.coeff k (by rw [n_eq] at hk; omega_using [hk])

end

end Cbd16

theorem cbd2_16_correct (s : State) (hs : Cbd16.cbd2_16K.pre s) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.cbd2_16 s t s' ∧ abiPreserved s s' ∧ Cbd16.cbd2_16K.post s s' :=
  Cbd16.correct hs

theorem cbd2_16_ct : ConstantTime isa Cbd16.cbd2_16K.pre Cbd16.cbd2_16K.pub Impl.MlKem.X86_64.cbd2_16 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: `vg_mlkem16_cbd2_avx2`

Each lane does what `vg_mlkem16_cbd2` does to a register (`lane_ok`, from
`Cbd16.lean`'s pieces), on the sixteen bytes the load puts in it (`ylanes`);
the coefficients of lane `l` of the four registers are those of bytes
`16 l` to `16 l + 15`, which `vperm2i128` puts in order for the stores.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Cbd16Y

open Cbd (cbdT cbdE nib eB word_lo word_hi word_psrlw m8V m9V m10V m11V m12V word_m Nibs)
open Cbd16 (Consts consts_iff grpX twoW qW)

/-! ## One lane -/

/-- `cbdFront` after its load, from the sixteen bytes at `a` in `xmm0`. -/
theorem frontT_ok {t : State} (hc : Consts t) {m : Mem} {a : Addr} (hx : t.xmm .xmm0 = m.readW a 128) :
    WP isa (.block cbdFront.tail) t fun t' =>
      Consts t' ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' ∧
      Nibs m a (t'.xmm .xmm4) (t'.xmm .xmm2) (t'.xmm .xmm0) (t'.xmm .xmm1) := by
  simp only [cbdFront, cbdNib, List.tail_cons, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  refine ⟨?_, by xonly, ?_⟩
  · exact ⟨hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.q⟩
  · constructor <;> intro k hk <;> (have hk2 : k / 2 < 8 := by bdd_omega) <;>
      (have h42 : 4 + k / 2 < 8 := by bdd_omega) <;>
      obtain ⟨a8, a9, a10, a11, a12⟩ := word_m hk2 <;> obtain ⟨b8, b9, b10, b11, b12⟩ := word_m h42 <;>
      simp (disch := first | decide | omega_using [hk]) only [hx, word_punpcklwd, word_punpckhwd, word_pand, word_paddw,
        word_psubw, word_psrlw, hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, a8, a9, a10, a11, a12, b8, b9,
        b10, b11, b12, show (1 : BitVec 8).toNat = 1 from rfl, show (2 : BitVec 8).toNat = 2 from rfl,
        show (4 : BitVec 8).toNat = 4 from rfl, show (8 : BitVec 8).toNat = 8 from rfl, word_lo _ _ hk2,
        word_lo _ _ h42, word_hi _ _ hk2, word_hi _ _ h42] <;>
      simp only [nib, eB, cbdE, cbdT]

/-- A group: sixteen coefficients from the words in `a` and `b`, to `d` and `a`. -/
theorem grpN_ok {d a b : XReg}
    (h : (d, a, b) = (.xmm7, .xmm4, .xmm2) ∨ (d, a, b) = (.xmm5, .xmm0, .xmm1)) {t : State} (hc : Consts t) :
    WP isa (.block (cbd16GrpN d a b)) t fun t' => Consts t' ∧ XOnly [d, a, .xmm6] t t' ∧
      t'.xmm d = grpX (t.xmm a) (t.xmm b) 0 ∧ t'.xmm a = grpX (t.xmm a) (t.xmm b) 1 := by
  rcases h with h | h <;> cases h <;>
  · simp only [cbd16GrpN, cbd16Fix, xmov, xb, List.cons_append, List.nil_append, grpX, Cbd16.outW, ite_true,
      ite_false, Nat.reduceEqDiff]
    vrun [eval_movdqa]
    refine ⟨⟨hc.m8, hc.m9, hc.m10, hc.m11, hc.m12, hc.two, hc.q⟩, by xonly, ?_, ?_⟩
    all_goals rw [hc.two, hc.q]

/-- The registers of a lane to store, from the sixteen bytes at `a` in `xmm0`. -/
abbrev lregs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

/-- What a lane computes from the sixteen bytes at `a` in `xmm0`. -/
def LaneOut (m : Mem) (a : Addr) (t : State) : Prop :=
  ∃ A₀ B₀ A₁ B₁, Nibs m a A₀ B₀ A₁ B₁ ∧ t.xmm .xmm7 = grpX A₀ B₀ 0 ∧ t.xmm .xmm4 = grpX A₀ B₀ 1 ∧
    t.xmm .xmm5 = grpX A₁ B₁ 0 ∧ t.xmm .xmm0 = grpX A₁ B₁ 1

theorem lane_ok {t : State} (hc : Consts t) {m : Mem} {a : Addr} (hx : t.xmm .xmm0 = m.readW a 128) :
    WP isa (.block cbd16Lane) t fun t' => (Consts t' ∧ LaneOut m a t') ∧ XOnly lregs t t' := by
  unfold cbd16Lane
  rw [WP.block_append_iff]
  refine WP.mono (frontT_ok hc hx) fun t1 ⟨c1, o1, n1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (grpN_ok (.inl rfl) c1) fun t2 ⟨c2, o2, d2, a2⟩ => ?_
  refine WP.mono (grpN_ok (.inr rfl) c2) fun t3 ⟨c3, o3, d3, a3⟩ => ?_
  have x0 : t2.xmm .xmm0 = t1.xmm .xmm0 := o2.xmm _ (by decide)
  have x1 : t2.xmm .xmm1 = t1.xmm .xmm1 := o2.xmm _ (by decide)
  have x7 : t3.xmm .xmm7 = t2.xmm .xmm7 := o3.xmm _ (by decide)
  have x4 : t3.xmm .xmm4 = t2.xmm .xmm4 := o3.xmm _ (by decide)
  refine ⟨⟨c3, t1.xmm .xmm4, t1.xmm .xmm2, t1.xmm .xmm0, t1.xmm .xmm1, n1, by rw [x7, d2], by rw [x4, a2],
    by rw [d3, x0, x1], by rw [a3, x0, x1]⟩, ((o1.trans o2).trans o3).mono (by simp)⟩

/-! ## The constants -/

/-- The constants in both lanes. -/
def YC (s : State) : Prop := ∀ l < 2, Consts (s.proj l)

theorem yc_keep {s s' : State} (h : YC s) (hl : ∀ r, r ∉ lregs → ∀ l < 2, s'.lane r l = s.lane r l) : YC s' :=
  fun l hl' => ⟨by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').m8,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').m9,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').m10,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').m11,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').m12,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').two,
    by rw [State.proj_xmm, hl _ (by decide) l hl']; exact (h l hl').q⟩

theorem consts_ok (s : State) :
    WP isa (.block cbd16YConsts) s fun s' => YC s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem := by
  simp only [cbd16YConsts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨l1, k1, m1, _, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm8 _ s1) fun s2 ⟨l2, k2, m2, _, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm9 _ s2) fun s3 ⟨l3, k3, m3, _, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm10 _ s3) fun s4 ⟨l4, k4, m4, _, o4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm11 _ s4) fun s5 ⟨l5, k5, m5, _, o5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm12 _ s5) fun s6 ⟨l6, k6, m6, _, o6⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 _ s6) fun s7 ⟨l7, k7, m7, _, o7⟩ =>
    ⟨fun l hl => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      (((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7 |>.mono (by simp),
      by rw [m7, m6, m5, m4, m3, m2, m1]⟩
  · rw [State.proj_xmm, o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) l hl,
      o4 _ (by decide) l hl, o3 _ (by decide) l hl, l2 l hl]; decide
  · rw [State.proj_xmm, o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) l hl,
      o4 _ (by decide) l hl, l3 l hl]; decide
  · rw [State.proj_xmm, o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) l hl, l4 l hl]; decide
  · rw [State.proj_xmm, o7 _ (by decide) l hl, o6 _ (by decide) l hl, l5 l hl]; decide
  · rw [State.proj_xmm, o7 _ (by decide) l hl, l6 l hl]; decide
  · rw [State.proj_xmm, l7 l hl]; decide
  · rw [State.proj_xmm, o7 _ (by decide) l hl, o6 _ (by decide) l hl, o5 _ (by decide) l hl,
      o4 _ (by decide) l hl, o3 _ (by decide) l hl, o2 _ (by decide) l hl, l1 l hl]; decide

/-! ## The stores -/

/-- The four `vperm2i128`: the first lanes of `ymm7` and `ymm4` to `ymm1`, of `ymm5` and `ymm0` to
`ymm2`, the second lanes of `ymm7` and `ymm4` to `ymm3`, of `ymm5` and `ymm0` to `ymm6`. -/
theorem perms_ok (s : State) :
    WP isa (.block cbd16Perms) s fun s' =>
      (∀ l < 2, s'.lane .xmm1 l = s.lane (if l = 0 then .xmm7 else .xmm4) 0 ∧
        s'.lane .xmm2 l = s.lane (if l = 0 then .xmm5 else .xmm0) 0 ∧
        s'.lane .xmm3 l = s.lane (if l = 0 then .xmm7 else .xmm4) 1 ∧
        s'.lane .xmm6 l = s.lane (if l = 0 then .xmm5 else .xmm0) 1) ∧
      YOnly [.xmm1, .xmm2, .xmm3, .xmm6] s s' := by
  apply WP.of_runBlock
  simp only [cbd16Perms, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left']
  have keep (t : State) (r : XReg) (lo hi : BitVec 128) : XKeep t (t.setV .l256 r lo hi) :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun l hl => ?_,
    ⟨(((keep _ _ _ _).trans (keep _ _ _ _)).trans (keep _ _ _ _)).trans (keep _ _ _ _), fun r hr l hl => ?_⟩⟩
  · rcases lane01 hl with rfl | rfl <;>
      simp [State.lane_setV256, perm2Lanes]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.lane_setV256, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- The four stores. -/
theorem stores_ok {s : State} (hw : ∀ t < 4, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (32 * t)) 32) :
    WP isa (.block cbd16Stores) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r l, s'.lane r l = s.lane r l) ∧
      s'.mem = (((s.mem.writeW (s.gpr .rsi) (s.ymm .xmm1)).writeW (s.gpr .rsi + BitVec.ofNat 64 32) (s.ymm .xmm2)).writeW
        (s.gpr .rsi + BitVec.ofNat 64 64) (s.ymm .xmm3)).writeW (s.gpr .rsi + BitVec.ofNat 64 96) (s.ymm .xmm6) := by
  have w0 := hw 0 (by decide); have w1 := hw 1 (by decide); have w2 := hw 2 (by decide)
  have w3 := hw 3 (by decide)
  simp only [Nat.reduceMul, add_ofNat_zero] at w0 w1 w2 w3
  apply WP.of_runBlock
  simp only [cbd16Stores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, ea_at, add_ofNat_zero,
    State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_ymm, w0, w1, w2, w3, ite_true,
    Option.some.injEq, exists_eq_left', State.setMem_rd, State.setMem_lane]
  exact ⟨trivial, trivial, trivial, fun _ _ => trivial, trivial⟩

/-- Four stores of 32 bytes to words `j, …, j + 63` of the polynomial at `P`. -/
theorem wstore4 (m : Mem) (P : Addr) {j : Nat} (hj : j + 64 ≤ 256) (Y0 Y1 Y2 Y3 : BitVec 256) :
    let m' := (((m.writeW (wAddr P j) Y0).writeW (wAddr P j + BitVec.ofNat 64 32) Y1).writeW
      (wAddr P j + BitVec.ofNat 64 64) Y2).writeW (wAddr P j + BitVec.ofNat 64 96) Y3
    (∀ k < 256, k < j ∨ j + 64 ≤ k → wordAt m' P k = wordAt m P k) ∧
      (∀ t < 4, ∀ e < 16, wordAt m' P (j + 16 * t + e) = ([Y0, Y1, Y2, Y3][t]!).extractLsb' (8 * (2 * e)) (8 * 2)) ∧
      Frame [sR P] m m' := by
  intro m'
  have a1 : wAddr P j + BitVec.ofNat 64 32 = wAddr P (j + 16) := wAddr_add P j 16
  have a2 : wAddr P j + BitVec.ofNat 64 64 = wAddr P (j + 32) := wAddr_add P j 32
  have a3 : wAddr P j + BitVec.ofNat 64 96 = wAddr P (j + 48) := wAddr_add P j 48
  simp only [m', a1, a2, a3]
  refine ⟨fun k hk ho => ?_, fun t ht e he => ?_, ?_⟩
  · rw [wordAt_write256 _ _ (by bdd_omega) _ hk, wordAt_write256 _ _ (by bdd_omega) _ hk,
      wordAt_write256 _ _ (by bdd_omega) _ hk, wordAt_write256 _ _ (by bdd_omega) _ hk]
    simp (disch := bdd_omega) only [ite_eq_right]
  · rw [wordAt_write256 _ _ (by bdd_omega) _ (by bdd_omega), wordAt_write256 _ _ (by bdd_omega) _ (by bdd_omega),
      wordAt_write256 _ _ (by bdd_omega) _ (by bdd_omega), wordAt_write256 _ _ (by bdd_omega) _ (by bdd_omega)]
    rcases (by bdd_omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, Nat.add_le_add_iff_left,
      Nat.add_lt_add_iff_left, Nat.le_add_right, Nat.add_sub_add_left, Nat.add_sub_cancel_left, true_and] <;>
    simp (disch := bdd_omega) only [ite_eq_left, ite_eq_right] <;> rfl
  · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega)) |>.writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by bdd_omega) (by bdd_omega))

/-- The pointers' and the count's updates. -/
theorem tail_ok (s : State) :
    WP isa (.block [.alu .add .rdi (.imm 32), .alu .add .rsi (.imm 128), .alu .sub .rcx (.imm 1)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rdi + BitVec.ofNat 64 32 ∧ s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 128 ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r l, s'.lane r l = s.lane r l) := by
  have sx32 : BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 32 := by decide
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 := by decide
  vrunm [sx32, sx128]
  intro r l; rfl

/-! ## The loop -/

open Cbd16 (cbd2_16K bP fP val grp_val word_grpX)

section
variable {s₀ : State} (hp : cbd2_16K.pre s₀)
include hp

/-- Coefficient `64 i + 32 L + 16 g + 8 t + j` from its byte, nibble `j mod 2` of byte
`8 g + 4 t + ⌊j / 2⌋` of lane `L`'s sixteen at `bP + 32 i + 16 L`. -/
theorem val_eqY {i L g t j : Nat} (hi : i < 4) (hL : L < 2) (hg : g < 2) (ht : t < 2) (hj : j < 8) {m : Mem}
    (hf : Frame [sR (fP s₀)] s₀.mem m) :
    (cbdX ((m (bP s₀ + BitVec.ofNat 64 (32 * i + 16 * L) + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat /
          16 ^ (j % 2)) + 3329 -
        cbdY ((m (bP s₀ + BitVec.ofNat 64 (32 * i + 16 * L) + BitVec.ofNat 64 (8 * g + 4 * t + j / 2))).toNat /
          16 ^ (j % 2))) % 3329 =
      val s₀ (64 * i + 32 * L + 16 * g + 8 * t + j) := by
  have hb : m (bP s₀ + BitVec.ofNat 64 (32 * i + 16 * L) + BitVec.ofNat 64 (8 * g + 4 * t + j / 2)) =
      (bytesAt s₀.mem (bP s₀) 128).getD ((64 * i + 32 * L + 16 * g + 8 * t + j) / 2) 0 := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytesAt_getD _ _ (by bdd_omega),
      show 32 * i + 16 * L + (8 * g + 4 * t + j / 2) = (64 * i + 32 * L + 16 * g + 8 * t + j) / 2 by bdd_omega]
    exact bytes_frame hf (by simpa using hp.2.2.1) (by decide) _ (by bdd_omega)
  rw [val, samplePolyCBD2_val _ (by rw [n_eq]; omega_using [hi, hL, hg, ht, hj]), nibble, q_eq, ← hb,
    show (64 * i + 32 * L + 16 * g + 8 * t + j) % 2 = j % 2 by bdd_omega]

/-- After `i` groups of 32 bytes. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = bP s₀ + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = wAddr (fP s₀) (64 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YC s
  frame : Frame [sR (fP s₀)] s₀.mem s.mem
  coeff : ∀ k < 64 * i, (wordAt s.mem (fP s₀) k).toNat = val s₀ k

omit hp in
theorem lane_sse : laneSseBlock (toY cbd16Lane) = some cbd16Lane := by decide +kernel

theorem step {i : Nat} (hi : i < 4) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (cbd2_16YBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' => Inv s₀ (i + 1) s' ∧
      s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hrd : s.rd ++ s.wr = [⟨bP s₀, 128⟩, sR (fP s₀)] := by rw [hI.rd, hI.wr, hp.1, hp.2.1]; rfl
  have hwr : s.wr = [sR (fP s₀)] := by rw [hI.wr, hp.2.1]
  have h32 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 0) 32 := by
    rw [hrd, add_ofNat_zero, hI.rdi]
    exact ⟨⟨bP s₀, 128⟩, by simp, Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩
  unfold cbd2_16YBody
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok h32) fun s1 ⟨L1, o1⟩ => ?_
  have c1 : YC s1 := yc_keep hI.c fun r hr l hl => o1.lane r (by simp_all) l hl
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_sse (rs := lregs)
    (P := fun l t => Consts t ∧ LaneOut s.mem (s.gpr .rdi + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) t)
    fun l hl => lane_ok (c1 l hl) (by rw [State.proj_xmm, L1 l hl])) fun s3 ⟨B3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (perms_ok s3) fun s4 ⟨P4, o4⟩ => ?_
  have o14 := (o1.trans o3).trans o4
  have g4 : s4.gpr = s.gpr := o14.gpr
  have hw : ∀ t < 4, InRegions s4.wr (s4.gpr .rsi + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [o14.wr, hwr, g4, hI.rsi, show 32 * t = 2 * (16 * t) by omega_using [], wAddr_add]
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base (fP s₀) (by bdd_omega) (by bdd_omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hw) fun s5 ⟨g5, rd5, wr5, l5, m5⟩ => ?_
  refine WP.mono (tail_ok s5) fun s6 ⟨di6, si6, cx6, z6, m6, rd6, wr6, l6⟩ => ⟨?_, by rw [cx6, g5, g4],
    by rw [z6, g5, g4]⟩
  have c3 : YC s3 := fun l hl => (B3 l hl).1
  have ma : s4.gpr .rsi = wAddr (fP s₀) (64 * i) := by rw [g4, hI.rsi]
  obtain ⟨wout, win, wfr⟩ := wstore4 s4.mem (fP s₀) (j := 64 * i) (by bdd_omega)
    (s4.ymm .xmm1) (s4.ymm .xmm2) (s4.ymm .xmm3) (s4.ymm .xmm6)
  rw [← ma] at wout win wfr
  have hm : s6.mem = (((s4.mem.writeW (s4.gpr .rsi) (s4.ymm .xmm1)).writeW (s4.gpr .rsi + BitVec.ofNat 64 32)
      (s4.ymm .xmm2)).writeW (s4.gpr .rsi + BitVec.ofNat 64 64) (s4.ymm .xmm3)).writeW
      (s4.gpr .rsi + BitVec.ofNat 64 96) (s4.ymm .xmm6) := by rw [m6, m5]
  have m4 : s4.mem = s.mem := o14.mem
  refine ⟨?_, ?_, rd6.trans (rd5.trans (o14.rd.trans hI.rd)), wr6.trans (wr5.trans (o14.wr.trans hI.wr)),
    yc_keep c3 fun r hr l hl => by
      rw [l6, l5, o4.lane r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with rfl | rfl | rfl | rfl <;> simp) l hl],
    ?_, fun k hk => ?_⟩
  · rw [di6, g5, g4, hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [si6, g5, ma, show (BitVec.ofNat 64 128 : BitVec 64) = BitVec.ofNat 64 (2 * 64) from rfl, wAddr_add,
      Nat.mul_succ]
  · rw [hm]; exact hI.frame.trans (by rw [← m4]; exact wfr)
  · have hrdi : ∀ l < 2, s.gpr .rdi + 0#64 + BitVec.ofNat 64 (16 * l) = bP s₀ + BitVec.ofNat 64 (32 * i + 16 * l) :=
      fun l _ => by rw [add_ofNat_zero, hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
    have key : ∀ l < 2, ∀ g < 2, ∀ b < 2, ∀ j < 8,
        (word (s3.lane (if g = 0 then (if b = 0 then .xmm7 else .xmm4) else (if b = 0 then .xmm5 else .xmm0)) l)
          j).toNat = val s₀ (64 * i + 32 * l + 16 * g + 8 * b + j) := fun l hl g hg b hb j hj => by
      obtain ⟨_, A₀, B₀, A₁, B₁, hn, h7, h4, h5, h0⟩ := B3 l hl
      rw [hrdi l hl] at hn
      have hv := grp_val hn hg hb hj
      rw [val_eqY hp hi hl hg hb hj hI.frame] at hv
      rw [← State.proj_xmm]
      rcases (by bdd_omega : g = 0 ∨ g = 1) with rfl | rfl <;> rcases (by bdd_omega : b = 0 ∨ b = 1) with rfl | rfl
      · rw [ite_eq_left rfl, ite_eq_left rfl, h7, word_grpX _ _ (by decide) hj]
        rw [ite_eq_left rfl, ite_eq_left rfl] at hv; exact hv
      · rw [ite_eq_left rfl, ite_eq_right (by decide), h4, word_grpX _ _ (by decide) hj]
        rw [ite_eq_left rfl, ite_eq_left rfl] at hv; exact hv
      · rw [ite_eq_right (by decide), ite_eq_left rfl, h5, word_grpX _ _ (by decide) hj]
        rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hv; exact hv
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), h0, word_grpX _ _ (by decide) hj]
        rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hv; exact hv
    rw [hm]
    by_cases hlo : k < 64 * i
    · rw [wout k (by bdd_omega) (.inl hlo), m4]; exact hI.coeff k hlo
    · obtain ⟨t, ht, e, he, rfl⟩ : ∃ t < 4, ∃ e < 16, k = 64 * i + 16 * t + e :=
        ⟨(k - 64 * i) / 16, by bdd_omega, (k - 64 * i) % 16, by bdd_omega, by bdd_omega⟩
      rw [win t ht e he]
      have hb : e / 8 < 2 := by bdd_omega
      have hj : e % 8 < 8 := by bdd_omega
      obtain ⟨p1, p2, p3, p6⟩ := P4 (e / 8) hb
      rcases (by bdd_omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
      · have := key 0 (by decide) 0 (by decide) (e / 8) hb (e % 8) hj
        simp only [ite_true] at this
        rw [show 64 * i + 32 * 0 + 16 * 0 + 8 * (e / 8) + e % 8 = 64 * i + 16 * 0 + e by bdd_omega] at this
        simp only [List.getElem!_cons_zero]
        rw [word_ymm _ _ he, p1]
        rcases (by bdd_omega : e / 8 = 0 ∨ e / 8 = 1) with h | h <;> rw [h] at this ⊢ <;> simpa using this
      · have := key 0 (by decide) 1 (by decide) (e / 8) hb (e % 8) hj
        simp only [ite_false, Nat.one_ne_zero] at this
        rw [show 64 * i + 32 * 0 + 16 * 1 + 8 * (e / 8) + e % 8 = 64 * i + 16 * 1 + e by bdd_omega] at this
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
        rw [word_ymm _ _ he, p2]
        rcases (by bdd_omega : e / 8 = 0 ∨ e / 8 = 1) with h | h <;> rw [h] at this ⊢ <;> simpa using this
      · have := key 1 (by decide) 0 (by decide) (e / 8) hb (e % 8) hj
        simp only [ite_true] at this
        rw [show 64 * i + 32 * 1 + 16 * 0 + 8 * (e / 8) + e % 8 = 64 * i + 16 * 2 + e by bdd_omega] at this
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
        rw [word_ymm _ _ he, p3]
        rcases (by bdd_omega : e / 8 = 0 ∨ e / 8 = 1) with h | h <;> rw [h] at this ⊢ <;> simpa using this
      · have := key 1 (by decide) 1 (by decide) (e / 8) hb (e % 8) hj
        simp only [ite_false, Nat.one_ne_zero] at this
        rw [show 64 * i + 32 * 1 + 16 * 1 + 8 * (e / 8) + e % 8 = 64 * i + 16 * 3 + e by bdd_omega] at this
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
        rw [word_ymm _ _ he, p6]
        rcases (by bdd_omega : e / 8 = 0 ∨ e / 8 = 1) with h | h <;> rw [h] at this ⊢ <;> simpa using this

theorem main : WP isa cbd2_16Avx2 s₀ fun s => Frame [sR (fP s₀)] s₀.mem s.mem ∧
    ∀ k < 256, (wordAt s.mem (fP s₀) k).toNat = val s₀ k := by
  unfold cbd2_16Avx2
  refine WP.seq (WP.mono (consts_ok s₀) fun s1 ⟨c1, k1, m1⟩ =>
    WP.seq (WP.mono (wp_rcxLoopY (N := 4) (by decide) (by decide) (Inv s₀) (s₀ := s1) (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => (consts_iff _).2 (by
          have := (consts_iff _).1 (c1 l hl); simp only [State.proj_xmm, State.lane] at this ⊢
          rw [o.xmm, hy]; exact this),
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k hk => absurd hk (by omega_using [])⟩)
      fun i hi u hI => step hp hi hI) fun u hI => ?_))
  vrunm
  exact ⟨hI.frame, fun k hk => hI.coeff k (by omega_using [hk])⟩

theorem correct : ∃ t s', Exec isa cbd2_16Avx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ cbd2_16K.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hf, hd⟩, hk⟩ := WP.keep [.rax, .rdi, .rsi, .rcx] (main hp) (by decide)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hp.2.2.2.2)), polyIsW_of_toNat fun k hk => ?_⟩
  rw [Cbd16.coeffAtW_eq]
  exact hd k (by rw [n_eq] at hk; omega_using [hk])

end

end Cbd16Y

theorem cbd2_16Y_correct (s : State) (hs : Cbd16.cbd2_16K.pre s) :
    ∃ t s', Exec isa cbd2_16Avx2 s t s' ∧ abiPreserved s s' ∧ Cbd16.cbd2_16K.post s s' :=
  Cbd16Y.correct hs

theorem cbd2_16Y_ct : ConstantTime isa Cbd16.cbd2_16K.pre Cbd16.cbd2_16K.pub cbd2_16Avx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2])
    (by taint_decide)

end VG.Proof.MlKem.X86_64
