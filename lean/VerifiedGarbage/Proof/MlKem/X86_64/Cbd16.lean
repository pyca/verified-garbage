module

public import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16
public import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlKem.X86_64.Cbd16
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMem
meta import VerifiedGarbage.Proof.MlKem.Kpke16Contract
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.Mem16
meta import VerifiedGarbage.Proof.Framework.Offset

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
  simp (disch := first | decide | omega) only [word_punpcklwd, word_punpckhwd, word_pand, word_paddw,
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
    obtain ⟨r, rfl, hr⟩ : ∃ r, k = b + r ∧ r < 16 := ⟨k - b, by omega, by omega⟩
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
  rw [val, samplePolyCBD2_val _ (by rw [n_eq]; omega), nibble, q_eq, ← hb,
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
  exact hI.coeff k (by rw [n_eq] at hk; omega)

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

/-- A state satisfying the precondition. -/
def cbd2_16Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 512⟩]

end VG.Proof.MlKem.X86_64
