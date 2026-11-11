module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Impl.Bignum.X86.R2Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In

/-!
# `R2Words` on x86: the reciprocal

`divBit` is a bit of restoring division by `d` (`divBit_ok`, `divBit_val`);
32 of them from `r = 2^32 - 1 - d` take `q` to `v = ⌊(2^64 - 1) / d⌋ - 2^32`
(`recip_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.R2Words VG.X86.Wp VG.Proof.Bignum.X86.PrecomputeRt VG.Impl.Bignum.X86.PublicRt
open VG.Proof.Bignum.X86.PublicRt

/-- The subtraction mask of a bit: all ones if the carry is set or `2 r + 1 ≥ d`. -/
def subMask (a D : BitVec 32) : BitVec 32 :=
  (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide ((a + a + 1).toNat < D.toNat)))) ^^^ -1 |||
    (0#32 - BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + a.toNat))))

theorem dbl1 (r : Nat) : BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1 = BitVec.ofNat 32 (2 * r + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.two_mul]

theorem subMask_eq {r d : Nat} (hr : r < d) (hd : d < 2 ^ 32) :
    subMask (BitVec.ofNat 32 r) (BitVec.ofNat 32 d) = if d ≤ 2 * r + 1 then BitVec.allOnes 32 else 0 := by
  have hr' : r < 2 ^ 32 := by omega
  unfold subMask
  rw [dbl1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr', Nat.mod_eq_of_lt hd]
  by_cases c : 2 ^ 32 ≤ r + r
  · rw [decide_eq_true c, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    generalize decide (_ < d) = b1
    cases b1 <;> rfl
  · rw [decide_eq_false c]
    by_cases b : (2 * r + 1) % 2 ^ 32 < d
    · rw [decide_eq_true b, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; rfl
    · rw [decide_eq_false b, ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; rfl

theorem divBit_rem {r d : Nat} (hr : r < d) (hd : d < 2 ^ 32) :
    BitVec.ofNat 32 r + BitVec.ofNat 32 r + 1 - (BitVec.ofNat 32 d &&& subMask (BitVec.ofNat 32 r) (BitVec.ofNat 32 d)) =
      BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by
  rw [subMask_eq hr hd, dbl1]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d ≤ 2 * r + 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h), BitVec.and_allOnes, BitVec.toNat_sub,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp

theorem divBit_quot {r d q : Nat} (hr : r < d) (hd : d < 2 ^ 32) :
    BitVec.ofNat 32 q + BitVec.ofNat 32 q - subMask (BitVec.ofNat 32 r) (BitVec.ofNat 32 d) =
      BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) := by
  rw [subMask_eq hr hd, ← BitVec.ofNat_add, ← Nat.two_mul]
  apply BitVec.eq_of_toNat_eq
  by_cases h : d ≤ 2 * r + 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h), BitVec.toNat_sub, BitVec.toNat_allOnes,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h)]
    simp

/-- A bit of the division: from `r < d` in `edx`, `d` in `esi`, `q` in `ecx`
and the count `n` in `edi`, the next remainder and quotient (`divBit_inv`), and
the count down. -/
theorem divBit_ok {s : State} {r d q n : Nat} (hdx : s.gpr .edx = BitVec.ofNat 32 r)
    (hsi : s.gpr .esi = BitVec.ofNat 32 d) (hcx : s.gpr .ecx = BitVec.ofNat 32 q)
    (hdi : s.gpr .edi = BitVec.ofNat 32 n) (hr : r < d) (hd : d < 2 ^ 32) :
    WP isa (.block divBit) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) ∧ t.gpr .esi = s.gpr .esi ∧
      t.gpr .edi = BitVec.ofNat 32 n - 1 ∧ t.zf = some (BitVec.ofNat 32 n - 1 == 0) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := by
  refine WP.mono (WP.keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] (Q := fun t =>
      t.gpr .edx = BitVec.ofNat 32 (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (2 * q + if d ≤ 2 * r + 1 then 1 else 0) ∧ t.gpr .esi = s.gpr .esi ∧
      t.gpr .edi = BitVec.ofNat 32 n - 1 ∧ t.zf = some (BitVec.ofNat 32 n - 1 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
  have e1 := divBit_rem hr hd
  have e2 := divBit_quot (q := q) hr hd
  unfold subMask at e1 e2
  xrun [divBit, hdx, hsi, hcx, hdi, e1, e2]

/-- The dividend of `recip` after `j` bits. -/
def rdiv (d j : Nat) : Nat := (2 ^ 32 - 1 - d) * 2 ^ j + (2 ^ j - 1)

theorem rdiv_succ (d j : Nat) : rdiv d (j + 1) = 2 * rdiv d j + 1 := by
  unfold rdiv
  generalize 2 ^ 32 - 1 - d = K
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_assoc]
  have := Nat.one_le_two_pow (n := j)
  omega

/-- The loop of `recip`: from `r = 2^32 - 1 - d`, `q = 0` and the count 32,
`q = ⌊rdiv d 32 / d⌋`. -/
theorem recipLoop_ok {s : State} {d : Nat} (hd : 2 ^ 31 ≤ d) (hd' : d < 2 ^ 32)
    (hdx : s.gpr .edx = BitVec.ofNat 32 (2 ^ 32 - 1 - d)) (hsi : s.gpr .esi = BitVec.ofNat 32 d)
    (hcx : s.gpr .ecx = BitVec.ofNat 32 0) (hdi : s.gpr .edi = BitVec.ofNat 32 32) :
    WP isa (.loop (.block divBit) .ne) s fun t => t.gpr .ecx = BitVec.ofNat 32 (rdiv d 32 / d) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ j q r, n = 32 - j ∧ j < 32 ∧ t.gpr .edx = BitVec.ofNat 32 r ∧
      t.gpr .ecx = BitVec.ofNat 32 q ∧ t.gpr .esi = BitVec.ofNat 32 d ∧ t.gpr .edi = BitVec.ofNat 32 (32 - j) ∧
      r < d ∧ rdiv d j = q * d + r ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t) ?_ _ s
    ⟨0, 0, 2 ^ 32 - 1 - d, rfl, by decide, hdx, hcx, hsi, hdi, by omega, by simp [rdiv], rfl, Keeps.refl _ _⟩
  rintro n t ⟨j, q, r, rfl, hj, hdx', hcx', hsi', hdi', hr, hP, hm, k⟩
  refine WP.mono (divBit_ok hdx' hsi' hcx' hdi' hr hd') fun t' ⟨h1, h2, h3, h4, h5, hm', k'⟩ => ?_
  obtain ⟨hP', hr'⟩ := VG.Proof.Bignum.WordStep32.divBit_inv hP hr (show 1 < 2 by decide)
  rw [← rdiv_succ] at hP'
  obtain ⟨c1, c2⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf (N := 32) (x := BitVec.ofNat 32 (32 - j))
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have hd₁ : t'.gpr .edi = BitVec.ofNat 32 (32 - (j + 1)) := by
    rw [h4]; apply BitVec.eq_of_toNat_eq; rw [c1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have K := k.trans k'
  by_cases e : j + 1 = 32
  · refine .inl ⟨by simp only [eval, h5, c2, e, decide_true, Option.map_some, Bool.not_true], ?_, hm'.trans hm, K⟩
    have e32 : rdiv d 32 = (2 * q + if d ≤ 2 * r + 1 then 1 else 0) * d +
        (if d ≤ 2 * r + 1 then 2 * r + 1 - d else 2 * r + 1) := by rw [show (32 : Nat) = j + 1 by omega]; exact hP'
    have key : ∀ Q R, R < d → (Q * d + R) / d = Q := fun Q R h' => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h', Nat.zero_add]
    rw [h2, e32, key _ _ hr']
  · refine .inr ⟨by simp only [eval, h5, c2, e, decide_false, Option.map_some, Bool.not_false], 32 - (j + 1), by omega,
      j + 1, _, _, rfl, by omega, h1, h2, by rw [h3]; exact hsi', hd₁, hr', hP', hm'.trans hm, K⟩

theorem xor_m1 (d : Nat) (hd : d < 2 ^ 32) : BitVec.ofNat 32 d ^^^ (-1) = BitVec.ofNat 32 (2 ^ 32 - 1 - d) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (-1 : BitVec 32) = BitVec.allOnes 32 from rfl, BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (by omega)]

/-- `recip`: `v = ⌊(2^64 - 1) / d⌋ - 2^32` at 168, for `d ≥ 2^31` at 164. -/
theorem recip_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {d : Nat}
    (h : PcIn base bytes len args s) (hD : w32 s.mem base oD = d) (hd1 : 2 ^ 31 ≤ d) (hd2 : d < 2 ^ 32) :
    WP isa recip s fun t => w32 t.mem base oV = (2 ^ 64 - 1) / d - 2 ^ 32 ∧ Outside base oV 4 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw' := h.scratch.nowrap
  have sp := h.space
  have hdims := h.dimensions
  have hb : 256 ≤ bytes := by have := (h.fits (j := 0) (by decide)).1; simp only [numAt, numOff] at this; omega
  have di : PtrAt s base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact h.edi
  have hdi := ptr_eq di
  have ha := addr_off base (x := 0) (d := oD) (by simp only [oD]; omega)
  have hin : InRegions (s.rd ++ s.wr) (off base (0 + oD)) 4 := ws_read h.ws (by simp only [oD]; omega)
  have hv : s.mem.readW (off base (0 + oD)) 32 = BitVec.ofNat 32 d := by
    rw [Nat.zero_add]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD)
  unfold recip
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keeps [.esi, .edx, .ecx, .edi] (Q := fun t => t.gpr .esi = BitVec.ofNat 32 d ∧
      t.gpr .edx = BitVec.ofNat 32 (2 ^ 32 - 1 - d) ∧ t.gpr .ecx = BitVec.ofNat 32 0 ∧
      t.gpr .edi = BitVec.ofNat 32 32 ∧ t.mem = s.mem) (by
    xrun [hd, hdi, ha, hin, hv, xor_m1 d hd2]; done) rfl) fun u ⟨⟨h1, h2, h3, h4, hm⟩, K⟩ => ?_)
  refine WP.seq (WP.mono (recipLoop_ok hd1 hd2 h2 h1 h3 h4) fun t ⟨hcx, hmt, Kt⟩ => ?_)
  have Kst : Keeps [.esi, .edx, .ecx, .edi, .eax, .ebx, .ebp] s t := (K.mono (by decide)).trans (Kt.mono (by decide))
  have A4 := (h.stack 4 (by decide)).keep Kst (by decide) (by rw [hmt, hm]; exact Outside.refl _ _ _ _)
  refine wp_movS A4.readSrc fun t₁ U₁ _ => ?_
  have di₁ : PtrAt t₁ base .edi 0 := by rw [PtrAt, U₁.gpr, h.edi_eq]; exact di
  have ws₁ : Ws t₁ base bytes := h.ws.of_wr (U₁.wr.trans Kt.2.2 |>.trans K.2.2)
  refine wp_storeS (ea_ptr ws₁ di₁ (d := oV) (by simp only [oV]; omega)) (ws_write ws₁ (by simp only [oV]; omega))
    fun t₂ M₂ => WP.block_nil ?_
  have hq : rdiv d 32 / d = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [← VG.Proof.Bignum.WordStep32.recip_eq hd2 (by omega)]; rfl
  have hv32 : (2 ^ 64 - 1) / d - 2 ^ 32 < 2 ^ 32 := by
    have : (2 ^ 64 - 1) / d < 2 ^ 33 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [M₂.mem, Nat.zero_add, w32_write_self, U₁.other _ (by decide), hcx, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]
  · rw [M₂.mem, U₁.mem, hmt, hm, Nat.zero_add]; exact writeW32_outside _ _ _ (by simp only [oV]; omega)
  · refine ⟨fun r hr => ?_, by rw [M₂.rd, U₁.rd, Kt.2.1, K.2.1], by rw [M₂.wr, U₁.wr, Kt.2.2, K.2.2]⟩
    rw [M₂.gpr]
    by_cases e : r = .edi
    · subst e; rw [U₁.gpr, h.edi_eq]
    · rw [U₁.other _ e, Kst.1 r (by revert hr e; cases r <;> decide)]

end VG.Proof.Bignum.X86.R2Words
