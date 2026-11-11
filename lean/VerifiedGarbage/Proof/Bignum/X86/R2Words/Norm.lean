module

public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Run
public import VerifiedGarbage.Impl.Bignum.X86.R2Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.R2Words.Ptr

-- separate module: its proofs build in parallel with those of the steps (`Quot` to `Loop`), which `Main` also imports

/-!
# `R2Words` on x86: `p = 2^z` and `d`

`normBit` doubles `eax` and `esi` where the top bit of `eax` is clear
(`normBit_ok`); 31 of them take the top word `T ≠ 0` of `M` to `T 2^z` and
`1` to `2^z`, for the leading zeros `z` of `T` (`normLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Bignum.X86.R2Words VG.X86.Wp VG.Impl.Bignum.X86.PublicRt VG.Proof.Bignum.X86.PublicRt
open VG.Proof.Bignum.X86.PrecomputeRt

/-- The mask of a clear top bit. -/
def clearMask (a : BitVec 32) : BitVec 32 := (a >>> 31) - 1

theorem normBit_ok {s : State} :
    WP isa (.block normBit) s fun t =>
      t.gpr .eax = s.gpr .eax + (s.gpr .eax &&& clearMask (s.gpr .eax)) ∧
      t.gpr .esi = s.gpr .esi + (s.gpr .esi &&& clearMask (s.gpr .eax)) ∧
      t.gpr .edx = s.gpr .edx - 1 ∧ t.zf = some (s.gpr .edx - 1 == 0) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (WP.keeps [.eax, .ecx, .edx, .ebp, .esi] (Q := fun t =>
      t.gpr .eax = s.gpr .eax + (s.gpr .eax &&& clearMask (s.gpr .eax)) ∧
      t.gpr .esi = s.gpr .esi + (s.gpr .esi &&& clearMask (s.gpr .eax)) ∧
      t.gpr .edx = s.gpr .edx - 1 ∧ t.zf = some (s.gpr .edx - 1 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  xrun [normBit, clearMask]

/-- The leading zeros of a nonzero word. -/
def lz (T : Nat) : Nat := 31 - T.log2

/-- `T 2^i` for `i ≤ lz T` fits a word, with its top bit set exactly when `i = lz T`. -/
theorem shifted_bounds {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    T * 2 ^ i < 2 ^ 32 ∧ (T * 2 ^ i / 2 ^ 31 = if i = lz T then 1 else 0) := by
  have hL : T.log2 < 32 := (Nat.log2_lt (by omega)).mpr hT'
  have h1 := Nat.log2_self_le (n := T) (by omega)
  have h2 := Nat.lt_log2_self (n := T)
  unfold lz at hi ⊢
  have u : T * 2 ^ i < 2 ^ (T.log2 + 1 + i) := by rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
  have l : 2 ^ (T.log2 + i) ≤ T * 2 ^ i := by rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ h1
  have p1 : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨Nat.lt_of_lt_of_le u p1, ?_⟩
  by_cases e : i = 31 - T.log2
  · simp only [e, ite_true]
    have a : 2 ^ (T.log2 + (31 - T.log2)) = 2 ^ 31 := congrArg _ (by omega)
    have b : 2 ^ (T.log2 + 1 + (31 - T.log2)) = 2 * 2 ^ 31 := by
      rw [show T.log2 + 1 + (31 - T.log2) = 31 + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [e] at u l
    rw [Nat.div_eq_iff (by decide)]; omega
  · simp only [e, ite_false]
    have : 2 ^ (T.log2 + 1 + i) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.div_eq_of_lt (by omega)

/-- A step of the doublings: `T 2^i` and `2^i` to `T 2^min(i + 1, z)` and `2^min(i + 1, z)`. -/
theorem normStep_val {T i : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hi : i ≤ lz T) :
    BitVec.ofNat 32 (T * 2 ^ i) + (BitVec.ofNat 32 (T * 2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (T * 2 ^ min (i + 1) (lz T)) ∧
    BitVec.ofNat 32 (2 ^ i) + (BitVec.ofNat 32 (2 ^ i) &&& clearMask (BitVec.ofNat 32 (T * 2 ^ i))) =
      BitVec.ofNat 32 (2 ^ min (i + 1) (lz T)) := by
  obtain ⟨b1, b2⟩ := shifted_bounds hT hT' hi
  have hm : clearMask (BitVec.ofNat 32 (T * 2 ^ i)) = if i = lz T then 0 else BitVec.allOnes 32 := by
    unfold clearMask
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b1,
      Nat.shiftRight_eq_div_pow, b2]
    by_cases e : i = lz T <;> simp [e]
  rw [hm]
  by_cases e : i = lz T
  · simp only [e, ite_true, Nat.min_eq_right (Nat.le_succ _)]
    exact ⟨by simp, by simp⟩
  · simp only [e, ite_false, BitVec.and_allOnes, ← BitVec.ofNat_add]
    rw [Nat.min_eq_left (by omega), Nat.pow_succ]
    exact ⟨congrArg _ (by rw [← Nat.mul_assoc]; omega), congrArg _ (by omega)⟩

/-- The 31 doublings: from `eax = T ≠ 0`, `esi = 1` and `edx = 31`, `eax = T 2^z`
and `esi = 2^z` for `z = lz T`. -/
theorem normLoop_ok {s : State} {T : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (hax : s.gpr .eax = BitVec.ofNat 32 T)
    (hsi : s.gpr .esi = 1) (hdx : s.gpr .edx = 31) :
    WP isa (.loop (.block normBit) .ne) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (T * 2 ^ lz T) ∧ t.gpr .esi = BitVec.ofNat 32 (2 ^ lz T) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .esi] s t := by
  have hz : lz T ≤ 31 := by unfold lz; omega
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 31 - j ∧ j < 31 ∧
      t.gpr .eax = BitVec.ofNat 32 (T * 2 ^ min j (lz T)) ∧ t.gpr .esi = BitVec.ofNat 32 (2 ^ min j (lz T)) ∧
      t.gpr .edx = BitVec.ofNat 32 (31 - j) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s t) ?_ _ s
    ⟨0, rfl, by decide, by rw [hax]; simp, by rw [hsi]; simp, by rw [hdx]; rfl, rfl, Keeps.refl _ _⟩
  rintro n t ⟨j, rfl, hj, hax', hsi', hdx', hm, k⟩
  refine WP.mono normBit_ok fun t' ⟨h1, h2, h3, h4, hm', k'⟩ => ?_
  obtain ⟨e1, e2⟩ := normStep_val hT hT' (i := min j (lz T)) (Nat.min_le_right _ _)
  have hmin : min (min j (lz T) + 1) (lz T) = min (j + 1) (lz T) := by omega
  rw [hmin] at e1 e2
  obtain ⟨c1, c2⟩ := VG.Proof.Bignum.X86.PublicRt.count1_zf (N := 31) (x := t.gpr .edx)
    (by rw [hdx', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) hj
  have hd : t'.gpr .edx = BitVec.ofNat 32 (31 - (j + 1)) := by
    rw [h3]; apply BitVec.eq_of_toNat_eq; rw [c1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have K := k.trans k'
  by_cases e : j + 1 = 31
  · refine .inl ⟨by simp only [eval, h4, c2, e, decide_true, Option.map_some, Bool.not_true], ?_, ?_, hm'.trans hm, K⟩
    · rw [h1, hax', e1, Nat.min_eq_right (by omega)]
    · rw [h2, hsi', hax', e2, Nat.min_eq_right (by omega)]
  · refine .inr ⟨by simp only [eval, h4, c2, e, decide_false, Option.map_some, Bool.not_false], 31 - (j + 1), by omega, j + 1, rfl, by omega, ?_, ?_, hd,
      hm'.trans hm, K⟩
    · rw [h1, hax', e1]
    · rw [h2, hsi', hax', e2]

/-- `norm`: `p = 2^z` at 160 and `d = T 2^z + ⌊U 2^z / 2^32⌋` at 164, for `M`'s top
word `T ≠ 0` and the one below it `U`. -/
theorem norm_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {T U : Nat}
    (h : PcIn base bytes len args s) (hT : w32 s.mem base (numAt len 0 + 4 * wp len - 4) = T)
    (hU : w32 s.mem base (numAt len 0 + 4 * wp len - 8) = U) (hT0 : 0 < T) :
    WP isa norm s fun t => w32 t.mem base oP = 2 ^ lz T ∧
      w32 t.mem base oD = T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 ∧ Outside base oP 8 s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have dims := h.dimensions
  have nw' := h.scratch.nowrap
  have f0 := (h.fits (j := 0) (by decide)).1
  have hwp := wp_le_nw (len := len)
  have hl := h.lower
  have hwp16 : 16 ≤ wp len := by simp only [wp]; omega
  have e0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have hT' : T < 2 ^ 32 := hT ▸ BitVec.isLt _
  have hU' : U < 2 ^ 32 := hU ▸ BitVec.isLt _
  unfold norm
  simp only [seqs]
  refine WP.seq (topPtr_ok h (r := .ebx) (t := .ecx) (j := 0) (i := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) fun u K m p _ => ?_)
  have hu := h.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_ptr hu.ws p (d := 4) (by rw [e0]; omega)) fun u₁ U₁ _ => ?_
  refine wp_movS rfl fun u₂ U₂ _ => wp_movS rfl fun u₃ U₃ _ => WP.block_nil ?_
  have K₃ : Keeps [.ebx, .ecx, .eax, .esi, .edx] s u₃ :=
    ((K.mono (by decide)).trans (U₁.keeps.mono (by decide))).trans
      ((U₂.keeps.mono (by decide)).trans (U₃.keeps.mono (by decide)))
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, U₂.mem, U₁.mem, m]
  have ax₃ : u₃.gpr .eax = BitVec.ofNat 32 T := by
    apply BitVec.eq_of_toNat_eq
    rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr, m, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT', ← hT]
    exact congrArg (fun d => (s.mem.readW (off base d) 32).toNat) (by rw [e0]; omega)
  refine WP.seq (WP.mono (normLoop_ok hT0 hT' ax₃ (by rw [U₃.other _ (by decide), U₂.gpr]) U₃.gpr)
    fun t ⟨ax, si, mt, Kt⟩ => ?_)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := (K₃.mono (by decide)).trans (Kt.mono (by decide))
  have ht := h.keep Kall (by decide) (by decide) (by rw [mt, m₃]; exact Outside.refl _ _ _ _)
  have bx : PtrAt t base .ebx (numAt len 0 + 4 * wp len - 4 * 2) := by
    rw [PtrAt, Kt.1 _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]; exact p
  have di : PtrAt t base .edi 0 := by rw [PtrAt, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]; exact ht.edi
  have hz := (shifted_bounds hT0 hT' (Nat.le_refl (lz T))).1
  -- `p` stored, `d` computed and stored.
  refine wp_storeS (ea_ptr ht.ws di (d := oP) (by simp only [oP]; omega)) (ws_write ht.ws (by simp only [oP]; omega))
    fun t₁ M₁ => ?_
  refine wp_movS rfl fun t₂ U₂' _ => ?_
  refine wp_movS (readSrc_ptr (ht.ws.of_wr (U₂'.wr.trans M₁.wr)) (by rw [PtrAt, U₂'.other _ (by decide), M₁.gpr]; exact bx)
    (d := 0) (by rw [e0]; omega)) fun t₃ U₃' _ => ?_
  refine wp_mul fun t₄ U₄ => wp_addS rfl fun t₅ U₅ _ => ?_
  refine wp_storeS (ea_ptr (ht.ws.of_wr (U₅.wr.trans (U₄.wr.trans (U₃'.wr.trans (U₂'.wr.trans M₁.wr)))))
    (by rw [PtrAt, U₅.other _ (by decide), U₄.other _ (by decide) (by decide), U₃'.other _ (by decide),
      U₂'.other _ (by decide), M₁.gpr]; exact di) (d := oD) (by simp only [oD]; omega))
    (ws_write (ht.ws.of_wr (U₅.wr.trans (U₄.wr.trans (U₃'.wr.trans (U₂'.wr.trans M₁.wr))))) (by simp only [oD]; omega))
    fun t₆ M₆ => WP.block_nil ?_
  have hz31 : lz T ≤ 31 := by unfold lz; omega
  have hp32 : 2 ^ lz T < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpm : 2 ^ lz T ∣ T * 2 ^ lz T := Nat.dvd_mul_left _ _
  have hdz : U * 2 ^ lz T / 2 ^ 32 < 2 ^ lz T := by
    rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm (2 ^ lz T)]; exact Nat.mul_lt_mul_of_pos_right hU' (Nat.two_pow_pos _)
  have hTz : T * 2 ^ lz T + 2 ^ lz T ≤ 2 ^ 32 := by
    have e : 2 ^ 32 = 2 ^ (32 - lz T) * 2 ^ lz T := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hlt : T < 2 ^ (32 - lz T) := by rw [e] at hz; exact Nat.lt_of_mul_lt_mul_right hz
    calc T * 2 ^ lz T + 2 ^ lz T = (T + 1) * 2 ^ lz T := by rw [Nat.succ_mul]
      _ ≤ 2 ^ (32 - lz T) * 2 ^ lz T := Nat.mul_le_mul_right _ hlt
      _ = 2 ^ 32 := e.symm
  have m₁ : t₁.mem = s.mem.writeW (off base oP) (BitVec.ofNat 32 (2 ^ lz T)) := by
    rw [M₁.mem, si, mt, m₃, Nat.zero_add]
  have m₅ : t₅.mem = t₁.mem := by rw [U₅.mem, U₄.mem, U₃'.mem, U₂'.mem]
  have uv : (t₃.gpr .eax).toNat = U := by
    rw [U₃'.gpr, U₂'.mem, m₁]
    change w32 (s.mem.writeW (off base oP) _) base (numAt len 0 + 4 * wp len - 4 * 2 + 0) = U
    rw [(writeW32_outside _ base _ (d := oP) (by simp only [oP]; omega)).w32 (by simp only [oP]; rw [e0]; omega)
      (by omega), ← hU]
    exact congrArg (fun d => (s.mem.readW (off base d) 32).toNat) (by rw [e0]; omega)
  have cx : (t₅.gpr .ecx).toNat = T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 := by
    rw [U₅.gpr, U₄.other .ecx (by decide) (by decide), U₄.edx, uv, U₃'.other .ecx (by decide),
      U₃'.other .esi (by decide), U₂'.gpr, U₂'.other .esi (by decide), M₁.gpr, ax, si, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp32, Nat.mod_eq_of_lt hz,
      Nat.mod_eq_of_lt (a := U * 2 ^ lz T / 2 ^ 32) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have m₆ : t₆.mem = t₁.mem.writeW (off base oD) (t₅.gpr .ecx) := by rw [M₆.mem, m₅, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [m₆, (writeW32_outside _ base _ (d := oD) (by simp only [oD]; omega)).w32 (d := oP) (.inl (by simp only [oP, oD]; omega)) (by simp only [oP]; omega), m₁,
      w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp32]
  · rw [m₆, w32_write_self, cx]
  · rw [m₆, m₁]
    exact ((writeW32_outside _ base _ (d := oP) (by simp only [oP]; omega)).mono (by simp only [oP]; omega) (by simp only [oP]; omega)).trans
      ((writeW32_outside _ base _ (d := oD) (by simp only [oD]; omega)).mono (by simp only [oP, oD]; omega) (by simp only [oP, oD]; omega))
  · exact Kall.trans (((M₁.keeps _).trans (((U₂'.keeps.mono (by decide)).trans (U₃'.keeps.mono (by decide))).trans
      ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide))))).trans (M₆.keeps _))

end VG.Proof.Bignum.X86.R2Words
