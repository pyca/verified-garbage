module
public import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces

import VerifiedGarbage.Proof.MillerRabin.Arm.Pieces2
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.RvBase

/-! # The Miller–Rabin round on ARMv7: the words of the exponent

`ew P σ i`: the 32-bit word `i` of the exponent's array, which the round
does not write: below `2 w`, the words of `E` (`In.ew_val`); words `2 w`
and `2 w + 1`, the halves of `2^(t mod 64)` (`In.ew_low`). The load of the
word of the windows left (`St.pwordLd`), the count read (`St.pwordK`) and
tested (`St.pwordEnd`), and the threshold `4 − σ` of the last squarings
(`St.plowBits`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- Word `i` of the exponent's array, in `σ`. -/
abbrev ew (P : MP) (σ : State) (i : Nat) : Nat := w32 σ.mem (State.addr P.B) (arr P.W aE + 4 * i)

/-- `t`, the exponent of 2 in `c − 1`. -/
abbrev tOf (P : MP) (σ : State) : Nat := (Spec.Rsa.splitTwos (cOf P σ.mem - 1)).1

/-- The exponent. -/
abbrev eOf (P : MP) (σ : State) : Nat := Proof.MillerRabin.Round.exponent (cOf P σ.mem)

/-- Word `i` of a number of `k` words. -/
theorem val32_word' (m : Mem) (base : Addr) {d k i : Nat} (hi : i < k) :
    w32 m base (d + 4 * i) = val32 m base d k / 2 ^ (32 * i) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega_arith⟩
  rw [val32_append m base d i (r + 1)]
  simp only [val32]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hw]

theorem bv_add_sub (x y z : BitVec 32) : x + y - z = x + (y - z) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

section
variable {P : MP} {σ : State}

theorem In.ew_val (h : In P σ) {i : Nat} (hi : i < 2 * P.w) :
    ew P σ i = eOf P σ / 2 ^ (32 * i) % 2 ^ 32 := by
  rw [ew, val32_word' _ _ hi, ← h.numAt_val32, h.exp]

theorem In.ew_low (h : In P σ) :
    ew P σ (2 * P.w) = 2 ^ (tOf P σ % 64) % 2 ^ 32 ∧ ew P σ (2 * P.w + 1) = 2 ^ (tOf P σ % 64) / 2 ^ 32 := by
  have e := congrArg BitVec.toNat h.low
  have k64 : tOf P σ % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) k64)] at e
  have ew2 := word_eq_w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w)
  simp only [VG.Proof.Mont.word, off] at ew2
  rw [e] at ew2
  have a1 : w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w) = ew P σ (2 * P.w) := by
    simp only [ew, w32]; rw [h.off_eq, ← h.arr_eq aE, show kOff + arr P.W aE + 8 * P.w = kOff + (arr P.W aE + 4 * (2 * P.w)) by omega_arith]
  have a2 : w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w + 4) = ew P σ (2 * P.w + 1) := by
    simp only [ew, w32]; rw [h.off_eq, ← h.arr_eq aE,
      show kOff + arr P.W aE + 8 * P.w + 4 = kOff + (arr P.W aE + 4 * (2 * P.w + 1)) by omega_arith]
  rw [a1, a2] at ew2
  have lt : ew P σ (2 * P.w) < 2 ^ 32 := (σ.mem.readW _ 32).isLt
  omega_arith

end

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The count of windows into `r1`. -/
theorem St.pwordK {K : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = K) :
    VP (St P E A L V LS) (.block wordK) (fun σ s => St P E A L V LS σ s ∧ s.gpr .r1 = BitVec.ofNat 32 K) := by
  refine VP.kv wordK_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine h.ldr hw hk (r := .r1) (by decide) fun t ht hwt u => WP.block_nil ⟨⟨e, ht, hwt⟩, ?_⟩
  rw [u.gpr, vk σ e]

/-- Word `m − 1` of the exponent into `sV`, for `r1 = 8 m`. -/
theorem St.pwordLd {m : Nat} (hE : ∀ σ, E σ → In P σ) (hm : 1 ≤ m) (hm2 : m ≤ 2 * P.w) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (8 * m)) (.block wordLd)
      (St P E A L (fun σ => upd (V σ) sV (ew P σ (m - 1))) (sV :: LS)) := by
  refine VP.taint [.r1, .r7, .r8, .r9] wordLd_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, r1⟩ => ?_
  · have w₁ := h₁.1.2.2; have w₂ := h₂.1.2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · rw [h₁.2, h₂.2]
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]
  have pre := hE σ e
  have w128 := pre.w128
  simp only [wordLd]
  refine ptr_ok hw (r := .r0) (by decide) (j := aE) (by decide) fun s1 p1 rr1 m1 hw1 => ?_
  have q1 : s1.gpr .r1 = BitVec.ofNat 32 (8 * m) := by rw [rr1.gpr _ (by decide), r1]
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  have q3 : s3.gpr .r1 = BitVec.ofNat 32 (m - 1) := by
    rw [u3.gpr, dpVal, u2.gpr, q1, ofNat_shr32 (by omega_arith), show 8 * m / 2 ^ 3 = m by omega_arith,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  have fitE := hw.arr_fit (j := aE) (by decide)
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hW : P.W = 2 * P.w + 2 := rfl
  have sh : BitVec.ofNat 32 (m - 1) <<< 2 = BitVec.ofNat 32 (4 * (m - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_toNat32 (by omega_arith), ofNat_toNat32 (by omega_arith)]
    omega_arith
  have q4 : s4.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W aE + 4 * (m - 1)) := by
    rw [u4.gpr, dpVal, u3.other _ (by decide), u2.other _ (by decide), p1, q3, sh, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  have hw4 : Ws s4 P.B P.Z P.W nArr :=
    ((hw1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  have ea : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W aE + 4 * (m - 1)) := by
    rw [q4, Offset.add_add, Nat.add_zero]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) ea (hw4.read (by omega_arith)) fun s5 u5 => ?_
  have r5 : Rest [.r0, .r1, .r2] s s5 := (rr1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  have m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have h5 := h.of_rest r5 m5
  have hw5 := hw4.of_upd u5 (by decide) (by decide) (by decide)
  refine h5.str hw5 (d := sV) (by decide) (r := .r2) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  have v : (s5.gpr .r2).toNat = ew P σ (m - 1) := by
    rw [u5.gpr, u4.mem, u3.mem, u2.mem, m1]
    show w32 s.mem (State.addr P.B) (arr P.W aE + 4 * (m - 1)) = _
    exact h.keep.word (by omega_arith) (fun k hk e' => by subst e'; revert hk; decide)
      (fun d hd => wDs_hdr d hd) (h.fit (by decide))
  rwa [v] at ht

/-- Z when no window is left. -/
theorem St.pwordEnd {K : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = K) (hK : K < 2 ^ 32) :
    VP (St P E A L V LS) (.block wordEnd) (fun σ s => St P E A L V LS σ s ∧ s.z = decide (K = 0)) := by
  refine VP.kv wordEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [wordEnd]
  refine h.ldr hw hk (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t u2 z2 => WP.block_nil ⟨⟨e, h1.of_rest (u2.rest []) u2.mem,
    hw1.rest (u2.rest [])⟩, ?_⟩
  rw [z2, u1.gpr, vk σ e, show BitVec.ofNat 32 K - 0 = BitVec.ofNat 32 K from BitVec.sub_zero _,
    ofNat_beq_zero hK]

/-- The threshold `4 − σ` of the last squarings, and their count 3. -/
theorem St.plowBits (hE : ∀ σ, E σ → In P σ) :
    VP (St P E A L V LS) (.block lowBits)
      (St P E A L (fun σ => upd (upd (V σ) sR
        (foldR (BitVec.ofNat 32 (ew P σ (2 * P.w))) (BitVec.ofNat 32 (ew P σ (2 * P.w + 1)))).toNat) sQ 3)
        (sQ :: sR :: LS)) := by
  refine VP.kv lowBits_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have pre := hE σ e
  have w128 := pre.w128
  have w4 := pre.w4
  simp only [lowBits]
  refine ptr_ok hw (r := .r0) (by decide) (j := aE) (by decide) fun s1 p1 rr1 m1 hw1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  have fitE := hw.arr_fit (j := aE) (by decide)
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hW : P.W = 2 * P.w + 2 := rfl
  have sh : BitVec.ofNat 32 P.W <<< 2 = BitVec.ofNat 32 (4 * P.W) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_toNat32 (by omega_arith), ofNat_toNat32 (by omega_arith)]
    omega_arith
  have q3 : s3.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W aE + 4 * (2 * P.w)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, show s1.gpr .r9 = BitVec.ofNat 32 P.W by rw [rr1.gpr _ (by decide), hw.r9],
      sh, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, bv_add_sub, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith),
      show arr P.W aE + 4 * P.W - 8 = arr P.W aE + 4 * (2 * P.w) by omega_arith]
  have hw3 : Ws s3 P.B P.Z P.W nArr :=
    (hw1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  have rd : ∀ i, i ≤ 1 → InRegions (s3.rd ++ s3.wr) (off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + i))) 4 :=
    fun i hi => hw3.read (by omega_arith)
  have a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + 0)) := by
    rw [q3, Offset.add_add, Nat.add_zero, Nat.add_zero]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) a0 (rd 0 (by decide)) fun s4 u4 => ?_
  have a1 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + 1)) := by
    rw [u4.other _ (by decide), q3, Offset.add_add,
      show arr P.W aE + 4 * (2 * P.w) + 4 = arr P.W aE + 4 * (2 * P.w + 1) by omega_arith]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) a1 (by rw [u4.rd, u4.wr]; exact rd 1 (by decide)) fun s5 u5 => ?_
  have mem : ∀ i, i ≤ 1 → (s3.mem.readW (off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + i))) 32) =
      BitVec.ofNat 32 (ew P σ (2 * P.w + i)) := fun i hi => by
    rw [u3.mem, u2.mem, m1]
    apply BitVec.eq_of_toNat_eq
    rw [ofNat_toNat32 (σ.mem.readW _ 32).isLt]
    exact h.keep.word (by omega_arith) (fun k hk e' => by subst e'; revert hk; decide)
      (fun d hd => wDs_hdr d hd) (h.fit (by decide))
  have g4 : s4.gpr .r1 = BitVec.ofNat 32 (ew P σ (2 * P.w)) := by rw [u4.gpr]; exact mem 0 (by decide)
  have g5 : s5.gpr .r2 = BitVec.ofNat 32 (ew P σ (2 * P.w + 1)) := by
    rw [u5.gpr, u4.mem]; exact mem 1 (by decide)
  generalize hlo : BitVec.ofNat 32 (ew P σ (2 * P.w)) = lo at g4
  generalize hhi : BitVec.ofNat 32 (ew P σ (2 * P.w + 1)) = hi at g5
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s7 u7 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s8 u8 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s9 u9 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  refine wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s12 u12 => ?_
  refine wp_dp (op2_imm (by decide)) fun s13 u13 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s14 u14 => ?_
  refine wp_dp (op2_imm (by decide)) fun s15 u15 => ?_
  refine wp_dp (op2_reg _ _) fun s16 u16 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s17 u17 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s18 u18 => ?_
  have y5 : s5.gpr .r1 = lo := by rw [u5.other _ (by decide), g4]
  have x6 : s6.gpr .r1 = lo ||| hi := by rw [u6.gpr, dpVal, y5, g5]
  have x11 : s11.gpr .r2 = s9.gpr .r1 >>> 1 &&& 1 := by rw [u11.gpr, dpVal, u10.gpr]
  have x13 : s13.gpr .r3 = s9.gpr .r1 >>> 2 &&& 1 := by
    rw [u13.gpr, dpVal, u12.gpr, u11.other _ (by decide), u10.other _ (by decide)]
  have x15 : s15.gpr .r4 = s9.gpr .r1 >>> 3 &&& 1 := by
    rw [u15.gpr, dpVal, u14.gpr, u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
      u10.other _ (by decide)]
  have x15b : s15.gpr .r2 = s11.gpr .r2 := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide)]
  have x15c : s15.gpr .r3 = s13.gpr .r3 := by rw [u15.other _ (by decide), u14.other _ (by decide)]
  have x16 : s16.gpr .r4 = s15.gpr .r4 + s15.gpr .r2 := by rw [u16.gpr, dpVal]
  have x17 : s17.gpr .r4 = s16.gpr .r4 + s16.gpr .r2 <<< 1 := by rw [u17.gpr, dpVal]
  have x18' : s18.gpr .r4 = s17.gpr .r4 + s17.gpr .r3 <<< 1 := by rw [u18.gpr, dpVal]
  have x16b : s16.gpr .r2 = s15.gpr .r2 := u16.other _ (by decide)
  have x17c : s17.gpr .r3 = s15.gpr .r3 := by rw [u17.other _ (by decide), u16.other _ (by decide)]
  have x9 : s9.gpr .r1 = (fun x3 : BitVec 32 => x3 ||| x3 >>> 4) ((fun x2 : BitVec 32 => x2 ||| x2 >>> 8)
      ((fun x1 : BitVec 32 => x1 ||| x1 >>> 16) (lo ||| hi))) := by
    rw [u9.gpr, dpVal, u8.gpr, dpVal, u7.gpr, dpVal, x6]
  have x18 : s18.gpr .r4 = foldR lo hi := by
    rw [x18', x17, x16, x17c, x16b, x15, x15b, x15c, x11, x13, x9]
    rfl
  have r18 : Rest [.r0, .r1, .r2, .r3, .r4] s s18 := (rr1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans
    ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans
    ((u11.rest (by simp)).trans ((u12.rest (by simp)).trans ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans
    ((u15.rest (by simp)).trans ((u16.rest (by simp)).trans ((u17.rest (by simp)).trans (u18.rest (by simp))))))))))))))))))
  have m18 : s18.mem = s.mem := by
    rw [u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem,
      u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  have h18 := h.of_rest r18 m18
  have hw18 := hw.rest r18
  refine h18.str hw18 (d := sR) (by decide) (r := .r4) fun s19 h19 hw19 _ => ?_
  rw [x18] at h19
  refine wp_mov (op2_imm (by decide)) fun s20 u20 => ?_
  have h20 := h19.of_rest (u20.rest (ws := [.r1]) (by simp)) u20.mem
  have hw20 := hw19.of_upd u20 (by decide) (by decide) (by decide)
  refine h20.str hw20 (d := sQ) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u20.gpr] at ht
  subst hlo hhi
  exact ht

end

end VG.Proof.MillerRabin.Arm
