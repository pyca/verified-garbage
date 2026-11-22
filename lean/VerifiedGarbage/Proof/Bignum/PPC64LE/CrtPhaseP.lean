module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.WinPow
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup

/-! ### `Bignum.PPC64LE.CrtPowerB`, which only this module used -/

section

/-!
# The RSA private-key operation on PPC64LE: a prime's power, the exponent

`powerB_ok`: the exponent's address and length from the header into `r30`
and `r31`, then `x^d mod p` into array 4 (`ModExp.powWin`), for `x` in array
4, `R² mod p` in array 1 and `-p⁻¹ mod 2³²` in `r12`. `power_ok`: all of
`power`, from `powerA_ok`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `power`'s second part, in the working space `off BX oA` with the prime
`P` in array 0, `R² mod P` in array 1 and `x` in array 4, for the `L`
bytes at `D` (from the header's words `oD` and `oLen`): `x^d mod P` into
array 4. -/
theorem powerB_ok {s : State} {BX D : Addr} {Z oA wA L Pv x oD oLen : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31) (h256 : 256 ≤ oA)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hDp : word s.mem BX oD = off D 0) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L)
    (hL : 1 ≤ L) (hL' : L < 2 ^ 63) (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : val32 s.mem (off BX oA) (slot wA 0) (2 * wA) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (h1 : val32 s.mem (off BX oA) (slot wA 1) (2 * wA) = 2 ^ (128 * wA) % Pv)
    (hx : val32 s.mem (off BX oA) (slot wA 4) (2 * wA) = x) :
    WP isa (.seq (.block [.load .d .r30 .r23 oD, .load .d .r31 .r23 oLen]) ModExp.powWinFn) s fun t =>
      (val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv ∧
        val32 t.mem (off BX oA) (slot wA 4) (2 * wA) = x ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot wA 24) s.mem t.mem) ∧ Keep powerRegs s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 24
  have hsA := hs.sub hA
  have hD' : s.mem.readW (off BX oD) 64 = off D 0 := hDp
  have hL'' : s.mem.readW (off BX oLen) 64 = BitVec.ofNat 64 L := hLw
  refine WP.seq (WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off D 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 L ∧ t.mem = s.mem) (by
      prun [h23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oD < 2 ^ 15 by omega_arith, show oD % 4 = 0 by omega_arith⟩,
        exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oLen < 2 ^ 15 by omega_arith, show oLen % 4 = 0 by omega_arith⟩,
        hs.ld (show oD + 8 ≤ Z by omega_arith), hs.ld (show oLen + 8 ≤ Z by omega_arith), hD', hL'']) rfl)
    fun s₁ ⟨⟨a30, a31, m1⟩, k1⟩ => ?_)
  rw [← m1] at hP h1 hx
  obtain hlow : (word s₁.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    obtain h1' := word_eq_w32 s₁.mem (off BX oA) (slot wA 0)
    have h2 : val32 s₁.mem (off BX oA) (slot wA 0) (2 * wA - 1 + 1) =
        w32 s₁.mem (off BX oA) (slot wA 0) + 2 ^ 32 * val32 s₁.mem (off BX oA) (slot wA 0 + 4) (2 * wA - 1) := rfl
    rw [Nat.sub_add_cancel (by omega_arith : 1 ≤ 2 * wA), hP] at h2
    simp only [Nat.reducePow] at h1' h2
    obtain hw : w32 s₁.mem (off BX oA) (slot wA 0) % 2 = 1 := by omega_using [h2, hPodd]
    rw [h1']
    omega_using [hw]
  have hb : Spec.Rsa.bytesAt s₁.mem D L = Spec.Rsa.bytesAt s.mem D L := by rw [m1]
  refine WP.mono (Win.powWinCall_ok (hsA.congr k1.wr) hw2 hw' (Nat.le_refl _)
    ((k1.gpr _ (by decide)).trans h10) ((k1.gpr _ (by decide)).trans h29)
    ((k1.gpr _ (by decide)).trans h11) hlow (by rw [hP]; exact hP2) (by rw [hP]; exact hPodd)
    (by rw [h1, hP]; exact Nat.mod_lt _ (by omega_arith)) a30 a31 hL hL'
    (fun i hi => by rw [k1.rd, k1.wr]; exact hrdD i hi)
    (fun i hi y hy => hsepD i hi y (by rw [ofs_sub hy (by omega_arith)]; omega_arith))) fun t ⟨⟨hpow, out10⟩, k10⟩ => ?_
  have hpr : ∀ r ∈ Win.win wA, slot wA 0 + 4 * (2 * wA) ≤ r.1 ∨ r.1 + r.2 ≤ slot wA 0 := by
    intro r hr
    rw [Win.win, List.mem_singleton] at hr
    subst hr
    left; simp only [e]; omega_arith
  refine ⟨⟨?_, ?_, ?_⟩, (k1.trans k10).mono (by decide)⟩
  · rw [out10.val32 hpr (by omega_arith), hP]
  · rw [hpow (by rw [h1, hP, ← Nat.pow_add, ← Nat.two_mul, ← Nat.mul_assoc]), hx, hP, hb]
  · rw [m1] at out10
    refine outs_sub out10 (fun r hr => ?_) (by omega_arith) (by omega_arith)
    rw [Win.win, List.mem_singleton] at hr
    subst hr
    simp only [e]; omega_arith

/-- `power xj oD oLen`, in the working space `off BX oA` of `w_A` words: for
the prime `P` (`w_A` words of `X`'s array `xj`) and the input `c` (the first
`w_A n` words of `X`'s array 6), array 4 holds `c^d mod P` for the exponent
`d` (`L` bytes at `D`), with `k`, `D` and `L` from the header. -/
theorem power_ok {pc q : Bool} {s : State} {BX D : Addr} {Z oA wA wX xj k L Pv Cv oD oLen : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hn : wA * nChunks ((k + 7) / 8) wA ≤ wX)
    (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hDp : word s.mem BX oD = off D 0) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L) (hL : 1 ≤ L)
    (hL' : L < 2 ^ 63) (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hC : wv s.mem BX (slot wX 6) (wA * nChunks ((k + 7) / 8) wA) = Cv)
    (hR2 : pc = true → ∃ S pL b, R2C q s BX S Z wA Pv pL b) :
    WP isa (powerG pc q xj oD oLen) s fun t =>
      (val32 t.mem (off BX oA) (slot wA 0) (2 * wA) = Pv ∧
        val32 t.mem (off BX oA) (slot wA 4) (2 * wA) = Cv ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot wA 24) s.mem t.mem ∧ t.gpr .r10 = off (off BX oA) (slot wA 0)) ∧
      Keep (.r10 :: powerRegs) s t := by
  have eX8 : slot wX 8 = hdrBytes + 8 * (8 * (wX + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  unfold powerG
  refine powerA_ok hs hA hXA hw2 hw' hwx hxj h10 h21 h29 h11 h23 h27 h28 hK hk hk' hn hP hP2 hPodd hC hR2
    fun t v0 v1 v4 t12 tinv out t10 k => ?_
  have hb : Spec.Rsa.bytesAt t.mem D L = Spec.Rsa.bytesAt s.mem D L := bytesAt_out out hA hsepD
  have hd : ∀ d, d + 8 ≤ 256 → word t.mem BX d = word s.mem BX d := fun d hd' =>
    out.word (Or.inl (by omega_arith)) (by omega_arith)
  refine WP.mono (powerB_ok (hs.congr k.wr) hA hw2 hw' (by omega_arith) t10
    ((k.gpr _ (by decide)).trans h29) ((k.gpr _ (by decide)).trans h11) ((k.gpr _ (by decide)).trans h23)
    hoD hoL (by rw [hd _ hoD.1]; exact hDp) (by rw [hd _ hoL.1]; exact hLw) hL hL'
    (fun i hi => by rw [k.rd, k.wr]; exact hrdD i hi) hsepD v0 hP2 hPodd v1 v4)
    fun u ⟨⟨u0, u4, uo⟩, ku⟩ => ⟨⟨u0, ?_, out.trans uo, (ku.gpr _ (by decide)).trans t10⟩,
      (k.trans ku).mono (by decide +kernel)⟩
  rw [u4, hb, ← Nat.pow_mod]

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: a prime's phase

`phaseP_ok`: `setupP` and `power`, the input to the power of the prime's
exponent modulo the prime, in its working space's array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The low words of a number below their range. -/
theorem wv_low {m : Mem} {B : Addr} {d wA wX v : Nat} (h : wv m B d wX = v) (hv : v < 2 ^ (64 * wA))
    (hw : wA ≤ wX) : wv m B d wA = v := by
  have hs := wv_add m B d wA (wX - wA)
  rw [show wA + (wX - wA) = wX by omega_arith, h] at hs
  have hl := wv_lt m B d wA
  rcases Nat.eq_zero_or_pos (wv m B (d + 8 * wA) (wX - wA)) with h0 | h0
  · rw [h0, Nat.mul_zero, Nat.add_zero] at hs; exact hs.symm
  · have := Nat.le_mul_of_pos_right (2 ^ (64 * wA)) h0
    omega_arith

/-- `setupP oB oLen` and `power`'s head (`powerA_ok`), then `c`. -/
theorem phasePA_ok {pc q : Bool} {s : State} {BX : Addr} {Z oA wX xj k L Pv Cv oB oLen : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot (wsWords L) 24 ≤ Z) (hXA : slot wX 8 ≤ oA)
    (hwX2 : wX = 2 * ((k + 7) / 8)) (hwk : wsWords L ≤ (k + 7) / 8) (hwX : wX < 2 ^ 31) (hxj : xj < 8)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0)
    (hB : word s.mem BX oB = off BX oA) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hP : Mont.val32 s.mem BX (slot wX xj) (2 * wX) = Pv) (hPb : Pv < 2 ^ (64 * wsWords L)) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) (hC : wv s.mem BX (slot wX 6) wX = Cv) (hCb : Cv < 256 ^ k)
    (hR2 : pc = true → ∃ S pL b, R2C q s BX S Z (wsWords L) Pv pL b)
    (hc : ∀ t, Outside BX oA (slot (wsWords L) 24) s.mem t.mem →
      t.gpr .r10 = off (off BX oA) (slot (wsWords L) 0) → t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords L) →
      t.gpr .r21 = off (off BX oA) (slot (wsWords L) 0) → t.gpr .r29 = BitVec.ofNat 64 (8 * (wsWords L + 2)) →
      Keep (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs) s t → WP isa c t Q) :
    WP isa (.seq (.block (setupP oB oLen)) (.seq (.block (([.load .d .r25 .r23 oNLen, .addi .r14 .r10 0] : List Instr) ++
      xb .r15 xj ++ r2Ptr pc q)) (.seq copyN (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++
      PublicChecked.base .r8 2 ++ PublicChecked.base .r9 3)) (.seq (r2Step pc) (.seq reduceIn c)))))) s Q := by
  have hn := hs.nowrap
  have e8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hw2 : 2 ≤ wsWords L := by unfold wsWords; omega_arith
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL (by omega_arith) hB hLw hL hL')
    fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  refine powerA_ok (k := k) (Cv := Cv) (hs.congr k1.wr) hA hXA hw2 (by omega_arith) (by omega_arith) hxj a10 a21 a29
    a11 ((k1.gpr _ (by decide)).trans h23) ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28)
    (by rw [m1]; exact hK) hk hk' (by rw [hwX2]; exact chunks_le (by omega_arith) hwk)
    (by rw [m1]; exact wv_low (by rw [← Pre.val32_eq_wv]; exact hP) hPb (by omega_arith)) hP2 hPodd
    (by rw [m1]; exact chunks_val (by omega_arith) hwk (by rw [← hwX2]; exact hC) hCb)
    (fun hp => let ⟨S, pL, b, C⟩ := hR2 hp
      ⟨S, pL, b, C.of_mem m1 (by rw [k1.rd, k1.wr]) (k1.gpr _ (by decide))⟩)
    fun t _ _ _ _ _ out t10 k => hc t (by rw [← m1]; exact out) t10 ((k.gpr _ (by decide)).trans a11)
      ((k.gpr _ (by decide)).trans a21) ((k.gpr _ (by decide)).trans a29) ((k1.trans k).mono (by decide +kernel))

/-- `setupP oB oLen` and `power xj oD oLen`: for the prime `P` in `X`'s array
`xj` (below `2^(64 w_A)`, `w_A` the words of its length `L`) and the input `c`
(`k` bytes) in `X`'s array 6, its working space at `off BX oA` (the header's
word `oB`) holds `P` in array 0 and `c^d mod P` in array 4. -/
theorem phaseP_ok {pc q : Bool} {s : State} {BX D : Addr} {Z oA wX xj k L Pv Cv oB oLen oD : Nat}
    (hs : Scr s BX Z) (hA : oA + slot (wsWords L) 24 ≤ Z) (hXA : slot wX 8 ≤ oA)
    (hwX2 : wX = 2 * ((k + 7) / 8)) (hwk : wsWords L ≤ (k + 7) / 8) (hwX : wX < 2 ^ 31) (hxj : xj < 8)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hoD : oD + 8 ≤ 256 ∧ oD % 8 = 0)
    (hB : word s.mem BX oB = off BX oA) (hLw : word s.mem BX oLen = BitVec.ofNat 64 L)
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hDp : word s.mem BX oD = off D 0) (hL : 1 ≤ L) (hL' : L < 2 ^ 60) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1) (hsepD : ∀ i < L, ∀ x, ofs BX x < Z → off D i ≠ x)
    (hP : Mont.val32 s.mem BX (slot wX xj) (2 * wX) = Pv) (hPb : Pv < 2 ^ (64 * wsWords L)) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) (hC : wv s.mem BX (slot wX 6) wX = Cv) (hCb : Cv < 256 ^ k)
    (hR2 : pc = true → ∃ S pL b, R2C q s BX S Z (wsWords L) Pv pL b) :
    WP isa (.seq (.block (setupP oB oLen)) (powerG pc q xj oD oLen)) s fun t =>
      (Mont.val32 t.mem (off BX oA) (slot (wsWords L) 0) (2 * wsWords L) = Pv ∧
        Mont.val32 t.mem (off BX oA) (slot (wsWords L) 4) (2 * wsWords L) =
          Cv ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D L) % Pv ∧
        Outside BX oA (slot (wsWords L) 24) s.mem t.mem ∧
        t.gpr .r10 = off (off BX oA) (slot (wsWords L) 0) ∧ t.gpr .r21 = off (off BX oA) (slot (wsWords L) 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (wsWords L + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords L)) ∧
      Keep (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs) s t := by
  have hn := hs.nowrap
  have e8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hw2 : 2 ≤ wsWords L := by unfold wsWords; omega_arith
  refine WP.seq (WP.mono (setupP_ok hs h23 hoB hoL (by omega_arith) hB hLw hL hL')
    fun s₁ ⟨⟨a10, a21, a29, a11, _, m1⟩, k1⟩ => ?_)
  refine WP.mono (power_ok (D := D) (k := k) (L := L) (Cv := Cv) (hs.congr k1.wr) hA hXA hw2 (by omega_arith)
    (by omega_arith) hxj a10 a21 a29 a11 ((k1.gpr _ (by decide)).trans h23) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) (by rw [m1]; exact hK) hk hk'
    (by rw [hwX2]; exact chunks_le (by omega_arith) hwk) hoD hoL (by rw [m1]; exact hDp)
    (by rw [m1]; exact hLw) hL (by omega_arith) (fun i hi => by rw [k1.rd, k1.wr]; exact hrdD i hi) hsepD
    (by rw [m1]; exact wv_low (by rw [← Pre.val32_eq_wv]; exact hP) hPb (by omega_arith)) hP2 hPodd
    (by rw [m1]; exact chunks_val (by omega_arith) hwk (by rw [← hwX2]; exact hC) hCb)
    (fun hp => let ⟨S, pL, b, C⟩ := hR2 hp
      ⟨S, pL, b, C.of_mem m1 (by rw [k1.rd, k1.wr]) (k1.gpr _ (by decide))⟩))
    fun t ⟨⟨v0, v4, o, t10⟩, k2⟩ => ⟨⟨v0, by rw [v4, m1], by rw [← m1]; exact o, t10,
      (k2.gpr _ (by decide)).trans a21, (k2.gpr _ (by decide)).trans a29, (k2.gpr _ (by decide)).trans a11⟩,
      (k1.trans k2).mono (by decide +kernel)⟩

end VG.Proof.Bignum.PPC64LE.Crt
