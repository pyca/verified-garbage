module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtR2
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreR2Fast
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: checking the cached `R² mod p`

`r2_check`: for an odd `N > 1` and `R = 2^(64 w)`, `x < N` and
`x R⁻² mod N = 1` (two Montgomery multiplications by 1) hold exactly when
`x = R² mod N`. `checkR2_ok`: `checkR2` clears the mask `r26` unless the
cached value it copies (`r2Copy`) is the prime's `R² mod p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE
open VG.Proof.Mont (val32 w32)

/-- `x < N` and `x R⁻² ≡ 1`, for the Montgomery products `v₅ ≡ x R⁻¹` and
`v₆ ≡ v₅ R⁻¹`, `v₆` below `N`, hold exactly when `x = R² mod N`. -/
theorem r2_check {N x v5 v6 k : Nat} (hN2 : 2 ≤ N) (hodd : N % 2 = 1)
    (h5 : v5 * 2 ^ k % N = x * 1 % N) (h6l : v6 < N) (h6 : v6 * 2 ^ k % N = v5 * 1 % N) :
    (x < N ∧ v6 = 1) ↔ x = 2 ^ (2 * k) % N := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd k
  rw [Nat.mul_one] at h5 h6
  have e2 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [Nat.two_mul, Nat.pow_add]
  constructor
  · rintro ⟨hx, rfl⟩
    rw [Nat.one_mul] at h6
    -- `v₅ = R mod N`, then `x ≡ v₅ R ≡ R²`.
    have hv5 : v5 % N = 2 ^ k % N := h6.symm
    rw [e2, ← Nat.mod_eq_of_lt hx, ← h5, Nat.mul_mod, hv5, ← Nat.mul_mod]
  · intro hx
    refine ⟨by rw [hx]; exact Nat.mod_lt _ (by omega), ?_⟩
    -- `v₅ R ≡ R R`, so `v₅ ≡ R`; `v₆ R ≡ 1 R`, so `v₆ ≡ 1`.
    have a5 : v5 % N = 2 ^ k % N := VG.Proof.Bignum.mont_cancel hR (by
      rw [h5, hx, e2, Nat.mod_mod])
    have a6 : v6 % N = 1 % N := VG.Proof.Bignum.mont_cancel hR (by rw [h6, Nat.one_mul, a5])
    rwa [Nat.mod_eq_of_lt h6l, Nat.mod_eq_of_lt (by omega : 1 < N)] at a6

/-- The masks of two conditions. -/
theorem and_masks (r : BitVec 64) (a b : Prop) [Decidable a] [Decidable b] :
    (r &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a then 1 else 0))) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)) =
      r &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a ∧ b then 1 else 0)) := by
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, ↓reduceIte, and_self, and_false, false_and] <;>
    simp [BitVec.and_assoc]

/-- The registers `checkR2` writes. -/
def checkR2Regs : List Reg :=
  [.r0, .r3, .r4, .r5, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r20, .r24, .r26] ++ Pub.montRegs

/-- An array's word `w` := 0. -/
theorem zeroTop_ok {t : State} {B : Addr} {Z w j : Nat} (hs : Scr t B Z) (hj : slot w j + 8 * w + 8 ≤ Z)
    (h10 : t.gpr .r10 = off B (slot w 0)) (h29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (PublicChecked.base .r14 j ++ [.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
      .store .d .r0 .r14 0])) t fun u =>
      u.mem = t.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ Keep [.r14, .r0] t u := by
  have hnw := hs.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 j) fun s₃ ⟨⟨a14, m3⟩, k3⟩ => ?_
  refine WP.mono (WP.keep [.r14, .r0] (Q := fun u =>
    u.mem = s₃.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64)) ?_ (by decide)) fun u ⟨m4, k4⟩ => ?_
  · have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith)]; congr 2
    prun [a14, (k3.gpr .r29 (by decide)).trans h29, off_add, e16,
      (hs.congr k3.wr).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith)]
    rfl
  · rw [m3] at m4; exact ⟨m4, (k3.trans k4).mono⟩

/-- `checkR2 q xj`, in the working space `off BX oA` of `w_A` words (its
registers set), for the prime `P` (`w_A` words of `X`'s array `xj`, odd,
above 1) and the cached value at `S` (`R2S`, under the mask of `b`): `r26 &=`
all ones if the value `r2Copy` copies is `R² mod P`, else 0. -/
theorem checkR2_ok {q : Bool} {s : State} {BX S : Addr} {Z oA wA wX xj Pv pL : Nat} {b : Bool}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA)) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hR : R2S q s BX S Z wA pL b) :
    WP isa (checkR2 q xj) s fun t =>
      (t.gpr .r26 = s.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
          (if (if b then wv s.mem S 0 wA else 1) = 2 ^ (128 * wA) % Pv then 1 else 0)) ∧
        Outside BX oA (slot wA 24) s.mem t.mem) ∧ Keep checkR2Regs s t := by
  have hn' := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA2 := e wA 2; have eA3 := e wA 3; have eA5 := e wA 5; have eA6 := e wA 6; have eA7 := e wA 7
  have eA8 := e wA 8; have eA24 := e wA 24
  have eX0 := e wX 0; have eX8 := e wX 8; have sXj := slot_le (w := wX) hxj
  have hsA := hs.sub hA
  have hnA := hsA.nowrap
  unfold checkR2
  -- The prime into array 0.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem) (by
      prun [h10, off_off]) rfl) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have v0 : val32 s₃.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  have hlow : (word s₃.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    rw [← Pre.wv_low_mod2' _ _ _ (show 1 ≤ wA by omega_arith), ← Pre.val32_eq_wv, v0, hPodd]
  -- `-p⁻¹ mod 2³²` and the bases.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hsA.congr k13.wr) ((k13.gpr _ (by decide)).trans h10) (by omega_arith) hlow)
    fun s₄ ⟨⟨i12, iinv, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 1) fun s₅ ⟨⟨a5, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 2) fun s₆ ⟨⟨a8, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h10)
    ((k16.gpr _ (by decide)).trans h29) 3) fun s₇ ⟨⟨a9, m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  have hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  have g12 : s₇.gpr .r12 = s₄.gpr .r12 := by
    rw [k7.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide)]
  -- The cached value into array 1.
  have hsepB : ∀ x, ofs S x < 8 * wA → slot wA 24 ≤ ofs (off BX oA) x := fun x hx => by
    have := hR.sep x hx
    rcases ofs_rebase BX x (o := oA) (by omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega_arith
  have R7 : R2S q s₇ BX S Z wA pL b :=
    { src := by rw [hm7, out3.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith)]; exact hR.src
      pl := fun hq => by
        rw [hm7, out3.word (Or.inl (by unfold oPLen; omega_arith)) (by unfold oPLen; omega_arith)]; exact hR.pl hq
      pl1 := hR.pl1, pl2 := hR.pl2, hS := hR.hS
      rd := fun i hi => by rw [k17.rd, k17.wr]; exact hR.rd i hi
      sep := hR.sep
      r26 := (k17.gpr _ (by decide)).trans hR.r26 }
  have hxv : wv s₇.mem S 0 wA = wv s.mem S 0 wA := by
    rw [hm7]; exact wv_congr2 fun i hi => Pub.Outside.word_apart (out3.mono (o' := oA) (n' := slot wA 24) (by omega_arith)
      (by omega_arith)) hR.sep hA (by omega_arith) hR.hS
  unfold r2Step
  refine WP.seq (WP.seq (WP.mono (r2Src_ok (hs.congr k17.wr) (by omega_arith) ((k17.gpr _ (by decide)).trans h23)
    R7.pl R7.pl1 R7.pl2) fun s₈ ⟨⟨b15, m8⟩, k8⟩ => ?_))
  rw [← R7.src] at b15
  have k18 := k17.trans k8
  refine WP.mono (r2Copy_ok (b := b) (hsA.congr k18.wr) hR.hS (fun i hi => by rw [k18.rd, k18.wr]; exact hR.rd i hi)
    hsepB (by rw [b15]; simp [off]) ((k18.gpr _ (by decide)).trans h10) ((k18.gpr _ (by decide)).trans h29)
    ((k18.gpr _ (by decide)).trans h11) ((k8.gpr _ (by decide)).trans R7.r26) (by omega_arith) hw'
    (by omega_arith)) fun s₉ ⟨⟨x1, out9⟩, k9⟩ => ?_
  have k19 := k18.trans k9
  rw [m8, hxv] at x1
  rw [m8, hm7] at out9
  -- What `r2Copy` kept: array 0.
  have o9 : Mont.Outside (off BX oA) (slot wA 1) (8 * wA) s₃.mem s₉.mem := fun x hx => out9 x hx
  have v0₉ : val32 s₉.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [o9.val32 (Or.inl (by omega_arith)) (by omega_arith), v0]
  have w0₉ : w32 s₉.mem (off BX oA) (slot wA 0) = w32 s₃.mem (off BX oA) (slot wA 0) :=
    o9.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have x1' : val32 s₉.mem (off BX oA) (slot wA 1) (2 * wA) = (if b then wv s.mem S 0 wA else 1) := by
    rw [Pre.val32_eq_wv, x1]
  -- 1 into array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok (hsA.congr k19.wr) (by omega_arith) hw' (by omega_arith)
    ((k19.gpr _ (by decide)).trans h10) ((k19.gpr _ (by decide)).trans h29) ((k19.gpr _ (by decide)).trans h11))
    fun s₁₀ ⟨⟨e7, out10⟩, k10⟩ => ?_)
  have k110 := k19.trans k10
  have o10 : Mont.Outside (off BX oA) (slot wA 7) (8 * wA) s₉.mem s₁₀.mem := fun x hx => out10 x hx
  have v0₁₀ : val32 s₁₀.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [o10.val32 (Or.inl (by omega_arith)) (by omega_arith), v0₉]
  have w0₁₀ : w32 s₁₀.mem (off BX oA) (slot wA 0) = w32 s₃.mem (off BX oA) (slot wA 0) := by
    rw [o10.w32 (Or.inl (by omega_arith)) (by omega_arith), w0₉]
  have x1₁₀ : val32 s₁₀.mem (off BX oA) (slot wA 1) (2 * wA) = (if b then wv s.mem S 0 wA else 1) := by
    rw [o10.val32 (Or.inl (by omega_arith)) (by omega_arith), x1']
  have g12' : s₁₀.gpr .r12 = s₄.gpr .r12 := by
    rw [k10.gpr .r12 (by decide), k9.gpr .r12 (by decide), k8.gpr .r12 (by decide), g12]
  -- `x R⁻¹` into array 5.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 1) (b := 7) (hsA.congr k110.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((k110.gpr _ (by decide)).trans h10) ((k110.gpr _ (by decide)).trans h29)
    ((k110.gpr _ (by decide)).trans h11) (by rw [g12']; exact i12) (by rw [g12', w0₁₀]; exact iinv)
    (by rw [e7, v0₁₀]; omega_arith)) fun s₁₁ ⟨⟨l5, e5, o11⟩, k11⟩ => ?_)
  have k111 := k110.trans k11
  rw [v0₁₀] at l5 e5
  rw [x1₁₀, e7] at e5
  have sep11 : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 5 → j < 24 → ∀ r ∈ [(slot wA 2, 8 * (wA + 2)), (slot wA 3, 8 * (wA + 2)),
      (slot wA 5, 8 * (wA + 2))], slot wA j + 4 * (2 * wA) ≤ r.1 ∨ r.1 + r.2 ≤ slot wA j := by
    intro j h2 h3 h5 h24 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have s2 := slot_sep (w := wA) h2; have s3 := slot_sep (w := wA) h3; have s5 := slot_sep (w := wA) h5
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have v0₁₁ : val32 s₁₁.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [o11.val32 (sep11 0 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v0₁₀]
  have e7₁₁ : val32 s₁₁.mem (off BX oA) (slot wA 7) (2 * wA) = 1 := by
    rw [o11.val32 (sep11 7 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), e7]
  have x1₁₁ : val32 s₁₁.mem (off BX oA) (slot wA 1) (2 * wA) = (if b then wv s.mem S 0 wA else 1) := by
    rw [o11.val32 (sep11 1 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), x1₁₀]
  have w0₁₁ : w32 s₁₁.mem (off BX oA) (slot wA 0) = w32 s₃.mem (off BX oA) (slot wA 0) := by
    have := o11.val32 (d := slot wA 0) (k := 1) (fun r hr => by
      have := sep11 0 (by decide) (by decide) (by decide) (by decide) r hr; omega_arith) (by omega_arith)
    rw [← w0₁₀]; simpa [val32] using this
  have g12'' : s₁₁.gpr .r12 = s₄.gpr .r12 := by rw [k11.gpr .r12 (by decide), g12']
  -- `x R⁻²` into array 6.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 6) (a := 5) (b := 7) (hsA.congr k111.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((k111.gpr _ (by decide)).trans h10) ((k111.gpr _ (by decide)).trans h29)
    ((k111.gpr _ (by decide)).trans h11) (by rw [g12'']; exact i12) (by rw [g12'', w0₁₁]; exact iinv)
    (by rw [e7₁₁, v0₁₁]; omega_arith)) fun s₁₂ ⟨⟨l6, e6, o12⟩, k12'⟩ => ?_)
  have k112 := k111.trans k12'
  rw [v0₁₁] at l6 e6
  rw [e7₁₁] at e6
  have sep12 : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 6 → j < 24 → ∀ r ∈ [(slot wA 2, 8 * (wA + 2)), (slot wA 3, 8 * (wA + 2)),
      (slot wA 6, 8 * (wA + 2))], slot wA j + 4 * (2 * wA) ≤ r.1 ∨ r.1 + r.2 ≤ slot wA j := by
    intro j h2 h3 h6 h24 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have s2 := slot_sep (w := wA) h2; have s3 := slot_sep (w := wA) h3; have s6 := slot_sep (w := wA) h6
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have v0₁₂ : val32 s₁₂.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [o12.val32 (sep12 0 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v0₁₁]
  have e7₁₂ : val32 s₁₂.mem (off BX oA) (slot wA 7) (2 * wA) = 1 := by
    rw [o12.val32 (sep12 7 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), e7₁₁]
  have x1₁₂ : val32 s₁₂.mem (off BX oA) (slot wA 1) (2 * wA) = (if b then wv s.mem S 0 wA else 1) := by
    rw [o12.val32 (sep12 1 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), x1₁₁]
  -- The top words of arrays 1, 6 and 7 := 0.
  refine WP.seq ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine WP.mono (zeroTop_ok (j := 1) (hsA.congr k112.wr) (by omega_arith) ((k112.gpr _ (by decide)).trans h10)
    ((k112.gpr _ (by decide)).trans h29)) fun u₁ ⟨mu1, ku1⟩ => ?_
  rw [WP.block_append_iff]
  have ku1' := k112.trans ku1
  refine WP.mono (zeroTop_ok (j := 6) (hsA.congr ku1'.wr) (by omega_arith) ((ku1'.gpr _ (by decide)).trans h10)
    ((ku1'.gpr _ (by decide)).trans h29)) fun u₂ ⟨mu2, ku2⟩ => ?_
  have ku2' := ku1'.trans ku2
  refine WP.mono (zeroTop_ok (j := 7) (hsA.congr ku2'.wr) (by omega_arith) ((ku2'.gpr _ (by decide)).trans h10)
    ((ku2'.gpr _ (by decide)).trans h29)) fun u₃ ⟨mu3, ku3⟩ => ?_
  have ku3' := ku2'.trans ku3
  have z1 := writeW_outside s₁₂.mem (off BX oA) (d := slot wA 1 + 8 * wA) (0 : BitVec 64) (by omega_arith)
  have z6 := writeW_outside u₁.mem (off BX oA) (d := slot wA 6 + 8 * wA) (0 : BitVec 64) (by omega_arith)
  have z7 := writeW_outside u₂.mem (off BX oA) (d := slot wA 7 + 8 * wA) (0 : BitVec 64) (by omega_arith)
  rw [← mu1] at z1; rw [← mu2] at z6; rw [← mu3] at z7
  have M1 : Mont.Outside (off BX oA) (slot wA 1 + 8 * wA) 8 s₁₂.mem u₁.mem := fun x hx => z1 x hx
  have M6 : Mont.Outside (off BX oA) (slot wA 6 + 8 * wA) 8 u₁.mem u₂.mem := fun x hx => z6 x hx
  have M7 : Mont.Outside (off BX oA) (slot wA 7 + 8 * wA) 8 u₂.mem u₃.mem := fun x hx => z7 x hx
  have hv : ∀ d, (d + 8 * wA ≤ slot wA 1 + 8 * wA ∨ slot wA 1 + 8 * wA + 8 ≤ d) →
      (d + 8 * wA ≤ slot wA 6 + 8 * wA ∨ slot wA 6 + 8 * wA + 8 ≤ d) →
      (d + 8 * wA ≤ slot wA 7 + 8 * wA ∨ slot wA 7 + 8 * wA + 8 ≤ d) → d + 8 * wA ≤ slot wA 24 →
      val32 u₃.mem (off BX oA) d (2 * wA) = val32 s₁₂.mem (off BX oA) d (2 * wA) := fun d d1 d6 d7 hd => by
    rw [M7.val32 (by omega_arith) (by omega_arith), M6.val32 (by omega_arith) (by omega_arith),
      M1.val32 (by omega_arith) (by omega_arith)]
  have v0₃ := (hv (slot wA 0) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)).trans v0₁₂
  have x1₃ := (hv (slot wA 1) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)).trans x1₁₂
  have e7₃ := (hv (slot wA 7) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)).trans e7₁₂
  have v6₃ := hv (slot wA 6) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
  have t1 : word u₃.mem (off BX oA) (slot wA 1 + 8 * wA) = 0 := by
    rw [z7.word (by omega_arith) (by omega_arith), z6.word (by omega_arith) (by omega_arith), mu1]
    exact word_writeW_self _ _ _ _
  have t6 : word u₃.mem (off BX oA) (slot wA 6 + 8 * wA) = 0 := by
    rw [z7.word (by omega_arith) (by omega_arith), mu2]; exact word_writeW_self _ _ _ _
  have t7 : word u₃.mem (off BX oA) (slot wA 7 + 8 * wA) = 0 := by rw [mu3]; exact word_writeW_self _ _ _ _
  have r26₃ : u₃.gpr .r26 = s.gpr .r26 := ku3'.gpr _ (by decide)
  -- `x < p`.
  refine WP.seq (WP.mono (checkLt_ok (a := 1) (m := 0) (hsA.congr ku3'.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' (by omega_arith) ((ku3'.gpr _ (by decide)).trans h10)
    ((ku3'.gpr _ (by decide)).trans h21) ((ku3'.gpr _ (by decide)).trans h29)
    ((ku3'.gpr _ (by decide)).trans h11) t1) fun w₁ ⟨⟨c26, co1, c10⟩, kc1⟩ => ?_)
  rw [x1₃, v0₃, r26₃] at c26
  have kw1 := ku3'.trans kc1
  -- `x R⁻² < 1`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 6) (m := 7) (hsA.congr kw1.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' (by omega_arith) c10 ((kw1.gpr _ (by decide)).trans h21)
    ((kw1.gpr _ (by decide)).trans h29) ((kw1.gpr _ (by decide)).trans h11)
    (by rw [(show Outside (off BX oA) (slot wA 3) (8 * wA) u₃.mem w₁.mem from fun x hx => co1 x hx).word
      (Or.inr (by omega_arith)) (by omega_arith)]; exact t6)) fun w₂ ⟨⟨a20, co2, a10⟩, kc2⟩ => ?_)
  rw [co1.val32 (Or.inr (by omega_arith)) (by omega_arith), co1.val32 (Or.inr (by omega_arith)) (by omega_arith),
    v6₃, e7₃] at a20
  refine WP.seq (WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = w₂.gpr .r20 ∧ t.mem = w₂.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun w₃ ⟨⟨a24, m3'⟩, k3'⟩ => ?_)
  have kw3 := (kw1.trans kc2).trans k3'
  -- `1 < x R⁻²`?
  refine WP.seq (WP.mono (cmpLt_ok (a := 7) (m := 6) (hsA.congr kw3.wr) (by decide) (by decide) (by decide)
    (by decide) (by omega_arith) hw' (by omega_arith) (by rw [k3'.gpr .r10 (by decide)]; exact a10)
    ((kw3.gpr _ (by decide)).trans h21) ((kw3.gpr _ (by decide)).trans h29) ((kw3.gpr _ (by decide)).trans h11)
    (by rw [m3', (show Outside (off BX oA) (slot wA 3) (8 * wA) w₁.mem w₂.mem from fun x hx => co2 x hx).word
      (Or.inr (by omega_arith)) (by omega_arith),
      (show Outside (off BX oA) (slot wA 3) (8 * wA) u₃.mem w₁.mem from fun x hx => co1 x hx).word
      (Or.inr (by omega_arith)) (by omega_arith)]; exact t7)) fun w₄ ⟨⟨b20, co4, b10⟩, kc4⟩ => ?_)
  rw [m3', co2.val32 (Or.inr (by omega_arith)) (by omega_arith), co2.val32 (Or.inr (by omega_arith)) (by omega_arith),
    co1.val32 (Or.inr (by omega_arith)) (by omega_arith), co1.val32 (Or.inr (by omega_arith)) (by omega_arith),
    v6₃, e7₃] at b20
  refine WP.mono (WP.keep [.r0, .r3, .r26] (Q := fun t => t.gpr .r26 = w₄.gpr .r26 &&&
    ((w₄.gpr .r24 ||| w₄.gpr .r20) ^^^ (BitVec.ofNat 64 0 - 1#64)) ∧ t.mem = w₄.mem) (by prun) (by decide))
    fun t ⟨⟨t26, tm⟩, k5'⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · have hiff := r2_check (N := Pv) (k := 64 * wA) hP2 hPodd e5 l6 e6
    rw [show 2 * (64 * wA) = 128 * wA by omega_arith] at hiff
    rw [t26, b20, kc4.gpr .r24 (by decide), a24, a20, eq_masks, kc4.gpr .r26 (by decide), k3'.gpr .r26 (by decide),
      kc2.gpr .r26 (by decide), c26, and_masks]
    simp only [hiff]
  · have cv : ∀ {d n : Nat} {m m' : Mem}, d + n ≤ slot wA 24 → Mont.Outside (off BX oA) d n m m' →
        Mont.Outside (off BX oA) 0 (slot wA 24) m m' := fun hd o x hx => o x (by
      rcases hx with h | h
      · omega_arith
      · exact Or.inr (by omega_arith))
    have cvs : ∀ {rs : List (Nat × Nat)} {m m' : Mem}, (∀ r ∈ rs, r.1 + r.2 ≤ slot wA 24) →
        Mont.Outs (off BX oA) rs m m' → Mont.Outside (off BX oA) 0 (slot wA 24) m m' := fun hr o x hx =>
      o x fun r hr' => Or.inr (by
        have := hr r hr'
        rcases hx with h | h
        · omega_arith
        · omega_arith)
    have b3 : ∀ j, j < 8 → ∀ r ∈ [(slot wA 2, 8 * (wA + 2)), (slot wA 3, 8 * (wA + 2)),
        (slot wA j, 8 * (wA + 2))], r.1 + r.2 ≤ slot wA 24 := by
      intro j hj r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have := slot_le (w := wA) hj
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
    have acc : Mont.Outside (off BX oA) 0 (slot wA 24) s₃.mem t.mem :=
      ((((((((((cv (by omega_arith) o9).trans (cv (by omega_arith) o10)).trans
        (cvs (b3 5 (by decide)) o11)).trans (cvs (b3 6 (by decide)) o12)).trans (cv (by omega_arith) M1)).trans
        (cv (by omega_arith) M6)).trans (cv (by omega_arith) M7)).trans (cv (by omega_arith) co1)).trans
        (cv (by omega_arith) co2)).trans (by have := cv (by omega_arith) co4; rwa [m3'] at this)).trans
        (by rw [tm]; exact Mont.Outside.refl _ _ _ _)
    exact (out3.mono (o' := oA) (n' := slot wA 24) (by omega_arith) (by omega_arith)).trans
      (out_sub (fun y hy => acc y hy) (by omega_arith) (by omega_arith) (by omega_arith))
  · exact ((kw3.trans kc4).trans k5').mono (by decide)
