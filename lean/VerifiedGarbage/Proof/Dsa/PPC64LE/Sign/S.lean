module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Add
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyProd
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on PPC64LE: `s = w (z + x r) mod q`

* `tail28_ok`, `montOp28_ok`, `mont28_ok`: `MontCore.lean`'s `tail_ok` and
  `PubMont.lean`'s `montOp_ok` for any of the 28 arrays a working space of
  `slot w 28` octets holds (those take arrays below 8), as `sValue` multiplies
  by r in array 9;
* `sValue_ok`: in the Q space, with q in array 0, w in array 4, `R² mod q` in
  array 8 and r in array 9, `w (z + x r) mod q` into array 6 (z the digest's
  scalar, x the key's last `q_len` octets).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot slot_sep hdr_lt_slot)

/-! ## Montgomery multiplications of any array -/

/-- `tail_ok` for arrays below 28, in a working space holding them. -/
theorem tail28_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 28) (ha : a < 28) (hb : b < 28) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 28 ≤ Z)
    (i5 : s.gpr .r5 = off B (slot w o)) (i6 : s.gpr .r6 = off B (slot w a))
    (i7 : s.gpr .r7 = off B (slot w b)) (i8 : s.gpr .r8 = off B (slot w 2))
    (i9 : s.gpr .r9 = off B (slot w 3)) (i10 : s.gpr .r10 = off B (slot w 0))
    (i11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (i4 : s.gpr .r4 = BitVec.ofNat 64 (2 * w))
    (i12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa tail s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep tailRegs s t := by
  have hnw := hs.nowrap
  have sl : ∀ j < 28, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hdr56 : 56 + 4 ≤ slot w 2 := by have := hdr_lt_slot w 2 (i := 7) (by decide); omega_arith
  have s0 := sl 0 (by decide)
  have s2 := sl 2 (by decide)
  have s3 := sl 3 (by decide)
  have sa := sl a ha
  have sb := sl b hb
  have so := sl o ho
  have p20 := sp (show (2 : Nat) ≠ 0 by decide)
  have p23 := sp (show (2 : Nat) ≠ 3 by decide)
  have p30 := sp (show (3 : Nat) ≠ 0 by decide)
  have p2a := sp (Ne.symm ha2)
  have p2b := sp (Ne.symm hb2)
  have p2o := sp (Ne.symm ho2)
  have p3o := sp (Ne.symm ho3)
  unfold tail
  -- The accumulator := 0.
  refine WP.seq (WP.mono (zeroAcc_ok hs i8 i11 hw' (by omega_arith)) fun s₂ ⟨hz, out₂, k₂⟩ => ?_)
  have hs₂ := hs.congr k₂.wr
  have g₂ : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], s₂.gpr r = s.gpr r := fun r hr =>
    k₂.gpr r (by revert r hr; decide)
  have v₂ : ∀ {j}, j < 28 → j ≠ 2 → val32 s₂.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj hne => out₂.val32 (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)
  have w0₂ : w32 s₂.mem B (slot w 0) = w32 s.mem B (slot w 0) := out₂.w32 (by omega_arith) (by omega_arith)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok (n := 2 * w) (da := slot w a) (dA := slot w 2) (dB := slot w b)
    (dM := slot w 0) hs₂ (by rw [g₂ .r6 (by decide), i6])
    (by rw [g₂ .r8 (by decide), i8]) (by rw [g₂ .r7 (by decide), i7]) (by rw [g₂ .r10 (by decide), i10])
    (by rw [g₂ .r11 (by decide), i11]) (by rw [g₂ .r4 (by decide), i4])
    (by rw [g₂ .r12 (by decide)]; exact i12)
    (by rw [g₂ .r12 (by decide), w0₂]; exact hinv) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (val32_zero fun j hj => hz j (by omega_arith))
    (by rw [v₂ hb hb2, v₂ (by decide) (by decide)]; exact hB))
    fun s₃ ⟨⟨tlt, teq, out₃⟩, k₃⟩ => ?_)
  rw [v₂ (by decide) (by decide)] at tlt teq
  rw [v₂ ha ha2, v₂ hb hb2] at teq
  have hs₃ := hs₂.congr k₃.wr
  have g₃ : ∀ r ∈ [Reg.r5, .r8, .r9, .r10, .r11], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr r (by revert r hr; decide), g₂ r (by revert r hr; decide)]
  have v₃ : ∀ {j}, j < 28 → j ≠ 2 → val32 s₃.mem B (slot w j) (2 * w) = val32 s.mem B (slot w j) (2 * w) :=
    fun hj hne => (out₃.val32 (by have := sp hne; omega_arith) (by have := sl _ hj; omega_arith)).trans (v₂ hj hne)
  -- `T - m`.
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dM := slot w 0) hs₃
    (by rw [g₃ .r8 (by decide), i8])
    (by rw [g₃ .r9 (by decide), i9]) (by rw [g₃ .r10 (by decide), i10]) (by rw [g₃ .r11 (by decide), i11])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith))
    fun s₄ ⟨⟨c, hc, hD, h20⟩, out₄, k₄⟩ => ?_)
  rw [v₃ (by decide) (by decide)] at hD
  have hs₄ := hs₃.congr k₄.wr
  have g₄ : ∀ r ∈ [Reg.r5, .r8, .r9, .r11], s₄.gpr r = s.gpr r := fun r hr => by
    rw [k₄.gpr r (by revert r hr; decide), g₃ r (by revert r hr; decide)]
  have accA : val32 s₄.mem B (slot w 2) (2 * w) = val32 s₃.mem B (slot w 2) (2 * w) :=
    out₄.val32 (by omega_arith) (by omega_arith)
  -- The selection.
  refine WP.mono (selectAcc_ok (n := 2 * w) (dA := slot w 2) (dT := slot w 3) (dO := slot w o)
    (b := decide (w32 s₃.mem B (slot w 2 + 4 * (2 * w)) < c)) hs₄
    (by rw [g₄ .r8 (by decide), i8]) (by rw [g₄ .r9 (by decide), i9]) (by rw [g₄ .r5 (by decide), i5])
    (by rw [g₄ .r11 (by decide), i11]) (by rw [h20]; simp only [decide_eq_true_eq])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith))
    fun t ⟨hv, out₅, k₅⟩ => ?_
  rw [accA] at hv
  have hM := val32_lt s.mem B (slot w 0) (2 * w)
  have hM0 : 0 < val32 s.mem B (slot w 0) (2 * w) := by omega_arith
  have pw : 2 ^ (32 * (2 * w)) = 2 ^ (64 * w) := by rw [← Nat.mul_assoc]
  rw [val32_succ] at tlt teq
  have hres : val32 t.mem B (slot w o) (2 * w) =
      (val32 s₃.mem B (slot w 2) (2 * w) + 2 ^ (32 * (2 * w)) * (w32 s₃.mem B (slot w 2 + 4 * (2 * w)) +
        2 ^ 64 * 0)) % val32 s.mem B (slot w 0) (2 * w) := by
    rw [hv, ← VG.Proof.Bignum.csub_result hM (val32_lt _ _ _ _) hc (val32_lt _ _ _ _) (by omega_arith) hD]
    by_cases h : w32 s₃.mem B (slot w 2 + 4 * (2 * w)) < c <;> simp [h]
  rw [Nat.mul_zero, Nat.add_zero] at hres
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hres]; exact Nat.mod_lt _ hM0
  · rw [hres, ← pw, Nat.mod_mul_mod, Nat.mul_comm, teq]
  · refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₂.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 2) (n := 8 * (w + 2))
      (out₃.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    refine Outs.trans (Outs.of_outside (o := slot w 3) (n := 8 * (w + 2))
      (out₄.mono (Nat.le_refl _) (by omega_arith)) (by simp)) ?_
    exact Outs.of_outside (o := slot w o) (n := 8 * (w + 2)) (out₅.mono (Nat.le_refl _) (by omega_arith)) (by simp)
  · exact (((k₂.trans k₃).trans k₄).trans k₅).mono

/-- `Pub.montOp_ok` for arrays below 28, in a working space holding them. -/
theorem montOp28_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    {o a b : Nat} (ho : o < 28) (ha : a < 28) (hb : b < 28) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2)
    (hb2 : b ≠ 2) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 28 ≤ Z)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w b) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (val32 t.mem B (slot w o) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w o) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w a) (2 * w) * val32 s.mem B (slot w b) (2 * w) %
            val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w o, 8 * (w + 2))] s.mem t.mem) ∧
      Keep Pub.montRegs s t := by
  unfold PublicChecked.montOp
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) h10 h29 o) fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r6) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h10)
    ((k1.gpr _ (by decide)).trans h29) a) fun t₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r7) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) b) fun t₃ ⟨⟨a7, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 2) fun t₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 3) fun t₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ t.mem = t₅.mem)
    (by prun [(k15.gpr .r11 (by decide)).trans h11, BitVec.add_zero]) (by decide)) fun t₆ ⟨⟨a4, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  have hm : t₆.mem = s.mem := by rw [m6, m5, m4, m3, m2, m1]
  have g : ∀ r ∈ [Reg.r10, .r11, .r12], t₆.gpr r = s.gpr r := fun r hr => k16.gpr r (by revert r hr; decide)
  have g5 : t₆.gpr .r5 = off B (slot w o) := by rw [k6.gpr .r5 (by decide), k5.gpr .r5 (by decide),
    k4.gpr .r5 (by decide), k3.gpr .r5 (by decide), k2.gpr .r5 (by decide), a5]
  have g6 : t₆.gpr .r6 = off B (slot w a) := by rw [k6.gpr .r6 (by decide), k5.gpr .r6 (by decide),
    k4.gpr .r6 (by decide), k3.gpr .r6 (by decide), a6]
  have g7 : t₆.gpr .r7 = off B (slot w b) := by rw [k6.gpr .r7 (by decide), k5.gpr .r7 (by decide),
    k4.gpr .r7 (by decide), a7]
  have g8 : t₆.gpr .r8 = off B (slot w 2) := by rw [k6.gpr .r8 (by decide), k5.gpr .r8 (by decide), a8]
  have g9 : t₆.gpr .r9 = off B (slot w 3) := by rw [k6.gpr .r9 (by decide), a9]
  rw [← hm] at hinv hB ⊢
  refine WP.mono (tail28_ok (hs.congr k16.wr) ho ha hb ho2 ho3 ha2 hb2 hw2 hw' hZ g5 g6 g7 g8 g9
    ((g _ (by decide)).trans h10) ((g _ (by decide)).trans h11) a4 (by rw [g _ (by decide)]; exact h12)
    (by rw [g _ (by decide)]; exact hinv) hB) fun t ⟨h, k⟩ => ⟨h, (k16.trans k).mono (by decide)⟩

/-- `montOp o a b` for `o` among 5 and 6 and any arrays `a` and `b`, `[b] < c`. -/
theorem mont28_ok {s : State} {B : Addr} {Z w : Nat} (h : MCtx s B Z w) {o a b : Nat}
    (ho : o = 5 ∨ o = 6) (ha : a < 28) (ha2 : a ≠ 2) (hb : b < 28) (hb2 : b ≠ 2)
    (hB : arr s.mem B w b < arr s.mem B w 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < arr s.mem B w 0 ∧
        arr t.mem B w o * 2 ^ (64 * w) % arr s.mem B w 0 = arr s.mem B w a * arr s.mem B w b % arr s.mem B w 0 ∧
        Outs B (montRanges w o) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep Pub.montRegs s t := by
  have hw := h.hw
  have hw' := h.hw'
  have h8 := slot_lt (w := w) (show 8 < 28 by decide)
  refine WP.mono (montOp28_ok h.hs (by omega) ha hb (by omega) (by omega) ha2 hb2
    (by omega) (by omega) h.hZ h.h10 h.h29 h.h11 h.h12 h.inv hB) fun t ⟨⟨hlt, heq, hout⟩, k⟩ =>
    ⟨⟨hlt, heq, hout, ?_⟩, k⟩
  refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => hout _ fun r hr => ?_)
  have := h.hs.nowrap
  have h0 := slot_lt (w := w) (show 0 < 28 by decide)
  have hZ := h.hZ
  rw [ofs_off B (by omega)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega

/-! ## The arrays a step keeps -/

/-- The Q space's arrays but those in `ws` are kept. -/
def AKeep (L : Lay) (ws : List Nat) (m m' : Mem) : Prop :=
  ∀ j, j < 28 → j ∉ ws → arrQ m' L j = arrQ m L j

theorem AKeep.get {L : Lay} {ws : List Nat} {m m' : Mem} (h : AKeep L ws m m') (j : Nat)
    (hj : j < 28 := by decide) (hn : j ∉ ws := by decide) : arr m' L.Q 4 j = arr m L.Q 4 j :=
  h j hj hn

theorem AKeep.trans {L : Lay} {ws ws' : List Nat} {m₁ m₂ m₃ : Mem} (h₁ : AKeep L ws m₁ m₂)
    (h₂ : AKeep L ws' m₂ m₃) : AKeep L (ws ++ ws') m₁ m₃ := fun j hj hn =>
  (h₂ j hj fun h => hn (List.mem_append_right _ h)).trans (h₁ j hj fun h => hn (List.mem_append_left _ h))

theorem AKeep.of_eq {L : Lay} {m m' : Mem} (h : m' = m) : AKeep L [] m m' := fun _ _ _ => by rw [h]

theorem AKeep.one {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.Q (slot 4 o) n m m') (hn : n ≤ 48) :
    AKeep L [o] m m' := fun j hj ho =>
  Outside.arrEq (h.mono (Nat.le_refl _) (by omega)) hj (by simpa only [List.mem_singleton] using ho) (by decide)

theorem AKeep.red {L : Lay} {m m' : Mem} (h : Outside L.Q (slot 4 1) (24 * (4 + 2)) m m') :
    AKeep L [1, 2, 3] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outside.val32 h (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)

theorem AKeep.add {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (hnw : L.Q.toNat + 1600 ≤ 2 ^ 64)
    (ho : o < 28) : AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact h.arr_eq (Z := 1600) (by decide) hnw hj hn.1 hn.2.1 hn.2.2 ho

theorem AKeep.mont {L : Lay} {o : Nat} {m m' : Mem} (h : Outs L.Q (montRanges 4 o) m m') :
    AKeep L [2, 3, o] m m' := fun j hj hn => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  exact Outs.arrEq_mont h hj hn.1 hn.2.1 hn.2.2 (by decide)

theorem AddFrame.qarr {L : Lay} {o : Nat} {m m' : Mem} (h : AddFrame L.Q 4 o m m') (ho1 : 1 ≤ o) (ho : o < 28) :
    QArr L m m' := by
  obtain ⟨m₁, h₁, h₂⟩ := h
  exact (QArr.of h₁ (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)).trans
    (QArr.of h₂ (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))

/-! ## s -/

/-- The registers `sValue` writes. -/
def sValueRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25,
    .r30]

/-- `sValueRegs`, and `r10` and `r31`, which `sValue` restores. -/
def sValueAll : List Reg := .r10 :: .r31 :: sValueRegs

/-- `sValue`: in the Q space, `w (z + x r) mod q` into array 6. -/
theorem sValue_ok {s : State} {L : Lay} {key nonce dig : Addr} {qb d : Nat} (h : QS s L key nonce dig)
    (hL : L.Ok) (h2 : s.gpr .r2 = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb)) (hk : Src s L key (3 * L.pl + 2 * L.ql))
    (hq3 : 3 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h8 : arrQ s.mem L 8 = 2 ^ (128 * 4) % arrQ s.mem L 0)
    (h4 : arrQ s.mem L 4 < arrQ s.mem L 0) (h9 : arrQ s.mem L 9 < arrQ s.mem L 0)
    (hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) < 2 * arrQ s.mem L 0) :
    WP isa sValue s fun t =>
      (QS t L key nonce dig ∧
        arrQ t.mem L 6 = arrQ s.mem L 4 * ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) %
          arrQ s.mem L 0 + xOf s.mem L key * arrQ s.mem L 9 % arrQ s.mem L 0) % arrQ s.mem L 0) %
            arrQ s.mem L 0 ∧
        arrQ t.mem L 9 = arrQ s.mem L 9 ∧ QArr L s.mem t.mem) ∧ Keep sValueRegs s t := by
  have hql := hL.ql
  have hcop : Nat.Coprime (2 ^ (64 * 4)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  have hRR := pow_sq_eq 4
  generalize (2 : Nat) ^ (128 * 4) = R2 at h8 hRR
  have hnw : L.Q.toNat + 1600 ≤ 2 ^ 64 := h.inq.env.hs.nowrap
  unfold sValue
  -- z into array 6, 0 into array 7, `z mod q` into array 6.
  refine WP.seq (WP.mono (prod_scalar_ok h hL h2 hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) = z at v6 hz ⊢
  have f1 : AKeep L [6] s.mem s₁.mem := AKeep.one o1 (by omega)
  have qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (by decide)
  have f2 : AKeep L [7] s₁.mem s₂.mem := AKeep.one o2 (by omega)
  have qa2 : QArr L s₁.mem s₂.mem := QArr.of o2 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have q2 : arr s₂.mem L.Q 4 0 = arrQ s.mem L 0 := (qa1.trans qa2).arr0
  have z2 : arr s₂.mem L.Q 4 6 = z := (f2.get 6).trans v6
  refine WP.seq (WP.mono (addMod_ok Q2.inq.env (o := 6) (a := 6) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [z2, z7, q2]; omega)) fun s₃ ⟨⟨a6, fr3⟩, k3⟩ => ?_)
  rw [z2, z7, q2, Nat.add_zero] at a6
  have Q3 := Q2.step k3 (by decide)
  have f3 := AKeep.add fr3 hnw (by decide)
  have qa13 : QArr L s.mem s₃.mem := (qa1.trans qa2).trans (AddFrame.qarr fr3 (by decide) (by decide))
  have q3 : arr s₃.mem L.Q 4 0 = arrQ s.mem L 0 := qa13.arr0
  have k13 := (k1.trans k2).trans k3
  -- x's octets, and `x mod q` into array 1.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ptrX_ok Q3.regs) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = off key (3 * L.pl + L.ql) ∧
      u.gpr .r31 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by prun [b12, b6, BitVec.add_zero]) (by decide))
    fun s₅ ⟨⟨c30, c31, m5⟩, k5⟩ => ?_
  have k35 := k4.trans k5
  have e3 := Q3.inq.env
  have hx := (hk.keep (k13.trans k35).rd (k13.trans k35).wr).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := off key (3 * L.pl + L.ql))
    (L := L.ql) (e3.hs.congr k35.wr) (by decide) (by decide) (by decide)
    ((k35.gpr .r10 (by decide)).trans e3.h10) ((k35.gpr .r29 (by decide)).trans e3.h29)
    ((k35.gpr .r11 (by decide)).trans e3.h11)
    (by rw [m5, m4]; show 0 < arr s₃.mem L.Q 4 0; rw [q3]; omega)
    (by rw [c30]; exact (BitVec.add_zero _).symm) c31 (by omega) (by omega) hx.rd (hx.sepQ hL))
    fun s₆ ⟨⟨v1, o6⟩, k6⟩ => ?_)
  have x6 : arr s₆.mem L.Q 4 1 = xOf s.mem L key % arrQ s.mem L 0 := by
    refine v1.trans ?_
    rw [m5, m4, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes (qa13.qbody.body hL) hL.z256]
    show _ % arr s₃.mem L.Q 4 0 = _
    rw [q3]
    rfl
  have f6 := AKeep.red o6
  have qa6 : QArr L s₅.mem s₆.mem := QArr.of o6 (Nat.le_refl _) (by simp only [slot_eq]; omega)
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₆.mem)
      (by prun [((k35.trans k6).gpr .r23 (by decide)).trans Q3.inq.h23, BitVec.add_zero]) (by decide))
    fun s₇ ⟨⟨a31, m7⟩, k7⟩ => ?_)
  have k37 := (k35.trans k6).trans k7
  have Q7 : QS s₇ L key nonce dig := ⟨⟨⟨e3.hs.congr k37.wr, (k37.gpr .r10 (by decide)).trans e3.h10,
    (k37.gpr .r29 (by decide)).trans e3.h29, (k37.gpr .r11 (by decide)).trans e3.h11, a31, e3.hw, e3.hw', e3.hZ⟩,
    (k37.gpr .r21 (by decide)).trans Q3.inq.h21, (k37.gpr .r23 (by decide)).trans Q3.inq.h23⟩,
    Q3.scr.congr k37.wr, Q3.regs.keep k37⟩
  -- `x mod q` into array 5, `R² mod q` into array 1, `-q⁻¹`.
  refine WP.seq (WP.mono (copy_ok Q7.inq.env (o := 5) (a := 1) (by decide) (by decide) (by decide))
    fun s₈ ⟨⟨v5, o8⟩, k8⟩ => ?_)
  rw [m7, x6] at v5
  have Q8 := Q7.step k8 (by decide)
  have f8 : AKeep L [5] s₇.mem s₈.mem := AKeep.one o8 (by omega)
  refine WP.seq (WP.mono (copy_ok Q8.inq.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₉ ⟨⟨v1', o9⟩, k9⟩ => ?_)
  have Q9 := Q8.step k9 (by decide)
  have f9 : AKeep L [1] s₈.mem s₉.mem := AKeep.one o9 (by omega)
  have F38 := ((AKeep.of_eq (L := L) (m5.trans m4)).trans f6).trans ((AKeep.of_eq m7).trans f8)
  have F08 := ((f1.trans f2).trans f3).trans F38
  have qa35 : QArr L s₃.mem s₅.mem := by rw [m5, m4]; exact QArr.refl _ _
  have qa68 : QArr L s₆.mem s₈.mem := by
    rw [← m7]; exact QArr.of o8 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have qa9 : QArr L s.mem s₉.mem := (((qa13.trans qa35).trans qa6).trans qa68).trans
    (QArr.of o9 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have q9 : arr s₉.mem L.Q 4 0 = arrQ s.mem L 0 := qa9.arr0
  have hodd : (word s₉.mem L.Q (slot 4 0)).toNat % 2 = 1 :=
    word_odd _ _ _ (2 * 4) (by decide) (by show arr s₉.mem L.Q 4 0 % 2 = 1; rw [q9]; exact hqo)
  refine WP.seq (WP.mono (Pub.minv_ok Q9.inq.env.hs Q9.inq.env.h10 (by decide) hodd)
    fun s₁₀ ⟨⟨i12, inv, m10⟩, k10⟩ => ?_)
  have M10 : MCtx s₁₀ L.Q 1600 4 := ⟨Q9.inq.env.keep k10 (by decide), i12, by rw [m10]; exact inv⟩
  have Q10 := Q9.step k10 (by decide)
  have F010 := (F08.trans f9).trans (AKeep.of_eq (L := L) m10)
  have A0 : arr s₁₀.mem L.Q 4 0 = arrQ s.mem L 0 := by rw [m10]; exact q9
  have A1 : arr s₁₀.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := by rw [m10, v1', F08.get 8]; exact h8
  have A4 : arr s₁₀.mem L.Q 4 4 = arrQ s.mem L 4 := F010.get 4
  have A5 : arr s₁₀.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 := by rw [m10, f9.get 5]; exact v5
  have A6 : arr s₁₀.mem L.Q 4 6 = z % arrQ s.mem L 0 :=
    ((F38.trans f9).trans (AKeep.of_eq (L := L) m10)).get 6 |>.trans a6
  have A9 : arr s₁₀.mem L.Q 4 9 = arrQ s.mem L 9 := F010.get 9
  -- `x r mod q` into array 5.
  refine WP.seq (WP.mono (mont28_ok M10 (o := 5) (a := 5) (b := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A9, A0]; exact h9)) fun s₁₁ ⟨⟨_, e11, o11, w11⟩, k11⟩ => ?_)
  have M11 := M10.keep k11 (by decide) w11
  have Q11 := Q10.step k11 (by decide)
  rw [A0, A5, A9] at e11
  have f11 := AKeep.mont o11
  have B0 : arr s₁₁.mem L.Q 4 0 = arrQ s.mem L 0 := (f11.get 0).trans A0
  have B1 : arr s₁₁.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f11.get 1).trans A1
  refine WP.seq (WP.mono (mont28_ok M11 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega))) fun s₁₂ ⟨⟨l12, e12, o12, w12⟩, k12⟩ => ?_)
  have M12 := M11.keep k12 (by decide) w12
  have Q12 := Q11.step k12 (by decide)
  rw [B0] at l12
  rw [B0, B1] at e12
  have X12 : arr s₁₂.mem L.Q 4 5 = xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9 % arrQ s.mem L 0 :=
    prod_mont_back hcop l12 e11 (by rw [e12, hRR])
  have f12 := AKeep.mont o12
  have F1012 := f11.trans f12
  have C0 : arr s₁₂.mem L.Q 4 0 = arrQ s.mem L 0 := (F1012.get 0).trans A0
  have C6 : arr s₁₂.mem L.Q 4 6 = z % arrQ s.mem L 0 := (F1012.get 6).trans A6
  -- `z + x r mod q` into array 6.
  have l1 := Nat.mod_lt z (show 0 < arrQ s.mem L 0 by omega)
  have l2 := Nat.mod_lt (xOf s.mem L key % arrQ s.mem L 0 * arrQ s.mem L 9) (show 0 < arrQ s.mem L 0 by omega)
  refine WP.seq (WP.mono (addMod_ok M12.toEnv (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [C6, X12, C0]; omega)) fun s₁₃ ⟨⟨a13, fr13⟩, k13'⟩ => ?_)
  rw [C6, X12, C0, Nat.mod_mul_mod] at a13
  have qa13' := AddFrame.qarr fr13 (by decide) (by decide)
  have M13 := M12.keep k13' (by decide)
    (Outside.w32 qa13' (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega))
  have Q13 := Q12.step k13' (by decide)
  have f13 := AKeep.add fr13 hnw (by decide)
  have F1013 := F1012.trans f13
  have D0 : arr s₁₃.mem L.Q 4 0 = arrQ s.mem L 0 := (F1013.get 0).trans A0
  have D1 : arr s₁₃.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (F1013.get 1).trans A1
  have D4 : arr s₁₃.mem L.Q 4 4 = arrQ s.mem L 4 := (F1013.get 4).trans A4
  -- `w (z + x r) mod q` into array 6.
  refine WP.seq (WP.mono (mont28_ok M13 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D4, D0]; exact h4)) fun s₁₄ ⟨⟨_, e14, o14, w14⟩, k14⟩ => ?_)
  have M14 := M13.keep k14 (by decide) w14
  have Q14 := Q13.step k14 (by decide)
  rw [D0, a13, D4] at e14
  have f14 := AKeep.mont o14
  have E0 : arr s₁₄.mem L.Q 4 0 = arrQ s.mem L 0 := (f14.get 0).trans D0
  have E1 : arr s₁₄.mem L.Q 4 1 = R2 % arrQ s.mem L 0 := (f14.get 1).trans D1
  refine WP.mono (mont28_ok M14 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [E1, E0]; exact Nat.mod_lt _ (by omega))) fun t ⟨⟨lt, et, ot, _⟩, kt⟩ => ?_
  rw [E0] at lt
  rw [E0, E1] at et
  have ft := AKeep.mont ot
  have Ft := (((F010.trans F1013).trans f14).trans ft)
  have qat : QArr L s.mem t.mem := (((qa9.trans (by rw [m10]; exact QArr.refl _ _)).trans
    (prod_qarr o11 (by decide))).trans ((prod_qarr o12 (by decide)).trans qa13')).trans
    ((prod_qarr o14 (by decide)).trans (prod_qarr ot (by decide)))
  have Qt := Q14.step kt (by decide)
  have kw : Keep sValueAll s t :=
    (((((((((((((k1.mono (rs' := sValueAll)).trans' (k2.mono)).trans' (k3.mono)).trans' (k4.mono)).trans'
      (k5.mono)).trans' (k6.mono)).trans' (k7.mono)).trans' (k8.mono)).trans' (k9.mono)).trans'
      (k10.mono)).trans' (k11.mono)).trans' (k12.mono)).trans' (k13'.mono)).trans' ((k14.mono).trans' (kt.mono))
  refine ⟨⟨Qt, ?_, Ft.get 9, qat⟩, ⟨fun r hr => ?_, kw.rd, kw.wr, kw.sp, kw.lr⟩⟩
  · exact (prod_mont_back hcop lt e14 (by rw [et, hRR])).trans (by rw [Nat.mul_comm _ (arrQ s.mem L 4)])
  · by_cases e10 : r = .r10
    · subst e10; rw [Qt.inq.env.h10, h.inq.env.h10]
    by_cases e31 : r = .r31
    · subst e31; rw [Qt.inq.env.h31, h.inq.env.h31]
    exact kw.gpr r fun h' => (List.mem_cons.mp h').elim e10 fun h' => (List.mem_cons.mp h').elim e31 hr

end VG.Proof.Dsa.PPC64LE
