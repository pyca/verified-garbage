module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreDouble
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The precomputed values of an RSA modulus on PPC64LE: `R² mod n` by squares

`r2Fast_ok`: `x := 2^(128 w) mod n`, for `n` of `w` words above
`2^(64 (w - 1))`: `x := 2^(64 (w - 1))` (`r2Top_ok`), `64 + w` doublings to
`2^w R mod n`, then six Montgomery squares (`r2Sq_ok`), each doubling the
exponent of `2^e R mod n`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute
open VG.Proof.Bignum.PPC64LE

/-- `2^(64 (w - 1))` in array 1, from `r5` and `r11`. -/
theorem r2Top_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B (slot w 1)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : slot w 1 + 8 * w ≤ Z) :
    WP isa r2Top s fun t =>
      (wv t.mem B (slot w 1) w = 2 ^ (64 * (w - 1)) ∧ Mont.Outside B (slot w 1) (8 * w) s.mem t.mem) ∧
        Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  unfold r2Top
  refine WP.seq (WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = off B (slot w 1) ∧ t.mem = s.mem)
    (by prun [h5, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k1.wr) a14 ((k1.gpr _ (by decide)).trans h11) hw hw' hZ)
    fun s₂ ⟨⟨_, hz, out2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have ea : BitVec.ofNat 64 (2 * w) <<< 2 + s₂.gpr .r5 - BitVec.ofNat 64 8 = off B (slot w 1 + 8 * (w - 1)) := by
    rw [k12.gpr .r5 (by decide), h5]
    simp only [off]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    have := B.isLt
    unfold slot hdrBytes at hZ ⊢
    omega
  refine WP.mono (WP.keep [.r0, .r14] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (slot w 1 + 8 * (w - 1))) (BitVec.ofNat 64 1)) (by
    prun [(k2.gpr .r11 (by decide)).trans ((k1.gpr .r11 (by decide)).trans h11), ea, BitVec.add_zero,
      (hs.congr k12.wr).st (show slot w 1 + 8 * (w - 1) + 8 ≤ Z by omega)]) (by decide)) fun t ⟨tm, k3⟩ => ⟨⟨?_, ?_⟩, (k12.trans k3).mono⟩
  · rw [tm]
    have e := wv_add (s₂.mem.writeW (off B (slot w 1 + 8 * (w - 1))) (BitVec.ofNat 64 1)) B (slot w 1) (w - 1) 1
    rw [show w - 1 + 1 = w by omega] at e
    rw [e]
    have hlow : wv (s₂.mem.writeW (off B (slot w 1 + 8 * (w - 1))) (BitVec.ofNat 64 1)) B (slot w 1) (w - 1) = 0 := by
      refine (wv_eq_zero_iff _ _ _ _).mpr fun q hq => ?_
      show Mem.readW _ (B + BitVec.ofNat 64 (slot w 1 + 8 * q)) 64 = 0
      rw [Mem.readW_writeW_sep (Offset.sep B (Or.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact hz q (by omega)
    rw [hlow, Nat.zero_add]
    simp only [wv, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [show (word _ B (slot w 1 + 8 * (w - 1))) = BitVec.ofNat 64 1 from Mem.readW_writeW_self64 _ _ _]
    simp
  · rw [tm, m1] at *
    rw [m1] at out2
    exact out2.trans ((writeW_outside s₂.mem B (d := slot w 1 + 8 * (w - 1)) _ (by omega)).mono (by omega)
      (by omega))

/-! ## Montgomery squares -/

theorem r2Stride_ok {t : State} {w : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)) :
    WP isa (.block r2Stride) t fun t' =>
      (t'.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
  refine WP.keep _ ?_ (by decide)
  unfold r2Stride
  prun [h11]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

theorem r2Base_cons (rd : Reg) (j : Nat) :
    r2Base rd (j + 1) = r2Base rd j ++ ([.add rd rd .r3] : List Instr) := by
  simp only [r2Base, List.replicate_succ', List.cons_append]

/-- `r2Base rd j`, array 0 at `r10` and the arrays' size in `r3`. -/
theorem r2Base_ok {t : State} {B : Addr} {w : Nat} {rd : Reg} (hrd : rd ≠ .r0) (hrd3 : rd ≠ .r3)
    (h10 : t.gpr .r10 = off B (slot w 0)) (h3 : t.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2))) :
    ∀ j, WP isa (.block (r2Base rd j)) t fun t' =>
      (t'.gpr rd = off B (slot w j) ∧ t'.mem = t.mem) ∧ Keep [rd] t t'
  | 0 => by
    apply WP.of_runBlock
    simp only [r2Base, List.replicate_zero, runBlock_cons, exec_addi (show Reg.r10 ≠ .r0 by decide)
      (show 0 < 2 ^ 15 by decide), runStep_some, runBlock_nil, BitVec.add_zero, h10]
    exact ⟨_, rfl, ⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩
  | j + 1 => by
    rw [r2Base_cons, WP.block_append_iff]
    refine WP.mono (r2Base_ok hrd hrd3 h10 h3 j) fun t₁ ⟨⟨h1, m1⟩, k1⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, exec_add, runStep_some, runBlock_nil, h1,
      (k1.gpr .r3 (by simpa using Ne.symm hrd3)).trans h3]
    refine ⟨_, rfl, ⟨?_, m1⟩, (k1.trans (Keep.write _ _ _)).mono (by simp)⟩
    rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e, off_add, show slot w (j + 1) = slot w j + 8 * (w + 2) by
      unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega]

/-- The registers a square writes. -/
def sqRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9] ++ tailRegs

/-- `r2Sq`: `x := x² R⁻¹ mod n`, `x` in array 1. -/
theorem r2Sq_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (h10 : s.gpr .r10 = off B (slot w 0)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w)) :
    WP isa r2Sq s fun t =>
      (val32 t.mem B (slot w 1) (2 * w) < val32 s.mem B (slot w 0) (2 * w) ∧
        val32 t.mem B (slot w 1) (2 * w) * 2 ^ (64 * w) % val32 s.mem B (slot w 0) (2 * w) =
          val32 s.mem B (slot w 1) (2 * w) * val32 s.mem B (slot w 1) (2 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
        Outs B [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 1, 8 * (w + 2))] s.mem t.mem) ∧
      Keep sqRegs s t := by
  unfold r2Sq
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (r2Stride_ok h11) fun t₀ ⟨⟨a3, m0⟩, k0⟩ => ?_
  have g10 : ∀ {u : State} {rs : List Reg}, Keep rs t₀ u → .r10 ∉ rs → u.gpr .r10 = off B (slot w 0) :=
    fun k h => (k.gpr _ h).trans ((k0.gpr _ (by decide)).trans h10)
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r5) (by decide) (by decide) (g10 (Keep.refl [] _) (by decide)) a3 1)
    fun t₁ ⟨⟨a5, m1⟩, k1⟩ => ?_
  have c1 : t₁.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2)) := (k1.gpr _ (by decide)).trans a3
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r6) (by decide) (by decide) (g10 k1 (by decide)) c1 1) fun t₂ ⟨⟨a6, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have c2 : t₂.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2)) := (k2.gpr _ (by decide)).trans c1
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r7) (by decide) (by decide) (g10 k12 (by decide)) c2 1) fun t₃ ⟨⟨a7, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have c3 : t₃.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2)) := (k3.gpr _ (by decide)).trans c2
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r8) (by decide) (by decide) (g10 k13 (by decide)) c3 2) fun t₄ ⟨⟨a8, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have c4 : t₄.gpr .r3 = BitVec.ofNat 64 (8 * (w + 2)) := (k4.gpr _ (by decide)).trans c3
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r9) (by decide) (by decide) (g10 k14 (by decide)) c4 3) fun t₅ ⟨⟨a9, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  refine WP.mono (WP.keep [.r4] (Q := fun u => u.gpr .r4 = BitVec.ofNat 64 (2 * w) ∧ u.mem = t₅.mem)
    (by prun [(k15.gpr .r11 (by decide)).trans ((k0.gpr .r11 (by decide)).trans h11), BitVec.add_zero])
    (by decide)) fun t₆ ⟨⟨a4, m6⟩, k6⟩ => ?_
  have k16 := (k0.trans k15).trans k6
  have hm : t₆.mem = s.mem := by rw [m6, m5, m4, m3, m2, m1, m0]
  rw [← hm] at hinv hB ⊢
  refine WP.mono (tailN_ok (hs.congr k16.wr) (n := 8) (o := 1) (a := 1) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' hZ
    (by rw [k6.gpr .r5 (by decide), k5.gpr .r5 (by decide), k4.gpr .r5 (by decide), k3.gpr .r5 (by decide),
      k2.gpr .r5 (by decide), a5])
    (by rw [k6.gpr .r6 (by decide), k5.gpr .r6 (by decide), k4.gpr .r6 (by decide), k3.gpr .r6 (by decide), a6])
    (by rw [k6.gpr .r7 (by decide), k5.gpr .r7 (by decide), k4.gpr .r7 (by decide), a7])
    (by rw [k6.gpr .r8 (by decide), k5.gpr .r8 (by decide), a8]) (by rw [k6.gpr .r9 (by decide), a9])
    (g10 (k15.trans k6) (by decide)) ((k16.gpr _ (by decide)).trans h11) a4
    (by rw [k16.gpr .r12 (by decide)]; exact h12) (by rw [k16.gpr .r12 (by decide)]; exact hinv) hB)
    fun t ⟨h, k⟩ => ⟨h, (k16.trans k).mono⟩

/-! ## `R² mod n` -/

/-- The registers `r2Fast` writes. -/
def r2FastRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22]

/-- The registers `r2Fast` changes: `r5`, `r8`, `r9`, `r19` and `r21` are
restored. -/
def r2ChgRegs : List Reg := [.r0, .r3, .r4, .r6, .r7, .r12, .r14, .r15, .r16, .r17, .r18, .r20, .r22]

theorem keep_chg {s t : State} (k : Keep r2FastRegs s t) (h5 : t.gpr .r5 = s.gpr .r5) (h8 : t.gpr .r8 = s.gpr .r8)
    (h9 : t.gpr .r9 = s.gpr .r9) (h19 : t.gpr .r19 = s.gpr .r19) (h21 : t.gpr .r21 = s.gpr .r21) :
    Keep r2ChgRegs s t := ⟨fun r hr => by
    by_cases e : r ∈ r2FastRegs
    · simp only [r2FastRegs, r2ChgRegs, List.mem_cons, List.not_mem_nil, or_false] at e hr
      rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp_all
    · exact k.gpr r e, k.rd, k.wr, k.sp, k.lr⟩

theorem pow_mod_double {a N : Nat} : 2 * (2 ^ a % N) % N = 2 ^ (a + 1) % N := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_comm]

/-- What holds between the squares, with `x ≡ 2^e R (mod N)`. -/
structure SqI (s : State) (B : Addr) (Z w N e : Nat) (t : State) : Prop where
  scr : Scr t B Z
  r10 : t.gpr .r10 = off B (slot w 0)
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  n : val32 t.mem B (slot w 0) (2 * w) = N
  lt : val32 t.mem B (slot w 1) (2 * w) < N
  x : val32 t.mem B (slot w 1) (2 * w) % N = 2 ^ e * 2 ^ (64 * w) % N
  out : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem
  r21 : t.gpr .r21 = s.gpr .r19
  keep : Keep r2FastRegs s t

theorem sqI_step {s t : State} {B : Addr} {Z w N e : Nat} (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z)
    (hodd : N % 2 = 1) (h : SqI s B Z w N e t) : WP isa r2Sq t (SqI s B Z w N (2 * e)) := by
  have hnw := h.scr.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  refine WP.mono (r2Sq_ok h.scr hw2 hw' hZ h.r10 h.r11 h.r12 h.inv (by rw [h.n]; exact h.lt))
    fun u ⟨⟨ul, ue, uo⟩, k⟩ => ?_
  rw [h.n] at ul ue
  have uo' : Mont.Outside B (slot w 1) (24 * (w + 2)) t.mem u.mem := fun x hx => uo x fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [Mont.ofs] at hx
    rcases hr with rfl | rfl | rfl <;> simp only [Mont.ofs] <;> omega
  have n0 : val32 u.mem B (slot w 0) (2 * w) = N := by rw [uo'.val32 (by omega) (by omega), h.n]
  have w0 : w32 u.mem B (slot w 0) = w32 t.mem B (slot w 0) := by
    have := uo'.val32 (d := slot w 0) (k := 1) (by omega) (by omega)
    simpa [val32] using this
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r21], u.gpr r = t.gpr r := fun r hr => k.gpr r (by revert r hr; decide)
  exact ⟨h.scr.congr k.wr, (g .r10 (by decide)).trans h.r10, (g .r11 (by decide)).trans h.r11,
    by rw [g .r12 (by decide)]; exact h.r12, by rw [g .r12 (by decide), w0]; exact h.inv, n0, ul,
    Pub.sq_step hR h.x ue, h.out.trans uo', (g .r21 (by decide)).trans h.r21, (h.keep.trans k).mono⟩

theorem r2Minv_eq : r2Minv = PublicChecked.minv := rfl

theorem wv_low_mod2' (m : Mem) (p : Addr) (d : Nat) {n : Nat} (hn : 1 ≤ n) :
    wv m p d n % 2 = (word m p d).toNat % 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega⟩
  rw [wv_add]
  simp only [wv, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
  rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- `r2Fast`, with `n` (odd, above `2^(64 (w - 1))`) in array 0 and the bases
of arrays 1–3 in `r5`, `r8`, `r9`: `x := 2^(128 w) mod n` in array 1,
changing only arrays 1–3; `r5`, `r8`, `r9` and `r19` are kept, and `r21` is
the working space. -/
theorem r2Fast_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h21 : s.gpr .r21 = B) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hZ : slot w 8 ≤ Z) (hN : 2 ^ (64 * (w - 1)) ≤ val32 s.mem B (slot w 0) (2 * w))
    (hodd : val32 s.mem B (slot w 0) (2 * w) % 2 = 1) :
    WP isa r2Fast s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep r2ChgRegs s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hlow : (Mont.word s.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2' _ _ _ (show 1 ≤ w by omega), ← VG.Proof.Bignum.read_eq_wv, ← show 4 * (2 * w) = 8 * w by omega,
      VG.Proof.Bignum.read_eq_val32]
    exact hodd
  generalize hNd : val32 s.mem B (slot w 0) (2 * w) = N at hN hodd hR ⊢
  replace hN : 2 ^ (64 * (w - 1)) < N := Nat.lt_of_le_of_ne hN fun h => by
    rw [← h, show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left] at hodd
    exact absurd hodd (by decide)
  have hN0 : 0 < N := by omega
  unfold r2Fast
  -- `x := 2^(64 (w - 1))`.
  refine WP.seq (WP.mono (r2Top_ok hs h5 h11 (by omega) hw' (by omega)) fun s₁ ⟨⟨x1, o1⟩, k1⟩ => ?_)
  have O1 : Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem s₁.mem := o1.mono (Nat.le_refl _) (by omega)
  -- The count.
  refine WP.seq (WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (64 + w) ∧ t.mem = s₁.mem)
    (by
      prun [(k1.gpr .r11 (by decide)).trans h11]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega) (by decide)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  -- The doublings.
  let Inv : Nat → State → Prop := fun j t =>
    val32 t.mem B (slot w 1) (2 * w) = 2 ^ (64 * (w - 1) + j) % N ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧ Keep [.r0, .r14, .r17, .r4, .r3, .r15, .r16, .r20] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r4) (N := 64 + w) (by omega) (by omega) Inv
    (fun j _ t ⟨tx, to, tk⟩ _ => ?_) ⟨?_, by rw [m2]; exact O1, k12.mono⟩ a4) fun s₃ ⟨x3, o3, k3⟩ => ?_)
  · have n0 : val32 t.mem B (slot w 0) (2 * w) = N := by rw [to.val32 (by omega) (by omega), hNd]
    refine WP.seq (WP.mono (doubleMod_ok (hs.congr tk.wr) ((tk.gpr _ (by decide)).trans h8)
      ((tk.gpr _ (by decide)).trans h9) ((tk.gpr _ (by decide)).trans h10) ((tk.gpr _ (by decide)).trans h5)
      ((tk.gpr _ (by decide)).trans h11) (by omega) hw' (by omega) (by rw [tx, n0]; exact Nat.mod_lt _ hN0))
      fun t₁ ⟨d1, od, kd⟩ => ?_)
    refine WP.mono (subi_ok t₁ .r4 (by decide)) fun t₂ e2 => ?_
    subst e2
    refine ⟨⟨?_, by rw [mem_write]; exact to.trans od, ((tk.trans kd).trans (Keep.write _ _ _)).mono⟩, ?_⟩
    · rw [mem_write, d1, tx, n0, pow_mod_double, Nat.add_assoc]
    · gsimp; rw [kd.gpr .r4 (by decide)]
  · rw [Nat.add_zero, m2, ← VG.Proof.Bignum.read_eq_val32, show 4 * (2 * w) = 8 * w by omega,
      VG.Proof.Bignum.read_eq_wv, x1]
    exact (Nat.mod_eq_of_lt hN).symm
  -- `-n⁻¹ mod 2³²`, and `pre` into `r21`.
  have n3 : val32 s₃.mem B (slot w 0) (2 * w) = N := by rw [o3.val32 (by omega) (by omega), hNd]
  have w3 : Mont.word s₃.mem B (slot w 0) = Mont.word s.mem B (slot w 0) := o3.word (Or.inl (by omega)) (by omega)
  refine WP.seq ?_
  rw [r2Minv_eq, WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hs.congr k3.wr) ((k3.gpr _ (by decide)).trans h10) (by omega)
    (by rw [w3]; exact hlow)) fun s₄ ⟨⟨i12, iinv, m4⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r21] (Q := fun t => t.gpr .r21 = s₄.gpr .r19 ∧ t.mem = s₄.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun s₅ ⟨⟨a21, m5⟩, k5⟩ => ?_
  have k35 := (k3.trans k4).trans k5
  have I0 : SqI s B Z w N w s₅ := by
    refine ⟨hs.congr k35.wr, (k35.gpr _ (by decide)).trans h10, (k35.gpr _ (by decide)).trans h11,
      by rw [k5.gpr .r12 (by decide)]; exact i12, by rw [k5.gpr .r12 (by decide), m5, m4]; exact iinv,
      by rw [m5, m4, n3], ?_, ?_, by rw [m5, m4]; exact o3, ?_, k35.mono⟩
    · rw [m5, m4, x3]; exact Nat.mod_lt _ hN0
    · rw [m5, m4, x3, Nat.mod_mod, show 64 * (w - 1) + (64 + w) = w + 64 * w by omega, Nat.pow_add]
    · rw [a21, k4.gpr .r19 (by decide), k3.gpr .r19 (by decide)]
  -- Six squares.
  have st := fun {e : Nat} {t : State} (h : SqI s B Z w N e t) => sqI_step hw hw' hZ hodd h
  refine WP.seq (WP.mono (st I0) fun u₁ I1 => WP.seq (WP.mono (st I1) fun u₂ I2 => WP.seq (WP.mono (st I2)
    fun u₃ I3 => WP.seq (WP.mono (st I3) fun u₄ I4 => WP.seq (WP.mono (st I4) fun u₅ I5 =>
      WP.seq (WP.mono (st I5) fun u I6 => ?_))))))
  -- `pre` back into `r19`, the working space into `r21`, the bases.
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r19, .r21] (Q := fun t => t.gpr .r19 = s.gpr .r19 ∧ t.gpr .r21 = B ∧ t.mem = u.mem)
    (by
      prun [BitVec.add_zero, I6.r21, I6.r10, exec_subi (n := .r10) (imm := hdrBytes) (by decide) (by decide)]
      show B + BitVec.ofNat 64 (hdrBytes + 0 * (8 * (w + 2))) - BitVec.ofNat 64 hdrBytes = B
      rw [Nat.zero_mul, Nat.add_zero, BitVec.add_sub_cancel]) (by decide)) fun v₁ ⟨⟨b19, b21, mv1⟩, kv1⟩ => ?_
  have c10 : v₁.gpr .r10 = off B (slot w 0) := (kv1.gpr _ (by decide)).trans I6.r10
  rw [WP.block_append_iff]
  refine WP.mono (r2Stride_ok ((kv1.gpr _ (by decide)).trans I6.r11)) fun v₂ ⟨⟨b3, mv2⟩, kv2⟩ => ?_
  have c10' := (kv2.gpr _ (by decide)).trans c10
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r5) (by decide) (by decide) c10' b3 1) fun v₃ ⟨⟨b5, mv3⟩, kv3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (r2Base_ok (rd := .r8) (by decide) (by decide) ((kv3.gpr _ (by decide)).trans c10')
    ((kv3.gpr _ (by decide)).trans b3) 2) fun v₄ ⟨⟨b8, mv4⟩, kv4⟩ => ?_
  refine WP.mono (r2Base_ok (rd := .r9) (by decide) (by decide) ((kv4.gpr _ (by decide)).trans
    ((kv3.gpr _ (by decide)).trans c10')) ((kv4.gpr _ (by decide)).trans ((kv3.gpr _ (by decide)).trans b3)) 3)
    fun t ⟨⟨b9, mt⟩, kt⟩ => ?_
  have hm : t.mem = u.mem := by rw [mt, mv4, mv3, mv2, mv1]
  have kvt := ((kv1.trans kv2).trans (kv3.trans kv4)).trans kt
  refine ⟨?_, by rw [hm]; exact I6.out, keep_chg (I6.keep.trans kvt).mono ?_ ?_ ?_ ?_ ?_⟩
  · rw [hm, ← Nat.mod_eq_of_lt I6.lt, I6.x, show 2 * (2 * (2 * (2 * (2 * (2 * w))))) = 64 * w by omega,
      ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
  · rw [kt.gpr .r5 (by decide), kv4.gpr .r5 (by decide), b5, h5]
  · rw [kt.gpr .r8 (by decide), b8, h8]
  · rw [b9, h9]
  · rw [kt.gpr .r19 (by decide), kv4.gpr .r19 (by decide), kv3.gpr .r19 (by decide), kv2.gpr .r19 (by decide), b19]
  · rw [kt.gpr .r21 (by decide), kv4.gpr .r21 (by decide), kv3.gpr .r21 (by decide), kv2.gpr .r21 (by decide), b21,
      h21]

end VG.Proof.Bignum.PPC64LE.Pre
