module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Al
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the scan of `EM` and the validity of the padding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecSel.lean`): the validity of the padding, the
selected length and the mask of the private-key operation's success
(`validBlock_ok`), from the registers the scan left.
-/

@[expose] public section

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the scan of `EM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecScan.lean`): the first zero of `EM` from index
2 (`scanPart_ok`): whether there is one as a mask in `a4`, and where in `a5`,
as `firstZero` says.
-/

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (firstZero)

/-- A Boolean as a mask. -/
def bm (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem zero_mask (b : Byte) :
    (0 : BitVec 64) - ((b.setWidth 64 - BitVec.ofNat 64 1) >>> 63) = bm (decide (b = 0)) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have hl := b.isLt
    have e : b.setWidth 64 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (b.toNat - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega),
        BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have e2 : BitVec.ofNat 64 (b.toNat - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega
    rw [e, e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

/-- The byte at `t1`. -/
abbrev byt (t : State) : Byte := t.mem (t.gpr .t1 + BitVec.ofNat 64 0)

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 0) 1)
    (h6 : t.gpr .a6 = 0) (h7 : t.gpr .a7 = BitVec.allOnes 64) :
    WP isa (.block scanBody) t fun u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t u ∧
      u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 1 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      u.gpr .a3 = t.gpr .a3 + BitVec.ofNat 64 1 ∧
      u.gpr .a4 = t.gpr .a4 ||| bm (decide (byt t = 0)) ∧
      u.gpr .a5 = t.gpr .a5 ||| ((t.gpr .a4 ^^^ BitVec.allOnes 64) &&& bm (decide (byt t = 0)) &&& t.gpr .a3) := by
  unfold scanBody
  refine wp_lbu rfl h0 fun v₁ p₁ f₁ => wp_subi (imm := 1) (fun v₂ p₂ f₂ => wp_srl (sh := 63) fun v₃ p₃ f₃ =>
    wp_sub fun v₄ p₄ f₄ => wp_xor fun v₅ p₅ f₅ => wp_and fun v₆ p₆ f₆ => wp_and fun v₇ p₇ f₇ =>
    wp_or fun v₈ p₈ f₈ => wp_or fun v₉ p₉ f₉ => wp_addi (imm := 1) (fun v₁₀ p₁₀ f₁₀ =>
    wp_addi (imm := 1) (fun v₁₁ p₁₁ f₁₁ => wp_subi (imm := 1) (fun v₁₂ p₁₂ f₁₂ => wp_nil ?_) (by decide))
      (by decide)) (by decide)) (by decide)
  have O₁ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  have O₂ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] v₄ v₈ := (p₅.trans (p₆.trans (p₇.trans p₈))).mono
  have O₃ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] v₈ v₁₂ := (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂))).mono
  have z : v₄.gpr .a0 = bm (decide (byt t = 0)) := by
    rw [f₄, f₃, f₂, f₁, p₃.get .a6, p₂.get .a6, p₁.get .a6, h6, zero_mask]
  have g4 : v₄.gpr .a4 = t.gpr .a4 := by rw [p₄.get .a4, p₃.get .a4, p₂.get .a4, p₁.get .a4]
  have g3 : v₄.gpr .a3 = t.gpr .a3 := by rw [p₄.get .a3, p₃.get .a3, p₂.get .a3, p₁.get .a3]
  have g5 : v₄.gpr .a5 = t.gpr .a5 := by rw [p₄.get .a5, p₃.get .a5, p₂.get .a5, p₁.get .a5]
  have g7 : v₄.gpr .a7 = t.gpr .a7 := by rw [p₄.get .a7, p₃.get .a7, p₂.get .a7, p₁.get .a7]
  refine ⟨(O₁.trans (O₂.trans O₃)).mono, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p₁₂.get .t1, f₁₁, p₁₀.get .t1, p₉.get .t1, p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1,
      p₄.get .t1, p₃.get .t1, p₂.get .t1, p₁.get .t1]
  · rw [f₁₂, p₁₁.get .t2, p₁₀.get .t2, p₉.get .t2, p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2,
      p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2]
  · rw [p₁₂.get .a3, p₁₁.get .a3, f₁₀, p₉.get .a3, p₈.get .a3, p₇.get .a3, p₆.get .a3, p₅.get .a3, g3]
  · rw [p₁₂.get .a4, p₁₁.get .a4, p₁₀.get .a4, f₉, p₈.get .a4, p₇.get .a4, p₆.get .a4, p₅.get .a4,
      p₈.get .a0, p₇.get .a0, p₆.get .a0, p₅.get .a0, z, g4]
  · rw [p₁₂.get .a5, p₁₁.get .a5, p₁₀.get .a5, p₉.get .a5, f₈, f₇, f₆, f₅, p₇.get .a5, p₆.get .a5, p₅.get .a5,
      g5, p₆.get .a3, p₅.get .a3, g3, p₅.get .a0, z, g4, g7, h7]

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem a5_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm true &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  show 0#64 ||| ((0#64 ^^^ BitVec.allOnes 64) &&& BitVec.allOnes 64 &&& BitVec.ofNat 64 n) = _
  rw [BitVec.zero_xor, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.zero_or]

theorem a5_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm false &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h1 : t₀.gpr .t1 = O + BitVec.ofNat 64 2) (h2 : t₀.gpr .t2 = BitVec.ofNat 64 (k - 2))
    (h3 : t₀.gpr .a3 = BitVec.ofNat 64 2) (h4 : t₀.gpr .a4 = 0) (h5 : t₀.gpr .a5 = 0)
    (h6 : t₀.gpr .a6 = 0) (h7 : t₀.gpr .a7 = BitVec.allOnes 64) :
    WP isa scanLoop t₀ fun u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t₀ u ∧
      u.gpr .a4 = bm (firstZero EM k).isSome ∧ u.gpr .a5 = BitVec.ofNat 64 ((firstZero EM k).getD 0) := by
  refine (VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (N := k - 2) (by omega) (by omega)
    (fun j u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t₀ u ∧
      u.gpr .t1 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .a3 = BitVec.ofNat 64 (2 + j) ∧
      u.gpr .a4 = bm (firstZero EM (2 + j)).isSome ∧ u.gpr .a5 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0))
    (fun j hj u ⟨ku, u1, u3, u4, u5⟩ _ => ?_)
    ⟨Only.refl _ _, h1, h3, by rw [h4]; rfl, by rw [h5]; rfl⟩ h2).mono
    fun u ⟨ku, _, _, u4, u5⟩ => by
      rw [show 2 + (k - 2) = k by omega] at u4 u5
      exact ⟨ku, u4, u5⟩
  have hr0 := hr (2 + j) (by omega)
  rw [← ku.rd, ← ku.wr] at hr0
  have hb : byt u = EM.getD (2 + j) 1 := by
    rw [byt, u1, BitVec.add_zero, ku.mem, hEM _ (by omega)]
  refine WP.mono (scanBody_ok (by rw [u1, BitVec.add_zero]; exact hr0) ((ku.get .a6).trans h6)
    ((ku.get .a7).trans h7))
    fun w ⟨kw, w1, w2, w3, w4, w5⟩ => ⟨⟨(ku.trans kw).mono, by rw [w1, u1, Offset.add_add]; rfl,
      by rw [w3, u3, ← BitVec.ofNat_add]; rfl, ?_, ?_⟩, w2⟩
  · rw [w4, u4, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.allOnes_or]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, bm, hz, decide_true, Bool.false_eq_true, ite_true, ite_false,
          Option.isSome_some]
        rfl
      · simp only [Option.isSome_none, bm, hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
  · rw [w5, u5, u4, u3, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i =>
      simp only [Option.isSome_some, bm, ite_true, BitVec.xor_self, BitVec.zero_and, BitVec.or_zero,
        Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact a5_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact a5_neg _

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- After the scan. -/
structure SCN (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  al : t.gpr .t6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))
  a4 : t.gpr .a4 = bm (firstZero EM (s.gpr .a4).toNat).isSome
  a5 : t.gpr .a5 = BitVec.ofNat 64 ((firstZero EM (s.gpr .a4).toNat).getD 0)
  a6 : t.gpr .a6 = 0
  a7 : t.gpr .a7 = BitVec.allOnes 64

/-- A byte of `out` is accessible. -/
theorem outIn {t : State} (hp : Post s R EM t) {i : Nat} (hi : i < (s.gpr .a4).toNat) :
    InRegions (t.rd ++ t.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h1] at this
  exact ⟨oR s, by rw [hp.wr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]
    exact Offset.contains_base _ (by omega) (by omega)⟩

theorem scanPart_ok {t : State} (hl : AL s R EM kd t) : WP isa scanPart t (SCN s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold scanPart scanInit
  refine WP.seq (wp_addi (imm := 2) (fun v₁ p₁ f₁ => wp_subi (imm := 2) (fun v₂ p₂ f₂ =>
    wp_li (imm := 2) (by decide) fun v₃ p₃ f₃ => wp_li (imm := 0) (by decide) fun v₄ p₄ f₄ =>
    wp_li (imm := 0) (by decide) fun v₅ p₅ f₅ => wp_li (imm := 0) (by decide) fun v₆ p₆ f₆ =>
    wp_li (imm := 0) (by decide) fun v₇ p₇ f₇ => wp_subi (imm := 1) (fun t₁ p₈ f₈ => wp_nil ?_) (by decide))
    (by decide)) (by decide))
  have O : Only [.t1, .t2, .a3, .a4, .a5, .a6, .a7] t t₁ :=
    (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans p₈))))))).mono
  have P₁ := hl.toAMR.only h O
  have e2 : s.gpr .a4 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (scanLoop_ok (O := s.gpr .a0) (EM := EM) (k := (s.gpr .a4).toNat) (by omega) (by omega)
    (fun i hi => by rw [← P₁.em, bytes_getD' _ _ hi]) (fun i hi => outIn h P₁.toPost hi)
    (by rw [p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1, p₄.get .t1, p₃.get .t1, p₂.get .t1, f₁, hl.s2])
    (by rw [p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2, p₄.get .t2, p₃.get .t2, f₂, p₁.get .s1, hl.s1, e2])
    (by rw [p₈.get .a3, p₇.get .a3, p₆.get .a3, p₅.get .a3, p₄.get .a3, f₃])
    (by rw [p₈.get .a4, p₇.get .a4, p₆.get .a4, p₅.get .a4, f₄]; rfl)
    (by rw [p₈.get .a5, p₇.get .a5, p₆.get .a5, f₅]; rfl)
    (by rw [p₈.get .a6, p₇.get .a6, f₆]; rfl)
    (by rw [f₈, f₇]; decide))
    fun u ⟨ku, u4, u5⟩ => ⟨P₁.only h ku, by rw [ku.get .t6, O.get .t6, hl.al], u4, u5,
      by rw [ku.get .a6, p₈.get .a6, p₇.get .a6, f₆]; rfl, by rw [ku.get .a7, f₈, f₇]; decide⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Proof.RsaPkcs1Enc (firstZero vOf lselOf outByte)

/-- `-(x = 0)`, for `x < 2 ^ 63`. -/
theorem zero_mask64 (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - ((x - BitVec.ofNat 64 1) >>> 63) = bm (decide (x = 0)) := by
  by_cases h : x = 0
  · subst h; decide
  · have hb : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have e2 : (x - BitVec.ofNat 64 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega
    rw [e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem ten_mask {sep : Nat} (h : sep < 2 ^ 63) :
    (0 : BitVec 64) - ((BitVec.ofNat 64 sep - BitVec.ofNat 64 10) >>> 63) = bm (decide (sep < 10)) := by
  rw [borrow _ _ h (by decide)]
  by_cases hs : sep < 10
  · simp only [show ¬ 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_true]; decide
  · simp only [show 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_false, Bool.false_eq_true]; decide

theorem bm_and (a b : Bool) : bm a &&& bm b = bm (a && b) := by
  cases a <;> cases b <;> rfl

theorem bm_not (a : Bool) : bm a ^^^ BitVec.allOnes 64 = bm (!a) := by
  cases a <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : x ^^^ ((y ^^^ x) &&& bm v) = if v then y else x := by
  cases v
  · simp [bm]
  · simp only [bm, ite_true, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem byte_zero (b : Byte) : decide (b.setWidth 64 = (0 : BitVec 64)) = decide (b = 0) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have : b.setWidth 64 ≠ 0 := fun e => hb (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this)
    simp only [this, h, decide_false]

theorem byte_two (b : Byte) :
    decide (b.setWidth 64 ^^^ BitVec.ofNat 64 2 = (0 : BitVec 64)) = decide (b = 2) := by
  rw [decide_eq_decide, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro e
    have := congrArg (BitVec.setWidth 8) e
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · intro e; subst e; decide

theorem byte_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
  exact Nat.lt_trans b.isLt (by decide)

theorem byte2_lt (b : Byte) : (b.setWidth 64 ^^^ BitVec.ofNat 64 2).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)),
    BitVec.toNat_ofNat]
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 8) b.isLt (by decide)) (by decide)

theorem vOf_bm (a b : Byte) (f : Bool) (sep : Nat) :
    bm f &&& (bm (decide (a = 0)) &&& bm (decide (b = 2))) &&& bm (!decide (sep < 10)) = bm (vOf a b f sep) := by
  have e : (!decide (sep < 10)) = decide (10 ≤ sep) := by
    by_cases hs : sep < 10
    · simp only [hs, decide_true, Bool.not_true, show ¬ 10 ≤ sep by omega, decide_false]
    · simp only [hs, decide_false, Bool.not_false, show 10 ≤ sep by omega, decide_true]
  rw [bm_and, bm_and, bm_and, e]
  congr 1
  unfold vOf
  cases f <;> by_cases ha : a = 0 <;> by_cases hb : b = 2 <;> by_cases hs : 10 ≤ sep <;> simp [ha, hb, hs]

/-- The block's results, from the registers the scan left. -/
theorem validBlock_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hp : Post s R EM t)
    (h0 : InRegions (t.rd ++ t.wr) (s.gpr .a0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (s.gpr .a0 + BitVec.ofNat 64 1) 1)
    {f : Bool} {sep al : Nat} (h4 : t.gpr .a4 = bm f) (h5 : t.gpr .a5 = BitVec.ofNat 64 sep)
    (h6 : t.gpr .t6 = BitVec.ofNat 64 al) (ha6 : t.gpr .a6 = 0) (ha7 : t.gpr .a7 = BitVec.allOnes 64)
    (hsep : sep < 2 ^ 63) (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa (.block validBlock) t fun u => Only [.t1, .t2, .a0, .a1, .a3, .a4, .a5, .t6] t u ∧
      u.gpr .t1 = s.gpr .a0 ∧ u.gpr .t2 = s.gpr .a4 ∧
      u.gpr .a4 = bm (vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .a3 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .t6 = (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep then
          s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
        bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .a5 = s.gpr .a4 - (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1))
          f sep then s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) := by
  unfold validBlock
  mrun [mov, hp.s2, hp.s1, hp.r, h0, h1, h4, h5, h6, ha6, ha7]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_⟩
  · obtain ⟨a, b, c, d, e, f, g, i⟩ : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧
        r ≠ .t6 := by simpa using hr
    simp only [a, b, c, d, e, f, g, i, ite_false]
  simp only [zero_mask64 _ (byte_lt _), zero_mask64 _ (byte2_lt _), zero_mask64 _ hR, ten_mask hsep, bm_not,
    byte_two, byte_zero, vOf_bm, sel_xor]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
