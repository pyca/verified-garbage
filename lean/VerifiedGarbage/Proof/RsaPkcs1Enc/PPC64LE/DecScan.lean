module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecAl
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the scan of `EM`

The first zero of `EM` from index 2 (`scanPart_ok`): whether there is one as
a mask in `r5`, and where in `r3`, as `firstZero` says.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
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

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1)
    (h0' : t.gpr .r0 = 0) (h8 : t.gpr .r8 = BitVec.allOnes 64) :
    WP isa (.block scanBody) t fun u => (u.mem = t.mem ∧ u.gpr .r11 = t.gpr .r11 + BitVec.ofNat 64 1 ∧
      u.gpr .r7 = t.gpr .r7 - BitVec.ofNat 64 1 ∧ u.gpr .r4 = t.gpr .r4 + BitVec.ofNat 64 1 ∧
      u.gpr .r5 = t.gpr .r5 ||| bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) ∧
      u.gpr .r3 = t.gpr .r3 ||| ((t.gpr .r5 ^^^ BitVec.allOnes 64) &&&
        bm (decide (t.mem (t.gpr .r11 + BitVec.ofNat 64 0) = 0)) &&& t.gpr .r4)) ∧
      Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t u := by
  refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ rfl
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1 : (1 : Nat) < 2 ^ 15 := by decide
  unfold scanBody
  prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c0 h0, exec_addi (show Reg.r4 ≠ .r0 by decide) c1,
    exec_addi (show Reg.r11 ≠ .r0 by decide) c1, h0', h8]
  simp only [read1_64, zero_mask]
  exact ⟨trivial, trivial⟩

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem r3_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm true &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  show 0#64 ||| ((0#64 ^^^ BitVec.allOnes 64) &&& BitVec.allOnes 64 &&& BitVec.ofNat 64 n) = _
  rw [BitVec.zero_xor, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.zero_or]

theorem r3_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm false &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h11 : t₀.gpr .r11 = O + BitVec.ofNat 64 2) (h7 : t₀.gpr .r7 = BitVec.ofNat 64 (k - 2))
    (h4 : t₀.gpr .r4 = BitVec.ofNat 64 2) (h5 : t₀.gpr .r5 = 0) (h3 : t₀.gpr .r3 = 0)
    (h0 : t₀.gpr .r0 = 0) (h8 : t₀.gpr .r8 = BitVec.allOnes 64) :
    WP isa scanLoop t₀ fun u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r5 = bm (firstZero EM k).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM k).getD 0) := by
  refine (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r7) (N := k - 2) (by omega) (by omega)
    (fun j u => u.mem = t₀.mem ∧ Keep [.r10, .r9, .r3, .r5, .r4, .r11, .r7] t₀ u ∧
      u.gpr .r11 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .r4 = BitVec.ofNat 64 (2 + j) ∧
      u.gpr .r5 = bm (firstZero EM (2 + j)).isSome ∧ u.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0))
    (fun j hj u ⟨um, ku, u11, u4, u5, u3⟩ _ => ?_)
    ⟨rfl, Keep.refl _ _, h11, h4, by rw [h5]; rfl, by rw [h3]; rfl⟩ h7).mono
    fun u ⟨um, ku, _, _, u5, u3⟩ => by
      rw [show 2 + (k - 2) = k by omega] at u5 u3
      exact ⟨um, ku, u5, u3⟩
  have hr0 := hr (2 + j) (by omega)
  rw [← ku.rd, ← ku.wr] at hr0
  have hb : u.mem (u.gpr .r11 + BitVec.ofNat 64 0) = EM.getD (2 + j) 1 := by
    rw [u11, BitVec.add_zero, um, hEM _ (by omega)]
  refine WP.mono (scanBody_ok (by rw [u11, BitVec.add_zero]; exact hr0) ((ku.gpr _ (by decide)).trans h0)
    ((ku.gpr _ (by decide)).trans h8))
    fun w ⟨⟨wm, w11, w7, w4, w5, w3⟩, kw⟩ => ⟨⟨wm.trans um, ku.trans' kw, by rw [w11, u11, Offset.add_add]; rfl,
      by rw [w4, u4, ← BitVec.ofNat_add]; rfl, ?_, ?_⟩, w7⟩
  · rw [w5, u5, hb, firstZero_succ]
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
  · rw [w3, u3, u5, u4, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i =>
      simp only [Option.isSome_some, bm, ite_true, BitVec.xor_self, BitVec.zero_and, BitVec.or_zero,
        Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact r3_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact r3_neg _

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- After the scan. -/
structure SCN (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  amr : AMR s R EM kd t
  al : t.gpr .r6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .r7).toNat (clOf kd))
  r5 : t.gpr .r5 = bm (firstZero EM (s.gpr .r7).toNat).isSome
  r3 : t.gpr .r3 = BitVec.ofNat 64 ((firstZero EM (s.gpr .r7).toNat).getD 0)
  r0 : t.gpr .r0 = 0
  r8 : t.gpr .r8 = BitVec.allOnes 64

/-- A byte of `out` is accessible. -/
theorem outIn {t : State} (hc : Post s R EM t) {i : Nat} (hi : i < (s.gpr .r7).toNat) :
    InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h4] at this
  exact ⟨oR s, by rw [hc.wr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .r3, (s.gpr .r7).toNat⟩ by simp only [oR, h.h4]]
    exact Offset.contains_base _ (by omega) (by omega)⟩

theorem scanPart_ok {t : State} (hl : AL s R EM kd t) : WP isa scanPart t (SCN s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  have hc := hl.amr.post
  have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have e7 : s.gpr .r7 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r4, .r5, .r3, .r0, .r8]
    (Q := fun u => u.mem = t.mem ∧ u.gpr .r11 = s.gpr .r3 + BitVec.ofNat 64 2 ∧
      u.gpr .r7 = BitVec.ofNat 64 ((s.gpr .r7).toNat - 2) ∧ u.gpr .r4 = BitVec.ofNat 64 2 ∧ u.gpr .r5 = 0 ∧
      u.gpr .r3 = 0 ∧ u.gpr .r0 = 0 ∧ u.gpr .r8 = BitVec.allOnes 64) ?_ rfl)
    fun t₁ ⟨⟨m₁, x11, x7, x4, x5, x3, x0, x8⟩, k₁⟩ => ?_)
  · unfold scanInit
    prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, e7,
      exec_addi (show Reg.r11 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide),
      exec_subi (show Reg.r7 ≠ .r0 by decide) (show 2 ≤ 2 ^ 15 by decide),
      exec_subi (show Reg.r8 ≠ .r0 by decide) (show 1 ≤ 2 ^ 15 by decide)]
    exact ⟨rfl, rfl, rfl, by decide⟩
  have hc₁ : Post s R EM t₁ := hc.regs k₁.rd k₁.wr k₁.sp m₁ fun r hr => k₁.gpr r (by revert r; decide)
  refine WP.mono (scanLoop_ok (O := s.gpr .r3) (EM := EM) (k := (s.gpr .r7).toNat) (by omega) (by omega)
    (fun i hi => by rw [← hc₁.em, bytes_getD' _ _ hi]) (fun i hi => outIn h hc₁ hi) x11 x7 x4 x5 x3 x0 x8)
    fun u ⟨um, ku, u5, u3⟩ => ⟨hl.amr.regs ((k₁.mono (by decide)).trans' (ku.mono (by decide))) (um.trans m₁),
      by rw [ku.gpr _ (by decide), k₁.gpr _ (by decide), hl.al], u5, u3, by rw [ku.gpr _ (by decide), x0],
      by rw [ku.gpr _ (by decide), x8]⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
