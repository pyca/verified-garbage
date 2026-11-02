module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.RsaPss.RISCV64

/-!
# RSASSA-PSS verification on RISC-V: the result

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Cmp.lean`): `cmpH_ok`: `cmpH o` ORs `H'`
(at `o`) XORed with `H` (after `DB`) into the accumulator, and returns 1 if
it is then zero, 0 if not.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view sc_inR fx)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_xor wp_or wp_lbu wp_srl wp_nil)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

theorem or_lt {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) : (a ||| b).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow ha hb

theorem byte_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega_arith

/-- `(a - 1) >>> 63` for `a < 2^63`: 1 if `a = 0`, 0 if not. -/
theorem isz64 {a : BitVec 64} (ha : a.toNat < 2 ^ 63) :
    (a - BitVec.ofNat 64 1) >>> 63 = if a = 0#64 then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
  by_cases h : a = 0#64
  · subst h; rw [ifp rfl]; rfl
  · rw [ifn h]
    have h0 : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    simp only [BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
    have : (2 ^ 64 - 1 % 2 ^ 64 + a.toNat) % 2 ^ 64 = a.toNat - 1 := by omega_arith
    rw [this, Nat.div_eq_of_lt (by omega_arith)]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

theorem cmpH_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {o : Nat} (ho : o + D ≤ oRsa) (ho2 : o < 2048) {t : State}
    (h : Base Sp (vP D) s t) (ha : (t.gpr .s10).toNat < 2 ^ 63) :
    WP isa (cmpH H o) t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      t'.gpr .a0 = if t.gpr .s10 = 0#64 ∧
        ∀ i < D, view t.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (o + i) then 1#64 else 0#64 := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hR : oRsa = 8192 := rfl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_addi (h := ho2)
    fun t₃ o₃ e₃ => wp_li (imm := H.D) (by rw [hD]; omega_arith) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.a1, .a2, .a3] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have g4 : t₄.gpr .a1 = off (Sp s) (lN + dN) := by
    rw [o₄.get .a1, o₃.get .a1, e₂, e₁, o₁.get .s4, h.s0, h.plo, L.hlo, h.pdb, L.hdb]; exact off_off _ _ _
  have g5 : t₄.gpr .a2 = off (Sp s) o := by rw [o₄.get .a2, e₃, o₂.get .s0, o₁.get .s0, h.s0]
  let Eq' := fun (i : Nat) => ∀ j < i, view t.mem (Sp s) (lN + dN + j) = view t.mem (Sp s) (o + j)
  refine WP.seq (WP.mono (wp_countdown (cnt := .a3) (N := D) (by omega_arith) hD0
    (fun i u => Only [.a1, .a2, .a3, .t1, .t2, .s10] t₄ u ∧ u.gpr .a1 = off (Sp s) (lN + dN + i) ∧
      u.gpr .a2 = off (Sp s) (o + i) ∧ (u.gpr .s10).toNat < 2 ^ 63 ∧
      (u.gpr .s10 = 0#64 ↔ t.gpr .s10 = 0#64 ∧ Eq' i)) ?_
    ⟨Only.refl _ _, by rw [g4]; rfl, by rw [g5]; rfl, by rw [k₄.get .s10]; exact ha,
      by rw [k₄.get .s10]; exact ⟨fun e => ⟨e, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun e => e.1⟩⟩
    (by rw [e₄, hD])) fun u ⟨ou, _, _, hu, hz⟩ => ?_)
  · intro i hi u ⟨ou, u4, u5, ul, uz⟩ _
    simp only [List.cons_append, List.nil_append]
    refine wp_lbu (a := off (Sp s) (lN + dN + i)) (by rw [u4, BitVec.add_zero])
      (by rw [ou.rd, ou.wr, k₄.rd, k₄.wr, h.wr]; exact sc_inR F (by omega_arith) _) fun u₁ p₁ f₁ => ?_
    refine wp_lbu (a := off (Sp s) (o + i)) (by rw [p₁.get .a2, u5, BitVec.add_zero])
      (by rw [p₁.rd, p₁.wr, ou.rd, ou.wr, k₄.rd, k₄.wr, h.wr]; exact sc_inR F (by omega_arith) _) fun u₂ p₂ f₂ => ?_
    refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi (imm := 1) fun u₅ p₅ f₅ => wp_addi (imm := 1) fun u₆ p₆ f₆ =>
      wp_subi (imm := 1) fun u₇ p₇ f₇ => wp_nil ?_
    have q : Only [.t1, .t2, .s10, .a1, .a2, .a3] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have mu : u.mem = t.mem := by rw [ou.mem, k₄.mem]
    have x7 : u₃.gpr .t1 = (view t.mem (Sp s) (lN + dN + i) ^^^ view t.mem (Sp s) (o + i)).setWidth 64 := by
      rw [f₃, p₂.get .t1, f₁, f₂, p₁.mem, mu, BitVec.setWidth_xor]; rfl
    have x24 : u₇.gpr .s10 = u.gpr .s10 ||| (view t.mem (Sp s) (lN + dN + i) ^^^
        view t.mem (Sp s) (o + i)).setWidth 64 := by
      rw [p₇.get .s10, p₆.get .s10, p₅.get .s10, f₄, x7, p₃.get .s10, p₂.get .s10, p₁.get .s10]
    refine ⟨⟨(ou.trans q).mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [p₇.get .a1, p₆.get .a1, f₅, p₄.get .a1, p₃.get .a1, p₂.get .a1, p₁.get .a1, u4]; exact off_off _ _ _
    · rw [p₇.get .a2, f₆, p₅.get .a2, p₄.get .a2, p₃.get .a2, p₂.get .a2, p₁.get .a2, u5]; exact off_off _ _ _
    · rw [x24]; exact or_lt ul (byte_lt _)
    · rw [x24, BitVec.or_eq_zero_iff, uz, and_assoc]
      refine and_congr_right fun _ => ⟨fun ⟨h₁, h₂⟩ j hj => ?_, fun h₁ => ⟨fun j hj => h₁ j (by omega_arith), ?_⟩⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h₁ j hj
        · have := congrArg (BitVec.setWidth 8) h₂
          rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
          exact BitVec.xor_eq_zero_iff.mp this
      · rw [BitVec.xor_eq_zero_iff.mpr (h₁ i (by omega_arith))]; rfl
    · rw [f₇, p₆.get .a3, p₅.get .a3, p₄.get .a3, p₃.get .a3, p₂.get .a3, p₁.get .a3]
  refine wp_subi (imm := 1) fun w₁ q₁ g₁ => wp_srl fun w q g => ?_
  have kw : Only [.a0, .a1, .a2, .a3, .t1, .t2, .s10] t w := (k₄.trans (ou.trans (q₁.trans q))).mono
  refine wp_nil ⟨h.only F kw, by rw [q.mem, q₁.mem, ou.mem, k₄.mem], ?_⟩
  rw [g, g₁, isz64 hu]
  by_cases e : u.gpr .s10 = 0#64
  · rw [ifp e, ifp (hz.mp e)]
  · rw [ifn e, ifn (fun h' => e (hz.mpr h'))]
end

end VG.Proof.RsaPss.RISCV64
