module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: the result

Untrusted: everything here is checked by Lean. `cmpH_ok`: `cmpH o` ORs `H'`
(at `o`) XORed with `H` (after `DB`) into the accumulator, and returns 1 if
it is then zero, 0 if not.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_xor wp_or wp_lbz wp_lsr wp_nil
  wp_countdown)
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

theorem cmpH_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {o : Nat} (ho : o + D ≤ oRsa) {t : State}
    (h : Base Sp (vP D) s t) (ha : (t.gpr .r24).toNat < 2 ^ 63) :
    WP isa (cmpH H o) t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      t'.gpr .r3 = if t.gpr .r24 = 0#64 ∧
        ∀ i < D, view t.mem (Sp s) (lN + dN + i) = view t.mem (Sp s) (o + i) then 1#64 else 0#64 := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64
  have hR : oRsa = 8192 := rfl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_addi (h := by unfold oRsa at ho; omega_arith)
    fun t₃ o₃ e₃ => wp_li (by rw [hD]; omega_arith) fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have g4 : t₄.gpr .r4 = off (Sp s) (lN + dN) := by
    rw [o₄.get .r4, o₃.get .r4, e₂, e₁, o₁.get .r21, h.r14, h.plo, L.hlo, h.pdb, L.hdb]; exact off_off _ _ _
  have g5 : t₄.gpr .r5 = off (Sp s) o := by rw [o₄.get .r5, e₃, o₂.get .r14, o₁.get .r14, h.r14]
  let Eq' := fun (i : Nat) => ∀ j < i, view t.mem (Sp s) (lN + dN + j) = view t.mem (Sp s) (o + j)
  refine WP.seq (WP.mono (wp_countdown (cnt := .r6) (N := D) (by omega_arith) hD0
    (fun i u => Only [.r4, .r5, .r6, .r7, .r8, .r24] t₄ u ∧ u.gpr .r4 = off (Sp s) (lN + dN + i) ∧
      u.gpr .r5 = off (Sp s) (o + i) ∧ (u.gpr .r24).toNat < 2 ^ 63 ∧
      (u.gpr .r24 = 0#64 ↔ t.gpr .r24 = 0#64 ∧ Eq' i)) ?_
    ⟨Only.refl _ _, by rw [g4]; rfl, by rw [g5]; rfl, by rw [k₄.get .r24]; exact ha,
      by rw [k₄.get .r24]; exact ⟨fun e => ⟨e, fun j hj => absurd hj (Nat.not_lt_zero _)⟩, fun e => e.1⟩⟩
    (by rw [e₄, hD])) fun u ⟨ou, _, _, hu, hz⟩ => ?_)
  · intro i hi u ⟨ou, u4, u5, ul, uz⟩ _
    refine wp_lbz (a := off (Sp s) (lN + dN + i)) (by rw [u4, BitVec.add_zero])
      (by rw [ou.rd, ou.wr, k₄.rd, k₄.wr, h.wr]; exact sc_inR F (by omega_arith) _) fun u₁ p₁ f₁ => ?_
    refine wp_lbz (a := off (Sp s) (o + i)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
      (by rw [p₁.rd, p₁.wr, ou.rd, ou.wr, k₄.rd, k₄.wr, h.wr]; exact sc_inR F (by omega_arith) _) fun u₂ p₂ f₂ => ?_
    refine wp_xor fun u₃ p₃ f₃ => wp_or fun u₄ p₄ f₄ => wp_addi fun u₅ p₅ f₅ => wp_addi fun u₆ p₆ f₆ =>
      wp_subi fun u₇ p₇ f₇ => wp_nil ?_
    have q : Only [.r7, .r8, .r24, .r4, .r5, .r6] u u₇ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans p₇)))))).mono
    have mu : u.mem = t.mem := by rw [ou.mem, k₄.mem]
    have x7 : u₃.gpr .r7 = (view t.mem (Sp s) (lN + dN + i) ^^^ view t.mem (Sp s) (o + i)).setWidth 64 := by
      rw [f₃, p₂.get .r7, f₁, f₂, p₁.mem, mu, BitVec.setWidth_xor]; rfl
    have x24 : u₇.gpr .r24 = u.gpr .r24 ||| (view t.mem (Sp s) (lN + dN + i) ^^^
        view t.mem (Sp s) (o + i)).setWidth 64 := by
      rw [p₇.get .r24, p₆.get .r24, p₅.get .r24, f₄, x7, p₃.get .r24, p₂.get .r24, p₁.get .r24]
    refine ⟨⟨(ou.trans q).mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [p₇.get .r4, p₆.get .r4, f₅, p₄.get .r4, p₃.get .r4, p₂.get .r4, p₁.get .r4, u4]; exact off_off _ _ _
    · rw [p₇.get .r5, f₆, p₅.get .r5, p₄.get .r5, p₃.get .r5, p₂.get .r5, p₁.get .r5, u5]; exact off_off _ _ _
    · rw [x24]; exact or_lt ul (byte_lt _)
    · rw [x24, BitVec.or_eq_zero_iff, uz, and_assoc]
      refine and_congr_right fun _ => ⟨fun ⟨h₁, h₂⟩ j hj => ?_, fun h₁ => ⟨fun j hj => h₁ j (by omega_arith), ?_⟩⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h₁ j hj
        · have := congrArg (BitVec.setWidth 8) h₂
          rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
          exact BitVec.xor_eq_zero_iff.mp this
      · rw [BitVec.xor_eq_zero_iff.mpr (h₁ i (by omega_arith))]; rfl
    · rw [f₇, p₆.get .r6, p₅.get .r6, p₄.get .r6, p₃.get .r6, p₂.get .r6, p₁.get .r6]
  refine wp_subi fun w₁ q₁ g₁ => wp_lsr fun w q g => ?_
  have kw : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r24] t w := (k₄.trans (ou.trans (q₁.trans q))).mono
  refine wp_nil ⟨h.only F kw, by rw [q.mem, q₁.mem, ou.mem, k₄.mem], ?_⟩
  rw [g, g₁, isz64 hu]
  by_cases e : u.gpr .r24 = 0#64
  · rw [ifp e, ifp (hz.mp e)]
  · rw [ifn e, ifn (fun h' => e (hz.mpr h'))]
end

end VG.Proof.RsaPss.PPC64LE
