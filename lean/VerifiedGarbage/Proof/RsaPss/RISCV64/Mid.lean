module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Pre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on RISC-V: after the public operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Mid.lean`): from an entry state `s` (after the call,
the entry with the memory after it), `Lay D s lN dN c`, the encoding's
parameters as numbers (`lo = lN`, `dbLen = dN`, `c`, with
`lN + dN + hLen + 1 = k`); `acc0_ok`, `acc0` replaces `EM`'s last byte by the
OR of the first checks (`accB`), which is zero exactly when they pass
(`accB_eq_zero`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx kR)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_lbu
  wp_sb wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- The encoding's parameters, as numbers. -/
structure Lay (D : Nat) (s : State) (lN dN : Nat) (c : Byte) : Prop where
  F : Fits Sp s
  hlo : lo s = BitVec.ofNat 64 lN
  hdb : dbLen D s = BitVec.ofNat 64 dN
  hc : cm s = c.setWidth 64
  l1 : lN ≤ 1
  d1 : 1 ≤ dN
  hk : lN + dN + D + 1 = (s.gpr .a1).toNat
  k2 : (s.gpr .a1).toNat ≤ 1024
  D0 : 0 < D
  D64 : D ≤ 64
  dr : dR D s ∈ s.rd
  dsc : (dR D s).Disjoint (SC Sp s)
  dk : (kR s).Disjoint (dR D s)
  wd : (s.gpr .a4).toNat + D ≤ 2 ^ 64
  al : (Sp s).toNat % 8 = 0

/-- `p + a - b = p + (a - b)`. -/
theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    p + BitVec.ofNat 64 a - BitVec.ofNat 64 b = off p (a - b) := by
  apply BitVec.eq_of_toNat_eq
  have := p.isLt
  simp only [off, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  (BitVec.ofNat_toNat _ x).trans (BitVec.setWidth_eq _)

/-- The first checks: `EM`'s last byte against `0xbc`, the top bits of
`maskedDB`'s first byte, and the leading byte if `lo = 1`. -/
def accB (V : Nat → Byte) (lN : Nat) (c : Byte) (k : Nat) : Byte :=
  (V (k - 1) ^^^ 0xbc) ||| (V lN &&& (0xFF ^^^ c)) ||| (V 0 &&& if lN = 1 then 0xFF else 0)

theorem accB_eq_zero {V : Nat → Byte} {lN : Nat} {c : Byte} {k : Nat} :
    accB V lN c k = 0 ↔ V (k - 1) = 0xbc ∧ V lN &&& ~~~c = 0 ∧ (lN = 1 → V 0 = 0) := by
  have hn : (0xFF : Byte) ^^^ c = ~~~c := BitVec.allOnes_xor
  have h0 : (0 : Byte) = 0#8 := rfl
  rw [accB, hn, h0, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases h : lN = 1
  · rw [ifp h, show (0xFF : Byte) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]; simp [h]
  · rw [ifn h, BitVec.and_zero]; simp [h]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `acc0`: `EM`'s last byte replaced by `accB`. -/
theorem acc0_ok {t : State} (h : Base Sp (vP D) s t) (x : Xs s t) :
    WP isa (.block acc0) t fun t' => Base Sp (vP D) s t' ∧ Kept [.a1, .a2, .a3, .a4, .a5] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if o = (s.gpr .a1).toNat - 1 then
        accB (view t.mem (Sp s)) lN c (s.gpr .a1).toNat else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hl := L.l1
  generalize hK : (s.gpr .a1).toNat = k at hk hk2
  have rd1 : ∀ {u : State} {o : Nat}, u.rd = t.rd → u.wr = t.wr → o < oRsa →
      InRegions (u.rd ++ u.wr) (off (Sp s) o) 1 := fun hr hw ho => by
    rw [hr, hw, h.wr]; exact sc_inR F (by omega) _
  have aK : off (Sp s) (k - 1) = t.gpr .s0 + t.gpr .s1 - BitVec.ofNat 64 1 := by
    rw [h.s0, h.pk, ← ofNat_toNat (s.gpr .a1), hK, off_sub _ (by omega) (by omega)]
  simp only [acc0]
  refine wp_add fun t₁ o₁ e₁ => wp_subi (imm := 1) fun t₂ o₂ e₂ => ?_
  have a₂ : t₂.gpr .a1 = off (Sp s) (k - 1) := by rw [e₂, e₁, aK]
  refine wp_lbu (a := off (Sp s) (k - 1)) (by rw [a₂, BitVec.add_zero])
    (rd1 ((o₂.rd.trans o₁.rd)) (o₂.wr.trans o₁.wr) (by unfold oRsa; omega)) fun t₃ o₃ e₃ => ?_
  refine wp_li (imm := 0xbc) (by decide) fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ => wp_add fun t₆ o₆ e₆ => ?_
  have k₆ : Only [.a1, .a2, .a3, .a4] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  have a₆ : t₆.gpr .a4 = off (Sp s) lN := by
    rw [e₆, o₅.get .s0, o₄.get .s0, o₃.get .s0, o₂.get .s0, o₁.get .s0, h.s0, o₅.get .s3, o₄.get .s3,
      o₃.get .s3, o₂.get .s3, o₁.get .s3, h.plo, L.hlo]
  refine wp_lbu (a := off (Sp s) lN) (by rw [a₆, BitVec.add_zero]) (rd1 k₆.rd k₆.wr (by unfold oRsa; omega))
    fun t₇ o₇ e₇ => ?_
  refine wp_li (imm := 0xFF) (by decide) fun t₈ o₈ e₈ => wp_xor fun t₉ o₉ e₉ => wp_and fun t₁₀ o₁₀ e₁₀ =>
    wp_or fun t₁₁ o₁₁ e₁₁ => ?_
  have k₁₁ : Only [.a1, .a2, .a3, .a4, .a5] t t₁₁ :=
    (k₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans o₁₁))))).mono
  refine wp_lbu (a := off (Sp s) 0) (by rw [k₁₁.get .s0, h.s0]) (rd1 k₁₁.rd k₁₁.wr (by unfold oRsa; omega))
    fun t₁₂ o₁₂ e₁₂ => ?_
  refine wp_li (imm := 0) (by decide) fun t₁₃ o₁₃ e₁₃ => wp_sub fun t₁₄ o₁₄ e₁₄ => wp_and fun t₁₅ o₁₅ e₁₅ =>
    wp_or fun t₁₆ o₁₆ e₁₆ => ?_
  have k₁₆ : Only [.a1, .a2, .a3, .a4, .a5] t t₁₆ :=
    (k₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans o₁₆))))).mono
  have a₁₆ : t₁₆.gpr .a1 = off (Sp s) (k - 1) := by
    rw [o₁₆.get .a1, o₁₅.get .a1, o₁₄.get .a1, o₁₃.get .a1, o₁₂.get .a1, o₁₁.get .a1, o₁₀.get .a1, o₉.get .a1,
      o₈.get .a1, o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, a₂]
  refine wp_sb (a := off (Sp s) (k - 1)) (by rw [a₁₆, BitVec.add_zero])
    (by rw [k₁₆.wr, h.wr]; exact sc_inW F (by unfold oRsa; omega)) fun w mw => wp_nil ?_
  -- The byte.
  have m₁₆ : t₁₆.mem = t.mem := k₁₆.mem
  have hb : (t₁₆.gpr .a2).setWidth 8 = accB (view t.mem (Sp s)) lN c k := by
    have v3 : t₂.mem (off (Sp s) (k - 1)) = view t.mem (Sp s) (k - 1) := by rw [o₂.mem, o₁.mem]; rfl
    have v7 : t₆.mem (off (Sp s) lN) = view t.mem (Sp s) lN := by rw [k₆.mem]; rfl
    have v12 : t₁₁.mem (off (Sp s) 0) = view t.mem (Sp s) 0 := by rw [k₁₁.mem]; rfl
    have c9 : t₈.gpr .s5 = c.setWidth 64 := by
      rw [o₈.get .s5, o₇.get .s5, k₆.get .s5, x.s5, L.hc]
    have l14 : t₁₃.gpr .s3 = BitVec.ofNat 64 lN := by
      rw [o₁₃.get .s3, o₁₂.get .s3, k₁₁.get .s3, h.plo, L.hlo]
    rw [e₁₆, o₁₅.get .a2, o₁₄.get .a2, o₁₃.get .a2, o₁₂.get .a2, e₁₁, o₁₀.get .a2, o₉.get .a2, o₈.get .a2,
      o₇.get .a2, o₆.get .a2, e₅, o₄.get .a2, e₃, v3, e₄, e₁₀, o₉.get .a3, o₈.get .a3, e₇, v7, e₉, e₈, c9, e₁₅,
      o₁₄.get .a3, o₁₃.get .a3, e₁₂, v12, e₁₄, e₁₃, l14]
    simp only [BitVec.setWidth_or, BitVec.setWidth_and, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq, accB]
    rcases (show lN = 0 ∨ lN = 1 by omega) with rfl | rfl <;> rfl
  have hK : Kept [.a1, .a2, .a3, .a4, .a5] t w := (k₁₆.keep.trans mw.keep).mono
  refine ⟨h.keep F hK (R := [⟨off (Sp s) (k - 1), 1⟩]) (by
      rw [mw.mem, m₁₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega))),
    hK, fun o ho => ?_⟩
  rw [mw.mem, m₁₆, view_w8 _ _ (by unfold oRsa; omega) ho, hb]

end

end VG.Proof.RsaPss.RISCV64
