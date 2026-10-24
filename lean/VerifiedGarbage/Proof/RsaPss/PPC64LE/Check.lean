module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: the delimiter and the salt's length

Untrusted: everything here is checked by Lean. `check_ok`: `posCheck` and
`lenCheck` put in `r24` the accumulator, `EM`'s last byte (the first checks)
ORed with `val ⊕ 1` and, for a given salt length, with its difference from
the salt's (`accW`), and in `r25` the salt's length `dbLen - pos - 1`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_or wp_lbz wp_nil
  eval_zero)
open VG.Proof.Mgf1 (ifp ifn)

/-- The accumulator after the delimiter's and the salt length's checks. -/
def accW (a : Byte) (val : BitVec 64) (sl : Nat) (any saltLen : BitVec 64) : BitVec 64 :=
  (a.setWidth 64 ||| (val ^^^ 1#64)) ||| if any = 0 then BitVec.ofNat 64 sl ^^^ saltLen else 0#64

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `posCheck`: the accumulator with `val ⊕ 1`, and the salt's length. -/
theorem posCheck_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) :
    WP isa (.block posCheck) t fun t' => Base Sp (vP D) s t' ∧ Only [.r4, .r24, .r3, .r9, .r25] t t' ∧
      t'.gpr .r24 = a.setWidth 64 ||| (val ^^^ 1#64) ∧ t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2
  generalize hK : (s.gpr .r4).toNat = kN at hk hk2 ha
  refine wp_add fun t₁ o₁ e₁ => wp_subi fun t₂ o₂ e₂ => ?_
  have a₂ : t₂.gpr .r4 = off (Sp s) (kN - 1) := by
    rw [e₂, e₁, h.r14, h.pk, ← ofNat_toNat (s.gpr .r4), hK, off_sub _ (by omega) (by omega)]
  refine wp_lbz (a := off (Sp s) (kN - 1)) (by rw [a₂, BitVec.add_zero])
    (by rw [o₂.rd, o₁.rd, o₂.wr, o₁.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun t₃ o₃ e₃ => ?_
  refine wp_li (by decide) fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ => wp_or fun t₆ o₆ e₆ =>
    wp_sub fun t₇ o₇ e₇ => wp_subi fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.r4, .r24, .r3, .r9, .r25] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  refine ⟨h.only F k₈, k₈, ?_, ?_⟩
  · rw [o₈.get .r24, o₇.get .r24, e₆, o₅.get .r24, o₄.get .r24, e₃, e₅, o₄.get .r9, o₃.get .r9, o₂.get .r9,
      o₁.get .r9, h9, e₄, o₂.mem, o₁.mem, ← ha]; rfl
  · rw [e₈, e₇, o₆.get .r21, o₅.get .r21, o₄.get .r21, o₃.get .r21, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb,
      o₆.get .r8, o₅.get .r8, o₄.get .r8, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8,
      Offset.ofNat_sub_ofNat (show pos ≤ dN by omega), Offset.ofNat_sub_ofNat (show 1 ≤ dN - pos by omega)]

/-- `lenCheck`: for a given salt length, the accumulator with the salt's
length's difference from it. -/
theorem lenCheck_ok {t : State} (h : Base Sp (vP D) s t) {v : BitVec 64} {sl : Nat} (h24 : t.gpr .r24 = v)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 sl) :
    WP isa lenCheck t fun t' => Base Sp (vP D) s t' ∧ Only [.r3, .r24] t t' ∧
      t'.gpr .r24 = v ||| if anyL s = 0 then BitVec.ofNat 64 sl ^^^ s.gpr .r10 else 0#64 := by
  have F := L.F
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have ha0 : anyL s = 0 := by rw [← h.pany]; simpa using hz
    refine wp_xor fun w₁ p₁ f₁ => wp_or fun w p f => ?_
    have q : Only [.r3, .r24] t w := (p₁.trans p).mono
    refine wp_nil ⟨h.only F q, q, ?_⟩
    rw [f, p₁.get .r24, h24, f₁, h25, h.psl, ifp ha0]
  · have ha0 : anyL s ≠ 0 := by rw [← h.pany]; simpa using hz
    refine wp_nil ⟨h, Only.refl _ t, ?_⟩
    rw [h24, ifn ha0, BitVec.or_zero]

theorem check_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .r4).toNat - 1) = a) (h8 : t.gpr .r8 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .r9 = val) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → t'.mem = t.mem →
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r8, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) →
      t'.gpr .r24 = accW a val (dN - pos - 1) (anyL s) (s.gpr .r10) →
      t'.gpr .r25 = BitVec.ofNat 64 (dN - pos - 1) → WP isa rest t' Q) :
    WP isa (.seq (.block posCheck) (.seq lenCheck rest)) t Q :=
  WP.seq (WP.mono (posCheck_ok L h ha h8 hp h9) fun t₈ ⟨b₈, k₈, x24, x25⟩ =>
    WP.seq (WP.mono (lenCheck_ok L b₈ x24 x25) fun w ⟨b, q, x⟩ => k w b (by rw [q.mem, k₈.mem])
      (fun r hr => by rw [q.gpr r (by revert r; decide), k₈.gpr r (by revert r; decide)])
      (by rw [x]; rfl) (by rw [q.get .r25, x25])))

end

end VG.Proof.RsaPss.PPC64LE
