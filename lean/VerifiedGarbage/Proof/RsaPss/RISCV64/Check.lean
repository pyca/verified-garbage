module

-- separate module: it builds in parallel with `Unmask`, `Scan` and `Finish`, which `Post` also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Impl.RsaPss.RISCV64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on RISC-V: the delimiter and the salt's length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Check.lean`): `check_ok`, `posCheck` and `lenCheck`
put in `s10` the accumulator, `EM`'s last byte (the first checks) ORed with
`val ⊕ 1` and, for a given salt length, with its difference from the salt's
(`accW`), in `s11` the salt's length `dbLen - pos - 1`, and `pos` in `s8`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view sc_in sc_inR fx)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_xor wp_or wp_mov wp_lbu
  wp_nil eval_zero)
open VG.Proof.Mgf1 (ifp ifn)

/-- The accumulator after the delimiter's and the salt length's checks. -/
def accW (a : Byte) (val : BitVec 64) (sl : Nat) (any saltLen : BitVec 64) : BitVec 64 :=
  (a.setWidth 64 ||| (val ^^^ 1#64)) ||| if any = 0 then BitVec.ofNat 64 sl ^^^ saltLen else 0#64

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `posCheck`: the accumulator with `val ⊕ 1`, the salt's length, and `pos`. -/
theorem posCheck_ok {t : State} (h : Base Sp (vP D) s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .a1).toNat - 1) = a) (h8 : t.gpr .a5 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .a6 = val) :
    WP isa (.block posCheck) t fun t' => Base Sp (vP D) s t' ∧ Only [.t1, .s10, .t2, .a6, .s11, .s8] t t' ∧
      t'.gpr .s10 = a.setWidth 64 ||| (val ^^^ 1#64) ∧ t'.gpr .s11 = BitVec.ofNat 64 (dN - pos - 1) ∧
      t'.gpr .s8 = BitVec.ofNat 64 pos := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2
  generalize hK : (s.gpr .a1).toNat = kN at hk hk2 ha
  refine wp_add fun t₁ o₁ e₁ => wp_subi (imm := 1) fun t₂ o₂ e₂ => ?_
  have a₂ : t₂.gpr .t1 = off (Sp s) (kN - 1) := by
    rw [e₂, e₁, h.s0, h.pk, ← ofNat_toNat (s.gpr .a1), hK, off_sub _ (by omega) (by omega)]
  refine wp_lbu (a := off (Sp s) (kN - 1)) (by rw [a₂, BitVec.add_zero])
    (by rw [o₂.rd, o₁.rd, o₂.wr, o₁.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun t₃ o₃ e₃ => ?_
  refine wp_li (imm := 1) (by decide) fun t₄ o₄ e₄ => wp_xor fun t₅ o₅ e₅ => wp_or fun t₆ o₆ e₆ =>
    wp_sub fun t₇ o₇ e₇ => wp_subi (imm := 1) fun t₈ o₈ e₈ => wp_mov fun t₉ o₉ e₉ => wp_nil ?_
  have k₉ : Only [.t1, .s10, .t2, .a6, .s11, .s8] t t₉ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))))))).mono
  refine ⟨h.only F k₉, k₉, ?_, ?_, ?_⟩
  · rw [o₉.get .s10, o₈.get .s10, o₇.get .s10, e₆, o₅.get .s10, o₄.get .s10, e₃, e₅, o₄.get .a6, o₃.get .a6,
      o₂.get .a6, o₁.get .a6, h9, e₄, o₂.mem, o₁.mem, ← ha]; rfl
  · rw [o₉.get .s11, e₈, e₇, o₆.get .s4, o₅.get .s4, o₄.get .s4, o₃.get .s4, o₂.get .s4, o₁.get .s4, h.pdb, L.hdb,
      o₆.get .a5, o₅.get .a5, o₄.get .a5, o₃.get .a5, o₂.get .a5, o₁.get .a5, h8,
      Offset.ofNat_sub_ofNat (show pos ≤ dN by omega), Offset.ofNat_sub_ofNat (show 1 ≤ dN - pos by omega)]
  · rw [e₉, o₈.get .a5, o₇.get .a5, o₆.get .a5, o₅.get .a5, o₄.get .a5, o₃.get .a5, o₂.get .a5, o₁.get .a5, h8]

/-- `lenCheck`: for a given salt length, the accumulator with the salt's
length's difference from it. -/
theorem lenCheck_ok {t : State} (h : Base Sp (vP D) s t) (x : Xs s t) {v : BitVec 64} {sl : Nat}
    (h24 : t.gpr .s10 = v) (h25 : t.gpr .s11 = BitVec.ofNat 64 sl) :
    WP isa lenCheck t fun t' => Base Sp (vP D) s t' ∧ Only [.t1, .s10] t t' ∧
      t'.gpr .s10 = v ||| if anyL s = 0 then BitVec.ofNat 64 sl ^^^ stackArg s 0 else 0#64 := by
  have F := L.F
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have ha0 : anyL s = 0 := by rw [← x.s7]; simpa using hz
    refine wp_xor fun w₁ p₁ f₁ => wp_or fun w p f => ?_
    have q : Only [.t1, .s10] t w := (p₁.trans p).mono
    refine wp_nil ⟨h.only F q, q, ?_⟩
    rw [f, p₁.get .s10, h24, f₁, h25, x.s6, ifp ha0]
  · have ha0 : anyL s ≠ 0 := by rw [← x.s7]; simpa using hz
    refine wp_nil ⟨h, Only.refl _ t, ?_⟩
    rw [h24, ifn ha0, BitVec.or_zero]

theorem check_ok {t : State} (h : Base Sp (vP D) s t) (x : Xs s t) {a : Byte} {pos : Nat} {val : BitVec 64}
    (ha : view t.mem (Sp s) ((s.gpr .a1).toNat - 1) = a) (h8 : t.gpr .a5 = BitVec.ofNat 64 pos) (hp : pos < dN)
    (h9 : t.gpr .a6 = val) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → Xs s t' → t'.mem = t.mem → Only [.t1, .s10, .t2, .a6, .s11, .s8] t t' →
      t'.syms = t.syms → t'.gpr .s10 = accW a val (dN - pos - 1) (anyL s) (stackArg s 0) →
      t'.gpr .s11 = BitVec.ofNat 64 (dN - pos - 1) → t'.gpr .s8 = BitVec.ofNat 64 pos → WP isa rest t' Q) :
    WP isa (.seq (.block posCheck) (.seq lenCheck rest)) t Q :=
  WP.seq (WP.mono_syms (posCheck_ok L h ha h8 hp h9) fun t₈ ⟨b₈, k₈, x24, x25, x8⟩ y₈ =>
    have x₈ : Xs s t₈ := x.of fun r hr => k₈.gpr r (by revert r; decide)
    WP.seq (WP.mono_syms (lenCheck_ok L b₈ x₈ x24 x25) fun w ⟨b, q, e⟩ yw =>
      k w b (x₈.of fun r hr => q.gpr r (by revert r; decide)) (by rw [q.mem, k₈.mem]) (k₈.trans q).mono
      (yw.trans y₈) (by rw [e]; rfl) (by rw [q.get .s11, x25]) (by rw [q.get .s8, x8])))

end

end VG.Proof.RsaPss.RISCV64
