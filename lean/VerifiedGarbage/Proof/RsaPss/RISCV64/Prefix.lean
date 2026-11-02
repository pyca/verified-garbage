module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaOaep.RISCV64
public import VerifiedGarbage.Impl.RsaPss.RISCV64
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSASSA-PSS verification on RISC-V: `M'`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Prefix.lean`): `prefix_ok`, `mPrefix nset` clears the
`n` bytes at `oY` that `nset` puts in `t5` and writes the digest `mHash`
after 8 of them; `salt_ok`, `copySalt` writes the last `salt_len` bytes of
`DB` after it; `copyDb_ok`, `copyDb` writes all of `DB` there. As views of
our part of the working space; each keeps every register but `a1`, `a4`,
`a5`, `t0` and `t5`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64 VG.WriteBytes
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_wb sc_in sc_inR sc_inW sc_w rd_in ne_of_dis fx
  kR bytes_entry)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_add wp_sub wp_mov wp_nil eval_nonzero
  ne_zero_iff fill_ok copy_ok)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- The digest. -/
abbrev mh (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a4) D

/-- The registers the writes of `M'` change. -/
abbrev mpR : List Reg := [.a1, .a4, .a5, .t0, .t5]

/-- `d := scratch + oY`. -/
theorem wp_yBase {d : Reg} {t : State} {S : Addr} (h0 : t.gpr .s0 = S) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Only [d] t t' → t'.gpr d = off S oY → WP isa (.block is) t' Q) :
    WP isa (.block (yBase d ++ is)) t Q :=
  wp_addi (imm := 2047) (fun t₁ o₁ e₁ => wp_addi (imm := 1) fun t₂ o₂ e₂ =>
    k t₂ ((o₁.trans o₂).mono fun r hr => by rcases List.mem_append.mp hr with h | h <;> exact h) (by rw [e₂, e₁, h0]; exact off_off _ _ _))

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `mPrefix nset`: `n` zeros at `oY`, and the digest after 8 of them. -/
theorem prefix_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {nset : List Instr} {n : Nat} (hn : 8 ≤ n)
    (hn' : n ≤ 2048)
    (hns : ∀ {u : State} {is : List Instr} {Q : State → Prop},
      (∀ u', Only [.t5] u u' → u'.gpr .t5 = BitVec.ofNat 64 n → WP isa (.block is) u' Q) →
      WP isa (.block (nset ++ is)) u Q)
    {t : State} (h : Base Sp (vP D) s t) :
    WP isa (mPrefix H nset) t fun t' => Base Sp (vP D) s t' ∧ Kept mpR t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 ≤ o ∧ o < oY + 8 + D then (mh D s).getD (o - (oY + 8)) 0
        else if oY ≤ o ∧ o < oY + n then 0 else view t.mem (Sp s) o := by
  have F := L.F
  have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2048 := rfl
  have hR : oRsa = 8192 := rfl
  have hB : WP isa (.block (yBase .a1 ++ nset ++ [.li .t0 0])) t fun t₃ => Only [.a1, .t5, .t0] t t₃ ∧
      t₃.gpr .a1 = off (Sp s) oY ∧ t₃.gpr .t5 = BitVec.ofNat 64 n ∧ t₃.gpr .t0 = 0#64 := by
    rw [List.append_assoc]
    exact wp_yBase h.s0 fun t₁ o₁ e₁ => hns fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ =>
      wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .a1, o₂.get .a1, e₁], by rw [o₃.get .t5, e₂], e₃⟩
  refine WP.seq (WP.seq (WP.mono hB fun t₃ ⟨k₃, a₃, n₃, z₃⟩ => ?_))
  refine WP.mono (fill_ok (p := off (Sp s) oY) (n := n) (b := 0) (by omega) (by omega) a₃ n₃
    (by rw [z₃]; rfl) (sc_w F (by rw [k₃.wr, h.wr]) (d := oY) (by omega))) fun t₄ ⟨hk₄, hm₄⟩ => ?_
  have K₄ : Kept mpR t t₄ := (k₃.keep.trans hk₄).mono
  have m₄ : t₄.mem = writeBytes t.mem (off (Sp s) oY) (List.replicate n 0) := by rw [hm₄, k₃.mem]
  have b₄ : Base Sp (vP D) s t₄ := h.wb F K₄ (by rw [List.length_replicate]; omega) m₄
  refine WP.seq (wp_mov fun t₅ o₅ e₅ => ?_)
  refine wp_yBase (by rw [o₅.get .s0, b₄.s0]) fun t₆ o₆ e₆ => wp_addi (imm := 8) fun t₇ o₇ e₇ =>
    wp_li (imm := H.D) (by rw [hD]; omega) fun t₈ o₈ e₈ => wp_nil ?_
  have k₈ : Only [.a4, .a1, .a5] t₄ t₈ := (o₅.trans (o₆.trans (o₇.trans o₈))).mono
  have hdg : ∀ j < D, ∀ i < D, s.gpr .a4 + BitVec.ofNat 64 j ≠ off (Sp s) (oY + 8) + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis L.dsc (Offset.contains_base _ (by omega) (by have := L.wd; omega))
      (by show (SC Sp s).Contains (off (off (Sp s) (oY + 8)) i) 1
          rw [off_off]; exact sc_in (o := oY + 8 + i) (n := 1) (by omega) _ (Region.contains_self _ _))
  refine WP.mono (copy_ok (q := s.gpr .a4) (p := off (Sp s) (oY + 8)) (n := D) hD0 (by omega)
    (by rw [o₈.get .a1, e₇, e₆]; exact off_off _ _ _) (by rw [o₈.get .a4, o₇.get .a4, o₆.get .a4, e₅, b₄.pdig])
    (by rw [e₈, hD]) (rd_in (by rw [k₈.rd, b₄.rd]) L.dr (by have := L.wd; omega) (Nat.le_refl _))
    (sc_w F (by rw [k₈.wr, b₄.wr]) (d := oY + 8) (by omega)) hdg) fun t' ⟨hk, hm⟩ => ?_
  have K : Kept mpR t₄ t' := (k₈.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₈.mem (s.gpr .a4) D = mh D s := by
    rw [k₈.mem]; exact bytes_entry b₄.mem L.dk L.dsc.symm (by omega)
  have m' : t'.mem = writeBytes t₄.mem (off (Sp s) (oY + 8)) (mh D s) := by rw [hm, hb, k₈.mem]
  refine ⟨b₄.wb F K (by rw [bytesAt_length]; omega) m', (K₄.trans K).mono, fun o ho => ?_⟩
  rw [m', view_wb _ _ (by rw [bytesAt_length]; omega) ho, bytesAt_length, m₄,
    view_wb _ _ (by rw [List.length_replicate]; omega) ho, List.length_replicate]
  by_cases e₁ : oY + 8 ≤ o ∧ o < oY + 8 + D
  · rw [ifp e₁, ifp e₁]
  · rw [ifn e₁, ifn e₁]
    by_cases e₂ : oY ≤ o ∧ o < oY + n
    · rw [ifp e₂, ifp e₂]; simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    · rw [ifn e₂, ifn e₂]

/-- `copyLoop` of `n > 0` bytes from `S + a` to `S + b` in our part of the
working space, the ranges apart. -/
theorem copyIn_ok {t : State} (h : Base Sp (vP D) s t) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ oRsa)
    (hb : b + n ≤ oRsa) (hab : a + n ≤ b ∨ b + n ≤ a) (h4 : t.gpr .a4 = off (Sp s) a)
    (h1 : t.gpr .a1 = off (Sp s) b) (h5 : t.gpr .a5 = BitVec.ofNat 64 n) :
    WP isa copyLoop t fun t' => Base Sp (vP D) s t' ∧ Kept [.t0, .a4, .a1, .a5] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o =
        if b ≤ o ∧ o < b + n then view t.mem (Sp s) (a + (o - b)) else view t.mem (Sp s) o := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  refine WP.mono (copy_ok (q := off (Sp s) a) (p := off (Sp s) b) (n := n) hn (by omega) h1 h4 h5
    (fun j hj => by
      show InRegions _ (off (off (Sp s) a) j) 1
      rw [off_off, h.wr]; exact sc_inR F (by omega) _)
    (sc_w F h.wr (d := b) hb)
    (fun j hj i hi => by
      show off (off (Sp s) a) j ≠ off (off (Sp s) b) i
      rw [off_off, off_off]; exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))) fun t' ⟨hk, hm⟩ => ?_
  refine ⟨h.wb F hk (by rw [bytesAt_length]; omega) hm, hk, fun o ho => ?_⟩
  rw [hm, view_wb _ _ (by rw [bytesAt_length]; omega) ho, bytesAt_length]
  by_cases e : b ≤ o ∧ o < b + n
  · rw [ifp e, ifp e]
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show o - b < n by omega), Option.map_some, Option.getD_some, view]
    exact congrArg t.mem (off_off (Sp s) a (o - b))
  · rw [ifn e, ifn e]

/-- `copySalt`: the last `salt_len` bytes of `DB` after `mHash`. -/
theorem salt_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    (x : Xs s t) (hsl : (s.gpr .a7).toNat + 1 ≤ dN) :
    WP isa (copySalt H) t fun t' => Base Sp (vP D) s t' ∧ Kept mpR t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 + D ≤ o ∧ o < oY + 8 + D + (s.gpr .a7).toNat then
        view t.mem (Sp s) (lN + dN - (s.gpr .a7).toNat + (o - (oY + 8 + D))) else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2048 := rfl
  generalize hS : (s.gpr .a7).toNat = sl at hsl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_sub fun t₃ o₃ e₃ => ?_)
  refine wp_yBase (by rw [o₃.get .s0, o₂.get .s0, o₁.get .s0, h.s0]) fun t₄ o₄ e₄ =>
    wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun t₅ o₅ e₅ => wp_mov fun t₆ o₆ e₆ => wp_nil ?_
  have k₆ : Only [.a4, .a1, .a5] t t₆ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  have b₆ := h.only F k₆
  have g5 : t₆.gpr .a5 = BitVec.ofNat 64 sl := by
    rw [e₆, o₅.get .s6, o₄.get .s6, o₃.get .s6, o₂.get .s6, o₁.get .s6, x.s6, ← ofNat_toNat (s.gpr .a7), hS]
  have g4 : t₆.gpr .a4 = off (Sp s) (lN + dN - sl) := by
    rw [o₆.get .a4, o₅.get .a4, o₄.get .a4, e₃, e₂, e₁, o₂.get .s6, o₁.get .s6, x.s6, o₁.get .s4, h.pdb, L.hdb,
      h.s0, h.plo, L.hlo, ← ofNat_toNat (s.gpr .a7), hS]
    exact (congrArg (· - BitVec.ofNat 64 sl) (off_off (Sp s) lN dN)).trans (off_sub _ (by omega) (by omega))
  have g1 : t₆.gpr .a1 = off (Sp s) (oY + 8 + D) := by
    rw [o₆.get .a1, e₅, e₄, hD]; exact (off_off _ _ _).trans (congrArg _ (Nat.add_assoc _ _ _).symm)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hs0 : sl ≠ 0 := by intro h0; rw [g5, ne_zero_iff, h0] at hc; simp at hc
    refine WP.mono (copyIn_ok L b₆ (a := lN + dN - sl) (b := oY + 8 + D) (n := sl) (by omega) (by omega)
      (by omega) (.inl (by omega)) g4 g1 g5) fun t' ⟨b', hk', v'⟩ =>
        ⟨b', (k₆.keep.trans hk').mono, fun o ho => ?_⟩
    rw [v' o ho, k₆.mem]
  · have hs0 : sl = 0 := by
      rw [g5, ne_zero_iff] at hc
      simp only [BitVec.toNat_ofNat, ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hc; omega
    refine wp_nil ⟨b₆, k₆.keep.mono, fun o ho => ?_⟩
    rw [ifn (by omega), k₆.mem]

/-- `copyDb`: `DB` after `mHash`. -/
theorem copyDb_ok {H : Impl.Hmac.Stream.RISCV64.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (copyDb H) t fun t' => Base Sp (vP D) s t' ∧ Kept mpR t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 + D ≤ o ∧ o < oY + 8 + D + dN then
        view t.mem (Sp s) (lN + (o - (oY + 8 + D))) else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hd1 := L.d1
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2048 := rfl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => ?_)
  refine wp_yBase (by rw [o₁.get .s0, h.s0]) fun t₂ o₂ e₂ =>
    wp_addi (imm := 8 + H.D) (h := by rw [hD]; omega) fun t₃ o₃ e₃ => wp_mov fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.a4, .a1, .a5] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine WP.mono (copyIn_ok L (h.only F k₄) (a := lN) (b := oY + 8 + D) (n := dN) (by omega) (by omega)
    (by omega) (.inl (by omega)) (by rw [o₄.get .a4, o₃.get .a4, o₂.get .a4, e₁, h.s0, h.plo, L.hlo])
    (by rw [o₄.get .a1, e₃, e₂, hD]; exact (off_off _ _ _).trans (congrArg _ (Nat.add_assoc _ _ _).symm))
    (by rw [e₄, o₃.get .s4, o₂.get .s4, o₁.get .s4, h.pdb, L.hdb]))
    fun t' ⟨b', hk', v'⟩ => ⟨b', (k₄.keep.trans hk').mono, fun o ho => ?_⟩
  rw [v' o ho, k₄.mem]

end

end VG.Proof.RsaPss.RISCV64
