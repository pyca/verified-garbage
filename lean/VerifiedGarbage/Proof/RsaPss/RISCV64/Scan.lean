module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
public import VerifiedGarbage.Impl.RsaPss.RISCV64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on RISC-V: the scan of `DB`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Scan.lean`): `scan_ok`, over the `dbLen` bytes of
`DB` (`w`), the number `z` of leading zero bytes (`Proof.RsaPss.lz`) without
branching on them: `pos` (`a5`) is `z` and `val` (`a6`) the byte there if
`z < dbLen`, both 0 if not. The invariant after `i` bytes is that of their
leading zeros (`lzr w i`, `lzr_succ`), with `a4` all ones while it is `i`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view sc_in sc_inR fx)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_and wp_or wp_srl
  wp_lbu wp_nil)
open VG.Proof.Bignum.RISCV64 (wp_countdown)
open VG.Proof.RsaPss (lz)
open VG.Proof.Mgf1 (ifp ifn)

/-- The leading zeros of the first `i` bytes of `w`. -/
def lzr (w : Nat → Byte) (i : Nat) : Nat := lz ((List.range i).map w)

theorem lz_append : ∀ (l : List Byte) (x : Byte),
    lz (l ++ [x]) = if lz l = l.length then (if x = 0 then l.length + 1 else l.length) else lz l
  | [], x => by simp only [List.nil_append, lz, List.length_nil]; split <;> simp
  | b :: bs, x => by
    rw [List.cons_append, lz, lz, lz_append bs x, List.length_cons]
    have := VG.Proof.RsaPss.lz_le bs
    by_cases hb : b = 0 <;> by_cases h : lz bs = bs.length <;> by_cases hx : x = 0 <;>
      simp only [hb, h, hx, ite_true, ite_false, Nat.add_right_cancel_iff] <;> (try split) <;> omega

theorem lzr_succ (w : Nat → Byte) (i : Nat) :
    lzr w (i + 1) = if lzr w i = i then (if w i = 0 then i + 1 else i) else lzr w i := by
  have := lz_append ((List.range i).map w) (w i)
  rw [List.length_map, List.length_range] at this
  rw [lzr, List.range_succ, List.map_append, List.map_singleton, this, lzr]

theorem lzr_le (w : Nat → Byte) (i : Nat) : lzr w i ≤ i := by
  have := VG.Proof.RsaPss.lz_le ((List.range i).map w); simpa [lzr] using this

/-- `(b - 1) >>> 63`: 1 if `b = 0`, 0 if not. -/
theorem isz_eq (b : Byte) : (b.setWidth 64 - BitVec.ofNat 64 1) >>> 63 = if b = 0 then 1#64 else 0#64 := by
  have hb := b.isLt
  have e : b = BitVec.ofNat 8 b.toNat := (BitVec.ofNat_toNat _ b).trans (BitVec.setWidth_eq _) |>.symm
  generalize b.toNat = n at hb e
  subst e
  revert n; decide +kernel

/-- What the scan keeps after `i` bytes: `r7` all ones while every byte so
far is zero, `pos` and `val` once one is not. -/
structure ScanI (w : Nat → Byte) (S : Addr) (lN i : Nat) (u : State) : Prop where
  a1 : u.gpr .a1 = off S (lN + i)
  a3 : u.gpr .a3 = BitVec.ofNat 64 i
  a4 : u.gpr .a4 = if lzr w i = i then BitVec.allOnes 64 else 0#64
  a5 : u.gpr .a5 = BitVec.ofNat 64 (if lzr w i < i then lzr w i else 0)
  a6 : u.gpr .a6 = (if lzr w i < i then w (lzr w i) else 0).setWidth 64

theorem scan_step {w : Nat → Byte} {S : Addr} {lN i : Nat} {u u' : State} (I : ScanI w S lN i u)
    (hb : (u'.gpr .a7) = (w i).setWidth 64)
    (h11 : u'.gpr .t1 = (u'.gpr .a7 - BitVec.ofNat 64 1) >>> 63)
    (h12 : u'.gpr .t2 = (u'.gpr .t1 - BitVec.ofNat 64 1) &&& u.gpr .a4)
    (h8 : u'.gpr .a5 = u.gpr .a5 ||| (u.gpr .a3 &&& u'.gpr .t2))
    (h9 : u'.gpr .a6 = u.gpr .a6 ||| (u'.gpr .a7 &&& u'.gpr .t2))
    (h7 : u'.gpr .a4 = u.gpr .a4 &&& (BitVec.ofNat 64 0 - u'.gpr .t1))
    (h4 : u'.gpr .a1 = u.gpr .a1 + BitVec.ofNat 64 1) (h6 : u'.gpr .a3 = u.gpr .a3 + BitVec.ofNat 64 1) :
    ScanI w S lN (i + 1) u' := by
  have hz := isz_eq (w i)
  rw [← hb] at hz
  rw [hz] at h11
  have hl := lzr_le w i
  have r4' : u'.gpr .a1 = off S (lN + (i + 1)) := by rw [h4, I.a1]; exact off_off _ _ _
  have r6' : u'.gpr .a3 = BitVec.ofNat 64 (i + 1) := by rw [h6, I.a3, BitVec.ofNat_add]
  by_cases e : lzr w i = i
  · have I7 := I.a4; have I8 := I.a5; have I9 := I.a6
    rw [ifp e] at I7
    rw [ifn (by omega)] at I8 I9
    by_cases z : w i = 0
    · rw [ifp z] at h11
      have h12' : u'.gpr .t2 = 0#64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifp z]
      · rw [ifp rfl, h7, I7, h11]; rfl
      · rw [ifn (by omega), h8, I8, h12', BitVec.and_zero, BitVec.or_zero]
      · rw [ifn (by omega), h9, I9, h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifn z] at h11
      have h12' : u'.gpr .t2 = BitVec.allOnes 64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifn z]
      · rw [ifn (by omega), h7, I7, h11]; rfl
      · rw [ifp (by omega), h8, I8, h12', BitVec.and_allOnes, I.a3]; simp
      · rw [ifp (by omega), h9, I9, h12', BitVec.and_allOnes, hb, ← e]; simp
  · have I7 := I.a4
    rw [ifn e] at I7
    have h12' : u'.gpr .t2 = 0#64 := by rw [h12, I7, BitVec.and_zero]
    refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifn e]
    · rw [ifn (by omega), h7, I7, BitVec.zero_and]
    · rw [ifp (by omega), h8, I.a5, ifp (by omega), h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifp (by omega), h9, I.a6, ifp (by omega), h12', BitVec.and_zero, BitVec.or_zero]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- The scan of `DB`'s `dbLen` bytes, `w`, at `S + lo`. -/
theorem scan_ok {t : State} (h : Base Sp (vP D) s t) {w : Nat → Byte}
    (hw : ∀ j < dN, view t.mem (Sp s) (lN + j) = w j) :
    WP isa scan t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      Only [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3] t t' ∧
      t'.gpr .a5 = BitVec.ofNat 64 (if lzr w dN < dN then lzr w dN else 0) ∧
      t'.gpr .a6 = (if lzr w dN < dN then w (lzr w dN) else 0).setWidth 64 := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hl := L.l1; have hd1 := L.d1
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (imm := 0) (by decide) fun t₃ o₃ e₃ =>
    wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ => wp_subi (imm := 1) fun t₅ o₅ e₅ =>
    wp_li (imm := 0) (by decide) fun t₆ o₆ e₆ => wp_li (imm := 0) (by decide) fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.a1, .a2, .a3, .a4, .a5, .a6] t t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have I0 : ScanI w (Sp s) lN 0 t₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁, h.s0, h.plo, L.hlo]; rfl
    · rw [o₇.get .a3, o₆.get .a3, o₅.get .a3, o₄.get .a3, e₃]
    · rw [o₇.get .a4, o₆.get .a4, e₅, e₄]; rfl
    · rw [o₇.get .a5, e₆]; rfl
    · rw [e₇]; rfl
  refine WP.mono (wp_countdown (cnt := .a2) (N := dN) (by omega) (by omega)
    (fun i u => ScanI w (Sp s) lN i u ∧ Only [.t3, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2] t₇ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, o₁.get .s4, h.pdb,
      L.hdb]))
    fun u ⟨I, o⟩ => ?_
  · intro i hi u ⟨I, o⟩ hc
    simp only [scanBody, List.cons_append, List.nil_append]
    refine wp_lbu (a := off (Sp s) (lN + i)) (by rw [I.a1, BitVec.add_zero])
      (by rw [o.rd, o.wr, k₇.rd, k₇.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi (imm := 1) fun u₂ p₂ f₂ => wp_srl fun u₃ p₃ f₃ => wp_subi (imm := 1) fun u₄ p₄ f₄ =>
      wp_and fun u₅ p₅ f₅ => wp_and fun u₆ p₆ f₆ => wp_or fun u₇ p₇ f₇ => wp_and fun u₈ p₈ f₈ =>
      wp_or fun u₉ p₉ f₉ => wp_li (imm := 0) (by decide) fun u₁₀ p₁₀ f₁₀ => wp_sub fun u₁₁ p₁₁ f₁₁ =>
      wp_and fun u₁₂ p₁₂ f₁₂ => wp_addi (imm := 1) fun u₁₃ p₁₃ f₁₃ => wp_addi (imm := 1) fun u₁₄ p₁₄ f₁₄ =>
      wp_subi (imm := 1) fun u₁₅ p₁₅ f₁₅ => wp_nil ?_
    have q : Only [.a7, .t1, .t2, .t3, .a5, .a6, .a4, .a1, .a3, .a2] u u₁₅ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans
        (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))))))))))).mono
    have v₁ : u₁₅.gpr .a7 = (w i).setWidth 64 := by
      rw [p₁₅.get .a7, p₁₄.get .a7, p₁₃.get .a7, p₁₂.get .a7, p₁₁.get .a7, p₁₀.get .a7,
        p₉.get .a7, p₈.get .a7, p₇.get .a7, p₆.get .a7, p₅.get .a7, p₄.get .a7, p₃.get .a7, p₂.get .a7, f₁,
        o.mem, k₇.mem, ← hw i hi]; rfl
    have p₁' : ∀ r ∈ [Reg.a1, .a2, .a3, .a4, .a5, .a6], u₁.gpr r = u.gpr r := fun r hr =>
      p₁.get r (by revert r; decide)
    refine ⟨⟨scan_step I v₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩ <;>
      simp (disch := decide) only [p₁₅.gpr, p₁₄.gpr, p₁₃.gpr, p₁₂.gpr, p₁₁.gpr, p₁₀.gpr, p₉.gpr, p₈.gpr, p₇.gpr,
        p₆.gpr, p₅.gpr, p₄.gpr, p₃.gpr, p₂.gpr, f₁₅, f₁₄, f₁₃, f₁₂, f₁₁, f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, f₂,
        p₁' _ (by decide : Reg.a1 ∈ _), p₁' _ (by decide : Reg.a2 ∈ _), p₁' _ (by decide : Reg.a3 ∈ _),
        p₁' _ (by decide : Reg.a4 ∈ _), p₁' _ (by decide : Reg.a5 ∈ _), p₁' _ (by decide : Reg.a6 ∈ _)]
  · have kk : Only [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3] t u := (k₇.trans o).mono
    exact ⟨h.only F kk, by rw [o.mem, k₇.mem], kk, I.a5, I.a6⟩

end

end VG.Proof.RsaPss.RISCV64
