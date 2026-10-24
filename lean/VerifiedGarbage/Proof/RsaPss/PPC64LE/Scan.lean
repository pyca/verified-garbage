module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE

/-!
# RSASSA-PSS verification on PPC64LE: the first nonzero byte of `DB`

Untrusted: everything here is checked by Lean. `scan_ok`: `scan` finds, in
the `dbLen` bytes of `DB` (`w`), the number `z` of leading zero bytes
(`Proof.RsaPss.lz`) without branching on them: `pos` (`r8`) is `z` and `val`
(`r9`) the byte there if `z < dbLen`, both 0 if not. The invariant after `i`
bytes is that of their leading zeros (`lzr w i`, `lzr_succ`), with `r7` all
ones while it is `i`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view sc_in sc_inR fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_and wp_or wp_lsr
  wp_lbz wp_nil wp_countdown)
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
  r4 : u.gpr .r4 = off S (lN + i)
  r6 : u.gpr .r6 = BitVec.ofNat 64 i
  r7 : u.gpr .r7 = if lzr w i = i then BitVec.allOnes 64 else 0#64
  r8 : u.gpr .r8 = BitVec.ofNat 64 (if lzr w i < i then lzr w i else 0)
  r9 : u.gpr .r9 = (if lzr w i < i then w (lzr w i) else 0).setWidth 64

theorem scan_step {w : Nat → Byte} {S : Addr} {lN i : Nat} {u u' : State} (I : ScanI w S lN i u)
    (hb : (u'.gpr .r10) = (w i).setWidth 64)
    (h11 : u'.gpr .r11 = (u'.gpr .r10 - BitVec.ofNat 64 1) >>> 63)
    (h12 : u'.gpr .r12 = (u'.gpr .r11 - BitVec.ofNat 64 1) &&& u.gpr .r7)
    (h8 : u'.gpr .r8 = u.gpr .r8 ||| (u.gpr .r6 &&& u'.gpr .r12))
    (h9 : u'.gpr .r9 = u.gpr .r9 ||| (u'.gpr .r10 &&& u'.gpr .r12))
    (h7 : u'.gpr .r7 = u.gpr .r7 &&& (BitVec.ofNat 64 0 - u'.gpr .r11))
    (h4 : u'.gpr .r4 = u.gpr .r4 + BitVec.ofNat 64 1) (h6 : u'.gpr .r6 = u.gpr .r6 + BitVec.ofNat 64 1) :
    ScanI w S lN (i + 1) u' := by
  have hz := isz_eq (w i)
  rw [← hb] at hz
  rw [hz] at h11
  have hl := lzr_le w i
  have r4' : u'.gpr .r4 = off S (lN + (i + 1)) := by rw [h4, I.r4]; exact off_off _ _ _
  have r6' : u'.gpr .r6 = BitVec.ofNat 64 (i + 1) := by rw [h6, I.r6, BitVec.ofNat_add]
  by_cases e : lzr w i = i
  · have I7 := I.r7; have I8 := I.r8; have I9 := I.r9
    rw [ifp e] at I7
    rw [ifn (by omega)] at I8 I9
    by_cases z : w i = 0
    · rw [ifp z] at h11
      have h12' : u'.gpr .r12 = 0#64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifp z]
      · rw [ifp rfl, h7, I7, h11]; rfl
      · rw [ifn (by omega), h8, I8, h12', BitVec.and_zero, BitVec.or_zero]
      · rw [ifn (by omega), h9, I9, h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifn z] at h11
      have h12' : u'.gpr .r12 = BitVec.allOnes 64 := by rw [h12, h11, I7]; rfl
      refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifp e, ifn z]
      · rw [ifn (by omega), h7, I7, h11]; rfl
      · rw [ifp (by omega), h8, I8, h12', BitVec.and_allOnes, I.r6]; simp
      · rw [ifp (by omega), h9, I9, h12', BitVec.and_allOnes, hb, ← e]; simp
  · have I7 := I.r7
    rw [ifn e] at I7
    have h12' : u'.gpr .r12 = 0#64 := by rw [h12, I7, BitVec.and_zero]
    refine ⟨r4', r6', ?_, ?_, ?_⟩ <;> rw [lzr_succ, ifn e]
    · rw [ifn (by omega), h7, I7, BitVec.zero_and]
    · rw [ifp (by omega), h8, I.r8, ifp (by omega), h12', BitVec.and_zero, BitVec.or_zero]
    · rw [ifp (by omega), h9, I.r9, ifp (by omega), h12', BitVec.and_zero, BitVec.or_zero]

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- The scan of `DB`'s `dbLen` bytes, `w`, at `S + lo`. -/
theorem scan_ok {t : State} (h : Base Sp (vP D) s t) {w : Nat → Byte}
    (hw : ∀ j < dN, view t.mem (Sp s) (lN + j) = w j) :
    WP isa scan t fun t' => Base Sp (vP D) s t' ∧ t'.mem = t.mem ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ ([.r24, .r25, .r26, .r27, .r28, .r29] : List Reg), t'.gpr r = t.gpr r) ∧
      t'.gpr .r8 = BitVec.ofNat 64 (if lzr w dN < dN then lzr w dN else 0) ∧
      t'.gpr .r9 = (if lzr w dN < dN then w (lzr w dN) else 0).setWidth 64 := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hl := L.l1; have hd1 := L.d1
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_li (by decide) fun t₄ o₄ e₄ => wp_subi fun t₅ o₅ e₅ => wp_li (by decide) fun t₆ o₆ e₆ =>
    wp_li (by decide) fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r4, .r5, .r6, .r7, .r8, .r9] t t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have I0 : ScanI w (Sp s) lN 0 t₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, h.plo, L.hlo]; rfl
    · rw [o₇.get .r6, o₆.get .r6, o₅.get .r6, o₄.get .r6, e₃]
    · rw [o₇.get .r7, o₆.get .r7, e₅, e₄]; rfl
    · rw [o₇.get .r8, e₆]; rfl
    · rw [e₇]; rfl
  refine WP.mono (wp_countdown (cnt := .r5) (N := dN) (by omega) (by omega)
    (fun i u => ScanI w (Sp s) lN i u ∧ Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t₇ u) ?_
    ⟨I0, Only.refl _ _⟩ (by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, o₁.get .r21, h.pdb, L.hdb]))
    fun u ⟨I, o⟩ => ?_
  · intro i hi u ⟨I, o⟩ hc
    refine wp_lbz (a := off (Sp s) (lN + i)) (by rw [I.r4, BitVec.add_zero])
      (by rw [o.rd, o.wr, k₇.rd, k₇.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun u₁ p₁ f₁ => ?_
    refine wp_subi fun u₂ p₂ f₂ => wp_lsr fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_and fun u₅ p₅ f₅ =>
      wp_and fun u₆ p₆ f₆ => wp_or fun u₇ p₇ f₇ => wp_and fun u₈ p₈ f₈ => wp_or fun u₉ p₉ f₉ =>
      wp_li (by decide) fun u₁₀ p₁₀ f₁₀ => wp_sub fun u₁₁ p₁₁ f₁₁ => wp_and fun u₁₂ p₁₂ f₁₂ =>
      wp_addi fun u₁₃ p₁₃ f₁₃ => wp_addi fun u₁₄ p₁₄ f₁₄ => wp_subi fun u₁₅ p₁₅ f₁₅ => wp_nil ?_
    have q : Only [.r10, .r11, .r12, .r3, .r8, .r9, .r7, .r4, .r6, .r5] u u₁₅ :=
      (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans (p₈.trans (p₉.trans (p₁₀.trans (p₁₁.trans (p₁₂.trans (p₁₃.trans (p₁₄.trans p₁₅)))))))))))))).mono
    have v₁ : u₁₅.gpr .r10 = (w i).setWidth 64 := by
      rw [p₁₅.get .r10, p₁₄.get .r10, p₁₃.get .r10, p₁₂.get .r10, p₁₁.get .r10, p₁₀.get .r10,
        p₉.get .r10, p₈.get .r10, p₇.get .r10, p₆.get .r10, p₅.get .r10, p₄.get .r10, p₃.get .r10, p₂.get .r10, f₁,
        o.mem, k₇.mem, ← hw i hi]; rfl
    have p₁' : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9], u₁.gpr r = u.gpr r := fun r hr => p₁.get r (by revert r; decide)
    refine ⟨⟨scan_step I v₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_, (o.trans q).mono⟩, ?_⟩ <;>
      simp (disch := decide) only [p₁₅.gpr, p₁₄.gpr, p₁₃.gpr, p₁₂.gpr, p₁₁.gpr, p₁₀.gpr, p₉.gpr, p₈.gpr, p₇.gpr, p₆.gpr, p₅.gpr, p₄.gpr, p₃.gpr, p₂.gpr, f₁₅, f₁₄, f₁₃, f₁₂, f₁₁, f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, f₂, p₁' _ (by decide : Reg.r4 ∈ _), p₁' _ (by decide : Reg.r5 ∈ _), p₁' _ (by decide : Reg.r6 ∈ _),
        p₁' _ (by decide : Reg.r7 ∈ _), p₁' _ (by decide : Reg.r8 ∈ _), p₁' _ (by decide : Reg.r9 ∈ _)]
  · have kk : Only [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] t u := (k₇.trans o).mono
    refine ⟨h.only F kk, by rw [o.mem, k₇.mem], fun r hr => ?_, I.r8, I.r9⟩
    exact kk.gpr r (by revert r; decide)

end

end VG.Proof.RsaPss.PPC64LE
