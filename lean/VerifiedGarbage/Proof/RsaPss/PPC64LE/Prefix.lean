module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSASSA-PSS verification on PPC64LE: `M'`

Untrusted: everything here is checked by Lean. `prefix_ok`: `mPrefix n`
clears `n` bytes at `oY` and writes the digest `mHash` after 8 of them;
`salt_ok`: `copySalt` writes the last `salt_len` bytes of `DB` after it;
`copyDb_ok`: `copyDb` writes all of `DB` there. As views of our part of the
working space.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa zeroLoop copyLoop)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_wb sc_in sc_inR sc_inW sc_w rd_in ne_of_dis fx
  hiRegs kR bytes_entry zero_ok copy_ok)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_add wp_sub wp_mov wp_nil eval_nonzero
  ne_zero_iff)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- The digest. -/
abbrev mh (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r7) D

/-- The registers the writes of `M'` keep. -/
abbrev kpR : List Reg := Reg.r14 :: fx ++ hiRegs ++ ([.r8, .r24, .r25, .r26, .r27, .r28, .r29] : List Reg)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `mPrefix n`: `n` zeros at `oY`, and the digest after 8 of them. -/
theorem prefix_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {n : Nat} (hn : 8 ≤ n) (hn' : n ≤ 2048)
    {t : State} (h : Base Sp (vP D) s t) :
    WP isa (mPrefix H n) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ kpR, t'.gpr r = t.gpr r) ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 ≤ o ∧ o < oY + 8 + D then (mh D s).getD (o - (oY + 8)) 0
        else if oY ≤ o ∧ o < oY + n then 0 else view t.mem (Sp s) o := by
  have F := L.F
  have hD0 := L.D0; have hD64 := L.D64
  have hY : oY = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  refine WP.seq (WP.seq (wp_addi (h := by decide) fun t₁ o₁ e₁ => wp_li (by omega) fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_nil ?_))
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (Sp s) oY) (n := n) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (sc_w F (by rw [k₃.wr, h.wr]) (d := oY) (by omega))) fun t₄ ⟨hk₄, hm₄⟩ => ?_
  have K₄ : Keep [.r4, .r5, .r6] t t₄ := (k₃.keep.trans hk₄).mono
  have m₄ : t₄.mem = writeBytes t.mem (off (Sp s) oY) (List.replicate n 0) := by rw [hm₄, k₃.mem]
  have b₄ : Base Sp (vP D) s t₄ := h.wb F K₄ (by rw [List.length_replicate]; omega) m₄
  refine WP.seq (wp_mov fun t₅ o₅ e₅ => wp_addi (h := by decide) fun t₆ o₆ e₆ => wp_li (by rw [hD]; omega) fun t₇ o₇ e₇ =>
    wp_nil ?_)
  have k₇ : Only [.r4, .r5, .r6] t₄ t₇ := (o₅.trans (o₆.trans o₇)).mono
  have hdg : ∀ j < D, ∀ i < D, s.gpr .r7 + BitVec.ofNat 64 j ≠ off (Sp s) (oY + 8) + BitVec.ofNat 64 i :=
    fun j hj i hi => ne_of_dis L.dsc (Offset.contains_base _ (by omega) (by have := L.wd; omega))
      (by show (SC Sp s).Contains (off (off (Sp s) (oY + 8)) i) 1
          rw [off_off]; exact sc_in (o := oY + 8 + i) (n := 1) (by omega) _ (Region.contains_self _ _))
  refine WP.mono (copy_ok (q := s.gpr .r7) (p := off (Sp s) (oY + 8)) (n := D) hD0 (by omega)
    (by rw [o₇.get .r4, o₆.get .r4, e₅, b₄.pdig]) (by rw [o₇.get .r5, e₆, o₅.get .r14, b₄.r14])
    (by rw [e₇, hD]) (rd_in (by rw [k₇.rd, b₄.rd]) L.dr (by have := L.wd; omega) (Nat.le_refl _))
    (sc_w F (by rw [k₇.wr, b₄.wr]) (d := oY + 8) (by omega)) hdg) fun t' ⟨hk, hm⟩ => ?_
  have K : Keep [.r4, .r5, .r6, .r7] t₄ t' := (k₇.keep.trans hk).mono
  have hb : Spec.Rsa.bytesAt t₇.mem (s.gpr .r7) D = mh D s := by
    rw [k₇.mem]; exact bytes_entry b₄.mem L.dk L.dsc.symm (by omega)
  have m' : t'.mem = writeBytes t₄.mem (off (Sp s) (oY + 8)) (mh D s) := by rw [hm, hb, k₇.mem]
  refine ⟨b₄.wb F K (by rw [bytesAt_length]; omega) m', fun r hr => ?_, fun o ho => ?_⟩
  · rw [K.gpr r (by revert r; decide), K₄.gpr r (by revert r; decide)]
  · rw [m', view_wb _ _ (by rw [bytesAt_length]; omega) ho, bytesAt_length, m₄,
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
    (hb : b + n ≤ oRsa) (hab : a + n ≤ b ∨ b + n ≤ a) (h4 : t.gpr .r4 = off (Sp s) a)
    (h5 : t.gpr .r5 = off (Sp s) b) (h6 : t.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa copyLoop t fun t' => Base Sp (vP D) s t' ∧ Keep [.r7, .r4, .r5, .r6] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o =
        if b ≤ o ∧ o < b + n then view t.mem (Sp s) (a + (o - b)) else view t.mem (Sp s) o := by
  have F := L.F
  have hR : oRsa = 8192 := rfl
  refine WP.mono (copy_ok (q := off (Sp s) a) (p := off (Sp s) b) (n := n) hn (by omega) h4 h5 h6
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
theorem salt_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t)
    (hsl : (s.gpr .r10).toNat + 1 ≤ dN) :
    WP isa (copySalt H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ kpR, t'.gpr r = t.gpr r) ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 + D ≤ o ∧ o < oY + 8 + D + (s.gpr .r10).toNat then
        view t.mem (Sp s) (lN + dN - (s.gpr .r10).toNat + (o - (oY + 8 + D))) else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  generalize hS : (s.gpr .r10).toNat = sl at hsl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_sub fun t₃ o₃ e₃ =>
    wp_addi (h := by rw [hD]; unfold oY; omega) fun t₄ o₄ e₄ => wp_mov fun t₅ o₅ e₅ => wp_nil ?_)
  have k₅ : Only [.r4, .r5, .r6] t t₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have b₅ := h.only F k₅
  have g6 : t₅.gpr .r6 = BitVec.ofNat 64 sl := by
    rw [e₅, o₄.get .r19, o₃.get .r19, o₂.get .r19, o₁.get .r19, h.psl, ← ofNat_toNat (s.gpr .r10), hS]
  have g4 : t₅.gpr .r4 = off (Sp s) (lN + dN - sl) := by
    rw [o₅.get .r4, o₄.get .r4, e₃, e₂, e₁, o₂.get .r19, o₁.get .r19, h.psl, o₁.get .r21, h.pdb, L.hdb,
      h.r14, h.plo, L.hlo, ← ofNat_toNat (s.gpr .r10), hS]
    exact (congrArg (· - BitVec.ofNat 64 sl) (off_off (Sp s) lN dN)).trans (off_sub _ (by omega) (by omega))
  have g5 : t₅.gpr .r5 = off (Sp s) (oY + 8 + D) := by
    rw [o₅.get .r5, e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14, hD]
  refine WP.ite _ (eval_nonzero _ _) (fun hc => ?_) (fun hc => ?_)
  · have hs0 : sl ≠ 0 := by intro h0; rw [g6, ne_zero_iff, h0] at hc; simp at hc
    refine WP.mono (copyIn_ok L b₅ (a := lN + dN - sl) (b := oY + 8 + D) (n := sl) (by omega) (by omega)
      (by omega) (.inl (by omega)) g4 g5 g6) fun t' ⟨b', hk', v'⟩ => ⟨b', fun r hr => ?_, fun o ho => ?_⟩
    · rw [hk'.gpr r (by revert r; decide), k₅.gpr r (by revert r; decide)]
    · rw [v' o ho, k₅.mem]
  · have hs0 : sl = 0 := by
      rw [g6, ne_zero_iff] at hc; simp only [BitVec.toNat_ofNat, ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hc; omega
    refine wp_nil ⟨b₅, fun r hr => k₅.gpr r (by revert r; decide), fun o ho => ?_⟩
    rw [ifn (by omega), k₅.mem]

/-- `copyDb`: `DB` after `mHash`. -/
theorem copyDb_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (copyDb H) t fun t' => Base Sp (vP D) s t' ∧ (∀ r ∈ kpR, t'.gpr r = t.gpr r) ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oY + 8 + D ≤ o ∧ o < oY + 8 + D + dN then
        view t.mem (Sp s) (lN + (o - (oY + 8 + D))) else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hD64 := L.D64; have hd1 := L.d1
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  refine WP.seq (wp_add fun t₁ o₁ e₁ => wp_addi (h := by rw [hD]; unfold oY; omega) fun t₂ o₂ e₂ =>
    wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (copyIn_ok L (h.only F k₃) (a := lN) (b := oY + 8 + D) (n := dN) (by omega) (by omega)
    (by omega) (.inl (by omega)) (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14, h.plo, L.hlo])
    (by rw [o₃.get .r5, e₂, o₁.get .r14, h.r14, hD]) (by rw [e₃, o₂.get .r21, o₁.get .r21, h.pdb, L.hdb]))
    fun t' ⟨b', hk', v'⟩ => ⟨b', fun r hr => ?_, fun o ho => ?_⟩
  · rw [hk'.gpr r (by revert r; decide), k₃.gpr r (by revert r; decide)]
  · rw [v' o ho, k₃.mem]

end

end VG.Proof.RsaPss.PPC64LE
