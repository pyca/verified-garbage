module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Finish
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Unmask
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Scan
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Check
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix

/-!
# RSASSA-PSS verification on PPC64LE: after the public operation

Untrusted: everything here is checked by Lean. `post_ok`: from `EM` in its
place (the view `V`), the code after the call returns 1 exactly when `Res`
holds: the accumulator of the checks (`accR`: `0xbc`, the leading byte, the
top bits, the delimiter and, for a given salt length, the salt's length) is
zero and `H` is the hash of `M'` (`mR`), from `DB` unmasked (`dbV`), the first
nonzero byte of `DB` (`lzr`) and the salt's length.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa mgfXor)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil eval_zero)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaOaep (mixV srcB)

section
variable (Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (D lN dN : Nat) (c : Byte) (k : Nat) (mh : List Byte)
  (any saltLen : BitVec 64)

/-- `EM` after `acc0`. -/
def v1 : Nat → Byte := fun o => if o = k - 1 then accB V lN c k else V o

/-- `DB`'s bytes, unmasked. -/
def wR (j : Nat) : Byte := dbV Gs (v1 V lN c k) lN dN D c (lN + j)

/-- The position of the first nonzero byte of `DB`, and its value. -/
def posR : Nat := if lzr (wR Gs V D lN dN c k) dN < dN then lzr (wR Gs V D lN dN c k) dN else 0
def valR : Byte := if lzr (wR Gs V D lN dN c k) dN < dN then wR Gs V D lN dN c k (lzr (wR Gs V D lN dN c k) dN) else 0

/-- The salt's length. -/
def slR : Nat := dN - posR Gs V D lN dN c k - 1

/-- The accumulator. -/
def accR : BitVec 64 :=
  accW (accB V lN c k) ((valR Gs V D lN dN c k).setWidth 64) (slR Gs V D lN dN c k) any saltLen

/-- `M'`. -/
def mR : List Byte :=
  if any = 0 then mFix (dbV Gs (v1 V lN c k) lN dN D c) mh lN dN saltLen.toNat
  else mAny (dbV Gs (v1 V lN c k) lN dN D c) mh lN dN (posR Gs V D lN dN c k) (slR Gs V D lN dN c k)

/-- What makes the result 1. -/
def Res : Prop :=
  accR Gs V D lN dN c k any saltLen = 0#64 ∧
    ∀ i < D, V (lN + dN + i) = (Gs.hash (mR Gs V D lN dN c k mh any saltLen)).getD i 0

instance : Decidable (Res Gs V D lN dN c k mh any saltLen) := by unfold Res; infer_instance

end

theorem dbV_congr {Gs : Spec.Mgf1.Hash} {V V' : Nat → Byte} {lN dN D : Nat} {c : Byte} (hf : lN + dN + D ≤ 1024)
    (h : ∀ o < 1024, V o = V' o) {o : Nat} (ho : o < 1024) : dbV Gs V lN dN D c o = dbV Gs V' lN dN D c o := by
  have hs : srcB V (lN + dN) D = srcB V' (lN + dN) D :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; omega_arith)
  simp only [dbV, mixV, hs, h o ho]

theorem xor1_lt (b : Byte) : ((b.setWidth 64) ^^^ 1#64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (byte_lt b) (by decide)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
include L hH

theorem post_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs) {t : State} (h : Base Sp (vP D) s t)
    (hfit : anyL s = 0 → (s.gpr .r10).toNat + 1 ≤ dN) :
    WP isa (.seq (.block acc0) (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block clearTop) (.seq scan
      (.seq (.block posCheck) (.seq lenCheck (finish H)))))))) t fun t' => Base Sp (vP D) s t' ∧
      t'.gpr .r3 = if Res Gs (view t.mem (Sp s)) D lN dN c (s.gpr .r4).toNat (mh D s) (anyL s) (s.gpr .r10)
        then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  generalize hK : (s.gpr .r4).toNat = k at hk hk2
  let V := view t.mem (Sp s)
  refine WP.seq (WP.mono (acc0_ok L h) fun t₁ ⟨b₁, g₁, v₁⟩ => ?_)
  rw [hK] at v₁
  refine unmask_ok L hH hD hGh hGl hGv b₁ fun t₂ b₂ v₂ => ?_
  have e₁ : ∀ o < 1024, view t₁.mem (Sp s) o = v1 V lN c k o := fun o ho => by rw [v₁ o (by omega_arith)]; rfl
  have W : ∀ o < 1024, view t₂.mem (Sp s) o = dbV Gs (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [v₂ o (by omega_arith), dbV_congr (by omega_arith) e₁ ho]
  refine WP.seq (WP.mono (scan_ok L b₂ (w := wR Gs V D lN dN c k) fun j hj => by rw [W _ (by omega_arith)]; rfl)
    fun t₃ ⟨b₃, m₃, g₃, x8, x9⟩ => ?_)
  have hpos : posR Gs V D lN dN c k < dN := by
    unfold posR; split <;> omega_arith
  have ha : view t₃.mem (Sp s) ((s.gpr .r4).toNat - 1) = accB V lN c k := by
    rw [hK, m₃, W _ (by omega_arith), dbV]
    simp only [mixV]
    rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifp rfl]
  refine check_ok L b₃ (a := accB V lN c k) (pos := posR Gs V D lN dN c k)
    (val := (valR Gs V D lN dN c k).setWidth 64) ha x8 hpos x9 fun t₄ b₄ m₄ g₄ x24 x25 => ?_
  have W₄ : ∀ o < 1024, view t₄.mem (Sp s) o = dbV Gs (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [m₄, m₃, W o ho]
  have vH : ∀ i < D, dbV Gs (v1 V lN c k) lN dN D c (lN + dN + i) = V (lN + dN + i) := fun i hi => by
    simp only [dbV, mixV]; rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifn (by omega_arith)]
  have hacc : (t₄.gpr .r24).toNat < 2 ^ 63 := by
    rw [x24, accW]
    refine or_lt (or_lt (byte_lt _) (xor1_lt _)) ?_
    split
    · rename_i h0
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
      have := hfit h0
      exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
    · decide
  have x24' : t₄.gpr .r24 = accR Gs V D lN dN c k (anyL s) (s.gpr .r10) := x24
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  all_goals have g20 : t₄.gpr .r20 = anyL s := by rw [g₄ _ (by decide), g₃ _ (by decide), b₂.pany]
  · have h0 : anyL s = 0 := by rw [g20] at hz; simpa using hz
    have hM : mFix (view t₄.mem (Sp s)) (mh D s) lN dN (s.gpr .r10).toNat =
        mR Gs V D lN dN c k (mh D s) (anyL s) (s.gpr .r10) := by
      rw [mR, ifp h0]
      have := hfit h0
      simp only [mFix]
      refine congrArg (_ ++ ·) (List.map_congr_left fun j hj => W₄ _ ?_)
      have := List.mem_range.mp hj; omega_arith
    refine WP.mono (fixed_ok L hH hD hGh b₄ (hfit h0) hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gs V D lN dN c k (mh D s) (anyL s) (s.gpr .r10)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]
  · have h0 : anyL s ≠ 0 := by rw [g20] at hz; simpa using hz
    have hM : mAny (view t₄.mem (Sp s)) (mh D s) lN dN (posR Gs V D lN dN c k) (slR Gs V D lN dN c k) =
        mR Gs V D lN dN c k (mh D s) (anyL s) (s.gpr .r10) := by
      rw [mR, ifn h0]
      simp only [mAny]
      refine congrArg (List.replicate 8 0 ++ mh D s ++ ·) (List.map_congr_left fun j hj => ?_)
      split
      · rw [W₄ _ (by omega_arith)]
      · rfl
    have hsl : slR Gs V D lN dN c k < dN := by unfold slR; omega_arith
    refine WP.mono (any_ok L hH hD hGh b₄ (pos := posR Gs V D lN dN c k) (sl := slR Gs V D lN dN c k)
      (by rw [g₄ _ (by decide), x8]; rfl) hpos x25 hsl hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gs V D lN dN c k (mh D s) (anyL s) (s.gpr .r10)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE
