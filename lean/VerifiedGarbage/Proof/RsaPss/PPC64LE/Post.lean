module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Finish
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Unmask
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Scan
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Check
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
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
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa Fns mgfXorT)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil eval_zero)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaOaep (mixV srcB)

section
variable (Gm Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (D lN dN : Nat) (c : Byte) (k : Nat) (mh : List Byte)
  (any saltLen : BitVec 64)

/-- `EM` after `acc0`. -/
def v1 : Nat → Byte := fun o => if o = k - 1 then accB V lN c k else V o

/-- `DB`'s bytes, unmasked. -/
def wR (j : Nat) : Byte := dbV Gm (v1 V lN c k) lN dN D c (lN + j)

/-- The position of the first nonzero byte of `DB`, and its value. -/
def posR : Nat := if lzr (wR Gm V D lN dN c k) dN < dN then lzr (wR Gm V D lN dN c k) dN else 0
def valR : Byte := if lzr (wR Gm V D lN dN c k) dN < dN then wR Gm V D lN dN c k (lzr (wR Gm V D lN dN c k) dN) else 0

/-- The salt's length. -/
def slR : Nat := dN - posR Gm V D lN dN c k - 1

/-- The accumulator. -/
def accR : BitVec 64 :=
  accW (accB V lN c k) ((valR Gm V D lN dN c k).setWidth 64) (slR Gm V D lN dN c k) any saltLen

/-- `M'`. -/
def mR : List Byte :=
  if any = 0 then mFix (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN saltLen.toNat
  else mAny (dbV Gm (v1 V lN c k) lN dN D c) mh lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k)

/-- What makes the result 1. -/
def Res : Prop :=
  accR Gm V D lN dN c k any saltLen = 0#64 ∧
    ∀ i < D, V (lN + dN + i) = (Gs.hash (mR Gm V D lN dN c k mh any saltLen)).getD i 0

instance : Decidable (Res Gm Gs V D lN dN c k mh any saltLen) := by unfold Res; infer_instance

end

theorem dbV_congr {Gm : Spec.Mgf1.Hash} {V V' : Nat → Byte} {lN dN D : Nat} {c : Byte} (hf : lN + dN + D ≤ 1024)
    (h : ∀ o < 1024, V o = V' o) {o : Nat} (ho : o < 1024) : dbV Gm V lN dN D c o = dbV Gm V' lN dN D c o := by
  have hs : srcB V (lN + dN) D = srcB V' (lN + dN) D :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; omega_arith)
  simp only [dbV, mixV, hs, h o ho]

theorem xor1_lt (b : Byte) : ((b.setWidth 64) ^^^ 1#64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (byte_lt b) (by decide)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) {H : Hash} (hH : HashOK H)
include L hH

theorem post_ok (hD : H.D = D) {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x)
    {G : Hash} (hG : HashOK G) {g : Fns} {pg : Addr} (Tg : TabS G g gArg Sp s pg) {Gm : Spec.Mgf1.Hash}
    (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
    {cn dn : String} {cc dc : Prog isa} {f : MdFns} {p : Addr} (T : MdTabS H cn cc dn dc f hArg Sp s p)
    {P : Params} {md : Md P.B P.N P.L} (ok : CtOK P md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv D)
    (hN : H.N = P.N) (hB : H.B = P.B) {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ dN) :
    WP isa (.seq (.block acc0) (.seq (.block (dbArgs H)) (.seq (mgfXorT g gArg) (.seq (.block clearTop) (.seq scan
      (.seq (.block posCheck) (.seq lenCheck (finish H P f)))))))) t fun t' => Base Sp (vP D) s t' ∧
      t'.gpr .r3 = if Res Gm Gs (view t.mem (Sp s)) D lN dN c (s.gpr .r4).toNat (mh D s) (anyL s) (stackArg s 0)
        then 1#64 else 0#64 := by
  have F := L.F
  obtain ⟨hE, hSt, hDg, hCt, hW, hRs⟩ := offs
  have hk := L.hk; have hk2 := L.k2; have hD0 := L.D0; have hD64 := L.D64; have hd1 := L.d1
  generalize hK : (s.gpr .r4).toNat = k at hk hk2
  let V := view t.mem (Sp s)
  refine WP.seq (WP.mono_syms (acc0_ok L h) fun t₁ ⟨b₁, g₁, v₁⟩ y₁ => ?_)
  rw [hK] at v₁
  refine unmask_ok L hD hG Tg hGmh hGml hGmv b₁ (y₁.trans sy) fun t₂ b₂ y₂ v₂ => ?_
  have e₁ : ∀ o < 1024, view t₁.mem (Sp s) o = v1 V lN c k o := fun o ho => by rw [v₁ o (by omega_arith)]; rfl
  have W : ∀ o < 1024, view t₂.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [v₂ o (by omega_arith), dbV_congr (by omega_arith) e₁ ho]
  refine WP.seq (WP.mono_syms (scan_ok L b₂ (w := wR Gm V D lN dN c k) fun j hj => by rw [W _ (by omega_arith)]; rfl)
    fun t₃ ⟨b₃, m₃, g₃, x8, x9⟩ y₃ => ?_)
  have hpos : posR Gm V D lN dN c k < dN := by
    unfold posR; split <;> omega_arith
  have ha : view t₃.mem (Sp s) ((s.gpr .r4).toNat - 1) = accB V lN c k := by
    rw [hK, m₃, W _ (by omega_arith), dbV]
    simp only [mixV]
    rw [ifn (by omega_arith), ifn (by omega_arith), v1, ifp rfl]
  refine check_ok L b₃ (a := accB V lN c k) (pos := posR Gm V D lN dN c k)
    (val := (valR Gm V D lN dN c k).setWidth 64) ha x8 hpos x9 fun t₄ b₄ m₄ g₄ x24 x25 y₄ => ?_
  have sy₄ : t₄.syms = s.syms := y₄.trans (y₃.trans y₂)
  have W₄ : ∀ o < 1024, view t₄.mem (Sp s) o = dbV Gm (v1 V lN c k) lN dN D c o := fun o ho => by
    rw [m₄, m₃, W o ho]
  have vH : ∀ i < D, dbV Gm (v1 V lN c k) lN dN D c (lN + dN + i) = V (lN + dN + i) := fun i hi => by
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
  have x24' : t₄.gpr .r24 = accR Gm V D lN dN c k (anyL s) (stackArg s 0) := x24
  refine WP.ite _ (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  all_goals have g20 : t₄.gpr .r20 = anyL s := by rw [g₄ _ (by decide), g₃ _ (by decide), b₂.pany]
  · have h0 : anyL s = 0 := by rw [g20] at hz; simpa using hz
    have hM : mFix (view t₄.mem (Sp s)) (mh D s) lN dN (stackArg s 0).toNat =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifp h0]
      have := hfit h0
      simp only [mFix]
      refine congrArg (_ ++ ·) (List.map_congr_left fun j hj => W₄ _ ?_)
      have := List.mem_range.mp hj; omega_arith
    refine WP.mono (fixed_ok L hH T hD hGh b₄ sy₄ (hfit h0) hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]
  · have h0 : anyL s ≠ 0 := by rw [g20] at hz; simpa using hz
    have hM : mAny (view t₄.mem (Sp s)) (mh D s) lN dN (posR Gm V D lN dN c k) (slR Gm V D lN dN c k) =
        mR Gm V D lN dN c k (mh D s) (anyL s) (stackArg s 0) := by
      rw [mR, ifn h0]
      simp only [mAny]
      refine congrArg (List.replicate 8 0 ++ mh D s ++ ·) (List.map_congr_left fun j hj => ?_)
      split
      · rw [W₄ _ (by omega_arith)]
      · rfl
    have hsl : slR Gm V D lN dN c k + posR Gm V D lN dN c k + 1 = dN := by unfold slR; omega_arith
    refine WP.mono (any_ok L hH T hD hGh ok hl hN hB b₄ sy₄ (pos := posR Gm V D lN dN c k)
      (sl := slR Gm V D lN dN c k) (by rw [g₄ _ (by decide), x8]; rfl) hpos x25 hsl hacc) fun t' ⟨b', r'⟩ => ⟨b', ?_⟩
    rw [r', hM]
    by_cases e : Res Gm Gs V D lN dN c k (mh D s) (anyL s) (stackArg s 0)
    · rw [ifp e, ifp ⟨by rw [x24']; exact e.1, fun i hi => by rw [W₄ _ (by omega_arith), vH i hi]; exact e.2 i hi⟩]
    · rw [ifn e, ifn fun h' => e ⟨by rw [← x24']; exact h'.1, fun i hi => by
        rw [← vH i hi, ← W₄ _ (by omega_arith)]; exact h'.2 i hi⟩]

end

end VG.Proof.RsaPss.PPC64LE
