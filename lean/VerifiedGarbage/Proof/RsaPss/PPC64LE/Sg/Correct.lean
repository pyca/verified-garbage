module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Blocks
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Spec
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPss.EncBytes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfT
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Tab
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Fixed
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Checks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.PrivCall
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Frame
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry

/-! ### `RsaPss.PPC64LE.Sg.Enc`, which only this module used -/

section

/-! ### `RsaPss.PPC64LE.Sg.EnView`, which only this module used -/

section

/-!
# RSASSA-PSS signing on PPC64LE: the bytes written, as views

Untrusted: everything here is checked by Lean. Pure facts about the views of
our part of `scratch` (`view`): `M'`'s bytes after `mPrime` (`mPrime_bytes`);
`EM` before masking (`emPre`) after `clearEm`, `putSalt` and `putH`
(`emPre_of`); and `EM` after MGF1's mask and `clearTop` is `emT`
(`emT_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Proof.RsaOaep.PPC64LE (off off_off view view_wb view_w8)
open VG.Proof.RsaOaep (mixV range_ext)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss (getD_app)

theorem getD_rep0 (n i : Nat) : (List.replicate n (0 : Byte)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl

theorem bytesAt_eq_view (m : Mem) (S : Addr) (d n : Nat) :
    Spec.Rsa.bytesAt m (off S d) n = (List.range n).map fun i => view m S (d + i) := by
  simp only [Spec.Rsa.bytesAt, view]
  exact List.map_congr_left fun i _ => by rw [← off_off]

/-- `M'` after `mPrime`. -/
theorem mPrime_bytes (m : Mem) (S : Addr) {D : Nat} (dig salt : List Byte) (hd : dig.length = D)
    (hl : oY + 8 + D + salt.length ≤ oRsa) :
    Spec.Rsa.bytesAt (writeBytes (writeBytes (writeBytes m (off S oY) (List.replicate 8 0)) (off S (oY + 8)) dig)
      (off S (oY + 8 + D)) salt) (off S oY) (8 + D + salt.length) = Spec.RsaPss.zeros 8 ++ dig ++ salt := by
  rw [bytesAt_eq_view]
  refine range_ext (by simp [Spec.RsaPss.zeros, hd]; omega_using []) fun i hi => ?_
  rw [view_wb _ _ (by omega_using [hl]) (by omega_using [hl, hi]), view_wb _ _ (by rw [hd]; omega_using [hl]) (by omega_using [hl, hi]),
    view_wb _ _ (by simp; omega_using [hl]) (by omega_using [hl, hi]), getD_app, getD_app]
  simp only [List.length_replicate, hd, Spec.RsaPss.zeros, List.length_append, getD_rep0]
  by_cases h1 : i < 8
  · rw [ifn (by omega_using [h1]), ifn (by omega_using [h1]), ifp ⟨by omega_using [], by omega_using [h1]⟩, ifp (by omega_using [h1]), ifp h1]
  by_cases h2 : i < 8 + D
  · rw [ifn (by omega_using [h2]), ifp ⟨by omega_using [h1], by omega_using [h2]⟩, ifp (by omega_using [h2]), ifn h1, show oY + i - (oY + 8) = i - 8 by omega_using []]
  · rw [ifp ⟨by omega_using [h2], by omega_using [hi]⟩, ifn (by omega_using [h2]), show oY + i - (oY + 8 + D) = i - (8 + D) by omega_using [],
      show i - (8 + D) = i - 8 - D by omega_using []]

/-- `EM` before masking, at offset `o < k`: zeros, `0x01`, the salt, `H` and
`0xbc`. -/
def emPre (k D sl : Nat) (salt h : List Byte) (o : Nat) : Byte :=
  if o = k - 1 then 0xbc else if k - D - 1 ≤ o then h.getD (o - (k - D - 1)) 0
  else if k - sl - D - 1 ≤ o then salt.getD (o - (k - sl - D - 1)) 0 else if o = k - sl - D - 2 then 1 else 0

/-- `EM` before masking, from the writes of `clearEm`, `putSalt` and `putH`. -/
theorem emPre_of {m m₁ m₂ m₃ : Mem} {S : Addr} {k D sl : Nat} {salt h : List Byte} (hs : salt.length = sl)
    (hh : h.length = D) (hk : k ≤ 1024) (hfit : sl + D + 2 ≤ k)
    (h₁ : m₁ = writeBytes m (off S oEm) (List.replicate k 0))
    (h₂ : m₂ = writeBytes (m₁.writeW (off S (oEm + (k - sl - D - 2))) (1 : Byte)) (off S (oEm + (k - sl - D - 1)))
      salt)
    (h₃ : m₃ = (writeBytes m₂ (off S (oEm + (k - D - 1))) h).writeW (off S (oEm + (k - 1))) (0xbc : Byte))
    {o : Nat} (ho : o < k) : view m₃ S o = emPre k D sl salt h o := by
  have hE : oEm = 0 := rfl
  have hR : oRsa = 8192 := rfl
  subst h₁ h₂ h₃
  rw [view_w8 _ _ (by omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR]), view_wb _ _ (by rw [hh]; omega_using [hk, hfit, hE, hR]) (by omega_using [hk, ho, hR]),
    view_wb _ _ (by rw [hs]; omega_using [hk, hfit, hE, hR]) (by omega_using [hk, ho, hR]), view_w8 _ _ (by omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR]),
    view_wb _ _ (by simp; omega_using [hk, hE, hR]) (by omega_using [hk, ho, hR])]
  simp only [emPre, hE, Nat.zero_add, hs, hh, List.length_replicate, getD_rep0]
  rcases (by omega_using [ho] : o = k - 1 ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨
      o = k - sl - D - 2 ∨ o < k - sl - D - 2) with h | h | h | h | h <;>
    simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]

/-- `EM` after the mask with `mk` on `DB` (at `lo`, `db` bytes) and its first
byte ANDed with `c`: `emT`. -/
theorem emT_of {k D sl lo db : Nat} (salt h mk : List Byte) (c : Byte) (hh : h.length = D) (hlo : lo ≤ 1)
    (hdb : db = k - lo - D - 1) (hfit : sl + D + 2 ≤ k - lo) {V : Nat → Byte}
    (hV : ∀ o < k, V o = emPre k D sl salt h o) {o : Nat} (ho : o < k) :
    (if o = lo then mixV V mk lo db o &&& c else mixV V mk lo db o) = RsaPss.emT lo db sl salt h mk c o := by
  simp only [RsaPss.emT, mixV, hV o ho, emPre, hh]
  rcases (by omega_using [ho] : o < lo ∨ (lo ≤ o ∧ o < k - sl - D - 2) ∨ o = k - sl - D - 2 ∨
      (k - sl - D - 1 ≤ o ∧ o < k - D - 1) ∨ (k - D - 1 ≤ o ∧ o < k - 1) ∨ o = k - 1) with h | h | h | h | h | h
  · simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
  · by_cases h5 : o = lo
    · subst h5; simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
    · simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - sl - D - 1) = o - lo - (db - sl) by omega_using [hdb, hfit]]
    simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
  · rw [show o - (k - D - 1) = o - lo - db by omega_using [hdb, hfit]]
    simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := first | decide | omega_arith) only [↓ite_eq_left, ↓ite_eq_right]

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: the encoding

Untrusted: everything here is checked by Lean. `signEnc_ok`: after the
checks, `M'` and its hash `H`, `EM`'s writes, MGF1's mask and `clearTop`
leave `encEm` (`Sg/Spec.lean`) at `scratch`, with `Base`, for the private
operation that follows.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.RsaPss.PPC64LE (oY)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_wb view_w8 fx hiRegs offs mgfXorT_ok MFit TabS)
open VG.Impl.RsaPss.PPC64LE (MdFns)
open VG.Impl.RsaOaep.PPC64LE (Fns)
open VG.Proof.RsaOaep (mixV srcB range_ext map_range_getD')
open VG.Proof.RsaPss.PPC64LE (hashFixedG_ok MdTabS)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreS pc Gs.len s) {H : Hash} (hH : HashOK H)
  (hGl : Gs.len = H.D) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Ss s (stackArg s 15))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Ss s (stackArg s 14))
include P hH hGl hG Tg hGmh hGml hGmv T

theorem signEnc_ok (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) {t : State} (E : Entered s t) (sy : t.syms = s.syms)
    (h0 : s.mem (s.gpr .r5) ≠ 0) (hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s) {Q : State → Prop}
    (k : ∀ t', Base Ss vS s t' → t'.syms = s.syms → Spec.Rsa.bytesAt t'.mem (off (Ss s) oEm) (kk s) = encEm Gs Gm s →
      WP isa (priv pc) t' Q) :
    WP isa (signMain H f g pc) t Q := by
  have F := fits P
  have hD0 : 0 < Gs.len := hGl ▸ hH.hD0
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  have hDF := hH.hDF
  have hFD := hH.hFD64
  have hk2 : kk s ≤ 1024 := P.k2
  have hl1 := loN_le s
  obtain ⟨hE, hSt, hDg, _, _, hR⟩ := offs
  have hY : oY = 2560 := rfl
  have hsalt : (saltB s).length = (stackArg s 11).toNat := bytesAt_length _ _ _
  have hhl : (hS Gs s).length = Gs.len := by
    rw [hS, hGh, hH.hashLen, hGl]
  unfold signMain
  -- `M'` and `H`.
  refine WP.seq (WP.mono_syms (mPrime_ok P hGl.symm hD0 hD64 E.base (by omega_using [hfit, hk2])) fun t₁ ⟨b₁, _, m₁⟩ y₁ => ?_)
  refine WP.seq (WP.mono (hashFixedG_ok F hH T hGl.symm (sl := (stackArg s 11).toNat)
    (by show stackArg s 11 = _; rw [ofNat_toNat]) b₁ (y₁.trans sy) (by omega_using [hfit, hk2])) fun t₂ ⟨⟨b₂, _, _, d₂⟩, y₂⟩ => ?_)
  have hM : Spec.Sha256.bytesAt t₁.mem (off (Ss s) oY) (8 + Gs.len + (stackArg s 11).toNat) =
      Spec.RsaPss.zeros 8 ++ digB Gs.len s ++ saltB s := by
    have := mPrime_bytes t.mem (Ss s) (digB Gs.len s) (saltB s) (bytesAt_length _ _ _) (by rw [hsalt]; omega_using [hfit, hk2, hR, hY])
    rw [hsalt] at this
    rw [m₁]; exact this
  have hh : ∀ i < Gs.len, view t₂.mem (Ss s) (oDig + i) = (hS Gs s).getD i 0 := by
    intro i hi
    have := congrArg (fun l => l.getD i 0) d₂
    simp only [show Spec.Sha256.bytesAt t₂.mem (off (Ss s) oDig) H.FD = Spec.Rsa.bytesAt t₂.mem (off (Ss s) oDig) H.FD
      from rfl, bytesAt_eq_view, map_range_getD' _ (show i < H.FD by omega_using [hGl, hDF, hi]), hM] at this
    rw [this, hS, hGh, hH.hashTake]
    simp [List.getD_eq_getElem?_getD, show i < H.D by omega_using [hGl, hi]]
  -- `EM` before masking.
  refine WP.seq (WP.mono_syms (clearEm_ok P b₂) fun t₃ ⟨b₃, _, m₃⟩ y₃ => ?_)
  refine WP.seq (WP.mono_syms (putSalt_ok P hGl.symm hD64 b₃ (by omega_using [hfit])) fun t₄ ⟨b₄, _, m₄⟩ y₄ => ?_)
  have hdig : Spec.Rsa.bytesAt t₄.mem (off (Ss s) oDig) Gs.len = hS Gs s := by
    rw [bytesAt_eq_view]
    refine range_ext hhl fun i hi => ?_
    rw [m₄, view_wb _ _ (by rw [hsalt]; omega_using [hfit, hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]), ifn (by omega_using [hfit, hk2, hE, hDg, hsalt]), view_w8 _ _ (by omega_using [hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]),
      ifn (by omega_using [hk2, hE, hDg]), m₃, view_wb _ _ (by simp; omega_using [hk2, hE, hR]) (by omega_using [hD64, hDg, hR, hi]), ifn (by simp only [List.length_replicate]; omega_using [hk2, hE, hDg])]
    exact hh i (by omega_using [hi])
  refine WP.seq (WP.mono_syms (putH_ok P hGl.symm hD0 hD64 b₄ (by omega_using [hfit])) fun t₅ ⟨b₅, _, m₅⟩ y₅ => ?_)
  have hpre : ∀ o < kk s, view t₅.mem (Ss s) o = emPre (kk s) Gs.len (stackArg s 11).toNat (saltB s) (hS Gs s) o :=
    fun o ho => emPre_of hsalt hhl hk2 (by omega_using [hfit]) m₃ m₄ (by rw [m₅, hdig]) ho
  -- MGF1 and `clearTop`.
  refine WP.seq (WP.mono_syms (dbArgs_ok P hGl.symm hD64 b₅ h0 (by omega_using [hfit])) fun t₆ ⟨b₆, v₆, x24, x25, x26, x27⟩ y₆ =>
    ?_)
  have hsrc : srcB (view t₆.mem (Ss s)) (oEm + (kk s - Gs.len - 1)) Gs.len = hS Gs s := by
    refine range_ext hhl fun i hi => ?_
    rw [v₆, hpre _ (by omega_using [hfit, hE, hi])]
    simp only [emPre, hE, Nat.zero_add]
    rw [ifn (by omega_using [hfit, hi]), ifp (by omega_using []), show kk s - Gs.len - 1 + i - (kk s - Gs.len - 1) = i by omega_using []]
  refine WP.seq (WP.mono (mgfXorT_ok F hG Tg hGmh hGml hGmv (src := oEm + (kk s - Gs.len - 1)) (srcLen := Gs.len)
    (dst := oEm + loN s) (dstLen := kk s - loN s - Gs.len - 1) ⟨by omega_using [hfit, hk2, hE], by omega_using [hfit, hk2, hE], .inr (by omega_using [hfit]), by omega_using [hfit]⟩
    b₆ (y₆.trans (y₅.trans (y₄.trans (y₃.trans y₂)))) x24 (by rw [x25]) x26 x27) fun t₇ ⟨⟨b₇, v₇⟩, y₇⟩ => ?_)
  refine WP.seq (WP.mono_syms (clearTop_ok P b₇ h0) fun t₈ ⟨b₈, m₈⟩ y₈ => ?_)
  refine k t₈ b₈ (y₈.trans y₇) ?_
  rw [bytesAt_eq_view]
  unfold encEm
  refine List.map_congr_left fun o ho => ?_
  have ho := List.mem_range.mp ho
  rw [m₈, view_w8 _ _ (by omega_using [hl1, hE, hR]) (by omega_using [hk2, hE, hR, ho]), hE, Nat.zero_add, Nat.zero_add]
  have e7 : ∀ x < kk s, view t₇.mem (Ss s) x = mixV (view t₆.mem (Ss s)) (Spec.Mgf1.mgf1 Gm (hS Gs s)
      (kk s - loN s - Gs.len - 1)) (loN s) (kk s - loN s - Gs.len - 1) x := fun x hx => by
    rw [v₇ x (by omega_using [hk2, hSt, hx]), hsrc, hE, Nat.zero_add]
  rw [e7 o ho, e7 (loN s) (by omega_using [hfit])]
  have := emT_of (saltB s) (hS Gs s) (Spec.Mgf1.mgf1 Gm (hS Gs s) (kk s - loN s - Gs.len - 1)) (cS s)
    (k := kk s) (sl := (stackArg s 11).toNat) hhl hl1 rfl (by omega_using [hfit]) (V := view t₆.mem (Ss s))
    (fun x hx => by rw [v₆]; exact hpre x hx) ho
  by_cases hl : o = loN s
  · subst hl; rw [ifp rfl]; rw [ifp rfl] at this; exact this
  · rw [ifn hl]; rw [ifn hl] at this; exact this

end

end VG.Proof.RsaPss.PPC64LE.Sg

end

end


/-!
# RSASSA-PSS signing on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`signOut_zero`), and an encoding too short
for the digest (`chkEm`) or the salt (`chkSalt`: `signOut_long`) write zeros
and return 0; otherwise the encoding (`signEnc_ok`) and the private operation
(`priv_ok`) give `signOut` (`signOut_eq`). `sign_ok`: the function, from
an entry state whose hash function's table holds the index of the code's
sizes, through `byIdx`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

variable {pc : Bool}

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore Fns tword)
open VG.Impl.RsaPss.PPC64LE (MdFns byIdx idxs shapeOf)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Saves restore_ok freed_gpr freed_mem TabS)
open VG.Proof.RsaPss.PPC64LE (MdTabS twordA_ok byIdx_ok idxs_certs tab_sub)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only eval_zero eval_nonzero wp_nil)

/-- The result and `out`, from the entry state `s`. -/
def Post (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .r3) (kk s) ((s'.gpr .r3).setWidth 32) (signOut Gs Gm s))

/-- Before the restores. -/
def Done (pc : Bool) (Gs Gm : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (HypS pc s →
    Spec.Rsa.writtenOutcome t.mem (s.gpr .r3) (kk s) ((t.gpr .r3).setWidth 32) (signOut Gs Gm s))

theorem n0_eq {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r5) = 0 := by
  have h : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [n0, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by have := (s.mem (s.gpr .r5)).isLt; omega_using [])] at this
  simpa using this

theorem n0_ne {s t : State} (E : Entered s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r5) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

/-- The frame's body depends on the hash function only by its digest
length. -/
theorem body_D {H H' : Hash} (hD : H.D = H'.D) (f : MdFns) (g : Fns) (pc : Bool) :
    body H f g pc = body H' f g pc := by
  simp only [body, checks, signMain, mPrime, chkEm, chkSalt, putSalt, putH, dbArgs,
    Impl.RsaPss.PPC64LE.hashFixed, hD]

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreS pc Gs.len s)
include P

theorem fail_done {t : State} (h : Base Ss vS s t) (hv : signOut Gs Gm s = .invalid) :
    WP isa Impl.RsaOaep.PPC64LE.encFail t (Done pc Gs Gm s) :=
  WP.mono (fail_ok P h) fun u ⟨sv, _, h3, hb⟩ => ⟨sv, fun _ => by rw [hv, h3]; exact ⟨rfl, hb⟩⟩

variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Ss s (stackArg s 15))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Ss s (stackArg s 14))
include hH hGh hGl hHv hG Tg hGmh hGml hGmv T

theorem checks_done (X : pc = true → PreXS s) {t : State} (E : Entered s t) (sy : t.syms = s.syms) :
    WP isa (checks H f g pc) t (Done pc Gs Gm s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : H.D ≤ 64 := hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_done P E.base (signOut_zero Gs Gm (by omega_using [hk1]) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  refine WP.seq (WP.mono_syms (chkEm_ok P hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₃.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega_using [hGl, hc]
  have hem : H.D + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega_using [hc]
  refine WP.seq (WP.mono_syms (chkSalt_ok P hD64 E₃ h0 hem) fun t₄ ⟨E₄, r3'⟩ y₄ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_done P E₄.base (signOut_long Gs Gm (by omega_using [hk1]) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc; simp at hc; omega_using [hGl, hc]
  have hfit : Gs.len + (stackArg s 11).toNat + 2 ≤ kk s - loN s := by rw [r3'] at hc; simp at hc; omega_using [hGl, hem, hc]
  refine signEnc_ok P hH hGl hG Tg hGmh hGml hGmv T hGh E₄ (y₄.trans (y₃.trans sy)) h0 hfit fun t' b' _ hb => ?_
  refine WP.mono (priv_ok P X b' hb) fun u ⟨sv, _, hw⟩ => ⟨sv, fun hy => ?_⟩
  rw [signOut_eq Gs Gm hHv hGmv (by omega_using [hk1]) h0 hfit]
  exact hw hy

theorem body_ok (X : pc = true → PreXS s) {u : State} (hu : Only [.r11, .r12] (allocated frameBytes s) u)
    (sy : u.syms = s.syms) : WP isa (body H f g pc) u fun w => Post pc Gs Gm s (freed frameBytes w) := by
  refine WP.seq (WP.mono_syms (entry_ok P hu) fun t E y => WP.seq (WP.mono
    (checks_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X E (y.trans sy)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv) fun w ⟨habi, h3, hm⟩ => ⟨habi, fun hy => ?_⟩))
  rw [freed_mem, freed_gpr, hm, h3]
  exact res hy

/-- `vg_rsa_pss_sign`, from an entry state whose hash function's table holds
the index `i`, whose code is for `H`'s digest length. -/
theorem sign_ok (X : pc = true → PreXS s) {i : Nat}
    (hidx : s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
    (hi : i ∈ idxs) (hD : (shapeOf i).1.D = H.D) : WP isa (signG f g pc) s (Post pc Gs Gm s) := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega_using [hi]
  refine WP.alloc (by decide) (by have := P.sp1; have := stackBytes_ge pc; unfold frameBytes; omega_arith) ?_
  show WP isa (.seq (.block (tword .r11 hArg 5 ++ [])) _) _ _
  refine WP.seq (WP.of_syms (twordA_ok (j := hArg) (k := 5) (p := stackArg s 14) (by decide) (by decide)
    ⟨aR pc s, by rw [P.hrd]; simp, in_aR (by decide)⟩
    ((P.ka.sub_left kR_sub).sub_right (in_aR_sub (pc := pc) (by decide))).symm
    rfl ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide) (by decide)⟩
    ((P.kth.sub_left kR_sub).sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm fun u o e => wp_nil fun y => ?_))
  rw [show 8 * 5 = 40 from rfl, hidx] at e
  refine byIdx_ok (D := i) (by omega_using [hi8])
    (F := fun u' => Only [.r11, .r12] (allocated frameBytes s) u' ∧ u'.syms = s.syms ∧
      u'.gpr .r11 = BitVec.ofNat 64 i)
    (fun _ h => h.2.2) (fun u₁ u₂ ⟨o₁, y₁, e₁⟩ o y => ⟨(o₁.trans o).mono, y.trans y₁, by rw [o.get .r11]; exact e₁⟩)
    (fun u' ⟨o', y', _⟩ => ?_) hi (fun x hx => (idxs_certs x hx).1) u ⟨o.mono, y.trans rfl, e⟩
  rw [body_D hD]
  exact body_ok P hH hGh hGl hHv hG Tg hGmh hGml hGmv T X o' y'

end

end VG.Proof.RsaPss.PPC64LE.Sg
