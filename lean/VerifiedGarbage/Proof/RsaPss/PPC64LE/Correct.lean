module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Logic
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ByIdx
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Call
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Params
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Post
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix

/-!
# RSASSA-PSS verification on PPC64LE: correctness

Untrusted: everything here is checked by Lean. The checks (`checks_done`): a
modulus whose first byte is zero (`verify_zero`), and an encoding too short
for the digest (`chkEm`) or the salt length expected (`expLen`, `chkSalt`:
`verify_short`) return 0; otherwise RSAVP1 of the signature (`call_ok`) and
the checks of `EM` (`post_ok`) return 1 exactly when EMSA-PSS-VERIFY accepts
it (`res_iff`, `verify_bytes`), if `pre` holds the modulus' values.
`code_correct`: the function against its shared contract.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes restore Fns tword)
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Proof.MdStream (Md)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view kR fx hiRegs Saves restore_ok freed_gpr ne_zero_ltBit msgBit
  TabS)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_li wp_sub wp_subi wp_lsr wp_or wp_mov wp_nil eval_zero eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.Mgf1 (ifp ifn)

/-- What the function returns, from its entry state. -/
def vOut (Gs Gm : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify Gs Gm (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (mh Gs.len s) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s))
    (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32))

/-- The result, from the entry state `s`. -/
def Post (Gs Gm : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ (PreOk s → s'.gpr .r3 = if vOut Gs Gm s then 1 else 0)

/-- Before the restores. -/
def Done (Gs Gm : Spec.Mgf1.Hash) (s t : State) : Prop :=
  Saves s t ∧ (PreOk s → t.gpr .r3 = if vOut Gs Gm s then 1 else 0)

/-- `lo` and `c`, from the modulus' first byte. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0
def cB (s : State) : Byte :=
  if (s.mem (s.gpr .r3)).toNat = 1 then 0xFF else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .r3)).toNat - 1)

theorem anyL_eq (s : State) : anyL s = 0 ↔ (stackArg s 1).setWidth 32 = 0 := by
  unfold anyL
  rw [BitVec.ushiftRight_zero, ← BitVec.toNat_inj, ← BitVec.toNat_inj (y := 0)]
  simp only [BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by have := (stackArg s 1).toNat.mod_lt (show 0 < 2 ^ 32 by decide); omega_arith)]
  simp

theorem sLen_eq (s : State) : Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32) =
    if anyL s = 0 then some (stackArg s 0).toNat else none := by
  unfold Spec.RsaPss.expectedSaltLen
  by_cases h : anyL s = 0
  · rw [ifp h, ifp ((anyL_eq s).mp h)]
  · rw [ifn h, ifn fun h' => h ((anyL_eq s).mpr h')]

theorem bytesAt_cons (m : Mem) (p : Addr) (n : Nat) :
    ∃ rest : List Byte, Spec.Rsa.bytesAt m p (n + 1) = m p :: rest ∧ rest.length = n :=
  ⟨(List.range n).map fun i => m (p + BitVec.ofNat 64 (i + 1)), by
    simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [show p + BitVec.ofNat 64 0 = p by simp]; rfl, by simp⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem emOf_length (s : State) : (emOf s).length = kk s := by
  unfold emOf
  cases hp : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s))
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s)) with
  | none => simp
  | some y => rw [Option.getD_some, Proof.RsaPss.publicOpChecked_length' hp, bytesAt_length]

/-! ## The specification's cases -/

section
variable (Gs Gm : Spec.Mgf1.Hash) {s : State} (hk : 1 ≤ kk s)
include hk

theorem nB_cons : ∃ rest : List Byte, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (kk s) = s.mem (s.gpr .r3) :: rest ∧
    rest.length = kk s - 1 := by
  obtain ⟨rest, h, hl⟩ := bytesAt_cons s.mem (s.gpr .r3) (kk s - 1)
  rw [show kk s - 1 + 1 = kk s by omega_arith] at h
  exact ⟨rest, h, hl⟩

theorem zero_false (h0 : s.mem (s.gpr .r3) = 0) : vOut Gs Gm s = false := by
  obtain ⟨rest, hn, -⟩ := nB_cons hk
  rw [vOut, hn, h0]
  exact Proof.RsaPss.verify_zero₂ Gm Gs _ _ _ _ _

theorem emLen_eq (h0 : s.mem (s.gpr .r3) ≠ 0) {rest : List Byte} (hr : rest.length = kk s - 1) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .r3) :: rest)) - 1) =
      kk s - loN s := by
  rw [Proof.RsaPss.emLength_eq rest h0, hr, loN]; split <;> omega_arith

theorem short_false (h0 : s.mem (s.gpr .r3) ≠ 0)
    (h : kk s - loN s < Gs.len + (Spec.RsaPss.expectedSaltLen (stackArg s 0) ((stackArg s 1).setWidth 32)).getD 0 + 2) :
    vOut Gs Gm s = false := by
  obtain ⟨rest, hn, hr⟩ := nB_cons hk
  rw [vOut, hn]
  exact Proof.RsaPss.verify_short₂ Gm Gs _ _ _ (by rw [emLen_eq hk h0 hr]; exact h)

end

/-- `Res` is verification, for `EM` in place. -/
theorem res_vOut {Gs Gm : Spec.Mgf1.Hash} (hGv : Proof.Mgf1.Valid Gm) (hHv : Proof.Mgf1.Valid Gs) {s : State}
    (P : PreP Gs.len s)
    (h0 : s.mem (s.gpr .r3) ≠ 0) {m : Mem} (hm : Spec.Rsa.bytesAt m (off (Sp s) 0) (kk s) = emOf s)
    (hem : Gs.len + 2 ≤ kk s - loN s)
    (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    Res Gm Gs (view m (Sp s)) Gs.len (loN s) (kk s - loN s - Gs.len - 1) (cB s) (kk s) (mh Gs.len s) (anyL s)
      (stackArg s 0) ↔ vOut Gs Gm s = true := by
  have hk1 : 64 ≤ kk s := P.k1; have hk2 : kk s ≤ 1024 := P.k2
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega_arith
  obtain ⟨rest, hn, hr⟩ := nB_cons (show 1 ≤ kk s by omega_arith)
  have hE := emLen_eq (by omega_arith) h0 hr
  have hM := Proof.RsaPss.mask_eq rest h0
  have hx : (Spec.Rsa.publicOpChecked (s.mem (s.gpr .r3) :: rest) (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (kk s))).getD (Spec.RsaPss.zeros (s.mem (s.gpr .r3) :: rest).length) =
      emOf s := by
    rw [emOf, hn, Spec.RsaPss.zeros, List.length_cons, hr, show kk s - 1 + 1 = kk s by omega_arith]
  generalize hB : Spec.RsaPss.bitLength (Spec.Rsa.os2ip (s.mem (s.gpr .r3) :: rest)) - 1 = eb at hE hM
  generalize hEg : Spec.RsaPss.emLength eb = E at hE hM
  have hc : cB s = (0xFF : Byte) >>> (8 * E - eb) := by rw [hM]; rfl
  have hV : ∀ i < E, view m (Sp s) (loN s + i) = ((emOf s).drop (loN s)).getD i 0 := fun i hi => by
    show m (off (Sp s) (loN s + i)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, ← hm,
      bytesAt_getD _ _ (by omega_arith), show off (Sp s) 0 + BitVec.ofNat 64 (loN s + i) = off (off (Sp s) 0) (loN s + i)
      from rfl, off_off, Nat.zero_add]
  have hV0 : view m (Sp s) 0 = (emOf s).getD 0 0 := by
    rw [← hm, bytesAt_getD _ _ (by omega_arith), BitVec.add_zero]; rfl
  have hEl : ((emOf s).drop (loN s)).length = E := by rw [List.length_drop, emOf_length]; omega_arith
  rw [show kk s - loN s - Gs.len - 1 = E - Gs.len - 1 by omega_arith, show kk s = loN s + E by omega_arith,
    res_iff (E := E) hGv hc hEl (by omega_arith) hV (bytesAt_length _ _ _) hHv (sLen_eq s) (by omega_arith), vOut, hn,
    Proof.RsaPss.verify_bytes₂ Gm Gs hGv (bytesAt_length _ _ _) (by rw [bytesAt_length, List.length_cons, hr]; omega_arith)
      hB hEg (by rw [List.length_cons, hr]; omega_arith) hl1 ?_, hx, hV0]
  rw [sLen_eq]; split
  · rename_i h; have := hfit h; simp only [Option.getD_some]; omega_arith
  · simp only [Option.getD_none]; omega_arith

/-! ## The code -/

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreP Gs.len s)
include P

theorem fail_ok {t : State} (h : Base Sp (vP Gs.len) s t) (hv : vOut Gs Gm s = false) :
    WP isa Impl.RsaPss.PPC64LE.fail t (Done Gs Gm s) :=
  wp_li (by decide) fun t' o e => wp_nil ⟨(h.only P.fits o).sv, fun _ => by rw [e, hv]; rfl⟩

omit P in
theorem expLen_ok {t : State} (h20 : t.gpr .r20 = anyL s) (h19 : t.gpr .r19 = stackArg s 0) :
    WP isa expLen t fun u => Only [.r4] t u ∧ u.gpr .r4 = if anyL s = 0 then stackArg s 0 else 0 := by
  refine WP.ite _ (eval_zero _ _) (fun hz => wp_mov fun u o e => wp_nil ⟨o, ?_⟩)
    (fun hz => wp_li (by decide) fun u o e => wp_nil ⟨o, ?_⟩)
  · rw [ifp (by rw [← h20]; simpa using hz), e, h19]
  · rw [ifn (by rw [← h20]; simpa using hz), e]; rfl

theorem lo_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : lo (reE s m) = lo s := by
  simp only [lo, smear, reE_n0 P hf]

theorem cm_reE {m : Mem} (hf : Frame [kR s, scR s] s.mem m) : cm (reE s m) = cm s := by
  rw [cm, cm, lo_reE P hf]; simp only [smear, reE_n0 P hf]

theorem lay_reE {H : Hash} (hH : HashOK H) (hGl : Gs.len = H.D) {m : Mem} (hf : Frame [kR s, scR s] s.mem m)
    (h0 : s.mem (s.gpr .r3) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s) :
    Lay Gs.len (reE s m) (loN s) (kk s - loN s - Gs.len - 1) (cB s) where
  F := reE_fits P hf
  hlo := by rw [lo_reE P hf, lo_eq h0]; rfl
  hdb := by
    show s.gpr .r4 - lo (reE s m) - BitVec.ofNat 64 (Gs.len + 1) = _
    have e : (s.gpr .r4).toNat = kk s := rfl
    rw [lo_reE P hf, lo_eq h0, show (if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0) = loN s from rfl,
      ← ofNat_toNat (s.gpr .r4), Offset.ofNat_sub_ofNat (by omega_arith), Offset.ofNat_sub_ofNat (by omega_arith),
      show (s.gpr .r4).toNat - loN s - (Gs.len + 1) = kk s - loN s - Gs.len - 1 by omega_arith]
  hc := by rw [cm_reE P hf, cm_eq h0]; rfl
  l1 := by unfold loN; split <;> omega_arith
  d1 := by omega_arith
  hk := by show _ = kk s; omega_arith
  k2 := P.k2
  D0 := by rw [hGl]; exact hH.hD0
  D64 := by rw [hGl]; exact hH.hD64
  dr := by show dR Gs.len s ∈ s.rd; rw [P.hrd]; simp
  dsc := by
    rw [show SC Sp (reE s m) = SC Sp s by simp only [SC, reE_Sp P hf]]; exact P.ds.sub_right (sc_sub P)
  dk := P.kd
  wd := P.wd

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered Gs.len s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9, .r24, .r25, .r26, .r27] : List Reg) := by decide) :
    Entered Gs.len s t' := by
  have g : ∀ r ∈ [Reg.r9, .r24, .r25, .r26, .r27], t'.gpr r = t.gpr r := fun r hr =>
    o.gpr r fun h => hrs r h (List.mem_append_right _ hr)
  exact ⟨E.base.only P.fits o fun r h h' => hrs r h (List.mem_append_left _ h'), (g _ (by decide)).trans E.r24,
    (g _ (by decide)).trans E.r25, (g _ (by decide)).trans E.r26, (g _ (by decide)).trans E.r27,
    (g _ (by decide)).trans E.r9⟩

omit P in
theorem Entered.before {t : State} (E : Entered Gs.len s t) : Before Gs.len s t := ⟨E.base, E.r24, E.r25, E.r26, E.r27⟩

omit P in
theorem n0_eq {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .r9 == 0) = true) : s.mem (s.gpr .r3) = 0 := by
  have : n0 s = 0#64 := by rw [← E.r9]; simpa using hz
  exact (setWidth64_eq_zero _).mp this

omit P in
theorem n0_ne {t : State} (E : Entered Gs.len s t) (hz : (t.gpr .r9 == 0) = false) : s.mem (s.gpr .r3) ≠ 0 :=
  fun h => by rw [E.r9, n0, h] at hz; simp at hz

theorem lo_N (h0 : s.mem (s.gpr .r3) ≠ 0) : s.gpr .r4 - lo s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .r4).toNat = kk s := rfl
  have hl1 : loN s ≤ 1 := by unfold loN; split <;> omega_arith
  rw [lo_eq h0, show (if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0) = loN s from rfl, ← ofNat_toNat (s.gpr .r4),
    Offset.ofNat_sub_ofNat (by omega_arith)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .r3) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s < Gs.len + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (h := by omega_arith) fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, E.base.pk, E.base.plo, lo_N P h0, ← hGl]
  exact ne_zero_ltBit (by omega_arith) (by omega_arith)

/-- `chkSalt`: whether the salt length expected is more than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Hash} (hGl : Gs.len = H.D) (hD64 : Gs.len ≤ 64) {t : State} (E : Entered Gs.len s t)
    (h0 : s.mem (s.gpr .r3) ≠ 0) (hem : Gs.len + 2 ≤ kk s - loN s)
    (h4 : t.gpr .r4 = if anyL s = 0 then stackArg s 0 else 0) :
    WP isa (.block (chkSalt H)) t fun t' => Entered Gs.len s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s - (Gs.len + 2) < (if anyL s = 0 then stackArg s 0 else 0).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (h := by omega_arith) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_lsr fun t₈ o₈ e₈ => wp_lsr fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.r3, .r5] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .r3, e₉, e₈, o₈.get .r4, e₇, o₇.get .r4, e₆, o₆.get .r4, e₅, o₅.get .r4, E.base.pk, E.base.plo,
    lo_N P h0, h4, ← hGl, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (Gs.len + 2)) (y := (if anyL s = 0 then stackArg s 0 else 0).toNat)
    (by omega_arith) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

section
variable {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Sp s (stackArg s 7))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Sp s (stackArg s 6))
  {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : H.N = P'.N) (hB : H.B = P'.B)
include hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB

theorem main_done {t : State} (B : Before Gs.len s t) (sy : t.syms = s.syms) (h0 : s.mem (s.gpr .r3) ≠ 0)
    (hem : Gs.len + 2 ≤ kk s - loN s) (hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1) :
    WP isa (verifyMain H P' f g) t (Done Gs Gm s) := by
  refine WP.seq (WP.mono_syms (pubArgs_ok P B) fun t₁ a₁ y₁ => WP.seq (WP.mono_syms (call_ok P a₁) fun t₂ c₂ y₂ => ?_))
  have L := lay_reE P hH hGl c₂.mem h0 hem
  have hS := reE_Sp P c₂.mem
  have hmh : mh Gs.len (reE s t₂.mem) = mh Gs.len s :=
    VG.Proof.RsaOaep.PPC64LE.bytes_entry c₂.mem P.kd P.ds.symm (by have := hH.hD64; omega_arith)
  have hany : anyL (reE s t₂.mem) = anyL s := by unfold anyL; rw [reE_args P c₂.mem 1 (by decide)]
  have hSC : SC Sp (reE s t₂.mem) = SC Sp s := by simp only [SC, hS]
  have hsl0 : stackArg (reE s t₂.mem) 0 = stackArg s 0 := reE_args P c₂.mem 0 (by decide)
  have hA : ∀ j < 8, ∀ r ∈ [kR s, scR s], Region.Disjoint ⟨stackArgAddr s j, 8⟩ r := fun j hj r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (P.ka.sub_right (in_aR_sub hj)).symm
    · exact (P.sa.sub_right (in_aR_sub hj)).symm
  have Tg' : TabS G g gArg Sp (reE s t₂.mem) (stackArg s 7) := Tg.transfer rfl rfl rfl hSC c₂.mem (hA 7 (by decide))
    fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.ktg.sub_right (tab_sub (n := 5) hk)).symm
      · exact (P.stg.sub_right (tab_sub (n := 5) hk)).symm
  have T' : MdTabS H cn cc dn dc f hArg Sp (reE s t₂.mem) (stackArg s 6) := T.transfer rfl rfl rfl hSC c₂.mem
    (hA 6 (by decide)) fun k hk r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (P.kth.sub_right (tab_sub (n := 11) hk)).symm
      · exact (P.sth.sub_right (tab_sub (n := 11) hk)).symm
  refine WP.mono (post_ok L hH hGl.symm hGh hG Tg' hGmh hGml hGmv T' ok hl hN hB c₂.base (y₂.trans (y₁.trans sy))
    (by rw [hany, hsl0]; exact hfit)) fun t' ⟨b', r'⟩ =>
    ⟨⟨b'.sv.sp, b'.sv.wr, b'.sv.hi, b'.sv.sv, b'.sv.ls⟩, fun hc => ?_⟩
  rw [r', hS, hmh, hany, hsl0, reE_gpr]
  have e := res_vOut hGmv hHv P h0 (c₂.em hc) hem hfit
  by_cases hv : vOut Gs Gm s = true
  · rw [ifp (e.mpr hv), ifp hv]; rfl
  · rw [ifn (fun h => hv (e.mp h)), ifn hv]; rfl

theorem checks_done {t : State} (E : Entered Gs.len s t) (sy : t.syms = s.syms) :
    WP isa (checks H P' f g) t (Done Gs Gm s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have hD64 : Gs.len ≤ 64 := hGl ▸ hH.hD64
  refine WP.ite _ (eval_zero _ _) (fun hz => fail_ok P E.base (zero_false Gs Gm (by omega_arith) (n0_eq E hz)))
    (fun hz => ?_)
  have h0 := n0_ne E hz
  -- `emLen < hLen + 2`.
  refine WP.seq (WP.mono_syms (chkEm_ok P hGl hD64 E h0) fun t₃ ⟨E₃, r3⟩ y₃ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₃.base (short_false Gs Gm (by omega_arith) h0 ?_))
    (fun hc => ?_)
  · rw [r3] at hc; simp at hc; omega_arith
  have hem : Gs.len + 2 ≤ kk s - loN s := by rw [r3] at hc; simp at hc; omega_arith
  -- The salt length expected.
  refine WP.seq (WP.mono_syms (expLen_ok E₃.base.pany E₃.base.psl) fun t₄ ⟨o₄, e₄⟩ y₄ => ?_)
  refine WP.seq (WP.mono_syms (chkSalt_ok P hGl hD64 (E₃.only P o₄) h0 hem e₄) fun t₁₀ ⟨E₁₀, r3'⟩ y₁₀ => ?_)
  refine WP.ite _ (eval_nonzero _ _) (fun hc => fail_ok P E₁₀.base (short_false Gs Gm (by omega_arith) h0 ?_))
    (fun hc => ?_)
  · rw [r3'] at hc
    rw [sLen_eq]
    by_cases ha : anyL s = 0
    · rw [ifp ha] at hc ⊢; simp only [Option.getD_some]; simp at hc; omega_arith
    · rw [ifn ha] at hc; simp at hc
  have hfit : anyL s = 0 → (stackArg s 0).toNat + 1 ≤ kk s - loN s - Gs.len - 1 := fun ha => by
    rw [r3', ifp ha] at hc; simp at hc; omega_arith
  exact main_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB E₁₀.before (y₁₀.trans (y₄.trans (y₃.trans sy)))
    h0 hem hfit

/-- The frame's body for `H`'s sizes, from the state after the frame's push
and the choice of the code, which writes only `r11` and `r12`. -/
theorem body_ok {u : State} (hu : Only [.r11, .r12] (allocated frameBytes s) u) (sy : u.syms = s.syms) :
    WP isa (body H P' f g) u fun w => Post Gs Gm s (freed frameBytes w) := by
  refine WP.seq (WP.mono_syms (entry_ok P hGl.symm (hGl ▸ hH.hD64) hu) fun t E y => WP.seq (WP.mono
    (checks_done P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB E (y.trans sy)) fun t' ⟨sv, res⟩ =>
      WP.mono (restore_ok sv) fun w ⟨habi, h3, _⟩ => ⟨habi, fun hc => ?_⟩))
  rw [freed_gpr, h3]
  exact res hc

end

end


/-- The frame's body depends on the hash function only through its digest
length. -/
theorem body_D {H H' : Hash} (hD : H.D = H'.D) (P : Params) (f : MdFns) (g : Fns) :
    body H P f g = body H' P f g := by
  simp only [body, checks, verifyMain, finish, prologue, chkEm, chkSalt, dbArgs, mPrefix, copySalt, copyDb, shiftPass,
    shift, hashFixed, ctHash, ctLens, cmpH, hD]

section
variable {Gs Gm : Spec.Mgf1.Hash} {s : State} (P : PreP Gs.len s)
  {H : Hash} (hH : HashOK H) (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hHv : Proof.Mgf1.Valid Gs) {G : Hash} (hG : HashOK G) {g : Fns} (Tg : TabS G g gArg Sp s (stackArg s 7))
  (hGmh : ∀ x, Gm.hash x = hG.SH.H.hash x) (hGml : Gm.len = G.D) (hGmv : Proof.Mgf1.Valid Gm)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} (T : MdTabS H cn cc dn dc f hArg Sp s (stackArg s 6))
  {P' : Params} {md : Md P'.B P'.N P'.L} (ok : CtOK P' md cc dc) {iv : md.HV} (hl : md.Link hH.SH iv Gs.len)
  (hN : H.N = P'.N) (hB : H.B = P'.B)
include P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB

/-- `vg_rsa_pss_verify_precomputed`, for a hash function's table whose index
`i` is one of `idxs`, whose sizes and parameters `shapeOf i` gives. -/
theorem verify_ok {i : Nat} (hidx : s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i)
    (hi : i ∈ idxs) (hD : (shapeOf i).1.D = H.D) (hP : (shapeOf i).2 = P') :
    WP isa (verifyPrecomputed f g) s (Post Gs Gm s) := by
  have hi8 : i < 8 := by simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi; omega
  refine WP.alloc (by decide) (by have := P.sp1; unfold frameBytes; omega_arith) ?_
  show WP isa (.seq (.block (tword .r11 hArg 5 ++ [])) _) _ _
  refine WP.seq (WP.of_syms (twordA_ok (j := 6) (k := 5) (p := stackArg s 6) (by decide) (by decide)
    ⟨aR s, by rw [P.hrd]; simp, in_aR (by decide)⟩ (P.ka.sub_right (in_aR_sub (by decide))).symm rfl
    ⟨tHR s, by rw [P.hrd]; simp, Offset.contains_base _ (by decide) (by decide)⟩
    (P.kth.sub_right (tab_sub (n := 11) (show 5 < 11 by decide))).symm fun u o e => wp_nil fun y => ?_))
  rw [show 8 * 5 = 40 from rfl, hidx] at e
  refine byIdx_ok (D := i) (by omega)
    (F := fun u' => Only [.r11, .r12] (allocated frameBytes s) u' ∧ u'.syms = s.syms ∧
      u'.gpr .r11 = BitVec.ofNat 64 i)
    (fun _ h => h.2.2) (fun u₁ u₂ ⟨o₁, y₁, e₁⟩ o y => ⟨(o₁.trans o).mono, y.trans y₁, by rw [o.get .r11]; exact e₁⟩)
    (fun u' ⟨o', y', _⟩ => ?_) hi (fun x hx => (idxs_certs x hx).1) u ⟨o.mono, y.trans rfl, e⟩
  rw [body_D hD, hP]
  exact body_ok P hH hGh hGl hHv hG Tg hGmh hGml hGmv T ok hl hN hB o' y'

end

end VG.Proof.RsaPss.PPC64LE
