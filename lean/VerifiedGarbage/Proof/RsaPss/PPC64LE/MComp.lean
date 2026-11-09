module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Tab
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Select
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on PPC64LE: the compression function and the digest through the table

Untrusted: everything here is checked by Lean. The calls through the hash
function's table of its compression function (`compM_ok`: one block of
`M'` at `oY + b` into the hash value at `oSt`, by `compressK`) and of the
digest of a hash value (`digM_ok`: of the hash value at `oSel` to `oDig`,
by `digestK`); and `selHash_ok`: the hash value at `oSt` copied to `oSel`
under the mask of `b = fb` (`r26`, `r27`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params)
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa tcall)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.MdHashTable.PPC64LE (digestK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW sc_cov sdis cR_dis Same
  same_of_frame not_r12)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_sub wp_xor wp_and wp_lsr wp_lbz wp_stb
  wp_nil wp_countdown)
open VG.Proof.RsaPss.PPC64LE (sel_byte)
open VG.Proof.Mgf1 (ifp ifn)

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (F : Fits S s) {H : Hash}
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j S s p)
  {P : Params} {md : Md P.B P.N P.L}
include F T

/-- The compression of the block at `oY + b` into the hash value at `oSt`,
through the table. -/
theorem compM_ok (hc : CalleeOk md cc) (hN : P.N ≤ 64) (hso : P.so ≤ 1024) {t : State} (h : Base S vf s t)
    (sy : t.syms = s.syms) {b : Nat} (h3 : t.gpr .r3 = off (S s) oSt) (h4 : t.gpr .r4 = off (S s) (oY + b))
    (h5 : t.gpr .r5 = BitVec.ofNat 64 1) (h6 : t.gpr .r6 = off (S s) oW) (hb : b + P.B ≤ 2048) :
    WP isa (tcall j 3 f.comp) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, P.N), (oW, P.so)] ∧
      md.stateAt t'.mem (off (S s) oSt) =
        md.compress (md.stateAt t.mem (off (S s) oSt)) (md.blockAt t.mem (off (S s) (oY + b)))) ∧
      t'.syms = s.syms := by
  have hR : oRsa = 8192 := rfl
  have hY : oY = 2560 := rfl
  have hSt : oSt = 1024 := rfl
  have hW : oW = 1352 := rfl
  have hB1 : P.B * (BitVec.ofNat 64 1).toNat = P.B := by simp
  refine tcallM_ok T h sy (k := 3) (by decide) T.ok.c (by rw [show 8 * 3 = 24 from rfl]; exact T.mc)
    fun t' o sy' => WP.mono_syms (Q := fun t'' => Base S vf s t'' ∧ (∀ r ∈ preserved, t''.gpr r = t.gpr r) ∧
      Same (S s) t t'' [(oSt, P.N), (oW, P.so)] ∧ md.stateAt t''.mem (off (S s) oSt) =
        md.compress (md.stateAt t.mem (off (S s) oSt)) (md.blockAt t.mem (off (S s) (oY + b)))) ?_
      fun t'' q y'' => ⟨q, y''.trans (sy'.trans sy)⟩
  have b' := h.only F o
  have e3 : t'.gpr .r3 = off (S s) oSt := by rw [o.get .r3, h3]
  have e4 : t'.gpr .r4 = off (S s) (oY + b) := by rw [o.get .r4, h4]
  have e5 : t'.gpr .r5 = BitVec.ofNat 64 1 := by rw [o.get .r5, h5]
  have e6 : t'.gpr .r6 = off (S s) oW := by rw [o.get .r6, h6]
  have hcw : Covers [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩] t'.wr := by
    rw [b'.wr]; exact Covers.pair (sc_cov F (by omega)) (sc_cov F (by omega))
  refine WP.call (k := compressK md) hc.verified (rd := [⟨off (S s) (oY + b), P.B⟩])
    (wr := [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩]) ?_
    (Covers.append_left (Covers.right (by rw [b'.wr]; exact sc_cov F (by omega))) (Covers.right hcw)) hcw
    (fun t'' hrd hwr hsp hf hg _ hpost => ?_) hc.noFrames
  · simp only [compressK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
      e3, e4, e5, e6, hB1]
    exact ⟨trivial, trivial, sdis (.inl (by omega)) (by omega) (by omega), sdis (.inr (by omega)) (by omega) (by omega),
      sdis (.inr (by omega)) (by omega) (by omega)⟩
  · simp only [compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_mem, e3, e4, e5] at hpost
    have hf' : Frame ([⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩] ++ [below t'.sp 48]) t'.mem t''.mem :=
      hf.mono fun r hr => List.mem_append_left _ hr
    refine ⟨h.call F (R := [⟨off (S s) oSt, P.N⟩, ⟨off (S s) oW, P.so⟩]) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sc_in (by omega)
        · exact sc_in (by omega)) (hrd.trans o.rd) (hwr.trans o.wr) (hsp.trans o.sp)
        (by rw [← o.sp, ← o.mem]; exact hf') (fun r hr => (hg r hr).trans (o.gpr r (not_r12 hr))),
      fun r hr => (hg r hr).trans (o.gpr r (not_r12 hr)),
      (Same.of_mem o.mem _).trans (same_of_frame F (b'.sp) (rgs := [(oSt, P.N), (oW, P.so)]) (by simp; omega) hf'),
      ?_⟩
    rw [hpost, BitVec.toNat_ofNat, Md.compressBlocks_one, o.mem]

/-- The digest of the hash value at `oSel` to `oDig`, through the table. -/
theorem digM_ok (hd : ∀ u, (digestK md).pre u → ∃ t u', Exec isa dc u t u' ∧ abiPreserved u u' ∧ (digestK md).post u u')
    (hdn : dc.noFrames = true) (hN : P.N ≤ 64) {t : State} (h : Base S vf s t) (sy : t.syms = s.syms)
    (h3 : t.gpr .r3 = off (S s) oSel) (h4 : t.gpr .r4 = off (S s) oDig) :
    WP isa (tcall j 4 f.dig) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oDig, P.N)] ∧
      t'.mem = WriteBytes.writeBytes t.mem (off (S s) oDig) (md.digest (md.stateAt t.mem (off (S s) oSel)))) ∧
      t'.syms = s.syms := by
  have hR : oRsa = 8192 := rfl
  have hDg : oDig = 1280 := rfl
  have hSl : oSel = 4800 := rfl
  refine tcallM_ok T h sy (k := 4) (by decide) T.ok.d (by rw [show 8 * 4 = 32 from rfl]; exact T.md)
    fun t' o sy' => WP.mono_syms (Q := fun t'' => Base S vf s t'' ∧ (∀ r ∈ preserved, t''.gpr r = t.gpr r) ∧
      Same (S s) t t'' [(oDig, P.N)] ∧
      t''.mem = WriteBytes.writeBytes t.mem (off (S s) oDig) (md.digest (md.stateAt t.mem (off (S s) oSel)))) ?_
      fun t'' q y'' => ⟨q, y''.trans (sy'.trans sy)⟩
  have b' := h.only F o
  have e3 : t'.gpr .r3 = off (S s) oSel := by rw [o.get .r3, h3]
  have e4 : t'.gpr .r4 = off (S s) oDig := by rw [o.get .r4, h4]
  have hcw : Covers [⟨off (S s) oDig, P.N⟩] t'.wr := by rw [b'.wr]; exact sc_cov F (by omega)
  refine WP.call (k := digestK md) hd (rd := [⟨off (S s) oSel, P.N⟩]) (wr := [⟨off (S s) oDig, P.N⟩]) ?_
    (Covers.append_left (Covers.right (by rw [b'.wr]; exact sc_cov F (by omega))) (Covers.right hcw)) hcw
    (fun t'' hrd hwr hsp hf hg _ hpost => ?_) hdn
  · simp only [digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      e3, e4]
    exact ⟨trivial, trivial, sdis (.inr (by omega)) (by omega) (by omega)⟩
  · simp only [digestK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
      State.callEntry_mem, e3, e4] at hpost
    have hf' : Frame ([⟨off (S s) oDig, P.N⟩] ++ [below t'.sp 48]) t'.mem t''.mem :=
      hf.mono fun r hr => List.mem_append_left _ hr
    refine ⟨h.call F (R := [⟨off (S s) oDig, P.N⟩]) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact sc_in (by omega)) (hrd.trans o.rd) (hwr.trans o.wr) (hsp.trans o.sp)
        (by rw [← o.sp, ← o.mem]; exact hf') (fun r hr => (hg r hr).trans (o.gpr r (not_r12 hr))),
      fun r hr => (hg r hr).trans (o.gpr r (not_r12 hr)),
      (Same.of_mem o.mem _).trans (same_of_frame F (b'.sp) (rgs := [(oDig, P.N)]) (by simp; omega) hf'), ?_⟩
    rw [hpost, o.mem]

end


section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

/-- `selHash`: the hash value at `oSt` to `oSel` if `b = fb` (`r26`, `r27`). -/
theorem selHash_ok {P : Params} (hN0 : 0 < P.N) (hN : P.N ≤ 64) {t : State} (h : Base Sp (vP D) s t)
    {Ln sl : Nat} (h26 : t.gpr .r26 = BitVec.ofNat 64 Ln) (h25 : t.gpr .r27 = BitVec.ofNat 64 sl)
    (hL : Ln < 2 ^ 63) (hs : sl < 2 ^ 63) :
    WP isa (selHash P) t fun t' => Base Sp (vP D) s t' ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8, .r12] t t' ∧
      ∀ o < oRsa, view t'.mem (Sp s) o = if oSel ≤ o ∧ o < oSel + P.N ∧ Ln = sl then
        view t.mem (Sp s) (oSt + (o - oSel)) else view t.mem (Sp s) o := by
  have F := L.F
  have hD0 := hN0; have hD64 := hN
  have hR : oRsa = 8192 := rfl
  have hS : oSel = 4800 := rfl
  have hDg : oSt = 1024 := rfl
  let V := view t.mem (Sp s)
  let bit : Bool := Ln = sl
  refine WP.seq (wp_xor fun t₁ o₁ e₁ => wp_subi fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_li (by decide)
    fun t₄ o₄ e₄ => wp_sub fun t₅ o₅ e₅ => wp_addi (h := by decide) fun t₆ o₆ e₆ =>
    wp_addi (h := by decide) fun t₇ o₇ e₇ => wp_li (by omega_arith) fun t₈ o₈ e₈ => wp_nil ?_)
  have k₈ : Only [.r3, .r12, .r4, .r5, .r6] t t₈ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans o₈))))))).mono
  have g3 : t₈.gpr .r3 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₈.get .r3, o₇.get .r3, o₆.get .r3, e₅, e₄, o₄.get .r3, e₃, e₂, e₁, h26, h25, eq_mask hL hs]
    simp only [bit, decide_eq_true_eq]
  refine WP.mono (wp_countdown (cnt := .r6) (N := P.N) (by omega_arith) hD0
    (fun i u => Base Sp (vP D) s u ∧ Keep [.r4, .r5, .r6, .r7, .r8] t₈ u ∧ u.gpr .r4 = off (Sp s) (oSt + i) ∧
      u.gpr .r5 = off (Sp s) (oSel + i) ∧ ∀ o < oRsa, view u.mem (Sp s) o =
        if oSel ≤ o ∧ o < oSel + i then (if bit then V (oSt + (o - oSel)) else V o) else V o) ?_
    ⟨h.only F k₈, Keep.refl _ _, by rw [o₈.get .r4, o₇.get .r4, e₆, o₅.get .r14, o₄.get .r14, o₃.get .r14,
      o₂.get .r14, o₁.get .r14, h.r14]; rfl, by rw [o₈.get .r5, e₇, o₆.get .r14, o₅.get .r14, o₄.get .r14,
      o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14]; rfl, fun o _ => by rw [ifn (by omega_arith), k₈.mem]⟩
    (by rw [e₈])) fun u ⟨bu, ku, _, _, vu⟩ => ⟨bu, (k₈.keep.trans ku).mono, fun o ho => ?_⟩
  · intro i hi u ⟨bu, ku, u4, u5, vu⟩ _
    refine wp_lbz (a := off (Sp s) (oSt + i)) (by rw [u4, BitVec.add_zero])
      (by rw [bu.wr]; exact sc_inR F (by omega_arith) _) fun u₁ p₁ f₁ => ?_
    refine wp_lbz (a := off (Sp s) (oSel + i)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
      (by rw [p₁.rd, p₁.wr, bu.wr]; exact sc_inR F (by omega_arith) _) fun u₂ p₂ f₂ => ?_
    refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
    have k₅ : Only [.r7, .r8] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
    refine wp_stb (a := off (Sp s) (oSel + i)) (by rw [k₅.get .r5, u5, BitVec.add_zero])
      (by rw [k₅.wr, bu.wr]; exact sc_inW F (by omega_arith)) fun u₆ m₆ => ?_
    refine wp_addi fun u₇ p₇ f₇ => wp_addi fun u₈ p₈ f₈ => wp_subi fun u₉ p₉ f₉ => wp_nil ?_
    have hb : (u₅.gpr .r8).setWidth 8 = if bit then V (oSt + i) else V (oSel + i) := by
      have va : u.mem (off (Sp s) (oSt + i)) = V (oSt + i) := by
        have := vu (oSt + i) (by omega_arith); rw [ifn (by omega_arith)] at this; exact this
      have vb : u₁.mem (off (Sp s) (oSel + i)) = V (oSel + i) := by
        have := vu (oSel + i) (by omega_arith); rw [ifn (by omega_arith)] at this; rw [p₁.mem]; exact this
      rw [f₅, p₄.get .r8, p₃.get .r8, f₂, f₄, f₃, p₂.get .r7, f₁, f₂, va, vb, p₃.get .r3, p₂.get .r3, p₁.get .r3,
        ku.get .r3, g3]
      exact sel_byte _ _ bit
    have q : Keep [.r7, .r8, .r4, .r5, .r6] u u₉ :=
      (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
    have hm : u₉.mem = u.mem.writeW (off (Sp s) (oSel + i)) (if bit then V (oSt + i) else V (oSel + i)) := by
      rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, k₅.mem]
    refine ⟨⟨bu.keep F q (R := [⟨off (Sp s) (oSel + i), 1⟩]) (by
        rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by omega_arith))),
      (ku.trans q).mono, ?_, ?_, fun o ho => ?_⟩, ?_⟩
    · rw [p₉.get .r4, p₈.get .r4, f₇, m₆.gpr, k₅.get .r4, u4]; exact off_off _ _ _
    · rw [p₉.get .r5, f₈, p₇.get .r5, m₆.gpr, k₅.get .r5, u5]; exact off_off _ _ _
    · rw [hm, view_w8 _ _ (by omega_arith) ho, vu o ho]
      by_cases e : o = oSel + i
      · subst e
        rw [ifp (show oSel + i = oSel + i from rfl),
          ifp (show oSel ≤ oSel + i ∧ oSel + i < oSel + (i + 1) from ⟨by omega_arith, by omega_arith⟩),
          show oSt + (oSel + i - oSel) = oSt + i by omega_arith]
      · rw [ifn e]
        by_cases e' : oSel ≤ o ∧ o < oSel + i
        · rw [ifp e', ifp (show oSel ≤ o ∧ o < oSel + (i + 1) from ⟨e'.1, by omega_arith⟩)]
        · rw [ifn e', ifn (show ¬(oSel ≤ o ∧ o < oSel + (i + 1)) by omega_arith)]
    · rw [f₉, p₈.get .r6, p₇.get .r6, m₆.gpr, k₅.get .r6]
  · rw [vu o ho]
    by_cases e : oSel ≤ o ∧ o < oSel + P.N
    · rw [ifp e]
      by_cases eb : Ln = sl
      · rw [ifp (show oSel ≤ o ∧ o < oSel + P.N ∧ Ln = sl from ⟨e.1, e.2, eb⟩), ifp (by simpa [bit] using eb)]
      · rw [ifn (show ¬(oSel ≤ o ∧ o < oSel + P.N ∧ Ln = sl) from fun h' => eb h'.2.2), ifn (by simpa [bit] using eb)]
    · rw [ifn e, ifn (show ¬(oSel ≤ o ∧ o < oSel + P.N ∧ Ln = sl) from fun h' => e ⟨h'.1, h'.2.1⟩)]

end

end VG.Proof.RsaPss.PPC64LE
