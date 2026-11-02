module

public import VerifiedGarbage.Proof.RsaPss.RISCV64.Mid
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Mgf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSASSA-PSS verification on RISC-V: unmasking `DB`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/Unmask.lean`): `unmask_ok`, `DB` unmasked with MGF1
of `H` and its first byte ANDed with `c` (`dbV`). MGF1 uses `s6`–`s11`, so
`c`, `salt_len` and the salt-length mode are saved at `scratch + oV` before
(`spill_ok`) and loaded back after (`reload_ok`): MGF1 changes our part of
the working space only in `DB`, the streaming state, the digest and its
counter (`mgfXor_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oEm oSt oDig oCtr oRsa mgfXor)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx MFit mgfXor_ok Kp offs)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_add wp_mov wp_and wp_lbu wp_sb wp_sd wp_ld
  wp_nil)
open VG.Proof.Mgf1 (ifp ifn)

/-- `DB` in `EM`'s place, from its view `V` before unmasking. -/
def dbV (Gs : Spec.Mgf1.Hash) (V : Nat → Byte) (lN dN D : Nat) (c : Byte) (o : Nat) : Byte :=
  let W := mixV V (Spec.Mgf1.mgf1 Gs (srcB V (lN + dN) D) dN) lN dN
  if o = lN then W o &&& c else W o

theorem srcB_congr {V V' : Nat → Byte} {src n : Nat} (h : ∀ i < n, V' (src + i) = V (src + i)) :
    srcB V' src n = srcB V src n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

section
variable {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c)
include L

theorem oV_al (j : Nat) : (off (Sp s) (oV + 8 * j)).toNat % 8 = 0 := by
  have := L.al; have := L.F.wS
  have e : (off (Sp s) (oV + 8 * j)).toNat = (Sp s).toNat + (oV + 8 * j) % 2 ^ 64 ∨
      (off (Sp s) (oV + 8 * j)).toNat = ((Sp s).toNat + (oV + 8 * j) % 2 ^ 64) - 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  unfold oV at *; omega

/-- `spill`: `c`, `salt_len` and the mode to `scratch + oV`. -/
theorem spill_ok {t : State} (h : Base Sp (vP D) s t) (x : Xs s t) :
    WP isa (.block spill) t fun t' => Base Sp (vP D) s t' ∧ (∀ r, t'.gpr r = t.gpr r) ∧
      (∀ o < oSt, view t'.mem (Sp s) o = view t.mem (Sp s) o) ∧
      t'.mem.readW (off (Sp s) oV) 64 = cm s ∧ t'.mem.readW (off (Sp s) (oV + 8)) 64 = s.gpr .a7 ∧
      t'.mem.readW (off (Sp s) (oV + 16)) 64 = anyL s := by
  have F := L.F
  obtain ⟨_, hSt, _, _, hRs⟩ := offs
  have w8 : ∀ {u : State} {d : Nat}, u.wr = t.wr → d + 8 ≤ oRsa → InRegions u.wr (off (Sp s) d) 8 :=
    fun hu hd => by rw [hu, h.wr]; exact sc_inW F hd
  simp only [spill]
  refine wp_sd (a := off (Sp s) oV) (by rw [h.s0]) (by have := oV_al L 0; simpa using this)
    (w8 rfl (by unfold oV; omega)) fun t₁ m₁ => ?_
  refine wp_sd (a := off (Sp s) (oV + 8)) (by rw [m₁.gpr, h.s0]) (oV_al L 1)
    (w8 m₁.wr (by unfold oV; omega)) fun t₂ m₂ => ?_
  refine wp_sd (a := off (Sp s) (oV + 16)) (by rw [m₂.gpr, m₁.gpr, h.s0]) (oV_al L 2)
    (w8 (m₂.wr.trans m₁.wr) (by unfold oV; omega)) fun w mw => wp_nil ?_
  have c8 : ∀ j < 3, Region.Contains ⟨off (Sp s) oV, 24⟩ (off (Sp s) (oV + 8 * j)) (64 / 8) := fun j hj => by
    have := Offset.contains (Sp s) (d := oV + 8 * j) (e := oV) (n := 8) (k := 24) (by omega) (by omega)
      (by unfold oV; omega)
    exact this
  have hf : Frame [⟨off (Sp s) oV, 24⟩] t.mem w.mem := by
    rw [mw.mem, m₂.mem, m₁.mem]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c8 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c8 1 (by omega))).writeW (List.mem_singleton_self _) _ (c8 2 (by omega))
  have hK : Kept [] t w := (m₁.keep.trans (m₂.keep.trans mw.keep)).mono
  have hd : ∀ o < oSt, ¬ Region.Contains ⟨off (Sp s) oV, 24⟩ (off (Sp s) o) 1 := fun o ho hc =>
    Proof.RsaOaep.RISCV64.sdis (s := s) (S := Sp) (a := o) (n := 1) (b := oV) (k := 24) (.inl (by unfold oV; omega))
      (by omega) (by unfold oV; omega) _ (Region.contains_self _ _) hc
  refine ⟨h.keep F hK hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oV; omega))),
    fun r => by rw [mw.gpr, m₂.gpr, m₁.gpr], fun o ho => ?_, ?_, ?_, ?_⟩
  · exact (hf _ fun r hr hc => by rw [List.mem_singleton.mp hr] at hc; exact hd o ho hc)
  · rw [mw.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oV; omega)) (by unfold oV; omega)
      (by unfold oV; omega)) (by decide), m₂.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oV; omega))
      (by unfold oV; omega) (by unfold oV; omega)) (by decide), m₁.mem, Mem.readW_writeW_self64, x.s5]
  · rw [mw.mem, Mem.readW_writeW_sep (Offset.sep _ (.inl (by unfold oV; omega)) (by unfold oV; omega)
      (by unfold oV; omega)) (by decide), m₂.mem, Mem.readW_writeW_self64, m₁.gpr, x.s6]
  · rw [mw.mem, Mem.readW_writeW_self64, m₂.gpr, m₁.gpr, x.s7]

/-- `reload`: `c`, `salt_len` and the mode back from `scratch + oV`. -/
theorem reload_ok {t : State} (h : Base Sp (vP D) s t) (h5 : t.mem.readW (off (Sp s) oV) 64 = cm s)
    (h6 : t.mem.readW (off (Sp s) (oV + 8)) 64 = s.gpr .a7)
    (h7 : t.mem.readW (off (Sp s) (oV + 16)) 64 = anyL s) :
    WP isa (.block reload) t fun t' => Base Sp (vP D) s t' ∧ Xs s t' ∧ Only [.s5, .s6, .s7] t t' := by
  have F := L.F
  obtain ⟨_, hSt, _, _, hRs⟩ := offs
  have r8 : ∀ {u : State} {d : Nat}, u.rd = t.rd → u.wr = t.wr → d + 8 ≤ oRsa →
      InRegions (u.rd ++ u.wr) (off (Sp s) d) 8 := fun hr hw hd => by
    rw [hr, hw, h.wr]; exact sc_inR F hd _
  simp only [reload]
  refine wp_ld (a := off (Sp s) oV) (by rw [h.s0]) (by have := oV_al L 0; simpa using this)
    (r8 rfl rfl (by unfold oV; omega)) fun t₁ o₁ e₁ => ?_
  refine wp_ld (a := off (Sp s) (oV + 8)) (by rw [o₁.get .s0, h.s0]) (oV_al L 1)
    (r8 o₁.rd o₁.wr (by unfold oV; omega)) fun t₂ o₂ e₂ => ?_
  refine wp_ld (a := off (Sp s) (oV + 16)) (by rw [o₂.get .s0, o₁.get .s0, h.s0]) (oV_al L 2)
    (r8 (o₂.rd.trans o₁.rd) (o₂.wr.trans o₁.wr) (by unfold oV; omega)) fun w ow ew => wp_nil ?_
  have k : Only [.s5, .s6, .s7] t w := (o₁.trans (o₂.trans ow)).mono
  exact ⟨h.only F k, ⟨by rw [ow.get .s5, o₂.get .s5, e₁, h5], by rw [ow.get .s6, e₂, o₁.mem, h6],
    by rw [ew, o₂.mem, o₁.mem, h7]⟩, k⟩

/-- MGF1's arguments for unmasking `DB`: `H` after it as the seed. -/
theorem dbArgs_ok {H : Hash} (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) :
    WP isa (.block (dbArgs H)) t fun t' => Base Sp (vP D) s t' ∧ Only [.s8, .s9, .s6, .s7] t t' ∧
      t'.gpr .s6 = off (Sp s) (lN + dN) ∧ t'.gpr .s7 = BitVec.ofNat 64 D ∧ t'.gpr .s8 = off (Sp s) lN ∧
      t'.gpr .s9 = BitVec.ofNat 64 dN := by
  have F := L.F
  have hD64 := L.D64
  subst hD
  refine wp_add fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_add fun t₃ o₃ e₃ =>
    wp_li (imm := H.D) (by omega) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.s8, .s9, .s6, .s7] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have a8 : t₁.gpr .s8 = off (Sp s) lN := by rw [e₁, h.s0, h.plo, L.hlo]
  exact ⟨h.only F k₄, k₄,
    by rw [o₄.get .s6, e₃, o₂.get .s8, a8, o₂.get .s4, o₁.get .s4, h.pdb, L.hdb]; exact off_off _ _ _,
    by rw [e₄], by rw [o₄.get .s8, o₃.get .s8, o₂.get .s8, a8],
    by rw [o₄.get .s9, o₃.get .s9, e₂, o₁.get .s4, h.pdb, L.hdb]⟩

/-- `clearTop`: `DB`'s first byte ANDed with `c`. -/
theorem clearTop_ok {t : State} (h : Base Sp (vP D) s t) (x : Xs s t) :
    WP isa (.block clearTop) t fun w => Base Sp (vP D) s w ∧ Kept [.a1, .a2] t w ∧
      ∀ o < oSt, view w.mem (Sp s) o = if o = lN then view t.mem (Sp s) lN &&& c else view t.mem (Sp s) o := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hl := L.l1
  have a6 : ∀ {u : State}, Only [.a1] t u → u.gpr .a1 = t.gpr .s0 + t.gpr .s3 → u.gpr .a1 = off (Sp s) lN :=
    fun o e => by rw [e, h.s0, h.plo, L.hlo]
  refine wp_add fun t₆ o₆ e₆ => ?_
  refine wp_lbu (a := off (Sp s) lN) (by rw [a6 o₆ e₆, BitVec.add_zero])
    (by rw [o₆.rd, o₆.wr, h.wr]; exact sc_inR F (by unfold oRsa; omega) _) fun t₇ o₇ e₇ => ?_
  refine wp_and fun t₈ o₈ e₈ => wp_sb (a := off (Sp s) lN) (by rw [o₈.get .a1, o₇.get .a1, a6 o₆ e₆,
    BitVec.add_zero]) (by rw [o₈.wr, o₇.wr, o₆.wr, h.wr]; exact sc_inW F (by unfold oRsa; omega)) fun w mw => ?_
  have k₈ : Only [.a1, .a2] t t₈ := (o₆.trans (o₇.trans o₈)).mono
  have hK : Kept [.a1, .a2] t w := (k₈.keep.trans mw.keep).mono
  have hb : (t₈.gpr .a2).setWidth 8 = view t.mem (Sp s) lN &&& c := by
    rw [e₈, e₇, o₇.get .s5, o₆.get .s5, x.s5, L.hc, o₆.mem]
    simp only [BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
    rfl
  have hm : w.mem = t.mem.writeW (off (Sp s) lN) (view t.mem (Sp s) lN &&& c) := by
    rw [mw.mem, hb, k₈.mem]
  refine wp_nil ⟨h.keep F hK (R := [⟨off (Sp s) lN, 1⟩]) (by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in (by unfold oRsa; omega))), hK, fun o ho => ?_⟩
  rw [hm, view_w8 _ _ (by unfold oRsa; omega) (by unfold oSt oRsa at *; omega)]

theorem unmask_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) (hD : H.D = D) {Gs : Spec.Mgf1.Hash}
    (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D) (hGv : Proof.Mgf1.Valid Gs) {t : State}
    (h : Base Sp (vP D) s t) (x : Xs s t) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t', Base Sp (vP D) s t' → Xs s t' →
      (∀ o < oSt, view t'.mem (Sp s) o = dbV Gs (view t.mem (Sp s)) lN dN D c o) → WP isa rest t' Q) :
    WP isa (.seq (.block spill) (.seq (.block (dbArgs H)) (.seq (mgfXor H) (.seq (.block reload)
      (.seq (.block clearTop) rest))))) t Q := by
  have F := L.F
  have hk := L.hk; have hk2 := L.k2; have hd1 := L.d1
  obtain ⟨_, hSt, _, hCt, hRs⟩ := offs
  refine WP.seq (WP.mono (spill_ok L h x) fun t₁ ⟨b₁, _, v₁, w5, w6, w7⟩ => ?_)
  refine WP.seq (WP.mono (dbArgs_ok L hD b₁) fun t₄ ⟨b₄, k₄, x6, x7, x8, x9⟩ => ?_)
  subst hD
  refine WP.seq (WP.mono (mgfXor_ok F hH hF hGh hGl hGv (src := lN + dN) (srcLen := H.D) (dst := lN) (dstLen := dN)
    ⟨by omega, by omega, .inr (by omega), by omega⟩ b₄ x6 x7 x8 x9) fun t₅ ⟨b₅, v₅⟩ => ?_)
  have V4 : view t₄.mem (Sp s) = view t₁.mem (Sp s) := by rw [k₄.mem]
  rw [V4] at v₅
  -- The saved words survive MGF1.
  have keepW : ∀ j < 3, t₅.mem.readW (off (Sp s) (oV + 8 * j)) 64 = t₁.mem.readW (off (Sp s) (oV + 8 * j)) 64 :=
    fun j hj => Mem.readW_congr fun i hi => by
      have e := v₅ (oV + 8 * j + i) ⟨by unfold oV; omega, .inr (by unfold oV; omega)⟩
      rw [mixV, ifn (by unfold oV; omega)] at e
      simp only [view] at e
      show t₅.mem (off (off (Sp s) (oV + 8 * j)) i) = t₁.mem (off (off (Sp s) (oV + 8 * j)) i)
      rw [off_off]; exact e
  have w5' : t₅.mem.readW (off (Sp s) oV) 64 = cm s := by have := keepW 0 (by omega); simp at this; rw [this, w5]
  refine WP.seq (WP.mono (reload_ok L b₅ w5' (by rw [keepW 1 (by omega), w6]) (by rw [keepW 2 (by omega), w7]))
    fun t₆ ⟨b₆, x₆, k₆⟩ => ?_)
  refine WP.seq (WP.mono (clearTop_ok L b₆ x₆) fun w ⟨b, kw, v⟩ => k w b (x₆.of fun r hr => kw.gpr r (by
    revert r; decide)) fun o ho => ?_)
  have V6 : view t₆.mem (Sp s) = view t₅.mem (Sp s) := by rw [k₆.mem]
  have hs : srcB (view t₁.mem (Sp s)) (lN + dN) H.D = srcB (view t.mem (Sp s)) (lN + dN) H.D :=
    srcB_congr fun i hi => v₁ _ (by omega)
  have v5' : ∀ o < oSt, view t₅.mem (Sp s) o =
      mixV (view t.mem (Sp s)) (Spec.Mgf1.mgf1 Gs (srcB (view t.mem (Sp s)) (lN + dN) H.D) dN) lN dN o :=
    fun o ho => by rw [v₅ o ⟨by omega, .inl ho⟩, hs, mixV, mixV, v₁ o ho]
  rw [v o ho, V6, dbV]
  by_cases e : o = lN
  · subst e; rw [ifp rfl, ifp rfl, v5' _ ho]
  · rw [ifn e, ifn e, v5' o ho]

end

end VG.Proof.RsaPss.RISCV64
