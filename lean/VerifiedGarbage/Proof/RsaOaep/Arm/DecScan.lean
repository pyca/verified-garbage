module

public import VerifiedGarbage.Proof.RsaPss.VerifyCases
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.VerifyCases
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step
public import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
meta import VerifiedGarbage.Proof.Bignum.Arm.CompareByteStep
public import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecChk
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Impl.RsaOaep.Arm
import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
meta import VerifiedGarbage.Proof.RsaOaep.Arm.MgfSlots
meta import VerifiedGarbage.Proof.RsaOaep.Arm.DecChk
meta import VerifiedGarbage.Proof.RsaOaep.Mask
meta import VerifiedGarbage.Proof.RsaOaep.Arm.LabelT
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.RsaOaep.Decode
meta import VerifiedGarbage.Proof.RsaOaep.Arm.Calls

/-! ### `RsaOaep.Arm.DecAcc`, which only this module used -/

section

/-! ### `RsaOaep.Arm.DecUnmask`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on ARMv7: `EM` unmasked

The label's hash, through its table, to `scratch + oLh` (`labT_vp`), then the seed unmasked
with MGF1 of `maskedDB` and `DB` with MGF1 of the seed, in place (`mgf_vp`,
with the slots `seedArgs` and `dbArgs` set): `EM`'s place holds `V5`, `EM`
unmasked as `Proof.RsaOaep.chain_eq` states it (`unmask_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sCtr sDone)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

variable (h g : OHash)

/-- What the decoding keeps: the result's slot, and that `k` is long enough. -/
abbrev K0 (P : EP) (σ : State) (m : Mem) : Prop :=
  In P σ ∧ 2 * h.H.D + 2 ≤ P.K ∧ m.readW (P.lay.fr sRes) 32 = rV P σ ∧ OcK P σ

/-- `lHash`, and where it is. -/
abbrev lhB (P : EP) (σ : State) : List Byte := h.G.hash (labB P σ)
abbrev LH (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < h.H.D, m (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0

/-- The seed unmasked (`V3`), then `DB` (`V5`). -/
abbrev mk3 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) h.H.D
abbrev V3 (P : EP) (σ : State) : Nat → Byte := mixV (V P σ) (mk3 h g P σ) 1 h.H.D
abbrev mk5 (P : EP) (σ : State) : List Byte :=
  Spec.Mgf1.mgf1 g.G (srcB (V3 h g P σ) 1 h.H.D) (P.K - h.H.D - 1)
abbrev V5 (P : EP) (σ : State) : Nat → Byte := mixV (V3 h g P σ) (mk5 h g P σ) (1 + h.H.D) (P.K - h.H.D - 1)

theorem srcB_getD (V : Nat → Byte) (a : Nat) {n i : Nat} (hi : i < n) : (srcB V a n).getD i 0 = V (a + i) :=
  Proof.RsaOaep.map_range_getD' (fun i => V (a + i)) hi

theorem srcB_length (V : Nat → Byte) (a n : Nat) : (srcB V a n).length = n := by simp [srcB]

theorem mix_in {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h₁ : e ≤ o) (h₂ : o < e + n) :
    mixV V mk e n o = V o ^^^ mk.getD (o - e) 0 := by
  simp only [mixV]; rw [ifp ⟨h₁, h₂⟩]

theorem mix_out {V : Nat → Byte} {mk : List Byte} {e n o : Nat} (h : o < e ∨ e + n ≤ o) :
    mixV V mk e n o = V o := by
  simp only [mixV]; rw [ifn (by omega_arith)]

section keep
variable {P : EP} {σ : State} {rs : List Region} {m m' : Mem}

theorem K0.keep (hk : K0 h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR P.lay sRes).Disjoint r) :
    K0 h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf hd hk.2.2.1, hk.2.2.2⟩

theorem LH.keep (hl : LH h P σ m) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sR P.scr oLh h.H.D).Disjoint r) :
    LH h P σ m' :=
  sbytes_keep hf hd (by have := h.D_le; oomega) hl

end keep

/-! ## The label's hash -/

/-- After the label's hash. -/
abbrev U1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ (K0 h P σ s.mem ∧ ∀ x < P.K, s.mem (sa P.scr x) = V P σ x) ∧ LH h P σ s.mem

/-- The label's hash function's table, the argument 23, in a buffer only
read. -/
theorem tblL_of {P : EP} {σ : State} (hi : In P σ) :
    ∃ R ∈ P.lay.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA P.tabL o) 4 := by
  have hf := hi.ok.fits P.TABL (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TABL, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tabL, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.tabL + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

/-- What the label's hash keeps, with its table's address in its slot. -/
abbrev L0 (P : EP) (σ : State) (m : Mem) : Prop :=
  (K0 h P σ m ∧ ∀ x < P.K, m (sa P.scr x) = V P σ x) ∧ m.readW (P.lay.fr sTab) 32 = P.tabL

/-- The label's hash function's table's address to its slot, and the label's
hash, with that table's hash function `h`. -/
theorem labT_vp (P : EP) {f : Fns} (hTL : ∀ σ, P.TL σ → TabFacts h.H f P.tabL P.aiL P.auL P.afL σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => (C2 h.H.D P σ s ∧ isa.eval .ne s = some false) ∧ s.syms = σ.syms)
      (.seq (.block (tabSlot 23)) (hashLabelT f 17 oLh)) (fun σ s => U1 h P σ s ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1.2.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have := h.S_le; have := h.Wb_le; have := h.F_le; have := h.D_le
  have hb : RBuf P.lay P.lab P.ll := by
    have hf := ok.fits P.LAB (by simp)
    simp only [Proof.X25519.Arm.addr_toNat] at hf
    exact ⟨hf, hi₀.ll32, ⟨P.LAB, by simp, Region.contains_self _ _⟩⟩
  -- The table's address to its slot.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ L0 h P σ s.mem) ∧ s.syms = σ.syms)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.1.st.sp.trans h₂.1.1.1.st.sp.symm)
      fun σ s ⟨⟨⟨hc, hi, he, hres, hk, z⟩, e⟩, sy⟩ => ?_) ?_
  · have hkD : 2 * h.H.D + 2 ≤ P.K := by
      rw [VG.Proof.X25519.Arm.eval_ne] at e
      have z' : s.z = true := by cases hz : s.z <;> simp_all
      rw [z'] at z
      exact of_decide_eq_true z.symm
    refine WP.mono (tabA_wp hg hc (j := 23) (by simp) (arg_lt (by decide))) fun t ⟨m, rd, wr, sp, _, _, ty⟩ => ?_
    have fr : Frame [slotR P.lay sTab] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
    refine ⟨⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
      ⟨⟨hi, hkD, slot_keep fr (fun r hr => ?_) hres, hk⟩, em_keep fr (fun r hr => ?_) (by omega_arith) he⟩, ?_⟩,
      ty.trans sy⟩
    · rw [List.mem_singleton.mp hr]; exact slotW hg (by decide)
    · rw [List.mem_singleton.mp hr]; exact slotSep (by decide) (by decide) (by decide)
    · rw [List.mem_singleton.mp hr]; exact slotSep (by decide) (by decide) (by decide)
    · rw [List.mem_singleton.mp hr]; exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · rw [m, Mem.readW_writeW_self32]; rfl
  -- The label's hash.
  refine (labelT_vp hg h (f := f) (p := P.tabL) (ai := P.aiL) (au := P.auL) (af := P.afL) (tblL_of hi₀) fne
    (j := 17) (o := oLh) (ll := P.ll) (lab := P.lab) (by simp) (arg_lt (by decide))
    (arg_lt (by decide)) rfl rfl hb (hg.ro ok (by oomega) (R := P.LAB) (by simp)).symm
    (hg.ro ok (by oomega) (R := P.LAB) (by simp)).symm (ok.low_buf (R := P.LAB) (.inl (by simp))).symm
    (by oomega) (by oomega) (labB := labB P) (fun σ s hc => hc.st.ro (R := P.LAB) (by simp))
    (Inv := L0 h P) ?_ (fun _ _ hm => hm.2) (fun σ _ hm => hTL σ hm.1.1.1.tabTL)).mono
    (fun _ _ h => h) fun σ s ⟨⟨hc, ⟨hk, _⟩, hd⟩, sy⟩ => ⟨⟨hc, hk, hd⟩, sy⟩
  intro σ m m' ⟨⟨hk, he⟩, hs⟩ hf
  have dslot : ∀ d, d + 4 ≤ frameBytes → ∀ r ∈ [sR P.scr oSt h.H.S, sR P.scr oW h.ok.Wb, P.lay.LOW,
      sR P.scr oLh h.H.F], (slotR P.lay d).Disjoint r := fun d hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hg.slot ok (by oomega) (by rw [hg.F]; omega_arith)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; omega_arith)
    · exact Lay.fr_low (by have : frameBytes ≤ 2 ^ 32 := (by decide); omega_arith)
    · exact hg.slot ok (by oomega) (by rw [hg.F]; omega_arith)
  refine ⟨⟨hk.keep h hf (dslot sRes (by decide)), em_keep hf (fun r hr => ?_) (by omega_arith) he⟩,
    slot_keep hf (dslot sTab (by decide)) hs⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)
  · exact hg.low ok (by oomega)
  · exact Geo.sep (by oomega) (by oomega) (by oomega)

/-! ## The seed -/

/-- What unmasking keeps: `K0`, `lHash` and `EM`'s first byte. -/
abbrev X1 (P : EP) (σ : State) (m : Mem) : Prop := K0 h P σ m ∧ LH h P σ m ∧ m (sa P.scr 0) = V P σ 0

theorem x1_keep {P : EP} (hg : Geo P.lay P.scr) {dOff dl : Nat} (hfd : dOff + dl ≤ oBuf) (h0 : 0 < dOff) :
    ∀ σ m m', X1 h P σ m → Frame (mgfW g P.lay P.scr dOff dl) m m' → X1 h P σ m' := by
  intro σ m m' ⟨hk, hl, h0'⟩ hf
  have := g.S_le; have := g.Wb_le; have := g.F_le; have := h.D_le
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hk.keep h hf (mgfW_slot g hg hfd (by decide) (by decide) (by decide)), hl.keep h hf fun r hr => ?_, ?_⟩
  · simp only [mgfW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact hg.low ok (by oomega)
    · exact Geo.sep (by oomega) (by oomega) (by oomega)
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · rw [← h0']
    have e := hf _ fun r hr => mgfW_byte g hg hfd (o := oEm + 0) (by oomega) (by oomega) r hr _
      (Region.contains_self _ _)
    simpa [sa, oEm] using e

/-- Four slots written. -/
theorem frame4 (L : Lay) (m : Mem) (a b c d : BitVec 32) :
    Frame [slotR L sDst, slotR L sDstLen, slotR L sSrc, slotR L sSrcLen] m
      ((((m.writeW (L.fr sDst) a).writeW (L.fr sDstLen) b).writeW (L.fr sSrc) c).writeW (L.fr sSrcLen) d) :=
  (((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))).trans
    ((slot_frame _ _ _ _).mono (by simp)) |>.trans ((slot_frame _ _ _ _).mono (by simp))

theorem dis4 {P : EP} (hg : Geo P.lay P.scr) {o n : Nat} (hon : o + n ≤ oRsa) :
    ∀ r ∈ [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen],
      (sR P.scr o n).Disjoint r := by
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm

theorem x1_keep4 {P : EP} (hg : Geo P.lay P.scr) {σ : State} {m m' : Mem}
    (hf : Frame [slotR P.lay sDst, slotR P.lay sDstLen, slotR P.lay sSrc, slotR P.lay sSrcLen] m m')
    (hx : X1 h P σ m) : X1 h P σ m' := by
  have := h.D_le
  refine ⟨hx.1.keep h hf fun r hr => ?_, hx.2.1.keep h hf (dis4 hg (by oomega)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hx.2.2]
    have e := sbytes_keep (o := 0) (n := 1) hf (dis4 hg (by oomega)) (by decide)
      (f := fun _ => m (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)
    simpa using e

/-- The slots for unmasking the seed with MGF1 of `maskedDB`. -/
theorem seed_vp (P : EP) :
    VP (U1 h P) (.block (seedArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i)) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hk, he⟩, hl⟩ => ?_
  have hi := hk.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hk.2.1
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have hw : WP isa (.block (seedArgs h.H 4)) s fun t =>
      t.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW
        (P.lay.fr sDstLen) (BitVec.ofNat 32 h.H.D)).writeW (P.lay.fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW (P.lay.fr sSrcLen)
            (BitVec.ofNat 32 (P.K - h.H.D - 1)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [seedArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a4, r4, v4, arg_lt,
      sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega_arith),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega_arith),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega_arith), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr := frame4 P.lay s.mem (P.scr + BitVec.ofNat 32 (oEm + 1)) (BitVec.ofNat 32 h.H.D)
    (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)) (BitVec.ofNat 32 (P.K - h.H.D - 1))
  rw [← m] at fr
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨x1_keep4 h hg fr ⟨hk, hl, he 0 (by omega_arith)⟩, ?_, ?_, ?_, ?_⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · have e := em_keep fr (dis4 hg (by oomega)) (by omega_arith) he (1 + i) (by omega_arith)
    rwa [show oEm + 1 + i = 1 + i by oomega]
  · rw [srcB_getD _ _ hi']
    have e := em_keep fr (dis4 hg (by oomega)) (by omega_arith) he (1 + h.H.D + i) (by omega_arith)
    rwa [show oEm + 1 + h.H.D + i = 1 + h.H.D + i by oomega]

/-- The slots for unmasking `DB` with MGF1 of the seed. -/
theorem db_vp (P : EP) :
    VP (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1 + h.H.D) (P.K - h.H.D - 1) (oEm + 1) h.H.D s.mem) ∧
        (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = V P σ (1 + i) ^^^ (mk3 h g P σ).getD i 0) ∧
        ∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) =
          (srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)).getD i 0)
      (.block (dbArgs h.H 4))
      (fun σ s => Ctx P.lay P.scr σ s ∧
        (X1 h P σ s.mem ∧ Sl P.lay P.scr (oEm + 1) h.H.D (oEm + 1 + h.H.D) (P.K - h.H.D - 1) s.mem) ∧
        (∀ i < P.K - h.H.D - 1, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = V3 h g P σ (1 + h.H.D + i)) ∧
        ∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + i)) = (srcB (V3 h g P σ) 1 h.H.D).getD i 0) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hx, _⟩, hsd, hdb⟩ => ?_
  have hi := hx.1.1
  have hg := hi.geo
  have hK := hi.k1024
  have hD := h.D_le
  have hfit := hx.1.2.1
  obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
  replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
  have hw : WP isa (.block (dbArgs h.H 4)) s fun t =>
      t.mem = (((s.mem.writeW (P.lay.fr sDst) (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D))).writeW
        (P.lay.fr sDstLen) (BitVec.ofNat 32 (P.K - h.H.D - 1))).writeW (P.lay.fr sSrc)
          (P.scr + BitVec.ofNat 32 (oEm + 1))).writeW (P.lay.fr sSrcLen) (BitVec.ofNat 32 h.H.D) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [dbArgs, atS, sp0, ld, st, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hc.slotS, a4, r4, v4, arg_lt,
      sDst_lt, sDstLen_lt, sSrc_lt, sSrcLen_lt,
      movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show h.H.D + 1 < 2 ^ 16 by omega_arith),
      movw_val (show oEm + 1 < 2 ^ 16 by decide), movw_val (show h.H.D < 2 ^ 16 by omega_arith),
      Offset.ofNat_sub_ofNat (show h.H.D + 1 ≤ P.K by omega_arith), Nat.sub_add_eq]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr := frame4 P.lay s.mem (P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D)) (BitVec.ofNat 32 (P.K - h.H.D - 1))
    (P.scr + BitVec.ofNat 32 (oEm + 1)) (BitVec.ofNat 32 h.H.D)
  rw [← m] at fr
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp,
    ⟨x1_keep4 h hg fr hx, ?_, ?_, ?_, ?_⟩, fun i hi' => ?_, fun i hi' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), slot_ww _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]
  · rw [V3, mix_out (by omega_arith), sbytes_keep fr (dis4 hg (by oomega)) (by oomega) hdb i hi', srcB_getD _ _ hi']
  · rw [srcB_getD _ _ hi', V3, mix_in (by omega_arith) (by omega_arith), show 1 + i - 1 = i by omega_arith]
    exact sbytes_keep fr (dis4 hg (by oomega)) (by oomega) hsd i hi'

/-! ## Unmasking -/

/-- After unmasking: `EM`'s place holds `V5`. -/
abbrev U5 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ X1 h P σ s.mem ∧ ∀ x < P.K, s.mem (sa P.scr x) = V5 h g P σ x

/-- MGF1's table, the argument 24, in a buffer only read. -/
theorem tbl_of {P : EP} {σ : State} (hi : In P σ) :
    ∃ R ∈ P.lay.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA (P.lay.argv.getD 24 0) o) 4 := by
  have hf := hi.ok.fits P.TAB (by simp)
  simp only [Sig.tableRegion, Proof.X25519.Arm.addr_toNat] at hf
  refine ⟨P.TAB, by simp, fun o ho => ?_⟩
  show (⟨State.addr P.tab, 11 * (32 / 8)⟩ : Region).Contains (State.addr (P.tab + BitVec.ofNat 32 o)) 4
  rw [VG.Arm.addr_add (by omega_using [hf, ho])]
  exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])

theorem unmask_vp (P : EP) {f : Fns} (hT : ∀ σ, P.T σ → TabFacts g.H f P.tab P.ai P.au P.af σ)
    (fne : f.init ≠ [] ∧ f.upd ≠ [] ∧ f.fin ≠ []) :
    VP (fun σ s => U1 h P σ s ∧ s.syms = σ.syms)
      (.seq (.block (seedArgs h.H 4)) (.seq (mgfXor f 24) (.seq (.block (dbArgs h.H 4)) (mgfXor f 24))))
      (fun σ s => U5 h g P σ s ∧ s.syms = σ.syms) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.2.1.1.1, hs.1.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have tab : ∀ σ m, X1 h P σ m → TabFacts g.H f (P.lay.argv.getD 24 0) P.ai P.au P.af σ :=
    fun σ m hx => hT σ hx.1.1.tabT
  have P1 := mpOf g hg (so := oEm + 1 + h.H.D) (sl := P.K - h.H.D - 1) (dOff := oEm + 1) (dl := h.H.D)
    (by omega_arith) hD0 (by oomega) (by oomega) (.inr (Nat.le_refl _))
    (seed := fun σ => srcB (V P σ) (1 + h.H.D) (P.K - h.H.D - 1)) (fun σ => srcB_length _ _ _)
    (x1_keep h g hg (by oomega) (by oomega)) (by simp) (tbl_of hi₀) tab fne
  have P2 := mpOf g hg (so := oEm + 1) (sl := h.H.D) (dOff := oEm + 1 + h.H.D) (dl := P.K - h.H.D - 1) hD0
    (by omega_arith) (by oomega) (by oomega) (.inl (Nat.le_refl _)) (seed := fun σ => srcB (V3 h g P σ) 1 h.H.D)
    (fun σ => srcB_length _ _ _) (x1_keep h g hg (by oomega) (by oomega)) (by simp) (tbl_of hi₀) tab fne
  refine VP.seq (VP.syms (seed_vp h P)) (VP.seq (mgf_vp g P1 (dstv := fun σ i => V P σ (1 + i)) (arg_lt (by decide)))
    (VP.seq (VP.syms (db_vp h g P)) ((mgf_vp g P2 (dstv := fun σ i => V3 h g P σ (1 + h.H.D + i))
      (arg_lt (by decide))).mono
      (fun _ _ hh => hh) fun σ s ⟨⟨hc, ⟨hx, _⟩, hdb, hsd⟩, sy⟩ => ⟨⟨hc, hx, fun x hx' => ?_⟩, sy⟩)))
  by_cases h0 : x = 0
  · subst h0
    rw [hx.2.2, V5, mix_out (by omega_arith), V3, mix_out (by omega_arith)]
  by_cases h1 : x < 1 + h.H.D
  · have e := hsd (x - 1) (by omega_arith)
    rw [show oEm + 1 + (x - 1) = x by oomega, srcB_getD _ _ (by omega_arith), show 1 + (x - 1) = x by omega_arith] at e
    rw [e, V5, mix_out (by omega_arith)]
  · have e := hdb (x - 1 - h.H.D) (by omega_arith)
    rw [show oEm + 1 + h.H.D + (x - 1 - h.H.D) = x by oomega, show 1 + h.H.D + (x - 1 - h.H.D) = x by omega_arith] at e
    rw [e, V5, mix_in (by omega_arith) (by omega_arith), show x - (1 + h.H.D) = x - 1 - h.H.D by omega_arith]

end VG.Proof.RsaOaep.Arm.Dec

end

end

/-!
# RSAES-OAEP decryption on ARMv7: `EM`'s first byte and `lHash`

`cmpS_vp`: `compareBytes` of two ranges of our part of `scratch` leaves in
`r2` a byte, zero exactly when they are equal. `acc_vp`: the accumulator
`acc` (in its slot) is a byte, zero exactly when `EM`'s first byte is zero
and `lHash' = lHash`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Bignum.Arm (CompareCtx CompareInv compareBody_ok)
open VG.Proof.X25519.Arm (dpVal)

/-- A byte or'ed with the xor of two bytes is a byte. -/
theorem or_xor_lt {x : BitVec 32} (hx : x.toNat < 256) (a b : Byte) :
    (x ||| (a.setWidth 32 ^^^ b.setWidth 32)).toNat < 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_xor, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have ha : a.toNat % 2 ^ 32 < 2 ^ 8 := by have := a.isLt; omega_arith
  have hb : b.toNat % 2 ^ 32 < 2 ^ 8 := by have := b.isLt; omega_arith
  exact Nat.or_lt_two_pow (n := 8) hx (Nat.xor_lt_two_pow ha hb)

/-- `compareBytes`, with `r2` a byte. -/
theorem cmp_ok (s : State) {a b : BitVec 32} {n : Nat} (ctx : CompareCtx s a b n) (hn : 0 < n)
    (ha : s.gpr .r0 = a) (hb : s.gpr .r1 = b) (hc : s.gpr .lr = BitVec.ofNat 32 n) (hz : s.gpr .r2 = 0) :
    WP isa Impl.Bignum.Arm.compareBytes s fun t => CompareInv s a b n n t ∧ (t.gpr .r2).toNat < 256 := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ CompareInv s a b n i t ∧ (t.gpr .r2).toNat < 256
  unfold Impl.Bignum.Arm.compareBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi, hr⟩ := h
    have ra := ctx.readA i (by omega_arith)
    have rb := ctx.readB i (by omega_arith)
    rw [← hi.rest.rd, ← hi.rest.wr] at ra rb
    refine WP.mono (WP.and (compareBody_ok ctx hi (by omega_arith))
      (VG.Proof.Bignum.Arm.compareByteStep_ok t _ _ (by rw [hi.first]; simp) (by rw [hi.second]; simp) ra rb)) ?_
    rintro u ⟨⟨hu, zero⟩, ⟨-, -, -, acc, -⟩⟩
    have hb' : (u.gpr .r2).toNat < 256 := by rw [acc]; exact or_xor_lt hr _ _
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu, hb'⟩
      change some (!u.z) = some false
      simp only [zero, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, hu, hb'⟩
      change some (!u.z) = some true
      simp only [zero, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_arith, hn, ?_, by rw [hz]; decide⟩
    exact ⟨by omega_arith, by simpa using ha, by simpa using hb, by simpa using hc,
      by simp [hz], rfl, VG.Proof.X25519.Arm.Rest.refl _ _⟩

variable {L : Lay} {scr : BitVec 32}

/-- `compareBytes` of the `n` bytes at `a` and at `b` in our part of `scratch`. -/
theorem cmpS_vp (hg : Geo L scr) {a b n : Nat} (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa) (hn : 0 < n)
    {X : State → Mem → Prop} {f f' : State → Nat → Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 a ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 b ∧ s.gpr .lr = BitVec.ofNat 32 n ∧ s.gpr .r2 = 0 ∧
        (∀ i < n, s.mem (sa scr (a + i)) = f σ i) ∧ ∀ i < n, s.mem (sa scr (b + i)) = f' σ i)
      Impl.Bignum.Arm.compareBytes
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
        (s.gpr .r2 = 0 ↔ ∀ i < n, f σ i = f' σ i)) := by
  have fa := fitS hg (o := a) (n := n) ha
  have fb := fitS hg (o := b) (n := n) hb
  refine VP.ct VG.Proof.Bignum.Arm.compareBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.1, h₂.2.2.2.1], by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩)
    fun σ s ⟨hc, hx, r0, r1, lr, r2, hf, hf'⟩ => ?_
  have ctx : CompareCtx s (scr + BitVec.ofNat 32 a) (scr + BitVec.ofNat 32 b) n :=
    ⟨by unfold oRsa at ha; omega_arith,
      fun i hi => by rw [byte32 fa hi, hg.byteAt_scr (by omega_arith)]; exact hg.rd hc.st (by omega_arith),
      fun i hi => by rw [byte32 fb hi, hg.byteAt_scr (by omega_arith)]; exact hg.rd hc.st (by omega_arith)⟩
  refine WP.mono (cmp_ok s ctx hn r0 r1 lr r2) fun t ⟨inv, bnd⟩ => ?_
  refine ⟨hc.regs inv.rest.rd inv.rest.wr inv.rest.sp inv.mem, by rw [inv.mem]; exact hx, bnd, ?_⟩
  rw [inv.equal]
  refine forall_congr' fun i => imp_congr_right fun hi' => ?_
  rw [byte32 fa hi', byte32 fb hi', hg.byteAt_scr (by omega_arith), hg.byteAt_scr (by omega_arith), hf i hi', hf' i hi']

variable (h g : OHash)

/-- What the checks keep: `X1` and `EM` unmasked. -/
abbrev Y (P : EP) (σ : State) (m : Mem) : Prop := X1 h P σ m ∧ ∀ x < P.K, m (sa P.scr x) = V5 h g P σ x

/-- `EM`'s first byte is zero and `lHash' = lHash`. -/
abbrev hdOk (P : EP) (σ : State) : Prop :=
  V P σ 0 = 0 ∧ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0

/-- After the checks of `EM`'s first byte and `lHash'`. -/
abbrev A1 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ ∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ a.toNat < 256 ∧
    (a = 0 ↔ hdOk h g P σ)

theorem accPut_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block accPut) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem byte_or_lt {x : BitVec 32} (hx : x.toNat < 256) (b : Byte) : (x ||| b.setWidth 32).toNat < 256 := by
  rw [BitVec.toNat_or, BitVec.toNat_setWidth]
  exact Nat.or_lt_two_pow (n := 8) hx (by have := b.isLt; omega_arith)

theorem setWidth_byte_eq_zero (b : Byte) : b.setWidth 32 = 0 ↔ b = 0 := by
  constructor
  · intro e; have := congrArg (BitVec.setWidth 8) e; simpa using this
  · rintro rfl; rfl

theorem acc_vp (P : EP) :
    VP (U5 h g P)
      (.seq (.block (cmpSet h.H)) (.seq Impl.Bignum.Arm.compareBytes (.seq (.block accSet)
        (.seq (.block accPut) (.block accSave)))))
      (A1 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1, hs.2.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  -- The comparison's registers.
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧ s.gpr .r1 = P.scr + BitVec.ofNat 32 oLh ∧
      s.gpr .lr = BitVec.ofNat 32 h.H.D ∧ s.gpr .r2 = 0 ∧
      (∀ i < h.H.D, s.mem (sa P.scr (oEm + 1 + h.H.D + i)) = V5 h g P σ (1 + h.H.D + i)) ∧
      ∀ i < h.H.D, s.mem (sa P.scr (oLh + i)) = (lhB h P σ).getD i 0)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx, he⟩ => ?_) ?_
  · have hw : WP isa (.block (cmpSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + h.H.D) ∧
        t.gpr .r1 = P.scr + BitVec.ofNat 32 oLh ∧ t.gpr .lr = BitVec.ofNat 32 h.H.D ∧ t.gpr .r2 = 0 := by
      prun [cmpSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm + 1 + h.H.D < 2 ^ 16 by oomega), movw_val (show oLh < 2 ^ 16 by decide),
        movw_val (show h.H.D < 2 ^ 16 by omega_arith)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ => ⟨hc.regs rd wr sp m, m ▸ ⟨hx, he⟩, r0, r1, lr, r2,
      fun i hi => ?_, fun i hi => by rw [m]; exact hx.2.1 i hi⟩
    rw [m, show oEm + 1 + h.H.D + i = 1 + h.H.D + i by oomega]; exact he _ (by omega_arith)
  refine VP.seq (cmpS_vp hg (a := oEm + 1 + h.H.D) (b := oLh) (n := h.H.D) (by oomega) (by oomega) hD0
    (X := Y h g P) (f := fun σ i => V5 h g P σ (1 + h.H.D + i)) (f' := fun σ i => (lhB h P σ).getD i 0)) ?_
  -- `EM`'s first byte.
  refine VP.seq (G := fun σ s => (Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
      (s.gpr .r2 = 0 ↔ ∀ i < h.H.D, V5 h g P σ (1 + h.H.D + i) = (lhB h P σ).getD i 0)) ∧
      s.gpr .r0 = P.scr + BitVec.ofNat 32 oEm)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s hs => ?_) ?_
  · have hc := hs.1
    have hw : WP isa (.block accSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 oEm ∧ t.gpr .r2 = s.gpr .r2 := by
      prun [accSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oEm < 2 ^ 16 by decide)]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r2⟩ =>
      ⟨⟨hc.regs rd wr sp m, m ▸ hs.2.1, r2 ▸ hs.2.2.1, r2 ▸ hs.2.2.2⟩, r0⟩
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧ (s.gpr .r2).toNat < 256 ∧
      (s.gpr .r2 = 0 ↔ hdOk h g P σ))
    (VP.taint _ accPut_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨⟨hc, hy, hb, he⟩, r0⟩ => ?_) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁.2, h₂.2]
  · have s0 : sa P.scr 0 = State.addr P.scr := by simp [sa]
    have a0 : State.addr (P.scr + BitVec.ofNat 32 oEm) = State.addr P.scr := (hg.addr (by oomega)).trans s0
    have rd0 : InRegions (s.rd ++ s.wr) (State.addr P.scr) 1 := s0 ▸ hg.rd hc.st (by oomega)
    have hw : WP isa (.block accPut) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r2 = s.gpr .r2 ||| (s.mem (sa P.scr 0)).setWidth 32 := by
      rw [s0]
      prun [accPut, r0, a0, rd0, dpVal]
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r2⟩ => ⟨hc.regs rd wr sp m, m ▸ hy, ?_, ?_⟩
    · rw [r2]; exact byte_or_lt hb _
    · rw [r2, or_eq_zero32, he, setWidth_byte_eq_zero, hy.1.2.2]
      exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  -- `acc` to its slot.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hy, hb, he⟩ => ?_
  have hi := hy.1.1.1
  have hw : WP isa (.block accSave) s fun t => t.mem = s.mem.writeW (P.lay.fr sAcc) (s.gpr .r2) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [accSave, sp0, st, hc.st.sp, slotAt hi (d := sAcc) (by decide),
      hc.st.inFr (d := sAcc) (n := 4) (by show sAcc + 4 ≤ frameBytes; decide)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sAcc] s.mem t.mem := by rw [m]; exact slot_frame _ _ _ _
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hy.1.1.keep h fr fun r hr => ?_,
    hy.1.2.1.keep h fr fun r hr => ?_, ?_⟩, em_keep fr (fun r hr => ?_) (by omega_arith) hy.2⟩,
    s.gpr .r2, by rw [m, Mem.readW_writeW_self32], hb, he⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact slotW hg (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr; exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm
  · rw [← hy.1.2.2]
    have e := em_keep (n := 1) fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm) (by decide)
      (f := fun _ => s.mem (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)
    exact e
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hg.slot ok (by oomega) (by rw [hg.F]; decide)).symm

end VG.Proof.RsaOaep.Arm.Dec

end

end

/-!
# RSAES-OAEP decryption on ARMv7: the scan of `T`

`scan_vp`: the scan of `n` bytes of our part of `scratch` finds the index
(`pzS`) and the value (`vzS`) of their first byte that is not zero, if any
(`nfS`), without a branch. `tscan_vp`: on `T = DB[hLen..]`, then `acc`
takes in that this byte is `0x01`, and `idx` goes to its slot.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (sp0 ld st mw atS frameBytes sS oRsa arg sAcc sPos countLoop scanBody)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.X25519.Arm (dpVal)

/-! ## The scan -/

section Scan

/-- The bytes, as a list. -/
abbrev sL (n : Nat) (f : Nat → Byte) : List Byte := (List.range n).map f

/-- Where the zeros end. -/
abbrev lzS (n : Nat) (f : Nat → Byte) : Nat := RsaPss.lz (sL n f)

/-- The index and value of the first byte not zero, after `j` bytes, and
whether none was found. -/
abbrev pzS (n : Nat) (f : Nat → Byte) (j : Nat) : Nat := if lzS n f < j then lzS n f else 0
abbrev vzS (n : Nat) (f : Nat → Byte) (j : Nat) : Byte := if lzS n f < j then f (lzS n f) else 0
abbrev nfS (n : Nat) (f : Nat → Byte) (j : Nat) : BitVec 32 := if lzS n f < j then 0 else BitVec.allOnes 32

theorem bz : ∀ b : Byte, (b.setWidth 32 - 1) >>> 31 = if b = 0 then 1 else 0 := by decide

/-- After `j` bytes of the scan of the `n` bytes at `o`. -/
structure SC (scr : BitVec 32) (o n : Nat) (f : Nat → Byte) (j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (o + j)
  r1 : s.gpr .r1 = BitVec.ofNat 32 j
  lr : s.gpr .lr = BitVec.ofNat 32 (n - j)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (pzS n f j)
  r5 : s.gpr .r5 = (vzS n f j).setWidth 32
  r6 : s.gpr .r6 = nfS n f j
  r7 : s.gpr .r7 = 0

theorem scanBody_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr])
    (.block scanBody) hc).isSome = true := ⟨_, by taint_decide⟩

theorem sL_getD {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) : (sL n f).getD j 0 = f j := by
  simp [sL, List.getD_eq_getElem?_getD, hj]

theorem sL_length (n : Nat) (f : Nat → Byte) : (sL n f).length = n := by simp [sL]

theorem lzS_le (n : Nat) (f : Nat → Byte) : lzS n f ≤ n := by
  have e := RsaPss.lz_le (sL n f); rwa [sL_length] at e

/-- One byte of the scan. -/
theorem scan_step {n : Nat} {f : Nat → Byte} {j : Nat} (hj : j < n) (b : Byte) (hb : b = f j) :
    let r3 : BitVec 32 := if b = 0 then 1 else 0
    let r8 := (r3 - 1) &&& nfS n f j
    BitVec.ofNat 32 (pzS n f j) ||| BitVec.ofNat 32 j &&& r8 = BitVec.ofNat 32 (pzS n f (j + 1)) ∧
    (vzS n f j).setWidth 32 ||| b.setWidth 32 &&& r8 = (vzS n f (j + 1)).setWidth 32 ∧
    nfS n f j &&& (0 - r3) = nfS n f (j + 1) := by
  intro r3 r8
  have az : ∀ x : BitVec 32, x &&& 0 = 0 := fun x => BitVec.and_zero
  have za : ∀ x : BitVec 32, 0 &&& x = 0 := fun x => BitVec.zero_and
  have oz : ∀ x : BitVec 32, x ||| 0 = x := fun x => BitVec.or_zero
  have zo : ∀ x : BitVec 32, 0 ||| x = x := fun x => BitVec.zero_or
  have hlt := lzS_le n f
  rcases Nat.lt_trichotomy (lzS n f) j with hl | hl | hl
  · have h8 : r8 = 0 := by simp only [r8, nfS, ite_eq_left hl, az]
    simp only [h8, az, oz, pzS, vzS, nfS, ite_eq_left hl, ite_eq_left (by omega_arith : lzS n f < j + 1), za]
    exact ⟨trivial, trivial, trivial⟩
  · have hne : b ≠ 0 := by
      rw [hb, ← hl, ← sL_getD (n := n) (f := f) (by omega_arith)]
      exact RsaPss.getD_lz_ne (by rw [sL_length]; show lzS n f < n; omega_arith)
    have h3 : r3 = 0 := by simp only [r3, hne, ite_false]
    have h8 : r8 = BitVec.allOnes 32 := by
      simp only [r8, h3, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith)]; decide
    simp only [h8, h3, BitVec.and_allOnes, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith),
      ite_eq_left (show lzS n f < j + 1 by omega_arith)]
    have sz : (0 : Byte).setWidth 32 = 0 := rfl
    refine ⟨by rw [hl, BitVec.zero_or], by rw [hl, hb, sz, zo], by decide⟩
  · have hz : b = 0 := by rw [hb, ← sL_getD (n := n) (f := f) hj]; exact RsaPss.getD_lt_lz hl
    have h3 : r3 = 1 := by simp only [r3, hz, ite_true]
    have h8 : r8 = 0 := by
      simp only [r8, h3]; rw [show (1 : BitVec 32) - 1 = 0 by decide, za]
    simp only [h8, h3, az, oz, pzS, vzS, nfS, ite_eq_right (show ¬ lzS n f < j by omega_arith),
      ite_eq_right (show ¬ lzS n f < j + 1 by omega_arith)]
    exact ⟨trivial, trivial, by decide⟩

variable {L : Lay} {scr : BitVec 32}

/-- The scan of the `n` bytes at `o`. -/
theorem scan_vp (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) (hn : 0 < n) {f : State → Nat → Byte}
    {X : State → Mem → Prop} (hX : ∀ σ m, X σ m → ∀ i < n, m (sa scr (o + i)) = f σ i) :
    VP (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ SC scr o n (f σ) 0 s)
      (countLoop scanBody)
      (fun σ s => Ctx L scr σ s ∧ X σ s.mem ∧ SC scr o n (f σ) n s) := by
  have e2 : oRsa = 8192 := rfl
  have fit := hg.fit
  let I : Nat → State → State → Prop := fun k σ s => k ≤ n ∧ Ctx L scr σ s ∧ X σ s.mem ∧
    SC scr o n (f σ) (n - k) s
  refine (VP.loop (I := I) (fun k => ?_) (n - 1)).mono (fun σ s ⟨hc, hx, hs⟩ => ⟨by omega_arith, hc, hx,
    by rw [show n - (n - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  refine VP.taint _ scanBody_cert (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hk, hc, hx, hs⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
  generalize hj : n - (k + 1) = j at hs
  have hjn : j < n := by omega_arith
  have ad : State.addr (scr + BitVec.ofNat 32 (o + j)) = sa scr (o + j) := hg.addr (by omega_arith)
  have rd : InRegions (s.rd ++ s.wr) (sa scr (o + j)) 1 := hg.rd hc.st (by omega_arith)
  have lr1 : BitVec.ofNat 32 (n - j) - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [show n - j = (n - (j + 1)) + 1 by omega_arith]; exact sub_one_ofNat (by omega_arith)
  have hw : WP isa (.block scanBody) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r0 = scr + BitVec.ofNat 32 (o + (j + 1)) ∧ t.gpr .r1 = BitVec.ofNat 32 (j + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (n - (j + 1)) ∧
      t.gpr .r4 = BitVec.ofNat 32 (pzS n (f σ) j) ||| BitVec.ofNat 32 j &&&
        ((if f σ j = 0 then 1 else 0) - 1 &&& nfS n (f σ) j) ∧
      t.gpr .r5 = (vzS n (f σ) j).setWidth 32 ||| (f σ j).setWidth 32 &&&
        ((if f σ j = 0 then 1 else 0) - 1 &&& nfS n (f σ) j) ∧
      t.gpr .r6 = nfS n (f σ) j &&& (0 - if f σ j = 0 then 1 else 0) ∧ t.gpr .r7 = 0 ∧
      t.z = decide (n - (j + 1) = 0) := by
    prun [scanBody, hs.r0, hs.r1, hs.lr, hs.r4, hs.r5, hs.r6, hs.r7, ad, rd, hX σ s.mem hx j hjn, bz, lr1, dpVal]
    refine ⟨?_, ?_, ?_⟩
    · rw [BitVec.add_assoc, VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
    · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 _
    · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  refine WP.mono hw fun t ⟨m, rd', wr, sp, r0, r1, lr, r4, r5, r6, r7, z⟩ => ?_
  have st := scan_step hjn _ rfl (f := f σ)
  have hc' : Ctx L scr σ t := hc.regs rd' wr sp m
  have hx' : X σ t.mem := m ▸ hx
  have sk : SC scr o n (f σ) (j + 1) t :=
    ⟨r0, r1, lr, by rw [r4]; exact st.1, by rw [r5]; exact st.2.1, by rw [r6]; exact st.2.2, r7⟩
  refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, show n - (j + 1) = k by omega_arith]; cases k <;> simp,
    fun h0 => ⟨hc', hx', by obtain rfl : n = j + 1 := (by omega_arith); exact sk⟩,
    fun hpos => ⟨by omega_arith, hc', hx', by rw [show n - k = j + 1 by omega_arith]; exact sk⟩⟩

end Scan

/-! ## `T` -/

variable (h g : OHash)

/-- `T = DB[hLen..]`, its length, and the index after its first byte not zero. -/
abbrev tN (P : EP) : Nat := P.K - (2 * h.H.D + 1)
abbrev T (P : EP) (σ : State) (j : Nat) : Byte := V5 h g P σ (1 + 2 * h.H.D + j)
abbrev idx (P : EP) (σ : State) : Nat := pzS (tN h P) (T h g P σ) (tN h P)

/-- The decoding's checks all pass. -/
abbrev allOk (P : EP) (σ : State) : Prop :=
  hdOk h g P σ ∧ lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1

/-- After the scan. -/
abbrev A2 (P : EP) (σ s : State) : Prop :=
  Ctx P.lay P.scr σ s ∧ Y h g P σ s.mem ∧
    (∃ a : BitVec 32, s.mem.readW (P.lay.fr sAcc) 32 = a ∧ a.toNat < 256 ∧ (a = 0 ↔ allOk h g P σ)) ∧
    s.mem.readW (P.lay.fr sPos) 32 = BitVec.ofNat 32 (idx h g P σ)

theorem endB : ∀ b : Byte, (((b.setWidth 32 ^^^ (1 : BitVec 32)) ||| (0 : BitVec 32) >>> 31).toNat < 256 ∧
    (((b.setWidth 32 ^^^ (1 : BitVec 32)) ||| (0 : BitVec 32) >>> 31) = 0 ↔ b = 1)) := by decide

/-- What the end of the scan adds to `acc`. -/
theorem endX (c : Prop) [Decidable c] (b : Byte) :
    (((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) |||
      (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31).toNat < 256 ∧
    ((((if c then b else 0).setWidth 32 ^^^ (1 : BitVec 32)) |||
      (if c then (0 : BitVec 32) else BitVec.allOnes 32) >>> 31) = 0 ↔
      c ∧ b = 1) := by
  by_cases hc : c
  · simp only [hc, ite_true, true_and]
    exact endB b
  · simp only [hc, ite_false, false_and, iff_false]
    exact ⟨by decide, by decide⟩

theorem tscan_vp (P : EP) :
    VP (A1 h g P) (.seq (.block (scanSet h.H)) (.seq (countLoop scanBody) (.block scanEnd))) (A2 h g P) := by
  by_cases hP : ∃ σ, In P σ ∧ 2 * h.H.D + 2 ≤ P.K
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.2.1.1.1.1, hs.2.1.1.1.2.1⟩
  obtain ⟨σ₀, hi₀, hfit⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  have hK := hi₀.k1024
  have hD := h.D_le
  have hD0 := h.D_pos
  have htN : tN h P = P.K - (2 * h.H.D + 1) := rfl
  let X : State → Mem → Prop := fun σ m => Y h g P σ m ∧ ∃ a : BitVec 32, m.readW (P.lay.fr sAcc) 32 = a ∧
    a.toNat < 256 ∧ (a = 0 ↔ hdOk h g P σ)
  refine VP.seq (G := fun σ s => Ctx P.lay P.scr σ s ∧ X σ s.mem ∧
      SC P.scr (oEm + 1 + 2 * h.H.D) (tN h P) (T h g P σ) 0 s)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hy, ha⟩ => ?_)
    (VP.seq (scan_vp hg (o := oEm + 1 + 2 * h.H.D) (n := tN h P) (by oomega) (by omega_arith) (f := T h g P) (X := X)
      fun σ m hx i hi => by rw [show oEm + 1 + 2 * h.H.D + i = 1 + 2 * h.H.D + i by oomega]; exact hx.1.2 _ (by omega_arith))
      ?_)
  · have hi := hy.1.1.1
    obtain ⟨a4, r4, v4⟩ := argAt hi hc.st (j := 4) (by decide)
    replace v4 : s.mem.readW (P.lay.fr (arg 4)) 32 = BitVec.ofNat 32 P.K := v4
    have hw : WP isa (.block (scanSet h.H)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = P.scr + BitVec.ofNat 32 (oEm + 1 + 2 * h.H.D) ∧ t.gpr .r1 = 0 ∧
        t.gpr .lr = BitVec.ofNat 32 (tN h P) ∧ t.gpr .r4 = 0 ∧ t.gpr .r5 = 0 ∧ t.gpr .r6 = BitVec.allOnes 32 ∧
        t.gpr .r7 = 0 := by
      prun [scanSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a4, r4, v4, arg_lt,
        movw_val (show oEm + 1 + 2 * h.H.D < 2 ^ 16 by oomega), movw_val (show 2 * h.H.D + 1 < 2 ^ 16 by omega_arith),
        movw_val (show 0 < 2 ^ 16 by decide), Offset.ofNat_sub_ofNat (show 2 * h.H.D + 1 ≤ P.K by omega_arith), dpVal]
      decide
    refine WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r4', r5, r6, r7⟩ =>
      ⟨hc.regs rd wr sp m, m ▸ ⟨hy, ha⟩, ⟨by rw [r0]; rfl, r1, by rw [lr, Nat.sub_zero], ?_, ?_, ?_, r7⟩⟩
    · rw [r4']; simp only [pzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [r5]; simp only [vzS, Nat.not_lt_zero, ite_false]; rfl
    · rw [r6]; simp only [nfS, Nat.not_lt_zero, ite_false]
  -- `acc` and `idx` to their slots.
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm)
    fun σ s ⟨hc, ⟨hy, a, ha, hab, hae⟩, hs⟩ => ?_
  have hi := hy.1.1.1
  have ex := endX (lzS (tN h P) (T h g P σ) < tN h P) (T h g P σ (lzS (tN h P) (T h g P σ)))
  have hw : WP isa (.block scanEnd) s fun t =>
      t.mem = (s.mem.writeW (P.lay.fr sAcc) (a ||| (((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
        nfS (tN h P) (T h g P σ) (tN h P) >>> 31))).writeW (P.lay.fr sPos) (BitVec.ofNat 32 (idx h g P σ)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [scanEnd, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, ha, hs.r4, hs.r5, hs.r6, dpVal,
      slot_ww _ _ (show sAcc + 4 ≤ frameBytes by decide) (show sPos + 4 ≤ frameBytes by decide) (by decide)]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  have fr : Frame [slotR P.lay sAcc, slotR P.lay sPos] s.mem t.mem := by
    rw [m]; exact ((slot_frame _ _ _ _).mono (by simp)).trans ((slot_frame _ _ _ _).mono (by simp))
  have dS : ∀ o n, o + n ≤ oRsa → ∀ r ∈ [slotR P.lay sAcc, slotR P.lay sPos], (sR P.scr o n).Disjoint r := by
    intro o n hon r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (hg.slot ok hon (by rw [hg.F]; decide)).symm
  have hx : (((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
      nfS (tN h P) (T h g P σ) (tN h P) >>> 31).toNat < 256 ∧
      ((((vzS (tN h P) (T h g P σ) (tN h P)).setWidth 32 ^^^ (1 : BitVec 32)) |||
        nfS (tN h P) (T h g P σ) (tN h P) >>> 31) = 0 ↔
        lzS (tN h P) (T h g P σ) < tN h P ∧ T h g P σ (lzS (tN h P) (T h g P σ)) = 1) := ex
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨⟨hy.1.1.keep h fr fun r hr => ?_,
    hy.1.2.1.keep h fr (dS _ _ (by oomega)), ?_⟩, em_keep fr (dS _ _ (by oomega)) (by omega_arith) hy.2⟩,
    ⟨_, by rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32], ?_, ?_⟩,
    by rw [m, Mem.readW_writeW_self32]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · rw [← hy.1.2.2]
    exact em_keep (n := 1) fr (dS _ _ (by oomega)) (by decide)
      (f := fun _ => s.mem (sa P.scr 0)) (fun i hi => by rw [show i = 0 by omega_arith]) 0 (by decide)
  · rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) hab hx.1
  · rw [or_eq_zero32, hae, hx.2]

end VG.Proof.RsaOaep.Arm.Dec
