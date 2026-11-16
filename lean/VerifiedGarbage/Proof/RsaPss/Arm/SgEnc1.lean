module

public import VerifiedGarbage.Proof.RsaPss.Arm.SgChk
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
import VerifiedGarbage.Proof.MdHashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.RsaPss.Arm.YDig
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPss.Arm.CtHash`, which only this module used -/

section

/-! ### `RsaPss.Arm.CtInit`, which only this module used -/

section

/-!
# RSASSA-PSS on ARMv7: hashing, the hash value and the length field

`init_vp`: the table of `MdHash` that is our argument `j` to the slot
`sTab`, and its streaming `init`, called through the table, sets the hash
value at `oSt` to the initial one.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaOaep.Arm (tA tabA_wp)
open VG.Impl.RsaOaep.Arm (sTab)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The slot `sTab`, apart from our part of `scratch` and from the slots
`ctHash` writes. -/
theorem sTab_sep (hg : Geo L scr) {o n : Nat} (h : o + n ≤ oRsa) : (slotR L sTab).Disjoint (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact hg.slot ok h (by rw [hg.F]; decide)

/-- The table that is our argument `j` to `sTab`, and the streaming `init`,
through the table, on the hash value at `oSt`. -/
theorem init_vp (hg : Geo L scr) {f : MdFns} {dn : String} {j : Nat} {ai ac ad : BitVec 32}
    (hj : j < L.argv.length) (hoff : arg j < 4096)
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA (L.argv.getD j 0) o) 4) (hne : f.init ≠ [])
    {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oSt (h.N + h.B), L.LOW, slotR L sTab] m m' → Inv σ m')
    (htab : ∀ σ m, Inv σ m → HTab h dn f (L.argv.getD j 0) ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem) ∧ s.syms = σ.syms)
      (initPart f j)
      (fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = L.argv.getD j 0) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) ∧ s.syms = σ.syms) := by
  have hN := h.N_le
  have hBl := h.B_le
  have fit := hg.fit
  have hS := h.S_eq
  obtain ⟨σ', ok⟩ := hg.ok
  let p := L.argv.getD j 0
  let F₀ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = p)) ∧
    s.syms = σ.syms
  let F₁ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ (Inv σ s.mem ∧ s.mem.readW (L.fr sTab) 32 = p) ∧
    s.gpr .r0 = scr + BitVec.ofNat 32 oSt) ∧ s.syms = σ.syms
  obtain dT : (slotR L sTab).Disjoint (slotR L sS) := Lay.fr_sep (by decide) (by decide) (by decide)
  refine VP.seq (G := F₀)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hi⟩, sy⟩ => ?_)
    (VP.seq (G := F₁)
      (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hi, ht⟩, sy⟩ => ?_)
      ?_)
  · refine WP.mono (tabA_wp hg hc hj hoff) fun t ⟨m, rd, wr, sp, _, _, ty⟩ => ?_
    obtain fr : Frame [slotR L sTab] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    obtain hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT.symm) rd wr sp
    exact ⟨⟨hc', hI σ _ _ hi (fr.mono fun r hr => by simp at hr; simp [hr]), by rw [m, Mem.readW_writeW_self32]⟩,
      ty.trans sy⟩
  · prun [initArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi, ht,
      movw_val (show oSt < 2 ^ 16 by decide), VG.Arm.RegUpd.syms_setReg, sy, F₁]
  obtain fitS : (scr + BitVec.ofNat 32 oSt).toNat + h.H.md.st.S ≤ 2 ^ 32 := by
    rw [hg.scr_lt (by decide), hS]; unfold oSt oRsa at *; omega_using [hN, hBl, fit]
  obtain cov : ∀ σ s, Ctx L scr σ s → Covers [⟨State.addr (scr + BitVec.ofNat 32 oSt), h.H.md.st.S⟩] s.wr :=
    fun σ s hc => by
      rw [hg.addr (by decide)]; refine Covers.one ?_
      rw [hS]; exact hg.wr hc.st (by unfold oSt oRsa; omega_using [hN, hBl])
  refine htcall_vp hg (F := F₁) (fun σ s hs => ⟨hs.1.1, hs.2, hs.1.2.1.2⟩)
    (fun σ s v ⟨⟨hc, hi, r0⟩, sy⟩ => ⟨⟨Ctx.setReg_iff.mpr hc, hi, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r0⟩, sy⟩) hR (k := 0) (by decide) hne
    (fun σ s hs => let T := htab σ _ hs.1.2.1.1; ⟨T.m0, T.i⟩) ?_
  refine VP.of_ct (fun _ _ => Pbkdf2.Stream.Arm.init_rel h.ok.stream (st := scr + BitVec.ofNat 32 oSt)
    fun a b hab => ⟨hab.1.1.2.2, hab.2.1.2.2, fitS, cov _ _ hab.1.1.1, cov _ _ hab.2.1.1⟩) ?_
  rintro σ s ⟨⟨hc, ⟨hi, ht⟩, r0⟩, sy⟩
  refine WP.mono_syms (Pbkdf2.Stream.Arm.init_call h.ok.stream r0 fitS (cov _ _ hc) fun s' af rp => ?_)
    fun s' hq sy' => ⟨hq, sy'.trans sy⟩
  obtain fr : Frame [sR scr oSt (h.N + h.B), L.LOW] s.mem s'.mem := by
    refine af.frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by rw [hg.addr (by decide), hS]; exact fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_low hg hc⟩
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) af.rd af.wr af.sp,
    ⟨hI σ _ _ hi (fr.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp), slot_keep fr (fun r hr => ?_) ht⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.inW (by unfold oSt oRsa; omega_using [hN, hBl])
    · exact ⟨L.LOW, by simp [Lay.W], fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hg.slot ok (by unfold oSt oRsa; omega_using [hN, hBl]) (by rw [hg.F]; decide)
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sTab_sep hg (by unfold oSt oRsa; omega_using [hN, hBl])
    · exact Lay.fr_low (by decide) (by have := hc.st.ok.B56; have := L.B.isLt; omega_arith)
  · obtain ⟨e, -⟩ := h.ok.repr _ _ _ (by rw [hg.addr (by decide)] at rp; exact rp)
    rw [e, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

end VG.Proof.RsaPss.Arm

end

end


/-!
# RSASSA-PSS on ARMv7: hashing a message of secret length

`ctHash_vp`: from a state whose `Y` holds the message `msg σ` followed by
zeros up to `nbm` blocks, with its length and `nbm` in their slots, `ctHash`
leaves the digest of the message at `oDig`, keeping any fact about memory
that its writes (`ctW`) do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaOaep.Arm (tA)
open VG.Impl.RsaOaep.Arm (sTab)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What `ctHash` writes. -/
abbrev ctW (L : Lay) (scr : BitVec 32) (T : Nat) : List Region :=
  [sR scr oSt (h.N + h.B), L.LOW, sR scr oLen h.B, sR scr oY T, sR scr oSt h.N, sR scr oCW h.H.md.so,
    sR scr oSel h.N, slotR L sBi, sR scr oDig h.N, slotR L sTab]

/-- The digest of `x` at `oDig`. -/
abbrev Dg (scr : BitVec 32) (x : List Byte) (m : Mem) : Prop :=
  ∀ i < h.D, m (sa scr (oDig + i)) = (h.ok.SH.H.hash x).getD i 0

/-- What `ctHash` writes misses the other slots. -/
theorem ctW_slot (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {d : Nat} (hd : d + 4 ≤ frameBytes)
    (hb : (d + 4 ≤ sBi ∨ sBi + 4 ≤ d) ∧ (d + 4 ≤ sTab ∨ sTab + 4 ≤ d)) :
    ∀ r ∈ ctW h L scr T, (slotR L d).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hF : d + 4 ≤ L.F + 56 := by rw [hg.F]; unfold frameBytes at hd ⊢; omega_using [hd]
  obtain hC : L.C ≤ 2 ^ 32 := by have := ok.B56; have := L.B.isLt; omega_arith
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by pomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega_using [hd]) hC
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hb.1
  · exact hg.slot ok (by pomega) hF
  · exact slotSep hd (by decide) hb.2

/-- And `EM`'s place. -/
theorem ctW_em (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) {o n : Nat} (h₂ : o + n ≤ oY) :
    ∀ r ∈ ctW h L scr T, (sR scr o n).Disjoint r := by
  have hN := h.N_le
  have hB := h.B_le
  have hso := h.so_le
  obtain ⟨σ', ok⟩ := hg.ok
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact hg.low ok (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
  · exact Geo.sep (by pomega) (by pomega) (by pomega)
  · exact (sTab_sep hg (by pomega)).symm

/-- The digest of the hash value at `oSel`, to `oDig`, by the digest of the
table at `p` in the slot `sTab`. -/
theorem out_vp (hg : Geo L scr) {f : MdFns} {dn : String} {p ai ac ad : BitVec 32}
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA p o) 4) (hne : f.dig ≠ []) {X : State → Mem → Prop}
    (hX : ∀ σ m, X σ m → m.readW (L.fr sTab) 32 = p ∧ HTab h dn f p ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ X σ s.mem) ∧ s.syms = σ.syms) (outPart f)
      (fun σ s => (Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame [sR scr oDig h.N] m₀ s.mem ∧
        s.mem = VG.WriteBytes.writeBytes m₀ (sa scr oDig) (h.md.digest (h.md.stateAt m₀ (sa scr oSel)))) ∧
        s.syms = σ.syms) := by
  have hN := h.N_le
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  obtain aSel : State.addr (scr + BitVec.ofNat 32 oSel) = sa scr oSel := hg.addr (by decide)
  obtain aDig : State.addr (scr + BitVec.ofNat 32 oDig) = sa scr oDig := hg.addr (by decide)
  obtain fSel : (scr + BitVec.ofNat 32 oSel).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  obtain fDig : (scr + BitVec.ofNat 32 oDig).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  obtain dSD : (sR scr oSel h.N).Disjoint (sR scr oDig h.N) := Geo.sep (by pomega) (by pomega) (by pomega)
  obtain rSel : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oSel) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  obtain rDigR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oDig) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  obtain rDig : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oDig) h.N := fun σ s hc => hg.wr hc.st (by pomega)
  obtain wDig : ∃ R ∈ L.W, Region.Sub (sR scr oDig h.N) R := hg.inW (by pomega)
  obtain tDig : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oDig h.N) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
  let F₁ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSel ∧
    s.gpr .r1 = scr + BitVec.ofNat 32 oDig) ∧ s.syms = σ.syms
  refine VP.seq (G := F₁)
    (VP.syms (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hx⟩ => ?_)) ?_
  · have hw : WP isa (.block outSet) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = scr + BitVec.ofNat 32 oSel ∧ t.gpr .r1 = scr + BitVec.ofNat 32 oDig := by
      prun [outSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS,
        movw_val (show oSel < 2 ^ 16 by decide), movw_val (show oDig < 2 ^ 16 by decide)]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1⟩ => ⟨hc.regs rd wr sp m, m ▸ hx, r0, r1⟩
  refine htcall_vp hg (F := F₁) (fun σ s hs => ⟨hs.1.1, hs.2, (hX σ _ hs.1.2.1).1⟩)
    (fun σ s v ⟨⟨hc, hx, r0, r1⟩, sy⟩ => ⟨⟨Ctx.setReg_iff.mpr hc, hx, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r0, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r1⟩, sy⟩) hR (k := 4) (by decide) hne
    (fun σ s hs => let T := (hX σ _ hs.1.2.1).2; ⟨T.m4, T.d⟩) ?_
  -- The call of the digest, by its contract.
  let rd : List Region := [⟨State.addr (scr + BitVec.ofNat 32 oSel), h.N⟩]
  let wr : List Region := [⟨State.addr (scr + BitVec.ofNat 32 oDig), h.N⟩]
  obtain c0 : ∀ s : State, s.gpr .r0 = scr + BitVec.ofNat 32 oSel → s.callEntry.gpr .r0 = scr + BitVec.ofNat 32 oSel :=
    fun s r0 => (State.callEntry_gpr _ (by decide)).trans r0
  obtain c1 : ∀ s : State, s.gpr .r1 = scr + BitVec.ofNat 32 oDig → s.callEntry.gpr .r1 = scr + BitVec.ofNat 32 oDig :=
    fun s r1 => (State.callEntry_gpr _ (by decide)).trans r1
  obtain pre : ∀ σ s, F₁ σ s → (MdHashTable.Arm.digestK h.md).pre (s.callEntry.withRegions rd wr) := by
    rintro σ s ⟨⟨_, _, r0, r1⟩, _⟩
    simp only [MdHashTable.Arm.digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      c0 s r0, c1 s r1, rd, wr]
    exact ⟨trivial, trivial, fSel, fDig, by rw [aSel, aDig]; exact dSD⟩
  obtain cov : ∀ σ s, F₁ σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := by
    rintro σ s ⟨⟨hc, _⟩, _⟩
    refine ⟨?_, ?_⟩
    · simp only [rd, wr, List.cons_append, List.nil_append]; rw [aSel, aDig]
      exact Covers.cons (Covers.one (rSel σ s hc)) (Covers.cons (Covers.one (rDigR σ s hc)) Covers.nil)
    · simp only [wr]; rw [aDig]; exact Covers.one (rDig σ s hc)
  refine VP.of_ct (fun _ _ => RelCT.call (k := MdHashTable.Arm.digestK h.md) (fun _ hp => MdHashTable.Arm.digest_ok h.ok.out hp)
    (MdHashTable.Arm.digest_ct h.outCk) rd wr fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨pre _ _ h₁, pre _ _ h₂, ?_, (cov _ _ h₁).1,
      (cov _ _ h₁).2, (cov _ _ h₂).1, (cov _ _ h₂).2⟩) fun σ s hs => ?_
  · obtain ⟨⟨_, _, a0, a1⟩, _⟩ := h₁
    obtain ⟨⟨_, _, b0, b1⟩, _⟩ := h₂
    simp only [MdHashTable.Arm.digestK, State.withRegions_gpr, c0 _ a0, c1 _ a1, c0 _ b0, c1 _ b1]
    exact ⟨trivial, trivial⟩
  obtain ⟨⟨hc, hx, r0, r1⟩, sy⟩ := hs
  obtain hs : F₁ σ s := ⟨⟨hc, hx, r0, r1⟩, sy⟩
  refine WP.mono_syms (WP.callCalls (k := MdHashTable.Arm.digestK h.md) (fun _ hp => MdHashTable.Arm.digest_ok h.ok.out hp)
    (pre σ s hs) (cov σ s hs).1 (cov σ s hs).2 (fun s' rd' wr' sp' fr _ _ hpost => ?_) rfl) fun s' hq sy' => ⟨hq, sy'.trans sy⟩
  simp only [MdHashTable.Arm.digestK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0 s r0,
    c1 s r1, aSel, aDig] at hpost
  simp only [wr] at fr
  rw [aDig] at fr
  exact ⟨hc.write fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact wDig)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact tDig) rd' wr' sp', s.mem, hx, fr, hpost⟩

/-- A byte of our part of `scratch` after bytes are written there. -/
theorem sa_writeBytes (scr : BitVec 32) (m : Mem) {o i : Nat} {xs : List Byte} (hi : i < xs.length)
    (ho : o + i < 2 ^ 64) : VG.WriteBytes.writeBytes m (sa scr o) xs (sa scr (o + i)) = xs.getD i 0 := by
  simp only [VG.WriteBytes.writeBytes, sa, Offset.sub_toNat _ (Nat.le_add_right o i) ho, Nat.add_sub_cancel_left,
    hi, ↓reduceIte]

/-- `ctHash`: the digest of the message in `Y`, of a length in its slot,
padded in `nbm` blocks. -/
theorem ctHash_vp (hg : Geo L scr) {f : MdFns} {dn : String} {j : Nat} {ai ac ad : BitVec 32}
    (hj : j < L.argv.length) (hoff : arg j < 4096)
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA (L.argv.getD j 0) o) 4)
    (hne : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {msg : State → List Byte} (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame (ctW h L scr (nbm * h.B)) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm)
    (htab : ∀ σ m, Inv σ m → HTab h dn f (L.argv.getD j 0) ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0) ∧
        s.syms = σ.syms)
      (ctHash f h.sh j)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < h.D, s.mem (sa scr (oDig + i)) = (h.ok.SH.H.hash (msg σ)).getD i 0) ∧ s.syms = σ.syms) := by
  have hso := h.so_le
  have hN := h.N_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hNL := h.NL
  have hDN := h.D_le
  have fit := hg.fit
  obtain hB0 : 0 < h.B := by omega_using [hB64]
  obtain hLB : h.L < h.B := by have := h.D_pos; omega_using [hB64, hL]
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hIs : ∀ rs : List Region, (∀ r ∈ rs, r ∈ ctW h L scr (nbm * h.B)) →
      ∀ σ m m', Inv σ m → Frame rs m m' → Inv σ m' :=
    fun rs hs σ m m' hi hf => hI σ m m' hi (Frame.subset hf hs)
  obtain hq : ∀ σ, ((msg σ).length + h.L) / h.B < nbm := fun σ =>
    (Nat.div_lt_iff_lt_mul hB0).2 (by have := hfit σ; omega_using [this])
  obtain hℓ : ∀ σ, (msg σ).length < 2048 := fun σ => by have := hfit σ; omega_using [hnb, this]
  let p := L.argv.getD j 0
  obtain tS : ∀ o n, o + n ≤ oRsa → (slotR L sTab).Disjoint (sR scr o n) := fun o n h' => sTab_sep hg h'
  obtain tB : (slotR L sTab).Disjoint (slotR L sBi) := Lay.fr_sep (by decide) (by decide) (by decide)
  show VP _ (.seq (initPart f j) (.seq (lenPart h.sh) (.seq (padPart h.sh) (.seq (compLoop f h.sh) (outPart f))))) _
  -- the table to its slot, the hash value initialized
  refine VP.seq (init_vp h hg hj hoff hR hne.1
    (Inv := fun σ m => Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0)
    (fun σ m m' ⟨hi, hy⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Geo.sep (by pomega) (by pomega) (by pomega)
        · exact hg.low ok (by pomega)
        · exact (tS _ _ (by pomega)).symm) (by pomega) hy⟩)
    fun σ m hm => htab σ m hm.1) ?_
  -- the length field
  refine VP.seq ((VP.syms (lenBlk_vp h hg (ℓ := fun σ => (msg σ).length) (Inv := fun σ m =>
      ((Inv σ m ∧ ∀ i < nbm * h.B, m (sa scr (oY + i)) = (msg σ).getD i 0) ∧ m.readW (L.fr sTab) 32 = p) ∧
        h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨⟨⟨hi, hy⟩, ht⟩, he⟩ hf => ⟨⟨⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf,
      sbytes_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)) (by pomega) hy⟩,
      slot_keep hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact tS _ _ (by pomega)) ht⟩,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    fun σ => by have := hℓ σ; omega_using [this])).mono
      (fun σ s ⟨⟨hc, ⟨hi, ht⟩, he⟩, sy⟩ => ⟨⟨hc, ⟨⟨hi, ht⟩, he⟩, hsl σ _ hi.1⟩, sy⟩) fun _ _ h => h) ?_
  -- the padding
  refine VP.seq ((VP.syms (pad_vp h hg hnb hnb0 hfit (Inv := fun σ m => (Inv σ m ∧ m.readW (L.fr sTab) 32 = p) ∧
      h.md.stateAt m (sa scr oSt) = h.ok.iv)
    (fun σ m m' ⟨⟨hi, ht⟩, he⟩ hf => ⟨⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; simp) σ m m' hi hf, slot_keep hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          subst hr; exact tS _ _ (by pomega)) ht⟩,
      (stateAt_keep h hf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)).trans he⟩)
    (fun σ m hi => hsl σ m hi.1.1) (fun σ m hi => hsn σ m hi.1.1))).mono
      (fun σ s ⟨⟨hc, ⟨⟨⟨hi, hy⟩, ht⟩, he⟩, hlb⟩, sy⟩ => ⟨⟨hc, ⟨⟨hi, ht⟩, he⟩, hlb, hy⟩, sy⟩) fun _ _ h => h) ?_
  -- every block compressed
  refine VP.seq ((compLoop_vp h hg hR hne.2.1 (dn := dn) (ai := ai) (ad := ad) hnb hnb0 (ℓ := fun σ => (msg σ).length)
    (yv := fun σ i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) hq hℓ
    (Inv := fun σ m => Inv σ m ∧ m.readW (L.fr sTab) 32 = p)
    (fun σ m m' ⟨hi, ht⟩ hf => ⟨hIs _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp) σ m m' hi hf, slot_keep hf (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact tS _ _ (by pomega)
          · exact tS _ _ (by pomega)
          · exact tS _ _ (by pomega)
          · exact tB) ht⟩)
    (fun σ m hi => hsl σ m hi.1) (fun σ m hi => hsn σ m hi.1) (fun σ m hi => ⟨hi.2, htab σ m hi.1⟩)).mono
      (fun σ s ⟨⟨hc, ⟨hi, he⟩, hy⟩, sy⟩ => ⟨⟨hc, hi, hy, he⟩, sy⟩) fun _ _ h => h) ?_
  -- the digest
  refine (out_vp h hg hR hne.2.2 (X := fun σ m => (Inv σ m ∧ m.readW (L.fr sTab) 32 = p) ∧ h.md.stateAt m (sa scr oSel) =
      h.md.compressList h.ok.iv (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1)) fun σ m hm => ⟨hm.1.2, htab σ m hm.1.1⟩).mono (fun _ _ h => h)
      fun σ s ⟨⟨hc, m₀, ⟨⟨hi, _⟩, he⟩, hf, hm⟩, sy⟩ => ?_
  refine ⟨⟨hc, hIs _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp) σ _ _ hi hf, fun i hi => ?_⟩, sy⟩
  obtain hl := h.md.digest_length (h.md.stateAt m₀ (sa scr oSel))
  rw [hm, sa_writeBytes scr m₀ (by omega_using [hDN, hi, hl]) (by pomega), he, h.ok.hash]
  obtain hq1 : ((msg σ).length + h.L) / h.B + 1 ≤ nbm := hq σ
  obtain key : h.md.compressList h.ok.iv
      (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1) =
      h.md.compressList h.ok.iv (h.md.pad (msg σ)) ((h.md.pad (msg σ)).length / h.B) := by
    rw [RsaPss.pad_length h.md _ hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine h.md.compressList_congr fun j hj => ?_
    obtain hT : j < nbm * h.B := by
      have := Nat.mul_le_mul_left h.B hq1
      rw [Nat.mul_comm h.B nbm] at this
      omega_using [hj, this]
    rw [ylist_getD hT, padY_eq hB0 hLB _ _ hj, RsaPss.pad_getD h.md _ hB0 hLB hj]
  rw [key, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rfl

end VG.Proof.RsaPss.Arm

end

end


/-!
# RSASSA-PSS signing on ARMv7: `H = Hash(M')`

When everything fits (`E0`): `M' = 0x00 ×8 ‖ mHash ‖ salt` in `Y`
(`yDig_vp`, `salt_vp`), its length and blocks to their slots (`lenSet_vp`),
and its hash `H` at `oDig` (`hash_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

variable (h : PssHash)

/-- The modulus' first byte, as a word; `dbLen`. -/
abbrev xB (P : EP) : BitVec 32 := (n0 P).setWidth 32
abbrev dbN (P : EP) : Nat := P.K - lo P - h.D - 1

/-- The slots of the encoding's parameters. -/
abbrev Bm (P : EP) (m : Mem) : Prop :=
  m.readW ((P.lay h.D).fr sC) 32 = cW (xB P) ∧ m.readW ((P.lay h.D).fr sLo) 32 = BitVec.ofNat 32 (lo P) ∧
    m.readW ((P.lay h.D).fr sDb) 32 = BitVec.ofNat 32 (dbN h P)

/-- What the encoding keeps. -/
abbrev Kp (P : EP) (σ : State) (m : Mem) : Prop := In h.D P σ ∧ fits h P ∧ Bm h P m

/-- When everything fits. -/
abbrev E0 (P : EP) (σ s : State) : Prop := Ctx (P.lay h.D) P.scr σ s ∧ Kp h P σ s.mem

/-- What misses the slots of the parameters. -/
abbrev Away3 (L : Lay) (r : Region) : Prop :=
  (slotR L sC).Disjoint r ∧ (slotR L sLo).Disjoint r ∧ (slotR L sDb).Disjoint r

theorem Kp.keep {P : EP} {σ : State} {m m' : Mem} {rs : List Region} (hk : Kp h P σ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Away3 (P.lay h.D) r) : Kp h P σ m' :=
  ⟨hk.1, hk.2.1, slot_keep hf (fun r hr => (hd r hr).1) hk.2.2.1, slot_keep hf (fun r hr => (hd r hr).2.1) hk.2.2.2.1,
    slot_keep hf (fun r hr => (hd r hr).2.2) hk.2.2.2.2⟩

theorem away3_scr {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {o n : Nat} (ho : o + n ≤ oRsa) :
    Away3 L (sR scr o n) := by
  obtain ⟨σ', ok⟩ := hg.ok
  exact ⟨hg.slot ok ho (by rw [hg.F]; decide), hg.slot ok ho (by rw [hg.F]; decide),
    hg.slot ok ho (by rw [hg.F]; decide)⟩

theorem away3_slot {L : Lay} {d : Nat} (hd : d + 4 ≤ frameBytes)
    (h₁ : (d + 4 ≤ sLo ∨ sDb + 4 ≤ d) ∧ (d + 4 ≤ sC ∨ sC + 4 ≤ d)) : Away3 L (slotR L d) := by
  have e1 : sLo = 84 := rfl
  have e2 : sC = 108 := rfl
  have e3 : sDb = 88 := rfl
  exact ⟨slotSep (by decide) hd (by omega_using [h₁]), slotSep (by decide) hd (by omega_using [h₁, e1, e3]), slotSep (by decide) hd (by omega_using [h₁, e1, e3])⟩

theorem away3_ctW {L : Lay} {scr : BitVec 32} (hg : Geo L scr) {T : Nat} (hT : T ≤ 2048) :
    ∀ r ∈ ctW h L scr T, Away3 L r := fun r hr =>
  ⟨ctW_slot h hg hT (by decide) (by decide) r hr, ctW_slot h hg hT (by decide) (by decide) r hr,
    ctW_slot h hg hT (by decide) (by decide) r hr⟩

/-- Everything fits, and the parameters are in their slots. -/
theorem e0_of {P : EP} {σ s : State} (hc : C1 h P σ s) (e : isa.eval .ne s = some false) : E0 h P σ s := by
  obtain ⟨hc, hi, sc, sl, sd, z⟩ := hc
  obtain hz : s.z = true := by
    rw [VG.Proof.X25519.Arm.eval_ne] at e
    simpa using e
  obtain hf : fits h P := of_decide_eq_true (z ▸ hz)
  refine ⟨hc, hi, hf, sc, sl, ?_⟩
  rw [sd, dbW_byte]
  have : lo P ≤ 1 := by unfold lo; split <;> omega_using []
  rw [Offset.ofNat_sub_ofNat (show lo P ≤ P.K by omega), Offset.ofNat_sub_ofNat (by omega)]
  congr 1

/-- The digest, a buffer the body only reads. -/
theorem dig_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.dig h.D := by
  obtain ⟨σ, hi⟩ := hP
  obtain hf := hi.ok.fits (P.DIG h.D) (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  exact ⟨hf, by omega_using [hD], ⟨P.DIG h.D, by simp, Region.contains_self _ _⟩⟩

/-- `M'`. -/
abbrev Mp (P : EP) (σ : State) : List Byte := Spec.RsaPss.zeros 8 ++ digB h P σ ++ saltB P σ

/-- `Y` cleared, and the digest after 8 zeros. -/
theorem yDig_sg (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (E0 h P) (yDig h.sh 16)
      (fun σ s => E0 h P σ s ∧ ∀ i < 2048, s.mem (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  refine (yDig_vp h hg (j := 16) (dgP := P.dig) (by decide) (by simp) rfl (dig_buf h ⟨σ₀, hi₀⟩)
    (fun o n hon => (hg.ro ok hon (R := P.DIG h.D) (by simp)).symm) (dl := digB h P)
    (fun σ => RsaPkcs1Sig.Arm.bytesAt_length _ _ _) (fun σ s hc i hi => ?_) (X := Kp h P)
    fun σ m m' hk hf => hk.keep h hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by decide)).mono
    (fun σ s h => h) fun σ s ⟨hc, hk, hy⟩ => ⟨⟨hc, hk⟩, hy⟩
  obtain e : Spec.Rsa.bytesAt s.mem (State.addr P.dig) h.D = Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D :=
    hc.st.ro (R := P.DIG h.D) (by simp)
  show s.mem (State.addr P.dig + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (State.addr P.dig) h.D).getD i 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD hi]

/-- `Y` before and after the salt. -/
abbrev Y1 (P : EP) (σ : State) (m : Mem) : Prop :=
  ∀ i < 2048, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0
abbrev Y2 (P : EP) (σ : State) (m : Mem) : Prop := ∀ i < 2048, m (sa P.scr (oY + i)) = (Mp h P σ).getD i 0

theorem salt_buf {P : EP} (hP : ∃ σ, In h.D P σ) : RBuf (P.lay h.D) P.salt P.sl := by
  obtain ⟨σ, hi⟩ := hP
  obtain hf := hi.ok.fits P.SALT (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hf
  exact ⟨hf, hi.sl32, ⟨P.SALT, by simp, Region.contains_self _ _⟩⟩

theorem salt_at {P : EP} {σ s : State} (hc : Ctx (P.lay h.D) P.scr σ s) {i : Nat} (hi : i < P.sl) :
    s.mem (byteAt P.salt i) = (saltB P σ).getD i 0 := by
  obtain e : Spec.Rsa.bytesAt s.mem (State.addr P.salt) P.sl = Spec.Rsa.bytesAt σ.mem (State.addr P.salt) P.sl :=
    hc.st.ro (R := P.SALT) (by simp)
  show s.mem (State.addr P.salt + BitVec.ofNat 64 i) = (Spec.Rsa.bytesAt σ.mem (State.addr P.salt) P.sl).getD i 0
  rw [← e, RsaPkcs1Sig.Arm.bytesAt_getD hi]

/-- The salt after the digest. -/
theorem salt_vp (P : EP) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => E0 h P σ s ∧ Y1 h P σ s.mem)
      (.seq (.block (cpSalt h.sh)) (.ite .eq (.block []) Impl.Bignum.Arm.copyBytes))
      (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  obtain ⟨σ', ok⟩ := hg.ok
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hK := hi₀.k1024
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.2.1
  obtain hsl : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_arith
  refine VP.seq (G := fun σ s => (E0 h P σ s ∧ Y1 h P σ s.mem) ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧
      s.gpr .r1 = P.salt ∧ s.gpr .lr = BitVec.ofNat 32 P.sl ∧ s.z = decide (P.sl = 0))
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_)
    (VP.ite (fun _ _ _ _ h₁ h₂ => by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, h₁.2.2.2.2,
      h₂.2.2.2.2]) (VP.block_nil fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, _, _, _, z⟩, e⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩) ?_)
  · obtain ⟨a17, r17, v17⟩ := argAt hk.1 hc.st (j := 18) (by decide)
    obtain ⟨a18, r18, v18⟩ := argAt hk.1 hc.st (j := 19) (by decide)
    obtain hz0 : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
    obtain hw : WP isa (.block (cpSalt h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
        t.gpr .r0 = P.scr + BitVec.ofNat 32 (oY + 8 + h.D) ∧ t.gpr .r1 = P.salt ∧
        t.gpr .lr = BitVec.ofNat 32 P.sl ∧ t.z = decide (P.sl = 0) := by
      prun [cpSalt, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, a17, r17, v17, a18, r18, v18, arg_lt,
        movw_val (show oY + 8 + dig h.sh < 2 ^ 16 by show oY + 8 + h.D < 2 ^ 16; pomega), hz0,
        VG.Proof.X25519.Arm.ofNat_beq_zero hk.1.sl32]
      exact ⟨rfl, rfl, VG.Proof.X25519.Arm.ofNat_beq_zero hk.1.sl32⟩
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, z⟩ => ⟨⟨⟨hc.regs rd wr sp m, m ▸ hk⟩, m ▸ hy⟩, r0, r1, lr, z⟩
  · have h0 : P.sl = 0 := by
      rw [VG.Proof.X25519.Arm.eval_eq, z] at e; simpa using e
    rw [hy i hi]
    simp [Mp, saltB, h0, Spec.Rsa.bytesAt]
  · by_cases h0 : P.sl = 0
    · exact VP.empty fun σ s ⟨⟨_, _, _, _, z⟩, e⟩ => by
        rw [VG.Proof.X25519.Arm.eval_eq, z, decide_eq_true h0] at e; exact absurd e (by decide)
    refine (copy_vp (hg.wbuf (o := oY + 8 + h.D) (n := P.sl) (by pomega) (by omega_arith))
      (salt_buf h ⟨σ₀, hi₀⟩) (by rw [hg.addr (by pomega)]; exact (hg.ro ok (by pomega) (R := P.SALT)
        (by simp)).symm) (by omega_arith) (f := fun σ i => (saltB P σ).getD i 0)
      (Inv := fun σ m => Kp h P σ m ∧ (∀ i < 8 + h.D, m (sa P.scr (oY + i)) = (Spec.RsaPss.zeros 8 ++ digB h P σ).getD i 0) ∧
        YZ P.scr (8 + h.D + P.sl) m) fun σ m m' ⟨hk, h1, h2⟩ hf => ?_).mono
      (fun σ s ⟨⟨⟨⟨hc, hk⟩, hy⟩, r0, r1, lr, _⟩, _⟩ => ⟨hc, ⟨hk, fun i hi => hy i (by omega_arith), fun i hi => ?_⟩, ?_, r1, lr,
        fun i hi => salt_at h hc hi⟩) fun σ s ⟨hc, ⟨hk, h1, h2⟩, hs⟩ => ⟨⟨hc, hk⟩, fun i hi => ?_⟩
    · rw [hg.addr (by pomega)] at hf
      refine ⟨hk.keep h hf fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact away3_scr hg (by pomega),
        sbytes_keep hf (fun r hr => ?_) (by pomega) h1, sbytes_keep hf (fun r hr => ?_) (by pomega) h2⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
      · simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega) (by pomega) (by pomega)
    · rw [show oY + (8 + h.D + P.sl) + i = oY + (8 + h.D + P.sl + i) by omega_arith, hy _ (by omega_arith),
        getD_ge (by simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]; omega_arith)]
    · rw [r0]
    · have hl : (Spec.RsaPss.zeros 8 ++ digB h P σ).length = 8 + h.D := by
        simp only [List.length_append, RsaPss.zeros_length, digB, RsaPkcs1Sig.Arm.bytesAt_length]
      rw [RsaPss.getD_app, hl]
      by_cases e1 : i < 8 + h.D
      · rw [ite_eq_left e1]; exact h1 i e1
      rw [ite_eq_right e1]
      by_cases e2 : i < 8 + h.D + P.sl
      · rw [← hs (i - (8 + h.D)) (by omega_arith), hg.byteAt_scr (by pomega),
          show oY + 8 + h.D + (i - (8 + h.D)) = oY + i by omega_arith]
      · rw [getD_ge (l := saltB P σ) (by rw [RsaPkcs1Sig.Arm.bytesAt_length]; omega_arith),
          show oY + i = oY + (8 + h.D + P.sl) + (i - (8 + h.D + P.sl)) by omega_arith]
        exact h2 _ (by omega_arith)

/-- `M'`'s blocks. -/
abbrev nbS (P : EP) : Nat := (P.sl + (8 + h.D) + h.L) / h.B + 1

/-- What `ctHash` keeps, with `M'`'s length and blocks in their slots. -/
abbrev Kh (P : EP) (σ : State) (m : Mem) : Prop :=
  Kp h P σ m ∧ m.readW ((P.lay h.D).fr sL) 32 = BitVec.ofNat 32 (Mp h P σ).length ∧
    m.readW ((P.lay h.D).fr sNb) 32 = BitVec.ofNat 32 (nbS h P)

theorem Mp_length (P : EP) (σ : State) : (Mp h P σ).length = P.sl + (8 + h.D) := by
  simp only [Mp, List.length_append, RsaPss.zeros_length, digB, saltB, RsaPkcs1Sig.Arm.bytesAt_length]; omega_using []

/-- `M'`'s length and blocks. -/
theorem lenSet_vp (P : EP) :
    VP (fun σ s => E0 h P σ s ∧ Y2 h P σ s.mem) (.block (lenSet h.sh 19))
      (fun σ s => Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) := by
  refine VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.1.st.sp.trans h₂.1.1.st.sp.symm) fun σ s ⟨⟨hc, hk⟩, hy⟩ => ?_
  have hg := hk.1.geo
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_ge
  have hsl := hk.1.sl32
  obtain hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hk.2.1.2; omega_using [this]
  have hK := hk.1.k1024
  obtain ⟨a18, r18, v18⟩ := argAt hk.1 hc.st (j := 19) (by decide)
  replace v18 : s.mem.readW ((P.lay h.D).fr (arg 19)) 32 = BitVec.ofNat 32 P.sl := v18
  obtain e1 : BitVec.ofNat 32 (P.sl + (8 + h.D) + h.L) >>> lgB h.sh = BitVec.ofNat 32 ((P.sl + (8 + h.D) + h.L) / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by omega_using [hL, hsl2, hK]), h.pow_lg]
  obtain hw : WP isa (.block (lenSet h.sh 19)) s fun t =>
      t.mem = (s.mem.writeW ((P.lay h.D).fr sL) (BitVec.ofNat 32 (P.sl + (8 + h.D)))).writeW ((P.lay h.D).fr sNb)
        (BitVec.ofNat 32 (nbS h P)) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    prun [lenSet, sp0, ld, st, mw, hc.st.sp, a18, r18, v18, arg_lt, slotAt hk.1 (d := sL) (by decide),
      slotAt hk.1 (d := sNb) (by decide), hc.st.inFr (d := sL) (n := 4) (by show sL + 4 ≤ frameBytes; decide),
      hc.st.inFr (d := sNb) (n := 4) (by show sNb + 4 ≤ frameBytes; decide),
      movw_val (show 8 + dig h.sh < 2 ^ 16 by show 8 + h.D < 2 ^ 16; omega_using [hD]),
      movw_val (show lenL h.sh < 2 ^ 16 by show h.L < 2 ^ 16; omega_using [hL]), BitVec.ofNat_add_ofNat, e1, h.lg_range,
      VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, dpVal]
  refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
  obtain fr : Frame [slotR (P.lay h.D) sL, slotR (P.lay h.D) sNb] s.mem t.mem := by
    rw [m]
    exact (slot_frame _ _ _ _).mono (by simp) |>.trans ((slot_frame _ _ _ _).mono (by simp))
  obtain ⟨σ', ok⟩ := hg.ok
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd wr sp, ⟨hk.keep h fr fun r hr => ?_, ?_, ?_⟩,
    sbytes_keep fr (fun r hr => ?_) (by pomega) hy⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotW hg (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact slotSep (by decide) (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact away3_slot (by decide) (by decide)
  · rw [m, slot_ww _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, Mp_length]
  · rw [m, Mem.readW_writeW_self32]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm
    · exact (hg.slot ok (by pomega) (by rw [hg.F]; decide)).symm

/-- `H = Hash(M')`, at `oDig`. -/
theorem hash_vp {g : RsaOaep.Arm.OHash} {f : MdFns} {fg : Impl.RsaOaep.Arm.Fns} {dn : String} (P : EP)
    (Q : TF h g f fg dn P) (hP : ∃ σ, In h.D P σ) :
    VP (fun σ s => (Ctx (P.lay h.D) P.scr σ s ∧ Kh h P σ s.mem ∧ Y2 h P σ s.mem) ∧ s.syms = σ.syms) (ctHash f h.sh 22)
      (fun σ s => (E0 h P σ s ∧ Dg h P.scr (Mp h P σ) s.mem) ∧ s.syms = σ.syms) := by
  obtain ⟨σ₀, hi₀⟩ := hP
  have hg := hi₀.geo
  by_cases hf : fits h P
  swap
  · exact VP.empty fun σ s h' => hf h'.1.2.1.1.2.1
  obtain hD : h.D ≤ 64 := by have := h.D_le; have := h.N_le; omega_arith
  have hL := h.L_le
  have hB := h.B_le
  obtain hB0 : 0 < h.B := by have := h.B_ge; omega_using [this]
  obtain hsl2 : P.sl + h.D + 2 ≤ P.K := by have := hf.2; omega_using [this]
  have hK := hi₀.k1024
  obtain q1 := Nat.lt_mul_div_succ (P.sl + (8 + h.D) + h.L) hB0
  obtain q2 := Nat.mul_div_le (P.sl + (8 + h.D) + h.L) h.B
  obtain hT : nbS h P * h.B ≤ 2048 := by
    show ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B ≤ 2048
    rw [Nat.succ_mul, Nat.mul_comm]; omega_using [hL, hB, hsl2, hK, q2]
  refine (ctHash_vp h hg (j := 22) (by simp) (arg_lt (by decide)) hi₀.htbl Q.fne (nbm := nbS h P) hT
    (Nat.succ_pos _) (msg := Mp h P) (fun σ => by
      rw [Mp_length]; show _ ≤ ((P.sl + (8 + h.D) + h.L) / h.B + 1) * h.B; rw [Nat.mul_comm]; omega_using [q1])
    (Inv := Kh h P) (fun σ m m' hk hf' => ⟨hk.1.keep h hf' (away3_ctW h hg hT), slot_keep hf'
      (ctW_slot h hg hT (by decide) (by decide)) hk.2.1, slot_keep hf' (ctW_slot h hg hT (by decide) (by decide)) hk.2.2⟩)
    (fun σ m hk => hk.2.1) (fun σ m hk => hk.2.2) (fun σ m hk => Q.ht σ hk.1.1.htabT)).mono
    (fun σ s ⟨⟨hc, hk, hy⟩, sy⟩ => ⟨⟨hc, hk, fun i hi => hy i (by omega_using [hT, hi])⟩, sy⟩)
    fun σ s ⟨⟨hc, hk, hd⟩, sy⟩ => ⟨⟨⟨hc, hk.1⟩, hd⟩, sy⟩

end VG.Proof.RsaPss.Arm.Sg
