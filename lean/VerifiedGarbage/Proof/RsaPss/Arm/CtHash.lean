module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
import VerifiedGarbage.Proof.MdHashTable.Arm
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPss.Arm.CtMgf

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPss.Arm.CtPad
import VerifiedGarbage.Proof.RsaPss.Arm.CtInit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.Arm.CtLoop
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.RsaPss.Arm.Step

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
  have hF : d + 4 ≤ L.F + 56 := by rw [hg.F]; unfold frameBytes at hd ⊢; omega
  have hC : L.C ≤ 2 ^ 32 := by have := ok.B56; have := L.B.isLt; omega
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg.slot ok (by pomega) hF
  · exact Lay.fr_low (by unfold frameBytes at hd; omega) hC
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
  have aSel : State.addr (scr + BitVec.ofNat 32 oSel) = sa scr oSel := hg.addr (by decide)
  have aDig : State.addr (scr + BitVec.ofNat 32 oDig) = sa scr oDig := hg.addr (by decide)
  have fSel : (scr + BitVec.ofNat 32 oSel).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  have fDig : (scr + BitVec.ofNat 32 oDig).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  have dSD : (sR scr oSel h.N).Disjoint (sR scr oDig h.N) := Geo.sep (by pomega) (by pomega) (by pomega)
  have rSel : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oSel) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  have rDigR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oDig) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  have rDig : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oDig) h.N := fun σ s hc => hg.wr hc.st (by pomega)
  have wDig : ∃ R ∈ L.W, Region.Sub (sR scr oDig h.N) R := hg.inW (by pomega)
  have tDig : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oDig h.N) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
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
  have c0 : ∀ s : State, s.gpr .r0 = scr + BitVec.ofNat 32 oSel → s.callEntry.gpr .r0 = scr + BitVec.ofNat 32 oSel :=
    fun s r0 => (State.callEntry_gpr _ (by decide)).trans r0
  have c1 : ∀ s : State, s.gpr .r1 = scr + BitVec.ofNat 32 oDig → s.callEntry.gpr .r1 = scr + BitVec.ofNat 32 oDig :=
    fun s r1 => (State.callEntry_gpr _ (by decide)).trans r1
  have pre : ∀ σ s, F₁ σ s → (MdHashTable.Arm.digestK h.md).pre (s.callEntry.withRegions rd wr) := by
    rintro σ s ⟨⟨_, _, r0, r1⟩, _⟩
    simp only [MdHashTable.Arm.digestK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      c0 s r0, c1 s r1, rd, wr]
    exact ⟨trivial, trivial, fSel, fDig, by rw [aSel, aDig]; exact dSD⟩
  have cov : ∀ σ s, F₁ σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := by
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
  have hs : F₁ σ s := ⟨⟨hc, hx, r0, r1⟩, sy⟩
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
  have hB0 : 0 < h.B := by omega
  have hLB : h.L < h.B := by have := h.D_pos; omega
  obtain ⟨σ', ok⟩ := hg.ok
  have hIs : ∀ rs : List Region, (∀ r ∈ rs, r ∈ ctW h L scr (nbm * h.B)) →
      ∀ σ m m', Inv σ m → Frame rs m m' → Inv σ m' :=
    fun rs hs σ m m' hi hf => hI σ m m' hi (Frame.subset hf hs)
  have hq : ∀ σ, ((msg σ).length + h.L) / h.B < nbm := fun σ =>
    (Nat.div_lt_iff_lt_mul hB0).2 (by have := hfit σ; omega)
  have hℓ : ∀ σ, (msg σ).length < 2048 := fun σ => by have := hfit σ; omega
  let p := L.argv.getD j 0
  have tS : ∀ o n, o + n ≤ oRsa → (slotR L sTab).Disjoint (sR scr o n) := fun o n h' => sTab_sep hg h'
  have tB : (slotR L sTab).Disjoint (slotR L sBi) := Lay.fr_sep (by decide) (by decide) (by decide)
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
    fun σ => by have := hℓ σ; omega)).mono
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
  have hl := h.md.digest_length (h.md.stateAt m₀ (sa scr oSel))
  rw [hm, sa_writeBytes scr m₀ (by omega) (by pomega), he, h.ok.hash]
  have hq1 : ((msg σ).length + h.L) / h.B + 1 ≤ nbm := hq σ
  have key : h.md.compressList h.ok.iv
      (ylist (fun i => padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) (nbm * h.B))
        (((msg σ).length + h.L) / h.B + 1) =
      h.md.compressList h.ok.iv (h.md.pad (msg σ)) ((h.md.pad (msg σ)).length / h.B) := by
    rw [RsaPss.pad_length h.md _ hB0 hLB, Nat.mul_div_cancel_left _ hB0]
    refine h.md.compressList_congr fun j hj => ?_
    have hT : j < nbm * h.B := by
      have := Nat.mul_le_mul_left h.B hq1
      rw [Nat.mul_comm h.B nbm] at this
      omega
    rw [ylist_getD hT, padY_eq hB0 hLB _ _ hj, RsaPss.pad_getD h.md _ hB0 hLB hj]
  rw [key, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rfl

end VG.Proof.RsaPss.Arm
