module
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Compress
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: hashing, every block compressed

`comp_vp`: one compression of a block of `Y` into the hash value at `oSt`,
by the compression function of the table of `MdHash` in the slot `sTab`.
`compLoop_vp`: every one of `Y`'s `nbm` blocks compressed, and the hash
value after block `lb` (the last of the padded message, `⌊(ℓ + L) / B⌋`)
selected into `oSel`: it is that of `Y`'s first `lb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaOaep.Arm (tA)
open VG.Impl.RsaOaep.Arm (sTab)

/-- `Y`'s first `T` bytes, as a list. -/
def ylist (yv : Nat → Byte) (T : Nat) : List Byte := (List.range T).map yv

theorem ylist_getD {yv : Nat → Byte} {T j : Nat} (h : j < T) : (ylist yv T).getD j 0 = yv j := by
  simp [ylist, List.getD_eq_getElem?_getD, h]

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The regions a compression writes. -/
abbrev compW (scr : BitVec 32) : List Region := [sR scr oSt h.N, sR scr oCW h.H.md.so]

/-- The setup of the compression's call. -/
theorem compSet_cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6])
    (.block [.mov .r1 (.reg .r6), .mov .r2 (.imm 1)]) hc).isSome = true := ⟨_, by taint_decide⟩

/-- One compression of the block at `src` (an offset `o` of our part of
`scratch`) into the hash value at `oSt`, with the working space at `oCW`, by
the compression function of the table at `p` in the slot `sTab`. -/
theorem comp_vp (hg : Geo L scr) {f : MdFns} {dn : String} {p ai ac ad : BitVec 32}
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA p o) 4) (hne : f.comp ≠ [])
    {o : Nat} (ho' : o + h.B ≤ oY + 2048) {X : State → Mem → Prop}
    (hX : ∀ σ m, X σ m → m.readW (L.fr sTab) 32 = p ∧ HTab h dn f p ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r3 = scr + BitVec.ofNat 32 oCW ∧
        s.gpr .r6 = scr + BitVec.ofNat 32 o) ∧ s.syms = σ.syms)
      (compCall f)
      (fun σ s => (Ctx L scr σ s ∧ ∃ m₀, X σ m₀ ∧ Frame (compW h scr) m₀ s.mem ∧
        h.md.stateAt s.mem (sa scr oSt) = h.md.compress (h.md.stateAt m₀ (sa scr oSt)) (h.md.blockAt m₀ (sa scr o))) ∧
        s.syms = σ.syms) := by
  have hN := h.N_le
  have hso := h.so_le
  have hB := h.B_le
  have hB64 := h.B_ge
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  have ho3 : o + h.B ≤ 3072 := ho'
  have aSt : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by decide)
  have aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by pomega)
  have a0 : State.addr (scr + BitVec.ofNat 32 oCW) = sa scr oCW := hg.addr (by decide)
  have d1 : (sR scr oSt h.N).Disjoint (sR scr oCW h.H.md.so) := Geo.sep (by pomega) (by pomega) (by pomega)
  have d2 : (sR scr o h.B).Disjoint (sR scr oSt h.N) := Geo.sep (o := o) (n := h.B) (e := oSt) (k := h.N)
    (by left; unfold oSt; omega) (by unfold oRsa; omega) (by unfold oSt oRsa at *; omega)
  have d3 : (sR scr o h.B).Disjoint (sR scr oCW h.H.md.so) := Geo.sep (o := o) (n := h.B) (e := oCW) (k := h.H.md.so)
    (by left; unfold oCW; omega) (by unfold oRsa; omega) (by unfold oCW oRsa at *; omega)
  have f0 : (scr + BitVec.ofNat 32 oSt).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  have f1 : (scr + BitVec.ofNat 32 o).toNat + h.B ≤ 2 ^ 32 := by rw [hg.scr_lt (by pomega)]; pomega
  have f3 : (scr + BitVec.ofNat 32 oCW).toNat + h.H.md.so ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  have rO : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr o) h.B :=
    fun σ s hc => hg.rd hc.st (o := o) (n := h.B) (by unfold oRsa; omega)
  have rSt : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oSt) h.N := fun σ s hc => hg.wr hc.st (by pomega)
  have rCW : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oCW) h.H.md.so := fun σ s hc => hg.wr hc.st (by pomega)
  have rStR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oSt) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  have rCWR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oCW) h.H.md.so :=
    fun σ s hc => hg.rd hc.st (by pomega)
  have wSt : ∃ R ∈ L.W, Region.Sub (sR scr oSt h.N) R := hg.inW (by pomega)
  have wCW : ∃ R ∈ L.W, Region.Sub (sR scr oCW h.H.md.so) R := hg.inW (by pomega)
  have tSt : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oSt h.N) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
  have tCW : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oCW h.H.md.so) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
  let F₁ : State → State → Prop := fun σ s => (Ctx L scr σ s ∧ X σ s.mem ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
    s.gpr .r1 = scr + BitVec.ofNat 32 o ∧ s.gpr .r2 = 1 ∧ s.gpr .r3 = scr + BitVec.ofNat 32 oCW) ∧ s.syms = σ.syms
  refine VP.seq (G := F₁) (VP.taint [.r6] compSet_cert (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.2.2.2, h₂.1.2.2.2.2])
    fun σ s ⟨⟨hc, hx, r0, r3, r6⟩, sy⟩ => ?_) ?_
  · prun [F₁, Ctx.setReg_iff, hc, hx, r0, r3, r6, sy, VG.Arm.RegUpd.syms_setReg]
  refine htcall_vp hg (F := F₁) (fun σ s hs => ⟨hs.1.1, hs.2, (hX σ _ hs.1.2.1).1⟩)
    (fun σ s v ⟨⟨hc, hx, r0, r1, r2, r3⟩, sy⟩ => ⟨⟨Ctx.setReg_iff.mpr hc, hx, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r0, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r1, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r2, by
      simp only [VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact r3⟩, sy⟩) hR (k := 3) (by decide) hne
    (fun σ s hs => let T := (hX σ _ hs.1.2.1).2; ⟨T.m3, T.c⟩) ?_
  -- The call of the compression function, by its contract.
  let rd : List Region := [⟨State.addr (scr + BitVec.ofNat 32 o), h.B⟩]
  let wr : List Region := [⟨State.addr (scr + BitVec.ofNat 32 oSt), h.N⟩, ⟨State.addr (scr + BitVec.ofNat 32 oCW), h.H.md.so⟩]
  have pre : ∀ σ s, F₁ σ s → (Pbkdf2.Md.Arm.compK h.md h.H.md.so).pre (s.callEntry.withRegions rd wr) := by
    rintro σ s ⟨⟨hc, _, r0, r1, r2, r3⟩, _⟩
    simp only [Pbkdf2.Md.Arm.compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      r0, r1, r2, r3, Pbkdf2.Md.Arm.one32, Nat.mul_one, rd, wr]
    refine ⟨trivial, trivial, ?_, ?_, ?_, f0, f1, f3⟩
    · rw [aSt, a0]; exact d1
    · rw [aO, aSt]; exact d2
    · rw [aO, a0]; exact d3
  have cov : ∀ σ s, F₁ σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := by
    rintro σ s ⟨⟨hc, _⟩, _⟩
    refine ⟨?_, ?_⟩
    · simp only [rd, wr, List.cons_append, List.nil_append]; rw [aO, aSt, a0]
      exact Covers.cons (Covers.one (rO σ s hc)) (Covers.cons (Covers.one (rStR σ s hc))
        (Covers.cons (Covers.one (rCWR σ s hc)) Covers.nil))
    · simp only [wr]; rw [aSt, a0]
      exact Covers.cons (Covers.one (rSt σ s hc)) (Covers.cons (Covers.one (rCW σ s hc)) Covers.nil)
  refine VP.of_ct (fun _ _ => RelCT.call (k := Pbkdf2.Md.Arm.compK h.md h.H.md.so) h.ok.comp.verified h.ok.comp.ct
    rd wr fun s₁ s₂ ⟨h₁, h₂⟩ => ⟨pre _ _ h₁, pre _ _ h₂, ?_, (cov _ _ h₁).1, (cov _ _ h₁).2,
      (cov _ _ h₂).1, (cov _ _ h₂).2⟩) fun σ s hs => ?_
  · obtain ⟨⟨_, _, a0', a1, a2, a3⟩, _⟩ := h₁
    obtain ⟨⟨_, _, b0, b1, b2, b3⟩, _⟩ := h₂
    simp only [Pbkdf2.Md.Arm.compK, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      a0', a1, a2, a3, b0, b1, b2, b3]
    exact ⟨trivial, trivial, trivial, trivial⟩
  obtain ⟨⟨hc, hx, r0, r1, r2, r3⟩, sy⟩ := hs
  refine WP.mono_syms (WP.call (k := Pbkdf2.Md.Arm.compK h.md h.H.md.so) h.ok.comp.verified (pre σ s ⟨⟨hc, hx, r0, r1, r2, r3⟩, sy⟩)
    (cov σ s ⟨⟨hc, hx, r0, r1, r2, r3⟩, sy⟩).1 (cov σ s ⟨⟨hc, hx, r0, r1, r2, r3⟩, sy⟩).2
    (fun s' rd' wr' sp' fr _ _ hpost => ?_) h.ok.comp.noCalls) fun s' hq sy' => ⟨hq, sy'.trans sy⟩
  have c0 : s.callEntry.gpr .r0 = scr + BitVec.ofNat 32 oSt := (State.callEntry_gpr _ (by decide)).trans r0
  have c1 : s.callEntry.gpr .r1 = scr + BitVec.ofNat 32 o := (State.callEntry_gpr _ (by decide)).trans r1
  have c2 : (s.callEntry.gpr .r2).toNat = 1 := by rw [State.callEntry_gpr _ (by decide), r2]; rfl
  simp only [Pbkdf2.Md.Arm.compK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0, c1, c2]
    at hpost
  simp only [wr] at fr
  rw [aSt, a0] at fr
  rw [aSt, aO, MdStream.Md.compressBlocks_one] at hpost
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) rd' wr' sp', s.mem, hx, fr, hpost⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact wSt
    · exact wCW
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact tSt
    · exact tCW

end VG.Proof.RsaPss.Arm
