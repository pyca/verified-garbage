module

public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaOaep.Arm.Calls
import VerifiedGarbage.Proof.RsaPss.Params
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPss.Arm.CtSel
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.Arm.CtBase
public import VerifiedGarbage.Proof.RsaPss.Arm.TabCall
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! ### `RsaPss.Arm.CtLoop`, which the modules that import this one used -/

section

/-! ### `RsaPss.Arm.CtComp`, which only this module used -/

section

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
  obtain aSt : State.addr (scr + BitVec.ofNat 32 oSt) = sa scr oSt := hg.addr (by decide)
  obtain aO : State.addr (scr + BitVec.ofNat 32 o) = sa scr o := hg.addr (by pomega)
  obtain a0 : State.addr (scr + BitVec.ofNat 32 oCW) = sa scr oCW := hg.addr (by decide)
  obtain d1 : (sR scr oSt h.N).Disjoint (sR scr oCW h.H.md.so) := Geo.sep (by pomega) (by pomega) (by pomega)
  obtain d2 : (sR scr o h.B).Disjoint (sR scr oSt h.N) := Geo.sep (o := o) (n := h.B) (e := oSt) (k := h.N)
    (by left; unfold oSt; omega_using [ho3]) (by unfold oRsa; omega_using [ho3]) (by unfold oSt oRsa at *; omega_using [hN])
  obtain d3 : (sR scr o h.B).Disjoint (sR scr oCW h.H.md.so) := Geo.sep (o := o) (n := h.B) (e := oCW) (k := h.H.md.so)
    (by left; unfold oCW; omega_using [ho3]) (by unfold oRsa; omega_using [ho3]) (by unfold oCW oRsa at *; omega_using [hso])
  obtain f0 : (scr + BitVec.ofNat 32 oSt).toNat + h.N ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  obtain f1 : (scr + BitVec.ofNat 32 o).toNat + h.B ≤ 2 ^ 32 := by rw [hg.scr_lt (by pomega)]; pomega
  obtain f3 : (scr + BitVec.ofNat 32 oCW).toNat + h.H.md.so ≤ 2 ^ 32 := by rw [hg.scr_lt (by decide)]; pomega
  obtain rO : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr o) h.B :=
    fun σ s hc => hg.rd hc.st (o := o) (n := h.B) (by unfold oRsa; omega_using [ho3])
  obtain rSt : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oSt) h.N := fun σ s hc => hg.wr hc.st (by pomega)
  obtain rCW : ∀ σ s, Ctx L scr σ s → InRegions s.wr (sa scr oCW) h.H.md.so := fun σ s hc => hg.wr hc.st (by pomega)
  obtain rStR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oSt) h.N := fun σ s hc => hg.rd hc.st (by pomega)
  obtain rCWR : ∀ σ s, Ctx L scr σ s → InRegions (s.rd ++ s.wr) (sa scr oCW) h.H.md.so :=
    fun σ s hc => hg.rd hc.st (by pomega)
  obtain wSt : ∃ R ∈ L.W, Region.Sub (sR scr oSt h.N) R := hg.inW (by pomega)
  obtain wCW : ∃ R ∈ L.W, Region.Sub (sR scr oCW h.H.md.so) R := hg.inW (by pomega)
  obtain tSt : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oSt h.N) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
  obtain tCW : Region.Disjoint ⟨L.fr sS, 4⟩ (sR scr oCW h.H.md.so) := hg.slot ok (by pomega) (by rw [hg.F]; decide)
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
  obtain pre : ∀ σ s, F₁ σ s → (Pbkdf2.Md.Arm.compK h.md h.H.md.so).pre (s.callEntry.withRegions rd wr) := by
    rintro σ s ⟨⟨hc, _, r0, r1, r2, r3⟩, _⟩
    simp only [Pbkdf2.Md.Arm.compK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
      r0, r1, r2, r3, Pbkdf2.Md.Arm.one32, Nat.mul_one, rd, wr]
    refine ⟨trivial, trivial, ?_, ?_, ?_, f0, f1, f3⟩
    · rw [aSt, a0]; exact d1
    · rw [aO, aSt]; exact d2
    · rw [aO, a0]; exact d3
  obtain cov : ∀ σ s, F₁ σ s → Covers (rd ++ wr) (s.rd ++ s.wr) ∧ Covers wr s.wr := by
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
  obtain c0 : s.callEntry.gpr .r0 = scr + BitVec.ofNat 32 oSt := (State.callEntry_gpr _ (by decide)).trans r0
  obtain c1 : s.callEntry.gpr .r1 = scr + BitVec.ofNat 32 o := (State.callEntry_gpr _ (by decide)).trans r1
  obtain c2 : (s.callEntry.gpr .r2).toNat = 1 := by rw [State.callEntry_gpr _ (by decide), r2]; rfl
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

end

end

/-!
# RSASSA-PSS on ARMv7: hashing, the compression loop

`compLoop_vp`: every one of `Y`'s `nbm` blocks compressed into the hash
value at `oSt`, and the hash value after block `lb` (the last of the padded
message, `⌊(ℓ + L) / B⌋`, under a mask) selected into `oSel`: it is that of
`Y`'s first `lb + 1` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaOaep.Arm (tA)
open VG.Impl.RsaOaep.Arm (sTab)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- What the compression loop writes. -/
abbrev loopW (L : Lay) (scr : BitVec 32) : List Region :=
  [sR scr oSt h.N, sR scr oCW h.H.md.so, sR scr oSel h.N, slotR L sBi]

/-- The memory of the loop's state after `b` blocks, from `Y`'s bytes `yv`
(`T` of them), with `lb` the last block of the padded message. -/
structure CM (L : Lay) (scr : BitVec 32) (T : Nat) (yv : Nat → Byte) (lb b : Nat) (m : Mem) : Prop where
  y : ∀ i < T, m (sa scr (oY + i)) = yv i
  bi : m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b
  st : h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist yv T) b
  sel : lb < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist yv T) (lb + 1)

theorem ofNat_shl {x : Nat} (hx : x * h.B < 2 ^ 32) : BitVec.ofNat 32 x <<< lgB h.sh = BitVec.ofNat 32 (x * h.B) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h.pow_lg,
    Nat.mod_eq_of_lt (a := x) (by have := Nat.le_mul_of_pos_right x (show 0 < h.B by have := h.B_ge; omega_using [this]); omega_using [hx, this])]


/-- `pomega`'s offsets, as one fact. -/
private theorem offs : oCW = 4096 ∧ oSt = 4608 ∧ oSel = 4864 ∧ oDig = 4928 ∧ oLen = 4992 ∧ oEm = 0 ∧ oY = 1024 ∧
    oRsa = 8192 ∧ frameBytes = 128 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `pomega` for `compLoop_vp`, which calls it thirty times among eighty hypotheses: the offsets by one
`have`, not nine, and `omega_arith`, which reads only the arithmetic facts of the context. -/
local macro "pomega'" : tactic =>
  `(tactic| (have _ := offs
             (try simp only [VG.Impl.RsaPss.Arm.blk, VG.Impl.RsaPss.Arm.dig, VG.Impl.RsaPss.Arm.hvN,
               VG.Impl.RsaPss.Arm.lenL, VG.Proof.RsaPss.Arm.PssHash.sh, VG.Impl.RsaPss.Arm.Hash.sh,
               VG.Impl.Pbkdf2.Md.Arm.Hash.B, VG.Impl.Pbkdf2.Md.Arm.Hash.D, VG.Proof.RsaPss.Arm.PssHash.B,
               VG.Proof.RsaPss.Arm.PssHash.D, VG.Proof.RsaPss.Arm.PssHash.N, VG.Proof.RsaPss.Arm.PssHash.L] at *)
             omega_arith))

/-- The compression loop. -/
theorem compLoop_vp (hg : Geo L scr) {f : MdFns} {dn : String} {p ai ac ad : BitVec 32}
    (hR : ∃ R ∈ L.ro, ∀ o, o + 4 ≤ 44 → R.Contains (tA p o) 4) (hne : f.comp ≠ []) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm)
    {yv : State → Nat → Byte} {ℓ : State → Nat} (hℓ : ∀ σ, (ℓ σ + h.L) / h.B < nbm) (hℓ2 : ∀ σ, ℓ σ < 2048)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame (loopW h L scr) m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (ℓ σ))
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm)
    (hX : ∀ σ m, Inv σ m → m.readW (L.fr sTab) 32 = p ∧ HTab h dn f p ai ac ad σ) :
    VP (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ (∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = yv σ i) ∧
        h.md.stateAt s.mem (sa scr oSt) = h.ok.iv) ∧ s.syms = σ.syms)
      (compLoop f h.sh)
      (fun σ s => (Ctx L scr σ s ∧ Inv σ s.mem ∧ h.md.stateAt s.mem (sa scr oSel) =
        h.md.compressList h.ok.iv (ylist (yv σ) (nbm * h.B)) ((ℓ σ + h.L) / h.B + 1)) ∧ s.syms = σ.syms) := by
  -- Facts are stated with `obtain`, not `have`: `have` keeps its proof in the context (a `let` nothing
  -- unfolds), and every `(by …)` in a term first instantiates and shares the whole context (`Term.runTactic`).
  have hN := h.N_le
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have hso := h.so_le
  have fit := hg.fit
  obtain ⟨σ', ok⟩ := hg.ok
  obtain nbB : nbm ≤ nbm * h.B := Nat.le_mul_of_pos_right nbm (by omega_arith)
  generalize hT : nbm * h.B = T at hnb nbB ⊢
  -- Disjointness of what the loop writes from what it keeps.
  obtain dY : ∀ r ∈ loopW h L scr, Region.Disjoint (sR scr oY T) r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Geo.sep (by pomega') (by pomega') (by pomega')
    · exact Geo.sep (by pomega') (by pomega') (by pomega')
    · exact Geo.sep (by pomega') (by pomega') (by pomega')
    · exact (hg.slot ok (by pomega') (by rw [hg.F]; decide)).symm
  obtain dB : ∀ r ∈ [sR scr oSt h.N, sR scr oCW h.H.md.so, sR scr oSel h.N], (slotR L sBi).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg.slot ok (by pomega') (by rw [hg.F]; decide)
  obtain dBN : ∀ r ∈ [slotR L sBi], (slotR L sNb).Disjoint r ∧ (slotR L sL).Disjoint r ∧ (slotR L sS).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨Lay.fr_sep (by decide) (by decide) (by decide), Lay.fr_sep (by decide) (by decide) (by decide),
      Lay.fr_sep (by decide) (by decide) (by decide)⟩
  obtain sp_eq : ∀ {F : State → State → Prop}, (∀ σ s, F σ s → Ctx L scr σ s) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp :=
    fun hF _ _ _ _ h₁ h₂ => (hF _ _ h₁).st.sp.trans (hF _ _ h₂).st.sp.symm
  let CS : Nat → State → State → Prop := fun b σ s =>
    (Ctx L scr σ s ∧ Inv σ s.mem ∧ CM h L scr T (yv σ) (((ℓ σ + h.L) / h.B)) b s.mem) ∧ s.syms = σ.syms
  -- The first block.
  refine VP.seq (G := CS 0) (VP.syms (VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1) fun σ s ⟨hc, hi, hy, hst⟩ => ?_)) ?_
  · have hw : WP isa (.block compInit) s fun t => t.mem = s.mem.writeW (L.fr sBi) (0 : BitVec 32) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
      prun [compInit, sp0, mw, st, hc.st.sp, hc.aFr hg, hc.wFr hg]
    refine WP.mono hw fun t ⟨m, rd, wr, sp⟩ => ?_
    obtain fr : Frame [slotR L sBi] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ((dBN r hr).2.2)) rd wr sp, hI σ _ _ hi (fr.mono ?_),
      ⟨sbytes_keep fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dY _ (by simp [loopW])) (by pomega') hy, ?_, ?_, fun h0 => absurd h0 (Nat.not_lt_zero _)⟩⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp
    · rw [m, Mem.readW_writeW_self32]; rfl
    · rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega') (by rw [hg.F]; decide)).symm),
        hst, Md.compressList_zero]
  -- The loop.
  have hlbT : ∀ σ, (ℓ σ + h.L) / h.B < nbm := hℓ
  refine (VP.loop (I := fun n σ s => n ≤ nbm ∧ CS (nbm - n) σ s) (fun n => ?_) (nbm - 1)).mono
    (fun σ s hs => ⟨by omega_arith, by rw [show nbm - (nbm - 1 + 1) = 0 by omega_arith]; exact hs⟩) fun _ _ h => h
  obtain keepI : ∀ σ m m' (rs : List Region), Inv σ m → (∀ r ∈ rs, r ∈ loopW h L scr) → Frame rs m m' → Inv σ m' :=
    fun σ m m' rs hi hs fr => hI σ m m' hi (fr.mono hs)
  -- Block `b`.
  by_cases hn : n + 1 ≤ nbm
  swap
  · exact VP.empty fun σ s ⟨h, _⟩ => hn h
  generalize hb : nbm - (n + 1) = b
  obtain hbn : b < nbm := by omega_arith
  obtain hbB : b * h.B + h.B ≤ T := by rw [← hT, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_arith)
  obtain hbB32 : b * h.B < 2 ^ 32 := by omega_arith
  -- What each stage keeps of memory.
  let X2 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧ h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (((ℓ σ + h.L) / h.B) < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1))
  let X4 : State → Mem → Prop := fun σ m => Inv σ m ∧ (∀ i < T, m (sa scr (oY + i)) = yv σ i) ∧
    m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b ∧ h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist (yv σ) T) (b + 1) ∧
    (((ℓ σ + h.L) / h.B) < b + 1 → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1))
  obtain hsub : ∀ rs : List Region, (∀ r ∈ rs, r ∈ loopW h L scr) → ∀ r ∈ rs, Region.Disjoint (sR scr oY T) r :=
    fun rs hs r hr => dY r (hs r hr)
  show VP _ (.seq (.block (compSet h.sh)) (.seq (compCall f) (.seq (.block (selSet h.sh))
    (.seq (countLoop selBody) (.block compNext))))) _
  refine VP.seq (G := fun σ s => ((Ctx L scr σ s ∧ Inv σ s.mem ∧ CM h L scr T (yv σ) (((ℓ σ + h.L) / h.B)) b s.mem) ∧
      s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ s.gpr .r3 = scr + BitVec.ofNat 32 oCW ∧
      s.gpr .r6 = scr + BitVec.ofNat 32 (oY + b * h.B)) ∧ s.syms = σ.syms) ?_
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X2 σ s.mem) ∧ s.syms = σ.syms) ?_
    (VP.seq (G := fun σ s => ((Ctx L scr σ s ∧ X2 σ s.mem) ∧ s.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧
        s.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧ s.gpr .lr = BitVec.ofNat 32 h.N ∧
        s.gpr .r2 = maskOf (b * h.B = ((ℓ σ + h.L) / h.B) * h.B)) ∧ s.syms = σ.syms) ?_
    (VP.seq (G := fun σ s => (Ctx L scr σ s ∧ X4 σ s.mem) ∧ s.syms = σ.syms) ?_ ?_)))
  · -- The compression's registers.
    refine (VP.syms (VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.2.1.1) fun σ s ⟨_, ⟨hc, hi, hm⟩, _⟩ => ?_)).mono
      (fun σ s hs => ⟨hs, hs.2.2⟩) fun _ _ h => h
    obtain hw : WP isa (.block (compSet h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r3 = scr + BitVec.ofNat 32 oCW ∧
        t.gpr .r6 = scr + BitVec.ofNat 32 (oY + b * h.B) := by
      prun [compSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hm.bi,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oY < 2 ^ 16 by decide),
        movw_val (show oCW < 2 ^ 16 by decide), ofNat_shl h hbB32, h.lg_range, dpVal,
        BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r3, r6⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hi, m ▸ hm⟩, r0, r3, r6⟩
  · -- The compression.
    refine (comp_vp h hg hR hne (dn := dn) (ai := ai) (ad := ad) (o := oY + b * h.B) (by pomega') (X := fun σ m => Inv σ m ∧
        CM h L scr T (yv σ) (((ℓ σ + h.L) / h.B)) b m) fun σ m hm => hX σ m hm.1).mono
      (fun σ s ⟨⟨⟨hc, hi, hm⟩, r0, r3, r6⟩, sy⟩ => ⟨⟨hc, ⟨hi, hm⟩, r0, r3, r6⟩, sy⟩)
      fun σ s ⟨⟨hc, m₀, ⟨hi, hm⟩, fr, e⟩, sy⟩ => ⟨⟨hc, keepI σ _ _ _ hi (by simp) fr, ?_, ?_, ?_, ?_⟩, sy⟩
    · exact sbytes_keep fr (hsub _ (by simp)) (by pomega') hm.y
    · exact slot_keep fr (fun r hr => dB r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h' | h' <;> simp [h'])) hm.bi
    · rw [e, hm.st, Md.compressList_succ]
      refine congrArg _ (h.md.parse_congr fun k hk => ?_)
      rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, show oY + b * h.B + k = oY + (b * h.B + k) by omega_arith,
        hm.y _ (by pomega'), ylist_getD (by have := Nat.mul_comm b h.B; pomega'), Nat.mul_comm]
    · intro hl
      obtain dsel : ∀ r ∈ compW h scr, Region.Disjoint (sR scr oSel h.N) r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Geo.sep (by pomega') (by pomega') (by pomega')
        · exact Geo.sep (by pomega') (by pomega') (by pomega')
      rw [stateAt_keep h fr dsel, hm.sel hl]
  · -- The selection's registers.
    refine (VP.syms (VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1) fun σ s ⟨hc, hx⟩ => ?_)).mono (fun _ _ h => h)
      fun _ _ h => h
    obtain l2 : ℓ σ + h.L < 2 ^ 32 := by have := hℓ2 σ; omega_arith
    obtain e1 : BitVec.ofNat 32 (ℓ σ) + BitVec.ofNat 32 h.L = BitVec.ofNat 32 (ℓ σ + h.L) := BitVec.ofNat_add_ofNat ..
    obtain e2 : BitVec.ofNat 32 (ℓ σ + h.L) >>> lgB h.sh = BitVec.ofNat 32 (((ℓ σ + h.L) / h.B)) := by
      rw [VG.Proof.MdStream.Arm.ofNat_shr l2, h.pow_lg]
    obtain e3 : BitVec.ofNat 32 (((ℓ σ + h.L) / h.B)) <<< lgB h.sh = BitVec.ofNat 32 (((ℓ σ + h.L) / h.B) * h.B) :=
      ofNat_shl h (by have := Nat.div_mul_le_self (ℓ σ + h.L) h.B; omega_arith)
    obtain e4 := eqBit (a := b * h.B) (b := ((ℓ σ + h.L) / h.B) * h.B) (by omega_arith)
      (by have := Nat.div_mul_le_self (ℓ σ + h.L) h.B; have := hℓ2 σ; omega_arith)
    obtain hw : WP isa (.block (selSet h.sh)) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 oSt ∧ t.gpr .r1 = scr + BitVec.ofNat 32 oSel ∧
        t.gpr .lr = BitVec.ofNat 32 h.N ∧ t.gpr .r2 = maskOf (b * h.B = ((ℓ σ + h.L) / h.B) * h.B) := by
      prun [selSet, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, hx.2.2.1, hsl σ _ hx.1,
        movw_val (show oSt < 2 ^ 16 by decide), movw_val (show oSel < 2 ^ 16 by decide),
        movw_val (show h.L < 2 ^ 16 by omega_arith), movw_val (show h.N < 2 ^ 16 by omega_arith),
        movw_val (show 0 < 2 ^ 16 by decide), ofNat_shl h hbB32, e1, e2, e3, e4, neg_bit, neg_bit', h.lg_range, dpVal]
    exact WP.mono hw fun t ⟨m, rd, wr, sp, r0, r1, lr, r2⟩ => ⟨⟨hc.regs rd wr sp m, m ▸ hx⟩, r0, r1, lr, r2⟩
  · -- The selection.
    refine (VP.syms (sel_vp h hg (c := fun σ => b * h.B = ((ℓ σ + h.L) / h.B) * h.B) (X := X2))).mono
      (fun σ s ⟨⟨⟨hc, hx⟩, r0, r1, lr, r2⟩, sy⟩ => ⟨⟨hc, hx, r0, r1, lr, r2⟩, sy⟩)
      fun σ s ⟨⟨hc, m₀, ⟨hi, hy, hbi, hst, hsel⟩, fr, hb'⟩, sy⟩ => ⟨⟨hc, keepI σ _ _ _ hi (by simp) fr, ?_, ?_, ?_, ?_⟩, sy⟩
    · exact sbytes_keep fr (hsub _ (by simp)) (by pomega') hy
    · exact slot_keep fr (fun r hr => dB r (by simp only [List.mem_singleton] at hr; simp [hr])) hbi
    · rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Geo.sep (by pomega') (by pomega') (by pomega')), hst]
    · intro hl
      by_cases e : b * h.B = ((ℓ σ + h.L) / h.B) * h.B
      · have eb : b = ((ℓ σ + h.L) / h.B) := Nat.eq_of_mul_eq_mul_right (by omega_arith) e
        rw [← eb, ← hst]
        refine h.ok.reloc _ _ _ _ fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_left e]
        simp only [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      · have hl' : ((ℓ σ + h.L) / h.B) < b := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with h' | h'
          · exact h'
          · exact absurd (by rw [h']) e
        rw [← hsel hl']
        refine h.md.stateAt_congr fun i hi' => ?_
        rw [sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← sa, hb' i hi', ite_eq_right e]
  · -- The next block.
    refine VP.blk (blkOk rfl) (sp_eq fun _ _ h => h.1.1) fun σ s ⟨⟨hc, hi, hy, hbi, hst, hsel⟩, sy⟩ => ?_
    obtain hw : WP isa (.block compNext) s fun t => t.mem = s.mem.writeW (L.fr sBi) (BitVec.ofNat 32 (b + 1)) ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.z = decide (b + 1 = nbm) := by
      prun [compNext, sp0, ld, st, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.wFr hg, hbi, hsn σ _ hi, dpVal,
        VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, VG.Proof.MdStream.Arm.sub_beq (show b + 1 < 2 ^ 32 by omega_arith)
          (show nbm < 2 ^ 32 by omega_arith)]
      rw [Mem.readW_writeW_sep (Offset.sep _ (by left; decide) (by decide) (by decide)) (by decide), hsn σ _ hi]
      exact VG.Proof.MdStream.Arm.sub_beq (by omega_arith) (by omega_arith)
    refine WP.mono_syms hw fun t ⟨m, rd, wr, sp, z⟩ ty => ?_
    obtain fr : Frame [slotR L sBi] s.mem t.mem := by rw [m]; exact slot_frame L _ _ _
    obtain hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.FR, List.mem_cons_self, Offset.sub_base _ (by rw [hg.F]; decide)⟩)
      (fun r hr => (dBN r hr).2.2) rd wr sp
    obtain hi' : Inv σ t.mem := keepI σ _ _ _ hi (by simp) fr
    obtain hsel' : ((ℓ σ + h.L) / h.B) < b + 1 → h.md.stateAt t.mem (sa scr oSel) = h.md.compressList h.ok.iv (ylist (yv σ) T) (((ℓ σ + h.L) / h.B) + 1) := fun hl => by
      rw [stateAt_keep h fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega') (by rw [hg.F]; decide)).symm),
        hsel hl]
    obtain dz : decide (b + 1 = nbm) = decide (n = 0) := by simp only [decide_eq_decide]; omega_arith
    obtain sy' : t.syms = σ.syms := ty.trans sy
    refine ⟨by rw [VG.Proof.X25519.Arm.eval_ne, z, dz]; cases n <;> simp,
      fun h0 => ⟨⟨hc', hi', hsel' (by have := hlbT σ; omega_arith)⟩, sy'⟩, fun hp => ⟨by omega_arith, ?_⟩⟩
    rw [show nbm - n = b + 1 by omega_arith]
    refine ⟨⟨hc', hi', sbytes_keep fr (hsub _ (by simp)) (by pomega') hy, by rw [m, Mem.readW_writeW_self32], ?_, hsel'⟩, sy'⟩
    rw [stateAt_keep h fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hg.slot ok (by pomega') (by rw [hg.F]; decide)).symm), hst]

end VG.Proof.RsaPss.Arm

end

end

/-!
# RSASSA-PSS on ARMv7: the encoding's parameters

From the modulus' first byte `n₀` (`x`), `params` stores the mask `c` of
`maskedDB`'s first byte (`cW`), `lo` (`loW`) and `dbLen = k - lo - hLen - 1`
(`dbW`) to their slots, and `saltFits` (after `expLen` when verifying) sets
the flags of whether everything fits (`fits_z`): `n₀ ≠ 0` and
`lo + hLen + 2 + sLen ≤ k`. The values, from a table of the 256 bytes
(`params_table`), are the specification's (`cW_byte`, `lo_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (dpVal)

/-- `2^⌊log₂ x⌋ - 1` for `x ≥ 2`, as `params` computes it. -/
abbrev smearW (x : BitVec 32) : BitVec 32 :=
  x >>> 1 ||| x >>> 1 >>> 1 ||| (x >>> 1 ||| x >>> 1 >>> 1) >>> 2 |||
    (x >>> 1 ||| x >>> 1 >>> 1 ||| (x >>> 1 ||| x >>> 1 >>> 1) >>> 2) >>> 4

/-- `lo`: 1 if `x ≤ 1`. -/
abbrev loW (x : BitVec 32) : BitVec 32 := (smearW x - 1) >>> 31

/-- The mask of `maskedDB`'s first byte. -/
abbrev cW (x : BitVec 32) : BitVec 32 := smearW x ||| (0 - loW x) &&& 0xFF

/-- `dbLen = k - lo - hLen - 1`. -/
abbrev dbW (K D : Nat) (x : BitVec 32) : BitVec 32 := BitVec.ofNat 32 K - loW x - BitVec.ofNat 32 (D + 1)

theorem params_table : ∀ x < 256, loW (BitVec.ofNat 32 x) = (if x ≤ 1 then 1 else 0) ∧
    (x = 1 → cW (BitVec.ofNat 32 x) = 0xFF) ∧
    (2 ≤ x → ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ cW (BitVec.ofNat 32 x) = BitVec.ofNat 32 (2 ^ j - 1)) := by
  decide +kernel

theorem setWidth_byte (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `lo` of a byte. -/
theorem loW_byte (b : Byte) : loW (b.setWidth 32) = BitVec.ofNat 32 (if b.toNat ≤ 1 then 1 else 0) := by
  rw [setWidth_byte, (params_table b.toNat b.isLt).1]
  split <;> rfl

theorem dbW_byte (K D : Nat) (b : Byte) :
    dbW K D (b.setWidth 32) = BitVec.ofNat 32 K - BitVec.ofNat 32 (if b.toNat ≤ 1 then 1 else 0) -
      BitVec.ofNat 32 (D + 1) := by
  show BitVec.ofNat 32 K - loW (b.setWidth 32) - _ = _
  rw [loW_byte]

/-- The mask of a byte not zero: the specification's `0xFF >>> z`. -/
theorem cW_byte {b : Byte} (h0 : b ≠ 0) (rest : List Byte) :
    (cW (b.setWidth 32)).setWidth 8 =
      (0xFF : Byte) >>> (8 * Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) -
        (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1)) := by
  rw [RsaPss.mask_eq rest h0, setWidth_byte]
  have hb := b.isLt
  have hn : b.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  obtain ⟨-, h1, h2⟩ := params_table b.toNat hb
  by_cases e : b.toNat = 1
  · rw [h1 e, ite_eq_left e]; rfl
  · obtain ⟨j, hj, hl, hu, he⟩ := h2 (by omega_arith)
    rw [he, ite_eq_right e, RsaPss.log2_eq hn hl hu]
    apply BitVec.eq_of_toNat_eq
    have : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-- `lo = k - emLen`, for a first byte not zero. -/
theorem lo_eq {b : Byte} (h0 : b ≠ 0) (rest : List Byte) :
    (b :: rest).length - Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip (b :: rest)) - 1) =
      if b.toNat ≤ 1 then 1 else 0 := by
  rw [RsaPss.emLength_eq rest h0, List.length_cons]
  have hn : b.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  by_cases e : b.toNat = 1
  · rw [ite_eq_left e, ite_eq_left (by omega_arith)]; omega_arith
  · rw [ite_eq_right e, ite_eq_right (by omega_arith)]; omega_arith

/-- Whether a word is not zero, as the top bit of `-x | x`. -/
theorem nzW (x : BitVec 32) : ((0 - x) ||| x) >>> 31 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · rw [ite_eq_right h]
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_or, BitVec.toNat_sub]
    show (((2 ^ 32 - x.toNat + 0) % 2 ^ 32) ||| x.toNat) / 2 ^ 31 = 1
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega_arith)]
    by_cases hb : x.toNat < 2 ^ 31
    · have : 2 ^ 31 ≤ (2 ^ 32 - x.toNat) ||| x.toNat := Nat.le_trans (by omega_arith) Nat.left_le_or
      have : (2 ^ 32 - x.toNat) ||| x.toNat < 2 ^ 32 := Nat.or_lt_two_pow (by omega_arith) hlt
      omega_arith
    · have : 2 ^ 31 ≤ (2 ^ 32 - x.toNat) ||| x.toNat := Nat.le_trans (by omega_arith) Nat.right_le_or
      have : (2 ^ 32 - x.toNat) ||| x.toNat < 2 ^ 32 := Nat.or_lt_two_pow (by omega_arith) hlt
      omega_arith

/-- The flags of `saltFits`: whether everything fits. -/
theorem fits_z {x K D sl lo : Nat} (hx : x < 256) (hK : K ≤ 1024) (hD : D ≤ 64) (hsl : sl < 2 ^ 32) (hlo : lo ≤ 1) :
    (((BitVec.ofNat 32 x - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1) >>> 31 |||
        (BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 - BitVec.ofNat 32 sl) >>> 31 |||
        BitVec.ofNat 32 sl >>> 31) - 0 == 0) = decide (x ≠ 0 ∧ lo + D + 2 + sl ≤ K) := by
  have e1 : (BitVec.ofNat 32 x - 1) >>> 31 = if x < 1 then 1 else 0 := ltBit (b := 1) (by omega_arith) (by decide)
  have e2 : BitVec.ofNat 32 K - BitVec.ofNat 32 lo - BitVec.ofNat 32 (D + 1) - 1 =
      BitVec.ofNat 32 K - BitVec.ofNat 32 (lo + D + 2) := by
    rw [BitVec.sub_sub, BitVec.sub_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat, show lo + (D + 1 + 1) = lo + D + 2 by omega_arith]
  have e3 : BitVec.ofNat 32 sl >>> 31 = if 2 ^ 31 ≤ sl then 1 else 0 := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr hsl]
    by_cases h : 2 ^ 31 ≤ sl
    · rw [ite_eq_left h, Nat.div_eq_of_lt_le (k := 1) (by omega_arith) (by omega_arith)]; rfl
    · rw [ite_eq_right h, Nat.div_eq_of_lt (by omega_arith)]; rfl
  have hz : ∀ y : BitVec 32, y - 0 = y := fun y => BitVec.sub_zero y
  have hor : ∀ a b : BitVec 32, (a ||| b = 0) ↔ (a = 0 ∧ b = 0) := fun a b => BitVec.or_eq_zero_iff
  have hb01 : ∀ (p : Prop) [Decidable p], ((if p then (1 : BitVec 32) else 0) = 0) ↔ ¬ p := by
    intro p _; by_cases hp : p <;> simp [hp]
  rw [e1, e2, ltBit (by omega_arith) (by omega_arith), e3, hz, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, hor, hor, hor,
    hb01, hb01, hb01]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hf : lo + D + 2 ≤ K := by omega_arith
    rw [Offset.ofNat_sub_ofNat hf, ltBit (by omega_arith) (by omega_arith), hb01] at h3
    omega_arith
  · rintro ⟨h1, h2⟩
    have hf : lo + D + 2 ≤ K := by omega_arith
    refine ⟨⟨⟨by omega_arith, by omega_arith⟩, ?_⟩, by omega_arith⟩
    rw [Offset.ofNat_sub_ofNat hf, ltBit (by omega_arith) (by omega_arith), hb01]
    omega_arith

variable {L : Lay} {scr : BitVec 32}

/-- `params`, from the modulus at `r0` (its first byte `x`), `k` in `r1` and
`hLen + 1` in `r11`, with `r12 = sp`. -/
theorem params_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) {nP : BitVec 32} {K D : Nat}
    (r0 : s.gpr .r0 = nP) (hn : InRegions (s.rd ++ s.wr) (State.addr nP) 1) (r1 : s.gpr .r1 = BitVec.ofNat 32 K)
    (r11 : s.gpr .r11 = BitVec.ofNat 32 (D + 1)) (r12 : s.gpr .r12 = L.B) :
    WP isa (.block params) s fun t =>
      t.mem = ((s.mem.writeW (L.fr sC) (cW ((s.mem (State.addr nP)).setWidth 32))).writeW (L.fr sLo)
        (loW ((s.mem (State.addr nP)).setWidth 32))).writeW (L.fr sDb) (dbW K D ((s.mem (State.addr nP)).setWidth 32)) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .r8 = ((s.mem (State.addr nP)).setWidth 32 - 1) >>> 31 |||
        (dbW K D ((s.mem (State.addr nP)).setWidth 32) - 1) >>> 31 ∧
      t.gpr .r9 = dbW K D ((s.mem (State.addr nP)).setWidth 32) - 1 ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r10 = s.gpr .r10 ∧ t.gpr .r12 = s.gpr .r12 := by
  prun [params, st, mw, r0, r1, r11, r12, hn, hc.aFr hg, hc.wFr hg, dpVal, smearW, loW, cW, dbW]

/-- `saltFits`: the flags of whether the salt length `r2` also fits. -/
theorem saltFits_wp (s : State) :
    WP isa (.block saltFits) s fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.z = ((s.gpr .r8 ||| (s.gpr .r9 - s.gpr .r2) >>> 31 ||| s.gpr .r2 >>> 31) - 0 == 0) := by
  prun [saltFits, dpVal]

/-- `expLen`: `[any_salt_len ≠ 0]` (from `r10`) to its slot, and the
expected salt length in `r2`, 0 if any. -/
theorem expLen_wp (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) (r12 : s.gpr .r12 = L.B) :
    WP isa (.block expLen) s fun t =>
      t.mem = s.mem.writeW (L.fr sAny) (if s.gpr .r10 = 0 then (0 : BitVec 32) else 1) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.gpr .r2 = (if s.gpr .r10 = 0 then s.gpr .r2 else 0) ∧ t.gpr .r8 = s.gpr .r8 ∧
      t.gpr .r9 = s.gpr .r9 := by
  have e : ∀ x : BitVec 32, (0 - x ||| x) >>> 31 = if x = 0 then 0 else 1 := nzW
  prun [expLen, st, mw, r12, hc.aFr hg, hc.wFr hg, dpVal, e]
  by_cases h0 : s.gpr .r10 = 0
  · simp only [h0, ite_true]
    rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
  · simp only [h0, ite_false]
    rw [show (1 : BitVec 32) - 1 = 0 by decide]
    exact BitVec.and_zero

end VG.Proof.RsaPss.Arm
