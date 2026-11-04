module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Hash
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-DSA on ARMv7, `verify_message` and `verify_message_cached`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`verifyContract p Arm.abi 36` whose frames use at most 36 bytes of stack
(`VerifyFn`): its call on the key, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`), after which the saves
are intact (`Fin`), for any layout with the facts `VFacts` (those of both
functions, `VPre.vfacts` and `CPre.vfacts`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified Arm.target c (verifyContract p Arm.abi 36)
  su : stackUse c ≤ 36

/-- The precondition of `verifyContract p Arm.abi 36`, from its facts. -/
theorem verifyC_pre {p : Params} {E : State} (sp : 36 ≤ E.sp.toNat)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), p.pkLen⟩, ⟨State.addr (E.gpr .r1), 64⟩,
      ⟨State.addr (E.gpr .r2), p.sigLen⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), p.pkLen⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), p.sigLen⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r0), p.pkLen⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r2), p.sigLen⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (n0 : (E.gpr .r0).toNat + p.pkLen ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + p.sigLen ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + sScr p ≤ 2 ^ 32) :
    (verifyContract p Arm.abi 36).pre E := by
  sig_pre [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨sp, by have := E.sp.isLt; omega, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fSig), (.r3, .slot fScr)]

section
variable {p : Params} {L : Lay}

/-- What a layout of `verify_message` (or `verify_message_cached`) says of
the key, `sig` and `scratch`, beyond `Lay.Ok`. -/
structure VFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.pkLen
  scrLen : L.scrLen = mScrLen p
  hE : L.E = oE p
  xSig : L.SC.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 32
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.rd

theorem VPre.vfacts {s : State} (h : VPre p s) : VFacts p (vlay p s) :=
  ⟨rfl, rfl, rfl, h.sigScr.symm, h.stkSig, h.nSig, by simp [vlay, h.rd]⟩

theorem CPre.vfacts {s : State} (h : CPre p s) : VFacts p (clay p s) :=
  ⟨rfl, rfl, rfl, h.sigScr.symm, h.stkSig, h.nSig, by simp [clay, h.rd]⟩

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (L : Lay) : List Region :=
  [⟨State.addr L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨State.addr L.sig, p.sigLen⟩]
abbrev verifyWr (p : Params) (L : Lay) : List Region := [⟨State.addr L.scr, sScr p⟩]

theorem VFacts.sub (F : VFacts p L) : Region.Sub ⟨State.addr L.scr, sScr p⟩ L.SC := by
  show Region.Sub _ ⟨_, L.scrLen⟩
  rw [F.scrLen]; exact sScr_sub p _

theorem VFacts.inKey (F : VFacts p L) (hL : L.Ok) : (⟨State.addr L.key, p.pkLen⟩ : Region) ∈ L.rd := by
  have := hL.inKey; simp only [Lay.KEY, F.key] at this; exact this

/-- The working space of the function on `μ` is writable. -/
theorem VFacts.wScr (F : VFacts p L) (hL : L.Ok) : ∃ R ∈ L.wr, Within ⟨State.addr L.scr, sScr p⟩ R :=
  ⟨_, hL.inSC, within_base _ (by show sScr p ≤ L.scrLen; rw [F.scrLen, mScr_eq]; simp only [sScr, oE]; omega)⟩

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) (hm : (∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = L.key ∧ t1.gpr .r1 = L.X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = L.sig ∧
      t1.gpr .r3 = L.scr := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fSig) (by simp)
  have e3 := hm (.r3, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega)] at e2
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega)] at e3
  simp only [Lay.vals, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre (hL : L.Ok) (F : VFacts p L) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : Ctx L g m₀ t)
    (hA : ∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = L.SP) :
    (verifyContract p Arm.abi 36).pre (t1.callEntry.withRegions (verifyRd p L) (verifyWr p L)) := by
  obtain ⟨e0, e1, e2, e3⟩ := verifyRegs_of hL hc hA
  have hsub := F.sub
  generalize hE : t1.callEntry.withRegions (verifyRd p L) (verifyWr p L) = E
  have gr : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ hr]
  have g0 : E.gpr .r0 = L.key := by rw [gr (by decide), e0]
  have g1 : State.addr (E.gpr .r1) = L.MU := by rw [gr (by decide), e1, mu_eq hL]
  have g2 : E.gpr .r2 = L.sig := by rw [gr (by decide), e2]
  have g3 : E.gpr .r3 = L.scr := by rw [gr (by decide), e3]
  have gsp : E.sp = L.SP := by rw [← hE, State.withRegions_sp, State.callEntry_sp, hsp1]
  have grd : E.rd = verifyRd p L := by rw [← hE]; rfl
  have gwr : E.wr = verifyWr p L := by rw [← hE]; rfl
  have xKey := hL.xKey; have kKey := hL.kKey; have nKey := hL.nKey
  simp only [Lay.KEY, F.key] at xKey kKey nKey
  refine verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [g0, g1, g2, g3, gsp, grd, gwr]
  · exact hL.nSP
  · exact xKey.symm.sub_right hsub
  · exact x_sScr hL F.hE (by omega)
  · exact F.xSig.symm.sub_right hsub
  · exact kKey
  · exact k_mu hL
  · exact F.kSig
  · exact hL.kX.sub_right hsub
  · exact nKey
  · rw [gr (by decide), e1]
    have := hL.x32_lt
    rw [x32_toNat hL (by omega)]; omega
  · exact F.nSig
  · have := hL.nScr; rw [F.scrLen] at this; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VerifyFn p c) (hL : L.Ok) (F : VFacts p L)
    {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (setArgs verifyArgs)) (.call n c)) t fun s' => Fin L g s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (State.addr L.key) p.pkLen)
          (bytesAt t.mem L.MU 64) (bytesAt t.mem (State.addr L.sig) p.sigLen);
        (s'.gpr .r0 = 1 ∧ ∃ b, w b = some true) ∨ (s'.gpr .r0 = 0 ∧ w minBounds ≠ some true)) := by
  refine WP.seq (WP.mono (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hL hc hA
  have hsp1 : t1.sp = L.SP := hc1.sp
  have hpre := verifyK_pre hL F hc hA hsp1
  obtain ⟨RS, hRS, wS⟩ := F.wScr hL
  refine WP.callF hV.ver.1 hpre ?_ ?_ (by rw [hsp1]; have := hV.su; have := hL.nSP; omega)
    fun s' hrd hwr hsp hf hcs hpost => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (F.inKey hL), within_self _⟩
    · exact ⟨_, List.mem_append_right _ hL.inSC, mu_within hL⟩
    · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · exact ⟨RS, List.mem_append_right _ hRS, wS⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨RS, hRS, wS⟩
  -- After the call.
  have hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW (L.X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact x_sScr hL F.hE (by omega)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA L.SP (stackUse c)) (.inr (belowA_sub hV.su)) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega)).trans hc1.s7, (hsv 4 (by omega)).trans hc1.sLR⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [e0, e1, e2, Proof.MlKem.Arm.setWidth_append32, o.mem] at hpost
  rw [show BitVec.setWidth 64 (L.X32 + 840#32) = L.MU from mu_eq hL] at hpost
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message
