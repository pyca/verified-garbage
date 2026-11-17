module

import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall
public import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Entry
import VerifiedGarbage.Proof.MlDsa.Arm.Message.Hash

/-! ### `MlDsa.Arm.Message.VerifyCall`, which this module and modules that import it used -/

section

/-!
# ML-DSA on ARMv7, `verify_message_cached`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`Verify.verifyE p prepared 52` (`vg_mldsa*_verify` with an encoded key, or
`vg_mldsa*_verify_prepared` with a prepared one) whose frames use at most 52
bytes of stack (`VerifyFn`): its call on the key, `μ` at `X + 840`, `sig` and
the first `scratchWords p` words of `scratch` (`verifyCall_ok`), after which
the saves are intact (`Fin`), for any layout with the facts `VFacts` (those of
`verify_message_cached`'s, `CPre.vfacts`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message_cached` can call. -/
structure VerifyFn (p : Params) (prepared : Bool) (c : Prog isa) : Prop where
  ok : ∀ s, (Verify.verifyE p prepared 52).pre s → ∃ t s', Exec isa c s t s' ∧ Arm.target.abiPreserved s s' ∧
    (Verify.verifyE p prepared 52).post s s'
  ct : ConstantTime isa (Verify.verifyE p prepared 52).pre (Verify.verifyE p prepared 52).pub c
  su : stackUse c ≤ 52

/-- The precondition of `Verify.verifyE p prepared 52`, from its facts. -/
theorem verifyC_pre {p : Params} {prepared : Bool} {E : State} (sp : 52 ≤ E.sp.toNat)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), publicKeyLen p prepared⟩, ⟨State.addr (E.gpr .r1), 64⟩,
      ⟨State.addr (E.gpr .r2), p.sigLen⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), publicKeyLen p prepared⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), p.sigLen⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 52, 52⟩ ⟨State.addr (E.gpr .r0), publicKeyLen p prepared⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 52, 52⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 52, 52⟩ ⟨State.addr (E.gpr .r2), p.sigLen⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 52, 52⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (n0 : (E.gpr .r0).toNat + publicKeyLen p prepared ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + p.sigLen ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + sScr p ≤ 2 ^ 32)
    (hk : PublicKeyOk p prepared E.mem (State.addr (E.gpr .r0))) :
    (Verify.verifyE p prepared 52).pre E :=
  ⟨sp, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3, hk⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fSig), (.r3, .slot fScr)]

section
variable {p : Params} {prepared : Bool} {L : Lay}

/-- What a layout of `verify_message_cached` says of
the key, `sig` and `scratch`, beyond `Lay.Ok`. -/
structure VFacts (p : Params) (prepared : Bool) (L : Lay) : Prop where
  key : L.keyLen = publicKeyLen p prepared
  scrLen : L.scrLen = mScrLen p
  hE : L.E = oE p
  xSig : L.SC.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  kSig : L.STK.Disjoint ⟨State.addr L.sig, p.sigLen⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 32
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.rd

theorem CPre.vfacts {s : State} (h : CPre p prepared s) : VFacts p prepared (clay p prepared s) :=
  ⟨rfl, rfl, rfl, h.sigScr.symm, h.stkSig, h.nSig, by simp [clay, h.rd]⟩

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (prepared : Bool) (L : Lay) : List Region :=
  [⟨State.addr L.key, publicKeyLen p prepared⟩, ⟨L.MU, 64⟩, ⟨State.addr L.sig, p.sigLen⟩]
abbrev verifyWr (p : Params) (L : Lay) : List Region := [⟨State.addr L.scr, sScr p⟩]

theorem VFacts.sub (F : VFacts p prepared L) : Region.Sub ⟨State.addr L.scr, sScr p⟩ L.SC := by
  show Region.Sub _ ⟨_, L.scrLen⟩
  rw [F.scrLen]; exact sScr_sub p _

theorem VFacts.inKey (F : VFacts p prepared L) (hL : L.Ok) :
    (⟨State.addr L.key, publicKeyLen p prepared⟩ : Region) ∈ L.rd := by
  have := hL.inKey; simp only [Lay.KEY, F.key] at this; exact this

/-- The working space of the function on `μ` is writable. -/
theorem VFacts.wScr (F : VFacts p prepared L) (hL : L.Ok) : ∃ R ∈ L.wr, Within ⟨State.addr L.scr, sScr p⟩ R :=
  ⟨_, hL.inSC, within_base _ (by show sScr p ≤ L.scrLen; rw [F.scrLen, mScr_eq]; simp only [sScr, oE]; omega_using [])⟩

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g m₀ t) (hm : (∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = L.key ∧ t1.gpr .r1 = L.X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = L.sig ∧
      t1.gpr .r3 = L.scr := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fSig) (by simp)
  have e3 := hm (.r3, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega_using [])] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega_using [])] at e2
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega_using [])] at e3
  simp only [Lay.vals, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre (hL : L.Ok) (F : VFacts p prepared L) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : Ctx L g m₀ t)
    (hA : ∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = L.SP)
    (hk : PublicKeyOk p prepared t1.mem (State.addr L.key)) :
    (Verify.verifyE p prepared 52).pre (t1.callEntry.withRegions (verifyRd p prepared L) (verifyWr p L)) := by
  obtain ⟨e0, e1, e2, e3⟩ := verifyRegs_of hL hc hA
  have hsub := F.sub
  generalize hE : t1.callEntry.withRegions (verifyRd p prepared L) (verifyWr p L) = E
  have gr : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ hr]
  have g0 : E.gpr .r0 = L.key := by rw [gr (by decide), e0]
  have g1 : State.addr (E.gpr .r1) = L.MU := by rw [gr (by decide), e1, mu_eq hL]
  have g2 : E.gpr .r2 = L.sig := by rw [gr (by decide), e2]
  have g3 : E.gpr .r3 = L.scr := by rw [gr (by decide), e3]
  have gsp : E.sp = L.SP := by rw [← hE, State.withRegions_sp, State.callEntry_sp, hsp1]
  have grd : E.rd = verifyRd p prepared L := by rw [← hE]; rfl
  have gm : E.mem = t1.mem := by rw [← hE, State.withRegions_mem, State.callEntry_mem]
  have gwr : E.wr = verifyWr p L := by rw [← hE]; rfl
  have xKey := hL.xKey; have kKey := hL.kKey; have nKey := hL.nKey
  simp only [Lay.KEY, F.key] at xKey kKey nKey
  refine verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [g0, g1, g2, g3, gsp, grd, gwr, gm]
  · exact hL.nSP
  · exact xKey.symm.sub_right hsub
  · exact x_sScr hL F.hE (by omega_using [])
  · exact F.xSig.symm.sub_right hsub
  · exact kKey
  · exact k_mu hL
  · exact F.kSig
  · exact hL.kX.sub_right hsub
  · exact nKey
  · rw [gr (by decide), e1]
    have := hL.x32_lt
    rw [x32_toNat hL (by omega_using [])]; omega_using [this]
  · exact F.nSig
  · have := hL.nScr; rw [F.scrLen] at this; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega_using [this]
  · exact hk

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VerifyFn p prepared c) (hL : L.Ok) (F : VFacts p prepared L)
    {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)
    (hk : PublicKeyOk p prepared t.mem (State.addr L.key)) :
    WP isa (.seq (.block (setArgs verifyArgs)) (.call n c)) t fun s' => Fin L g s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (State.addr L.key) p.pkLen)
          (bytesAt t.mem L.MU 64) (bytesAt t.mem (State.addr L.sig) p.sigLen);
        (s'.gpr .r0 = 1 ∧ ∃ b, w b = some true) ∨ (s'.gpr .r0 = 0 ∧ w minBounds ≠ some true)) := by
  refine WP.seq (WP.mono (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx L g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hL hc hA
  have hsp1 : t1.sp = L.SP := hc1.sp
  have hpre := verifyK_pre hL F hc hA hsp1 (by rw [o.mem]; exact hk)
  obtain ⟨RS, hRS, wS⟩ := F.wScr hL
  refine WP.callF hV.ok hpre ?_ ?_ (by rw [hsp1]; have := hV.su; have := hL.nSP; omega_arith)
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
      · exact x_sScr hL F.hE (by omega_using [hd'])
      · rw [hsp1]
        exact hL.sv_disj (r := belowA L.SP (stackUse c)) (.inr (belowA_sub hV.su)) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega_using [])).trans hc1.s7, (hsv 4 (by omega_using [])).trans hc1.sLR⟩, ?_⟩
  have hpost' : Verify.VOut p (t1.callEntry.withRegions (verifyRd p prepared L) (verifyWr p L))
      ((s'.withRegions (verifyRd p prepared L) (verifyWr p L)).gpr .r0) := hpost
  unfold Verify.VOut Verify.vv at hpost'
  simp only [Verify.pkOf, Verify.muOf, Verify.sgOf, Verify.vPk, Verify.vMu, Verify.vSg, State.withRegions_gpr,
    State.withRegions_mem, State.callEntry_mem, State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide),
    e0, e1, e2, o.mem] at hpost'
  rw [show State.addr (L.X32 + 840#32) = L.MU from mu_eq hL] at hpost'
  exact hpost'

end

end VG.Proof.MlDsa.Arm.Message

end

end

/-!
# ML-DSA on ARMv7, `verify_message_cached`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageCachedContract p Arm.abi 52`, `verifyMessageCached n c p`
returns 2 if the context string is longer than 255 bytes; otherwise it
computes `μ` of the formatted message from the 64 bytes at `tr`, which the
contract says are `H(pk, 64)`, and calls the verification function on `μ`
`c`, which gives the result of `ML-DSA.Verify_internal` on the formatted
message (`verifyMessageCached_wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The words on the stack of a state satisfying `CPre` are readable. -/
theorem CPre.args {p : Params} {prepared : Bool} {s : State} (h : CPre p prepared s) {o : Nat} (ho : o + 4 ≤ 16) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
  refine ⟨rArgs s 16, by simp [h.rd], ?_⟩
  simp only [rArgs, stackArgAddr0]
  rw [addr_add (by have := h.spA; omega_using [ho, this])]
  exact Offset.contains_base _ ho (by omega_using [ho])

/-- The entry of `verify_message_cached`, from a state with the registers,
permissions and memory of an entry state. -/
theorem enterC_ok {p : Params} {prepared : Bool} (hp : p ∈ params) {s s1 : State} (h : CPre p prepared s)
    (h8 : (stackArg s 0).toNat < 256) (o1 : Only [.r12] s s1) :
    WP isa (.block (enter 8 p cachedLoads)) s1 fun t => Ctx (clay p prepared s) s1.gpr s1.mem t := by
  have hs1 : ∀ o, o + 4 ≤ 16 → s1.mem.readW (State.addr (s1.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun _ _ => by rw [o1.mem, o1.sp]
  exact enter_ok (clay_ok hp h h8) rfl (nA := 16) (by decide) (Nat.le_refl _) (o1.sp)
    (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .r0) (o1.get .r1) (o1.get .r2) (o1.get .r3)
    (fun o ho => by rw [o1.rd, o1.wr, o1.sp]; exact h.args ho) (by rw [o1.sp]; exact h.spA)
    (by rw [o1.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega_using [])
    (by rw [hs1 8 (by omega_using [])]; exact stackArg_eq s 2) (by decide) (fun j hj => by
      have hj4 : j < 4 := hj
      rcases (by omega_using [hj4] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · exact (hs1 0 (by decide)).trans (stackArg_eq s 0)
      · exact (hs1 12 (by decide)).trans (stackArg_eq s 3)
      · exact (hs1 4 (by decide)).trans (stackArg_eq s 1)
      · exact (hs1 8 (by decide)).trans (stackArg_eq s 2))

/-- Where a cached `tr` is: readable, apart from `scratch` and `STK`. -/
structure TrSide (L : Lay) : Prop where
  inRd : (⟨State.addr L.rnd, 64⟩ : Region) ∈ L.rd
  x : L.SC.Disjoint ⟨State.addr L.rnd, 64⟩
  k : L.STK.Disjoint ⟨State.addr L.rnd, 64⟩
  n : L.rnd.toNat + 64 ≤ 2 ^ 32

/-- The side conditions of `muHash_ok` on the cached `tr`. -/
theorem TrSide.side {L : Lay} (hL : L.Ok) (h : TrSide L) :
    L.rnd.toNat + 64 ≤ 2 ^ 32 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr L.rnd, 64⟩ R) ∧
      Region.Disjoint ⟨State.addr L.rnd, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨State.addr L.rnd, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr L.rnd, 64⟩ := by
  have hst : Region.Sub ⟨L.ST, 200⟩ L.SC := by
    have := hL.sub_sc (e := 0) (k := 200) (by omega_using [])
    simpa only [x0] using this
  exact ⟨h.n, ⟨_, List.mem_append_left _ h.inRd, within_self _⟩, h.x.symm.sub_right hst,
    h.x.symm.sub_right (hL.sub_sc (by omega_using [] : 200 + 640 ≤ 1024)), h.k⟩

/-- The cached `tr`, as `clay` places it. -/
theorem CPre.trSide {p : Params} {prepared : Bool} {s : State} (h : CPre p prepared s) :
    TrSide (clay p prepared s) :=
  ⟨by simp [clay, h.rd], h.scrTr, h.stkTr, h.nTr⟩

theorem Ctx.trV {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) :
    (Arg.slot fRnd).val t = L.rnd := by
  rw [hc.slotV hL (f := fRnd) (j := 5) rfl (by omega_using [])]; rfl

/-- `muHash` on the cached `tr`. -/
theorem muHashC_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t)
    (hT : TrSide L) :
    WP isa (muHash (.slot fRnd)) t fun t' => Ctx L g m₀ t' ∧
      bytesAt t'.mem L.MU 64 = Spec.MlDsa.H (bytesAt m₀ (State.addr L.rnd) 64 ++ hdrBytes L ++
        bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m₀ (State.addr L.msg) L.len.toNat) 64 := by
  obtain ⟨a, b, c, d, e⟩ := hT.side hL
  refine WP.mono (muHash_ok hL hc (tr := .slot fRnd) (trp := L.rnd) (by decide) rfl
    (fun t' hc' => hc'.trV hL) a b c d e) fun t' ⟨hc', hμ⟩ => ⟨hc', ?_⟩
  rw [hμ, hc.bytesAt_eq hT.x hT.k (by decide)]

theorem verifyMessageCached_wp {p : Params} {prepared : Bool} {n : String} {c : Prog isa}
    (hV : VerifyFn p prepared c) (hp : p ∈ params) {s : State} (h : CPre p prepared s) :
    WP isa (verifyMessageCached n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageCachedContract p Arm.abi 52).post s s' := by
  unfold verifyMessageCached top
  refine WP.seq (WP.mono (chk_ok (h.args (by omega_using []))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := clay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono (enterC_ok hp h h8 o1) fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (muHashC_ok hL hc h.trSide) fun t₂ ⟨hc₂, hμ⟩ => ?_))
    have hm₀ : s1.mem = s.mem := o1.mem
    have hkb : bytesAt t₂.mem (State.addr (s.gpr .r0)) (publicKeyLen p prepared) =
        bytesAt s.mem (State.addr (s.gpr .r0)) (publicKeyLen p prepared) :=
      (hc₂.bytesAt_eq (p := State.addr (clay p prepared s).key) (n := publicKeyLen p prepared) hL.xKey hL.kKey
        (by have := h.nPk; omega_using [this])).trans (by rw [hm₀]; rfl)
    have hk : PublicKeyOk p prepared t₂.mem (State.addr (clay p prepared s).key) := fun e => by
      subst e
      exact PreparedKey.preparedPublicKey_of_bytes hkb (h.key rfl)
    refine WP.mono (verifyCall_ok hV hL h.vfacts hc₂ hk) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), by rw [hsp]; rfl⟩, ?_⟩
    sig_post [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have ek : bytesAt t₂.mem (State.addr (s.gpr .r0)) p.pkLen = bytesAt s.mem (State.addr (s.gpr .r0)) p.pkLen :=
      (hc₂.bytesAt_eq (p := State.addr (clay p prepared s).key) (n := p.pkLen)
        (hL.xKey.sub_right (Region.sub_prefix (pkLen_le prepared)))
        (hL.kKey.sub_right (Region.sub_prefix (pkLen_le prepared)))
        (by have := h.nPk; have := pkLen_le (p := p) prepared; omega_arith)).trans (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (State.addr (stackArg s 1)) p.sigLen =
        bytesAt s.mem (State.addr (stackArg s 1)) p.sigLen :=
      (hc₂.bytesAt_eq (p := State.addr (clay p prepared s).sig) (n := p.sigLen) h.sigScr.symm h.stkSig
        (by have := h.nSig; omega_using [this])).trans (by rw [hm₀]; rfl)
    have etr : bytesAt s1.mem (State.addr (clay p prepared s).rnd) 64 = H (bytesAt s.mem (State.addr (s.gpr .r0)) p.pkLen) 64 := by
      rw [hm₀]; exact h.tr
    have hμ' := hμ
    rw [etr, hm₀] at hμ'
    rw [show (clay p prepared s).key = s.gpr .r0 from rfl, show (clay p prepared s).sig = stackArg s 1 from rfl] at hq
    rw [ek, es, hμ'] at hq
    rw [Proof.MlKem.Arm.setWidth_append32, hx0]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movImm (by decide) fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h12 : r ∉ [Reg.r12] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.gpr r h0, o1.gpr r h12]
    · sig_post [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_using [h8]), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message
