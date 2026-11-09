module

public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values

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
  rw [addr_add (by have := h.spA; omega)]
  exact Offset.contains_base _ ho (by omega)

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
    (by rw [o1.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega)
    (by rw [hs1 8 (by omega)]; exact stackArg_eq s 2) (by decide) (fun j hj => by
      have hj4 : j < 4 := hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
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
    have := hL.sub_sc (e := 0) (k := 200) (by omega)
    simpa only [x0] using this
  exact ⟨h.n, ⟨_, List.mem_append_left _ h.inRd, within_self _⟩, h.x.symm.sub_right hst,
    h.x.symm.sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)), h.k⟩

/-- The cached `tr`, as `clay` places it. -/
theorem CPre.trSide {p : Params} {prepared : Bool} {s : State} (h : CPre p prepared s) :
    TrSide (clay p prepared s) :=
  ⟨by simp [clay, h.rd], h.scrTr, h.stkTr, h.nTr⟩

theorem Ctx.trV {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) :
    (Arg.slot fRnd).val t = L.rnd := by
  rw [hc.slotV hL (f := fRnd) (j := 5) rfl (by omega)]; rfl

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
  refine WP.seq (WP.mono (chk_ok (h.args (by omega))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := clay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono (enterC_ok hp h h8 o1) fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (muHashC_ok hL hc h.trSide) fun t₂ ⟨hc₂, hμ⟩ => ?_))
    have hm₀ : s1.mem = s.mem := o1.mem
    have hkb : bytesAt t₂.mem (State.addr (s.gpr .r0)) (publicKeyLen p prepared) =
        bytesAt s.mem (State.addr (s.gpr .r0)) (publicKeyLen p prepared) :=
      (hc₂.bytesAt_eq (p := State.addr (clay p prepared s).key) (n := publicKeyLen p prepared) hL.xKey hL.kKey
        (by have := h.nPk; omega)).trans (by rw [hm₀]; rfl)
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
        (by have := h.nPk; have := pkLen_le (p := p) prepared; omega)).trans (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (State.addr (stackArg s 1)) p.sigLen =
        bytesAt s.mem (State.addr (stackArg s 1)) p.sigLen :=
      (hc₂.bytesAt_eq (p := State.addr (clay p prepared s).sig) (n := p.sigLen) h.sigScr.symm h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
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
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message
