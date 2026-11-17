module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Hash
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! ### `MlDsa.X86_64.Message.VerifyCorrect`, which only this module used -/

section

/-!
# ML-DSA on x86-64, `verify_message_cached`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageCachedContract p X86_64.abi 112`, `verifyMessageCached n c p`
returns 2 if the context string is longer than 255 bytes; otherwise it
computes `μ` of the formatted message from the `tr = H(pk, 64)` it is given,
and calls the verification function on `μ` `c`, which gives
`ML-DSA.Verify_internal` of the formatted message (`verifyMessage_wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `scratch` to `r11`, `tr` to `r10`, 0 to `rax`. -/
theorem verifyMov_ok {p : Params} {prep : Bool} {s s1 : State} (h : VPre p prep s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r11 (.mem (stk 8)), .mov .r10 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r11 = stackArg s 0 ∧ s2.gpr .r10 = stackArg s 1 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧
        s2.mxcsr = s1.mxcsr) ∧ Keep [.r10, .r11, .rax] s1 s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨vArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← add_add, ← stackArgAddr0]
    exact Offset.contains_base _ hd (by omega_using [hd])
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  have h8 := hin 0 (by omega_using [])
  have h16 := hin 8 (by omega_using [])
  simp only [Nat.add_zero, Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl, rfl⟩

/-- The arguments of `verifyRegs`, pushed. -/
theorem verifyRegs_vals {p : Params} {prep : Bool} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r)
    (h11 : s2.gpr .r11 = stackArg s 0) (h10 : s2.gpr .r10 = stackArg s 1) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (verifyRegs[j]'(by simp [verifyRegs]; omega_using [hj])) =
      (vlay p prep s).vals[j]'(by simp [Lay.vals]; omega_using [hj]) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega_using [hj]
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [verifyRegs, Lay.vals, vlay, List.getElem_cons_zero, List.getElem_cons_succ, h10, h11, hax] <;>
    exact hk _ (by decide)

/-- The facts `muHash` needs of `tr`, the slot of `rnd`. -/
theorem trFacts {p : Params} {prep : Bool} {L : Lay} (hL : L.Ok) (F : VFacts p prep L) :
    (∃ R ∈ L.rd ++ L.FR :: L.wr, Within ⟨L.rnd, 64⟩ R) ∧ Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.rnd, 64⟩ ⟨L.KS, 640⟩ ∧ Region.Disjoint ⟨L.B, 40⟩ ⟨L.rnd, 64⟩ :=
  ⟨⟨_, List.mem_append_left _ F.inTr, within_self _⟩,
    by have := hL.x_r F.xTr (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
    (hL.x_r F.xTr (e := 200) (k := 640) (by decide)).symm,
    F.kTr.sub_left (Region.sub_prefix (by decide))⟩

/-- The postcondition of `verifyMessageCachedContract` and `preparedVerifyMessageContract`, spelled out. -/
def VPost (p : Params) (s s' : State) : Prop :=
  match formatMessage (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) with
  | none => (s'.gpr .rax).setWidth 32 = 2
  | some M' =>
    let v := fun b => verifyInternal p b (bytesAt s.mem (s.gpr .rdi) p.pkLen) M' (bytesAt s.mem (s.gpr .r9) p.sigLen)
    ((s'.gpr .rax).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨ ((s'.gpr .rax).setWidth 32 = 0 ∧ v minBounds ≠ some true)

theorem verifyMessage_wp {p : Params} {prep : Bool} {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) {s : State} (h : VPre p prep s) :
    WP isa (verifyMessageCached n c p (flagOf prep)) s fun s' => abiPreserved s s' ∧ VPost p s s' := by
  have hK := keyLenV_ge hp prep
  unfold verifyMessageCached top
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (verifyMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h11, h10, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := vlay_ok (prep := prep) hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (vlay p prep s).B + BitVec.ofNat 64 112 := by
      rw [hg2 _ (by decide), vlay_B]
    have hn : 8 * verifyRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [verifyRegs, List.length_cons, List.length_nil]; omega_using [this]
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (verifyRegs_vals hg2 h11 h10 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have F : VFacts p prep (vlay p prep s) := VOk.facts ⟨s, h, h8, rfl, rfl⟩
    obtain ⟨hin, dS, dK, kD⟩ := trFacts hL F
    refine WP.seq (WP.mono (muHash_ok hL rfl hc (tr := .slot fRnd) (by decide)
      (fun t' hc' => by rw [hc'.slot, fRnd, hc'.pRnd]) hin dS dK kD)
      fun t₂ ⟨hc₂, _, hμ⟩ => ?_)
    refine WP.mono (verifyCall_ok hV hp hL F hc₂ (by rw [hm2]; exact h.prepK)) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₂.rsp, ← htsp, hc.rsp], by rw [hwr', hc₂.wr, ← htw, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₂.rsp, Lay.SP, add_add, show 40 + 8 * verifyRegs.length = 112 from rfl, vlay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hcs' r hr, hc₂.cs r hr hr', hg2 r (cs_tmp r hr)]
      · have eR : rRet s = ⟨(vlay p prep s).B + BitVec.ofNat 64 112, 8⟩ := by rw [vlay_B]
        have dB : ∀ k, k ≤ 112 → (rRet s).Disjoint ⟨(vlay p prep s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega_using [])
        rw [popped_mem, hf'.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (scrV_sub p _)
            · exact dB 40 (by decide)) (by decide),
          hc₂.frame.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (vlay_X p prep s).sub
            · exact dB 112 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₂.mx, hx2, hx1]
    · unfold VPost
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr]
      have ek : bytesAt t₂.mem (vlay p prep s).key p.pkLen = bytesAt s.mem (s.gpr .rdi) p.pkLen := by
        rw [hc₂.bytesAt_eq (p := (vlay p prep s).key) (n := p.pkLen) (hL.xKey.sub_right (Region.sub_prefix hK.2.2))
          (hL.kKey.sub_right (Region.sub_prefix hK.2.2)) (by have := h.nPk; omega_using [hK]), hm₀]; rfl
      have es : bytesAt t₂.mem (vlay p prep s).sig p.sigLen = bytesAt s.mem (s.gpr .r9) p.sigLen := by
        rw [hc₂.bytesAt_eq (p := (vlay p prep s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (vlay_X p prep s).sub) h.stkSig
          (by have := h.nSig; omega_using [this]), hm₀]; rfl
      have etr : bytesAt t.mem (vlay p prep s).rnd 64 = pkTr (bytesAt s.mem (s.gpr .rdi) p.pkLen) := by
        rw [hc.bytesAt_eq F.xTr F.kTr (by decide), hm₀]; exact h.tr
      have hμ' := hμ
      rw [etr, hm₀] at hμ'
      simp only [pkTr] at hμ'
      simp only [Verify.res] at hq
      rw [ek, es, hμ'] at hq
      simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · unfold VPost
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega_using [h8])]
      rfl

theorem vPost_of {p : Params} {s s' : State} (h : VPost p s s') :
    (verifyMessageCachedContract p X86_64.abi 112).post s s' := by
  sig_post [verifyMessageCachedContract, verifyMessageCachedSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop]
  exact h

theorem vPostP_of {p : Params} {s s' : State} (h : VPost p s s') :
    (preparedVerifyMessageContract p X86_64.abi 112).post s s' := by
  sig_post [preparedVerifyMessageContract, preparedVerifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop]
  exact h

end VG.Proof.MlDsa.X86_64.Message

end

end

/-! ### `MlDsa.X86_64.Message.VerifyCT`, which only this module used -/

section

/-!
# ML-DSA on x86-64, `verify_message_cached`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the moves and the frame depend only on the pointers
and the lengths; the hashing leaks only the layout (`muHash_tr`); and the
call of the verification function on `μ` leaks only
`pk`, `μ` and `sig`, which are the same in both runs (`verifyCall_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep RelCT.postDep)
open VG.Proof.MlDsa.X86_64.Verify (verifyK)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {prep : Bool}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m L.key p.pkLen ++ bytesAt m L.msg L.len.toNat ++ bytesAt m L.ctx L.ctxLen.toNat ++
    bytesAt m L.sig p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ L.key p.pkLen = bytesAt m₂ L.key p.pkLen ∧
      bytesAt m₁ L.msg L.len.toNat = bytesAt m₂ L.msg L.len.toNat ∧
      bytesAt m₁ L.ctx L.ctxLen.toNat = bytesAt m₂ L.ctx L.ctxLen.toNat ∧
      bytesAt m₁ L.sig p.sigLen = bytesAt m₂ L.sig p.sigLen := by
  have e := leakBytes_inj h
  obtain ⟨e, e₄⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  obtain ⟨e₁, e₂⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
  exact ⟨e₁, e₂, e₃, e₄⟩

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m L.key p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m L.ctx L.ctxLen.toNat ++ bytesAt m L.msg L.len.toNat) 64

/-- Two runs of the call of the verification function on `μ`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m t => VOk p prep L m ∧ VMuOk p L m t) (callA n c (verifyArgs p prep))
      fun _ _ => True := by
  refine call_tr (verifyArgs_ok hp) hV.ok hV.ct (verifyRd p) (verifyWr p)
    (fun L g mx m₀ t t1 hL hc hφ hm => verifyK_pre hp hL hφ.1.facts hc hφ.1.prep hm)
    (fun L g₁ g₂ mx₁ mx₂ m₁ m₂ a b a1 b1 hL hi c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_)
    (fun L g mx m₀ t hL hc hφ => ?_)
  · have F := φ₁.1.facts
    obtain ⟨x1, x2, x3, x4, x5⟩ := verifyRegsL F.e c₁ f₁
    obtain ⟨y1, y2, y3, y4, y5⟩ := verifyRegsL F.e c₂ f₂
    have hkl : p.pkLen ≤ L.keyLen := by rw [F.key]; exact (keyLenV_ge hp prep).2.2
    have kK : L.STK.Disjoint ⟨L.key, p.pkLen⟩ := hL.kKey.sub_right (Region.sub_prefix hkl)
    have xK : L.XS.Disjoint ⟨L.key, p.pkLen⟩ := hL.xKey.sub_right (Region.sub_prefix hkl)
    simp only [verifyK, Verify.vPk, Verify.vMu, Verify.vSig, State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_rsp, x1, x2, x3, x4, x5, y1, y2, y3, y4, y5, f₁.2.gpr (by decide : Reg.rsp ∉ argRegs),
      f₂.2.gpr (by decide : Reg.rsp ∉ argRegs), c₁.rsp, c₂.rsp, true_and, and_true]
    have hk := hL.nKey
    have ce : ∀ {g mx m₀} {a a1 : State} {q : Addr} {k : Nat}, Ctx L g mx m₀ a → Moved (verifyArgs p prep) a a1 →
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 32, 8⟩ ⟨q, k⟩ → k ≤ 2 ^ 64 →
        bytesAt a1.callEntry.mem q k = bytesAt a.mem q k := fun c f hd hn => by
      rw [(c.regs f.2.2.1 f.2.2.2 f.1.2.1 f.1.2.2 fun r hr => f.2.gpr (argRegs_cs r hr)).ce_bytesAt hd hn, f.1.2.1]
    have dk := hL.stk_r kK (d := 32) (n := 8) (by decide)
    have dμ := hL.stk_x (d := 32) (n := 8) (e := 840) (k := 64) (by decide) (by decide)
    have ds := hL.stk_r F.kSig (d := 32) (n := 8) (by decide)
    have hsx : L.XS.Disjoint ⟨L.sig, p.sigLen⟩ := by
      have hX : Within L.XS ⟨L.scr, mScrLen p⟩ := ⟨L.E, rfl, by rw [mScr_eq, F.e]⟩
      exact F.sigScr.symm.sub_left hX.sub
    have ns := F.nSig
    obtain ⟨ek, -, ec, es⟩ := verifyI_eq hi
    obtain ⟨-, em, -, -⟩ := verifyI_eq hi
    refine ⟨?_, ?_, ?_⟩
    · rw [ce c₁ f₁ dk (by omega_using [hkl, hk]), ce c₂ f₂ dk (by omega_using [hkl, hk]), c₁.bytesAt_eq xK kK (by omega_using [hkl, hk]),
        c₂.bytesAt_eq xK kK (by omega_using [hkl, hk]), ek]
    · rw [ce c₁ f₁ dμ (by decide), ce c₂ f₂ dμ (by decide), φ₁.2, φ₂.2, ek, ec, em]
    · rw [ce c₁ f₁ ds (by omega_using [ns]), ce c₂ f₂ ds (by omega_using [ns]), c₁.bytesAt_eq hsx F.kSig (by omega_using [ns]),
        c₂.bytesAt_eq hsx F.kSig (by omega_using [ns]), es]
  · have F := hφ.1.facts
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
      · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
      · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact F.inScr

/-- The public data of the contract, spelled out. -/
structure VPub (p : Params) (s₁ s₂ : State) : Prop where
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  leak : leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) p.pkLen ++ bytesAt s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx).toNat ++
      bytesAt s₁.mem (s₁.gpr .rcx) (s₁.gpr .r8).toNat ++ bytesAt s₁.mem (s₁.gpr .r9) p.sigLen) =
    leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) p.pkLen ++ bytesAt s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx).toNat ++
      bytesAt s₂.mem (s₂.gpr .rcx) (s₂.gpr .r8).toNat ++ bytesAt s₂.mem (s₂.gpr .r9) p.sigLen)
  rdi : s₁.gpr .rdi = s₂.gpr .rdi
  rsi : s₁.gpr .rsi = s₂.gpr .rsi
  rdx : s₁.gpr .rdx = s₂.gpr .rdx
  rcx : s₁.gpr .rcx = s₂.gpr .rcx
  r8 : s₁.gpr .r8 = s₂.gpr .r8
  r9 : s₁.gpr .r9 = s₂.gpr .r9
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1

theorem vPub_of {s₁ s₂ : State} (h : (verifyMessageCachedContract p X86_64.abi 112).pub s₁ s₂) :
    VPub p s₁ s₂ := by
  sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

theorem vPubP_of {s₁ s₂ : State} (h : (preparedVerifyMessageContract p X86_64.abi 112).pub s₁ s₂) :
    VPub p s₁ s₂ := by
  sig_pub [preparedVerifyMessageContract, preparedVerifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
    List.range.loop] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem vlay_eq {s₁ s₂ : State} (h₁ : VPre p prep s₁) (h₂ : VPre p prep s₂) (h : VPub p s₁ s₂) :
    vlay p prep s₁ = vlay p prep s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]; simp only [vPk, rMsg, rCtx, vSigR, vTr, vArgs, stackArgAddr, h.rdi, h.rsi, h.rdx, h.rcx,
      h.r8, h.r9, h.rsp, h.a1]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [vScr, h.a0]
  simp only [vlay, h.rsp, h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.a0, h.a1, e1, e2]

/-- The body of the frame. -/
theorem verifyBody_tr {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    RelCT isa (Two (verifyI p) fun L m _ => VOk p prep L m)
      (.seq (muHash p (.slot fRnd)) (callA n c (verifyArgs p prep))) fun _ _ => True := by
  have hE := oE_lt hp
  have mh := muHash_tr_of (I := verifyI p) (Φ := fun L m _ => VOk p prep L m) (G := VFacts p prep) hE
    (fun _ _ _ h => ⟨h.facts.e, h.facts⟩) (tr := .slot fRnd) (by decide) (fun L => L.rnd)
    (fun L g mx m t hc _ => by rw [hc.slot, fRnd, hc.pRnd]) fun L hL F => trFacts hL F
  have mh' := two_wp (I := verifyI p) (Φ := fun L m _ => VOk p prep L m)
    (Ψ := fun L m t => VOk p prep L m ∧ VMuOk p L m t) mh fun L g mx m₀ t hL hc hφ => by
      have F := hφ.facts
      obtain ⟨hin, dS, dK, kD⟩ := trFacts hL F
      refine WP.mono (muHash_ok hL F.e hc (tr := .slot fRnd) (by decide)
        (fun t' hc' => by rw [hc'.slot, fRnd, hc'.pRnd]) hin dS dK kD) fun t' ⟨hc', _, hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold VMuOk
      rw [hμ, hc.bytesAt_eq F.xTr F.kTr (by decide), hφ.tr, pkTr]
  exact mh'.seq (verifyCall_tr hV hp)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev VP2 (p : Params) (prep : Bool) (x y : State) : Prop :=
  VPre p prep x ∧ VPre p prep y ∧ VPub p x y

/-- After the moves before the push. -/
abbrev VMov (x x2 : State) : Prop :=
  (x.gpr .r8).toNat < 256 ∧ ((x2.gpr .r11 = stackArg x 0 ∧ x2.gpr .r10 = stackArg x 1 ∧ x2.gpr .rax = 0 ∧
    x2.mem = x.mem ∧ x2.mxcsr = x.mxcsr) ∧ (∀ r, r ∉ [Reg.r10, .r11, .rax] → x2.gpr r = x.gpr r) ∧
    x2.rd = x.rd ∧ x2.wr = x.wr)

theorem verifyMessage_ct {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    ConstantTime isa (VPre p prep) (VPub p) (verifyMessageCached n c p (flagOf prep)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => VPre p prep s₁ ∧ VPre p prep s₂ ∧ VPub p s₁ s₂) =
      Ghost (VP2 p prep) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessageCached top
  -- `cmp r8, 256`.
  have hcmp := ghost_step (P := VP2 p prep) (A := fun x a => a = x) (B := ACmp) (c := .block [.alu .cmp .r8 (.imm 256)])
    (block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨x, y, hxy, e₁, e₂⟩ => by subst e₁ e₂; exact hxy.2.2.rsp)
    fun x y a b _ e₁ e₂ => by subst e₁ e₂; exact ⟨cmp_ok _, cmp_ok _⟩
  refine RelCT.seq hcmp (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2.2.2.2.2, f₂.2.2.2.2.2, hxy.2.2.r8]) ?_ ?_)
  · -- `ctx_len < 256`.
    have hmov := ghost_step (P := VP2 p prep) (A := fun x a => ACmp x a ∧ (x.gpr .r8).toNat < 256) (B := VMov)
      (c := .block [.mov .r11 (.mem (stk 8)), .mov .r10 (.mem (stk 16)), .mov32 .rax (.imm 0)])
      (block_rsp_tr (fun i hi => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact ⟨fun s₁ s₂ h => by simp [addrs, srcAddrs, State.ea, stk, h], rfl⟩
          · exact spOnly_nomem (fun _ => rfl) rfl)
        fun a b ⟨x, y, hxy, f₁, f₂⟩ => by rw [f₁.1.1, f₂.1.1]; exact hxy.2.2.rsp)
      fun x y a b hxy f₁ f₂ => by
        have mv : ∀ {x a : State}, VPre p prep x → ACmp x a →
            (x.gpr .r8).toNat < 256 →
            WP isa (.block [.mov .r11 (.mem (stk 8)), .mov .r10 (.mem (stk 16)), .mov32 .rax (.imm 0)]) a
              (VMov x) := fun hx f h8 =>
          WP.mono (verifyMov_ok hx f.1 f.2.1 f.2.2.1) fun x2 ⟨h, k⟩ =>
            ⟨h8, ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans f.2.2.2.2.1⟩,
              fun r hr => (k.gpr hr).trans (by rw [f.1]), k.2.1.trans f.2.2.1, k.2.2.trans f.2.2.2.1⟩
        exact ⟨mv hxy.1 f₁.1 f₁.2, mv hxy.2.1 f₂.1 f₂.2⟩
    refine RelCT.seq (RelCT.mono hmov (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, ?_⟩, ⟨f₂, ?_⟩⟩)
      fun _ _ h => h) ?_
    · rw [f₁.2.2.2.2.2] at hc; simpa using hc
    · rw [f₁.2.2.2.2.2, hxy.2.2.r8, ← f₂.2.2.2.2.2] at hc
      rw [f₂.2.2.2.2.2] at hc; simpa using hc
    refine RelCT.frame (R := fun _ _ => True) (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
      rw [f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide)]; exact hxy.2.2.rsp) ?_
    -- The frame's body, from the push.
    let A : State → State → Prop := fun x a => ∃ s₁, VMov x s₁ ∧ a = pushed verifyRegs s₁
    let B : State → State → Prop := fun x t => (x.gpr .r8).toNat < 256 ∧ Ctx (vlay p prep x) x.gpr x.mxcsr x.mem t
    have hdr := ghost_step (P := VP2 p prep) (A := A) (B := B) (c := .block setHdr)
      (block_rsp_tr (fun i hi => by
          simp only [setHdr, List.mem_singleton] at hi; subst hi
          exact ⟨fun s₁ s₂ h => by simp [addrs, State.ea, stk, h], rfl⟩)
        fun a b ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩ => by
          subst e₁ e₂
          rw [pushed_rsp, pushed_rsp, f₁.2.2.1 _ (by decide), f₂.2.2.1 _ (by decide), hxy.2.2.rsp])
      fun x y a b hxy fa fb => by
        have en : ∀ {x a : State}, VPre p prep x → A x a →
            WP isa (.block setHdr) a (B x) := fun hx ⟨s₁, f, e⟩ => by
          subst e
          have h := hx
          have hL := vlay_ok hp h f.1
          refine WP.mono (entry_ok hL rfl (by decide) (by rw [f.2.2.1 _ (by decide), vlay_B])
            (f.2.2.2.1.trans rfl) (f.2.2.2.2.trans rfl) (verifyRegs_vals f.2.2.1 f.2.1.1 f.2.1.2.1 f.2.1.2.2.1)
            (f.2.2.1 _ (by decide))) fun t ⟨hc, _, _⟩ =>
            ⟨f.1, hc.congr (fun r hr _ => f.2.2.1 r (cs_tmp r hr)) f.2.1.2.2.2.2 f.2.1.2.2.2.1⟩
        exact ⟨en hxy.1 fa, en hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hdr (fun a b ⟨s₁, s₂, ⟨x, y, hxy, f₁, f₂⟩, e₁, e₂⟩ =>
      ⟨x, y, hxy, ⟨s₁, f₁, e₁⟩, ⟨s₂, f₂, e₂⟩⟩) fun a b ⟨x, y, hxy, ⟨h8x, ca⟩, ⟨h8y, cb⟩⟩ => ?_)
      (verifyBody_tr hV hp)
    have hx := hxy.1
    have hy := hxy.2.1
    have hpub := hxy.2.2
    have e := vlay_eq hx hy hpub
    refine ⟨vlay p prep x, x.gpr, y.gpr, x.mxcsr, y.mxcsr, x.mem, y.mem, vlay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, rfl⟩, ⟨y, hy, h8y, e.symm, rfl⟩⟩
    have lk := hpub.leak
    rw [← hpub.rdi, ← hpub.rsi, ← hpub.rdx, ← hpub.rcx, ← hpub.r8, ← hpub.r9] at lk
    exact lk
  · exact block_rsp_tr (fun i hi => by
        simp only [List.mem_singleton] at hi; subst hi; exact spOnly_nomem (fun _ => rfl) rfl)
      fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, _⟩ => by rw [f₁.1, f₂.1]; exact hxy.2.2.rsp

end

end VG.Proof.MlDsa.X86_64.Message

end

end


/-!
# ML-DSA on x86-64, `verify_message_cached`: verified

Untrusted: everything here is checked by Lean. `verifyMessageCached n c p`,
for any verification function on `μ` `c` that `verify_message_cached` can
call (`VerifyFn`), is verified against
`verifyMessageCachedContract p X86_64.abi 112`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The memory of a state satisfying the precondition: `pk` (zeros) at
`0x1000`, `tr = H(pk, 64)` at `0x8000`, and the stack arguments `scratch =
0x10000` and `tr = 0x8000` at `0x80008` and `0x80010`. -/
def stkMem : Mem := fun a => if a = 0x8000A then 0x01 else if a = 0x80011 then 0x80 else 0

def satMem (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then
    (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).getD (a.toNat - 0x8000) 0
  else stkMem a

theorem satMem_stk (p : Params) {a : Addr} (ha : 0x8040 ≤ a.toNat) (hb : a.toNat + 8 < 2 ^ 64) :
    (satMem p).readW a 64 = stkMem.readW a 64 :=
  Mem.readW_congr fun i hi => by
    have he : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi] : i < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega_using [hb, hi])
    simp only [satMem, he]
    split
    · omega
    · rfl

theorem satMem_key {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (satMem p) 0x1000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen := by
  apply Proof.MlKem.bytesAt_congr
  intro i hi
  have he : ((0x1000 : Addr) + BitVec.ofNat 64 i).toNat = 0x1000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega_using [hp, hi]
  simp only [satMem, he]
  split
  · omega
  simp only [stkMem]
  repeat' split
  all_goals first
    | rfl
    | (rename_i e _; have := congrArg BitVec.toNat e; simp only [he, BitVec.reduceToNat] at this; omega)
    | (rename_i e; have := congrArg BitVec.toNat e; simp only [he, BitVec.reduceToNat] at this; omega_using [hp, hi, this])

theorem satMem_digest {p : Params} (hp : p.pkLen < 0x7000) :
    bytesAt (satMem p) 0x8000 64 = pkTr (bytesAt (satMem p) 0x1000 p.pkLen) := by
  rw [satMem_key hp]
  have hl : (pkTr (bytesAt (fun _ => 0) 0x1000 p.pkLen)).length = 64 := Proof.MlDsa.Verify.H_length _ _
  apply Proof.MlKem.bytesAt_eq hl
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
    omega_using [hi]
  simp only [satMem, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega_using [hi], true_and, ite_true,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega_using [hl, hi]), Option.getD_some]

/-- A state satisfying the precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem p
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, p.sigLen⟩, ⟨0x8000, 64⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x10000, mScrLen p⟩]

theorem verifyMessage_sat {p : Params} (hp : p ∈ params) :
    ∃ s, (verifyMessageCachedContract p X86_64.abi 112).pre s := by
  refine ⟨verifySat p, ?_⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  have a0 : stackArg (verifySat p) 0 = 0x10000 := by
    rw [stackArg, show stackArgAddr (verifySat p) 0 = 0x80008 from rfl]
    exact (satMem_stk p (by decide) (by decide)).trans (by decide)
  have a1 : stackArg (verifySat p) 1 = 0x8000 := by
    rw [stackArg, show stackArgAddr (verifySat p) 1 = 0x80010 from rfl]
    exact (satMem_stk p (by decide) (by decide)).trans (by decide)
  rcases hp with rfl | rfl | rfl <;>
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, X86_64.abi, X86_64.argRegs,
      List.range, List.range.loop] <;> sig_and_intros <;> (try simp only [a0, a1])
  all_goals first
    | exact satMem_digest (by decide)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

theorem verifyMessage_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) :
    Verified X86_64.target (verifyMessageCached n c p 0) (verifyMessageCachedContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp (prep := false) hV hp (vPre_of h)
      ⟨t, s', he, ha, vPost_of hq⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => verifyMessage_ct (prep := false) hV hp s₁ s₂ t₁ t₂ s₁' s₂'
      (vPre_of h₁) (vPre_of h₂) (vPub_of hpub) e₁ e₂,
    verifyMessage_sat hp⟩

/-- `verify_message_prepared`, given a state satisfying its precondition (which holds a prepared key). -/
theorem verifyMessagePrepared_verified {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c)
    (hp : p ∈ params) (hsat : ∃ s, (preparedVerifyMessageContract p X86_64.abi 112).pre s) :
    Verified X86_64.target (verifyMessageCached n c p 1) (preparedVerifyMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verifyMessage_wp (prep := true) hV hp (vPreP_of h)
      ⟨t, s', he, ha, vPostP_of hq⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => verifyMessage_ct (prep := true) hV hp s₁ s₂ t₁ t₂ s₁' s₂'
      (vPreP_of h₁) (vPreP_of h₂) (vPubP_of hpub) e₁ e₂,
    hsat⟩

end VG.Proof.MlDsa.X86_64.Message
