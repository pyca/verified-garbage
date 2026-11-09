module
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall

import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCorrect
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.Arm.Common

import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values

/-!
# ML-DSA on ARMv7, `verify_message_cached`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which include `pk`, the
message, the context string and the signature (`verifyI`), leak the same:
the branch on `ctx_len`, the entry and the exit depend only on the pointers
and the lengths; the hashing of `μ` from the cached `tr` leaks only the
layout (`muHash_tr_of`); and the call of the verification function on `μ`
leaks only `pk`, `μ` and `sig`, which are the same in both runs, since the
contract says `tr` is `H(pk, 64)` (`verifyCall_tr`, `cachedBody_tr`,
`verifyMessageCached_ct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {prepared : Bool}

/-- The inputs of a run, with the memory `m`. -/
abbrev vIn (p : Params) (L : Lay) (m : Mem) : List Byte :=
  bytesAt m (State.addr L.key) p.pkLen ++ bytesAt m (State.addr L.msg) L.len.toNat ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.sig) p.sigLen

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def verifyI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop := leakBytes (vIn p L m₁) = leakBytes (vIn p L m₂)

theorem verifyI_eq {L : Lay} {m₁ m₂ : Mem} (h : verifyI p L m₁ m₂) :
    bytesAt m₁ (State.addr L.key) p.pkLen = bytesAt m₂ (State.addr L.key) p.pkLen ∧
      bytesAt m₁ (State.addr L.msg) L.len.toNat = bytesAt m₂ (State.addr L.msg) L.len.toNat ∧
      bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat = bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat ∧
      bytesAt m₁ (State.addr L.sig) p.sigLen = bytesAt m₂ (State.addr L.sig) p.sigLen :=
  leak4 (by simp only [Proof.MlKem.bytesAt_length]) (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length]) h

/-- `μ` at `X + 840`. -/
def VMuOk (p : Params) (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (H (bytesAt m (State.addr L.key) p.pkLen) 64 ++ hdrBytes L ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64

/-- Two runs of the call of the verification function on `μ`, from any
layouts with the facts `VFacts` and `μ` at `X + 840`. -/
theorem verifyCall_tr {n : String} {c : Prog isa} (hV : VerifyFn p prepared c) {Φ : Lay → Mem → State → Prop}
    (hΦ : ∀ L m t, Φ L m t → VFacts p prepared L ∧ VMuOk p L m t ∧ PublicKeyOk p prepared m (State.addr L.key)) :
    RelCT isa (Two (verifyI p) Φ) (.seq (.block (setArgs verifyArgs)) (.call n c)) fun _ _ => True := by
  refine RelCT.seq (setArgs_two (by decide)) ?_
  refine RelCT.mono (P := fun a1 b1 => ∃ L : Lay, ∃ x y, (∃ g₁ g₂ m₁ m₂, L.Ok ∧ verifyI p L m₁ m₂ ∧
      Ctx L g₁ m₁ x ∧ Ctx L g₂ m₂ y ∧ Φ L m₁ x ∧ Φ L m₂ y) ∧
      Moved verifyArgs x a1 ∧ Moved verifyArgs y b1)
    (RelCT.exists_ fun L => RelCT.call hV.ok hV.ct (verifyRd p prepared L) (verifyWr p L) fun a1 b1 h => ?_)
    (fun a1 b1 ⟨x, y, ⟨L, hp'⟩, f₁, f₂⟩ => ⟨L, x, y, hp', f₁, f₂⟩) fun _ _ h => h
  obtain ⟨x, y, ⟨g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, φ₁, φ₂⟩, f₁, f₂⟩ := h
  obtain ⟨F, μ₁, k₁⟩ := hΦ _ _ _ φ₁
  obtain ⟨-, μ₂, k₂⟩ := hΦ _ _ _ φ₂
  have xKey := hL.xKey; have kKey := hL.kKey; have nKey := hL.nKey
  simp only [Lay.KEY, F.key] at xKey kKey nKey
  have kOk : ∀ {g m₀} {a a1 : State}, Ctx L g m₀ a → Moved verifyArgs a a1 →
      PublicKeyOk p prepared m₀ (State.addr L.key) → PublicKeyOk p prepared a1.mem (State.addr L.key) :=
    fun c f hk e => by
      subst e
      refine PreparedKey.preparedPublicKey_of_bytes ?_ (hk rfl)
      rw [f.2.mem]
      exact c.bytesAt_eq xKey kKey (by have : publicKeyLen p true = preparedPublicKeyBytes p := rfl; omega)
  have pre₁ := verifyK_pre hL F c₁ f₁.1 (f₁.2.sp.trans c₁.sp) (kOk c₁ f₁ k₁)
  have pre₂ := verifyK_pre hL F c₂ f₂.1 (f₂.2.sp.trans c₂.sp) (kOk c₂ f₂ k₂)
  obtain ⟨RS, hRS, wS⟩ := F.wScr hL
  have cv : ∀ {t t1 : State} {g m₀}, Ctx L g m₀ t → Moved verifyArgs t t1 →
      Covers (verifyRd p prepared L ++ verifyWr p L) (t1.rd ++ t1.wr) ∧ Covers (verifyWr p L) t1.wr :=
    fun hc f => by
      rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
      have hw : ∀ r ∈ verifyWr p L, ∃ R ∈ L.wr, Within r R := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact ⟨RS, hRS, wS⟩
      refine ⟨covers_of_within fun r hr => ?_, covers_of_within hw⟩
      rcases List.mem_append.mp hr with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact ⟨_, List.mem_append_left _ (F.inKey hL), within_self _⟩
        · exact ⟨_, List.mem_append_right _ hL.inSC, mu_within hL⟩
        · exact ⟨_, List.mem_append_left _ F.inSig, within_self _⟩
      · obtain ⟨R, hR, w⟩ := hw r h
        exact ⟨R, List.mem_append_right _ hR, w⟩
  refine ⟨pre₁, pre₂, ?_, (cv c₁ f₁).1, (cv c₁ f₁).2, (cv c₂ f₂).1, (cv c₂ f₂).2⟩
  obtain ⟨x0, x1, x2, x3⟩ := verifyRegs_of hL c₁ f₁.1
  obtain ⟨y0, y1, y2, y3⟩ := verifyRegs_of hL c₂ f₂.1
  have ek : ∀ {g m₀} {a a1 : State}, Ctx L g m₀ a → Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr L.key) p.pkLen = bytesAt m₀ (State.addr L.key) p.pkLen := fun c f => by
    rw [f.2.mem]
    exact c.bytesAt_eq (xKey.sub_right (Region.sub_prefix (pkLen_le prepared)))
      (kKey.sub_right (Region.sub_prefix (pkLen_le prepared))) (by have := pkLen_le (p := p) prepared; omega)
  have es : ∀ {g m₀} {a a1 : State}, Ctx L g m₀ a → Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr L.sig) p.sigLen = bytesAt m₀ (State.addr L.sig) p.sigLen :=
    fun c f => by
      rw [f.2.mem]
      exact c.bytesAt_eq F.xSig F.kSig (by have := F.nSig; omega)
  have eμ : ∀ {a a1 : State}, Moved verifyArgs a a1 →
      bytesAt a1.mem (State.addr (L.X32 + BitVec.ofNat 32 840)) 64 = bytesAt a.mem L.MU 64 :=
    fun f => by rw [f.2.mem, mu_eq hL]
  obtain ⟨ik, im, ic, is⟩ := verifyI_eq hi
  have sw : ∀ a : BitVec 32, BitVec.setWidth 64 a = State.addr a := fun _ => rfl
  have g : ∀ {a1 : State} {r : Reg}, r ∉ linkRegs →
      (a1.callEntry.withRegions (verifyRd p prepared L) (verifyWr p L)).gpr r = a1.gpr r := fun hr => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp]; rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]
  · rw [g (by decide), g (by decide), x0, y0]
  · rw [g (by decide), g (by decide), x1, y1]
  · rw [g (by decide), g (by decide), x2, y2]
  · rw [g (by decide), g (by decide), x3, y3]
  · simp only [Verify.pkOf, Verify.vPk, State.withRegions_mem, State.callEntry_mem]
    rw [g (by decide), g (by decide), x0, y0, ek c₁ f₁, ek c₂ f₂, ik]
  · simp only [Verify.muOf, Verify.vMu, State.withRegions_mem, State.callEntry_mem]
    rw [g (by decide), g (by decide), x1, y1, eμ f₁, eμ f₂, μ₁, μ₂, ik, im, ic]
  · simp only [Verify.sgOf, Verify.vSg, State.withRegions_mem, State.callEntry_mem]
    rw [g (by decide), g (by decide), x2, y2, es c₁ f₁, es c₂ f₂, is]

/-- The layout is that of a run of `verify_message_cached` from a state with
the memory `m`, past the branch on `ctx_len`. -/
def COk (p : Params) (prepared : Bool) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, CPre p prepared σ ∧ (stackArg σ 0).toNat < 256 ∧ clay p prepared σ = L ∧ σ.mem = m

theorem COk.facts {L : Lay} {m : Mem} (h : COk p prepared L m) : VFacts p prepared L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact hσ.vfacts

theorem COk.key {L : Lay} {m : Mem} (h : COk p prepared L m) : PublicKeyOk p prepared m (State.addr L.key) := by
  obtain ⟨σ, hσ, _, rfl, rfl⟩ := h
  exact hσ.key

theorem COk.trSide {L : Lay} {m : Mem} (h : COk p prepared L m) : TrSide L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact hσ.trSide

/-- The cached `tr` is `H(pk, 64)`. -/
theorem COk.digest {L : Lay} {m : Mem} (h : COk p prepared L m) :
    bytesAt m (State.addr L.rnd) 64 = H (bytesAt m (State.addr L.key) p.pkLen) 64 := by
  obtain ⟨σ, hσ, _, rfl, rfl⟩ := h
  exact hσ.tr

/-- The body, between the entry and the exit: its runs end with the same
`r7` and stack pointer. -/
theorem cachedBody_tr {n : String} {c : Prog isa} (hV : VerifyFn p prepared c) :
    RelCT isa (Two (verifyI p) fun L m _ => COk p prepared L m)
      (.seq (muHash (.slot fRnd)) (.seq (.block (setArgs verifyArgs)) (.call n c)))
      fun a b => a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp := by
  have mh := muHash_tr_of (I := verifyI p) (Φ := fun L m _ => COk p prepared L m) (G := TrSide) (tr := .slot fRnd)
    (fun _ _ _ h => h.trSide) (by decide) rfl (fun L => L.rnd) (fun _ _ _ _ hL hc => hc.trV hL)
    fun _ hL h => h.side hL
  have mh' := two_wp (I := verifyI p) (Φ := fun L m _ => COk p prepared L m)
    (Ψ := fun L m t => COk p prepared L m ∧ VMuOk p L m t) mh fun L g m₀ t hL hc hφ =>
      WP.mono (muHashC_ok hL hc hφ.trSide) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, by
        unfold VMuOk; rw [hμ, hφ.digest]⟩
  refine RelCT.postDep (F := fun x x' => x'.gpr .r7 = x.gpr .r7 ∧ x'.sp = x.sp)
    (mh'.seq (verifyCall_tr hV fun _ _ _ h => ⟨h.1.facts, h.2, h.1.key⟩)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g m₀} {t : State}, L.Ok → Ctx L g m₀ t → COk p prepared L m₀ →
        WP isa (.seq (muHash (.slot fRnd)) (.seq (.block (setArgs verifyArgs)) (.call n c))) t
          fun t' => t'.gpr .r7 = t.gpr .r7 ∧ t'.sp = t.sp := fun hL hc hφ =>
      WP.seq (WP.mono (muHashC_ok hL hc hφ.trSide) fun t₂ ⟨hc₂, _⟩ =>
        WP.mono (verifyCall_ok hV hL hφ.facts hc₂ (fun e => by
          subst e
          have xKey := hL.xKey; have kKey := hL.kKey; have nKey := hL.nKey
          simp only [Lay.KEY, hφ.facts.key] at xKey kKey nKey
          exact PreparedKey.preparedPublicKey_of_bytes (hc₂.bytesAt_eq xKey kKey (by have : publicKeyLen p true = preparedPublicKeyBytes p := rfl; omega)) (hφ.key rfl)))
          fun s' ⟨hf, _⟩ =>
          ⟨hf.r7.trans hc.r7.symm, hf.sp.trans hc.sp.symm⟩)
    obtain ⟨L, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.r7, c₂.r7], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- The public data of the contract, spelled out. -/
structure CPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : leakBytes (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.pkLen ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r1)) (s₁.gpr .r2).toNat ++
      bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat ++
      bytesAt s₁.mem (State.addr (stackArg s₁ 1)) p.sigLen) =
    leakBytes (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.pkLen ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r1)) (s₂.gpr .r2).toNat ++
      bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat ++
      bytesAt s₂.mem (State.addr (stackArg s₂ 1)) p.sigLen)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1
  a2 : stackArg s₁ 2 = stackArg s₂ 2
  a3 : stackArg s₁ 3 = stackArg s₂ 3

theorem cPub_of {s₁ s₂ : State} (h : (verifyMessageCachedContract p Arm.abi 52).pub s₁ s₂) : CPub p s₁ s₂ := by
  sig_pub [verifyMessageCachedContract, verifyMessageCachedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

theorem cPub_of_prepared {s₁ s₂ : State} (h : (preparedVerifyMessageContract p Arm.abi 52).pub s₁ s₂) :
    CPub p s₁ s₂ := by
  sig_pub [preparedVerifyMessageContract, preparedVerifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem clay_eq {s₁ s₂ : State} (h₁ : CPre p prepared s₁) (h₂ : CPre p prepared s₂) (h : CPub p s₁ s₂) :
    clay p prepared s₁ = clay p prepared s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]
    simp only [rKey, rMsg, rCtx, rArgs, sArg, stackArgAddr0, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a3]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [sArg, h.a2]
  simp only [clay, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, h.a3, e1, e2]

/-- Two states with the stack pointer, permissions and memory of two entry
states agreeing on the public data agree on the first `n ≤ 16` bytes of the
arguments on the stack. -/
theorem cAgree {x y a b : State} (hx : CPre p prepared x) (hy : CPre p prepared y) (hpub : CPub p x y)
    (ha : a.sp = x.sp ∧ a.wr = x.wr ∧ a.mem = x.mem) (hb : b.sp = y.sp ∧ b.wr = y.wr ∧ b.mem = y.mem)
    {n : Nat} (hn : n ≤ 16) : VG.Arm.Taint.Agree (argTaint [] n) a b := by
  have w : ∀ {z c : State}, CPre p prepared z → c.sp = z.sp ∧ c.wr = z.wr ∧ c.mem = z.mem →
      c.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ c.wr, Region.Disjoint ⟨State.addr c.sp, n⟩ r := fun {z c} hz hc => by
    refine ⟨by rw [hc.1]; have := hz.spA; omega, fun r hr => ?_⟩
    rw [hc.2.1, hz.wr] at hr
    have hs : Region.Sub ⟨State.addr c.sp, n⟩ (rArgs z 16) := by
      simp only [rArgs, stackArgAddr0, hc.1]; exact Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (hz.scrArgs.sub_right hs).symm
  have hsp : a.sp = b.sp := by rw [ha.1, hb.1, hpub.sp]
  refine agree_argTaint (fun r hr => by simp at hr) hsp (w hx ha) (w hy hb) fun k hk => ?_
  exact argMem_of (s₁ := a) (s₂ := b) (j := 4) hsp (by rw [ha.1]; have := hx.spA; omega) (fun i hi => by
    simp only [stackArg, stackArgAddr, ha.1, hb.1, ha.2.2, hb.2.2]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hpub.a0
    · exact hpub.a1
    · exact hpub.a2
    · exact hpub.a3) k (by omega)

/-- The entry states of two runs: the precondition and the public data. -/
abbrev CP2 (p : Params) (prepared : Bool) (x y : State) : Prop :=
  CPre p prepared x ∧ CPre p prepared y ∧ CPub p x y

theorem enterC_taint (p : Params) :
    (VG.Arm.taint.check (argTaint [] 16) (.block (enter 8 p cachedLoads)) (.block [])).isSome = true := by
  rfl

theorem verifyMessageCached_ct {n : String} {c : Prog isa} (hV : VerifyFn p prepared c) (hp : p ∈ params) :
    ConstantTime isa (CPre p prepared) (CPub p) (verifyMessageCached n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => CPre p prepared s₁ ∧ CPre p prepared s₂ ∧ CPub p s₁ s₂) =
      Ghost (CP2 p prepared) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold verifyMessageCached top
  have hchk := ghost_step (P := CP2 p prepared) (A := fun x a => a = x) (B := AChk)
    (c := .block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (argRel [] 4 (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂
      exact cAgree hxy.1 hxy.2.1 hxy.2.2 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by omega))
      chk_taint)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂; exact ⟨chk_ok (hxy.1.args (by omega)), chk_ok (hxy.2.1.args (by omega))⟩
  refine RelCT.seq hchk (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, hxy.2.2.a0]) ?_ ?_)
  · exact taintRel [] (fun _ _ _ r hr => by simp at hr) mov2_taint
  · let A : State → State → Prop := fun x a => AChk x a ∧ isa.eval .ne a = some false
    let B : State → State → Prop := fun x t => (stackArg x 0).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (clay p prepared x) a.gpr a.mem t
    have hent := ghost_step (P := CP2 p prepared) (A := A) (B := B) (c := .block (enter 8 p cachedLoads))
      (argRel [] 16 (fun a b ⟨x, y, hxy, f₁, f₂⟩ =>
        cAgree hxy.1 hxy.2.1 hxy.2.2 ⟨f₁.1.1.sp, f₁.1.1.wr, f₁.1.1.mem⟩
          ⟨f₂.1.1.sp, f₂.1.1.wr, f₂.1.1.mem⟩ (Nat.le_refl _)) (enterC_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), CPre p prepared x' → A x' a' →
            WP isa (.block (enter 8 p cachedLoads)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (stackArg x' 0).toNat < 256 := by
            rw [e] at ef; simpa using ef
          exact WP.mono (enterC_ok hp hx h8 o) fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← hxy.2.2.a0, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h)
      (RelCT.seq (RelCT.mono (cachedBody_tr hV) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
        ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (taintRel [.r7] (fun a b h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1) leave_taint))
    have hx := hxy.1
    have hy := hxy.2.1
    have hpub := hxy.2.2
    have e := clay_eq hx hy hpub
    refine ⟨clay p prepared x, a'.gpr, b'.gpr, a'.mem, b'.mem, clay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.r0, ← hpub.r1, ← hpub.r2, ← hpub.r3, ← hpub.a0, ← hpub.a1] at lk
    unfold verifyI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.Arm.Message
