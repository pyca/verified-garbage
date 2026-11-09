module
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashMu
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.Rel
public import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall

import VerifiedGarbage.Proof.MlDsa.Arm.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.Arm.Common

/-!
# ML-DSA on ARMv7, `sign_message`: constant time

Untrusted: everything here is checked by Lean. Two runs from states that
satisfy the contract and agree on its public data, which includes what
`signMessageLeak` says (`signI`), leak the same: the branch on `ctx_len`,
the entry and the exit depend only on the pointers and the lengths (the
taint analysis, with the arguments on the stack public); the hashing leaks
only the layout (`muHash_tr`); and the call of the signing function on `μ`
leaks only `signLeak` of the key, `μ` and `rnd`, which is `signMessageLeak`
of the inputs (`signCall_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (push2_frame push2_arg view_gpr below push_eq)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {prepared : Bool}

/-- What the contract says two runs agree on, beyond the pointers and lengths. -/
def signI (p : Params) (L : Lay) (m₁ m₂ : Mem) : Prop :=
  signMessageLeak p (bytesAt m₁ (State.addr L.key) p.skLen) (bytesAt m₁ (State.addr L.msg) L.len.toNat)
      (bytesAt m₁ (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m₁ (State.addr L.rnd) 32) =
    signMessageLeak p (bytesAt m₂ (State.addr L.key) p.skLen) (bytesAt m₂ (State.addr L.msg) L.len.toNat)
      (bytesAt m₂ (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m₂ (State.addr L.rnd) 32)

/-- The layout is that of a run of `sign_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def SOk (p : Params) (prepared : Bool) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, SPre p prepared σ ∧ (stackArg σ 0).toNat < 256 ∧ slay p prepared σ = L ∧ σ.mem = m

/-- `μ` at `X + 840`. -/
def MuOk (L : Lay) (m : Mem) (t : State) : Prop :=
  bytesAt t.mem L.MU 64 = H (bytesAt m (State.addr (L.key + BitVec.ofNat 32 64)) 64 ++ hdrBytes L ++
    bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {L : Lay} (hL : L.Ok) (hk : p.skLen ≤ L.keyLen) (hs : 128 ≤ p.skLen) (m : Mem) :
    signMessageLeak p (bytesAt m (State.addr L.key) p.skLen) (bytesAt m (State.addr L.msg) L.len.toNat)
        (bytesAt m (State.addr L.ctx) L.ctxLen.toNat) (bytesAt m (State.addr L.rnd) 32) =
      signLeak p (bytesAt m (State.addr L.key) p.skLen) (H (bytesAt m (State.addr (L.key + BitVec.ofNat 32 64)) 64 ++
        hdrBytes L ++ bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ bytesAt m (State.addr L.msg) L.len.toNat) 64)
        (bytesAt m (State.addr L.rnd) 32) := by
  have := hL.hKey
  have := hL.nKey
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact hL.ctxLt)]
  simp only [messageRep, skTr, hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc]
  rw [addr_add (by omega), Proof.MlKem.bytesAt_slice _ _ (by omega)]

/-- What a layout of `sign_message` says of `rnd`, `sig` and `scratch`. -/
structure SFacts (p : Params) (prepared : Bool) (L : Lay) : Prop where
  key : L.keyLen = secretKeyLen p prepared
  xRnd : L.SC.Disjoint ⟨State.addr L.rnd, 32⟩
  kRnd : L.STK.Disjoint ⟨State.addr L.rnd, 32⟩
  inRnd : (⟨State.addr L.rnd, 32⟩ : Region) ∈ L.rd
  inSig : (⟨State.addr L.sig, p.sigLen⟩ : Region) ∈ L.wr

theorem SOk.facts {L : Lay} {m : Mem} (h : SOk p prepared L m) : SFacts p prepared L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, hσ.rndScr.symm, hσ.stkRnd, by simp [slay, hσ.rd], by simp [slay, hσ.wr]⟩

/-- The key of the layout, at the memory of a run from it. -/
theorem SOk.keyOk {L : Lay} {m : Mem} (h : SOk p prepared L m) (hL : L.Ok) {g : Reg → BitVec 32} {t : State}
    (hc : Ctx L g m t) : SecretKeyOk p prepared t.mem (State.addr L.key) := by
  obtain ⟨σ, hσ, -, rfl, rfl⟩ := h
  intro hpr
  subst hpr
  exact VG.Proof.MlDsa.PreparedKey.preparedSecretKey_of_bytes
    (hc.bytesAt_eq hL.xKey hL.kKey (by
      have := hσ.nSk; have e : secretKeyLen p true = preparedSecretKeyBytes p := rfl; omega))
    (hσ.key rfl)

/-- The regions the signing function on `μ` is given, as functions of the layout. -/
abbrev sRd (L : Lay) : List Region :=
  [⟨State.addr L.key, L.keyLen⟩, ⟨L.MU, 64⟩, ⟨State.addr L.rnd, 32⟩, ⟨State.addr L.SP - BitVec.ofNat 64 8, 4⟩]
abbrev sWr (p : Params) (L : Lay) : List Region := [⟨State.addr L.sig, p.sigLen⟩, ⟨State.addr L.scr, sScr p⟩]

/-- The entry state of the signing function on `μ`, from either run. -/
theorem sView {σ : State} (hp : p ∈ params) (hσ : SPre p prepared σ) (h8 : (stackArg σ 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 E : State} (hc : Ctx (slay p prepared σ) g m₀ t) (f : Moved signArgs t t1)
    (hE : (pushed [.r12, .lr] t1).callEntry.withRegions (sRd (slay p prepared σ)) (sWr p (slay p prepared σ)) = E) :
    E.sp = σ.sp - BitVec.ofNat 32 8 ∧ E.gpr .r0 = σ.gpr .r0 ∧
      E.gpr .r1 = (slay p prepared σ).X32 + BitVec.ofNat 32 840 ∧ E.gpr .r2 = stackArg σ 1 ∧ E.gpr .r3 = stackArg σ 2 ∧
      stackArg E 0 = stackArg σ 3 ∧
      bytesAt E.mem (State.addr (σ.gpr .r0)) p.skLen = bytesAt m₀ (State.addr (σ.gpr .r0)) p.skLen ∧
      bytesAt E.mem (State.addr ((slay p prepared σ).X32 + BitVec.ofNat 32 840)) 64 = bytesAt t.mem (slay p prepared σ).MU 64 ∧
      bytesAt E.mem (State.addr (stackArg σ 1)) 32 = bytesAt m₀ (State.addr (stackArg σ 1)) 32 := by
  have hL := slay_ok hp hσ h8
  have F : SFacts p prepared (slay p prepared σ) := SOk.facts ⟨σ, hσ, h8, rfl, rfl⟩
  obtain ⟨e0, e1, e2, e3, e4⟩ := signRegs_of hL hc f.1
  have hsp1 : t1.sp = σ.sp := f.2.sp.trans hc.sp
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := hσ.sp; omega
  obtain ⟨-, a1, -⟩ := push2_arg (t := E) h8' (by rw [← hE]; rfl) (by rw [← hE]; rfl)
  have bk : Region.Sub (below t1 8) (slay p prepared σ).STK := below_stk hsp1
  have em : E.mem = storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr] := by rw [← hE]; rfl
  have g : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE]; exact view_gpr _ _ _ _ hr
  refine ⟨by rw [← hE, State.withRegions_sp, State.callEntry_sp, VG.Arm.pushed_sp, hsp1]; rfl,
    by rw [g (by decide), e0], by rw [g (by decide), e1], by rw [g (by decide), e2], by rw [g (by decide), e3],
    by rw [a1, e4], ?_, ?_, ?_⟩
  · have hkl := skLen_le (p := p) prepared
    rw [em, storeWords_bytes h8' ((hσ.stkSk.sub_right (Region.sub_prefix hkl)).symm.sub_right bk)
      (by have := hσ.nSk; omega), f.2.mem]
    exact hc.bytesAt_eq (p := State.addr (slay p prepared σ).key) (hL.xKey.sub_right (Region.sub_prefix hkl))
      (hL.kKey.sub_right (Region.sub_prefix hkl)) (by have := hσ.nSk; omega)
  · rw [em, storeWords_bytes h8' (by rw [mu_eq hL]; exact (k_mu hL).symm.sub_right bk) (by decide), f.2.mem,
      mu_eq hL]
  · rw [em, storeWords_bytes h8' (hσ.stkRnd.symm.sub_right bk) (by decide), f.2.mem]
    exact hc.bytesAt_eq (p := State.addr (slay p prepared σ).rnd) F.xRnd F.kRnd (by decide)

/-- Two runs of the call of the signing function on `μ`. -/
theorem signCall_tr {n : String} {c : Prog isa} (hS : SignFn p prepared c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m t => SOk p prepared L m ∧ MuOk L m t)
      (.seq (.block (setArgs signArgs)) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))) fun _ _ => True := by
  refine RelCT.seq (setArgs_two (by decide)) (VG.Arm.RelCT.frame (fun a b ⟨x, y, h, f₁, f₂⟩ => by
    rw [f₁.2.sp, f₂.2.sp]; exact h.r7.2) ?_)
  -- The layout, out of the relation, so that the call's regions are fixed.
  refine RelCT.mono (P := fun a b => ∃ L : Lay, ∃ x y a1 b1, (∃ g₁ g₂ m₁ m₂, L.Ok ∧ signI p L m₁ m₂ ∧
      Ctx L g₁ m₁ x ∧ Ctx L g₂ m₂ y ∧ (SOk p prepared L m₁ ∧ MuOk L m₁ x) ∧ (SOk p prepared L m₂ ∧ MuOk L m₂ y)) ∧
      Moved signArgs x a1 ∧ Moved signArgs y b1 ∧ a = pushed [.r12, .lr] a1 ∧ b = pushed [.r12, .lr] b1)
    (RelCT.exists_ fun L => RelCT.call hS.ok hS.ct (sRd L) (sWr p L) fun a b h => ?_)
    (fun a b ⟨a1, b1, ⟨x, y, ⟨L, hp'⟩, f₁, f₂⟩, ea, eb⟩ => ⟨L, x, y, a1, b1, hp', f₁, f₂, push_eq ea, push_eq eb⟩)
    fun _ _ h => h
  obtain ⟨x, y, a1, b1, ⟨g₁, g₂, m₁, m₂, hL, hi, c₁, c₂, ⟨φ₁, μ₁⟩, ⟨φ₂, μ₂⟩⟩, f₁, f₂, rfl, rfl⟩ := h
  have F := φ₁.facts
  have k₁ := φ₁.keyOk hL c₁
  have k₂ := φ₂.keyOk hL c₂
  obtain ⟨σ, hσ, h8, rfl, -⟩ := φ₁
  have hsx : a1.sp = σ.sp := f₁.2.sp.trans c₁.sp
  have hsy : b1.sp = σ.sp := f₂.2.sp.trans c₂.sp
  have eR : ∀ t1 : State, t1.sp = σ.sp → signRd p prepared σ ++ [argR t1] = sRd (slay p prepared σ) := fun t1 ht => by
    simp only [argR, ht, List.cons_append, List.nil_append]; rfl
  have pre₁ := signK_pre hp hσ h8 c₁ f₁.1 hsx f₁.2.mem k₁
  have pre₂ := signK_pre hp hσ h8 c₂ f₂.1 hsy f₂.2.mem k₂
  rw [eR a1 hsx] at pre₁
  rw [eR b1 hsy] at pre₂
  have hL' := slay_ok hp hσ h8
  have cv : ∀ {t t1 : State} {g m₀}, Ctx (slay p prepared σ) g m₀ t → Moved signArgs t t1 →
      Covers (sRd (slay p prepared σ) ++ sWr p (slay p prepared σ)) ((pushed [.r12, .lr] t1).rd ++ (pushed [.r12, .lr] t1).wr) ∧
        Covers (sWr p (slay p prepared σ)) (pushed [.r12, .lr] t1).wr := fun {t t1 _ _} hc f => by
    have ht : t1.sp = σ.sp := f.2.sp.trans hc.sp
    have h8' : 8 ≤ t1.sp.toNat := by rw [ht]; have := hσ.sp; omega
    have := cov_pushed h8' (rd := signRd p prepared σ) (wr := signWr p σ) (fun r hr => by
        rw [f.2.rd, f.2.wr, hc.rd, hc.wr]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_append_left _ (F.key ▸ hL'.inKey), within_self _⟩
        · exact ⟨_, List.mem_append_right _ hL'.inSC, mu_within hL'⟩
        · exact ⟨_, List.mem_append_left _ F.inRnd, within_self _⟩)
      (fun r hr => by
        rw [f.2.wr, hc.wr]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, F.inSig, within_self _⟩
        · exact ⟨_, hL'.inSC, within_base _ (by simp only [slay]; rw [mScr_eq]; simp only [sScr, oE]; omega)⟩)
    rwa [eR t1 ht] at this
  refine ⟨pre₁, pre₂, ?_, (cv c₁ f₁).1, (cv c₁ f₁).2, (cv c₂ f₂).1, (cv c₂ f₂).2⟩
  generalize hE₁ : (pushed [.r12, .lr] a1).callEntry.withRegions (sRd (slay p prepared σ)) (sWr p (slay p prepared σ)) = E₁
  generalize hE₂ : (pushed [.r12, .lr] b1).callEntry.withRegions (sRd (slay p prepared σ)) (sWr p (slay p prepared σ)) = E₂
  obtain ⟨s₁, x0, x1, x2, x3, x4, kb₁, u₁, r₁⟩ := sView hp hσ h8 c₁ f₁ hE₁
  obtain ⟨s₂, y0, y1, y2, y3, y4, kb₂, u₂, r₂⟩ := sView hp hσ h8 c₂ f₂ hE₂
  simp only [Sign.signE]
  rw [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, s₁, s₂, kb₁, kb₂, u₁, u₂, r₁, r₂, μ₁, μ₂]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  have := hi
  unfold signI at this
  have hk : p.skLen ≤ (slay p prepared σ).keyLen := by rw [F.key]; exact skLen_le prepared
  rw [leak_eq hL' hk (skLen_ge hp).1, leak_eq hL' hk (skLen_ge hp).1] at this
  exact this

/-- The public data of the contract, spelled out. -/
structure SPub (p : Params) (s₁ s₂ : State) : Prop where
  sp : s₁.sp = s₂.sp
  leak : signMessageLeak p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen)
      (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) (s₁.gpr .r2).toNat)
      (bytesAt s₁.mem (State.addr (s₁.gpr .r3)) (stackArg s₁ 0).toNat) (bytesAt s₁.mem (State.addr (stackArg s₁ 1)) 32) =
    signMessageLeak p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen)
      (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) (s₂.gpr .r2).toNat)
      (bytesAt s₂.mem (State.addr (s₂.gpr .r3)) (stackArg s₂ 0).toNat) (bytesAt s₂.mem (State.addr (stackArg s₂ 1)) 32)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  a0 : stackArg s₁ 0 = stackArg s₂ 0
  a1 : stackArg s₁ 1 = stackArg s₂ 1
  a2 : stackArg s₁ 2 = stackArg s₂ 2
  a3 : stackArg s₁ 3 = stackArg s₂ 3

theorem sPub_of {s₁ s₂ : State} (h : (signMessageContract p Arm.abi 52).pub s₁ s₂) : SPub p s₁ s₂ := by
  sig_pub [signMessageContract, signMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

theorem sPub_of_prepared {s₁ s₂ : State} (h : (preparedSignMessageContract p Arm.abi 52).pub s₁ s₂) :
    SPub p s₁ s₂ := by
  sig_pub [preparedSignMessageContract, preparedSignMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, h, i, j⟩

/-- Two runs from states agreeing on the public data have the same layout. -/
theorem slay_eq {s₁ s₂ : State} (h₁ : SPre p prepared s₁) (h₂ : SPre p prepared s₂) (h : SPub p s₁ s₂) : slay p prepared s₁ = slay p prepared s₂ := by
  have e1 : s₁.rd = s₂.rd := by
    rw [h₁.rd, h₂.rd]
    simp only [rKey, rMsg, rCtx, rArgs, sArg, stackArgAddr0, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1]
  have e2 : s₁.wr = s₂.wr := by
    rw [h₁.wr, h₂.wr]; simp only [sArg, h.a2, h.a3]
  simp only [slay, h.sp, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, h.a3, e1, e2]

/-- The body, between the entry and the exit: its runs end with the same
`r7` and stack pointer. -/
theorem signBody_tr {n : String} {c : Prog isa} (hS : SignFn p prepared c) (hp : p ∈ params) :
    RelCT isa (Two (signI p) fun L m _ => SOk p prepared L m)
      (.seq (muHash (.slotOff fKey 64)) (.seq (.block (setArgs signArgs))
        (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))))
      fun a b => a.gpr .r7 = b.gpr .r7 ∧ a.sp = b.sp := by
  have side : ∀ L : Lay, L.Ok → (L.key + BitVec.ofNat 32 64).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ R) ∧
      Region.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ := fun L hL => by
    have := hL.hKey
    have := hL.nKey
    have w : Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ L.KEY := by
      rw [addr_add (by omega)]; exact within_off _ (by omega)
    have hst : Region.Sub ⟨L.ST, 200⟩ L.SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [x0] using this
    refine ⟨?_, ⟨_, List.mem_append_left _ hL.inKey, w⟩, (hL.xKey.symm.sub_left w.sub).sub_right hst,
      (hL.xKey.symm.sub_left w.sub).sub_right (hL.sub_sc (by decide : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right w.sub⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]
    omega
  have mh := muHash_tr (I := signI p) (Φ := fun L m _ => SOk p prepared L m) (tr := .slotOff fKey 64) (by decide) rfl
    (fun L => L.key + BitVec.ofNat 32 64) (fun L g m t hL hc => hc.slotOffV hL 64) side
  have mh' := two_wp (I := signI p) (Φ := fun L m _ => SOk p prepared L m) (Ψ := fun L m t => SOk p prepared L m ∧ MuOk L m t) mh
    fun L g m₀ t hL hc hφ => by
      have := hL.hKey
      have := hL.nKey
      have w : Within ⟨State.addr (L.key + BitVec.ofNat 32 64), 64⟩ L.KEY := by
        rw [addr_add (by omega)]; exact within_off _ (by omega)
      obtain ⟨a, b, c, d, e⟩ := side L hL
      refine WP.mono (muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl (fun t' hc' => hc'.slotOffV hL 64)
        a b c d e) fun t' ⟨hc', hμ⟩ => ⟨hc', hφ, ?_⟩
      unfold MuOk
      rw [hμ, hc.bytesAt_eq (hL.xKey.sub_right w.sub) (hL.kKey.sub_right w.sub) (by decide)]
  refine RelCT.postDep (F := fun x x' => x'.gpr .r7 = x.gpr .r7 ∧ x'.sp = x.sp)
    (mh'.seq (signCall_tr hS hp)) (fun x y hxy => ?_) fun x y x' y' hxy f₁ f₂ => ?_
  · have run : ∀ {L : Lay} {g m₀} {t : State}, L.Ok → Ctx L g m₀ t → SOk p prepared L m₀ →
        WP isa (.seq (muHash (.slotOff fKey 64)) (.seq (.block (setArgs signArgs))
          (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)))) t
          fun t' => t'.gpr .r7 = t.gpr .r7 ∧ t'.sp = t.sp := fun hL hc hφ => by
      have hφ' := hφ
      obtain ⟨σ, hσ, h8, rfl, -⟩ := hφ
      obtain ⟨a, b, c, d, e⟩ := side _ hL
      refine WP.seq (WP.mono (muHash_ok hL hc (tr := .slotOff fKey 64) (by decide) rfl
        (fun t' hc' => hc'.slotOffV hL 64) a b c d e) fun t₁ ⟨hc₁, _⟩ => ?_)
      exact WP.mono (signCall_ok hS hp hσ h8 hc₁ (hφ'.keyOk hL hc₁)) fun s' ⟨hf, _⟩ =>
        ⟨hf.r7.trans hc.r7.symm, hf.sp.trans hc.sp.symm⟩
    obtain ⟨L, _, _, _, _, hL, _, c₁, c₂, φ₁, φ₂⟩ := hxy
    exact ⟨run hL c₁ φ₁, run hL c₂ φ₂⟩
  · obtain ⟨L, _, _, _, _, _, _, c₁, c₂, _, _⟩ := hxy
    exact ⟨by rw [f₁.1, f₂.1, c₁.r7, c₂.r7], by rw [f₁.2, f₂.2, c₁.sp, c₂.sp]⟩

/-- Two states with the stack pointer, permissions and memory of two entry
states agreeing on the public data agree on the first `n ≤ 16` bytes of the
arguments on the stack. -/
theorem sAgree {x y a b : State} (hx : SPre p prepared x) (hy : SPre p prepared y) (hpub : SPub p x y)
    (ha : a.sp = x.sp ∧ a.wr = x.wr ∧ a.mem = x.mem) (hb : b.sp = y.sp ∧ b.wr = y.wr ∧ b.mem = y.mem)
    {n : Nat} (hn : n ≤ 16) : VG.Arm.Taint.Agree (argTaint [] n) a b := by
  have w : ∀ {z c : State}, SPre p prepared z → c.sp = z.sp ∧ c.wr = z.wr ∧ c.mem = z.mem →
      c.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ c.wr, Region.Disjoint ⟨State.addr c.sp, n⟩ r := fun {z c} hz hc => by
    refine ⟨by rw [hc.1]; have := hz.spA; omega, fun r hr => ?_⟩
    rw [hc.2.1, hz.wr] at hr
    have hs : Region.Sub ⟨State.addr c.sp, n⟩ (rArgs z 16) := by
      simp only [rArgs, stackArgAddr0, hc.1]; exact Region.sub_prefix hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hz.sigArgs.sub_right hs).symm
    · exact (hz.scrArgs.sub_right hs).symm
  have hsp : a.sp = b.sp := by rw [ha.1, hb.1, hpub.sp]
  refine agree_argTaint (fun r hr => by simp at hr) hsp (w hx ha) (w hy hb) fun k hk => ?_
  have := argMem_of (s₁ := a) (s₂ := b) (j := 4) hsp (by rw [ha.1]; have := hx.spA; omega) (fun i hi => by
    simp only [stackArg, stackArgAddr, ha.1, hb.1, ha.2.2, hb.2.2]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hpub.a0
    · exact hpub.a1
    · exact hpub.a2
    · exact hpub.a3) k (by omega)
  exact this

/-- The entry states of two runs: the precondition and the public data. -/
abbrev SP2 (p : Params) (prepared : Bool) (x y : State) : Prop :=
  SPre p prepared x ∧ SPre p prepared y ∧ SPub p x y

/-- After the shift of `ctx_len` and the comparison. -/
abbrev AChk (x s1 : State) : Prop := Only [.r12] x s1 ∧ isa.eval .ne s1 = some (decide ¬ (stackArg x 0).toNat < 256)

theorem chk_taint : (VG.Arm.taint.check (argTaint [] 4)
    (.block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)]) (.block [])).isSome = true := by
  rfl

theorem mov2_taint : (VG.Arm.taint.check (Taint.ofRegs []) (.block [.mov .r0 (.imm 2)]) (.block [])).isSome = true := by
  rfl

theorem leave_taint : (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.block leave) (.block [])).isSome = true := by
  rfl

theorem enterS_taint (p : Params) :
    (VG.Arm.taint.check (argTaint [] 16) (.block (enter 12 p signLoads)) (.block [])).isSome = true := by
  rfl

theorem signMessage_ct {n : String} {c : Prog isa} (hS : SignFn p prepared c) (hp : p ∈ params) :
    ConstantTime isa (SPre p prepared) (SPub p) (signMessage n c p) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  have e0 : (fun s₁ s₂ => SPre p prepared s₁ ∧ SPre p prepared s₂ ∧ SPub p s₁ s₂) =
      Ghost (SP2 p prepared) (fun x a => a = x) := by
    funext a b; apply propext
    exact ⟨fun h => ⟨a, b, h, rfl, rfl⟩, fun ⟨_, _, h, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h⟩
  rw [e0]
  unfold signMessage top
  -- `r12 ← ctx_len >> 8`, compared with 0.
  have hchk := ghost_step (P := SP2 p prepared) (A := fun x a => a = x) (B := AChk)
    (c := .block [.ldrSp .r12 0, .mov .r12 (.shifted .r12 .lsr 8), .cmp .r12 (.imm 0)])
    (argRel [] 4 (fun a b ⟨x, y, hxy, e₁, e₂⟩ => by
      subst e₁ e₂
      exact sAgree hxy.1 hxy.2.1 hxy.2.2 ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (by omega))
      chk_taint)
    fun x y a b hxy e₁ e₂ => by
      subst e₁ e₂; exact ⟨chk_ok (hxy.1.args (by omega)), chk_ok (hxy.2.1.args (by omega))⟩
  refine RelCT.seq hchk (RelCT.ite (fun a b ⟨x, y, hxy, f₁, f₂⟩ => by
    rw [f₁.2, f₂.2, hxy.2.2.a0]) ?_ ?_)
  · -- `ctx_len ≥ 256`: return 2.
    exact taintRel [] (fun _ _ _ r hr => by simp at hr) mov2_taint
  · -- The entry.
    let A : State → State → Prop := fun x a => AChk x a ∧ isa.eval .ne a = some false
    let B : State → State → Prop := fun x t => (stackArg x 0).toNat < 256 ∧
      ∃ a : State, a.mem = x.mem ∧ Ctx (slay p prepared x) a.gpr a.mem t
    have hent := ghost_step (P := SP2 p prepared) (A := A) (B := B) (c := .block (enter 12 p signLoads))
      (argRel [] 16 (fun a b ⟨x, y, hxy, f₁, f₂⟩ =>
        sAgree hxy.1 hxy.2.1 hxy.2.2 ⟨f₁.1.1.sp, f₁.1.1.wr, f₁.1.1.mem⟩
          ⟨f₂.1.1.sp, f₂.1.1.wr, f₂.1.1.mem⟩ (Nat.le_refl _)) (enterS_taint p))
      fun x y a b hxy fa fb => by
        have en : ∀ (x' a' : State), SPre p prepared x' → A x' a' →
            WP isa (.block (enter 12 p signLoads)) a' (B x') := fun x' a' hx ⟨⟨o, e⟩, ef⟩ => by
          have h8 : (stackArg x' 0).toNat < 256 := by
            rw [e] at ef; simpa using ef
          have h := hx
          have hL := slay_ok hp h h8
          have hs1 : ∀ o', o' + 4 ≤ 16 → a'.mem.readW (State.addr (a'.sp + BitVec.ofNat 32 o')) 32 =
              x'.mem.readW (State.addr (x'.sp + BitVec.ofNat 32 o')) 32 := fun _ _ => by rw [o.mem, o.sp]
          exact WP.mono (enter_ok hL rfl (nA := 16) (by decide) (Nat.le_refl _) o.sp
            (by rw [o.rd]; rfl) (by rw [o.wr]; rfl) (o.get .r0) (o.get .r1) (o.get .r2) (o.get .r3)
            (fun o' ho => by rw [o.rd, o.wr, o.sp]; exact h.args ho) (by rw [o.sp]; exact h.spA)
            (by rw [o.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega)
            (by rw [hs1 12 (by omega)]; exact stackArg_eq x' 3) (by decide) (fun j hj => by
              have hj4 : j < 4 := hj
              rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
              · exact (hs1 0 (by decide)).trans (stackArg_eq x' 0)
              · exact (hs1 4 (by decide)).trans (stackArg_eq x' 1)
              · exact (hs1 8 (by decide)).trans (stackArg_eq x' 2)
              · exact (hs1 12 (by decide)).trans (stackArg_eq x' 3)))
            fun t hc => ⟨h8, a', o.mem, hc⟩
        exact ⟨en x a hxy.1 fa, en y b hxy.2.1 fb⟩
    refine RelCT.seq (RelCT.mono hent (fun a b ⟨⟨x, y, hxy, f₁, f₂⟩, hc⟩ => ⟨x, y, hxy, ⟨f₁, hc⟩, ⟨f₂, by
      rw [f₂.2, ← hxy.2.2.a0, ← f₁.2]; exact hc⟩⟩) fun _ _ h => h)
      (RelCT.seq (RelCT.mono (signBody_tr hS hp) (fun a b ⟨x, y, hxy, ⟨h8x, a', ma, ca⟩,
        ⟨h8y, b', mb, cb⟩⟩ => ?_) fun _ _ h => h) (taintRel [.r7] (fun a b h r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h.1) leave_taint))
    have hx := hxy.1
    have hy := hxy.2.1
    have hpub := hxy.2.2
    have e := slay_eq hx hy hpub
    refine ⟨slay p prepared x, a'.gpr, b'.gpr, a'.mem, b'.mem, slay_ok hp hx h8x, ?_, ca, e ▸ cb,
      ⟨x, hx, h8x, rfl, ma.symm⟩, ⟨y, hy, h8y, e.symm, mb.symm⟩⟩
    have lk := hpub.leak
    rw [← hpub.r0, ← hpub.r1, ← hpub.r2, ← hpub.r3, ← hpub.a0, ← hpub.a1] at lk
    unfold signI
    rw [ma, mb]
    exact lk

end

end VG.Proof.MlDsa.Arm.Message
