module

public import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall
import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.VerifyCall
meta import VerifiedGarbage.Proof.MlKem.X86.Top
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ML-DSA on x86 (32-bit), `verify_message_cached`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` from the `tr` argument, which the
precondition says is `H(pk, 64)`, then the call of the verification function
on it (`cachedRest_piece`); in the leaf, after the check
(`verifyMessageCached_piece`); and what that says of the contract's
postcondition (`verifyMessageCached_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params}

theorem H_length (s : List Byte) (n : Nat) : (H s n).length = n :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-- What `verify_message_cached` changes is apart from its frame and return address. -/
theorem verify_hW {na : Nat} {T : State → List Region} :
    ∀ s₀, VPre p na T s₀ → ∀ r ∈ vW p na s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (sStk s₀ 132) := by rw [stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 132 - 16) (by omega),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 132 - 16) (k := 16) (by omega) hsp)⟩

/-- `μ` from the cached `tr`, then the call of the verification function on it. -/
theorem cachedRest_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f) :
    Piece (CPre p) (VPub p 8) (CtxO (vlay p 8)) (fun s₀ s => LeafEnd s₀ (vW p 8 s₀) s ∧ VB p 8 s₀ s)
      (.seq (muHash (.arg 7)) (.seq (.block (setArgs verifyArgs)) (Impl.MlKem.X86.callRet rs4 n f))) := by
  have hk : ∀ {s₀ : State} {R : Region}, CPre p s₀ → (vlay p 8 s₀).Ok → (sStk s₀ 132).Disjoint R →
      (vlay p 8 s₀).STK.Disjoint R := fun h₀ hL h => (stk_eq h₀.sp ▸ h).sub_left hL.stk_sub
  refine Piece.seq ((muHash_piece (lay := vlay p 8) (.arg 7) (fun s₀ => arg s₀ 7)
    (fun s₀ => H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64) (by native_taint_decide)
    (fun s₀ s₀' h₀ h₀' hq => (vShape hp).pubL s₀ s₀' h₀.toVPre h₀'.toVPre hq) (fun _ _ _ h => h)
    (fun _ _ => by show 5 ≤ 8; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.argV (by show 7 < 8; decide)) (fun s₀ s₀' h₀ h₀' hq => hq.args 7 (by decide))
    (fun s₀ s h₀ hc => ?_) (fun _ _ => H_length _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩)
    ((verifyCall_piece hp hf).pre_mono (fun _ h => h.toVPre) fun _ _ _ _ h => h)
  · have hL := hc.ok
    rw [hc.ctx.bytesAt_eq h₀.scrTr (hk h₀ hL h₀.kTr) (by decide), p0_bytes (by decide) h₀.sp h₀.kTr (by decide)]
    exact h₀.tr
  · have hst : Region.Sub ⟨(vlay p 8 s₀).ST, 200⟩ (vlay p 8 s₀).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega)
      simpa only [x0] using this
    exact ⟨h₀.nTr, ⟨aR s₀ 7 64, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩,
      h₀.scrTr.symm.sub_right hst, h₀.scrTr.symm.sub_right (hL.sub_sc (by omega : 200 + 640 ≤ 1024)),
      hk h₀ hL h₀.kTr⟩
  · rw [hm]
    simp only [ctxB, msgB]
    rw [p0_bytes (a := (vlay p 8 s₀).ctx.setWidth 64) (n := (vlay p 8 s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega),
      p0_bytes (a := (vlay p 8 s₀).msg.setWidth 64) (n := (vlay p 8 s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega)]
    rfl

/-- `verify_message_cached`, in its leaf. -/
theorem verifyMessageCached_piece (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece (CPre p) (VPub p 8) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ VB p 8 s₀ s) s₀ s') (verifyMessageCached n f p) :=
  top_piece ((vShape hp).pre_mono fun _ h => h.toVPre) tt (vW p 8) (fun s₀ h₀ => verify_hW s₀ h₀.toVPre)
    (nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_ite (NoSp.of_all (by decide +kernel))
      (nosp_seq (enter_nosp 6 p) (nosp_seq (NoSp.of_all (by decide +kernel))
        (nosp_seq (NoSp.of_all (by decide +kernel)) (callRet_nosp hf.nosp))))))
    (cachedRest_piece hp hf)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000`,
`0x10000` and `0x8000` at `0x5004`. -/
def satMemC0 : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501e then 1 else if a = 0x5021 then 0x80 else 0

/-- `satMemC0`, with `tr = H(pk, 64)` at `0x8000`. -/
def satMemC (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then (pkTr (bytesAt satMemC0 0 p.pkLen)).getD (a.toNat - 0x8000) 0
  else satMemC0 a

theorem satMemC_digest {p : Params} (hp : p.pkLen < 0x8000) :
    bytesAt (satMemC p) 0x8000 64 = pkTr (bytesAt (satMemC p) 0 p.pkLen) := by
  have hk : bytesAt (satMemC p) 0 p.pkLen = bytesAt satMemC0 0 p.pkLen := Proof.MlKem.bytesAt_congr fun i hi => by
    have he : ((0 : Addr) + BitVec.ofNat 64 i).toNat = i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
    simp only [satMemC, he, show ¬(0x8000 ≤ i ∧ i < 0x8040) by omega, ↓reduceIte]
  rw [hk]
  apply Proof.MlKem.bytesAt_eq (H_length _ _)
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
  simp only [satMemC, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega, and_self, ↓reduceIte,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [pkTr, H_length]; omega), Option.getD_some]
  rfl

/-- A state satisfying the precondition of `verify_message_cached`. -/
def cachedSat (p : Params) : State :=
  Proof.MlKem.X86.satState (satMemC p) [⟨0, p.pkLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x8000, 64⟩]
    [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]

/-- Its arguments, as `satMemC0` holds them. -/
theorem cachedSat_arg {p : Params} (i : Nat) (hi : i < 8) :
    arg (cachedSat p) i = (satMemC0.readW ((0x5000 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32) :=
  Mem.readW_congr fun j hj => by
    have he : (argAddr (cachedSat p) i + BitVec.ofNat 64 j).toNat = 0x5004 + 4 * i + j := by
      show (((0x5000 : BitVec 32) + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j).toNat = _
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega
    show satMemC p _ = _
    simp only [satMemC, he, show ¬(0x8000 ≤ 0x5004 + 4 * i + j ∧ 0x5004 + 4 * i + j < 0x8040) by omega, ↓reduceIte]

theorem verifyMessageCached_verified (hp : p ∈ params) {n : String} {f : Prog isa} (hf : VerifyFn p f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Verified X86.target (verifyMessageCached n f p) (verifyMessageCachedContract p X86.abi 132) := by
  refine Piece.verified (((verifyMessageCached_piece hp hf tt).pre_mono (fun _ h => cPre_of h)
    fun _ _ _ _ h => cpub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hB, -, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [verifyMessageCachedContract, verifyMessageCachedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [Proof.MlKem.X86.setWidth_append32, hax]
    rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
    · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
    · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr, Proof.MlKem.bytesAt_length]
      simp only [vMu, hdrBytes, vlay, List.append_assoc] at hout
      simp only [List.append_assoc]
      exact hout
  · refine ⟨cachedSat p, ?_⟩
    simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals
      sig_apply_check
      · decide +kernel
      · sig_reduce [verifyMessageCachedContract, verifyMessageCachedSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes]
        sig_and_intros
        all_goals first
          | (rw [cachedSat_arg 7 (by decide), cachedSat_arg 0 (by decide)]; exact satMemC_digest (by decide))
          | decide

end

end VG.Proof.MlDsa.X86.Message
