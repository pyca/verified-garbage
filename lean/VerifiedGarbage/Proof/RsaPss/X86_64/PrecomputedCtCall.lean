module
public import VerifiedGarbage.Impl.RsaPss.X86_64.Precomputed
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCtCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCall

import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs
meta import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedArgs
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.RsaPss.Encoding
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.SignCases
import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.DirectLen
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT
import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirectCT
import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedBody
import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedContract
import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedFront
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBackCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCt
import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
meta import VerifiedGarbage.Proof.Rsa.X86_64.ExpCheck
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
meta import VerifiedGarbage.Proof.RsaPss.Encoding
meta import VerifiedGarbage.Proof.RsaPss.MgfBytes
meta import VerifiedGarbage.Proof.RsaPss.SignCases
meta import VerifiedGarbage.Proof.RsaPss.X86_64.BufferCopy
meta import VerifiedGarbage.Proof.RsaPss.X86_64.DirectLen
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.FixedSaltCopy
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirect
meta import VerifiedGarbage.Proof.RsaPss.X86_64.MgfDirectCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedBody
meta import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedContract
meta import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCorrect
meta import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedFront
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBack
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SaltBackCT
meta import VerifiedGarbage.Proof.RsaPss.X86_64.SignFail
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyBody
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCt
meta import VerifiedGarbage.Proof.Sha256.StateMem

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Pc

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {G : Spec.Mgf1.Hash} {H : Hash}

def extra (G : Spec.Mgf1.Hash) (a s : State) : Prop :=
  Pre G a ∧ Pre G s ∧ stackArg s 5 = stackArg a 5 ∧ stackArg s 6 = stackArg a 6 ∧
    Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat

abbrev Sib := VSib (extra := extra G) G
abbrev At := VAt (extra := extra G) G

variable (H) in
/-- Before the call. -/
def JC (s t : State) : Prop :=
  VS H s t KM [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrR s) s.mem t.mem ∧
    (∀ i < 4, word t.mem (fb s) (8 * i) = vArg s i) ∧ t.gpr .rdi = off (stackArg s 3) oEm ∧
    t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 5 ∧ t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .rdx ∧
    t.gpr .r9 = s.gpr .rcx ∧ H.D + 2 ≤ veml s

theorem dbPub_ct : RelCT isa (Two fun a t => At (G := G) (J7 H) a t ∧ isa.eval .b t = some false)
    (.seq (.block dbSlots) (.block Impl.RsaPss.X86_64.Precomputed.pubArgs)) (Two (At (G := G) (JC H))) := by
  refine two_post (vtwo (G := G) (H := H) [17, 18, 19, 20, 21, 22, 26, 38] [.rax]
    (fun a => [(.rax, BitVec.ofNat 64 (veml a - (H.D + 2)))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (fun k hk => by
      simp only [K5, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; omega) _ (fun p hp => by
        rw [List.mem_singleton.mp hp, ← S.veml]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) (by taint_decide)) fun a t ⟨⟨s, S, h⟩, _⟩ => ?_
  obtain ⟨v, hrd, hM, hax, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.2.2.2.2.1
  have L := v.L
  have w : ∀ k ∈ K5, W k = vw H s k := hw
  refine WP.seq (WP.mono (WP.keepIn (by safe_by [dbSlots]) (by exact Nat.zero_le 8)
    (dbSlots_ok L R (w 26 (by decide)) hax)) fun u1 ⟨⟨L1, k1, R1⟩, f1⟩ => ?_)
  have hM1 := vframe_keep hp.toVPre v.wr L.rsp hM f1
  have g1 : ∀ j, j ≠ 23 → j ≠ 24 → upd (upd W 24 (BitVec.ofNat 64 (veml s - (H.D + 2) + 1))) 23
      (off (stackArg s 3) (oEm + vlo s)) j = W j := fun j h23 h24 => by simp [upd, h23, h24]
  refine WP.mono (WP.keepIn (by decide) (by exact Nat.zero_le 8)
    (args_ok hp L1 R1 (k1.2.2.trans v.wr) (k1.2.1.trans hrd) hM1 (by rw [g1 17 (by decide) (by decide)]; exact w 17 (by decide))
      (by rw [g1 18 (by decide) (by decide)]; exact w 18 (by decide))
      (by rw [g1 19 (by decide) (by decide)]; exact w 19 (by decide))
      (by rw [g1 20 (by decide) (by decide)]; exact w 20 (by decide))
      (by rw [g1 22 (by decide) (by decide)]; exact w 22 (by decide))
      (by rw [g1 38 (by decide) (by decide)]; exact w 38 (by decide))))
    fun u2 ⟨⟨k2, L2, ⟨W2, R2, hW2a, hW2b⟩, h2di, h2si, h2dx, h2cx, h2r8, h2r9⟩, f2⟩ => ?_
  have hw1 : u1.wr = frR s :: s.wr := k1.2.2.trans v.wr
  refine ⟨s, S, ⟨L2, k2.2.2.trans hw1, ⟨V, W2, R2, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
    (k2.2.1.trans k1.2.1).trans hrd, vframe_keep hp.toVPre hw1 L1.rsp hM1 f2,
    fun i hi => (R2.fr i (by unfold nW frameBytes; omega)).trans (hW2a i hi), h2di, h2si, h2dx, h2cx, h2r8, h2r9,
    hok⟩
  have h4 : 4 ≤ k := by simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  rw [hW2b k (km_lt hk) h4]
  by_cases h23 : k = 23
  · subst h23; simp [upd, vw]
  by_cases h24 : k = 24
  · subst h24
    simp only [upd, Nat.reduceEqDiff, ite_false, ite_true, vw, vdb]
    congr 1; omega
  rw [g1 k h23 h24]; exact w k (km_k5 hk h23 h24)

theorem entry_pre {a s t : State} (S : Sib (G := G) a s) (hst : t.gpr .rsp = fb s)
    (hM : Frame (vwrR s) s.mem t.mem) :
    Spec.Rsa.wordsAt t.callEntry.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat := by
  have fE : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, hst]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))
  have fSE : Frame (vwrR s) s.mem t.callEntry.mem := hM.trans (fE.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vret_sub s⟩)
  exact (pre_words S.2.2.2.2.1 fSE).trans S.2.2.2.2.2.2.2

theorem call_pub {a s₁ s₂ t₁ t₂ : State} (S₁ : Sib (G := G) a s₁) (h₁ : JC H s₁ t₁) (S₂ : Sib (G := G) a s₂)
    (h₂ : JC H s₂ t₂) :
    pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (vWr s₁)) (t₂.callEntry.withRegions (callRd s₂) (vWr s₂)) := by
  obtain ⟨v₁, -, hM₁, ha₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, -⟩ := h₁
  obtain ⟨v₂, -, hM₂, ha₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, -⟩ := h₂
  have p₁ := S₁.ps
  have p₂ := S₂.ps
  have hE₁ : ∀ i < 4, stackArg (t₁.callEntry.withRegions (callRd s₁) (vWr s₁)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₁ v₁.L.rsp _ _ hi).trans (ha₁ i hi)).trans (vArg_sib S₁)
  have hE₂ : ∀ i < 4, stackArg (t₂.callEntry.withRegions (callRd s₂) (vWr s₂)) i = vArg a i :=
    fun i hi => ((vstackArg_call p₂ v₂.L.rsp _ _ hi).trans (ha₂ i hi)).trans (vArg_sib S₂)
  have bn₁ := entry_pre S₁ v₁.L.rsp hM₁
  have bn₂ := entry_pre S₂ v₂.L.rsp hM₂
  have be₁ := entry_e S₁ v₁.L.rsp hM₁
  have be₂ := entry_e S₂ v₂.L.rsp hM₂
  rw [show pdChkContract.pub = pdContract.pub from rfl]
  have g : ∀ (t : State) (rd wr : List Region) {r : Reg}, r ≠ .rsp → (t.callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun t rd wr r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  refine ⟨fun r hr => ?_, by rw [hE₁ 0 (by decide), hE₂ 0 (by decide)], by rw [hE₁ 1 (by decide), hE₂ 1 (by decide)],
    by rw [hE₁ 2 (by decide), hE₂ 2 (by decide)], by rw [hE₁ 3 (by decide), hE₂ 3 (by decide)], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), di₁, di₂, S₁.arg3, S₂.arg3]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), si₁, si₂, S₁.gpr (r := .rsi) (by decide),
        S₂.gpr (r := .rsi) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, S₁.2.2.2.2.2.1, S₂.2.2.2.2.2.1]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), cx₁, cx₂, S₁.2.2.2.2.2.2.1, S₂.2.2.2.2.2.2.1]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, S₁.gpr (r := .rdx) (by decide),
        S₂.gpr (r := .rdx) (by decide)]
    · rw [g _ _ _ (by decide), g _ _ _ (by decide), r9₁, r9₂, S₁.gpr (r := .rcx) (by decide),
        S₂.gpr (r := .rcx) (by decide)]
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, v₁.L.rsp,
        v₂.L.rsp, S₁.fb, S₂.fb]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), dx₁, dx₂, cx₁, cx₂, bn₁, bn₂]
  · rw [State.withRegions_mem, State.withRegions_mem, g _ _ _ (by decide), g _ _ _ (by decide),
      g _ _ _ (by decide), g _ _ _ (by decide), r8₁, r8₂, r9₁, r9₂, be₁, be₂]

theorem call_ct (impl : PublicImpl) : RelCT isa (Two (At (G := G) (JC H))) (.call impl.name impl.code) (Two (At (G := G) (JM H fun _ _ _ => True))) := by
  refine two_post (RelCT.callEx (k := pdChkContract) impl.ok impl.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, h₁⟩, ⟨s₂, S₂, h₂⟩⟩ => ?_)
    fun a t ⟨s, S, h⟩ => ?_
  · obtain ⟨c₁, w₁⟩ := call_covers S₁.2.2.2.2.1 h₁.2.1 h₁.1.wr
    obtain ⟨c₂, w₂⟩ := call_covers S₂.2.2.2.2.1 h₂.2.1 h₂.1.wr
    exact ⟨_, _, _, _, call_pre S₁.2.2.2.2.1 h₁.1.L.rsp h₁.2.2.2.1 h₁.2.2.2.2.1 h₁.2.2.2.2.2.1 h₁.2.2.2.2.2.2.1
      h₁.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.1 h₁.2.2.2.2.2.2.2.2.2.1,
      call_pre S₂.2.2.2.2.1 h₂.1.L.rsp h₂.2.2.2.1 h₂.2.2.2.2.1 h₂.2.2.2.2.2.1 h₂.2.2.2.2.2.2.1
      h₂.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.1 h₂.2.2.2.2.2.2.2.2.2.1, call_pub S₁ h₁ S₂ h₂, c₁, w₁, c₂, w₂,
      by rw [h₁.1.L.rsp, h₂.1.L.rsp, S₁.fb, S₂.fb]⟩
  · obtain ⟨v, hrd, hM, ha, di, si, dx, cx, r8, r9, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have hp := S.2.2.2.2.1
    have hk2 := hp.k2
    refine WP.mono (call_ok impl hp v.L.rsp hrd v.wr hM ha di si dx cx r8 r9)
      fun u ⟨rd', wr', cs', _, _, hk', _⟩ => ?_
    have hEm : oEm + (s.gpr .rsi).toNat ≤ oRsa := by unfold oEm oRsa; omega
    have R' := R.of_em v.L.geo hEm hk'
    exact ⟨s, S, ⟨v.L.of_rep' R R' rfl (cs' .rsp (by decide)) wr', wr'.trans v.wr, ⟨_, W, R', hw, trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, hok⟩


end VG.Proof.RsaPss.X86_64.Pc
