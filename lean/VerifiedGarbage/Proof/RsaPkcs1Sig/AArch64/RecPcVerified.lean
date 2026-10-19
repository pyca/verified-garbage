module

import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCorrect
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCT
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcTail
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify

/-!
# `vg_rsa_pkcs1_recover_precomputed` on AArch64: `Verified`

Constant time (`code_ct`): before the call as `vg_rsa_pkcs1_recover`
(`Rec.code_ct`); the call constant time for the precomputed public
operation's contract, whose public data are `pre`'s words with `e`
(`call_ct`); after it, whatever the call left, the blocks and loops are
checked by the taint analysis from the registers `Mid` fixes, and the one
branch, on whether `encode` succeeds, depends on `hash` and `n_len` alone
(`encode_isSome`), not on `EM₁`. With correctness (`code_correct`) and a
state meeting the precondition, the function is verified against the shared
contract (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.RecPc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 restore)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (lenCheck zeroArgs zeroKept encArgs cmpArgs)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two Pins two_taint two_post two_ite two_alloc PdChecked pdCallCT)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk fb sR kR frame_sub0 in_frame eval_zero' bytes_of_frame)
open VG.Proof.RsaPkcs1Sig.AArch64.Rec (PreR PubR Mid AtCall AtEnc AfterEnc encRes pins_sub pins_and)
open VG.Proof.RsaPkcs1Sig.AArch64.Pc (stackArgs_five words_of_frame)
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_strx eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)

/-! ## The public data -/

/-- The public data: `vg_rsa_pkcs1_recover`'s, and the precomputed values. -/
structure PubPR (a s : State) : Prop where
  r : PubR a s
  a3 : stackArg s 3 = stackArg a 3
  a4 : stackArg s 4 = stackArg a 4
  w : Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 3) (stackArg a 4).toNat

theorem PubPR.refl (s : State) : PubPR s s := ⟨PubR.refl s, rfl, rfl, rfl⟩

theorem pubPR_of {S : Nat} {s₁ s₂ : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi S).pub s₁ s₂) :
    PubPR s₁ s₂ := by
  sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4⟩ := h
  obtain ⟨hb, hq⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5, a0])
  have hw := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hq
  obtain ⟨hn, he, hg⟩ := Rec.leak_eq3 (by rw [bytesAt_length, bytesAt_length, h3])
    (by rw [bytesAt_length, bytesAt_length, h5]) hb
  refine ⟨⟨hsp.symm, fun r hr => ?_, h6.symm, fun i hi => ?_, hn.symm, he.symm, hg.symm⟩, a3.symm, a4.symm,
    hw.symm⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm]

/-! ## The points of the code -/

/-- An entry state with the anchor's public data. -/
def E (K : Nat) (a s : State) : Prop := PrePR K s ∧ PubPR a s

theorem E.rec {K : Nat} {a s : State} (h : E K a s) : Rec.E K a s := ⟨h.1.r, h.2.r⟩

/-- `J` at a point of the code, from an entry state with the anchor `a`'s
public data and a signature of `k` bytes. -/
def At (K : Nat) (J : State → State → Prop) (a t : State) : Prop :=
  ∃ s, E K a s ∧ stackArg s 0 = s.gpr .x3 ∧ J s t

theorem pins_mid {K : Nat} {J : State → State → Prop} (hJ : ∀ s t, J s t → Mid s t) :
    Pins (At K J) [.x19, .x20, .x21, .x22] := fun a t₁ t₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
  have m₁ := hJ _ _ j₁; have m₂ := hJ _ _ j₂
  refine ⟨by rw [m₁.sp, m₂.sp, h₁.rec.fb, h₂.rec.fb], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [m₁.x19, m₂.x19, h₁.rec.gpr (by decide), h₂.rec.gpr (by decide)]
  · rw [m₁.x20, m₂.x20, h₁.rec.gpr (by decide), h₂.rec.gpr (by decide)]
  · rw [m₁.x21, m₂.x21, h₁.rec.gpr (by decide), h₂.rec.gpr (by decide)]
  · rw [m₁.x22, m₂.x22, h₁.2.r.h6, h₂.2.r.h6]

/-- The hash function of an entry state. -/
def hS (s : State) : Spec.RsaPkcs1Sig.Hash :=
  (Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat).getD .md5

theorem hS_eq {K : Nat} {s : State} (hp : PreR K s) :
    Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some (hS s) ∧ (s.gpr .x1).toNat = (hS s).len := by
  obtain ⟨h, e, l⟩ := hp.hh
  unfold hS; rw [e]
  exact ⟨rfl, l⟩

theorem E.hash {K : Nat} {a s : State} (h : E K a s) : hS s = hS a := by
  unfold RecPc.hS; rw [h.2.r.h6]

/-! ## The call -/

theorem call_ct (c : PdChecked) :
    RelCT isa (Two (At c.stack AtCallP)) (.call c.name c.code) fun _ _ => True := by
  refine pdCallCT c fun t₁ t₂ ⟨a, ⟨s₁, h₁, g₁, c₁⟩, ⟨s₂, h₂, g₂, c₂⟩⟩ => ⟨pdOk_of c h₁.1 c₁ g₁,
    pdOk_of c h₂.1 c₂ g₂, ?_⟩
  obtain ⟨⟨u₁, b₁, o₁⟩, x2₁, x3₁⟩ := c₁
  obtain ⟨⟨u₂, b₂, o₂⟩, x2₂, x3₂⟩ := c₂
  have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], s₁.gpr r = s₂.gpr r :=
    fun r hr => (h₁.rec.gpr hr).trans (h₂.rec.gpr hr).symm
  have g : ∀ {t u : State}, Only [.x2, .x3] u t → ∀ r ∈ [Reg.x0, .x1, .x4, .x5, .x6, .x7],
      t.gpr r = u.gpr r := fun o r hr =>
    o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
                rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
  have sa : ∀ {t u : State} {s : State}, Only [.x2, .x3] u t → AtCall s u → ∀ i < 2,
      stackArg t i = stackArg s (i + 1) := fun o b i hi => by
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [← b.a0]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
    · rw [← b.a1]; simp only [stackArg, stackArgAddr, o.sp, o.mem]
  refine ⟨⟨?_, fun r hr => ?_, fun i hi => ?_⟩, ?_, ?_⟩
  · rw [o₁.sp, o₂.sp, b₁.sp, b₂.sp, h₁.rec.fb, h₂.rec.fb]
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g o₁ .x0 (by simp), g o₂ .x0 (by simp), b₁.x0, b₂.x0, h₁.rec.fb, h₂.rec.fb]
    · rw [g o₁ .x1 (by simp), g o₂ .x1 (by simp), b₁.x1, b₂.x1, e .x3 (by decide)]
    · rw [x2₁, x2₂, h₁.2.a3, h₂.2.a3]
    · rw [x3₁, x3₂, h₁.2.a4, h₂.2.a4]
    · rw [g o₁ .x4 (by simp), g o₂ .x4 (by simp), b₁.x4, b₂.x4, e .x4 (by decide)]
    · rw [g o₁ .x5 (by simp), g o₂ .x5 (by simp), b₁.x5, b₂.x5, e .x5 (by decide)]
    · rw [g o₁ .x6 (by simp), g o₂ .x6 (by simp), b₁.x6, b₂.x6, e .x7 (by decide)]
    · rw [g o₁ .x7 (by simp), g o₂ .x7 (by simp), b₁.x7, b₂.x7, e .x3 (by decide)]
  · rw [sa o₁ b₁ i hi, sa o₂ b₂ i hi, h₁.2.r.args (i + 1) (by omega), h₂.2.r.args (i + 1) (by omega)]
  · have fr : ∀ {s t u : State}, PrePR c.stack s → AtCall s u → Only [.x2, .x3] u t →
        Frame [kR c.stack s, sR s] s.mem t.mem := fun hp b o => by
      rw [o.mem]
      exact b.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩
    rw [x2₁, x2₂, x3₁, x3₂, words_of_frame (fr h₁.1 b₁ o₁) h₁.1.kp h₁.1.sp h₁.1.wp,
      words_of_frame (fr h₂.1 b₂ o₂) h₂.1.kp h₂.1.sp h₂.1.wp, h₁.2.w, h₂.2.w]
  · have b : ∀ {s t u : State}, PrePR c.stack s → AtCall s u → Only [.x2, .x3] u t →
        Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat =
          Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat := fun hp b o => by
      rw [g o .x4 (by simp), g o .x5 (by simp), b.x4, b.x5, o.mem]
      exact bytes_of_frame (b.mem.sub fun r hr => by
        rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub0 c.stack _⟩) hp.r.ke
        hp.r.es.symm (by have := hp.r.we; omega)
    rw [b h₁.1 b₁ o₁, b h₂.1 b₂ o₂, h₁.2.r.be, h₂.2.r.be]

/-! ## After the call -/

/-- `encode`'s status depends only on the length of the hash value. -/
theorem encode_isSome {h : Spec.RsaPkcs1Sig.Hash} {H H' : List Byte} {k : Nat} (hl : H.length = H'.length) :
    (Spec.RsaPkcs1Sig.encode h H k).isSome = (Spec.RsaPkcs1Sig.encode h H' k).isSome := by
  simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hl]
  split <;> rfl

/-- Before `encode`, `EM₁` holding some `k` bytes. -/
def JE (s u : State) : Prop := ∃ em : List Byte, em.length = (s.gpr .x3).toNat ∧ AtEnc s em u

/-- After `encode`. -/
def JF (s w : State) : Prop := ∃ em : List Byte, em.length = (s.gpr .x3).toNat ∧ AfterEnc s (hS s) em w

theorem head_ok {K : Nat} {s t : State} (hp : PreR K s) (hm : Mid s t) :
    WP isa (.block (([.addSp .x16 0, .str .x .x0 .x16 oSt] : List Instr) ++ encArgs)) t (JE s) := by
  rw [WP.block_append_iff]
  refine wp_addSp (by decide) fun t₁ o₁ e₁ => wp_strx (a := fb s + BitVec.ofNat 64 oSt) (by decide)
    (by rw [e₁, hm.sp, BitVec.add_zero]) (by rw [o₁.wr, hm.wr]; exact in_frame _ _ (by decide))
    fun t₂ m₂ => wp_nil ?_
  have mid₂ : Mid s t₂ := slot_write (hm.only o₁) (d := oSt) (by decide) (by decide) m₂
  exact WP.mono (Rec.encArgs_ok hp mid₂) fun u ⟨O, x8, x9, x10, x12, x11⟩ =>
    ⟨_, bytesAt_length _ _ _, mid₂.only O, x8, x9, x10, x12, x11, by rw [O.mem]⟩

/-- Whether `encode` fails, from the entry state. -/
def stat (s : State) : Bool :=
  (Spec.RsaPkcs1Sig.encode (hS s)
    (List.replicate ((s.gpr .x3).toNat - ((s.gpr .x3).toNat - (hS s).len)) 0) (s.gpr .x3).toNat).isNone

theorem eval_stat {s w : State} (h : JF s w) : isa.eval (.zero .x .x0) w = some (stat s) := by
  obtain ⟨em, hl, hw⟩ := h
  have hr := hw.res
  have hst : stat s = (encRes s (hS s) em).isNone := by
    unfold stat encRes
    rw [← Option.not_isSome, ← Option.not_isSome,
      encode_isSome (by rw [List.length_drop, hl, List.length_replicate])]
  rw [eval_zero', hst]
  cases he : encRes s (hS s) em with
  | none => rw [he] at hr; rw [hr]; rfl
  | some em' => rw [he] at hr; rw [hr.1]; rfl

theorem afterPub_ct {K : Nat} : RelCT isa (Two (At K fun s t => AfterCallP s t)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq (two_post (Ψ := At K JE)
    (two_taint [] (pins_sub (pins_mid fun _ _ h => h.toMid)) (by taint_decide))
    fun a t ⟨s, h, g, ht⟩ => WP.mono (head_ok h.1.r ht.toMid) fun u hu => ⟨s, h, g, hu⟩) ?_
  refine RelCT.seq (two_post (Ψ := At K JF)
    (Rec.encode_taint fun a u₁ u₂ ⟨s₁, h₁, _, em₁, _, j₁⟩ ⟨s₂, h₂, _, em₂, _, j₂⟩ =>
      ⟨by rw [j₁.mid.sp, j₂.mid.sp, h₁.rec.fb, h₂.rec.fb], fun r hr => ?_⟩)
    fun a u ⟨s, h, g, em, hl, hu⟩ => WP.mono (Rec.enc_ok h.1.r (hS_eq h.1.r).1 (hS_eq h.1.r).2 hu)
      fun w hw => ⟨s, h, g, em, hl, hw.1⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [j₁.x8, j₂.x8, h₁.rec.fb, h₂.rec.fb]
    · rw [j₁.x9, j₂.x9, h₁.rec.gpr (r := .x3) (by decide), h₂.rec.gpr (r := .x3) (by decide)]
    · rw [j₁.x10, j₂.x10, h₁.2.r.h6, h₂.2.r.h6]
    · rw [j₁.x11, j₂.x11, h₁.rec.valA, h₂.rec.valA]
    · rw [j₁.x12, j₂.x12, h₁.rec.gpr (r := .x1) (by decide), h₂.rec.gpr (r := .x1) (by decide)]
  unfold tail
  refine two_ite (fun a w₁ w₂ ⟨s₁, h₁, _, j₁⟩ ⟨s₂, h₂, _, j₂⟩ => by
      rw [eval_stat j₁, eval_stat j₂]
      unfold stat
      rw [h₁.hash, h₂.hash, h₁.rec.gpr (r := .x3) (by decide), h₂.rec.gpr (r := .x3) (by decide)])
    (Rec.zeroKept_taint (pins_and (pins_sub (pins_mid fun _ _ ⟨_, _, h⟩ => h.mid))))
    (two_taint [.x19, .x20, .x21] (pins_and (pins_sub (pins_mid fun _ _ ⟨_, _, h⟩ => h.mid))) (by taint_decide))

/-! ## The whole function -/

theorem pubArgs_taint {α : Type} {Φ : α → State → Prop} (h : Pins Φ []) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True :=
  two_taint [] h (by taint_decide)

theorem code_ct (c : PdChecked) :
    RelCT isa (Two (E c.stack)) (code c.name c.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := fun a t => ∃ s, E c.stack a s ∧ Only [.x8] s t ∧
      t.gpr .x8 = stackArg s 0 - s.gpr .x3)
    (Rec.lenCheck_taint fun _ _ _ h₁ h₂ => ⟨by rw [h₁.2.r.sp, h₂.2.r.sp], fun _ h => absurd h List.not_mem_nil⟩)
    fun a s h => WP.mono (Rec.lenCheck_ok h.1.r) fun t ht => ⟨s, h, ht⟩) ?_
  refine two_ite (fun a t₁ t₂ ⟨s₁, h₁, _, e₁⟩ ⟨s₂, h₂, _, e₂⟩ => by
      rw [Rec.eval_len e₁, Rec.eval_len e₂, h₁.2.r.args 0 (by decide), h₂.2.r.args 0 (by decide),
        h₁.rec.gpr (r := .x3) (by decide), h₂.rec.gpr (r := .x3) (by decide)])
    (Rec.zeroArgs_taint fun _ _ _ ⟨⟨s₁, h₁, o₁, _⟩, _⟩ ⟨⟨s₂, h₂, o₂, _⟩, _⟩ =>
      ⟨by rw [o₁.sp, o₂.sp, h₁.2.r.sp, h₂.2.r.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [o₁.get .x0, o₂.get .x0, h₁.rec.gpr (by decide), h₂.rec.gpr (by decide)]
        · rw [o₁.get .x1, o₂.get .x1, h₁.rec.gpr (by decide), h₂.rec.gpr (by decide)]⟩) ?_
  refine two_alloc (R := fun _ _ => True) ?_
  unfold body
  refine RelCT.seq (two_post (Ψ := At c.stack AtCallP)
    (pubArgs_taint fun _ _ _ ⟨u₁, ⟨⟨s₁, h₁, o₁, _⟩, _⟩, e₁⟩ ⟨u₂, ⟨⟨s₂, h₂, o₂, _⟩, _⟩, e₂⟩ =>
      ⟨by rw [e₁, e₂]; simp only [allocated, o₁.sp, o₂.sp, h₁.2.r.sp, h₂.2.r.sp],
        fun _ h => absurd h List.not_mem_nil⟩) fun a u ⟨t, ⟨⟨s, h, o, e⟩, hb⟩, hu⟩ => ?_) ?_
  · have hsig : stackArg s 0 = s.gpr .x3 := by
      rw [Rec.eval_len e] at hb; simpa using hb
    subst hu
    exact WP.mono (pubArgs_okP h.1 (by simp [allocated, o.sp]) (by simp [allocated, o.rd])
      (by simp [allocated, o.sp, o.wr]) (by simp [allocated, o.mem])
      (fun r hr => by simp only [allocated]; exact o.gpr r (by simpa using hr)) (fun r hr => o.vcs r hr))
      fun t ht => ⟨s, h, hsig, ht⟩
  refine RelCT.seq (two_post (Ψ := At c.stack fun s t => AfterCallP s t) (call_ct c) fun a t ⟨s, h, g, ht⟩ =>
    WP.mono (callP_ok c h.1 ht g) fun w hw => ⟨s, h, g, hw⟩) ?_
  refine RelCT.seq (two_post (Ψ := At c.stack Mid) afterPub_ct
    fun a t ⟨s, h, g, ht⟩ => WP.mono (afterPub_ok h.1.r (hS_eq h.1.r).1 (hS_eq h.1.r).2 ht)
      fun w hw => ⟨s, h, g, hw.1⟩) ?_
  exact Rec.restore_taint (pins_sub (pins_mid fun _ _ h => h))

theorem code_constantTime (c : PdChecked) :
    ConstantTime isa (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk c.stack)).pre
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk c.stack)).pub (code c.name c.code) :=
  RelCT.constantTime ((code_ct c).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨s₁, ⟨prePR_of h₁, PubPR.refl s₁⟩, prePR_of h₂, pubPR_of hp⟩) fun _ _ h => h)

/-! ## A state meeting the precondition -/

/-- `vg_rsa_pkcs1_recover`'s (`Rec.satState`), with 16 precomputed words at
`0x6000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 32 | .x2 => 0x1000 | .x3 => 64 | .x4 => 0x2000 | .x5 => 1 | .x6 => 3
    | .x7 => 0x4000 | _ => 0
  sp := 0x10000000000
  mem a := bif Nat.beq a.toNat 0x10000000010 then 0x20
    else bif Nat.beq a.toNat 0x10000000000 then 1 else bif Nat.beq a.toNat 0x1000000000A then 1
    else bif Nat.beq a.toNat 0x10000000011 then 4 else bif Nat.beq a.toNat 0x10000000019 then 0x60
    else bif Nat.beq a.toNat 0x10000000020 then 16 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x6000, 128⟩, ⟨0x10000000000, 40⟩]
  wr := [⟨0x5000, 32⟩, ⟨0x10000, 8448⟩]

theorem sat_args : stackArg satState 0 = 1 ∧ stackArg satState 1 = 0x10000 ∧ stackArg satState 2 = 1056 ∧
    stackArg satState 3 = 0x6000 ∧ stackArg satState 4 = 16 := by
  decide

theorem sat (K : Nat) (hK : K ≤ 2 ^ 20) :
    ∃ s, (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk K)).pre s := by
  refine ⟨satState, ?_⟩
  have e : stk K = (frameBytes + K - 1) + 1 := by unfold stk frameBytes; omega
  rw [e]
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq]
  obtain ⟨a0, a1, a2, a3, a4⟩ := sat_args
  have hS : frameBytes + K - 1 + 1 = 2128 + K := by unfold frameBytes; omega
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 (2128 + K)).toNat = 2 ^ 40 - (2128 + K) := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; omega
  have ha : stackArgAddr satState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, hS, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 (2128 + K), 2128 + K⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; omega)) (by dsimp only; rw [hkb]; omega)
      (by dsimp only; omega)
  refine ⟨by rw [hsp]; omega, by decide, by decide, by decide, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide),
    kd _ _ (by decide), kd _ _ (by decide), kd _ _ (by decide),
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; omega))
      (by dsimp only; rw [hkb]; omega) (by dsimp only; rw [hsp]; omega),
    by decide, by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide,
    by decide, ⟨.sha256, by decide, by decide⟩, by decide, by decide⟩

theorem code_verified (c : PdChecked) :
    Verified AArch64.target (code c.name c.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi (stk c.stack)) :=
  ⟨code_correct c, code_constantTime c, sat c.stack c.le⟩

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc
