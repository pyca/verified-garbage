module
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Contract

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.CT
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Callee
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.Contract
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Contract
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Verified
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Whole.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.CT
meta import Mathlib.Tactic.NormNum.Pow
meta import Mathlib.Tactic.NormNum.Inv
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Env
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Last8
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Env
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Last8
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Verified
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.RoundsVL
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Last
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512.Xor
meta import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: by length

Untrusted: everything here is checked by Lean. `sealGatherBy` compares
`len` with `lim`, 961 or 1025 (`lenCmp_ok`, through `rax`) and runs, for less, the code that
gathers every slice and calls `seal` (`Whole`), else the code that calls
`seal_split` (`Gather/Fn.lean`). Each is proven from its own precondition,
which `gatherPre` (with the 1880 bytes of stack the second needs) gives in
the state after the comparison, which differs only in `rax` and the flags
(`CmpSame`, `whole_pre`, `pre_same`); their postconditions and public data
are the same functions of the arguments (`post_same`, `pub_same`). Both
runs of the constant-time proof take the same branch, `len` being public
(`sealGatherBy_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Impl.AesGcm.X86_64 (at_ imm)
open VG.Proof.AesGcm.X86_64 (imm_eq)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width sealGather sealGatherWhole sealGatherBy)

/-- The comparison of `len` with `lim`. -/
abbrev lenCmp (lim : Nat) : List Instr := [.mov .rax (.mem (at_ .rsp 16)), .alu .cmp .rax (imm lim)]

/-- A state that differs from `s` at most in `rax` and the flags. -/
structure CmpSame (s e : State) : Prop where
  gpr : ∀ r, r ≠ .rax → e.gpr r = s.gpr r
  mem : e.mem = s.mem
  rd : e.rd = s.rd
  wr : e.wr = s.wr
  mx : e.mxcsr = s.mxcsr

theorem lenCmp_ok {lim : Nat} (hlim : lim < 2 ^ 31) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8) :
    WP isa (.block (lenCmp lim)) s fun e => isa.eval .b e = some (decide (L s < lim)) ∧ CmpSame s e := by
  have il := imm_eq hlim
  apply WP.of_runBlock
  refine ⟨_, by xrun [lenCmp, hin, il], ?_⟩
  refine ⟨?_, ⟨fun r hr => by simp [gpr_setReg, gpr_arithFlags, hr], rfl, rfl, rfl, rfl⟩⟩
  show (State.cf _) = _
  simp only [cf_arithFlags, gpr_setReg, ↓reduceIte, BitVec.toNat_ofNat]
  show some (decide ((s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 16) 64).toNat < lim % 2 ^ 64)) = _
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

section
variable {s e : State} (h : CmpSame s e)
include h

theorem CmpSame.arg (i : Nat) : stackArg e i = stackArg s i := by
  show e.mem.readW (e.gpr .rsp + _) 64 = s.mem.readW (s.gpr .rsp + _) 64
  rw [h.mem, h.gpr .rsp (by decide)]

theorem CmpSame.argAddr (i : Nat) : stackArgAddr e i = stackArgAddr s i := by
  show e.gpr .rsp + _ = s.gpr .rsp + _
  rw [h.gpr .rsp (by decide)]

/-- The arguments, the regions and the slices' length, after the comparison. -/
theorem CmpSame.eqs : kR e = kR s ∧ nR e = nR s ∧ aR e = aR s ∧ dsR e = dsR s ∧ lsR e = lsR s ∧
    dR e = dR s ∧ tgR e = tgR s ∧ argR e = argR s ∧ retR e = retR s ∧ stkR e = stkR s ∧
    K e = K s ∧ Nn e = Nn s ∧ Ad e = Ad s ∧ AL e = AL s ∧ Dst e = Dst s ∧ L e = L s ∧ Tg e = Tg s ∧
    Src e = Src s ∧ Cnt e = Cnt s ∧ SP e = SP s ∧ gl e (Cnt e) = gl s (Cnt s) := by
  have hK : K e = K s := h.gpr .rdi (by decide)
  have hN : Nn e = Nn s := h.gpr .rsi (by decide)
  have hA : Ad e = Ad s := h.gpr .rdx (by decide)
  have hAL : AL e = AL s := congrArg BitVec.toNat (h.gpr .rcx (by decide))
  have hS : Src e = Src s := h.gpr .r8 (by decide)
  have hC : Cnt e = Cnt s := congrArg BitVec.toNat (h.gpr .r9 (by decide))
  have hSP : SP e = SP s := h.gpr .rsp (by decide)
  have hD : Dst e = Dst s := h.arg 0
  have hL : L e = L s := congrArg BitVec.toNat (h.arg 1)
  have hT : Tg e = Tg s := h.arg 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hK, hN, hA, hAL, hD, hL, hT, hS, hC, hSP, ?_⟩
  · show (⟨K e, 32⟩ : Region) = ⟨K s, 32⟩; rw [hK]
  · show (⟨Nn e, 12⟩ : Region) = ⟨Nn s, 12⟩; rw [hN]
  · show (⟨Ad e, AL e⟩ : Region) = ⟨Ad s, AL s⟩; rw [hA, hAL]
  · show (⟨Src e, Cnt e * 16⟩ : Region) = ⟨Src s, Cnt s * 16⟩; rw [hS, hC]
  · show Sig.listed 64 e.mem .u8 (Src e) (Cnt e) = Sig.listed 64 s.mem .u8 (Src s) (Cnt s); rw [h.mem, hS, hC]
  · show (⟨Dst e, L e⟩ : Region) = ⟨Dst s, L s⟩; rw [hD, hL]
  · show (⟨Tg e, 16⟩ : Region) = ⟨Tg s, 16⟩; rw [hT]
  · show (⟨stackArgAddr e 0, 24⟩ : Region) = ⟨stackArgAddr s 0, 24⟩; rw [h.argAddr]
  · show (⟨SP e, 8⟩ : Region) = ⟨SP s, 8⟩; rw [hSP]
  · show below (SP e) 1880 = below (SP s) 1880; rw [hSP]
  · show Spec.ChaCha20Poly1305.gatheredLen 64 e.mem (Src e) (Cnt e) = Spec.ChaCha20Poly1305.gatheredLen 64 s.mem (Src s) (Cnt s); rw [h.mem, hS, hC]

/-- `gatherPre`, after the comparison. -/
theorem pre_same (hs : gatherPre s) : gatherPre e := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅, e₁₆, e₁₇, e₁₈, e₁₉, e₂₀, e₂₁⟩ := h.eqs
  unfold gatherPre
  rw [h.rd, h.wr, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, e₁₁, e₁₂, e₁₃, e₁₄, e₁₅, e₁₆, e₁₇, e₁₈, e₂₁, e₁₉, e₂₀]
  exact hs

/-- `Whole`'s precondition, after the comparison. -/
theorem whole_pre (hs : gatherPre s) : Whole.gatherPre e := by
  have he := pre_same h hs
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, darg, rdd, rt, bk, bn, ba, bd, bt, bds, bls, ok, on, oa,
    od, ot, ods, ol, w₁, w₂, hgl, hpm, -, -⟩ := he
  have sub : (Whole.stkR e).Sub (stkR e) := by
    show Region.Sub (below (e.gpr .rsp) 1808) (below (e.gpr .rsp) 1880)
    simp only [below]
    rw [show e.gpr .rsp - BitVec.ofNat 64 1808 = e.gpr .rsp - BitVec.ofNat 64 1880 + BitVec.ofNat 64 72 by
      rw [Offset.sub_ofNat_eq _ (show 1808 ≤ 1880 by decide)]]
    exact Offset.sub_base _ (by decide)
  exact ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, dds, dls, darg, rdd, rt, bk.sub_left sub, bn.sub_left sub,
    ba.sub_left sub, bd.sub_left sub, bt.sub_left sub, bds.sub_left sub, fun r hr => (bls r hr).sub_left sub,
    ok, on, oa, od, ot, ods, ol, by have : 1880 ≤ (e.gpr .rsp).toNat := w₁; show 1808 ≤ (e.gpr .rsp).toNat; omega, w₂, hgl, hpm⟩

/-- What the code leaves, from `s` or from the state after the comparison. -/
theorem post_same {z : State} : gatherPost e z ↔ gatherPost s z := by
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  simp only [gatherPost, pt, K, Nn, Ad, AL, Src, Cnt, Dst, L, Tg, g .rdi (by decide), g .rsi (by decide),
    g .rdx (by decide), g .rcx (by decide), g .r8 (by decide), g .r9 (by decide), h.mem, h.arg]

theorem whole_post {z : State} : Whole.gatherPost e z ↔ gatherPost s z := by
  have g (r : Reg) (hr : r ≠ .rax) := h.gpr r hr
  simp only [Whole.gatherPost, gatherPost, Whole.pt, pt, Whole.K, K, Whole.Nn, Nn, Whole.Ad, Ad, Whole.AL, AL,
    Whole.Src, Src, Whole.Cnt, Cnt, Whole.Dst, Dst, Whole.L, L, Whole.Tg, Tg, g .rdi (by decide),
    g .rsi (by decide), g .rdx (by decide), g .rcx (by decide), g .r8 (by decide), g .r9 (by decide), h.mem,
    h.arg]

theorem abi_same {z : State} (hz : abiPreserved e z) : abiPreserved s z := by
  obtain ⟨h₁, h₂, h₃⟩ := hz
  refine ⟨fun r hr => (h₁ r hr).trans (h.gpr r fun e => by subst e; simp [calleeSaved] at hr), ?_, ?_⟩
  · rw [← h.mem, ← h.gpr .rsp (by decide)]; exact h₂
  · rw [← h.mx]; exact h₃

end

/-- Public data, after the comparison in both runs. -/
theorem pub_same {s₁ s₂ e₁ e₂ : State} (h₁ : CmpSame s₁ e₁) (h₂ : CmpSame s₂ e₂) (hp : gatherPub s₁ s₂) :
    gatherPub e₁ e₂ := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, hd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h₁.arg, h₂.arg]; exact a₀, by rw [h₁.arg, h₂.arg]; exact a₁,
    by rw [h₁.arg, h₂.arg]; exact a₂, fun i hi => ?_⟩
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₁
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₂
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₃
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₄
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₅
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₆
  · rw [h₁.gpr _ (by decide), h₂.gpr _ (by decide)]; exact q₇
  · simp only [Src, Cnt, h₁.gpr .r8 (by decide), h₁.gpr .r9 (by decide), h₁.mem, h₂.mem] at hi ⊢
    exact hd i hi

theorem whole_pub {s₁ s₂ e₁ e₂ : State} (h₁ : CmpSame s₁ e₁) (h₂ : CmpSame s₂ e₂) (hp : gatherPub s₁ s₂) :
    Whole.gatherPub e₁ e₂ :=
  pub_same h₁ h₂ hp

/-- `len`'s word is a stack argument. -/
theorem len_in {s : State} (hs : gatherPre s) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 16) 8 := by
  obtain ⟨rd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w₁, w₂, -⟩ := hs
  have w₂' : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 := w₂
  refine ⟨argR s, List.mem_append_left _ (by rw [rd]; simp), ?_⟩
  show (⟨s.gpr .rsp + BitVec.ofNat 64 8, 24⟩ : Region).Contains _ 8
  rw [show s.gpr .rsp + BitVec.ofNat 64 16 = s.gpr .rsp + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 by
    rw [Offset.add_ofNat_add_ofNat]]
  exact Offset.contains_base _ (by decide) (by decide)

theorem sealGatherBy_correct {lim : Nat} (hlim : lim < 2 ^ 31) (w : Width) (F : Whole.SealFn) (G : SealSplitFn)
    (s : State) (hs : gatherPre s) :
    ∃ t s', Exec isa (sealGatherBy lim w F.name F.code G.name G.code) s t s' ∧ abiPreserved s s' ∧
      gatherPost s s' := by
  have hw : WP isa (sealGatherBy lim w F.name F.code G.name G.code) s fun z =>
      abiPreserved s z ∧ gatherPost s z := by
    refine WP.seq (WP.mono (lenCmp_ok hlim s (len_in hs)) fun e ⟨hb, he⟩ => ?_)
    refine WP.ite (decide (L s < lim)) hb (fun _ => ?_) (fun _ => ?_)
    · exact WP.mono (Whole.sealGather_wp w F (whole_pre he hs)) fun z ⟨ha, hp⟩ =>
        ⟨abi_same he ha, (whole_post he).mp hp⟩
    · exact WP.mono (sealGather_wp w G (pre_same he hs)) fun z ⟨ha, hp⟩ =>
        ⟨abi_same he ha, (post_same he).mp hp⟩
  obtain ⟨t, s', he, hq⟩ := hw
  exact ⟨t, s', he, hq⟩

/-- Two runs of constant-time code from states it allows, with the same
public data. -/
theorem rel_of_ct {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (hc : ConstantTime isa pre pub c) {σ₁ σ₂ : State} (h₁ : pre σ₁) (h₂ : pre σ₂) (hp : pub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  intro a b t₁ t₂ a' b' ⟨ea, eb⟩ e₁ e₂
  subst ea eb
  exact ⟨hc _ _ _ _ _ _ h₁ h₂ hp e₁ e₂, trivial⟩

theorem sealGatherBy_ct {lim : Nat} (hlim : lim = 961 ∨ lim = 1025) (w : Width) (F : Whole.SealFn)
    (G : SealSplitFn) :
    ConstantTime isa gatherPre gatherPub (sealGatherBy lim w F.name F.code G.name G.code) := by
  have hl : lim < 2 ^ 31 := by omega
  have ht : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block (lenCmp lim)) h).isSome = true := by
    rcases hlim with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have hsp : σ₁.gpr .rsp = σ₂.gpr .rsp := hq.2.2.2.2.2.2.1
  have hL : L σ₂ = L σ₁ := congrArg BitVec.toNat hq.2.2.2.2.2.2.2.2.1.symm
  refine rel_seq (rel_regs [.rsp] (by simp [hsp]) ht)
    (lenCmp_ok hl σ₁ (len_in p₁)) (lenCmp_ok hl σ₂ (len_in p₂)) fun e₁ e₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ => ?_
  rw [hL] at b₂
  refine rel_ite b₁ b₂ (fun _ => ?_) (fun _ => ?_)
  · exact rel_of_ct (Whole.sealGather_ct w F) (whole_pre h₁ p₁) (whole_pre h₂ p₂) (whole_pub h₁ h₂ hq)
  · exact rel_of_ct (sealGather_ct w G) (pre_same h₁ p₁) (pre_same h₂ p₂) (pub_same h₁ h₂ hq)

theorem sealGatherBy_verified {lim : Nat} (hlim : lim = 961 ∨ lim = 1025) (w : Width) (F : Whole.SealFn)
    (G : SealSplitFn) :
    Verified X86_64.target (sealGatherBy lim w F.name F.code G.name G.code)
      (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) :=
  Verified.of_correct (k := gatherX86_64) (sealGatherBy_correct (by omega) w F G) (sealGatherBy_ct hlim w F G)
    gather_implies

/-- `Whole` alone, from `gatherPre` (with 1880 bytes of stack). -/
theorem sealGatherWhole_verified (w : Width) (F : Whole.SealFn) :
    Verified X86_64.target (sealGatherWhole w F.name F.code)
      (Spec.ChaCha20Poly1305.sealGatherContract X86_64.abi 1880) := by
  have same (s : State) : CmpSame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine Verified.of_correct (k := gatherX86_64) (fun s hs => ?_) (fun s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂ =>
    Whole.sealGather_ct w F s₁ s₂ t₁ t₂ s₁' s₂' (whole_pre (same _) p₁) (whole_pre (same _) p₂)
      (whole_pub (same _) (same _) hp) e₁ e₂) gather_implies
  obtain ⟨t, s', he, ha, hp⟩ := Whole.sealGather_wp w F (whole_pre (same s) hs)
  exact ⟨t, s', he, ha, (whole_post (same s)).mp hp⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
