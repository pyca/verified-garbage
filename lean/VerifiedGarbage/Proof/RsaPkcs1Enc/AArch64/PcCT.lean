module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcCorrect
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.PcCorrect
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCT
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on AArch64: constant time

`contract` is the shared contract's precondition, `post`, and `encK`'s public
data with `pre` and its words. Two runs whose public data agree are related
by `Two PreOk` (`pre` in the layout of both): the pieces of
`vg_rsa_pkcs1_encrypt` (`EncCT`) carry it, the loads of `pre` and `pre_len`
are checked by the taint analysis, and the call is constant time for the
precomputed public operation's contract (`pdCallCT`), whose public data
(`pre`'s words with `e`) agree. Nothing after the call branches on its
result.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked PdOk pdCallCT ArgsEq)

/-- The shared contract, with `post` and `encK`'s public data with `pre`
and its words. -/
def contract (P : Nat) : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (P + 1088)).pre
  post := post P
  pub a s := (encK P).pub a s ∧ stackArg a 4 = stackArg s 4 ∧ stackArg a 5 = stackArg s 5 ∧
    Spec.Rsa.wordsAt a.mem (stackArg a 4) (stackArg a 5).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat

theorem callArgs_ct (S : Nat) :
    RelCT isa (Two PreOk S fun L g vv m₀ t => MsgInv L g vv m₀ L.ml.toNat t)
      (.block Impl.RsaPkcs1Enc.AArch64.Precomputed.callArgs) (Two PreOk S ReadyP) :=
  two [] (by taint_decide) (fun _ _ _ _ _ _ _ _ _ _ f₁ f₂ =>
    ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ _ _ _ hL _ hg hq h => callArgs_inv hL hq hg h

/-- Two layouts' `pre` from the two entry memories are the same. -/
theorem pre_eq {L : Lay} {m₁ m₂ : Mem} (q₁ : PreOk L m₁) (q₂ : PreOk L m₂) :
    preW L m₁ = preW L m₂ ∧ prlW L m₁ = prlW L m₂ := by
  have h := q₁.hx.symm.trans q₂.hx
  simp only [List.cons.injEq, Region.mk.injEq, and_true] at h
  exact ⟨h.1, BitVec.eq_of_toNat_eq (by omega)⟩

theorem args_ready {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : ReadyP L g vv m₀ t) : stackArg t 0 = L.scr ∧ stackArg t 1 = L.sl := by
  have hc := h.ctx
  refine ⟨?_, ?_⟩
  · show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [hc.sp]; exact hc.kept.scr
  · show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
    rw [hc.sp]; exact hc.kept.sl

theorem e_ready {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : ReadyP L g vv m₀ t) :
    Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat = Spec.Rsa.bytesAt m₀ L.e L.el.toNat := by
  rw [h.x4, h.x5]
  exact bytesAt_eq fun i hi => h.ctx.byte_ro (R := L.E) hL.oE.symm hL.eS hL.kE.symm (Nat.le_of_lt L.el.isLt) hi

theorem call_ct (c : PdChecked) :
    RelCT isa (Two PreOk c.stack ReadyP) (.call c.name c.code) (Two PreOk c.stack CalledF) :=
  two_wp (pdCallCT c fun t₁ t₂ ⟨e, hL, hP, hk, _, _, f₁, f₂, q₁, q₂⟩ => by
      obtain ⟨w, wl⟩ := pre_eq q₁ q₂
      obtain ⟨a0₁, a1₁⟩ := args_ready f₁
      obtain ⟨a0₂, a1₂⟩ := args_ready f₂
      refine ⟨hP ▸ pd_ok hL f₁, hP ▸ pd_ok hL f₂, ⟨f₁.ctx.sp.trans f₂.ctx.sp.symm, fun r hr => ?_,
        fun i hi => ?_⟩, ?_, by rw [e_ready hL f₁, e_ready hL f₂, hk.2.1]⟩
      · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [f₁.x0, f₂.x0]
        · rw [f₁.x1, f₂.x1]
        · rw [f₁.x2, f₂.x2, w]
        · rw [f₁.x3, f₂.x3, wl]
        · rw [f₁.x4, f₂.x4]
        · rw [f₁.x5, f₂.x5]
        · rw [f₁.x6, f₂.x6]
        · rw [f₁.x7, f₂.x7]
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [a0₁, a0₂]
        · rw [a1₁, a1₂]
      · have hx := hk.2.2 (PRE e.L e.m₁) (by rw [q₁.hx]; exact List.mem_singleton_self _)
        simp only [Nat.mul_div_cancel _ (by decide : 0 < 8)] at hx
        rw [f₁.x2, f₁.x3, f₂.x2, f₂.x3, pre_words hL f₁.ctx q₁, pre_words hL f₂.ctx q₂, hx, w, wl])
    fun _ _ _ _ _ hL hP _ _ h => WP.mono (pd_call c hL hP h) fun _ h => h.toCalledF

/-- Two calls whose public data agree, in the inner frame. -/
def EnteredP (P : Nat) (a b : State) : Prop :=
  ∃ s₁ s₂, (contract P).pre s₁ ∧ (contract P).pre s₂ ∧ (contract P).pub s₁ s₂ ∧ a = entered s₁ ∧
    b = entered s₂

theorem setup_ct (P : Nat) :
    RelCT isa (EnteredP P) (.block setup) (Two PreOk P fun L g vv m₀ t => PsInv L g vv m₀ 0 t) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, ⟨hp, a4, a5, hw⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, hn, he⟩ := hp
  have ht := (RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun _ hr => False.elim (by simp at hr)⟩) (by taint_decide)
    _ _ _ _ _ _ (by show (entered s₁).sp = (entered s₂).sp; rw [entered_sp P, entered_sp P]; simp only [lay, hsp]) e₁ e₂).1
  obtain ⟨L₁, r₁, w₁, p₁, -⟩ := pre_of h₁
  obtain ⟨L₂, r₂, w₂, p₂, -⟩ := pre_of h₂
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_okX L₁ r₁ w₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_okX L₂ r₂ w₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have e : layP P s₂ = layP P s₁ := by
    simp only [layP, lay, preX, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, hsp]
  refine ⟨ht, ⟨layP P s₁, s₁.gpr, s₂.gpr, s₁.v, s₂.v, s₁.mem, s₂.mem⟩, L₁, rfl, ⟨?_, ?_, ?_⟩,
    regsOf _ s₁, e ▸ regsOf _ s₂, setup_inv y₁.1 y₁.2, e ▸ setup_inv y₂.1 y₂.2, preOk_of p₁,
    e ▸ preOk_of p₂⟩
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat
    rw [hn, h2, h3]
  · show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat = Spec.Rsa.bytesAt s₂.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat
    rw [he, h4, h5]
  · intro R hR
    simp only [layP, lay, preX, List.mem_singleton] at hR
    subst hR
    show Spec.Rsa.wordsAt s₁.mem (stackArg s₁ 4) ((stackArg s₁ 5).toNat * 8 / 8) =
      Spec.Rsa.wordsAt s₂.mem (stackArg s₁ 4) ((stackArg s₁ 5).toNat * 8 / 8)
    rw [Nat.mul_div_cancel _ (by decide : 0 < 8), hw, a4, a5]

theorem code_constantTime (c : PdChecked) :
    ConstantTime isa (contract c.stack).pre (contract c.stack).pub
      (Impl.RsaPkcs1Enc.AArch64.Precomputed.code c.name c.code) := by
  refine RelCT.constantTime (RelCT.pushFrame (fun _ _ h => h.2.2.1.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [body_eq]
  refine ((setup_ct c.stack).seq ((psLoop_ct _).seq ((sep_ct _).seq ((msgCopy_ct _).seq
    ((callArgs_ct _).seq ((call_ct c).seq ((maskArgs_ct _).seq (maskLoop_ct _)))))))).mono ?_
    fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Enc.Pc
