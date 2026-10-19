module
public import VerifiedGarbage.Proof.AesOcb.X86_64.CTBase
public import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce

import VerifiedGarbage.Proof.AesOcb.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesOcb.X86_64.TagCT
import VerifiedGarbage.Proof.AesOcb.X86_64.Words
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Words
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Impl.AesCcm.X86_64
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesOcb.X86_64.Contract
import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0
import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Gcm.X86_64.Bits
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Spec.Ocb.Contract
meta import VerifiedGarbage.Impl.AesCcm.X86_64
meta import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
meta import VerifiedGarbage.Proof.AesCcm.Ctr
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Contract
meta import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0
meta import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Run
meta import VerifiedGarbage.Proof.Cmac.Dbl32
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
meta import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Bswap
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Gcm.X86_64.Bits
meta import VerifiedGarbage.Proof.Ocb.Spec
meta import VerifiedGarbage.Spec.Ccm.Contract
meta import VerifiedGarbage.Spec.Ocb.Contract

/-!
# AES-OCB on x86-64: the rest of the data is constant time

Untrusted: everything here is checked by Lean. The code around the call
passes the taint analysis from the public slots and the address and length
of the rest in `rbx` and `r12` (`rel_taintC`); the call of
`vg_aes_encrypt_blocks` has the same arguments in both runs (`callTmp_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append)

/-- A run before the rest: the public arguments, its address and length. -/
def RRun (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (P : Addr) (r : Nat) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.gpr .rbx = P ∧ s.gpr .r12 = BitVec.ofNat 64 r

theorem both_rr {K W SP : Addr} {R : Nat} {N A D : Addr} {nl n tl : Nat} {P : Addr} {r : Nat} {s₁ s₂ : State}
    (h₁ : RRun K W SP R N A D nl n tl P r s₁) (h₂ : RRun K W SP R N A D nl n tl P r s₂) :
    Both K W SP R N A D nl n tl [.rbx, .r12] [] s₁ s₂ :=
  ⟨h₁.1.env, h₂.1.env, h₁.1.sl, h₂.1.sl, h₁.1.wr, h₂.1.wr, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2], fun _ h => (nomatch h)⟩

/-- `Offset_*` and a copy of it at `W + tmpO`. -/
theorem restHead1_one {K W SP : Addr} (L : Lay K W SP) {N A D : Addr} {R nl n tl : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {P : Addr} {r : Nat} {s : State}
    (h : RRun K W SP R N A D nl n tl P r s) :
    WP isa (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) s (RRun K W SP R N A D nl n tl P r) := by
  have E := h.1.env
  obtain ⟨t₁, run₁, B₁⟩ := xor16_ok (s := s) (b := .r14) (a := 240) (d := ofsO) E.r15 E.r14 (by decide) (by decide)
    (E.perm.kR (by decide)) (E.perm.kR (by decide)) (E.perm.wW (by decide)) (E.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx] := by decide
  have E₁ : Env K W SP t₁ := E.keep (fun r hr => B₁.gpr r (nE r hr)) B₁.rd B₁.wr
  obtain ⟨t₂, run₂, B₂⟩ := copy16_ok (s := t₁) (a := ofsO) (d := tmpO) E₁.r15
    (E₁.perm.wR (by decide)) (E₁.perm.wR (by decide)) (E₁.perm.wW (by decide)) (E₁.perm.wW (by decide))
  have E₂ : Env K W SP t₂ := E₁.keep (fun r hr => B₂.gpr r (nE r hr)) B₂.rd B₂.wr
  refine WP.of_runBlock ⟨t₂, by rw [runBlock_append, run₁, Option.bind_some, run₂],
    h.1.step L hDW E₂ (by rw [B₂.wr, B₁.wr]) (((B₁.frame.sub fun r hr => ?_).trans (B₂.frame.sub fun r hr => ?_))),
    by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.1], by rw [B₂.gpr _ (by decide), B₁.gpr _ (by decide), h.2.2]⟩
  all_goals simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩

/-- The call on the block at `W + tmpO` keeps the callee-saved registers. -/
theorem callTmp_rr (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩) {P : Addr} {r : Nat} {s : State}
    (h : RRun K W SP R N A D nl n tl P r s) :
    WP isa (callBlocks (callees v).enc (oneBlock tmpO)) s (RRun K W SP R N A D nl n tl P r) :=
  WP.mono (callBlocks_ok (f := Spec.Aes.cipher) v.encOk v.encNosp v.encDepth L h.1.env hR h.1.sl.rounds
    (oneBlock_ok h.1.env.r15 tmpO (by decide)) (dstW L h.1.env.perm (d := tmpO) (n := 1) (by decide))) fun s' Q => by
    have E' := h.1.env.of_saved Q.saved Q.rd Q.wr
    refine ⟨h.1.step L hDW E' Q.wr (Q.frame.sub fun r hr => ?_), by rw [Q.saved _ (by decide), h.2.1],
      by rw [Q.saved _ (by decide), h.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
    · exact ⟨_, by simp, sub_wC (by decide) (by decide)⟩
    · rw [h.1.env.rsp]; exact ⟨_, by simp, fun _ h => h⟩

/-- `rest enc` in two runs. -/
theorem rest_rel (v : BlocksImpl) (enc : Bool) {K W SP : Addr} (L : Lay K W SP) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {N A D : Addr} {nl n tl : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    (hn : n ≤ 2 ^ 64) {P : Addr} {r : Nat} {Q : State → State → Prop}
    (hQ : ∀ s₁ s₂, Q s₁ s₂ → RRun K W SP R N A D nl n tl P r s₁ ∧ RRun K W SP R N A D nl n tl P r s₂) :
    RelCT isa Q (rest (callees v) enc) fun _ _ => True := by
  unfold rest
  have a := (rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ h => both_rr (hQ s₁ s₂ h).1 (hQ s₁ s₂ h).2)
    (c := .block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO)) ⟨_, by taint_decide⟩).wp
    (F₁ := RRun K W SP R N A D nl n tl P r) (F₂ := RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨restHead1_one L hDW (hQ s₁ s₂ h).1, restHead1_one L hDW (hQ s₁ s₂ h).2⟩
  have b := ((callTmp_rel v L hR hDW hn (P := fun s₁ s₂ => True ∧ RRun K W SP R N A D nl n tl P r s₁ ∧
    RRun K W SP R N A D nl n tl P r s₂) fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := RRun K W SP R N A D nl n tl P r) (F₂ := RRun K W SP R N A D nl n tl P r)
    fun s₁ s₂ h => ⟨callTmp_rr v L hR hDW h.2.1, callTmp_rr v L hR hDW h.2.2⟩)
  have c := rel_taintC [.rbx, .r12] [] hDW hn (fun s₁ s₂ (h : (One K W SP R N A D nl n tl s₁ ∧
      One K W SP R N A D nl n tl s₂) ∧ RRun K W SP R N A D nl n tl P r s₁ ∧ RRun K W SP R N A D nl n tl P r s₂) =>
    both_rr h.2.1 h.2.2) (c := if enc then .seq padCk xorPad else .seq xorPad padCk)
    (by cases enc <;> exact ⟨_, by taint_decide⟩)
  exact RelCT.seq a (RelCT.seq b c)

end VG.Proof.AesOcb.X86_64
