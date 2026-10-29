module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.PublicOutput

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.OutputBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskOutput
import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
/-! # FFDH on x86-64: generated-key outputs and status -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Status.lean`, which only this module imported.
section

/-! # FFDH on x86-64: encode success or a degenerate-public-value rejection -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem status_ok {s : State} {B : Addr} {Z : Nat} {c : Bool}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hF : word s.mem B (8 * sF) = BitVec.ofNat 64 c.toNat) :
    WP isa (.block status) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 (if c then 1 else 3) ∧ t.mem = s.mem) ∧ Keep [.rax, .rdx] s t := by
  refine WP.keep _ ?_ rfl
  unfold status
  xrun [State.ea, hdr, hd, hdrOff, hs.ld (d := 8 * sF) (by change 248 ≤ Z; omega), hF]
  cases c <;> rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem bit_eq_bool (P : Prop) [Decidable P] :
    bit P = BitVec.ofNat 64 (decide P).toNat := by
  by_cases h : P <;> simp only [bit, h, ↓reduceIte, decide_true, decide_false] <;> rfl

/-- Both outputs are masked when the generated public value is degenerate. -/
def PowerPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  t.gpr .rax = BitVec.ofNat 64 (if p.fl rb then 1 else 3) ∧ t.gpr .rdi = p.B ∧
    Spec.Rsa.bytesAt t.mem p.xp p.k = (if p.fl rb then p.cut rb else List.replicate p.k 0) ∧
    Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl rb then p.z rb else 0) p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem outputs_ok {p : GkP} {rb : List Byte} {s₀ s : State}
    (h : PublicPost p rb s₀ s) (ho : OutOk s p.B p.Z p.xp p.k)
    (hy : OutOk s p.B p.Z p.yp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hZ : 256 ≤ p.Z) (hk : p.k < 2 ^ 31) (hld : p.ld < p.k) (hlen : (p.cut rb).length = p.k) :
    WP isa (seqs [maskX, .block status]) s (PowerPost p rb s) := by
  obtain ⟨hY, hax, hd, hx, hs, hX, hXl, hK, _, _⟩ := h
  change WP isa (.seq maskX (.block status)) s _
  refine WP.seq (WP.mono (maskX_ok hs hd hZ hk hld hX hXl hK
    (c := decide (p.fl rb)) (hax.trans (bit_eq_bool (p.fl rb))) ho)
    fun u ⟨hm, hF, hd', hf, hs', k₁⟩ => ?_)
  have hxu := bytes_masked hx hlen hm
  have hYu : Spec.Rsa.bytesAt u.mem p.yp p.k = Spec.Rsa.bytesAt s.mem p.yp p.k := by
    change (List.range p.k).map _ = (List.range p.k).map _
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    exact hf _ (hy.sep i hi') (fun j hj => Ne.symm (ha j hj i hi'))
  refine WP.mono (status_ok (hs.congr k₁.2.2) hd' hZ hF) fun t ⟨⟨ha', hm'⟩, k₂⟩ => ?_
  refine ⟨?_, (k₂.gpr (by decide)).trans hd', ?_, ?_, ?_, ?_, (k₁.trans k₂).mono (by decide)⟩
  · simpa only [decide_eq_true_eq] using ha'
  · rw [hm', hxu]
    simp only [decide_eq_true_eq]
  · rw [hm', hYu, hY]
  · intro i hi
    rw [hm']; exact hs' i hi
  · intro a ha hx _
    rw [hm']
    exact hf a ha hx

end VG.Proof.Ffdh.X86_64.GenerateKey
