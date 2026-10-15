module

public import VerifiedGarbage.Proof.AesSiv.X86_64.Enc
public import VerifiedGarbage.Proof.AesSiv.X86_64.Open
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesSiv.X86_64.Call
import VerifiedGarbage.Proof.AesSiv.X86_64.Common
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-SIV on x86-64: the whole of `vg_aes_siv_decrypt`

`Enc.lean`'s start of `decrypt`, followed by its end, `openTail_wp`. This is
a module of its own so that `Enc.lean` builds alongside `Open.lean`, and the
constant-time proofs alongside `Open.lean` too.
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.CmacAes.X86_64 (bytesAt_frame k0 UpdateImpl)

variable {s₀ : State} {C A P W D : Addr} {R N L : Nat} {T : Addr}

theorem decrypt_wp (v : UpdateImpl) (h : EPre s₀ C A P W D R N L) (hT : SivArg s₀ P W D T L) :
    WP isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s₀ fun s' => gprPreserved s₀ s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s₀.mem C R) (Spec.Siv.ctxCiph s₀.mem C R)
          (Spec.Siv.components 64 s₀.mem A N) (Spec.Aes.bytesAt s₀.mem T 16) (Spec.Aes.bytesAt s₀.mem P L) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have e := h.env
  have hRb : 16 * (R + 1) ≤ 240 := by rcases e.rounds with h | h | h <;> omega_arith
  obtain ⟨dC, dP, -, dR⟩ := h.sdone_dis
  have wC := one_out (e.c_w.sub_right (Region.sub_prefix (len := 16) (by decide)))
  refine WP.seq (WP.mono (encS2v_wp v h) fun s hs => WP.seq (WP.mono (sivIn_wp h hT hs)
    fun s₁ ⟨sp₁, sv₁, f₁, v₁⟩ => WP.mono (openTail_wp v e h.cp h.pw sp₁ sv₁)
    fun s' ⟨g', sp', f', out'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩))
  · by_cases hsp : r = .rsp
    · subst hsp; exact sp'
    · exact g' r (saved_all r hr hsp)
  · have c := Region.contains_self (s₀.gpr .rsp) 8
    rw [f'.readW c h.ret_end (by decide),
      f₁.readW c (one_out (e.ret_w.sub_right (Region.sub_prefix (by decide)))) (by decide),
      hs.frame.readW c dR (by decide)]
  · rw [ctxMac_frame f₁ wC hRb, ctxCiph_frame f₁ wC hRb,
      bytesAt_frame f₁ (one_out (e.p_w.symm.sub_left (Region.sub_prefix (by decide))).symm) (by have := e.lt; omega_arith),
      bytesAt_frame f₁ (one_out (e.d_w.sub_right (Region.sub_prefix (by decide)))) (by decide), v₁,
      ctxMac_frame hs.frame dC hRb, ctxCiph_frame hs.frame dC hRb,
      bytesAt_frame hs.frame dP (by have := e.lt; omega_arith), hs.acc] at out'
    rw [Spec.Siv.decryptWith_eq]
    exact out'

end VG.Proof.AesSiv.X86_64
