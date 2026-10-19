module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
import VerifiedGarbage.Proof.Framework.Omega

/-! # Every failed search zeros the complete output and returns zero -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

theorem outputZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {len : Nat}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 len)
    (hl : 0 < len ∧ len ≤ 1024) (hw : (⟨W 6, len⟩ : Region) ∈ s.wr)
    (hb : (W 6).toNat + len ≤ 2 ^ 64) (ha : Apart F S ⟨W 6, len⟩) :
    WP isa Impl.Dsa.X86_64.Generation.outputZero s fun t =>
      t.gpr .rax = 0 ∧ Spec.Rsa.bytesAt t.mem (W 6) len = List.replicate len 0 ∧
      Frame [⟨F, frameBytes⟩, ⟨W 6, len⟩] s.mem t.mem ∧ Keep [.rdi, .r10, .rax, .r8] s t := by
  unfold Impl.Dsa.X86_64.Generation.outputZero
  refine WP.seq (WP.mono (zeroArgs_ok L R) fun u ⟨Lu, Ru, fu, ku⟩ => ?_)
  refine WP.mono (zeroOut_ok Lu Ru (by simp [upd]) (by simpa [upd] using hlen) hl.1 hl.2
    (by rw [ku.2.2]; exact hw) hb ha) fun t ⟨_, kt, _, hr, bytes, ft⟩ => ?_
  refine ⟨hr, bytes, ?_, (ku.trans kt).mono (by decide)⟩
  exact (fu.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp)).trans
    (ft.mono (by intro r h; rcases List.mem_singleton.mp h with rfl; simp))

end VG.Proof.Dsa.X86_64.Generation
