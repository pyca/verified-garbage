module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero

/-!
# DSA key derivation on PPC64LE: a domain that fails the checks

`dzero_ok`: `out`'s `3 p_len + 2 q_len` octets (`out` in `r26`) are zeroed,
by `Sign/Zero.lean`'s loop, and `r3 := 0`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

/-- The registers `Derive.zeroOut` writes. -/
def dzeroRegs : List Reg := [.r0, .r3, .r16, .r17]

theorem dzero_ok {s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hr : Regs s L key x out)
    (ho : Scr s out (3 * L.pl + 2 * L.ql)) :
    WP isa Derive.zeroOut s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) = List.replicate (3 * L.pl + 2 * L.ql) 0 ∧
        Outside out 0 (3 * L.pl + 2 * L.ql) s.mem t.mem ∧ t.gpr .r3 = 0) ∧ Keep dzeroRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have hno := ho.nowrap
  unfold Derive.zeroOut
  refine WP.seq (WP.mono (WP.keep [.r16, .r17, .r0] (Q := fun u => u.gpr .r0 = 0 ∧ u.gpr .r16 = off out 0 ∧
      u.gpr .r17 = BitVec.ofNat 64 (3 * L.pl + 2 * L.ql) ∧ u.mem = s.mem) (by
      unfold getP getQ
      prun [hr.r26, Regs.p_eq hr, Regs.q_eq hr, BitVec.add_zero]
      exact ⟨rfl, by simp only [BitVec.ofNat_add_ofNat]; congr 1; omega⟩) (by decide))
    fun s₁ ⟨⟨a0, a16, a17, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok (N := 3 * L.pl + 2 * L.ql) (by omega) (by omega) (ho.congr k1.wr) a0 a16 a17)
    fun t ⟨⟨tz, tout⟩, tk⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = 0 ∧ u.mem = t.mem) (by prun []; rfl) (by decide))
    fun u ⟨⟨u3, mu⟩, ku⟩ => ⟨⟨by rw [mu]; exact tz, by rw [mu, ← m1]; exact tout, u3⟩,
      ((k1.trans tk).trans ku).mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
