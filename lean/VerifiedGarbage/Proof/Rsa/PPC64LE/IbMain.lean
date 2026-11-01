module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbBatch
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The batched inverse on PPC64LE: the batches

`loop_ok`: `3 (n + 1)` batches from the start of the inversion, counted in
`r10`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S)
open VG.Proof.Rsa.Divstep (oddInput)

/-- After `k` batches. -/
def LoopAt (s₀ : State) (B : Addr) (Z w N n p iv x : Nat) (k : Nat) (t : State) : Prop :=
  Ctx t B Z w N n (3 * (n + 1) - k) ∧ StateAt t B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) k) ∧
    KeyWorkspace.Keep B w [aF, aG, aA, aB, aT1, aT2, aT3, aW] [] s₀.mem t.mem ∧ Keep (.r10 :: kRegs) s₀ t

theorem loop_ok {s : State} {B : Addr} {Z w N n p iv x : Nat} (hN : N ≤ 256)
    (h : Ctx s B Z w N n (3 * (n + 1)))
    (hst : StateAt s B w n p iv (Divstep.W32.invRun 30 p iv (oddInput p x) 0))
    (odd : p % 2 = 1) (large : 1 < p) (hinv : (p * iv + 1) % 2 ^ 32 = 0)
    (pc : p < 2 ^ (32 * n)) (xc : x < 2 ^ (32 * n)) :
    WP isa (.loop batch (.nonzero .d .r3)) s (LoopAt s B Z w N n p iv x (3 * (n + 1))) := by
  have hn := h.nw
  have hw := h.ws.wle
  have cap : p + x < 2 ^ (32 * n + 1) := by rw [Nat.pow_succ]; omega
  have ox : oddInput p x ≤ p + x := by unfold oddInput; split <;> omega
  refine count_loop (by omega) (LoopAt s B Z w N n p iv x) (fun k hk t ⟨Ht, It, Kt, kt⟩ => ?_)
    ⟨by simpa using h, hst, KeyWorkspace.Keep.refl _ _ _ _ _, Keep.refl _ _⟩
  obtain ⟨bd, fo, fb, gb, a0, a1, b0, b1⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := p + x)
    odd large hinv (by omega) ox k
  rw [show 3 * (n + 1) - k = (3 * (n + 1) - k - 1) + 1 by omega] at Ht
  refine WP.mono (batch_ok Ht It hN (cap := p + x) (by push_cast at bd ⊢; omega) fo fb gb cap a0 a1 b0 b1 pc
    (by omega) hinv) fun u ⟨Hu, Iu, ru, Ku, ku⟩ => ?_
  rw [show 3 * (n + 1) - k - 1 = 3 * (n + 1) - (k + 1) by omega] at Hu
  exact ⟨⟨Hu, Iu, Kt.trans Ku, kt.trans' ku⟩, by rw [ru]; omega⟩

end VG.Proof.Rsa.PPC64LE.InvBatch
