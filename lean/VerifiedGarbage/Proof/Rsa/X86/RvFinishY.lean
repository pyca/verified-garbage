module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.Math

/-! # Leaving Montgomery form and preserving the success mask -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

theorem finHead_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m k c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m k c st s) (one : A aOne = 1) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.finHead s fun t =>
      KS g s0 (upd (upd A mY (st.1 * 2 ^ (64 * g.n) % m)) mXm 1) (mXm :: liveSq) AW [wR]
        (upd (VS V k c st) sMask (b2n st.2.2)) (sMask :: slotsSq) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.finHead
  simp only [seqs]
  refine WP.seq (wp_movS (h.readSlot (by simp [slotsSq] : sOk ∈ slotsSq)) fun u U _ => ?_)
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine WP.mono (hu.storeSlot (d := sMask) (by decide) .eax) fun s1 ⟨h1, _, _⟩ => ?_
  have mask : (u.gpr .eax).toNat = b2n st.2.2 := by
    rw [U.gpr]
    simp only [VS, upd_self, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := VG.Proof.Rsa.b2n_le st.2.2; omega)
  rw [mask] at h1
  refine WP.mono (h1.copy_w (o := mXm) (a := aOne) (by decide)
    (by simp [liveSq, liveM]) (by decide) (by decide)) fun s2 ⟨h2, _, _⟩ => ?_
  simp only [upd_ne _ _ (by decide : aOne ≠ mY), one] at h2
  exact h2

theorem finY_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m k c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m k c st s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aOne = 1) (yl : st.1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.finY s fun t =>
      KS g s0 (upd A mY st.1) [mY, aN, aZ, aOne] (fun _ => 0) []
        (fun _ => b2n st.2.2) [sMask] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.finY
  refine WP.seq (WP.mono (finHead_ok h one) fun s2 h2 => ?_)
  have mr := h2.montReady (m := m) (by simp [liveSq, liveM]) (by simp [slotsSq])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mXm),
      upd_ne _ _ (by decide : mBase ≠ mY)] using value) bound
    (by simpa [VS, upd, sInv, sMask, sK, sCnt, sDone, sOk] using inverse)
  refine WP.mono (h2.mmul mr (o := mY) (a := mY) (b := mXm)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveSq]) (by simp)
    (by simpa only [upd_ne _ _ (by decide : mY ≠ mXm), upd_self] using
      Nat.mod_lt (st.1 * 2 ^ (64 * g.n)) (by omega : 0 < m))
    (by simpa only [upd_self] using hm) (by decide) (by decide)) fun t ⟨Y, ht, _, _, ylt, yv⟩ => ?_
  have y : Y = st.1 := by
    apply VG.Proof.Rsa.mont_inj (VG.Proof.Bignum.coprime_pow2 odd _) ylt yl
    simpa only [upd_ne _ _ (by decide : mY ≠ mXm), upd_self, Nat.mul_one, Nat.mod_mod] using yv
  rw [y] at ht
  refine ht.mono ?_ (by simp) ?_
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;>
      simp [liveSq, liveM, upd, mY, mXm, aN, aZ, aOne]
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact ⟨by simp, upd_self _ _ _⟩

end VG.Proof.Rsa.X86.Recover
