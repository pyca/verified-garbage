module

public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvSquareMasks
import VerifiedGarbage.Proof.Rsa.X86.RvSquareCount
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Bignum.Math

/-! # A masked squaring step of prime recovery -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n sqStep)

abbrev liveSq : List Nat := mY :: liveM
abbrev slotsSq : List Nat := [sInv, sCnt, sTc, sCand, sK, sDone, sOk]

def VS (V : Nat → Nat) (k c : Nat) (st : Nat × Bool × Bool) : Nat → Nat :=
  upd (upd (upd (upd V sK k) sCnt c) sDone (b2n st.2.1)) sOk (b2n st.2.2)

def SI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (m k c : Nat)
    (st : Nat × Bool × Bool) (s : State) : Prop :=
  KS g s0 (upd A mY (st.1 * 2 ^ (64 * g.n) % m)) liveSq AW [wR] (VS V k c st) slotsSq s

theorem sqBody_step {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m k c : Nat}
    {st : Nat × Bool × Bool} (h : SI g s0 A AW V m k c st s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1) (hm : 1 < m)
    (one : A aO = 2 ^ (64 * g.n) % m) (neg : A aNg = m - 2 ^ (64 * g.n) % m)
    (hk : k + 1 < 2 ^ 31) (ht : V sTc < 2 ^ 31) (lo : 1 ≤ c) (hi : c < 2 ^ 32) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.sqBody s fun t => SI g s0 A AW V m (k + 1) (c - 1)
      (sqStep m (V sTc) k st) t ∧ t.zf = some (decide (c - 1 = 0)) := by
  have positive : 0 < m := by omega
  have cop := VG.Proof.Bignum.coprime_pow2 odd (64 * g.n)
  have mr := h.montReady (m := m) (by simp [liveSq, liveM]) (by simp [slotsSq])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY)] using value) bound
    (by simpa [VS, upd, sInv, sK, sCnt, sDone, sOk] using inverse)
  unfold VG.Impl.Rsa.X86.RecoverRt.sqBody VG.Impl.Rsa.X86.RecoverRt.sqTail VG.Impl.Rsa.X86.RecoverRt.eqAt
  simp only [seqs]
  refine WP.seq (WP.mono (h.mmul mr (o := mX) (a := mY) (b := mY)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveSq]) (by simp [liveSq])
    (by simpa only [upd_self] using Nat.mod_lt (st.1 * 2 ^ (64 * g.n)) positive)
    (by simpa only [upd_self] using Nat.mod_lt (st.1 * 2 ^ (64 * g.n)) positive)
    (by decide) (by decide)) fun s1 ⟨X, h1, _, _, xlt, xv⟩ => ?_)
  have square : X = st.1 * st.1 % m * 2 ^ (64 * g.n) % m :=
    VG.Proof.Rsa.sq_mont cop (by rw [upd_self]) xlt xv
  rw [square] at h1
  refine WP.seq (WP.mono (h1.eqS_w (d := sE1) (a := mX) (b := aO)
    (by simp) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.eqS_w (d := sE2) (a := mX) (b := aNg)
    (by simp) (by simp [liveSq, liveM]) (by decide) (by decide) (by decide) (by decide))
    fun s3 ⟨h3, _⟩ => ?_)
  have eo : (if st.1 * st.1 % m * 2 ^ (64 * g.n) % m = A aO then 1 else 0) =
      b2n (decide (st.1 * st.1 % m = 1)) := by
    simp only [one, VG.Proof.Rsa.eq_one_mont cop hm (Nat.mod_lt _ positive) rfl]
    simp [b2n]
  have en : (if st.1 * st.1 % m * 2 ^ (64 * g.n) % m = A aNg then 1 else 0) =
      b2n (decide (st.1 * st.1 % m = m - 1)) := by
    simp only [neg, VG.Proof.Rsa.eq_neg_mont cop hm (Nat.mod_lt _ positive) rfl]
    simp [b2n]
  simp only [upd_self, upd_ne _ _ (by decide : aO ≠ mX), upd_ne _ _ (by decide : aO ≠ mY),
    upd_ne _ _ (by decide : aNg ≠ mX), upd_ne _ _ (by decide : aNg ≠ mY), eo, en] at h3
  refine WP.seq (WP.mono (sqMasks_ok h3 (k := k) (t := V sTc)
    (dn := st.2.1) (ok := st.2.2) (e1 := decide (st.1 * st.1 % m = 1))
    (e2 := decide (st.1 * st.1 % m = m - 1))
    (by simp [slotsSq]) (by simp [slotsSq]) (by simp [slotsSq]) (by simp [slotsSq])
    (by simp) (by simp) hk ht
    (by simp [VS, upd, sK, sCnt, sDone, sOk, sE1, sE2])
    (by simp [VS, upd, sTc, sK, sCnt, sDone, sOk, sE1, sE2])
    (by simp [VS, upd, sDone, sOk, sE1, sE2])
    (by simp [VS, upd, sOk, sE1, sE2])
    (by simp [upd, sE1, sE2]) (by simp [upd])) fun s4 h4 => ?_)
  refine WP.seq (WP.mono (h4.copy_w (o := aU) (a := mY) (by decide) (by simp [liveSq])
    (by decide) (by decide)) fun s5 ⟨h5, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h5.sel_w (o := mY) (a := aU) (b := mX) (sl := sLive)
    (by decide) (by simp) (by simp) (by simp)
    (by rw [upd_self]; exact VG.Proof.Rsa.b2n_le _) (.inl (by decide)) (by decide)) fun s6 ⟨h6, _⟩ => ?_)
  refine WP.mono (h6.sqNext_ok (by simp [slotsSq]) (by simp [slotsSq])
    (by simpa [VS, upd, sK, sLive, sDone, sOk, sE1, sE2, sCnt] using (show k + 1 < 2 ^ 32 by omega))
    (by simpa [VS, upd, sCnt, sK, sLive, sDone, sOk, sE1, sE2] using lo)
    (by simpa [VS, upd, sCnt, sK, sLive, sDone, sOk, sE1, sE2] using hi)) fun t ⟨hout, zt⟩ => ?_
  refine ⟨hout.mono ?_ (by simp) ?_, ?_⟩
  · intro j hj
    refine ⟨by simp [hj], ?_⟩
    simp only [liveSq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [upd_self, upd_ne _ _ (by decide : mX ≠ aU),
        upd_ne _ _ (by decide : mY ≠ mX)]
      simp only [sqStep]
      cases (!st.2.1 && decide (k < V sTc) && !decide (st.1 * st.1 % m = 1) &&
        !(decide (st.1 * st.1 % m = m - 1) || decide (k + 1 = V sTc))) <;>
        simp [b2n]
    all_goals simp [upd, mY, mX, aU, aNg, aO, mR2, mBase, aOne, aZ, aN]
  · intro d hd
    refine ⟨by simp [hd], ?_⟩
    simp only [slotsSq, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [VS, upd, sqStep, sInv, sCnt, sTc, sCand, sK, sDone, sOk, sLive, sE1, sE2]
  · simpa [VS, upd, sCnt, sK, sLive, sDone, sOk, sE1, sE2] using zt

end VG.Proof.Rsa.X86.Recover
