module

import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Context
meta import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract
meta import VerifiedGarbage.Proof.MillerRabin.Representation
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The callable round keeps candidates and witnesses secret -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.MillerRabin.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64

private def coreSpace (s : State) : VG.Proof.Bignum.AArch64.Ws :=
  ⟨s.gpr .x0, (s.gpr .x1).toNat * 8, Proof.Rsa.Mont.wOf s.mem (s.gpr .x0)⟩

private theorem initial_core {s : State} (h : roundPre s) : CorePre (coreSpace s) s := by
  obtain ⟨h4, h128, hEZ, bm, hc, hE, hodd, h3, hx⟩ := initial_ctx h
  obtain ⟨b, -, hb⟩ := witness_exists (coprime_pow2 hodd _) hx
  refine ⟨h4, h128, hEZ, _, bm, b, hc, hE, hodd, by omega_arith, ?_⟩
  simpa only [coreSpace, VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb

private theorem core_base (M : Mont) (L : VG.Proof.Bignum.AArch64.Ws) (s : State)
    (h : CorePre L s) :
    WP isa (seqs (preparedRound M.mm)) s fun t => t.gpr .x0 = L.B := by
  obtain ⟨h4, h128, hEZ, c, bm, b, hc, hE, hodd, h1, hX⟩ := h
  have hfit : mrE c < 16 ^ (16 * L.w) := by
    change mrE c < (2 ^ 4) ^ (16 * L.w)
    rw [← Nat.pow_mul,
      show 4 * (16 * L.w) = 64 * L.w by omega_arith]
    have hn : c < 2 ^ (64 * L.w) := hc.n ▸ wv_lt s.mem L.B (slot L.w aN) L.w
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)
  exact WP.mono (core_ok M h128 hEZ hc hE hodd (by omega_arith) hfit hX)
    fun t ⟨ht, _⟩ => ht.ws.x0

private theorem round_rel (M : Mont) :
    RelCT isa (Two CorePre) (round M.mm) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.AArch64.round
  refine RelCT.seq (two_post (Ψ := fun L s => s.gpr .x0 = L.B) (core_ct M) (core_base M)) ?_
  exact two_taint [.x0] (fun L s t hs ht r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hs.trans ht.symm) (by unfold returnFlag; taint_decide)

theorem round_ct (M : Mont) : ConstantTime isa roundPre roundPub (round M.mm) := by
  apply RelCT.constantTime
  refine (round_rel M).mono (fun s t ⟨hs, ht, hp⟩ => ?_) (fun _ _ h => h)
  obtain ⟨hsp, h0, h1, hw⟩ := hp
  have hL : coreSpace s = coreSpace t := by
    unfold coreSpace
    congr 1
    rw [h1]
  exact ⟨coreSpace s, initial_core hs, hL.symm ▸ initial_core ht, hsp⟩

end VG.Proof.MillerRabin.AArch64
