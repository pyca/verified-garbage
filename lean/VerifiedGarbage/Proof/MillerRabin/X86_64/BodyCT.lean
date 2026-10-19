module
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase

import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizedPublic
import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Constant time of the saved prepared round body -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Bignum.X86_64
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

structure BodyPub where
  B : Addr
  Z : Nat
  w : Nat
  wr : List Region
  sp : Addr

def BodyPre (p : BodyPub) (s : State) : Prop :=
  s.gpr .rsp = p.sp ∧ KW p.B p.wr ∧ MrDims p.B p.Z p.w ∧
    ∃ (mi : BitVec 64) (c bm b : Nat), MrCtx s p.B p.Z p.w mi c bm ∧
      ECtx s.mem p.B p.w c ∧ c % 2 = 1 ∧ 3 ≤ c ∧
      wv s.mem p.B (slot p.w aXm) p.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * p.w) % c

private def corePub (p : BodyPub) : RPub :=
  ⟨normalizedPub p.B p.Z p.w p.wr, 0, 0, false⟩

private def CoreStage (p : BodyPub) (s : State) : Prop :=
  s.gpr .rsp = p.sp ∧ CorePre (corePub p) s

private theorem normalize_core (p : BodyPub) (s : State) (h : BodyPre p s)
    (hw : s.wr = p.wr) : WP isa (.block normalize) s (CoreStage p) := by
  obtain ⟨hsp, hk, hd, mi, c, bm, b, hc, he, ho, h3, hx⟩ := h
  refine WP.mono (normalize_ok hc.good hd.z) ?_
  rintro t ⟨hm, ht⟩
  obtain ⟨hct, het⟩ := normalized_ctx hc hd he hm ht
  have hz0 : slot p.w 8 ≤ p.Z := hd.z
  have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hc.good.scr.nowrap
  have hxt : wv t.mem p.B (slot p.w aXm) p.w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * p.w) % c := by
    rw [hm, (normalized_outside s.mem p.B p.w).wv
      (Or.inr (by simp only [slot, hdrBytes]; omega_arith)) (by
        have := slot_le (w := p.w) (show aXm < 8 by decide)
        have := hd.z
        omega_arith)]
    exact hx
  refine ⟨(ht.gpr (by decide)).trans hsp, hk, ?_, hd, mi, c, bm, b, hct, het, hxt, ho, by omega_arith⟩
  have hp := normalized_hp hct.good (ht.2.2.trans hw) hm
  simpa only [corePub, normalizedPub, Nat.zero_add] using hp

private theorem core_pins (M : Mont) (p : BodyPub) (s : State) (h : CoreStage p s) :
    WP isa (seqs (preparedRound M.mm)) s fun t => t.gpr .rdi = p.B ∧ t.gpr .rsp = p.sp := by
  dsimp only [CoreStage, CorePre, corePub, normalizedPub] at h
  obtain ⟨hsp, hk, hp, hd, mi, c, bm, b, hc, he, hx, ho, h1⟩ := h
  have hfit : mrE c < 16 ^ (16 * p.w) := by
    change mrE c < (2 ^ 4) ^ (16 * p.w)
    rw [← Nat.pow_mul, show 4 * (16 * p.w) = 64 * p.w by omega_arith]
    have hn : c < 2 ^ (64 * p.w) := hc.n ▸ wv_lt s.mem p.B (slot p.w aN) p.w
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt (Nat.sub_le _ _) hn)
  exact WP.mono (core_ok M hd hc he ho (by omega_arith) hfit hx)
    fun t ⟨ht, _, _, _, hkeep⟩ => ⟨ht.good.rdi, (hkeep.gpr (by decide)).trans hsp⟩

theorem body_ct (M : Mont) :
    RelCT isa (Two fun p s => BodyPre p s ∧ s.wr = p.wr)
      (VG.Impl.MillerRabin.X86_64.body M.mm) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.X86_64.body
  refine RelCT.seq (two_post (Ψ := CoreStage) ?_ (fun p s h => normalize_core p s h.1 h.2)) ?_
  · refine normalize_ct.mono ?_ (fun _ _ h => h)
    rintro s t ⟨p, hs, ht⟩
    refine ⟨⟨p.B, p.wr, p.w⟩, ?_, ?_⟩
    · obtain ⟨_, hk, _, mi, c, bm, b, hc, _⟩ := hs.1
      refine ⟨hk, hc.good.rdi, hs.2, ?_⟩
      rintro e he
      simp only [List.mem_singleton] at he
      subst he
      exact hc.good.hdr.hw
    · obtain ⟨_, hk, _, mi, c, bm, b, hc, _⟩ := ht.1
      refine ⟨hk, hc.good.rdi, ht.2, ?_⟩
      rintro e he
      simp only [List.mem_singleton] at he
      subst he
      exact hc.good.hdr.hw
  · refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = p.B ∧ s.gpr .rsp = p.sp)
      ((core_ct M).mono (fun _ _ h => by
          obtain ⟨p, hs, ht⟩ := h
          exact ⟨corePub p, hs.2, ht.2⟩)
        (fun _ _ _ => trivial)) (core_pins M)) ?_
    exact finish_ct.mono (fun _ _ h => by
      obtain ⟨p, hs, ht⟩ := h
      exact ⟨(p.B, p.sp), hs, ht⟩) (fun _ _ h => h)

end VG.Proof.MillerRabin.X86_64
