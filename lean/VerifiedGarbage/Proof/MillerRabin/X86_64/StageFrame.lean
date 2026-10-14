module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
public import VerifiedGarbage.Proof.MillerRabin.X86_64.FrameCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackRegions
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The callable's public inputs supply the framed body's context -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def inputPub (s : State) : BodyPub :=
  ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8, Spec.Rsa.Mont.wOf s.mem (s.gpr .rdi),
    [⟨s.gpr .rsp - 112#64, 8⟩, ⟨s.gpr .rsp - 104#64, 104⟩,
      ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩], s.gpr .rsp - 112#64⟩

theorem stage_frame_ok {s : State} (h : roundPre s) :
    WP isa (.block stage) s (FramePre (inputPub s)) := by
  obtain ⟨hdim, bm, hc, he, ho, h3, hx⟩ := initial_ctx h
  obtain ⟨hrd, hwr, hn, hs, hret, hstack, hL, hP⟩ := h
  let B := s.gpr .rdi
  let Z := (s.gpr .rsi).toNat * 8
  let w := Spec.Rsa.Mont.wOf s.mem B
  let c := Spec.Rsa.Mont.numAt s.mem B w 0
  obtain ⟨b, _, hb⟩ := witness_exists (coprime_pow2 ho (64 * w)) hx
  have hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    simpa only [VG.Proof.Bignum.powMod_eq, Nat.pow_one] using hb
  have hz : 256 ≤ Z := by
    have := hdr_lt_slot w 8 (show 31 < 32 by decide)
    have hz0 : slot w 8 ≤ Z := hdim.z
    omega_arith
  refine WP.mono (stage_ok hc.good hdim.z) ?_
  rintro t ⟨hm, hv, hk⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := hk.gpr (by decide)
  have hst : 120 ≤ (t.gpr .rsp).toNat := hsp ▸ hs
  have hdt : Region.Disjoint ⟨t.gpr .rsp - 120#64, 120⟩ ⟨B, Z⟩ := by
    rw [hsp]
    exact hstack
  have hd : Region.Disjoint ⟨t.gpr .rsp - 112#64, 112⟩ ⟨B, Z⟩ :=
    hdt.sub_left (Offset.sub_below _ (a := 112) (n := 112) (b := 120) (m := 120) (by decide) (by decide))
  obtain ⟨hct, het⟩ := staged_context hc he hm hk
  have hce := entered_ctx hct hdim hst hd
  have hee := entered_exp het hdim hst hn hd
  have hxe : wv (entered t).mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [entered_wv hst hn hd (by
      have := slot_le (w := w) (show aXm < 8 by decide)
      have hz0 : slot w 8 ≤ Z := hdim.z
      omega_arith), hm]
    exact hX
  have hw : (entered t).wr = (inputPub s).wr := by
    rw [entered_wr, hk.2.2, hwr, hsp]
    rfl
  have hkw := entered_kw (hk.2.2.trans hwr) hz hn hdt
  refine ⟨⟨?_, ?_, hdim, _, c, bm, b, hce, hee, ho, h3, hxe⟩, hw⟩
  · rw [entered_rsp, hsp]
    rfl
  · rw [hw] at hkw
    exact hkw

end VG.Proof.MillerRabin.X86_64
