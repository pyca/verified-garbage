module
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Restore

import VerifiedGarbage.Proof.MillerRabin.X86_64.NormalizeContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.CoreFrame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Finish
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Correctness of the round body within its saved frame -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

private theorem outside_frame {B : Addr} {Z : Nat} {m m' : Mem} (h : Outside B 0 Z m m') :
    Frame [⟨B, Z⟩] m m' := by
  intro x hx
  apply h
  right
  have := hx ⟨B, Z⟩ (List.mem_singleton_self _)
  simp only [Region.Contains, ofs] at *
  omega_arith

private theorem xm_fits {B : Addr} {Z w : Nat} (h : MrDims B Z w) : slot w aXm + 8 * w ≤ Z := by
  have hz := h.z
  have := slot_le (w := w) (show aXm < 8 by decide)
  omega_arith

private theorem exponent_fits {s : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (h : MrCtx s B Z w mi c bm) : mrE c < 16 ^ (16 * w) := by
  change mrE c < (2 ^ 4) ^ (16 * w)
  rw [← Nat.pow_mul, show 4 * (16 * w) = 64 * w by omega_arith]
  have hc : c < 2 ^ (64 * w) := h.n ▸ wv_lt s.mem B (slot w aN) w
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_le_of_lt (Nat.sub_le _ _) hc)

theorem body_ok (M : Mont) {s : State} {B S : Addr} {Z w c bm b : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h : MrDims B Z w) (he : ECtx s.mem B w c)
    (hodd : c % 2 = 1) (h3 : 3 ≤ c)
    (hX : wv s.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c)
    (hsp : s.gpr .rsp = S) (hd : Region.Disjoint ⟨B, Z⟩ ⟨S, 112⟩)
    (hl : ∀ d, 8 ≤ d → d + 8 ≤ 112 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 d) 8) :
    WP isa (VG.Impl.MillerRabin.X86_64.body M.mm) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Proof.MillerRabin.Round.round c b).toNat ∧
      t.gpr .rbx = s.mem.readW (S + 104#64) 64 ∧
      t.gpr .r12 = s.mem.readW (S + 96#64) 64 ∧
      t.gpr .r13 = s.mem.readW (S + 88#64) 64 ∧
      t.gpr .r14 = s.mem.readW (S + 80#64) 64 ∧
      t.gpr .r15 = s.mem.readW (S + 72#64) 64 ∧ Keep mmRegs s t ∧
      Frame [⟨B, Z⟩] s.mem t.mem ∧
      ∃ u : State, t.mem = restoredMem u.mem B S ∧ Frame [⟨B, Z⟩] s.mem u.mem ∧
        Frm B (coreRanges w) (normalizedMem s.mem B w) u.mem := by
  have h256 : 256 ≤ Z := by have := hdr_lt_slot w 8 (show 31 < 32 by decide); have := h.z; omega_arith
  have hn := hc.good.scr.nowrap
  unfold VG.Impl.MillerRabin.X86_64.body
  refine WP.seq (WP.mono (normalize_ok hc.good h.z) fun u ⟨hm, hk⟩ => ?_)
  obtain ⟨hu, hEu⟩ := normalized_ctx hc h he hm hk
  have hf0 : Frame [⟨B, Z⟩] s.mem u.mem := by
    rw [hm]
    exact outside_frame ((normalized_outside s.mem B w).mono (Nat.zero_le _) (by omega_arith))
  have hXu : wv u.mem B (slot w aXm) w = Spec.Rsa.powMod b 1 c * 2 ^ (64 * w) % c := by
    rw [hm, (normalized_outside s.mem B w).wv (Or.inr (by simp only [slot, hdrBytes]; omega_arith))
      (by have := xm_fits h; omega_arith)]
    exact hX
  refine WP.seq (WP.mono (core_ok M h hu hEu hodd h3 (exponent_fits hu) hXu)
    fun v ⟨hv, hEv, hp, hf, kv⟩ => ?_)
  have ksv := hk.trans kv
  have hfv : Frame [⟨B, Z⟩] s.mem v.mem := hf0.trans (core_frame h hf)
  refine WP.mono (finish_ok hv.good h.z ((ksv.gpr (by decide)).trans hsp) hp hd (fun d h8 h112 => by
    rw [ksv.2.1, ksv.2.2]
    exact hl d h8 h112)) fun t ⟨mt, hr, hbx, h12, h13, h14, h15, kt⟩ => ?_
  have hstack : ∀ d, d + 8 ≤ 112 → v.mem.readW (S + BitVec.ofNat 64 d) 64 = s.mem.readW (S + BitVec.ofNat 64 d) 64 := by
    intro d hread
    apply hfv.readW (r := ⟨S, 112⟩)
    · exact Offset.contains_base S hread (by omega_arith)
    · intro r hr'
      simp only [List.mem_singleton] at hr'
      subst hr'
      exact hd.symm
    · decide
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, (ksv.trans kt).mono (by decide), ?_, v, mt, hfv, ?_⟩
  · exact hbx.trans (hstack 104 (by decide))
  · exact h12.trans (hstack 96 (by decide))
  · exact h13.trans (hstack 88 (by decide))
  · exact h14.trans (hstack 80 (by decide))
  · exact h15.trans (hstack 72 (by decide))
  · rw [mt]
    exact hfv.trans (outside_frame ((restored_outside v.mem B S).mono (Nat.zero_le _) (by omega_arith)))
  · rw [← hm]
    exact hf

end VG.Proof.MillerRabin.X86_64
