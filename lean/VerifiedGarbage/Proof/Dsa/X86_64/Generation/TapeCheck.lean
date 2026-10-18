module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
import VerifiedGarbage.Proof.Framework.Omega

/-! # Refuse an incomplete draw without advancing the random tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem tapeCheck_ok {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) (hu : used ≤ P.rand.length) :
    WP isa (.block Impl.Dsa.X86_64.Generation.tapeCheck) s fun t =>
      t.cf = some (decide (P.rand.length < used + P.drawBytes)) ∧ t.mem = s.mem ∧ Keep [.rcx, .rax] s t := by
  have hld : ∀ i < 32, InRegions (s.rd ++ s.wr) (off P.B (8 * i)) 8 := fun i hi =>
    h.ready.good.scr.ld (by have := hdr_lt_slot P.w 8 hi; have := P.dims.z; omega)
  have hsub : BitVec.ofNat 64 P.rand.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (P.rand.length - used) :=
    Offset.ofNat_sub_ofNat hu
  have hrem : P.rand.length - used < 2 ^ 64 := by have := P.randMax; omega
  have hdraw : P.drawBytes < 2 ^ 64 := by have := P.drawMax; omega
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t =>
    t.cf = some (decide (P.rand.length < used + P.drawBytes)) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.tapeCheck, State.ea, hdr, hdrOff, h.ready.good.rdi,
      hld kRandLen (by decide), hld kUsed (by decide), hld kLen (by decide), h.randLen, h.used, h.draw,
      hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrem, Nat.mod_eq_of_lt hdraw]
    exact decide_eq_decide.mpr (by omega)) rfl) fun _ ⟨⟨hf, hm⟩, hk⟩ => ⟨hf, hm, hk⟩

end VG.Proof.Dsa.X86_64.Generation
