module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Save the unused RSA bookkeeping before the shared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

def Staged (B : Addr) (s t : State) : Prop :=
  ∀ e ∈ bookkeeping, t.gpr e.2 = word s.mem B (8 * e.1)

theorem stage_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block stage) s fun t => t.mem = s.mem ∧ Staged B s t ∧
      Keep [.rsi, .rdx, .rcx, .r8, .r9, .rax, .r10, .r11] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    h.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8, .r9, .rax, .r10, .r11]
    (Q := fun t => t.mem = s.mem ∧ Staged B s t) ?_ rfl)
    fun t ⟨⟨hm, hv⟩, hk⟩ => ⟨hm, hv, hk⟩
  simp only [stage, bookkeeping, List.map_cons, List.map_nil]
  xrun [bookkeeping, Staged, kOut, kLen, kUsedP, kRand, kRandLen,
    kChecks, kE, kI, kElen, kUsed, sFn, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_eq, false_imp_iff, forall_const, State.ea, hdr, hdrOff, h.rdi,
    hl 16 (by decide), hl 17 (by decide), hl 18 (by decide), hl 23 (by decide),
    hl 24 (by decide), hl 19 (by decide), hl 20 (by decide), hl 25 (by decide)]

end VG.Proof.MillerRabin.X86_64
