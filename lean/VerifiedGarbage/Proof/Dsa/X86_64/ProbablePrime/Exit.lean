module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-! # The probable-prime test's exit: `used`, and the status in `rax` -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.RsaKeyGen.X86_64.Candidate

/-- The test's status as the function returns it. -/
def returned (stat : BitVec 64) : BitVec 64 := stat - (stat >>> 1)

theorem returned_status (n : Nat) (h : n = 0 ∨ n = 1 ∨ n = 3) :
    returned (BitVec.ofNat 64 n) = BitVec.ofNat 64 (if n = 3 then 2 else n) := by
  rcases h with rfl | rfl | rfl <;> decide

theorem exit_ok {s : State} {B U : Addr} (hdi : s.gpr .rdi = B)
    (hu1 : InRegions (s.rd ++ s.wr) (off B 200) 8) (hs1 : InRegions (s.rd ++ s.wr) (off B 232) 8)
    (hf : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 48) 8)
    (hU : word s.mem (s.gpr .rsp) 48 = U) (hu : InRegions s.wr U 8)
    (hsep : Mem.Sep (off B 232) 8 U 8) :
    WP isa (.block exit) s fun t =>
      t.gpr .rax = returned (word s.mem B 232) ∧
      t.mem = s.mem.writeW U (word s.mem B 200) ∧
      Keep [.rax, .rcx, .r8] s t := by
  have hread : (s.mem.writeW U (word s.mem B 200)).readW (off B 232) 64 = word s.mem B 232 := by
    rw [Mem.readW_writeW_sep hsep (by decide)]
  have h0 : ∀ a : Addr, a + BitVec.ofInt 64 0 = a := fun a => by
    rw [show BitVec.ofInt 64 0 = 0 by decide]; exact BitVec.add_zero a
  refine WP.mono (WP.keep [.rax, .rcx, .r8] (Q := fun t =>
      t.gpr .rax = returned (word s.mem B 232) ∧
      t.mem = s.mem.writeW U (word s.mem B 200)) (by
    xrun [Impl.Dsa.X86_64.ProbablePrime.exit, sp, State.ea, BitVec.ofInt_natCast,
      Impl.Bignum.X86_64.hdr, hdi, kUsed, kStat, VG.Impl.Bignum.sFn, hdrOff, Nat.reduceAdd, Nat.reduceMul,
      h0, hu1, hs1, hf, hU, hu, hread]
    rfl) rfl) fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
