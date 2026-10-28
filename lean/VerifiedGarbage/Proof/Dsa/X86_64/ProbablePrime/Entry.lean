module

public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! # The probable-prime test's entry: `used` in the frame, the size in `r8`, the arithmetic workspace in `rdi` -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

theorem entry_ok {s : State} (hf : Scr s (s.gpr .rsp) 56) :
    WP isa (.block entry) s fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8) ∧
      Keep [.rdi, .rsi, .r9, .r8] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .r9, .r8] (Q := fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8)) (by
    xrun [entry, sp, State.ea, BitVec.ofInt_natCast, hf.st (d := 48) (by decide)]
    rw [show BitVec.signExtend 64 (BitVec.ofNat 32 Impl.Dsa.Generation.Layout.arithmetic) =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic by decide]) rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
