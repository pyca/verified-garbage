module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Impl
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4BaseCT
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Avx
import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: the variant list (`Proof/Variants/SlhDsaThash4/X86_64.lean`) only names the implementations; their records and the facts they are built from are the algorithm's proofs.

/-!
# SLH-DSA on x86-64: the implementations of `thash4`

For each output length `n` (16, 24 and 32 bytes): the baseline (`base`,
four scalar Keccak-f[1600] one after the other, whose calls take 8 bytes of
stack), AVX2 (`avx2`) and AVX-512VL (`avx512vl`, the four states in the
registers for the 24 rounds), each with its proof and the facts a call of it
needs.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64

/-- `NoSp` of code none of whose instructions writes `rsp`, from the check. -/
theorem nosp_of {c : Prog isa} (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

section
open Impl.SlhDsa.X86_64

theorem base_keeps16 : ((instrs (Thash4Base.thash4 16)).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel
theorem base_keeps24 : ((instrs (Thash4Base.thash4 24)).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel
theorem base_keeps32 : ((instrs (Thash4Base.thash4 32)).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel
theorem avx_keeps (n : Nat) (fast : Bool) (hn : n = 16 ∨ n = 24 ∨ n = 32) :
    ((instrs (Thash4.thash4 n fast)).all fun i => !Taint.clobbers i .rsp) = true := by
  rcases hn with rfl | rfl | rfl <;> cases fast <;> (rw [← Code.allInstrs_eq]; decide +kernel)

theorem base_depth16 : (Thash4Base.thash4 16).depth = 1 := by decide +kernel
theorem base_depth24 : (Thash4Base.thash4 24).depth = 1 := by decide +kernel
theorem base_depth32 : (Thash4Base.thash4 32).depth = 1 := by decide +kernel
theorem avx_depth16 : (Thash4.thash4 16 false).depth = 0 ∧ (Thash4.thash4 16 true).depth = 0 := by decide +kernel
theorem avx_depth24 : (Thash4.thash4 24 false).depth = 0 ∧ (Thash4.thash4 24 true).depth = 0 := by decide +kernel
theorem avx_depth32 : (Thash4.thash4 32 false).depth = 0 ∧ (Thash4.thash4 32 true).depth = 0 := by decide +kernel

end

/-- The baseline `thash4` for outputs of `n` bytes. -/
def base16 : Thash4Impl 16 :=
  ⟨"", Impl.SlhDsa.X86_64.Thash4Base.thash4 16, 8, Thash4Base.thash4_verified16, nosp_of base_keeps16,
    by rw [base_depth16], by decide, Thash4Base.mx16, .sse,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.base16
      (Impl.Scrub.X86_64.VecLevel.sse).level 16 = true by lit_decide)⟩
def base24 : Thash4Impl 24 :=
  ⟨"", Impl.SlhDsa.X86_64.Thash4Base.thash4 24, 8, Thash4Base.thash4_verified24, nosp_of base_keeps24,
    by rw [base_depth24], by decide, Thash4Base.mx24, .sse,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.base24
      (Impl.Scrub.X86_64.VecLevel.sse).level 16 = true by lit_decide)⟩
def base32 : Thash4Impl 32 :=
  ⟨"", Impl.SlhDsa.X86_64.Thash4Base.thash4 32, 8, Thash4Base.thash4_verified32, nosp_of base_keeps32,
    by rw [base_depth32], by decide, Thash4Base.mx32, .sse,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.base32
      (Impl.Scrub.X86_64.VecLevel.sse).level 16 = true by lit_decide)⟩

/-- `thash4` with AVX2 for outputs of `n` bytes. -/
def avx2_16 : Thash4Impl 16 :=
  ⟨"_avx2", Impl.SlhDsa.X86_64.Thash4.thash4 16 false, 0, Thash4Avx.thash4_verified16,
    nosp_of (avx_keeps 16 false (by decide)), by rw [avx_depth16.1]; decide, by decide, Thash4Avx.mx16, .avx,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx2_16
      (Impl.Scrub.X86_64.VecLevel.avx).level 16 = true by lit_decide)⟩
def avx2_24 : Thash4Impl 24 :=
  ⟨"_avx2", Impl.SlhDsa.X86_64.Thash4.thash4 24 false, 0, Thash4Avx.thash4_verified24,
    nosp_of (avx_keeps 24 false (by decide)), by rw [avx_depth24.1]; decide, by decide, Thash4Avx.mx24, .avx,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx2_24
      (Impl.Scrub.X86_64.VecLevel.avx).level 16 = true by lit_decide)⟩
def avx2_32 : Thash4Impl 32 :=
  ⟨"_avx2", Impl.SlhDsa.X86_64.Thash4.thash4 32 false, 0, Thash4Avx.thash4_verified32,
    nosp_of (avx_keeps 32 false (by decide)), by rw [avx_depth32.1]; decide, by decide, Thash4Avx.mx32, .avx,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx2_32
      (Impl.Scrub.X86_64.VecLevel.avx).level 16 = true by lit_decide)⟩

/-- `thash4` with AVX-512VL for outputs of `n` bytes. -/
def avx512vl_16 : Thash4Impl 16 :=
  ⟨"_avx512vl", Impl.SlhDsa.X86_64.Thash4.thash4 16 true, 0, Thash4Avx.thash4_verified16f,
    nosp_of (avx_keeps 16 true (by decide)), by rw [avx_depth16.2]; decide, by decide, Thash4Avx.mx16f, .evex,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx512vl_16
      (Impl.Scrub.X86_64.VecLevel.evex).level 16 = true by lit_decide)⟩
def avx512vl_24 : Thash4Impl 24 :=
  ⟨"_avx512vl", Impl.SlhDsa.X86_64.Thash4.thash4 24 true, 0, Thash4Avx.thash4_verified24f,
    nosp_of (avx_keeps 24 true (by decide)), by rw [avx_depth24.2]; decide, by decide, Thash4Avx.mx24f, .evex,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx512vl_24
      (Impl.Scrub.X86_64.VecLevel.evex).level 16 = true by lit_decide)⟩
def avx512vl_32 : Thash4Impl 32 :=
  ⟨"_avx512vl", Impl.SlhDsa.X86_64.Thash4.thash4 32 true, 0, Thash4Avx.thash4_verified32f,
    nosp_of (avx_keeps 32 true (by decide)), by rw [avx_depth32.2]; decide, by decide, Thash4Avx.mx32f, .evex,
    by exact (show X86_64.Scrub.calleeSide Thash4Lit.avx512vl_32
      (Impl.Scrub.X86_64.VecLevel.evex).level 16 = true by lit_decide)⟩

end VG.Proof.SlhDsa.X86_64
