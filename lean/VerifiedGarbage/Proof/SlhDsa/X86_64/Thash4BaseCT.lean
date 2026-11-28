module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Avx
public import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4BaseCorrect
public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4Base
public meta import VerifiedGarbage.Proof.SlhDsa.X86_64.Thash4Avx
public meta import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4Base

/-!
# SLH-DSA on x86-64: the baseline `thash4`, verified

`Thash4Base.thash4 n` is `Verified` against `thash4Contract n 8`, for `n`
16, 24 and 32: its correctness is `Thash4Base.correct`, the facts of the
calling convention are `Thash4Avx.hv_of`'s (the 8 bytes below the stack
pointer hold the return address of its calls of `vg_keccak_f1600`), it is
constant time by the taint analysis from the taint `Thash4Avx.τ₀` of the
AVX2 implementations, and its precondition is satisfiable (`sat8_pre`, the
AVX2 implementations' witness, whose 8 bytes below `rsp` are outside its
regions).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Thash4Base

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64.Thash4Base (thash4)
open VG.Proof.SlhDsa.X86_64 (thash4Contract Thash4Pre workLen)
open VG.Proof.SlhDsa.X86_64.Thash4Avx (τ₀ agree₀ hv_of sat sat_rc)

theorem ct16 : ConstantTime isa (thash4Contract 16 8).pre (thash4Contract 16 8).pub (thash4 16) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct24 : ConstantTime isa (thash4Contract 24 8).pre (thash4Contract 24 8).pub (thash4 24) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)
theorem ct32 : ConstantTime isa (thash4Contract 32 8).pre (thash4Contract 32 8).pub (thash4 32) :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

theorem mx16 : (thash4 16).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx24 : (thash4 24).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel
theorem mx32 : (thash4 32).allInstrs (fun i => !loadsMxcsr i) = true := by decide +kernel

/-- The AVX2 implementations' witness, with 8 bytes below its stack pointer
outside its regions. -/
theorem sat8_pre {n : Nat} (hn : n + 32 + n ≤ 128) : Thash4Pre n 8 (sat n) where
  rd := rfl
  wr := rfl
  lanes_work := (Thash4Avx.sat_pre hn).lanes_work
  ret_lanes := (Thash4Avx.sat_pre hn).ret_lanes
  ret_work := (Thash4Avx.sat_pre hn).ret_work
  stk_lanes := Region.disjoint_of_sep (by
    show Region.sep ⟨(0x200000 : Addr) - BitVec.ofNat 64 8, 8⟩ ⟨0x10000, 4 * (128 : BitVec 64).toNat⟩ = true; decide)
  stk_work := Region.disjoint_of_sep (by
    show Region.sep ⟨(0x200000 : Addr) - BitVec.ofNat 64 8, 8⟩ ⟨0x100000, workLen⟩ = true; decide)
  lanes_fit := (Thash4Avx.sat_pre hn).lanes_fit
  work_fit := (Thash4Avx.sat_pre hn).work_fit
  len_pos := (Thash4Avx.sat_pre hn).len_pos
  len_mod := (Thash4Avx.sat_pre hn).len_mod
  len_le := (Thash4Avx.sat_pre hn).len_le
  out_eq := rfl
  out_fit := hn
  rc := sat_rc n

theorem verified_of {n : Nat} (hn : n % 8 = 0) (hn' : n ≤ 136) (hn'' : n + 32 + n ≤ 128)
    (hmx : (thash4 n).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (thash4Contract n 8).pre (thash4Contract n 8).pub (thash4 n)) :
    Verified X86_64.target (thash4 n) (thash4Contract n 8) :=
  ⟨hv_of (by decide) (fun _ hp => correct hp hn hn') hmx, hct, ⟨_, sat8_pre hn''⟩⟩

theorem thash4_verified16 : Verified X86_64.target (thash4 16) (thash4Contract 16 8) :=
  verified_of (by decide) (by decide) (by decide) mx16 ct16
theorem thash4_verified24 : Verified X86_64.target (thash4 24) (thash4Contract 24 8) :=
  verified_of (by decide) (by decide) (by decide) mx24 ct24
theorem thash4_verified32 : Verified X86_64.target (thash4 32) (thash4Contract 32 8) :=
  verified_of (by decide) (by decide) (by decide) mx32 ct32

end VG.Proof.SlhDsa.X86_64.Thash4Base
