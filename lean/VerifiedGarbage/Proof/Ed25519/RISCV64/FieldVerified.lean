module

public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.SpecConv
public import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg

/-!
# `vg_gf25519_r32_pow250` on RISC-V, by register

`pow250` meets a contract of its facts by register (`powRV`, `pow_ok'`), with
no stack, from a working space aligned to 8 bytes, as an `[u64]` is
(`RISCV64.abi`'s `alignsBufs`): the callers in this library call it through
this. It calls no other function and writes no callee-saved register or `ra`
(`WP.keep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- The registers the functions may write. -/
def fnWrites : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- The working space of `pow250` and the point addition, `bytes` long and aligned, in `a0`. -/
def wsPre (bytes : Nat) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .a0, bytes⟩] ∧ (s.gpr .a0).toNat % 8 = 0

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

/-- `pow250`'s facts by register: `a^(2^250 - 1)` and `a^11` from `a`, the rest of the
working space kept. -/
def powRV : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .a0) s.mem s'.mem
  pub := wsPub

theorem pow_ok' (s : State) (hs : powRV.pre s) :
    ∃ t s', Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powRV.post s s' := by
  obtain ⟨_, hwr, hal⟩ := hs
  obtain ⟨t, s', he, ⟨_, hF, hE⟩, hk⟩ := WP.keep fnWrites
    (pow250Fn_ok (s := s) rfl hal (by rw [hwr]; exact List.mem_singleton_self _)) (by decide +kernel)
  have h15 : env s'.mem (s.gpr .a0) 15 = Proof.X25519.pw (env s.mem (s.gpr .a0) 2) (2 ^ 250 - 1) := by
    rw [congrFun hE 15, (power250Env_eval _).1, Proof.X25519.chainF_eq]
  have h14 : env s'.mem (s.gpr .a0) 14 = Proof.X25519.pw (env s.mem (s.gpr .a0) 2) 11 := by
    rw [congrFun hE 14, (power250Env_eval _).2, Proof.X25519.chainF_eq]
  refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ?_, ?_, keeps_pow hF⟩
  · rw [show Proof.X25519.Field32.oAt = offset 15 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    have h := val_of_env h15
    exact h
  · rw [show Proof.X25519.Field32.eAt = offset 14 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    exact val_of_env (e := 11) h14

end VG.Proof.Ed25519.RISCV64
