module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.SpecConv
public import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Spec.Ed25519.Point32
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Point
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAdd
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# `vg_gf25519_r32_mul`, `vg_gf25519_r32_pow250` and `vg_ed25519_r32_point_add` on RISC-V

Each function meets a contract of its facts by register (`mulRV`, `powRV`,
`addRV`), with no stack, from a working space aligned to 8 bytes, as an
`[u64]` is (`RISCV64.abi`'s `alignsBufs`): the callers in this library call
them through these, and the shared contracts of `Spec/X25519/Field32.lean` and
`Spec/Ed25519/Point32.lean` imply them, with no stack (`mulFn_verified`,
`pow250Fn_verified`, `addFn_verified`). None calls another function or writes
a callee-saved register or `ra` (`WP.keep`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)
open VG.Spec.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- The registers the functions may write. -/
def fnWrites : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

/-- `mulContract` by register: `ws` in `a0`, aligned, `o`, `a` and `b` in `a1`–`a3`. -/
def mulRV : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 4096⟩] ∧ Fits (offArg s .a1) ∧ Fits (offArg s .a2) ∧
    Fits (offArg s .a3) ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := valAt s'.mem (s.gpr .a0) (offArg s .a1) % P =
      valAt s.mem (s.gpr .a0) (offArg s .a2) * valAt s.mem (s.gpr .a0) (offArg s .a3) % P ∧
    Keeps (s.gpr .a0) (offArg s .a1) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ offArg s₁ .a1 = offArg s₂ .a1 ∧ offArg s₁ .a2 = offArg s₂ .a2 ∧
    offArg s₁ .a3 = offArg s₂ .a3 ∧ s₁.sp = s₂.sp

/-- The working space of `pow250` and the point addition, `bytes` long and aligned, in `a0`. -/
def wsPre (bytes : Nat) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .a0, bytes⟩] ∧ (s.gpr .a0).toNat % 8 = 0

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.sp = s₂.sp

/-- `pow250Contract` by register. -/
def powRV : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Spec.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Spec.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .a0) (BitVec.ofNat 32 Spec.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .a0) (BitVec.ofNat 32 Spec.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .a0) s.mem s'.mem
  pub := wsPub

/-- `addContract` by register. -/
def addRV : Contract isa where
  pre s := wsPre 8192 s ∧ Spec.Ed25519.Point32.elemAt s.mem (s.gpr .a0) Spec.Ed25519.Point32.dAt = Spec.Ed25519.d
  post s s' :=
    Spec.Ed25519.Point32.pointAt s'.mem (s.gpr .a0) Spec.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (Spec.Ed25519.Point32.pointAt s.mem (s.gpr .a0) Spec.Ed25519.Point32.pAt)
          (Spec.Ed25519.Point32.pointAt s.mem (s.gpr .a0) Spec.Ed25519.Point32.qAt) ∧
      Spec.Ed25519.Point32.Keeps (s.gpr .a0) s.mem s'.mem
  pub := wsPub

theorem mul_ok' (s : State) (hs : mulRV.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulRV.post s s' := by
  obtain ⟨hrd, hwr, f1, f2, f3, hal⟩ := hs
  have h1 : (offArg s .a1).toNat + 32 ≤ 768 := by
    simpa [Fits, Spec.X25519.Field32.elemBytes, Spec.X25519.Field32.ownAt] using f1
  obtain ⟨t, s', he, ⟨hV, hF⟩, hk⟩ := WP.keep fnWrites (mulFn_ok hrd hwr f1 f2 f3 hal) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hV, keeps_mul h1 hF⟩

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
  · rw [show Spec.X25519.Field32.oAt = offset 15 from rfl, show Spec.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    have h := val_of_env h15
    exact h
  · rw [show Spec.X25519.Field32.eAt = offset 14 from rfl, show Spec.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    exact val_of_env (e := 11) h14

theorem add_ok' (s : State) (hs : addRV.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addRV.post s s' := by
  obtain ⟨⟨_, hwr, hal⟩, hd⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep fnWrites (addFn_ok hwr hal hd) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hp⟩

/-! ## The shared contracts -/

/-- A state satisfying the preconditions of `mul` and `pow250`: `ws` at `0x1000`, every offset
0. -/
def satWs : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 4096⟩]

theorem mulFn_verified : Verified RISCV64.target mulFn (Spec.X25519.Field32.mulContract RISCV64.abi) :=
  Verified.of_correct mul_ok' (mulFn_ct fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩) (by
    contract_implies [Spec.X25519.Field32.mulContract, Spec.X25519.Field32.sig, mulRV, offArg,
      RISCV64.abi, RISCV64.argRegs] [satWs] using satWs)

theorem pow250Fn_verified :
    Verified RISCV64.target pow250Fn (Spec.X25519.Field32.pow250Contract RISCV64.abi) :=
  Verified.of_correct pow_ok' (pow250Fn_ct fun _ _ _ _ ⟨h0, hsp⟩ => ⟨hsp, h0⟩) (by
    contract_implies [Spec.X25519.Field32.pow250Contract, Spec.X25519.Field32.pow250Sig, powRV, wsPre, wsPub,
      RISCV64.abi, RISCV64.argRegs] [satWs] using satWs)

def dLit : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- The working space at `0x1000`, holding `d` in slot 16. -/
def addMem : Mem := fun a =>
  if 0x1240 ≤ a.toNat ∧ a.toNat < 0x1260 then BitVec.ofNat 8 (dLit / 256 ^ (a.toNat - 0x1240)) else 0

/-- A state satisfying the point addition's precondition. -/
def satAdd : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := addMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem addMem_d : (addMem.read ((0x1000 : Addr) + BitVec.ofNat 64 576) 32).toNat = dLit := by
  decide +kernel

theorem d_eq : Spec.Ed25519.d = Fin.ofNat Spec.X25519.P dLit := by decide +kernel

theorem satAdd_d :
    Spec.Ed25519.Point32.elemAt satAdd.mem (0x1000 : Addr) Spec.Ed25519.Point32.dAt = Spec.Ed25519.d := by
  rw [d_eq, Spec.Ed25519.Point32.elemAt]
  exact congrArg _ addMem_d

theorem addFn_verified : Verified RISCV64.target addFn (Spec.Ed25519.Point32.addContract RISCV64.abi) :=
  Verified.of_correct add_ok' (addFn_ct fun _ _ _ _ ⟨h0, hsp⟩ => ⟨hsp, h0⟩)
    { pre := by implies_pre [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addRV, wsPre, wsPub,
        RISCV64.abi, RISCV64.argRegs]
      post := by implies_post [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addRV, wsPre, wsPub,
        RISCV64.abi, RISCV64.argRegs]
      pub := by implies_pub [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addRV, wsPre, wsPub,
        RISCV64.abi, RISCV64.argRegs]
      sat := by
        refine ⟨satAdd, ?_⟩
        sig_pre [Spec.Ed25519.Point32.addContract, Spec.Ed25519.Point32.sig, addRV, wsPre, RISCV64.abi,
          RISCV64.argRegs, satAdd]
        sig_and_intros
        all_goals first
          | exact satAdd_d
          | rfl
          | decide }

end VG.Proof.Ed25519.RISCV64
