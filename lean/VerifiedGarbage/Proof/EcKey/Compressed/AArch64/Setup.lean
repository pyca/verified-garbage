module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.Step

/-! # Adapt the compressed-point arguments to the existing EC setup -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem args_ok (s : State) :
    WP isa (.block Impl.EcKey.Compressed.AArch64.args) s fun s' =>
      s'.gpr .x4 = s.gpr .x2 ∧ s'.gpr .x6 = s.gpr .x1 ∧
      s'.gpr .x3 = s.gpr .x1 + 1 ∧ s'.gpr .x1 = s.gpr .x1 + 1 ∧
      s'.gpr .x2 = s.gpr .x1 + 1 ∧ Keeps [.x4, .x6, .x3, .x1, .x2] s s' := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.AArch64.args, runBlock_cons, runStep_some, runBlock_nil,
    exec, read_x, show (0 : Nat) < 4096 by decide, show (1 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2, ite_false]

 theorem setup_fixed {c : Cfg} {s₀ s : State} {base : Addr}
    (P : SetupPost c none s₀ base s) : Fixed c base s₀.gpr s.mem :=
  ⟨P.consts (MP, c.C.p) (by simp [Cfg.consts]), P.consts (MN, c.C.n) (by simp [Cfg.consts]),
    P.consts (ZERO, 0) (by simp [Cfg.consts]), P.consts (ONE, 1) (by simp [Cfg.consts]),
    (P.consts (ONEP, c.mont 1) (by simp [Cfg.consts])).trans (by simp only [Cfg.mont, Cfg.R, Nat.one_mul]),
    P.consts (AP, c.mont c.C.a) (by simp [Cfg.consts]),
    P.consts (BM, c.mont c.C.b) (by simp [Cfg.consts]),
    P.consts (GX, c.mont c.C.gx) (by simp [Cfg.consts]),
    P.consts (GY, c.mont c.C.gy) (by simp [Cfg.consts]),
    P.consts (R2N, c.R * c.R % c.C.n) (by simp [Cfg.consts]),
    P.consts (ONEN, c.R % c.C.n) (by simp [Cfg.consts]), P.saved⟩

end VG.Proof.EcKey.Compressed.AArch64
