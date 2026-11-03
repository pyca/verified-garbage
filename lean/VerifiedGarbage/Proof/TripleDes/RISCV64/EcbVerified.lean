module

import VerifiedGarbage.Proof.TripleDes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
public import VerifiedGarbage.Proof.TripleDes.RISCV64.EcbLoop

/-!
# Serial Triple DES ECB encryption on RISC-V meets its contract

`ecbC` states the frame of 944 bytes below the stack pointer. Streaming
TDEA-CMAC calls this code on one block at a time
(`vg_triple_des_ecb_encrypt_serial`), by `ecb_ok` and `encrypt_ct`; the
artifacts `vg_triple_des_ecb_encrypt` and `_decrypt` are bitsliced
(`Bitsliced/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Ecb

open VG VG.RISCV64 VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction)

/-- The ECB contract as the code sees it. -/
def ecbC (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 384⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 944, 944⟩
    s.rd = [key] ∧ s.wr = [data] ∧ key.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ 944 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint data
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem ecb_blocks (K : Spec.TripleDes.Schedule) (d : Direction) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, Spec.TripleDes.blockAt m' (wAt D b) = blockResult K d (Spec.TripleDes.blockAt m (wAt D b))) :
    Spec.TripleDes.blocksAt m' D n = Spec.TripleDes.ecb K d (Spec.TripleDes.blocksAt m D n) := by
  simp only [Spec.TripleDes.blocksAt, Spec.TripleDes.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases d <;> rfl

theorem ecb_ok (d : Direction) (s : State) (hs : (ecbC d).pre s) :
    ∃ t s', Exec isa (Ecb.ecb d) s t s' ∧ abiPreserved s s' ∧ (ecbC d).post s s' := by
  obtain ⟨rd, wr, kd, fit, al, sp, sk, sd⟩ := hs
  obtain ⟨t, s', he, hp, hb⟩ := ecb_wp d ⟨rd, wr, kd, fit, al, sp, sk, sd⟩
  exact ⟨t, s', he, hp, ecb_blocks _ _ _ _ _ _ hb⟩

theorem ecb_agree (d : Direction) : ∀ s₁ s₂, (ecbC d).pre s₁ → (ecbC d).pre s₂ → (ecbC d).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC .encrypt).pre (ecbC .encrypt).pub Ecb.encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree .encrypt)
    (by taint_decide)

end VG.Proof.TripleDes.RISCV64.Ecb
