module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Blowfish.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.Ecb
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Blowfish.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Blowfish.RISCV64.Lit

/-!
# Blowfish ECB on RISC-V meets its contract

The proof is written against `ecbC`, which states the frame of 4176 bytes
below the stack pointer, and moved to the shared contracts of
`Spec/Blowfish/Contract.lean` with `stack := 4176`. The code writes only
temporaries and argument registers.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

def dir (up : Bool) : Direction := if up then .encrypt else .decrypt

/-- The ECB contract as the code sees it. -/
def ecbC (up : Bool) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 4168⟩
    let data : Region := ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
    let stack : Region := ⟨s.sp - 4176, 4176⟩
    s.rd = [key] ∧ s.wr = [data] ∧ key.Disjoint data ∧
      (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ 4176 ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint data
  post s s' :=
    blocksAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
      Spec.Blowfish.ecb (scheduleAt s.mem (s.gpr .a0)) (dir up) (blocksAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem ecb_blocks (K : Schedule) (up : Bool) (m m' : Mem) (D : Addr) (n : Nat)
    (h : ∀ b < n, blockAt m' (wAt D b) = blockOut K up (blockAt m (wAt D b))) :
    blocksAt m' D n = Spec.Blowfish.ecb K (dir up) (blocksAt m D n) := by
  simp only [blocksAt, Spec.Blowfish.ecb, List.map_map]
  apply List.map_congr_left
  intro b hb
  rw [Function.comp_apply, h b (List.mem_range.mp hb)]
  cases up <;> rfl

/-- The registers ECB writes: no preserved register, nor `ra`. -/
def ecbRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem ecb_ok (up : Bool) (hw : writesOnly ecbRegs (Impl.Blowfish.RISCV64.ecb up) = true)
    (hn : callFree (Impl.Blowfish.RISCV64.ecb up) = true) (s : State) (hs : (ecbC up).pre s) :
    ∃ t s', Exec isa (Impl.Blowfish.RISCV64.ecb up) s t s' ∧ abiPreserved s s' ∧ (ecbC up).post s s' := by
  obtain ⟨rd, wr, kd, fit, al, sp, sk, sd⟩ := hs
  obtain ⟨t, s', he, hp, hk⟩ := WP.keep ecbRegs (ecb_wp up ⟨rd, wr, kd, fit, al, sp, sk, sd⟩) hw hn
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), ecb_blocks _ _ _ _ _ _ hp.1⟩

theorem ecb_agree (up : Bool) : ∀ s₁ s₂, (ecbC up).pre s₁ → (ecbC up).pre s₂ → (ecbC up).pub s₁ s₂ →
    taint.Agree (Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  intro s₁ s₂ _ _ h
  refine ⟨h.2.2.2, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem encrypt_ct : ConstantTime isa (ecbC true).pre (ecbC true).pub encrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree true) (by taint_decide)

theorem decrypt_ct : ConstantTime isa (ecbC false).pre (ecbC false).pub decrypt :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) (ecb_agree false) (by taint_decide)

def ecbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 0⟩]

theorem encrypt_verified : Verified RISCV64.target encrypt (Spec.Blowfish.ecbEncryptContract RISCV64.abi 4176) := by
  refine Verified.of_correct (k := ecbC true) (ecb_ok true (by lit_decide) (by lit_decide)) encrypt_ct ?_
  contract_implies [Spec.Blowfish.ecbEncryptContract, Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig,
    Spec.Blowfish.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC, dir] [ecbSat] using ecbSat

theorem decrypt_verified : Verified RISCV64.target decrypt (Spec.Blowfish.ecbDecryptContract RISCV64.abi 4176) := by
  refine Verified.of_correct (k := ecbC false) (ecb_ok false (by lit_decide) (by lit_decide)) decrypt_ct ?_
  contract_implies [Spec.Blowfish.ecbDecryptContract, Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig,
    Spec.Blowfish.ecbPost, RISCV64.abi, RISCV64.argRegs, ecbC, dir] [ecbSat] using ecbSat

end VG.Proof.Blowfish.RISCV64
