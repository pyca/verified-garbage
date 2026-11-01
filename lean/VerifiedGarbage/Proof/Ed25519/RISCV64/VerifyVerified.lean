module

import VerifiedGarbage.Proof.Ed25519.RISCV64.VerifyCT
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# `vg_ed25519_verify_equation` on RISC-V, by register

The function meets a contract of its facts by register (`verifyRV`), with no
stack, from a working space aligned to 8 bytes, as an `[u64]` is: the
callers in this library call it through it. It saves and restores the
callee-saved registers and `ra` (`verify_ok`). The contract declares the
inputs public, and two runs on the same inputs leak the same trace
(`verifyEquation_rel`, `verify_ct`). The shared contract of
`Spec/Ed25519/Contract.lean` implies it (`verifyEquation_verified`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64

/-- `verifyEquationContract` by register. -/
def verifyRV : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .a0, 32⟩
    let sig : Region := ⟨s.gpr .a1, 64⟩
    let ch : Region := ⟨s.gpr .a2, 64⟩
    let ws : Region := ⟨s.gpr .a3, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ (s.gpr .a3).toNat % 8 = 0 ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧
      ch.Disjoint ws
  post s s' := (s'.gpr .a0).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .a0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .a2) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a0) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a1) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .a2) 64).map (·.toNat)

theorem verify_ok' (s : State) (hs : verifyRV.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.RISCV64.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyRV.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hra, hr⟩ := verify_ok ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨t, s', he, ⟨hg, hsp, hra⟩, ?_⟩
  show (s'.gpr .a0).setWidth 32 = _
  rw [hr]
  split <;> rfl

theorem bytes_of_leak {a₁ b₁ c₁ a₂ b₂ c₂ : List Byte} (ha : a₁.length = a₂.length) (hb : b₁.length = b₂.length)
    (h : (a₁ ++ b₁ ++ c₁).map (·.toNat) = (a₂ ++ b₂ ++ c₂).map (·.toNat)) : a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  have e : a₁ ++ b₁ ++ c₁ = a₂ ++ b₂ ++ c₂ := by
    have := congrArg (List.map fun n => BitVec.ofNat 8 n) h
    simpa [List.map_map, Function.comp_def] using this
  obtain ⟨e1, e2⟩ := List.append_inj e (by simp [ha, hb])
  obtain ⟨e3, e4⟩ := List.append_inj e1 ha
  exact ⟨e3, e4, e2⟩

theorem verify_ct : ConstantTime isa verifyRV.pre verifyRV.pub Impl.Ed25519.RISCV64.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p0, p1, p2, p3, psp, pl⟩ := hp
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b0, b1, b2⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  have pre : ∀ s, verifyRV.pre s → VerifyPre s := fun s ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩
  refine verifyEquation_rel (b := s₁.gpr .a3) (sp := s₁.sp) (pk := s₁.gpr .a0) (sig := s₁.gpr .a1)
    (ch := s₁.gpr .a2) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a0) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a1) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .a2) 64)
    _ _ _ _ _ _ ⟨⟨pre _ h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨pre _ h₂, p0.symm, p1.symm, p2.symm, p3.symm, psp.symm, by rw [b0, p0], by rw [b1, p1],
        by rw [b2, p2]⟩⟩ e₁ e₂

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_verified :
    Verified RISCV64.target Impl.Ed25519.RISCV64.verifyEquation (Proof.Ed25519.verifyEquationContract RISCV64.abi) :=
  Verified.of_correct verify_ok' verify_ct (by
    contract_implies [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig, verifyRV,
      Spec.Ed25519.scratchWords, RISCV64.abi, RISCV64.argRegs] [verifySat] using verifySat)

end VG.Proof.Ed25519.RISCV64
