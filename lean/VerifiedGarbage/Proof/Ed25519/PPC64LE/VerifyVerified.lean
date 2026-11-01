module

import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed25519_verify_equation` on PPC64LE, verified

The function meets its contract of `Spec/Ed25519/Contract.lean`, with no
stack: the proof against the contract's facts by register (`verifyPPC`),
which it implies, and a state satisfying it. The function saves and restores
the nonvolatile registers it writes, and `lr`, which its calls overwrite
(`verify_ok`). The contract declares the inputs public, and two runs on the
same inputs leak the same trace (`verifyEquation_rel`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE

/-- `verifyEquationContract` by register. -/
def verifyPPC : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 32⟩
    let sig : Region := ⟨s.gpr .r4, 64⟩
    let ch : Region := ⟨s.gpr .r5, 64⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws
  post s s' := (s'.gpr .r3).setWidth 32 = if Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .r3) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .r5) 64) then 1 else 0
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp ∧
    (Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64).map (·.toNat) =
    (Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r3) 32 ++ Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r4) 64 ++
      Spec.Ed25519.bytesAt s₂.mem (s₂.gpr .r5) 64).map (·.toNat)

theorem verify_ok' (s : State) (hs : verifyPPC.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed25519.PPC64LE.verifyEquation s t s' ∧ abiPreserved s s' ∧
      verifyPPC.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hg, hsp, hlr, hr⟩ := verify_ok ⟨h1, h2, h3, h4, h5⟩
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, ?_⟩
  show (s'.gpr .r3).setWidth 32 = _
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

theorem verify_ct : ConstantTime isa verifyPPC.pre verifyPPC.pub Impl.Ed25519.PPC64LE.verifyEquation := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨p3, p4, p5, p6, psp, pl⟩ := hp
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (Spec.Ed25519.bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [Spec.Ed25519.bytesAt]
  obtain ⟨b3, b4, b5⟩ := bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl]) pl
  have pre : ∀ s, verifyPPC.pre s → VerifyPre s := fun s ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩
  refine verifyEquation_rel (b := s₁.gpr .r6) (sp := s₁.sp) (pk := s₁.gpr .r3) (sig := s₁.gpr .r4)
    (ch := s₁.gpr .r5) (PK := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r3) 32)
    (SG := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r4) 64) (CH := Spec.Ed25519.bytesAt s₁.mem (s₁.gpr .r5) 64)
    _ _ _ _ _ _ ⟨⟨pre _ h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨pre _ h₂, p3.symm, p4.symm, p5.symm, p6.symm, psp.symm, by rw [b3, p3], by rw [b4, p4],
        by rw [b5, p5]⟩⟩ e₁ e₂

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_verified :
    Verified PPC64LE.target Impl.Ed25519.PPC64LE.verifyEquation (Proof.Ed25519.verifyEquationContract PPC64LE.abi) :=
  Verified.of_correct verify_ok' verify_ct (by
    contract_implies [Proof.Ed25519.verifyEquationContract, Proof.Ed25519.verifyEquationSig, verifyPPC,
      Spec.Ed25519.scratchWords, PPC64LE.abi, PPC64LE.argRegs] [verifySat] using verifySat)

end VG.Proof.Ed25519.PPC64LE
