module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contract
public import VerifiedGarbage.Proof.AesGcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE

def openSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x4000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9061 then 0x50 else bif Nat.beq a.toNat 0x9071 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩]

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

theorem probePre : ∀ s, (Proof.AesGcm.openScratchContract PPC64LE.abi).pre s → openPPC64LE.pre s := by
  sig_implies_pre [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
    openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]

theorem probePost : ∀ s s', (Proof.AesGcm.openScratchContract PPC64LE.abi).pre s → openPPC64LE.post s s' →
    (Proof.AesGcm.openScratchContract PPC64LE.abi).post s s' := by
  intro s s' _ h
  sig_eval [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPost, PPC64LE.abi,
    PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
  simp only [openPPC64LE] at h
  intro _
  exact h

theorem probePub : ∀ s₁ s₂, (Proof.AesGcm.openScratchContract PPC64LE.abi).pre s₁ →
    (Proof.AesGcm.openScratchContract PPC64LE.abi).pre s₂ → (Proof.AesGcm.openScratchContract PPC64LE.abi).pub s₁ s₂ →
    openPPC64LE.pub s₁ s₂ := by
  intro s₁ s₂ _ _ h
  sig_pub [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openLeak, openPPC64LE,
    openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range,
    List.range.loop] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2⟩ := h
  refine ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, hsp, fun i hi => ?_⟩, fun hr => leak_bool ?_⟩
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
  · have e₁ : ¬((s₁.gpr .r4).toNat = 10 ∨ (s₁.gpr .r4).toNat = 12 ∨ (s₁.gpr .r4).toNat = 14) ↔ False :=
      ⟨fun x => x hr, False.elim⟩
    have e₂ : ¬((s₂.gpr .r4).toNat = 10 ∨ (s₂.gpr .r4).toNat = 12 ∨ (s₂.gpr .r4).toNat = 14) ↔ False :=
      ⟨fun x => x (h4 ▸ hr), False.elim⟩
    simp only [e₁, e₂, ↓reduceIte] at hl
    exact hl

theorem probeSat : ∃ s, (Proof.AesGcm.openScratchContract PPC64LE.abi).pre s := by
  sig_implies_sat [Proof.AesGcm.openScratchContract, Proof.AesGcm.openScratchSig, Spec.Gcm.openPre,
    openPPC64LE, openPre, onePub, args, rounds, PPC64LE.abi, PPC64LE.argRegs,
    stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat

end VG.Proof.AesGcm.PPC64LE
