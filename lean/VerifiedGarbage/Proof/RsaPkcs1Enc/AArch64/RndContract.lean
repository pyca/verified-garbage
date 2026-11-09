module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndBody
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndReject

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the contract

`contract` is the shared contract's precondition, `post`, and its public data
by name (`pub`); it implies the shared contract (`implies`), which a state
with an empty message and tape meets (`sat`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64

/-- The trace of drawing `PS`. -/
abbrev trace (s : State) : List Nat := (Spec.RsaPkcs1Enc.padSearch (psLen s) (randB s)).trace

/-- The public data, by name. -/
def pub (a s : State) : Prop :=
  a.sp = s.sp ∧ (∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], a.gpr r = s.gpr r) ∧
    (∀ j < 7, stackArg a j = stackArg s j) ∧ nB a = nB s ∧ eB a = eB s ∧ preW a = preW s ∧ trace a = trace s

def contract (P : Nat) : Contract isa where
  pre := (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)).pre
  post := post
  pub := pub

theorem wordsAt_two (m : Mem) (p : Addr) :
    Spec.Rsa.wordsAt m p 2 = [m.readW p 64, m.readW (p + BitVec.ofNat 64 8) 64] := by
  simp [Spec.Rsa.wordsAt, List.range_succ]

theorem stackArgs_seven (s : State) :
    List.map (stackArg s) (List.range 7) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-- A state meeting the precondition: a 512-bit key, an empty message and tape. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 64 | .x5 => 0x4000 | .x6 => 1
    | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10009 then 0x60
    else bif Nat.beq a.toNat 0x1001A then 0x02 else bif Nat.beq a.toNat 0x10020 then 0x70
    else bif Nat.beq a.toNat 0x10029 then 0x70 else bif Nat.beq a.toNat 0x10030 then 0x10 else 0
  rd := [⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x7000, 128⟩, ⟨0x10000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 16⟩, ⟨0x20000, 896⟩]

/-- It meets the shared contract with 16 bytes of stack for the callee's call. -/
theorem sat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack 16)).pre s := by
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
    AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq, rndStack] [satState, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using satState

theorem implies (P : Nat) (hsat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)).pre s) :
    (contract P).Implies (Spec.RsaPkcs1Enc.encryptRandomContract AArch64.abi (rndStack P)) where
  pre := fun _ h => h
  post := by
    intro s u _ h
    sig_post [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq]
    obtain ⟨⟨req, h0, h1, hr⟩, hm⟩ := h
    exact ⟨⟨req, by rw [wordsAt_two, h0, h1]; rfl, hr⟩, hm⟩
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
      AArch64.abi, AArch64.argRegs, stackArgs_seven, List.append_eq, List.getD_cons_succ,
      List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6⟩ := h
    have hl' : (List.map BitVec.toNat (nB s₁ ++ eB s₁) ++ List.map BitVec.toNat (preW s₁)) ++ trace s₁ =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂) ++ List.map BitVec.toNat (preW s₂)) ++ trace s₂ := hl
    have hl1 : (List.map BitVec.toNat (nB s₁ ++ eB s₁)).length =
        (List.map BitVec.toNat (nB s₂ ++ eB s₂)).length := by
      simp [nB, eB, kOf, Spec.Rsa.bytesAt, h4, h6]
    have hl2 : (List.map BitVec.toNat (preW s₁)).length = (List.map BitVec.toNat (preW s₂)).length := by
      simp [preW, Spec.Rsa.wordsAt, a6]
    obtain ⟨h12, h3'⟩ := List.append_inj hl' (by simp only [List.length_append, hl1, hl2])
    obtain ⟨h1', h2'⟩ := List.append_inj h12 hl1
    have inj : ∀ {w : Nat} {l₁ l₂ : List (BitVec w)}, l₁.map BitVec.toNat = l₂.map BitVec.toNat → l₁ = l₂ :=
      fun h => (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h
    have hne := inj h1'
    obtain ⟨hn, he⟩ := List.append_inj hne (by simp [nB, kOf, Spec.Rsa.bytesAt, h4])
    refine ⟨hsp, ?_, fun j hj => ?_, hn, he, inj h2', h3'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> with_reducible assumption
    · match j, hj with
      | 0, _ => exact a0 | 1, _ => exact a1 | 2, _ => exact a2 | 3, _ => exact a3 | 4, _ => exact a4
      | 5, _ => exact a5 | 6, _ => exact a6
  sat := hsat

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
