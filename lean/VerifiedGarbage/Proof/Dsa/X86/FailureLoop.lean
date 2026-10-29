module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.Dsa.X86.Bytes
/-! # Complete public-domain rejection zeroization and termination -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/FailureStep.lean`, which only this module imported.
section

/-! # A byte step of public-domain rejection zeroization -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Proof.Zeroize VG.Impl.Dsa.X86

def failureStep : List Instr :=
  [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]

theorem failureStep_ok {s : State} {out : BitVec 32} {len i : Nat}
    (hi : i < len) (hf : out.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hp : s.gpr .esi = out + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (len - i)) (hz : s.gpr .eax = 0)
    (hw : InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1)
    (zeroed : Prefix s.mem (out.setWidth 64) i) :
    WP isa (.block failureStep) s fun t =>
      t.gpr .esi = out + BitVec.ofNat 32 (i + 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (len - (i + 1)) ∧
      t.zf = some (decide (i + 1 = len)) ∧
      Prefix t.mem (out.setWidth 64) (i + 1) ∧
      Outside (out.setWidth 64) 0 len s.mem t.mem ∧ Keeps [.esi, .ecx] s t := by
  have A : s.ea (at_ .esi 0) = out.setWidth 64 + BitVec.ofNat 64 i := by
    change addr (s.gpr .esi) 0 = _
    rw [hp]
    simpa only [addr, BitVec.add_zero] using addr_eq (x := out) (k := i) (by omega)
  unfold failureStep
  refine VG.Proof.Weierstrass.X86.wp_store8' A hw fun u su => ?_
  refine wp_addS rfl fun v uv _ => ?_
  refine wp_subi fun t vt _ Z => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt.other _ (by decide), uv.gpr, su.gpr, hp, BitVec.add_assoc]
    congr 1
    exact (BitVec.ofNat_add i 1).symm
  · rw [vt.gpr, uv.other _ (by decide), su.gpr, hc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from by decide]
    simpa only [Nat.sub_sub] using sub_ofNat (a := len - i) (b := 1) (by omega)
  · rw [Z, uv.other _ (by decide), su.gpr, hc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from by decide]
    have H := sub_beq (a := len - i) (b := 1) (by omega) (by decide)
    rw [H]
    simp only [show len - i = 1 ↔ i + 1 = len by omega]
  · rw [vt.mem, uv.mem, su.mem]
    change Prefix (s.mem.writeW _ ((s.gpr .eax).setWidth 8)) _ _
    rw [hz]
    change Prefix (s.mem.writeW _ (0 : BitVec 8)) _ _
    exact prefix_writeW zeroed (by omega)
  · rw [vt.mem, uv.mem, su.mem]
    exact (writeW8_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega)
  · exact ((su.keeps []).mono (by simp)).trans ((uv.keeps.mono (by decide)).trans (vt.keeps.mono (by decide)))

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Zeroize

structure FailureInv (out : BitVec 32) (len i : Nat) (s t : State) : Prop where
  pointer : t.gpr .esi = out + BitVec.ofNat 32 i
  counter : t.gpr .ecx = BitVec.ofNat 32 (len - i)
  zero : t.gpr .eax = 0
  bytes : Prefix t.mem (out.setWidth 64) i
  mem : Outside (out.setWidth 64) 0 len s.mem t.mem
  keeps : Keeps [.esi, .ecx] s t

theorem failureLoop_ok {s : State} {out : BitVec 32} {len : Nat}
    (hl : 0 < len) (h32 : len < 2 ^ 32) (hf : out.toNat + len ≤ 2 ^ 32)
    (hp : s.gpr .esi = out) (hc : s.gpr .ecx = BitVec.ofNat 32 len) (hz : s.gpr .eax = 0)
    (hw : ∀ i, i < len → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.loop (.block failureStep) .ne) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧ Keeps [.esi, .ecx] s t := by
  have I0 : FailureInv out len 0 s s :=
    ⟨by simpa using hp, by simpa using hc, hz, by intro j hj; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, k = len - i ∧ i < len ∧ FailureInv out len i s t)
    ?_ len s ⟨0, rfl, hl, I0⟩
  rintro k t ⟨i, rfl, hi, I⟩
  refine WP.mono (failureStep_ok hi hf h32 I.pointer I.counter I.zero
    (by rw [I.keeps.2.2]; exact hw i hi) I.bytes) fun u ⟨P, C, Z, B, O, K⟩ => ?_
  have next : FailureInv out len (i + 1) s u :=
    ⟨P, C, by rw [K.1 _ (by decide), I.zero], B, I.mem.trans O, I.keeps.trans K⟩
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, ?_, next.zero, next.mem, next.keeps⟩
    · simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
    · have H := prefix_spec (done ▸ next.bytes)
      exact H
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

end VG.Proof.Dsa.X86
