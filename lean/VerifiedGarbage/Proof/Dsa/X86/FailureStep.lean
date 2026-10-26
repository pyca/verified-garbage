module

public import VerifiedGarbage.Proof.Zeroize.Common
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Impl.Dsa.X86.Bytes

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
