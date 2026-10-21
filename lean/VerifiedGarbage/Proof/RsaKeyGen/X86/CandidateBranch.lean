module

public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Candidate branch flags are exact Boolean status tests -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

theorem cmp_bool {s : State} {bit : Bool} (flag : s.gpr .eax = BitVec.ofNat 32 bit.toNat) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s fun t =>
      Fupd s t ∧ isa.eval .e t = some (!bit) ∧ isa.eval .ne t = some bit := by
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨T, ?_, ?_⟩
  · change t.zf = _
    rw [Z, flag]
    cases bit <;> decide
  · change t.zf.map Bool.not = _
    rw [Z, flag]
    cases bit <;> decide

theorem cmp_src_cf {s : State} {src : Src} {value : BitVec 32} (read : readSrc s src = some value) :
    WP isa (.block [.alu .cmp .eax src]) s fun t =>
      Fupd s t ∧ t.cf = some (decide ((s.gpr .eax).toNat < value.toNat)) := by
  refine cons (s' := arithFlags s (s.gpr .eax - value)
    (decide ((s.gpr .eax).toNat < value.toNat)) (subOverflow (s.gpr .eax) value (s.gpr .eax - value)))
    (by simp only [exec, execAlu, read, Option.bind_some]) (WP.block_nil ?_)
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end VG.Proof.RsaKeyGen.X86.Candidate
