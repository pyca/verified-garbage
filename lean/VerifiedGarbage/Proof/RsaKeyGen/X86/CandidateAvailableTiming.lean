module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming

/-! # The public byte length selects a candidate width without exposing its entropy -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen
open VG.Impl.Mont.X86

def widthArgs : List Instr := [.mov .eax (.mem (sc 4)), .shift .shr .eax 3]

theorem widthArgs_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s) : WP isa (.block widthArgs) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 E.width ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.syms = s.syms := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  unfold widthArgs
  refine wp_movS (readSrc_sc I.scratch (d := 4) (by omega)) fun a A _ => wp_shr (by decide) fun t T _ => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.trans T.keeps, T.syms.trans A.syms⟩
  rw [T.gpr, A.gpr, I.header 1 (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change (E.length % 2 ^ 32) / 8 = E.width % 2 ^ 32
  rw [Nat.mod_eq_of_lt (by have := v.length; unfold Spec.RsaKeyGen.primeLenValid at this; omega),
    Nat.mod_eq_of_lt (by have := v.width_bounds.2; omega)]
  rfl

theorem widthArgs_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (.block widthArgs)
      (WithValue (ClearedPair E eBytes pBytes qBytes rBytes sBytes) (BitVec.ofNat 32 E.width)) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block widthArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨valueU, memU, KU, symU⟩ := wp_result (widthArgs_ok v P.left) A
  obtain ⟨valueZ, memZ, KZ, symZ⟩ := wp_result (widthArgs_ok v P.right) B
  exact ⟨(raw _ _ _ _ _ _ P.toInputPair.agree A B).1,
    P.keepMem v memU memZ KU KZ (by decide) (by decide) symU symZ, valueU, valueZ⟩

theorem available_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.available montName mont roundName round) (fun _ _ => True) := by
  have bounds := v.width_bounds
  unfold VG.Impl.RsaKeyGen.X86.Candidate.available
  refine RelCT.seq (widthArgs_trace v)
    (dispatch_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length rEnough enough leak _ ?_ ?_)
  · exact List.mem_map.mpr ⟨E.width - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w mem
    obtain ⟨i, index, rfl⟩ := List.mem_map.mp mem
    have bound := List.mem_range.mp index
    omega

end VG.Proof.RsaKeyGen.X86.Candidate
