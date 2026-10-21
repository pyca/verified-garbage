module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrime
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Framework.Offset

/-! # Prime export retains the workspace header needed to write entropy consumption -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

def primeArgs : List Instr := [.mov .ebx (.mem (sc 0)), .mov .ecx (.mem (sc 4))]

theorem primeArgs_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 8 ≤ size) :
    WP isa (.block primeArgs) s fun t =>
      t.gpr .ebx = s.mem.readW (off base 0) 32 ∧ t.gpr .ecx = s.mem.readW (off base 4) 32 ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t := by
  unfold primeArgs
  refine wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) header) fun t T _ => WP.block_nil ?_
  exact ⟨(T.other .ebx (by decide)).trans A.gpr, by rw [T.gpr, A.mem], T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

theorem PrimeInput.keepMem {s t : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s) (M : t.mem = s.mem)
    {regs : List Reg} (K : Keeps regs s t) (baseReg : .edi ∉ regs) (sp : .esp ∉ regs) :
    PrimeInput base size w candidate out usedPtr count t := by
  refine ⟨S.scratch.of_keeps K baseReg sp, S.positive, S.space, S.header, ?_, ?_, ?_, ?_, ?_, S.outFit, ?_,
    S.usedWrite.of_keeps K, S.workspaceFar, S.usedFar⟩
  · rw [M]; exact S.outEq
  · rw [M]; exact S.lengthEq
  · rw [M]; exact S.usedEq
  · rw [M]; exact S.countEq
  · rw [M]; exact S.candidateEq
  · rw [K.2.2]; exact S.outWrite

theorem export_header_ok {s : State} {base : Addr} {size w candidate : Nat} {out usedPtr count : BitVec 32}
    (S : PrimeInput base size w candidate out usedPtr count s)
    (destination : s.gpr .ebx = out) (length : s.gpr .ecx = BitVec.ofNat 32 (8 * w)) :
    WP isa (VG.Impl.Bignum.X86.storeBE (slot w 0)) s fun t =>
      Scr t base size ∧ t.mem.readW (off base 44) 32 = usedPtr ∧ Keeps [.eax, .ebx, .ecx, .esi] s t := by
  refine WP.mono (VG.Proof.Bignum.X86.storeBE_ok S.scratch (by have := S.positive; omega) (Nat.le_refl _) S.space length
    (by rw [wordsVal_eq_val32, show 8 * (8 * w) = 32 * (2 * w) by omega]; exact val32_lt _ _ _ _)
    (by rw [destination]; exact S.outFit) (by rw [destination]; exact S.outWrite)
    (by rw [destination]; exact S.workspaceFar.sub_left (Offset.sub_base base S.space))) fun t ⟨_, F, K⟩ => ?_
  rw [destination] at F
  have header := F.readW (r := (⟨base, size⟩ : Region)) (a := off base 44) (w := 32)
    (Offset.contains_base _ (by have := S.header; omega) (by decide))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.workspaceFar) (by decide)
  exact ⟨S.scratch.of_keeps K (by decide), header.trans S.usedEq, K.mono (by decide)⟩

end VG.Proof.RsaKeyGen.X86.CandidateFinish
