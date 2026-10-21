module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
public import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderSourceTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CloseTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Optional-prime checks branch on a public length and keep both primes private -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateClose
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

theorem other_trace {base : Addr} {size : Nat} (header : 24 ≤ size) (w : Nat) :
    RelCT isa (HeaderSource.Pair base size 20) (VG.Impl.RsaKeyGen.X86.CandidateClose.other w)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClose.other
  refine RelCT.seq (HeaderSource.source_trace header) (RelCT.seq (Import.load_trace (2 * w) (slot w 4)) ?_)
  exact (Close.code_trace (2 * w) (slot w 2) (slot w 3) (slot w 0) (slot w 4)).mono
    (fun _ _ H => taint.le_sound (by decide +kernel) H) (fun _ _ H => H)

def ClosePair (base : Addr) (size : Nat) (s t : State) : Prop :=
  HeaderSource.Pair base size 20 s t ∧ s.mem.readW (off base 24) 32 = t.mem.readW (off base 24) 32

def lengthArgs : List Instr := [.mov .eax (.mem (sc 24)), .alu .cmp .eax (.imm 0)]

theorem length_ok {base : Addr} {size : Nat} {s : State} (S : Scr s base size) (header : 28 ≤ size) :
    WP isa (.block lengthArgs) s fun t =>
      isa.eval .e t = some (s.mem.readW (off base 24) 32 == 0#32) ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold lengthArgs
  refine wp_movS (readSrc_sc S (d := 24) header) fun a A _ => wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans A.mem, A.keeps.widen (T.keeps [])⟩
  change t.zf = _
  rw [Z, A.gpr]
  change some (s.mem.readW (off base 24) 32 - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]

theorem length_trace {base : Addr} {size : Nat} (header : 28 ≤ size) :
    RelCT isa (ClosePair base size) (.block lengthArgs)
      (fun s t => ClosePair base size s t ∧ isa.eval .e s = isa.eval .e t) := by
  intro s t tr ur u z ⟨P, len⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block lengthArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨Zu, Mu, Ku⟩ := wp_result (length_ok P.left header) E
  obtain ⟨Zz, Mz, Kz⟩ := wp_result (length_ok P.right header) G
  refine ⟨(raw _ _ _ _ _ _ P.agree E G).1, ?_, ?_⟩
  · refine ⟨⟨P.left.of_keeps Ku (by decide), P.right.of_keeps Kz (by decide), ?_, ?_⟩, ?_⟩
    · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact P.stack
    · rw [Mu, Mz]; exact P.pointer
    · rw [Mu, Mz]; exact len
  · rw [Zu, Zz, len]

theorem code_trace {base : Addr} {size : Nat} (header : 28 ≤ size) (w : Nat) :
    RelCT isa (ClosePair base size) (VG.Impl.RsaKeyGen.X86.CandidateClose.code w) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClose.code
  refine RelCT.seq (length_trace header) ?_
  refine VG.RelCT.ite (fun _ _ H => H.2) ?_ ?_
  · have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .eax (.imm 0)])
        (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
    exact raw.mono (fun _ _ H => H.1.1.1.agree) (fun _ _ _ => trivial)
  · exact (other_trace (by omega) w).mono (fun _ _ H => H.1.1.1) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.CandidateClose
