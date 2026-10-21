module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDispatchTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair

/-! # The public modulus byte count becomes the native key width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Candidate
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.Key

theorem widthArgs_ok {E : Environment} {s : State} (h : Input E s) :
    WP isa (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) s fun t =>
      Input E t ∧ t.mem = s.mem ∧ t.gpr .eax = BitVec.ofNat 32 (E.primeLength / 8) ∧ Keeps [.eax] s t := by
  have valid := h.valid.length
  have dimensions := h.valid.widths
  have lengthBound : 2 * E.primeLength < 2 ^ 32 := by omega
  have widthBound : E.primeLength / 8 < 2 ^ 32 := by omega
  have head := h.ws.hdr_le
  refine wp_movS (readSrc_sc h.ws.workspace (by unfold VG.Impl.Rsa.X86.Keys.hdr at head; omega))
    fun a A _ => wp_shr (by decide) fun t T _ => WP.block_nil ?_
  have memory := T.mem.trans A.mem
  have K : Keeps [.eax] s t := A.keeps.trans T.keeps
  refine ⟨h.keep (h.ws.rest K) K (by intro d hd; rw [memory]), memory, ?_, K⟩
  rw [T.gpr, A.gpr, h.arguments 1 (by decide)]
  change BitVec.ofNat 32 (2 * E.primeLength) >>> 4 = BitVec.ofNat 32 (E.primeLength / 8)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt lengthBound, Nat.mod_eq_of_lt widthBound]
  change (2 * E.primeLength) / 16 = E.primeLength / 8
  omega

theorem widthArgs_trace (E : Environment) (e p q p' q' : Nat) :
    RelCT isa (SizedStart E e p q p' q') (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4])
      (WithValue (SizedStart E e p q p' q') (BitVec.ofNat 32 (E.primeLength / 8))) := by
  intro s t tr ur u v P A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    checkedBlockInvariant rfl rfl
  obtain ⟨leftInput, leftMem, leftValue, leftKeeps⟩ := wp_result (widthArgs_ok P.inputs.left) A
  obtain ⟨rightInput, rightMem, rightValue, rightKeeps⟩ := wp_result (widthArgs_ok P.inputs.right) C
  refine ⟨(raw _ _ _ _ _ _ P.inputs.agree A C).1, ?_, leftValue, rightValue⟩
  refine ⟨⟨leftInput, rightInput, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.inputs.stack
  · rw [leftMem]
    exact P.leftExponent
  · rw [rightMem]
    exact P.rightExponent
  · rw [leftMem]
    exact P.leftP
  · rw [leftMem]
    exact P.leftQ
  · rw [rightMem]
    exact P.rightP
  · rw [rightMem]
    exact P.rightQ

theorem front_trace (E : Environment) (v : E.Valid) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (SizedStart E e p q p' q')
      (.seq (.block [.mov .eax (.mem (sc 4)), .shift .shr .eax 4]) (dispatch widths)) (fun _ _ => True) := by
  have lengths := v.length
  have width : E.n = 4 * (E.primeLength / 8) := by
    unfold Environment.n
    obtain ⟨_, _, _⟩ := lengths
    omega
  have bounds : 4 ≤ E.primeLength / 8 ∧ E.primeLength / 8 ≤ 64 := by
    obtain ⟨_, _, _⟩ := lengths
    omega
  apply RelCT.seq (widthArgs_trace E e p q p' q')
  apply dispatch_trace E e p q p' q' (E.primeLength / 8) width (by omega) release widths
  · exact List.mem_map.mpr ⟨E.primeLength / 8 - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega

end VG.Proof.RsaKeyGen.X86.Key
