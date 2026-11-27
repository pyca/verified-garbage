module

import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.RsaKeyGen.Trial32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-! ### `RsaKeyGen.X86.TrialLoad`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.TrialStep`, which this module and modules that import it used -/

section

/-! # Execute the carried 32-bit trial-division reduction -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Trial

theorem redc32_code (s : State) :
    WP isa (.block redc32) s fun t => t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t ∧
      t.gpr .ebp = quotient (s.gpr .eax) (s.gpr .ebp) (s.gpr .ebx) (s.gpr .esi) := by
  unfold redc32
  refine wp_addS rfl fun a A cfA => ?_
  refine wp_movS rfl fun b B cfB => ?_
  refine wp_adcS rfl (cfB.trans cfA) fun c C _ => ?_
  have carryX : c.gpr .ebp = carryWord (carry (s.gpr .eax) (s.gpr .ebp)) := by
    rw [C.gpr, B.gpr]
    rw [show (0 : BitVec 32) + 0 = 0#32 from rfl, BitVec.zero_add]
    rfl
  refine wp_movS rfl fun d D _ => ?_
  have loD : d.gpr .ecx = s.gpr .eax + s.gpr .ebp := by
    rw [D.gpr, C.other .eax (by decide), B.other .eax (by decide), A.gpr]
  refine wp_mul fun e E => ?_
  have qE : e.gpr .eax = BitVec.ofNat 32
      ((s.gpr .eax + s.gpr .ebp).toNat * (s.gpr .esi).toNat) := by
    rw [E.eax, D.other .eax (by decide), C.other .eax (by decide), B.other .eax (by decide), A.gpr,
      D.other .esi (by decide), C.other .esi (by decide), B.other .esi (by decide), A.other .esi (by decide)]
  refine wp_mul fun f F => ?_
  have primeE : e.gpr .ebx = s.gpr .ebx := by
    rw [E.other .ebx (by decide) (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
  have loF : f.gpr .ecx = s.gpr .eax + s.gpr .ebp := by
    rw [F.other .ecx (by decide) (by decide), E.other .ecx (by decide) (by decide), loD]
  have carryF : f.gpr .ebp = carryWord (carry (s.gpr .eax) (s.gpr .ebp)) := by
    rw [F.other .ebp (by decide) (by decide), E.other .ebp (by decide) (by decide), D.other .ebp (by decide), carryX]
  refine wp_addS rfl fun g G cfG => ?_
  refine wp_adcS rfl cfG fun u U _ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .edx, .ecx, .ebp] s t := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans
      ((D.keeps.mono (by decide)).trans ((E.keeps.mono (by decide)).trans
        ((F.keeps.mono (by decide)).trans ((G.keeps.mono (by decide)).trans
          ((U.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))))))))
  have M : t.mem = s.mem := T.mem.trans (U.mem.trans (G.mem.trans (F.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans (A.mem))))))))
  refine ⟨M, K, ?_⟩
  rw [T.gpr, U.gpr, G.other .edx (by decide), F.edx, qE, primeE,
    G.other .ebp (by decide), carryF, F.eax, qE, primeE, loF]
  rfl

/-- The machine remainder stays below twice the trial prime and carries the
same modular invariant as the x86-64 sieve. -/
theorem redc32_ok (s : State)
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 65537)
    (accBound : (s.gpr .ebp).toNat < 2 * (s.gpr .ebx).toNat)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block redc32) s fun t => t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t ∧
      (t.gpr .ebp).toNat < 2 * (s.gpr .ebx).toNat ∧
      (t.gpr .ebp).toNat * 2 ^ 32 % (s.gpr .ebx).toNat =
        ((s.gpr .eax).toNat + (s.gpr .ebp).toNat) % (s.gpr .ebx).toNat := by
  refine WP.mono (redc32_code s) ?_
  rintro t ⟨M, K, value⟩
  have result := quotient_correct (s.gpr .eax) (s.gpr .ebp) (s.gpr .ebx) (s.gpr .esi)
    primeLow primeHigh accBound inverse
  have bound : (s.gpr .eax).toNat + (s.gpr .ebp).toNat < (s.gpr .ebx).toNat * 2 ^ 32 := by
    have := (s.gpr .eax).isLt
    omega_using [primeLow]
  have math := VG.Proof.RsaKeyGen.redc32_math inverse bound
  rw [value, result]
  exact ⟨M, K, math.2⟩

end VG.Proof.RsaKeyGen.X86.Trial

end

end

/-! # A whole-word sieve step preserves the candidate and its public bounds -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Trial

theorem wordStep_ok (s : State) (endOffset : Nat) (endPtr : BitVec 32)
    (candidateRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) 0) 4)
    (endRead : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) endOffset) 4)
    (endValue : s.mem.readW (addr (s.gpr .esp) endOffset) 32 = endPtr)
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 65537)
    (accBound : (s.gpr .ebp).toNat < 2 * (s.gpr .ebx).toNat)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 32 = 0) :
    WP isa (.block (wordStep endOffset)) s fun t => t.mem = s.mem ∧
      Keeps [.eax, .edx, .ecx, .ebp, .edi] s t ∧ t.gpr .edi = s.gpr .edi + 4 ∧
      (t.gpr .ebp).toNat < 2 * (s.gpr .ebx).toNat ∧
      (t.gpr .ebp).toNat * 2 ^ 32 % (s.gpr .ebx).toNat =
        ((s.mem.readW (addr (s.gpr .edi) 0) 32).toNat + (s.gpr .ebp).toNat) % (s.gpr .ebx).toNat ∧
      t.zf = some (s.gpr .edi + 4 - endPtr == 0) := by
  unfold wordStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS (readSrc_mem rfl candidateRead) fun a A _ => WP.block_nil ?_
  refine WP.mono (redc32_ok a
    (by rw [A.other .ebx (by decide)]; exact primeLow)
    (by rw [A.other .ebx (by decide)]; exact primeHigh)
    (by rw [A.other .ebp (by decide), A.other .ebx (by decide)]; exact accBound)
    (by rw [A.other .ebx (by decide), A.other .esi (by decide)]; exact inverse)) ?_
  rintro b ⟨M, K, bound, remainder⟩
  have Kb : Keeps [.eax, .edx, .ecx, .ebp] s b := (A.keeps.mono (by decide)).trans K
  have Mb : b.mem = s.mem := M.trans A.mem
  refine wp_addS rfl fun c C _ => ?_
  have Kc : Keeps [.eax, .edx, .ecx, .ebp, .edi] s c := (Kb.mono (by decide)).trans (C.keeps.mono (by decide))
  have Mc : c.mem = s.mem := C.mem.trans Mb
  have read : readSrc c (.mem ⟨.esp, endOffset⟩) = some endPtr := by
    have ptr := Kc.1 .esp (by decide)
    have readable : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) endOffset) 4 := by
      rw [Kc.2.1, Kc.2.2, ptr]
      exact endRead
    have raw := readSrc_mem rfl readable
    rw [Mc, ptr, endValue] at raw
    exact raw
  refine wp_cmpS read fun t T Z => WP.block_nil ?_
  have Kt : Keeps [.eax, .edx, .ecx, .ebp, .edi] s t := Kc.trans (T.keeps _)
  have ptr : c.gpr .edi = s.gpr .edi + 4 := by rw [C.gpr, Kb.1 .edi (by decide)]
  refine ⟨T.mem.trans Mc, Kt, (congrFun T.gpr .edi).trans ptr, ?_, ?_, ?_⟩
  · rw [congrFun T.gpr .ebp, C.other .ebp (by decide)]
    rw [A.other .ebx (by decide)] at bound
    exact bound
  · rw [congrFun T.gpr .ebp, C.other .ebp (by decide)]
    rw [A.other .ebx (by decide), A.other .ebp (by decide), A.gpr] at remainder
    exact remainder
  · rw [ptr] at Z
    exact Z

end VG.Proof.RsaKeyGen.X86.Trial

end

end

/-! # The sieve's word loop branches only at the public end pointer -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

theorem word_address (p : BitVec 32) {n i : Nat} (fit : p.toNat + 4 * n ≤ 2 ^ 32) (index : i < n) :
    addr (p + BitVec.ofNat 32 (4 * i)) 0 = off (byteAddr p) (4 * i) := by
  change byteAddr (p + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0) = _
  rw [BitVec.add_zero, byteAddr_add (by omega_using [fit, index])]

theorem pointer_zf (p : BitVec 32) {n i : Nat} (lengthBound : 4 * n < 2 ^ 32) (index : i < n) :
    (p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n)) == 0) = decide (i + 1 = n) := by
  by_cases done : i + 1 = n
  · rw [done, BitVec.sub_self, decide_eq_true rfl]
    rfl
  · have different : p + BitVec.ofNat 32 (4 * (i + 1)) ≠ p + BitVec.ofNat 32 (4 * n) := by
      intro equal
      have small := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp equal)
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [lengthBound, index] : 4 * (i + 1) < 2 ^ 32),
        Nat.mod_eq_of_lt lengthBound] at small
      omega_using [done, small]
    have nonzero : p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n)) ≠ 0 := by
      intro zero
      apply different
      calc p + BitVec.ofNat 32 (4 * (i + 1)) =
          (p + BitVec.ofNat 32 (4 * (i + 1)) - (p + BitVec.ofNat 32 (4 * n))) +
            (p + BitVec.ofNat 32 (4 * n)) := (BitVec.sub_add_cancel _ _).symm
        _ = p + BitVec.ofNat 32 (4 * n) := by rw [zero]; exact BitVec.zero_add _
    rw [beq_eq_false_iff_ne.mpr nonzero, decide_eq_false done]

end VG.Proof.RsaKeyGen.X86.Trial
