module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialWord

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
    (primeLow : 3 ≤ (s.gpr .ebx).toNat) (primeHigh : (s.gpr .ebx).toNat ≤ 8161)
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
    omega
  have math := VG.Proof.RsaKeyGen.redc32_math inverse bound
  rw [value, result]
  exact ⟨M, K, math.2⟩

end VG.Proof.RsaKeyGen.X86.Trial
