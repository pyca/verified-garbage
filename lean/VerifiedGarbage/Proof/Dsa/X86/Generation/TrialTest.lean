module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialScan
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFlag
public import VerifiedGarbage.Proof.RsaKeyGen.TrialMath

/-! A complete small-prime test returns whether the candidate is divisible. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem trial_test {s : State} {base : Addr} {size offset w endSlot : Nat}
    (ws : Rt.Ws s base size) (hp : Rt.PtrAt s base .ebp offset)
    (fit : offset + 8 * w ≤ size) (small : 8 * w < 2 ^ 32) (nonempty : 0 < w)
    (prime : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (odd : (s.gpr .ebx).toNat % 2 = 1)
    (inverse : ((s.gpr .ebx).toNat * (s.gpr .esi).toNat + 1) % 2 ^ 16 = 0)
    (last : readSrc s (.mem (at_ .esp endSlot)) =
      some (s.gpr .ebp + BitVec.ofNat 32 (8 * w))) :
    WP isa (trialTest endSlot) s fun t =>
      t.gpr .eax = BitVec.ofNat 32
        (decide (val32 s.mem base offset (2 * w) % (s.gpr .ebx).toNat = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps trialClob s t := by
  have fits : offset + 4 * (2 * w) ≤ size := by omega
  have small' : 4 * (2 * w) < 2 ^ 32 := by omega
  have last' : readSrc s (.mem (at_ .esp endSlot)) =
      some (s.gpr .ebp + BitVec.ofNat 32 (4 * (2 * w))) := by
    rwa [show 4 * (2 * w) = 8 * w by omega]
  unfold trialTest
  refine WP.seq (WP.mono (trial_scan ws hp fits small' (by omega) prime inverse last') ?_)
  intro u I
  have residue := I.residue
  rw [show 32 * (2 * w) = 64 * w by omega] at residue
  have div := VG.Proof.RsaKeyGen.trial_div odd I.bound residue
  have same (x y : BitVec 32) : x = y ↔ x.toNat = y.toNat :=
    ⟨congrArg BitVec.toNat, BitVec.eq_of_toNat_eq⟩
  have flag : (u.gpr .edi = 0 ∨ u.gpr .edi = u.gpr .ebx) ↔
      val32 s.mem base offset (2 * w) % (s.gpr .ebx).toNat = 0 := by
    rw [same, same, I.keeps.1 .ebx (by decide)]
    change ((u.gpr .edi).toNat = 0 ∨ (u.gpr .edi).toNat = (s.gpr .ebx).toNat) ↔ _
    exact div.symm
  refine WP.mono (trial_flag u) ?_
  rintro t ⟨value, mem, K⟩
  refine ⟨?_, mem.trans I.mem, I.keeps.trans (K.mono (by decide))⟩
  simpa only [flag] using value

end VG.Proof.Dsa.X86.Generation
