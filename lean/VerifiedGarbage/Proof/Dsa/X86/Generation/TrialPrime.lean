module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialInverse
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTest

/-! One trial-prime test includes the shared inverse setup. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

def trialPrimeClob : List Reg := [.eax, .ecx, .edx, .ebp, .esi, .edi]

theorem trial_prime {s : State} {base : Addr} {size offset w startSlot endSlot : Nat} {ptr : BitVec 32}
    (ws : Rt.Ws s base size) (hp : ptr.toNat = (base.toNat + offset) % 2 ^ 32)
    (fit : offset + 8 * w ≤ size) (small : 8 * w < 2 ^ 32) (nonempty : 0 < w)
    (prime : 3 ≤ (s.gpr .ebx).toNat ∧ (s.gpr .ebx).toNat < 8162)
    (odd : (s.gpr .ebx).toNat % 2 = 1)
    (start : readSrc s (.mem (at_ .esp startSlot)) = some ptr)
    (last : readSrc s (.mem (at_ .esp endSlot)) = some (ptr + BitVec.ofNat 32 (8 * w))) :
    WP isa (trialPrime startSlot endSlot) s fun t =>
      t.gpr .eax = BitVec.ofNat 32
        (decide (val32 s.mem base offset (2 * w) % (s.gpr .ebx).toNat = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps trialPrimeClob s t := by
  unfold trialPrime
  refine WP.seq (WP.mono (trial_inverse s odd) ?_)
  rintro u ⟨inverse, mem, K⟩
  have start' := (trial_read_keeps mem K (m := at_ .esp startSlot)
    (by change Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebp, .esi]; decide)).trans start
  refine WP.seq (wp_movS start' fun v V _ => WP.block_nil ?_)
  have memv : v.mem = s.mem := V.mem.trans mem
  have Kv : Keeps trialPrimeClob s v := (K.mono (by decide)).trans (V.keeps.mono (by decide))
  have pv : Rt.PtrAt v base .ebp offset := by rw [Rt.PtrAt, V.gpr]; exact hp
  have primes : 3 ≤ (v.gpr .ebx).toNat ∧ (v.gpr .ebx).toNat < 8162 := by
    rw [Kv.1 .ebx (by decide)]; exact prime
  have odds : (v.gpr .ebx).toNat % 2 = 1 := by rw [Kv.1 .ebx (by decide)]; exact odd
  have inv : ((v.gpr .ebx).toNat * (v.gpr .esi).toNat + 1) % 2 ^ 16 = 0 := by
    rw [Kv.1 .ebx (by decide), V.other .esi (by decide)]; exact inverse
  have lastv : readSrc v (.mem (at_ .esp endSlot)) =
      some (v.gpr .ebp + BitVec.ofNat 32 (8 * w)) := by
    rw [V.gpr, trial_read_keeps memv Kv (by change .esp ∉ trialPrimeClob; decide)]
    exact last
  refine WP.mono (trial_test (ws.of_keeps Kv) pv fit small nonempty primes odds inv lastv) ?_
  rintro t ⟨value, mem', K'⟩
  rw [memv, Kv.1 .ebx (by decide)] at value
  exact ⟨value, mem'.trans memv, Kv.trans (K'.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
