import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPaddingWord

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

def paddedState (A : Spec.Sha3.State) (j : Nat) : Spec.Sha3.State :=
  xorWord (xorWord A j 0x1f) 16 0x8000000000000000

/-- Adds SHAKE256 domain separation and the rate-block terminal bit. -/
theorem padding_ok {s : State} {A B : Spec.Sha3.State} {j : Nat}
    (hj : j<25) (hp : Pairs s A B) :
    WP isa (.block (paddingWord j 31 0 ++ paddingWord 16 0x8000 3)) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ Pairs t (paddedState A j) B := by
  rw [WP.block_append_iff]
  refine WP.mono (paddingWord_ok hj 31 0 (by decide) hp) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (paddingWord_ok (by decide) 0x8000 3 (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

/-- ML-DSA-65 has two words left after six complete rate blocks. -/
theorem tail_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hin : ∀j<2, InRegions (s.rd++s.wr) (s.gpr .x5+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.block tail) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧
      Pairs t (paddedState (xorWords A s.mem (s.gpr .x5) 2) 2) B := by
  change WP isa (.block (((List.range 2).flatMap fun j => lowWord (vreg j) (8*j)) ++
    (paddingWord 2 31 0 ++ paddingWord 16 0x8000 3))) s _
  rw [WP.block_append_iff]
  refine WP.mono (lowWords_ok hp 2 (by decide) hin) fun a ⟨ha,hma,hpa⟩ => ?_
  refine WP.mono (padding_ok (by decide) hpa) fun t ⟨ht,hmt,hpt⟩ => ?_
  exact ⟨(ha.trans ht).mono (by simp),hmt.trans hma,hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
