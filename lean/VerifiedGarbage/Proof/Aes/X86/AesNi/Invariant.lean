module

public import VerifiedGarbage.Proof.Aes.X86.AesNi.Context
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Setup
import VerifiedGarbage.Proof.Aes.X86.AesNi.Data
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (GPre dstP dstR srcR schP nRounds ctrP datP nBlk scrP scrR ctrR)
open VG.Spec.Gcm (blockAt inc32)

/-- `edx` in the loops: the counter pointer in place, and out of place the
destination of block `p`. -/
abbrev edxAt (to : Bool) (s₀ : State) (p : Nat) : BitVec 32 :=
  if to then dstP to s₀ + BitVec.ofNat 32 (16 * p) else ctrP s₀

/-- After c encrypted blocks, public data/count registers point at block p.
The prefix and saved callee registers stay in scratch throughout both loops. -/
structure Inv (to : Bool) (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ nBlk s₀
  ebx : s.gpr .ebx = (cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c
  esp : s.gpr .esp = s₀.gpr .esp
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = edxAt to s₀ p
  ebp : s.gpr .ebp = scrP s₀
  esi : s.gpr .esi = datP s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (nBlk s₀ - p)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dstR to s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  scratchPrefix : s.mem.readW (addr (scrP s₀) 16) 128 = (0 : BitVec 32) ++ pfx s₀
  blocks : ∀ k < nBlk s₀,
    blockAt s.mem (tAddr s₀ to k) = if k < c then
      blk s₀ k ^^^ ciph s₀ (Nat.repeat inc32 k (cb s₀)) else blockAt s₀.mem (tAddr s₀ to k)

/-- A subrange of the encrypted run lies in the public destination region. -/
theorem run_in {to : Bool} {s₀ : State} {c n : Nat} (hn : c + n ≤ nBlk s₀) :
    Region.Sub ⟨tAddr s₀ to c, 16 * n⟩ (dstR to s₀) :=
  Offset.sub_base _ (by omega)

/-- A destination block outside the encrypted run cannot overlap that run. -/
theorem run_sep {to : Bool} {s₀ : State} (hp : GPre to s₀) {c n k : Nat} (hk : k < nBlk s₀)
    (hn : c + n ≤ nBlk s₀) (hout : ¬ (c ≤ k ∧ k < c + n)) :
    Region.Disjoint ⟨tAddr s₀ to k, 16⟩ ⟨tAddr s₀ to c, 16 * n⟩ := by
  have hw := hp.fD
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The source blocks not yet read are as they were: they are the
destination's in place, and apart from everything written out of place. -/
theorem Inv.src {to : Bool} {s₀ s : State} (hp : GPre to s₀) {c p : Nat} (hI : Inv to s₀ c p s) {k : Nat}
    (hk : k < nBlk s₀) (hc : c ≤ k) : blockAt s.mem (bAddr s₀ k) = blk s₀ k := by
  rcases hp.sd with he | hdis
  · have e : bAddr s₀ k = tAddr s₀ to k := by simp only [bAddr, tAddr, he]
    have hb := hI.blocks k hk
    rw [ite_eq_right (show ¬ k < c by omega)] at hb
    rw [e, hb, ← e]
  · exact blockAt_frame hI.frame fun r hr => by
      have hs : Region.Sub ⟨bAddr s₀ k, 16⟩ (srcR s₀) := Offset.sub_base _ (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdis.sub_left hs
      · exact hp.dSrcB.sub_left hs

/-- Entry setup, with `edx` set for the loops, supplies the loop invariant
before any data is encrypted. -/
theorem Inv.of_start {to : Bool} {s₀ s₁ s : State} (hp : GPre to s₀) (hs : Start s₀ s₁)
    (hg : ∀ r, r ≠ .edx → s.gpr r = s₁.gpr r) (hedx : s.gpr .edx = edxAt to s₀ 0) (hm : s.mem = s₁.mem)
    (hrd : s.rd = s₁.rd) (hwr : s.wr = s₁.wr) : Inv to s₀ 0 0 s := by
  refine ⟨Nat.zero_le _, ?_, by rw [hg _ (by decide)]; exact hs.esp, by rw [hg _ (by decide)]; exact hs.ecx,
    hedx, by rw [hg _ (by decide)]; exact hs.ebp, ?_, ?_, by rw [hrd]; exact hs.rd, by rw [hwr]; exact hs.wr,
    ?_, by rw [hm]; exact hs.saved, by rw [hm]; exact hs.scratchPrefix, ?_⟩
  · rw [hg _ (by decide), hs.ebx, BitVec.add_zero]
  · rw [hg _ (by decide), hs.esi, Nat.mul_zero, BitVec.add_zero]
  · rw [hg _ (by decide)]; simpa only [Nat.sub_zero] using hs.edi
  · rw [hm]; exact hs.frame.sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩
  · intro k hk
    simp only [Nat.not_lt_zero, ite_false]
    rw [hm]
    exact blockAt_frame hs.frame (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact hp.dDB.sub_left (run_in (s₀ := s₀) (c := k) (n := 1) (by omega)))

end VG.Proof.Aes.X86.AesNi
