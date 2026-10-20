module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchControl

/-! # Advance exactly once after a rejected p candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem pSearchAdvance_ok {s : State} {base : Addr} {counter stride limit : Nat}
    (C : SearchControl base counter stride s) (more : counter < limit) (bound : limit ≤ 12288) :
    WP isa (pSearchAdvance limit stride) s fun t => SearchControl base (counter + 1) stride t ∧
      t.mem.readW (off base 8) 32 = BitVec.ofNat 32 (if counter + 1 < limit then 3 else 2) ∧
      Outside base 0 12 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold pSearchAdvance
  refine WP.seq (WP.mono (pSearchAdvanceHead_ok C.scr (by decide) (by omega) (by omega) C.count C.offset)
    fun a ⟨count, position, cf, Oa, Ka⟩ => ?_)
  have Ca : SearchControl base (counter + 1) stride a :=
    ⟨C.scr.of_keeps Ka (by decide), count, by simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using position⟩
  have finish (status : Nat) : WP isa (.block (pSearchStatus status)) a fun t => SearchControl base (counter + 1) stride t ∧
      t.mem.readW (off base 8) 32 = BitVec.ofNat 32 status ∧
      Outside base 0 12 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
    refine WP.mono (pSearchStatus_ok Ca status) fun t ⟨Ct, value, Ot, Kt⟩ => ?_
    exact ⟨Ct, value, (Oa.mono (by omega) (by omega)).trans Ot, Ka.trans (Kt.mono (by decide))⟩
  by_cases again : counter + 1 < limit
  · rw [ite_eq_left again]
    exact WP.ite true (by simp [eval, cf, again]) (fun _ => finish 3) (fun h => Bool.noConfusion h)
  · rw [ite_eq_right again]
    exact WP.ite false (by simp [eval, cf, again]) (fun h => Bool.noConfusion h) (fun _ => finish 2)
end VG.Proof.Dsa.X86.Generation
