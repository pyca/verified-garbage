module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCount
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundDecision

/-! A failed round stops; successful rounds update both policy counters. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

def nextStatus (passed : Bool) (i uniform checks : Nat) (u : Bool) : Nat :=
  if passed then if i + 1 < 17 ∨ uniform + u.toNat < checks then 4 else 1 else 3

def countMemory (m : Mem) (base : Addr) (i uniform : Nat) (u : Bool) : Mem :=
  (m.writeW (off base roundIndex) (BitVec.ofNat 32 (i + 1))).writeW
    (off base uniformCount) (BitVec.ofNat 32 (uniform + u.toNat))

theorem round_outcome {s : State} {base : Addr} {bytes i uniform checks : Nat} {passed u : Bool}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (index : s.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i)
    (count : s.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform)
    (witness : s.mem.readW (off base witnessUniform) 32 = BitVec.ofNat 32 u.toNat)
    (hi : i + 1 < 2 ^ 32) (hu : uniform + u.toNat < 2 ^ 32) (hc : checks < 2 ^ 32)
    (zf : s.zf = some (!passed)) :
    WP isa (roundOutcome checks) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextStatus passed i uniform checks u) ∧
      t.mem = (if passed then countMemory s.mem base i uniform u else s.mem) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  unfold roundOutcome
  cases passed
  · refine WP.ite true zf ?_ (by intro h; cases h)
    intro _
    refine wp_movS rfl fun t T _ => WP.block_nil ?_
    exact ⟨T.gpr, T.mem, T.keeps.mono (by decide)⟩
  · refine WP.ite false zf (by intro h; cases h) ?_
    intro _
    refine WP.seq (WP.mono (round_count scr capacity index count witness)
      fun a ⟨ia, ua, ma, Ka⟩ => ?_)
    refine WP.mono (round_decision hi hu hc ia ua) fun t ⟨value, mem, Kt⟩ => ?_
    exact ⟨value, mem.trans ma, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
