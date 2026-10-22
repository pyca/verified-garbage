module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawFromTape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleRound
import VerifiedGarbage.Proof.Framework.Offset

/-! Consume and test a complete witness draw while retaining the candidate and policy state. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.MillerRabin.X86

def drawnWitness (candidate : Nat) (m : Mem) (src : BitVec 32) (drawBytes : Nat) : Nat × Bool :=
  Spec.RsaKeyGen.witness (candidate - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr src) drawBytes))

theorem PrimeState.draw {s t : State} {base : Addr} {n len candidate : Nat}
    (S : PrimeState base n candidate s) (F : DrawFrame base len s t) (length : len ≤ 384)
    (K : Keeps [.eax, .ebx, .ecx, .esi] s t) : PrimeState base n candidate t := by
  have C := S.context.frame_keep K (by decide) (by decide) F (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint base (by decide : montgomeryBytes ≤ Layout.witness)
        (by unfold Layout.witness; omega)
    · exact Offset.base_disjoint base (by decide) (by decide))
  apply S.sample C
  exact F.sub (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base base (by
        unfold Layout.witness Layout.arithmetic; omega)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base base (by decide)⟩)

def DrawRoundResult (s : State) (base : Addr) (n len drawBytes remaining candidate : Nat)
    (src : BitVec 32) (t : State) : Prop :=
      PrimeState base n candidate t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.MillerRabin.round candidate (drawnWitness candidate s.mem src drawBytes).1).toNat ∧
      w32 t.mem base witnessUniform = (if (drawnWitness candidate s.mem src drawBytes).2 then 1 else 0) ∧
      t.mem.readW (off base witnessCursor) 32 = src + BitVec.ofNat 32 drawBytes ∧
      t.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 (remaining - drawBytes) ∧
      (∀ d, Layout.control ≤ d → d + 4 ≤ Layout.control + 32 →
        t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32) ∧
      SampleRoundFrame base (s.gpr .esp) len s t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t

theorem draw_round (v : RoundImpl) {s : State} {base : Addr}
    {bytes n len drawBytes remaining candidate : Nat} {src : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (S : PrimeState base n candidate s)
    (stack : RoundRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0) (padded : len ≤ drawBytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (cursor : s.mem.readW (off base witnessCursor) 32 = src)
    (value : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 remaining)
    (room : drawBytes ≤ remaining) (bound : remaining < 2 ^ 32)
    (sourceFit : src.toNat + drawBytes ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) drawBytes)
    (apart : Region.Disjoint ⟨byteAddr src, drawBytes⟩ ⟨base, bytes⟩) :
    WP isa (drawRound v.name v.code n len drawBytes) s
      (DrawRoundResult s base n len drawBytes remaining candidate src) := by
  have lenBound : len ≤ 384 := by omega
  unfold drawRound
  refine WP.seq (WP.mono (draw_from_tape scr capacity (by omega) padded lenBound cursor value room bound
    sourceFit read apart) fun u ⟨copy, next, left, F, Ffine, K⟩ => ?_)
  have U := S.draw F lenBound K
  have Su := scr.of_keeps K (by decide)
  have Ru : RoundRoom (u.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  have spec : drawnWitness candidate s.mem src drawBytes = sampledWitness candidate u.mem base len :=
    draw_witness padded bits copy
  refine WP.mono (sample_round v Su capacity U Ru positive upper lower length aligned bits)
    fun t ⟨T, result, uniform, Ft, controls, Kt⟩ => ?_
  rw [← spec] at result uniform
  refine ⟨T, result, uniform, ?_, ?_, ?_, ?_, (K.mono (by decide)).trans Kt⟩
  · rw [controls witnessCursor (by decide) (by decide), next]
  · rw [controls witnessRemaining (by decide) (by decide), left]
  · intro d lo hi
    rw [controls d lo (by omega), draw_control_before Ffine lenBound lo hi]
  · have first : SampleRoundFrame base (s.gpr .esp) len s u := F.mono (by simp)
    have last : SampleRoundFrame base (s.gpr .esp) len u t := by
      rw [K.1 .esp (by decide)] at Ft
      exact Ft
    exact first.trans last

end VG.Proof.Dsa.X86.Generation
