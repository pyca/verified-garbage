module

public import VerifiedGarbage.Proof.Mont.X86.Square.CrossTail

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def inputLow (s : State) (W : Addr) (a N k : Nat) : Nat :=
  2*pairLow s W a N k + if k%2=0 then diagProduct s W a k % 2^32 else 0
def inputHigh (s : State) (W : Addr) (a N k : Nat) : Nat :=
  2*pairHigh s W a N k + if k%2=0 then diagProduct s W a k / 2^32 else 0

theorem crossBody_ok {s : State} {W : Addr} {L a N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (al : a+4*N ≤ L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (hN : N = 2*(A 2).toNat) (h8 : 8*N < 2^32) (hk : k+1 < 2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (z0 : s.xmm .xmm0 = packed 0) (z1 : s.xmm .xmm1 = packed 0) :
    WP isa VG.Impl.Mont.X86.Rt.Square.crossBody s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (inputLow s W a N k)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (inputHigh s W a N k)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t := by
  have body : WP isa (.seq pairStage crossTail) s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (inputLow s W a N k)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (inputHigh s W a N k)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t := by
    refine WP.seq (WP.mono (pairStage_ok ha hw al base argAeq hN h8 hk si z0 z1)
      fun t1 ⟨low, high, c3, c7, mem, keep⟩ => ?_)
    have ha1 := ha.of_keeps keep (by decide) (by rw [mem]; exact Outs.refl _ _ _)
    have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (keep.1 _ (by decide)).trans si
    refine WP.mono (crossTail_ok ha1 (hw.of_keeps keep) al base argAeq h8 (by omega) si1 low high)
      fun u ⟨lo, hi, c3', c7', mem', keep'⟩ => ?_
    refine ⟨?_, ?_, c3'.trans c3, c7'.trans c7, mem'.trans mem, keep.trans (keep'.mono (by decide))⟩
    · simpa only [diagProduct, mem, inputLow] using lo
    · simpa only [diagProduct, mem, inputHigh] using hi
  simpa only [VG.Impl.Mont.X86.Rt.Square.crossBody, VG.Impl.Mont.X86.Rt.Square.seqs, pairStage, lower, crossPtr, crossTail,
    double, diagPtr, diagMul, VG.Impl.Mont.X86.Rt.ptr, WP.seq_iff (M := isa), List.cons_append, List.nil_append] using body

end VG.Proof.Mont.X86.Square
