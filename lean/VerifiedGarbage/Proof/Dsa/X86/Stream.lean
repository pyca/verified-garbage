module

public import VerifiedGarbage.Proof.Dsa.X86.StreamInit

/-! # Complete streaming reduction, including the empty input -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : len < 2 ^ 32)
    (inp : StreamInput s base (contextBytes n) p len) (hp : s.mem.readW (off base sourcePointer) 32 = p) :
    WP isa (reduceStream n len) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold reduceStream
  refine WP.seq (WP.mono (streamInit_ok h) fun u ⟨cu, count, Y, B, O, K⟩ => ?_)
  by_cases hz : len = 0
  · rw [ite_eq_left hz]
    refine WP.block_nil ⟨cu, ?_, O, K⟩
    rw [Y, hz]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  · rw [ite_eq_right hz]
    have source : u.mem.readW (off base sourcePointer) 32 = p := (streamRanges_header O).trans hp
    refine WP.mono (streamLoop_ok cu hm (by omega) hlen (inp.keep K) source count Y (by rw [B]; decide))
      fun t I => ?_
    refine ⟨I.context, ?_, O.trans I.mem, K.trans I.keeps⟩
    rw [I.value, inp.bytes (streamRanges_whole (Nat.le_refl _) O)]

end VG.Proof.Dsa.X86
