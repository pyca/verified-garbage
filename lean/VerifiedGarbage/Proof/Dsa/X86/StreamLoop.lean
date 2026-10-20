module

public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.StreamBytes

/-! # Functional correctness and termination of streaming reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

structure StreamInv (n size m len i : Nat) (base : Addr) (p : BitVec 32) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .esi = p + BitVec.ofNat 32 i
  stop : t.gpr .ebx = p + BitVec.ofNat 32 len
  value : wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) i) % m
  lt : wordsVal t.mem base (slot n 6) n < m
  pad : wordsVal t.mem base (slot n 7) n < 2 ^ 32
  mem : Outs base (streamRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem streamLoop_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : 0 < len) (hlen32 : len < 2 ^ 32)
    (inp : StreamInput s base (contextBytes n) p len)
    (hc : s.gpr .esi = p) (he : s.gpr .ebx = p + BitVec.ofNat 32 len) (hv : wordsVal s.mem base (slot n 6) n = 0)
    (hpad : wordsVal s.mem base (slot n 7) n < 2 ^ 32) :
    WP isa (.loop (streamStep n) .ne) s (StreamInv n size m len len base p s) := by
  have init : StreamInv n size m len 0 base p s s := by
    refine ⟨h, by rw [hc]; exact (BitVec.add_zero _).symm, he, ?_, by rw [hv]; omega, hpad, Outs.refl _ _ _,
      Keeps.refl _ _⟩
    rw [hv]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = len - i ∧ i < len ∧ StreamInv n size m len i base p s t)
    ?_ len s ⟨0, rfl, hlen, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  have inpt := inp.keep I.keeps
  refine WP.mono (streamStep_ok I.context hm hi hlen32 I.counter I.stop inpt.fit (inpt.read i hi) I.lt I.pad)
    fun u ⟨cu, count, stop, zf, val, pad, O, K⟩ => ?_
  have next : StreamInv n size m len (i + 1) base p s u := by
    refine ⟨cu, count, stop.trans I.stop, ?_, ?_, pad, I.mem.trans O, I.keeps.trans K⟩
    · rw [val, I.value, inp.byte hi (streamRanges_whole (Nat.le_refl _) I.mem), VG.Proof.Dsa.reduce_prefix_succ]
    · rw [val]; exact Nat.mod_lt _ (by omega)
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, zf, decide_eq_false done, Option.map_some, Bool.not_false]

end VG.Proof.Dsa.X86
