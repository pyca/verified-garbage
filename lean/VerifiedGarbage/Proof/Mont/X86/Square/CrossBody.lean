module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Square.PairStage
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Mont.X86.Square.DiagMul
public import VerifiedGarbage.Proof.Mont.X86.Square.DiagPtr
public import VerifiedGarbage.Proof.Mont.X86.Square.Double

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Square/CrossTail.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def diagProduct (s : State) (W : Addr) (a k : Nat) : Nat :=
  w32 s.mem W (a+4*(k/2)) * w32 s.mem W (a+4*(k/2))

def crossTail : Prog isa := .seq (.block double) (.ite .e (.block (diagPtr ++ diagMul)) (.block []))

theorem crossTail_ok {s : State} {W : Addr} {L a N k l h : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (al : a+4*N ≤ L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (h8 : 8*N < 2^32) (hk : k<2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h)) :
    WP isa crossTail s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (2*l + if k%2=0 then diagProduct s W a k % 2^32 else 0)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (2*h + if k%2=0 then diagProduct s W a k / 2^32 else 0)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
  let t1 := doubleState s
  have d := double_values low high si
  change t1.xmm .xmm0 = _ ∧ t1.xmm .xmm1 = _ ∧ t1.xmm .xmm3 = _ ∧ t1.xmm .xmm7 = _ ∧
    t1.mem = _ ∧ Keeps [.eax] s t1 ∧ t1.zf = _ at d
  have ha1 := ha.of_keeps d.2.2.2.2.2.1 (by decide) (by rw [d.2.2.2.2.1]; exact Outs.refl _ _ _)
  have hw1 := hw.of_keeps d.2.2.2.2.2.1
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (d.2.2.2.2.2.1.1 _ (by decide)).trans si
  unfold crossTail
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨t1, run_double s, ?_⟩
  refine WP.ite (decide (k%2=0)) (by change t1.zf = _; exact d.2.2.2.2.2.2) ?_ ?_
  · intro yes
    have even : k%2=0 := of_decide_eq_true yes
    apply WP.block_append
    refine WP.mono (diagPtr_ok ha1 base argAeq si1 (by omega) even) fun t2 ⟨ptr, m2, K2, x2⟩ => ?_
    have hw2 := hw1.of_keeps K2
    refine WP.mono (diagMul_ok hw2 ptr (by omega)) fun t eq => ?_
    subst t
    have low2 : t2.xmm .xmm0 = packed (BitVec.ofNat 64 (2*l)) := by rw [x2]; exact d.1
    have high2 : t2.xmm .xmm1 = packed (BitVec.ofNat 64 (2*h)) := by rw [x2]; exact d.2.1
    have v := prod_values (t2.mem.readW (off W (a+4*(k/2))) 32)
      (t2.mem.readW (off W (a+4*(k/2))) 32) low2 high2
    have frame := prod_frame t2 (t2.mem.readW (off W (a+4*(k/2))) 32)
      (t2.mem.readW (off W (a+4*(k/2))) 32)
    have mem2 : t2.mem = s.mem := m2.trans d.2.2.2.2.1
    refine ⟨?_, ?_, ?_, ?_, frame.2.trans mem2, ?_⟩
    · rw [v.1, mem2]
      simp only [even, ↓reduceIte, diagProduct, w32, BitVec.ofNat_add]
    · rw [v.2.1, mem2]
      simp only [even, ↓reduceIte, diagProduct, w32, BitVec.ofNat_add]
    · rw [v.2.2.1, x2, d.2.2.1]
    · rw [v.2.2.2, x2, d.2.2.2.1]
    · exact (d.2.2.2.2.2.1.mono (by decide)).trans (K2.trans frame.1)
  · intro no
    have odd : ¬ k%2=0 := of_decide_eq_false no
    apply WP.block_nil
    simpa only [odd, ↓reduceIte, Nat.add_zero] using
      (show t1.xmm .xmm0 = packed (BitVec.ofNat 64 (2*l)) ∧
        t1.xmm .xmm1 = packed (BitVec.ofNat 64 (2*h)) ∧ t1.xmm .xmm3 = s.xmm .xmm3 ∧
        t1.xmm .xmm7 = s.xmm .xmm7 ∧ t1.mem = s.mem ∧ Keeps [.eax, .edx] s t1 from
        ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2.1.mono (by decide)⟩)

end VG.Proof.Mont.X86.Square
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
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
