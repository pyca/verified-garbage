module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.DiagMul
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Square.CrossPtr
public import VerifiedGarbage.Proof.Mont.X86.Square.Dot
public import VerifiedGarbage.Proof.Mont.X86.Square.Lower
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.TCB.Code

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def pairCount (N k : Nat) : Nat := (k+1)/2-(k+1-N)
def pairLow (s : State) (W : Addr) (a N k : Nat) : Nat :=
  total (fun j => dotProd s W (a+4*(k+1-N)) (a+4*(k-(k+1-N))) j % 2^32) (pairCount N k)
def pairHigh (s : State) (W : Addr) (a N k : Nat) : Nat :=
  total (fun j => dotProd s W (a+4*(k+1-N)) (a+4*(k-(k+1-N))) j / 2^32) (pairCount N k)

def pairStage : Prog isa := .seq (lower .eax) (.seq (.block crossPtr)
  (.ite .b VG.Impl.Mont.X86.Rt.Square.pairLoop (.block [])))

theorem pairStage_ok {s : State} {W : Addr} {L a N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (al : a+4*N ≤ L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (hN : N = 2*(A 2).toNat) (h8 : 8*N < 2^32) (hk : k+1 < 2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (z0 : s.xmm .xmm0 = packed 0) (z1 : s.xmm .xmm1 = packed 0) :
    WP isa pairStage s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (pairLow s W a N k)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (pairHigh s W a N k)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t := by
  let l := k+1-N
  let K := pairCount N k
  have lp : l≤k := by dsimp [l]; omega
  have ln : l<N := by dsimp [l]; omega
  have kn : k-l<N := by dsimp [l]; omega
  have kpos : 0<K ↔ 2*l<k := by dsimp [K, l, pairCount]; omega
  have lK : l+K = (k+1)/2 := by dsimp [K, l, pairCount]; omega
  have Kn : K≤k-l := by dsimp [K, l, pairCount]; omega
  unfold pairStage
  refine WP.seq (WP.mono (lower_ok ha (.inl rfl) hN h8 (by omega) si) fun t1 ⟨dx1, _, m1, K1, x1⟩ => ?_)
  have ha1 := ha.of_keeps K1 (by decide) (by rw [m1]; exact Outs.refl _ _ _)
  have ws1 := hw.of_keeps K1
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
  refine WP.seq (WP.mono (crossPtr_ok ha1 ws1 al base argAeq ln kn lp dx1 si1)
    fun t2 ⟨left, right, cf2, m2, K2, x2⟩ => ?_)
  have before : Keeps [.eax, .edx, .ecx, .ebp] s t2 :=
    (K1.mono (by decide)).trans (K2.mono (by decide))
  have mem : t2.mem = s.mem := m2.trans m1
  have xmm : t2.xmm = s.xmm := x2.trans x1
  refine WP.ite (decide (2*l<k)) (by change t2.cf = _; exact cf2) ?_ ?_
  · intro pos
    have Kp : 0<K := kpos.mpr (of_decide_eq_true pos)
    have cmp : ∀ j≤K, (W.toNat+(a+4*l)+4*j < W.toNat+(a+4*(k-l)-4*j)) ↔ j<K := by
      intro j hj
      omega
    have d := dotLoop_ok (r := .ebp) (.inl rfl) (ws1.of_keeps K2) left right
      (by rw [xmm]; exact z0) (by rw [xmm]; exact z1) Kp (by omega) (by omega) (by omega)
      (by simpa using cmp)
    change WP isa (.loop (.block (VG.Impl.Mont.X86.Rt.Square.prod ++ ctl .ebp)) .b) t2 _
    refine WP.mono d fun u du => ?_
    refine ⟨?_, ?_, ?_, ?_, du.mem.trans mem, before.trans du.keep⟩
    · simpa [pairLow, pairCount, dotProd, mem, l, K] using du.low
    · simpa [pairHigh, pairCount, dotProd, mem, l, K] using du.high
    · rw [du.c3, xmm]
    · rw [du.c7, xmm]
  · intro no
    have Kz : K=0 := by have := of_decide_eq_false no; omega
    apply WP.block_nil
    refine ⟨?_, ?_, ?_, ?_, mem, before⟩
    · rw [xmm, z0]
      simp only [pairLow, show pairCount N k = 0 from Kz, total]
      rfl
    · rw [xmm, z1]
      simp only [pairHigh, show pairCount N k = 0 from Kz, total]
      rfl
    · rw [xmm]
    · rw [xmm]

end VG.Proof.Mont.X86.Square
