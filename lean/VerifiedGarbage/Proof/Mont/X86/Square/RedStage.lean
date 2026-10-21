module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Square.Dot
public import VerifiedGarbage.Proof.Mont.X86.Square.Lower
public import VerifiedGarbage.Proof.Mont.X86.Square.RedPtr
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Square.RedEnd

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def redCount (N k : Nat) : Nat := min k N-(k+1-N)
def redLow (s : State) (W : Addr) (S m N k : Nat) : Nat :=
  total (fun j => dotProd s W (S+52+4*(k+1-N)) (m+4*(k-(k+1-N))) j % 2^32) (redCount N k)
def redHigh (s : State) (W : Addr) (S m N k : Nat) : Nat :=
  total (fun j => dotProd s W (S+52+4*(k+1-N)) (m+4*(k-(k+1-N))) j / 2^32) (redCount N k)

def redStage : Prog isa := .seq (lower .ebx) (.seq (.block redPtr) (.seq redEnd
  (.ite .b VG.Impl.Mont.X86.Rt.Square.redLoop (.block []))))

theorem redStage_ok {s : State} {W : Addr} {L S m N k l h : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (ml : m+4*N≤L) (scr : S+52+4*N<L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argMeq : A 3 = BitVec.ofNat 32 m)
    (hN : N = 2*(A 2).toNat) (h8 : 8*N < 2^32) (hk : k<2*N)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h)) :
    WP isa redStage s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (l+redLow s W S m N k)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (h+redHigh s W S m N k)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t := by
  let q := k+1-N
  let K := redCount N k
  have qp : q≤k := by dsimp [q]; omega
  have qn : q≤N := by dsimp [q]; omega
  have kn : k-q<N := by dsimp [q]; omega
  have Kp : 0<K ↔ q<min k N := by dsimp [K, redCount, q]; omega
  have qK : q+K = min k N := by dsimp [K, redCount, q]; omega
  have Km : K≤k-q := by dsimp [K, redCount, q]; omega
  unfold redStage
  refine WP.seq (WP.mono (lower_ok ha (.inr rfl) hN h8 hk si) fun t1 ⟨dx1, bx1, m1, K1, x1⟩ => ?_)
  have ha1 := ha.of_keeps K1 (by decide) (by rw [m1]; exact Outs.refl _ _ _)
  have ws1 := hw.of_keeps K1
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
  have edi1 : PtrAt t1 W .edi S := by rw [PtrAt, K1.1 _ (by decide)]; exact edi
  refine WP.seq (WP.mono (redPtr_ok ha1 base argMeq edi1 qp (by omega) h8 hk dx1 si1 bx1)
    fun t2 ⟨left, right, cf2, m2, K2, x2⟩ => ?_)
  have ws2 := ws1.of_keeps K2
  have edi2 : PtrAt t2 W .edi S := by rw [PtrAt, K2.1 _ (by decide)]; exact edi1
  refine WP.seq (WP.mono (redEnd_ok ws2 scr qn edi2 left
    (by rw [K2.1 _ (by decide)]; exact si1) (by rw [K2.1 _ (by decide)]; exact bx1) cf2)
    fun t3 ⟨ebx3, cf3, m3, K3, x3⟩ => ?_)
  have before : Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t3 :=
    (K1.mono (by decide)).trans ((K2.mono (by decide)).trans (K3.mono (by decide)))
  have mem : t3.mem = s.mem := m3.trans (m2.trans m1)
  have xmm : t3.xmm = s.xmm := x3.trans (x2.trans x1)
  have left3 : PtrAt t3 W .ecx (S+52+4*q) := by rw [PtrAt, K3.1 _ (by decide)]; exact left
  have right3 : PtrAt t3 W .ebp (m+4*(k-q)) := by rw [PtrAt, K3.1 _ (by decide)]; exact right
  have ws3 := ws2.of_keeps K3
  refine WP.ite (decide (q<min k N)) (by change t3.cf = _; exact cf3) ?_ ?_
  · intro yes
    have pos : 0<K := Kp.mpr (of_decide_eq_true yes)
    have endEq : (t3.gpr .ebx).toNat = W.toNat+(S+52+4*min k N) := by
      rw [ebx3, Nat.mod_eq_of_lt (by have := hw.nowrap; have := Nat.min_le_right k N; omega)]
    have cmp : ∀ j≤K, (W.toNat+(S+52+4*q)+4*j <
        if Reg.ebx = .ebp then W.toNat+(m+4*(k-q)-4*j) else (t3.gpr .ebx).toNat) ↔ j<K := by
      intro j hj
      simp only [show Reg.ebx ≠ Reg.ebp by decide, ↓reduceIte, endEq]
      omega
    have d := dotLoop_ok (r := .ebx) (.inr rfl) ws3 left3 right3
      (by rw [xmm]; exact low) (by rw [xmm]; exact high) pos (by omega) (by omega) (by omega) cmp
    change WP isa (.loop (.block (VG.Impl.Mont.X86.Rt.Square.prod ++ ctl .ebx)) .b) t3 _
    refine WP.mono d fun u du => ?_
    refine ⟨?_, ?_, by rw [du.c3, xmm], by rw [du.c7, xmm], du.mem.trans mem, before.trans (du.keep.mono (by decide))⟩
    · simpa only [redLow, dotProd, mem, BitVec.ofNat_add] using du.low
    · simpa only [redHigh, dotProd, mem, BitVec.ofNat_add] using du.high
  · intro no
    have zero : K=0 := by have := of_decide_eq_false no; omega
    apply WP.block_nil
    refine ⟨?_, ?_, by rw [xmm], by rw [xmm], mem, before⟩
    · rw [xmm, low]
      simp only [redLow, show redCount N k=0 from zero, total, Nat.add_zero]
    · rw [xmm, high]
      simp only [redHigh, show redCount N k=0 from zero, total, Nat.add_zero]

end VG.Proof.Mont.X86.Square
