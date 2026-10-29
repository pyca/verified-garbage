module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Square.Dot
public import VerifiedGarbage.Proof.Mont.X86.Square.Lower
public import VerifiedGarbage.Proof.Mont.X86.Square.RedPtr
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Square/RedEnd.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def redEnd : Prog isa := .seq
  (.ite .b (.block [.mov .ebx (.reg .esi)]) (.block []))
  (.block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)])

theorem redEnd_ok {s : State} {W : Addr} {L S N k l : Nat}
    (hw : Ws s W L) (scr : S+52+4*N<L) (ln : l≤N)
    (edi : PtrAt s W .edi S) (cx : PtrAt s W .ecx (S+52+4*l))
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) (bx : s.gpr .ebx = BitVec.ofNat 32 (4*N))
    (cf : s.cf = some (decide (k<N))) :
    WP isa redEnd s fun t =>
      PtrAt t W .ebx (S+52+4*min k N) ∧ t.cf = some (decide (l<min k N)) ∧
      t.mem = s.mem ∧ Keeps [.ebx] s t ∧ t.xmm = s.xmm := by
  have select : WP isa (.ite .b (.block [.mov .ebx (.reg .esi)]) (.block [])) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (4*min k N) ∧ t.mem = s.mem ∧ Keeps [.ebx] s t ∧ t.xmm = s.xmm := by
    refine WP.ite (decide (k<N)) (by change s.cf = _; exact cf) ?_ ?_
    · intro yes
      have lt : k<N := of_decide_eq_true yes
      refine VG.X86.Wp.cons rfl (WP.block_nil ?_)
      have u := VG.X86.Wp.Upd.setReg s .ebx (s.gpr .esi)
      exact ⟨by rw [u.gpr, si, Nat.min_eq_left (by omega)], rfl, u.keeps, rfl⟩
    · intro no
      have le : N≤k := by have := of_decide_eq_false no; omega
      exact WP.block_nil ⟨by rw [Nat.min_eq_right le]; exact bx, rfl, Keeps.refl _ _, rfl⟩
  unfold redEnd
  refine WP.seq (WP.mono select fun t1 ⟨bx1, m1, K1, x1⟩ => ?_)
  have body : WP isa (.block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)])
      t1 fun t => PtrAt t W .ebx (S+52+4*min k N) ∧ t.cf = some (decide (l<min k N)) ∧
        t.mem = t1.mem ∧ Keeps [.ebx] t1 t := by
    refine wp_addS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => wp_cmpCF rfl fun t4 f4 cf4 => WP.block_nil ?_
    have ei : t1.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq
      rw [K1.1 _ (by decide), edi, BitVec.toNat_ofNat]
    have b3 : t3.gpr .ebx = BitVec.ofNat 32 (W.toNat+S+52+4*min k N) := by
      rw [u3.gpr, u2.gpr, bx1, ei]
      change (BitVec.ofNat 32 (4*min k N)+BitVec.ofNat 32 (W.toNat+S))+BitVec.ofNat 32 52 = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
    have c3 : (t3.gpr .ecx).toNat = W.toNat+(S+52+4*l) := by
      rw [u3.other _ (by decide), u2.other _ (by decide), K1.1 _ (by decide), cx, Nat.mod_eq_of_lt (by have := hw.nowrap; omega)]
    refine ⟨?_, ?_, f4.mem.trans (u3.mem.trans u2.mem), u2.keeps.trans (u3.keeps.trans (f4.keeps _))⟩
    · rw [PtrAt, f4.gpr, b3, BitVec.toNat_ofNat]; congr 1; omega
    · rw [cf4, c3, b3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hw.nowrap; have := Nat.min_le_right k N; omega)]
      have e : W.toNat+(S+52+4*l)<W.toNat+S+52+4*min k N ↔ l<min k N := by omega
      simp only [e]
  exact WP.mono (scalar_frame (by simp [scalar]) body)
    fun t ⟨⟨b, cf', mem, keep⟩, xmm⟩ => ⟨b, cf', mem.trans m1, K1.trans keep, xmm.trans x1⟩

end VG.Proof.Mont.X86.Square
end

end

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
  have qp : q≤k := by dsimp [q]; omega_arith
  have qn : q≤N := by dsimp [q]; omega_arith
  have kn : k-q<N := by dsimp [q]; omega_arith
  have Kp : 0<K ↔ q<min k N := by dsimp [K, redCount, q]; omega_arith
  have qK : q+K = min k N := by dsimp [K, redCount, q]; omega_arith
  have Km : K≤k-q := by dsimp [K, redCount, q]; omega_arith
  unfold redStage
  refine WP.seq (WP.mono (lower_ok ha (.inr rfl) hN h8 hk si) fun t1 ⟨dx1, bx1, m1, K1, x1⟩ => ?_)
  have ha1 := ha.of_keeps K1 (by decide) (by rw [m1]; exact Outs.refl _ _ _)
  have ws1 := hw.of_keeps K1
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
  have edi1 : PtrAt t1 W .edi S := by rw [PtrAt, K1.1 _ (by decide)]; exact edi
  refine WP.seq (WP.mono (redPtr_ok ha1 base argMeq edi1 qp (by omega_arith) h8 hk dx1 si1 bx1)
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
      rw [ebx3, Nat.mod_eq_of_lt (by have := hw.nowrap; have := Nat.min_le_right k N; omega_arith)]
    have cmp : ∀ j≤K, (W.toNat+(S+52+4*q)+4*j <
        if Reg.ebx = .ebp then W.toNat+(m+4*(k-q)-4*j) else (t3.gpr .ebx).toNat) ↔ j<K := by
      intro j hj
      simp only [show Reg.ebx ≠ Reg.ebp by decide, ↓reduceIte, endEq]
      omega_arith
    have d := dotLoop_ok (r := .ebx) (.inr rfl) ws3 left3 right3
      (by rw [xmm]; exact low) (by rw [xmm]; exact high) pos (by omega_arith) (by omega_arith) (by omega_arith) cmp
    change WP isa (.loop (.block (VG.Impl.Mont.X86.Rt.Square.prod ++ ctl .ebx)) .b) t3 _
    refine WP.mono d fun u du => ?_
    refine ⟨?_, ?_, by rw [du.c3, xmm], by rw [du.c7, xmm], du.mem.trans mem, before.trans (du.keep.mono (by decide))⟩
    · simpa only [redLow, dotProd, mem, BitVec.ofNat_add] using du.low
    · simpa only [redHigh, dotProd, mem, BitVec.ofNat_add] using du.high
  · intro no
    have zero : K=0 := by have := of_decide_eq_false no; omega_arith
    apply WP.block_nil
    refine ⟨?_, ?_, by rw [xmm], by rw [xmm], mem, before⟩
    · rw [xmm, low]
      simp only [redLow, show redCount N k=0 from zero, total, Nat.add_zero]
    · rw [xmm, high]
      simp only [redHigh, show redCount N k=0 from zero, total, Nat.add_zero]

end VG.Proof.Mont.X86.Square
