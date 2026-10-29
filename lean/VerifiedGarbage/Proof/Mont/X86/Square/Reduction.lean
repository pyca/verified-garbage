module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.DigitFull
public import VerifiedGarbage.Proof.Mont.X86.Square.OutStore
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Square.RedStage
public import VerifiedGarbage.Proof.Mont.X86.Square.Width
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

import VerifiedGarbage.Proof.Mont.X86.Square.Store
import VerifiedGarbage.Proof.Mont.X86.Square.EndCtl

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Square/Snapshot.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def snapshot : List Instr := [.movqStore (sc 20) .xmm0] ++ widthTest

theorem snapshot_ok {s : State} {W : Addr} {L S N k l : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (sl : S+20+8≤L)
    (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l)) :
    WP isa (.block snapshot) s fun t =>
      t.mem = s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 l) ∧
      t.cf = some (decide (k<N)) ∧ Keeps [.eax] s t ∧ t.xmm = s.xmm := by
  unfold snapshot
  apply WP.block_append
  refine WP.mono (storePacked_ok hw edi sl low) fun t1 eq => ?_
  subst t1
  have K1 := writeState_keep s (off W (S+20)) (BitVec.ofNat 64 l)
  have O : Outside W (S+20) 8 s.mem (writeState s (off W (S+20)) (BitVec.ofNat 64 l)).mem := by
    exact writeW_outside _ _ _ (by have := hw.nowrap; omega)
  have ha1 := ha.of_keeps K1 (by simp) (Outs.of_outside (O.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  refine WP.mono (widthTest_ok ha1 hN h8 hk si) fun t ⟨cf, mem, keep, xmm⟩ => ?_
  exact ⟨mem, cf, (K1.mono (by simp)).trans keep, xmm⟩

end VG.Proof.Mont.X86.Square
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def reductionCode : Prog isa := .seq redStage (.seq (.block snapshot)
  (.ite .b (.block digitFull) (.block outStore)))

theorem reductionCode_ok {s : State} {W : Addr} {L S m inv N k l h : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (ml : m+4*N≤L) (il : inv+4≤L) (scr : S+12*N+56≤L)
    (sepM : m+4*N≤S ∨ S+12*N+56≤m) (sepI : inv+4≤S ∨ S+12*N+56≤inv)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (mv : A 3 = BitVec.ofNat 32 m) (iv : A 4 = BitVec.ofNat 32 inv)
    (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h)) :
    WP isa reductionCode s fun t =>
      let lo := l+redLow s W S m N k
      let hi := h+redHigh s W S m N k
      let q := if k<N then ((lo%2^32)*w32 s.mem W inv)%2^32 else 0
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (lo+(q*w32 s.mem W m)%2^32)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (hi+(q*w32 s.mem W m)/2^32)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = (s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)).writeW (off W (S+52+4*k))
        (BitVec.ofNat 32 (if k<N then q else lo)) ∧
      Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t := by
  let lo := l+redLow s W S m N k
  let hi := h+redHigh s W S m N k
  let q := if k<N then ((lo%2^32)*w32 s.mem W inv)%2^32 else 0
  change WP isa reductionCode s fun t =>
    t.xmm .xmm0 = packed (BitVec.ofNat 64 (lo+(q*w32 s.mem W m)%2^32)) ∧
    t.xmm .xmm1 = packed (BitVec.ofNat 64 (hi+(q*w32 s.mem W m)/2^32)) ∧
    t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
    t.mem = (s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo)).writeW (off W (S+52+4*k))
      (BitVec.ofNat 32 (if k<N then q else lo)) ∧ Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t
  unfold reductionCode
  refine WP.seq (WP.mono (redStage_ok ha hw ml (by omega_arith) base mv hN h8 hk edi si low high)
    fun t1 ⟨low1, high1, c31, c71, mem1, K1⟩ => ?_)
  have ha1 := ha.of_keeps K1 (by decide) (by rw [mem1]; exact Outs.refl _ _ _)
  have ws1 := hw.of_keeps K1
  have edi1 : PtrAt t1 W .edi S := by rw [PtrAt, K1.1 _ (by decide)]; exact edi
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
  refine WP.seq (WP.mono (snapshot_ok ha1 ws1 (by omega_arith) hN h8 hk edi1 si1 low1)
    fun t2 ⟨mem2, cf2, K2, x2⟩ => ?_)
  have O : Outside W (S+20) 8 s.mem t2.mem := by
    rw [mem2, mem1]
    exact writeW_outside _ _ _ (by have := hw.nowrap; omega_arith)
  have allK : Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t2 := K1.trans (K2.mono (by decide))
  have ha2 := ha.of_keeps allK (by decide)
    (Outs.of_outside (O.mono (Nat.zero_le _) (by omega_arith)) (List.mem_singleton_self _))
  have ws2 := ws1.of_keeps K2
  have edi2 : PtrAt t2 W .edi S := by rw [PtrAt, K2.1 _ (by decide)]; exact edi1
  have si2 : t2.gpr .esi = BitVec.ofNat 32 (4*k) := (K2.1 _ (by decide)).trans si1
  have mem2' : t2.mem = s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 lo) := by
    rw [mem2, mem1]
  have low2 : t2.xmm .xmm0 = packed (BitVec.ofNat 64 lo) := by rw [x2]; exact low1
  have high2 : t2.xmm .xmm1 = packed (BitVec.ofNat 64 hi) := by rw [x2]; exact high1
  have wm : w32 t2.mem W m = w32 s.mem W m := O.w32 (by omega_arith) (by have := hw.nowrap; omega_arith)
  have wi : w32 t2.mem W inv = w32 s.mem W inv := O.w32 (by omega_arith) (by have := hw.nowrap; omega_arith)
  have wl : w32 t2.mem W (S+20) = lo%2^32 := by rw [mem2']; exact write64_w32 _ _ _ _
  refine WP.ite (decide (k<N)) (by change t2.cf = _; exact cf2) ?_ ?_
  · intro yes
    have small : k<N := of_decide_eq_true yes
    have qeq : digit t2 W S inv = q := by
      unfold digit q
      rw [wl, wi, ite_eq_left small]
    refine WP.mono (digitFull_ok ha2 ws2 base iv mv il (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) edi2 si2 low2 high2) fun t ⟨lo3, hi3, c33, c73, mem3, K3⟩ => ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, allK.trans K3⟩
    · simpa only [qeq, wm] using lo3
    · simpa only [qeq, wm] using hi3
    · rw [c33, x2, c31]
    · rw [c73, x2, c71]
    · rw [mem3, mem2', qeq]
      simp only [small, ↓reduceIte]
  · intro no
    have large : ¬ k<N := of_decide_eq_false no
    have qz : q=0 := by simp only [q, large, ↓reduceIte]
    refine WP.mono (outStore_ok ws2 (by omega_arith) (by omega_arith) edi2 si2) fun t ⟨mem3, K3, x3⟩ => ?_
    have word : t2.mem.readW (off W (S+20)) 32 = BitVec.ofNat 32 lo := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      exact wl
    refine ⟨?_, ?_, ?_, ?_, ?_, allK.trans (K3.mono (by decide))⟩
    · rw [x3, low2]
      simp only [qz, Nat.zero_mul, Nat.zero_mod, Nat.add_zero]
    · rw [x3, high2]
      simp only [qz, Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    · rw [x3, x2, c31]
    · rw [x3, x2, c71]
    · rw [mem3, word, mem2']
      simp only [large, ↓reduceIte]

end VG.Proof.Mont.X86.Square
