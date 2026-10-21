module

public import VerifiedGarbage.Proof.Mont.X86.Square.CrossBody

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def crossGuard : List Instr := lenTimes .eax 1 ++ [.alu .sub .eax (.imm 4), .alu .cmp .esi (.reg .eax)]

theorem crossGuard_ok {s : State} {W : Addr} {L N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block crossGuard) s fun t => t.cf = some (decide (k+1<2*N)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block crossGuard) s fun t => t.cf = some (decide (k+1<2*N)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
    unfold crossGuard
    apply WP.block_append
    refine WP.mono (lenTimes_ok ha (r := .eax) 1) fun t1 ⟨len, mem, keep⟩ => ?_
    have ea : t1.gpr .eax = BitVec.ofNat 32 (8*N) := by
      apply BitVec.eq_of_toNat_eq
      rw [len, BitVec.toNat_ofNat, hN]
      congr 1
      omega
    have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (keep.1 _ (by decide)).trans si
    refine wp_subS rfl fun t2 u2 _ => wp_cmpCF rfl fun t3 f3 cf => WP.block_nil ?_
    have ea2 : t2.gpr .eax = BitVec.ofNat 32 (8*N-4) := by
      rw [u2.gpr, ea]
      change BitVec.ofNat 32 (8*N) - BitVec.ofNat 32 4 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    refine ⟨?_, f3.mem.trans (u2.mem.trans mem), keep.trans (u2.keeps.trans (f3.keeps _))⟩
    rw [cf, u2.other _ (by decide), si1, ea2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have e : 4*k<8*N-4 ↔ k+1<2*N := by omega
    simp only [e]
  exact WP.mono (scalar_frame (by simp [crossGuard, lenTimes, scalar]) body)
    fun t ⟨⟨cf, mem, keep⟩, xmm⟩ => ⟨cf, mem, keep, xmm⟩

theorem cross_ok {s : State} {W : Addr} {L a N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (al : a+4*N ≤ L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (hN : N = 2*(A 2).toNat) (h8 : 8*N < 2^32) (hk : k<2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (z0 : s.xmm .xmm0 = packed 0) (z1 : s.xmm .xmm1 = packed 0) :
    WP isa VG.Impl.Mont.X86.Rt.Square.cross s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (inputLow s W a N k)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (inputHigh s W a N k)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ecx, .ebp] s t := by
  change WP isa (.seq (.block crossGuard) (.ite .b VG.Impl.Mont.X86.Rt.Square.crossBody (.block []))) s _
  refine WP.seq (WP.mono (crossGuard_ok ha hN h8 hk si) fun t1 ⟨cf, mem, keep, xmm⟩ => ?_)
  refine WP.ite (decide (k+1<2*N)) (by change t1.cf = _; exact cf) ?_ ?_
  · intro yes
    have before := ha.of_keeps keep (by decide) (by rw [mem]; exact Outs.refl _ _ _)
    refine WP.mono (crossBody_ok before (hw.of_keeps keep) al base argAeq hN h8 (of_decide_eq_true yes)
      (by rw [keep.1 _ (by decide)]; exact si) (by rw [xmm]; exact z0) (by rw [xmm]; exact z1))
      fun u ⟨lo, hi, c3, c7, m2, K2⟩ => ?_
    refine ⟨?_, ?_, by rw [c3, xmm], by rw [c7, xmm], m2.trans mem, (keep.mono (by decide)).trans K2⟩
    · simpa only [inputLow, pairLow, diagProduct, dotProd, mem] using lo
    · simpa only [inputHigh, pairHigh, diagProduct, dotProd, mem] using hi
  · intro no
    have last : k+1=2*N := by have := of_decide_eq_false no; omega
    have odd : ¬ k%2=0 := by omega
    have Kz : pairCount N k=0 := by dsimp [pairCount]; omega
    apply WP.block_nil
    refine ⟨?_, ?_, by rw [xmm], by rw [xmm], mem, keep.mono (by decide)⟩
    · rw [xmm, z0]
      simp only [inputLow, pairLow, Kz, total, Nat.mul_zero, odd, ↓reduceIte, Nat.add_zero]
      rfl
    · rw [xmm, z1]
      simp only [inputHigh, pairHigh, Kz, total, Nat.mul_zero, odd, ↓reduceIte, Nat.add_zero]
      rfl

end VG.Proof.Mont.X86.Square
