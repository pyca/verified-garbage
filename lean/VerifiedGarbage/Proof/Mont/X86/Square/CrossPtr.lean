module

public import VerifiedGarbage.Proof.Mont.X86.Square.Lower

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def crossPtr : List Instr :=
  ptr .ecx argA .eax ++ [.mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .ecx (.reg .ebp)]

theorem crossPtr_ok {s : State} {W : Addr} {L a N k l : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (al : a+4*N ≤ L)
    (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (ll : l < N) (kl : k-l < N) (lk : l ≤ k)
    (cx : s.gpr .edx = BitVec.ofNat 32 (4*l)) (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block crossPtr) s fun t =>
      PtrAt t W .ecx (a+4*l) ∧ PtrAt t W .ebp (a+4*(k-l)) ∧
      t.cf = some (decide (2*l<k)) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx, .ebp] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block crossPtr) s fun t =>
      PtrAt t W .ecx (a+4*l) ∧ PtrAt t W .ebp (a+4*(k-l)) ∧
      t.cf = some (decide (2*l<k)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .ebp] s t := by
    unfold crossPtr
    apply WP.block_append
    refine WP.mono (ptr_ok ha (r := .ecx) (t := .eax) (i := 7) (by decide) (by decide) (by decide))
      fun t1 ⟨c1, _, m1, K1⟩ => ?_
    have c1' : t1.gpr .ecx = BitVec.ofNat 32 (W.toNat+a) := by
      rw [c1, base, argAeq, ← BitVec.ofNat_add]
    have dx1 : t1.gpr .edx = BitVec.ofNat 32 (4*l) := (K1.1 _ (by decide)).trans cx
    have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
    refine wp_movS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ =>
      wp_addS rfl fun t4 u4 _ => wp_subS rfl fun t5 u5 _ => wp_cmpCF rfl fun t6 f6 cf => WP.block_nil ?_
    have c3 : t3.gpr .ecx = BitVec.ofNat 32 (W.toNat+a+4*l) := by
      rw [u3.gpr, u2.other _ (by decide), c1', u2.other _ (by decide), dx1, ← BitVec.ofNat_add]
    have p4 : t4.gpr .ebp = BitVec.ofNat 32 (W.toNat+a+4*k) := by
      rw [u4.gpr, u3.other _ (by decide), u2.gpr, c1', u3.other _ (by decide),
        u2.other _ (by decide), si1, ← BitVec.ofNat_add]
    have p5 : t5.gpr .ebp = BitVec.ofNat 32 (W.toNat+a+4*(k-l)) := by
      rw [u5.gpr, p4, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), dx1,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by have := hw.nowrap; omega) (by omega)]
      congr 1
      omega
    have c5 : t5.gpr .ecx = BitVec.ofNat 32 (W.toNat+a+4*l) := by
      rw [u5.other _ (by decide), u4.other _ (by decide), c3]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [PtrAt, f6.gpr, c5, BitVec.toNat_ofNat]
      congr 1
      omega
    · rw [PtrAt, f6.gpr, p5, BitVec.toNat_ofNat]
      congr 1
      omega
    · rw [cf, c5, p5, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := hw.nowrap; omega), Nat.mod_eq_of_lt (by have := hw.nowrap; omega)]
      have e : W.toNat+a+4*l < W.toNat+a+4*(k-l) ↔ 2*l<k := by omega
      simp only [e]
    · rw [f6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
    · exact (K1.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans
        ((u3.keeps.mono (by decide)).trans ((u4.keeps.mono (by decide)).trans
          ((u5.keeps.mono (by decide)).trans (f6.keeps [.eax, .ecx, .ebp])))))
  exact WP.mono (scalar_frame (by simp [crossPtr, ptr, scalar]) body)
    fun t ⟨⟨c, p, flag, mem, keep⟩, xmm⟩ => ⟨c, p, flag, mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square
