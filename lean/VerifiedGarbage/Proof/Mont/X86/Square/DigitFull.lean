module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.DigitStore
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Square.Step
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Square/ProdByB.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem mul_by_b_eq (s : State) (a : BitVec 32) :
    execMul .ebx (s.setReg .eax a) = execMul .edx ((s.setReg .eax a).setReg .edx (s.gpr .ebx)) := by
  cases s
  simp only [execMul, State.setReg, State.setFlags, show Reg.eax ≠ Reg.edx by decide,
    show Reg.ebx ≠ Reg.eax by decide, ↓reduceIte]
  congr 1
  funext r
  by_cases h₁ : r = Reg.eax <;> by_cases h₂ : r = Reg.edx <;> simp_all

def prodByB : List Instr := [.mov .eax (.mem (at_ .ebp 0)), .mul .ebx] ++ VG.Impl.Mont.X86.Rt.Square.accum

theorem prodByB_ok {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L)
    (hx : PtrAt s W .ebp x) (xl : x+4≤L) :
    WP isa (.block prodByB) s fun t => t = prodState s (s.mem.readW (off W x) 32) (s.gpr .ebx) := by
  apply WP.of_runBlock
  refine ⟨_, ?_, rfl⟩
  have read := readSrc_ptr hw hx (d := 0) (by omega)
  simp only [Nat.add_zero] at read
  simp only [prodByB, List.cons_append, List.nil_append, runBlock_cons, exec, read,
    Option.map_some, runStep_some, run_accum, mul_by_b_eq, prodState]

end VG.Proof.Mont.X86.Square
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def digitFull : List Instr := digitStore ++ ptr .ebp argM .edx ++ prodByB

theorem digitFull_ok {s : State} {W : Addr} {L S inv m k l h : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (base : A 0 = BitVec.ofNat 32 W.toNat)
    (iv : A 4 = BitVec.ofNat 32 inv) (mv : A 3 = BitVec.ofNat 32 m)
    (il : inv+4≤L) (ml : m+4≤L) (tl : S+20+4≤L) (ql : S+52+4*k+4≤L)
    (sep : m+4≤S+52+4*k ∨ S+52+4*k+4≤m)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (low : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (high : s.xmm .xmm1 = packed (BitVec.ofNat 64 h)) :
    WP isa (.block digitFull) s fun t =>
      t.xmm .xmm0 = packed (BitVec.ofNat 64 (l+(digit s W S inv*w32 s.mem W m)%2^32)) ∧
      t.xmm .xmm1 = packed (BitVec.ofNat 64 (h+(digit s W S inv*w32 s.mem W m)/2^32)) ∧
      t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
      t.mem = s.mem.writeW (off W (S+52+4*k)) (BitVec.ofNat 32 (digit s W S inv)) ∧
      Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t := by
  unfold digitFull
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (digitStore_ok ha hw base iv il tl ql edi si) fun t1 ⟨mem1, ebx1, K1, x1⟩ => ?_
  have O : Outside W (S+52+4*k) 4 s.mem t1.mem := by
    rw [mem1]
    exact writeW32_outside _ _ _ (by have := hw.nowrap; omega)
  have ha1 := ha.of_keeps K1 (by decide) (Outs.of_outside (O.mono (Nat.zero_le _) (by omega)) (List.mem_singleton_self _))
  have hw1 := hw.of_keeps K1
  apply WP.block_append
  refine WP.mono (scalar_frame (by simp [ptr, scalar])
    (ptr_ok ha1 (r := .ebp) (t := .edx) (i := 3) (by decide) (by decide) (by decide)))
      fun t2 ⟨⟨bp2, _, mem2, K2⟩, x2⟩ => ?_
  have p2 : PtrAt t2 W .ebp m := by
    rw [PtrAt, bp2, base, mv, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
  have hw2 := hw1.of_keeps K2
  refine WP.mono (prodByB_ok hw2 p2 ml) fun t eq => ?_
  subst t
  have low2 : t2.xmm .xmm0 = packed (BitVec.ofNat 64 l) := by rw [x2, x1]; exact low
  have high2 : t2.xmm .xmm1 = packed (BitVec.ofNat 64 h) := by rw [x2, x1]; exact high
  have values := prod_values (t2.mem.readW (off W m) 32) (t2.gpr .ebx) low2 high2
  have frame := prod_frame t2 (t2.mem.readW (off W m) 32) (t2.gpr .ebx)
  have mem : t2.mem = t1.mem := mem2
  have b2 : t2.gpr .ebx = BitVec.ofNat 32 (digit s W S inv) := by rw [K2.1 _ (by decide), ebx1]
  have db : digit s W S inv < 2^32 := Nat.mod_lt _ (by decide)
  have product : (t2.mem.readW (off W m) 32).toNat*(t2.gpr .ebx).toNat = digit s W S inv*w32 s.mem W m := by
    rw [b2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt db]
    change w32 t2.mem W m*digit s W S inv = _
    rw [mem, O.w32 sep (by have := hw.nowrap; omega), Nat.mul_comm]
  refine ⟨?_, ?_, ?_, ?_, frame.2.trans (mem2.trans mem1), ?_⟩
  · rw [values.1, product]
    simp only [BitVec.ofNat_add]
  · rw [values.2.1, product]
    simp only [BitVec.ofNat_add]
  · rw [values.2.2.1, x2, x1]
  · rw [values.2.2.2, x2, x1]
  · exact (K1.mono (by decide)).trans ((K2.mono (by decide)).trans (frame.1.mono (by decide)))

end VG.Proof.Mont.X86.Square
