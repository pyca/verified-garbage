module

import VerifiedGarbage.Proof.Mont.X86.Compact.Length
import VerifiedGarbage.Proof.Mont.X86.Rt.Blocks
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Public row count in prepared Montgomery multiplication -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- `ebp` up a word, and ZF after the last row. -/
theorem rowEnd_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {S i N : Nat} (base : (A 0).toNat = W.toNat)
    (width : w32 s.mem W 48 * 8 = 4 * N) (headerFit : 52 ≤ L) (hN32 : 4 * N < 2 ^ 32)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp (S + Compact.accOff + 4 * i)) (hi : i < N)
    (hL : S + Compact.accOff + 4 * N ≤ L) :
    WP isa (.block Compact.rowEnd) s fun u =>
      PtrAt u W .ebp (S + Compact.accOff + 4 * (i + 1)) ∧ u.zf = some (decide (i + 1 = N)) ∧
      u.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s u := by
  have hn' := hw.nowrap
  have acc : Compact.accOff = 24 := rfl
  simp only [Compact.rowEnd, List.cons_append, List.append_assoc]
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  rw [List.nil_append]
  refine WP.block_append (WP.mono (lenTimes_ok (hw.of_keeps u₁.keeps) (ha.of_upd u₁ (by decide)) base headerFit 0)
    fun s₂ ⟨l₂, m₂, K₂⟩ => ?_)
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_cmpS rfl fun s₅ f₅ z₅ => WP.block_nil ?_
  have ebp₄ : (s₄.gpr .ebp).toNat = (W.toNat + (S + Compact.accOff + 4 * (i + 1))) % 2 ^ 32 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide), u₁.gpr, ptr_add hebp]
    congr 1
  have eax₄ : (s₄.gpr .eax).toNat = (W.toNat + (S + Compact.accOff + 4 * N)) % 2 ^ 32 := by
    rw [u₄.gpr, u₃.gpr, K₂.1 .edi (by decide), u₁.other _ (by decide),
      BitVec.toNat_add, BitVec.toNat_add, l₂, show w32 s₁.mem W 48 * 2 ^ (3 + 0) % 2 ^ 32 = 4 * N from by
        rw [u₁.mem, show 2 ^ (3 + 0) = 8 from rfl, width, Nat.mod_eq_of_lt hN32], hedi]
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [PtrAt, f₅.gpr]; exact ebp₄, ?_, by rw [f₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem], ?_⟩
  · rw [z₅]
    congr 1
    by_cases h : i + 1 = N
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, ebp₄, eax₄, h]
      simp
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro hz
      have := congrArg BitVec.toNat hz
      rw [BitVec.toNat_sub, ebp₄, eax₄] at this
      simp at this
      have := hL
      omega
  · exact ((((u₁.keeps.mono (rs' := [.eax, .edx, .ebp]) (by decide)).widen K₂).widen u₃.keeps).widen u₄.keeps).widen (f₅.keeps [])

end VG.Proof.Mont.X86.Compact
