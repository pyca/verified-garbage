module

import VerifiedGarbage.Proof.Mont.X86.Compact.Length
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Rt.Zero
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Zeroing the compact product without touching prepared operands -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The accumulator, `2 N + 1` words at `S + Compact.accOff`, zeroed. -/
theorem zero_ok {t : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws t W L) (ha : Args t W L A)
    (base : (A 0).toNat = W.toNat) {N S : Nat}
    (width : w32 t.mem W 48 * 8 = 4 * N) (headerFit : 52 ≤ L)
    (scratchFit : S + Compact.accOff + 4 * (2 * N + 1) ≤ L)
    (hedi : PtrAt t W .edi S) :
    WP isa Compact.zeroAcc t fun u =>
      val32 u.mem W (S + Compact.accOff) (2 * N + 1) = 0 ∧
      Outside W (S + Compact.accOff) (4 * (2 * N + 1)) t.mem u.mem ∧ Keeps [.eax, .ebp, .esi] t u := by
  have hn := hw.nowrap
  have eacc : Compact.accOff = 24 := rfl
  unfold Compact.zeroAcc
  simp only [Compact.accPtr, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => ?_)
  have ha₂ : Args s₂ W L A := (ha.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  rw [List.nil_append]
  refine WP.block_append (WP.mono (lenTimes_ok ((hw.of_keeps u₁.keeps).of_keeps u₂.keeps) ha₂ base headerFit 1) fun s₃ ⟨l₃, m₃, K₃⟩ => ?_)
  refine wp_addS rfl fun s₄ u₄ _ => wp_movS rfl fun s₅ u₅ _ => WP.block_nil ?_
  have K₅ : Keeps [.eax, .ebp, .esi] t s₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen K₃).widen u₄.keeps).widen u₅.keeps
  have ebp₅ : PtrAt s₅ W .ebp (S + Compact.accOff) := by
    rw [PtrAt, u₅.other _ (by decide), u₄.other _ (by decide), K₃.1 _ (by decide), u₂.gpr, u₁.gpr,
      ptr_add hedi]
    simp only [BitVec.toNat_ofNat]; omega_using [eacc]
  have esi₅ : (s₅.gpr .esi).toNat = 4 * (2 * N + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, BitVec.toNat_add, l₃]
    have count : w32 s₂.mem W 48 * 2 ^ (3 + 1) = 8 * N := by
      rw [u₂.mem, u₁.mem]
      have : 2 ^ (3 + 1) = 16 := rfl
      rw [this]
      omega
    rw [count, show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  refine WP.mono (Rt.zeroLoop_ok (hw.of_keeps K₅) (by omega_using []) (by omega_using [scratchFit, eacc]) ebp₅ esi₅ u₅.gpr)
    fun u ⟨O, Z, K⟩ => ⟨Z, ?_, K₅.trans (K.mono (by decide))⟩
  rwa [u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem] at O

end VG.Proof.Mont.X86.Compact
