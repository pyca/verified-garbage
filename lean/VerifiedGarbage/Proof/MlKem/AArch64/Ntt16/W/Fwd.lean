module
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Pass1
public import VerifiedGarbage.Proof.Framework.Covers

import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdW

/-!
# ML-KEM's 16-bit NTT on AArch64, of a polynomial stored with 16 bits

`Impl.MlKem.AArch64.Ntt16.Readonly.fwdW` transforms the polynomial at `x0`,
stored with 16-bit coefficients, in place, with 512 bytes of working space
at `x1` and the table `VG_MLKEM_NTT16_ZETAS` (`fwdW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16
open VG.Impl.MlKem.AArch64.Ntt16

/-- What the transform needs: its precondition, and the table at `symbol`, readable and apart
from the polynomial and the working space. -/
structure Input (s : State) (symbol : String) (H : List Nat) : Prop extends W.Pre s where
  table : ∀ j < 64, s.mem.readW (s.syms symbol + BitVec.ofNat 64 (8 * j)) 64 = hw4 H j
  readable : Covers [⟨s.syms symbol, 512⟩] (s.rd ++ s.wr)
  apartOutput : (fR s).Disjoint ⟨s.syms symbol, 512⟩
  apartScratch : (sR s).Disjoint ⟨s.syms symbol, 512⟩

theorem Input.read {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {o : Nat} (ho : o + 16 ≤ 512) : InRegions (s.rd ++ s.wr) (s.syms symbol + BitVec.ofNat 64 o) 16 :=
  h.readable _ _ (in_regions (List.mem_singleton_self _) (contains_off ho (by decide)))

theorem Input.table_frame {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {m : Mem} (hf : Frame [sR s] s.mem m) :
    ∀ j < 64, m.readW (s.syms symbol + BitVec.ofNat 64 (8 * j)) 64 = hw4 H j := by
  intro j hj
  rw [hf.readW (r := ⟨s.syms symbol, 512⟩) (contains_off (by omega) (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.apartScratch.symm) (by decide)]
  exact h.table j hj

theorem fwdW_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_NTT16_ZETAS" tableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwdW s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (fP s₀) (Spec.MlKem.ntt (P₀ s₀)) := by
  exact NttR.fwdW_run s₀ ⟨hi.wr, hi.disj, hi.red, hi.table, hi.readable, hi.apartOutput, hi.apartScratch⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
