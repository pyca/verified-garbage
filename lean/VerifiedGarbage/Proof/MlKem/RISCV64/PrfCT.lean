module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Prf
public import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT

import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Prf
meta import VerifiedGarbage.Proof.MlKem.RISCV64.HashCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.CallsCT
meta import VerifiedGarbage.Proof.MlKem.RISCV64.SampleCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelBlock
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on RISC-V: the `PRF`s in constant time

As on PPC64LE (`Proof/MlKem/PPC64LE/PrfCT.lean`): two runs of `prfLoop` with
the same `scratch` leak the same trace (`prfLoop_ct`), since every address is
`scratch` plus an offset that depends only on the counter `N`, and the calls
take the same pointers in both runs. What each run is at each point comes
from its correctness (`relct_wp`).
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem prf_hashOk {L : Lay} {s : State} (hc : Ctx L s) :
    HashOk L (fun _ => 0) [⟨.s11, oSigma, 33⟩] [⟨.s11, oPrf, 128⟩] s := by
  refine ⟨hc, fun p hp => ?_, fun p hp => ?_⟩ <;> rw [List.mem_singleton] at hp <;> subst hp
  · exact ⟨by decide, hc.s11, by decide, by decide, by decide, hc.sepAll0 (by decide) (by decide),
      mem_rd_wr hc.cw⟩
  · exact ⟨by decide, hc.s11, by decide, by decide, by decide, hc.sepAll0 (by decide) (by decide), hc.cw⟩

/-- A state `prfBody` runs from, as far as its timing is concerned. -/
abbrev PS (L : Lay) (N : Nat) (s : State) : Prop := Ctx L s ∧ s.gpr .s6 = BitVec.ofNat 64 N

theorem prfBody_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₁ N : Nat} (hN : N < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) :
    RelCT isa (fun a b => PS L N a ∧ PS L N b) (K.prfBody withNtt N₁) fun _ _ => True := by
  have k4 := hK.k4
  -- the counter
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (taint_block [.s11] (fun a b hab => hab.1.1.sp_eq hab.2.1) (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.s11, hab.2.1.s11]) (by taint_decide))
      fun a b hab => ⟨WP.mono (sb6_ok hab.1.1 (by omega) hab.1.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.1.1, by rw [k'.cs .s6 (by decide) (by decide), hab.1.2]⟩,
        WP.mono (sb6_ok hab.2.1 (by omega) hab.2.2) fun s' ⟨k', _⟩ =>
          ⟨k'.ctx (by decide) hab.2.1, by rw [k'.cs .s6 (by decide) (by decide), hab.2.2]⟩⟩) ?_
  -- `PRF`
  have hh : ∀ s, PS L N s → WP isa (hash 136 0x1f [⟨.s11, oSigma, 33⟩] [⟨.s11, oPrf, 128⟩]) s (PS L N) :=
    fun s h => WP.mono (hash_ok (idx := fun _ => 0) rate136 (by decide) h.1 (List.cons_ne_nil _ _)
      (prf_hashOk h.1).ins (prf_hashOk h.1).outs (List.pairwise_singleton _ _)) fun s' ⟨k', _⟩ =>
      ⟨h.1.kept k', by rw [k'.cs .s6 (by decide), h.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (hash_ct rate136 (by decide) (List.cons_ne_nil _ _) fun a b hab =>
      ⟨prf_hashOk hab.1.1, prf_hashOk hab.2.1, hab.1.1.sp_eq hab.2.1⟩) fun a b hab => ⟨hh a hab.1, hh b hab.2⟩) ?_
  -- `SamplePolyCBD₂`
  let F : State → Prop := fun s => PS L N s ∧ s.gpr .a0 = L.ptr 0 + BitVec.ofNat 64 oPrf ∧
    s.gpr .a1 = L.ptr 0 + BitVec.ofNat 64 (oPoly (K.k + N))
  have ha : ∀ s, PS L N s → WP isa (.block (.addi .a0 .s11 oPrf :: slotAt .a1 .s6 K.k)) s F :=
    fun s h => WP.mono (cbdArgs_ok hK (by omega) h.1.s11 h.2) fun s' ⟨o', g3, g4⟩ =>
      ⟨⟨h.1.only o', by rw [o'.cs .s6 (by decide), h.2]⟩, g3, g4⟩
  refine RelCT.seq (R := fun a b => F a ∧ F b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨ha a hab.1, ha b hab.2⟩) ?_
  have hcb : ∀ s, F s → WP isa callCbd2 s (PS L N) := fun s h =>
    cbd2L h.1.1.ok h.2.1 h.2.2 (h.1.1.sep00 (by offs) (by offs) (by offs)) (mem_rd_wr h.1.1.cw) h.1.1.cw
      (h.1.1.alP _) fun s' k' _ => ⟨h.1.1.kept k', by rw [k'.cs .s6 (by decide), h.1.2]⟩
  refine RelCT.seq (R := fun a b => PS L N a ∧ PS L N b)
    (relct_wp (RelCT.callT cbd2T (regs2 fun a b hab =>
      ⟨hab.1.1.1.sp_eq hab.2.1.1, by rw [hab.1.2.1, hab.2.2.1], by rw [hab.1.2.2, hab.2.2.2]⟩))
      fun a b hab => ⟨hcb a hab.1, hcb b hab.2⟩) ?_
  -- the NTT, and the counter
  cases withNtt
  · exact RelCT.seq (R := fun _ _ => True) (relct_noMem (by rfl)) (relct_noMem (by rfl))
  · refine RelCT.seq (R := fun _ _ => True) ?_ (relct_noMem (by rfl))
    let G : State → Prop := fun s => s.sp = s.sp ∧ s.gpr .a0 = L.ptr 0 + BitVec.ofNat 64 (oPoly (K.k + N)) ∧
      s.gpr .a1 = L.ptr 0 + BitVec.ofNat 64 K.oNtt
    have hn : ∀ s, PS L N s → WP isa (.block (slotAt .a0 .s6 K.k ++ polyAddr .a1 K.jNtt)) s
        fun s' => G s' ∧ Ctx L s' := fun s h =>
      WP.mono (nttArgs_ok hK (by omega) h.1.s11 h.2) fun s' ⟨o', g3, g4⟩ =>
        ⟨⟨rfl, g3, g4⟩, h.1.only o'⟩
    exact RelCT.seq (R := fun a b => (G a ∧ Ctx L a) ∧ (G b ∧ Ctx L b))
      (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨hn a hab.1, hn b hab.2⟩)
      (RelCT.callT nttT (regs2 fun a b hab =>
        ⟨hab.1.2.sp_eq hab.2.2, by rw [hab.1.1.2.1, hab.2.1.2.1], by rw [hab.1.1.2.2, hab.2.1.2.2]⟩))

theorem prfLoop_ct {K : KemLay} (hK : K.WF) {L : Lay} (withNtt : Bool) {N₀ N₁ : Nat} (h01 : N₀ < N₁)
    (hN₁ : N₁ ≤ 2 * K.k + 1) {s₀₁ s₀₂ : State} (hc₁ : Ctx L s₀₁) (hc₂ : Ctx L s₀₂) {σ₁ σ₂ : List Byte}
    (hσ₁ : bytesAt s₀₁.mem (L.A 0 oSigma) 32 = σ₁) (hσ₂ : bytesAt s₀₂.mem (L.A 0 oSigma) 32 = σ₂) :
    RelCT isa (fun a b => a = s₀₁ ∧ b = s₀₂) (K.prfLoop withNtt N₀ N₁) fun _ _ => True := by
  have k4 := hK.k4
  refine RelCT.seq (R := fun a b => PrfInv K L withNtt σ₁ N₀ N₁ s₀₁ 0 a ∧ PrfInv K L withNtt σ₂ N₀ N₁ s₀₂ 0 b)
    (relct_wp (relct_noMem (by rfl)) fun a b hab => ⟨?_, ?_⟩)
    (RelCT.mono (relct_loop_nz (I₁ := PrfInv K L withNtt σ₁ N₀ N₁ s₀₁)
      (I₂ := PrfInv K L withNtt σ₂ N₀ N₁ s₀₂) (N := N₁ - N₀) (by omega) fun t ht => ?_)
      (fun _ _ h => h) fun _ _ _ => trivial)
  · rw [hab.1]
    exact WP.mono (li6_ok (by omega)) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₁,
        fun N h1 h2 => absurd h2 (by omega)⟩
  · rw [hab.2]
    exact WP.mono (li6_ok (by omega)) fun s₁ ⟨k₁, g₁, m₁⟩ =>
      ⟨k₁.mono (fun _ h => absurd h List.not_mem_nil), by rw [g₁, Nat.add_zero], by rw [m₁]; exact hσ₂,
        fun N h1 h2 => absurd h2 (by omega)⟩
  -- one iteration: the body's timing from where it runs, and each run by correctness
  exact relct_wp (RelCT.mono (prfBody_ct hK (N := N₀ + t) withNtt (by omega) hN₁) (fun a b hab =>
      ⟨⟨hab.1.kx.ctx (by decide) hc₁, hab.1.s6⟩, ⟨hab.2.kx.ctx (by decide) hc₂, hab.2.s6⟩⟩) fun _ _ h => h)
    fun a b hab => ⟨prfStep_ok hK hc₁ withNtt hN₁ ht hab.1, prfStep_ok hK hc₂ withNtt hN₁ ht hab.2⟩

end VG.Proof.MlKem.RISCV64
