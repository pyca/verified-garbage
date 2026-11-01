module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Loop
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Loop
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.Stream
public import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Impl.Sha3.RISCV64.Stream

/-!
# ML-DSA on RISC-V: `vg_mldsa_simple_bit_pack`

The loop is proven once for every width (`packLoop_ok`), and the function by
its three cases. Constant time: the branch on the width by `sel_ct`, and each
loop by the taint analysis.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.RISCV64 (toNat_setWidth64)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat fun _ => True := fun j s _ hj hin hal => by
  refine WP.keep _ ?_ rfl rfl
  unfold sbpLd
  exact Steps.wp_lwu hj rfl hal hin fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, toNat_setWidth64], u₁.mem⟩

theorem true_stable : Stable fun _ => True := fun _ _ _ _ => trivial

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem sbp_wp {s₀ : State} (hp : SbpPre s₀) :
    WP isa Impl.MlDsa.RISCV64.Pack.simpleBitPack s₀ fun s' =>
      bytesAt s'.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat =
        simpleBitPack (natPolyAt s₀.mem (s₀.gpr .a0)) (lo s₀ .a1) := by
  unfold Impl.MlDsa.RISCV64.Pack.simpleBitPack
  refine WP.seq (WP.mono (mov2_ok (a := .a0) (b := .a2) (by decide) s₀)
    fun s₁ ⟨⟨g10, g11, m₁⟩, k₁⟩ => ?_)
  have e4 : lo s₁ .a1 = lo s₀ .a1 := by simp only [lo]; rw [k₁.gpr (by decide)]
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (lo s₀ .a1) = d → ∀ s : State, Same s₁ s →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        bytesAt s'.mem (s₀.gpr .a2) (s₀.gpr .a3).toNat =
          simpleBitPack (natPolyAt s₀.mem (s₀.gpr .a0)) (lo s₀ .a1) := by
    intro d c nb hs hd s hS
    have hlen := hp.len
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok true_stable hs (pf := s₀.gpr .a0) (po := s₀.gpr .a2) (m₀ := s₀.mem)
      (rd := s₀.rd) (wr := s₀.wr) (sE := s) trivial
      (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hp.disj)
      (fun i hi => by rw [← hd]; exact lt_bitlen (hp.le i hi)) hp.al
      (by rw [hS.1.gpr (by decide), g10]) (by rw [hS.1.gpr (by decide), g11])
      (by rw [hS.1.2.1, k₁.2.1]) (by rw [hS.1.2.2, k₁.2.2]) (by rw [hS.2, m₁]) (Keep.refl _ _))
      fun s' ⟨hB, _, _⟩ => ?_
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  refine sel_ok .a1 (by decide) 15 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n15 => ?_)
  · rw [e4] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) (by rw [e]; decide) s₂ h₂
  rw [e4] at n15
  refine sel_ok .a1 (by decide) 43 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n43 => ?_)
  · rw [show lo s₂ .a1 = lo s₀ .a1 by simp only [lo]; rw [h₂.1.gpr (by decide)]; exact e4] at e
    exact go (d := 6) (c := 4) (nb := 3) (by constructor <;> decide) (by rw [e]; decide) s₃ (h₂.trans h₃)
  · rw [show lo s₂ .a1 = lo s₀ .a1 by simp only [lo]; rw [h₂.1.gpr (by decide)]; exact e4] at n43
    have e : lo s₀ .a1 = 1023 := by
      have hb := hp.b
      simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    exact go (d := 10) (c := 4) (nb := 5) (by constructor <;> decide) (by rw [e]; decide) s₃ (h₂.trans h₃)

theorem simpleBitPack_ct :
    ConstantTime isa (simpleBitPackContract RISCV64.abi).pre (simpleBitPackContract RISCV64.abi).pub
      Impl.MlDsa.RISCV64.Pack.simpleBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.simpleBitPack
  refine RelCT.seq (R := Agr .a1) (((relct_noMem (by rfl)).wpDep
    (F := fun (σ s' : State) => ((s'.gpr .a7 = σ.gpr .a0 ∧ s'.gpr .t1 = σ.gpr .a2 ∧ s'.mem = σ.mem) ∧
      Keep [.a7, .t1] σ s') ∧ s'.sp = σ.sp)
    fun a b _ => ⟨WP.withSp (mov2_ok (by decide) a),
      WP.withSp (mov2_ok (by decide) b)⟩).mono (fun _ _ h => h)
    fun a' b' ⟨_, σ₁, σ₂, ⟨_, _, hpub⟩, ⟨⟨⟨g₁, h₁, _⟩, k₁⟩, p₁⟩, ⟨⟨⟨g₂, h₂, _⟩, k₂⟩, p₂⟩⟩ => by
      sig_pub [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs] at hpub
      obtain ⟨hsp, e3, e4, e5, -⟩ := hpub
      refine ⟨by rw [p₁, p₂, hsp], by rw [g₁, g₂, e3], by rw [h₁, h₂, e5], ?_⟩
      simp only [lo]; rw [k₁.gpr (by decide), k₂.gpr (by decide), e4]) ?_
  exact sel_ct (by decide) (by decide) (leaf_ct (by taint_decide))
    (sel_ct (by decide) (by decide) (leaf_ct (by taint_decide)) (leaf_ct (by taint_decide)))

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp [coeffAt, Mem.readW, Mem.read]

/-- A state satisfying the precondition. -/
def sbpSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 15 | .a2 => 0x2000 | .a3 => 128 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

example : ∃ pre post leak, simpleBitPackContract RISCV64.abi =
    simpleBitPackApi.sig.contract RISCV64.target.abi pre post simpleBitPackApi.writeArgs 0 leak := ⟨_, _, _, rfl⟩

theorem simpleBitPack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.simpleBitPack (simpleBitPackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, simpleBitPack_ct, ?_⟩
  · obtain ⟨t, s', he, hpost⟩ := sbp_wp (SbpPre.of hs)
    refine ⟨t, s', he, abi_of (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel) he, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs]
    exact hpost
  · refine ⟨sbpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [simpleBitPackContract, simpleBitPackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
        | (simp only [simpleBitPackBounds, t1Max_eq]; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack
