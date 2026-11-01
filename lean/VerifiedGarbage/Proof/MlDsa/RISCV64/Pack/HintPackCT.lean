module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintPack
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Pack.HintCT
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.MlDsa.Pack.Coeffs
meta import VerifiedGarbage.Proof.MlDsa.Pack.HintMem
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RelCT

/-!
# ML-DSA on RISC-V: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Constant time but for the hint, as on AArch64: zeroing `y` leaks only the
pointers and `len` (the taint analysis), and leaves states that agree on
`k`, `ω` and the pointers, and on all the memory the loops may access (the
hint, which the contract lets them leak, and `y`, zeroed); `memTaint`
proves the rest. `omega` is a `u32`, whose register's upper bits the two
runs need not agree on: the code zero-extends it before using it.
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Pack.Hint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem pre_of {s : State} (h : (hintBitPackContract RISCV64.abi).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The public registers of the loops: the pointers, `k`, `ω`. -/
abbrev hbpTaint : VG.RISCV64.Taint.T := VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]

theorem ct : ConstantTime isa (hintBitPackContract RISCV64.abi).pre (hintBitPackContract RISCV64.abi).pub
    Impl.MlDsa.RISCV64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.RISCV64.Pack.hintBitPack
  refine RelCT.seq (R := MAgree hbpTaint) ?_
    (RelCT.taint (A := memTaint) hbpTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := fun (s₀ s : State) => ZPost s₀ s ∧ s.sp = s₀.sp)
    (RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs [.a3, .a4]) ?_ (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨wp_sp (zero_ok (pre_of hx)), wp_sp (zero_ok (pre_of hy))⟩)) (fun _ _ h => h) ?_
  · rintro a b ⟨_, _, hab⟩
    sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hab
    obtain ⟨hsp, -, -, -, -, h6, h7⟩ := hab
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h6
    · exact h7
  rintro x' y' ⟨_, x, y, ⟨hx, hy, hpb⟩, ⟨fx, spx⟩, ⟨fy, spy⟩⟩
  have px := pre_of hx
  have py := pre_of hy
  sig_pub [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs] at hpb
  obtain ⟨hsp, hleak, p3, p4, p5, p6, p7⟩ := hpb
  have hω : pω x = pω y := by simp only [pω, w32, p5]
  have hrd : x'.rd = y'.rd := by rw [fx.rd, fy.rd, px.rd, py.rd]; simp only [hR, pH, p3, p4]
  have hwr : x'.wr = y'.wr := by rw [fx.wr, fy.wr, px.wr, py.wr]; simp only [yR, pY, pLen, p6, p7]
  refine ⟨⟨by rw [spx, spy, hsp], fun r hr => ?_⟩, hrd, hwr, fun a ha => ?_⟩
  · simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [fx.a0, fy.a0]; simp only [pH, p3]
    · rw [fx.a1, fy.a1]; simp only [pk, pLen, p7, hω]
    · rw [fx.a2, fy.a2, hω]
    · rw [fx.a3, fy.a3]; simp only [pY, p6]
  · rw [fx.rd, fx.wr, px.rd, px.wr] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      have hxy : ¬ (yR x).Contains a 1 := fun hc' => px.d_hy a hc hc'
      rw [fx.frame a (fun r hr hc' => by simp only [List.mem_singleton] at hr; subst hr; exact hxy hc'),
        fy.frame a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [yR, pY, pLen, ← p6, ← p7] at hc'
          exact hxy hc')]
      exact bytes_of_words (by simpa only [p3, p4] using hleak) (by simpa only [hR, pH, p3, p4] using hc)
    · -- `y`: zeros.
      have hlt : (a - pY x).toNat < pLen x := by simp only [Region.Contains] at hc; omega
      have ea : a = pY x + BitVec.ofNat 64 (a - pY x).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := fx.zero _ hlt
      have h₂ := fy.zero _ (show _ < pLen y by simpa only [pLen, ← p7] using hlt)
      rw [← ea] at h₁
      rw [show pY y = pY x by simp only [pY, p6], ← ea] at h₂
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1024 | .a2 => 80 | .a3 => 0x3000 | .a4 => 84 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

end VG.Proof.MlDsa.RISCV64.Pack.Hint

namespace VG.Proof.MlDsa.RISCV64.Pack

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Pack
open VG.Proof.MlDsa.RISCV64.Pack.Hint

theorem hintBitPack_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Pack.hintBitPack (hintBitPackContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, ct, ⟨satState, ?_⟩⟩
  · obtain ⟨t, s', he, hy, hk⟩ := correct (pre_of hs)
    refine ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel), ?_⟩
    sig_post [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
    exact hy
  · sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | (rw [hintOnes_zero]; exact Nat.zero_le _)
        | trivial
        | exact Region.disjoint_of_sep (by decide)
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Pack
