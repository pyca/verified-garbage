module

public import VerifiedGarbage.Proof.MlKem.AArch64.DotW.Loop
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Result
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# ML-KEM's fused dot product of polynomials stored with 16 bits, on AArch64

`Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms` writes `Σ F ∘ G`
(`polySum`) with 16-bit coefficients to `bo + out` (`dotW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.DotW

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Dot

def setupW (bo : Reg) (out : Nat) : List Instr := ptrTo .x0 bo out ++ vconsts ++
  [.adrSym .x3 "VG_MLKEM_GAMMA", .movz .x .x11 16 0, .movz .x .x12 0 0]

theorem setupW_ok {s : State} {bo : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (O : Nat → BitVec 16) :
    WP isa (.block (setupW bo out)) s
      (LoopInvW s (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") O 0) := by
  unfold setupW
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (wp_ptrTo' (d := .x0) (b := bo) (s := s)
    (Q := fun s' => Only [.x0] s s' ∧ s'.gpr .x0 = s.gpr bo + BitVec.ofNat 64 out)
    hbo.symm ho (fun _ hk hx => ⟨hk, hx⟩)) ?_
  intro s₁ h₁ sy₁
  rw [WP.block_append_iff]
  refine WP.mono_syms (Ntt.vconsts_ok s₁) ?_
  intro s₂ ⟨k₂, m₂, c₂, _⟩ sy₂
  refine WP.mono (WP.keepV (Q := fun s₃ => Only [.x3, .x11, .x12] s₂ s₃ ∧
    s₃.gpr .x3 = s₂.syms "VG_MLKEM_GAMMA" ∧ s₃.gpr .x11 = BitVec.ofNat 64 16 ∧ s₃.gpr .x12 = 0)
    (by rfl) (wp_x (by rfl) fun s₃ k₃ e₃ => wp_movz fun s₄ k₄ e₄ =>
      wp_movz fun s₅ k₅ e₅ => wp_nil ⟨((k₃.trans k₄).trans k₅).mono,
        by rw [k₅.get .x3, k₄.get .x3, e₃], by rw [k₅.get .x11, e₄]; rfl, by rw [e₅]; rfl⟩))
    fun s₃ ⟨⟨k₃, e₃, e11, e12⟩, v₃⟩ => ?_
  have hm : s₃.mem = s.mem := k₃.mem.trans (m₂.trans h₁.1.mem)
  refine ⟨((h₁.1.keep.trans k₂).trans k₃.keep).mono,
    by rw [hm]; exact Frame.refl _ _, ⟨by rw [v₃]; exact c₂.q, by rw [v₃]; exact c₂.m⟩,
    ?_, ?_, e12, ?_, ?_⟩
  · rw [k₃.get .x0, k₂.get .x0, h₁.2]; exact (BitVec.add_zero _).symm
  · rw [e₃, sy₂, sy₁]; exact (BitVec.add_zero _).symm
  · rw [e11]; rfl
  · rw [hm]; intro i _; rw [ite_eq_right (by omega)]

theorem dotW_partition (bo bf bg : Reg) (out : Nat) (terms : List (Nat × Nat)) :
    Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms =
      .seq (.block (setupW bo out))
        (.loop (.block (Impl.MlKem.AArch64.DotW.bodyW bf bg terms)) (.nonzero .x .x11)) := by
  simp only [Impl.MlKem.AArch64.DotW.dotW, setupW, List.append_assoc]

theorem dotW_ok {s : State} {bo bf bg : Reg} (hbo : bo ≠ .x0) {out : Nat} (ho : out < 65536)
    (terms : List (Nat × Nat)) {F G : (Nat × Nat) → Poly}
    (hd : LoopDataW s bf bg (s.gpr bo + BitVec.ofNat 64 out) (s.syms "VG_MLKEM_GAMMA") terms
      (polyValues F) (polyValues G) gammaValues) :
    WP isa (Impl.MlKem.AArch64.DotW.dotW bo bf bg out terms) s fun s' =>
      Keep clob s s' ∧ Frame [⟨s.gpr bo + BitVec.ofNat 64 out, 512⟩] s.mem s'.mem ∧
      PolyIsW 16 s'.mem (s.gpr bo + BitVec.ofNat 64 out) (polySum terms F G) := by
  rw [dotW_partition]
  refine WP.seq (WP.mono (setupW_ok hbo ho (resultW terms (polyValues F) (polyValues G) gammaValues))
    fun s₁ h₁ => ?_)
  refine WP.mono (loopW_ok hd h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.keep, h₂.frame, h₂.out.polyIs (fun i hi => by omega) fun i hi => ?_⟩
  rw [resultW, result_field terms F G hi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : ((polySum terms F G)[i]!).val < 3329 := Fin.isLt _
  change _ % 2 ^ 32 % 2 ^ 16 = _
  omega

end VG.Proof.MlKem.AArch64.DotW
