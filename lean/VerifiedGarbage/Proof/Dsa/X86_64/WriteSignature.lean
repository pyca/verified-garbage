module
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.Execution

import VerifiedGarbage.Proof.Dsa.X86_64.ReleaseBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # Release both signature scalars, or zero the complete output -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem writeSignature_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (.seq (SignVerify.writeScalar r false) (SignVerify.writeScalar s true)) s0 fun s2 =>
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep [.rax, .rsi, .rdx, .rcx, .r8] s0 s2 := by
  obtain ⟨hq1, hq32, _, _⟩ := L.widths
  have hn := h0.scratch.nowrap
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega
  have hout := h0.fields .out (by decide)
  have hql : word s0.mem L.base Field.qLen.offset = BitVec.ofNat 64 L.qLen := h0.length .q
  refine WP.seq (WP.mono (writeScalar_ok h0.scratch h0.parent.rdi (by decide) (by decide) hout hql hm false
    (by omega) (by omega) hr (fun i hi => hw i (by omega)) (fun i hi => hsep i (by omega)))
    fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at hb1 hf1
  have hmem1 (d i : Nat) (hd : d + i < usedBytes) :
      s1.mem (off L.base d + BitVec.ofNat 64 i) = s0.mem (off L.base d + BitVec.ofNat 64 i) :=
    hf1 _ (fun j hj => scr_ne_out hsep hd (by omega) j (by omega))
  have hword1 (f : Field) : word s1.mem L.base f.offset = word s0.mem L.base f.offset := by
    apply Mem.readW_congr
    intro i hi
    have hb := VG.Proof.Dsa.field_bounds f
    have hpu : pWorkspace ≤ usedBytes := by decide
    exact hmem1 _ _ (by omega)
  have hwr2 : ∀ i < L.qLen, InRegions s1.wr ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk1.2.2, Offset.add_add]
    exact hw _ (by omega)
  have hsep2 : ∀ i < L.qLen, usedBytes ≤ ofs L.base ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) := by
    intro i hi
    rw [Offset.add_add]
    exact hsep _ (by omega)
  refine WP.mono (writeScalar_ok (h0.scratch.congr hk1.2.2) ((hk1.gpr (by decide)).trans h0.parent.rdi)
    (by decide) (by decide) ((hword1 .out).trans hout) ((hword1 .qLen).trans hql) ((hword1 .mask).trans hm)
    true (by omega) (by omega) hs hwr2 hsep2) fun s2 ⟨hb2, hf2, hk2⟩ => ?_
  simp only [↓reduceIte] at hb2 hf2
  have hbr : ∀ i < L.qLen, s2.mem (L.fields .out + BitVec.ofNat 64 i) =
      if valid then s0.mem (off L.base r + BitVec.ofNat 64 i) else 0 := by
    intro i hi
    rw [hf2 _ ?_]
    · exact hb1 i hi
    · intro j hj
      rw [Offset.add_add]
      exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have hbs : ∀ i < L.qLen, s2.mem ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) =
      if valid then s0.mem (off L.base s + BitVec.ofNat 64 i) else 0 := by
    intro i hi
    rw [hb2 i hi, hmem1 s i (by omega)]
  refine ⟨?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [Nat.two_mul, bytesAt_split, bytesAt_masked hbr, bytesAt_masked hbs]
    cases valid <;> simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
  · intro x hx
    rw [hf2 x (fun j hj => by simpa only [Offset.add_add] using hx (L.qLen + j) (by omega))]
    exact hf1 x (fun j hj => hx j (by omega))

end VG.Proof.Dsa.X86_64
