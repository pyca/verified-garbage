module
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.AArch64.WriteSignature`, which only this module used -/

section

/-! ### `Dsa.AArch64.ReleaseBytes`, which only this module used -/

section

/-! # Byte-string postconditions for masked DSA signature release -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64

theorem bytesAt_split (mem : Mem) (ptr : Addr) (n k : Nat) :
    Spec.Rsa.bytesAt mem ptr (n + k) = Spec.Rsa.bytesAt mem ptr n ++
      Spec.Rsa.bytesAt mem (ptr + BitVec.ofNat 64 n) k := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def,
    BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_masked {mem mem' : Mem} {src dst : Addr} {n : Nat} {valid : Bool}
    (h : ∀ i < n, mem' (dst + BitVec.ofNat 64 i) = if valid then mem (src + BitVec.ofNat 64 i) else 0) :
    Spec.Rsa.bytesAt mem' dst n = if valid then Spec.Rsa.bytesAt mem src n else List.replicate n 0 := by
  cases valid
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (List.mem_range.mp hi)
  · simp only [↓reduceIte] at h ⊢
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

end VG.Proof.Dsa.AArch64

end

end

/-! # Release both signature scalars, or zero the complete output -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem writeSignature_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (.seq (SignVerify.writeScalar r false) (SignVerify.writeScalar s true)) s0 fun s2 =>
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep [.x3, .x1, .x2, .x9, .x8] s0 s2 := by
  obtain ⟨hq1, hq32, _, _⟩ := L.widths
  have hn := h0.scratch.nowrap
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega_using [hq32]
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega_using [hq32]
  have hout := h0.fields .out (by decide)
  have hql : word s0.mem L.base Field.qLen.offset = BitVec.ofNat 64 L.qLen := h0.length .q
  refine WP.seq (WP.mono (writeScalar_ok h0.scratch h0.parent.x0 (by decide) (by decide) hout hql hm false
    (by omega_using [hq1]) (by omega_using [hq32]) hr (fun i hi => hw i (by omega_using [hi])) (fun i hi => hsep i (by omega_using [hi])))
    fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte] at hb1 hf1
  have hmem1 (d i : Nat) (hd : d + i < usedBytes) :
      s1.mem (off L.base d + BitVec.ofNat 64 i) = s0.mem (off L.base d + BitVec.ofNat 64 i) :=
    hf1 _ (fun j hj => scr_ne_out hsep hd (by omega_using [hn]) j (by omega_using [hj]))
  have hword1 (f : Field) : word s1.mem L.base f.offset = word s0.mem L.base f.offset := by
    apply Mem.readW_congr
    intro i hi
    have hb := VG.Proof.Dsa.field_bounds f
    have hpu : pWorkspace ≤ usedBytes := by decide
    exact hmem1 _ _ (by omega_using [hi, hb, hpu])
  have hwr2 : ∀ i < L.qLen, InRegions s1.wr ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk1.wr, Offset.add_add]
    exact hw _ (by omega_using [hi])
  have hsep2 : ∀ i < L.qLen, usedBytes ≤ ofs L.base ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) := by
    intro i hi
    rw [Offset.add_add]
    exact hsep _ (by omega_using [hi])
  refine WP.mono (writeScalar_ok (h0.scratch.congr hk1.wr) ((hk1.gpr .x0 (by decide)).trans h0.parent.x0)
    (by decide) (by decide) ((hword1 .out).trans hout) ((hword1 .qLen).trans hql) ((hword1 .mask).trans hm)
    true (by omega_using [hq1]) (by omega_using [hq32]) hs hwr2 hsep2) fun s2 ⟨hb2, hf2, hk2⟩ => ?_
  simp only [↓reduceIte] at hb2 hf2
  have hbr : ∀ i < L.qLen, s2.mem (L.fields .out + BitVec.ofNat 64 i) =
      if valid then s0.mem (off L.base r + BitVec.ofNat 64 i) else 0 := by
    intro i hi
    rw [hf2 _ ?_]
    · exact hb1 i hi
    · intro j hj
      rw [Offset.add_add]
      exact Offset.add_ofNat_ne _ (by omega_using [hq32, hi]) (by omega_using [hq32, hj]) (by omega_using [hi])
  have hbs : ∀ i < L.qLen, s2.mem ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) =
      if valid then s0.mem (off L.base s + BitVec.ofNat 64 i) else 0 := by
    intro i hi
    rw [hb2 i hi, hmem1 s i (by omega_using [hs, hi])]
  refine ⟨?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [Nat.two_mul, bytesAt_split, bytesAt_masked hbr, bytesAt_masked hbs]
    cases valid <;> simp only [Bool.false_eq_true, ↓reduceIte, List.replicate_append_replicate]
  · intro x hx
    rw [hf2 x (fun j hj => by simpa only [Offset.add_add] using hx (L.qLen + j) (by omega_using [hj]))]
    exact hf1 x (fun j hj => hx j (by omega_using [hj]))

end VG.Proof.Dsa.AArch64

end

end


/-! # Signature release, success return value and restored registers -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def signRelease : Prog isa := seqs [SignVerify.writeScalar r false, SignVerify.writeScalar s true,
  .block SignVerify.result]

theorem signRelease_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa signRelease s0 fun s2 =>
      s2.gpr .x0 = BitVec.ofNat 64 valid.toNat ∧
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep coreRegs s0 s2 := by
  unfold signRelease seqs
  apply WP.assoc
  refine WP.seq (WP.mono (writeSignature_ok h0 hm hw hsep) fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  have hn := h0.scratch.nowrap
  have hword (d : Nat) (hd : d + 8 ≤ usedBytes) : word s1.mem L.base d = word s0.mem L.base d := by
    apply Mem.readW_congr
    intro i hi
    exact hf1 _ (fun j hj => scr_ne_out hsep (by omega_using [hd, hi]) (by omega_using [hn]) j hj)
  have hmask := (hword Field.mask.offset (by decide)).trans hm
  refine WP.mono (result_ok (h0.scratch.congr hk1.wr) ((hk1.gpr .x0 (by decide)).trans h0.parent.x0)
    (by decide) hmask) fun s2 ⟨ha, hmem, hk2⟩ => ?_
  refine ⟨ha, ?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [hmem]
    exact hb1
  · intro x hx
    rw [hmem]
    exact hf1 x hx

end VG.Proof.Dsa.AArch64
