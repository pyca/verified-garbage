module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyCompute
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Tactic.Convert
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Execution
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words

/-! ### `Dsa.AArch64.SignRelease`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.CopyMasked`, which this module and modules that import it used -/

section

/-! # Fixed-length masked signature output -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.WriteBytes (writeW8_apply)

abbrev copyMaskedByte := VG.Impl.Dsa.AArch64.SignVerify.copyMaskedByte

theorem masked_byte (b : Byte) (valid : Bool) :
    (b.zeroExtend 64 &&& mask valid).setWidth 8 = if valid then b else 0 := by
  cases valid <;> simp [mask, BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le]
  exact BitVec.and_allOnes

structure CopyMaskedInv (s : State) (src out : Addr) (n j : Nat) (valid : Bool) (t : State) : Prop where
  keep : Keep [.x3, .x1, .x2, .x9] s t
  rsi : t.gpr .x1 = src + BitVec.ofNat 64 j
  rdx : t.gpr .x2 = out + BitVec.ofNat 64 j
  rcx : t.gpr .x9 = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copyMasked_ok {s : State} {src out : Addr} {n : Nat} {valid : Bool}
    (hsi : s.gpr .x1 = src) (hdx : s.gpr .x2 = out) (hcx : s.gpr .x9 = BitVec.ofNat 64 n)
    (h8 : s.gpr .x8 = mask valid) (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block copyMaskedByte) (.nonzero .x .x9)) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x3, .x1, .x2, .x9] s t := by
  refine WP.mono (wp_countdown (N := n) h64 h1 (fun j t => CopyMaskedInv s src out n j valid t)
    ?_ ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩ hcx)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j hj t ht hcount
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.rd, ht.keep.wr]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.wr]; exact hw j hj
  have ht8 := (ht.keep.gpr .x8 (by decide)).trans h8
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega_using [hj, hi]))
  refine WP.mono (WP.keep [.x3, .x1, .x2, .x9] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (if valid then s.mem (src + BitVec.ofNat 64 j) else (0 : Byte)) ∧
    u.gpr .x1 = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .x9 = BitVec.ofNat 64 (n - (j + 1))) ?_ rfl rfl rfl)
    fun u ⟨⟨hum, husi, hudx, hucx⟩, hku⟩ => ?_
  · unfold copyMaskedByte VG.Impl.Dsa.AArch64.SignVerify.copyMaskedByte
    have hb : ((s.mem (src + BitVec.ofNat 64 j)).setWidth 32).setWidth 64 =
        (s.mem (src + BitVec.ofNat 64 j)).zeroExtend 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
      have := (s.mem (src + BitVec.ofNat 64 j)).isLt
      omega_using []
    have hp : BitVec.ofNat 64 (n - j) - (1#64) = BitVec.ofNat 64 (n - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_using [hj]
    brun [ht.rsi, ht.rdx, ht.rcx, ht8, hrd, hwr, read_one, hb, hval, masked_byte,
      hp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rfl
  · refine ⟨⟨(ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [h64, hj, hi]) (by omega_using [h64, hj]) hij))]
        exact ht.bytes i (by omega_using [hi, hij])
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
      exact ht.frame x fun i hi => hx i (by omega_using [hi])

    · rw [hucx, hcount]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_using [hj]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.WriteScalarHead`, which this module and modules that import it used -/

section

/-! # Resolving the two signature output halves -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev scalarHead (offset : Nat) (second : Bool) : List Instr :=
  ([movi .x3 offset, .add .x .x1 .x0 .x3,
    Core.field .x2 .out, Core.field .x9 .qLen, Core.field .x8 .mask] : List Instr) ++
    (if second then [.add .x .x2 .x2 .x9] else [])

theorem scalarHead_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 16)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool) :
    WP isa (.block (scalarHead offset second)) s fun t =>
      t.gpr .x1 = off B offset ∧ t.gpr .x2 = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .x9 = BitVec.ofNat 64 q ∧ t.gpr .x8 = mask valid ∧
      t.mem = s.mem ∧ Keep [.x3, .x1, .x2, .x9, .x8] s t := by
  have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [ho]
  unfold scalarHead
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x1, .x2, .x9, .x8] (Q := fun t =>
    t.gpr .x1 = off B offset ∧ t.gpr .x2 = out ∧ t.gpr .x9 = BitVec.ofNat 64 q ∧
    t.gpr .x8 = mask valid ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h1, h2, h9, h8, hmem⟩, hk⟩ => ?_
  · brun [h0, hoff, Core.field, fieldAddress, field_enc .out, field_enc .qLen, field_enc .mask,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), hout, hq, hm]
  cases second
  · exact WP.block_nil ⟨h1, h2, h9, h8, hmem, hk⟩
  · refine WP.mono (WP.keep [.x2] (Q := fun u => u.gpr .x2 = out + BitVec.ofNat 64 q ∧ u.mem = t.mem)
      (by brun [h2, h9]) rfl rfl rfl) fun u ⟨⟨hu2, hum⟩, hku⟩ => ?_
    exact ⟨(hku.gpr .x1 (by decide)).trans h1, hu2, (hku.gpr .x9 (by decide)).trans h9,
      (hku.gpr .x8 (by decide)).trans h8, hum.trans hmem, (hk.trans hku).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.WriteScalar`, which this module and modules that import it used -/

section

/-! # Masked copying of each DSA signature scalar to the caller -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem writeScalar_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 16)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool)
    (h1 : 0 < q) (h64 : q < 2 ^ 64) (hsrc : offset + q ≤ Z)
    (hw : ∀ i < q, InRegions s.wr ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < q, Z ≤ ofs B ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i)) :
    WP isa (SignVerify.writeScalar offset second) s fun t =>
      (∀ i < q, t.mem ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) =
        if valid then s.mem (off B offset + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < q, x ≠ (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.x3, .x1, .x2, .x9, .x8] s t := by
  unfold SignVerify.writeScalar seqs
  refine WP.seq (WP.mono (scalarHead_ok hs hdi hZ ho hout hq hm second)
    fun u ⟨husi, hudx, hucx, hu8, hum, hku⟩ => ?_)
  have hr : ∀ i < q, InRegions (u.rd ++ u.wr) (off B offset + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.rd, hku.wr, show off B offset + BitVec.ofNat 64 i = off B (offset + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    obtain ⟨r, hr, hc⟩ := hs.region (d := offset + i) (by omega_using [hsrc, hi]) (show 0 < 1 by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsep' : ∀ i < q, ∀ j < q, off B offset + BitVec.ofNat 64 i ≠
      (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 j := by
    intro i hi j hj
    exact scr_ne_out hsep (d := offset) (i := i) (by omega_using [hsrc, hi]) (by have := hs.nowrap; omega_using [this]) j hj
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 h1 h64 hr
    (fun i hi => by rw [hku.wr]; exact hw i hi) hsep') fun t ⟨htb, htf, hkt⟩ => ?_
  exact ⟨by rw [hum] at htb; exact htb, fun x hx => (htf x hx).trans (congrFun hum x),
    (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

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

end

end

/-! ### `Dsa.AArch64.SignBytesSpec`, which only this module used -/

section

/-! # The computed scalars and rejection mask implement the packed signing spec -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG

def SignValues.key (L : ExecutionLayout) (data : SignValues) (yb : List Byte) : Spec.Dsa.Key :=
  ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩, Spec.Dsa.decodeBE yb,
    some (Spec.Dsa.decodeBE data.privateScalar)⟩

theorem signNonce_compute (L : ExecutionLayout) (data : SignValues) (yb digest : List Byte) (n : Nat)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.signWithNonce (data.key L yb) digest (Spec.Dsa.decodeBE data.nonce) =
      if !Spec.Dsa.keyValid (data.key L yb) ||
          !(0 < Spec.Dsa.decodeBE data.nonce && Spec.Dsa.decodeBE data.nonce < L.subgroup) then none else
        if data.r L == 0 || data.s L == 0 then none else some ⟨data.r L, data.s L⟩ := by
  have h := VG.Proof.Dsa.signWithNonce_reduced (data.key L yb) digest (Spec.Dsa.decodeBE data.nonce)
    (Spec.Dsa.decodeBE data.privateScalar) n rfl hq
  simp only [SignValues.key, SignValues.r, SignValues.s, VG.Proof.Dsa.powMod_rsa, hz,
    Bool.or_eq_true, beq_iff_eq] at h ⊢
  convert h using 1
  congr 1

theorem signBytes_compute (L : ExecutionLayout) (data : SignValues) (yb key digest : List Byte) (n : Nat)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hyl : yb.length = L.pLen) (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hnl : data.nonce.length = L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest =
      if signAccepted L data yb true then some (Spec.Dsa.encodeBE L.qLen (data.r L) ++
        Spec.Dsa.encodeBE L.qLen (data.s L)) else none := by
  have hqpos : 0 < L.subgroup := by have := (VG.Proof.Dsa.supported_bounds hsize).2.1; omega_using [hoq]
  rw [signAccepted_nonzero L data yb true hqpos hqf, privateAccepted_spec L data yb hsize hop hoq hpf hyl]
  unfold Spec.Dsa.signBytes
  simp only [L.lengths, decide_true, Bool.not_true, hkl, hnl, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk]
  rw [signNonce_compute L data yb digest n hq hz]
  change (if !decide (Spec.Dsa.parametersValid (data.key L yb).params) then none else
    (if !Spec.Dsa.keyValid (data.key L yb) ||
      !(0 < Spec.Dsa.decodeBE data.nonce && Spec.Dsa.decodeBE data.nonce < L.subgroup) then none else
      if data.r L == 0 || data.s L == 0 then none else some (⟨data.r L, data.s L⟩ : Spec.Dsa.Signature)) >>= fun sig =>
        some (Spec.Dsa.encodeBE L.qLen sig.r ++ Spec.Dsa.encodeBE L.qLen sig.s)) = _
  by_cases hp : Spec.Dsa.parametersValid (data.key L yb).params <;>
    cases hv : Spec.Dsa.keyValid (data.key L yb) <;>
    by_cases hn : 0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup <;>
    by_cases hr : data.r L = 0 <;> by_cases hs : data.s L = 0 <;>
    simp_all [SignValues.key, ← Bool.decide_and]

end VG.Proof.Dsa.AArch64

end

end


/-! # Complete computation and signature release from initialized scratch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SigningOperands (L : ExecutionLayout) (data : SignValues) (yb qb : List Byte) (s : State) : Prop where
  generator : OperandBytes s L.base usedBytes Core.generator data.generator
  publicValue : OperandBytes s L.base usedBytes Core.publicValue yb
  subgroup : OperandBytes s L.base usedBytes ⟨.input .q, .qLen⟩ qb
  privateScalar : OperandBytes s L.base usedBytes Core.privateScalar data.privateScalar
  nonce : OperandBytes s L.base usedBytes Core.nonce data.nonce
  digest : OperandBytes s L.base usedBytes Core.digest data.digest
  generatorLength : data.generator.length = L.pLen
  publicLength : yb.length = L.pLen
  subgroupLength : qb.length = L.qLen
  privateLength : data.privateScalar.length = L.qLen
  nonceLength : data.nonce.length = L.qLen
  digestBound : data.digest.length < 2 ^ 64
  subgroupValue : Spec.Dsa.decodeBE qb = L.subgroup

def signBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (signCompute mul) signRelease

theorem signBody_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte} (h : SigningOperands L data yb qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (signBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (signAccepted L data yb valid).toNat ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) =
        (if signAccepted L data yb valid then Spec.Dsa.encodeBE L.qLen (data.r L) ++
          Spec.Dsa.encodeBE L.qLen (data.s L) else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  unfold signBody
  refine WP.seq (WP.mono (signCompute_ok M h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.subgroup h.privateScalar h.nonce h.digest h.generatorLength h.publicLength h.subgroupLength
    h.privateLength h.nonceLength h.digestBound h.subgroupValue hm)
    fun s1 ⟨h1, hm1, hr1, hs1, hf1, hk1⟩ => ?_)
  refine WP.mono (signRelease_ok h1 hm1 (fun i hi => by rw [hk1.wr]; exact hw i hi) hsep)
    fun t ⟨ha, hb, hf, hk⟩ => ?_
  refine ⟨ha, ?_, ?_, (hk1.trans hk).mono (by decide)⟩
  · rw [hr1, hs1] at hb
    exact hb
  · intro x hx ho
    exact (hf x ho).trans (hf1 x (Or.inr (by
      have hu : 128 ≤ usedBytes := by decide
      omega_using [hx, hu])))

theorem signBody_spec (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : SignValues) {yb qb key digest : List Byte} {n : Nat}
    (h : SigningOperands L data yb qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hm : word s0.mem L.base Field.mask.offset = mask true)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (signBody M.mm) s0 fun t =>
      let result := Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) = result.getD (List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have he := signBytes_compute L data yb key digest n hsize hop hoq hpf hqf h.publicLength hkl h.nonceLength hk hqn hz
  refine WP.mono (signBody_ok M h0 hp hq hop hoq hpf hqf data h hm hw hsep) fun t ht => ?_
  rw [he]
  cases hc : signAccepted L data yb true <;> simpa only [hc, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
    Spec.Dsa.signStatus, Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some] using ht

end VG.Proof.Dsa.AArch64
