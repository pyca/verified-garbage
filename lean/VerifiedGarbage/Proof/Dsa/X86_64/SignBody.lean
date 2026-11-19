module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Arithmetic
import Mathlib.Tactic.Convert
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
public import VerifiedGarbage.Impl.Bignum.X86_64
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Dsa.X86_64.SignRelease`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.CopyMasked`, which this module and modules that import it used -/

section

/-! # Fixed-length masked signature output -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

abbrev copyMaskedByte : List Instr :=
  [.movzx8 .rax (at0 .rsi), .alu .and .rax (.reg .r8), .store8 (at0 .rdx) .rax,
    .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

theorem masked_byte (b : Byte) (valid : Bool) :
    (b.zeroExtend 64 &&& mask valid).setWidth 8 = if valid then b else 0 := by
  cases valid <;> simp [mask, BitVec.zeroExtend, BitVec.setWidth_setWidth_of_le]
  exact BitVec.and_allOnes

structure CopyMaskedInv (s : State) (src out : Addr) (n j : Nat) (valid : Bool) (t : State) : Prop where
  keep : Keep [.rax, .rsi, .rdx, .rcx] s t
  rsi : t.gpr .rsi = src + BitVec.ofNat 64 j
  rdx : t.gpr .rdx = out + BitVec.ofNat 64 j
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - j)
  bytes : ∀ i < j, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x

theorem copyMasked_ok {s : State} {src out : Addr} {n : Nat} {valid : Bool}
    (hsi : s.gpr .rsi = src) (hdx : s.gpr .rdx = out) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (h8 : s.gpr .r8 = mask valid) (h1 : 0 < n) (h64 : n < 2 ^ 64)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < n, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < n, ∀ j < n, src + BitVec.ofNat 64 i ≠ out + BitVec.ofNat 64 j) :
    WP isa (.loop (.block copyMaskedByte) .ne) s fun t =>
      (∀ i < n, t.mem (out + BitVec.ofNat 64 i) = if valid then s.mem (src + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < n, x ≠ out + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .rsi, .rdx, .rcx] s t := by
  refine WP.mono (wp_upto (a := 0) (N := n) h1 (CopyMaskedInv s src out n · valid) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by simpa using hsi, by simpa using hdx, by simpa using hcx,
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩)
    fun t ht => ⟨ht.bytes, ht.frame, ht.keep⟩
  intro j _ hj t ht
  have hrd : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.1, ht.keep.2.2]; exact hr j hj
  have hwr : InRegions t.wr (out + BitVec.ofNat 64 j) 1 := by
    rw [ht.keep.2.2]; exact hw j hj
  have ht8 := (ht.keep.gpr (show Reg.r8 ∉ _ by decide)).trans h8
  have hval := ht.frame (src + BitVec.ofNat 64 j) (fun i hi => hsep j hj i (by omega_using [hj, hi]))
  refine WP.mono (WP.keep [.rax, .rsi, .rdx, .rcx] (Q := fun u =>
    u.mem = t.mem.writeW (out + BitVec.ofNat 64 j) (if valid then s.mem (src + BitVec.ofNat 64 j) else (0 : Byte)) ∧
    u.gpr .rsi = src + BitVec.ofNat 64 (j + 1) ∧ u.gpr .rdx = out + BitVec.ofNat 64 (j + 1) ∧
    u.gpr .rcx = BitVec.ofNat 64 (n - (j + 1)) ∧ u.zf = some (decide (j + 1 = n))) ?_ rfl)
    fun u ⟨⟨hum, husi, hudx, hucx, huz⟩, hku⟩ => ?_
  · unfold copyMaskedByte
    xrun [State.ea, at0, ht.rsi, ht.rdx, ht.rcx, ht8,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrd, hwr, masked_byte, hval,
      ofNat64_pred (show 1 ≤ n - j by omega_using [hj]) (by omega_using [h64]), BitVec.add_assoc, ofNat_add_one,
      ofNat64_beq_zero (show n - j - 1 < 2 ^ 64 by omega_using [h64])]
    exact ⟨by rw [show n - j - 1 = n - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩
  · refine ⟨huz, (ht.keep.trans hku).mono (by decide), husi, hudx, hucx, ?_, ?_⟩
    · intro i hi
      rw [hum, writeW8_apply]
      by_cases hij : i = j
      · subst i; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [h64, hj, hi]) (by omega_using [h64, hj]) hij))]
        exact ht.bytes i (by omega_using [hi, hij])
    · intro x hx
      rw [hum, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
      exact ht.frame x fun i hi => hx i (by omega_using [hi])

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.WriteScalarHead`, which this module and modules that import it used -/

section

/-! # Resolving the two signature output halves -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev scalarHead (offset : Nat) (second : Bool) : List Instr :=
  ([.mov .rsi (.reg .rdi), .alu .add .rsi (.imm (BitVec.ofNat 32 offset)),
    .mov .rdx (.mem (Core.field .out)), .mov .rcx (.mem (Core.field .qLen)),
    .mov .r8 (.mem (Core.field .mask))] : List Instr) ++
    (if second then [.alu .add .rdx (.reg .rcx)] else [])

theorem scalarHead_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 31)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool) :
    WP isa (.block (scalarHead offset second)) s fun t =>
      t.gpr .rsi = off B offset ∧ t.gpr .rdx = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .rcx = BitVec.ofNat 64 q ∧ t.gpr .r8 = mask valid ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8] (Q := fun t =>
      t.gpr .rsi = off B offset ∧ t.gpr .rdx = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .rcx = BitVec.ofNat 64 q ∧ t.gpr .r8 = mask valid ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨hsi, hdx, hcx, h8, hmem⟩, hk⟩ => ⟨hsi, hdx, hcx, h8, hmem, hk⟩
  · cases second <;> unfold scalarHead <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
    all_goals
      xrun [State.ea, Core.field, fieldAddress, hdi, hout, hq, hm, sx_ofNat ho,
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
  · cases second <;> rfl

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.WriteScalar`, which this module and modules that import it used -/

section

/-! # Masked copying of each DSA signature scalar to the caller -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem writeScalar_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 31)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool)
    (h1 : 0 < q) (h64 : q < 2 ^ 64) (hsrc : offset + q ≤ Z)
    (hw : ∀ i < q, InRegions s.wr ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < q, Z ≤ ofs B ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i)) :
    WP isa (SignVerify.writeScalar offset second) s fun t =>
      (∀ i < q, t.mem ((if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) =
        if valid then s.mem (off B offset + BitVec.ofNat 64 i) else 0) ∧
      (∀ x, (∀ i < q, x ≠ (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep [.rax, .rsi, .rdx, .rcx, .r8] s t := by
  unfold SignVerify.writeScalar seqs
  refine WP.seq (WP.mono (scalarHead_ok hs hdi hZ ho hout hq hm second)
    fun u ⟨husi, hudx, hucx, hu8, hum, hku⟩ => ?_)
  have hr : ∀ i < q, InRegions (u.rd ++ u.wr) (off B offset + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hku.2.1, hku.2.2, show off B offset + BitVec.ofNat 64 i = off B (offset + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    obtain ⟨r, hr, hc⟩ := hs.region (d := offset + i) (by omega_using [hsrc, hi]) (show 0 < 1 by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hsep' : ∀ i < q, ∀ j < q, off B offset + BitVec.ofNat 64 i ≠
      (if second then out + BitVec.ofNat 64 q else out) + BitVec.ofNat 64 j := by
    intro i hi j hj
    exact scr_ne_out hsep (d := offset) (i := i) (by omega_using [hsrc, hi]) (by have := hs.nowrap; omega_using [this]) j hj
  refine WP.mono (copyMasked_ok husi hudx hucx hu8 h1 h64 hr
    (fun i hi => by rw [hku.2.2]; exact hw i hi) hsep') fun t ⟨htb, htf, hkt⟩ => ?_
  exact ⟨by rw [hum] at htb; exact htb, fun x hx => (htf x hx).trans (congrFun hum x),
    (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.WriteSignature`, which only this module used -/

section

/-! ### `Dsa.X86_64.ReleaseBytes`, which only this module used -/

section

/-! # Byte-string postconditions for masked DSA signature release -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64

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

end VG.Proof.Dsa.X86_64

end

end


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
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega_using [hq32]
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega_using [hq32]
  have hout := h0.fields .out (by decide)
  have hql : word s0.mem L.base Field.qLen.offset = BitVec.ofNat 64 L.qLen := h0.length .q
  refine WP.seq (WP.mono (writeScalar_ok h0.scratch h0.parent.rdi (by decide) (by decide) hout hql hm false
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
    rw [hk1.2.2, Offset.add_add]
    exact hw _ (by omega_using [hi])
  have hsep2 : ∀ i < L.qLen, usedBytes ≤ ofs L.base ((L.fields .out + BitVec.ofNat 64 L.qLen) + BitVec.ofNat 64 i) := by
    intro i hi
    rw [Offset.add_add]
    exact hsep _ (by omega_using [hi])
  refine WP.mono (writeScalar_ok (h0.scratch.congr hk1.2.2) ((hk1.gpr (by decide)).trans h0.parent.rdi)
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

end VG.Proof.Dsa.X86_64

end

end


/-! # Signature release, success return value and restored registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def signRelease : Prog isa := seqs [SignVerify.writeScalar r false, SignVerify.writeScalar s true,
  .block SignVerify.result]

theorem signRelease_ok {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa signRelease s0 fun s2 =>
      s2.gpr .rax = BitVec.ofNat 64 valid.toNat ∧
      Spec.Rsa.bytesAt s2.mem (L.fields .out) (2 * L.qLen) =
        (if valid then Spec.Rsa.bytesAt s0.mem (off L.base r) L.qLen ++
          Spec.Rsa.bytesAt s0.mem (off L.base s) L.qLen else List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, s2.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) → s2.mem x = s0.mem x) ∧
      Keep mmRegs s0 s2 := by
  unfold signRelease seqs
  apply WP.assoc
  refine WP.seq (WP.mono (writeSignature_ok h0 hm hw hsep) fun s1 ⟨hb1, hf1, hk1⟩ => ?_)
  have hn := h0.scratch.nowrap
  have hword (d : Nat) (hd : d + 8 ≤ usedBytes) : word s1.mem L.base d = word s0.mem L.base d := by
    apply Mem.readW_congr
    intro i hi
    exact hf1 _ (fun j hj => scr_ne_out hsep (by omega_using [hd, hi]) (by omega_using [hn]) j hj)
  have hmask := (hword Field.mask.offset (by decide)).trans hm
  refine WP.mono (result_ok (h0.scratch.congr hk1.2.2) ((hk1.gpr (by decide)).trans h0.parent.rdi)
    (by decide) hmask) fun s2 ⟨ha, hsaved, hmem, hk2⟩ => ?_
  refine ⟨ha, ?_, ?_, ?_, (hk1.trans hk2).mono (by decide)⟩
  · rw [hmem]
    exact hb1
  · intro i hi
    exact (hsaved i hi).trans (hword _ (by change 8 * i + 8 ≤ 15712; omega_using [hi]))
  · intro x hx
    rw [hmem]
    exact hf1 x hx

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SignBytesSpec`, which this module and modules that import it used -/

section

/-! # The computed scalars and rejection mask implement the packed signing spec -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
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

end VG.Proof.Dsa.X86_64

end

end

/-! # Complete computation and signature release from initialized scratch -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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

def signBody (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (signCompute sq mul) signRelease

theorem signBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte} (h : SigningOperands L data yb qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (signBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (signAccepted L data yb valid).toNat ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) =
        (if signAccepted L data yb valid then Spec.Dsa.encodeBE L.qLen (data.r L) ++
          Spec.Dsa.encodeBE L.qLen (data.s L) else List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  unfold signBody
  refine WP.seq (WP.mono (signCompute_ok M Sq h0 hp hq hop hoq hpf hqf data h.generator h.publicValue
    h.subgroup h.privateScalar h.nonce h.digest h.generatorLength h.publicLength h.subgroupLength
    h.privateLength h.nonceLength h.digestBound h.subgroupValue hm)
    fun s1 ⟨h1, hm1, hr1, hs1, hf1, hk1⟩ => ?_)
  refine WP.mono (signRelease_ok h1 hm1 (fun i hi => by rw [hk1.2.2]; exact hw i hi) hsep)
    fun t ⟨ha, hb, hsave, hf, hk⟩ => ?_
  refine ⟨ha, ?_, ?_, ?_, (hk1.trans hk).mono (by decide)⟩
  · rw [hr1, hs1] at hb
    exact hb
  · intro i hi
    exact (hsave i hi).trans (hf1.word (Or.inl (by omega_using [hi])) (by omega_using [hi]))
  · intro x hx ho
    exact (hf x ho).trans (hf1 x (Or.inr (by
      have hu : 128 ≤ usedBytes := by decide
      omega_using [hx, hu])))

theorem signBody_spec (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
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
    WP isa (signBody Sq.mm M.mm) s0 fun t =>
      let result := Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) = result.getD (List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have he := signBytes_compute L data yb key digest n hsize hop hoq hpf hqf h.publicLength hkl h.nonceLength hk hqn hz
  refine WP.mono (signBody_ok M Sq h0 hp hq hop hoq hpf hqf data h hm hw hsep) fun t ht => ?_
  rw [he]
  cases hc : signAccepted L data yb true <;> simpa only [hc, Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, ↓reduceIte,
    Spec.Dsa.signStatus, Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some] using ht

end VG.Proof.Dsa.X86_64
