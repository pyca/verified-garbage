module

import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.SignBody
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyBody
public import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
public import VerifiedGarbage.Proof.Dsa.AArch64.SignRelease
public import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignRelease
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run

/-! ### `Dsa.AArch64.BodyCT`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.SignReleaseCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.WriteScalarCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.FailureCT`, which this module and modules that import it used -/

section

/-! # Constant-time clearing of a rejected DSA signature -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure FailurePublic where
  base : Addr
  output : Addr
  width : Nat

def FailurePre (p : FailurePublic) (s : State) : Prop :=
  ∃ Z, Scr s p.base Z ∧ pWorkspace ≤ Z ∧ s.gpr .x0 = p.base ∧
    word s.mem p.base Field.out.offset = p.output ∧
    word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.width

def FailureRegs (p : FailurePublic) (s : State) : Prop :=
  s.gpr .x0 = p.base ∧ s.gpr .x1 = p.output ∧ s.gpr .x2 = BitVec.ofNat 64 (2 * p.width)

theorem signFailure_ct : RelCT isa (Two FailurePre) SignVerify.signFailure (fun _ _ => True) := by
  unfold SignVerify.signFailure seqs
  refine RelCT.seq (two_piece (Ψ := FailureRegs) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, ho, hq⟩
    refine WP.mono (WP.keep [.x3, .x1, .x2] (Q := fun t =>
      t.gpr .x1 = p.output ∧ t.gpr .x2 = BitVec.ofNat 64 (2 * p.width)) ?_ rfl rfl rfl)
      fun t ⟨⟨hsi, hcx⟩, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hdi, hsi, hcx⟩
    brun [field_enc .out, field_enc .qLen, Core.field, fieldAddress, hdi, ho, hq,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ)]
    rw [BitVec.ofNat_add_ofNat, Nat.two_mul]
  · exact two_taint [.x0, .x1, .x2]
      (pins_of (fun p r => if r = .x0 then p.base else if r = .x1 then p.output else BitVec.ofNat 64 (2 * p.width))
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant-time signature output, including rejection masks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ScalarOutRegs (offset : Nat) (second : Bool) (p : FailurePublic) (s : State) : Prop :=
  s.gpr .x1 = off p.base offset ∧
  s.gpr .x2 = (if second then p.output + BitVec.ofNat 64 p.width else p.output) ∧
  s.gpr .x9 = BitVec.ofNat 64 p.width

theorem writeScalar_ct (offset : Nat) (second : Bool) (ho : offset < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (scalarHead offset second)) hc).isSome = true) :
    RelCT isa (Two FailurePre) (SignVerify.writeScalar offset second) (fun _ _ => True) := by
  unfold SignVerify.writeScalar seqs
  refine RelCT.seq (two_piece (Ψ := ScalarOutRegs offset second) [.x0]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr
      obtain ⟨_, _, _, hdi, _⟩ := h
      simp only [List.mem_singleton] at hr
      subst r
      exact hdi)) hT ?_) ?_
  · intro p s ⟨Z, hs, hZ, hdi, hout, hq⟩
    have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_using [ho]
    change WP isa (.block (scalarHead offset second)) s (ScalarOutRegs offset second p)
    unfold scalarHead
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x3, .x1, .x2, .x9, .x8] (Q := fun t =>
      t.gpr .x1 = off p.base offset ∧ t.gpr .x2 = p.output ∧ t.gpr .x9 = BitVec.ofNat 64 p.width)
      ?_ rfl rfl rfl) fun t ⟨⟨h1, h2, h9⟩, hk⟩ => ?_
    · brun [Core.field, field_enc .out, field_enc .qLen, field_enc .mask, fieldAddress,
        hdi, hout, hq, hoff,
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
    cases second
    · exact WP.block_nil ⟨h1, h2, h9⟩
    · brun [ScalarOutRegs, h1, h2, h9]
  · exact two_taint [.x1, .x2, .x9]
      (pins_of (fun p r => if r = .x1 then off p.base offset else if r = .x2 then
          (if second then p.output + BitVec.ofNat 64 p.width else p.output) else BitVec.ofNat 64 p.width)
        (by
          intro p s h r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.1
          · exact h.2.1
          · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of masked signature release and register restoration -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReleasePublic extends FailurePublic where
  positive : 0 < width
  bound : width ≤ 32

structure ReleasePre (p : ReleasePublic) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  out : word s.mem p.base Field.out.offset = p.output
  width : word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.width
  mask : ∃ valid : Bool, word s.mem p.base Field.mask.offset = mask valid
  writable : ∀ i < 2 * p.width, InRegions s.wr (p.output + BitVec.ofNat 64 i) 1
  separate : ∀ i < 2 * p.width, usedBytes ≤ ofs p.base (p.output + BitVec.ofNat 64 i)

theorem releaseScalar_ct (offset : Nat) (second : Bool) (ho : offset < 2 ^ 16)
    (hend : offset + 32 ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (scalarHead offset second)) hc).isSome = true) :
    RelCT isa (Two ReleasePre) (SignVerify.writeScalar offset second) (Two ReleasePre) := by
  refine two_post (two_map ReleasePublic.toFailurePublic
    (fun _ _ h => ⟨usedBytes, h.scratch, by decide, h.x0, h.out, h.width⟩)
    (writeScalar_ct offset second ho hT)) ?_
  intro p s h
  obtain ⟨valid, hm⟩ := h.mask
  have hw : ∀ i < p.width, InRegions s.wr
      ((if second then p.output + BitVec.ofNat 64 p.width else p.output) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    cases second
    · exact h.writable i (by omega_using [hi])
    · rw [ite_eq_left rfl, Offset.add_add]
      exact h.writable _ (by omega_using [hi])
  have hsep : ∀ i < p.width, usedBytes ≤ ofs p.base
      ((if second then p.output + BitVec.ofNat 64 p.width else p.output) + BitVec.ofNat 64 i) := by
    intro i hi
    cases second
    · exact h.separate i (by omega_using [hi])
    · rw [ite_eq_left rfl, Offset.add_add]
      exact h.separate _ (by omega_using [hi])
  refine WP.mono (writeScalar_ok h.scratch h.x0 (by decide) ho h.out h.width hm second p.positive
    (by have := p.bound; omega_using [this]) (by have := p.bound; omega_using [hend, this]) hw hsep) fun t ⟨_, hf, hk⟩ => ?_
  have hword (f : Field) : word t.mem p.base f.offset = word s.mem p.base f.offset := by
    apply Mem.readW_congr
    intro i hi
    apply hf _
    intro j hj
    exact scr_ne_out hsep (by have hb := (VG.Proof.Dsa.field_bounds f).2; change f.offset + 8 ≤ 3456 at hb; change f.offset + i < 15712; omega_using [hi, hb])
      (by have := h.scratch.nowrap; omega_using [this]) j hj
  exact ⟨h.scratch.congr hk.wr, (hk.gpr .x0 (by decide)).trans h.x0,
    (hword .out).trans h.out, (hword .qLen).trans h.width, ⟨valid, (hword .mask).trans hm⟩,
    fun i hi => by rw [hk.wr]; exact h.writable i hi, h.separate⟩

theorem signRelease_ct : RelCT isa (Two ReleasePre) signRelease (fun _ _ => True) := by
  unfold signRelease seqs
  refine RelCT.seq (releaseScalar_ct r false (by decide) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (releaseScalar_ct s true (by decide) (by decide) (by taint_decide)) ?_
  exact two_map (fun p : ReleasePublic => p.base) (fun _ _ h => h.x0) result_ct

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time through validation, computation and the ABI return -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SigningBodyPre (p : SchedulePublic) (s : State) : Prop :=
  Ready p.layout s ∧
  (∃ data yb qb, SigningOperands p.layout data yb qb s ∧ data.digest.length = p.digestLen) ∧
  (∃ valid : Bool, word s.mem p.layout.base Field.mask.offset = mask valid) ∧
  (∀ i < 2 * p.layout.qLen, InRegions s.wr (p.layout.fields .out + BitVec.ofNat 64 i) 1) ∧
  (∀ i < 2 * p.layout.qLen, usedBytes ≤ ofs p.layout.base (p.layout.fields .out + BitVec.ofNat 64 i))

theorem SigningBodyPre.schedule {p : SchedulePublic} {s : State} (h : SigningBodyPre p s) :
    PublicKeyPre signComputeInputs p s := by
  obtain ⟨hr, ⟨data, yb, qb, ho, hd⟩, hm, _, _⟩ := h
  refine ⟨⟨hr, ?_, hm⟩, qb, ho.subgroup, ho.subgroupLength, ho.subgroupValue⟩
  intro a ha
  simp only [signComputeInputs, signInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨yb, ho.publicValue, ho.publicLength⟩
  · exact ⟨qb, ho.subgroup, ho.subgroupLength⟩
  · exact ⟨data.generator, ho.generator, ho.generatorLength⟩
  · exact ⟨data.nonce, ho.nonce, ho.nonceLength⟩
  · exact ⟨data.privateScalar, ho.privateScalar, ho.privateLength⟩
  · exact ⟨data.digest, ho.digest, hd⟩

def SchedulePublic.release (p : SchedulePublic) : ReleasePublic where
  base := p.layout.base
  output := p.layout.fields .out
  width := p.layout.qLen
  positive := p.layout.widths.1
  bound := p.layout.widths.2.1

theorem signingComputeRelease_ok (M : Mont) {p : SchedulePublic} {s : State} (h : SigningBodyPre p s) :
    WP isa (signCompute M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (signCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits data
    ho.generator ho.publicValue ho.subgroup ho.privateScalar ho.nonce ho.digest
    ho.generatorLength ho.publicLength ho.subgroupLength ho.privateLength ho.nonceLength
    ho.digestBound ho.subgroupValue hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.x0, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.wr]; exact hw i hi, hsep⟩

theorem signBody_ct (M : Mont) : RelCT isa (Two SigningBodyPre) (signBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule) (signCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => signingComputeRelease_ok M h
  · exact two_map SchedulePublic.release (fun _ _ h => h) signRelease_ct

def VerifyingBodyPre (p : SchedulePublic) (s : State) : Prop :=
  Ready p.layout s ∧
  (∃ data qb, VerificationOperands p.layout data qb s ∧ data.digest.length = p.digestLen) ∧
  ∃ valid : Bool, word s.mem p.layout.base Field.mask.offset = mask valid

theorem VerifyingBodyPre.schedule {p : SchedulePublic} {s : State} (h : VerifyingBodyPre p s) :
    PublicKeyPre verifyComputeInputs p s := by
  obtain ⟨hr, ⟨data, qb, ho, hd⟩, hm⟩ := h
  refine ⟨⟨hr, ?_, hm⟩, qb, ho.subgroup, ho.subgroupLength, ho.subgroupValue⟩
  intro a ha
  simp only [verifyComputeInputs, verifyInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨qb, ho.subgroup, ho.subgroupLength⟩
  · exact ⟨data.generator, ho.generator, ho.generatorLength⟩
  · exact ⟨data.publicValue, ho.publicValue, ho.publicLength⟩
  · exact ⟨data.signatureR, ho.signatureR, ho.rLength⟩
  · exact ⟨data.signatureS, ho.signatureS, ho.sLength⟩
  · exact ⟨data.digest, ho.digest, hd⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant-time argument capture and packed-key pointer setup -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Scratch and the stack pointer are public; pointed-to argument values
need not agree except for the scratch pointer loaded from its ABI slot. -/
def EntryStart (j : Nat) (p : Addr × Addr) (s : State) : Prop :=
  s.sp = p.2 ∧ word s.mem p.2 (8 * j) = p.1 ∧
    InRegions (s.rd ++ s.wr) (off p.2 (8 * j)) 8

def EntryPtrs (p : Addr × Addr) (s : State) : Prop := s.gpr .x11 = p.1 ∧ s.sp = p.2

theorem pins_entryPtrs : Pins EntryPtrs [.x11] :=
  pins_of (fun p _ => p.1) (by
    intro p s h r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1)

theorem entryScratch_ct (j : Nat) (hj : j < 4096) {hint : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs []) (.block [.ldrSp .x11 (8 * j)]) hint).isSome = true) :
    RelCT isa (Two (EntryStart j)) (.block [.ldrSp .x11 (8 * j)]) (Two EntryPtrs) := by
  refine two_piece [] (by intro p s t hs ht r hr; cases hr) hT ?_
  intro p s h
  exact WP.mono (entryScratch_ok j hj h.1 h.2.2 h.2.1) fun t ⟨hb, _, hk⟩ =>
    ⟨hb, hk.sp.trans h.1⟩

theorem signEntry_ct : RelCT isa (Two (EntryStart 1)) (.block SignVerify.signEntry) (fun _ _ => True) := by
  unfold SignVerify.signEntry
  rw [List.append_assoc]
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 1 (by decide) (by taint_decide))
    (two_taint [.x11] pins_entryPtrs (by taint_decide))

theorem verifyEntry_ct : RelCT isa (Two (EntryStart 0)) (.block SignVerify.verifyEntry) (fun _ _ => True) := by
  unfold SignVerify.verifyEntry
  rw [List.append_assoc]
  apply RelCT.block_append
  exact RelCT.seq (entryScratch_ct 0 (by decide) (by taint_decide))
    (two_taint [.x11] pins_entryPtrs (by taint_decide))

end VG.Proof.Dsa.AArch64
