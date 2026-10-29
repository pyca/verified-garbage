module

public import VerifiedGarbage.Proof.Ffdh.Arm.SampleBoundLaw
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedCap
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCap
import VerifiedGarbage.Proof.Ffdh.Arm.VettedCapCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBound
import VerifiedGarbage.Proof.Ffdh.Arm.KeyBoundCT
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Ffdh.Arm.BranchCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Compose public group recognition with the verified cap installation -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedCap
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure RecognitionLaw (env : SampleEnvironment) (cap : Inputs → Nat) (code : Prog isa) : Prop where
  correct : ∀ (s : State) {p : Inputs} {slots : List Nat}, Context p slots s → env.holds p s →
    (2 ^ (64 * (p.w - 1)) ≤ p.P) → 24 ∈ slots → 28 ∈ slots → 32 ∈ slots →
    WP isa code s fun t => Context p slots t ∧ t.gpr .r11 = BitVec.ofNat 32 (cap p) ∧
      t.mem = s.mem ∧ Rest roundClobbers s t
  ct : ∀ {p : Inputs} {slots : List Nat}, (2 ^ (64 * (p.w - 1)) ≤ p.P) → 24 ∈ slots → 28 ∈ slots → 32 ∈ slots →
    RelCT isa (fun s t => (Context p slots s ∧ env.holds p s) ∧ (Context p slots t ∧ env.holds p t) ∧
      env.publicRel s t ∧ s.sp = t.sp) code (fun _ _ => True)

structure LayoutLaw (cap : Inputs → Nat) (layout : (p : Inputs) → ScalarLayout p) : Prop where
  zero : ∀ p, (2 ^ (64 * (p.w - 1)) ≤ p.P) → p.P % 2 = 1 → BitVec.ofNat 32 (cap p) = 0 →
    (layout p).width = p.scalarWidth ∧ (layout p).mask = p.scalarMask
  nonzero : ∀ p, (2 ^ (64 * (p.w - 1)) ≤ p.P) → p.P % 2 = 1 → BitVec.ofNat 32 (cap p) ≠ 0 → ∀ old,
    VG.Impl.Ffdh.Arm.VettedCap.result VG.Impl.Ffdh.Arm.VettedCap.choices
      (BitVec.ofNat 32 (cap p)) old = (BitVec.ofNat 32 (layout p).width, (layout p).mask)

theorem standard_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound s fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 p.scalarWidth ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = p.scalarMask ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  refine WP.mono (keyBound_ok s h stable h24 h28 h32 h60) ?_
  rintro t ⟨⟨context, frame⟩, rest⟩
  have common : Context p slots t :=
    ⟨⟨context.workspace, context.locals, context.domain, context.domainStack,
      fun d hd => context.saved d (by simp only [List.mem_cons]; exact Or.inr (Or.inr hd))⟩, context.ptr⟩
  exact ⟨common, context.saved 20 (by simp), context.saved 68 (by simp), frame,
    rest.mono (by simp [roundClobbers])⟩

theorem apply_ok {cap : Inputs → Nat} {layout : (p : Inputs) → ScalarLayout p}
    (law : LayoutLaw cap layout) (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1)
    (capReg : s.gpr .r11 = BitVec.ofNat 32 (cap p))
    (stable : stableSlots slots = true) (common : sampleSlots slots)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    WP isa (.seq VG.Impl.Ffdh.Arm.Domain.testFlag (.ite .ne VG.Impl.Ffdh.Arm.VettedCap.code
      VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound)) s fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 (layout p).width ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = (layout p).mask ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (testFlag_ok s) ?_
  rintro u ⟨⟨flag, mem⟩, rest⟩
  have ctx := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
  have capU : u.gpr .r11 = BitVec.ofNat 32 (cap p) := (rest.gpr .r11 (by simp)).trans capReg
  have finish {c : Prog isa} (run : WP isa c u fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 (layout p).width ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = (layout p).mask ∧
      Frame [⟨off (State.addr u.sp) 20, 4⟩, ⟨off (State.addr u.sp) 68, 4⟩] u.mem t.mem ∧
      Rest roundClobbers u t) : WP isa c u fun t => Context p slots t ∧
      t.mem.readW (off (State.addr t.sp) 20) 32 = BitVec.ofNat 32 (layout p).width ∧
      t.mem.readW (off (State.addr t.sp) 68) 32 = (layout p).mask ∧
      Frame [⟨off (State.addr s.sp) 20, 4⟩, ⟨off (State.addr s.sp) 68, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
    refine WP.mono run ?_
    rintro t ⟨context, width, mask, frame, restT⟩
    rw [mem, rest.sp] at frame
    exact ⟨context, width, mask, frame, (rest.mono (by simp [roundClobbers])).trans restT⟩
  by_cases zero : BitVec.ofNat 32 (cap p) = 0
  · refine WP.ite false (by change some (!u.z) = some false; rw [flag, capReg, zero]; rfl) (by simp) ?_
    intro _
    apply finish
    obtain ⟨width, mask⟩ := law.zero p normalized odd zero
    rw [width, mask]
    exact standard_ok u ctx stable h24 h28 h32 h60
  · refine WP.ite true (by
      change some (!u.z) = some true
      have flagFalse : (BitVec.ofNat 32 (cap p) == 0) = false :=
        Bool.eq_false_iff.mpr (fun same => zero (beq_iff_eq.mp same))
      rw [flag, capReg, flagFalse]
      rfl) ?_ (by simp)
    intro _
    apply finish
    refine WP.mono (code_ok u ctx common) ?_
    rintro t ⟨context, width, mask, frame, restT⟩
    rw [capU, law.nonzero p normalized odd zero] at width mask
    exact ⟨context, width, mask, frame, restT⟩


private structure Flagged (p : Inputs) (slots : List Nat) (bits : BitVec 32) (s : State) : Prop where
  context : Context p slots s
  capReg : s.gpr .r11 = bits
  flag : s.z = (bits == 0)

theorem apply_ct {p : Inputs} {slots : List Nat} (bits : BitVec 32)
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ s.gpr .r11 = bits) ∧
      (Context p slots t ∧ t.gpr .r11 = bits) ∧ s.sp = t.sp)
      (.seq VG.Impl.Ffdh.Arm.Domain.testFlag (.ite .ne VG.Impl.Ffdh.Arm.VettedCap.code
        VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound)) (fun _ _ => True) := by
  have wp (s : State) (h : Context p slots s ∧ s.gpr .r11 = bits) :
      WP isa VG.Impl.Ffdh.Arm.Domain.testFlag s (Flagged p slots bits) := by
    refine WP.mono (testFlag_ok s) ?_
    rintro t ⟨⟨flag, mem⟩, rest⟩
    exact ⟨h.1.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.1.ptr),
      (rest.gpr .r11 (by simp)).trans h.2, by rw [flag, h.2]⟩
  have branches : RelCT isa (fun s t => Flagged p slots bits s ∧ Flagged p slots bits t ∧ s.sp = t.sp)
      (.ite .ne VG.Impl.Ffdh.Arm.VettedCap.code VG.Impl.Ffdh.Arm.Domain.GenerateKey.bound)
      (fun _ _ => True) := by
    apply RelCT.ite (fun s t h => by change some (!s.z) = some (!t.z); rw [h.1.flag, h.2.1.flag])
    · exact code_ct.mono (fun _ _ h => ⟨h.1.1.capReg.trans h.1.2.1.capReg.symm, h.1.2.2⟩)
        (fun _ _ _ => trivial)
    · exact (keyBound_ct h24 h28 h32 h60).mono
        (fun _ _ h => ⟨h.1.1.context, h.1.2.1.context, h.1.2.2⟩) (fun _ _ _ => trivial)
  exact relCT_chain (testFlag_ct.mono (fun _ _ _ => trivial) (fun _ _ _ => trivial)) wp wp branches


theorem boundLaw {env : SampleEnvironment} {cap : Inputs → Nat}
    {layout : (p : Inputs) → ScalarLayout p} {recognizer : Prog isa}
    (recognition : RecognitionLaw env cap recognizer) (layoutLaw : LayoutLaw cap layout) :
    SampleBoundLaw env layout (VG.Impl.Ffdh.Arm.VettedCap.bound recognizer) := by
  constructor
  · intro s p slots context environment normalized odd stable common h24 h28 h32 h60
    rw [VG.Impl.Ffdh.Arm.VettedCap.bound, WP.seq_iff]
    refine WP.mono (recognition.correct s context environment normalized h24 h28 h32) ?_
    rintro u ⟨ctx, capReg, mem, rest⟩
    refine WP.mono (apply_ok layoutLaw u ctx normalized odd capReg stable common h24 h28 h32 h60) ?_
    rintro t ⟨ctxT, width, mask, frame, restT⟩
    rw [mem, rest.sp] at frame
    exact ⟨ctxT, width, mask, frame, rest.trans restT⟩
  · intro p slots _stable _common normalized _odd h24 h28 h32 h60 s t tr1 tr2 u v h e1 e2
    let P1 := fun z : State => Context p slots z ∧ env.holds p z ∧ z.syms = s.syms
    let P2 := fun z : State => Context p slots z ∧ env.holds p z ∧ z.syms = t.syms
    have first : RelCT isa (fun z z' => P1 z ∧ P2 z' ∧ z.sp = z'.sp) recognizer (fun _ _ => True) :=
      (recognition.ct normalized h24 h28 h32).mono
        (fun _ _ k => ⟨⟨k.1.1, k.1.2.1⟩, ⟨k.2.1.1, k.2.1.2.1⟩,
          env.public_stable h.2.2.1 k.1.2.2 k.2.1.2.2, k.2.2⟩) (fun _ _ _ => trivial)
    have run : RelCT isa (fun z z' => P1 z ∧ P2 z' ∧ z.sp = z'.sp)
        (VG.Impl.Ffdh.Arm.VettedCap.bound recognizer) (fun _ _ => True) := by
      unfold VG.Impl.Ffdh.Arm.VettedCap.bound
      exact relCT_chain first
        (fun z k => WP.mono (recognition.correct z k.1 k.2.1 normalized h24 h28 h32) fun _ a => ⟨a.1, a.2.1⟩)
        (fun z k => WP.mono (recognition.correct z k.1 k.2.1 normalized h24 h28 h32) fun _ a => ⟨a.1, a.2.1⟩)
        (apply_ct (BitVec.ofNat 32 (cap p)) h24 h28 h32 h60)
    exact run s t tr1 tr2 u v ⟨⟨h.1.1, h.1.2, rfl⟩, ⟨h.2.1.1, h.2.1.2, rfl⟩, h.2.2.2⟩ e1 e2


end VG.Proof.Ffdh.Arm.VettedCap
