module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtPre
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext

/-! ### `Rsa.Arm.PrivCall`, which this module and modules that import it used -/

section

/-! # Calls with their own frames preserve retained private-wrapper state -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def callClobbers : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

theorem call_rest {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (regs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) : Rest callClobbers s t := by
  refine ⟨?_, rd, wr, sp⟩
  intro r hr
  apply regs r
  · cases r <;> simp_all [callClobbers, preserved]
  · intro eq; subst r; exact hr (by simp [callClobbers])

theorem private_call_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : FrameStack.armStack code ≤ 56)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R)
    (separate : ∀ r ∈ wr, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r) :
    WP isa (.call name code) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧
      contract.post (s.callEntry.withRegions rd wr) (t.withRegions rd wr) := by
  refine FrameStack.WP.callF verified.1 pre read write
    (by rw [h.sp]; exact Nat.le_trans stack h.valid.stackLow) ?_
  intro t rdT wrT spT frame regs post
  have frame56 := FrameStack.Frame.belowA_mono frame stack (by rw [h.sp]; exact h.valid.stackLow)
  rw [h.sp] at frame56
  have rest := call_rest rdT wrT spT regs
  have frameBody : Frame (bodyWrites g) s.mem t.mem := frame56.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact sub r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  refine ⟨h.after frameBody rest, slots.after frame56 ?_, frame56, rest, post⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact separate r hr
  · simp only [List.mem_singleton] at hr
    subst r
    exact (h.valid.calleeInner.sub_right (Offset.sub_base _ (by decide : 64 + 24 ≤ frameBytes))).symm
end VG.Proof.Rsa.Arm

end

end

/-! # Call the verified CRT into the private stack temporary -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem PrivContext.temporaryWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (State.addr g.temporary) g.length := by
  rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
  exact ⟨_, h.inner.writable, Offset.contains_base _
    (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega_using [this]) (by decide : oM < 2 ^ 64)⟩

theorem crtCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (crtRd g ++ crtWr g) (s.rd ++ s.wr) ∧ Covers (crtWr g) s.wr := by
  have wr : Covers (crtWr g) s.wr := (Covers.one h.temporaryWrite).pair (Covers.one h.workspaceWrite)
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  refine (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 2).read).cons
    ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).cons
    ((Covers.one (h.sources 7).read).cons ?_))))))
  exact (Covers.one (show InRegions s.wr (State.addr g.stack) 56 from
    ⟨_, h.inner.writable, by simp [Region.Contains, frameBytes]⟩)).right

theorem crtWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ crtWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [oM, frameBytes]; omega_using [this])
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩

theorem crtWrites_slots {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ crtWr g, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r := by
  intro r hr
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.disjoint _ (Or.inl (by decide : 64 + 24 ≤ oM)) (by decide) (by have := h.maxLength; simp only [oM]; omega_using [this])
  · exact h.stackWorkspace.sub_left (fun x hx => h.innerSub x
      (Offset.sub_base _ (by decide : 64 + 24 ≤ frameBytes) x hx))

def CrtOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  Spec.Rsa.written s.mem (State.addr g.temporary) g.length (s.gpr .r0)
    (Spec.Rsa.privateCrt (bs 0) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7))

theorem crt_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (args : CrtArgs g s) :
    WP isa (.call v.name v.code) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (crtWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧ CrtOut g bs t := by
  refine WP.mono (private_call_ok h slots v.verified v.stack (crtCall_pre h args)
    (crtCovers h).1 (crtCovers h).2 (crtWrites_sub h.valid) (crtWrites_slots h.valid)) ?_
  rintro t ⟨ht, slotsT, frame, rest, post⟩
  refine ⟨ht, slotsT, frame, rest, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  have sa := fun {j} (hj : j < 14) => crtArgs_stack h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  simp only [args.output, args.modulus, args.length,
    sa (by decide : 0 < 14), sa (by decide : 2 < 14), sa (by decide : 3 < 14),
    sa (by decide : 4 < 14), sa (by decide : 5 < 14), sa (by decide : 6 < 14),
    sa (by decide : 8 < 14), sa (by decide : 10 < 14), PrivGeometry.argument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right] at post
  change Spec.Rsa.written t.mem (State.addr g.temporary) g.length (t.gpr .r0)
    (Spec.Rsa.privateCrt
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 2)) (g.sourceLength 2))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.mem (State.addr (g.sources 7)) (g.sourceLength 7))) at post
  rw [(h.sources 0).bytes, (h.sources 2).bytes, (h.sources 3).bytes, (h.sources 4).bytes,
    (h.sources 5).bytes, (h.sources 6).bytes, (h.sources 7).bytes] at post
  exact post
end VG.Proof.Rsa.Arm
