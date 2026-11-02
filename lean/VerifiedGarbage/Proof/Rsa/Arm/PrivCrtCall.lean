module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Call the verified CRT into the private stack temporary -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem PrivContext.temporaryWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (State.addr g.temporary) g.length := by
  rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
  exact ⟨_, h.inner.writable, Offset.contains_base _
    (by have := h.valid.maxLength; simp only [oM, frameBytes]; omega) (by decide : oM < 2 ^ 64)⟩

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
    exact Offset.sub_base _ (by have := h.maxLength; simp only [oM, frameBytes]; omega)
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩

theorem crtWrites_slots {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ crtWr g, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r := by
  intro r hr
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.disjoint _ (Or.inl (by decide : 64 + 24 ≤ oM)) (by decide) (by have := h.maxLength; simp only [oM]; omega)
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
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
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
