module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! Controller writes preserve the entropy tape, domain and saved AAPCS registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem KeyInput.domain_control {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨State.addr p.dp, p.dlen⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  rw [← h.2]
  exact (h.layout.separate (inControl s) (by simp [writes]) (inDomain s) (by simp [reads])).symm

theorem KeyInput.random_control {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨State.addr p.rp, p.randLen⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  rw [← h.2]
  exact (h.layout.separate (inControl s) (by simp [writes]) (inRand s) (by simp [reads])).symm

theorem KeyInput.saved_control {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨State.addr (p.sp - BitVec.ofNat 32 24), 24⟩ : Region).Disjoint ⟨State.addr p.control, 128⟩ := by
  have fit := h.bounds.stackFits
  rw [← h.2] at fit ⊢
  change stackUse ≤ s.sp.toNat at fit
  have sep := h.layout.stack (inControl s) (List.mem_append_left _ (by simp [writes]))
  rw [← FrameStack.addr_sub' fit] at sep
  exact sep.sub_left (FrameStack.belowA_sub (by decide : 24 ≤ stackUse) fit)

theorem bytesAt_frame {r : Region} {m m' : Mem} {changes : List Region}
    (frame : Frame changes m m') (sep : ∀ w ∈ changes, r.Disjoint w)
    (fit : r.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro j hj
  exact frame.bytes sep fit (List.mem_range.mp hj)

theorem KeyLive.after_control {p : KeyPublic} {original s t : State} {used keys scalars : Nat}
    {newUsed newKeys newScalars : Nat} {rs : List Reg}
    (h : KeyLive p original used keys scalars s) (rest : Rest rs s t)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs)
    (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem)
    (usedBound : newUsed ≤ p.randLen) (keysBound : newKeys ≤ 128) (scalarsBound : newScalars ≤ 128)
    (headers : Slots t.mem p.control (p.headers newUsed newKeys newScalars))
    (high : ∀ j < 3, t.mem.readW (off (State.addr p.control) (8 * j + 4)) 32 = 0) :
    KeyLive p original newUsed newKeys newScalars t := by
  refine ⟨h.input, usedBound, keysBound, scalarsBound, rest.rd.trans h.rd, rest.wr.trans h.wr,
    rest.sp.trans h.sp, (rest.gpr .r4 (kept .r4 (by decide))).trans h.pointer,
    fun r hr => (rest.gpr r (kept r (List.mem_cons_of_mem _ hr))).trans (h.kept r hr),
    ?_, ?_, ?_, headers, high⟩
  · apply h.saved.frame (lo := 0) (hi := 24) (by decide) frame
    simpa using h.input.saved_control
  · exact (bytesAt_frame frame (by simpa using h.input.random_control)
      (by change p.randLen ≤ 2 ^ 64; have := h.input.bounds.randomFits; omega)).trans h.random
  · exact (bytesAt_frame frame (by simpa using h.input.domain_control)
      (by change p.dlen ≤ 2 ^ 64; have := h.input.bounds.domainFit; omega)).trans h.domain

theorem KeyLive.update {p : KeyPublic} {original s t : State} {used keys scalars : Nat}
    {newUsed newKeys newScalars : Nat} {rs : List Reg}
    (h : KeyLive p original used keys scalars s) (rest : Rest rs s t)
    (kept : ∀ r ∈ keptRegisters, r ∉ rs)
    (values : List (Nat × BitVec 32)) (bounds : ∀ e ∈ values, e.1 < 16)
    (mem : t.mem = writeLow s.mem p.control values)
    (usedBound : newUsed ≤ p.randLen) (keysBound : newKeys ≤ 128) (scalarsBound : newScalars ≤ 128)
    (headers : Slots t.mem p.control (p.headers newUsed newKeys newScalars)) :
    KeyLive p original newUsed newKeys newScalars t := by
  apply h.after_control rest kept (by rw [mem]; exact writeLow_frame _ _ _ bounds)
    usedBound keysBound scalarsBound headers
  intro j hj
  rw [mem, highWord_writeLow _ _ _ bounds j (by omega)]
  exact h.high j hj

end VG.Proof.Ffdh.Arm.KeySearch
