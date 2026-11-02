module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Factor validation preserves all three RSA workspace layouts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

def crtValidationWrites (w : Nat) : List (Nat × Nat) :=
  [(128, 20), (productOffset w, 4 * (4 * w + 2)),
    (modulusOffset w, 4 * (4 * w + 2)), (compareOffset w, 4 * (4 * w + 2))]

theorem WorkspaceEq.of_outs_offset {base child : Addr} {d n : Nat} {ranges : List (Nat × Nat)} {m m' : Mem}
    (address : child = base + BitVec.ofNat 64 d) (fit : d + n < 2 ^ 64)
    (sep : ∀ r ∈ ranges, d + n ≤ r.1 ∨ r.1 + r.2 ≤ d)
    (outside : Outs base ranges m m') : WorkspaceEq child n m m' := by
  refine ⟨fun k bytes hk => Mem.read_congr ?_⟩
  intro i hi
  apply outside
  intro r hr
  rw [address, show off (base + BitVec.ofNat 64 d) k =
    off base (d + k) by simp only [off, Offset.add_add], ofs_off base (by omega)]
  have := sep r hr
  omega

theorem CrtShared.validation_child_eq {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem) :
    WorkspaceEq (State.addr (crtP g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem ∧
    WorkspaceEq (State.addr (crtQ g.base g.words)) (8 * workspaceWords g.words) s.mem t.mem := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses h.buffers.workspace h.buffers.storageFits
  have size := h.buffers.storageFits
  have nowrap := h.buffers.workspace.nowrap
  have small := h.main.toCrtLayoutState.size
  have bounds : 3 * stride g.words ≤ g.size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset] at size
    omega
  constructor
  · apply WorkspaceEq.of_outs_offset paddr (by change stride g.words + stride g.words < _; omega) _ outside
    intro r hr
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [pOffset, productOffset, modulusOffset, compareOffset, stride] <;> omega
  · apply WorkspaceEq.of_outs_offset qaddr (by change 2 * stride g.words + stride g.words < _; omega) _ outside
    intro r hr
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [qOffset, productOffset, modulusOffset, compareOffset, stride] <;> omega

theorem CrtShared.validation_main {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem) :
    CrtMainState g.base (workspaceWords g.words) g.words t.mem ∧
    numAt t.mem (State.addr g.base) g.words 0 = numAt s.mem (State.addr g.base) g.words 0 := by
  have small := h.main.toCrtLayoutState.size
  have lower (r : Nat × Nat) (hr : r ∈ crtValidationWrites g.words) :
      r = (128, 20) ∨ 3 * stride g.words ≤ r.1 := by
    simp only [crtValidationWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · right; exact Nat.le_refl _
    · right; simp only [modulusOffset, compareOffset, productOffset]; omega
    · right; simp only [compareOffset, productOffset]; omega
  have head := control_buffers_header outside (by
    intro r hr
    rcases lower r hr with rfl | bound
    · exact Nat.le_refl _
    · change 128 ≤ r.1; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega)
  have word (d : Nat) (hd : d = 224 ∨ d = 228 ∨ d = 232 ∨ d = 236 ∨ d = 240) :
      t.mem.readW (off (State.addr g.base) d) 32 = s.mem.readW (off (State.addr g.base) d) 32 := by
    apply outs_readW outside
    · intro r hr
      rcases lower r hr with rfl | bound
      · simp only; omega
      · left; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega
    · omega
  refine ⟨⟨h.main.toCrtLayoutState.of_header_eq head,
    (word 224 (by simp)).trans h.main.p, (word 228 (by simp)).trans h.main.q,
    (word 232 (by simp)).trans h.main.product, (word 236 (by simp)).trans h.main.compare,
    (word 240 (by simp)).trans h.main.modulus⟩, ?_⟩
  have end0 := Nat.le_trans (array_end_le (w := g.words) (j := 0) (by decide)) h.buffers.context.arraysFit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    rcases lower r hr with rfl | bound
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    · left; change 3 * (8 * workspaceWords g.words) ≤ r.1 at bound; omega
  · have := h.buffers.context.main.nowrap; omega

theorem CrtShared.after_validation {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s) (outside : Outs (State.addr g.base) (crtValidationWrites g.words) s.mem t.mem)
    (frame : Frame [⟨State.addr g.base, g.size⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtShared g bs t := by
  obtain ⟨pEq, qEq⟩ := h.validation_child_eq outside
  obtain ⟨main, modulus⟩ := h.validation_main outside
  exact h.after_frame (frame.mono (by simp [crtLiveMutable])) rest main (h.p.congr pEq) (h.q.congr qEq) modulus

end VG.Proof.Bignum.Arm
