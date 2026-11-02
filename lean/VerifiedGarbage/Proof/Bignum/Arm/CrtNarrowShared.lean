module
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedState

import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout

/-! # The narrow CRT workspace: its width, and the shared state around it

Each factor's exponentiation runs in the narrow workspace with
`max(2, ⌈len/8⌉)` limbs for the factor's public byte length. Work there
preserves the main and both full-width factor workspaces.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest)

/-- The limbs of a factor of `k` bytes in the narrow workspace. -/
def narrowWords (k : Nat) : Nat := max 2 ((k + 7) / 8)

theorem narrowWords_bounds {k n : Nat} (positive : 0 < k) (short : k < n) (hn : 2 ≤ Spec.Rsa.modulusWords n) :
    2 ≤ narrowWords k ∧ narrowWords k ≤ Spec.Rsa.modulusWords n ∧ k ≤ 8 * narrowWords k := by
  simp only [narrowWords, Spec.Rsa.modulusWords] at *
  omega

theorem CrtShared.narrow_member {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (_h : CrtShared g bs s) :
    (⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region) ∈
      crtRegions g.base (workspaceWords g.words) g.words := by
  simp [crtRegions]

/-- The factor's limbs fit the narrow workspace, which the full width sizes. -/
theorem CrtShared.narrow_fits {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    2 ≤ narrowWords (g.sourceLength j.succ) ∧ narrowWords (g.sourceLength j.succ) ≤ g.words ∧
      g.sourceLength j.succ ≤ 8 * narrowWords (g.sourceLength j.succ) ∧ 0 < g.sourceLength j.succ ∧
      g.sourceLength j.succ ≤ 1024 ∧
      arrAt (narrowWords (g.sourceLength j.succ)) 8 ≤ 8 * workspaceWords g.words := by
  have valid := crt_width_valid h.buffers.lengthValid
  have bounds : 0 < g.sourceLength j.succ ∧ g.sourceLength j.succ < g.length := by
    rcases prime with rfl | rfl
    · exact ⟨h.buffers.pPositive, h.buffers.pShort⟩
    · exact ⟨h.buffers.qPositive, h.buffers.qShort⟩
  obtain ⟨two, le, fit⟩ := narrowWords_bounds bounds.1 bounds.2 valid.1
  refine ⟨two, le, fit, bounds.1, by have := h.buffers.lengthValid.2; omega, ?_⟩
  have arrays := h.buffers.context.arraysFit
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at arrays ⊢
  change _ ≤ g.words at le
  have := Nat.mul_le_mul_left 8 (Nat.add_le_add_right le 2)
  omega

theorem CrtShared.after_narrow {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtShared g bs t := by
  have mainEq := h.workspace_eq_after h.buffers.context.main (by simp [crtRegions]) h.buffers.context.sepMN frame
  have pEq := h.workspace_eq_after h.buffers.context.p (by simp [crtRegions]) h.buffers.context.sepPN frame
  have qEq := h.workspace_eq_after h.buffers.context.q (by simp [crtRegions]) h.buffers.context.sepQN frame
  exact h.after_frame (crt_workspace_frame h.buffers.workspace h.buffers.storageFits h.narrow_member frame) rest
    (h.main.congr mainEq) (h.p.congr pEq) (h.q.congr qEq) (mainEq.number h.buffers.context.arraysFit (by decide))

theorem CrtShared.of_mem {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtShared g bs s) (mem : t.mem = s.mem) (rest : Rest rs s t) : CrtShared g bs t :=
  h.after_external (regions := []) (by rw [mem]; exact Frame.refl _ _) rest (by simp) (by simp)

/-- Saving a workspace of any width in slot 0 keeps the shared state and selects it. -/
theorem crt_selectedWidth_ready {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {v : Nat}
    (h : CrtShared g bs s) (ws : Workspace s child (8 * workspaceWords g.words))
    (layout : CrtLayoutState child (workspaceWords g.words) v s.mem)
    (member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words)
    (ptr : t.gpr .r0 = child) (mem : t.mem = s.mem.writeW (State.addr s.sp) child)
    (frame : Frame [⟨State.addr s.sp, 4⟩] s.mem t.mem) {rs : List Reg} (rest : Rest rs s t) :
    CrtShared g bs t ∧ LayoutFrameReady child (workspaceWords g.words) v t := by
  have sep : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr s.sp, 4⟩ :=
    h.stack.separate.symm.sub_right (Region.sub_prefix (by decide))
  have shared := h.after_external frame rest (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; simp [crtLiveMutable])
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)
  have childSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member
  have eq : WorkspaceEq (State.addr child) (8 * workspaceWords g.words) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep.sub_left childSub)
  have childLayout := layout.congr eq
  refine ⟨shared, ⟨⟨ws.congr rest.wr, childLayout.layout, childLayout.width, ptr⟩, ?_, ?_, ?_⟩⟩
  · simpa only [off, BitVec.add_zero] using shared.stack.read (d := 0) (by decide)
  · rw [rest.sp]; exact sep.symm.sub_right childSub
  · rw [rest.sp, mem, Mem.readW_writeW_self32]

/-- A full-width factor workspace and its link slot in the main header. -/
def CrtChild (g : CrtGeometry) (child : BitVec 32) (slot : Nat) : Prop :=
  (child = crtP g.base g.words ∧ slot = 224) ∨ (child = crtQ g.base g.words ∧ slot = 228)

theorem CrtShared.child {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtShared g bs s) (kind : CrtChild g child slot) :
    (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words ∧
    Workspace s child (8 * workspaceWords g.words) ∧
    CrtLayoutState child (workspaceWords g.words) g.words s.mem ∧
    Region.Disjoint ⟨State.addr child, 8 * workspaceWords g.words⟩
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ ∧
    slot + 4 ≤ 8 * workspaceWords g.words ∧ slot < 4096 ∧
    s.mem.readW (off (State.addr g.base) slot) 32 = child := by
  have size := h.buffers.context.size
  rcases kind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by simp [crtRegions], h.buffers.context.p, h.p, h.buffers.context.sepPN, by omega, by decide, h.main.p⟩
  · exact ⟨by simp [crtRegions], h.buffers.context.q, h.q, h.buffers.context.sepQN, by omega, by decide, h.main.q⟩

/-- A workspace of the CRT storage is unchanged by writes to other regions of it and the stack. -/
theorem CrtShared.eq_of_frame {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {base : BitVec 32}
    {regions : List Region} {m m' : Mem} (h : CrtShared g bs s)
    (ws : Workspace s base (8 * workspaceWords g.words))
    (member : (⟨State.addr base, 8 * workspaceWords g.words⟩ : Region) ∈
      crtRegions g.base (workspaceWords g.words) g.words)
    (frame : Frame (⟨State.addr s.sp, 4⟩ :: regions) m m')
    (sep : ∀ r ∈ regions, (⟨State.addr base, 8 * workspaceWords g.words⟩ : Region).Disjoint r) :
    WorkspaceEq (State.addr base) (8 * workspaceWords g.words) m m' := by
  apply WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact (h.stack.separate.symm.sub_right (Region.sub_prefix (by decide))).sub_left
      (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member)
  · exact sep r hr

end VG.Proof.Bignum.Arm
