module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
public import VerifiedGarbage.Proof.Framework.Arm.Inline

/-! # Derive the three CRT subworkspaces from the caller's scratch region

The expanded permission list names subregions already covered by scratch;
it grants no additional memory access and does not change machine state.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

def crtExpanded (s : State) (base : BitVec 32) (w : Nat) : State :=
  s.withRegions s.rd (crtRegions base (workspaceWords w) w ++ s.wr)

theorem crt_storage_addresses {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) :
    State.addr (crtP base w) = State.addr base + BitVec.ofNat 64 (pOffset w) ∧
    State.addr (crtQ base w) = State.addr base + BitVec.ofNat 64 (qOffset w) ∧
    (crtP base w).toNat + stride w ≤ 2 ^ 32 ∧ (crtQ base w).toNat + stride w ≤ 2 ^ 32 := by
  have nowrap := ws.nowrap
  have p : pOffset w + stride w ≤ size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords, pOffset] at *
    omega
  have q : qOffset w + stride w ≤ size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords, qOffset] at *
    omega
  have positive : 0 < stride w := by simp only [stride, workspaceWords]; omega
  have pnat : (crtP base w).toNat = base.toNat + pOffset w := by
    simp only [crtP, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : pOffset w < 2 ^ 32), Nat.mod_eq_of_lt (by omega : base.toNat + pOffset w < 2 ^ 32)]
  have qnat : (crtQ base w).toNat = base.toNat + qOffset w := by
    simp only [crtQ, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : qOffset w < 2 ^ 32), Nat.mod_eq_of_lt (by omega : base.toNat + qOffset w < 2 ^ 32)]
  exact ⟨addr_add (by omega), addr_add (by omega), by rw [pnat]; omega, by rw [qnat]; omega⟩

theorem crt_narrow_address {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) :
    State.addr (crtN base w) = State.addr base + BitVec.ofNat 64 (narrowOffset w) ∧
    (crtN base w).toNat + stride w ≤ 2 ^ 32 := by
  have nowrap := ws.nowrap
  have n : narrowOffset w + stride w ≤ size := fit
  have positive : 0 < stride w := by simp only [stride, workspaceWords]; omega
  have nnat : (crtN base w).toNat = base.toNat + narrowOffset w := by
    simp only [crtN, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : narrowOffset w < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + narrowOffset w < 2 ^ 32)]
  exact ⟨addr_add (by omega), by rw [nnat]; omega⟩

theorem crt_regions_covered {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) :
    Covers (crtRegions base (workspaceWords w) w) s.wr := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses ws fit
  obtain ⟨naddr, _⟩ := crt_narrow_address ws fit
  apply Covers.of_sub
  intro r hr
  simp only [crtRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨State.addr base, size⟩, ws.writable, 0, by simp, ?_⟩
    change 0 + 8 * workspaceWords w ≤ size
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords, stride] at fit
    omega
  · refine ⟨⟨State.addr base, size⟩, ws.writable, pOffset w, paddr, ?_⟩
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords, pOffset, stride] at *
    omega
  · refine ⟨⟨State.addr base, size⟩, ws.writable, qOffset w, qaddr, ?_⟩
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords, qOffset, stride] at *
    omega
  · refine ⟨⟨State.addr base, size⟩, ws.writable, narrowOffset w, naddr, ?_⟩
    exact fit

theorem crt_region_sub_workspace {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) {r : Region}
    (member : r ∈ crtRegions base (workspaceWords w) w) :
    r.Sub ⟨State.addr base, size⟩ := by
  obtain ⟨paddr, qaddr, _, _⟩ := crt_storage_addresses ws fit
  obtain ⟨naddr, _⟩ := crt_narrow_address ws fit
  have small : 3 * stride w ≤ size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords] at fit
    omega
  simp only [crtRegions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Region.sub_prefix (by change stride w ≤ size; omega)
  · rw [paddr]
    exact Offset.sub_base _ (by change stride w + stride w ≤ size; omega)
  · rw [qaddr]
    exact Offset.sub_base _ (by change 2 * stride w + stride w ≤ size; omega)
  · rw [naddr]
    exact Offset.sub_base _ (by change narrowOffset w + stride w ≤ size; exact fit)

theorem crt_expanded_context {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) :
    CrtSetupContext base (workspaceWords w) w (crtExpanded s base w) := by
  obtain ⟨paddr, qaddr, pfit, qfit⟩ := crt_storage_addresses ws fit
  obtain ⟨naddr, nfit⟩ := crt_narrow_address ws fit
  have nowrap := ws.nowrap
  have small : 3 * stride w ≤ size := by
    simp only [totalBytes, narrowOffset, modulusOffset, compareOffset, productOffset, productBytes, productWords] at fit
    omega
  have after : 3 * stride w ≤ narrowOffset w := by
    simp only [narrowOffset, modulusOffset, compareOffset, productOffset]; omega
  have nend : narrowOffset w + stride w ≤ 2 ^ 64 := by
    have : narrowOffset w + stride w ≤ size := fit
    omega
  refine ⟨⟨by change base.toNat + stride w ≤ 2 ^ 32; omega, by simp [crtExpanded, State.withRegions, crtRegions]⟩,
    ⟨pfit, by simp [crtExpanded, State.withRegions, crtRegions]⟩,
    ⟨qfit, by simp [crtExpanded, State.withRegions, crtRegions]⟩,
    ⟨nfit, by simp [crtExpanded, State.withRegions, crtRegions]⟩, hw, hw', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact crt_workspace_end w
  · rw [paddr]
    exact Offset.base_disjoint _ (by simp [pOffset, stride]) (by change stride w + stride w ≤ 2 ^ 64; omega)
  · rw [qaddr]
    exact Offset.base_disjoint _ (by change stride w ≤ 2 * stride w; omega) (by change 2 * stride w + stride w ≤ 2 ^ 64; omega)
  · rw [paddr, qaddr]
    exact Offset.disjoint _ (Or.inl (by change stride w + stride w ≤ 2 * stride w; omega))
      (by change stride w + stride w ≤ 2 ^ 64; omega) (by change 2 * stride w + stride w ≤ 2 ^ 64; omega)
  · rw [naddr]
    exact Offset.base_disjoint _ (by change stride w ≤ narrowOffset w; omega) nend
  · rw [paddr, naddr]
    exact Offset.disjoint _ (Or.inl (by change stride w + stride w ≤ narrowOffset w; omega))
      (by change stride w + stride w ≤ 2 ^ 64; omega) nend
  · rw [qaddr, naddr]
    exact Offset.disjoint _ (Or.inl (by change 2 * stride w + stride w ≤ narrowOffset w; omega))
      (by change 2 * stride w + stride w ≤ 2 ^ 64; omega) nend

theorem crt_expanded_covers {s : State} {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size) :
    Covers (crtExpanded s base w).wr s.wr ∧
      Covers ((crtExpanded s base w).rd ++ (crtExpanded s base w).wr) (s.rd ++ s.wr) := by
  have write := (crt_regions_covered ws fit).append_left (Covers.refl s.wr)
  exact ⟨write, (Covers.refl s.rd).append write⟩

end VG.Proof.Bignum.Arm
