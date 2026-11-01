module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Translate RSA key-array frames back to the shared Montgomery arrays. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt)

def keyArrayRegions (base : BitVec 32) (w : Nat) (js : List Nat) : List Region :=
  js.map fun j => ⟨off (State.addr base) (arrAt w j), 8 * (w + 2)⟩

theorem KeyReady.arrayFit {s : State} {base : BitVec 32} {capacity w j : Nat}
    (h : KeyReady base capacity w s) (bound : j < 30) :
    arrAt w j + 8 * (w + 2) ≤ 8 * capacity := by
  have native := h.arr_fit bound
  rw [keyView_stride] at native
  rw [← keyView_array w j]
  have stridePositive : 16 ≤ 8 * (w + 2) := by omega
  omega

theorem KeyReady.arraysFit {s : State} {base : BitVec 32} {capacity w j : Nat}
    (h : KeyReady base capacity w s) (bound : j < 30) : arrAt w (j + 1) ≤ 8 * capacity := by
  have fit := h.arrayFit bound
  have next : arrAt w (j + 1) = arrAt w j + 8 * (w + 2) := by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  rw [next]
  exact fit

theorem KeyReady.baseShiftFits {s : State} {base : BitVec 32} {capacity w : Nat}
    (h : KeyReady base capacity w s) (workspace : Workspace s base (8 * capacity)) :
    base.toNat + 96 < 2 ^ 32 := by
  have fit := h.arrayFit (j := 0) (by decide)
  have nowrap := workspace.nowrap
  simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit
  omega

theorem key_keep_number {s : State} {base : BitVec 32} {capacity w j : Nat}
    {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bound : j < 30) (unchanged : ∀ a ∈ js, a ≠ j)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    numAt m' (State.addr base) w j = numAt s.mem (State.addr base) w j := by
  have value := keep.num unchanged (by simp) (ready.fit64 bound)
  have fits := ready.baseShiftFits workspace
  rw [← keyView_number_mod m' base w j fits, ← keyView_number_mod s.mem base w j fits, value]

theorem key_keep_frame {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat} {m m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] m m') :
    Frame (keyArrayRegions base w js) m m' := by
  have zeroFit := h.arrayFit (j := 0) (by decide)
  have shiftFits : base.toNat + 96 < 2 ^ 32 := by
    have := workspace.nowrap
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at zeroFit
    omega
  change Outs (State.addr (base + 96#32)) (VG.Proof.Rsa.KeyWorkspace.ranges (2 * w + 2) js []) m m' at keep
  have native := VG.Proof.Bignum.outs_frame keep (by
    intro r hr
    simp only [VG.Proof.Rsa.KeyWorkspace.ranges, List.map_nil, List.append_nil, List.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact h.fit64 (bounds j hj))
  have address (j : Nat) : off (State.addr (base + 96#32)) (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j) =
      off (State.addr base) (arrAt w j) := by
    unfold off
    rw [VG.Arm.addr_add shiftFits, BitVec.add_assoc, ← BitVec.ofNat_add, keyView_array]
  simp only [VG.Proof.Rsa.KeyWorkspace.ranges, List.map_nil, List.append_nil, List.map_map] at native
  have equal : (js.map fun j => (⟨off (State.addr (base + 96#32))
      (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j), VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)⟩ : Region)) =
      keyArrayRegions base w js := by
    unfold keyArrayRegions
    apply List.map_congr_left
    intro j _
    rw [address, keyView_stride]
  change Frame (js.map fun j => ⟨off (State.addr (base + 96#32))
    (VG.Proof.Rsa.Arm.Keys.arr (2 * w + 2) j), VG.Proof.Rsa.Arm.Keys.S (2 * w + 2)⟩) m m' at native
  rw [equal] at native
  exact native

theorem keyArrayRegions.header {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) :
    ∀ r ∈ keyArrayRegions base w js, (⟨State.addr base, 128⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have fit := h.arrayFit (bounds j hj)
  have nowrap := workspace.nowrap
  apply Region.Disjoint.symm
  apply Offset.disjoint_base
  · simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega
  · omega

theorem key_keep_workspace {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    Frame [⟨State.addr base, 8 * capacity⟩] s.mem m' := by
  refine (key_keep_frame workspace ready bounds keep).sub ?_
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact ⟨_, by simp, Offset.sub_base _ (ready.arrayFit (bounds j hj))⟩

theorem key_keep_header {s : State} {base : BitVec 32} {capacity w d : Nat}
    {js : List Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) (fit : d + 8 ≤ 256)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    m'.readW (off (State.addr base) d) 64 = s.mem.readW (off (State.addr base) d) 64 := by
  refine (key_keep_frame workspace ready bounds keep).readW (r := ⟨State.addr base, 256⟩)
    (Offset.contains_base _ fit (by omega)) ?_ (by decide)
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have arrayFit := ready.arrayFit (bounds j hj)
  have nowrap := workspace.nowrap
  apply Region.Disjoint.symm
  apply Offset.disjoint_base
  · simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega
  · omega

theorem keyArrayRegions.modulus {s : State} {base : BitVec 32} {capacity w : Nat} {js : List Nat}
    (workspace : Workspace s base (8 * capacity)) (h : KeyReady base capacity w s)
    (bounds : ∀ j ∈ js, j < 30) (nonzero : ∀ j ∈ js, j ≠ 0) :
    ∀ r ∈ keyArrayRegions base w js,
      (⟨off (State.addr base) (arrAt w 0), 8 * w⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  have fit := h.arrayFit (bounds j hj)
  have fit0 := h.arrayFit (j := 0) (by decide)
  have nowrap := workspace.nowrap
  refine Offset.disjoint _ (.inl ?_) (by omega) (by omega)
  have positive : 1 ≤ j := by have := nonzero j hj; omega
  have scale := Nat.mul_le_mul_right (8 * (w + 2)) positive
  simp only [Nat.one_mul] at scale
  simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero]
  omega

theorem MontData.after_key_keep {s : State} {base : BitVec 32} {capacity w : Nat}
    {js : List Nat} {m' : Mem}
    (data : MontData base capacity w s.mem) (workspace : Workspace s base (8 * capacity))
    (ready : KeyReady base capacity w s) (bounds : ∀ j ∈ js, j < 30)
    (nonzero : ∀ j ∈ js, j ≠ 0)
    (keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) js [] s.mem m') :
    MontData base capacity w m' ∧ numAt m' (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 :=
  data.after_frame (key_keep_frame workspace ready bounds keep)
    (keyArrayRegions.header workspace ready bounds) (keyArrayRegions.modulus workspace ready bounds nonzero)

end VG.Proof.Ffdh.Arm.ParameterCandidate
