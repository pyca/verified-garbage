module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Stack-local writes preserve the exact same scratch bytes through the
native RSA and shared Montgomery views. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt wordAt)

theorem key_number_of_workspaceEq {s : State} {base : BitVec 32} {capacity w j : Nat} {m' : Mem}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (equal : WorkspaceEq (State.addr base) (8 * capacity) s.mem m') (bound : j < 30) :
    VG.Proof.Rsa.Arm.Keys.num m' (base + 96#32) (2 * w + 2) j =
      VG.Proof.Rsa.Arm.Keys.num s.mem (base + 96#32) (2 * w + 2) j := by
  unfold VG.Proof.Rsa.Arm.Keys.num
  rw [VG.Arm.addr_add (ready.baseShiftFits workspace), VG.Proof.Rsa.Arm.CrtValues.val32_off,
    VG.Proof.Rsa.Arm.CrtValues.val32_off, keyView_array]
  apply val32_congr
  intro i hi
  apply congrArg BitVec.toNat
  exact equal.word (bits := 32) (by have := ready.arrayFit bound; omega)

theorem MontData.after_workspaceEq {base : BitVec 32} {capacity w : Nat} {m m' : Mem}
    (data : MontData base capacity w m) (equal : WorkspaceEq (State.addr base) (8 * capacity) m m') :
    MontData base capacity w m' := by
  have fits : arrAt w 8 ≤ 8 * capacity := data.width ▸ data.layout.2.2.1
  have headerFits : 128 ≤ 8 * capacity := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  have num0 := equal.number fits (j := 0) (by decide)
  refine ⟨equal.layout data.layout, (equal.width (by omega)).trans data.width, ?_, ?_⟩
  · unfold word wordAt
    rw [equal.word (bits := 64) (by have := array_end_le (w := w) (j := 0) (k := 8) (by decide); omega),
      equal.word (bits := 64) (by change 64 ≤ 8 * capacity; omega)]
    exact data.inverse
  · rw [num0]
    exact data.modulus

theorem stackWrite_workspaceEq {s : State} {base : BitVec 32} {capacity d : Nat}
    (workspace : Workspace s base (8 * capacity)) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (fit : d + 4 ≤ 72) (value : BitVec 32) :
    WorkspaceEq (State.addr base) (8 * capacity) s.mem
      (s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) value) := by
  have frame : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩] s.mem
      (s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 d)) value) :=
    (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  refine WorkspaceEq.of_frame (by have := workspace.nowrap; omega) frame ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact (separate.sub_left (Offset.sub_base _ fit)).symm

end VG.Proof.Ffdh.Arm.ParameterCandidate
