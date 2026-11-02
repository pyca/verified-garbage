module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2
import VerifiedGarbage.Proof.Rc2.PairMem

/-! Store both halves of the shared power-of-two metadata in the exponent
array's padding, preserving all bytes of its actual exponent. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.Rsa.Arm.Keys (arr S)

theorem exponentPowerStore_words {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) s fun t =>
      t.mem = (s.mem.writeW (off (State.addr base) (arrAt w 27 + 8 * w)) (s.gpr .r2)).writeW
        (off (State.addr base) (arrAt w 27 + 8 * w + 4)) (s.gpr .r3) ∧ Rest [.r0] s t := by
  let B := base + 96#32
  have fit := ready.arrayFit (j := 27) (by decide)
  have r7 : s.gpr .r7 = BitVec.ofNat 32 (S (2 * w + 2)) := ready.r7
  have r8 : s.gpr .r8 = B := ready.r8
  have r9 : s.gpr .r9 = BitVec.ofNat 32 (2 * w + 2) := ready.r9
  have ptrValue : BitVec.ofNat 32 27 * BitVec.ofNat 32 (S (2 * w + 2)) + B +
      BitVec.ofNat 32 VG.Impl.Rsa.Arm.Keys.hdr = B + BitVec.ofNat 32 (arr (2 * w + 2) 27) :=
    VG.Proof.Rsa.Arm.Keys.ptr_val B 27 (S (2 * w + 2))
  have shifted : BitVec.ofNat 32 (2 * w + 2) <<< 2 = BitVec.ofNat 32 (4 * (2 * w + 2)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 (2 * w + 2) * BitVec.ofNat 32 4 = _
    rw [BitVec.ofNat_mul_ofNat]
    congr 1
    omega_arith
  have pointer : B + BitVec.ofNat 32 (arr (2 * w + 2) 27) + BitVec.ofNat 32 (4 * (2 * w + 2)) - 8 =
      base + BitVec.ofNat 32 (arrAt w 27 + 8 * w) := by
    change base + 96#32 + BitVec.ofNat 32 (arr (2 * w + 2) 27) +
      BitVec.ofNat 32 (4 * (2 * w + 2)) - BitVec.ofNat 32 8 = _
    rw [VG.Proof.Rsa.Arm.Recover.add_ofNat_sub32 _ (by omega_arith), BitVec.add_assoc,
      ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    rw [← Nat.add_assoc, keyView_array]
    congr 1
    omega_arith
  have addr0 : State.addr (base + BitVec.ofNat 32 (arrAt w 27 + 8 * w)) =
      off (State.addr base) (arrAt w 27 + 8 * w) := VG.Arm.addr_add (by have := workspace.nowrap; omega_arith)
  have addr4 : State.addr (base + BitVec.ofNat 32 (arrAt w 27 + 8 * w) + 4#32) =
      off (State.addr base) (arrAt w 27 + 8 * w + 4) := by
    rw [Offset.add_add]
    exact VG.Arm.addr_add (by have := workspace.nowrap; omega_arith)
  have write0 := workspace.write (off := arrAt w 27 + 8 * w) (by omega_arith)
  have write4 := workspace.write (off := arrAt w 27 + 8 * w + 4) (by omega_arith)
  refine withRest_all [.r0] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore VG.Impl.Rsa.Arm.Keys.ptr
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, r7, r8, r9, ptrValue, shifted, pointer,
    addr0, addr4, write0, write4]

theorem exponentPowerStore_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      t.mem.readW (off (State.addr base) (arrAt w 27 + 8 * w)) 64 = (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) ∧
      numAt t.mem (State.addr base) w 27 = numAt s.mem (State.addr base) w 27 ∧
      VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [27] [] s.mem t.mem ∧ Rest [.r0] s t := by
  refine WP.mono (exponentPowerStore_words workspace ready) ?_
  rintro t ⟨mem, rest⟩
  have fit := ready.arrayFit (j := 27) (by decide)
  have nowrap := workspace.nowrap
  have written : t.mem = s.mem.writeW (off (State.addr base) (arrAt w 27 + 8 * w))
      (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) := by
    rw [VG.Proof.Rc2.Word32.write64_pair, Offset.add_add]
    exact mem
  have frame : Frame [⟨off (State.addr base) (arrAt w 27 + 8 * w), 8⟩] s.mem t.mem := by
    rw [written]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have number : numAt t.mem (State.addr base) w 27 = numAt s.mem (State.addr base) w 27 := by
    unfold numAt
    apply congrArg BitVec.toNat
    exact frame.read (r := ⟨off (State.addr base) (arrAt w 27), 8 * w⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r
          exact Offset.disjoint _ (.inl (Nat.le_refl _)) (by omega_arith) (by omega_arith)) (by omega_arith)
  have shiftFits := ready.baseShiftFits workspace
  have offNative : off (State.addr base) (arrAt w 27 + 8 * w) =
      off (State.addr (base + 96#32)) (arr (2 * w + 2) 27 + 8 * w) := by
    rw [VG.Arm.addr_add shiftFits]
    unfold off
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.add_assoc, keyView_array]
  have keep : VG.Proof.Rsa.Arm.Keys.Keep (base + 96#32) (2 * w + 2) [27] [] s.mem t.mem := by
    rw [written, offNative]
    exact VG.Proof.Rsa.Arm.Keys.Keep.of_arr (d := 8 * w)
      (writeW_outside _ _ _ (by have := ready.fit64 (j := 27) (by decide); simp only [S] at this; omega_arith))
      (by simp only [S]; omega_arith) (by simp)
  exact ⟨ready.rest rest (by decide) (by decide) (by decide),
    (data.after_key_keep workspace ready (by simp) (by simp) keep).1,
    by rw [written, Mem.readW_writeW_self64], number, keep, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
