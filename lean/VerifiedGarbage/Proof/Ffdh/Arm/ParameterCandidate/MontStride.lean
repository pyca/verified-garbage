module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The shared compact round's stride is a complete u64 header word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

def strideMemory (m : Mem) (base : BitVec 32) (w : Nat) : Mem :=
  (m.writeW (off (State.addr base) 224) (BitVec.ofNat 32 (8 * (w + 2)))).writeW
    (off (State.addr base) 228) (0#32)

theorem keyStride_words {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (ptr : s.gpr .r0 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride) s fun t =>
      t.mem = strideMemory s.mem base w ∧ Rest [.r1] s t := by
  have fit := ready.arrayFit (j := 0) (by decide)
  have write224 : InRegions s.wr (State.addr (base + 224#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega)]
    exact workspace.write (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      Nat.zero_mul, Nat.add_zero] at fit; omega)
  have write228 : InRegions s.wr (State.addr (base + 228#32)) 4 := by
    rw [VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega)]
    exact workspace.write (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
      Nat.zero_mul, Nat.add_zero] at fit; omega)
  refine withRest_all [.r1] ?_ (by rfl) (by rfl)
  have stride := ready.r7
  rw [keyView_stride] at stride
  have addr224 : State.addr (base + 224#32) = off (State.addr base) 224 :=
    VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega)
  have addr228 : State.addr (base + 228#32) = off (State.addr base) 228 :=
    VG.Arm.addr_add (by have := workspace.nowrap; simp only [Proof.Rsa.Mont.arrAt,
      Proof.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] at fit; omega)
  change s.gpr .r7 = _ at stride
  rw [addr224] at write224
  rw [addr228] at write228
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride strideMemory
  ffrun [ptr, stride, write224, write228, addr224, addr228,
    show (0 : BitVec 32) = 0#32 from rfl]

theorem strideMemory_write64 (m : Mem) (base : BitVec 32) {w : Nat} (bound : w ≤ 1024) :
    strideMemory m base w = m.writeW (off (State.addr base) 224) (BitVec.ofNat 64 (8 * (w + 2))) := by
  unfold strideMemory
  have offset : off (State.addr base) 228 = off (State.addr base) 224 + BitVec.ofNat 64 4 := by
    rw [Offset.add_add]
  rw [offset, ← VG.Proof.Rc2.Word32.write64_pair]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (by omega : 8 * (w + 2) < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 8 * (w + 2) < 2 ^ 64)]

theorem strideMemory_frame (m : Mem) (base : BitVec 32) {w : Nat} (bound : w ≤ 1024) :
    Frame [⟨off (State.addr base) 224, 8⟩] m (strideMemory m base w) := by
  rw [strideMemory_write64 m base bound]
  exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

theorem keyStride_ok {s : State} {base : BitVec 32} {capacity w : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (ptr : s.gpr .r0 = base) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.keyStride) s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      t.mem.readW (off (State.addr base) 224) 64 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      (∀ j, j < 35 → numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j) ∧
      Frame [⟨off (State.addr base) 224, 8⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  have wBound : w ≤ 1024 := by have := ready.wle; omega
  refine WP.mono (keyStride_words workspace ready ptr) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨off (State.addr base) 224, 8⟩] s.mem t.mem := by
    rw [mem]
    exact strideMemory_frame s.mem base wBound
  have values (j : Nat) (jBound : j < 35) : numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j := by
    unfold numAt
    apply congrArg BitVec.toNat
    refine frame.read (r := ⟨off (State.addr base) (Proof.Rsa.Mont.arrAt w j), 8 * w⟩)
      (Region.contains_self _ _) ?_ (by omega)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    have scale := Nat.mul_le_mul_right (8 * (w + 2)) (show j ≤ 35 by omega)
    apply Offset.disjoint _ (.inr ?_) (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega) (by decide)
    simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
    omega
  have dataT := data.after_value frame (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact (Offset.disjoint_base _ (by decide : 128 ≤ 224) (by decide : 224 + 8 ≤ 2 ^ 64)).symm) (values 0 (by decide))
  refine ⟨ready.rest rest (by decide) (by decide) (by decide), dataT.1, ?_, values, frame, rest⟩
  rw [mem, strideMemory_write64 s.mem base wBound, Mem.readW_writeW_self64]

end VG.Proof.Ffdh.Arm.ParameterCandidate
