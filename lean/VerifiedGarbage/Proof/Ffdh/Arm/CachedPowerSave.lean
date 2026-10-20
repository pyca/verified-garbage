module

public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Save public context metadata without disturbing the arithmetic arrays. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest wp_str)

theorem save_ok (s : State) {base source table : BitVec 32} {len w bytes N : Nat}
    (h : ArithmeticReady base len w s)
    (sourcePtr : s.mem.readW (off (State.addr base) 128) 32=source)
    (byteCount : s.mem.readW (off (State.addr base) 132) 32=BitVec.ofNat 32 bytes)
    (bits : s.gpr .r1=BitVec.ofNat 32 N)
    (rows : s.gpr .r2=BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows N))
    (tablePtr : s.gpr .r4=table) :
    WP isa (.block VG.Impl.Ffdh.Arm.CachedPower.save) s fun t =>
      ArithmeticReady base len w t ∧ CombExp.Controls base source table bytes N t ∧
      (∀q<8,numAt t.mem (State.addr base) w q=numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base,8*len⟩] s.mem t.mem ∧ Rest [] s t := by
  have size : 256≤8*len := by
    have fits := h.width ▸ h.layout.2.2.1
    simp only [arrAt,Spec.Rsa.Mont.hdrBytes] at fits
    omega
  have addr (d : Nat) (hd : d≤252) : State.addr (s.gpr .r0+BitVec.ofNat 32 d)=off (State.addr base) d := by
    rw [h.ptr]; exact addr_add (by have := h.workspace.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.CachedPower.save
  refine wp_str (a:=off (State.addr base) 136) (by decide) (addr 136 (by decide))
    (h.workspace.write (by omega)) fun a one => ?_
  have restA : Rest [] s a := one.rest []
  obtain ⟨readyA,frameA,arraysA⟩ := h.after_header (d:=136) (by decide) (by decide) one.mem restA
    ((restA.gpr .r0 (by simp)).trans h.ptr)
  refine wp_str (a:=off (State.addr base) 204) (by decide)
    (by rw [restA.gpr .r0 (by simp)]; exact addr 204 (by decide))
    (by rw [restA.wr]; exact h.workspace.write (by omega)) fun b two => ?_
  have restB : Rest [] a b := two.rest []
  obtain ⟨readyB,frameB,arraysB⟩ := readyA.after_header (d:=204) (by decide) (by decide) two.mem restB
    ((restB.gpr .r0 (by simp)).trans readyA.ptr)
  have restAB := restA.trans restB
  refine wp_str (a:=off (State.addr base) 232) (by decide)
    (by rw [restAB.gpr .r0 (by simp)]; exact addr 232 (by decide))
    (by rw [restAB.wr]; exact h.workspace.write (by omega)) fun t three => WP.block_nil ?_
  have restT : Rest [] b t := three.rest []
  obtain ⟨readyT,frameT,arraysT⟩ := readyB.after_header (d:=232) (by decide) (by decide) three.mem restT
    ((restT.gpr .r0 (by simp)).trans readyB.ptr)
  have outsideA := writeW32_outside s.mem (State.addr base) (d:=136) (s.gpr .r1) (by decide)
  have outsideB := writeW32_outside a.mem (State.addr base) (d:=204) (a.gpr .r2) (by decide)
  have outsideT := writeW32_outside b.mem (State.addr base) (d:=232) (b.gpr .r4) (by decide)
  rw [←one.mem] at outsideA
  rw [←two.mem] at outsideB
  rw [←three.mem] at outsideT
  have early (d : Nat) (hd : d+4≤136) :
      t.mem.readW (off (State.addr base) d) 32=s.mem.readW (off (State.addr base) d) 32 := by
    rw [outside_read32 outsideT (by omega) (by omega),outside_read32 outsideB (by omega) (by omega),
      outside_read32 outsideA (by omega) (by omega)]
  refine ⟨readyT,⟨(early 128 (by decide)).trans sourcePtr,(early 132 (by decide)).trans byteCount,?_,?_,?_⟩,
    fun q hq=>(arraysT q hq).trans ((arraysB q hq).trans (arraysA q hq)),
    frameA.trans (frameB.trans frameT),restAB.trans restT⟩
  · rw [outside_read32 outsideT (d:=136) (by decide) (by decide),
      outside_read32 outsideB (d:=136) (by decide) (by decide),one.mem,Mem.readW_writeW_self32,bits]
  · rw [outside_read32 outsideT (d:=204) (by decide) (by decide),two.mem,Mem.readW_writeW_self32,
      restA.gpr .r2 (by simp),rows]
  · rw [three.mem,Mem.readW_writeW_self32,restAB.gpr .r4 (by simp),tablePtr]

end VG.Proof.Ffdh.Arm.CachedPower
