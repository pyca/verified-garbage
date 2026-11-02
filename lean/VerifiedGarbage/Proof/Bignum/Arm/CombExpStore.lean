module

import VerifiedGarbage.Proof.Bignum.Arm.CombExpKernel
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! Store the gathered secret digit without changing the public comb controls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem saveDigit_ok {base source table : BitVec 32} {len w bytes N M g E i : Nat}
    {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (s : State)
    (h : Power base len w M g E s) (hp : P s) (controls : Controls base source table bytes N s)
    (counter : Counter base i s) :
    WP isa (.block [.str .r11 .r0 196]) s fun t =>
      Power base len w M g E t ∧ P t ∧ Controls base source table bytes N t ∧ Counter base i t ∧
      t.mem.readW (off (State.addr base) 196) 32=s.gpr .r11 ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 256≤8*len := by
    have fits := h.ready.width ▸ h.ready.layout.2.2.1
    simp only [Proof.Rsa.Mont.arrAt,Proof.Rsa.Mont.hdrBytes] at fits
    omega
  refine wp_str (a:=off (State.addr base) 196) (by decide)
    (by rw [h.ready.ptr]; exact addr_add (by have := h.ready.workspace.nowrap; omega))
    (h.ready.workspace.write (by omega)) fun t update => WP.block_nil ?_
  have rest : Rest roundClobbers s t := (update.rest []).mono (by decide)
  obtain ⟨powerT,frame⟩ := h.after_header (d:=196) (by decide) (by decide) update.mem (update.rest [])
    ((update.rest []).gpr .r0 (by decide) |>.trans h.ready.ptr)
  have outside := writeW32_outside s.mem (State.addr base) (d:=196) (s.gpr .r11) (by decide)
  rw [←update.mem] at outside
  have controlsT : Controls base source table bytes N t := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact (outside_read32 outside (d:=128) (by decide) (by decide)).trans controls.sourcePtr
    · exact (outside_read32 outside (d:=132) (by decide) (by decide)).trans controls.byteCount
    · exact (outside_read32 outside (d:=136) (by decide) (by decide)).trans controls.bitCount
    · exact (outside_read32 outside (d:=204) (by decide) (by decide)).trans controls.spacing
    · exact (outside_read32 outside (d:=232) (by decide) (by decide)).trans controls.tablePtr
  refine ⟨powerT,A.stable frame rest hp,controlsT,?_,?_,frame.mono (by simpa using A.workspace),rest⟩
  · exact (outside_read32 outside (d:=192) (by decide) (by decide)).trans counter
  · rw [update.mem,Mem.readW_writeW_self32]

end VG.Proof.Bignum.Arm.CombExp
