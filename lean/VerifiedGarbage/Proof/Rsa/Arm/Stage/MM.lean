module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The ARMv7 key stages: Montgomery multiplication's stage

`MM P s`: Montgomery multiplication ready but for `r0`, and `n` in its
array 0. Steps of the key working space that write none of the key arrays
16–20 keep it (`MM.of_keep`). The frame's
words are those the body started with (`Bs.fw`), and loads of them
(`Bs.ldrSp`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-! ## The frame -/

/-- A frame word but word 0. -/
theorem Bs.fwEq {P : RP} {σ s : State} (h : Bs P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88) :
    fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ ho')
  · exact Offset.disjoint_base _ ho (by omega)

/-- `ldr t, [sp, #o]` of a frame word but word 0. -/
theorem Bs.ldrSp {P : RP} {σ s : State} (h : Bs P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88)
    (h4 : o % 4 = 0) {t : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  have ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega)
  refine wp_loadStack (by omega) ea ?_ fun s' u => k s' (by rw [← h.fwEq ho ho']; exact u)
  rw [h.rd, h.wr]
  rcases (by omega : o + 4 ≤ 56 ∨ 56 ≤ o) with c | c
  · exact ⟨⟨State.addr P.sp, 56⟩, List.mem_append_right _ (by rw [pre.wr]; simp),
      Offset.contains_base _ c (by omega)⟩
  · have read := CallLay.inRegions_sub pre.rdA (off := o - 56) (l := 4) (by omega) (by decide)
    rwa [show off (State.addr P.sp) 56 + BitVec.ofNat 64 (o - 56) = off (State.addr P.sp) o by
      simp only [off]; rw [Offset.add_add]; congr 2; omega] at read

end VG.Proof.Rsa.Arm.Recover
