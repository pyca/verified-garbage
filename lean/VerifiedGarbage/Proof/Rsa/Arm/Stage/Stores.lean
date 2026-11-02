module

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Div
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Store
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint4
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Slots
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # The ARMv7 key stages: the factors written out (`stores_vp`)

`Bo P σ s`: what the end of the body keeps of `σ`, memory but in the working
space, frame word 0 and the outputs `p` and `q`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa (b2n)

structure Bo (P : RP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame [P.rS, P.r0F, P.rP, P.rQ] σ.mem s.mem

theorem Bs.bo {P : RP} {σ s : State} (h : Bs P σ s) : Bo P σ s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame.mono (by simp)⟩

/-- A frame word but word 0. -/
theorem Bo.fwEq {P : RP} {σ s : State} (h : Bo P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88) :
    fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pre.sF.symm.sub_left (Offset.sub_base _ ho')
  · exact Offset.disjoint_base _ ho (by omega)
  · exact pre.pF.symm.sub_left (Offset.sub_base _ ho')
  · exact pre.qF.symm.sub_left (Offset.sub_base _ ho')

/-- `ldr t, [sp, #o]` of a frame word but word 0. -/
theorem Bo.ldrSp {P : RP} {σ s : State} (h : Bo P σ s) {o : Nat} (ho : 4 ≤ o) (ho' : o + 4 ≤ 88)
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

/-- Memory of the working space through a step that writes only `R`. -/
theorem w32_frame {P : RP} {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (hZ : P.Z ≤ 2 ^ 64) {d : Nat} (hd : d + 4 ≤ P.Z) : w32 m' (State.addr P.B) d = w32 m (State.addr P.B) d := by
  simp only [w32]
  rw [f.readW (r := P.rS) (Offset.contains_base _ hd (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) (by decide)]

theorem num_frame {P : RP} {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (sz : Sizes P) {j : Nat} (hj : j < nArr) : num m' P.B P.w j = num m P.B P.w j := by
  have fz := fitZ_w sz hj
  have hS : S P.w = 4 * (P.w + 2) := rfl
  exact val32_congr fun i hi => w32_frame f hR (Z_64 sz) (by omega)

section
variable {P : RP}

theorem Bo.of_upd {σ s t : State} (h : Bo P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : Bo P σ t :=
  ⟨h.pre, u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, u.mem ▸ h.frame⟩

end

end VG.Proof.Rsa.Arm.Recover
