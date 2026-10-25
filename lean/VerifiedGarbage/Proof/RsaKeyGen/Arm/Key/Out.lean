module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Base
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Arm.Contract

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mul
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front3

/-! # An RSA key on ARMv7: the outputs

The seven outputs by index (`oPtr`, `oLen`, `oR`; their frame words `oFw`,
`oFl`, and their arrays `oArr`). `Bo P σ s`: what the stages that write
outputs keep of `σ`. The outputs written from their arrays under the mask
(`stores_vp`), or zeros (`zeros_vp`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

def oPtr (P : KP) : Nat → BitVec 32
  | 0 => P.nP | 1 => P.dP | 2 => P.pP | 3 => P.qP | 4 => P.dpP | 5 => P.dqP | _ => P.qiP
def oLen (P : KP) (i : Nat) : Nat := if i < 2 then 2 * P.K else P.K
abbrev oR (P : KP) (i : Nat) : Region := ⟨State.addr (oPtr P i), oLen P i⟩
def oFw : Nat → Nat
  | 0 => aoN | 1 => aoD | 2 => aoP | 3 => aoQ | 4 => aoDp | 5 => aoDq | _ => aoQi
def oFl (i : Nat) : Nat := if i < 2 then aoNl else aoPl
def oArr : Nat → Nat
  | 0 => aN | 1 => aD | 2 => aP | 3 => aQ | 4 => aDP | 5 => aDQ | _ => aQi

/-- What the stages writing outputs keep of `σ`. -/
structure Bo (P : KP) (σ s : State) : Prop where
  pre : In P σ
  sp : s.sp = σ.sp
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  frame : Frame (P.rS :: P.outs) σ.mem s.mem

section
variable {P : KP} {σ s t : State}

theorem oR_eq (i : Nat) (hi : i < 7) :
    oR P i = [P.rN, P.rD, P.rP, P.rQ, P.rDp, P.rDq, P.rQi][i]'(by simpa using hi) := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem oR_mem (i : Nat) (hi : i < 7) : oR P i ∈ P.outs := by
  rw [oR_eq i hi]; exact List.getElem_mem _

theorem In.fwO (pre : In P σ) (i : Nat) (hi : i < 7) : fw σ.mem P (oFw i) = oPtr P i := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pre.wN
  · exact pre.wD
  · exact pre.aP
  · exact pre.aQ
  · exact pre.aDp
  · exact pre.aDq
  · exact pre.aQi

theorem In.flO (pre : In P σ) (i : Nat) : fw σ.mem P (oFl i) = BitVec.ofNat 32 (oLen P i) := by
  unfold oFl oLen
  split
  · exact pre.wNl
  · exact pre.aPl

theorem In.oFit (pre : In P σ) (i : Nat) (hi : i < 7) : (oPtr P i).toNat + oLen P i ≤ 2 ^ 32 := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pre.fN
  · exact pre.fD
  · exact pre.fP
  · exact pre.fQ
  · exact pre.fDp
  · exact pre.fDq
  · exact pre.fQi

theorem In.oS (pre : In P σ) (i : Nat) (hi : i < 7) : (oR P i).Disjoint P.rS := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pre.sN.symm
  · exact pre.sD.symm
  · exact pre.sP.symm
  · exact pre.sQ.symm
  · exact pre.sDp.symm
  · exact pre.sDq.symm
  · exact pre.sQi.symm

theorem In.oF (pre : In P σ) (i : Nat) (hi : i < 7) : (oR P i).Disjoint P.rF := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pre.nF
  · exact pre.dF
  · exact pre.pF
  · exact pre.qF
  · exact pre.dpF
  · exact pre.dqF
  · exact pre.qiF

theorem In.oO (pre : In P σ) (i k : Nat) (hi : i < 7) (hk : k < 7) (hik : i ≠ k) :
    (oR P i).Disjoint (oR P k) := by
  have l : ∀ a b : Nat, a < b → b < 7 → (oR P a).Disjoint (oR P b) := by
    intro a b hab hb
    rcases (by omega_arith : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · obtain rfl : a = 0 := by omega_arith
      exact pre.nD
    · rcases (by omega_arith : a = 0 ∨ a = 1) with rfl | rfl
      · exact pre.nP
      · exact pre.dP
    · rcases (by omega_arith : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl
      · exact pre.nQ
      · exact pre.dQ
      · exact pre.pQ
    · rcases (by omega_arith : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl
      · exact pre.nDp
      · exact pre.dDp
      · exact pre.pDp
      · exact pre.qDp
    · rcases (by omega_arith : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) with rfl | rfl | rfl | rfl | rfl
      · exact pre.nDq
      · exact pre.dDq
      · exact pre.pDq
      · exact pre.qDq
      · exact pre.dpDq
    · rcases (by omega_arith : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5) with rfl | rfl | rfl | rfl | rfl | rfl
      · exact pre.nQi
      · exact pre.dQi
      · exact pre.pQi
      · exact pre.qQi
      · exact pre.dpQi
      · exact pre.dqQi
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · exact l i k h hk
  · exact (l k i h hi).symm

theorem In.oW (pre : In P σ) (i : Nat) (hi : i < 7) : oR P i ∈ σ.wr := by
  rw [pre.wr, oR_eq i hi]
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem oLen_pos (pre : In P σ) (i : Nat) : 0 < oLen P i := by
  have := pre.k1; unfold oLen; split <;> omega_arith

theorem oLen_le (pre : In P σ) (i : Nat) : oLen P i ≤ 4 * P.W := by
  have := pre.k1; unfold oLen; simp only [KP.W]; split <;> omega_arith

/-- A frame word keeps its value. -/
theorem Bo.fwEq (h : Bo P σ s) {o : Nat} (ho' : o + 4 ≤ 112) : fw s.mem P o = fw σ.mem P o := by
  have pre := h.pre
  refine h.frame.readW (r := ⟨off (State.addr P.sp) o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact pre.sF.symm.sub_left (Offset.sub_base _ ho')
  · have : ∃ i, i < 7 ∧ r = oR P i := by
      simp only [KP.outs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩, ⟨4, by decide, rfl⟩,
        ⟨5, by decide, rfl⟩, ⟨6, by decide, rfl⟩]
    obtain ⟨i, hi, rfl⟩ := this
    exact (pre.oF i hi).symm.sub_left (Offset.sub_base _ ho')

/-- `ldr t, [sp, #o]` of a frame word. -/
theorem Bo.ldrSp (h : Bo P σ s) {o : Nat} (ho' : o + 4 ≤ 112) (h4 : o % 4 = 0) {t : Reg} {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', Upd s s' t (fw σ.mem P o) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q := by
  have pre := h.pre
  have spf := pre.spFit
  have ea : State.addr (s.sp + BitVec.ofNat 32 o) = off (State.addr P.sp) o := by
    rw [h.sp, pre.sp]; exact addr_add (by omega_arith)
  refine wp_loadStack (by omega_arith) ea ?_ fun s' u => k s' (by rw [← h.fwEq ho']; exact u)
  rw [h.rd, h.wr]
  exact pre.fwRead ho' h4

theorem Bo.of_upd (h : Bo P σ s) {r : Reg} {v : BitVec 32} (u : Upd s t r v) : Bo P σ t :=
  ⟨h.pre, u.sp.trans h.sp, u.rd.trans h.rd, u.wr.trans h.wr, u.mem ▸ h.frame⟩

theorem KS.bo {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat} (h : KS P σ A live V ls s) :
    Bo P σ s :=
  ⟨h.pre, h.sp, h.rd, h.wr, h.frame.mono (by simp)⟩

end

end VG.Proof.RsaKeyGen.Arm.Key
