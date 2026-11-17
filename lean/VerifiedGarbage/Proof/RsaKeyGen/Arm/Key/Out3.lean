module

import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint5
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Fail
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Stores
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Rsa.BoolNat
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint4
import VerifiedGarbage.Proof.Rsa.Sub32
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint4
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Key3
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Store
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Base
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Mul
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Front3

/-! ### `RsaKeyGen.Arm.Key.Out2`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Key.Out`, which only this module used -/

section

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

end

end

/-! # An RSA key on ARMv7: the outputs written under the mask (`stores_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- Output `i` as it is written. -/
def oExp (P : KP) (σ : State) (i : Nat) : List Byte :=
  if maskv P σ = true then Spec.Rsa.i2osp (AK P σ (oArr i) % 2 ^ (8 * oLen P i)) (oLen P i)
  else List.replicate (oLen P i) 0

/-- The stores, after `k` outputs. -/
structure SS (P : KP) (E : State → Prop) (k : Nat) (σ s : State) : Prop where
  e : E σ
  bo : Bo P σ s
  ws : Ws s P.B P.Z P.W nArr
  arrs : ∀ i < 7, num s.mem P.B P.W (oArr i) = AK P σ (oArr i)
  mask : slot s.mem P.B sMask = b2n (maskv P σ)
  outs : ∀ i < k, Spec.Rsa.bytesAt s.mem (State.addr (oPtr P i)) (oLen P i) = oExp P σ i

section
variable {P : KP} {σ s t : State}

theorem oArr_lt (i : Nat) (hi : i < 7) : oArr i < nArr := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem oArr_mem (i : Nat) (hi : i < 7) : oArr i ∈ LK := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Memory of the working space through a step that writes only an output. -/
theorem w32_frameK {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (hZ : P.Z ≤ 2 ^ 64) {d : Nat} (hd : d + 4 ≤ P.Z) : w32 m' (State.addr P.B) d = w32 m (State.addr P.B) d := by
  simp only [w32]
  rw [f.readW (r := P.rS) (Offset.contains_base _ hd (by omega_using [hZ, hd])) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) (by decide)]

theorem num_frameK {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS) (pre : In P σ)
    {j : Nat} (hj : j < nArr) : num m' P.B P.W j = num m P.B P.W j := by
  have fz := pre.fitZ hj
  have hZ := pre.Z_le
  have hS : S P.W = 4 * (P.W + 2) := rfl
  exact val32_congr fun i hi => w32_frameK f hR (by omega_using [hZ]) (by omega_using [fz, hS, hi])

/-- The stage of the key, as the stores' start. -/
theorem KF.ss {E : State → Prop} (h : KF P E σ s) : SS P E 0 σ s :=
  ⟨h.1, h.2.1.bo, h.2.2, fun i hi => h.2.1.arrs _ (oArr_mem i hi),
    by rw [h.2.1.sl sMask (by simp)]; simp only [upd_self], fun _ h => absurd h (by omega_using [])⟩

/-- Output `i` written from its array under the mask. -/
theorem store_vp {E : State → Prop} (i : Nat) (hi : i < 7) (cert : SCert (oArr i)) :
    VP (SS P E i) (seqs (storeTo (oFw i) (oFl i) (oArr i))) (SS P E (i + 1)) := by
  simp only [storeTo, seqs]
  refine VP.seq (G := fun σ s => SS P E i σ s ∧ s.gpr .r10 = oPtr P i ∧ s.gpr .r11 = BitVec.ofNat 32 (oLen P i))
    ?_ ?_
  · show VP _ (.block ([(Reg.r10, oFw i), (Reg.r11, oFl i)].map fun p => Instr.ldrSp p.1 p.2)) _
    have fw4 : oFw i + 4 ≤ 112 ∧ oFw i % 4 = 0 := by
      rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have fl4 : oFl i + 4 ≤ 112 ∧ oFl i % 4 = 0 := by unfold oFl; split <;> decide
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s h => ?_
    · rw [h₁.bo.sp, h₁.bo.pre.sp, h₂.bo.sp, h₂.bo.pre.sp]
    · show WP isa (.block [.ldrSp .r10 (oFw i), .ldrSp .r11 (oFl i)]) s _
      refine h.bo.ldrSp fw4.1 fw4.2 fun s1 u1 => ?_
      refine (h.bo.of_upd u1).ldrSp fl4.1 fl4.2 fun t u2 => WP.block_nil ?_
      refine ⟨⟨h.e, (h.bo.of_upd u1).of_upd u2, (h.ws.of_upd u1 (by decide) (by decide) (by decide)).of_upd u2
        (by decide) (by decide) (by decide), by rw [u2.mem, u1.mem]; exact h.arrs, by rw [u2.mem, u1.mem]; exact h.mask,
        by rw [u2.mem, u1.mem]; exact h.outs⟩, ?_, ?_⟩
      · rw [u2.other _ (by decide), u1.gpr, h.bo.pre.fwO i hi]
      · rw [u2.gpr, h.bo.pre.flO i]
  · refine VP.taint [.r7, .r8, .r9, .r10, .r11] cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨h, p10, p11⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      · rw [h₁.1.ws.r7, h₂.1.ws.r7]
      · rw [h₁.1.ws.r8, h₂.1.ws.r8]
      · rw [h₁.1.ws.r9, h₂.1.ws.r9]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]
    have pre := h.bo.pre
    have hm : slot s.mem P.B VG.Impl.Rsa.Arm.CrtValues.sMask = b2n (maskv P σ) := h.mask
    refine WP.mono (store_ok' h.ws (Z := P.Z) (w := P.W) (dst := oPtr P i) (k := oLen P i) (j := oArr i)
      (R := oR P i) (by decide) (oArr_lt i hi) (pre.oS i hi) (by rw [h.bo.wr]; exact pre.oW i hi) rfl
      (oLen_pos pre i) (oLen_le pre i) (pre.oFit i hi) p10 p11 (by rw [hm]; exact b2n_le' _)
      (Nat.le_trans (by decide) pre.hdr_Z)) fun t ⟨hwt, bt, ft, rt⟩ => ?_
    refine ⟨h.e, ⟨pre, rt.sp.trans h.bo.sp, rt.rd.trans h.bo.rd, rt.wr.trans h.bo.wr,
      h.bo.frame.trans (ft.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (oR_mem i hi))⟩, hwt,
      fun i' hi' => by rw [num_frameK ft (pre.oS i hi) pre (oArr_lt i' hi')]; exact h.arrs i' hi', ?_, fun k hk => ?_⟩
    · rw [← h.mask]; exact w32_frameK ft (pre.oS i hi) (by have := pre.Z_le; omega_using [this]) (Nat.le_trans (by decide) pre.hdr_Z)
    · rcases (by omega_using [hk] : k < i ∨ k = i) with hk' | rfl
      · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame ft (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact pre.oO k i (by omega_using [hi, hk]) hi (by omega_using [hk']))
          (by have := pre.oFit k (by omega_using [hi, hk]); omega_using [this])]
        exact h.outs k hk'
      · rw [bt, hm, h.arrs k hi]
        unfold oExp
        cases maskv P σ <;> simp [b2n]

end

end VG.Proof.RsaKeyGen.Arm.Key

end

end

/-! # An RSA key on ARMv7: the seven outputs and the mask returned (`stores_vp`), or zeros and 2 (`zeros_vp`) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP sub32 VP.of_imp)
open VG.Proof.Rsa (b2n)

/-- Zeros at the first `k` outputs. -/
def ZS (P : KP) (E : State → Prop) (k : Nat) (σ s : State) : Prop :=
  E σ ∧ Bo P σ s ∧ ∀ i < k, Spec.Rsa.bytesAt s.mem (State.addr (oPtr P i)) (oLen P i) = List.replicate (oLen P i) 0

section
variable {P : KP}

theorem oFw_ok (i : Nat) (hi : i < 7) : oFw i + 4 ≤ 112 ∧ oFw i % 4 = 0 := by
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem oFl_ok (i : Nat) : oFl i + 4 ≤ 112 ∧ oFl i % 4 = 0 := by unfold oFl; split <;> decide

/-- The seven outputs, and the mask returned. -/
theorem stores_vp {E : State → Prop} :
    VP (SS P E 0) stores (fun σ s => SS P E 7 σ s ∧ s.gpr .r0 = BitVec.ofNat 32 (b2n (maskv P σ))) := by
  simp only [stores, List.cons_append, List.nil_append, storeTo, seqs]
  refine VP.assoc ((store_vp 0 (by decide) storeN_taint).seq ?_)
  refine VP.assoc ((store_vp 1 (by decide) storeD_taint).seq ?_)
  refine VP.assoc ((store_vp 2 (by decide) storeP_taint).seq ?_)
  refine VP.assoc ((store_vp 3 (by decide) storeQ_taint).seq ?_)
  refine VP.assoc ((store_vp 4 (by decide) storeDp_taint).seq ?_)
  refine VP.assoc ((store_vp 5 (by decide) storeDq_taint).seq ?_)
  refine VP.assoc ((store_vp 6 (by decide) storeQi_taint).seq ?_)
  refine VP.taint [.r7, .r8, .r9] retMask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [h₁.ws.r7, h₂.ws.r7]
    · rw [h₁.ws.r8, h₂.ws.r8]
    · rw [h₁.ws.r9, h₂.ws.r9]
  · refine wp_ldrSlot h.ws (d := sMask) (by decide) fun t u => WP.block_nil ⟨⟨h.e, h.bo.of_upd u,
      h.ws.of_upd u (by decide) (by decide) (by decide), by rw [u.mem]; exact h.arrs, by rw [u.mem]; exact h.mask,
      by rw [u.mem]; exact h.outs⟩, ?_⟩
    rw [u.gpr, ← h.mask]
    simp only [slot, w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Zeros to output `i`. -/
theorem zeroOut_vp {E : State → Prop} (i : Nat) (hi : i < 7) :
    VP (ZS P E i) (zeroOut (oFw i) (oFl i)) (ZS P E (i + 1)) := by
  unfold zeroOut
  have fw4 := oFw_ok i hi
  have fl4 := oFl_ok i
  refine VP.seq (G := fun σ s => ZS P E i σ s ∧ s.gpr .r0 = oPtr P i ∧
    s.gpr .lr = BitVec.ofNat 32 (oLen P i) ∧ s.gpr .r2 = 0) ?_ ?_
  · show VP _ (.block (([(Reg.r0, oFw i), (Reg.lr, oFl i)].map fun p => Instr.ldrSp p.1 p.2) ++
      [.mov .r2 (.imm 0)])) _
    refine VP.block_append (G := fun σ s => ZS P E i σ s ∧ s.gpr .r0 = oPtr P i ∧
      s.gpr .lr = BitVec.ofNat 32 (oLen P i)) ?_ ?_
    · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, x⟩ => ?_
      · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
      · show WP isa (.block [.ldrSp .r0 (oFw i), .ldrSp .lr (oFl i)]) s _
        refine h.ldrSp fw4.1 fw4.2 fun s1 u1 => ?_
        refine (h.of_upd u1).ldrSp fl4.1 fl4.2 fun t u2 => WP.block_nil ?_
        exact ⟨⟨e, (h.of_upd u1).of_upd u2, by rw [u2.mem, u1.mem]; exact x⟩,
          by rw [u2.other _ (by decide), u1.gpr, h.pre.fwO i hi], by rw [u2.gpr, h.pre.flO i]⟩
    · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.movR2_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
        fun σ s ⟨⟨e, h, x⟩, p0, plr⟩ => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]
      · refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_upd u, by rw [u.mem]; exact x⟩,
          by rw [u.other _ (by decide), p0], by rw [u.other _ (by decide), plr], by rw [u.gpr]⟩
  · refine VP.taint [.r0, .lr] VG.Proof.Rsa.Arm.Recover.mask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
      fun σ s ⟨⟨e, h, x⟩, p0, plr, p2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
    have pre := h.pre
    have hl := oLen_le pre i
    have hW : 4 * P.W < 2 ^ 32 := by have := pre.k2; simp only [KP.W]; omega_using [this]
    have hwr : InRegions s.wr (State.addr (oPtr P i)) (oLen P i) :=
      ⟨_, by rw [h.wr]; exact pre.oW i hi, Region.contains_self _ _⟩
    refine WP.mono (maskBuffer_ok s (oLen_pos pre i) (by omega_using [hl, hW]) (pre.oFit i hi) hwr p0 plr)
      fun t ⟨b, f, r⟩ => ⟨e, ⟨pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, h.frame.trans (f.mono ?_)⟩,
        fun k hk => ?_⟩
    · intro r' hr; simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (oR_mem i hi)
    · rcases (by omega_using [hk] : k < i ∨ k = i) with hk' | rfl
      · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact pre.oO k i (by omega_using [hi, hk]) hi (by omega_using [hk']))
          (by have := pre.oFit k (by omega_using [hi, hk]); omega_using [this])]
        exact x k hk'
      · rw [b, p2, VG.Proof.Rsa.Arm.CrtValues.zero_mask_bytes, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]

/-- Zeros to the seven outputs, and 2 returned. -/
theorem zeros_vp {E : State → Prop} :
    VP (ZS P E 0) zeros (fun σ s => ZS P E 7 σ s ∧ s.gpr .r0 = 2) := by
  simp only [zeros, seqs]
  refine (zeroOut_vp 0 (by decide)).seq ?_
  refine (zeroOut_vp 1 (by decide)).seq ?_
  refine (zeroOut_vp 2 (by decide)).seq ?_
  refine (zeroOut_vp 3 (by decide)).seq ?_
  refine (zeroOut_vp 4 (by decide)).seq ?_
  refine (zeroOut_vp 5 (by decide)).seq ?_
  refine (zeroOut_vp 6 (by decide)).seq ?_
  refine VP.taint [] ret2_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
    fun σ s ⟨e, h, z⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨⟨e, h.of_upd u, by rw [u.mem]; exact z⟩, u.gpr⟩

end

end VG.Proof.RsaKeyGen.Arm.Key
