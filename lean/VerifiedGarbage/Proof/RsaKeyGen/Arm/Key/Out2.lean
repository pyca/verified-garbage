module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Out
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Taint4
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Key3
import VerifiedGarbage.Proof.Rsa.Arm.RvStore
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.RecoverSubtract

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
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem oArr_mem (i : Nat) (hi : i < 7) : oArr i ∈ LK := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Memory of the working space through a step that writes only an output. -/
theorem w32_frameK {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS)
    (hZ : P.Z ≤ 2 ^ 64) {d : Nat} (hd : d + 4 ≤ P.Z) : w32 m' (State.addr P.B) d = w32 m (State.addr P.B) d := by
  simp only [w32]
  rw [f.readW (r := P.rS) (Offset.contains_base _ hd (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) (by decide)]

theorem num_frameK {m m' : Mem} {R : Region} (f : Frame [R] m m') (hR : R.Disjoint P.rS) (pre : In P σ)
    {j : Nat} (hj : j < nArr) : num m' P.B P.W j = num m P.B P.W j := by
  have fz := pre.fitZ hj
  have hZ := pre.Z_le
  have hS : S P.W = 4 * (P.W + 2) := rfl
  exact val32_congr fun i hi => w32_frameK f hR (by omega) (by omega)

/-- The stage of the key, as the stores' start. -/
theorem KF.ss {E : State → Prop} (h : KF P E σ s) : SS P E 0 σ s :=
  ⟨h.1, h.2.1.bo, h.2.2, fun i hi => h.2.1.arrs _ (oArr_mem i hi),
    by rw [h.2.1.sl sMask (by simp)]; simp only [upd_self], fun _ h => absurd h (by omega)⟩

/-- Output `i` written from its array under the mask. -/
theorem store_vp {E : State → Prop} (i : Nat) (hi : i < 7) (cert : SCert (oArr i)) :
    VP (SS P E i) (seqs (storeTo (oFw i) (oFl i) (oArr i))) (SS P E (i + 1)) := by
  simp only [storeTo, seqs]
  refine VP.seq (G := fun σ s => SS P E i σ s ∧ s.gpr .r10 = oPtr P i ∧ s.gpr .r11 = BitVec.ofNat 32 (oLen P i))
    ?_ ?_
  · show VP _ (.block ([(Reg.r10, oFw i), (Reg.r11, oFl i)].map fun p => Instr.ldrSp p.1 p.2)) _
    have fw4 : oFw i + 4 ≤ 112 ∧ oFw i % 4 = 0 := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
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
    · rw [← h.mask]; exact w32_frameK ft (pre.oS i hi) (by have := pre.Z_le; omega) (Nat.le_trans (by decide) pre.hdr_Z)
    · rcases (by omega : k < i ∨ k = i) with hk' | rfl
      · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame ft (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact pre.oO k i (by omega) hi (by omega))
          (by have := pre.oFit k (by omega); omega)]
        exact h.outs k hk'
      · rw [bt, hm, h.arrs k hi]
        unfold oExp
        cases maskv P σ <;> simp [b2n]

end

end VG.Proof.RsaKeyGen.Arm.Key
