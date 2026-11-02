module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont1
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.St

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont7
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont2
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2

/-! # A candidate on ARMv7: Montgomery multiplications as pieces

`St.pmont0`: the base into `r0`; `St.pmontOp`: a Montgomery multiplication
modulo `c`, which keeps `MS` and the key arrays but its own two and its
result's; `St.pctxClr`: the context, and the top words of the result's key
array cleared.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem MS.ready {σ s : State} (h : MS P σ s) (pre : In P σ) (r0 : s.gpr .r0 = P.M0) :
    ArithmeticReady P.M0 P.lenM P.w s :=
  ⟨h.workspace, h.layout, h.width, r0, h.inverse, by rw [h.n0]; exact cv_gt pre, h.stackRead, h.stackSep, h.saved⟩

/-- A Montgomery multiplication's frame keeps `MS`. -/
theorem MS.of_keeps {σ s t : State} (pre : In P σ) (h : MS P σ s) {o : Nat} (ho : o < 8) (ho0 : o ≠ 0)
    (ho4 : o ≠ 4) (k : Keeps (State.addr P.M0) P.lenM P.w o s.mem t.mem) (fr : Frame [P.rM] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MS P σ t := by
  have hw := pre.w4
  have a : ∀ j, arrAt P.w j = 256 + j * (8 * (P.w + 2)) := fun j => rfl
  have kb : ∀ i, i < 8 * P.lenM → (i < arrAt P.w 1 ∨ arrAt P.w 4 ≤ i ∧ i < arrAt P.w 4 + 8 * P.w) →
      t.mem (State.addr P.M0 + BitVec.ofNat 64 i) = s.mem (State.addr P.M0 + BitVec.ofNat 64 i) := by
    intro i hi hr
    refine k i hi fun j hj => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    have e1 := a 1; have e2 := a 2; have e3 := a 3; have e4 := a 4; have e5 := a 5; have eo := a o
    have m1 : o * (8 * (P.w + 2)) ≥ 1 * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega_arith)
    rcases hj with hj | hj | hj <;> rw [hj]
    · simp only [Proof.Rsa.Mont.aAcc]; omega_arith
    · simp only [Proof.Rsa.Mont.aTmp]; omega_arith
    · rcases (by omega_arith : o < 4 ∨ 4 < o) with c | c
      · have : (o + 1) * (8 * (P.w + 2)) ≤ 4 * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega_arith)
        rw [Nat.add_mul] at this; omega_arith
      · have : 5 * (8 * (P.w + 2)) ≤ o * (8 * (P.w + 2)) := Nat.mul_le_mul_right _ (by omega_arith)
        omega_arith
  have lm : arrAt P.w 8 = 8 * P.lenM := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega_arith
  have a28 : arrAt P.w 4 + 8 * P.w ≤ arrAt P.w 8 := by simp only [arrAt]; omega_arith
  refine h.of_read (fun d n hd => ?_) ?_ ?_ sp rd wr
  · have hb : d + n ≤ arrAt P.w 1 := by
      have : 232 ≤ arrAt P.w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith
      rcases hd with (h1 | ⟨_, h1⟩) | ⟨_, h1⟩ <;> simp only [mHd, arrAt] at * <;> omega_arith
    refine Mem.read_congr fun i hi => ?_
    simp only [off]; rw [Offset.add_add]
    exact kb _ (by simp only [arrAt] at *; omega_arith) (.inl (by simp only [arrAt] at *; omega_arith))
  · unfold numAt
    exact congrArg BitVec.toNat (Mem.read_congr fun i hi => by
      rw [Offset.add_add]; exact kb _ (by omega_arith) (.inr ⟨by omega_arith, by omega_arith⟩))
  · rw [sp]
    have hc : (⟨State.addr s.sp, 4⟩ : Region).Contains (State.addr s.sp) (32 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    refine fr.readW hc (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr; exact h.stackSep

/-- `mont0`: the base into `r0`. -/
theorem St.pmont0 :
    VP (fun σ s => St P E A L V LS σ s ∧ MS P σ s) (.block mont0)
      (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r0 = P.M0) := by
  show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
  refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, x⟩ => ?_
  · rw [h₁.1.2.1.sp, h₁.1.2.1.pre.sp, h₂.1.2.1.sp, h₂.1.2.1.pre.sp]
  have sp : s.sp = P.sp := h.sp.trans h.pre.sp
  refine h.bk.ldrSpV (o := 0) (by decide) (by decide) (x.toMSp.fw0 sp) fun t u => WP.block_nil ?_
  have r := u.rest (ws := [.r0]) (by simp)
  exact ⟨⟨⟨e, h.of_rest r u.mem, hw.of_upd u (by decide) (by decide) (by decide)⟩,
    ⟨x.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact x.stride⟩⟩, u.gpr⟩

/-- A Montgomery multiplication modulo `c`, `[o] := [a] [b] R⁻¹` in its arrays. -/
theorem St.pmontOp {o a b : Nat} (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0) (ho4 : o ≠ 4)
    {na nb : State → Nat}
    (hn : ∀ σ s, St P E A L V LS σ s → MS P σ s →
      numAt s.mem (State.addr P.M0) P.w a = na σ ∧ numAt s.mem (State.addr P.M0) P.w b = nb σ)
    (hnb : ∀ σ, E σ → In P σ → nb σ < cv P σ) {L' : List Nat}
    (hL' : ∀ j ∈ L', j ∈ L ∧ j ≠ mBase + 2 ∧ j ≠ mBase + 3 ∧ j ≠ mBase + o) :
    VP (fun σ s => (St P E A L V LS σ s ∧ MS P σ s) ∧ s.gpr .r0 = P.M0) (VG.Impl.Bignum.Arm.montOp o a b)
      (fun σ s => (E σ ∧ KS P σ (A σ) L' (V σ) LS s) ∧ MS P σ s ∧
        numAt s.mem (State.addr P.M0) P.w o < cv P σ ∧
        numAt s.mem (State.addr P.M0) P.w o * 2 ^ (64 * P.w) % cv P σ = na σ * nb σ % cv P σ) := by
  have fitM : arrAt P.w 3 + 32 ≤ 8 * P.lenM := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes, CP.lenM]; omega_arith
  refine VP.of_ct (fun σ₁ σ₂ => (montOp_ct (base := P.M0) (len := P.lenM) (w := P.w) ho ha hb fitM).mono
    (fun s t ⟨⟨⟨⟨e₁, h₁, w₁⟩, m₁⟩, r₁⟩, ⟨⟨⟨e₂, h₂, w₂⟩, m₂⟩, r₂⟩⟩ => ⟨⟨m₁.ready h₁.pre r₁, ?_⟩, ⟨m₂.ready h₂.pre r₂, ?_⟩,
      by rw [h₁.sp, h₁.pre.sp, h₂.sp, h₂.pre.sp]⟩) fun _ _ _ => trivial) fun σ s ⟨⟨⟨e, h, hw⟩, m⟩, r0⟩ => ?_
  · rw [(hn σ₁ s ⟨e₁, h₁, w₁⟩ m₁).2, m₁.n0]; exact hnb σ₁ e₁ h₁.pre
  · rw [(hn σ₂ t ⟨e₂, h₂, w₂⟩ m₂).2, m₂.n0]; exact hnb σ₂ e₂ h₂.pre
  have pre := h.pre
  obtain ⟨va, vb⟩ := hn σ s ⟨e, h, hw⟩ m
  refine WP.mono (montOp_ok s (m.ready pre r0) ho ha hb ho0 (by rw [vb, m.n0]; exact hnb σ e pre))
    fun t ⟨ar, n0, lt, val, keeps, fr, rest⟩ => ⟨⟨e, ?_⟩, ?_, by rw [← m.n0]; exact lt,
      by rw [← m.n0, ← va, ← vb]; exact val⟩
  · have kp := keep_of_mont pre keeps fr
    have hjs : ∀ j ∈ [mBase + 2, mBase + 3, mBase + o], j < nArr := by
      have := ho.1; simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro j (rfl | rfl | rfl) <;>
        simp only [mBase, nArr] <;> omega_arith
    refine h.core kp hjs (by simp) rest.sp rest.rd rest.wr (fun j hj => ?_) (h.sl_keep kp (by simp) (by simp))
      (fun j hj => h.live_lt j (hL' j hj).1) h.ls_ok
    obtain ⟨hjL, h2, h3, ho'⟩ := hL' j hj
    rw [kp.num (fun i hi e' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> simp_all) (by simp) (pre.fit (h.live_lt j hjL))]
    exact h.arrs j hjL
  · exact m.of_keeps pre ho.1 ho0 ho4 keeps fr rest.sp rest.rd rest.wr

end

end VG.Proof.RsaKeyGen.Arm.Cand
