module
public import VerifiedGarbage.Proof.Rsa.Arm.RvFin5

import VerifiedGarbage.Proof.Rsa.Arm.RvRest
import VerifiedGarbage.Proof.Rsa.Arm.RvTaint5
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer

/-! # `vg_rsa_recover_primes` on ARMv7: zeros written out and 0 returned (`fail_vp`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

section
variable {P : RP}

/-- Zeros written to `dst`, an output. -/
theorem zeroOut_vp {E : State → Prop} {X : State → Mem → Prop} {o : Nat} {dst : BitVec 32} (ho : 4 ≤ o)
    (ho' : o + 4 ≤ 88) (h4 : o % 4 = 0) (hd : ∀ σ, In P σ → fw σ.mem P o = dst)
    (hR : P.rP = ⟨State.addr dst, P.K⟩ ∨ P.rQ = ⟨State.addr dst, P.K⟩) (fit : dst.toNat + P.K ≤ 2 ^ 32)
    (hX : ∀ σ m m', X σ m → Frame [⟨State.addr dst, P.K⟩] m m' → X σ m') :
    VP (fun σ s => E σ ∧ Bo P σ s ∧ X σ s.mem) (zeroOut o)
      (fun σ s => E σ ∧ Bo P σ s ∧ X σ s.mem ∧
        Spec.Rsa.bytesAt s.mem (State.addr dst) P.K = List.replicate P.K 0) := by
  unfold zeroOut
  refine VP.seq (G := fun σ s => (E σ ∧ Bo P σ s ∧ X σ s.mem) ∧ s.gpr .r0 = dst ∧
    s.gpr .lr = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = 0) ?_ ?_
  · show VP _ (.block (([(Reg.r0, o), (Reg.lr, aoK)].map fun p => Instr.ldrSp p.1 p.2) ++
      [.mov .r2 (.imm 0)])) _
    refine VP.block_append (G := fun σ s => (E σ ∧ Bo P σ s ∧ X σ s.mem) ∧ s.gpr .r0 = dst ∧
      s.gpr .lr = BitVec.ofNat 32 P.K) ?_ ?_
    · refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, x⟩ => ?_
      · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
      · refine h.ldrSp (o := o) ho ho' h4 fun s1 u1 => ?_
        refine (h.of_upd u1).ldrSp (o := aoK) (by decide) (by decide) (by decide) fun t u2 => WP.block_nil ?_
        exact ⟨⟨e, (h.of_upd u1).of_upd u2, by rw [u2.mem, u1.mem]; exact x⟩,
          by rw [u2.other _ (by decide), u1.gpr, hd σ h.pre], by rw [u2.gpr, h.pre.aK]⟩
    · refine VP.taint [.r0, .lr] movR2_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, x⟩, p0, plr⟩ => ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2]
      · refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ⟨⟨e, h.of_upd u, by rw [u.mem]; exact x⟩,
          by rw [u.other _ (by decide), p0], by rw [u.other _ (by decide), plr], by rw [u.gpr]⟩
  · refine VP.taint [.r0, .lr] mask_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, x⟩, p0, plr, p2⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
    have pre := h.pre
    have k2 := pre.k2; have k1 := pre.k1
    have hwr : (⟨State.addr dst, P.K⟩ : Region) ∈ s.wr := by
      rw [h.wr, pre.wr]; rcases hR with e | e <;> rw [← e] <;> simp
    refine WP.mono (maskBuffer_ok s (by omega) (by omega) fit ⟨_, hwr, Region.contains_self _ _⟩ p0 plr)
      fun t ⟨b, f, r⟩ => ⟨e, ⟨pre, r.sp.trans h.sp, r.rd.trans h.rd, r.wr.trans h.wr, h.frame.trans (f.mono ?_)⟩,
        hX σ _ _ x f, ?_⟩
    · rcases hR with e | e <;> rw [← e] <;> simp
    · rw [b, p2, VG.Proof.Rsa.Arm.CrtValues.zero_mask_bytes, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]

/-- Zeros to `p` and `q`, and 0 returned. -/
theorem fail_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ Bo P σ s) fail (fun σ s => E σ ∧ Bo P σ s ∧
      Spec.Rsa.bytesAt s.mem (State.addr P.pP) P.K = List.replicate P.K 0 ∧
      Spec.Rsa.bytesAt s.mem (State.addr P.qP) P.K = List.replicate P.K 0 ∧ s.gpr .r0 = 0) := by
  refine VP.of_imp (p := P.pP.toNat + P.K ≤ 2 ^ 32 ∧ P.qP.toNat + P.K ≤ 2 ^ 32 ∧ P.rP.Disjoint P.rQ ∧
    P.K ≤ 1024) (fun σ s h => ⟨h.2.pre.fP, h.2.pre.fQ, h.2.pre.pQ, h.2.pre.k2⟩) fun ⟨fp, fq, pq, k2⟩ => ?_
  simp only [fail, seqs]
  refine VP.seq ((zeroOut_vp (E := E) (X := fun _ _ => True) (o := oP) (dst := P.pP) (by decide) (by decide)
    (by decide) (fun σ h => h.wP) (.inl rfl) fp fun _ _ _ _ _ => trivial).mono (fun σ s h => ⟨h.1, h.2, trivial⟩)
    fun σ s h => h) ?_
  refine VP.seq ((zeroOut_vp (E := E)
    (X := fun _ m => Spec.Rsa.bytesAt m (State.addr P.pP) P.K = List.replicate P.K 0) (o := oQ) (dst := P.qP)
    (by decide) (by decide) (by decide) (fun σ h => h.wQ) (.inr rfl) fq fun σ m m' x f => ?_).mono
    (fun σ s h => ⟨h.1, h.2.1, h.2.2.2⟩) fun σ s h => h) ?_
  · rw [VG.Proof.Rsa.Arm.CrtValues.bytes_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact pq) (by omega), x]
  refine VP.taint [] ret0_taint (fun _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil)
    fun σ s ⟨e, h, bp, bq⟩ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil
      ⟨e, h.of_upd u, by rw [u.mem]; exact bp, by rw [u.mem]; exact bq, u.gpr⟩

end

end VG.Proof.Rsa.Arm.Recover
