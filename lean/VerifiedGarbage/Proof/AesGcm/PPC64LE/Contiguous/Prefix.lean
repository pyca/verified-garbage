module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Fused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk
import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # The optional fused prefix of contiguous POWER AES-GCM -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Contiguous
open VG.Spec.Gcm (Block blocksAt blockAt ctxH ctxCiph ctr32 ghashFrom inc32)

abbrev prefixCode : Prog isa := .seq (.block [.lsr .d .r12 .r23 9])
  (.ite (.zero .d .r12) (.block [mov .r24 .r19,mov .r18 .r27,mov .r25 .r23]) (.seq fused (.block afterBulk)))

abbrev suffix : Prog isa := .seq (.ite (.zero .d .r25) (.block []) remaining)
  (.seq (.block [mov .r24 .r22, mov .r26 .r23]) (tag 0))

abbrev prefixKeep : List Reg := [.r2,.r14,.r15,.r16,.r17,.r19,.r20,.r21,.r22,.r23,.r27,.r28,.r29,.r30,.r31]

structure PrefixResult (s t : State) : Prop where
  src : t.gpr .r24 = s.gpr .r19 + BitVec.ofNat 64 (DirectGather.prefixLen (s.gpr .r23).toNat)
  dst : t.gpr .r18 = s.gpr .r27 + BitVec.ofNat 64 (DirectGather.prefixLen (s.gpr .r23).toNat)
  len : t.gpr .r25 = BitVec.ofNat 64 ((s.gpr .r23).toNat - DirectGather.prefixLen (s.gpr .r23).toNat)
  saved : ∀ r ∈ prefixKeep, t.gpr r=s.gpr r
  sp : t.sp=s.sp
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  effect : if (s.gpr .r23).toNat<512 then t.mem=s.mem else ∃ u, t.mem=u.mem ∧ FusedResult s u

private theorem and127 (x : Addr) : x &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := 127) (by decide),
    show (127 : Nat)=2^7-1 by decide,Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem prefix_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (access : FusedAccess s) (read : Covers (fusedRead s++fusedWrite s) (s.rd++s.wr))
    (write : Covers (fusedWrite s) s.wr) : WP isa prefixCode s (PrefixResult s) := by
  let n := (s.gpr .r23).toNat
  let z := s.write .r12 (BitVec.ofNat 64 (n/512))
  have len : s.gpr .r23 = BitVec.ofNat 64 n := by simp [n]
  have step : WP isa (.block [.lsr .d .r12 .r23 9]) s (· = z) := by
    have sh := DirectGather.shrNat 9 (s.gpr .r23).isLt
    rw [← len] at sh
    crun [z,sh,n]
  refine WP.seq (WP.mono step fun _ eq => ?_)
  subst_vars
  refine WP.ite (decide (n/512=0)) (eval_zero (s := z) (r := .r12) (by rfl) (by have := (s.gpr .r23).isLt; omega))
    (fun h => ?_) (fun h => ?_)
  · have small : n<512 := by simpa using h
    have h0 : DirectGather.prefixLen n = 0 := by simp [DirectGather.prefixLen,small]
    let u := ((z.write .r24 (s.gpr .r19)).write .r18 (s.gpr .r27)).write .r25 (s.gpr .r23)
    have b : WP isa (.block [mov .r24 .r19,mov .r18 .r27,mov .r25 .r23]) z (· = u) := by
      crun [mov,BitVec.or_self,u,z]
    refine WP.mono b fun t eq => ?_
    subst t
    refine ⟨by rw [h0]; simp [u,State.write],by rw [h0]; simp [u,State.write],by rw [h0,Nat.sub_zero]; exact len,?_,rfl,rfl,rfl,?_⟩
    · intro r hr
      have nr : r ≠ .r25 ∧ r ≠ .r18 ∧ r ≠ .r24 ∧ r ≠ .r12 := by revert r; decide
      simp [u,z,State.write,nr.1,nr.2.1,nr.2.2.1,nr.2.2.2]
    · change if n<512 then _ else _
      simp [small,u,z,State.write]
  · have big : ¬ n<512 := fun lt => (show n/512 ≠ 0 by simpa using h) (Nat.div_eq_of_lt lt)
    have fa : FusedAccess z := ⟨access.ctxDst,access.ctxCtr,access.ctxHash,access.ctrDst,access.hashDst,
      access.scratch,access.buffers,access.dstFit,access.rounds⟩
    refine WP.seq (WP.mono (fused_wp (fused_pre fa) read write) fun v fv => ?_)
    have regs (r : Reg) (hr : r ∈ preserved) : v.gpr r=s.gpr r := by
      rw [fv.regs r hr]
      simp [z,State.write,show r ≠ .r12 by revert r; decide]
    have count := regs .r23 (by decide)
    have rs := regs .r19 (by decide)
    have rd := regs .r27 (by decide)
    let left := BitVec.ofNat 64 (n%128)
    let doneBytes := BitVec.ofNat 64 (n-n%128)
    let u := ((((v.write .r0 127).write .r25 left).write .r11 doneBytes).write .r24
      (s.gpr .r19+doneBytes)).write .r18 (s.gpr .r27+doneBytes)
    have minus : s.gpr .r23 - left = doneBytes := by
      rw [len]; exact ofNat_sub64 (Nat.mod_le n _) (s.gpr .r23).isLt
    have b : WP isa (.block afterBulk) v (· = u) := by
      crun [afterBulk,count,rs,rd,and127,u,minus,left,doneBytes,n]
    refine WP.mono b fun t eq => ?_
    subst t
    have vlen : DirectGather.prefixLen n = n - n%128 := by simp only [DirectGather.prefixLen,big,↓reduceIte,DirectGather.bulkLen]; omega
    refine ⟨by rw [vlen]; rfl,by rw [vlen]; rfl,?_,?_,fv.sp,fv.rd,fv.wr,?_⟩
    · change left=BitVec.ofNat 64 (n-DirectGather.prefixLen n)
      rw [vlen,Nat.sub_sub_self (Nat.mod_le n 128)]
    · intro r hr
      have good : r ≠ .r18 ∧ r ≠ .r24 ∧ r ≠ .r11 ∧ r ≠ .r25 ∧ r ≠ .r0 ∧ r ∈ preserved := by revert r; decide
      simp [u,State.write,good.1,good.2.1,good.2.2.1,good.2.2.2.1,good.2.2.2.2.1,regs r good.2.2.2.2.2]
    · change if n<512 then _ else _
      simp only [big,↓reduceIte]
      exact ⟨v,rfl,⟨fv.rd,fv.wr,fv.sp,regs,fv.frame,fv.data,fv.counter,fv.hash⟩⟩

end VG.Proof.AesGcm.PPC64LE.Contiguous
