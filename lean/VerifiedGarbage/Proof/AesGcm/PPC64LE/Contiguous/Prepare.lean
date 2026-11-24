module

-- separate module: The nonce and AAD proofs recover their inputs without unfolding the payload.

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Frame
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Contiguous.Aad
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Seal
import VerifiedGarbage.Proof.Framework.Offset

/-! # Prepare GCM from the caller's nonce and AAD in the contiguous POWER ABI -/

public section
namespace VG.Proof.AesGcm.PPC64LE.Contiguous
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH blockAt)

abbrev ivBytes (s : State) := bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat
abbrev aadBytes (s : State) := bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat
abbrev nonceAad : Prog isa := .seq VG.Impl.AesGcm.PPC64LE.Contiguous.nonceC VG.Impl.AesGcm.PPC64LE.Contiguous.aadC
abbrev ReadyData (s e t : State) := OA t.gpr e.sp (ctxH s.mem (s.gpr .r3)) (ivBytes s) (aadBytes s) t.mem

theorem args_data {s t : State} (h : CallLayout s) {r : Region} (hr : r∈argsRegions s)
    (lt : r.len<2^64) (rd : Covers [r] (t.rd++t.wr)) :
    DataOk (work s+16) (work s) t r.base r.len := by
  have sep := (stack_disjoint h hr).symm.sub_right (work_sub s)
  exact ⟨rd,lt,h.fit r hr,sep.sub_right (Offset.sub_base _ (by decide)),sep.sub_right (Region.sub_prefix (by decide))⟩

theorem args_lay {s : State} (h : CallLayout s) : Lay (s.gpr .r3) (work s+16) (work s) :=
  oneLay (h.fit (ctxR s) (by simp [argsRegions])) (work_fit h) ((stack_disjoint h (r:=ctxR s) (by simp [argsRegions])).symm.sub_right (work_sub s))

theorem prepare_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] {s e t : State}
    (h : CallLayout s) (p : Args s e) (q : Started e (work s) t) : WP isa nonceAad t (ReadyData s e t) := by
  have key := q.key.trans (p.regs _ (by decide) (by decide))
  have n := q.nonce.trans (p.regs _ (by decide) (by decide))
  have nl := q.nonceLen.trans (p.regs _ (by decide) (by decide))
  have al := q.aadLen.trans (p.regs _ (by decide) (by decide))
  have a := q.aad.trans (p.regs _ (by decide) (by decide))
  have full := p.enteredFrame q
  have read {r : Region} (hr : r∈[ctxR s,nonceR s,aadR s]) : Covers [r] (t.rd++t.wr) := by
    rw [q.entered.keeps.rd,q.entered.keeps.wr];exact p.read h hr
  have ww := p.workWrite
  have env : Env t.gpr e.sp t := ⟨fun _ _ => rfl,q.entered.keeps.sp,by
    rw [key,q.stream,q.scratch]
    apply Perm.of_eq (s := e) _ q.entered.keeps.rd q.entered.keeps.wr
    exact ⟨p.read h (by simp [ctxR]),covers_off ww (by decide) (by decide),covers_prefix ww (by decide)⟩⟩
  have apart {r : Region} (hr : r∈argsRegions s) : ∀ y∈[stack s],r.Disjoint y := by
    intro y mem;obtain rfl := List.mem_singleton.mp mem;exact (stack_disjoint h hr).symm
  have hash := blockAt_frame full (fun r hr => (apart (r:=ctxR s) (by simp [argsRegions]) r hr).sub_left (Offset.sub_base _ (by decide : 240+16≤256)))
  have ni := bytesAt_frame full (apart (r:=nonceR s) (by simp [argsRegions])) (Nat.le_of_lt (s.gpr .r6).isLt)
  have ai := bytesAt_frame full (apart (r:=aadR s) (by simp [argsRegions])) (Nat.le_of_lt (s.gpr .r8).isLt)
  have pre : J0In t.gpr e.sp (ctxH s.mem (s.gpr .r3)) (s.gpr .r5) (s.gpr .r6).toNat t := by
    refine ⟨env,by rw [key];exact hash,n,by simp [nl],?_,?_⟩
    · rw [q.nonceLenSaved,p.regs .r6 (by decide) (by decide)];simp
    · rw [q.stream,q.scratch]
      exact args_data h (r:=nonceR s) (by simp [argsRegions]) (s.gpr .r6).isLt (read (by simp))
  have dat : DataOk (t.gpr .r30) (t.gpr .r31) t (t.gpr .r21) (t.gpr .r22).toNat := by
    rw [q.stream,q.scratch,a,al]
    exact args_data h (r:=aadR s) (by simp [argsRegions]) (s.gpr .r8).isLt (read (by simp))
  have z := nonce_aad_wp ((args_lay h).v key q.stream q.scratch) pre dat
  simpa only [a,al,ni,ai] using z

end VG.Proof.AesGcm.PPC64LE.Contiguous
