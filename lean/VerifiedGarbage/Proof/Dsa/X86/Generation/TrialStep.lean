module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialReduce
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # One trial divisor either rejects the candidate or extends the checked prefix -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

theorem trialCheckStep_ok {s t : State} {base : Addr} {input table : BitVec 32} {len entries i : Nat}
    (R : TrialInputs s base input table len entries) (hi : i < entries)
    (I : TrialLoopInv s base input table len i t) :
    WP isa (trialCheckStep len entries) t fun u =>
      u.zf = some (decide (trialValue s input len % tabEntry i = 0 ∨ i + 1 = entries)) ∧
      ((u.zf = some true ∧ TrialDone s base input len entries u) ∨
      (u.zf = some false ∧ i + 1 < entries ∧ TrialLoopInv s base input table len (i + 1) u)) := by
  have eb := R.entriesBound
  have lb := R.lenBound
  have lp := R.lenPos
  have le := R.lenEven
  have half : 2 * (len / 2) = len := by omega
  have pf := VG.Proof.RsaKeyGen.tabEntry_facts (by omega : i < 1024)
  unfold trialCheckStep
  refine WP.seq (WP.mono (trialCheckArgs_ok R I.context hi I.source I.table I.index)
    fun a ⟨Ca, ma, ps, vi, bp, cx⟩ => ?_)
  refine WP.seq (WP.mono (trialReduce_ok (by omega) (by omega) (by omega) (by omega)
    bp cx ps vi (by rw [half]; exact R.inputFit)
    (fun j hj => by rw [Ca.keeps.2.1, Ca.keeps.2.2]; exact R.inputRead j (by omega)))
    fun b ⟨bx, mb, kb⟩ => ?_)
  have Cb := Ca.unchanged kb (by decide) mb
  have value : b.gpr .ebx = BitVec.ofNat 32 (trialValue s input len % tabEntry i) := by
    rw [bx, half, Ca.inputBytes R]; rfl
  refine WP.seq (wp_cmpi fun c bc _ zc => WP.block_nil ?_)
  have Cc := Cb.fupd bc
  have mc : c.mem = t.mem := by rw [bc.mem, mb, ma]
  have zf : c.zf = some (decide (trialValue s input len % tabEntry i = 0)) := by
    rw [zc, value]
    change some (BitVec.ofNat 32 (trialValue s input len % tabEntry i) - BitVec.ofNat 32 0 == (0 : BitVec 32)) = _
    rw [sub_beq (by have := Nat.mod_lt (trialValue s input len) (by omega : 0 < tabEntry i); omega) (by decide)]
  by_cases hz : trialValue s input len % tabEntry i = 0
  · refine WP.ite true (by simp only [eval, zf, hz, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine WP.mono (trialCheckReject_ok Cc) fun u ⟨Cu, status, zu⟩ => ?_
    exact ⟨by simp [zu, hz], .inl ⟨zu, Cu, status.trans (trialStatus_fail hi hz).symm⟩⟩
  · refine WP.ite false (by simp only [eval, zf, hz, decide_false]) (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.mono (trialCheckNext_ok Cc hi eb (by rw [mc]; exact I.index)) fun u ⟨Cu, idx, slots, zu⟩ => ?_
    have clear : ∀ j < i + 1, trialValue s input len % tabEntry j ≠ 0 := by
      intro j hj
      by_cases eq : j = i
      · simpa only [eq] using hz
      · exact I.clear j (by omega)
    have status : trialSlot u.mem base 12 = 1 := by rw [slots 12 (by decide) (by decide), mc]; exact I.status
    refine ⟨by simpa only [hz, false_or] using zu, ?_⟩
    by_cases done : i + 1 = entries
    · exact .inl ⟨by simpa only [done, decide_true] using zu,
        Cu, status.trans (trialStatus_pass (done ▸ clear)).symm⟩
    · refine .inr ⟨by simpa only [done, decide_false] using zu, by omega, Cu, ?_, ?_, idx, status, clear⟩
      · rw [slots 0 (by decide) (by decide), mc]; exact I.source
      · rw [slots 4 (by decide) (by decide), mc]; exact I.table
end VG.Proof.Dsa.X86.Generation
