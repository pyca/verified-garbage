module

public import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
public import VerifiedGarbage.Proof.Bignum.Arm.PcBodyCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The callable RSA precomputation leaks only its public arguments and modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem pcFn_ct {base dst src : BitVec 32} {len k : Nat} {nb : List Byte} :
    RelCT isa (fun s t =>
      (PcFnInput base dst src len k s ∧ Spec.Rsa.bytesAt s.mem (State.addr src) k = nb) ∧
      (PcFnInput base dst src len k t ∧ Spec.Rsa.bytesAt t.mem (State.addr src) k = nb) ∧ s.sp = t.sp)
      PcFn.code (fun _ _ => True) := by
  unfold PcFn.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨⟨hs, bs⟩, ⟨ht, bt⟩, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := pcEntry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, frame1, _, _⟩ := pc_entry_ready s0 hs
      obtain ⟨_, t1, run2, ready2, frame2, _, _⟩ := pc_entry_ready t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have bytes1 := (rsa_bytes_frame (src := State.addr src) (k := k) frame1
        (by have := hs.maxLength; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hs.stackInput.symm)).trans bs
      have bytes2 := (rsa_bytes_frame (src := State.addr src) (k := k) frame2
        (by have := ht.maxLength; omega)
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ht.stackInput.symm)).trans bt
      have body := relCT_keep_sp
        (pcBody_ct (base := base) (dst := dst) (src := src) (len := len) (nb := nb) hs.maxLength)
        (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := body.seq restore _ _ _ _ _ _ ⟨⟨ready1, bytes1⟩, ⟨ready2, bytes2⟩, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
