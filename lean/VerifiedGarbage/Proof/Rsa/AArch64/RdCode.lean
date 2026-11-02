module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdMain
public import VerifiedGarbage.Proof.Rsa.AArch64.RpCode
import VerifiedGarbage.Proof.Rsa.AArch64.RpOut
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# `vg_rsa_recover_primes_det` on AArch64: correctness

`RecoverDet.code`, from a state its contract allows, writes `primesKeyDet`
of its inputs (`rdCode_correct`), against `rdA`: `vg_rsa_recover_primes`'
contract on the registers and the stack (`rpA`) with `e` at most 8 bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `vg_rsa_recover_primes_det`'s contract on the registers and the stack. -/
def rdA : Contract isa where
  pre s := rpA.pre s ∧ (s.gpr .x7).toNat ≤ 8
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .x0, (s.gpr .x5).toNat), (s.gpr .x2, (s.gpr .x5).toNat)]
      ((s'.gpr .x0).setWidth 32)
      ((Spec.Rsa.primesKeyDet (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x6) (s₁.gpr .x7).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x6) (s₂.gpr .x7).toNat

/-- What `RecoverDet.code` leaves, from a valid modulus. -/
theorem rdWritten_of {m : Mem} {pp pq : Addr} {x0 : BitVec 64} {nb eb db : List Byte}
    {res : Option (Nat × Nat)}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hres : Spec.Rsa.recoverDet (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = res)
    (b1 : Spec.Rsa.bytesAt m pp nb.length = Spec.Rsa.i2osp (fstOr' res) nb.length)
    (b2 : Spec.Rsa.bytesAt m pq nb.length = Spec.Rsa.i2osp (sndOr' res) nb.length)
    (hr : x0 = BitVec.ofNat 64 res.isSome.toNat) :
    Spec.Rsa.writtenAll m [(pp, nb.length), (pq, nb.length)] (x0.setWidth 32)
      ((Spec.Rsa.primesKeyDet nb eb db).map fun v => [v.1, v.2]) := by
  simp only [Spec.Rsa.primesKeyDet, hv, ite_true]
  rw [hr, setWidth_flag, hres]
  cases res with
  | none =>
    simp only [fstOr', sndOr', Option.isSome_none, Bool.false_eq_true, ite_false, Option.map_none, Spec.Rsa.writtenAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, i2osp_zero'], by rw [b2, i2osp_zero']⟩
  | some v =>
    obtain ⟨p, q⟩ := v
    simp only [fstOr', sndOr', Option.isSome_some, ite_true, Option.map_some, Spec.Rsa.writtenAll, List.map_cons,
      List.map_nil] at b1 b2 ⊢
    exact ⟨trivial, by rw [b1, b2]⟩

/-- `vg_rsa_recover_primes_det`. -/
theorem rdCode_correct [InvLaw] (s : State) (h : rdA.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ rdA.post s s' := by
  have c := rpCtx_of h.1
  have hel8 := h.2
  clear h
  have hk1 : 64 ≤ (s.gpr .x5).toNat := c.L.k1
  have hk2 : (s.gpr .x5).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa code s fun s' => abiPreserved s s' ∧ rdA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (rpIn s).nb.length = (s.gpr .x5).toNat := bytesAt_length _ _ _
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h₁.x2 h₁.x3 hk1 hk2 hnl
    (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₁.val i _))
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have hpre := rpPre_of c h₁ hm₂ k₂
  have kk := h₁.keep.trans k₂
  refine WP.ite (!Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat)
    (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .x5).toNat ≤ (stackArg s 3).toNat * 8 := c.L.z
    exact WP.mono (rpFail_ok hpre.scr hpre.x0 (show 8 * 32 ≤ (stackArg s 3).toNat * 8 by omega) hpre.args
      (show 1 ≤ (s.gpr .x5).toNat by omega) (show (s.gpr .x5).toNat < 2 ^ 31 by omega) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, _, kt⟩ => ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.primesKeyDet (rpIn s).nb (rpIn s).eb (rpIn s).db = none := by
          simp only [Spec.Rsa.primesKeyDet]
          rw [hnl, hv]; simp
        simp only [rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .x5).toNat = true := by simpa using hb
    have dpre : DPre (rpIn s) t₂ := ⟨hpre.scr, hpre.x0, hpre.args, hpre.n, hpre.e, hpre.d, hpre.L, hel8, hpre.oP,
      hpre.oQ, hpre.a, hpre.wr⟩
    refine WP.mono (WP.keep (.x0 :: mmRegs) (rdMain_ok dpre hv) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)) fun t ⟨⟨res, hres, b1, b2, hax, _⟩, kt⟩ =>
      ⟨abiPreserved_of_keep ((kk.trans kt).mono (by decide)), ?_⟩
    have := rdWritten_of (m := t.mem) (pp := s.gpr .x0) (pq := s.gpr .x2) (by rw [hnl]; exact hv) hres
      (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
    rw [hnl] at this
    exact this

end VG.Proof.Rsa.AArch64.Rd
