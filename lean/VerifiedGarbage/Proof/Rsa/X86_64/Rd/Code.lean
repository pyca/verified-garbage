module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Main
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86_64.RpOut
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: correctness

`RecoverDet.code`, from a state its contract allows, writes `primesKeyDet`
of its inputs (`rdCode_correct`), against `rdContract`, which states the
shared contract's precondition on the registers and the stack, and implies
`vg_rsa_recover_primes`' (`rpContract`), whose entry and failure it shares.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (aN)

/-- `vg_rsa_recover_primes_det(p = rdi, p_len = rsi, q = rdx, q_len = rcx,
n = r8, n_len = r9, e = [rsp + 8], e_len = [rsp + 16], d = [rsp + 24],
d_len = [rsp + 32], scratch = [rsp + 40], scratch_len = [rsp + 48])`. -/
def rdContract : Contract isa where
  pre s := rpContract.pre s ∧ (stackArg s 1).toNat ≤ 8
  post s s' :=
    Spec.Rsa.writtenAll s'.mem [(s.gpr .rdi, (s.gpr .r9).toNat), (s.gpr .rdx, (s.gpr .r9).toNat)]
      ((s'.gpr .rax).setWidth 32)
      ((Spec.Rsa.primesKeyDet (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)).map fun v => [v.1, v.2])
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧ stackArg s₁ 4 = stackArg s₂ 4 ∧ stackArg s₁ 5 = stackArg s₂ 5 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 0) (stackArg s₁ 1).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 0) (stackArg s₂ 1).toNat

/-- `rdContract`'s precondition is `rpContract`'s, with `e_len ≤ 8`. -/
theorem rd_rp {s : State} (h : rdContract.pre s) : rpContract.pre s ∧ (stackArg s 1).toNat ≤ 8 := h

/-- What `RecoverDet.code` leaves, from a valid modulus. -/
theorem rdWritten_of {m : Mem} {pp pq : Addr} {rax : BitVec 64} {nb eb db : List Byte}
    {res : Option (Nat × Nat)}
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) nb.length = true)
    (hres : Spec.Rsa.recoverDet (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = res)
    (b1 : Spec.Rsa.bytesAt m pp nb.length = Spec.Rsa.i2osp (fstOr res) nb.length)
    (b2 : Spec.Rsa.bytesAt m pq nb.length = Spec.Rsa.i2osp (sndOr res) nb.length)
    (hr : rax = BitVec.ofNat 64 res.isSome.toNat) :
    Spec.Rsa.writtenAll m [(pp, nb.length), (pq, nb.length)] (rax.setWidth 32)
      ((Spec.Rsa.primesKeyDet nb eb db).map fun v => [v.1, v.2]) := by
  simp only [Spec.Rsa.primesKeyDet, hv, ite_true]
  rw [hr, setWidth_flag]
  subst hres
  generalize Spec.Rsa.recoverDet (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip eb) (Spec.Rsa.os2ip db) = r1 at b1 b2 ⊢
  cases r1 with
  | none =>
    simp only [fstOr, sndOr, Option.isSome_none, Option.map_none, Spec.Rsa.writtenAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b1 b2 ⊢
    exact ⟨rfl, by rw [b1, i2osp_zero'], by rw [b2, i2osp_zero']⟩
  | some v =>
    obtain ⟨p, q⟩ := v
    simp only [fstOr, sndOr, Option.isSome_some, Option.map_some, Spec.Rsa.writtenAll, List.map_cons,
      List.map_nil] at b1 b2 ⊢
    exact ⟨rfl, by rw [b1, b2]⟩

theorem rdCode_correct [InvLaw] (hmx : Impl.Rsa.X86_64.Keys.RecoverDet.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : rdContract.pre s) :
    ∃ t s', Exec isa Impl.Rsa.X86_64.Keys.RecoverDet.code s t s' ∧ abiPreserved s s' ∧ rdContract.post s s' := by
  obtain ⟨h, hel8⟩ := rd_rp h
  have c := rpCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .r9).toNat := c.L.k1
  have hk2 : (s.gpr .r9).toNat ≤ 1024 := c.L.k2
  suffices hwp : WP isa Impl.Rsa.X86_64.Keys.RecoverDet.code s fun s' => gprPreserved s s' ∧ rdContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold Impl.Rsa.X86_64.Keys.RecoverDet.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rpHead_ok' c) fun t₁ h₁ => ?_
  have hnb₁ := c.n.congrK h₁.inScr h₁.keep
  have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
  refine WP.mono (invalid_ok h₁.rdx h₁.rcx hk1 hk2 hnl (fun i hi => hnb₁.rd i (by rw [hnl]; exact hi))
    (fun i hi => hnb₁.val i _)) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have hpre := rpPre_of c h₁ hm₂ k₂
  have hsp₂ : t₂.gpr .rsp = s.gpr .rsp := hpre.rsp
  refine WP.ite (!Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat) (by simp [eval, hz₂]) (fun hb => ?_)
    (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat = false := by simpa using hb
    have z : 128 * (s.gpr .r9).toNat ≤ (stackArg s 5).toNat * 8 := c.L.z
    exact WP.mono (rpFail_ok hpre.scr hpre.rdi (show 8 * 32 ≤ (stackArg s 5).toNat * 8 by omega_arith) hpre.args
      (show 1 ≤ (s.gpr .r9).toNat by omega_arith) (show (s.gpr .r9).toNat < 2 ^ 31 by omega_arith) hpre.oP hpre.oQ hpre.a)
      fun t ⟨z1, z2, hax, hsv, hfr, hsp⟩ => ⟨rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x n1 n2, hm₂]; exact h₁.inScr x hx, by
        show Spec.Rsa.writtenAll _ _ _ _
        have hnone : Spec.Rsa.primesKeyDet (rpIn s).nb (rpIn s).eb (rpIn s).db = none := by
          simp only [Spec.Rsa.primesKeyDet]
          rw [hnl, hv]; simp
        simp only [rpIn] at hnone
        rw [hnone, hax]
        simp only [Option.map_none, Spec.Rsa.writtenAll, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨rfl, bytesAt_zero z1, bytesAt_zero z2⟩⟩
  · have hv : Spec.Rsa.modulusValid (rpIn s).N (s.gpr .r9).toNat = true := by simpa using hb
    exact WP.mono (rdMain_ok hpre hel8 hv) fun t ⟨res, hres, b1, b2, hax, hsv, hfr, hsp⟩ =>
      ⟨rpGpr_of c hsv hsp hsp₂ fun x hx n1 n2 => by
        rw [hfr x hx n1 n2, hm₂]; exact h₁.inScr x hx, by
        have := rdWritten_of (m := t.mem) (pp := s.gpr .rdi) (pq := s.gpr .rdx) (eb := (rpIn s).eb)
          (db := (rpIn s).db) (by rw [hnl]; exact hv) hres (by rw [hnl]; exact b1) (by rw [hnl]; exact b2) hax
        rw [hnl] at this
        exact this⟩

end VG.Proof.Rsa.X86_64.Rd
