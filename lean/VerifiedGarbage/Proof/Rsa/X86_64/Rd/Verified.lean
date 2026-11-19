module

-- separate module: it builds in parallel with the batched inverse's proofs (`InvInstance`, which imports the divstep algebra), which only `Instances` brings in
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Main
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Main
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Entry
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtFin
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtNorm
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoop
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtCorr
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoops
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtFin
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtNorm
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtCorr
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
meta import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtEntry
meta import VerifiedGarbage.Spec.Rsa.RecoverDet
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-! ### `Rsa.X86_64.Rd.CTMain`, which only this module used -/

section

/-! ### `Rsa.X86_64.Rd.Code`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_recover_primes_det` on x86-64: correctness

`RecoverDet.code`, from a state its contract allows, writes `primesKeyDet`
of its inputs (`rdCode_correct`), against `rdContract`, which states the
shared contract's precondition on the registers and the stack: `rpPre`, the
precondition of the entry and the failure path (`Rd/Entry.lean`), with
`e_len ≤ 8`.
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
  pre s := rpPre s ∧ (stackArg s 1).toNat ≤ 8
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

/-- `rdContract`'s precondition is `rpPre`, with `e_len ≤ 8`. -/
theorem rd_rp {s : State} (h : rdContract.pre s) : rpPre s ∧ (stackArg s 1).toNat ≤ 8 := h

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

end

end

/-! ### `Rsa.X86_64.Rd.CTQDiv`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the division by words

`qDiv e`'s step reloads the count `j + 1` from the header and addresses the
dividend's digit and the quotient's word by it: its runs agree from states
whose count is the same (`QB`), the count being public. The step proper
(`WordReduce.step`) is checked from the registers `qDigit` pins, and needs
the loop's invariant (`QInv`) for its arithmetic; its setup needs the
divisor's top bit set (`FDp`) for the reciprocal.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## A step, from a public count -/

/-- Before a step with the count `c` (`a = (p, c)`): `qBody_ok`'s hypotheses
at the wide width `W = 2 h + 4`. -/
structure QB (e : Nat) (a : RpP × Nat) (s : State) : Prop where
  ws : Ws s a.1.B a.1.Z (wW a.1.k)
  kb : 8 ≤ wk a.1.k ∧ wk a.1.k ≤ 128
  e1 : 1 ≤ e
  e3 : e ≤ 3
  cnt : word s.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2
  c1 : 1 ≤ a.2
  cN : a.2 ≤ wk a.1.k + e
  hd : 2 ^ 63 ≤ (word s.mem a.1.B (slot (wW a.1.k) qD + 8 * (wk a.1.k - 1))).toNat
  hv : (word s.mem a.1.B (slot (wW a.1.k) qV)).toNat =
    (2 ^ 128 - 1) / (word s.mem a.1.B (slot (wW a.1.k) qD + 8 * (wk a.1.k - 1))).toNat - 2 ^ 64
  hx : wv s.mem a.1.B (slot (wW a.1.k) qR) (wk a.1.k) < wv s.mem a.1.B (slot (wW a.1.k) qD) (wk a.1.k)

theorem QB.lay {e : Nat} {a : RpP × Nat} {s : State} (h : QB e a s) : QLay (wW a.1.k) (wk a.1.k) e :=
  ⟨wW_eq _, h.kb.1, h.e1, h.e3⟩

/-- After `qLoad`. -/
def qLoadVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .r12 => BitVec.ofNat 64 (wW a.1.k)
  | .r9 => BitVec.ofNat 64 (8 * (wW a.1.k + 2))
  | .rbp => off a.1.B (slot (wW a.1.k) qV)
  | .r11 => off a.1.B (slot (wW a.1.k) qA)
  | .rcx => BitVec.ofNat 64 a.2
  | _ => 0

/-- The step's registers. -/
def qStepVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) qR)
  | .r10 => off a.1.B (slot (wW a.1.k) qD)
  | .r8 => off a.1.B (slot (wW a.1.k) qT)
  | .rbp => off a.1.B (slot (wW a.1.k) qV)
  | .r12 => BitVec.ofNat 64 (wk a.1.k)
  | _ => 0

/-- After `qLoad` and `qDigit`, from `s`. -/
def Q1 (e : Nat) (a : RpP × Nat) (t : State) : Prop :=
  ∃ s, QB e a s ∧ (∀ r ∈ [.rdi, .rbx, .r10, .r8, .rbp, .r12], t.gpr r = qStepVal a r) ∧
    t.mem = s.mem.writeW (off a.1.B (slot (wW a.1.k) qV + 8)) (word s.mem a.1.B (slot (wW a.1.k) qA + 8 * (a.2 - 1))) ∧
    Keep [.r12, .r9, .rbp, .r11, .rcx, .rdx, .rbx, .r10, .r8] s t

/-- After the step. -/
def Q2 (e : Nat) (a : RpP × Nat) (t : State) : Prop :=
  Ws t a.1.B a.1.Z (wW a.1.k) ∧ word t.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2 ∧ 1 ≤ a.2 ∧
    a.2 ≤ wk a.1.k + e ∧ 8 ≤ wk a.1.k ∧ wk a.1.k ≤ 128 ∧ e ≤ 3

/-- After `qPos`. -/
def qPosVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) qQ)
  | .rax => BitVec.ofNat 64 a.2
  | _ => 0

theorem pins_list {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

theorem qLoadDigit_ok {e : Nat} {a : RpP × Nat} {s : State} (h : QB e a s) :
    WP isa (.seq (.block qLoad) (.block qDigit)) s (Q1 e a) := by
  have hw := h.ws
  obtain hW := wW_eq a.1.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  have kb := h.kb
  have e3 := h.e3
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  have hc1 := h.c1
  have hcN := h.cN
  refine WP.seq (WP.mono (qLoad_ok hw h.cnt) fun s₁ ⟨hdi₁, h12₁, h9₁, hbp₁, h11₁, hcx₁, hm₁, k₁⟩ => ?_)
  refine WP.mono (qDigit_ok (hw.scr.congr k₁.2.2) hdi₁ h9₁ h12₁ hbp₁ h11₁ hcx₁ hc1 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hbx, h10, h8', hbp, h12, hm, k₂⟩ => ?_
  refine ⟨s, h, fun r hr => ?_, by rw [hm, hm₁], (k₁.trans k₂).mono (by simp)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k₂.gpr (by decide)).trans hdi₁
  · exact hbx
  · exact h10
  · exact h8'
  · exact hbp
  · rw [h12]; show _ = BitVec.ofNat 64 (wk a.1.k); congr 1; omega_arith

theorem qStepW_ok {e : Nat} {a : RpP × Nat} {t : State} (h1 : Q1 e a t) :
    WP isa Impl.Rsa.X86_64.WordReduce.step t (Q2 e a) := by
  obtain ⟨s, h, hr, hm₂, k12⟩ := h1
  obtain hbx₂ := hr .rbx (by simp)
  obtain h10₂ := hr .r10 (by simp)
  obtain h8₂ := hr .r8 (by simp)
  obtain hbp₂ := hr .rbp (by simp)
  obtain h12₂ := hr .r12 (by simp)
  simp only [qStepVal] at hbx₂ h10₂ h8₂ hbp₂ h12₂
  clear hr
  have hw := h.ws
  obtain hW := wW_eq a.1.k
  have h8 := h.kb.1
  have e3 := h.e3
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have h256 := hw.h256
  have hw2 := hw.w2
  have kb := h.kb
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  have hct : 8 * sCt = 200 := rfl
  have hc1 := h.c1
  have hcN := h.cN
  have hcnt := h.cnt
  have hhd := h.hd
  have hhv := h.hv
  have hhx := h.hx
  clear h
  obtain ⟨p, c⟩ := a
  unfold Q2
  simp only at *
  generalize wW p.k = W at *
  generalize wk p.k = hh at *
  obtain hs₂ := hw.scr.congr k12.2.2
  obtain wD : ∀ i < hh, word t.mem p.B (slot W qD + 8 * i) = word s.mem p.B (slot W qD + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  obtain wR : ∀ i < hh, word t.mem p.B (slot W qR + 8 * i) = word s.mem p.B (slot W qR + 8 * i) := fun i hi => by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  obtain vD : wv t.mem p.B (slot W qD) hh = wv s.mem p.B (slot W qD) hh := wv_congr wD
  obtain vR : wv t.mem p.B (slot W qR) hh = wv s.mem p.B (slot W qR) hh := wv_congr wR
  obtain tD : word t.mem p.B (slot W qD + 8 * (hh - 1)) = word s.mem p.B (slot W qD + 8 * (hh - 1)) :=
    wD _ (by omega_arith)
  obtain rV : word t.mem p.B (slot W qV) = word s.mem p.B (slot W qV) := by
    rw [hm₂]; exact (writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega)
  refine WP.mono (WordReduce.stepQ_ok hs₂ hbx₂ h10₂ h8₂ h12₂ hbp₂ (by omega_arith) (by omega_arith)
    (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega) (by q_omega)
    (by rw [tD]; exact hhd) (by rw [rV, tD]; exact hhv) (by rw [vR, vD]; exact hhx))
    fun s₃ ⟨_, f₃, k₃, _⟩ => ?_
  obtain hw₂ : Ws t p.B p.Z W := hw.congrP (P := fun y => slot W qV + 8 ≤ y ∧ y < slot W qV + 16)
    (by rw [hm₂]; exact FrmP.of_writeW _ (by q_omega) fun _ h1 h2 => ⟨h1, h2⟩)
    (fun y hy => .inl (by omega_arith)) k12 (by decide)
  obtain hw₃ : Ws s₃ p.B p.Z W := hw₂.congr f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Or.inl (by q_omega)) k₃ (by decide)
  refine ⟨hw₃, ?_, hc1, hcN, h8, kb.2, e3⟩
  rw [f₃.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> q_omega) (by q_omega), hm₂]
  rw [(writeW_outside s.mem p.B _ (by q_omega)).word (by q_omega) (by q_omega), hcnt]

theorem qBody_ct (e : Nat) : RelCT isa (Two (QB e)) qBody fun _ _ => True := by
  change RelCT isa _ (.seq (.block (qLoad ++ qDigit)) (.seq Impl.Rsa.X86_64.WordReduce.step
    (.block (qPos ++ qTail)))) _
  refine RelCT.seq (RelCT.block_append (pin_ct (Ψ := Q1 e) [.rdi] [.rdi, .r12, .r9, .rbp, .r11, .rcx] qLoadVal
    (pins_list (fun a => qLoadVal a) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ws.rdi)
    (by taint_decide) (fun a s h => WP.mono (qLoad_ok h.ws h.cnt) fun t ⟨hdi, h12, h9, hbp, h11, hcx, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdi
      · exact h12
      · exact h9
      · exact hbp
      · exact h11
      · exact hcx)
    (by taint_decide) fun a s h => qLoadDigit_ok h)) (RelCT.seq (two_post (Ψ := Q2 e)
      (two_taint [.rdi, .rbx, .r10, .r8, .rbp, .r12] (pins_list qStepVal fun a s h => h.choose_spec.2.1)
        (by taint_decide)) fun a s h => qStepW_ok h) ?_)
  refine RelCT.mono (RelCT.block_append (pin_ct (Ψ := fun _ _ => True) [.rdi] [.rdi, .rbx, .rax] qPosVal
    (pins_list (fun a => qPosVal a) fun a s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
    (by taint_decide) (fun a s h => WP.mono (qPos_ok h.1 h.2.1) fun t ⟨hbx, hax, _, k⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans h.1.rdi
      · exact hbx
      · exact hax)
    (by taint_decide) fun a s h => ?_)) (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨hw, hc, hc1, hcN, h8, hk, e3⟩ := h
  have hZ := hw.hZ
  have h256 := hw.h256
  obtain hW := wW_eq a.1.k
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW a.1.k)
  rw [s16] at hZ
  refine WP.seq (WP.mono (qPos_ok hw hc) fun t ⟨hbx, hax, _, k⟩ => WP.mono (qTail_ok (hw.scr.congr k.2.2)
    ((k.gpr (by decide)).trans hw.rdi) hbx hax hc1 (by omega_arith) (by omega_arith) h256) fun _ _ => trivial)

/-! ## `qDiv`'s setup -/

/-- The divisor's top bit set, for the public data. -/
def FDp (p : RpP) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat

/-- Facts that writes to the arrays and the count keep. -/
abbrev ArrC (F : RpIn → State → Prop) : Prop := Stab F fun y => 256 ≤ y ∨ (200 ≤ y ∧ y < 208)

section
variable {F : RpIn → State → Prop}

theorem ArrC.arr (hF : ArrC F) : Arr F := fun I s t P h hf hP h1 h2 =>
  hF I s t P h hf (fun y hy => ⟨.inl (hP y hy).1, (hP y hy).2⟩) h1 h2

theorem outD {p : RpP} {s t : State} (h : GD wW F p s ∧ FDp p s) {o n : Nat}
    (ho : Outside p.B o n s.mem t.mem) (h256 : 256 ≤ o) (hon : o + n ≤ p.Z)
    (hfar : o + n ≤ slot (wW p.k) qD ∨ slot (wW p.k) qD + 8 * (wW p.k + 2) ≤ o) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Arr F) : GD wW F p t ∧ FDp p t := by
  refine ⟨h.1.out ho h256 hon k hr hF, ?_⟩
  have hn := h.1.ws.scr.nowrap
  have hZ := h.1.ws.hZ
  have kb := h.1.kb
  obtain hW := wW_eq p.k
  obtain e16 := slotE (wW p.k) 16
  obtain eD := slotE (wW p.k) qD
  unfold FDp
  rw [ho.word (by simp only [qD] at *; omega_arith) (by simp only [qD] at *; omega_arith)]
  exact h.2

/-- `GD` after writes to arrays and the count. -/
theorem GD.frmC {p : RpP} {s t : State} (h : GD wW F p s) {rs : List (Nat × Nat)} (hf : Frm p.B rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, (256 ≤ r.1 ∧ r.1 + r.2 ≤ p.Z) ∨ r = (200, 8)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : ArrC F) : GD wW F p t := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  have h256 := h.ws.h256
  obtain hP : ∀ y, (∃ r ∈ rs, r.1 ≤ y ∧ y < r.1 + r.2) → (256 ≤ y ∨ (200 ≤ y ∧ y < 208)) ∧ y < p.Z :=
    fun y ⟨r, hr, h1, h2⟩ => by
      rcases hrs r hr with ⟨a, b⟩ | rfl
      · exact ⟨.inl (by omega_arith), by omega_arith⟩
      · simp only at h1 h2; exact ⟨.inr ⟨h1, h2⟩, by omega_arith⟩
  obtain hf' : FrmP p.B (fun y => ∃ r ∈ rs, r.1 ≤ y ∧ y < r.1 + r.2) s.mem t.mem :=
    FrmP.of_frm hf fun r hr y h1 h2 => ⟨r, hr, h1, h2⟩
  refine h.next hf' (fun y hy => ⟨?_, (hP y hy).2⟩) k hr (fun c hc => ⟨c, ?_⟩)
    fun I e hFI => by subst e; exact hF I s t _ hFI hf' hP k.2.1 k.2.2
  · rcases (hP y hy).1 with a | a
    · exact .inl a
    · unfold DOk; omega_arith
  · unfold mw at hc ⊢
    rw [hf'.word_eq (fun y h1 h2 hy => by
      have := (hP y hy).1; simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

theorem zeroQ_ct {j : Nat} (hj : j < 16) (hjD : j ≠ qD) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8)) zeroAccLoop) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (zeroA j) (Two fun p s => GD wW F p s ∧ FDp p s) :=
  wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => WP.mono (zeroA_ok h.1.ws hj) fun _ ⟨_, o, k⟩ =>
    outD h o (slot_256 _ _) (slot_Z h.1 hj) (by have := slot_far (w := wW p.k) hjD; omega_arith) k (by decide) hF

theorem qSeed_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : Arr F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (qSeed e) (Two fun p s => GD wW F p s ∧ FDp p s) := by
  obtain eq : qSeed e = .seq (.block (ws ++ (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr)))))) copyWords := by
    simp only [qSeed, List.append_assoc]
  rw [eq]
  refine wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => ?_
  rw [← eq]
  have hw := h.1.ws
  obtain L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, h.1.kb.1, he1, he3⟩
  have kb := h.1.kb
  obtain hW := wW_eq p.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  unfold qSeed
  refine WP.seq (WP.mono (qSeedB_ok hw L) fun u ⟨hsi, hbx, h12, mu, ku⟩ => ?_)
  obtain hsu := hw.scr.congr ku.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hsu.ld (by omega_arith)) (fun i hi => hsu.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off p.B (by omega_arith)]; omega_arith)) fun t ⟨_, _, o, k⟩ => ?_
  rw [mu] at o
  exact outD h o (by omega_arith) (by omega_arith) (by omega_arith) (ku.trans k) (by decide) hF

theorem recipQ_ct (hF : Arr F) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s)
      (.seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip)
      (Two fun p s => GD wW F p s ∧ FDp p s) := by
  obtain eq : ws ++ base qD .r10 ++ base qV .r8 ++ hOf = ws ++ (base qD .r10 ++ (base qV .r8 ++ hOf)) := by
    simp only [List.append_assoc]
  rw [eq]
  refine wsG_ct (w := wW) (F := F) (fun _ _ h => h.1) (by taint_decide) fun p s h => ?_
  rw [← eq]
  have hw := h.1.ws
  obtain L : QLay (wW p.k) (wk p.k) 1 := ⟨wW_eq _, h.1.kb.1, by decide, by decide⟩
  have kb := h.1.kb
  obtain hW := wW_eq p.k
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  refine WP.seq (WP.mono (qRcp_ok hw L) fun u ⟨h10, h8', h12, mu, ku⟩ =>
    WP.mono (R2w.recip_ok (hw.scr.congr ku.2.2) h10 h12 h8' (w := wk p.k) (by omega_arith) (by omega_arith)
      (by omega_arith) (by rw [mu]; exact h.2)) fun t ⟨m, k⟩ => ?_)
  rw [mu] at m
  obtain o : Outside p.B (slot (wW p.k) qV) 8 s.mem t.mem := by rw [m]; exact writeW_outside _ _ _ (by omega_arith)
  exact outD h o (by omega_arith) (by omega_arith) (by omega_arith) (ku.trans k) (by decide) hF

theorem qCnt_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) hc).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s)
      (.block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))) (Two fun p s => GD wW F p s ∧ FDp p s) := by
  rw [List.append_assoc]
  refine wsG_block_ct (w := wW) (F := F) (fun _ _ h => h.1) ht fun p s h => ?_
  rw [← List.append_assoc]
  have hw := h.1.ws
  obtain L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, h.1.kb.1, he1, he3⟩
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have h256 := hw.h256
  refine WP.mono (qCnt_ok hw L) fun t ⟨_, m, k⟩ => ⟨h.1.frmC (rs := [(200, 8)]) (by
    rw [m]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [sCt, sFn]; omega_arith)) (List.mem_singleton_self _))
    (fun r hr => .inr (List.mem_singleton.mp hr)) k (by decide) hF, ?_⟩
  have kb := h.1.kb
  obtain hW := wW_eq p.k
  obtain eD := slotE (wW p.k) qD
  unfold FDp
  rw [m, (writeW_outside s.mem p.B _ (by simp only [sCt, sFn]; omega_arith)).word (by simp only [qD] at *; simp only [sCt, sFn]; omega_arith)
    (by simp only [qD] at *; omega_arith)]
  exact h.2

end

/-! ## The division -/

/-- After `qDiv`'s setup: the loop's invariant with `h + e` steps left. -/
def QS (e : Nat) (F : RpIn → State → Prop) (p : RpP) (t : State) : Prop :=
  GD wW F p t ∧ ∃ M, 0 < M ∧ QInv t p.B p.Z (wW p.k) (wk p.k) e M (wk p.k + e) t ∧
    t.gpr .rax = BitVec.ofNat 64 (wk p.k + e) ∧
    2 ^ 63 ≤ (word t.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat ∧
    (word t.mem p.B (slot (wW p.k) qV)).toNat =
      (2 ^ 128 - 1) / (word t.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat - 2 ^ 64

/-- Before step `j` of `qDiv`'s loop. -/
def QL (e : Nat) (F : RpIn → State → Prop) (p : RpP) (j : Nat) (t : State) : Prop :=
  ∃ s₀ M, GD wW F p s₀ ∧ 0 < M ∧
    2 ^ 63 ≤ (word s₀.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat ∧
    (word s₀.mem p.B (slot (wW p.k) qV)).toNat =
      (2 ^ 128 - 1) / (word s₀.mem p.B (slot (wW p.k) qD + 8 * (wk p.k - 1))).toNat - 2 ^ 64 ∧
    QInv s₀ p.B p.Z (wW p.k) (wk p.k) e M (wk p.k + e - j) t

section
variable {F : RpIn → State → Prop}

theorem pos_of_top {m : Mem} {B : Addr} {d h : Nat} (h1 : 1 ≤ h) (hd : 2 ^ 63 ≤ (word m B (d + 8 * (h - 1))).toNat) :
    0 < wv m B d h := by
  have := wv_add m B d (h - 1) 1
  rw [show h - 1 + 1 = h by omega_arith] at this
  simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero] at this
  obtain hp := Nat.two_pow_pos (64 * (h - 1))
  have : 0 < 2 ^ (64 * (h - 1)) * (word m B (d + 8 * (h - 1))).toNat := Nat.mul_pos hp (by omega_arith)
  omega_arith

theorem qLoop_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) :
    RelCT isa (Two (QS e F)) (.loop qBody .ne) (Two (GD wW F)) := by
  refine ct_pre (two_loop (Φ := QL e F) (fun p => wk p.k + e)
    (two_map (fun q => (q.1, wk q.1.k + e - q.2)) (fun q s ⟨hj, s₀, M, g, hM, hd, hv, hI⟩ => ?_) (qBody_ct e))
    fun p j s hj ⟨s₀, M, g, hM, hd, hv, hI⟩ => ?_) fun p s ⟨g, M, hM, hI, ha, hd, hv⟩ =>
      ⟨by omega_arith, s, M, g, hM, hd, hv, by rw [Nat.sub_zero]; exact hI⟩
  · have kb := g.kb
    refine WP.mono (qIter_ok ⟨wW_eq _, kb.1, he1, he3⟩ hI (by omega_arith) (by omega_arith) hM hd hv)
      fun s' ⟨hI', _, hz⟩ => ⟨?_, fun hl => ⟨s₀, M, g, hM, hd, hv, ?_⟩, fun he => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases hl : j + 1 < wk p.k + e
      · rw [decide_eq_true hl, decide_eq_false (by omega_arith)]; rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega_arith)]; rfl
    · rwa [show wk p.k + e - (j + 1) = wk p.k + e - j - 1 by omega_arith]
    · have hn := hI'.ws.scr.nowrap
      have hZ := hI'.ws.hZ
      obtain hW := wW_eq p.k
      obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
      rw [s16] at hZ
      refine g.frmC hI'.frm (fun r hr => ?_) hI'.keep (by simp [mmRegs]) hF
      simp only [qRsAll, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact .inl ⟨by omega_using [sT], by omega_using [sT, hZ, hW]⟩
      · exact .inl ⟨by omega_using [sR], by omega_using [sR, hZ, hW]⟩
      · exact .inl ⟨by omega_using [sV], by omega_using [sV, hZ]⟩
      · exact .inl ⟨by omega_using [sQ], by omega_using [sQ, hZ]⟩
      · exact .inr rfl
  · obtain ⟨p, j⟩ := q
    simp only at hj hd hv hI ⊢
    have kb := g.kb
    exact ⟨hI.ws, kb, he1, he3, hI.cnt, by show 1 ≤ wk p.k + e - j; omega_using [hj], by show wk p.k + e - j ≤ wk p.k + e; omega_using [], by rw [hI.top]; exact hd,
      by rw [hI.recip, hI.top]; exact hv, by rw [hI.rem, hI.dv]; exact Nat.mod_lt _ hM⟩

theorem qPre_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (tS : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) h₁).isSome = true)
    (tC : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) h₂).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (seqs [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))]) (Two (QS e F)) := by
  have hA := hF.arr
  refine two_post ((ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qQ) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qR) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qT) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroQ_ct (j := qV) (by decide) (by decide) hA (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (qSeed_ct e he1 he3 hA tS)
    (ct_cons (List.cons_ne_nil _ _) (recipQ_ct hA) (ct_one (qCnt_ct e he1 he3 hF tC)))))))).mono
      (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  have hw := h.1.ws
  have kb := h.1.kb
  obtain L : QLay (wW p.k) (wk p.k) e := ⟨wW_eq _, kb.1, he1, he3⟩
  refine WP.mono (qPre_ok hw L h.2) fun t ⟨hI, ha, top, rcp, _, _, _, f, k⟩ => ⟨?_, _,
    pos_of_top (by omega_arith) h.2, hI, ha, by rw [top]; exact h.2, rcp⟩
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  obtain hW := wW_eq p.k
  obtain ⟨sA, sQ, sR, sD, sT, sV, s16⟩ := qSlots (wW p.k)
  rw [s16] at hZ
  refine h.1.frmC f (fun r hr => ?_) k (by simp [mmRegs]) hF
  simp only [qDivRs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨by omega_using [sQ], by omega_using [sQ, hZ]⟩
  · exact .inl ⟨by omega_using [sR], by omega_using [sR, hZ]⟩
  · exact .inl ⟨by omega_using [sT], by omega_using [sT, hZ]⟩
  · exact .inl ⟨by omega_using [sV], by omega_using [sV, hZ]⟩
  · exact .inr rfl

/-- `qDiv e`, from the divisor's top bit set. -/
theorem qDiv_ct (e : Nat) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hF : ArrC F) {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (tS : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base qA .rsi ++ (base qR .rbx ++ (hOf ++
      ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .shift .shl .rax 3, .alu .add .rsi (.reg .rax),
        .alu .sub .r12 (.imm 1)] : List Instr))))) copyWords) h₁).isSome = true)
    (tC : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++ ([.mov .rax (.reg .r12),
      .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] : List Instr))) h₂).isSome = true) :
    RelCT isa (Two fun p s => GD wW F p s ∧ FDp p s) (seqs (qDiv e)) (Two (GD wW F)) := by
  have eq : qDiv e = [zeroA qQ, zeroA qR, zeroA qT, zeroA qV, qSeed e,
      .seq (.block (ws ++ base qD .r10 ++ base qV .r8 ++ hOf)) R2Words.recip,
      .block (ws ++ hOf ++ ([.mov .rax (.reg .r12), .alu .add .rax (.imm (BitVec.ofNat 32 e)), .store (hdr sCt) .rax] :
        List Instr))] ++ [.loop qBody .ne] := rfl
  rw [eq]
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (qPre_ct e he1 he3 hF tS tC)
    (ct_one (qLoop_ct e he1 he3 hF))

end

end VG.Proof.Rsa.X86_64.Rd

end

end

/-! ### `Rsa.X86_64.Rd.CTSqrt`, which only this module used -/

section

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the square root

The square root's pieces at the wide width `W = 2 h + 4`. The normalization
by stages, the first digit (its reciprocal needs the digit's top bit, which
`firstA_ok` gives), the digit loop (each step reloads the count, and its
estimate needs the loop's invariant `SqI`, which `stepXE_ok` gives), and the
root's shift by stages. Facts kept in the header: `sZ` a mask (`MZ`), `sK2`
below `2^63` (`MK`), `sC` below 64 (`MC`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Header facts -/

/-- A fact of header word `i`. -/
def HF (i : Nat) (P : BitVec 64 → Prop) (I : RpIn) (s : State) : Prop := P (word s.mem I.B (8 * i))

theorem stab_HF {i : Nat} (hi : i < 32) (P : BitVec 64 → Prop) {Q : Nat → Prop}
    (hQ : ∀ y, Q y → y < 8 * i ∨ 8 * i + 8 ≤ y) : Stab (HF i P) Q :=
  fun _ _ _ _ h hf hP _ _ => by
    unfold HF at h ⊢
    rw [hf.word_eq (fun y h1 h2 hy => by have := hQ y (hP y hy).1; omega_arith) (by omega_arith)]
    exact h

/-- What the square root's pieces write but `zeroX`: the arrays, the mask and
the header slots `sCt`, `sU`, `sB2`, `sC` and `sK2`. -/
def SqW (y : Nat) : Prop := 256 ≤ y ∨ (200 ≤ y ∧ y < 224) ∨ (240 ≤ y ∧ y < 256) ∨ (176 ≤ y ∧ y < 184)

abbrev ArrS (F : RpIn → State → Prop) : Prop := Stab F SqW

theorem stab_mono {F : RpIn → State → Prop} {Q Q' : Nat → Prop} (h : Stab F Q) (hQ : ∀ y, Q' y → Q y) :
    Stab F Q' := fun I s t P hF hf hP h1 h2 => h I s t P hF hf (fun y hy => ⟨hQ y (hP y hy).1, (hP y hy).2⟩) h1 h2

theorem ArrS.arr {F : RpIn → State → Prop} (h : ArrS F) : Arr F := stab_mono h fun _ hy => .inl hy
theorem ArrS.hdr {F : RpIn → State → Prop} (h : ArrS F) {i : Nat}
    (hi : 25 ≤ i ∧ i < 28 ∨ 30 ≤ i ∧ i < 32 ∨ i = 22) : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8 :=
  stab_mono h fun y hy => by unfold SqW; omega_arith
theorem ArrS.and {F G : RpIn → State → Prop} (hF : ArrS F) (hG : ArrS G) : ArrS fun I s => F I s ∧ G I s :=
  Stab.and hF hG

/-- `sZ` a mask. -/
abbrev MZ : RpIn → State → Prop := HF sZ fun v => ∃ b, v = mask b
/-- `sK2` below `2^63`. -/
abbrev MK : RpIn → State → Prop := HF sK2 fun v => v.toNat < 2 ^ 63

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- `GD` after a store to a header slot, with a fact of what was stored. -/
theorem GD.setH {p : RpP} {s t : State} (h : GD w F p s) {i : Nat} (hi : DOk (8 * i)) (hi' : i < 32)
    (hne : i ≠ Impl.Bignum.X86_64.Public.sMask) {P : BitVec 64 → Prop} {v : BitVec 64} (hv : P v)
    (hm : t.mem = s.mem.writeW (off p.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8) :
    GD w (fun I s => F I s ∧ HF i P I s) p t :=
  h.hdrW hm hi hi' k hr (fun e => absurd e hne) fun I e hFI => by
    obtain eB : p.B = I.B := (congrArg RpP.B e).symm
    obtain eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
    have hZ := h.ws.h256
    rw [eB] at hm
    rw [eZ] at hZ
    obtain ⟨a, b'⟩ := stab_writeW hF hZ hi' hFI hm k.2.1 k.2.2
    exact ⟨a, by unfold HF; rw [b']; exact hv⟩

theorem GD.hf {G : RpIn → State → Prop} {i : Nat} {P : BitVec 64 → Prop} {p : RpP} {s : State}
    (h : GD w (fun I s => G I s ∧ HF i P I s) p s) : P (word s.mem p.B (8 * i)) := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, -, hP⟩ := h
  exact hP

theorem GD.wkW {p : RpP} {s : State} (h : GD wW F p s) : wW p.k = 2 * wk p.k + 4 ∧ 8 ≤ wk p.k ∧ wk p.k ≤ 128 :=
  ⟨wW_eq _, h.kb⟩

/-! ## The normalization -/

theorem topX_ct (hF : Arr F) : RelCT isa (Two (GD wW F)) (.block topX) (Two (GD wW F)) := by
  obtain e : topX = ws ++ (base sqZ .rbx ++ ([.mov32 .rax (.imm 0), .store (ix .rbx .r12 (-32)) .rax,
      .store (ix .rbx .r12 (-24)) .rax, .store (ix .rbx .r12 (-16)) .rax, .store (ix .rbx .r12 (-8)) .rax] :
        List Instr)) := by simp only [topX, List.append_assoc]
  rw [e]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨hW, kb⟩ := h.wkW
  have hw := h.ws
  have hn := hw.scr.nowrap
  obtain sl := slot_Z h (j := sqZ) (by decide)
  refine WP.mono (topX_ok hw hW) fun t ⟨hm, k⟩ => h.out (o := slot (wW p.k) sqZ + 8 * (2 * wk p.k)) (n := 32)
    (fun x hx => ?_) (by have := slot_256 (wW p.k) sqZ; omega_arith) (by omega_arith) k (by decide) hF
  rw [hm, writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 3)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 2)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 1)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k)) (by omega_arith) x (by omega_arith)]

/-- The words of `X` or'ed into `rbp`. -/
theorem orX_ct (hF : Arr F) :
    RelCT isa (Two (GD wW F)) (.seq (.block (ws ++ base sqZ .rbx ++ ([.mov32 .rbp (.imm 0)] : List Instr)))
      (wordLoop 0 or1Body)) (Two (GD wW F)) := by
  rw [List.append_assoc]
  refine wsG_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have hw := h.ws
  have hw2 := hw.w2
  have hw1 := hw.w1
  obtain sl := slot_Z h (j := sqZ) (by decide)
  refine WP.seq (WP.mono (orXHd_ok hw) fun u ⟨hbx, _, h12, mu, ku⟩ =>
    WP.mono (or1_ok (hw.scr.congr ku.2.2) hbx h12 (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨_, mt, kt⟩ => h.same (by rw [mt, mu]) (ku.trans kt) (by decide) hF)

theorem zeroX_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) : RelCT isa (Two (GD wW F)) (.block zeroX) (Two (GD wW fun I s => F I s ∧ MZ I s)) := by
  obtain e : zeroX = ws ++ (base sqZ .rbx ++ ([.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .store (hdr sZ) .rbp,
      .mov .rax (.reg .rbp), .alu .and .rax (.imm 1), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
      .mov32 .rax (.imm 0), .store (hdr sK2) .rax] : List Instr)) := by simp only [zeroX, List.append_assoc]
  rw [e]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  obtain sl := slot_Z h (j := sqZ) (by decide)
  obtain s256 := slot_256 (wW p.k) sqZ
  refine WP.mono (zeroX_ok hw (z := s.gpr .rbp = 0) Iff.rfl) fun t ⟨hm, k⟩ => ?_
  obtain hP : ∀ y, (232 ≤ y ∧ y < 240 ∨ slot (wW p.k) sqZ ≤ y ∧ y < slot (wW p.k) sqZ + 8 ∨ 248 ≤ y ∧ y < 256) →
      (SqW y ∨ (232 ≤ y ∧ y < 240)) ∧ y < p.Z := fun y hy => ⟨by unfold SqW; omega_arith, by omega_arith⟩
  obtain hf : FrmP p.B (fun y => 232 ≤ y ∧ y < 240 ∨ slot (wW p.k) sqZ ≤ y ∧ y < slot (wW p.k) sqZ + 8 ∨
      248 ≤ y ∧ y < 256) s.mem t.mem := by
    intro x hx
    simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
    rw [hm, writeW_outside _ _ _ (d := 8 * sK2) (by simp only [sK2, sFn]; omega_arith) x
        (by simp only [sK2, sFn]; omega_arith),
      writeW_outside _ _ _ (d := slot (wW p.k) sqZ) (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (d := 8 * sZ) (by simp only [sZ, sFn]; omega_arith) x (by simp only [sZ, sFn]; omega_arith)]
  refine h.next hf (fun y hy => ⟨?_, (hP y hy).2⟩) k (by decide) (fun c hc => ⟨c, ?_⟩) fun I e hFI => ⟨?_, ?_⟩
  · have := (hP y hy).1; unfold DOk; unfold SqW at this; omega_arith
  · unfold mw at hc ⊢
    rw [hf.word_eq (fun y h1 h2 hy => by simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]
  · subst e
    exact hF I s t _ hFI hf hP k.2.1 k.2.2
  · subst e
    refine ⟨decide (s.gpr .rbp = 0), ?_⟩
    have hz : 8 * sZ = 232 := rfl
    have hk : 8 * sK2 = 248 := rfl
    show word t.mem (pubD I).B (8 * sZ) = _
    rw [hm, (writeW_outside _ _ _ (d := 8 * sK2) (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ _ _ (d := slot (wW (pubD I).k) sqZ) (by omega_arith)).word (by omega_arith) (by omega_arith),
      word_writeW_self]

theorem clzX_ct (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    RelCT isa (Two (GD wW F)) (.block clzX) (Two (GD wW fun I s => F I s ∧ MC I s)) := by
  obtain e : clzX = ws ++ (base sqZ .rbx ++ (([.mov .rdx (.mem (ix .rbx .r12 (-40))), .mov32 .r11 (.imm 0)] : List Instr) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++
      ([.alu .and .r11 (.imm (BitVec.ofInt 32 (-2))), .store (hdr sC) .r11] : List Instr)))) := by
    simp only [clzX, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← e]
    have kb := h.kb
    exact WP.mono (clzX_ok h.ws (by have := wW_eq p.k; omega_arith)) fun _ ⟨hm, k⟩ =>
      h.setC (by omega_arith) hm k (by decide) hFc

theorem testX_ct {c : Nat} (hc1 : 1 ≤ c) (hc128 : c ≤ 128)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) (hw : ∀ p s, GD wW F p s → c ≤ 2 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (seqs (testX c)) (Two (GD wW fun I s => F I s ∧ MB I s)) := by
  obtain e : seqs (testX c) = .seq (.seq (.block (ws ++ (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (wordLoop 0 or1Body)) (.block keepOf) := by
    simp only [testX, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testX_ok h.ws (wW_eq p.k) hc1 (hw p s h) hc128) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

/-- `addK c`: `sK2 := sK2 + c` unless `keep`. -/
theorem addK_ct {c : Nat} (hc128 : c ≤ 128) (hFk : Stab F fun y => 8 * sK2 ≤ y ∧ y < 8 * sK2 + 8)
    (hb : ∀ p s, GD wW F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (addK c)) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (.block (addK c)) (Two (GD wW F)) :=
  two_piece [.rdi] pins_GD ht fun p s h => by
    obtain ⟨b, hb⟩ := hb p s h
    refine WP.mono (addK_ok h.ws hc128 hb (K := (word s.mem p.B (8 * sK2)).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun t ⟨hm, k⟩ => (h.setH (P := fun _ => True) (by unfold DOk; simp only [sK2, sFn]; omega_arith) (by decide)
        (by decide) trivial hm k (by decide) hFk).mono fun _ _ hI => hI.1

/-- A stage of `c` words of the normalization. -/
theorem stageX_ct {c : Nat} (hc1 : 1 ≤ c) (hc128 : c ≤ 128) (hF : ArrS F) {h₀ h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 5)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base sqZ .rsi ++ (base sqT .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi]) (.block (addK c)) h₃).isSome = true) :
    RelCT isa (Two (GD wW F)) (stageX c) (Two (GD wW F)) := by
  unfold stageX
  refine stage_ct (cnd := fun p => decide (2 * wk p.k < c + 1)) hF.arr t₀ (fun p s h => WP.mono
    (stageXHd_ok h.ws (wW_eq p.k) hc128) fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  obtain hG : ArrS fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k := hF.and (stab_const _)
  obtain hGB := arr_mb hG.arr
  refine ct_pre (Ψ := GD wW fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by
      simp only [decide_eq_false_iff_not] at hc; change ¬ 2 * wk I.k < c + 1 at hc; show c + 1 ≤ 2 * wk I.k
      omega_arith⟩
  obtain hwk : ∀ p s, GD wW (fun I s => (F I s ∧ c + 1 ≤ 2 * wk I.k) ∧ MB I s) p s → c + 1 ≤ 2 * wk p.k :=
    fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h; exact hI.2
  obtain hT := testX_ct (F := fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k) hc1 hc128 (hG.hdr (by decide))
    (fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h; have := hI.2; show c ≤ 2 * wk I.k; omega_arith) t₁
  obtain hS := shlWordsF_ct (j := sqZ) (t := sqT) (w := wW) (by decide) (by decide) (by decide) hc128 hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₂
  obtain hK := selK_ct (w := wW) false (j := sqZ) (t := sqT) (by decide) (by decide) (sel_far sqZ sqT (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  obtain hA := addK_ct (F := fun I s => (F I s ∧ c + 1 ≤ 2 * wk I.k) ∧ MB I s) hc128
    ((hG.hdr (by decide)).and (stab_MB fun y hy => by simp only [sK2, sFn] at hy; omega_arith)) (fun _ _ h => h.mb) t₃
  exact ct_post (ct_app (by simp [testX]) (List.cons_ne_nil _ _)
    (ct_app (by simp [testX]) (by simp [shlWords]) hT hS) (ct_cons (List.cons_ne_nil _ _) hK (ct_one hA)))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

theorem arrS_mz {F : RpIn → State → Prop} (hF : ArrS F) : ArrS fun I s => F I s ∧ MZ I s :=
  hF.and (stab_HF (i := sZ) (by decide) _ fun y hy => by unfold SqW at hy; simp only [sZ, sFn]; omega_arith)

theorem stab_mz {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 232 ∨ 240 ≤ y) : Stab MZ Q :=
  stab_HF (i := sZ) (by decide) _ fun y hy => by simp only [sZ, sFn]; exact hQ y hy

theorem stab_mk {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 248 ∨ 256 ≤ y) : Stab MK Q :=
  stab_HF (i := sK2) (by decide) _ fun y hy => by simp only [sK2, sFn]; exact hQ y hy

section
variable {F : RpIn → State → Prop}

theorem normX_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs normX) (Two (GD wW fun I s => (F I s ∧ MZ I s) ∧ MC I s)) := by
  obtain hS : ArrS F := stab_mono hF fun y hy => .inl hy
  obtain hZ := arrS_mz hS
  obtain hSt : ∀ c ∈ 128 :: wordStages, RelCT isa (Two (GD wW fun I s => F I s ∧ MZ I s)) (stageX c)
      (Two (GD wW fun I s => F I s ∧ MZ I s)) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageX_ct (by decide) (by decide) hZ (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  unfold normX
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp)
      (ct_cons (List.cons_ne_nil _ _) (topX_ct hS.arr) (ct_cons (List.cons_ne_nil _ _) (orX_ct hS.arr)
        (ct_one (zeroX_ct hF))))
      (ct_map _ (128 :: wordStages) (List.cons_ne_nil _ _) hSt))
    (ct_cons (List.cons_ne_nil _ _) (clzX_ct (hZ.hdr (by decide)))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := sqZ) (d := sqT) (by decide) (by decide) (by decide) hZ.arr
      (by taint_decide))
    (ct_one (copyA_ct (o := sqZ) (a := sqT) (by decide) (by decide) (by decide) (arr_mc hZ.arr) (by taint_decide)))))

end

/-! ## A digit step, from a public count -/

/-- Before a step's pieces, at count `c` (`a = (p, c)`). -/
def SM (a : RpP × Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z (wW a.1.k) ∧ word s.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2 ∧ 1 ≤ a.2 ∧
    a.2 + 1 ≤ wk a.1.k ∧ wk a.1.k ≤ 128

/-- `winPtrs`' registers. -/
def winVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) sqZ + 16 * (a.2 - 1))
  | .r8 => off a.1.B (slot (wW a.1.k) sqZ + 16 * (a.2 - 1))
  | .r10 => off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1))
  | .r12 => BitVec.ofNat 64 (wk a.1.k - (a.2 - 1) + 2)
  | .r9 => BitVec.ofNat 64 (8 * (wW a.1.k + 2))
  | _ => 0

theorem pins_SM : Pins SM [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi]

theorem winPins_ok {a : RpP × Nat} {s : State} (h : SM a s) :
    WP isa (.block winPtrs) s fun t => ∀ r ∈ [.rdi, .rbx, .r8, .r10, .r12, .r9], t.gpr r = winVal a r := by
  obtain ⟨hw, hc, hc1, hch, -⟩ := h
  refine WP.mono (winPtrs_ok hw (wW_eq _) hc hc1 hch) fun t ⟨hbx, h8, h10, h12, h9, _, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans hw.rdi
  · exact hbx
  · exact h8
  · exact h10
  · exact h12
  · exact h9

/-- The step's pieces from `winPtrs`, which loads the count. -/
theorem win_ct {c₂ : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rbx, .r8, .r10, .r12, .r9]) c₂ hc).isSome = true)
    (hw : ∀ a s, SM a s → WP isa (.seq (.block winPtrs) c₂) s (SM a)) :
    RelCT isa (Two SM) (.seq (.block winPtrs) c₂) (Two SM) :=
  pin_ct [.rdi] [.rdi, .rbx, .r8, .r10, .r12, .r9] winVal pins_SM (by taint_decide) (fun _ _ h => winPins_ok h) ht hw

/-- `SM` after writes within the arrays. -/
theorem SM.frm {a : RpP × Nat} {s t : State} (h : SM a s) {P : Nat → Prop} (hf : FrmP a.1.B P s.mem t.mem)
    (hP : ∀ y, P y → 256 ≤ y) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : SM a t := by
  obtain ⟨hw, hc, hc1, hch, hh⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine ⟨hw.congrP hf (fun y hy => .inl (hP y hy)) k hr, ?_, hc1, hch, hh⟩
  rw [hf.word_eq (fun y h1 h2 hy => by have := hP y hy; simp only [sCt, sFn] at h1 h2; omega_arith)
    (by simp only [sCt, sFn]; omega_arith), hc]

theorem SM.lay {a : RpP × Nat} {s : State} (h : SM a s) :
    slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ≤ slot (wW a.1.k) sqZ + 8 * (wW a.1.k + 2) ∧
    slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16 ≤ slot (wW a.1.k) sqD + 8 * (wW a.1.k + 2) ∧
    256 ≤ slot (wW a.1.k) sqD ∧ slot (wW a.1.k) sqZ + 8 * (wW a.1.k + 2) ≤ a.1.Z ∧
    slot (wW a.1.k) sqD + 8 * (wW a.1.k + 2) ≤ slot (wW a.1.k) sqZ := by
  obtain ⟨hw, hc, hc1, hch, hh⟩ := h
  obtain hW := wW_eq a.1.k
  have hZ := hw.hZ
  rw [slotE] at hZ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [slotE, sqZ, sqD] <;> omega_arith

theorem mulSubX_ct : RelCT isa (Two SM) mulSubX (Two SM) := by
  have e : mulSubX = .seq (.block (winPtrs ++ ([.mov .rcx (.mem (hdr sU)), .store (at0 .r10) .rcx, .mov32 .r9 (.imm 0),
      .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 msBody) := rfl
  rw [e]
  refine RelCT.block_seq (win_ct (by taint_decide) fun a s h => WP.block_seq_iff.mp ?_)
  rw [← e]
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine WP.mono (mulSubX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1 (q := (word s.mem a.1.B (8 * sU)).toNat)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨_, _, o, k⟩ =>
    h.frm (P := fun y => slot (wW a.1.k) sqZ + 16 * (a.2 - 1) ≤ y ∧
      y < slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ∨
      slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 8)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by decide)
  simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [o x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]

theorem two_ct (blk : List Instr) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rbx, .r8, .r10, .r12, .r9]) (.block blk) hc).isSome = true)
    (hok : ∀ a s, SM a s → WP isa (.block (winPtrs ++ blk)) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1))) lo).writeW
        (off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 8)) hi ∧ Keep mmRegs s t) :
    RelCT isa (Two SM) (.block (winPtrs ++ blk)) (Two SM) := by
  refine RelCT.block_append (win_ct ht fun a s h => WP.seq (WP.block_append_iff.mp ?_))
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine WP.mono (hok a s h) fun t ⟨lo, hi, hm, k⟩ =>
    h.frm (P := fun y => slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by simp [mmRegs])
  simp only [not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x
    (by omega_arith)]

theorem toE_ct : RelCT isa (Two SM) (.block toE) (Two SM) :=
  two_ct _ (by taint_decide) fun a s h => WP.mono (toE_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1)
    fun _ ⟨lo, hi, hm, _, k⟩ => ⟨lo, hi, hm, k⟩

theorem updX_ct : RelCT isa (Two SM) (.block updX) (Two SM) :=
  two_ct _ (by taint_decide) fun a s h => WP.mono (updX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1)
    fun _ ⟨lo, hi, hm, _, k⟩ => ⟨lo, hi, hm, k⟩

theorem fixX_ct : RelCT isa (Two SM) fixX (Two SM) := by
  obtain e : fixX = .seq (.seq (.block (winPtrs ++ ([.mov .rax (.mem (ix .rbx .r12 (-8))), .alu .add .rax (.reg .rax),
      .alu .sbb .r15 (.reg .r15), .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 addMBody))
    (.block [.mov .r11 (.reg .r15), .alu .and .r11 (.imm 2), .mov .rax (.mem (at0 .r10)),
      .mov .rdx (.mem { base := .r10, disp := 8 }), .alu .sub .rax (.reg .r11), .alu .sbb .rdx (.imm 0),
      .store (at0 .r10) .rax, .store { base := .r10, disp := 8 } .rdx]) := rfl
  rw [e]
  refine RelCT.assoc' (RelCT.block_seq (win_ct (by taint_decide) fun a s h => ?_))
  obtain hfix := fixX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1
  rw [e] at hfix
  refine WP.block_seq_iff.mp (WP.assoc hfix) |> fun w => WP.mono w fun t ⟨m, _, lo, hi, _, o, hm, _, k⟩ => ?_
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine h.frm (P := fun y => slot (wW a.1.k) sqZ + 16 * (a.2 - 1) ≤ y ∧
      y < slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ∨
      slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by simp [mmRegs])
  simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x
    (by omega_arith), o x (by omega_arith)]

theorem countNext_sm : RelCT isa (Two SM) (.block countNext) (Two fun (_ : RpP × Nat) (_ : State) => True) :=
  two_post (two_taint [.rdi] pins_SM (by taint_decide)) fun _ s h =>
    WP.mono (countNext_ok h.1 h.2.1 h.2.2.1 (by have := h.2.2.2.1; have := h.2.2.2.2; omega_arith)) fun _ _ => trivial

/-- Before a step: the loop's invariant at count `c`. -/
def SE (a : RpP × Nat) (s : State) : Prop :=
  ∃ s₀ X, X < 2 ^ (64 * (2 * wk a.1.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk a.1.k - 1)) ≤ X ∧
    SqI s₀ a.1.B a.1.Z (wW a.1.k) (wk a.1.k) X a.2 s ∧ 1 ≤ a.2 ∧ a.2 + 1 ≤ wk a.1.k ∧ wk a.1.k ≤ 128

theorem SE.sm {a : RpP × Nat} {s : State} (h : SE a s) : SM a s :=
  let ⟨_, _, _, _, hI, h1, h2, h3⟩ := h; ⟨hI.ws, hI.ct, h1, h2, h3⟩

/-- The estimate's registers, from its setup. -/
def estVal (a : RpP × Nat) : Reg → BitVec 64
  | .rsi => off a.1.B (slot (wW a.1.k) sqU)
  | .r11 => off a.1.B (slot (wW a.1.k) sqS)
  | r => winVal a r

theorem estA_ok {a : RpP × Nat} {s : State} (h : SM a s) :
    WP isa (.block (ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs)) s fun t =>
      ∀ r ∈ [.rdi, .rbx, .r8, .r10, .r12, .r9, .rsi, .r11], t.gpr r = estVal a r := by
  obtain ⟨hw, hc, hc1, hch, -⟩ := h
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (base2_ok sqU sqS (r₁ := .rsi) (r₂ := .r11) (w := wW a.1.k) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun s₂ ⟨hsi, h11, m₂, k₂⟩ => ?_
  obtain hw₂ : Ws s₂ a.1.B a.1.Z (wW a.1.k) := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₂, m₁])
    (fun _ f => f.elim) (k₁.trans k₂) (by simp)
  refine WP.mono (winPtrs_ok hw₂ (wW_eq _) (by rw [m₂, m₁, hc]) hc1 hch) fun t ⟨hbx, h8, h10, h12', h9', _, k₃⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k₃.gpr (by decide)).trans hw₂.rdi
  · exact hbx
  · exact h8
  · exact h10
  · exact h12'
  · exact h9'
  · exact (k₃.gpr (by decide)).trans hsi
  · exact (k₃.gpr (by decide)).trans h11

theorem estX_ct : RelCT isa (Two SE) (.block estX) (Two SM) := by
  obtain e : estX = (ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs) ++
      (half .rbx .rsi (-4) 0 ++ half .rbx .rsi (-3) 1 ++ half .rbx .rsi (-2) 2 ++ half .r10 .r11 (-4) 1 ++
      half .r10 .r11 (-3) 2 ++
      ([.mov .rbx (.reg .rsi), .mov .r10 (.reg .r11), .mov .rbp (.reg .r11), .mov32 .r12 (.imm 3)] : List Instr) ++
      R2Words.quot ++ R2Words.refine3 ++ ([.store (hdr sU) .rcx] : List Instr)) := by
    simp only [estX, List.append_assoc]
  rw [e]
  refine RelCT.block_append (pin_ct [.rdi] [.rdi, .rbx, .r8, .r10, .r12, .r9, .rsi, .r11] estVal
    (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.sm.1.rdi, h₂.sm.1.rdi])
    (by taint_decide) (fun _ _ h => estA_ok h.sm) (by taint_decide) fun a s h => WP.seq (WP.block_append_iff.mp ?_))
  rw [← e]
  obtain ⟨s₀, X, hX, hXt, hI, h1, h2, h3⟩ := h
  exact WP.mono (stepXE_ok (wW_eq _) h3 hX hXt h1 h2 hI).2 fun t ⟨hw, hc⟩ => ⟨hw, hc, h1, h2, h3⟩

theorem stepX_ct : RelCT isa (Two SE) stepX fun _ _ => True := by
  change RelCT isa _ (seqs [.block estX, mulSubX, .block toE, fixX, fixX, fixX, .block updX, .block countNext]) _
  exact (ct_cons (List.cons_ne_nil _ _) estX_ct (ct_cons (List.cons_ne_nil _ _) mulSubX_ct
    (ct_cons (List.cons_ne_nil _ _) toE_ct (ct_cons (List.cons_ne_nil _ _) fixX_ct
    (ct_cons (List.cons_ne_nil _ _) fixX_ct (ct_cons (List.cons_ne_nil _ _) fixX_ct
    (ct_cons (List.cons_ne_nil _ _) updX_ct (ct_one countNext_sm)))))))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- What the digit loop writes: the arrays, the count and `sU`. -/
def LW (y : Nat) : Prop := 256 ≤ y ∨ (200 ≤ y ∧ y < 216)

abbrev ArrL (F : RpIn → State → Prop) : Prop := Stab F LW

/-- After the first digit: the loop's invariant at `h - 1`. -/
def SQ0 (G : RpIn → State → Prop) (p : RpP) (t : State) : Prop :=
  GD wW G p t ∧ ∃ X, X < 2 ^ (64 * (2 * wk p.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk p.k - 1)) ≤ X ∧
    SqI t p.B p.Z (wW p.k) (wk p.k) X (wk p.k - 1) t

/-- Before step `j` of the digit loop. -/
def SL (G : RpIn → State → Prop) (p : RpP) (j : Nat) (t : State) : Prop :=
  ∃ s₀ X, GD wW G p s₀ ∧ X < 2 ^ (64 * (2 * wk p.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk p.k - 1)) ≤ X ∧
    SqI s₀ p.B p.Z (wW p.k) (wk p.k) X (wk p.k - 1 - j) t

theorem sqLoop_ct {G : RpIn → State → Prop} (hG : ArrL G) :
    RelCT isa (Two (SQ0 G)) (.loop stepX .ne) (Two (GD wW G)) := by
  refine ct_pre (two_loop (Φ := SL G) (fun p => wk p.k - 1)
    (two_map (fun q => (q.1, wk q.1.k - 1 - q.2)) (fun q s ⟨hj, s₀, X, g, hX, hXt, hI⟩ => ?_) stepX_ct)
    fun p j s hj ⟨s₀, X, g, hX, hXt, hI⟩ => ?_) fun p s ⟨g, X, hX, hXt, hI⟩ =>
      ⟨by have := g.kb; omega_arith, s, X, g, hX, hXt, by rw [Nat.sub_zero]; exact hI⟩
  · have kb := g.kb
    refine WP.mono (stepX_ok (wW_eq _) kb.2 hX hXt (by omega_arith) (by omega_arith) hI)
      fun s' ⟨hz, hI'⟩ => ⟨?_, fun hl => ⟨s₀, X, g, hX, hXt, ?_⟩, fun he => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases hl : j + 1 < wk p.k - 1
      · rw [decide_eq_true hl, decide_eq_false (by omega_arith)]; rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega_arith)]; rfl
    · rwa [show wk p.k - 1 - (j + 1) = wk p.k - 1 - j - 1 by omega_arith]
    · have hn := hI'.ws.scr.nowrap
      have hZ := hI'.ws.hZ
      rw [slotE] at hZ
      obtain hP : ∀ y, SqLP (wW p.k) y → (DOk y ∧ LW y ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < p.Z := fun y hy => by
        unfold SqLP at hy; unfold DOk LW; simp only [slotE, sqS, sqD, sqU, sqZ, sCt, sU, sFn] at hy; omega_arith
      refine g.next hI'.frm (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) hI'.keep (by simp [mmRegs])
        (fun c hc => ⟨c, ?_⟩) fun I e hFI => by
          subst e; exact hG I s₀ s' _ hFI hI'.frm (fun y hy => ⟨(hP y hy).1.2.1, (hP y hy).2⟩) hI'.keep.2.1 hI'.keep.2.2
      unfold mw at hc ⊢
      rw [hI'.frm.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
          simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
        (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

  · obtain ⟨p, j⟩ := q
    have kb := g.kb
    simp only at hj hI kb ⊢
    exact ⟨s₀, X, hX, hXt, hI, by show 1 ≤ wk p.k - 1 - j; omega_arith,
      by show wk p.k - 1 - j + 1 ≤ wk p.k; omega_arith, kb.2⟩

/-! ## The first digit -/

section
variable {G : RpIn → State → Prop}

/-- `GD` after writes to the arrays, the count and `sU`. -/
theorem GD.sqlp {p : RpP} {s t : State} (h : GD wW G p s) (hf : FrmP p.B (SqLP (wW p.k)) s.mem t.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hG : ArrL G) : GD wW G p t := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  obtain hP : ∀ y, SqLP (wW p.k) y → (DOk y ∧ LW y ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < p.Z := fun y hy => by
    unfold SqLP at hy; unfold DOk LW; simp only [slotE, sqS, sqD, sqU, sqZ, sCt, sU, sFn] at hy; omega_arith
  refine h.next hf (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) k hr (fun c hc => ⟨c, ?_⟩) fun I e hFI => by
    subst e; exact hG I s t _ hFI hf (fun y hy => ⟨(hP y hy).1.2.1, (hP y hy).2⟩) k.2.1 k.2.2
  unfold mw at hc ⊢
  rw [hf.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
      simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

/-- The first digit's loop, from `X`'s top two words. -/
theorem isqP_ct (hG : Arr G) :
    RelCT isa (Two (GD wW G)) (.seq (.block (ws ++ base sqZ .rbx ++ ([.mov .r8 (.mem (ix .rbx .r12 (-40))),
      .mov .r9 (.mem (ix .rbx .r12 (-48))), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0), .mov32 .r13 (.imm 0),
      .mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block isqBody) .ne)) (Two (GD wW G)) := by
  rw [List.append_assoc]
  refine wsG_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have kb := h.kb
  obtain hW := wW_eq p.k
  refine WP.seq (WP.mono (firstHd_ok h.ws (by omega_arith)) fun t₄ ⟨h8, h9, h10, h11, h13, hcx, m₄, k₄⟩ => ?_)
  generalize hw5 : word s.mem p.B (slot (wW p.k) sqZ + 8 * (wW p.k - 5)) = w5 at h8
  generalize hw6 : word s.mem p.B (slot (wW p.k) sqZ + 8 * (wW p.k - 6)) = w6 at h9
  have l5 := w5.isLt
  have l6 := w6.isLt
  obtain hT : w5.toNat * 2 ^ 64 + w6.toNat < 2 ^ 128 := by omega_arith
  obtain h8' : t₄.gpr .r8 = BitVec.ofNat 64 ((w5.toNat * 2 ^ 64 + w6.toNat) / 2 ^ 64) := by
    rw [h8, show (w5.toNat * 2 ^ 64 + w6.toNat) / 2 ^ 64 = w5.toNat by omega_arith, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  obtain h9' : t₄.gpr .r9 = BitVec.ofNat 64 ((w5.toNat * 2 ^ 64 + w6.toNat) % 2 ^ 64) := by
    rw [h9, show (w5.toNat * 2 ^ 64 + w6.toNat) % 2 ^ 64 = w6.toNat by omega_arith, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  exact WP.mono (isq_ok hT (isqInv0 (t₀ := t₄) hT h10 h11 h13 h8' h9' hcx rfl (Keep.refl _ _)))
    fun t ⟨_, _, _, _, _, _, m₅, k₅⟩ => h.same (by rw [m₅, m₄]) (k₄.trans k₅) (by decide) hG

/-- The first digit's stores. -/
theorem firstSt_ct (hG : Arr G) :
    RelCT isa (Two (GD wW G)) (.block (ws ++ base sqZ .rbx ++ ([.store (ix .rbx .r12 (-40)) .r11,
      .store (ix .rbx .r12 (-48)) .r13] : List Instr) ++ base sqD .rsi ++ hOf ++ ([.mov .rax (.reg .r10),
      .alu .add .rax (.reg .rax), .store (ix .rsi .r12 (-8)) .rax, .mov .rax (.reg .r10), .shift .shr .rax 63,
      .store (ix .rsi .r12) .rax] : List Instr) ++ base sqS .rsi ++ ([.store { base := .rsi, disp := 16 } .r10] :
        List Instr))) (Two (GD wW G)) := by
  simp only [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  simp only [← List.append_assoc]
  have kb := h.kb
  obtain hW := wW_eq p.k
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  obtain s1 := slotE (wW p.k) sqS
  obtain s8 := slotE (wW p.k) 8
  obtain sD := slotE (wW p.k) sqD
  obtain sZ' := slotE (wW p.k) sqZ
  simp only [sqS, sqD, sqZ] at s1 sD sZ'
  refine WP.mono (firstSt_ok h.ws hW (by omega_arith)) fun t ⟨hm, k⟩ =>
    h.arr (P := fun y => slot (wW p.k) sqS ≤ y ∧ y < slot (wW p.k) 8) ?_
    (fun y hy => ⟨by simp only [sqS] at hy; omega_arith, by simp only [sqS] at hy; omega_arith⟩) k (by decide) hG
  intro x hx
  simp only [sqS, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (d := slot (wW p.k) sqS + 16) (by simp only [sqS]; omega_arith) x
      (by simp only [sqS]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqD + 8 * wk p.k) (by simp only [sqD]; omega_arith) x
      (by simp only [sqD]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqD + 8 * (wk p.k - 1)) (by simp only [sqD]; omega_arith) x
      (by simp only [sqD]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (wW p.k - 6)) (by simp only [sqZ]; omega_arith) x
      (by simp only [sqZ]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (wW p.k - 5)) (by simp only [sqZ]; omega_arith) x
      (by simp only [sqZ]; omega_arith)]

/-- The first digit's top bit set. -/
def FSq (p : RpP) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem p.B (slot (wW p.k) sqS + 8 * (3 - 1))).toNat

/-- The first digit's reciprocal. -/
theorem recipS_ct (hG : Arr G) :
    RelCT isa (Two fun p s => GD wW G p s ∧ FSq p s)
      (.seq (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) R2Words.recip)
      (Two (GD wW G)) := by
  obtain e : ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr) =
      ws ++ (base sqS .r10 ++ (base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) := by simp only [List.append_assoc]
  rw [e]
  refine wsG_ct (w := wW) (F := G) (fun _ _ h => h.1) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.1.ws
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  refine WP.seq (WP.mono (firstRcp_ok hw) fun u ⟨h10, h8, h12, mu, ku⟩ =>
    WP.mono (R2w.recip_ok (hw.scr.congr ku.2.2) h10 h12 h8 (by decide) (by simp only [slotE, sqS]; omega_arith)
      (by simp only [slotE, sqS]; omega_arith) (by rw [mu]; exact h.2)) fun t ⟨m, k⟩ => ?_)
  rw [mu] at m
  obtain o : Outside p.B (slot (wW p.k) sqS) 8 s.mem t.mem := by
    rw [m]; exact writeW_outside _ _ _ (by simp only [slotE, sqS]; omega_arith)
  exact h.1.out o (slot_256 _ _) (by simp only [slotE, sqS]; omega_arith) (ku.trans k) (by decide) hG

theorem ctX_ct (hG : ArrL G) :
    RelCT isa (Two (GD wW G)) (.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr)))
      (Two (GD wW G)) := by
  rw [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have kb := h.kb
  refine WP.mono (ctX_ok h.ws (wW_eq p.k) (by omega_arith)) fun t ⟨hm, k⟩ =>
    h.hdrW hm (by unfold DOk; simp only [sCt, sFn]; omega_arith) (by decide) k (by decide)
      (fun e => absurd e (by decide)) fun I e hGI => ?_
  subst e
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  have hct : 8 * sCt = 200 := rfl
  obtain hf : FrmP (pubD I).B (fun y => 8 * sCt ≤ y ∧ y < 8 * sCt + 8) s.mem t.mem := by
    rw [hm]; exact FrmP.of_writeW _ (by omega_arith) fun _ h1 h2 => ⟨h1, h2⟩
  exact hG I s t _ hGI hf (fun y hy => ⟨by unfold LW; omega_arith, by show y < (pubD I).Z; omega_arith⟩) k.2.1 k.2.2

end

/-- The normalized `X`. -/
def NXv (I : RpIn) (s : State) : Prop :=
  ∃ X, wv s.mem I.B (slot (wW I.k) sqZ) (wW I.k) = X ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk I.k - 1)) ≤ X ∧
    X < 2 ^ (64 * (2 * wk I.k))

section
variable {G : RpIn → State → Prop}

theorem firstX_ct (hG : ArrL G) (hGa : Arr G) :
    RelCT isa (Two (GD wW fun I s => G I s ∧ NXv I s))
      (seqs (firstX ++ ([.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] :
      List (Prog isa))))
      (Two (SQ0 G)) := by
  have e : firstX ++ [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] =
      firstX.take 5 ++ [.seq (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr)))
        R2Words.recip, .block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] := rfl
  obtain weakA : RelCT isa (Two (GD wW G)) (seqs (firstX.take 5)) (Two (GD wW G)) :=
    ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqD) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqS) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqU) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (isqP_ct hGa) (ct_one (firstSt_ct hGa)))))
  obtain inner : RelCT isa (Two (GD wW fun I s => G I s ∧ NXv I s)) (seqs (firstX.take 5))
      (Two fun p s => GD wW G p s ∧ FSq p s) :=
    two_post ((ct_pre weakA fun p s h => h.mono fun _ _ h => h.1).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun p s h => by
        obtain ⟨I, m₀, e', h', L, O, he, hm, hGI, X, hX, hXt, hXh⟩ := id h
        subst e'
        have kb : 8 ≤ wk I.k := h.kb.1
        obtain hW := wW_eq I.k
        refine WP.mono (firstA_ok h'.ws hW (by omega_arith) (top_pair hW (by omega_arith) hX hXh)
          (top_pair_lo (by omega_arith) hXt)) fun t ⟨_, f, k, top⟩ =>
            ⟨(h.mono fun _ _ h => h.1).sqlp f k (by simp [mmRegs]) hG, top⟩
  refine two_post ?_ fun p s h => ?_
  · rw [e]
    exact (ct_app (by simp [firstX]) (List.cons_ne_nil _ _) inner (ct_cons (List.cons_ne_nil _ _) (recipS_ct hGa)
      (ct_one (ctX_ct hG)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  · obtain ⟨I, m₀, e', h', L, O, he, hm, hGI, X, hX, hXt, hXh⟩ := id h
    subst e'
    have kb : 8 ≤ wk I.k := h.kb.1
    refine WP.mono (sqInit_ok h'.ws (wW_eq _) (by omega_arith) hX hXt hXh) fun t ⟨hI, f, k⟩ =>
      ⟨(h.mono fun _ _ h => h.1).sqlp f k (by simp [mmRegs]) hG, X, hXh, hXt, hI⟩

end

/-! ## The root's shift -/

/-- `[o] := [j] / 2`, for what it changes. -/
theorem shrTo_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j o : Nat} (hj : j < 16) (ho : o < 16)
    (hjo : j ≠ o) :
    WP isa (.seq (.block (ws ++ base j .r8 ++ base o .rsi)) (wordLoop 0 shrBody)) s fun s' =>
      Outside B (slot w o) (8 * w) s.mem s'.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  obtain sj := h.sl hj
  obtain so := h.sl ho
  obtain pj := slot_sep (w := w) hjo
  have hw1 := h.w1
  have hw2 := h.w2
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j o (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (shr_ok (h.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨_, ho', k₃⟩ => ?_
  rw [m₂, m₁] at ho'
  exact ⟨ho', ((k₁.trans k₂).trans k₃).mono (by simp)⟩

section
variable {G : RpIn → State → Prop}

theorem halfA_ct {t j : Nat} (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base t .rsi))
      (wordLoop 0 shrBody)) hc).isSome = true) :
    RelCT isa (Two (GD wW G)) (halfA t j) (Two (GD wW G)) := by
  obtain e : halfA t j = .seq (.block (ws ++ (base j .r8 ++ base t .rsi))) (wordLoop 0 shrBody) := by
    simp only [halfA, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) htc fun p s h => by
    rw [← e]
    exact WP.mono (shrTo_frm h.ws hj ht hjt) fun _ ⟨o, k⟩ =>
      h.out o (slot_256 _ _) (by have := slot_Z h ht; omega_arith) k (by decide) hG

/-- The facts the root's shift keeps. -/
abbrev G1 (F : RpIn → State → Prop) : RpIn → State → Prop := fun I s => ((F I s ∧ MZ I s) ∧ MK I s) ∧ MC I s

theorem G1.arrL {F : RpIn → State → Prop} (hF : ArrS F) : ArrL (G1 F) :=
  ((((stab_mono hF fun y hy => by unfold LW at hy; unfold SqW; omega_arith)).and
    (stab_mz fun y hy => by unfold LW at hy; omega_arith)).and (stab_mk fun y hy => by unfold LW at hy; omega_arith)).and
    (stab_MC fun y hy => by unfold LW at hy; omega_arith)

theorem G1.arr {F : RpIn → State → Prop} (hF : ArrS F) : Arr (G1 F) :=
  stab_mono (G1.arrL hF) fun _ hy => .inl hy

theorem g1_facts {F : RpIn → State → Prop} {p : RpP} {s : State} (h : GD wW (G1 F) p s) :
    (∃ b, word s.mem p.B (8 * sZ) = mask b) ∧ (word s.mem p.B (8 * sK2)).toNat < 2 ^ 63 ∧
      ∃ z, z < 64 ∧ word s.mem p.B (8 * sC) = BitVec.ofNat 64 z := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, ⟨⟨⟨-, hz⟩, hk⟩, hc⟩⟩ := h
  exact ⟨hz, hk, hc⟩

theorem kBlk_ct {F : RpIn → State → Prop} (hF : ArrS F) :
    RelCT isa (Two (GD wW (G1 F))) (.block [.mov .rax (.mem (hdr sK2)), .mov .rdx (.reg .rax), .shift .shr .rax 1,
      .store (hdr sK2) .rax, .alu .and .rdx (.imm 1), .shift .shl .rdx 5, .mov .rax (.mem (hdr sC)),
      .shift .shr .rax 1, .alu .add .rax (.reg .rdx), .store (hdr sC) .rax]) (Two (GD wW (G1 F))) :=
  two_piece [.rdi] pins_GD (by taint_decide) fun p s h => by
    obtain ⟨-, hK, z, hz, hc⟩ := g1_facts h
    have hn := h.ws.scr.nowrap
    have hZ := h.ws.hZ
    rw [slotE] at hZ
    have e2 : 8 * sK2 = 248 := rfl
    have e3 : 8 * sC = 240 := rfl
    refine WP.mono (kBlk_ok h.ws hK hz (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) hc) fun t ⟨hm, k⟩ => ?_
    generalize (word s.mem p.B (8 * sK2)).toNat = K at hK hm
    obtain hf : FrmP p.B (fun y => 240 ≤ y ∧ y < 256) s.mem t.mem := by
      intro x hx
      simp only [not_and_or, Nat.not_le, Nat.not_lt] at hx
      rw [hm, writeW_outside _ _ _ (d := 8 * sC) (by omega_arith) x (by omega_arith),
        writeW_outside _ _ _ (d := 8 * sK2) (by omega_arith) x (by omega_arith)]
    refine h.next hf (fun y hy => ⟨by unfold DOk; omega_arith, by omega_arith⟩) k (by decide)
      (fun c hc => ⟨c, by unfold mw at hc ⊢; rw [hf.word_eq (fun y h1 h2 hy => by
        simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
        (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]⟩) fun I e hI => ?_
    subst e
    obtain ⟨⟨⟨hFI, hZI⟩, -⟩, -⟩ := hI
    refine ⟨⟨⟨hF I s t _ hFI hf (fun y hy => ⟨by unfold SqW; omega_arith, by show y < (pubD I).Z; omega_arith⟩)
      k.2.1 k.2.2, stab_mz (Q := fun y => 240 ≤ y ∧ y < 256) (fun y hy => by omega_arith) I s t _ hZI hf
      (fun y hy => ⟨hy, by show y < (pubD I).Z; omega_arith⟩) k.2.1 k.2.2⟩, ?_⟩, ?_⟩
    · show (word t.mem (pubD I).B (8 * sK2)).toNat < 2 ^ 63
      rw [hm, (writeW_outside _ _ _ (d := 8 * sC) (by omega_arith)).word (by omega_arith) (by omega_arith),
        word_writeW_self, BitVec.toNat_ofNat]
      omega_arith
    · refine ⟨z / 2 + 32 * (K % 2), by omega_arith, ?_⟩
      show word t.mem (pubD I).B (8 * sC) = _
      rw [hm, word_writeW_self]

/-- `sB2 := ` the mask of `K`'s bit `c` clear. -/
theorem kSel_ct {c : Nat} (hc : c < 2 ^ 31) {F : RpIn → State → Prop} (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hK : ∀ p s, GD wW F p s → (word s.mem p.B (8 * sK2)).toNat < 2 ^ 63)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax]) hc').isSome = true) :
    RelCT isa (Two (GD wW F)) (.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax])
      (Two (GD wW fun I s => F I s ∧ MB I s)) :=
  two_piece [.rdi] pins_GD ht fun p s h =>
    WP.mono (kSel_ok h.ws (hK p s h) hc (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun _ ⟨hm, k⟩ =>
      h.setB hm k (by decide) hFb

/-- A stage of `c` words of the root's shift. -/
theorem stageR_ct {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) {F : RpIn → State → Prop} (hF : ArrS F)
    {h₀ h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 4)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sK2)),
      .alu .and .rax (.imm (BitVec.ofNat 32 c)), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
      .store (hdr sB2) .rax]) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base sqR .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++
        base sqT .rbx)))) copyWords) h₂).isSome = true) :
    RelCT isa (Two (GD wW (G1 F))) (stageR c) (Two (GD wW (G1 F))) := by
  unfold stageR
  obtain hA := G1.arr hF
  refine stage_ct (cnd := fun p => decide (wW p.k < c + 4)) hA t₀ (fun p s h => WP.mono
    (stageRHd_ok h.ws (by omega_arith)) fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  obtain hG : Arr fun I s => G1 F I s ∧ c + 4 ≤ wW I.k := hA.and (stab_const _)
  obtain hGB := arr_mb hG
  refine ct_pre (Ψ := GD wW fun I s => G1 F I s ∧ c + 4 ≤ wW I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by
      simp only [decide_eq_false_iff_not] at hc; change ¬ wW I.k < c + 4 at hc; show c + 4 ≤ wW I.k; omega_arith⟩
  obtain hK := kSel_ct (F := fun I s => G1 F I s ∧ c + 4 ≤ wW I.k) (c := c) (by omega_arith)
    (((((stab_mono hF fun y hy => by unfold SqW; simp only [sB2, sFn] at hy; omega_arith).and
      (stab_mz fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and
      (stab_mk fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and
      (stab_MC fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and (stab_const _))
    (fun p s h => (g1_facts (GD.mono h fun _ _ h => h.1)).2.1) t₁
  obtain hS := shrWords_ct (j := sqR) (t := sqT) (w := wW) (by decide) (by decide) (by decide) hc64 hGB
    (fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h; have := hI.2; show c + 1 ≤ wW I.k; omega_arith)
    (by taint_decide) t₂
  obtain hSel := selK_ct (w := wW) false (j := sqR) (t := sqT) (by decide) (by decide) (sel_far sqR sqT (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  exact ct_post (ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp [shrWords]) (ct_one hK) hS) (ct_one hSel))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

section
variable {F : RpIn → State → Prop}

theorem lastR_ct (hF : ArrS F) :
    RelCT isa (Two (GD wW (G1 F))) (.block (ws ++ base sqR .rbx ++ ([.mov .rax (.mem (hdr sZ)), .alu .and .rax (.imm 1),
      .mov .rdx (.mem (at0 .rbx)), .alu .sub .rdx (.reg .rax), .store (at0 .rbx) .rdx] : List Instr)))
      (Two (GD wW (G1 F))) := by
  rw [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  obtain ⟨⟨b, hb⟩, -⟩ := g1_facts h
  have hn := h.ws.scr.nowrap
  obtain sl := slot_Z h (j := sqR) (by decide)
  refine WP.mono (lastR_ok h.ws hb) fun t ⟨hm, k⟩ => ?_
  obtain o : Outside p.B (slot (wW p.k) sqR) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  exact h.out o (slot_256 _ _) (by omega_arith) k (by decide) (G1.arr hF)

theorem finishX_ct (hF : ArrS F) : RelCT isa (Two (GD wW (G1 F))) (seqs finishX) (Two (GD wW (G1 F))) := by
  obtain hA := G1.arr hF
  obtain hS : ∀ c ∈ wordStages, RelCT isa (Two (GD wW (G1 F))) (stageR c) (Two (GD wW (G1 F))) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageR_ct (by decide) (by decide) hF (by taint_decide) (by taint_decide) (by taint_decide)
  obtain hM : Stab (G1 F) fun y => 176 ≤ y ∧ y < 184 :=
    (((stab_mono hF fun y hy => by unfold SqW; omega_arith).and (stab_mz fun y hy => by omega_arith)).and
      (stab_mk fun y hy => by omega_arith)).and (stab_MC fun y hy => by omega_arith)
  unfold finishX
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp [wordStages])
      (ct_cons (List.cons_ne_nil _ _) (orX_ct hA) (ct_cons (List.cons_ne_nil _ _) (andZero_ct hM)
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqR) (by decide) hA (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (halfA_ct (t := sqR) (j := sqD) (by decide) (by decide) (by decide) hA
        (by taint_decide)) (ct_one (kBlk_ct hF))))))
      (ct_map _ wordStages (by simp [wordStages]) hS))
    (ct_cons (List.cons_ne_nil _ _) (shrZ_ct (a := sqR) (d := sqT) (G := fun I s => (F I s ∧ MZ I s) ∧ MK I s)
      (by decide) (by decide) (by decide) ((hF.arr.and (stab_mz fun y hy => .inr (by omega_arith))).and (stab_mk fun y hy => .inr (by omega_arith)))
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := sqR) (a := sqT) (by decide) (by decide) (by decide) hA
      (by taint_decide)) (ct_one (lastR_ct hF))))

end

section
variable {F : RpIn → State → Prop}

/-- `normX`, with what it establishes. -/
theorem normXs_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs normX) (Two (GD wW fun I s => G1 F I s ∧ NXv I s)) := by
  refine two_post ((normX_ct hF).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  obtain ⟨I, m₀, e, h', L, O, he, hm, hFI⟩ := id h
  subst e
  have kb : 8 ≤ wk I.k ∧ wk I.k ≤ 128 := h.kb
  have hn := h'.ws.scr.nowrap
  have hZ := h'.ws.hZ
  rw [slotE] at hZ
  refine WP.mono (normX_ok h'.ws (wW_eq I.k) (by omega_arith) kb.2 rfl)
    fun t ⟨C, z, _, hz64, hC, hX, hlo, hhi, hK, hzC, hZm, f, k, hw⟩ => ?_
  obtain hP : ∀ y, NxP (wW I.k) y → (DOk y ∧ (SqW y ∨ (232 ≤ y ∧ y < 240)) ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < I.Z :=
    fun y hy => by unfold NxP at hy; unfold DOk SqW; simp only [slotE, sqT] at hy; omega_arith
  refine h.next (F' := fun I s => G1 F I s ∧ NXv I s) f (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) k
    (by simp [mmRegs]) (fun c hc => ⟨c, ?_⟩) fun J e hFJ => ?_
  · unfold mw at hc ⊢
    show word t.mem I.B _ = _
    rw [f.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
        simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)]
    exact hc
  · have eB : J.B = I.B := congrArg RpP.B e
    obtain eK : J.k = I.k := congrArg RpP.k e
    obtain eZ : J.Z = I.Z := congrArg RpP.Z e
    refine ⟨⟨⟨⟨hF J s t _ hFJ (by rw [eB]; exact f) (fun y hy => ⟨(hP y hy).1.2.1, by rw [eZ]; exact (hP y hy).2⟩)
      k.2.1 k.2.2, ?_⟩, ?_⟩, z, hz64, ?_⟩,
      Xn (wv s.mem I.B (slot (wW I.k) sqZ) (wW I.k)) (wk I.k) * 2 ^ (64 * C) * 2 ^ z, ?_, ?_, ?_⟩
    · show ∃ b, word t.mem J.B (8 * sZ) = mask b
      rw [eB, hZm]; exact ⟨_, rfl⟩
    · show (word t.mem J.B (8 * sK2)).toNat < 2 ^ 63
      rw [eB, hK, BitVec.toNat_ofNat]; omega_arith
    · show word t.mem J.B (8 * sC) = _; rw [eB, hzC]
    · rw [eB, eK]; exact hX
    · rw [eK]; exact hlo
    · rw [eK]; exact hhi
end

/-- The square root, at the wide width. -/
theorem sqrt_ct {F : RpIn → State → Prop} (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs RecoverDet.sqrt) (Two (GD wW (G1 F))) := by
  obtain hS : ArrS F := stab_mono hF fun y hy => .inl hy
  obtain e : RecoverDet.sqrt = normX ++ ((firstX ++ [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1),
      .store (hdr sCt) .r12] : List Instr))]) ++ ([.loop stepX .ne] ++ finishX)) := by
    simp only [RecoverDet.sqrt, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  exact ct_app (by simp [normX]) (by simp) (normXs_ct hF)
    (ct_app (by simp) (by simp) (firstX_ct (G1.arrL hS) (G1.arr hS))
      (ct_cons (by simp [finishX]) (sqLoop_ct (G1.arrL hS)) (finishX_ct hS)))

end VG.Proof.Rsa.X86_64.Rd

end

end

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time but for `n` and `e`

`main`, piece by piece (`main_ct`), then the entry, the modulus' check and
the failure path (`rdCode_ct`), and the contract's `ConstantTime`
(`rdCode_constantTime`). The pieces' runs agree from `GD`, whose facts are
those of the header the pieces need; `divA`'s division needs its divisor
normalized, which the correctness of what precedes it gives (`pre3_ok`,
`divA12_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## `e`'s length for the wide products -/

/-- `e`'s length `4 W - 8` in the header. -/
def FE (I : RpIn) (s : State) : Prop :=
  word s.mem I.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (4 * wW I.k - 8)

theorem stab_FE {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 160 ∨ 168 ≤ y) : Stab FE Q :=
  stab_hdr (i := Impl.Bignum.X86_64.Public.sElen) (by decide) (fun I => BitVec.ofNat 64 (4 * wW I.k - 8))
    (fun y hy => by have := hQ y hy; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith)

abbrev FT : RpIn → State → Prop := fun _ _ => True

theorem gr_ct {w : Nat → Nat} {F : RpIn → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (GD w F)) c Q) : RelCT isa (Two (GR w F)) c Q :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ h => h

theorem drop_ct {w : Nat → Nat} {F G : RpIn → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (GD w G)) c Q) (hFG : ∀ I s, F I s → G I s) : RelCT isa (Two (GD w F)) c Q :=
  h.mono (fun _ _ h => two_mono (fun _ _ h => h.mono fun I _ => hFG I _) h) fun _ _ h => h

theorem setEl_ct : RelCT isa (Two (GD wW FT)) (.block setEl) (Two (GD wW FE)) :=
  two_post (two_taint [.rdi] pins_GD (by taint_decide)) fun p s h =>
    WP.mono (hdr_gd (i := Impl.Bignum.X86_64.Public.sElen)
      (by unfold DOk; simp only [Impl.Bignum.X86_64.Public.sElen, sFn]; omega_arith) (by decide) (by decide)
      (fun p => BitVec.ofNat 64 (4 * wW p.k - 8)) stab_true
      (fun p s h => WP.mono (setEl_ok h.ws) fun t ⟨hm, k⟩ => ⟨hm, _, k, by decide⟩) p s h)
      fun _ ht => ht.mono fun _ _ hI => hI.2

/-! ## The stages -/

theorem arrT : Arr FT := stab_true
theorem arrE : Arr FE := stab_FE fun y hy => .inr (by omega_arith)
theorem mskT : Stab FT fun y => 176 ≤ y ∧ y < 184 := stab_true
theorem mskE : Stab FE fun y => 176 ≤ y ∧ y < 184 := stab_FE fun y hy => .inr (by omega_arith)
theorem widT : Stab FT fun y => 48 ≤ y ∧ y < 128 ∨ 224 ≤ y ∧ y < 232 := stab_true
theorem deMinus_ct : RelCT isa (Two (GD wW FT)) (seqs deMinus) (Two (GD wW FT)) :=
  ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 1) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (setOneA_ct (j := 1) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 2) (a := 5) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskT))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 3) (a := 2) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_one (gr_ct (andZero_ct mskT)))))))

theorem twosInit_ct : RelCT isa (Two (GD nv FT)) (seqs twosInit) (Two (GD nv FT)) :=
  ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 6) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 6) (a := 4) (by decide) (by decide) (by decide) arrT
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 7) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 7) (a := 0) (b := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (zeroA_ct (j := 12) (by decide) arrT (by taint_decide)))
    (ct_one (zeroA_ct (j := 13) (by decide) arrT (by taint_decide)))))))

theorem hZ26 {F : RpIn → State → Prop} (p : RpP) (s : State) (h : GD nv F p s) : slot (nv p.k) 26 ≤ p.Z := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  exact (rd_bounds L.k1 L.k2 L.z).2.1

theorem hw20 {F : RpIn → State → Prop} (p : RpP) (s : State) (h : GD nv F p s) : nv p.k < 2 ^ 20 := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  exact (rd_bounds L.k1 L.k2 L.z).2.2.1

theorem prodE_ct : RelCT isa (Two (GD wW FE)) (seqs Recover.prod) (Two (GD wW FE)) :=
  prod_ct arrE (fun p => 4 * wW p.k - 8) fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hE⟩ := h
    exact ⟨hE, by show 1 ≤ 4 * (2 * (wk I.k + 1) + 2) - 8; omega_arith, by omega_arith⟩

theorem prod1_ct : RelCT isa (Two (GD nv F1)) (seqs Recover.prod) (Two (GD nv F1)) :=
  prod_ct arr_F1 RpP.el fun p s h => by
    obtain ⟨I, m₀, rfl, -, L, -, -, -, ha, -⟩ := h
    exact ⟨ha.el, L.el1, by have := L.el2; show I.el ≤ 8 * nv I.k; unfold nv wk; omega_arith⟩

/-! ## Before `divA` -/

/-- From a valid modulus. -/
def GMv (p : RpP) (s : State) : Prop :=
  ∃ I : RpIn, pubD I = p ∧ RpPre I s ∧ I.el ≤ 8 ∧ Spec.Rsa.modulusValid I.N I.k = true

theorem preA_ct [InvLaw] : RelCT isa (Two GM) (seqs (p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))))) (Two (GD wW FT)) := by
  have e : p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))) = [.block RecoverDet.head] ++
      ((loadA Impl.Bignum.X86_64.Public.aN Impl.Bignum.X86_64.Public.sN Impl.Bignum.X86_64.Public.sK ++
        ([zeroA 1] ++ (loadA Recover.aE Impl.Bignum.X86_64.Public.sE Impl.Bignum.X86_64.Public.sElen ++
        loadA Recover.aD Recover.sD Recover.sDl))) ++ (Recover.prod ++ ([.block (width true)] ++
      (deMinus ++ ([.block (width false)] ++ (twosInit ++ (twos ++ ([gcdW 6 12 7] ++
      [.block (width true)])))))))) := by
    simp only [p1, p2, List.append_assoc]
  rw [e]
  have ne : ∀ {a : Prog isa} {l : List (Prog isa)}, [a] ++ l ≠ [] := List.cons_ne_nil _ _
  exact ct_app ne (by simp [loadA]) (ct_one head_ct) (ct_app (by simp [loadA]) (by simp [Recover.prod])
    loads_ct (ct_app (by simp [Recover.prod]) ne prod1_ct
    (ct_app ne (by simp [deMinus]) (ct_one (drop_ct (width_ct true widT (by taint_decide)) fun _ _ _ => trivial))
    (ct_app (by simp [deMinus]) ne deMinus_ct
    (ct_app ne (by simp [twosInit]) (ct_one (width_ct false widT (by taint_decide)))
    (ct_app (by simp [twosInit]) (by simp [twos, wordStages]) twosInit_ct
    (ct_app (by simp [twos, wordStages]) ne (twos_ct arrT stab_true)
    (ct_cons ne (gcdW_ct (iU := 6) (iV := 12) (iM := 7) hZ26 hw20 (by decide) (by decide)
      (by decide) arrT (by taint_decide))
      (ct_one (width_ct true widT (by taint_decide)))))))))))

/-- What `divA`'s first parts need: `n`, `g` and `x` (wide). -/
def FA (I : RpIn) (s : State) : Prop :=
  (∃ G X, wv s.mem I.B (slot (wW I.k) 0) (wW I.k) = I.N ∧ wv s.mem I.B (slot (wW I.k) 6) (wW I.k) = G ∧
    G < 2 ^ (64 * (wk I.k + 1)) ∧ wv s.mem I.B (slot (wW I.k) 2) (wW I.k) = X) ∧
  2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧ I.N < 2 ^ (64 * wk I.k)

theorem preA_ok [InvLaw] : RelCT isa (Two GMv) (seqs (p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa))))) (Two (GD wW FA)) :=
  two_post ((ct_pre preA_ct fun _ _ ⟨I, e, h, hel, _⟩ => ⟨I, e, h, hel⟩).mono (fun _ _ h => h)
    fun _ _ _ => trivial) fun p s ⟨I, e, h, hel, hv⟩ => by
      obtain ⟨-, hNk, hNlo, -⟩ := rd_nums h.L hel hv
      exact WP.mono (pre3_ok h hel hv) fun t ⟨m₀, G, X, S, hm, n, g, gl, x⟩ =>
        ⟨I, m₀, e, S, h.L, h.outs, hel, hm, ⟨G, X, n, g, gl, x⟩, hNlo, hNk⟩

/-! ## `divA` -/

/-- `e`'s length and `sC`. -/
abbrev FEC : RpIn → State → Prop := fun I s => FE I s ∧ MC I s

theorem arrEC : ArrC FEC :=
  (stab_FE fun y hy => by omega_arith).and (stab_MC fun y hy => by omega_arith)

theorem divAp_ct : RelCT isa (Two (GD wW FA))
    (seqs (([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod ++
      ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] : List (Prog isa)))) (Two fun p s => GD wW FEC p s ∧ FDp p s) := by
  have hC : Arr FEC := arrEC.arr
  have weak : RelCT isa (Two (GD wW FT)) (seqs ([.block setEl, copyA 8 6, copyA 9 2] ++ Recover.prod ++
      [.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9])) (Two (GD wW FEC)) :=
    ct_app (by simp) (List.cons_ne_nil _ _)
      (ct_app (List.cons_ne_nil _ _) (by simp [Recover.prod]) (ct_cons (List.cons_ne_nil _ _) setEl_ct
        (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 8) (a := 6) (by decide) (by decide) (by decide) arrE
          (by taint_decide))
        (ct_one (copyA_ct (o := 9) (a := 2) (by decide) (by decide) (by decide) arrE (by taint_decide)))))
        prodE_ct)
      (ct_cons (List.cons_ne_nil _ _) (clzTop_ct (j := 0) (by decide)
        (stab_FE fun y hy => by simp only [sC, sFn] at hy; omega_arith)
        (fun p s h => by have := h.kb; have := wW_eq p.k; omega_arith) (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 8) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 0) (d := 8) (by decide) (by decide) (by decide) arrE
        (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 9) (by decide) hC (by taint_decide))
      (ct_one (shlZ_ct (a := 10) (d := 9) (by decide) (by decide) (by decide) arrE (by taint_decide)))))))
  refine two_post ((ct_pre weak fun p s h => h.mono fun _ _ _ => trivial).mono (fun _ _ h => h)
    fun _ _ _ => trivial) fun p s h => ?_
  obtain ⟨I, m₀, e, h', L, O, he, ⟨c, hm⟩, ⟨G, X, hN, hG, hGv, hX⟩, hNlo, hNhi⟩ := id h
  subst e
  have kb : 8 ≤ wk I.k := h.kb.1
  have hnw := h'.ws.scr.nowrap
  have hZ := h'.ws.hZ
  rw [slotE] at hZ
  refine WP.mono (divA12_ok h'.ws (wW_eq I.k) kb hN hNlo hNhi hG hGv hX) fun t ⟨top, ⟨z, hz, hzC⟩, el, mm, f, k, hw⟩ =>
    ⟨h.next (F' := FEC) f (fun y hy => ⟨?_, ?_⟩) k (by simp [mmRegs]) (fun c' hc' => ⟨c', by show mw t.mem I.B = _; rw [mm]; exact hc'⟩)
      fun J e' _ => ?_, top⟩
  · unfold DaP at hy; unfold DOk; simp only [slotE] at hy; omega_arith
  · unfold DaP at hy; simp only [slotE] at hy; show y < I.Z; omega_arith
  · have eB : J.B = I.B := congrArg RpP.B e'
    have eK : J.k = I.k := congrArg RpP.k e'
    refine ⟨?_, z, hz, ?_⟩
    · show word t.mem J.B _ = _; rw [eB, el, eK]
    · show word t.mem J.B _ = _; rw [eB, hzC]

theorem divAr_ct : RelCT isa (Two (GD wW FEC)) (seqs [zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11])
    (Two (GD wW FEC)) := by
  have hC : Arr FEC := arrEC.arr
  exact ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 6) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shrZ_ct (a := 12) (d := 6) (by decide) (by decide) (by decide) arrE
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 14) (a := 11) (b := 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (andNz_ct ((stab_FE fun y hy => by omega_arith).and
      (stab_MC fun y hy => by omega_arith)))
    (ct_one (copyA_ct (o := 7) (a := 11) (by decide) (by decide) (by decide) hC (by taint_decide))))))

/-! ## `divB` -/

theorem gd_fd {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD wW (fun I s => G I s ∧ FD I s) p s) :
    GD wW G p s ∧ FDp p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hG, hd⟩ := h
  exact ⟨⟨I, m₀, rfl, h', L, O, he, hm, hG⟩, hd⟩

theorem divB_ct : RelCT isa (Two (GD wW FEC)) (seqs divB) (Two (GD wW FEC)) := by
  have hC : Arr FEC := arrEC.arr
  have hMk : Stab FEC fun y => 176 ≤ y ∧ y < 184 :=
    (stab_FE fun y hy => by omega_arith).and (stab_MC fun y hy => by omega_arith)
  unfold divB
  exact ct_app (by simp [qDiv, normDN]) (List.cons_ne_nil _ _)
    (ct_app (by simp [qDiv, normDN]) (by simp [eqA])
    (ct_app (by simp [qDiv, normDN]) (List.cons_ne_nil _ _)
    (ct_app (by simp [normDN]) (by simp [qDiv])
    (ct_app (List.cons_ne_nil _ _) (by simp [normDN, wordStages])
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 5) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 5) (a := 0) (b := 6) (by decide) (by decide) (by decide)
        (by decide) (by decide) hC (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (gr_ct (zeroA_ct (j := 2) (by decide) hC (by taint_decide)))
      (ct_one (addA_ct (o := 2) (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide) hC
        (by taint_decide))))))
      (ct_post (ct_pre (normDN_ct (F := FE) arrE (stab_FE fun y hy => by simp only [sB2, sFn] at hy; omega_arith)
        (stab_FE fun y hy => by simp only [sC, sFn] at hy; omega_arith)) fun _ _ h => h.mono fun _ _ h => h.1)
        fun _ _ h => h))
    (ct_pre (qDiv_ct (F := FEC) 1 (by decide) (by decide) arrEC (by taint_decide) (by taint_decide))
      fun _ _ h => gd_fd h))
    (ct_one (zeroA_ct (j := 3) (by decide) hC (by taint_decide))))
    (eqA_ct (a := 12) (b := 3) (by decide) (by decide) hC (by taint_decide)))
    (ct_cons (List.cons_ne_nil _ _) (andZero_ct hMk)
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 4) (by decide) hC (by taint_decide))
    (ct_one (addA_ct (o := 4) (a := 11) (b := 1) (by decide) (by decide) (by decide) (by decide) (by decide) hC
      (by taint_decide)))))

/-! ## `b² - 4 n`, its square root, the factors -/

theorem minus4n_ct : RelCT isa (Two (GD wW FE)) (seqs minus4n) (Two (GD wW FE)) :=
  ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := 8) (a := 4) (by decide) (by decide) (by decide) arrE
        (by taint_decide))
      (ct_one (copyA_ct (o := 9) (a := 4) (by decide) (by decide) (by decide) arrE (by taint_decide))))
      (prodB_ct arrE fun p s h => by
        obtain ⟨I, m₀, rfl, -, -, -, -, -, hE⟩ := h
        show word s.mem I.B _ = BitVec.ofNat 64 (8 * nv I.k)
        rw [hE]; congr 1; simp only [wW]; omega_arith))
    (ct_cons (List.cons_ne_nil _ _) (shlA_ct (fun _ _ h => h) false (j := 0) (by decide) arrE
      (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlA_ct (fun _ _ h => h.1) false (j := 0) (by decide) arrE
      (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (subA_ct (t := 12) (a := 10) (b := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) arrE (by taint_decide)))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskE))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 13) (a := 12) (b := 1) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrE (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (gr_ct (andZero_ct mskE))
    (ct_one (copyA_ct (o := 7) (a := 12) (by decide) (by decide) (by decide) arrE (by taint_decide)))))))))

theorem p4_ct : RelCT isa (Two (GD wW FEC)) (seqs p4) (Two (GD nv FT)) :=
  ct_app (by simp [minus4n]) (by simp [RecoverDet.sqrt, normX]) (ct_pre minus4n_ct fun _ _ h => h.mono fun _ _ h => h.1)
    (ct_app (by simp [RecoverDet.sqrt, normX]) (List.cons_ne_nil _ _)
      (sqrt_ct (F := FE) (stab_FE fun y hy => by unfold SqW at hy; omega_arith))
      (ct_one (drop_ct (G := G1 FE) (width_ct false ((((stab_FE fun y hy => by omega_arith).and
        (stab_mz fun y hy => by omega_arith)).and (stab_mk fun y hy => by omega_arith)).and
        (stab_MC fun y hy => by omega_arith)) (by taint_decide)) fun _ _ h => h) |>.mono
          (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.mono fun _ _ _ => trivial) h))

theorem factors_eq : factors = [zeroA 10, addA 10 8 4, shrA 10, zeroA 11, subA 11 8 4, shrA 11] ++
    (storeA 10 Recover.sP Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
    (storeA 11 Recover.sQ Impl.Bignum.X86_64.Public.sK Impl.Bignum.X86_64.Public.sMask ++
    ([.block retMask] : List (Prog isa)))) := by
  simp only [factors, List.append_assoc]

theorem factors_ct : RelCT isa (Two (GD nv FT)) (seqs factors) fun _ _ => True := by
  rw [factors_eq]
  exact RelCT.seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (RelCT.seq
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 10) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (addA_ct (o := 10) (a := 8) (b := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shrA_ct (j := 10) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 11) (by decide) arrT (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (subA_ct (t := 11) (a := 8) (b := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) arrT (by taint_decide))
    (ct_one (gr_ct (shrA_ct (j := 11) (by decide) arrT (by taint_decide)))))))))
    (stores_ct.mono (fun _ _ h => two_mono (fun _ _ h => GD.gt h) h) fun _ _ h => h))

theorem factorsT_ct : RelCT isa (Two (GD nv FT)) (seqs factors) (Two fun (_ : RpP) (_ : State) => True) :=
  factors_ct.mono (fun _ _ h => h) fun _ _ _ => ⟨(default : RpP), trivial, trivial⟩

/-! ## `main` -/

theorem main_split : RecoverDet.main = seqs ((p1 ++ (p2 ++ ([.block (width true)] : List (Prog isa)))) ++
    ((([.block setEl, copyA 8 6, copyA 9 2] : List (Prog isa)) ++ Recover.prod ++
      ([.block (clzTop 0), zeroA 8, shlZ 0 8, zeroA 9, shlZ 10 9] : List (Prog isa))) ++ (qDiv 3 ++ (([zeroA 6, shrZ 12 6, subA 14 11 0, .block andNz, copyA 7 11] : List (Prog isa)) ++
    (divB ++ (p4 ++ factors)))))) := by
  rw [main_eq]
  simp only [p1, p2, p3, p4, divA, List.append_assoc, List.cons_append, List.nil_append]

/-- `main` leaks the same in two runs with the same public data, from a valid modulus. -/
theorem main_ct [InvLaw] : RelCT isa (Two GMv) RecoverDet.main fun _ _ => True := by
  rw [main_split]
  exact (ct_app (by simp) (by simp) preA_ok (ct_app (by simp) (by simp [qDiv]) divAp_ct
    (ct_app (by simp [qDiv]) (List.cons_ne_nil _ _) (qDiv_ct (F := FEC) 3 (by decide) (by decide) arrEC
      (by taint_decide) (by taint_decide))
    (ct_app (List.cons_ne_nil _ _) (by simp [divB]) divAr_ct
    (ct_app (by simp [divB]) (by simp [minus4n]) divB_ct
    (ct_app (by simp [minus4n]) (by simp [factors]) p4_ct
      factorsT_ct)))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The code -/

/-- A state the contract allows, with the public data `p`. -/
def RDRel (p : RpP) (s : State) : Prop := rdContract.pre s ∧ pubD (rpIn s) = p

/-- After `entry`'s first instruction. -/
def RD1 (p : RpP) (t : State) : Prop :=
  ∃ s, RDRel p s ∧ t.gpr .r11 = p.B ∧ t.gpr .rsp = p.sp ∧
    WP isa (.block ((Recover.entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
      .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))])) t (RpHeadPost s)

/-- After `entry` and the reloads. -/
def RD2 (p : RpP) (t : State) : Prop := ∃ s, RDRel p s ∧ RpHeadPost s t

/-- After the modulus' check. -/
def RD3 (p : RpP) (t : State) : Prop :=
  ∃ s t₁, RDRel p s ∧ RpHeadPost s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.k)

/-- `RecoverDet.code` leaks the same in runs that agree on the public data. -/
theorem rdCode_ct [InvLaw] : RelCT isa (Two RDRel) RecoverDet.code fun _ _ => True := by
  unfold RecoverDet.code
  refine RelCT.seq (R := Two RD3) (RelCT.block_append (RelCT.seq (R := Two RD2) ?_ ?_)) ?_
  · rw [rpEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := RD1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (congrArg RpP.sp h₁.2).trans (congrArg RpP.sp h₂.2).symm) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := rpCtx_of (rd_rp hs.1).1
    have hh : WP isa (.block (([.mov .r11 (.mem { base := .rsp, disp := 40 })] : List Instr) ++
        ((Recover.entry.drop 1) ++ [.mov .rdx (.mem (hdr Impl.Bignum.X86_64.Public.sN)),
          .mov .rcx (.mem (hdr Impl.Bignum.X86_64.Public.sK))]))) s (RpHeadPost s) := by
      rw [← rpEntry_split]; exact rpHead_ok' c
    have e4 : s.gpr .rsp + BitVec.ofInt 64 40 = stackArgAddr s 4 := rfl
    have hB' : s.mem.readW (stackArgAddr s 4) 64 = stackArg s 4 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 4)
      (by xrun [State.ea, e4, c.ha 4 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans (congrArg RpP.B hs.2), (k.gpr (by decide)).trans (congrArg RpP.sp hs.2), hw⟩
  -- The modulus' check.
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx]
        exact (congrArg RpP.pN c₁.2).trans (congrArg RpP.pN c₂.2).symm
      · rw [h₁.rcx, h₂.rcx]
        exact congrArg (BitVec.ofNat 64) ((congrArg RpP.k c₁.2).trans (congrArg RpP.k c₂.2).symm))
      (by taint_decide) ?_
    rintro p t ⟨s, hs, h⟩
    have c := rpCtx_of (rd_rp hs.1).1
    have hnb := c.n.congrK h.inScr h.keep
    have hnl : (rpIn s).nb.length = (s.gpr .r9).toNat := bytesAt_length _ _ _
    refine WP.mono (invalid_ok h.rdx h.rcx c.L.k1 c.L.k2 hnl (fun i hi => hnb.rd i (by rw [hnl]; exact hi))
      (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
    rw [hz, ← hs.2]
    rfl
  -- `fail` or `main`.
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁⟩ ⟨_, _, _, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_
  · exact Rp.failR_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ => by
      have hpre := rpPre_of (rpCtx_of (rd_rp hs.1).1) h hm k
      have L := hpre.L
      have O := hpre.outs
      exact ⟨fk (rpIn s), hs.2, hpre.scr, hpre.rdi, hpre.args, hpre.wr,
        ⟨L.k1, L.k2, L.el1, L.el2, L.dl1, L.dl2, L.nbl, L.ebl, List.length_replicate, L.z⟩,
        ⟨O.p, O.q, O.sp, O.sq, O.a⟩⟩) h)
      fun _ _ h => h
  · exact main_ct.mono (fun _ _ h => two_mono (fun p t ⟨⟨s, t₁, hs, h, hm, k, z⟩, hc⟩ =>
      ⟨rpIn s, hs.2, rpPre_of (rpCtx_of (rd_rp hs.1).1) h hm k, (rd_rp hs.1).2, by
        simp only [eval, z, Option.map_some, Option.some.injEq, Bool.not_eq_false'] at hc
        rw [← hs.2] at hc
        exact hc⟩) h) fun _ _ h => h

/-- `vg_rsa_recover_primes_det` is constant time but for `n` and `e`. -/
theorem rdCode_constantTime [InvLaw] : ConstantTime isa rdContract.pre rdContract.pub RecoverDet.code := by
  refine RelCT.constantTime (rdCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pubD (rpIn s₁), ⟨h₁, rfl⟩, ⟨h₂, ?_⟩⟩)
    fun _ _ h => h)
  obtain ⟨hr, a0, a1, a2, a3, a4, a5, hn, he⟩ := hp
  have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
  have w₁ := h₁.1.2.2.1
  have w₂ := h₂.1.2.2.1
  simp only [pubD, fk, RpIn.pub, rpIn, RpP.mk.injEq]
  refine ⟨a4.symm, by rw [a5], by rw [r .r9 (by decide)], by rw [a1], by rw [a3], r .rdi (by decide),
    r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, hn.symm, he.symm, ?_, r .rsp (by decide)⟩
  rw [w₁, w₂, r .rdi (by decide), r .rsi (by decide), r .rdx (by decide), r .rcx (by decide), a4, a5]

end VG.Proof.Rsa.X86_64.Rd

end

end

/-!
# `vg_rsa_recover_primes_det` on x86-64: verified against the shared contract

`rdContract` states the shared contract on the registers and the stack
(`rd_implies`); with correctness (`rdCode_correct`) and constant time
(`rdCode_constantTime`), `RecoverDet.code` is verified (`rd_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- A state meeting `rdContract.pre`: a 512-bit modulus, one-byte exponents,
and the stack arguments at `0x6008`. -/
def rpSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1100 | .rcx => 64 | .r8 => 0x2000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6030 then 0x20
    else if a = 0x6009 then 0x30 else if a = 0x6010 then 1 else if a = 0x6019 then 0x31
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x80 else if a = 0x6031 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6008, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8448⟩]

theorem rd_implies : rdContract.Implies (Spec.Rsa.recoverPrimesDetContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | (simp only [Spec.Rsa.lenValid] at *; omega_arith)
  post := by sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract,
    stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, stackArgs_six,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, h9])
    refine ⟨?_, a0, a1, a2, a3, a4, a5, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract,
    rpPre, stackArgs_six, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

/-- `vg_rsa_recover_primes_det`, given that its code never loads MXCSR (which
the registration file evaluates). -/
theorem rd_verified [InvLaw] (hmx : RecoverDet.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct (rdCode_correct hmx) rdCode_constantTime rd_implies

end VG.Proof.Rsa.X86_64.Rd
