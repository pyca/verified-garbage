module

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ControllerFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! # A complete native p-search body, including controller entry and return -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pAttempt_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash} {p : PPrimalityPlan}
    (hG : Calls.StreamOK (if p.construct.hash.len = 20 then G1 else G256).stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.construct.hash.len = 20 then G1 else G256).D = p.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {C : Addr} {counter stride used : Nat}
    (entry : AttemptEntry p.construct H W s) (ctrl : SearchControl C counter stride s)
    (hoff : 1 + counter * stride = p.construct.hash.offset)
    (hbase : p.construct.hash.W 5 + BitVec.ofNat 64 control = C)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.construct.hash.len) bs).length = 8 * p.construct.hash.len)
    (hused : p.construct.hash.W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.length)
    (htape : Src s p.construct.B p.construct.Z p.rp p.rand)
    (htapeFrame : (⟨p.rp, p.rand.length⟩ : Region).Disjoint ⟨p.construct.hash.F, frameBytes⟩)
    (hA : Scr s (p.construct.hash.W 5) domainCheck)
    (htc : Covers [⟨p.rp, p.rand.length⟩] (s.rd ++ s.wr))
    (hcontrol : ∀ r ∈ ⟨p.construct.hash.F, frameBytes⟩ :: p.changed, (⟨C, 24⟩ : Region).Disjoint r)
    (hframeControl : (⟨p.construct.hash.F, frameBytes⟩ : Region).Disjoint ⟨C, 24⟩)
    (hhashControl : (⟨p.construct.hash.S, oRsa⟩ : Region).Disjoint ⟨C, 24⟩)
    (hpControl : (⟨VG.Proof.Bignum.off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p, p.construct.len⟩ : Region).Disjoint ⟨C, 24⟩)
    (heControl : (⟨VG.Proof.Bignum.off (p.construct.hash.W 5) exponent, p.construct.len⟩ : Region).Disjoint ⟨C, 24⟩) :
    WP isa (Impl.Dsa.AArch64.Generation.pAttempt G1 G256 T.run p.construct.len p.construct.hash.len) s fun t =>
      SearchControl C counter stride t ∧
      ∃ (used' : Nat) (status : BitVec 64) (V : Nat → Byte),
        used' ≤ p.rand.length ∧ Lay t p.construct.hash.F p.construct.hash.S ∧
        Rep t.mem p.construct.hash.F p.construct.hash.S V
          (upd (upd p.construct.hash.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        VG.Proof.Bignum.word t.mem C 16 = status ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.construct.len =
          Spec.Dsa.encodeBE p.construct.len p.construct.value ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.construct.hash.W 5) exponent) p.construct.len =
          Spec.Dsa.encodeBE p.construct.len ((p.construct.value - 1) / Spec.Rsa.os2ip p.construct.qb) ∧
        (p.result used = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, p.result used = some (b, rest) →
          status = BitVec.ofNat 64 (if b then 1 else 3) ∧ used' = p.rand.length - rest.length) ∧
        Frame (⟨C, 24⟩ :: ⟨p.construct.hash.F, frameBytes⟩ :: p.changed) s.mem t.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.pAttempt
  refine WP.seq (WP.mono (attemptEntry_ok entry ctrl.x0 (ctrl.scr.ld (by decide))
    (by rw [ctrl.offset, hoff])) fun u ⟨stateU, fu, ku⟩ => ?_)
  have tape := source_of_frame htape fu (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact htapeFrame) p.randMax ku.rd ku.wr
  refine WP.seq (WP.mono (pConstructTest_ok (G := if p.construct.hash.len = 20 then G1 else G256) hG hHh hsize T hd stateU hhash hseedsize hused
    hu tape (hA.congr ku.wr) (by rw [ku.rd, ku.wr]; exact htc)) fun v hv => ?_)
  obtain ⟨used', status, V, hvused, Lv, Rv, vp, ve, hexhaust, hres, fv, rdv, wrv⟩ := hv
  have total : Frame (⟨p.construct.hash.F, frameBytes⟩ :: p.changed) s.mem v.mem :=
    (fu.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)).trans
      (fv.mono (fun r hr => List.mem_cons_of_mem _ hr))
  have hcount := controller_word_of_frame total hcontrol (d := 0) (by decide)
  have hoffset := controller_word_of_frame total hcontrol (d := 8) (by decide)
  have sv := ctrl.scr.congr (wrv.trans ku.wr)
  refine WP.mono (searchReturn_ok Lv Rv (by simpa [upd] using hbase) (sv.st (by decide)))
    fun t ⟨hdi, hstatus, ft, kt⟩ => ?_
  have ff : Frame [⟨C, 24⟩] v.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨C, 24⟩ (by simp)
    change ¬ ofs C a < 24 at hn
    omega
  have Rt := rep_of_disjoint_frame Rv ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hframeControl)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hhashControl)
  have Lt := lay_of_rep Lv Rv Rt rfl kt.sp kt.wr
  have hlen : p.construct.len ≤ 2 ^ 64 := by rcases p.construct.width with hh | hh | hh <;> omega
  refine ⟨⟨sv.congr kt.wr, hdi, ?_, ?_⟩, used', status, V, hvused, Lt, Rt,
    by simpa [upd] using hstatus, ?_, ?_, hexhaust, hres, ?_,
    kt.rd.trans (rdv.trans ku.rd), kt.wr.trans (wrv.trans ku.wr)⟩
  · rw [ft.word (d := 0) (Or.inl (by decide)) (by decide), hcount, ctrl.count]
  · rw [ft.word (d := 8) (Or.inl (by decide)) (by decide), hoffset, ctrl.offset]
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hpControl) hlen, vp]
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact heControl) hlen, ve]
  · exact (total.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans
      (ff.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp))

end VG.Proof.Dsa.AArch64.Generation
