module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PPrimalityPlan
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory

/-! ### `Dsa.AArch64.Generation.PAttempt`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.ControllerFrame`, which only this module used -/

section

/-! # Preserve the counter and offset while a native candidate is evaluated -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Bignum

theorem controller_word_of_frame {m m' : Mem} {C : Addr} {rs : List Region} {d : Nat}
    (hf : Frame rs m m') (hsep : ∀ r ∈ rs, (⟨C, 24⟩ : Region).Disjoint r) (hd : d + 8 ≤ 24) :
    VG.Proof.Bignum.word m' C d = VG.Proof.Bignum.word m C d := by
  have sub : Region.Sub ⟨VG.Proof.Bignum.off C d, 8⟩ ⟨C, 24⟩ := Offset.sub_base C hd
  exact hf.readW (Region.contains_self _ _) (fun r hr a ha hb => hsep r hr a (sub a ha) hb) (by decide)

end VG.Proof.Dsa.AArch64.Generation

end

end


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
    omega_using [hn]
  have Rt := rep_of_disjoint_frame Rv ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hframeControl)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hhashControl)
  have Lt := lay_of_rep Lv Rv Rt rfl kt.sp kt.wr
  have hlen : p.construct.len ≤ 2 ^ 64 := by rcases p.construct.width with hh | hh | hh <;> omega_using [hh]
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

end

end


/-! # The complete p body returns the persistent state needed by its next iteration -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.AArch64

def SearchPlan.candidate (p : SearchPlan) (counter : Nat) : Nat :=
  Spec.Dsa.pCandidate (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed
    (1 + counter * (p.attempt.construct.hash.count + 1))

def SearchPlan.stepResult (p : SearchPlan) (counter used : Nat) : Option (Bool × List Byte) :=
  if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then some (false, p.attempt.rand.drop used)
  else Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used)

theorem searchBody_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256).stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {counter used : Nat} (h : SearchMemory p W s)
    (ctrl : SearchControl p.C counter (p.attempt.construct.hash.count + 1) s)
    (hc : counter < 32 * p.attempt.construct.len)
    (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.pAttempt G1 G256 T.run
      p.attempt.construct.len p.attempt.construct.hash.len) s fun t =>
      SearchControl p.C counter (p.attempt.construct.hash.count + 1) t ∧
      ∃ (W' : Nat → BitVec 64) (used' : Nat) (status : BitVec 64),
        SearchMemory p W' t ∧ used' ≤ p.attempt.rand.length ∧ W' 16 = BitVec.ofNat 64 used' ∧
        W' 19 = status ∧ VG.Proof.Bignum.word t.mem p.C 16 = status ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
          Spec.Dsa.encodeBE p.attempt.construct.len (p.candidate counter) ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
          Spec.Dsa.encodeBE p.attempt.construct.len ((p.candidate counter - 1) / Spec.Rsa.os2ip p.attempt.construct.qb) ∧
        (p.stepResult counter used = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, p.stepResult counter used = some (b, rest) →
          status = BitVec.ofNat 64 (if b then 1 else 3) ∧ used' = p.attempt.rand.length - rest.length) ∧
        Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let offset := 1 + counter * (p.attempt.construct.hash.count + 1)
  have carry : offset + p.attempt.construct.hash.count < 2 ^ 32 := by
    have hcmax : counter < 12288 := by rcases p.attempt.construct.width with hh | hh | hh <;> omega_using [hc, hh]
    have hmul := Nat.mul_le_mul_left counter (show p.attempt.construct.hash.count + 1 ≤ 12 by
      have := p.attempt.construct.hash.count_le; omega_using [this])
    dsimp only [offset]
    omega_using [p.attempt.construct.hash.count_le, hcmax, hmul]
  let call := h.attemptPlan offset carry
  have h5 := h.slots 5 (by simp [searchSlots])
  have cw5 : call.construct.hash.W 5 = p.attempt.construct.hash.W 5 := by
    simpa [SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe,
      attemptWords, upd, call] using h5
  have clen : call.construct.len = p.attempt.construct.len := rfl
  have cF : call.construct.hash.F = p.attempt.construct.hash.F := rfl
  have changed : call.changed = p.attempt.changed := by
    dsimp only [call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed, HashPlan.changed]
    simp only [attemptWords, upd, ite_false, show ¬ (5 : Nat) = 25 by decide,
      show ¬ (5 : Nat) = 2 by decide, show ¬ (5 : Nat) = 0 by decide, h5]
  refine WP.mono (pAttempt_ok (p := call) hG hHh hsize T hd (h.entry offset carry H)
    ctrl rfl (by rw [cw5]; exact p.controlBase) hhash hseedsize
    (by simpa [call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, attemptWords, upd] using hused) hu h.tape
    (by
      change (⟨p.attempt.rp, p.attempt.rand.length⟩ : Region).Disjoint ⟨p.attempt.construct.hash.F, frameBytes⟩
      exact p.tapeSeparate _ (by simp [searchWrites]))
    (by rw [cw5]; exact h.arena) h.tapeCover
    (by rw [changed]; exact p.controlSeparate) p.frameControl p.hashControl
    (by simpa only [cw5, clen] using p.pControl) (by simpa only [cw5, clen] using p.exponentControl))
    fun t ⟨ct, Wused, status, V, bound, Lt, Rt, htstatus, bp, be, he, hr, ft, rdt, wrt⟩ => ?_
  have ff : Frame (searchWrites p.attempt p.C) s.mem t.mem := by
    change Frame (⟨p.C, 24⟩ :: ⟨p.attempt.construct.hash.F, frameBytes⟩ :: p.attempt.changed) s.mem t.mem
    simpa only [changed, cF] using ft
  let W' := upd (upd call.construct.hash.W 16 (BitVec.ofNat 64 Wused)) 19 status
  have memory : SearchMemory p W' t := h.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    dsimp only [W', call, SearchMemory.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upd, attemptWords]) ff rdt wrt
  refine ⟨ct, W', Wused, status, memory, bound, by simp [W', upd], by simp [W', upd], htstatus,
    ?_, ?_, he, hr, ff, rdt, wrt⟩
  · rw [cw5] at bp
    exact bp
  · rw [cw5] at be
    exact be

end VG.Proof.Dsa.AArch64.Generation
