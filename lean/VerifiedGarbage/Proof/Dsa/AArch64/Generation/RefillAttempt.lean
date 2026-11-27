module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSeed
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSearch
import VerifiedGarbage.Proof.Dsa.Generation.SearchDomain
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorCall
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Proof.Framework.AArch64.ModeSim
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Subgroup
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

/-! ### `Dsa.AArch64.Generation.SearchStable`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchLoop`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchAdvance`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchStatus`, which this module and modules that import it used -/

section

/-! # Status handling and termination test of the native p search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchStatus_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.pSearchStatus status)) s fun t =>
      SearchControl B counter stride t ∧ word t.mem B 16 = BitVec.ofNat 64 status ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.x3] s t := by
  have hst := h.scr.st (d := 16) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off B 16) (BitVec.ofNat 64 status)) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatus, h.x0,
      hdr_enc (by decide : 2 < 32), hst]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hv]) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 16 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ⟨⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, ?_, ?_⟩,
    by rw [hm, word_writeW_self], ho, hk⟩
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.count
  · rw [ho.word (Or.inl (by decide)) (by decide)]; exact h.offset

theorem searchStatusCmp_ok {s : State} {B : Addr} {counter stride status : Nat}
    (h : SearchControl B counter stride s) (hv : status ≤ 3)
    (hstat : word s.mem B 16 = BitVec.ofNat 64 status) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchStatusCmp) s fun t =>
      eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    eval (.zero .x .x3) t = some (decide (status = 3)) ∧ t.mem = s.mem) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchStatusCmp, h.x0,
      hdr_enc (by decide : 2 < 32), h.scr.ld (d := 16) (by decide), hstat, eval]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add]
    change BitVec.ofNat 64 status = (3#64) ↔ status = 3
    constructor
    · intro he
      have hn := congrArg BitVec.toNat he
      change status % 2 ^ 64 = 3 at hn
      rwa [Nat.mod_eq_of_lt (by omega_using [hv] : status < 2 ^ 64)] at hn
    · intro he; subst status; rfl) rfl rfl rfl) fun t ⟨⟨hz, hm⟩, hk⟩ => ⟨hz, hm, hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The p search advances exactly one counter and one hash stride -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchAdvance_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearchAdvance limit stride) s fun t =>
      SearchControl B (counter + 1) stride t ∧
      word t.mem B 16 = BitVec.ofNat 64 (if counter + 1 < limit then 3 else 2) ∧
      Outside B 0 24 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x7] s t := by
  unfold Impl.Dsa.AArch64.Generation.pSearchAdvance
  refine WP.seq (WP.mono (searchAdvanceHead_ok h hc hl hs) fun u ⟨hu, hflag, ho, hk⟩ => ?_)
  refine WP.ite (decide (counter + 1 < limit)) (by
    by_cases he : counter + 1 < limit
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_right (show ¬ limit ≤ counter + 1 by omega_using [he]), decide_eq_true he]; rfl
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_left (show limit ≤ counter + 1 by omega_using [he]), decide_eq_false he]; rfl) (fun hyes => ?_) (fun hno => ?_)
  · have hlt : counter + 1 < limit := of_decide_eq_true hyes
    refine WP.mono (searchStatus_ok hu (by decide : 3 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hlt, ite_true] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩
  · have hge : ¬ counter + 1 < limit := of_decide_eq_false hno
    refine WP.mono (searchStatus_ok hu (by decide : 2 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hge, ite_false] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩

theorem searchInit_ok {s : State} {B : Addr} (h : Scr s B 24) (hdi : s.gpr .x0 = B) (stride : Nat) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchInit) s fun t =>
      SearchControl B 0 stride t ∧ Outside B 0 16 s.mem t.mem ∧ Keep [.x3] s t := by
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 0)).writeW (off B 8) (BitVec.ofNat 64 1)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = m) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchInit, hdi,
      hdr_enc (by decide : 0 < 32), hdr_enc (by decide : 1 < 32),
      h.st (d := 0) (by decide), h.st (d := 8) (by decide)]; rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.congr hk.wr, (hk.gpr _ (by decide)).trans hdi, ?_, ?_⟩, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm, Nat.zero_mul, Nat.add_zero]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Total correctness of the bounded native candidate-search loop

The payload invariant describes the candidate and witness tape; the
controller owns only its three words. Each rejected candidate advances
exactly once, including the final rejection at the attempt limit.
-/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Payload facts survive changes confined to the controller and its two
volatile registers. The payload must not include the controller words. -/
def SearchPayload (B : Addr) (P : State → Prop) : Prop :=
  ∀ {s t}, P s → Outside B 0 24 s.mem t.mem → Keep [.x3, .x4, .x5, .x7] s t → P t

theorem SearchControl.congr {s t : State} {B : Addr} {counter stride : Nat}
    (h : SearchControl B counter stride s) (hm : t.mem = s.mem) (hk : Keep [.x3] s t) :
    SearchControl B counter stride t :=
  ⟨h.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.x0, hm ▸ h.count, hm ▸ h.offset⟩

/-- One candidate body may finish or request the next attempt. An exhausted
attempt budget is a distinct terminal outcome handled by `done`. -/
theorem searchIteration_ok {body : Prog isa} {B : Addr} {limit stride counter : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hc : counter < limit) (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearchIteration body limit stride) s fun t =>
      (eval (.zero .x .x3) t = some false ∧ Q t) ∨
      (eval (.zero .x .x3) t = some true ∧ I (counter + 1) t ∧
        SearchControl B (counter + 1) stride t ∧ counter + 1 < limit) := by
  unfold Impl.Dsa.AArch64.Generation.pSearchIteration
  simp only [Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (body_ok counter s hc hi h) fun u ⟨hu, status, hv, hstat, hp⟩ => ?_)
  refine WP.seq (WP.mono (searchStatusCmp_ok hu hv hstat) fun v ⟨hz, hm, hk⟩ => ?_)
  have hvctrl := hu.congr hm hk
  have hframe : Outside B 0 24 u.mem v.mem := by rw [hm]; exact Outside.refl _ _ _ _
  by_cases hretry : status = 3
  · have hiu : I (counter + 1) u := by simpa only [hretry, ite_true] using hp
    have hiv := stable (counter + 1) hiu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite true (by simp [hz, hretry]) (fun _ => ?_) (fun he => Bool.noConfusion he))
    refine WP.mono (searchAdvance_ok hvctrl hc hl hs) fun w ⟨hw, hstatus, hf, kw⟩ => ?_
    have hiw := stable (counter + 1) hiv hf kw
    let next := if counter + 1 < limit then 3 else 2
    have hn : next ≤ 3 := by dsimp [next]; split <;> decide
    refine WP.mono (searchStatusCmp_ok hw hn hstatus) fun t ⟨hzt, hmt, kt⟩ => ?_
    have hit := stable (counter + 1) hiw (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))
    have ht := hw.congr hmt kt
    by_cases hlt : counter + 1 < limit
    · exact Or.inr ⟨by simp [hzt, next, hlt], hit, ht, hlt⟩
    · have he : counter + 1 = limit := by omega_using [hc, hlt]
      refine Or.inl ⟨by simp [hzt, next, hlt], ?_⟩
      apply done t (he ▸ hit) (he ▸ ht)
      rw [hmt, hstatus, ite_eq_right hlt]
      rfl
  · have hqu : Q u := by simpa only [hretry, ite_false] using hp
    have hqv := finish hqu hframe (hk.mono (by decide))
    refine WP.seq (WP.ite false (by simp [hz, hretry]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    refine WP.mono (searchStatusCmp_ok hvctrl hv (hm ▸ hstat)) fun t ⟨hzt, hmt, kt⟩ => ?_
    exact Or.inl ⟨by simp [hzt, hretry],
      finish hqv (by rw [hmt]; exact Outside.refl _ _ _ _) (kt.mono (by decide))⟩

/-- The native loop always terminates within its public attempt budget. -/
theorem searchLoop_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} {counter : Nat} (hc : counter < limit)
    (hi : I counter s) (h : SearchControl B counter stride s) :
    WP isa (.loop (Impl.Dsa.AArch64.Generation.pSearchIteration body limit stride) (.zero .x .x3)) s Q := by
  exact WP.loop
    (fun n t => ∃ c, n = limit - c ∧ c < limit ∧ I c t ∧ SearchControl B c stride t)
    (fun n t ⟨c, hn, hc, hi, hctrl⟩ =>
      WP.mono (searchIteration_ok hl hs stable finish done body_ok hc hi hctrl)
        fun t' ht => ht.imp (fun h => h) fun ⟨hz, hi', hc', hlt⟩ =>
          ⟨hz, limit - (c + 1), by omega_using [hn, hc], c + 1, rfl, hlt, hi', hc'⟩)
    (limit - counter) s ⟨counter, rfl, hc, hi, h⟩

/-- Initialization and the bounded search compose without any host loop. -/
theorem pSearch_ok {body : Prog isa} {B : Addr} {limit stride : Nat}
    {I : Nat → State → Prop} {Q : State → Prop}
    (hl : limit ≤ 12288) (hpos : 0 < limit) (hs : stride ≤ 12)
    (stable : ∀ c, SearchPayload B (I c)) (finish : SearchPayload B Q)
    (done : ∀ t, I limit t → SearchControl B limit stride t →
      word t.mem B 16 = 2 → Q t)
    (body_ok : ∀ c s, c < limit → I c s → SearchControl B c stride s →
      WP isa body s fun t => SearchControl B c stride t ∧
        ∃ status ≤ 3, word t.mem B 16 = BitVec.ofNat 64 status ∧
          (if status = 3 then I (c + 1) t else Q t))
    {s : State} (hi : I 0 s) (h : Scr s B 24) (hdi : s.gpr .x0 = B) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearch body limit stride) s Q := by
  unfold Impl.Dsa.AArch64.Generation.pSearch
  refine WP.seq (WP.mono (searchInit_ok h hdi stride) fun t ⟨ht, hf, hk⟩ => ?_)
  exact searchLoop_ok hl hs stable finish done body_ok hpos
    (stable 0 hi (hf.mono (by decide) (by decide)) (hk.mono (by decide))) ht

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Controller updates preserve the persistent search payload -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem SearchMemory.stable {p : SearchPlan} {W : Nat → BitVec 64} :
    SearchPayload p.C (SearchMemory p W) := by
  intro s t h hf hk
  have ff : Frame [⟨p.C, 24⟩] s.mem t.mem := by
    intro a ha
    apply hf a
    right
    have hn := ha ⟨p.C, 24⟩ (by simp)
    change ¬ ofs p.C a < 24 at hn
    omega_using [hn]
  obtain ⟨V, R⟩ := h.rep
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.frameControl)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.hashControl)
  exact h.frame (lay_of_rep h.layout R Rt rfl hk.sp hk.wr) ⟨V, Rt⟩
    (fun _ _ => rfl) (ff.mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])) hk.rd hk.wr

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.HashChoice`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SeedSubgroup`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.Generation.Subgroup`, which only this module used -/

section

/-! # Complete native subgroup-candidate generation and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem subgroup_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash}
    (h1 : Pbkdf2.Md.AArch64.Calls.StreamOK G1.stream) (h256 : Pbkdf2.Md.AArch64.Calls.StreamOK G256.stream)
    (he1 : ∀ x, Spec.Mgf1.sha1.hash x = h1.SH.H.hash x)
    (he256 : ∀ x, Spec.Mgf1.sha256.hash x = h256.SH.H.hash x)
    (hs1 : ∀ x, (Spec.Mgf1.sha1.hash x).length = G1.D)
    (hs256 : ∀ x, (Spec.Mgf1.sha256.hash x).length = G256.D)
    (hd1 : G1.D = 20) (hd256 : G256.D = 32) (T : PrimeTest)
    {p : SubgroupPlan} {used : Nat} {s : State} (h : SubgroupState p used s) :
    WP isa (Impl.Dsa.AArch64.Generation.subgroup G1 G256 T.run p.prime.len) s fun t =>
      let res := Spec.Dsa.probablePrime p.prime.N (p.prime.rand.drop used)
      ∃ used' status V', used' ≤ p.prime.rand.length ∧
        Lay t p.F p.hash ∧
        Rep t.mem p.F p.hash V' (upd (upd p.W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        Spec.Rsa.bytesAt t.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.prime.rand.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have plen : p.prime.len ≤ 32 := by rcases p.width with hh | hh <;> omega_using [hh]
  unfold Impl.Dsa.AArch64.Generation.subgroup
  refine WP.seq (WP.mono (qBuild_ok h1 h256 he1 he256 hs1 hs256 hd1 hd256 p.width
    h.layout R h.label p.outputSlot h.outputWrite p.outputFrame.symm p.outputScratch)
    fun u ⟨uq, stepU, fu, Lu, Vu, Ru⟩ => ?_)
  have urd := stepU.rd
  have uwr := stepU.wr
  have ubytes : Spec.Rsa.bytesAt u.mem p.output p.prime.len = Spec.Dsa.encodeBE p.prime.len p.prime.N := by
    rw [uq, h.seed, ← p.modulus]
  have tapeU := source_of_frame h.tape fu p.tapeHash p.prime.randMax urd uwr
  have hc : Impl.Dsa.AArch64.ProbablePrime.candidate (8 * p.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.AArch64.ProbablePrime.candidate
    rcases p.width with hh | hh <;> rw [hh] <;> decide
  have hin : PrimeCallInputs (8 * p.prime.len) p.F p.hash (p.W 5) p.prime.rp p.prime.rand
      p.prime.N used p.W Vu u := {
    layout := Lu
    rep := Ru
    arena := rfl
    arenaWrite := h.arena.congr uwr
    tapePtr := p.tapePtr
    tapeLength := p.tapeLength
    usedSlot := h.usedSlot
    usedBound := h.usedBound
    tapeSize := p.prime.randMax
    tapeCover := by rw [urd, uwr]; exact h.tapeCover
    tapeBytes := bytes_of_src tapeU
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem (p.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q)
        p.prime.len) = p.prime.N
      rw [p.outputPtr, ubytes, VG.Proof.Dsa.decodeBE_os2ip]
      exact p.encoding
    odd := by
      rw [p.modulus]
      exact (VG.Proof.Dsa.Generation.qCandidate_shape
        (show 2 ≤ 8 * p.prime.len by rcases p.width with hh | hh <;> omega_using [hh]) p.seed).1
    bitLen := p.bits }
  have hch : primeCallChanged (8 * p.prime.len) p.F (p.W 5) =
      p.primeWrites ++ [⟨p.F, frameBytes⟩] := by
    rw [SubgroupPlan.primeWrites, ← p.base, ← p.witnessPtr, primeCallChanged,
      Nat.mul_div_cancel_left _ (by decide)]
    rfl
  have hsup : ProbablePrime.Supported (8 * p.prime.len) := by
    rcases p.width with hh | hh <;> rw [hh] <;> unfold ProbablePrime.Supported <;> decide
  refine WP.mono (primeCall_ok T hsup hin p.geometry)
    fun t ⟨used', status, hb, Lt, Rt, he, hr, ft, rdt, wrt⟩ => ?_
  rw [hch] at ft
  refine ⟨used', status, Vu, hb, Lt, Rt, ?_, he, hr, ?_, rdt.trans urd, wrt.trans uwr⟩
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact p.outputPrime r hr
      · rcases List.mem_singleton.mp hr with rfl; exact p.outputFrame) (by omega_using [plen]), ubytes]
  · exact (fu.mono (by intro r hr; simp only [SubgroupPlan.changed, List.mem_append]; exact Or.inl (Or.inl hr))).trans
      (ft.mono (by intro r hr; simp only [SubgroupPlan.changed, List.append_assoc]; exact List.mem_append_right _ hr))

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Complete first phase of a seed attempt, retaining every retry input -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.MillerRabin.AArch64

theorem seedSubgroup_ok (H : GenerationHashes) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr) {used : Nat}
    (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.seedArguments p.geo.qLen))
      (Impl.Dsa.AArch64.Generation.subgroup H.sha1 H.sha256 T.run p.geo.qLen)) s fun t =>
      let res := Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used)
      ∃ used' status, used' ≤ p.rand.bytes.length ∧
        GenerationMemory p (upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 used')) 19 status) t ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
          Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = p.rand.bytes.length - rest.length) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  refine WP.seq (WP.mono (prepareSeed_ok h) fun u ⟨huMem, fu, ku⟩ => ?_)
  have hseedU := hseed.frame fu ku.rd ku.wr
  have hb : W 5 = p.geo.B := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h0 : seedWords W p.geo.qLen 0 = VG.Proof.Bignum.off p.geo.B q := by simp [seedWords, upd, hb]
  have h25 : seedWords W p.geo.qLen 25 = seed.ptr := by simp [seedWords, upd, h1]
  have h16u : seedWords W p.geo.qLen 16 = BitVec.ofNat 64 used := by simpa [seedWords, upd] using h16
  have state := huMem.subgroupState seed hlen hseedU h0 h25 h16u hu
  refine WP.mono (subgroup_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256 H.width1 H.width256 T state)
    fun t ⟨used', status, Vt, bound, Lt, Rt, bytes, fail, result, ft, rd, wr⟩ => ?_
  have ff := huMem.subgroup_frame seed hlen h0 ft
  refine ⟨used', status, bound, huMem.frame Lt ⟨Vt, Rt⟩ ?_ ff rd wr,
    bytes, fail, result, fu.trans ff, rd.trans ku.rd, wr.trans ku.wr⟩
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (ite_eq_right (by decide)).trans (ite_eq_right (by decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # One hash selection shared by the subgroup and prime searches -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.Proof.Pbkdf2.Md.AArch64

def GenerationHashes.streamOK (H : GenerationHashes) (len : Nat) :
    Calls.StreamOK (if len = 20 then H.sha1 else H.sha256).stream where
  SH := if len = 20 then H.h1.SH else H.h256.SH
  Wb := if len = 20 then H.h1.Wb else H.h256.Wb
  hS := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS
    · simpa [h] using H.h256.hS
  hD := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD
    · simpa [h] using H.h256.hD
  hB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB
    · simpa [h] using H.h256.hB
  hDF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hDF
    · simpa [h] using H.h256.hDF
  hF := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hF
    · simpa [h] using H.h256.hF
  hD0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hD0
    · simpa [h] using H.h256.hD0
  hS0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hS0
    · simpa [h] using H.h256.hS0
  hSB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hSB
    · simpa [h] using H.h256.hSB
  hB0 := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hB0
    · simpa [h] using H.h256.hB0
  hBB := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hBB
    · simpa [h] using H.h256.hBB
  hWb := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hWb
    · simpa [h] using H.h256.hWb
  hW := by
    by_cases h : len = 20
    · simpa [h] using H.h1.hW
    · simpa [h] using H.h256.hW
  repr := by
    by_cases h : len = 20
    · simpa [h] using H.h1.repr
    · simpa [h] using H.h256.repr
  init := by
    by_cases h : len = 20
    · simpa [h] using H.h1.init
    · simpa [h] using H.h256.init
  upd := by
    by_cases h : len = 20
    · simpa [h] using H.h1.upd
    · simpa [h] using H.h256.upd
  fin := by
    by_cases h : len = 20
    · simpa [h] using H.h1.fin
    · simpa [h] using H.h256.fin
  initDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.initDepth
    · simpa [h] using H.h256.initDepth
  updDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.updDepth
    · simpa [h] using H.h256.updDepth
  finDepth := by
    by_cases h : len = 20
    · simpa [h] using H.h1.finDepth
    · simpa [h] using H.h256.finDepth

def generationHash (len : Nat) : Spec.Mgf1.Hash :=
  if len = 20 then Spec.Mgf1.sha1 else Spec.Mgf1.sha256

theorem GenerationHashes.hash_matches (H : GenerationHashes) (len : Nat) :
    ∀ x, (generationHash len).hash x = (H.streamOK len).SH.H.hash x := by
  intro x
  by_cases h : len = 20
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash1 x
  · simpa [generationHash, GenerationHashes.streamOK, h] using H.hash256 x

theorem GenerationHashes.hash_size (H : GenerationHashes) (len : Nat) :
    ∀ x, ((generationHash len).hash x).length = (if len = 20 then H.sha1 else H.sha256).D := by
  intro x
  unfold generationHash
  split
  · exact H.size1 x
  · exact H.size256 x

theorem GenerationHashes.hash_width (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32) :
    (if len = 20 then H.sha1 else H.sha256).D = len := by
  rcases hw with rfl | rfl
  · simpa using H.width1
  · simpa using H.width256

theorem generationHash_seed {len : Nat} (hw : len = 20 ∨ len = 32) (bs : List Byte) :
    (generationHash len).hash bs = Spec.Dsa.seedHash (8 * len) bs := by
  rcases hw with rfl | rfl <;> rfl

theorem GenerationHashes.seed_size (H : GenerationHashes) {len : Nat} (hw : len = 20 ∨ len = 32)
    (bs : List Byte) : 8 * (Spec.Dsa.seedHash (8 * len) bs).length = 8 * len := by
  rw [← generationHash_seed hw, H.hash_size, H.hash_width hw]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.GeneratorCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorStage`, which this module and modules that import it used -/

section

/-! # The generator stages parameter generation calls

`vg_dsa_generator_{bits}` for each width of p: each one's name, its code, its
proof, and the stack its frames use. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

structure GeneratorStage where
  name : Nat → String
  code : Nat → Prog isa
  verified : ∀ pLen, Generator.Supported pLen → Verified target (code pLen) (Generator.contract pLen)
  depth : ∀ pLen, 16 * (code pLen).aarch64Depth ≤ 272
  /-- It never touches PSTATE.DIT (`ConstantTime.withDit`). -/
  noDit : ∀ pLen, Generator.Supported pLen → (code pLen).all (fun i => !i.touchesDit) = true

/-- The call of the stage for a p of `pLen` bytes. -/
def GeneratorStage.run (G : GeneratorStage) (pLen : Nat) : Prog isa := .call (G.name pLen) (G.code pLen)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Calling the generator stage from the generation frame

The stage runs on the generation's scratch space, with the h tape, and
returns its end and the octets of the candidates it read
(`Proof.Dsa.GeneratorStage.result`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

theorem GenerationGeometry.supported (p : GenerationGeometry) : Generator.Supported p.pLen := p.width

theorem GenerationGeometry.qLen_eq (p : GenerationGeometry) : Impl.Dsa.AArch64.Generator.qLen p.pLen = p.qLen := by
  rcases p.lengths with h | h | h <;> simp [h.1, h.2, Impl.Dsa.AArch64.Generator.qLen]

/-- The stage's arguments, from the frame. -/
theorem generatorCallArgs_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs p.geo.pLen)) s fun u =>
      u.gpr .x0 = p.geo.B ∧ u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) ∧
      u.gpr .x2 = p.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length ∧ u.mem = s.mem ∧
      Keep [.x0, .x1, .x2, .x3] s u := by
  have L := h.layout
  obtain ⟨V, R⟩ := h.rep
  have w5 : s.mem.readW (p.geo.F + BitVec.ofNat 64 40) 64 = p.geo.B :=
    (R.fr 5 (by decide)).trans ((h.slots 5 (by decide)).trans p.baseSlot)
  have w11 : s.mem.readW (p.geo.F + BitVec.ofNat 64 88) 64 = p.hs.ptr :=
    (R.fr 11 (by decide)).trans ((h.slots 11 (by decide)).trans p.hSlot)
  have w13 : s.mem.readW (p.geo.F + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 p.hs.bytes.length :=
    (R.fr 13 (by decide)).trans ((h.slots 13 (by decide)).trans p.hLengthSlot)
  have l40 := L.ld (d := 40) (n := 8) (by decide)
  have l88 := L.ld (d := 88) (n := 8) (by decide)
  have l104 := L.ld (d := 104) (n := 8) (by decide)
  simp only [off] at l40 l88 l104
  rw [← L.sp] at w5 w11 w13 l40 l88 l104
  have hu : BitVec.setWidth 64 (BitVec.ofNat 16 (usedBytes p.geo.pLen / 8)) = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) := by
    rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide
  have run : WP isa (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs p.geo.pLen)) s fun u =>
      u.gpr .x0 = p.geo.B ∧ u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8) ∧
      u.gpr .x2 = p.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length ∧ u.mem = s.mem := by
    unfold Impl.Dsa.AArch64.Generation.generatorCallArgs
    brun [State.write, exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 88) (by decide),
      exec_ldrSp (off := 104) (by decide), l40, l88, l104, w5, w11, w13, hu]
  exact WP.mono (WP.keep [.x0, .x1, .x2, .x3] run
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide) rfl
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide +kernel)) fun u ⟨hu, hk⟩ =>
    ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2, hk⟩

/-- The stage's regions: the h tape; the scratch space. -/
def generatorCallRd (p : GenerationContext) : List Region := [⟨p.hs.ptr, p.hs.bytes.length⟩]

def generatorCallWr (p : GenerationContext) : List Region := [⟨p.geo.B, usedBytes p.geo.pLen⟩]

theorem usedBytes_words {pLen : Nat} (h : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    (BitVec.ofNat 64 (usedBytes pLen / 8)).toNat * 8 = usedBytes pLen ∧
      usedBytes pLen ≤ 8 * (BitVec.ofNat 64 (usedBytes pLen / 8)).toNat := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the call itself leaves, before its result is stored. -/
structure GeneratorCalled (p : GenerationContext) (value q : Nat) (s u t : State) : Prop where
  rd : t.rd = u.rd
  wr : t.wr = u.wr
  sp : t.sp = p.geo.F
  status : t.gpr .x0 = BitVec.ofNat 64 (Proof.Dsa.GeneratorStage.result p.geo.pLen value q
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE))
  packed : ∀ a, Proof.Dsa.GeneratorStage.stage value q
      ((Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE) = some a →
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
      Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a
  keeps : Proof.Dsa.ModPow.Keeps p.geo.B (usedBytes p.geo.pLen / 8)
    (Impl.Dsa.AArch64.Generator.layout p.geo.pLen).scratch s.mem t.mem
  frame : Frame [⟨p.geo.B, usedBytes p.geo.pLen⟩, below p.geo.F 272] s.mem t.mem

/-- What the callee starts from: its precondition, regions of the caller's,
and the values it reads. -/
structure GeneratorEntry (p : GenerationContext) (value qval : Nat) (u : State) : Prop where
  pre : (Generator.contract p.geo.pLen).pre (u.callEntry.withRegions (generatorCallRd p) (generatorCallWr p))
  reads : Covers (generatorCallRd p ++ generatorCallWr p) (u.rd ++ u.wr)
  writes : Covers (generatorCallWr p) u.wr
  pv : Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = value
  qv : Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = qval
  tape : Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length = p.hs.bytes

theorem generatorCall_entry {p : GenerationContext} {W : Nat → BitVec 64} {s u : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    (h0 : u.gpr .x0 = p.geo.B) (h1 : u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8))
    (h2 : u.gpr .x2 = p.hs.ptr) (h3 : u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length) (hm : u.mem = s.mem)
    (hsp : u.sp = p.geo.F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    GeneratorEntry p value qval u := by
  have hb := p.geo.supported
  have hn := p.hs.size
  have qq := p.geo.qLen_eq
  have hw := usedBytes_words p.geo.width
  have hl : (BitVec.ofNat 64 p.hs.bytes.length).toNat = p.hs.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have pfit : value < 256 ^ p.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using domain.upper
  have pv : Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = value := by
    unfold Proof.Dsa.GeneratorStage.pAt Proof.Dsa.GeneratorStage.numberAt
    rw [hm]
    exact (congrArg Spec.Dsa.decodeBE bp).trans (VG.Proof.Dsa.decodeBE_encodeBE pfit)
  have qv : Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout p.geo.pLen) u.mem p.geo.B = qval := by
    unfold Proof.Dsa.GeneratorStage.qAt Proof.Dsa.GeneratorStage.numberAt
    rw [hm]
    change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q)
      (Impl.Dsa.AArch64.Generator.qLen p.geo.pLen)) = qval
    rw [qq]
    exact (congrArg Spec.Dsa.decodeBE bq).trans (VG.Proof.Dsa.decodeBE_encodeBE qfit)
  have tapeV : Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length = p.hs.bytes := by rw [hm]; exact h.hs.bytes
  -- The callee's regions are the generation's.
  have cW : Covers (generatorCallWr p) u.wr := by
    obtain ⟨⟨B₀, o, L₀, hmem, hbase, hle, _⟩, _⟩ := h.scratch
    rw [hwr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, hmem, o, hbase, hle⟩
  have cR : Covers (generatorCallRd p) (u.rd ++ u.wr) := by
    rw [hrd, hwr]; exact h.hs.cover
  have frameBelow : Region.Disjoint ⟨p.geo.F, frameBytes⟩ (below p.geo.F 288) :=
    Offset.base_disjoint_below p.geo.F (by decide)
  have pre : (Generator.contract p.geo.pLen).pre
      (u.callEntry.withRegions (generatorCallRd p) (generatorCallWr p)) := by
    sig_pre [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    sig_and_intros
    all_goals try simp only [h0, h1, h2, h3, hsp, hl, hw.1, generatorCallRd, generatorCallWr]
    · exact p.geo.callSize
    · exact p.hs.arena.symm
    · exact p.geo.callArena
    · exact p.hs.callStack.symm
    · exact p.geo.arenaBound
    · exact p.hs.bound
    · exact hw.2
    · rw [pv]; exact domain.odd
    · rw [pv]
      exact (VG.Proof.Dsa.bitLength_iff_bounds (by rcases domain.width with h | h | h <;> omega_using [h])).mpr
        ⟨domain.lower, domain.upper⟩
    · rw [qv]; exact qpos
    · rw [pv, qv, hm]; exact be
  exact ⟨pre, cR.append_left cW.right, cW, pv, qv, tapeV⟩

theorem generatorCall_call_ok (G : GeneratorStage) {p : GenerationContext} {W : Nat → BitVec 64} {s u : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    (h0 : u.gpr .x0 = p.geo.B) (h1 : u.gpr .x1 = BitVec.ofNat 64 (usedBytes p.geo.pLen / 8))
    (h2 : u.gpr .x2 = p.hs.ptr) (h3 : u.gpr .x3 = BitVec.ofNat 64 p.hs.bytes.length) (hm : u.mem = s.mem)
    (hsp : u.sp = p.geo.F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    WP isa (G.run p.geo.pLen) u (GeneratorCalled p value qval s u) := by
  have hb := p.geo.supported
  have hd := G.depth p.geo.pLen
  have hn := p.hs.size
  have qq := p.geo.qLen_eq
  have hl : (BitVec.ofNat 64 p.hs.bytes.length).toNat = p.hs.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have E := generatorCall_entry h value qval domain qfit qpos bp be bq h0 h1 h2 h3 hm hsp hrd hwr
  have pv := E.pv
  have qv := E.qv
  have tapeV := E.tape
  refine WP.callF (G.verified p.geo.pLen hb).1 E.pre E.reads E.writes ?_
    (by have := hd; omega_using [hd])
  intro t hrd' hwr' hsp' hf _ hpost
  sig_post [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    at hpost
  simp only [h0, h1, h2, h3, hl] at hpost
  rw [pv, qv] at hpost
  obtain ⟨hr, hkeeps, hpk⟩ := hpost
  have cands : Proof.Dsa.GeneratorStage.candidates p.geo.pLen (Spec.Rsa.bytesAt u.mem p.hs.ptr p.hs.bytes.length) =
      (Spec.Dsa.generationChunks p.geo.pLen p.hs.bytes).map Spec.Dsa.decodeBE := by
    rw [tapeV]; rfl
  rw [cands] at hr hpk
  refine ⟨hrd', hwr', hsp'.trans hsp, hr, fun a ha => ?_, ?_, ?_⟩
  · have := hpk a ha
    rw [← qq]
    exact this
  · rw [← hm]
    have := hkeeps
    rw [show (BitVec.ofNat 64 (usedBytes p.geo.pLen / 8)).toNat = usedBytes p.geo.pLen / 8 by
      rcases p.geo.width with hw' | hw' | hw' <;> rw [hw'] <;> decide] at this
    exact this
  · rw [← hm]
    refine Frame.sub hf fun r hr => ?_
    simp only [generatorCallWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · rw [hsp]
      exact ⟨below p.geo.F 272, by simp, below_sub (by omega_using [hd]) (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SeedPrime`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.ContextSearchFrame`, which only this module used -/

section

/-! # Lift the bounded prime search back to the persistent generation state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationMemory.search_frame {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (h1 : W 1 = seed.ptr) {m m' : Mem}
    (hf : Frame (searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C) m m') :
    Frame p.changed m m' := by
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have writes : searchWrites (h.searchPlan seed hlen h1).attempt (h.searchPlan seed hlen h1).C =
      p.geo.part VG.Impl.Dsa.Generation.Layout.control 24 :: ⟨p.geo.F, frameBytes⟩ :: p.geo.pWork := by
    dsimp only [searchWrites, GenerationMemory.searchPlan, GenerationGeometry.searchPlan,
      PPrimalityPlan.changed, PPrimalityPlan.testWrites, PConstructPlan.changed,
      HashPlan.changed, GenerationGeometry.primalityPlan, GenerationGeometry.constructPlan,
      GenerationGeometry.hashPlan, searchWords, upd]
    rw [h5]
    rfl
  rw [writes] at hf
  apply GenerationContext.frame_parts hf
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have part (d n : Nat) (hd : d ≤ domainCheck) (hn : n ≤ arithmeticBytes) :
      ∃ out ∈ p.changed, Region.Sub (p.geo.part d n) out :=
    ⟨⟨p.geo.B, usedBytes p.geo.pLen⟩, by simp [GenerationContext.changed],
      p.geo.part_sub (p.geo.small_bound hd hn)⟩
  intro r hr
  simp only [GenerationGeometry.pWork, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact part VG.Impl.Dsa.Generation.Layout.control 24 (by decide) (by decide)
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact part shaped p.geo.pLen (by decide) (by unfold arithmeticBytes; omega_using [pn])
  · exact part hashes ((p.geo.count + 1) * p.geo.qLen) (by decide)
      (by have := p.geo.hashSizes.2.1; unfold arithmeticBytes; omega_using [this])
  · exact part wrappedSeed p.geo.qLen (by decide) (by unfold arithmeticBytes; omega_using [qn])
  · exact part VG.Impl.Dsa.Generation.Layout.hash oRsa (by decide) (by decide)
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], below_sub (by decide) (by decide)⟩
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part VG.Impl.Dsa.Generation.Layout.p p.geo.pLen (by decide) (by unfold arithmeticBytes; omega_using [pn])
  · exact part exponent p.geo.pLen (by decide) (by unfold arithmeticBytes; omega_using [pn])
  · exact part arithmetic arithmeticBytes (by decide) (by rfl)
  · exact part witness p.geo.pLen (by decide) (by unfold arithmeticBytes; omega_using [pn])
  · exact ⟨below p.geo.F 272, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨⟨p.geo.F, frameBytes⟩, by simp [GenerationContext.changed], fun _ h => h⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.NativeSearch`, which only this module used -/

section

/-! # Complete native bounded p search against the specification -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SearchSemantics.lean`, which only this module imported.
section

/-! # Match each native body result to the reviewed p-search recursion -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

def SearchPlan.remaining (p : SearchPlan) (counter used : Nat) : Option (Option Nat × List Byte) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed counter (p.attempt.rand.drop used)

theorem SearchPlan.stepCursor {p : SearchPlan} {counter used : Nat} {b : Bool} {rest : List Byte}
    (h : p.stepResult counter used = some (b, rest)) :
    p.attempt.rand.drop (p.attempt.rand.length - rest.length) = rest := by
  unfold SearchPlan.stepResult at h
  split at h
  · cases h
    apply VG.Proof.Dsa.Generation.suffix_drop_length
    exact List.drop_suffix _ _
  · exact VG.Proof.Dsa.Generation.probablePrime_cursor h

theorem SearchPlan.remaining_step {p : SearchPlan} {counter used : Nat}
    (hc : counter < 32 * p.attempt.construct.len) :
    p.remaining counter used =
      match p.stepResult counter used with
      | none => none
      | some (true, rest) => some (some (p.candidate counter), rest)
      | some (false, rest) => p.remaining (counter + 1) (p.attempt.rand.length - rest.length) := by
  have hc' : counter < 4 * (8 * p.attempt.construct.len) := by omega_using [hc]
  unfold SearchPlan.remaining
  rw [VG.Proof.Dsa.Generation.primeSearch_step _ _ hc']
  rw [← p.attempt.construct.hashCount]
  change (if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then _ else _) = _
  by_cases hs : p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1)
  · simp only [hs, ite_true, SearchPlan.stepResult]
    rw [VG.Proof.Dsa.Generation.suffix_drop_length (List.drop_suffix used p.attempt.rand)]
  · simp only [hs, ite_false, SearchPlan.stepResult]
    rcases hp : Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used) with _ | ⟨b, rest⟩
    · simp only [SearchPlan.candidate] at hp
      rw [hp]
    · have hp' := hp
      simp only [SearchPlan.candidate] at hp'
      rw [hp']
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        rw [VG.Proof.Dsa.Generation.probablePrime_cursor hp]
      · rfl

theorem SearchPlan.remaining_done (p : SearchPlan) (used : Nat) :
    p.remaining (32 * p.attempt.construct.len) used = some (none, p.attempt.rand.drop used) :=
  VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega_using [])

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SearchInvariant.lean`, which only this module imported.
section

/-! # The p-search invariant retains its exact specification result -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def SearchOutcome (p : SearchPlan) (res : Option (Option Nat × List Byte))
    (W : Nat → BitVec 64) (used : Nat) (t : State) : Prop :=
  (W 19 = BitVec.ofNat 64 0 ∧ res = none) ∨
  (W 19 = BitVec.ofNat 64 1 ∧ ∃ value,
    res = some (some value, p.attempt.rand.drop used) ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len value ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.attempt.construct.hash.W 5) exponent) p.attempt.construct.len =
      Spec.Dsa.encodeBE p.attempt.construct.len ((value - 1) / Spec.Rsa.os2ip p.attempt.construct.qb)) ∨
  (W 19 = BitVec.ofNat 64 3 ∧ res = some (none, p.attempt.rand.drop used))

def SearchInvariant (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State)
    (counter : Nat) (t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    (0 < counter → W 19 = BitVec.ofNat 64 3) ∧ res = p.remaining counter used ∧
    Frame (searchWrites p.attempt p.C) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr

def SearchFinished (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s t : State) : Prop :=
  ∃ W used, SearchMemory p W t ∧ used ≤ p.attempt.rand.length ∧ W 16 = BitVec.ofNat 64 used ∧
    SearchOutcome p res W used t ∧ Frame (searchWrites p.attempt p.C) s.mem t.mem ∧
    t.rd = s.rd ∧ t.wr = s.wr

theorem controller_frame {C : Addr} {m m' : Mem} (hf : Outside C 0 24 m m') : Frame [⟨C, 24⟩] m m' := by
  intro a ha
  apply hf a
  right
  have hn := ha ⟨C, 24⟩ (by simp)
  change ¬ ofs C a < 24 at hn
  omega_using [hn]

theorem searchInvariant_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) (c : Nat) :
    SearchPayload p.C (SearchInvariant p res s c) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  exact ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, h19, hr,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.rd.trans rd, hk.wr.trans wr⟩

theorem searchFinished_stable (p : SearchPlan) (res : Option (Option Nat × List Byte)) (s : State) :
    SearchPayload p.C (SearchFinished p res s) := by
  intro u t h hf hk
  obtain ⟨W, used, hm, hu, h16, ho, ff, rd, wr⟩ := h
  refine ⟨W, used, SearchMemory.stable hm hf hk, hu, h16, ?_,
    ff.trans ((controller_frame hf).mono (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [searchWrites])), hk.rd.trans rd, hk.wr.trans wr⟩
  rcases ho with ho | ⟨h19, value, hr, hp, he⟩ | ho
  · exact Or.inl ho
  · refine Or.inr (Or.inl ⟨h19, value, hr, ?_, ?_⟩)
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.pControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega_using [hh]), hp]
    · rw [VG.Proof.Dsa.Generation.frame_bytesAt (controller_frame hf) (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.exponentControl)
        (by rcases p.attempt.construct.width with hh | hh | hh <;> omega_using [hh]), he]
  · exact Or.inr (Or.inr ho)

theorem searchInvariant_done {p : SearchPlan} {res : Option (Option Nat × List Byte)} {s t : State}
    (h : SearchInvariant p res s (32 * p.attempt.construct.len) t) : SearchFinished p res s t := by
  obtain ⟨W, used, hm, hu, h16, h19, hr, ff, rd, wr⟩ := h
  refine ⟨W, used, hm, hu, h16, Or.inr (Or.inr ⟨h19 ?_, ?_⟩), ff, rd, wr⟩
  · rcases p.attempt.construct.width with hh | hh | hh <;> omega_using [hh]
  · exact hr.trans (p.remaining_done used)

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Proof.Pbkdf2.Md.AArch64

theorem nativeSearch_ok {G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash} {p : SearchPlan}
    (hG : Calls.StreamOK (if p.attempt.construct.hash.len = 20 then G1 else G256).stream)
    {H : Spec.Mgf1.Hash} (hHh : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ bytes, (H.hash bytes).length = (if p.attempt.construct.hash.len = 20 then G1 else G256).D)
    (T : PrimeTest)
    (hd : (if p.attempt.construct.hash.len = 20 then G1 else G256).D = p.attempt.construct.hash.len)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.attempt.construct.hash.len) bs).length = 8 * p.attempt.construct.hash.len)
    {s : State} {W : Nat → BitVec 64} {used : Nat} (h : SearchMemory p W s)
    (hC : Scr s p.C 24) (hused : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.attempt.rand.length) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch G1 G256 T.run
      p.attempt.construct.len p.attempt.construct.hash.len) s
      (SearchFinished p (p.remaining 0 used) s) := by
  have hlimit : 0 < 32 * p.attempt.construct.len ∧ 32 * p.attempt.construct.len ≤ 12288 := by
    rcases p.attempt.construct.width with hh | hh | hh <;> omega_using [hh]
  have hstride : p.attempt.construct.hash.count + 1 ≤ 12 := by
    have := p.attempt.construct.hash.count_le; omega_using [this]
  obtain ⟨V, R⟩ := h.rep
  unfold Impl.Dsa.AArch64.Generation.primeSearch
  rw [← p.attempt.construct.hashCount]
  refine WP.seq (WP.mono (controlBase_ok (B := p.C) h.layout R (by
    rw [h.slots 5 (by simp [searchSlots])]; exact p.controlBase)) fun u ⟨udi, um, ku⟩ => ?_)
  have Ru : Rep u.mem p.attempt.construct.hash.F p.attempt.construct.hash.S V W := um ▸ R
  have Lu := lay_of_rep h.layout R Ru rfl ku.sp ku.wr
  have fu : Frame (searchWrites p.attempt p.C) s.mem u.mem := by rw [um]; exact Frame.refl _ _
  have mu := h.frame Lu ⟨V, Ru⟩ (fun _ _ => rfl) fu ku.rd ku.wr
  apply pSearch_ok hlimit.2 hlimit.1 hstride
    (searchInvariant_stable p (p.remaining 0 used) s) (searchFinished_stable p (p.remaining 0 used) s)
    (fun t ht _ _ => searchInvariant_done ht)
    (fun c v hc hi ctrl => ?_)
    (show SearchInvariant p (p.remaining 0 used) s 0 u from
      ⟨W, used, mu, hu, hused, by omega_using [], rfl, fu, ku.rd, ku.wr⟩)
    (hC.congr ku.wr) udi
  obtain ⟨Wv, usedv, mv, huv, h16v, _, hremaining, fv, rdv, wrv⟩ := hi
  refine WP.mono (searchBody_ok hG hHh hsize T hd hhash hseedsize mv ctrl hc h16v huv)
    fun t ⟨ct, Wt, usedt, status, mt, hut, h16t, h19t, hct, bp, be, he, hr, ft, rdt, wrt⟩ => ?_
  have frame := fv.trans ft
  have rd := rdt.trans rdv
  have wr := wrt.trans wrv
  have step := hremaining.trans (p.remaining_step hc)
  rcases result : p.stepResult c usedv with _ | ⟨b, rest⟩
  · have hs := he result
    rw [result] at step
    refine ⟨ct, 0, by decide, hct.trans hs, ?_⟩
    change SearchFinished p (p.remaining 0 used) s t
    exact ⟨Wt, usedt, mt, hut, h16t, Or.inl ⟨h19t.trans hs, step⟩, frame, rd, wr⟩
  · obtain ⟨hs, hcursor⟩ := hr b rest result
    rw [result] at step
    cases b with
    | false =>
      refine ⟨ct, 3, by decide, hct.trans hs, ?_⟩
      change SearchInvariant p (p.remaining 0 used) s (c + 1) t
      refine ⟨Wt, usedt, mt, hut, h16t, fun _ => h19t.trans hs, ?_, frame, rd, wr⟩
      rw [hcursor]
      exact step
    | true =>
      refine ⟨ct, 1, by decide, hct.trans hs, ?_⟩
      change SearchFinished p (p.remaining 0 used) s t
      refine ⟨Wt, usedt, mt, hut, h16t, Or.inr (Or.inl ⟨h19t.trans hs, p.candidate c, ?_, bp, be⟩), frame, rd, wr⟩
      rw [hcursor, p.stepCursor result]
      exact step

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The full p search returns to the persistent seed-search state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem GenerationGeometry.qDecode (p : GenerationGeometry) (seed : List Byte) :
    Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.qLen (Spec.Dsa.qCandidate (8 * p.qLen) seed)) =
      Spec.Dsa.qCandidate (8 * p.qLen) seed := by
  rw [← VG.Proof.Dsa.decodeBE_os2ip]
  apply VG.Proof.Dsa.decodeBE_encodeBE
  have h := (VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases p.qWidth with hh | hh <;> omega_using [hh] : 2 ≤ 8 * p.qLen) seed).2.2
  simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using h

theorem seedPrime_ok (H : GenerationHashes) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen) s fun t =>
      let res := Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
        (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used)
      ∃ W' used', used' ≤ p.rand.bytes.length ∧ GenerationMemory p W' t ∧
        W' 16 = BitVec.ofNat 64 used' ∧
        (∀ k ∈ searchSlots, W' k = W k) ∧
        Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
          Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) ∧
        ((W' 19 = 0 ∧ res = none) ∨
         (W' 19 = 1 ∧ ∃ value, res = some (some value, p.rand.bytes.drop used') ∧
           VG.Proof.Dsa.Generation.PDomain p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value ∧
           Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen =
             Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)) ∨
         (W' 19 = 3 ∧ res = some (none, p.rand.bytes.drop used'))) ∧
        Frame p.changed s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let a := h.searchPlan seed hlen h1
  have state := h.searchState seed hlen hseed h1 hq
  have hw : a.attempt.construct.hash.len = 20 ∨ a.attempt.construct.hash.len = 32 := p.geo.qWidth
  have hc := h.scratch.sub (n := 24) (p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.control)
    (n := 24) (by decide) (by decide)) (by decide)
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have qdecode := p.geo.qDecode seed.bytes
  have remaining : a.remaining 0 used = Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) seed.bytes (p.rand.bytes.drop used) := by
    change VG.Proof.Dsa.Generation.primeSearch _ _ _ _ 0 _ = _
    rw [VG.Proof.Dsa.Generation.primeSearch_start]
    change Spec.Dsa.primeFromSeed (8 * p.geo.pLen) (8 * p.geo.qLen)
      (Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)))
      seed.bytes (p.rand.bytes.drop used) = _
    rw [qdecode]
  refine WP.mono (nativeSearch_ok (H.streamOK _) (H.hash_matches _) (H.hash_size _) T
    (H.hash_width hw) (generationHash_seed hw) (H.seed_size hw) state hc h16 hu)
    fun t ⟨Wt, usedt, mt, hut, h16t, outcome, ft, rd, wr⟩ => ?_
  have ff := h.search_frame seed hlen h1 ft
  have slots : ∀ k ∈ searchSlots, Wt k = W k := by
    intro k hk
    have he := mt.slots k hk
    change Wt k = searchWords p.geo.B W k at he
    have hn : k ≠ 0 ∧ k ≠ 2 ∧ k ≠ 25 := by simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simpa [searchWords, upd, hn.1, hn.2.1, hn.2.2] using he
  have mem := h.frame mt.layout mt.rep (fun k hk => slots k (by
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [searchSlots])) ff rd wr
  refine ⟨Wt, usedt, hut, mem, h16t, slots, ?_, ?_, ff, rd, wr⟩
  · have bytes := source_octets mt.qSource
    change Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) q) (Spec.Dsa.encodeBE p.geo.qLen
      (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes)).length =
        Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) at bytes
    simpa only [h5, VG.Proof.Dsa.encodeBE_length] using bytes
  · rcases outcome with ⟨h19, hr⟩ | ⟨h19, value, hr, bp, be⟩ | ⟨h19, hr⟩
    · exact Or.inl ⟨h19, remaining ▸ hr⟩
    · refine Or.inr (Or.inl ⟨h19, value, remaining ▸ hr, ?_, ?_, ?_⟩)
      · apply VG.Proof.Dsa.Generation.primeSearch_domain p.geo.width (H.seed_size p.geo.qWidth) seed.bytes
          (List.range (4 * (8 * p.geo.pLen))) (p.rand.bytes.drop used) (p.rand.bytes.drop usedt)
        exact remaining ▸ hr
      · change Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen value at bp
        simpa only [h5] using bp
      · change Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (W 5) exponent) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / Spec.Rsa.os2ip (Spec.Dsa.encodeBE p.geo.qLen
            (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))) at be
        simpa only [h5, qdecode] using be
    · exact Or.inr (Or.inr ⟨h19, remaining ▸ hr⟩)
end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # One seed of the refillable-tape search on AArch64

`refillAttempt_ok`: the seed attempt of the refillable-tape search
(`Impl.Dsa.AArch64.Generation.Refill.refillAttempt`) computes
`Proof.Dsa.Generation.refillAttempt`. Once `p` is found, the generator
stage's `h` tape is the window of the witness tape after `p`'s witnesses
(`window`); the octets of the candidates it read count as consumed, and a
window cut short without a generator ran out (`stageStatus`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Bignum.AArch64 (movi)

/-- Without a generator, `generator` reads every candidate. -/
theorem generatorCount_of_none {p q : Nat} :
    ∀ {hs : List Nat}, Spec.Dsa.generator p q hs = none →
      VG.Proof.Dsa.Generation.generatorCount p q hs = hs.length
  | [], _ => rfl
  | h :: hs, hn => by
    rw [VG.Proof.Dsa.Generation.generator_cons'] at hn
    cases hit : VG.Proof.Dsa.Generation.generatorHit p q h
    · simp only [hit, Bool.false_eq_true, ite_false] at hn
      simp only [VG.Proof.Dsa.Generation.generatorCount, hit, Bool.false_eq_true, ite_false,
        List.length_cons, generatorCount_of_none hn]
    · simp [hit] at hn

/-- `subs` of two numbers: the carry is set iff there is no borrow. -/
theorem refill_subs_ge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~BitVec.ofNat 64 b).toNat + (true).toNat) = decide (b ≤ a) := by
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Bool.toNat_true]
  exact decide_eq_decide.mpr (by omega_arith)

theorem movi_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h] : n < 2 ^ 64)]

/-! ## The window -/

theorem window_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {base : Addr} {used total pLen : Nat}
    (h14 : W 14 = base) (h16 : W 16 = BitVec.ofNat 64 used) (h15 : W 15 = BitVec.ofNat 64 total)
    (hle : used ≤ total) (hmax : total < 2 ^ 64) (hp : 128 * pLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.off F 88) (VG.Proof.Bignum.off base used)).writeW (VG.Proof.Bignum.off F 104)
        (BitVec.ofNat 64 (min (total - used) (128 * pLen))) := by
  have w14 : s.mem.readW (s.sp + BitVec.ofNat 64 112) 64 = base := by
    rw [L.sp]; exact (R.fr 14 (by decide)).trans h14
  have w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 used := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  have w15 : s.mem.readW (s.sp + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 total := by
    rw [L.sp]; exact (R.fr 15 (by decide)).trans h15
  have l112 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 112) 8 := by rw [L.sp]; exact L.ld (d := 112) (by decide)
  have l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  have l120 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 120) 8 := by rw [L.sp]; exact L.ld (d := 120) (by decide)
  have s88 : InRegions s.wr (s.sp + BitVec.ofNat 64 88) 8 := by rw [L.sp]; exact L.st (d := 88) (by decide)
  have s104 : InRegions s.wr (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.st (d := 104) (by decide)
  have hsub : BitVec.ofNat 64 total - BitVec.ofNat 64 used = BitVec.ofNat 64 (total - used) :=
    Offset.ofNat_sub_ofNat hle
  have hm := movi_ofNat hp
  unfold Impl.Dsa.AArch64.Generation.Refill.window Impl.Dsa.AArch64.Generation.Refill.windowBytes
  brun [State.write, exec_ldrSp (off := 112) (by decide), exec_ldrSp (off := 128) (by decide),
    exec_ldrSp (off := 120) (by decide), exec_storeSp (off := 88) (by decide),
    exec_storeSp (off := 104) (by decide), w14, w16, w15, l112, l128, l120, s88, s104, hsub, hm,
    refill_subs_ge (show total - used < 2 ^ 64 by omega_using [hmax]) (show 128 * pLen < 2 ^ 64 by omega_using [hp])]
  rw [L.sp]
  by_cases hc : 128 * pLen ≤ total - used
  · simp only [hc, decide_true, ite_true, Nat.min_eq_right hc]
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, Nat.min_eq_left (by omega_using [hc] : total - used ≤ 128 * pLen)]

theorem slice_length {g : GenerationGeometry} (t : GenerationTape g) {d n : Nat}
    (h : d + n ≤ t.bytes.length) : (t.slice d n h).bytes.length = n := by
  simp only [GenerationTape.slice, List.length_take, List.length_drop]; omega_using [h]

/-- `window`: the `h` tape is the window of `rand` after its first `used`
octets. -/
theorem refillWindow_ok {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) {used n : Nat} (h16 : W 16 = BitVec.ofNat 64 used)
    (hu : used ≤ p.rand.bytes.length) (hn : n = min (p.rand.bytes.length - used) (128 * p.geo.pLen)) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window p.geo.pLen)) s fun t =>
      GenerationMemory (p.withHs (p.rand.slice used n (by omega_using [hu, hn])))
        (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) t ∧
      Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨V, R⟩ := h.rep
  have L := h.layout
  have h14 : W 14 = p.rand.ptr := (h.slots 14 (by simp [generationSlots])).trans p.randSlot
  have h15 : W 15 = BitVec.ofNat 64 p.rand.bytes.length :=
    (h.slots 15 (by simp [generationSlots])).trans p.randLengthSlot
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6]
    (window_run L R h14 h16 h15 hu p.rand.size (by omega_using [pn]))
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide) rfl
    (by rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide +kernel)) fun t ⟨hm, kt⟩ => ?_
  rw [← hn] at hm
  have Rt : Rep t.mem p.geo.F p.geo.hash V (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) := by
    rw [hm]; exact (R.wf L.geo (k := 11) (by decide) _).wf L.geo (k := 13) (by decide) _
  have ft : Frame [⟨p.geo.F, frameBytes⟩] s.mem t.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cF p.geo.F (d := 88) (by decide))).writeW
      List.mem_cons_self _ (cF p.geo.F (d := 104) (by decide))
  have fc : Frame p.changed s.mem t.mem := GenerationContext.frame_single ft
  have room : used + n ≤ p.rand.bytes.length := by omega_using [hu, hn]
  refine ⟨⟨lay_of_rep L R Rt (by simp [upd]) kt.sp kt.wr, ⟨V, Rt⟩, ?_, h.scratch.congr kt.wr,
    h.seeds.frame fc kt.rd kt.wr, (h.rand.frame fc kt.rd kt.wr).slice room, h.rand.frame fc kt.rd kt.wr⟩,
    ft, kt.rd, kt.wr⟩
  intro k hk
  by_cases e11 : k = 11
  · subst e11; simp [upd, GenerationContext.withHs, GenerationTape.slice]
  by_cases e13 : k = 13
  · subst e13; simp [upd, GenerationContext.withHs, slice_length]
  simp only [upd, GenerationContext.withHs, e11, e13, ite_false]
  exact h.slots k hk

/-! ## The stage's result -/

theorem shr2_ofNat {c b : Nat} (hc : c < 4) (h : c + 4 * b < 2 ^ 64) :
    BitVec.ofNat 64 (c + 4 * b) >>> 2 = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h]
  omega_using [hc, h]

theorem shl2_ofNat (b : Nat) : BitVec.ofNat 64 b <<< 2 = BitVec.ofNat 64 (4 * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- The seed's status from the stage's end `c` (`Proof.Dsa.GeneratorStage.code`)
and the window's length `n`. -/
def refillStatus (c n pLen : Nat) : Nat := if c = 3 then (if n < 128 * pLen then 0 else 3) else 2 * c - 1

theorem consumed_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c b u : Nat} (hc : c < 4) (hb : b < 2 ^ 32)
    (hx : s.gpr .x0 = BitVec.ofNat 64 (c + 4 * b)) (h16 : W 16 = BitVec.ofNat 64 u) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.consumed) s fun t =>
      (t.mem = s.mem.writeW (VG.Proof.Bignum.off F 128) (BitVec.ofNat 64 (u + b)) ∧ t.gpr .x3 = BitVec.ofNat 64 c ∧
        t.gpr .x4 = BitVec.ofNat 64 c - 3) ∧ Keep [.x3, .x4, .x5] s t := by
  have w16 : s.mem.readW (s.sp + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 u := by
    rw [L.sp]; exact (R.fr 16 (by decide)).trans h16
  have l128 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.ld (d := 128) (by decide)
  have s128 : InRegions s.wr (s.sp + BitVec.ofNat 64 128) 8 := by rw [L.sp]; exact L.st (d := 128) (by decide)
  have e1 := shr2_ofNat hc (by omega_using [hc, hb] : c + 4 * b < 2 ^ 64)
  have e2 := shl2_ofNat b
  have e3 : BitVec.ofNat 64 (c + 4 * b) - BitVec.ofNat 64 (4 * b) = BitVec.ofNat 64 c := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [])]; congr 1; omega_using []
  refine WP.keep [.x3, .x4, .x5] ?_ (by decide)
  unfold Impl.Dsa.AArch64.Generation.Refill.consumed
  brun [State.write, exec_lsr_x' (by decide : 2 < 64), exec_lsl_x (by decide : 2 < 64),
    exec_ldrSp (off := 128) (by decide), exec_storeSp (off := 128) (by decide), w16, l128, s128, hx, e1, e2, e3]
  refine ⟨?_, rfl⟩
  rw [L.sp, ← BitVec.ofNat_add]

theorem shortStatus_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {n pLen : Nat} (h13 : W 13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hp : 128 * pLen < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 (if n < 128 * pLen then 0 else 3)) ∧
        t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w13 : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = BitVec.ofNat 64 n := by
    rw [L.sp]; exact (R.fr 13 (by decide)).trans h13
  have l104 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by rw [L.sp]; exact L.ld (d := 104) (by decide)
  have s152 : InRegions s.wr (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.st (d := 152) (by decide)
  have hm := movi_ofNat hp
  unfold Impl.Dsa.AArch64.Generation.Refill.shortStatus Impl.Dsa.AArch64.Generation.Refill.windowBytes
  brun [State.write, exec_ldrSp (off := 104) (by decide), exec_storeSp (off := 152) (by decide), w13, l104, s152, hm,
    refill_subs_ge hn (show 128 * pLen < 2 ^ 64 by omega_using [hp])]
  rw [L.sp]
  by_cases hc : 128 * pLen ≤ n
  · simp only [hc, decide_true, ite_true, show ¬ n < 128 * pLen by omega_using [hc], ite_false]; rfl
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, show n < 128 * pLen by omega_using [hc], ite_true]; rfl

theorem foundStatus_run {s : State} {F S : Addr} (L : Lay s F S) {c : Nat} (hc : 1 ≤ c ∧ c < 4) (hx : s.gpr .x3 = BitVec.ofNat 64 c) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 (2 * c - 1)) := by
  have s152 : InRegions s.wr (s.sp + BitVec.ofNat 64 152) 8 := by rw [L.sp]; exact L.st (d := 152) (by decide)
  have e : BitVec.ofNat 64 c + BitVec.ofNat 64 c - BitVec.ofNat 64 1 = BitVec.ofNat 64 (2 * c - 1) := by
    rw [← BitVec.ofNat_add, Offset.ofNat_sub_ofNat (by omega_using [hc])]; congr 1; omega_using []
  unfold Impl.Dsa.AArch64.Generation.Refill.foundStatus
  brun [State.write, exec_subImm_x' (by decide : 1 < 4096), exec_storeSp (off := 152) (by decide), s152, hx, e]
  rw [L.sp]

/-- The stage's result as the seed's status, and its candidates' octets
consumed. -/
theorem stageStatus_run {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {c b u n pLen : Nat} (hc : c = 1 ∨ c = 2 ∨ c = 3)
    (hb : b < 2 ^ 32) (hx : s.gpr .x0 = BitVec.ofNat 64 (c + 4 * b))
    (h16 : W 16 = BitVec.ofNat 64 u) (h13 : W 13 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) (hp : 128 * pLen < 2 ^ 16) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.stageStatus pLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.Refill.stageStatus
  refine WP.seq (WP.mono (consumed_run L R (by omega_using [hc]) hb hx h16) fun u₁ ⟨⟨hm₁, h3, h4⟩, k₁⟩ => ?_)
  have R₁ : Rep u₁.mem F S V (upd W 16 (BitVec.ofNat 64 (u + b))) := by
    rw [hm₁]; exact R.wf L.geo (k := 16) (by decide) _
  have L₁ := lay_of_rep L R R₁ (by simp [upd]) k₁.sp k₁.wr
  have f₁ : Frame [⟨F, frameBytes⟩] s.mem u₁.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (cF F (d := 128) (by decide))
  have done : ∀ (v : Nat) (t : State), t.mem = u₁.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 v) →
      t.sp = u₁.sp → t.rd = u₁.rd → t.wr = u₁.wr → v = refillStatus c n pLen →
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    intro v t hm hsp hrd hwr hv
    subst hv
    have Rt : Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 (u + b))) 19 (BitVec.ofNat 64 (refillStatus c n pLen))) := by
      rw [hm]; exact R₁.wf L₁.geo (k := 19) (by decide) _
    refine ⟨lay_of_rep L₁ R₁ Rt (by simp [upd]) hsp hwr, Rt, ?_, hrd.trans k₁.rd, hwr.trans k₁.wr⟩
    rw [hm]
    exact f₁.writeW List.mem_cons_self _ (cF F (d := 152) (by decide))
  by_cases h3c : c = 3
  · subst h3c
    refine WP.ite true (by simp [eval, State.read, h4]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    have h13' : upd W 16 (BitVec.ofNat 64 (u + b)) 13 = BitVec.ofNat 64 n := by simp [upd, h13]
    refine WP.mono (shortStatus_run L₁ R₁ h13' hn hp) fun t ⟨hm, hsp, hrd, hwr⟩ =>
      done _ t hm hsp hrd hwr (by simp [refillStatus])
  · have hc' : c = 1 ∨ c = 2 := by omega_using [hc, h3c]
    refine WP.ite false (by
      simp only [eval, State.read, h4, BitVec.setWidth_eq, Option.some.injEq, beq_eq_false_iff_ne]
      rcases hc' with rfl | rfl <;> decide) (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.mono (WP.keep [.x3] (foundStatus_run L₁ (by omega_using [hc]) h3) (by decide)) fun t ⟨hm, kt⟩ =>
      done _ t hm kt.sp kt.rd kt.wr (by simp [refillStatus, h3c])

/-! ## After `p`: the window, the stage and the status -/

theorem GenerationGeometry.frame_bytes {g : GenerationGeometry} {m m' : Mem}
    (hf : Frame [⟨g.F, frameBytes⟩] m m') {d n : Nat} (hd : d + n ≤ usedBytes g.pLen) :
    Spec.Rsa.bytesAt m' (VG.Proof.Bignum.off g.B d) n = Spec.Rsa.bytesAt m (VG.Proof.Bignum.off g.B d) n := by
  have pn : g.pLen ≤ 384 := by rcases g.width with hh | hh | hh <;> omega_using [hh]
  apply VG.Proof.Dsa.Generation.frame_bytesAt hf
  · intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (g.frame_part hd).symm
  · unfold usedBytes domainCheck at hd; omega_using [hd, pn]

/-- The generation's memory after the stage's call: the frame and the hash
workspace are as they were. -/
theorem generatorCalled_memory {p : GenerationContext} {W : Nat → BitVec 64} {s u t : State}
    {value qval : Nat} (h : GenerationMemory p W s) (C : GeneratorCalled p value qval s u t)
    (hu : u.wr = s.wr) (hr : u.rd = s.rd) :
    ∃ V, Lay t p.geo.F p.geo.hash ∧ Rep t.mem p.geo.F p.geo.hash V W ∧ Frame p.changed s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have L := h.layout
  obtain ⟨V, R⟩ := h.rep
  have hashKept : ∀ o < oRsa, t.mem (VG.Proof.Bignum.off p.geo.hash o) = s.mem (VG.Proof.Bignum.off p.geo.hash o) := by
    intro o ho
    have c8 : VG.Impl.Dsa.Generation.Layout.hash = 16384 := rfl
    have c9 : oRsa = 8192 := rfl
    have hw8 : 8 * (usedBytes p.geo.pLen / 8) = usedBytes p.geo.pLen := by
      rcases p.geo.width with hw | hw | hw <;> rw [hw] <;> decide
    have hhb : VG.Impl.Dsa.Generation.Layout.hash + oRsa ≤ usedBytes p.geo.pLen :=
      p.geo.small_bound (by decide) (by decide)
    have k := C.keeps (VG.Impl.Dsa.Generation.Layout.hash + o) (by omega_using [ho, hw8, hhb]) (by
      intro r hr
      have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hw | hw | hw <;> omega_using [hw]
      have qn : Impl.Dsa.AArch64.Generator.qLen p.geo.pLen ≤ 32 := by
        unfold Impl.Dsa.AArch64.Generator.qLen; split <;> omega_using []
      simp only [Impl.Dsa.AArch64.Generator.layout, Impl.Dsa.AArch64.Generator.scratch, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [parent, g, packed, Impl.Dsa.AArch64.Generator.spill,
          VG.Impl.Dsa.Generation.Layout.control, arithmetic, domainCheck, Impl.Dsa.Layout.activeBytes,
          Impl.Dsa.AArch64.Generator.spillBytes, Impl.Dsa.Layout.usedBytes, arithmeticBytes] <;> omega_arith)
    simpa only [GenerationGeometry.hash, VG.Proof.Bignum.off, BitVec.add_assoc, BitVec.ofNat_add] using k
  have frameKept : ∀ k < nW, VG.Proof.Bignum.word t.mem p.geo.F (8 * k) = W k := by
    intro k hk
    rw [← R.fr k hk]
    refine C.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    have hf : Region.Sub ⟨VG.Proof.Bignum.off p.geo.F (8 * k), 8⟩ ⟨p.geo.F, frameBytes⟩ :=
      Offset.sub_base _ (by have : nW = 34 := rfl; have : frameBytes = 272 := rfl; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact p.geo.frameArena.sub_left hf
    · exact p.geo.frame_below.sub_left hf
  have Rt : Rep t.mem p.geo.F p.geo.hash V W :=
    ⟨fun o ho => (hashKept o ho).trans (R.scr o ho), frameKept⟩
  have Lt : Lay t p.geo.F p.geo.hash := lay_of_rep L R Rt rfl (C.sp.trans L.sp.symm) (C.wr.trans hu)
  refine ⟨V, Lt, Rt, Frame.sub C.frame fun r hr => ?_, C.rd.trans hr, C.wr.trans hu⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩
  · exact ⟨_, by simp [GenerationContext.changed], fun _ h => h⟩

theorem stage_code_cases (p q : Nat) (hs : List Nat) :
    Proof.Dsa.GeneratorStage.code p q hs = 1 ∨ Proof.Dsa.GeneratorStage.code p q hs = 2 ∨
      Proof.Dsa.GeneratorStage.code p q hs = 3 := by
  unfold Proof.Dsa.GeneratorStage.code
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem refillGenerator_ok (G : GeneratorStage) {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (value qval : Nat)
    (domain : VG.Proof.Dsa.Generation.PDomain p.geo.pLen value) (qfit : qval < 256 ^ p.geo.qLen) (qpos : 0 < qval)
    (bp : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
      Spec.Dsa.encodeBE p.geo.pLen value)
    (be : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen =
      Spec.Dsa.encodeBE p.geo.pLen ((value - 1) / qval))
    (bq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen qval)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length)
    {res : Option (Option Spec.Dsa.Params × List Byte)}
    (hnone : Spec.Dsa.generator value qval (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen
        Spec.Dsa.generatorAttempts (p.rand.bytes.drop used)) = none →
      res = if Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length then
        some (none, (p.rand.bytes.drop used).drop (Spec.Dsa.generatorAttempts * p.geo.pLen)) else none)
    (hsome : ∀ gv, Spec.Dsa.generator value qval (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen
        Spec.Dsa.generatorAttempts (p.rand.bytes.drop used)) = some gv →
      res = some (if Spec.Dsa.parametersValid ⟨value, qval, gv⟩ then some ⟨value, qval, gv⟩ else none,
        (p.rand.bytes.drop used).drop (p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval
          (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used))))) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run p.geo.pLen) s (RefillFinished p W res s) := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have p0 : 0 < p.geo.pLen := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have hp_b : VG.Impl.Dsa.Generation.Layout.p + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have he_b : exponent + p.geo.pLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have hq_b : q + p.geo.qLen ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [qn])
  have hpk_b : packed + (2 * p.geo.pLen + p.geo.qLen) ≤ usedBytes p.geo.pLen :=
    p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  obtain ⟨n, hn⟩ : ∃ n, n = min (p.rand.bytes.length - used) (128 * p.geo.pLen) := ⟨_, rfl⟩
  have rlen : (p.rand.bytes.drop used).length = p.rand.bytes.length - used := List.length_drop
  have hwin : used + n ≤ p.rand.bytes.length := by omega_using [hu, hn]
  let win := p.rand.slice used n hwin
  have hsub : Region.Sub ⟨win.ptr, win.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩ := by
    rw [slice_length]
    exact Offset.sub_base p.rand.ptr hwin
  have hlen : (VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
      (p.rand.bytes.drop used)).length = n / p.geo.pLen := by
    simp only [VG.Proof.Dsa.Generation.windowCandidates, List.length_map, Spec.Dsa.generationChunks,
      List.length_range, List.length_take, rlen, Spec.Dsa.generatorAttempts]
    rw [hn, Nat.min_comm]
  have hcand : (Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE =
      VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts (p.rand.bytes.drop used) := by
    show (Spec.Dsa.generationChunks p.geo.pLen ((p.rand.bytes.drop used).take n)).map Spec.Dsa.decodeBE = _
    have ht : (p.rand.bytes.drop used).take n =
        (p.rand.bytes.drop used).take (Spec.Dsa.generatorAttempts * p.geo.pLen) :=
      List.take_eq_take_iff.mpr (by rw [rlen]; unfold Spec.Dsa.generatorAttempts; omega_using [hn])
    unfold VG.Proof.Dsa.Generation.windowCandidates
    rw [ht]
  simp only [Impl.Dsa.AArch64.Generation.Refill.refillGenerator, VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (refillWindow_ok h h16 hu hn) fun u ⟨mu, fu, ru, wu⟩ => ?_)
  refine WP.seq (WP.mono (generatorCallArgs_ok (p := p.withHs win) mu) fun v ⟨h0, h1, h2, h3, hmv, kv⟩ => ?_)
  have hsp : v.sp = p.geo.F := kv.sp.trans mu.layout.sp
  refine WP.seq (WP.mono (generatorCall_call_ok (p := p.withHs win) G mu value qval domain qfit qpos
    ((p.geo.frame_bytes fu hp_b).trans bp) ((p.geo.frame_bytes fu he_b).trans be)
    ((p.geo.frame_bytes fu hq_b).trans bq) h0 h1 h2 h3 hmv hsp kv.rd kv.wr) fun t C => ?_)
  obtain ⟨V, Lt, Rt, ft, rt, wt⟩ := generatorCalled_memory mu C kv.wr kv.rd
  have hx0 : t.gpr .x0 = BitVec.ofNat 64 (Proof.Dsa.GeneratorStage.result p.geo.pLen value qval
      ((Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE)) := C.status
  have hpk : ∀ a, Proof.Dsa.GeneratorStage.stage value qval
      ((Spec.Dsa.generationChunks p.geo.pLen win.bytes).map Spec.Dsa.decodeBE) = some a →
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) =
        Spec.Dsa.encodeParams p.geo.pLen p.geo.qLen a := C.packed
  rw [hcand] at hx0 hpk
  generalize hhs : VG.Proof.Dsa.Generation.windowCandidates p.geo.pLen Spec.Dsa.generatorAttempts
    (p.rand.bytes.drop used) = hs at hx0 hpk hnone hsome hlen
  have hc : p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs ≤ n :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _)
      (Nat.le_of_eq hlen))) (Nat.mul_div_le n _)
  let c := Proof.Dsa.GeneratorStage.code value qval hs
  let b := p.geo.pLen * VG.Proof.Dsa.Generation.generatorCount value qval hs
  have hx : t.gpr .x0 = BitVec.ofNat 64 (c + 4 * b) := hx0
  have t16 : upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n) 16 = BitVec.ofNat 64 used := by
    simp [upd, h16]
  have t13 : upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n) 13 = BitVec.ofNat 64 n := by
    simp [upd]
  refine WP.mono (stageStatus_run Lt Rt (stage_code_cases value qval hs) (by omega) hx t16 t13 (by omega_using [pn, hn]) (by omega_using [pn]))
    fun t' ⟨Lt', Rt', ft', rt', wt'⟩ => ?_
  have fut : Frame p.changed u.mem t'.mem := ft.trans (GenerationContext.frame_single ft')
  have fsx : Frame p.changed s.mem t'.mem := (GenerationContext.frame_single fu).trans fut
  have rsx : t'.rd = s.rd := rt'.trans (rt.trans ru)
  have wsx : t'.wr = s.wr := wt'.trans (wt.trans wu)
  let Wt := upd (upd (upd (upd W 11 (VG.Proof.Bignum.off p.rand.ptr used)) 13 (BitVec.ofNat 64 n)) 16
    (BitVec.ofNat 64 (used + b))) 19 (BitVec.ofNat 64 (refillStatus c n p.geo.pLen))
  have mt : GenerationMemory (p.withHs win) Wt t' := by
    refine mu.frame Lt' ⟨V, Rt'⟩ (fun k hk => ?_) fut (rt'.trans rt) (wt'.trans wt)
    have : k ≠ 16 ∧ k ≠ 19 := by simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simp [Wt, upd, this.1, this.2]
  have hbound : used + b ≤ p.rand.bytes.length := by omega_using [hu, hn, hc]
  have wslots : ∀ k ∈ refillSlots, Wt k = W k := by
    intro k hk
    have : k ≠ 11 ∧ k ≠ 13 ∧ k ≠ 16 ∧ k ≠ 19 := by
      simp only [refillSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [hk]
    simp [Wt, upd, this.1, this.2.1, this.2.2.1, this.2.2.2]
  have w16 : Wt 16 = BitVec.ofNat 64 (used + b) := by simp [Wt, upd]
  have w19 : Wt 19 = BitVec.ofNat 64 (refillStatus c n p.geo.pLen) := by simp [Wt, upd]
  have hdrop : ∀ k, (p.rand.bytes.drop used).drop k = p.rand.bytes.drop (used + k) := fun _ => List.drop_drop
  refine ⟨win, Wt, used + b, hsub, mt, hbound, w16, wslots, ?_, fsx, rsx, wsx⟩
  cases hg : Spec.Dsa.generator value qval hs with
  | none =>
    have hcode : c = 3 := by simp [c, Proof.Dsa.GeneratorStage.code, hg]
    have hcount := generatorCount_of_none hg
    by_cases short : n < 128 * p.geo.pLen
    · have hnot : ¬ (Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length) := by
        simp only [rlen, Spec.Dsa.generatorAttempts]; omega_using [hu, pn, p0, qn, hp_b, he_b, hq_b, hpk_b, hn, hwin, hc, hbound, hcount, short]
      refine Or.inl ⟨by rw [w19, hcode]; simp [refillStatus, short], by rw [hnone hg, ite_eq_right hnot]⟩
    · have hn128 : n = 128 * p.geo.pLen := by omega_using [hn, short]
      have hc128 : VG.Proof.Dsa.Generation.generatorCount value qval hs = 128 := by
        rw [hcount, hlen, hn128, Nat.mul_div_cancel _ p0]
      have hyes : Spec.Dsa.generatorAttempts * p.geo.pLen ≤ (p.rand.bytes.drop used).length := by
        simp only [rlen, Spec.Dsa.generatorAttempts]; omega_using [hwin, short]
      refine Or.inr (Or.inl ⟨by rw [w19, hcode]; simp [refillStatus, short], ?_⟩)
      rw [hnone hg, ite_eq_left hyes, hdrop]
      congr 3
      simp only [b, hc128, Spec.Dsa.generatorAttempts, Nat.mul_comm]
  | some gv =>
    rw [hsome gv hg, hdrop]
    by_cases valid : Spec.Dsa.parametersValid ⟨value, qval, gv⟩
    · have hcode : c = 1 := by simp [c, Proof.Dsa.GeneratorStage.code, hg, valid]
      refine Or.inr (Or.inr ⟨by rw [w19, hcode]; rfl, ⟨value, qval, gv⟩, by simp only [valid, ite_true]; rfl, ?_⟩)
      have hst : Proof.Dsa.GeneratorStage.stage value qval hs = some ⟨value, qval, gv⟩ := by
        simp [Proof.Dsa.GeneratorStage.stage, hg, valid]
      rw [VG.Proof.Dsa.Generation.frame_bytesAt ft' (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact (p.geo.frame_part hpk_b).symm) (by omega_using [pn, qn])]
      exact hpk _ hst
    · have hcode : c = 2 := by simp [c, Proof.Dsa.GeneratorStage.code, hg, valid]
      exact Or.inr (Or.inl ⟨by rw [w19, hcode]; rfl, by simp only [valid, ite_false]; rfl⟩)

/-! ## The seed -/

theorem refillPrimeFinish_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (hhs : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
      Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes))
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length)
    {rest : List Byte}
    (hprime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) rest =
      some (true, p.rand.bytes.drop used)) :
    WP isa (.seq (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run p.geo.pLen p.geo.qLen)
      (Impl.Dsa.AArch64.Generation.onSuccess
        (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run p.geo.pLen))) s
      (RefillFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest) s) := by
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases p.geo.qWidth with hh | hh <;> omega_using [hh] : 2 ≤ 8 * p.geo.qLen) seed.bytes
  have qfit : Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes < 256 ^ p.geo.qLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using shape.2.2
  have qpos : 0 < Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1
  refine WP.seq (WP.mono (seedPrime_ok H T h seed hlen hseed h1 hq h16 hu)
    fun u ⟨Wu, usedu, huu, mu, u16, slots, bqu, result, fu, ru, wu⟩ => ?_)
  rcases result with ⟨h19, hr⟩ | ⟨h19, value, hr, domain, bp, be⟩ | ⟨h19, hr⟩
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (0 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine refillFinished_of mt hhs huu u16 slots (Or.inl ⟨h19, ?_⟩) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]
  · apply onSuccess_generation_ok mu
    · intro v mv hm kv _
      have bv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B VG.Impl.Dsa.Generation.Layout.p) p.geo.pLen =
          Spec.Dsa.encodeBE p.geo.pLen value := hm ▸ bp
      have ev : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B exponent) p.geo.pLen = Spec.Dsa.encodeBE p.geo.pLen
          ((value - 1) / Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ be
      have qv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen = Spec.Dsa.encodeBE p.geo.qLen
          (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
      have call := refillGenerator_ok G mv value (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) domain qfit qpos
        bv ev qv u16 huu
        (res := VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes rest)
        (fun hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
        (fun gv hg => by simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr, hg])
      exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.rd.trans ru) (kv.wr.trans wu)
    · intro _ _ _ _ hn
      exact False.elim (hn h19)
  · apply onSuccess_generation_ok mu
    · intro _ _ _ _ hs
      have impossible : (3 : BitVec 64) = 1 := h19.symm.trans hs
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine refillFinished_of mt hhs huu u16 slots (Or.inr (Or.inl ⟨h19, ?_⟩)) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, hprime, hr]

/-- One seed of the refillable-tape search, at `W 1`, with its witnesses
and its generator's candidates read from `rand` after its first `used`
octets. -/
theorem refillAttempt_ok (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s)
    (hhs : Region.Sub ⟨p.hs.ptr, p.hs.bytes.length⟩ ⟨p.rand.ptr, p.rand.bytes.length⟩)
    (seed : GenerationTape p.geo) (hlen : seed.bytes.length = p.geo.qLen)
    (hseed : GenerationTapeMemory seed s) (h1 : W 1 = seed.ptr)
    {used : Nat} (h16 : W 16 = BitVec.ofNat 64 used) (hu : used ≤ p.rand.bytes.length) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run p.geo.pLen p.geo.qLen) s
      (RefillFinished p W (VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen seed.bytes
        (p.rand.bytes.drop used)) s) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.refillAttempt
  refine WP.seq (WP.mono (seedSubgroup_ok H T h seed hlen hseed h1 h16 hu)
    fun u ⟨usedu, status, huu, mu, bqu, fail, result, fu, ru, wu⟩ => ?_)
  let Wu := upd (upd (seedWords W p.geo.qLen) 16 (BitVec.ofNat 64 usedu)) 19 status
  have u16 : Wu 16 = BitVec.ofNat 64 usedu := by simp [Wu, upd]
  have u19 : Wu 19 = status := by simp [Wu, upd]
  have slots : ∀ k ∈ searchSlots, Wu k = W k := by
    intro k hk
    simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | simpa [Wu, seedWords, upd] using ((h.slots 26 (by simp [generationSlots])).trans p.hashLenSlot).symm
  have u1 : Wu 1 = seed.ptr := (slots 1 (by simp [searchSlots])).trans h1
  have seedu := hseed.frame fu ru wu
  cases qr : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) (p.rand.bytes.drop used) with
  | none =>
    have hs : Wu 19 = 0 := u19.trans (fail qr)
    apply onSuccess_generation_ok mu
    · intro _ _ _ _ accepted
      have impossible : (0 : BitVec 64) = 1 := hs.symm.trans accepted
      exact False.elim (by cases impossible)
    · intro t mt hm kt _
      refine refillFinished_of mt hhs huu u16 slots (Or.inl ⟨hs, ?_⟩) (by rw [hm]; exact fu)
        (kt.rd.trans ru) (kt.wr.trans wu)
      simp only [VG.Proof.Dsa.Generation.refillAttempt, qr]
  | some pair =>
    rcases pair with ⟨accepted, rest⟩
    obtain ⟨hs, cursor⟩ := result accepted rest qr
    have suffix : p.rand.bytes.drop usedu = rest := by
      rw [cursor]
      exact VG.Proof.Dsa.Generation.probablePrime_cursor qr
    cases accepted with
    | false =>
      have hstatus : Wu 19 = 3 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro _ _ _ _ accepted
        have impossible : (3 : BitVec 64) = 1 := hstatus.symm.trans accepted
        exact False.elim (by cases impossible)
      · intro t mt hm kt _
        refine refillFinished_of mt hhs huu u16 slots (Or.inr (Or.inl ⟨hstatus, ?_⟩)) (by rw [hm]; exact fu)
          (kt.rd.trans ru) (kt.wr.trans wu)
        simp only [VG.Proof.Dsa.Generation.refillAttempt, qr, suffix]
    | true =>
      have hstatus : Wu 19 = 1 := u19.trans hs
      apply onSuccess_generation_ok mu
      · intro v mv hm kv _
        have seedv := seedu.frame (p := p) (by rw [hm]; exact Frame.refl _ _) kv.rd kv.wr
        have qv : Spec.Rsa.bytesAt v.mem (VG.Proof.Bignum.off p.geo.B q) p.geo.qLen =
            Spec.Dsa.encodeBE p.geo.qLen (Spec.Dsa.qCandidate (8 * p.geo.qLen) seed.bytes) := hm ▸ bqu
        have call := refillPrimeFinish_ok H G T mv hhs seed hlen seedv u1 qv u16 huu (by rw [qr, suffix])
        exact WP.mono call fun t ht => ht.prepend slots (by rw [hm]; exact fu) (kv.rd.trans ru) (kv.wr.trans wu)
      · intro _ _ _ _ hn
        exact False.elim (hn hstatus)

end VG.Proof.Dsa.AArch64.Generation
