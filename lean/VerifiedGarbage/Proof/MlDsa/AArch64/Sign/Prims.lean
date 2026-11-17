module

public import VerifiedGarbage.Proof.MlDsa.HighPackContract
public import VerifiedGarbage.Proof.MlDsa.ResidentMaskContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Inline
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Base
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Frag

/-! ### `MlDsa.AArch64.Sign.CallMore`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on AArch64: calls of the other primitives

As `Proof/MlDsa/AArch64/Call/`, for the other primitives signing calls: `vg_mldsa_expand_mask_poly` and
`vg_mldsa_hint_bit_pack`.

Signing branches on the results of the two samplers, so it needs them to be
the same in two runs whose samplers' public data agree: a callee whose
result is public in its own runs (`RetPub`) returns the same in both
(`RelCT.callRet`, `callAt_trRet`). And its leakage is stated for
`maxBounds`, so it needs that a sampler succeeds only if the algorithm
finishes within them: a fact of each run of the callee added to its
postcondition (`withPost`, `CalleeOk.withPost`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Results that are public -/

/-- The result `w0` of `c` is the same in two runs from states that satisfy
`k.pre` and agree on `k.pub` but for the mode (`Contract.ditFree`). -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.ditFree.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32

/-- Code that never touches the mode and whose result is public in its own runs
under its public data with the mode has it public without (`Exec.withDit`). -/
theorem RetPub.of_noDit {k : Contract isa} {c : Prog isa} (hc : c.all (fun i => !i.touchesDit) = true)
    (hpre : ∀ s d, k.pre s → k.pre (s.withDit d))
    (h : RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32) : RetPub k c :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨p₁, p₂, hp⟩ e₁ e₂ =>
    h s₁ (s₂.withDit s₁.dit) t₁ t₂ s₁' (s₂'.withDit s₁.dit) ⟨p₁, hpre _ _ p₂, hp⟩ e₁ (Exec.withDit hc e₂ _)

/-- The run of verified code from a state with more permissions than its
contract gives it is the run its contract describes, but for the permissions. -/
theorem run_narrow {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {t : List Leak} {s' : State}
    (he : Exec isa c s t s') : ∃ s'', Exec isa c (s.withRegions rd wr) t s'' ∧ s''.gpr = s'.gpr := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  have hw' := Exec.widen he' (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, rfl⟩ := Exec.det he hw'
  exact ⟨_, he', rfl⟩

/-- A call of verified code whose result is public in its own runs: the same
trace, and the same result. -/
theorem RelCT.callRet {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.ditFree.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr ∧
      Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr) :
    RelCT isa P (.call n c) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      rw [call_callEntry, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨_, n₁, g₁⟩ := run_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂, g₂⟩ := run_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hx⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ n₁ n₂
      simp only [isa, ret] at r₁ r₂
      split at r₁ <;> [skip; cases r₁]
      split at r₂ <;> [skip; cases r₂]
      cases r₁; cases r₂
      refine ⟨by simp only [ht], ?_⟩
      show (s₁'.gpr .x0).setWidth 32 = (s₂'.gpr .x0).setWidth 32
      rw [← g₁, ← g₂]; exact hx

/-- The trace of the moves then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem callAt_trRet {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    (hr : RetPub k c) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.ditFree.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok hok hnd x, glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.ditFree.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.callRet C.correct hr a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

/-- A genuine inline body retains the public sampler result. -/
theorem inlineBody_trRet {c : Prog isa} {k : Contract isa}
    (hv : ∀s,k.pre s → ∃t s',Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hr : RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀x y,P x y → k.pre (x.withRegions rd wr) ∧ k.pre (y.withRegions rd wr) ∧
      k.ditFree.pub (x.withRegions rd wr) (y.withRegions rd wr) ∧
      Covers (rd++wr) (x.rd++x.wr) ∧ Covers wr x.wr ∧
      Covers (rd++wr) (y.rd++y.wr) ∧ Covers wr y.wr) :
    RelCT isa P c fun x y=>(x.gpr .x0).setWidth 32=(y.gpr .x0).setWidth 32 := by
  intro x y tx ty u v hp ex ey
  obtain ⟨px,py,pub,cx,wx,cy,wy⟩:=hP x y hp
  obtain ⟨u',eu,gu⟩:=run_narrow hv px cx wx ex
  obtain ⟨v',ev,gv⟩:=run_narrow hv py cy wy ey
  obtain ⟨et,er⟩:=hr _ _ _ _ _ _ ⟨px,py,pub⟩ eu ev
  exact ⟨et,by simpa only [gu,gv] using er⟩

theorem inlineAt_trRet {S : Nat} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    (hr : RetPub k c) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.withRegions rd wr) ∧ k.pre (y1.withRegions rd wr) ∧
      k.ditFree.pub (x1.withRegions rd wr) (y1.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (.seq (.block (glue as)) c) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok hok hnd x, glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.withRegions a.1 a.2) ∧ k.pre (y1.withRegions a.1 a.2) ∧
        k.ditFree.pub (x1.withRegions a.1 a.2) (y1.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => inlineBody_trRet C.correct hr a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

/-- A sampler's call leaves the result `w0` public in two runs whose seeds agree. -/
theorem rejNttAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S))
    (hr : RetPub (rejNTTContract AArch64.abi S) P.rejNTT)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 34 = bytesAt y.mem (pa y seed) 34 ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT (rejNttArgs seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet C hr (rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rejNtt_pre Lx hc h1, ?_, ?_, (rejNtt_cov Lx hc).1, (rejNtt_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rejNtt_pre Ly hc h2
  · sig_pub [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).2

theorem rejNttInlineK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S))
    (hr : RetPub (rejNTTContract AArch64.abi S) P.rejNTT)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 34 = bytesAt y.mem (pa y seed) 34 ∧ SameB x y) :
    RelCT isa Q (.seq (.block (glue (rejNttArgs seed a ss))) P.rejNTT)
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine inlineAt_trRet C hr (rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rejNttInline_pre Lx hc h1, ?_, ?_, (rejNtt_cov Lx hc).1, (rejNtt_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rejNttInline_pre Ly hc h2
  · sig_pub [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rejNtt_cov Ly hc).2

theorem ballAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.ball (sampleInBallContract AArch64.abi S))
    (hr : RetPub (sampleInBallContract AArch64.abi S) P.ball)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {ct c ss : Ptr} {len : Nat}
    (hc : ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x ct) len = bytesAt y.mem (pa y ct) len ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_sample_in_ball" ++ P.suffix) P.ball (ballArgs ct len tau c ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega_using [ht]
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : ct.1 ∈ bases ∧ c.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet C hr (ball_args hB len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, ball_pre Lx hc ht h1, ?_, ?_, (ball_cov Lx hc).1, (ball_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact ball_pre Ly hc ht h2
  · sig_pub [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl])]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, trivial, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).2

/-! ## `ExpandMask` -/

def maskChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 66 a 1024 && sepB rbs wbs seed 66 ss 2048 && sepB rbs wbs a 1024 ss 2048 &&
    inB (rbs ++ wbs) seed 66 && inB (rbs ++ wbs) a 1024 && inB (rbs ++ wbs) ss 2048 && inB wbs a 1024 &&
    inB wbs ss 2048

abbrev maskArgs (seed : Ptr) (γ : Nat) (a ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr seed), (.x1, .imm γ), (.x2, .ptr a), (.x3, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : maskChk rbs wbs seed a ss = true)
include L hc

theorem mask_cov : Covers ([⟨pa s seed, 66⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem mask_pre {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {s1 : State} (h1 : Args (maskArgs seed γ a ss) s s1) :
    (expandMaskContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega_arith)]
  cpre L
  exact hγ

theorem mask_inline_pre {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {s1 : State} (h1 : Args (maskArgs seed γ a ss) s s1) :
    (expandMaskContract AArch64.abi S).pre
      (s1.withRegions [⟨pa s seed, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega_arith)]
  cpre L
  exact hγ

end

theorem mask_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (γ : Nat) (c4 : inB bs seed 66 = true)
    (c5 : inB bs a 1024 = true) (c6 : inB bs ss 2048 = true) :
    ∀ x ∈ maskArgs seed γ a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩,
    ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem maskAtCall_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : maskChk rbs wbs seed a ss = true) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    WP isa (callAt ("vg_mldsa_expand_mask_poly" ++ P.suffix) P.expandMask (maskArgs seed γ a ss)) s fun s' =>
      PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (mask_args L.ok γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mask_pre L hc hγ h1) (mask_cov L hc).1 (mask_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega_arith)] at hq
  exact hq

theorem maskAtCall_tr {S : Nat} {P : Prims} (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : maskChk rbs wbs seed a ss = true)
    {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_expand_mask_poly" ++ P.suffix) P.expandMask (maskArgs seed γ a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (mask_args hB γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, mask_pre Lx hc hγ h1, ?_, ?_, (mask_cov Lx hc).1, (mask_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact mask_pre Ly hc hγ h2
  · sig_pub [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).2

theorem maskAtInline_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : maskChk rbs wbs seed a ss = true) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    WP isa (.seq (.block (glue (maskArgs seed γ a ss))) P.expandMask) s fun s' =>
      PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (inlineAt_ok hS C (mask_args L.ok γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => mask_inline_pre L hc hγ h1) (mask_cov L hc).1 (mask_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega_arith)] at hq
  exact hq

theorem maskAtInline_tr {S : Nat} {P : Prims} (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : maskChk rbs wbs seed a ss = true)
    {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (.seq (.block (glue (maskArgs seed γ a ss))) P.expandMask) fun _ _ => True := by
  have hc' := hc
  simp only [maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine inlineAt_tr C (mask_args hB γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, mask_inline_pre Lx hc hγ h1, ?_, ?_, (mask_cov Lx hc).1, (mask_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact mask_inline_pre Ly hc hγ h2
  · sig_pub [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (mask_cov Ly hc).2

theorem maskAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : maskChk rbs wbs seed a ss = true) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    WP isa (maskCallAt P seed γ a ss) s fun s' =>
      PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s seed) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  unfold maskCallAt
  split
  · exact maskAtCall_ok hS C L hc hγ
  · exact maskAtInline_ok hS C L hc hγ

theorem maskAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : maskChk rbs wbs seed a ss = true)
    {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ SameB x y) :
    RelCT isa Q (maskCallAt P seed γ a ss) fun _ _ => True := by
  unfold maskCallAt
  split
  · exact maskAtCall_tr C hB hc hγ hQ
  · exact maskAtInline_tr C hB hc hγ hQ

/-! ## `MakeHint` -/

def hintChk (rbs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  sepB rbs wbs z 1024 h 1024 && sepB rbs wbs r 1024 h 1024 && inB (rbs ++ wbs) z 1024 &&
    inB (rbs ++ wbs) r 1024 && inB (rbs ++ wbs) h 1024 && inB wbs h 1024

/-! ## `HintBitPack` -/

abbrev hbpArgs (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr h), (.x1, .imm hlen), (.x2, .imm omega), (.x3, .ptr y), (.x4, .imm len)]

theorem hbp_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {h y : Ptr} (hlen omega len : Nat)
    (c2 : inB bs h (hlen * 4) = true) (c3 : inB bs y len = true) :
    ∀ x ∈ hbpArgs h hlen omega y len, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_kept L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `HintBitPack` asks of its arguments. -/
structure HbpOk (hlen omega len : Nat) : Prop where
  hp : (omega, len - omega) ∈ hintParams
  hle : omega ≤ len
  hh : hlen = 256 * (len - omega)
  hlt : hlen < 2 ^ 32 ∧ omega < 2 ^ 32 ∧ len < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h y : Ptr} {hlen omega len : Nat}
  (hc : rwChk rbs wbs h (hlen * 4) y len = true)
include L hc

theorem hbp_pre (hb : HbpOk hlen omega len) (hn : hintOnes (hintAt s.mem (pa s h) (len - omega)) ≤ omega)
    {s1 : State} (h1 : Args (hbpArgs h hlen omega y len) s s1) :
    (hintBitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s h, hlen * 4⟩] [⟨pa s y, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  sig_pre [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega_using [l1]),
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega_using [l3])]
  cpre L
  exacts [hb.hp, hb.hle, hb.hh, hn]

end

theorem hbpAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : HbpOk hlen omega len)
    (hn : hintOnes (hintAt s.mem (pa s h) (len - omega)) ≤ omega) :
    WP isa (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (hbpArgs h hlen omega y len)) s fun s' =>
      PPostB S s s' [(y, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s y) len = hintBitPack omega (len - omega) (hintAt s.mem (pa s h) (len - omega)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  refine WP.mono (callAt_ok hS C (hbp_args L.ok hlen omega len c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => hbp_pre L hc hb hn h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega_using [l3])] at hq
  exact hq

theorem hbpAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : HbpOk hlen omega len) {Q : State → State → Prop}
    (hQ : ∀ x y', Q x y' → Lay S rbs wbs x ∧ Lay S rbs wbs y' ∧
      hintOnes (hintAt x.mem (pa x h) (len - omega)) ≤ omega ∧
      hintOnes (hintAt y'.mem (pa y' h) (len - omega)) ≤ omega ∧
      (List.range hlen).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range hlen).map (fun i => (coeffAt y'.mem (pa y' h) i).toNat) ∧ SameB x y') :
    RelCT isa Q (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (hbpArgs h hlen omega y len)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  have hbs : h.1 ∈ bases ∧ y.1 ∈ bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (hbp_args hB hlen omega len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y' x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, nx, ny, hl, e⟩ := hQ x y' hp
  refine ⟨_, _, hbp_pre Lx hc hb nx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact hbp_pre Ly hc hb ny h2
  · sig_pub [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega_using [l1])]
    exact ⟨e.2, hl, e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-!
# ML-DSA signing on AArch64: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is correct and constant time under its shared contract
(`Proof/MlDsa/Contract.lean`) with the `S` bytes of stack the function gives its
calls, and its frames use at most those (`CalleeOk`); and, of the two samplers
whose result the function branches on, that the result is public in their own
runs (`RetPub`) and that they succeed only when the algorithm finishes within
`maxBounds`, the bounds the leakage of signing is stated for.

For each call of a primitive, as the proof of signing uses it: what it does
(`…_ok`), and that two runs in the same layout leak the same (`…_tr`), from
the calls of `Proof/MlDsa/AArch64/Call/` and `CallMore.lean`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- What the proofs need of the implementations `P` of the primitives, with
`S` bytes of stack for each call. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  s16 : 16 ≤ S
  sl : S < 2 ^ 16
  ntt : CalleeOk S P.ntt (nttContract AArch64.abi S)
  rej4 : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S)
  rej4Ret : RetPub (rejNTT4Contract AArch64.abi S) P.rej4
  rej4Max : ∀ s t s', (rejNTT4Contract AArch64.abi S).pre s → Exec isa P.rej4 s t s' →
    (s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (s.gpr .x0) k)).isSome
  rejNTT : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S)
  expandMask : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S)
  expandMaskPair : CalleeOk S P.expandMaskPair (expandMaskPairContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  highPack : ∀ g, g ∈ gamma2s → CalleeOk S (P.highPack g) (highPackContract g AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  hintBitPack : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S)
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : RetPub (rejNTTContract AArch64.abi S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract AArch64.abi S).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .x0) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : RetPub (sampleInBallContract AArch64.abi S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract AArch64.abi S).pre s → Exec isa P.ball s t s' →
    (s'.gpr .x0).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .x2).setWidth 32).toNat maxBounds.ball (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).isSome

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega_using [this]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem LRel.same {x y : State} (R : LRel D rbs wbs x y) : SameB x y := ⟨R.regs, R.sp⟩

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of an in-place transformation of `f` needs of the layout. -/
abbrev ipChkS (rbs wbs : List (Reg × Nat)) (f : Ptr) : Bool := ipChk rbs wbs f (sc oPS)

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
abbrev rejChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := rejNttChk rbs wbs (sc oRS) a (sc oPS)

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCallRaw_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChkS rbs wbs a = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))]) s
      fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (pa s a)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.rejNTT.withPost hP.rejMax) (rejNtt_args L.ok c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => rejNtt_pre L hc h1) (rejNtt_cov L hc).1
    (rejNtt_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), Args.r0 h1, Args.mem h1, Arg.val] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCallRaw_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChkS rbs wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))])
      fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => rejNttAtK_trRet (Q := fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34) hP.rejNTT hP.rejRet hp.1.ok hc
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem rejCallInline_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChkS rbs wbs a = true) :
    WP isa (.seq (.block (glue [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))])) P.rejNTT) s
      fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (pa s a)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (inlineAt_ok L.s64 (hP.rejNTT.withPost hP.rejMax) (rejNtt_args L.ok c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => rejNttInline_pre L hc h1) (rejNtt_cov L hc).1
    (rejNtt_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTTContract, rejNTTSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, Args.r0 h1, Args.mem h1, Arg.val] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCallInline_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChkS rbs wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (.seq (.block (glue [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))])) P.rejNTT)
      fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => rejNttInlineK_trRet (Q := fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34) hP.rejNTT hP.rejRet hp.1.ok hc
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem rejCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChkS rbs wbs a = true) :
    WP isa (rejCallAt P a) s
      fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (pa s a)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  unfold rejCallAt
  split
  · exact rejCallRaw_ok hP L hc
  · exact rejCallInline_ok hP L hc

theorem rejCall_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChkS rbs wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (rejCallAt P a)
      fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 := by
  unfold rejCallAt
  split
  · exact rejCallRaw_tr hP hc
  · exact rejCallInline_tr hP hc

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
abbrev maskChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := maskChk rbs wbs (sc oMS) a (sc oPS)

theorem maskAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChkS rbs wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) :=
  maskAtK_ok L.s64 hP.expandMask L hc hγ

theorem maskAt_tr {P : Prims} (hP : PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : maskChkS rbs wbs a = true) :
    RelCT isa (LRel D rbs wbs) (maskAt P γ a) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => maskAtK_tr (Q := LRel D rbs wbs) hP.expandMask hp.ok hc hγ
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
abbrev ballChkS (rbs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool := ballChk rbs wbs (sc oCT) len c (sc oPS)

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChkS rbs wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s (sc oCT)) len)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s c)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (pa s (sc oCT)) len)).isSome) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega_using [hp]
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.ball.withPost hP.ballMax) (ball_args L.ok len tau c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => ball_pre L hc hp h1) (ball_cov L hc).1
    (ball_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl]), imm32 hl.2] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1,
    Arg.val] at hx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hl]), imm32 hl.2] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : ballChkS rbs wbs len c = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => ballAtK_trRet (Q := fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len) hP.ball hP.ballRet hq.1.ok hc hp
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
abbrev normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool := inB bs f 1024

/-! ## Encodings -/

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpOk_of {a b len : Nat} (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) : BpOk a b len := by
  obtain ⟨h1, h2, h3⟩ := bitPackParams_lt hp
  exact ⟨hp, hl, h1, h2, by rw [hl]; exact h3⟩

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
abbrev InRange (m : Mem) (p : Addr) (a b : Nat) : Prop := BpRange m p a b

theorem bpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true)
    (hr : Reduced s.mem (pa s f)) (hrg : InRange s.mem (pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s out) len = bitPack ((polyAt s.mem (pa s f)).map fun c => modPm c.val q) a b :=
  AArch64.bpAt_ok L.s64 hP.bitPack L hc (bpOk_of hp hl) hr hrg

theorem bpAt_tr {P : Prims} (hP : PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => AArch64.bpAt_tr (Q := fun x y => LRel D rbs wbs x y ∧ (Reduced x.mem (pa x f) ∧ InRange x.mem (pa x f) a b) ∧
      (Reduced y.mem (pa y f) ∧ InRange y.mem (pa y f) a b)) hP.bitPack hq.1.ok hc (bpOk_of hp hl)
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem bupAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) (toRq (bitUnpack (bytesAt s.mem (pa s v) len) a b)) :=
  buAt_ok L.s64 hP.bitUnpack L hc (bpOk_of hp hl)

theorem bupAt_tr {P : Prims} (hP : PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    RelCT isa (LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => buAt_tr (Q := LRel D rbs wbs) hP.bitUnpack hq.ok hc (bpOk_of hp hl)
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpOk_of {ω k : Nat} (hp : (ω, k) ∈ hintParams) : HbpOk (256 * k) ω (ω + k) := by
  obtain ⟨h1, h2, h3⟩ := hintParams_lt hp
  exact ⟨by rw [show ω + k - ω = k by omega_using []]; exact hp, by omega_using [], by rw [show ω + k - ω = k by omega_using []], h3, h1, h2⟩

theorem hbpAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ bytesAt s'.mem (pa s y) (ω + k) = hintBitPack ω k (hintAt s.mem (pa s h) k) := by
  have ek : ω + k - ω = k := by omega_using []
  have := hbpAtK_ok L.s64 hP.hintBitPack L hc (hbpOk_of hp) (by rw [ek]; exact hones)
  rw [ek] at this
  exact this

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  have ek : ω + k - ω = k := by omega_using []
  exact fun x z t₁ t₂ x' z' hq e₁ e₂ => hbpAtK_tr (Q := fun x z => LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (pa z h) i).toNat)) hP.hintBitPack hq.1.ok hc (hbpOk_of hp)
    (fun _ _ ⟨R, ox, oz, hl⟩ => ⟨R.lx, R.ly, by rw [ek]; exact ox, by rw [ek]; exact oz, hl, R.same⟩)
    x z t₁ t₂ x' z' hq e₁ e₂

end

end VG.Proof.MlDsa.AArch64.Sign
