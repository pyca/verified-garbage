import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlDsa.Sign.Vals
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.MlDsa.Sign.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Base`. -/
section

/-!
# ML-DSA signing on AArch64: the layout registers

The proof of `vg_mldsa*_sign` uses the framework of
`Proof/MlDsa/AArch64/Call/`: the function keeps the addresses of its buffers
in `bases`, which two runs agree on (`SameB`, `LRel`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.x23, .x25, .x26, .x27, .x28]

theorem bases_pres : ∀ r ∈ VG.Proof.MlDsa.AArch64.Sign.bases, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem bases_kept : ∀ r ∈ VG.Proof.MlDsa.AArch64.Sign.bases, r ∈ keptRegs := by decide

/-- The buffers of a layout are in the registers `bases`. -/
abbrev LayOk : List (Reg × Nat) → Prop := LayIn VG.Proof.MlDsa.AArch64.Sign.bases

/-- Two states whose layout registers and stack pointer agree. -/
abbrev SameB : State → State → Prop := SameIn VG.Proof.MlDsa.AArch64.Sign.bases

/-! ## Two runs in the same layout -/

/-- Two states in the same layout (whose buffers are in `bases`), with the
same stack pointer. -/
structure LRel (S : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : Lay S rbs wbs x
  ly : Lay S rbs wbs y
  regs : ∀ r ∈ VG.Proof.MlDsa.AArch64.Sign.bases, x.gpr r = y.gpr r
  sp : x.sp = y.sp
  ok : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)

theorem LRel.pa {S : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x y) {p : Ptr}
    (hp : p.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases) : VG.Proof.MlDsa.AArch64.pa x p = VG.Proof.MlDsa.AArch64.pa y p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, h.regs _ hp]

theorem LRel.post {S : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x y) (hx : PostB S x x' W₁) (hy : PostB S y y' W₂) : VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x' y' :=
  ⟨h.lx.post hx, h.ly.post hy, fun r hr => by
    rw [hx.bs r (VG.Proof.MlDsa.AArch64.Sign.bases_kept r hr), hy.bs r (VG.Proof.MlDsa.AArch64.Sign.bases_kept r hr), h.regs r hr], by rw [hx.sp, hy.sp, h.sp], h.ok⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CallMore`. -/
section

/-!
# ML-DSA signing on AArch64: calls of the other primitives

As `Proof/MlDsa/AArch64/Call/`, for the other primitives signing calls: `vg_mldsa_expand_mask_poly`, `vg_mldsa_high_bits`,
`vg_mldsa_low_bits`, `vg_mldsa_make_hint` and `vg_mldsa_hint_bit_pack`.

Signing branches on the results of the two samplers, so it needs them to be
the same in two runs whose samplers' public data agree: a callee whose
result is public in its own runs (`RetPub`) returns the same in both
(`RelCT.callRet`, `callAt_trRet`). And its leakage is stated for
`maxBounds`, so it needs that a sampler succeeds only if the algorithm
finishes within them: a fact of each run of the callee added to its
postcondition (`withPost`, `CalleeOk.withPost`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Results that are public -/

/-- The result `w0` of `c` is the same in two runs from states that satisfy
`k.pre` and agree on `k.pub`. -/
def RetPub (k : Contract isa) (c : Prog isa) : Prop :=
  RelCT isa (fun s₁ s₂ => k.pre s₁ ∧ k.pre s₂ ∧ k.pub s₁ s₂) c
    fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32

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
    (hr : VG.Proof.MlDsa.AArch64.Sign.RetPub k c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      k.pre (s₁.callEntry.withRegions rd wr) ∧ k.pre (s₂.callEntry.withRegions rd wr) ∧
      k.pub (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) ∧
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
      obtain ⟨_, n₁, g₁⟩ := VG.Proof.MlDsa.AArch64.Sign.run_narrow hv p₁ (by simpa using c₁) (by simpa using w₁) b₁
      obtain ⟨_, n₂, g₂⟩ := VG.Proof.MlDsa.AArch64.Sign.run_narrow hv p₂ (by simpa using c₂) (by simpa using w₂) b₂
      obtain ⟨ht, hx⟩ := hr _ _ _ _ _ _ ⟨p₁, p₂, hpub⟩ n₁ n₂
      simp only [isa, VG.AArch64.ret] at r₁ r₂
      split at r₁ <;> [skip; cases r₁]
      split at r₂ <;> [skip; cases r₂]
      cases r₁; cases r₂
      refine ⟨by simp only [ht], ?_⟩
      show (s₁'.gpr .x0).setWidth 32 = (s₂'.gpr .x0).setWidth 32
      rw [← g₁, ← g₂]; exact hx

/-- The trace of the moves then a call whose result is public: the same
trace, and the same result, in both runs. -/
theorem callAt_trRet {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    (hr : VG.Proof.MlDsa.AArch64.Sign.RetPub k c) {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.AArch64.Args as x x1 → VG.Proof.MlDsa.AArch64.Args as y y1 → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ VG.Proof.MlDsa.AArch64.Args as x x1 ∧ VG.Proof.MlDsa.AArch64.Args as y y1)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glue_ok hok hnd x, glue_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.callRet C.correct hr a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)

/-- A sampler's call leaves the result `w0` public in two runs whose seeds agree. -/
theorem rejNttAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S))
    (hr : VG.Proof.MlDsa.AArch64.Sign.RetPub (rejNTTContract AArch64.abi S) P.rejNTT)
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rejNttChk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x seed) 34 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y seed) 34 ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT (rejNttArgs seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rejNttChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine VG.Proof.MlDsa.AArch64.Sign.callAt_trRet C hr (rejNtt_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
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

theorem ballAtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.ball (sampleInBallContract AArch64.abi S))
    (hr : VG.Proof.MlDsa.AArch64.Sign.RetPub (sampleInBallContract AArch64.abi S) P.ball)
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {ct c ss : Ptr} {len : Nat}
    (hc : ballChk rbs wbs ct len c ss = true) {tau : Nat} (ht : (len, tau) ∈ ballParams) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x ct) len = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y ct) len ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_sample_in_ball" ++ P.suffix) P.ball (ballArgs ct len tau c ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ht; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : ct.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ c.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine VG.Proof.MlDsa.AArch64.Sign.callAt_trRet C hr (ball_args hB len tau c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, ball_pre Lx hc ht h1, ?_, ?_, (ball_cov Lx hc).1, (ball_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact ball_pre Ly hc ht h2
  · sig_pub [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, trivial, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (ball_cov Ly hc).2

/-! ## `ExpandMask` -/

def maskChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 66 a 1024 && sepB rbs wbs seed 66 ss 2048 && sepB rbs wbs a 1024 ss 2048 &&
    VG.CallLay.inB (rbs ++ wbs) seed 66 && VG.CallLay.inB (rbs ++ wbs) a 1024 && VG.CallLay.inB (rbs ++ wbs) ss 2048 && VG.CallLay.inB wbs a 1024 &&
    VG.CallLay.inB wbs ss 2048

abbrev maskArgs (seed : Ptr) (γ : Nat) (a ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr seed), (.x1, .imm γ), (.x2, .ptr a), (.x3, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.Sign.maskChk rbs wbs seed a ss = true)
include L hc

theorem mask_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s seed, 66⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem mask_pre {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.Sign.maskArgs seed γ a ss) s s1) :
    (expandMaskContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s seed, 66⟩] [⟨VG.Proof.MlDsa.AArch64.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 2048⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.maskChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega)]
  cpre L
  exact hγ

end

theorem mask_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (γ : Nat) (c4 : VG.CallLay.inB bs seed 66 = true)
    (c5 : VG.CallLay.inB bs a 1024 = true) (c6 : VG.CallLay.inB bs ss 2048 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.Sign.maskArgs seed γ a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩,
    ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem maskAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.Sign.maskChk rbs wbs seed a ss = true) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    WP isa (callAt ("vg_mldsa_expand_mask_poly" ++ P.suffix) P.expandMask (VG.Proof.MlDsa.AArch64.Sign.maskArgs seed γ a ss)) s fun s' =>
      PPostB S s s' [(a, 1024), (ss, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s a) (toRq (VG.Spec.MlDsa.bitUnpack (H (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s seed) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.Sign.mask_args L.ok γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.mask_pre L hc hγ h1) (VG.Proof.MlDsa.AArch64.Sign.mask_cov L hc).1 (VG.Proof.MlDsa.AArch64.Sign.mask_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega)] at hq
  exact hq

theorem maskAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.maskChk rbs wbs seed a ss = true)
    {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_expand_mask_poly" ++ P.suffix) P.expandMask (VG.Proof.MlDsa.AArch64.Sign.maskArgs seed γ a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.maskChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.Sign.mask_args hB γ c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.mask_pre Lx hc hγ h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.Sign.mask_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.Sign.mask_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.Sign.mask_pre Ly hc hγ h2
  · sig_pub [expandMaskContract, expandMaskSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.mask_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.mask_cov Ly hc).2

/-! ## `HighBits` and `LowBits` -/

/-- The contract of `vg_mldsa_high_bits` or `vg_mldsa_low_bits`: `bitsSig`'s,
with the postcondition `Q γ₂ (the polynomial at r) m' out`. -/
abbrev bitsC (Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop) (S : Nat) : Contract isa :=
  bitsSig.contract AArch64.abi
    (pre := fun r gamma2 _out m => gamma2.toNat ∈ gamma2s ∧ Reduced m r)
    (post := fun r gamma2 out m m' _ => Q gamma2.toNat (polyAt m r) m' out)
    (writeArgs := true)
    (stack := S)

abbrev bitsArgs (r : Ptr) (g2 : Nat) (out : Ptr) : List (Reg × Arg) := [(.x0, .ptr r), (.x1, .imm g2), (.x2, .ptr out)]

theorem bits_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {r out : Ptr} (g2 : Nat) (c2 : VG.CallLay.inB bs r 1024 = true)
    (c3 : VG.CallLay.inB bs out 1024 = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.Sign.bitsArgs r g2 out, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_kept L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {r out : Ptr}
  (hc : rwChk rbs wbs r 1024 out 1024 = true)
include L hc

theorem bits_pre {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r))
    {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.Sign.bitsArgs r g2 out) s s1) :
    (VG.Proof.MlDsa.AArch64.Sign.bitsC Q S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s r, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s out, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [bitsSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hr]

end

theorem bitsAtK_ok {S : Nat} (hS : S < 2 ^ 64) {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : CalleeOk S c (VG.Proof.MlDsa.AArch64.Sign.bitsC Q S)) {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {r out : Ptr}
    (hc : rwChk rbs wbs r 1024 out 1024 = true) {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r)) :
    WP isa (callAt n c (VG.Proof.MlDsa.AArch64.Sign.bitsArgs r g2 out)) s fun s' => PPostB S s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Q g2 (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r)) s'.mem (VG.Proof.MlDsa.AArch64.pa s out) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.Sign.bits_args L.ok g2 c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.bits_pre L hc hg hr h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [bitsSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 (gamma2_lt hg)] at hq
  exact hq

theorem bitsAtK_tr {S : Nat} {Q : Nat → VG.Spec.MlDsa.Poly → Mem → Addr → Prop} {n : String} {c : Prog isa}
    (C : CalleeOk S c (VG.Proof.MlDsa.AArch64.Sign.bitsC Q S)) {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {r out : Ptr}
    (hc : rwChk rbs wbs r 1024 out 1024 = true) {g2 : Nat} (hg : g2 ∈ gamma2s) {R : State → State → Prop}
    (hR : ∀ x y, R x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r) ∧
      VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa R (callAt n c (VG.Proof.MlDsa.AArch64.Sign.bitsArgs r g2 out)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hb : r.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ out.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.Sign.bits_args hB g2 c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hR x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.bits_pre Lx hc hg rx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact VG.Proof.MlDsa.AArch64.Sign.bits_pre Ly hc hg ry h2
  · sig_pub [bitsSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, trivial, e.pa hb.2⟩
  · rw [e.pa hb.1, e.pa hb.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hb.2]; exact (rw_cov Ly hc).2

/-! ## `MakeHint` -/

def hintChk (rbs wbs : List (Reg × Nat)) (z r h : Ptr) : Bool :=
  sepB rbs wbs z 1024 h 1024 && sepB rbs wbs r 1024 h 1024 && VG.CallLay.inB (rbs ++ wbs) z 1024 &&
    VG.CallLay.inB (rbs ++ wbs) r 1024 && VG.CallLay.inB (rbs ++ wbs) h 1024 && VG.CallLay.inB wbs h 1024

abbrev hintArgs (z r : Ptr) (g2 : Nat) (h : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm g2), (.x3, .ptr h)]

theorem hint_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {z r h : Ptr} (g2 : Nat) (c3 : VG.CallLay.inB bs z 1024 = true)
    (c4 : VG.CallLay.inB bs r 1024 = true) (c5 : VG.CallLay.inB bs h 1024 = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.Sign.hintArgs z r g2 h, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c3), by decide⟩, ⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_kept L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {z r h : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.Sign.hintChk rbs wbs z r h = true)
include L hc

theorem hint_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s z, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s r, 1024⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hintChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, _⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c3) (L.cR c4)) (Covers.right (L.cW c6)), L.cW c6⟩

theorem hint_pre {g2 : Nat} (hg : g2 ∈ gamma2s) (hz : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r))
    {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.Sign.hintArgs z r g2 h) s s1) :
    (makeHintContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s z, 1024⟩, ⟨VG.Proof.MlDsa.AArch64.pa s r, 1024⟩] [⟨VG.Proof.MlDsa.AArch64.pa s h, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hintChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hz, hr]

end

theorem hintAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.makeHint (makeHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {z r h : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.hintChk rbs wbs z r h = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) (hz : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r)) :
    WP isa (callAt "vg_mldsa_make_hint" P.makeHint (VG.Proof.MlDsa.AArch64.Sign.hintArgs z r g2 h)) s fun s' =>
      PPostB S s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      HintIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint g2) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r))] ∧
      ((s'.gpr .x0).setWidth 32).toNat =
        hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint g2) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r))] := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.hintChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.Sign.hint_args L.ok g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.hint_pre L hc hg hz hr h1) (VG.Proof.MlDsa.AArch64.Sign.hint_cov L hc).1 (VG.Proof.MlDsa.AArch64.Sign.hint_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 (gamma2_lt hg)] at hq
  exact hq

theorem hintAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.makeHint (makeHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {z r h : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.hintChk rbs wbs z r h = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x z) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y z) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r)) ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_make_hint" P.makeHint (VG.Proof.MlDsa.AArch64.Sign.hintArgs z r g2 h)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.hintChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  have hb : z.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ r.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ h.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.Sign.hint_args hB g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.hint_pre Lx hc hg rx.1 rx.2 h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.Sign.hint_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.Sign.hint_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.Sign.hint_pre Ly hc hg ry.1 ry.2 h2
  · sig_pub [makeHintContract, makeHintSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, trivial, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.hint_cov Ly hc).1
  · rw [e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.hint_cov Ly hc).2

/-! ## `HintBitPack` -/

abbrev hbpArgs (h : Ptr) (hlen omega : Nat) (y : Ptr) (len : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr h), (.x1, .imm hlen), (.x2, .imm omega), (.x3, .ptr y), (.x4, .imm len)]

theorem hbp_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {h y : Ptr} (hlen omega len : Nat)
    (c2 : VG.CallLay.inB bs h (hlen * 4) = true) (c3 : VG.CallLay.inB bs y len = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.Sign.hbpArgs h hlen omega y len, x.2.Ok ∧ x.1 ∈ argRegs := by
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

theorem hbp_pre (hb : VG.Proof.MlDsa.AArch64.Sign.HbpOk hlen omega len) (hn : hintOnes (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s h) (len - omega)) ≤ omega)
    {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.Sign.hbpArgs h hlen omega y len) s s1) :
    (hintBitPackContract AArch64.abi S).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s h, hlen * 4⟩] [⟨VG.Proof.MlDsa.AArch64.pa s y, len⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  sig_pre [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)]
  cpre L
  exacts [hb.hp, hb.hle, hb.hh, hn]

end

theorem hbpAtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : VG.Proof.MlDsa.AArch64.Sign.HbpOk hlen omega len)
    (hn : hintOnes (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s h) (len - omega)) ≤ omega) :
    WP isa (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (VG.Proof.MlDsa.AArch64.Sign.hbpArgs h hlen omega y len)) s fun s' =>
      PPostB S s s' [(y, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s y) len = VG.Spec.MlDsa.hintBitPack omega (len - omega) (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s h) (len - omega)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.Sign.hbp_args L.ok hlen omega len c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.hbp_pre L hc hb hn h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 l2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega)] at hq
  exact hq

theorem hbpAtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {h y : Ptr} {hlen omega len : Nat}
    (hc : rwChk rbs wbs h (hlen * 4) y len = true) (hb : VG.Proof.MlDsa.AArch64.Sign.HbpOk hlen omega len) {Q : State → State → Prop}
    (hQ : ∀ x y', Q x y' → Lay S rbs wbs x ∧ Lay S rbs wbs y' ∧
      hintOnes (hintAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) (len - omega)) ≤ omega ∧
      hintOnes (hintAt y'.mem (VG.Proof.MlDsa.AArch64.pa y' h) (len - omega)) ≤ omega ∧
      (List.range hlen).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) i).toNat) =
        (List.range hlen).map (fun i => (coeffAt y'.mem (VG.Proof.MlDsa.AArch64.pa y' h) i).toNat) ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y') :
    RelCT isa Q (callAt "vg_mldsa_hint_bit_pack" P.hintBitPack (VG.Proof.MlDsa.AArch64.Sign.hbpArgs h hlen omega y len)) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have l1 := hb.hlt.1; have l2 := hb.hlt.2.1; have l3 := hb.hlt.2.2
  have hbs : h.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ y.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.Sign.hbp_args hB hlen omega len c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y' x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, nx, ny, hl, e⟩ := hQ x y' hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.hbp_pre Lx hc hb nx h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.Sign.hbp_pre Ly hc hb ny h2
  · sig_pub [hintBitPackContract, hintBitPackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by omega)]
    exact ⟨e.2, hl, e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks`. -/
section

/-!
# ML-DSA signing on AArch64: the blocks between the calls

What the function's own instructions do, in its layout, besides those of
`Proof/MlDsa/AArch64/Call/Blocks.lean`: stores of 8 bytes (`setQ_ok`), copies
of any number of bytes, one at a time (`copy_ok`), the counters `κ` and `CNT`
and the bytes of `κ + r` for `ExpandMask` (`kapAdd_ok`, `cntDec_ok`,
`setKappa_ok`), the sum of the 1s of the hint (`onesAdd_ok`) and its check
(`onesOk_run`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrb wp_ldrw wp_strw wp_ldrx wp_strx
  wp_addImm wp_subImm wp_lsr count_loop)
open VG.Spec.MlDsa (coeffAt integerToBytes)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_add32 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.add .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

end

/-! ## Stores -/

theorem imm64 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The 8 bytes `v` to `p`. -/
theorem setQ_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {p : Ptr} {v : Nat}
    (ho : p.2 % 8 = 0 ∧ p.2 < 4096 * 8) (hv : v < 65536) (hw : VG.CallLay.inB wbs p 8 = true) (hb : p.1 ∈ keptRegs) :
    WP isa (.block (setQ p v)) s fun s' => PPostB S s s' [(p, 8)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9] s s' ∧
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s p) (BitVec.ofNat 64 v) := by
  have h9 := ne_x9 hb
  refine wp_movz fun s₁ h₁ e₁ => wp_strx (a := VG.Proof.MlDsa.AArch64.pa s p) ho (by rw [h₁.get p.1 (by simpa using h9)])
    (by rw [h₁.wr]; exact L.inW hw) fun s₂ h₂ => wp_nil ?_
  have m₂ : s₂.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s p) (BitVec.ofNat 64 v) := by rw [h₂.mem, e₁, h₁.mem, VG.Proof.MlDsa.AArch64.Sign.imm64 hv]
  have k₂ : VG.Proof.MlKem.AArch64.Keep [.x9] s s₂ := (h₁.keep.trans h₂.keep).mono (by simp)
  refine ⟨postB_of_keep k₂ (by decide) ?_, k₂, m₂⟩
  rw [m₂]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The AND of a result -/

/-- A result (1 or 0) as a 64-bit register. -/
abbrev bit (b : Prop) [Decidable b] : BitVec 64 := if b then 1 else 0

theorem bit_and {a b : Prop} [Decidable a] [Decidable b] {x y : BitVec 64} (hx : x = VG.Proof.MlDsa.AArch64.Sign.bit a)
    (hy : y.setWidth 32 = if b then 1 else 0) :
    BitVec.setWidth 64 (x.setWidth 32 &&& y.setWidth 32) = VG.Proof.MlDsa.AArch64.Sign.bit (a ∧ b) := by
  subst hx
  rw [hy]
  by_cases ha : a <;> by_cases hb : b <;> simp [VG.Proof.MlDsa.AArch64.Sign.bit, ha, hb]

theorem bit_setWidth {a : Prop} [Decidable a] : (VG.Proof.MlDsa.AArch64.Sign.bit a).setWidth 32 = if a then 1 else 0 := by
  by_cases ha : a <;> simp [VG.Proof.MlDsa.AArch64.Sign.bit, ha]

/-- A block that writes only `x24` keeps `PostB`. -/
theorem postB24 {S : Nat} {s s' : State} (k : Only [.x24] s s') (W : List Region) : PostB S s s' W :=
  postB_of_keep k.keep (by decide) (by rw [k.mem]; exact Frame.refl _ _)

/-! ## Copies, a byte at a time -/

theorem ne_x0 {r : Reg} (h : r ∈ keptRegs) : r ≠ .x0 := by
  intro e; rw [e] at h; revert h; decide

theorem ne_x1 {r : Reg} (h : r ∈ keptRegs) : r ≠ .x1 := by
  intro e; rw [e] at h; revert h; decide

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1) (h1 : InRegions s.wr (s.gpr .x0) 1) :
    WP isa (.block copyBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x0) (s.mem (s.gpr .x1)) ∧ s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 1 ∧
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 1 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1) ∧
      VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x9] s s' := by
  have e1 : s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 := BitVec.add_zero _
  have e0 : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := BitVec.add_zero _
  refine wp_ldrb (a := s.gpr .x1) (by decide) e1 h0 fun s₁ h₁ v₁ =>
    wp_strb (a := s.gpr .x0) (by decide) (by rw [h₁.get .x0, e0]) (by rw [h₁.wr]; exact h1) fun s₂ h₂ =>
      wp_addImm (by decide) fun s₃ h₃ e₃ => wp_addImm (by decide) fun s₄ h₄ e₄ =>
        wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono (by simp)⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, v₁, h₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [h₅.get .x0, h₄.get .x0, e₃, show s₂.gpr .x0 = s₁.gpr .x0 by rw [h₂.gpr], h₁.get .x0]
  · rw [h₅.get .x1, e₄, h₃.get .x1, show s₂.gpr .x1 = s₁.gpr .x1 by rw [h₂.gpr], h₁.get .x1]
  · rw [e₅, h₄.get .x2, h₃.get .x2, show s₂.gpr .x2 = s₁.gpr .x2 by rw [h₂.gpr], h₁.get .x2]

theorem off_add1 (b : Addr) (i : Nat) : b + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = b + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ofNat_sub_one {n i : Nat} (h : i < n) :
    BitVec.ofNat 64 (n - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The glue of a copy: `x0 ← dst`, `x1 ← src`, `x2 ← n`. -/
theorem copyGlue_ok {dst src : Ptr} {n : Nat} (hd : dst.1 ∈ keptRegs) (hs : src.1 ∈ keptRegs) (s : State) :
    WP isa (.block (lea .x0 dst.1 dst.2 ++ lea .x1 src.1 src.2 ++ movV .x2 n)) s fun s' =>
      (s'.gpr .x0 = VG.Proof.MlDsa.AArch64.pa s dst ∧ s'.gpr .x1 = VG.Proof.MlDsa.AArch64.pa s src ∧ s'.gpr .x2 = BitVec.ofNat 64 n) ∧ Only [.x0, .x1, .x2] s s' := by
  rw [List.append_assoc, ← List.append_nil (movV .x2 n)]
  refine lea_ok (VG.Proof.MlDsa.AArch64.Sign.ne_x0 hd).symm dst.2 fun s₁ h₁ e₁ => lea_ok (VG.Proof.MlDsa.AArch64.Sign.ne_x1 hs).symm src.2 fun s₂ h₂ e₂ =>
    movV_ok .x2 n fun s₃ h₃ e₃ => wp_nil ⟨⟨?_, ?_, e₃⟩, ((h₁.trans h₂).trans h₃).mono (by simp)⟩
  · rw [h₃.get .x0, h₂.get .x0, e₁]
  · rw [h₃.get .x1, e₂, h₁.get src.1 (by simpa using VG.Proof.MlDsa.AArch64.Sign.ne_x0 hs)]

/-- A copy of `n` bytes from `src` to `dst`, apart. -/
theorem copy_core {dst src : Ptr} {n : Nat} (h0 : 0 < n) (hn : n < 2 ^ 32) (hd : dst.1 ∈ keptRegs) (hs : src.1 ∈ keptRegs)
    (s : State) (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s src) n) (hwr : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s dst) n)
    (hdj : Region.Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s src, n⟩ ⟨VG.Proof.MlDsa.AArch64.pa s dst, n⟩) :
    WP isa (copy dst src n) s fun s' =>
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s src) n ∧ Frame [⟨VG.Proof.MlDsa.AArch64.pa s dst, n⟩] s.mem s'.mem ∧
        VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x9] s s' := by
  unfold copy
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.copyGlue_ok hd hs s) fun s1 ⟨⟨a0, a1, a2⟩, k1⟩ => ?_)
  refine WP.mono (count_loop (cr := .x2) (n := n) h0 (fun k s' =>
      s'.gpr .x0 = VG.Proof.MlDsa.AArch64.pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .x1 = VG.Proof.MlDsa.AArch64.pa s src + BitVec.ofNat 64 k ∧
      s'.gpr .x2 = BitVec.ofNat 64 (n - k) ∧ VG.Proof.MlKem.AArch64.Keep [.x0, .x1, .x2, .x9] s s' ∧
      Frame [⟨VG.Proof.MlDsa.AArch64.pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (VG.Proof.MlDsa.AArch64.pa s dst + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlDsa.AArch64.pa s src + BitVec.ofNat 64 j)))
    (fun k hk s' ⟨e0, e1, e2, kk, hf, hc⟩ => ?_)
    ⟨by rw [a0, BitVec.add_zero], by rw [a1, BitVec.add_zero], by rw [a2, Nat.sub_zero], k1.keep.mono (by simp),
      by rw [k1.mem]; exact Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨?_, hf, kk⟩
  · have hsrc : s'.mem (VG.Proof.MlDsa.AArch64.pa s src + BitVec.ofNat 64 k) = s.mem (VG.Proof.MlDsa.AArch64.pa s src + BitVec.ofNat 64 k) :=
      hf.bytes (R := ⟨VG.Proof.MlDsa.AArch64.pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) hk
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.copyBody_ok s' (by rw [kk.rd, kk.wr, e1]; exact VG.CallLay.inRegions_sub hrd (by omega) (by omega))
      (by rw [kk.wr, e0]; exact VG.CallLay.inRegions_sub hwr (by omega) (by omega))) fun s'' ⟨⟨hm, e0', e1', e2'⟩, k'⟩ =>
        ⟨⟨by rw [e0', e0, VG.Proof.MlDsa.AArch64.Sign.off_add1], by rw [e1', e1, VG.Proof.MlDsa.AArch64.Sign.off_add1], by rw [e2', e2, VG.Proof.MlDsa.AArch64.Sign.ofNat_sub_one hk],
          (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [hm, e0]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, e0, e1, Proof.MlKem.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [Proof.MlDsa.KeyGen.ifp rfl, hsrc]
      · rw [Proof.MlDsa.KeyGen.ifn (fun h => e (by
          have h' := congrArg (fun x => x - VG.Proof.MlDsa.AArch64.pa s dst) h
          simp only [Offset.add_sub_cancel_left] at h'
          have := congrArg BitVec.toNat h'
          simp only [BitVec.toNat_ofNat] at this
          omega)), hc j (by omega)]
    · rw [e2', e2, VG.Proof.MlDsa.AArch64.Sign.ofNat_sub_one hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

/-- What a copy of `n` bytes from `src` to `dst` needs of the layout. -/
def copyChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  VG.CallLay.inB wbs dst n && VG.CallLay.inB (rbs ++ wbs) src n && sepB rbs wbs src n dst n && decide (0 < n) && decide (n < 2 ^ 32)

theorem copy_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {dst src : Ptr} {n : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.copyChk rbs wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => PPostB S s s' [(dst, n)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s src) n := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.copyChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨w, i⟩, d⟩, h0⟩, hn⟩ := hc
  have id := (sepB_spec d).2.1
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_core h0 hn (L.ptrBs id) (L.ptrBs i) s (L.inR i) (L.inW w) (L.disj d))
    fun s' ⟨hb, hf, k⟩ => ⟨postB_of_keep k (by decide) hf, k.get .x24, hb⟩

/-! ## Counters -/

theorem ofNat64_add {a b : Nat} : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

/-- `KAP ← KAP + ℓ`. -/
theorem kapAdd_ok (p : Spec.MlDsa.Params) (hl : p.ℓ < 4096) (s : State) (hw : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 8)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 8) :
    WP isa (.block (kapAdd p)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) (s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 + BitVec.ofNat 64 p.ℓ) ∧
        VG.Proof.MlKem.AArch64.Keep [.x9] s s' := by
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) (by decide) rfl hrd fun s₁ h₁ e₁ => wp_addImm hl fun s₂ h₂ e₂ =>
    wp_strx (a := VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact hw)
      fun s₃ h₃ => wp_nil ⟨?_, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem]

/-- `CNT ← CNT - 1`, and `x9 = CNT`. -/
theorem cntDec_ok (s : State) (hw : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 8)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 8) :
    WP isa (.block cntDec) s fun s' =>
      (s'.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) (s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 - BitVec.ofNat 64 1) ∧
        s'.gpr .x9 = s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 - BitVec.ofNat 64 1) ∧ VG.Proof.MlKem.AArch64.Keep [.x9] s s' := by
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) (by decide) rfl hrd fun s₁ h₁ e₁ => wp_subImm (by decide) fun s₂ h₂ e₂ =>
    wp_strx (a := VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact hw)
      fun s₃ h₃ => wp_nil ⟨⟨?_, ?_⟩, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  · rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem]
  · rw [show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁]

/-- The two bytes of `KAP + r` to `MS + 64`. -/
theorem setKappa_run (r : Nat) (hr : r < 4096) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 8) (h2 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 1)
    (h3 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) 1) :
    WP isa (.block (setKappa r)) s fun s' =>
      s'.mem = (s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)))
        ((s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) (((s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
        VG.Proof.MlKem.AArch64.Keep [.x9] s s' := by
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_addImm hr fun s₂ h₂ e₂ =>
    wp_strb (a := VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_lsr (by decide) fun s₄ h₄ e₄ =>
        wp_strb (a := VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) (by decide) (by rw [h₄.get .x28, show s₃.gpr .x28 = s₂.gpr .x28 by
                                 rw [h₃.gpr], h₂.get .x28, h₁.get .x28]) (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact h3)
          fun s₅ h₅ => wp_nil ⟨?_, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono
            (by simp)⟩
  rw [h₅.mem, e₄, h₄.mem, h₃.mem, show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁, h₂.mem, h₁.mem]

/-! ## The 1s of the hint -/

theorem onesAdd_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 8)
    (h2 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 8) :
    WP isa (.block onesAdd) s fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.AArch64.pa s (sc oONES))
      (BitVec.setWidth 64 ((s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 64).setWidth 32 + (s.gpr .x0).setWidth 32)) ∧
      VG.Proof.MlKem.AArch64.Keep [.x9] s s' := by
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.pa s (sc oONES)) (by decide) rfl h1 fun s₁ h₁ e₁ => VG.Proof.MlDsa.AArch64.Sign.wp_add32 fun s₂ h₂ e₂ =>
    wp_strx (a := VG.Proof.MlDsa.AArch64.pa s (sc oONES)) (by decide) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_nil ⟨?_, ((h₁.keep.trans h₂.keep).trans h₃.keep).mono (by simp)⟩
  rw [h₃.mem, e₂, e₁, h₂.mem, h₁.mem, h₁.get .x0]

theorem onesOk_run (p : Spec.MlDsa.Params) (hω : p.ω + 1 < 4096) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 8) :
    WP isa (.block (onesOk p)) s fun s' => (s'.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&&
      ((s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 64 - BitVec.ofNat 64 (p.ω + 1)) >>> 63).setWidth 32) ∧
      s'.mem = s.mem) ∧ VG.Proof.MlKem.AArch64.Keep [.x9, .x24] s s' := by
  refine wp_ldrx (a := VG.Proof.MlDsa.AArch64.pa s (sc oONES)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_subImm hω fun s₂ h₂ e₂ =>
    wp_lsr (by decide) fun s₃ h₃ e₃ => wp_and32 fun s₄ h₄ e₄ =>
      wp_nil ⟨⟨?_, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]⟩,
        ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep)).mono (by simp)⟩
  rw [e₄, e₃, e₂, e₁, h₃.get .x24, h₂.get .x24, h₁.get .x24]

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Top`. -/
section

/-!
# ML-DSA signing on AArch64: the function's contract, layout, entry and exit

The contract the proof is written against (`signK`, which the shared contract
implies), the layout of the function's buffers (`sk`, `mu`, `rnd` read, in
`x25`, `x26`, `x27`; `scratch` and `sig` written, in `x28` and `x23`), what
holds of the state throughout (`Top`: the permissions and the stack pointer of
entry, the pointers in their registers, the callee-saved registers it never
writes, and the caller's registers saved in `scratch`), the saves (`pro_ok`),
the return (`epi_ok`), branches on `w24` (`ifOkElse_ok`, `ifOkElse_tr`) and
sequences of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm wp_ldrx in_rd_wr)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`, with `S` bytes of stack
below `sp`, and the leakage `signLeakT`. -/
def signK (p : Params) (S : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩] ∧
    s.wr = [⟨s.gpr .x3, p.sigLen⟩, ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x3, p.sigLen⟩ ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x0, p.skLen⟩ ∧ (below s.sp S).Disjoint ⟨s.gpr .x1, 64⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x2, 32⟩ ∧ (below s.sp S).Disjoint ⟨s.gpr .x3, p.sigLen⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ ∧
    (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + VG.Proof.MlDsa.AArch64.Sign.scrLen p ≤ 2 ^ 64 ∧
    S ≤ s.sp.toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .x0) p.skLen) (bytesAt s.mem (s.gpr .x1) 64)
      (bytesAt s.mem (s.gpr .x2) 32)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x3) p.sigLen)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    signLeakT p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) 64)
        (bytesAt s₁.mem (s₁.gpr .x2) 32) =
      signLeakT p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) 64)
        (bytesAt s₂.mem (s₂.gpr .x2) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.x25, p.skLen), (.x26, 64), (.x27, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.x28, VG.Proof.MlDsa.AArch64.Sign.scrLen p), (.x23, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := VG.Proof.MlDsa.AArch64.Sign.sgR p ++ VG.Proof.MlDsa.AArch64.Sign.sgW p

/-- The pointers the function keeps, and the registers they arrive in. -/
abbrev sgM : List (Reg × Reg) := [(.x28, .x4), (.x25, .x0), (.x26, .x1), (.x27, .x2), (.x23, .x3)]

theorem sgB_bases (p : Params) : ∀ b ∈ VG.Proof.MlDsa.AArch64.Sign.sgB p, b.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := by
  intro b hb; simp only [VG.Proof.MlDsa.AArch64.Sign.sgB, VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
theorem sgM_bases : ∀ m ∈ VG.Proof.MlDsa.AArch64.Sign.sgM, m.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := by decide

/-- The callee-saved registers the function never writes. -/
abbrev untouched : List Reg := [.x19, .x20, .x21, .x22]

theorem untouched_kept : ∀ r ∈ VG.Proof.MlDsa.AArch64.Sign.untouched, r ∈ keptRegs := by decide

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .x0

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ m ∈ VG.Proof.MlDsa.AArch64.Sign.sgM, s.gpr m.1 = σ.gpr m.2
  cs : ∀ r ∈ VG.Proof.MlDsa.AArch64.Sign.untouched, s.gpr r = σ.gpr r
  saved : ∀ k < 7, s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc (oSV + 8 * k))) 64 = σ.gpr (VG.Proof.MlDsa.AArch64.Sign.savedReg k)
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

section
variable {p : Params} {S : Nat} {σ : State} (hp : (VG.Proof.MlDsa.AArch64.Sign.signK p S).pre σ)
include hp

theorem sgLay (hsz : VG.Proof.MlDsa.AArch64.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.Top σ s) : Lay S (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e1 : s.gpr .x28 = σ.gpr .x4 := h.regs (.x28, .x4) (by decide)
  have e2 : s.gpr .x25 = σ.gpr .x0 := h.regs (.x25, .x0) (by decide)
  have e3 : s.gpr .x26 = σ.gpr .x1 := h.regs (.x26, .x1) (by decide)
  have e4 : s.gpr .x27 = σ.gpr .x2 := h.regs (.x27, .x2) (by decide)
  have e5 : s.gpr .x23 = σ.gpr .x3 := h.regs (.x23, .x3) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩,
    fun b hb => VG.Proof.MlDsa.AArch64.Sign.bases_kept _ (VG.Proof.MlDsa.AArch64.Sign.sgB_bases p b hb), by rw [h.sp]; exact hsp⟩
  · intro b hb
    simp only [VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    have w : ∀ r, VG.CallLay.isW (VG.Proof.MlDsa.AArch64.Sign.sgW p) r = (r == .x28 || r == .x23) := fun r => by cases r <;> rfl
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [w, beq_iff_eq, reduceCtorEq, Bool.or_eq_true, or_self, or_false, false_or, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e1, e2, e3, e4, e5]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, h.sp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [n1, n2, n3, n5, n4]
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgR, VG.Proof.MlDsa.AArch64.Sign.sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [mem ⟨σ.gpr .x0, p.skLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .x1, 64⟩ (by rw [hrd]; simp),
      mem ⟨σ.gpr .x2, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ (by rw [hwr]; simp),
      mem ⟨σ.gpr .x3, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e1, e5]
    exacts [memw ⟨σ.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ (by rw [hwr]; simp), memw ⟨σ.gpr .x3, p.sigLen⟩ (by rw [hwr]; simp)]

end

/-- The saved registers are apart from the regions `ws`. -/
def topChk (rbs wbs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 7).all fun k => keepB rbs wbs ws (sc (oSV + 8 * k)) 8

theorem Top.step {S : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : VG.Proof.MlDsa.AArch64.Sign.Top σ s)
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : VG.Proof.MlDsa.AArch64.Sign.topChk rbs wbs ws = true) : VG.Proof.MlDsa.AArch64.Sign.Top σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.topChk, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp,
    fun m hm => (hP.bs _ (VG.Proof.MlDsa.AArch64.Sign.bases_kept _ (VG.Proof.MlDsa.AArch64.Sign.sgM_bases m hm))).trans (h.regs m hm),
    fun r hr => by rw [hP.cs r (VG.Proof.MlDsa.AArch64.Sign.untouched_kept r hr), h.cs r hr], fun k hk => ?_,
    fun r hr => (hP.vcs r hr).trans (h.vcs r hr)⟩
  rw [L.keepW hP (hc k hk)]; exact h.saved k hk

/-! ## Saving the registers -/

theorem pro_eq : VG.Impl.MlDsa.AArch64.Sign.pro = (List.range 7).map (fun k => .str .x (savedRegs.getD k .x0) .x4 (oSV + 8 * k)) ++
    ([.addImm .x .x28 .x4 0, .addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0,
      .addImm .x .x23 .x3 0, .movz .x .x24 1 0] : List Instr) := rfl

theorem pro_ok {σ : State} (hin : ∀ k < 7, InRegions σ.wr (σ.gpr .x4 + BitVec.ofNat 64 (oSV + 8 * k)) 8) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Sign.pro) σ fun s => VG.Proof.MlDsa.AArch64.Sign.Top σ s ∧ s.gpr .x24 = 1 ∧
      Frame [⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩] σ.mem s.mem := by
  rw [VG.Proof.MlDsa.AArch64.Sign.pro_eq, WP.block_append_iff]
  refine WP.mono (WP.preservedV (Proof.MlKem.AArch64.KeyGen.saves_ok
    (σ.gpr .x4) .x4 oSV savedRegs (by decide) (by decide) 7
    (by decide) rfl hin) (by lit_decide)) fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ e₂ => wp_addImm (by decide) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_addImm (by decide) fun s₅ h₅ e₅ =>
      wp_addImm (by decide) fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => wp_nil ?_
  have o : Only [.x28, .x25, .x26, .x27, .x23, .x24] s₁ s₇ :=
    (((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  have e28 : s₇.gpr .x28 = σ.gpr .x4 := by
    rw [h₇.get .x28, h₆.get .x28, h₅.get .x28, h₄.get .x28, h₃.get .x28, e₂, BitVec.add_zero, g₁]
  refine ⟨⟨by rw [o.rd, r₁], by rw [o.wr, w₁], by rw [o.sp, p₁], fun m hm => ?_, fun r hr => ?_, fun k hk => ?_,
    fun r hr => (o.vcs r hr).trans (hv₁ r hr)⟩,
    by rw [e₇]; rfl, by rw [o.mem]; exact f₁⟩
  · simp only [VG.Proof.MlDsa.AArch64.Sign.sgM, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact e28
    · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, h₄.get .x25, e₃, BitVec.add_zero, h₂.get .x0, g₁]
    · rw [h₇.get .x26, h₆.get .x26, h₅.get .x26, e₄, BitVec.add_zero, h₃.get .x1, h₂.get .x1, g₁]
    · rw [h₇.get .x27, h₆.get .x27, e₅, BitVec.add_zero, h₄.get .x2, h₃.get .x2, h₂.get .x2, g₁]
    · rw [h₇.get .x23, e₆, BitVec.add_zero, h₅.get .x3, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]
  · rw [o.get r (by revert r; decide), g₁]
  · rw [o.mem, VG.Proof.MlDsa.AArch64.pa, e28]; exact z₁ k hk

/-! ## The return -/

theorem epi_eq : VG.Impl.MlDsa.AArch64.Sign.epi = .addImm .x .x0 .x24 0 :: [.ldr .x .x23 .x28 (oSV + 8 * 0), .ldr .x .x24 .x28 (oSV + 8 * 1),
    .ldr .x .x25 .x28 (oSV + 8 * 2), .ldr .x .x26 .x28 (oSV + 8 * 3), .ldr .x .x27 .x28 (oSV + 8 * 4),
    .ldr .x .x30 .x28 (oSV + 8 * 5), .ldr .x .x28 .x28 (oSV + 8 * 6)] := rfl

theorem epi_ok {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.Top σ s) (hin : ∀ k < 7, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.AArch64.pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block VG.Impl.MlDsa.AArch64.Sign.epi) s fun s' => abiPreserved σ s' ∧ s'.gpr .x0 = s.gpr .x24 ∧ s'.mem = s.mem := by
  have ld : ∀ k < 7, ∀ {w : State}, w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = s.gpr .x28 →
      w.gpr .x28 + BitVec.ofNat 64 (oSV + 8 * k) = VG.Proof.MlDsa.AArch64.pa s (sc (oSV + 8 * k)) ∧
      InRegions (w.rd ++ w.wr) (VG.Proof.MlDsa.AArch64.pa s (sc (oSV + 8 * k))) 8 ∧
      w.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc (oSV + 8 * k))) 64 = σ.gpr (VG.Proof.MlDsa.AArch64.Sign.savedReg k) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ => ⟨by rw [h28], by rw [hr, hw]; exact hin k hk', by rw [hm]; exact h.saved k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = s.gpr .x28 →
      w'.rd = s.rd ∧ w'.wr = s.wr ∧ w'.mem = s.mem ∧ w'.gpr .x28 = s.gpr .x28 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  rw [VG.Proof.MlDsa.AArch64.Sign.epi_eq]
  refine wp_addImm (by decide) fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, rfl⟩
  have l₁ := ld 0 (by decide) g₁
  refine wp_ldrx (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 1 (by decide) g₂
  refine wp_ldrx (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 2 (by decide) g₃
  refine wp_ldrx (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 3 (by decide) g₄
  refine wp_ldrx (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 4 (by decide) g₅
  refine wp_ldrx (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 5 (by decide) g₆
  refine wp_ldrx (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ => ?_
  have g₇ := st h₇ (by decide) g₆
  have l₇ := ld 6 (by decide) g₇
  refine wp_ldrx (by decide) l₇.1 l₇.2.1 fun s₈ h₈ e₈ => wp_nil ?_
  have o₈ : Only [.x0, .x23, .x24, .x25, .x26, .x27, .x30, .x28] s s₈ :=
    (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₈.sp, h.sp], fun r hr => (o₈.vcs r hr).trans (h.vcs r hr)⟩, ?_, o₈.mem⟩
  · by_cases ho : r ∈ savedRegs
    · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₈.get .x23, h₇.get .x23, h₆.get .x23, h₅.get .x23, h₄.get .x23, h₃.get .x23, e₂]; exact l₁.2.2
      · rw [h₈.get .x24, h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₈.get .x25, h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₈.get .x26, h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₈.get .x27, h₇.get .x27, e₆]; exact l₅.2.2
      · rw [h₈.get .x30, e₇]; exact l₆.2.2
      · rw [e₈]; exact l₇.2.2
    · have hu : r ∈ VG.Proof.MlDsa.AArch64.Sign.untouched := by revert r ho hr; decide
      rw [o₈.get r (by revert r hu; decide), h.cs r hu]
  · rw [h₈.get .x0, h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, BitVec.add_zero]

/-! ## Branches on `w24` -/

theorem eval24 (s : State) : isa.eval (.nonzero .w .x24) s = some ((s.gpr .x24).setWidth 32 != 0) := rfl

theorem ifOkElse_ok {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : (s.gpr .x24).setWidth 32 ≠ 0 → WP isa t s Q) (he : (s.gpr .x24).setWidth 32 = 0 → WP isa e s Q) :
    WP isa (ifOkElse t e) s Q :=
  WP.ite (M := isa) _ (VG.Proof.MlDsa.AArch64.Sign.eval24 s) (fun hb => ht (by simpa using hb)) fun hb => he (by simpa using hb)

theorem ifOkElse_tr {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → (x.gpr .x24).setWidth 32 = (y.gpr .x24).setWidth 32)
    (ht : RelCT isa (fun x y => P x y ∧ (x.gpr .x24).setWidth 32 ≠ 0) t Q)
    (he : RelCT isa (fun x y => P x y ∧ (x.gpr .x24).setWidth 32 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q :=
  RelCT.ite (fun x y h => by rw [VG.Proof.MlDsa.AArch64.Sign.eval24, VG.Proof.MlDsa.AArch64.Sign.eval24, hq x y h])
    (RelCT.mono ht (fun x y ⟨h, hc⟩ => ⟨h, by rw [VG.Proof.MlDsa.AArch64.Sign.eval24] at hc; simpa using hc⟩) fun _ _ h => h)
    (RelCT.mono he (fun x y ⟨h, hc⟩ => ⟨h, by rw [VG.Proof.MlDsa.AArch64.Sign.eval24] at hc; simpa using hc⟩) fun _ _ h => h)

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv`. -/
section

/-!
# ML-DSA signing on AArch64: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x1) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x2) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (S : Nat) (σ s : State) : Prop where
  top : VG.Proof.MlDsa.AArch64.Sign.Top σ s
  lay : Lay S (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) s
  sk : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x25, 0)) p.skLen = VG.Proof.MlDsa.AArch64.Sign.skOf p σ
  mu : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x26, 0)) 64 = VG.Proof.MlDsa.AArch64.Sign.muOf σ
  rnd : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x27, 0)) 32 = VG.Proof.MlDsa.AArch64.Sign.rndOf σ

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.topChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (.x25, 0) p.skLen && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (.x26, 0) 64 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (.x27, 0) 32

theorem St.step {p : Params} {S : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.AArch64.Sign.St p S σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.stChk p ws = true) : VG.Proof.MlDsa.AArch64.Sign.St p S σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.stChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP, (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : VG.Spec.MlDsa.Poly) : Prop := PolyIs s.mem (VG.Proof.MlDsa.AArch64.pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → VG.Spec.MlDsa.Poly) : Prop := ∀ j < m, VG.Proof.MlDsa.AArch64.Sign.Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (rbs wbs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool :=
  m == 0 || keepB rbs wbs ws (pS b) (1024 * m)

theorem famChk_one {rbs wbs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.famChk rbs wbs ws b m = true)
    (hj : j < m) : keepB rbs wbs ws (pS (b + j)) 1024 = true := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega

theorem Fam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay S rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly}
    (hc : VG.Proof.MlDsa.AArch64.Sign.famChk rbs wbs ws b m = true) (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b m f) : VG.Proof.MlDsa.AArch64.Sign.Fam s' b m f :=
  fun j hj => L.keepPoly hP (VG.Proof.MlDsa.AArch64.Sign.famChk_one hc hj) (h j hj)

theorem Pl.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay S rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) {j : Nat} {f : VG.Spec.MlDsa.Poly}
    (hc : keepB rbs wbs ws (pS j) 1024 = true) (h : VG.Proof.MlDsa.AArch64.Sign.Pl s j f) : VG.Proof.MlDsa.AArch64.Sign.Pl s' j f :=
  L.keepPoly hP hc h

theorem Fam.congr {s : State} {b m : Nat} {f g : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b m f) (e : ∀ j < m, f j = g j) :
    VG.Proof.MlDsa.AArch64.Sign.Fam s b m g := fun j hj => e j hj ▸ h j hj

/-- The first `r` slots of a family, and the rest. -/
theorem Fam.split {s : State} {b m r : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (hr : r ≤ m) :
    VG.Proof.MlDsa.AArch64.Sign.Fam s b m f ↔ VG.Proof.MlDsa.AArch64.Sign.Fam s b r f ∧ VG.Proof.MlDsa.AArch64.Sign.Fam s (b + r) (m - r) fun j => f (r + j) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), fun j hj => by rw [Nat.add_assoc]; exact h (r + j) (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    by_cases e : j < r
    · exact h1 j e
    · have := h2 (j - r) (by omega)
      simp only [show b + r + (j - r) = b + j by omega, show r + (j - r) = j by omega] at this
      exact this

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Prims`. -/
section

/-!
# ML-DSA signing on AArch64: the primitives it calls

What the proofs need of the implementations of the primitives (`PrimsOk`):
each is correct and constant time under its shared contract
(`Spec/MlDsa/Poly.lean`) with the `S` bytes of stack the function gives its
calls, and its frames use at most those (`CalleeOk`); and, of the two samplers
whose result the function branches on, that the result is public in their own
runs (`RetPub`) and that they succeed only when the algorithm finishes within
`maxBounds`, the bounds the leakage of signing is stated for.

For each call of a primitive, as the proof of signing uses it: what it does
(`…_ok`), and that two runs in the same layout leak the same (`…_tr`), from
the calls of `Proof/MlDsa/AArch64/Call/` and `CallMore.lean`.
-/

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
  invNtt : CalleeOk S P.invNtt (nttInvContract AArch64.abi S)
  mul : CalleeOk S P.mul (mulContract AArch64.abi S)
  mulAdd : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S)
  add : CalleeOk S P.add (addContract AArch64.abi S)
  sub : CalleeOk S P.sub (subContract AArch64.abi S)
  rej4 : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S)
  rej4Ret : VG.Proof.MlDsa.AArch64.Sign.RetPub (rejNTT4Contract AArch64.abi S) P.rej4
  rej4Max : ∀ s t s', (rejNTT4Contract AArch64.abi S).pre s → Exec isa P.rej4 s t s' →
    (s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (s.gpr .x0) k)).isSome
  rejNTT : CalleeOk S P.rejNTT (rejNTTContract AArch64.abi S)
  expandMask : CalleeOk S P.expandMask (expandMaskContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  highBits : CalleeOk S P.highBits (highBitsContract AArch64.abi S)
  lowBits : CalleeOk S P.lowBits (lowBitsContract AArch64.abi S)
  normLt : CalleeOk S P.normLt (normLtContract AArch64.abi S)
  makeHint : CalleeOk S P.makeHint (makeHintContract AArch64.abi S)
  simpleBitPack : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  hintBitPack : CalleeOk S P.hintBitPack (hintBitPackContract AArch64.abi S)
  /-- `vg_mldsa_rej_ntt_poly`'s result depends only on its public data (its seed). -/
  rejRet : VG.Proof.MlDsa.AArch64.Sign.RetPub (rejNTTContract AArch64.abi S) P.rejNTT
  /-- `vg_mldsa_rej_ntt_poly` succeeds only if `RejNTTPoly` finishes within `maxBounds`. -/
  rejMax : ∀ s t s', (rejNTTContract AArch64.abi S).pre s → Exec isa P.rejNTT s t s' →
    (s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (s.gpr .x0) 34)).isSome
  /-- `vg_mldsa_sample_in_ball`'s result depends only on its public data (`c̃`). -/
  ballRet : VG.Proof.MlDsa.AArch64.Sign.RetPub (sampleInBallContract AArch64.abi S) P.ball
  /-- `vg_mldsa_sample_in_ball` succeeds only if `SampleInBall` finishes within `maxBounds`. -/
  ballMax : ∀ s t s', (sampleInBallContract AArch64.abi S).pre s → Exec isa P.ball s t s' →
    (s'.gpr .x0).setWidth 32 = 1 →
    (sampleInBall ((s.gpr .x2).setWidth 32).toNat maxBounds.ball (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)).isSome

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem LRel.same {x y : State} (R : VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y) : VG.Proof.MlDsa.AArch64.Sign.SameB x y := ⟨R.regs, R.sp⟩

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of an in-place transformation of `f` needs of the layout. -/
abbrev ipChkS (rbs wbs : List (Reg × Nat)) (f : Ptr) : Bool := ipChk rbs wbs f (sc oPS)

theorem ipAt_ok {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : CalleeOk D c (inPlaceContract AArch64.abi t D))
    {s : State} (L : Lay D rbs wbs s) {f : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.ipChkS rbs wbs f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) :
    WP isa (callAt n c [(.x0, .ptr f), (.x1, .ptr (sc oPS))]) s fun s' =>
      PPostB D s s' [(f, 1024), (sc oPS, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f))) :=
  AArch64.ipAt_ok L.s64 C L hc hr

theorem ipAt_tr {t : VG.Spec.MlDsa.Poly → VG.Spec.MlDsa.Poly} {n : String} {c : Prog isa} (C : CalleeOk D c (inPlaceContract AArch64.abi t D))
    {f : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.ipChkS rbs wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f))
      (callAt n c [(.x0, .ptr f), (.x1, .ptr (sc oPS))]) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.ipAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f)) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## Products -/

theorem mulAt_ok {P : Prims} (C : CalleeOk D P.mul (mulContract AArch64.abi D))
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (rf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (mulAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g))) :=
  AArch64.mulAt_ok L.s64 C L hc rf rg

theorem mulAddAt_ok {P : Prims} (C : CalleeOk D P.mulAdd (mulAddContract AArch64.abi D))
    {s : State} (L : Lay D rbs wbs s) {h f g : Ptr} (hc : mulChk rbs wbs h f g = true)
    (rh : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s h)) (rf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (mulAddAt P h f g) s fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h)
        (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s h)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g)))) :=
  AArch64.mulAddAt_ok L.s64 C L hc rh rf rg

theorem mulAt_tr {P : Prims} (C : CalleeOk D P.mul (mulContract AArch64.abi D))
    {h f g : Ptr} (hc : mulChk rbs wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (mulAt P h f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.mulAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem mulAddAt_tr {P : Prims} (C : CalleeOk D P.mulAdd (mulAddContract AArch64.abi D))
    {h f g : Ptr} (hc : mulChk rbs wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧
      (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (mulAddAt P h f g)
      fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => AArch64.mulAddAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧
      (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) C hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## Addition and subtraction -/

theorem addAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk rbs wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (addAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g))) :=
  accAt_ok (op := VG.Spec.MlDsa.add) L.s64 hP.add L hc rf rg

theorem subAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f g : Ptr}
    (hc : accChk rbs wbs f g = true) (rf : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s g)) :
    WP isa (subAt P f g) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (VG.Spec.MlDsa.sub (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s g))) :=
  accAt_ok (op := VG.Spec.MlDsa.sub) L.s64 hP.sub L hc rf rg

theorem addAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {f g : Ptr} (hc : accChk rbs wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (addAt P f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => accAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (op := VG.Spec.MlDsa.add) hP.add hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

theorem subAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {f g : Ptr} (hc : accChk rbs wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (subAt P f g) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => accAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y g))) (op := VG.Spec.MlDsa.sub) hP.sub hp.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
abbrev rejChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := rejNttChk rbs wbs (sc oRS) a (sc oPS)

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.Sign.rejChkS rbs wbs a = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))]) s
      fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 34)) ((s'.gpr .x0).setWidth 32)
        (polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 34)).isSome) := by
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

theorem rejCall_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {a : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.rejChkS rbs wbs a = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x (sc oRS)) 34 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y (sc oRS)) 34)
      (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr a), (.x2, .ptr (sc oPS))])
      fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => VG.Proof.MlDsa.AArch64.Sign.rejNttAtK_trRet (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x (sc oRS)) 34 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y (sc oRS)) 34) hP.rejNTT hP.rejRet hp.1.ok hc
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
abbrev maskChkS (rbs wbs : List (Reg × Nat)) (a : Ptr) : Bool := VG.Proof.MlDsa.AArch64.Sign.maskChk rbs wbs (sc oMS) a (sc oPS)

theorem maskAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : VG.Proof.MlDsa.AArch64.Sign.maskChkS rbs wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s a) (toRq (VG.Spec.MlDsa.bitUnpack (H (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) :=
  VG.Proof.MlDsa.AArch64.Sign.maskAtK_ok L.s64 hP.expandMask L hc hγ

theorem maskAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : VG.Proof.MlDsa.AArch64.Sign.maskChkS rbs wbs a = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs) (maskAt P γ a) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hp e₁ e₂ => VG.Proof.MlDsa.AArch64.Sign.maskAtK_tr (Q := VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs) hP.expandMask hp.ok hc hγ
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hp e₁ e₂

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
abbrev ballChkS (rbs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool := ballChk rbs wbs (sc oCT) len c (sc oPS)

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.AArch64.Sign.ballChkS rbs wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) len)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s c)) ∧
      ((s'.gpr .x0).setWidth 32 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) len)).isSome) := by
  have hl : len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
    simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega
  have hc' := hc
  simp only [ballChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.ball.withPost hP.ballMax) (ball_args L.ok len tau c4 c5 c6)
    (by simp only [List.map_cons, List.map_nil]; decide) (fun s1 h1 => ball_pre L hc hp h1) (ball_cov L hc).1
    (ball_cov L hc).2) fun s' ⟨hP', s1, h1, hq, hx⟩ => ⟨hP'.b, hP'.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [sampleInBallContract, sampleInBallSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1,
    Arg.val] at hx
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), imm32 hl.2] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem ballCall_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : VG.Proof.MlDsa.AArch64.Sign.ballChkS rbs wbs len c = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x (sc oCT)) len = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32 :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => VG.Proof.MlDsa.AArch64.Sign.ballAtK_trRet (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x (sc oCT)) len = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y (sc oCT)) len) hP.ball hP.ballRet hq.1.ok hc hp
    (fun _ _ ⟨R, hb⟩ => ⟨R.lx, R.ly, hb, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## `HighBits` and `LowBits` -/

theorem highBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk rbs wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r)) :
    WP isa (highBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r)).map fun c => (VG.Spec.MlDsa.highBits γ c).toNat) :=
  VG.Proof.MlDsa.AArch64.Sign.bitsAtK_ok (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (VG.Spec.MlDsa.highBits γ c).toNat)) L.s64 hP.highBits L hc
    hγ hr

theorem highBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk rbs wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r))
      (highBitsAt P r γ out) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ =>
    VG.Proof.MlDsa.AArch64.Sign.bitsAtK_tr (R := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r)) (Q := fun γ f m out => NatPolyIs m out (f.map fun c => (VG.Spec.MlDsa.highBits γ c).toNat)) hP.highBits
      hq.1.ok hc hγ (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem lowBitsAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {r out : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : rwChk rbs wbs r 1024 out 1024 = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r)) :
    WP isa (lowBitsAt P r γ out) s fun s' => PPostB D s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s out) ((polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r)).map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c)) :=
  VG.Proof.MlDsa.AArch64.Sign.bitsAtK_ok (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c))) L.s64 hP.lowBits L hc hγ hr

theorem lowBitsAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {r out : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : rwChk rbs wbs r 1024 out 1024 = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r))
      (lowBitsAt P r γ out) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ =>
    VG.Proof.MlDsa.AArch64.Sign.bitsAtK_tr (R := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r)) (Q := fun γ f m out => PolyIs m out (f.map fun c => ofInt (VG.Spec.MlDsa.lowBits γ c))) hP.lowBits
      hq.1.ok hc hγ (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## Norms -/

/-- What a call of `vg_mldsa_norm_lt` on `f` needs of the layout. -/
abbrev normChk (bs : List (Reg × Nat)) (f : Ptr) : Bool := VG.CallLay.inB bs f 1024

theorem normCall_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f : Ptr} {B : Nat}
    (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.AArch64.Sign.normChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) :
    WP isa (callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm B)]) s fun s' => PPostB D s s' [] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ (s'.gpr .x0).setWidth 32 = if normRq [polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)] < B then 1 else 0 :=
  normAt_ok L.s64 hP.normLt L hc hB hr

theorem normCall_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {f : Ptr} {B : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.normChk (rbs ++ wbs) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f))
      (callAt "vg_mldsa_norm_lt" P.normLt [(.x0, .ptr f), (.x1, .imm B)]) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => normAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f)) hP.normLt hq.1.ok hc
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## `MakeHint` -/

theorem hintCall_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {z r h : Ptr} {γ : Nat}
    (hγ : γ ∈ gamma2s) (hc : VG.Proof.MlDsa.AArch64.Sign.hintChk rbs wbs z r h = true) (rz : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s z))
    (rr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s r)) :
    WP isa (callAt "vg_mldsa_make_hint" P.makeHint [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm γ), (.x3, .ptr h)]) s
      fun s' => PPostB D s s' [(h, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      HintIs s'.mem (VG.Proof.MlDsa.AArch64.pa s h) 1 [Vector.zipWith (VG.Spec.MlDsa.makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r))] ∧
      ((s'.gpr .x0).setWidth 32).toNat =
        hintOnes [Vector.zipWith (VG.Spec.MlDsa.makeHint γ) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s z)) (polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s r))] :=
  VG.Proof.MlDsa.AArch64.Sign.hintAtK_ok L.s64 hP.makeHint L hc hγ rz rr

theorem hintCall_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {z r h : Ptr} {γ : Nat} (hγ : γ ∈ gamma2s)
    (hc : VG.Proof.MlDsa.AArch64.Sign.hintChk rbs wbs z r h = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x z) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y z) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r)))
      (callAt "vg_mldsa_make_hint" P.makeHint [(.x0, .ptr z), (.x1, .ptr r), (.x2, .imm γ), (.x3, .ptr h)])
      fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => VG.Proof.MlDsa.AArch64.Sign.hintAtK_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x z) ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x r)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y z) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y r))) hP.makeHint hq.1.ok hc hγ
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

/-! ## Encodings -/

theorem sbpOk_of {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) : SbpOk b len := by
  refine ⟨hb, hl, ?_⟩
  subst hl
  simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk rbs wbs f 1024 out len = true)
    (hle : ∀ i < 256, (coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s f) i).toNat ≤ b) :
    WP isa (simpleBitPackAt P f b out len) s fun s' => PPostB D s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s out) len = VG.Spec.MlDsa.simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)) b :=
  AArch64.sbpAt_ok L.s64 hP.simpleBitPack L hc (VG.Proof.MlDsa.AArch64.Sign.sbpOk_of hb hl) hle

theorem sbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {f out : Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : rwChk rbs wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (VG.Proof.MlDsa.AArch64.pa y f) i).toNat ≤ b)) (simpleBitPackAt P f b out len) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => AArch64.sbpAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (∀ i < 256, (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x f) i).toNat ≤ b) ∧
      (∀ i < 256, (coeffAt y.mem (VG.Proof.MlDsa.AArch64.pa y f) i).toNat ≤ b)) hP.simpleBitPack hq.1.ok hc (VG.Proof.MlDsa.AArch64.Sign.sbpOk_of hb hl)
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem bitPackParams_lt {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ 32 * bitlen (a + b) < 2 ^ 32 := by
  simp only [bitPackParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bpOk_of {a b len : Nat} (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) : BpOk a b len := by
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.AArch64.Sign.bitPackParams_lt hp
  exact ⟨hp, hl, h1, h2, by rw [hl]; exact h3⟩

/-- The coefficients of a polynomial of `R` in `[-a, b]`. -/
abbrev InRange (m : Mem) (p : Addr) (a b : Nat) : Prop := BpRange m p a b

theorem bpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) (hrg : VG.Proof.MlDsa.AArch64.Sign.InRange s.mem (VG.Proof.MlDsa.AArch64.pa s f) a b) :
    WP isa (bitPackAt P f a b out len) s fun s' => PPostB D s s' [(out, len)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s out) len = VG.Spec.MlDsa.bitPack ((polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)).map fun c => modPm c.val q) a b :=
  AArch64.bpAt_ok L.s64 hP.bitPack L hc (VG.Proof.MlDsa.AArch64.Sign.bpOk_of hp hl) hr hrg

theorem bpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {f out : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs f 1024 out len = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ VG.Proof.MlDsa.AArch64.Sign.InRange x.mem (VG.Proof.MlDsa.AArch64.pa x f) a b) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ VG.Proof.MlDsa.AArch64.Sign.InRange y.mem (VG.Proof.MlDsa.AArch64.pa y f) a b)) (bitPackAt P f a b out len) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => AArch64.bpAt_tr (Q := fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ VG.Proof.MlDsa.AArch64.Sign.InRange x.mem (VG.Proof.MlDsa.AArch64.pa x f) a b) ∧
      (Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f) ∧ VG.Proof.MlDsa.AArch64.Sign.InRange y.mem (VG.Proof.MlDsa.AArch64.pa y f) a b)) hP.bitPack hq.1.ok hc (VG.Proof.MlDsa.AArch64.Sign.bpOk_of hp hl)
    (fun _ _ ⟨R, rx, ry⟩ => ⟨R.lx, R.ly, rx, ry, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem bupAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    WP isa (bitUnpackAt P v len a b f) s fun s' => PPostB D s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.AArch64.pa s f) (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s v) len) a b)) :=
  buAt_ok L.s64 hP.bitUnpack L hc (VG.Proof.MlDsa.AArch64.Sign.bpOk_of hp hl)

theorem bupAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {v f : Ptr} {a b len : Nat}
    (hp : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : rwChk rbs wbs v len f 1024 = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs) (bitUnpackAt P v len a b f) fun _ _ => True :=
  fun x y t₁ t₂ x' y' hq e₁ e₂ => buAt_tr (Q := VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs) hP.bitUnpack hq.ok hc (VG.Proof.MlDsa.AArch64.Sign.bpOk_of hp hl)
    (fun _ _ R => ⟨R.lx, R.ly, R.same⟩) x y t₁ t₂ x' y' hq e₁ e₂

theorem hintParams_lt {ω k : Nat} (h : (ω, k) ∈ hintParams) : ω < 2 ^ 32 ∧ ω + k < 2 ^ 32 ∧ 256 * k < 2 ^ 32 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem hbpOk_of {ω k : Nat} (hp : (ω, k) ∈ hintParams) : VG.Proof.MlDsa.AArch64.Sign.HbpOk (256 * k) ω (ω + k) := by
  obtain ⟨h1, h2, h3⟩ := VG.Proof.MlDsa.AArch64.Sign.hintParams_lt hp
  exact ⟨by rw [show ω + k - ω = k by omega]; exact hp, by omega, by rw [show ω + k - ω = k by omega], h3, h1, h2⟩

theorem hbpAt_ok {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {h y : Ptr} {ω k : Nat}
    (hp : (ω, k) ∈ hintParams) (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true)
    (hones : hintOnes (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s h) k) ≤ ω) :
    WP isa (hintBitPackAt P h (256 * k) ω y (ω + k)) s fun s' => PPostB D s s' [(y, ω + k)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧ bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s y) (ω + k) = VG.Spec.MlDsa.hintBitPack ω k (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s h) k) := by
  have ek : ω + k - ω = k := by omega
  have := VG.Proof.MlDsa.AArch64.Sign.hbpAtK_ok L.s64 hP.hintBitPack L hc (VG.Proof.MlDsa.AArch64.Sign.hbpOk_of hp) (by rw [ek]; exact hones)
  rw [ek] at this
  exact this

/-- Two runs leak the same when their hints (as the `u32`s at `h`) agree. -/
theorem hbpAt_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {h y : Ptr} {ω k : Nat} (hp : (ω, k) ∈ hintParams)
    (hc : rwChk rbs wbs h (256 * k * 4) y (ω + k) = true) :
    RelCT isa (fun x z => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (VG.Proof.MlDsa.AArch64.pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (VG.Proof.MlDsa.AArch64.pa z h) i).toNat))
      (hintBitPackAt P h (256 * k) ω y (ω + k)) fun _ _ => True := by
  have ek : ω + k - ω = k := by omega
  exact fun x z t₁ t₂ x' z' hq e₁ e₂ => VG.Proof.MlDsa.AArch64.Sign.hbpAtK_tr (Q := fun x z => VG.Proof.MlDsa.AArch64.Sign.LRel D rbs wbs x z ∧ hintOnes (hintAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) k) ≤ ω ∧
      hintOnes (hintAt z.mem (VG.Proof.MlDsa.AArch64.pa z h) k) ≤ ω ∧
      (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x h) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt z.mem (VG.Proof.MlDsa.AArch64.pa z h) i).toNat)) hP.hintBitPack hq.1.ok hc (VG.Proof.MlDsa.AArch64.Sign.hbpOk_of hp)
    (fun _ _ ⟨R, ox, oz, hl⟩ => ⟨R.lx, R.ly, by rw [ek]; exact ox, by rw [ek]; exact oz, hl, R.same⟩)
    x z t₁ t₂ x' z' hq e₁ e₂

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA`. -/
section

/-!
# ML-DSA signing on AArch64: `ExpandA`

`ρ` to `RS`, then entry `e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from
the seed `ρ ‖ j ‖ i`, with `x24` the AND of the results (`IA`): if it is 1,
every entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one
entry's `RejNTTPoly` does not finish within `minBounds` (`expandA_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (VG.Proof.MlDsa.AArch64.Sign.skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : VG.Spec.MlDsa.Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : VG.Impl.MlDsa.AArch64.Sign.aP p (e / p.ℓ) (e % p.ℓ) = pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ) = pS (5 + 4 * p.k + 3 * p.ℓ + e)
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

theorem Fam.snoc {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b m f) (h' : VG.Proof.MlDsa.AArch64.Sign.Pl s (b + m) (f m)) :
    VG.Proof.MlDsa.AArch64.Sign.Fam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  st : VG.Proof.MlDsa.AArch64.Sign.St p D σ s
  rs : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 32 = VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  ok : s.gpr .x24 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e')).isSome) ∧
    VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.aBase p) e (VG.Proof.MlDsa.AArch64.Sign.aVal p σ)
  bad : s.gpr .x24 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    VG.Proof.MlDsa.AArch64.Sign.integerToBytes_one, VG.Proof.MlDsa.AArch64.Sign.integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : VG.Proof.MlDsa.AArch64.pa s (sc a) + BitVec.ofNat 64 b = VG.Proof.MlDsa.AArch64.pa s (sc (a + b)) := by
  rw [VG.Proof.MlDsa.AArch64.pa, VG.Proof.MlDsa.AArch64.pa, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

/-! ## An entry -/

/-- What entry `e` needs of the layout. -/
def eChk (p : Params) (e : Nat) : Bool :=
  let a := pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e)
  let w1 : List (Ptr × Nat) := [(sc (oRS + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS + 33), 1)]
  let w3 : List (Ptr × Nat) := [(a, 1024), (sc oPS, 2048)]
  VG.Proof.MlDsa.AArch64.Sign.stChk p w1 && VG.Proof.MlDsa.AArch64.Sign.stChk p w2 && VG.Proof.MlDsa.AArch64.Sign.stChk p w3 && VG.Proof.MlDsa.AArch64.Sign.stChk p [] && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS + 32)) 1 &&
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS + 33)) 1 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (sc oRS) 32 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (sc oRS) 32 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (sc oRS) 32 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (sc (oRS + 32)) 1 && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (VG.Proof.MlDsa.AArch64.Sign.aBase p) e &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (VG.Proof.MlDsa.AArch64.Sign.aBase p) e && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (VG.Proof.MlDsa.AArch64.Sign.aBase p) e && VG.Proof.MlDsa.AArch64.Sign.rejChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) a &&
    decide (e % p.ℓ < 256) && decide (e / p.ℓ < 256)

theorem eChk_spec {p : Params} {e : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) :
    VG.Proof.MlDsa.AArch64.Sign.stChk p [(sc (oRS + 32), 1)] = true ∧ VG.Proof.MlDsa.AArch64.Sign.stChk p [(sc (oRS + 33), 1)] = true ∧
      VG.Proof.MlDsa.AArch64.Sign.stChk p [(pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e), 1024), (sc oPS, 2048)] = true ∧ VG.Proof.MlDsa.AArch64.Sign.stChk p [] = true ∧
      VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS + 32)) 1 = true ∧ VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS + 33)) 1 = true ∧
      keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS + 32), 1)] (sc oRS) 32 = true ∧ keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS + 33), 1)] (sc oRS) 32 = true ∧
      keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e), 1024), (sc oPS, 2048)] (sc oRS) 32 = true ∧
      keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS + 33), 1)] (sc (oRS + 32)) 1 = true ∧
      VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS + 32), 1)] (VG.Proof.MlDsa.AArch64.Sign.aBase p) e = true ∧ VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS + 33), 1)] (VG.Proof.MlDsa.AArch64.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e), 1024), (sc oPS, 2048)] (VG.Proof.MlDsa.AArch64.Sign.aBase p) e = true ∧
      VG.Proof.MlDsa.AArch64.Sign.rejChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.eChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD VG.Spec.MlDsa.zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem outcome01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α} (h : Outcome f r out) :
    r = 1 ∨ r = 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .x28 = s.gpr .x28) {b m : Nat}
    {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b m f) : VG.Proof.MlDsa.AArch64.Sign.Fam s' b m f := fun j hj => by
  simp only [VG.Proof.MlDsa.AArch64.Sign.Pl, VG.Proof.MlDsa.AArch64.pa, hm, hb]; exact h j hj

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

theorem blkE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s) : WP isa (.block (VG.Proof.MlDsa.AArch64.Sign.blkE p e)) s fun s' =>
      (VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' (sc oRS)) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ e) ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨c1, c2, _, _, w1, w2, k1, k2, _, k12, f1, f2, _, _, hj, hi⟩ := VG.Proof.MlDsa.AArch64.Sign.eChk_spec he
  have L := h.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (by decide) w1 (by decide)) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (setB_ok S1.lay (by decide) w2 (by decide)) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have e15 : s2.gpr .x24 = s.gpr .x24 := by rw [hcs2.get .x24, hcs1.get .x24]
  have hrs : bytesAt s2.mem (VG.Proof.MlDsa.AArch64.pa s2 (sc oRS)) 32 = VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ :=
    (S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)
  refine ⟨⟨⟨S2, hrs, e15 ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (e15 ▸ h0)⟩, VG.Proof.MlDsa.AArch64.Sign.seed34 hrs ?_ ?_⟩, e15⟩
  · obtain ⟨ok, fam⟩ := h.ok (e15 ▸ h1)
    exact ⟨ok, Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)⟩
  · rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact VG.Proof.MlDsa.AArch64.Sign.bytes1_write _ _ _
  · rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add, hm2, hP2.pa (by decide)]; exact VG.Proof.MlDsa.AArch64.Sign.bytes1_write _ _ _

/-- What the call of entry `e` leaves. -/
def CallE (D : Nat) (a : Ptr) (x : List Byte) (s s' : State) : Prop :=
  PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
    ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT x) ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (VG.Proof.MlDsa.AArch64.pa s a)) ∧
    ((s'.gpr .x0).setWidth 32 = 1 → (rejNTTPoly maxBounds.rejNTT x).isSome)

/-- Entry `e`'s call is done. -/
def JE (p : Params) (D : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s₀ ∧ VG.Proof.MlDsa.AArch64.Sign.CallE D (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e)) (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e) s₀ s

theorem callE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ e) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e))),
      (.x2, .ptr (sc oPS))]) s
      (VG.Proof.MlDsa.AArch64.Sign.JE p D e σ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.AArch64.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ => ⟨s, h, hP3, hcs3, hred, ?_, ?_⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem andE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.JE p D e σ s) : WP isa (.block and24) s (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (e + 1)) := by
  obtain ⟨_, _, c3, c0, _, _, _, _, k3, _, _, _, f3, _, _, _⟩ := VG.Proof.MlDsa.AArch64.Sign.eChk_spec he
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := h
  have S3 := h.st.step hP3 c3
  refine WP.mono (and24_ok s) fun s4 ⟨k4, h15⟩ => ?_
  have hm4 : s4.mem = s.mem := k4.mem
  have hP4 : PPostB D s s4 [] := VG.Proof.MlDsa.AArch64.Sign.postB24 k4 _
  rw [hcs3] at h15
  have hr := VG.Proof.MlDsa.AArch64.Sign.outcome01 hout
  have hb4 : s4.gpr .x28 = s₀.gpr .x28 := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [hm4, hP4.pa (by decide), h.st.lay.keepBytes hP3 k3, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .x24 = 1 ∧ (s.gpr .x0).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep h.st.lay hP3 f3 fam)
    · show PolyIs s4.mem (VG.Proof.MlDsa.AArch64.pa s4 (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e))) (VG.Proof.MlDsa.AArch64.Sign.aVal p σ e)
      rw [hm4, show VG.Proof.MlDsa.AArch64.pa s4 (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e)) = VG.Proof.MlDsa.AArch64.pa s₀ (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e)) by simp only [VG.Proof.MlDsa.AArch64.pa, hb4]]
      exact ⟨hred hs.2, VG.Proof.MlDsa.AArch64.Sign.rej_val hout hs.2 hm⟩
  · rw [h15] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega, hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega, hn⟩

theorem sampleE_eq (P : Prims) (p : Params) (e : Nat) : sampleE P p e = .seq (.block (VG.Proof.MlDsa.AArch64.Sign.blkE p e))
    (.seq (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e))),
      (.x2, .ptr (sc oPS))]) (.block and24)) := by
  unfold sampleE rejAt; rw [VG.Proof.MlDsa.AArch64.Sign.aP_eq]

theorem sampleE_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s) : WP isa (sampleE P p e) s (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (e + 1)) := by
  rw [VG.Proof.MlDsa.AArch64.Sign.sampleE_eq]
  exact WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.blkE_ok he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.callE_ok hP he h1 hs1) fun s2 h2 => VG.Proof.MlDsa.AArch64.Sign.andE_ok he h2))

/-! ## The matrix -/

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (VG.Proof.MlDsa.AArch64.Sign.eChk p) && copyPChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oRS) (.x25, 0) &&
    VG.Proof.MlDsa.AArch64.Sign.stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen)

theorem aChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide


end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel`. -/
section

/-!
# ML-DSA signing on AArch64: two runs

Constant time is proven piece by piece (`RelCT`) for two runs from entry
states that satisfy `signK`'s precondition and agree on its public data, each
satisfying the invariant `I` of the correctness proof, and related by `E`
(`RR`): each piece leaks the same, correctness gives each run's next
invariant, and the piece's own proof the next relation (`relInvE`). The runs
are in the same layout (`RR.lrel`) and agree on `ρ` (`RR.rho`), which the
leakage begins with.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, each satisfying `I` from its entry state, related by `E`. -/
def RR (p : Params) (D : Nat) (I E : State → State → Prop) (x y : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Rel2 (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub I x y ∧ E x y

section
variable {p : Params} {D : Nat}

/-- Two runs in the same layout: their entry states agree on the pointers. -/
theorem lrel_of {σ₁ σ₂ x y : State} (hpub : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub σ₁ σ₂) (S₁ : VG.Proof.MlDsa.AArch64.Sign.St p D σ₁ x) (S₂ : VG.Proof.MlDsa.AArch64.Sign.St p D σ₂ y) :
    VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hpub
  refine ⟨S₁.lay, S₂.lay, fun r hr => ?_, by rw [S₁.top.sp, S₂.top.sp, h6], fun b hb => ⟨VG.Proof.MlDsa.AArch64.Sign.sgB_bases p b hb, VG.Proof.MlDsa.AArch64.Sign.bases_kept _ (VG.Proof.MlDsa.AArch64.Sign.sgB_bases p b hb)⟩⟩
  have r₁ := S₁.top.regs
  have r₂ := S₂.top.regs
  simp only [VG.Proof.MlDsa.AArch64.Sign.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [r₁ (.x23, .x3) (by decide), r₂ (.x23, .x3) (by decide), h4]
  · rw [r₁ (.x25, .x0) (by decide), r₂ (.x25, .x0) (by decide), h1]
  · rw [r₁ (.x26, .x1) (by decide), r₂ (.x26, .x1) (by decide), h2]
  · rw [r₁ (.x27, .x2) (by decide), r₂ (.x27, .x2) (by decide), h3]
  · rw [r₁ (.x28, .x4) (by decide), r₂ (.x28, .x4) (by decide), h5]

theorem relInvE {I J E E' : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D I E) c E') : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D I E) c (VG.Proof.MlDsa.AArch64.Sign.RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', he⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, he⟩

theorem RR.mono {I I' E E' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.AArch64.Sign.RR p D I E x y)
    (hI : ∀ σ s, I σ s → I' σ s) (hE : E x y → E' x y) : VG.Proof.MlDsa.AArch64.Sign.RR p D I' E' x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, e⟩ := h
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, hI _ _ i₁, hI _ _ i₂⟩, hE e⟩

theorem RR.lrel {I E : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.RR p D I E x y) : VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y := by
  obtain ⟨⟨σ₁, σ₂, _, _, hpub, i₁, i₂⟩, _⟩ := h
  exact VG.Proof.MlDsa.AArch64.Sign.lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem WP.conj {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun s' => Q₁ s' ∧ Q₂ s' := by
  obtain ⟨t, s', e, q₁⟩ := h₁
  obtain ⟨_, _, e', q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, _, e, q₁, q₂⟩

/-- A piece that takes each run from `I` to `J` and from `s` to `s'` with
`F s s'`, and leaks the same from runs related by `RR p D I E`, with `Q₀` of
the final states. -/
theorem stepRR {I J E E' Q₀ F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D I E) c Q₀)
    (hE : ∀ x y x' y', VG.Proof.MlDsa.AArch64.Sign.RR p D I E x y → F x x' → F y y' → Q₀ x' y' → E' x' y') :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D I E) c (VG.Proof.MlDsa.AArch64.Sign.RR p D J E') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ := hr
  obtain ⟨_, u₁, f₁, g₁, k₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂, k₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', ⟨σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩, hE _ _ _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, he⟩ k₁ k₂ hq⟩

end

/-! ## Runs related through their entry states -/

/-- Two runs, each satisfying `I` from its entry state, the entry states related by `E`. -/
def RS (p : Params) (D : Nat) (E I : State → State → Prop) (x y : State) : Prop :=
  ∃ σ₁ σ₂, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ₁ ∧ (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ₂ ∧ (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub σ₁ σ₂ ∧ E σ₁ σ₂ ∧ I σ₁ x ∧ I σ₂ y

section
variable {p : Params} {D : Nat}

theorem RS.lrel {E I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.Sign.St p D σ s) {x y : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.RS p D E I x y) : VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y := by
  obtain ⟨σ₁, σ₂, _, _, hpub, _, i₁, i₂⟩ := h
  exact VG.Proof.MlDsa.AArch64.Sign.lrel_of hpub (hI _ _ i₁) (hI _ _ i₂)

theorem RS.mono {E I E' I' : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.AArch64.Sign.RS p D E I x y)
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → E' σ₁ σ₂) (hI : ∀ σ s, I σ s → I' σ s) : VG.Proof.MlDsa.AArch64.Sign.RS p D E' I' x y := by
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, e, i₁, i₂⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, hE _ _ e, hI _ _ i₁, hI _ _ i₂⟩

/-- A piece that leaks the same from two runs in the layout that satisfy `T`, and takes each run from
`I` to `J`. -/
theorem liftL {E I J : State → State → Prop} {T : State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.Sign.St p D σ s ∧ T s) (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ T x ∧ T y) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E I) c (VG.Proof.MlDsa.AArch64.Sign.RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ ⟨VG.Proof.MlDsa.AArch64.Sign.lrel_of hpub (hI _ _ i₁).1 (hI _ _ i₂).1, (hI _ _ i₁).2, (hI _ _ i₂).2⟩ e₁ e₂
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- `liftL`, with a leakage proof from any relation the runs satisfy. -/
theorem liftR {E I J : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E I) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E I) c (VG.Proof.MlDsa.AArch64.Sign.RS p D E J) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, he, g₁, g₂⟩

/-- Two pieces in sequence, from two runs in the layout that satisfy `I` (what the first piece needs),
each piece leaving the layout. -/
theorem seqL {c₁ c₂ : Prog isa} {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, Lay D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x → I x → WP isa c₁ x fun x' => (∃ W, PostB D x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, PostB D x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.lx h.2.1, w₁ y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hx hy, jx, jy⟩) h₂

theorem trL_mono {c : Prog isa} {I I' : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True) (hI : ∀ s, I' s → I s) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I' x ∧ I' y) c fun _ _ => True :=
  RelCT.mono h (fun _ _ h => ⟨h.1, hI _ h.2.1, hI _ h.2.2⟩) fun _ _ h => h

end

/-! ## Blocks -/

/-- Code that leaks only through the pointers of the layout (and the stack
pointer), as the taint analysis proves: for a block, by evaluation of
`checkBlock`, which does not look at offsets and immediates, so that they
may be variables. -/
theorem lrel_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {c : Prog isa}
    {hc : VG.Taint.Hint AArch64.Taint.T} (hr : ∀ x y, P x y → VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x y)
    (h : (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  taintRel VG.Proof.MlDsa.AArch64.Sign.bases (fun x y hp => ⟨(hr x y hp).sp, (hr x y hp).regs⟩) h

theorem vector_lrel_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {c : Prog isa}
    {hc : VG.Taint.Hint VectorTaint.T} (hr : ∀ x y, P x y → VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x y)
    (h : (VectorTaint.taint.check (VectorTaint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  VectorTaint.relRegs VG.Proof.MlDsa.AArch64.Sign.bases (fun x y hp => ⟨(hr x y hp).sp, (hr x y hp).regs⟩) h

/-! ## `ρ` -/

theorem signLeakT_head (p : Params) (sk μ rnd : List Byte) :
    ∃ X, signLeakT p sk μ rnd = leakBytes (sk.take 32) ++ X := by
  unfold signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  subst hρ
  exact ⟨_, rfl⟩

theorem leak_rho {p : Params} {sk₁ sk₂ μ₁ μ₂ r₁ r₂ : List Byte} (h1 : sk₁.length = p.skLen)
    (h2 : sk₂.length = p.skLen) (h : signLeakT p sk₁ μ₁ r₁ = signLeakT p sk₂ μ₂ r₂) :
    sk₁.take 32 = sk₂.take 32 := by
  obtain ⟨X₁, e₁⟩ := VG.Proof.MlDsa.AArch64.Sign.signLeakT_head p sk₁ μ₁ r₁
  obtain ⟨X₂, e₂⟩ := VG.Proof.MlDsa.AArch64.Sign.signLeakT_head p sk₂ μ₂ r₂
  rw [e₁, e₂] at h
  refine VG.Proof.MlDsa.Sign.leakBytes_inj (List.append_inj h ?_).1
  rw [leakBytes_length, leakBytes_length, List.length_take, List.length_take, h1, h2]

theorem pub_rho {p : Params} {D : Nat} {σ₁ σ₂ : State} (h : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub σ₁ σ₂) :
    VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ₁ = VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ₂ :=
  VG.Proof.MlDsa.AArch64.Sign.leak_rho (VG.Proof.MlKem.bytesAt_length _ _ _) (VG.Proof.MlKem.bytesAt_length _ _ _) h.2.2.2.2.2.2

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.BlockTr`. -/
section

/-!
# ML-DSA signing on AArch64: blocks that leak only their pointers

The taint analysis of a block does not look at its offsets and immediates, so
its check evaluates for code in which they are variables (`setKappa_taint`); a
copy's moves of its addresses and length depend on their values only through
the choice of instructions (`copy_taint`), each of which leaves them public.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)

/-- The hint of a copy: its pointers and its counter are public in its loop. -/
abbrev copyHint : VG.Taint.Hint AArch64.Taint.T :=
  .seq (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block []) (.loop (AArch64.Taint.ofRegs [.x0, .x1, .x2]) (.block []))

theorem copy_taint {b₁ b₂ : Reg} (h₁ : b₁ = .x28 ∨ b₁ = .x23) (h₂ : b₂ = .x28) (o₁ o₂ n : Nat) :
    (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (copy (b₁, o₁) (b₂, o₂) n) VG.Proof.MlDsa.AArch64.Sign.copyHint).isSome = true := by
  subst h₂
  rcases h₁ with rfl | rfl <;> dsimp only [copy, lea, movV] <;> (repeat' split) <;> rfl

theorem copy_tr {S : Nat} {rbs wbs : List (Reg × Nat)} {P : State → State → Prop} {b₁ b₂ : Reg}
    (h₁ : b₁ = .x28 ∨ b₁ = .x23) (h₂ : b₂ = .x28) {o₁ o₂ n : Nat} (hr : ∀ x y, P x y → VG.Proof.MlDsa.AArch64.Sign.LRel S rbs wbs x y) :
    RelCT isa P (copy (b₁, o₁) (b₂, o₂) n) fun _ _ => True :=
  VG.Proof.MlDsa.AArch64.Sign.lrel_tr hr (VG.Proof.MlDsa.AArch64.Sign.copy_taint h₁ h₂ o₁ o₂ n)

theorem setKappa_taint (r : Nat) :
    (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (.block (setKappa r)) (.block [])).isSome = true := by
  dsimp only [setKappa]; rfl

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Call4`. -/
section

/-!
# ML-DSA signing on AArch64: calls of the samplers

For each call of `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_sample_in_ball`: what it
needs of the layout (`…Chk`), what it does (`…_ok`), and that two runs whose
layout registers agree, and whose sampler leaks the same, leak the same
(`…_tr`).
-/

/-! Calls of the four-way sampler through the shared contract, including public return values. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `RejNTTPoly` -/

def rej4Chk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 136 a 4096 && sepB rbs wbs seed 136 ss 8192 && sepB rbs wbs a 4096 ss 8192 &&
    VG.CallLay.inB (rbs ++ wbs) seed 136 && VG.CallLay.inB (rbs ++ wbs) a 4096 && VG.CallLay.inB (rbs ++ wbs) ss 8192 && VG.CallLay.inB wbs a 4096 &&
    VG.CallLay.inB wbs ss 8192

abbrev rej4Args (seed a ss : Ptr) : List (Reg × Arg) := [(.x0, .ptr seed), (.x1, .ptr a), (.x2, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.Sign.rej4Chk rbs wbs seed a ss = true)
include L hc

theorem rej4_cov : Covers ([⟨VG.Proof.MlDsa.AArch64.pa s seed, 136⟩] ++ [⟨VG.Proof.MlDsa.AArch64.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.AArch64.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 8192⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss) s s1) :
    (rejNTT4Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.AArch64.pa s seed, 136⟩] [⟨VG.Proof.MlDsa.AArch64.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.AArch64.pa s ss, 8192⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej4_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (c4 : VG.CallLay.inB bs seed 136 = true)
    (c5 : VG.CallLay.inB bs a 4096 = true) (c6 : VG.CallLay.inB bs ss 8192 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rej4AtK_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.Sign.rej4Chk rbs wbs seed a ss = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss)) s fun s' => PPostB S s s' [(a, 4096), (ss, 8192)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced s'.mem (poly4 (VG.Proof.MlDsa.AArch64.pa s a) k)) ∧
      (((s'.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s seed) k) = some (polyAt s'.mem (poly4 (VG.Proof.MlDsa.AArch64.pa s a) k))) ∨
        ((s'.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s seed) k) = none)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.Sign.rej4_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.rej4_pre L hc h1) (VG.Proof.MlDsa.AArch64.Sign.rej4_cov L hc).1 (VG.Proof.MlDsa.AArch64.Sign.rej4_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rej4AtK_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x seed) 136 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y seed) 136 ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss)) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.Sign.rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.rej4_pre Lx hc h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.Sign.rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Ly hc).2


theorem rej4AtK_trRet {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    (hr : VG.Proof.MlDsa.AArch64.Sign.RetPub (rejNTT4Contract AArch64.abi S) P.rej4)
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.Sign.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x seed) 136 = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y seed) 136 ∧ VG.Proof.MlDsa.AArch64.Sign.SameB x y) :
    RelCT isa Q (callAt ("vg_mldsa_rej_ntt_poly4" ++ P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.Sign.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine VG.Proof.MlDsa.AArch64.Sign.callAt_trRet C hr (VG.Proof.MlDsa.AArch64.Sign.rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.Sign.rej4_pre Lx hc h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.Sign.rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.Sign.rej4_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Seed4`. -/
section

/-! Signing matrix expansion: four seeds, with the earlier matrix and caller state preserved. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def seedCopy4 (j : Nat) : List Instr := lea .x10 .x28 (oRS4+34*j) ++ Impl.MlKem.AArch64.copy32 .x28 oRS .x10 0

theorem copySeed4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : VG.CallLay.inB (rbs++wbs) (sc oRS) 32 = true)
    (hdst : VG.CallLay.inB wbs (sc (oRS4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oRS) 32 (sc (oRS4+34*j)) 32 = true) :
    WP isa (.block (VG.Proof.MlDsa.AArch64.Sign.seedCopy4 j)) s fun t =>
      PPostB S s t [(sc (oRS4+34*j),32)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9,.x10] s t ∧
        bytesAt t.mem (VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*j))) 32 = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 32 := by
  unfold VG.Proof.MlDsa.AArch64.Sign.seedCopy4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oRS,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨VG.Proof.MlDsa.AArch64.pa s (sc oRS),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*j))) (sb := .x28) (db := .x10) (so := oRS) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨VG.Proof.MlDsa.AArch64.pa s (sc oRS),32⟩ : Region).Disjoint ⟨VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : VG.Proof.MlKem.AArch64.Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]


end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

structure AS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s
  done : ∀ k < j,bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc (oRS4+34*k))) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+k)

def slotChk (p : Params) (e j : Nat) : Bool :=
  let ws : List (Ptr × Nat) := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)]
  VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oRS) 32 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS4+34*j)) 32 &&
    sepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oRS) 32 (sc (oRS4+34*j)) 32 && VG.Proof.MlDsa.AArch64.Sign.stChk p ws &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oRS) 32 && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.aBase p) e &&
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS4+34*j+32)) 1 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oRS4+34*j+33)) 1 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j+32)) 1 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)] (sc (oRS4+34*j)) 32 &&
    (List.range j).all (fun k => keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc (oRS4+34*k)) 34)

theorem slotChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ e < p.k*p.ℓ,∀ j < 4,VG.Proof.MlDsa.AArch64.Sign.slotChk p e j = true := by
  decide +kernel

theorem IA.keep {p : Params} {D : Nat} {σ s t : State} {e : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s)
    {ws : List (Ptr × Nat)} (hp : PPostB D s t ws) (hc : VG.Proof.MlDsa.AArch64.Sign.stChk p ws = true)
    (hr : keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oRS) 32 = true) (hf : VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.aBase p) e = true)
    (h24 : t.gpr .x24 = s.gpr .x24) : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e t :=
  ⟨h.st.step hp hc,(h.st.lay.keepBytes hp hr).trans h.rs,h24 ▸ h.r01,
    fun ht => let ⟨ok,fam⟩ := h.ok (h24 ▸ ht); ⟨ok,Fam.keep h.st.lay hp hf fam⟩,
    fun ht => h.bad (h24 ▸ ht)⟩

theorem slot4_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj : j < 4)
    (hc : VG.Proof.MlDsa.AArch64.Sign.slotChk p e j = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.AS p D σ e j s) :
    WP isa (seedSlot4 p e j) s fun t => VG.Proof.MlDsa.AArch64.Sign.AS p D σ e (j+1) t ∧ t.gpr .x24 = s.gpr .x24 := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.slotChk,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨csrc,cdst⟩,csep⟩,cst⟩,crs⟩,cfam⟩,cw1⟩,cw2⟩,ck12⟩,ck32⟩,ckprev⟩ := hc
  have L := h.ia.st.lay
  unfold seedSlot4
  change WP isa (.seq (.block (VG.Proof.MlDsa.AArch64.Sign.seedCopy4 j)) _) s _
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.copySeed4_ok L csrc cdst csep) fun s1 ⟨hP1,k1,b1⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok (L.post hP1) (p := sc (oRS4+34*j+32)) (v := (e+j)%p.ℓ)
    (by dsimp only [oRS4]; omega) cw1 (by change Reg.x28 ∈ keptRegs; decide)) fun s2 ⟨hP2,k2,m2⟩ => ?_
  refine WP.mono (setB_ok ((L.post hP1).post hP2) (p := sc (oRS4+34*j+33)) (v := (e+j)/p.ℓ)
    (by dsimp only [oRS4]; omega) cw2 (by change Reg.x28 ∈ keptRegs; decide)) fun t ⟨hP3,k3,m3⟩ => ?_
  have hp12 := PPostB.trans hP1 hP2 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  have hp := PPostB.trans hp12 hP3 (ws := [(sc (oRS4+34*j),32),(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  have h24 : t.gpr .x24 = s.gpr .x24 := by rw [k3.get .x24,k2.get .x24,k1.get .x24]
  refine ⟨⟨h.ia.keep hp cst crs cfam h24,fun k hk => ?_⟩,h24⟩
  by_cases heq : k = j
  · subst k
    have hrho : bytesAt t.mem (VG.Proof.MlDsa.AArch64.pa t (sc (oRS4+34*j))) 32 = VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ := by
      have hp23 := PPostB.trans hP2 hP3 (ws := [(sc (oRS4+34*j+32),1),(sc (oRS4+34*j+33),1)])
        (by simp [sc,keptRegs]) (by simp) (by simp)
      rw [(L.post hP1).keepBytes hp23 ck32,hP1.pa (by change Reg.x28 ∈ keptRegs; decide),b1,h.ia.rs]
    refine VG.Proof.MlDsa.AArch64.Sign.seed34 hrho ?_ ?_
    · rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add,((L.post hP1).post hP2).keepBytes hP3 ck12,m2,hP2.pa (by change Reg.x28 ∈ keptRegs; decide)]
      exact VG.Proof.MlDsa.AArch64.Sign.bytes1_write _ _ _
    · rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add,m3,hP3.pa (by change Reg.x28 ∈ keptRegs; decide)]
      exact VG.Proof.MlDsa.AArch64.Sign.bytes1_write _ _ _
  · rw [L.keepBytes hp (ckprev k (by omega))]
    exact h.done k (by omega)

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4`. -/
section

/-! Signing matrix expansion in batches of four: sampler outcomes, bounded failure, and the single-stream remainder. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem aseeds_eq {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.AS p D σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS4)) k = VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+k) := by
  unfold seed4
  rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add]
  exact h.done k hk

theorem rej4Call_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {s : State} (L : Lay D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) s)
    {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.Sign.rej4Chk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) seed a ss = true) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args seed a ss)) s fun t =>
      PPostB D s t [(a,4096),(ss,8192)] ∧ t.gpr .x24 = s.gpr .x24 ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced t.mem (poly4 (VG.Proof.MlDsa.AArch64.pa s a) k)) ∧
      (((t.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s seed) k) = some (polyAt t.mem (poly4 (VG.Proof.MlDsa.AArch64.pa s a) k))) ∨
        ((t.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s seed) k) = none)) ∧
      ((t.gpr .x0).setWidth 32 = 1 → ∀ k < 4,(rejNTTPoly maxBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.AArch64.pa s seed) k)).isSome) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.rej4Chk,Bool.and_eq_true,and_assoc] at hc'
  obtain ⟨_,_,_,c4,c5,c6,_,_⟩ := hc'
  refine WP.mono (callAt_ok L.s64 (hP.rej4.withPost hP.rej4Max) (VG.Proof.MlDsa.AArch64.Sign.rej4_args L.ok c4 c5 c6)
    (by simp only [List.map_cons,List.map_nil]; decide) (fun s1 h1 => VG.Proof.MlDsa.AArch64.Sign.rej4_pre L hc h1) (VG.Proof.MlDsa.AArch64.Sign.rej4_cov L hc).1
    (VG.Proof.MlDsa.AArch64.Sign.rej4_cov L hc).2) fun t ⟨hp,s1,h1,hq,hx⟩ => ⟨hp.b,hp.cs .x24 (by decide) (by decide),?_⟩
  sig_post [rejNTT4Contract,rejNTT4Sig,AArch64.abi,AArch64.argRegs] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
  simp only [State.withRegions_gpr,State.withRegions_mem,State.callEntry_mem,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),Args.r0 h1,Args.mem h1,Arg.val] at hx
  exact ⟨hq.1,hq.2,hx⟩

def batchChk (p : Params) (g : Nat) : Bool :=
  let a := pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g)
  let ws : List (Ptr × Nat) := [(a,4096),(sc (oR4 p),8192)]
  VG.Proof.MlDsa.AArch64.Sign.rej4Chk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oRS4) a (sc (oR4 p)) && VG.Proof.MlDsa.AArch64.Sign.stChk p ws && VG.Proof.MlDsa.AArch64.Sign.stChk p [] &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oRS) 32 && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.aBase p) (4*g)

theorem batchChk_ok : ∀ p ∈ [mlDsa44,mlDsa65,mlDsa87],∀ g < p.k*p.ℓ/4,VG.Proof.MlDsa.AArch64.Sign.batchChk p g = true := by decide +kernel

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (VG.Proof.MlDsa.AArch64.pa s (pS e)) k = VG.Proof.MlDsa.AArch64.pa s (pS (e+k)) := by
  unfold poly4
  rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc_add]
  rw [show oP e+1024*k = oP (e+k) by simp only [oP]; omega]

theorem batch_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.batchChk p g = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.AS p D σ (4*g) 4 s) :
    WP isa (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4
      (VG.Proof.MlDsa.AArch64.Sign.rej4Args (sc oRS4) (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g)) (sc (oR4 p)))) (.block and24)) s
      (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (4*g+4)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.batchChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨cr,cst⟩,c0⟩,crs⟩,cfam⟩ := hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.rej4Call_ok hP h.ia.st.lay cr) fun s1 ⟨hp,h24,hred,hout,hmax⟩ => ?_)
  have S1 := h.ia.st.step hp cst
  refine WP.mono (and24_ok s1) fun t ⟨kt,et⟩ => ?_
  have hpt : PPostB D s1 t [] := VG.Proof.MlDsa.AArch64.Sign.postB24 kt _
  have hr : (s1.gpr .x0).setWidth 32 = 1 ∨ (s1.gpr .x0).setWidth 32 = 0 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩; exacts [.inl h1,.inr h0]
  have et' : t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s1.gpr .x0).setWidth 32) := by rw [et,h24]
  refine ⟨S1.step hpt c0,by rw [kt.mem,hpt.pa (by decide),h.ia.st.lay.keepBytes hp crs]; exact h.ia.rs,
    ?_,fun ht => ?_,fun ht => ?_⟩
  · rw [et']
    rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] <;> decide
  · have hs : s.gpr .x24 = 1 ∧ (s1.gpr .x0).setWidth 32 = 1 := by
      rw [et'] at ht
      rcases h.ia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0,e1] at ht <;>
        first | exact ⟨e0,e1⟩ | exact absurd ht (by decide)
    obtain ⟨ok,fam⟩ := h.ia.ok hs.1
    have fm := Fam.of_eq kt.mem (hpt.bs _ (by decide)) (Fam.keep h.ia.st.lay hp cfam fam)
    refine ⟨fun e' he' => ?_,fun e' he' => ?_⟩
    · by_cases hlt : e' < 4*g
      · exact ok e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
        rw [← VG.Proof.MlDsa.AArch64.Sign.aseeds_eq h (by omega)]; exact hmax hs.2 k (by omega)
    · by_cases hlt : e' < 4*g
      · exact fm e' hlt
      · obtain ⟨k,rfl⟩ : ∃ k,e'=4*g+k := ⟨e'-4*g,by omega⟩
        have hk : k < 4 := by omega
        have hm := hmax hs.2 k hk
        have hv : polyAt s1.mem (poly4 (VG.Proof.MlDsa.AArch64.pa s (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g))) k) = VG.Proof.MlDsa.AArch64.Sign.aVal p σ (4*g+k) := by
          obtain ⟨_,hb⟩ | ⟨h0,_⟩ := hout
          · have hv := VG.Proof.MlDsa.AArch64.Sign.rej_val (.inl ⟨hs.2,hb k hk⟩) hs.2 hm
            rw [VG.Proof.MlDsa.AArch64.Sign.aseeds_eq h hk] at hv
            exact hv
          · rw [hs.2] at h0; cases h0
        show PolyIs t.mem (VG.Proof.MlDsa.AArch64.pa t (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+(4*g+k)))) (VG.Proof.MlDsa.AArch64.Sign.aVal p σ (4*g+k))
        rw [kt.mem,hpt.pa (by change Reg.x28 ∈ keptRegs; decide),hp.pa (by change Reg.x28 ∈ keptRegs; decide),← Nat.add_assoc,← VG.Proof.MlDsa.AArch64.Sign.pa_poly4]
        exact ⟨hred hs.2 k hk,hv⟩
  · rw [et'] at ht
    rcases h.ia.r01 with e0 | e0
    · obtain ⟨e',he',hn⟩ := h.ia.bad e0; exact ⟨e',by omega,hn⟩
    · rcases hr with e1 | e1
      · rw [e0,e1] at ht; exact absurd ht (by decide)
      · rcases hout with ⟨h1,_⟩ | ⟨_,k,hk,hn⟩
        · exact absurd (e1.symm.trans h1) (by decide)
        · exact ⟨4*g+k,by omega,by rw [← VG.Proof.MlDsa.AArch64.Sign.aseeds_eq h hk]; exact hn⟩

end VG.Proof.MlDsa.AArch64.Sign

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem sample4_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hb : VG.Proof.MlDsa.AArch64.Sign.batchChk p g = true) (hs : ∀ j < 4,VG.Proof.MlDsa.AArch64.Sign.slotChk p (4*g) j = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ (4*g) s) :
    WP isa (sample4 P p g) s (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (4*g+4)) := by
  unfold sample4
  refine WP.seq (WP.mono (seqR_ok (I := VG.Proof.MlDsa.AArch64.Sign.AS p D σ (4*g)) 4 0
    (fun j _ hj s h => WP.mono (VG.Proof.MlDsa.AArch64.Sign.slot4_ok (by omega) (hs j (by omega)) h) fun _ ht => ht.1)
    s ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩) fun t ht => ?_)
  exact VG.Proof.MlDsa.AArch64.Sign.batch_ok hP hb (by simpa using ht)

theorem sampleAll_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p)
    (hc : VG.Proof.MlDsa.AArch64.Sign.aChk p = true) {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ 0 s) :
    WP isa (sampleAll P p) s (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (p.k*p.ℓ)) := by
  have hp : p ∈ [mlDsa44,mlDsa65,mlDsa87] := by rcases h3 with rfl | rfl | rfl <;> simp
  have he : ∀ e < p.k*p.ℓ,VG.Proof.MlDsa.AArch64.Sign.eChk p e = true := by
    simp only [VG.Proof.MlDsa.AArch64.Sign.aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc
    exact hc.1.1.1
  unfold sampleAll
  refine WP.seq (WP.mono (seqR_ok (I := fun g => VG.Proof.MlDsa.AArch64.Sign.IA p D σ (4*g)) (p.k*p.ℓ/4) 0
    (fun g _ hg s h => VG.Proof.MlDsa.AArch64.Sign.sample4_ok hP (VG.Proof.MlDsa.AArch64.Sign.batchChk_ok p hp g (by omega))
      (fun j hj => VG.Proof.MlDsa.AArch64.Sign.slotChk_ok p hp (4*g) (by omega) j hj) h) s h) fun t ht => ?_)
  have htail := seqR_ok (I := VG.Proof.MlDsa.AArch64.Sign.IA p D σ) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
    (fun e _ he' s h => VG.Proof.MlDsa.AArch64.Sign.sampleE_ok hP (he e (by omega)) h) t (by simpa only [Nat.zero_add] using ht)
  have eqn : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [eqn] using htail

theorem expandA_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (hc : VG.Proof.MlDsa.AArch64.Sign.aChk p = true) {σ s : State}
    (hs : VG.Proof.MlDsa.AArch64.Sign.St p D σ s) (h15 : s.gpr .x24 = 1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s (VG.Proof.MlDsa.AArch64.Sign.IA p D σ (p.k*p.ℓ)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.aChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨_,hcp⟩,hst⟩,hsk⟩ := hc'
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine WP.seq (WP.mono (copyP_ok hs.lay hcp) fun s1 ⟨hP1,hcs1,hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24,h15]
  exact VG.Proof.MlDsa.AArch64.Sign.sampleAll_ok hP h3 hc ⟨S1,by rw [hP1.pa (by decide),hb,VG.Proof.MlDsa.AArch64.Sign.rhoOf,← hs.sk,VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15,fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _),fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD`. -/
section

/-!
# ML-DSA signing on AArch64: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : VG.Spec.MlDsa.Poly := s1F p (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : VG.Spec.MlDsa.Poly := s2F p (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : VG.Spec.MlDsa.Poly := t0F p (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((VG.Proof.MlDsa.AArch64.Sign.skOf p σ).drop 32).take 32 ++ VG.Proof.MlDsa.AArch64.Sign.rndOf σ ++ VG.Proof.MlDsa.AArch64.Sign.muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.AArch64.Sign.St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e)).isSome
  A : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.aBase p) (p.k * p.ℓ) (VG.Proof.MlDsa.AArch64.Sign.aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlDsa.AArch64.Sign.stChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.AArch64.Sign.IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.imChk p ws = true) : VG.Proof.MlDsa.AArch64.Sign.IM p D σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

theorem IA.im {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ (p.k * p.ℓ) s) (h1 : s.gpr .x24 = 1) :
    VG.Proof.MlDsa.AArch64.Sign.IM p D σ s := ⟨h.st, (h.ok h1).1, (h.ok h1).2⟩

/-! ## The private key -/

/-- `Â`, the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (D : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : VG.Proof.MlDsa.AArch64.Sign.IM p D σ s
  s1 : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.s1Base p) a (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)
  s2 : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.s2Base p) b (VG.Proof.MlDsa.AArch64.Sign.S2v p σ)
  t0 : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.t0Base p) c (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.imChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.s1Base p) a && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.s2Base p) b && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.t0Base p) c

theorem ID.step {p : Params} {D : Nat} {σ s s' : State} {a b c : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.ID p D σ a b c s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.idChk p ws a b c = true) : VG.Proof.MlDsa.AArch64.Sign.ID p D σ a b c s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.idChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.im.st.lay
  exact ⟨h.im.step hP h1, Fam.keep L hP h2 h.s1, Fam.keep L hP h3 h.s2, Fam.keep L hP h4 h.t0⟩

theorem pS_bases (j : Nat) : (pS j).1 ∈ keptRegs := by simp

theorem sc_bases (o : Nat) : (sc o).1 ∈ keptRegs := by simp

theorem pa_add (s : State) (r : Reg) (a b : Nat) : VG.Proof.MlDsa.AArch64.pa s (r, a) + BitVec.ofNat 64 b = VG.Proof.MlDsa.AArch64.pa s (r, a + b) := by
  rw [VG.Proof.MlDsa.AArch64.pa, VG.Proof.MlDsa.AArch64.pa, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x25, o)) len = ((VG.Proof.MlDsa.AArch64.Sign.skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, VG.Proof.MlDsa.AArch64.Sign.pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) src len (pS j) 1024 && VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (pS j) &&
    VG.Proof.MlDsa.AArch64.Sign.idChk p [(pS j, 1024)] a b c && VG.Proof.MlDsa.AArch64.Sign.idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

theorem dec_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {a b c : Nat} {src : Ptr}
    {len x y j : Nat} (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y))
    (hc : VG.Proof.MlDsa.AArch64.Sign.decChk p a b c src len j = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.ID p D σ a b c s) :
    WP isa (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) s fun s' =>
      VG.Proof.MlDsa.AArch64.Sign.ID p D σ a b c s' ∧ VG.Proof.MlDsa.AArch64.Sign.Pl s' j (VG.Spec.MlDsa.ntt (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s src) len) x y))) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.bupAt_ok hP h.im.st.lay hp hl h1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 h3
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt I1.im.st.lay h2 (by rw [hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases j)]; exact hq1.1))
    fun s2 ⟨hP2, _, hq2⟩ => ⟨I1.step hP2 h4, ?_⟩
  show PolyIs s2.mem (VG.Proof.MlDsa.AArch64.pa s2 (pS j)) _
  rw [hP2.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases j), hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases j), ← hq1.2]
  rw [hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases j)] at hq2
  exact hq2

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => VG.Proof.MlDsa.AArch64.Sign.decChk p r 0 0 (.x25, skS1 p r) (sLen p) (VG.Proof.MlDsa.AArch64.Sign.s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.AArch64.Sign.decChk p p.ℓ i 0 (.x25, skS2 p i) (sLen p) (VG.Proof.MlDsa.AArch64.Sign.s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => VG.Proof.MlDsa.AArch64.Sign.decChk p p.ℓ p.k i (.x25, skT0 p i) 416 (VG.Proof.MlDsa.AArch64.Sign.t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    hashChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩ &&
    VG.Proof.MlDsa.AArch64.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oMS)) 64 = VG.Proof.MlDsa.AArch64.Sign.rppOf p σ

theorem dChk_spec {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.dChk p = true) :
    (∀ r < p.ℓ, VG.Proof.MlDsa.AArch64.Sign.decChk p r 0 0 (.x25, skS1 p r) (sLen p) (VG.Proof.MlDsa.AArch64.Sign.s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.AArch64.Sign.decChk p p.ℓ i 0 (.x25, skS2 p i) (sLen p) (VG.Proof.MlDsa.AArch64.Sign.s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, VG.Proof.MlDsa.AArch64.Sign.decChk p p.ℓ p.k i (.x25, skT0 p i) 416 (VG.Proof.MlDsa.AArch64.Sign.t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    hashChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩ = true ∧
    VG.Proof.MlDsa.AArch64.Sign.idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.dChk p = true) {σ : State}
include hP hc

theorem decS1_ok {r : Nat} (hr : r < p.ℓ) {s : State} (hs : VG.Proof.MlDsa.AArch64.Sign.ID p D σ r 0 0 s) :
    WP isa (decS1 P p r) s (VG.Proof.MlDsa.AArch64.Sign.ID p D σ (r + 1) 0 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc).1 r hr
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.dec_ok hP (VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.AArch64.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, Fam.snoc I'.s1 ?_, I'.s2, I'.t0⟩
  rw [VG.Proof.MlDsa.AArch64.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decS2_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ i 0 s) :
    WP isa (decS2 P p i) s (VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ (i + 1) 0) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc).2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.dec_ok hP (VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc).2.2.2.2.2.2.1 (VG.Proof.MlDsa.AArch64.Sign.sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, I'.s1, Fam.snoc I'.s2 ?_, I'.t0⟩
  rw [VG.Proof.MlDsa.AArch64.Sign.sk_slice hs.im.st ck] at hq
  exact hq

theorem decT0_ok {i : Nat} (hi : i < p.k) {s : State} (hs : VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k i s) :
    WP isa (decT0 P p i) s (VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k (i + 1)) := by
  obtain ⟨c, ck⟩ := (VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc).2.2.1 i hi
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.dec_ok hP (by decide) (by decide) c hs) fun s' ⟨I', hq⟩ => ⟨I'.im, I'.s1, I'.s2,
    Fam.snoc I'.t0 ?_⟩
  have e : skT0 p i = 128 + lenS p * p.ℓ + lenS p * p.k + 32 * 13 * i := by
    unfold skT0 lenS sLen; rw [Nat.mul_add]; omega
  rw [VG.Proof.MlDsa.AArch64.Sign.sk_slice hs.im.st ck, e] at hq
  exact hq

theorem rpp_ok {s : State} (hs : VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k p.k s) :
    WP isa (shakeAtWith keccak.callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, oMS, 64⟩) s (VG.Proof.MlDsa.AArch64.Sign.IK p D σ) := by
  obtain ⟨_, _, _, h4, h5, _, _, hsk⟩ := VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc
  refine WP.mono (shake_ok hP.s16 hP.s64 hs.im.st.lay (by simp) h4) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs.step hP4 h5, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show H (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x25, 32)) 32 ++ (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x27, 0)) 32 ++
    bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x26, 0)) 64)) 64 = _
  rw [VG.Proof.MlDsa.AArch64.Sign.sk_slice hs.im.st (o := 32) (len := 32) (by omega), hs.im.st.rnd, hs.im.st.mu, ← List.append_assoc]

theorem decode_ok {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IM p D σ s) : WP isa (decodeWith keccak.callee P p) s (VG.Proof.MlDsa.AArch64.Sign.IK p D σ) := by
  unfold decodeWith
  refine WP.seq (WP.mono (seqR_ok (I := fun r => VG.Proof.MlDsa.AArch64.Sign.ID p D σ r 0 0) p.ℓ 0
    (fun r _ hr s hs => VG.Proof.MlDsa.AArch64.Sign.decS1_ok hP hc (by omega) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ i 0) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.decS2_ok hP hc (by omega) hs) s1
    ⟨hs1.im, hs1.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.decT0_ok hP hc (by omega) hs) s2
    ⟨hs2.im, hs2.s1, hs2.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  exact VG.Proof.MlDsa.AArch64.Sign.rpp_ok hP hc hs3

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseC`. -/
section

/-!
# ML-DSA signing on AArch64: the commitment of an iteration

At the head of iteration `t` of the loop (`IL`): what decoding left, `κ = ℓt`
at `KAP`, `814 - t` at `CNT`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`
(`maskR_ok`), `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` (`rowW_ok`),
`w1Encode(HighBits(w[i]))` at `W1` (`w1R_ok`), and `c̃ = H(μ ‖ w1Encode(w₁),
λ/4)` at `CT` (`commit_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : VG.Spec.MlDsa.Poly := aF maxBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := toRq (yF p (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := yhF p (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := wF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.AArch64.Sign.aVal p σ (p.ℓ * i + j) = VG.Proof.MlDsa.AArch64.Sign.Am p σ i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.AArch64.Sign.aVal, e1, e2]

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * t)
  cnt : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  t_lt : t < 814
  rej : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.idChk p ws p.ℓ p.k p.k && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps `IL`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ikChk p ws && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oKAP) 8 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oCNT) 8

theorem IK.step {p : Params} {D : Nat} {σ s s' : State} (h : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.ikChk p ws = true) : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.ikChk, Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hc.1, (h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

theorem IL.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.ilChk p ws = true) : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.ilChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP h1, (L.keepW hP h2).trans h.kap, (L.keepW hP h3).trans h.cnt, h.t_lt, h.rej⟩

theorem IL.st {p : Params} {D : Nat} {σ s : State} {t : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) : VG.Proof.MlDsa.AArch64.Sign.St p D σ s := h.k.d.im.st

/-! ## `κ + r` -/

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [VG.Proof.MlDsa.AArch64.Sign.integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, ifn (VG.Proof.MlDsa.AArch64.Sign.add_one_ne a), ifp rfl,
    VG.Proof.MlKem.writeW8_apply, ifp rfl]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r x : Nat}
    (hr : r < 4096) (hx : x + r < 2 ^ 16) (h1 : VG.CallLay.inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : VG.CallLay.inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKappa r)) s fun s' => PPostB D s s' [(sc (oMS + 64), 2)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 := by
  have e65 : VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65)) = VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)) + 1 := (VG.Proof.MlDsa.AArch64.Sign.pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 1 := by
    have := Offset.contains_base (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 1 := by
    have := VG.CallLay.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.CallLay.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setKappa_run r hr s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, VG.Proof.MlDsa.AArch64.Sign.bytes2_write, hk, VG.Proof.MlDsa.AArch64.Sign.ofNat64_add, VG.Proof.MlDsa.AArch64.Sign.kappa_bytes hx]

/-! ## `y` and `ŷ` -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure ICm (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) r (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yhBase p) r (VG.Proof.MlDsa.AArch64.Sign.YHv p σ (p.ℓ * t))

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ilChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p) r && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yhBase p) r

theorem ICm.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.icmChk p ws r = true) : VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t r s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.icmChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (VG.Proof.MlDsa.AArch64.Sign.yBase p + r)
  let yh := pS (VG.Proof.MlDsa.AArch64.Sign.yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  VG.Proof.MlDsa.AArch64.Sign.icmChk p w1 r && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oKAP) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc (oMS + 64)) 2 && VG.Proof.MlDsa.AArch64.Sign.maskChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) y &&
    VG.Proof.MlDsa.AArch64.Sign.icmChk p w2 r && VG.Proof.MlDsa.AArch64.Sign.copyChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) yh y 1024 && VG.Proof.MlDsa.AArch64.Sign.icmChk p w3 r && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (VG.Proof.MlDsa.AArch64.Sign.yBase p) (r + 1) &&
    VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) yh && VG.Proof.MlDsa.AArch64.Sign.icmChk p w4 r && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w4 (VG.Proof.MlDsa.AArch64.Sign.yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 4096) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem maskR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.mChk p r = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t r s) : WP isa (maskR P p r) s (VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, k1⟩, w1⟩, cm⟩, c2⟩, cc⟩, c3⟩, f3⟩, ci⟩, c4⟩, f4⟩, hx⟩, hr⟩, hγ⟩ := hc
  have ht := h.l.t_lt
  unfold maskR
  have hx' : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega); omega
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.step hP1 c1
  have hms : bytesAt s1.mem (VG.Proof.MlDsa.AArch64.pa s1 (sc oMS)) 66 = VG.Proof.MlDsa.AArch64.Sign.rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, I1.l.k.rpp, VG.Proof.MlDsa.AArch64.Sign.pa_sc_add, hP1.pa (by decide), hb1]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.maskAt_ok hP I1.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 c2
  have hy2 : VG.Proof.MlDsa.AArch64.Sign.Fam s2 (VG.Proof.MlDsa.AArch64.Sign.yBase p) (r + 1) (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t)) :=
    Fam.snoc I2.y (by
      show PolyIs s2.mem (VG.Proof.MlDsa.AArch64.pa s2 (pS (VG.Proof.MlDsa.AArch64.Sign.yBase p + r))) _
      rw [hP2.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq2)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_ok I2.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I2.step hP3 c3
  have hyh3 : VG.Proof.MlDsa.AArch64.Sign.Pl s3 (VG.Proof.MlDsa.AArch64.Sign.yhBase p + r) (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]
    exact polyIs_of_bytes hb3 (hy2 r (by omega))
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I2.l.st.lay hP3 f3 hy2), Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _), hyh3.2] at *
  exact hq4

/-! ## `w` -/

/-- Iteration `t`, with `y`, `ŷ`, and the first `i` polynomials of `w`. -/
structure ICw (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s
  y : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t))
  yh : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yhBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.YHv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p) i (VG.Proof.MlDsa.AArch64.Sign.Wv p σ (p.ℓ * t))

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.icmChk p ws p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p) i

theorem ICw.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.icwChk p ws i = true) : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.icwChk, Bool.and_eq_true] at hc
  have I : VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t p.ℓ s' := (ICm.mk h.l h.y h.yh).step hP hc.1
  exact ⟨I.l, I.y, I.yh, Fam.keep h.l.st.lay hP hc.2 h.w⟩

/-- `∑_{j < m} Â[i, j] ŷ[j]`, summed from `j = 0` with `AddNTT`. -/
abbrev wAcc (p : Params) (σ : State) (κ i m : Nat) : VG.Spec.MlDsa.Poly :=
  ((List.range m).map fun j => multiplyNTT (VG.Proof.MlDsa.AArch64.Sign.Am p σ i j) (VG.Proof.MlDsa.AArch64.Sign.YHv p σ κ j)).foldl VG.Spec.MlDsa.add VG.Spec.MlDsa.zero

theorem add_zero_left (x : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.add VG.Spec.MlDsa.zero x = x := by
  apply Vector.ext
  intro j hj
  simp [VG.Spec.MlDsa.add, VG.Spec.MlDsa.zero]

theorem wAcc_one (p : Params) (σ : State) (κ i : Nat) :
    VG.Proof.MlDsa.AArch64.Sign.wAcc p σ κ i 1 = multiplyNTT (VG.Proof.MlDsa.AArch64.Sign.Am p σ i 0) (VG.Proof.MlDsa.AArch64.Sign.YHv p σ κ 0) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.wAcc, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, VG.Proof.MlDsa.AArch64.Sign.add_zero_left]

theorem wAcc_succ (p : Params) (σ : State) (κ i m : Nat) :
    VG.Proof.MlDsa.AArch64.Sign.wAcc p σ κ i (m + 1) = VG.Spec.MlDsa.add (VG.Proof.MlDsa.AArch64.Sign.wAcc p σ κ i m) (multiplyNTT (VG.Proof.MlDsa.AArch64.Sign.Am p σ i m) (VG.Proof.MlDsa.AArch64.Sign.YHv p σ κ m)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.wAcc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem aP_ij (p : Params) (i j : Nat) : VG.Impl.MlDsa.AArch64.Sign.aP p i j = pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.AArch64.Sign.wBase p + i)
  (List.range p.ℓ).all (fun j => mulChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w (VG.Impl.MlDsa.AArch64.Sign.aP p i j) (yhP p j)) && VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w &&
    VG.Proof.MlDsa.AArch64.Sign.icwChk p [(w, 1024)] i && VG.Proof.MlDsa.AArch64.Sign.icwChk p [(w, 1024), (sc oPS, 1024)] i && decide (0 < p.ℓ)

theorem rowW_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.wChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) :
    WP isa (rowW P p i) s (VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, c2⟩, hl⟩ := hc
  have hA : ∀ {s : State} (I : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.AArch64.pa s (VG.Impl.MlDsa.AArch64.Sign.aP p i j)) (VG.Proof.MlDsa.AArch64.Sign.Am p σ i j) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.AArch64.Sign.aVal_ij hj] at this
      rw [VG.Proof.MlDsa.AArch64.Sign.aP_ij]; exact this
  have hY : ∀ {s : State} (I : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) j, j < p.ℓ → PolyIs s.mem (VG.Proof.MlDsa.AArch64.pa s (yhP p j)) (VG.Proof.MlDsa.AArch64.Sign.YHv p σ (p.ℓ * t) j) :=
    fun I j hj => I.yh j hj
  unfold rowW
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul h.l.st.lay (cm 0 hl) (hA h 0 hl).1 (hY h 0 hl).1)
    fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 c1
  rw [(hA h 0 hl).2, (hY h 0 hl).2, ← VG.Proof.MlDsa.AArch64.Sign.wAcc_one] at hq1
  refine WP.seq (WP.mono (seqR_ok (I := fun j s => VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s ∧ VG.Proof.MlDsa.AArch64.Sign.Pl s (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.wAcc p σ (p.ℓ * t) i j))
    (p.ℓ - 1) 1 (fun j hj1 hj s ⟨I, hw⟩ => ?_) s1 ⟨I1, by show PolyIs _ _ _; rw [hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq1⟩)
    fun s2 ⟨I2, hw2⟩ => ?_)
  · refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAddAt_ok hP.mulAdd I.l.st.lay (cm j (by omega)) hw.1 (hA I j (by omega)).1
      (hY I j (by omega)).1) fun s' ⟨hP', _, hq'⟩ => ⟨I.step hP' c1, ?_⟩
    rw [hw.2, (hA I j (by omega)).2, (hY I j (by omega)).2, ← VG.Proof.MlDsa.AArch64.Sign.wAcc_succ] at hq'
    show PolyIs _ _ _
    rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq'
  rw [show 1 + (p.ℓ - 1) = p.ℓ by omega] at hw2
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I2.l.st.lay ci hw2.1) fun s3 ⟨hP3, _, hq3⟩ => ?_
  have I3 := I2.step hP3 c2
  refine ⟨I3.l, I3.y, I3.yh, Fam.snoc I3.w ?_⟩
  show PolyIs _ _ _
  rw [hP3.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]
  rw [hw2.2] at hq3
  exact hq3

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => VG.Spec.MlDsa.simpleBitPack (w1F p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `ŷ`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure ICh (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t p.k s
  w1 : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.AArch64.Sign.w1Enc p σ (p.ℓ * t) i

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let w := pS (VG.Proof.MlDsa.AArch64.Sign.wBase p + i)
  let o := sc (oW1 + w1Len p * i)
  rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w 1024 t1P 1024 && rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t1P 1024 o (w1Len p) &&
    VG.Proof.MlDsa.AArch64.Sign.icwChk p [(t1P, 1024)] p.k && VG.Proof.MlDsa.AArch64.Sign.icwChk p [(o, w1Len p)] p.k && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(t1P, 1024)] (sc oW1) (w1Len p * i) &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(o, w1Len p)] (sc oW1) (w1Len p * i) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (p.γ₂ ∈ gamma2s)

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

theorem w1R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.hChk p i = true) (hi : i < p.k) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i s) :
    WP isa (w1R P p i) s (VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, k1⟩, k2⟩, e1⟩, e2⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.highBitsAt_ok hP h.c.l.st.lay hγ c1 (h.c.w i hi).1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.c.step hP1 k1
  rw [(h.c.w i hi).2] at hq1
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.sbpAt_ok hP I1.l.st.lay hb rfl c2 fun j hj => ?_) fun s2 ⟨hP2, _, hq2⟩ => ?_
  · rw [hP1.pa (by decide), VG.Proof.MlDsa.AArch64.Sign.natPolyIs_coeff hq1 hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _
  have I2 := I1.step hP2 k2
  refine ⟨I2, ?_⟩
  have b1 : bytesAt s2.mem (VG.Proof.MlDsa.AArch64.pa s2 (sc oW1)) (w1Len p * i) = VG.Proof.MlDsa.AArch64.Sign.w1Enc p σ (p.ℓ * t) i := by
    rw [I1.l.st.lay.keepBytes hP2 e2, h.c.l.st.lay.keepBytes hP1 e1, h.w1]
  have b2 : bytesAt s2.mem (VG.Proof.MlDsa.AArch64.pa s2 (sc (oW1 + w1Len p * i))) (w1Len p) =
      VG.Spec.MlDsa.simpleBitPack (w1F p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    rw [hP2.pa (VG.Proof.MlDsa.AArch64.Sign.sc_bases _), hq2, hP1.pa (by decide), show natPolyAt s1.mem (VG.Proof.MlDsa.AArch64.pa s t1P) = _ from hq1]
    rfl
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, VG.Proof.MlDsa.AArch64.Sign.pa_sc_add, b1, b2, VG.Proof.MlDsa.AArch64.Sign.w1Enc, VG.Proof.MlDsa.AArch64.Sign.w1Enc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]

/-- The commitment of iteration `t`: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
structure IC (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  (List.range p.ℓ).all (VG.Proof.MlDsa.AArch64.Sign.mChk p) && (List.range p.k).all (VG.Proof.MlDsa.AArch64.Sign.wChk p) && (List.range p.k).all (VG.Proof.MlDsa.AArch64.Sign.hChk p) &&
    hashChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩ &&
    VG.Proof.MlDsa.AArch64.Sign.icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem commit_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) : WP isa (commitWith keccak.callee P p) s (VG.Proof.MlDsa.AArch64.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commitWith
  refine WP.seq (WP.mono (seqR_ok (I := fun r => VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t r) p.ℓ 0
    (fun r _ hr s hs => VG.Proof.MlDsa.AArch64.Sign.maskR_ok hP (hm r (by omega)) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.rowW_ok hP (hw i (by omega)) (by omega) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i) p.k 0
    (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.w1R_ok hP (hh i (by omega)) (by omega) hs) s2
    ⟨hs2, by simp [VG.Proof.MlDsa.AArch64.Sign.w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (shake_ok hP.s16 hP.s64 hs3.c.l.st.lay (by simp) hs) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show H (bytesAt s3.mem (VG.Proof.MlDsa.AArch64.pa s3 (.x26, 0)) 64 ++ bytesAt s3.mem (VG.Proof.MlDsa.AArch64.pa s3 (sc oW1)) (p.k * w1Len p)) (cLen p) = _
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [VG.Proof.MlDsa.AArch64.Sign.CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK`. -/
section

/-!
# ML-DSA signing on AArch64: the checks of an iteration

`c = SampleInBall(c̃)` at `ĉ` (`ball_ok`), and, if it succeeded, `ĉ = NTT(c)`
and each check of the iteration, their results ANDed into `x24`: the norm of
each `z[r]` (`zR_ok`), of each `r₀[i]` (`r0R_ok`) and of each `ct₀[i]`, with
each hint `h[i]` and the number of its 1s summed at `ONES` (`hR_ok`), and that
sum against `ω` (`onesOk_ok`); so `x24` is 1 exactly when the iteration passes
(`checks_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `c = SampleInBall(c̃)` of the iteration with counter `κ`, within `maxBounds`. -/
abbrev cV (σ : State) (κ : Nat) : IPoly :=
  (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).getD (Vector.replicate n 0)

/-- `z[r]`, `r₀[i]`, `ct₀[i]`, `w[i] - cs₂[i]`, `w[i] - cs₂[i] + ct₀[i]` and `h[i]`. -/
abbrev Zv (σ : State) (κ r : Nat) : VG.Spec.MlDsa.Poly := zF p (VG.Proof.MlDsa.AArch64.Sign.S1v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) r
abbrev R0v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := r0F p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) i
abbrev CT0v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := ct0F (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) i
abbrev W'v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w'F p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) i
abbrev W''v (σ : State) (κ i : Nat) : VG.Spec.MlDsa.Poly := w''F p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) i
abbrev Hv (σ : State) (κ i : Nat) : Vector Bool n := hF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) i

/-- Whether the iteration with counter `κ` passes, once `SampleInBall` succeeded. -/
abbrev PassV (σ : State) (κ : Nat) : Prop :=
  passF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S1v p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ)

end

/-! ## `SampleInBall` -/

/-- After `SampleInBall`: the commitment, and `c` at `ĉ` if it succeeded. -/
structure IB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)
  r01 : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1
  ok : (s.gpr .x0).setWidth 32 = 1 → VG.Proof.MlDsa.AArch64.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.AArch64.Sign.cV p σ (p.ℓ * t))) ∧
    (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome
  bad : (s.gpr .x0).setWidth 32 = 0 → sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)) = none

def bChk (p : Params) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ballChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (cLen p) cP && VG.Proof.MlDsa.AArch64.Sign.icwChk p [(cP, 1024), (sc oPS, 2048)] p.k &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(cP, 1024), (sc oPS, 2048)] (sc oCT) (cLen p) && decide ((cLen p, p.τ) ∈ ballParams)

theorem ball_val {τ : Nat} {x : List Byte} {r : BitVec 32} {out : VG.Spec.MlDsa.Poly}
    (h : Outcome (fun b => (sampleInBall τ b.ball x).map toRq) r out) (h1 : r = 1)
    (hm : (sampleInBall τ maxBounds.ball x).isSome) :
    out = toRq ((sampleInBall τ maxBounds.ball x).getD (Vector.replicate n 0)) := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
    have e1 := sampleInBall_mono (Nat.le_max_left b.ball maxBounds.ball) hc
    have e2 := sampleInBall_mono (Nat.le_max_right b.ball maxBounds.ball) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem ball_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.bChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IC p D σ t s) : WP isa (ballAt P (cLen p) p.τ cP) s (VG.Proof.MlDsa.AArch64.Sign.IB p D σ t) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, hbp⟩ := hc
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.ballCall_ok hP h.c.l.st.lay hbp c1) fun s' ⟨hP1, _, hred, hout, hmax⟩ => ?_
  rw [h.ct] at hout hmax
  refine ⟨h.c.step hP1 c2, by rw [h.c.l.st.lay.keepBytes hP1 c3, h.ct], ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rcases hout with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  · refine ⟨?_, hmax h1⟩
    show PolyIs _ _ _
    rw [hP1.pa (by decide)]
    exact ⟨hred h1, VG.Proof.MlDsa.AArch64.Sign.ball_val hout h1 (hmax h1)⟩
  · rcases hout with ⟨e, _⟩ | ⟨_, hn⟩
    · rw [h0] at e; cases e
    · exact Option.map_eq_none_iff.mp hn

/-! ## Norms, into `x24` -/

theorem normAt_okB {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay D rbs wbs s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.AArch64.Sign.normChk (rbs ++ wbs) f = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) {a : Prop} [Decidable a] (h15 : s.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit a) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] ∧
      s'.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit (a ∧ normRq [polyAt s.mem (VG.Proof.MlDsa.AArch64.pa s f)] < B) := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  refine WP.mono (and24_ok s1) fun s2 ⟨k2, h15'⟩ => ?_
  refine ⟨PPostB.trans hP1 (VG.Proof.MlDsa.AArch64.Sign.postB24 k2 _) (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil), ?_⟩
  rw [h15', VG.Proof.MlDsa.AArch64.Sign.bit_and (hcs1.trans h15) hq1]

theorem bit_congr {a b : Prop} [Decidable a] [Decidable b] (h : a ↔ b) : VG.Proof.MlDsa.AArch64.Sign.bit a = VG.Proof.MlDsa.AArch64.Sign.bit b := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.AArch64.Sign.bit a = 1 from ifp ha _ _, show VG.Proof.MlDsa.AArch64.Sign.bit b = 1 from ifp (h.mp ha) _ _]
  · rw [show VG.Proof.MlDsa.AArch64.Sign.bit a = 0 from ifn ha _ _, show VG.Proof.MlDsa.AArch64.Sign.bit b = 0 from ifn (fun hb => ha (h.mpr hb)) _ _]

theorem bit01 {a : Prop} [Decidable a] : VG.Proof.MlDsa.AArch64.Sign.bit a = 0 ∨ VG.Proof.MlDsa.AArch64.Sign.bit a = 1 := by
  by_cases ha : a
  · exact .inr (ifp ha _ _)
  · exact .inl (ifn ha _ _)

theorem bit_one {a : Prop} [Decidable a] : VG.Proof.MlDsa.AArch64.Sign.bit a = 1 ↔ a := by
  by_cases ha : a
  · exact ⟨fun _ => ha, fun _ => ifp ha _ _⟩
  · exact ⟨fun h => absurd (h.symm.trans (ifn ha 1 0)) (by decide), fun h => absurd h ha⟩

theorem bit_zero {a : Prop} [Decidable a] : VG.Proof.MlDsa.AArch64.Sign.bit a = 0 ↔ ¬ a := by
  by_cases ha : a
  · exact ⟨fun h => absurd (h.symm.trans (ifp ha 1 0)) (by decide), fun h => absurd ha h⟩
  · exact ⟨fun _ => ha, fun _ => ifn ha _ _⟩

theorem forall_lt_succ {P : Nat → Prop} {r : Nat} : ((∀ j < r, P j) ∧ P r) ↔ ∀ j < r + 1, P j :=
  ⟨fun ⟨h1, h2⟩ j hj => by
    rcases (by omega : j < r ∨ j = r) with hj | rfl
    exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h r (by omega)⟩⟩

theorem Fam.head {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b (m + 1) f) : VG.Proof.MlDsa.AArch64.Sign.Pl s b (f 0) := h 0 (by omega)

theorem Fam.tail {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b (m + 1) f) :
    VG.Proof.MlDsa.AArch64.Sign.Fam s (b + 1) m fun j => f (j + 1) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.AArch64.Sign.Pl s (b + 1 + j) _
  rw [show b + 1 + j = b + (j + 1) by omega]
  exact this

theorem Fam.shift {s : State} {b m r : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s (b + r) (m - r) fun j => f (r + j))
    (hr : r < m) : VG.Proof.MlDsa.AArch64.Sign.Fam s (b + (r + 1)) (m - (r + 1)) fun j => f (r + 1 + j) := fun j hj => by
  have := h (j + 1) (by omega)
  show VG.Proof.MlDsa.AArch64.Sign.Pl s (b + (r + 1) + j) (f (r + 1 + j))
  rw [show b + (r + 1) + j = b + r + (j + 1) by omega, show r + 1 + j = r + (j + 1) by omega]
  exact this

theorem Fam.zero {s : State} {b m : Nat} {f : Nat → VG.Spec.MlDsa.Poly} (h : VG.Proof.MlDsa.AArch64.Sign.Fam s b m f) :
    VG.Proof.MlDsa.AArch64.Sign.Fam s (b + 0) (m - 0) fun j => f (0 + j) := fun j hj => by
  show VG.Proof.MlDsa.AArch64.Sign.Pl s (b + 0 + j) (f (0 + j))
  rw [Nat.add_zero, Nat.zero_add]
  exact h j hj

/-! ## The checks' state -/

/-- The checks of iteration `t`, once `SampleInBall` succeeded: `ĉ = NTT(c)`. -/
structure KB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  l : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s
  ct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)
  c : VG.Proof.MlDsa.AArch64.Sign.Pl s 0 (chF (VG.Proof.MlDsa.AArch64.Sign.cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome

def kbChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ilChk p ws && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oCT) (cLen p) && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws cP 1024

theorem KB.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.kbChk p ws = true) : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.kbChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP h1, (L.keepBytes hP h2).trans h.ct, L.keepPoly hP h3 h.c, h.some⟩

/-! ## `z` -/

/-- The checks of `z[j]` for `j < r`, with `ONES = 0` (but `x24`). -/
structure IZb (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) r (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t))
  y : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (p.ℓ - r) fun j => VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t) (r + j)
  w : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k (VG.Proof.MlDsa.AArch64.Sign.Wv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 64 = 0

/-- The checks of `z[j]` for `j < r`, their results in `x24`. -/
def IZ (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t r s ∧ s.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit (∀ j < r, normRq [VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t) j] < p.γ₁ - p.β)

def zfam (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.kbChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p) r && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oONES) 8

theorem IZb.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.zfam p ws r = true)
    (hy : VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (p.ℓ - r) = true) : VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t r s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.zfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP hy h.y, Fam.keep L hP h3 h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `z[r]` needs of the layout. -/
def zChk (p : Params) (r : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(yP p r, 1024)]
  mulChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t1P cP (s1P p r) && VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t1P && accChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (yP p r) t1P &&
    VG.Proof.MlDsa.AArch64.Sign.normChk (VG.Proof.MlDsa.AArch64.Sign.sgB p) (yP p r) && VG.Proof.MlDsa.AArch64.Sign.zfam p w1 r && VG.Proof.MlDsa.AArch64.Sign.zfam p w2 r && VG.Proof.MlDsa.AArch64.Sign.zfam p w3 r && VG.Proof.MlDsa.AArch64.Sign.zfam p [] (r + 1) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (p.ℓ - r) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (p.ℓ - r) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (VG.Proof.MlDsa.AArch64.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.yBase p + (r + 1)) (p.ℓ - (r + 1)) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (VG.Proof.MlDsa.AArch64.Sign.yBase p) r && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (s1P p r) 1024 && decide (p.γ₁ - p.β < 2 ^ 32) &&
    decide (r < p.ℓ)

theorem zR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.zChk p r = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r s) : WP isa (zR P p r) s (VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t (r + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, y1⟩, y2⟩, y3⟩, y4⟩, f3⟩, e1⟩, hB⟩, hr⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs1 := h.b.l.k.d.s1 r hr
  unfold zR
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm h.b.c.1 hs1.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs1.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hy2 : VG.Proof.MlDsa.AArch64.Sign.Pl s2 (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t) r) := I2.y 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_ok hP I2.b.l.st.lay ca hy2.1 (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1))
    fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hy2.2, hP2.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.AArch64.Sign.zfam, Bool.and_eq_true] at z3 z4
  have hz3 : VG.Proof.MlDsa.AArch64.Sign.Pl s3 (VG.Proof.MlDsa.AArch64.Sign.yBase p + r) (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t (r + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.snoc (Fam.keep L2 hP3 f3 I2.z) hz3,
    Fam.keep L2 hP3 y3 (I2.y.shift hr),
    Fam.keep L2 hP3 z3.1.2 I2.w, (L2.keepW hP3 z3.2).trans I2.ones⟩
  have e15 : s3.gpr .x24 = s.gpr .x24 := by
    rw [hcs3, hcs2, hcs1]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.normAt_okB hP J3.b.l.st.lay hB cn hz3.1 (e15.trans h15)) fun s4 ⟨hP4, h4⟩ => ?_
  have L3 := J3.b.l.st.lay
  refine ⟨⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z, Fam.keep L3 hP4 y4 J3.y,
    Fam.keep L3 hP4 z4.1.2 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩, ?_⟩
  rw [h4, hz3.2]
  exact VG.Proof.MlDsa.AArch64.Sign.bit_congr VG.Proof.MlDsa.AArch64.Sign.forall_lt_succ

/-! ## `r₀` -/

/-- The checks of `r₀[j]` for `j < i` (`w[j]` is `w[j] - cs₂[j]`), with `z` checked and `ONES = 0`. -/
structure IRb (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p) i (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (p.k - i) fun j => VG.Proof.MlDsa.AArch64.Sign.Wv p σ (p.ℓ * t) (i + j)
  ones : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 64 = 0

/-- `z` passed. -/
abbrev ZOk (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.ℓ, normRq [VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ j] < p.γ₁ - p.β

def IR (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t i s ∧
    s.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit (VG.Proof.MlDsa.AArch64.Sign.ZOk p σ (p.ℓ * t) ∧ ∀ j < i, normRq [VG.Proof.MlDsa.AArch64.Sign.R0v p σ (p.ℓ * t) j] < p.γ₂ - p.β)

def rfam (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.kbChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p) i && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oONES) 8

theorem IRb.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.rfam p ws i = true)
    (hw : VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (p.k - i) = true) : VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t i s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.rfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w', Fam.keep L hP hw h.w,
    (L.keepW hP h4).trans h.ones⟩

/-- What `r₀[i]` needs of the layout. -/
def rChk (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t1P, 1024)]
  let w2 : List (Ptr × Nat) := [(t1P, 1024), (sc oPS, 1024)]
  let w3 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w4 : List (Ptr × Nat) := [(t2P, 1024)]
  mulChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t1P cP (s2P p i) && VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t1P && accChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (wP p i) t1P &&
    rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (wP p i) 1024 t2P 1024 && VG.Proof.MlDsa.AArch64.Sign.normChk (VG.Proof.MlDsa.AArch64.Sign.sgB p) t2P && VG.Proof.MlDsa.AArch64.Sign.rfam p w1 i && VG.Proof.MlDsa.AArch64.Sign.rfam p w2 i &&
    VG.Proof.MlDsa.AArch64.Sign.rfam p w3 i && VG.Proof.MlDsa.AArch64.Sign.rfam p w4 (i + 1) && VG.Proof.MlDsa.AArch64.Sign.rfam p [] (i + 1) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (p.k - i) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (p.k - i) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w3 (VG.Proof.MlDsa.AArch64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w4 (VG.Proof.MlDsa.AArch64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w4 (wP p i) 1024 &&
    decide (p.γ₂ - p.β < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k)

theorem r0R_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.rChk p i = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i s) : WP isa (r0R P p i) s (VG.Proof.MlDsa.AArch64.Sign.IR p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, z3⟩, z4⟩, z5⟩, y1⟩, y2⟩, y3⟩, y4⟩, y5⟩, k4⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have hs2 := h.b.l.k.d.s2 i hi
  unfold r0R
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm h.b.c.1 hs2.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, hs2.2] at hq1
  have I1 := h.step hP1 z1 y1
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci
    (by rw [hP1.pa (by decide)]; exact hq1.1)) fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [hP1.pa (by decide), hq1.2] at hq2
  have I2 := I1.step hP2 z2 y2
  have hw2 : VG.Proof.MlDsa.AArch64.Sign.Pl s2 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.Wv p σ (p.ℓ * t) i) := I2.w 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_ok hP I2.b.l.st.lay ca hw2.1
    (by rw [hP2.pa (by decide), hP1.pa (by decide)]; exact hq2.1)) fun s3 ⟨hP3, hcs3, hq3⟩ => ?_)
  rw [hw2.2, hP2.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1), hP1.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1), hq2.2] at hq3
  have L2 := I2.b.l.st.lay
  simp only [VG.Proof.MlDsa.AArch64.Sign.rfam, Bool.and_eq_true] at z3 z4 z5
  have hw3 : VG.Proof.MlDsa.AArch64.Sign.Pl s3 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _
    rw [hP3.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]
    exact hq3
  have J3 : VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t (i + 1) s3 := ⟨I2.b.step hP3 z3.1.1.1, Fam.keep L2 hP3 z3.1.1.2 I2.z,
    Fam.snoc (Fam.keep L2 hP3 z3.1.2 I2.w') hw3, Fam.keep L2 hP3 y3 (I2.w.shift hi), (L2.keepW hP3 z3.2).trans I2.ones⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.lowBitsAt_ok hP J3.b.l.st.lay hγ cl hw3.1) fun s4 ⟨hP4, hcs4, hq4⟩ => ?_)
  rw [hw3.2] at hq4
  have L3 := J3.b.l.st.lay
  have J4 : VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t (i + 1) s4 := ⟨J3.b.step hP4 z4.1.1.1, Fam.keep L3 hP4 z4.1.1.2 J3.z,
    Fam.keep L3 hP4 z4.1.2 J3.w', Fam.keep L3 hP4 y4 J3.w, (L3.keepW hP4 z4.2).trans J3.ones⟩
  have e15 : s4.gpr .x24 = s.gpr .x24 := by
    rw [hcs4, hcs3, hcs2, hcs1]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.normAt_okB hP J4.b.l.st.lay hB cn (by rw [hP4.pa (by decide)]; exact hq4.1) (e15.trans h15))
    fun s5 ⟨hP5, h5⟩ => ?_
  have L4 := J4.b.l.st.lay
  refine ⟨⟨J4.b.step hP5 z5.1.1.1, Fam.keep L4 hP5 z5.1.1.2 J4.z, Fam.keep L4 hP5 z5.1.2 J4.w',
    Fam.keep L4 hP5 y5 J4.w, (L4.keepW hP5 z5.2).trans J4.ones⟩, ?_⟩
  rw [h5, hP4.pa (by decide), hq4.2]
  exact VG.Proof.MlDsa.AArch64.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
    fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## Hints and their 1s -/

theorem zq_sub_add (a b : Zq) : a - (a + b) = -b := by
  apply Fin.ext
  have ha := a.isLt; have hb := b.isLt
  simp only [Fin.sub_def, Fin.add_def, Fin.neg_def, q] at *
  omega

theorem sub_add_neg (a b : VG.Spec.MlDsa.Poly) : VG.Spec.MlDsa.sub a (VG.Spec.MlDsa.add a b) = neg b := by
  apply Vector.ext
  intro j hj
  simp only [VG.Spec.MlDsa.sub, VG.Spec.MlDsa.add, neg, Vector.getElem_zipWith, Vector.getElem_map, VG.Proof.MlDsa.AArch64.Sign.zq_sub_add]

theorem hintIs_congr {m m' : Mem} {a : Addr} {h : List (Vector Bool n)}
    (hb : ∀ k < 1024, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) (H : HintIs m a 1 h) :
    HintIs m' a 1 h :=
  ⟨H.1, fun i hi j hj => by
    have hn : n = 256 := rfl
    rw [coeffAt_congr₂ hb (show 256 * i + j < 256 by omega)]; exact H.2 i hi j hj⟩

/-- The hints of the first `m` slots from `b`. -/
def HFam (s : State) (b m : Nat) (f : Nat → Vector Bool n) : Prop :=
  ∀ j < m, HintIs s.mem (VG.Proof.MlDsa.AArch64.pa s (pS (b + j))) 1 [f j]

theorem HFam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Vector Bool n}
    (hc : VG.Proof.MlDsa.AArch64.Sign.famChk rbs wbs ws b m = true) (h : VG.Proof.MlDsa.AArch64.Sign.HFam s b m f) : VG.Proof.MlDsa.AArch64.Sign.HFam s' b m f := fun j hj => by
  have hk := VG.Proof.MlDsa.AArch64.Sign.famChk_one hc hj
  rw [hP.pa (L.keepBs hk)]
  exact VG.Proof.MlDsa.AArch64.Sign.hintIs_congr (VG.Proof.MlKem.bytes_frame hP.frame (L.fdisj hk) (by decide)) (h j hj)

theorem HFam.snoc {s : State} {b m : Nat} {f : Nat → Vector Bool n} (h : VG.Proof.MlDsa.AArch64.Sign.HFam s b m f)
    (h' : HintIs s.mem (VG.Proof.MlDsa.AArch64.pa s (pS (b + m))) 1 [f m]) : VG.Proof.MlDsa.AArch64.Sign.HFam s b (m + 1) f := fun j hj => by
  rcases (by omega : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

theorem hintOnes_le (h : Vector Bool n) : hintOnes [h] ≤ 256 := by
  rw [VG.Proof.MlDsa.Sign.hintOnes_single]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The sum of the 1s of the first `i` hints. -/
abbrev onesSum (f : Nat → Vector Bool n) (i : Nat) : Nat := ((List.range i).map fun j => hintOnes [f j]).sum

theorem onesSum_le (f : Nat → Vector Bool n) : ∀ i, VG.Proof.MlDsa.AArch64.Sign.onesSum f i ≤ 256 * i
  | 0 => by simp [VG.Proof.MlDsa.AArch64.Sign.onesSum]
  | i + 1 => by
    simp only [VG.Proof.MlDsa.AArch64.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    have := VG.Proof.MlDsa.AArch64.Sign.onesSum_le f i; have := VG.Proof.MlDsa.AArch64.Sign.hintOnes_le (f i)
    simp only [VG.Proof.MlDsa.AArch64.Sign.onesSum] at *
    omega

theorem onesSum_succ (f : Nat → Vector Bool n) (i : Nat) : VG.Proof.MlDsa.AArch64.Sign.onesSum f (i + 1) = VG.Proof.MlDsa.AArch64.Sign.onesSum f i + hintOnes [f i] := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.onesSum, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-! ## `ct₀` and the hint -/

/-- `r₀` passed. -/
abbrev R0Ok (p : Params) (σ : State) (κ : Nat) : Prop := ∀ j < p.k, normRq [VG.Proof.MlDsa.AArch64.Sign.R0v p σ κ j] < p.γ₂ - p.β

/-- The checks of `ct₀[j]` for `j < a`, where `w[j]` is `w[j] - cs₂[j] + ct₀[j]`, and the hints `h[j]` for
`j < c`, their 1s summed at `ONES`. -/
structure IHb (p : Params) (D : Nat) (σ : State) (t a c : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t))
  w'' : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p) a (VG.Proof.MlDsa.AArch64.Sign.W''v p σ (p.ℓ * t))
  w' : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p + a) (p.k - a) fun j => VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) (a + j)
  h : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 c (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t))
  ones : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oONES)) 64 = BitVec.ofNat 64 (VG.Proof.MlDsa.AArch64.Sign.onesSum (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) c)

def IH (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Sign.IHb p D σ t i i s ∧ s.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit ((VG.Proof.MlDsa.AArch64.Sign.ZOk p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.AArch64.Sign.R0Ok p σ (p.ℓ * t)) ∧
    ∀ j < i, normRq [VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) j] < p.γ₂)

def hfam (p : Params) (ws : List (Ptr × Nat)) (a c : Nat) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.kbChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p) a &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.wBase p + a) (p.k - a) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws 5 c

theorem IHb.step {p : Params} {D : Nat} {σ s s' : State} {t a c : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.IHb p D σ t a c s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.hfam p ws a c = true)
    (ho : keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (sc oONES) 8 = true) : VG.Proof.MlDsa.AArch64.Sign.IHb p D σ t a c s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hfam, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  have L := h.b.l.st.lay
  exact ⟨h.b.step hP h1, Fam.keep L hP h2 h.z, Fam.keep L hP h3 h.w'', Fam.keep L hP h4 h.w',
    HFam.keep L hP h5 h.h, (L.keepW hP ho).trans h.ones⟩

theorem ones32 {m : Mem} {a : Addr} {x : Nat} (h : m.readW a 64 = BitVec.ofNat 64 x) :
    (m.readW a 64).setWidth 32 = BitVec.ofNat 32 x := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- What `h[i]` needs of the layout. -/
def hChk2 (p : Params) (i : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(t3P, 1024)]
  let w2 : List (Ptr × Nat) := [(t3P, 1024), (sc oPS, 1024)]
  let w4 : List (Ptr × Nat) := [(t4P, 1024)]
  let w5 : List (Ptr × Nat) := [(wP p i, 1024)]
  let w7 : List (Ptr × Nat) := [(hP i, 1024)]
  let w8 : List (Ptr × Nat) := [(sc oONES, 8)]
  mulChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t3P cP (t0P p i) && VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t3P && VG.Proof.MlDsa.AArch64.Sign.normChk (VG.Proof.MlDsa.AArch64.Sign.sgB p) t3P &&
    VG.Proof.MlDsa.AArch64.Sign.copyChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t4P (wP p i) 1024 && accChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (wP p i) t3P &&
    accChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t4P (wP p i) && VG.Proof.MlDsa.AArch64.Sign.hintChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) t4P (wP p i) (hP i) &&
    VG.Proof.MlDsa.AArch64.Sign.hfam p w1 i i && VG.Proof.MlDsa.AArch64.Sign.hfam p w2 i i && VG.Proof.MlDsa.AArch64.Sign.hfam p [] i i && VG.Proof.MlDsa.AArch64.Sign.hfam p w4 i i &&
    (VG.Proof.MlDsa.AArch64.Sign.kbChk p w5 && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 5 i) &&
    VG.Proof.MlDsa.AArch64.Sign.hfam p w4 (i + 1) i && VG.Proof.MlDsa.AArch64.Sign.hfam p w7 (i + 1) i && VG.Proof.MlDsa.AArch64.Sign.hfam p w8 (i + 1) (i + 1) &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 (VG.Proof.MlDsa.AArch64.Sign.wBase p) i && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 (VG.Proof.MlDsa.AArch64.Sign.wBase p + (i + 1)) (p.k - (i + 1)) &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (sc oONES) 8 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w2 (sc oONES) 8 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (sc oONES) 8 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w4 (sc oONES) 8 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 (sc oONES) 8 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w7 (sc oONES) 8 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] t3P 1024 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w4 t3P 1024 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w5 t4P 1024 && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) w1 (t0P p i) 1024 &&
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oONES) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oONES) 8 &&
    decide (p.γ₂ < 2 ^ 32) && decide (p.γ₂ ∈ gamma2s) && decide (i < p.k) && decide (256 * p.k < 2 ^ 32)

theorem pa_sc {s s' : State} (h : s'.gpr .x28 = s.gpr .x28) (o : Nat) : VG.Proof.MlDsa.AArch64.pa s' (sc o) = VG.Proof.MlDsa.AArch64.pa s (sc o) := by
  simp only [VG.Proof.MlDsa.AArch64.pa, h]

theorem hR_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : VG.Proof.MlDsa.AArch64.Sign.hChk2 p i = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i s) : WP isa (VG.Impl.MlDsa.AArch64.Sign.hR P p i) s (VG.Proof.MlDsa.AArch64.Sign.IH p D σ t (i + 1)) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, f5a⟩, f5b⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩, o7⟩, t3⟩, t4⟩, u5⟩, v1⟩, i1⟩, i2⟩, hγ'⟩, hγ⟩, hi⟩, hk⟩ := hc
  obtain ⟨h, h15⟩ := h
  have L := h.b.l.st.lay
  have ht0 := h.b.l.k.d.t0 i hi
  unfold VG.Impl.MlDsa.AArch64.Sign.hR
  -- `ĉ t̂₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm h.b.c.1 ht0.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_)
  rw [h.b.c.2, ht0.2] at hq1
  have I1 := h.step hP1 g1 o1
  have b1 : s1.gpr .x28 = s.gpr .x28 := hP1.bs _ (by decide)
  -- `ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt I1.b.l.st.lay ci (by rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc b1]; exact hq1.1))
    fun s2 ⟨hP2, hcs2, hq2⟩ => ?_)
  rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc b1, hq1.2] at hq2
  have I2 := I1.step hP2 g2 o2
  have b2 : s2.gpr .x28 = s.gpr .x28 := (hP2.bs _ (by decide)).trans b1
  have q2 : VG.Proof.MlDsa.AArch64.Sign.Pl s2 3 (VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) i) := by show PolyIs _ _ _; rw [VG.Proof.MlDsa.AArch64.Sign.pa_sc b2]; exact hq2
  -- its norm
  have e2 : s2.gpr .x24 = s.gpr .x24 := by rw [hcs2, hcs1]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.normAt_okB hP I2.b.l.st.lay hγ' cn q2.1 (e2.trans h15)) fun s3 ⟨hP3, h3⟩ => ?_)
  rw [q2.2] at h3
  have I3 := I2.step hP3 g3 o3
  have q3 : VG.Proof.MlDsa.AArch64.Sign.Pl s3 3 (VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) i) := I2.b.l.st.lay.keepPoly hP3 t3 q2
  -- `T4 ← w[i] - cs₂[i]`
  have hw3 : VG.Proof.MlDsa.AArch64.Sign.Pl s3 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) := I3.w' 0 (by omega)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_ok I3.b.l.st.lay cc) fun s4 ⟨hP4, hcs4, hb4⟩ => ?_)
  have I4 := I3.step hP4 g4 o4
  have q4 : VG.Proof.MlDsa.AArch64.Sign.Pl s4 3 (VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) i) := I3.b.l.st.lay.keepPoly hP4 t4 q3
  have r4 : VG.Proof.MlDsa.AArch64.Sign.Pl s4 4 (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP4.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 4)]; exact polyIs_of_bytes hb4 hw3
  have hw4 : VG.Proof.MlDsa.AArch64.Sign.Pl s4 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) := I4.w' 0 (by omega)
  -- `w[i] ← w[i] - cs₂[i] + ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_ok hP I4.b.l.st.lay ca hw4.1 q4.1) fun s5 ⟨hP5, hcs5, hq5⟩ => ?_)
  rw [hw4.2, q4.2] at hq5
  have L4 := I4.b.l.st.lay
  have hw5 : VG.Proof.MlDsa.AArch64.Sign.Pl s5 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.W''v p σ (p.ℓ * t) i) := by
    show PolyIs _ _ _; rw [hP5.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq5
  have J5 : VG.Proof.MlDsa.AArch64.Sign.IHb p D σ t (i + 1) i s5 := ⟨I4.b.step hP5 g5.1.1, Fam.keep L4 hP5 g5.1.2 I4.z,
    Fam.snoc (Fam.keep L4 hP5 f5a I4.w'') hw5, Fam.keep L4 hP5 f5b (I4.w'.shift hi), HFam.keep L4 hP5 g5.2 I4.h,
    (L4.keepW hP5 o5).trans I4.ones⟩
  have r5 : VG.Proof.MlDsa.AArch64.Sign.Pl s5 4 (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) := L4.keepPoly hP5 u5 r4
  -- `T4 ← -ct₀[i]`
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_ok hP J5.b.l.st.lay cs r5.1 hw5.1) fun s6 ⟨hP6, hcs6, hq6⟩ => ?_)
  rw [r5.2, hw5.2, show VG.Proof.MlDsa.AArch64.Sign.W''v p σ (p.ℓ * t) i = VG.Spec.MlDsa.add (VG.Proof.MlDsa.AArch64.Sign.W'v p σ (p.ℓ * t) i) (VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) i) from rfl,
    VG.Proof.MlDsa.AArch64.Sign.sub_add_neg] at hq6
  have J6 := J5.step hP6 g6 o4
  have r6 : VG.Proof.MlDsa.AArch64.Sign.Pl s6 4 (neg (VG.Proof.MlDsa.AArch64.Sign.CT0v p σ (p.ℓ * t) i)) := by show PolyIs _ _ _; rw [hP6.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 4)]; exact hq6
  have hw6 : VG.Proof.MlDsa.AArch64.Sign.Pl s6 (VG.Proof.MlDsa.AArch64.Sign.wBase p + i) (VG.Proof.MlDsa.AArch64.Sign.W''v p σ (p.ℓ * t) i) := J6.w'' i (by omega)
  -- the hint
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.hintCall_ok hP J6.b.l.st.lay hγ ch r6.1 hw6.1) fun s7 ⟨hP7, hcs7, hq7, he7⟩ => ?_)
  rw [r6.2, hw6.2] at hq7 he7
  have J7 := J6.step hP7 g7 o7
  have hh7 : VG.Proof.MlDsa.AArch64.Sign.HFam s7 5 (i + 1) (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) :=
    HFam.snoc J7.h (by rw [hP7.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq7)
  -- `ONES`
  have ho7 : (s7.mem.readW (VG.Proof.MlDsa.AArch64.pa s7 (sc oONES)) 64).setWidth 32 = BitVec.ofNat 32 (VG.Proof.MlDsa.AArch64.Sign.onesSum (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) i) := VG.Proof.MlDsa.AArch64.Sign.ones32 J7.ones
  have L7 := J7.b.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.onesAdd_ok s7 (L7.inR i1) (L7.inW i2)) fun s8 ⟨hm8, k8⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.AArch64.pa s7 (sc oONES), 8⟩] s7.mem s8.mem := by
    rw [hm8]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP8 : PostB D s7 s8 _ := postB_of_keep k8 (by decide) hf
  have hcs8 : s8.gpr .x24 = s7.gpr .x24 := k8.get .x24
  have hP8' : PPostB D s7 s8 [(sc oONES, 8)] := hP8
  simp only [VG.Proof.MlDsa.AArch64.Sign.hfam, Bool.and_eq_true] at g8
  have hS := VG.Proof.MlDsa.AArch64.Sign.onesSum_le (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) i
  have hS1 := VG.Proof.MlDsa.AArch64.Sign.hintOnes_le (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t) i)
  have hik : 256 * (i + 1) ≤ 256 * p.k := Nat.mul_le_mul_left _ hi
  refine ⟨⟨J7.b.step hP8' g8.1.1.1.1, Fam.keep L7 hP8' g8.1.1.1.2 J7.z, Fam.keep L7 hP8' g8.1.1.2 J7.w'',
    Fam.keep L7 hP8' g8.1.2 J7.w', HFam.keep L7 hP8' g8.2 hh7, ?_⟩, ?_⟩
  · rw [hP8'.pa (VG.Proof.MlDsa.AArch64.Sign.sc_bases _), hm8, Mem.readW_writeW_self64, ho7, VG.Proof.MlDsa.AArch64.Sign.onesSum_succ]
    have he7' : ((s7.gpr .x0).setWidth 32).toNat = hintOnes [VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t) i] := he7
    have ea : (s7.gpr .x0).setWidth 32 = BitVec.ofNat 32 (hintOnes [VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t) i]) := by
      apply BitVec.eq_of_toNat_eq; rw [he7', BitVec.toNat_ofNat]; omega
    have hlt : VG.Proof.MlDsa.AArch64.Sign.onesSum (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) i + hintOnes [VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t) i] < 2 ^ 32 := by omega
    rw [ea, ← BitVec.ofNat_add, VG.Proof.MlDsa.AArch64.Sign.sw_ofNat hlt]
  · have e8 : s8.gpr .x24 = s3.gpr .x24 := by
      rw [hcs8, hcs7, hcs6, hcs5, hcs4]
    rw [e8, h3]
    exact VG.Proof.MlDsa.AArch64.Sign.bit_congr ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, forall_lt_succ.mp ⟨b, c⟩⟩,
      fun ⟨a, b⟩ => ⟨⟨a, (forall_lt_succ.mpr b).1⟩, (forall_lt_succ.mpr b).2⟩⟩

/-! ## `ω` -/

theorem sign_bit {S w : Nat} (hS : S < 2 ^ 32) (hw : w < 2 ^ 31) :
    ((BitVec.ofNat 64 S - BitVec.ofNat 64 w) >>> 63).setWidth 32 = if S < w then 1 else 0 := by
  by_cases h : S < w
  · rw [ifp h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · rw [ifn h]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow, show (0 : BitVec 32).toNat = 0 from rfl]
    omega

/-! ## The checks -/

/-- Iteration `t` after `SampleInBall` succeeded. -/
structure KA (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t p.k s
  ct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)
  cc : VG.Proof.MlDsa.AArch64.Sign.Pl s 0 (toRq (VG.Proof.MlDsa.AArch64.Sign.cV p σ (p.ℓ * t)))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome

/-- Iteration `t` passed: `c̃`, `z` and `h`, and `CNT = 1`. -/
structure EP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  ct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t))
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome
  pass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 1
  cnt : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t

/-- Iteration `t` was rejected: `κ = ℓ(t + 1)`, `CNT = 814 - t`. -/
structure EF (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  kap : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * (t + 1))
  cnt : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  some : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome
  fail : ¬ VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t)
  x24 : s.gpr .x24 = 0
  t_lt : t < 814
  rej : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t

/-- What the checks need of the layout. -/
def ksChk (p : Params) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) cP && VG.Proof.MlDsa.AArch64.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oONES) 8 &&
    VG.Proof.MlDsa.AArch64.Sign.kbChk p [(sc oONES, 8)] && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oONES, 8)] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oONES, 8)] (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k &&
    (List.range p.ℓ).all (VG.Proof.MlDsa.AArch64.Sign.zChk p) && (List.range p.k).all (VG.Proof.MlDsa.AArch64.Sign.rChk p) && (List.range p.k).all (VG.Proof.MlDsa.AArch64.Sign.hChk2 p) &&
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oONES) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oCNT) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oKAP) 8 &&
    VG.Proof.MlDsa.AArch64.Sign.kbChk p [] &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] 5 p.k &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] 5 p.k &&
    VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oCNT, 8)] && VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oKAP, 8)] && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oKAP, 8)] (sc oCNT) 8 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) && decide (p.ω + 1 < 4096) && decide (p.ℓ < 4096) &&
    decide (256 * p.k < 2 ^ 32) && decide (0 < p.ℓ) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oKAP) 8

theorem bit_ne {a : Prop} [Decidable a] : (VG.Proof.MlDsa.AArch64.Sign.bit a).setWidth 32 ≠ 0 ↔ a := by
  by_cases ha : a
  · rw [show VG.Proof.MlDsa.AArch64.Sign.bit a = 1 from ifp ha _ _]; exact ⟨fun _ => ha, fun _ => by decide⟩
  · rw [show VG.Proof.MlDsa.AArch64.Sign.bit a = 0 from ifn ha _ _]; exact ⟨fun h => absurd rfl h, fun h => absurd h ha⟩

theorem bit_and' {a b : Prop} [Decidable a] [Decidable b] :
    BitVec.setWidth 64 ((VG.Proof.MlDsa.AArch64.Sign.bit a).setWidth 32 &&& (if b then (1 : BitVec 32) else 0)) = VG.Proof.MlDsa.AArch64.Sign.bit (a ∧ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [VG.Proof.MlDsa.AArch64.Sign.bit, ha, hb]

theorem passV_iff {p : Params} {σ : State} {κ : Nat} :
    (((VG.Proof.MlDsa.AArch64.Sign.ZOk p σ κ ∧ VG.Proof.MlDsa.AArch64.Sign.R0Ok p σ κ) ∧ ∀ j < p.k, normRq [VG.Proof.MlDsa.AArch64.Sign.CT0v p σ κ j] < p.γ₂) ∧ VG.Proof.MlDsa.AArch64.Sign.onesSum (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ) p.k < p.ω + 1) ↔
      VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ :=
  ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, Nat.le_of_lt_succ d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, Nat.lt_succ_of_le d⟩⟩

theorem ksChk_spec {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) : ∀ {Q : Prop}, (VG.Proof.MlDsa.AArch64.Sign.ipChkS (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) cP = true →
    VG.Proof.MlDsa.AArch64.Sign.icwChk p [(cP, 1024), (sc oPS, 1024)] p.k = true →
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(cP, 1024), (sc oPS, 1024)] (sc oCT) (cLen p) = true → VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oONES) 8 = true →
    VG.Proof.MlDsa.AArch64.Sign.kbChk p [(sc oONES, 8)] = true → VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oONES, 8)] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oONES, 8)] (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k = true →
    (∀ r < p.ℓ, VG.Proof.MlDsa.AArch64.Sign.zChk p r = true) → (∀ i < p.k, VG.Proof.MlDsa.AArch64.Sign.rChk p i = true) → (∀ i < p.k, VG.Proof.MlDsa.AArch64.Sign.hChk2 p i = true) →
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oONES) 8 = true → VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oCNT) 8 = true → VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oKAP) 8 = true →
    VG.Proof.MlDsa.AArch64.Sign.kbChk p [] = true → VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] 5 p.k = true → VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ = true →
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] 5 p.k = true → VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oCNT, 8)] = true → VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oKAP, 8)] = true →
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oKAP, 8)] (sc oCNT) 8 = true → keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) = true →
    p.ω + 1 < 4096 → p.ℓ < 4096 → 256 * p.k < 2 ^ 32 → 0 < p.ℓ → VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k = true →
    VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oKAP) 8 = true → Q) → Q := by
  intro Q k
  simp only [VG.Proof.MlDsa.AArch64.Sign.ksChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, hz⟩, hr⟩, hh⟩, c8⟩, c9⟩, c10⟩, c13⟩, c14⟩, c15⟩, c16⟩, c17⟩, c18⟩, c19⟩, c20⟩, c21⟩, hω⟩, hl⟩, hk⟩, hl0⟩, c22⟩, c23⟩ := hc
  exact k c1 c2 c3 c4 c5 c6 c7 hz hr hh c8 c9 c10 c13 c14 c15 c16 c17 c18 c19 c20 c21 hω hl hk hl0 c22 c23

/-- The checks, after `ĉ = NTT(c)`. -/
structure KN (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s
  y : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Yv p σ (p.ℓ * t))
  w : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.wBase p) p.k (VG.Proof.MlDsa.AArch64.Sign.Wv p σ (p.ℓ * t))

theorem cntt_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.KA p D σ t s) : WP isa (nttAt P cP) s (VG.Proof.MlDsa.AArch64.Sign.KN p D σ t) := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun c1 c2 c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  have L := h.c.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.ntt L c1 h.cc.1) fun s1 ⟨hP1, hcs1, hq1⟩ => ?_
  rw [h.cc.2] at hq1
  have I1 := h.c.step hP1 c2
  exact ⟨⟨I1.l, by rw [L.keepBytes hP1 c3, h.ct], by
    show PolyIs _ _ _; rw [hP1.pa (by decide)]; exact hq1, h.some⟩, I1.y, I1.w⟩

/-- `x24 ← 1`, `ONES ← 0`. -/
abbrev kInit : List Instr := [.movz .x .x24 1 0] ++ setQ (sc oONES) 0

theorem kInit_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.KN p D σ t s) : WP isa (.block VG.Proof.MlDsa.AArch64.Sign.kInit) s (VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t 0) := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun _ _ _ c4 c5 c6 c7 _ _ _ _ _ _ c13 _ _ c16 _ _ _ _ _ _ _ _ _ c22 _ => ?_
  have L1 := h.b.l.st.lay
  rw [WP.block_append_iff]
  refine wp_movz fun s2 k2 h152 => wp_nil ?_
  have hP2 : PPostB D s s2 [] := VG.Proof.MlDsa.AArch64.Sign.postB24 k2 _
  have B2 := h.b.step hP2 c13
  have L2 := B2.l.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setQ_ok L2 (by decide) (by decide) c4 (by decide)) fun s3 ⟨hP3, hcs3, hm3⟩ => ?_
  have y3 := Fam.keep L2 hP3 c6 (Fam.keep L1 hP2 c16 h.y)
  exact ⟨⟨B2.step hP3 c5, fun _ h => absurd h (Nat.not_lt_zero _), y3.zero,
    Fam.keep L2 hP3 c7 (Fam.keep L1 hP2 c22 h.w), by rw [hP3.pa (by decide), hm3, Mem.readW_writeW_self64]; rfl⟩,
    by rw [hcs3.get .x24, h152]; exact (bit_one.mpr fun _ h => absurd h (Nat.not_lt_zero _)).symm⟩

theorem IZ.ir {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t p.ℓ s) : VG.Proof.MlDsa.AArch64.Sign.IR p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w.zero, h.1.ones⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.AArch64.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

theorem IR.ih {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IR p D σ t p.k s) : VG.Proof.MlDsa.AArch64.Sign.IH p D σ t 0 s :=
  ⟨⟨h.1.b, h.1.z, fun _ h => absurd h (Nat.not_lt_zero _), h.1.w'.zero, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h.1.ones]; rfl⟩,
    by rw [h.2]; exact VG.Proof.MlDsa.AArch64.Sign.bit_congr ⟨fun h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩, fun h => h.1⟩⟩

/-- The checks done: whether the iteration passes in `x24`. -/
structure KO (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  b : VG.Proof.MlDsa.AArch64.Sign.KB p D σ t s
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t))
  h : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t))
  x24 : s.gpr .x24 = VG.Proof.MlDsa.AArch64.Sign.bit (VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t))

theorem onesOk_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.IH p D σ t p.k s) : WP isa (.block (onesOk p)) s (VG.Proof.MlDsa.AArch64.Sign.KO p D σ t) := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ c8 _ _ c13 _ _ c16 c17 _ _ _ _ hω _ hk _ _ _ => ?_
  obtain ⟨J6, h156⟩ := h
  have L6 := J6.b.l.st.lay
  have hS := VG.Proof.MlDsa.AArch64.Sign.onesSum_le (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t)) p.k
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.onesOk_run p hω s (L6.inR c8)) fun s7 ⟨⟨h157, hm7⟩, k7⟩ => ?_
  rw [J6.ones, VG.Proof.MlDsa.AArch64.Sign.sign_bit (by omega) (by omega), h156, VG.Proof.MlDsa.AArch64.Sign.bit_and', VG.Proof.MlDsa.AArch64.Sign.bit_congr VG.Proof.MlDsa.AArch64.Sign.passV_iff] at h157
  have hP7 : PPostB D s s7 [] := postB_of_keep k7 (by decide) (by rw [hm7]; exact Frame.refl _ _)
  exact ⟨J6.b.step hP7 c13, Fam.keep L6 hP7 c16 J6.z, HFam.keep L6 hP7 c17 J6.h, h157⟩

theorem kBranch_ok {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.KO p D σ t s) :
    WP isa (ifOkElse (.block (setQ (sc oCNT) 1)) (.block (kapAdd p))) s fun s' => VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ _ _ _ _ c9 c10 _ c14 c15 _ _ c18 c19 c20 c21 _ hl _ _ _ c23 => ?_
  have B7 := h.b
  have L7 := B7.l.st.lay
  refine VG.Proof.MlDsa.AArch64.Sign.ifOkElse_ok (fun hne => ?_) fun he => ?_
  · rw [h.x24] at hne
    have hpass := bit_ne.mp hne
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setQ_ok L7 (by decide) (by decide) c9 (by decide)) fun s9 ⟨hP9, hcs9, hm9⟩ => ?_
    exact .inl ⟨B7.l.k.step hP9 c18, by rw [L7.keepBytes hP9 c21, B7.ct],
      Fam.keep L7 hP9 c14 h.z, HFam.keep L7 hP9 c15 h.h, B7.some,
      hpass, by rw [hcs9.get .x24, h.x24]; exact bit_one.mpr hpass,
      by rw [hP9.pa (by decide), hm9, Mem.readW_writeW_self64]; rfl, B7.l.t_lt, B7.l.rej⟩
  · rw [h.x24] at he
    have hfail : ¬ VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t) := fun hp => (bit_ne.mpr hp) he
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.kapAdd_ok p hl s (L7.inW c10) (L7.inR c23)) fun s9 ⟨hm9, k9⟩ => ?_
    have hf : Frame [⟨VG.Proof.MlDsa.AArch64.pa s (sc oKAP), 8⟩] s.mem s9.mem := by
      rw [hm9]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hP9' : PPostB D s s9 [(sc oKAP, 8)] := postB_of_keep k9 (by decide) hf
    refine .inr ⟨B7.l.k.step hP9' c19, ?_, by rw [L7.keepW hP9' c20, B7.l.cnt], B7.some, hfail,
      by rw [k9.get .x24, h.x24]; exact bit_zero.mpr hfail, B7.l.t_lt, B7.l.rej⟩
    rw [hP9'.pa (by decide), hm9, Mem.readW_writeW_self64, B7.l.kap, VG.Proof.MlDsa.AArch64.Sign.ofNat64_add, Nat.mul_succ]

theorem checks_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.KA p D σ t s) :
    WP isa (checks P p) s fun s' => VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s' ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s' := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun _ _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.cntt_ok hP hc h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.kInit_ok hc h1) fun s3 I3 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r) p.ℓ 0 (fun r _ hr s hs => VG.Proof.MlDsa.AArch64.Sign.zR_ok hP (hz r (by omega)) hs)
    s3 I3) fun s4 hs4 => ?_)
  rw [Nat.zero_add] at hs4
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.r0R_ok hP (hr i (by omega)) hs)
    s4 hs4.ir) fun s5 hs5 => ?_)
  rw [Nat.zero_add] at hs5
  refine WP.seq (WP.mono (seqR_ok (I := fun i => VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i) p.k 0 (fun i _ hi s hs => VG.Proof.MlDsa.AArch64.Sign.hR_ok hP (hh i (by omega)) hs)
    s5 hs5.ih) fun s6 hs6 => ?_)
  rw [Nat.zero_add] at hs6
  exact WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.onesOk_ok hc hs6) fun s7 h7 => VG.Proof.MlDsa.AArch64.Sign.kBranch_ok hc h7)

theorem ksChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem bChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.bChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL`. -/
section

/-!
# ML-DSA signing on AArch64: the rejection sampling loop

An iteration (`iter_ok`) either continues, with the next iteration's head
(`IL`), or ends the loop (`XS`): with `x24 = 1` when it passed, as
`signIteration` does within `maxBounds` after the iterations before were
rejected; with `x24 = 0` when `signLoop` returns nothing within `minBounds`
(its `SampleInBall` did not finish, or it was the 814th rejected). So the loop
(`signLoop_ok`) ends in `XS`.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_movz wp_nil)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem paramsOk {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : ParamsOk p := by
  rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

section
variable (p : Params) (σ : State)

/-- `signLoop`'s arguments for the function entered in `σ`: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, `μ`, `ρ″`. -/
abbrev loopF (b : Bounds) (n κ : Nat) : Option (List Byte × List VG.Spec.MlDsa.Poly × List (Vector Bool Spec.MlDsa.n)) :=
  signLoop p b (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) n κ

abbrev iterF (b : Bounds) (κ : Nat) : Option (List Byte × Option (List VG.Spec.MlDsa.Poly × List (Vector Bool Spec.MlDsa.n))) :=
  signIteration p b (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ

end

section
variable {p : Params} {σ : State} {κ : Nat}

theorem iterF_eq (hp : ParamsOk p) (b : Bounds) :
    VG.Proof.MlDsa.AArch64.Sign.iterF p σ b κ = (sampleInBall p.τ b.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).map fun c =>
      (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ, if passF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S1v p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ c then
        some ((List.range p.ℓ).map (zF p (VG.Proof.MlDsa.AArch64.Sign.S1v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ c),
          (List.range p.k).map (hF p (VG.Proof.MlDsa.AArch64.Sign.Am p σ) (VG.Proof.MlDsa.AArch64.Sign.S2v p σ) (VG.Proof.MlDsa.AArch64.Sign.T0v p σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) κ c)) else none) :=
  signIteration_eqF hp b _ _ _ _ _ _ κ

theorem cV_eq (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).isSome) :
    sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ) = some (VG.Proof.MlDsa.AArch64.Sign.cV p σ κ) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  simp only [VG.Proof.MlDsa.AArch64.Sign.cV, hc, Option.getD_some]

theorem iter_rej (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).isSome)
    (hf : ¬ VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ) : VG.Proof.MlDsa.AArch64.Sign.iterF p σ maxBounds κ = some (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ, none) := by
  rw [VG.Proof.MlDsa.AArch64.Sign.iterF_eq hp, VG.Proof.MlDsa.AArch64.Sign.cV_eq h, Option.map_some, ifn hf]

theorem iter_pass (hp : ParamsOk p) (h : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).isSome)
    (hf : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ) : VG.Proof.MlDsa.AArch64.Sign.iterF p σ maxBounds κ =
      some (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ, some ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ))) := by
  rw [VG.Proof.MlDsa.AArch64.Sign.iterF_eq hp, VG.Proof.MlDsa.AArch64.Sign.cV_eq h, Option.map_some, ifp hf]

theorem iter_none (h : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ) = none) : VG.Proof.MlDsa.AArch64.Sign.iterF p σ minBounds κ = none := by
  rw [VG.Proof.MlDsa.AArch64.Sign.iterF, signIteration_eq, signCommit_eq, h]; rfl

end

/-! ## The end of the loop -/

/-- The loop ended: in `x24`, whether an iteration passed (and its signature), or `signLoop` returns
nothing within `minBounds`. -/
structure XS (p : Params) (D : Nat) (σ : State) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  pass : s.gpr .x24 = 1 → ∃ t < 814, VG.Proof.MlDsa.AArch64.Sign.RejT p σ t ∧
    (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome ∧ VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t) ∧
    bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t) ∧ VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ (p.ℓ * t)) ∧
    VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ (p.ℓ * t))
  fail : s.gpr .x24 = 0 → VG.Proof.MlDsa.AArch64.Sign.loopF p σ minBounds minBounds.sign 0 = none

/-- `SampleInBall` did not finish within `minBounds`: `x24 = 0`, `CNT = 1`. -/
structure EB (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  none : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)) = none
  x24 : s.gpr .x24 = 0
  cnt : s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 = 1
  t_lt : t < 814
  rej : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t

theorem rej_zero {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t) :
    Rej p (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ))
      ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) maxBounds 0 t := h

theorem loop_none_ball {p : Params} {σ : State} {t : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t)
    (hn : sampleInBall p.τ minBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t)) = none) : VG.Proof.MlDsa.AArch64.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inr (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.AArch64.Sign.iter_none hn))

theorem loop_none_exh {p : Params} {σ : State} (h : VG.Proof.MlDsa.AArch64.Sign.RejT p σ 814) : VG.Proof.MlDsa.AArch64.Sign.loopF p σ minBounds minBounds.sign 0 = none :=
  signLoop_min_none p _ _ _ _ _ _ (by decide) h (.inl (by decide))

/-! ## An iteration -/

/-- After iteration `t`: the loop continues with iteration `t + 1` (`x9 ≠ 0`), or ends (`x9 = 0`). -/
def LP (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop :=
  (s.gpr .x9 ≠ 0 ∧ VG.Proof.MlDsa.AArch64.Sign.IL p D σ (t + 1) s) ∨ (s.gpr .x9 = 0 ∧ VG.Proof.MlDsa.AArch64.Sign.XS p D σ s)

/-- What the end of an iteration needs of the layout. -/
def lChk (p : Params) : Bool :=
  VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oCNT) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc oCNT) 8 && VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oCNT, 8)] && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (sc oKAP) 8 &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (sc oCT) (cLen p) && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ &&
    VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oCNT, 8)] 5 p.k && VG.Proof.MlDsa.AArch64.Sign.icwChk p [] p.k && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] (sc oCT) (cLen p) &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [] cP 1024 && VG.Proof.MlDsa.AArch64.Sign.ikChk p [] &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(sc oKAP, 8)] (sc oCNT) 8 && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgW p) (sc oKAP) 8 && VG.Proof.MlDsa.AArch64.Sign.ikChk p [(sc oKAP, 8)]

theorem lChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.lChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

theorem one_sub_one : (1 : BitVec 64) - BitVec.ofNat 64 1 = 0 := by decide

theorem dec_end {D : Nat} {p : Params} (hp : ParamsOk p) (hc : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s ∨ VG.Proof.MlDsa.AArch64.Sign.EB p D σ t s) : WP isa (.block cntDec) s (VG.Proof.MlDsa.AArch64.Sign.LP p D σ t) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, k1⟩, k2⟩, k3⟩, f1⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have hk : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s := by rcases h with h | h | h <;> exact h.k
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.AArch64.pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  have K := hk.step hP k1
  have e15 : s'.gpr .x24 = s.gpr .x24 := k.get .x24
  rcases h with h | h | h
  · -- passed
    rw [h.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one] at hz
    refine .inr ⟨hz, K, .inr (e15.trans h.x24), fun _ => ⟨t, h.t_lt, h.rej, h.some, h.pass,
      by rw [L.keepBytes hP k3, h.ct], Fam.keep L hP f1 h.z, HFam.keep L hP f2 h.h⟩,
      fun h0 => absurd (h0.symm.trans (e15.trans h.x24)) (by decide)⟩
  · -- rejected
    have hr : VG.Proof.MlDsa.AArch64.Sign.RejT p σ (t + 1) := Rej.succ _ _ _ _ _ _ _ h.rej (by rw [Nat.zero_add]; exact VG.Proof.MlDsa.AArch64.Sign.iter_rej hp h.some h.fail)
    rw [h.cnt, VG.Proof.MlDsa.AArch64.Sign.ofNat_sub_one h.t_lt] at hz
    by_cases ht : t = 813
    · subst ht
      refine .inr ⟨hz, K, .inl (e15.trans h.x24),
        fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => VG.Proof.MlDsa.AArch64.Sign.loop_none_exh hr⟩
    · refine .inl ⟨by
        have hne : (BitVec.ofNat 64 (814 - (t + 1))).toNat ≠ 0 := by
          have := h.t_lt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        rw [hz]; intro h0; rw [h0] at hne; exact hne rfl, K, by rw [L.keepW hP k2, h.kap], ?_, by have := h.t_lt; omega, hr⟩
      rw [hP.pa (by decide), hm, Mem.readW_writeW_self64, h.cnt, VG.Proof.MlDsa.AArch64.Sign.ofNat_sub_one h.t_lt]
  · -- `SampleInBall` failed
    rw [h.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one] at hz
    exact .inr ⟨hz, K, .inl (e15.trans h.x24),
      fun h1 => absurd (h1.symm.trans (e15.trans h.x24)) (by decide), fun _ => VG.Proof.MlDsa.AArch64.Sign.loop_none_ball h.rej h.none⟩

theorem IB.ka {D : Nat} {p : Params} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IB p D σ t s)
    (h1 : (s.gpr .x0).setWidth 32 = 1) : VG.Proof.MlDsa.AArch64.Sign.KA p D σ t s :=
  ⟨h.c, h.ct, (h.ok h1).1, (h.ok h1).2⟩

theorem else_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IB p D σ t s)
    (h0 : (s.gpr .x0).setWidth 32 = 0) :
    WP isa (.block (([.movz .x .x24 0 0] : List Instr) ++ setQ (sc oCNT) 1)) s (VG.Proof.MlDsa.AArch64.Sign.EB p D σ t) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.AArch64.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, k0⟩, -⟩, -⟩, -⟩ := hc4'
  rw [WP.block_append_iff]
  refine wp_movz fun s4 k4 h154 => wp_nil ?_
  have hP4 : PPostB D s s4 [] := VG.Proof.MlDsa.AArch64.Sign.postB24 k4 _
  have K4 := h.c.l.k.step hP4 k0
  have L4 := K4.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setQ_ok L4 (by decide) (by decide) w1 (by decide)) fun s5 ⟨hP5, hcs5, hm5⟩ => ?_
  exact ⟨K4.step hP5 k1, h.bad h0, by rw [hcs5.get .x24, h154]; rfl,
    by rw [hP5.pa (by decide), hm5, Mem.readW_writeW_self64]; rfl, h.c.l.t_lt, h.c.l.rej⟩

/-- What the end of an iteration keeps, for the proof that two runs leak the same. -/
theorem decF {D : Nat} {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {s : State} (hk : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) :
    WP isa (.block cntDec) s fun s' =>
      s'.gpr .x9 = s.mem.readW (VG.Proof.MlDsa.AArch64.pa s (sc oCNT)) 64 - BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' (sc oCT)) (cLen p) = bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) ∧
      ∀ f, VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.AArch64.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨VG.Proof.MlDsa.AArch64.pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  exact ⟨hz, k.get .x24, L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

theorem eval_w0 (s : State) : isa.eval (.nonzero .w .x0) s = some ((s.gpr .x0).setWidth 32 != 0) := rfl

theorem iter_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.AArch64.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.AArch64.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {t : Nat} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) : WP isa (iterWith keccak.callee P p) s (VG.Proof.MlDsa.AArch64.Sign.LP p D σ t) := by
  unfold iterWith
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.commit_ok hP hc1 h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.ball_ok hP hc2 h1) fun s3 I3 => ?_)
  refine WP.seq (WP.ite (M := isa) _ (VG.Proof.MlDsa.AArch64.Sign.eval_w0 s3) (fun hb => ?_) fun hb => ?_)
  · have h1 : (s3.gpr .x0).setWidth 32 = 1 := by
      rcases I3.r01 with e | e
      · rw [e] at hb; exact absurd hb (by decide)
      · exact e
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.checks_ok hP hc3 (I3.ka h1)) fun s' h' => VG.Proof.MlDsa.AArch64.Sign.dec_end hp hc4 (h'.elim .inl (fun h => .inr (.inl h)))
  · exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.else_ok hc4 I3 (by simpa using hb)) fun s' h' => VG.Proof.MlDsa.AArch64.Sign.dec_end hp hc4 (.inr (.inr h'))

/-! ## The loop -/

theorem loopInit_ok {D : Nat} {p : Params} (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) :
    WP isa (.block (setQ (sc oKAP) 0 ++ setQ (sc oCNT) 814)) s (VG.Proof.MlDsa.AArch64.Sign.IL p D σ 0) := by
  have hc4' := hc4
  simp only [VG.Proof.MlDsa.AArch64.Sign.lChk, Bool.and_eq_true] at hc4'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, -⟩, k1⟩, kk'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, wk⟩, ik⟩ := hc4'
  rw [WP.block_append_iff]
  have L := h.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setQ_ok L (by decide) (by decide) wk (by decide)) fun s1 ⟨hP1, _, hm1⟩ => ?_
  have K1 := h.step hP1 ik
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setQ_ok K1.d.im.st.lay (by decide) (by decide) w1 (by decide)) fun s2 ⟨hP2, _, hm2⟩ => ?_
  exact ⟨K1.step hP2 k1, by
      rw [K1.d.im.st.lay.keepW hP2 kk', hP1.pa (by decide), hm1, Mem.readW_writeW_self64]; rfl,
    by rw [hP2.pa (by decide), hm2, Mem.readW_writeW_self64], by decide, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem eval_x9 (s : State) : isa.eval (.nonzero .x .x9) s = some (s.gpr .x9 != 0) := rfl

theorem signLoop_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hp : ParamsOk p) (hc1 : VG.Proof.MlDsa.AArch64.Sign.cChk p = true)
    (hc2 : VG.Proof.MlDsa.AArch64.Sign.bChk p = true) (hc3 : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {σ : State} {s : State}
    (h : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) : WP isa (Impl.MlDsa.AArch64.Sign.signLoopWith keccak.callee P p) s (VG.Proof.MlDsa.AArch64.Sign.XS p D σ) := by
  unfold Impl.MlDsa.AArch64.Sign.signLoopWith
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.loopInit_ok hc4 h) fun s2 I0 => ?_)
  refine WP.loop (M := isa) (fun n s => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) (fun n s ⟨t, hn, hs⟩ => ?_) 814 s2
    ⟨0, rfl, I0⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.iter_ok hP hp hc1 hc2 hc3 hc4 hs) fun s' h' => ?_
  rcases h' with ⟨hz, hI⟩ | ⟨hz, hX⟩
  · exact .inr ⟨by rw [VG.Proof.MlDsa.AArch64.Sign.eval_x9]; simpa using hz, 814 - (t + 1), by have := hs.t_lt; omega, t + 1, rfl, hI⟩
  · exact .inl ⟨by rw [VG.Proof.MlDsa.AArch64.Sign.eval_x9, hz]; rfl, hX⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseO`. -/
section

/-!
# ML-DSA signing on AArch64: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`output_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : VG.Proof.MlDsa.AArch64.Sign.InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [VG.Proof.MlDsa.AArch64.Sign.coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = VG.Proof.MlDsa.AArch64.Sign.onesSum f k := by
  simp only [hintOnes, VG.Proof.MlDsa.AArch64.Sign.onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    VG.Proof.MlDsa.AArch64.pa s (pS (5 + i)) = VG.Proof.MlDsa.AArch64.pa s (Impl.MlDsa.AArch64.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show s.gpr .x28 + BitVec.ofNat 64 (oP (5 + i)) = s.gpr .x28 + BitVec.ofNat 64 (oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega]

theorem r14_bases (o : Nat) : ((.x23, o) : Ptr).1 ∈ keptRegs := by
  show Reg.x23 ∈ keptRegs; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => VG.Spec.MlDsa.bitPack ((VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s
  z : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ)
  h : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ)
  sig : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x23, 0)) (cLen p + zLen p * r) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ ++ VG.Proof.MlDsa.AArch64.Sign.zEnc p σ κ r
  x24 : s.gpr .x24 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.ikChk p ws && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ && VG.Proof.MlDsa.AArch64.Sign.famChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : VG.Proof.MlDsa.AArch64.Sign.ofam p ws = true)
    (hs : keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) ws (.x23, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .x24 = s.gpr .x24) :
    VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ r s' := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.x24⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.copyChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (.x23, 0) (sc oCT) (cLen p) && VG.Proof.MlDsa.AArch64.Sign.ofam p [((.x23, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (yP p r) 1024 (.x23, sigZ p r) (zLen p) &&
      VG.Proof.MlDsa.AArch64.Sign.ofam p [((.x23, sigZ p r), zLen p)] && keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [((.x23, sigZ p r), zLen p)] (.x23, 0) (cLen p + zLen p * r)) &&
    rwChk (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) (hP 0) (256 * p.k * 4) (.x23, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    VG.Proof.MlDsa.AArch64.Sign.ikChk p [((.x23, sigH p), p.ω + p.k)] &&
    keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [((.x23, sigH p), p.ω + p.k)] (.x23, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ, (List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ), (List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ)) (h15 : s.gpr .x24 = 1) :
    WP isa (copy (.x23, 0) (sc oCT) (cLen p)) s fun s1 =>
      VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ 0 s1 ∧ ∀ f, VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.AArch64.Sign.HFam s1 5 p.k f := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_ok L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [VG.Proof.MlDsa.AArch64.Sign.ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1, h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [VG.Proof.MlDsa.AArch64.Sign.zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ r s) (hpass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ (r + 1) s' ∧ ∀ f, VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.AArch64.Sign.HFam s' 5 p.k f := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.d.im.st.lay
  have hzr := h.z r hr
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.bpAt_ok hPO Lh hbp hzl c1 hzr.1 (VG.Proof.MlDsa.AArch64.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs')
  have c2' := c2
  simp only [VG.Proof.MlDsa.AArch64.Sign.ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.x24⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, VG.Proof.MlDsa.AArch64.Sign.pa_add, Nat.zero_add,
    hP'.pa (VG.Proof.MlDsa.AArch64.Sign.r14_bases _), hb', hzr.2, VG.Proof.MlDsa.AArch64.Sign.zEnc, VG.Proof.MlDsa.AArch64.Sign.zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ) :
    hintOnes (hintAt s.mem (VG.Proof.MlDsa.AArch64.pa s (Impl.MlDsa.AArch64.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [VG.Proof.MlDsa.AArch64.Sign.hintAt_of (f := VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [VG.Proof.MlDsa.AArch64.Sign.pS_hint] at this,
    VG.Proof.MlDsa.AArch64.Sign.hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ p.ℓ s) (hpass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.AArch64.Sign.hP 0) (256 * p.k) p.ω (.x23, sigH p) (p.ω + p.k)) s fun s' =>
      VG.Proof.MlDsa.AArch64.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' (.x23, 0)) p.sigLen = VG.Proof.MlDsa.AArch64.Sign.sigV p σ κ ∧ s'.gpr .x24 = 1 := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.d.im.st.lay
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.hbpAt_ok hPO L2 hhp ch (VG.Proof.MlDsa.AArch64.Sign.hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3, h2.x24]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), VG.Proof.MlDsa.AArch64.Sign.pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, VG.Proof.MlDsa.AArch64.Sign.hintAt_of (f := VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [VG.Proof.MlDsa.AArch64.Sign.pS_hint] at this]
  simp only [VG.Proof.MlDsa.AArch64.Sign.sigV, sigOf, sigEncode, VG.Proof.MlDsa.AArch64.Sign.zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) (hct : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)
    (hz : VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ)) (hh : VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ)) (hpass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ)
    (h15 : s.gpr .x24 = 1) :
    WP isa (output P p) s fun s' => VG.Proof.MlDsa.AArch64.Sign.IK p D σ s' ∧ bytesAt s'.mem (VG.Proof.MlDsa.AArch64.pa s' (.x23, 0)) p.sigLen = VG.Proof.MlDsa.AArch64.Sign.sigV p σ κ ∧
      s'.gpr .x24 = 1 := by
  unfold output
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (VG.Proof.MlDsa.AArch64.Sign.packZ_ok hPO hc (by omega) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact VG.Proof.MlDsa.AArch64.Sign.hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct`. -/
section

/-!
# ML-DSA signing on AArch64: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : VG.Proof.MlDsa.AArch64.Sign.seedE p σ (p.ℓ * i + j) = aSeed (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [VG.Proof.MlDsa.AArch64.Sign.seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e)).isSome) :
    expandA p maxBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← VG.Proof.MlDsa.AArch64.Sign.seedE_ij hj]; exact hok _ (VG.Proof.MlDsa.AArch64.Sign.ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (VG.Proof.MlDsa.AArch64.Sign.seedE p σ e) = none) :
    signMu p minBounds (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)))
    (hL : VG.Proof.MlDsa.AArch64.Sign.loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rndOf σ) = none := by
  cases e : expandA p minBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ) = some (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ))) {t : Nat}
    (ht : t < 814) (hr : VG.Proof.MlDsa.AArch64.Sign.RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ (p.ℓ * t))).isSome)
    (hpass : VG.Proof.MlDsa.AArch64.Sign.PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rndOf σ) = some (VG.Proof.MlDsa.AArch64.Sign.sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (VG.Proof.MlDsa.AArch64.Sign.iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `x24`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : VG.Proof.MlDsa.AArch64.Sign.St p D σ s
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  ok : s.gpr .x24 = 1 →
    signMu p maxBounds (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rndOf σ) = some (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x23, 0)) p.sigLen)
  bad : s.gpr .x24 = 0 → signMu p minBounds (VG.Proof.MlDsa.AArch64.Sign.skOf p σ) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  (List.range 7).all (fun k => VG.CallLay.inB (VG.Proof.MlDsa.AArch64.Sign.sgB p) (sc (oSV + 8 * k)) 8) &&
    decide (VG.Proof.MlDsa.AArch64.Sign.scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32 ∧ oSV + 56 ≤ VG.Proof.MlDsa.AArch64.Sign.scrLen p)

theorem fChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  VG.Proof.MlDsa.AArch64.Sign.aChk p && VG.Proof.MlDsa.AArch64.Sign.dChk p && VG.Proof.MlDsa.AArch64.Sign.cChk p && VG.Proof.MlDsa.AArch64.Sign.bChk p && VG.Proof.MlDsa.AArch64.Sign.ksChk p && VG.Proof.MlDsa.AArch64.Sign.lChk p && VG.Proof.MlDsa.AArch64.Sign.oChk p && VG.Proof.MlDsa.AArch64.Sign.fChk p

theorem allChk_ok {p : Params} (h : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) : VG.Proof.MlDsa.AArch64.Sign.allChk p = true := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.allChk, VG.Proof.MlDsa.AArch64.Sign.aChk_ok h, VG.Proof.MlDsa.AArch64.Sign.dChk_ok h, VG.Proof.MlDsa.AArch64.Sign.cChk_ok h, VG.Proof.MlDsa.AArch64.Sign.bChk_ok h, VG.Proof.MlDsa.AArch64.Sign.ksChk_ok h, VG.Proof.MlDsa.AArch64.Sign.lChk_ok h, VG.Proof.MlDsa.AArch64.Sign.oChk_ok h, VG.Proof.MlDsa.AArch64.Sign.fChk_ok h,
    Bool.and_self]

theorem x24_one {s : State} (h : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) (hne : (s.gpr .x24).setWidth 32 ≠ 0) :
    s.gpr .x24 = 1 := by
  rcases h with e | e
  · rw [e] at hne; exact absurd rfl hne
  · exact e

theorem x24_zero {s : State} (h : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) (he : (s.gpr .x24).setWidth 32 = 0) :
    s.gpr .x24 = 0 := by
  rcases h with e | e
  · exact e
  · rw [e] at he; exact absurd he (by decide)

theorem rest_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IM p D σ s) :
    WP isa (restWith keccak.callee P p) s (VG.Proof.MlDsa.AArch64.Sign.FS p D σ) := by
  have hc := VG.Proof.MlDsa.AArch64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, -⟩ := hc
  have hp := VG.Proof.MlDsa.AArch64.Sign.paramsOk h3
  have hA := VG.Proof.MlDsa.AArch64.Sign.expandA_max h.ok
  unfold restWith
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.decode_ok hP hd h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.signLoop_ok hP hp hc1 hb hks hl h1) fun s2 h2 => ?_)
  unfold ifOk
  refine VG.Proof.MlDsa.AArch64.Sign.ifOkElse_ok (fun hne => ?_) fun he => ?_
  · have h15 := VG.Proof.MlDsa.AArch64.Sign.x24_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.output_ok hP ho h2.k hct hz hh hpass h15)
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact VG.Proof.MlDsa.AArch64.Sign.signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := VG.Proof.MlDsa.AArch64.Sign.x24_zero h2.r01 he
    exact WP.block_nil ⟨h2.k.d.im.st, .inl h15, fun h1 => absurd (h1.symm.trans h15) (by decide),
      fun _ => VG.Proof.MlDsa.AArch64.Sign.signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨σ.gpr r, len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (b, 0)) len = bytesAt σ.mem (σ.gpr r) len := by
  rw [VG.Proof.MlDsa.AArch64.pa, hb, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {D : Nat} {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) {σ s : State}
    (hpre : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ) (ht : VG.Proof.MlDsa.AArch64.Sign.Top σ s)
    (hf : Frame [⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩] σ.mem s.mem) : VG.Proof.MlDsa.AArch64.Sign.St p D σ s := by
  have hc := VG.Proof.MlDsa.AArch64.Sign.fChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, h1, h2, h3', h4⟩ := hc
  have hsub : Region.Sub ⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩ ⟨σ.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩ := Offset.sub_base _ h4
  have hpre' := hpre
  obtain ⟨_, _, _, d2, _, d4, _, d6, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hpre'
  exact ⟨ht, VG.Proof.MlDsa.AArch64.Sign.sgLay hpre ⟨h1, h2, h3'⟩ ht,
    VG.Proof.MlDsa.AArch64.Sign.entry_bytes hf (d2.sub_right hsub) (by omega) (ht.regs (.x25, .x0) (by decide)),
    VG.Proof.MlDsa.AArch64.Sign.entry_bytes hf (d4.sub_right hsub) (by omega) (ht.regs (.x26, .x1) (by decide)),
    VG.Proof.MlDsa.AArch64.Sign.entry_bytes hf (d6.sub_right hsub) (by omega) (ht.regs (.x27, .x2) (by decide))⟩

/-- The prologue saves the registers in `scratch`. -/
theorem pro_in {D : Nat} {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) {σ : State} (hpre : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ) :
    ∀ k < 7, InRegions σ.wr (σ.gpr .x4 + BitVec.ofNat 64 (oSV + 8 * k)) 8 := by
  have hc := VG.Proof.MlDsa.AArch64.Sign.fChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, -, -, -, hsz⟩ := hc
  intro k hk
  exact ⟨⟨σ.gpr .x4, VG.Proof.MlDsa.AArch64.Sign.scrLen p⟩, by rw [hpre.2.1]; simp,
    Offset.contains_base _ (by omega) (by simp only [oSV]; omega)⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (σ : State)
    (hpre : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.AArch64.Sign.signWith keccak.callee P p) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlDsa.AArch64.Sign.signK p D).post σ s' := by
  have hc := VG.Proof.MlDsa.AArch64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [VG.Proof.MlDsa.AArch64.Sign.fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨hsv, -⟩ := hf'
  have hin := VG.Proof.MlDsa.AArch64.Sign.pro_in h3 hpre
  have main : WP isa (Impl.MlDsa.AArch64.Sign.signWith keccak.callee P p) σ fun s₅ => abiPreserved σ s₅ ∧
      ∃ s₄, VG.Proof.MlDsa.AArch64.Sign.FS p D σ s₄ ∧ s₅.gpr .x0 = s₄.gpr .x24 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.AArch64.Sign.signWith
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.pro_ok hin) fun s₁ ⟨h₁, h15, hf₁⟩ => ?_)
    have S1 := VG.Proof.MlDsa.AArch64.Sign.entry_st h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.expandA_ok hP h3 ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (restWith keccak.callee P p)) s₂ (VG.Proof.MlDsa.AArch64.Sign.FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine VG.Proof.MlDsa.AArch64.Sign.ifOkElse_ok (fun hne => ?_) fun he => ?_
      · have h1 := VG.Proof.MlDsa.AArch64.Sign.x24_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact VG.Proof.MlDsa.AArch64.Sign.rest_ok hP h3 ⟨h₂.st, ok, fam⟩
      · have h0 := VG.Proof.MlDsa.AArch64.Sign.x24_zero h₂.r01 he
        exact WP.block_nil ⟨h₂.st, .inl h0, fun h1 => absurd (h1.symm.trans h0) (by decide),
          fun _ => VG.Proof.MlDsa.AArch64.Sign.signMu_min_A (h₂.bad h0)⟩
    · exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.epi_ok h₄.st.top fun k hk => h₄.st.lay.inR (hsv k hk)) fun s₅ ⟨hg, hr, hm⟩ =>
        ⟨hg, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, hg, ?_⟩
  have e23 : VG.Proof.MlDsa.AArch64.pa s₄ (.x23, 0) = σ.gpr .x3 := by
    rw [VG.Proof.MlDsa.AArch64.pa, h₄.st.top.regs (.x23, .x3) (by decide), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0]; rfl, h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1]; rfl, maxBounds, by rw [hm, ← e23]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT`. -/
section

/-!
# ML-DSA signing on AArch64: decoding leaks only the pointers

Each call while decoding leaks only its pointers, given that its input
polynomial is reduced (`dec_tr`); so two runs agree on what decoding leaks
(`decode_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A piece that leaks only its pointers, from runs in the layout. -/
theorem liftT {p : Params} {D : Nat} {E I J : State → State → Prop} {c : Prog isa}
    (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.Sign.St p D σ s) (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s (J σ))
    (ht : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p)) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E I) c (VG.Proof.MlDsa.AArch64.Sign.RS p D E J) :=
  VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun _ => True) (fun σ s h => ⟨hI σ s h, trivial⟩) hw (RelCT.mono ht (fun _ _ h => h.1) fun _ _ h => h)

theorem dec_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {a b c : Nat} {src : Ptr} {len x y j : Nat}
    (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y)) (hc : VG.Proof.MlDsa.AArch64.Sign.decChk p a b c src len j = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p)) (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hc
  refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.seqL (p := p) (I := fun _ => True) (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (pS j)))
    (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.bupAt_tr hP hp hl h1) (fun _ _ h => h.1) fun _ _ h => h)
    (fun s L _ => WP.mono (VG.Proof.MlDsa.AArch64.Sign.bupAt_ok hP L hp hl h1) fun s' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩)
    (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt h2)) (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem decode_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.dChk p = true) {E : State → State → Prop} :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IM p D)) (decodeWith keccak.callee P p) (VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IK p D)) := by
  have hs := VG.Proof.MlDsa.AArch64.Sign.dChk_spec hc
  unfold decodeWith
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ 0 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k p.k s) ?_ ?_))
  · refine RelCT.mono (seqR_tr (Q := fun r => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ r 0 0 s) p.ℓ 0 fun r _ hr =>
      VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.decS1_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.AArch64.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.AArch64.Sign.sLen_eq p) (hs.1 r (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
            fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ i 0 s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.decS2_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.AArch64.Sign.dec_tr hP hs.2.2.2.2.2.2.1 (VG.Proof.MlDsa.AArch64.Sign.sLen_eq p) (hs.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · refine RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ID p D σ p.ℓ p.k i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.decT0_ok hP hc (by omega) h)
        (VG.Proof.MlDsa.AArch64.Sign.dec_tr hP (by decide) (by decide) (hs.2.2.1 i (by omega)).1)) (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
          ⟨h.im, h.s1, h.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x y h => by rwa [Nat.zero_add] at h
  · exact VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.im.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.rpp_ok hP hc h)
      (VG.Proof.MlDsa.AArch64.Sign.vector_lrel_tr (fun _ _ h => h) keccak.mldsaSignDecodeTaint.choose_spec)

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT`. -/
section

/-!
# ML-DSA signing on AArch64: the commitment leaks only the pointers

Each piece of the commitment leaks only its pointers, given that its inputs
are reduced (and the coefficients of `HighBits(w[i])` bounded): `maskR_trL`,
`rowW_trL`, `w1R_trL`; so two runs agree on what the commitment leaks
(`commit_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- A piece that keeps `I`, from runs in the layout that satisfy it. -/
theorem stepSelf {c : Prog isa} {I : State → Prop}
    (h : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y) c fun _ _ => True)
    (w : ∀ x, Lay D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x → I x → WP isa c x fun x' => (∃ W, PostB D x x' W) ∧ I x') :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y) c
      fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ I x ∧ I y :=
  RelCT.postDep h (F := fun x x' => (∃ W, PostB D x x' W) ∧ I x')
    (fun x y h => ⟨w x h.1.lx h.2.1, w y h.1.ly h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hx hy, jx, jy⟩

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r : Nat}
    (hr : r < 4096) (h1 : VG.CallLay.inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : VG.CallLay.inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65)) = VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)) + 1 := (VG.Proof.MlDsa.AArch64.Sign.pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 1 := by
    have := Offset.contains_base (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩ : Region).Contains (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64))) 1 := by
    have := VG.CallLay.inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact VG.CallLay.inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.setKappa_run r hr s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (postB_of_keep k (by decide)
    (W := [⟨VG.Proof.MlDsa.AArch64.pa s (sc (oMS + 64)), 2⟩]) ?_)⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

theorem maskR_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {r : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.mChk p r = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  unfold maskR
  refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1) (VG.Proof.MlDsa.AArch64.Sign.setKappa_taint r))
    (fun x L _ => WP.mono (VG.Proof.MlDsa.AArch64.Sign.setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (yP p r)))
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (VG.Proof.MlDsa.AArch64.Sign.maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩)
      (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (yhP p r)))
        (VG.Proof.MlDsa.AArch64.Sign.copy_tr (.inl rfl) rfl fun x y h => h.1)
        (fun x L hy => WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_ok L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
        (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.wChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨cm, ci⟩, c1⟩, _⟩, hl⟩ := hc
  have hA : ∀ {σ s : State} (I : VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) j, j < p.ℓ → Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (VG.Impl.MlDsa.AArch64.Sign.aP p i j)) :=
    fun I j hj => by
      have := I.l.k.d.im.A (p.ℓ * i + j) (by
        have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega)
      rw [VG.Proof.MlDsa.AArch64.Sign.aP_ij]; exact this.1
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (wP p i))
  unfold rowW
  refine VG.Proof.MlDsa.AArch64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.AArch64.Sign.seqL (J := J) ?_ ?_ ?_)
  · refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_tr hP.mul (cm 0 hl)) (fun x y ⟨R, ⟨σ₁, I₁⟩, ⟨σ₂, I₂⟩⟩ =>
      ⟨R, ⟨hA I₁ 0 hl, (I₁.yh 0 hl).1⟩, ⟨hA I₂ 0 hl, (I₂.yh 0 hl).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L (cm 0 hl) (hA I 0 hl) (I.yh 0 hl).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩
  · refine RelCT.mono (seqR_tr (Q := fun _ x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ J x ∧ J y) (p.ℓ - 1) 1
      fun j hj1 hj => VG.Proof.MlDsa.AArch64.Sign.stepSelf ?_ ?_) (fun _ _ h => h) fun _ _ _ => trivial
    · refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.mulAddAt_tr hP.mulAdd (cm j (by omega))) (fun x y ⟨R, ⟨⟨σ₁, I₁⟩, r₁⟩, ⟨⟨σ₂, I₂⟩, r₂⟩⟩ =>
        ⟨R, ⟨r₁, hA I₁ j (by omega), (I₁.yh j (by omega)).1⟩, ⟨r₂, hA I₂ j (by omega), (I₂.yh j (by omega)).1⟩⟩)
        fun _ _ h => h
    · rintro x L ⟨⟨σ, I⟩, r⟩
      refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAddAt_ok hP.mulAdd L (cm j (by omega)) r (hA I j (by omega)) (I.yh j (by omega)).1)
        fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩
  · rintro x L ⟨I, r⟩
    exact WP.mono (seqR_ok (I := fun _ s => ∃ W, PostB D x s W ∧ J s) (p.ℓ - 1) 1
      (fun j hj1 hj s ⟨W, hW, ⟨σ, I'⟩, r'⟩ => WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAddAt_ok hP.mulAdd I'.l.st.lay (cm j (by omega)) r'
        (hA I' j (by omega)) (I'.yh j (by omega)).1) fun x' ⟨hP', _, hq⟩ =>
          ⟨_, hW.trans hP' (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h),
            ⟨σ, I'.step hP' c1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩) x ⟨[], PostB.refl x [], I, r⟩)
      fun x' ⟨W, hW, j⟩ => ⟨⟨W, hW⟩, j⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun _ _ h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {t i : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (VG.Proof.MlDsa.AArch64.Sign.sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), VG.Proof.MlDsa.AArch64.Sign.natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (hc : VG.Proof.MlDsa.AArch64.Sign.cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t p.k s) :
    WP isa (shakeAtWith keccak.callee [⟨.x26, 0, 64⟩, ⟨.x28, oW1, p.k * w1Len p⟩] ⟨.x28, oCT, cLen p⟩) s (VG.Proof.MlDsa.AArch64.Sign.IC p D σ t) := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (shake_ok hP.s16 hP.s64 h.c.l.st.lay (by simp) hs) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  show H (bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (.x26, 0)) 64 ++ bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oW1)) (p.k * w1Len p)) (cLen p) = _
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [VG.Proof.MlDsa.AArch64.Sign.CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (hc : VG.Proof.MlDsa.AArch64.Sign.cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) (commitWith keccak.callee P p) (VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IC p D σ t s) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨hm, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commitWith
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t 0 s) ?_ (RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t p.k s) ?_ ?_))
  · refine RelCT.mono (seqR_tr (Q := fun r => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICm p D σ t r s) p.ℓ 0 fun r _ hr =>
      VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.l.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.maskR_ok hP (hm r (by omega)) h) (VG.Proof.MlDsa.AArch64.Sign.maskR_trL hP (hm r (by omega))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.rowW_ok hP (hw i (by omega)) (by omega) h) (VG.Proof.MlDsa.AArch64.Sign.rowW_trL hP (hw i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [VG.Proof.MlDsa.AArch64.Sign.w1Enc]; rfl⟩
  · refine RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i s) p.k 0 fun i _ hi =>
      VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.AArch64.Sign.ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.w1R_ok hP (hh i (by omega)) (by omega) h) (VG.Proof.MlDsa.AArch64.Sign.w1R_trL hP (hh i (by omega)) (by omega)))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · refine VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.ctShake_ok hP hc h) ?_
    obtain ⟨hint, hh⟩ := keccak.mldsaSignCommitTaint p h3
    exact VG.Proof.MlDsa.AArch64.Sign.vector_lrel_tr (fun _ _ h => h) hh

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT`. -/
section

/-!
# ML-DSA signing on AArch64: the checks leak only the pointers and whether they passed

Each check leaks only its pointers, given that its inputs are reduced
(`zR_trL`, `r0R_trL`, `hR_trL`); the branch on their result leaks whether the
iteration passed, which two runs agree on when they agree on what the
iteration leaks (`checks_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params}
include hP

theorem normAt_post {s : State} (L : Lay D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) s) {f : Ptr} {B : Nat} (hB : B < 2 ^ 32)
    (hc : VG.Proof.MlDsa.AArch64.Sign.normChk (VG.Proof.MlDsa.AArch64.Sign.sgB p) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s f)) :
    WP isa (normAt P f B) s fun s' => PPostB D s s' [] := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sign.normCall_ok hP L hB hc hr) fun s1 ⟨hP1, _, _⟩ => ?_)
  exact WP.mono (and24_ok s1) fun s2 ⟨k2, _⟩ => PPostB.trans hP1 (VG.Proof.MlDsa.AArch64.Sign.postB24 k2 _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)

theorem normAt_trL {f : Ptr} {B : Nat} (hB : B < 2 ^ 32) (hc : VG.Proof.MlDsa.AArch64.Sign.normChk (VG.Proof.MlDsa.AArch64.Sign.sgB p) f = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ Reduced x.mem (VG.Proof.MlDsa.AArch64.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.AArch64.pa y f)) (normAt P f B)
      fun _ _ => True :=
  VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun _ => True) (VG.Proof.MlDsa.AArch64.Sign.normCall_tr hP hc)
    (fun x L hr => WP.mono (VG.Proof.MlDsa.AArch64.Sign.normCall_ok hP L hB hc hr) fun _ h => ⟨⟨_, h.1⟩, trivial⟩)
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1) (by taint_decide))

/-! ## `z` -/

theorem zR_trL {t r : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.zChk p r = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r x) ∧ ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r y) (zR P p r)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.zChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩, hr⟩ := hc
  unfold zR
  refine VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IZb p D σ t r s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (yP p r))) ?_ ?_ (VG.Proof.MlDsa.AArch64.Sign.normAt_trL hP hB cn)))
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s1 r hr).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s1 r hr).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s1 r hr).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.y 0 (by omega)).1, r₁⟩, ⟨(I₂.y 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_ok hP L ca (I.y 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩

/-! ## `r₀` -/

theorem r0R_trL {t i : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.rChk p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i y) (r0R P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.rChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, ca⟩, cl⟩, cn⟩, z1⟩, z2⟩, _⟩, _⟩, _⟩, y1⟩, y2⟩, _⟩, _⟩, _⟩, _⟩, hB⟩,
    hγ⟩, hi⟩ := hc
  unfold r0R
  refine VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t1P)) ?_ ?_
    (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IRb p D σ t i s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t1P)) ?_ ?_
      (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t2P)) ?_ ?_ (VG.Proof.MlDsa.AArch64.Sign.normAt_trL hP hB cn))))
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.s2 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.s2 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.s2 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' z1 y1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' z2 y2⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 1)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_tr hP ca) (fun x y ⟨R, ⟨⟨_, I₁⟩, r₁⟩, ⟨⟨_, I₂⟩, r₂⟩⟩ =>
      ⟨R, ⟨(I₁.w 0 (by omega)).1, r₁⟩, ⟨(I₂.w 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_ok hP L ca (I.w 0 (by omega)).1 r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩
  · exact VG.Proof.MlDsa.AArch64.Sign.lowBitsAt_tr hP hγ cl
  · intro x L r1
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.lowBitsAt_ok hP L hγ cl r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 2)]; exact hq.1⟩

/-! ## `ct₀` and `h` -/

theorem hR_trL {t i : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.hChk2 p i = true) :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i x) ∧ ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i y) (VG.Impl.MlDsa.AArch64.Sign.hR P p i)
      fun _ _ => True := by
  simp only [VG.Proof.MlDsa.AArch64.Sign.hChk2, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cm, ci⟩, cn⟩, cc⟩, ca⟩, cs⟩, ch⟩, g1⟩, g2⟩, g3⟩, g4⟩, _⟩, g6⟩, _⟩, _⟩,
    _⟩, _⟩, o1⟩, o2⟩, o3⟩, o4⟩, _⟩, _⟩, t3⟩, t4⟩, u5⟩, _⟩, _⟩, _⟩, hγ'⟩, hγ⟩, hi⟩, _⟩ := hc
  have f6 : keepB (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) [(t4P, 1024)] (wP p i) 1024 = true := by
    simp only [VG.Proof.MlDsa.AArch64.Sign.hfam, Bool.and_eq_true] at g6
    exact VG.Proof.MlDsa.AArch64.Sign.famChk_one (b := VG.Proof.MlDsa.AArch64.Sign.wBase p) g6.1.1.2 (show i < i + 1 by omega)
  let J : State → Prop := fun s => (∃ σ, VG.Proof.MlDsa.AArch64.Sign.IHb p D σ t i i s) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t3P)
  unfold VG.Impl.MlDsa.AArch64.Sign.hR
  refine VG.Proof.MlDsa.AArch64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.AArch64.Sign.seqL (J := J) ?_ ?_ (VG.Proof.MlDsa.AArch64.Sign.seqL (J := J) ?_ ?_
    (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => J s ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t4P)) ?_ ?_
      (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (wP p i))) ?_ ?_
        (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s t4P) ∧ Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (wP p i))) ?_ ?_
          (VG.Proof.MlDsa.AArch64.Sign.seqL (J := fun _ => True) ?_ ?_ ?_))))))
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_tr hP.mul cm) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
      ⟨R, ⟨I₁.1.b.c.1, (I₁.1.b.l.k.d.t0 i hi).1⟩, ⟨I₂.1.b.c.1, (I₂.1.b.l.k.d.t0 i hi).1⟩⟩) fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.mulAt_ok hP.mul L cm I.1.b.c.1 (I.1.b.l.k.d.t0 i hi).1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.1.step hP' g1 o1⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt ci) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.invNtt L ci r1) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g2 o2⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 3)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.normAt_trL hP hγ' cn) (fun x y h => ⟨h.1, h.2.1.2, h.2.2.2⟩) fun _ _ h => h
  · rintro x L ⟨⟨σ, I⟩, r1⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.normAt_post hP L hγ' cn r1) fun x' hP' => ⟨⟨_, hP'⟩, ⟨σ, I.step hP' g3 o3⟩, L.keepRed hP' t3 r1⟩
  · exact VG.Proof.MlDsa.AArch64.Sign.copy_tr (.inl rfl) rfl fun x y h => h.1
  · rintro x L ⟨⟨σ, I⟩, r3⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.copy_ok L cc) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, ⟨⟨σ, I.step hP' g4 o4⟩, L.keepRed hP' t4 r3⟩,
      by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 4)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.w' 0 (by omega)).1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_tr hP ca) (fun x y ⟨R, ⟨⟨⟨_, I₁⟩, r₁⟩, _⟩, ⟨⟨⟨_, I₂⟩, r₂⟩, _⟩⟩ =>
      ⟨R, ⟨(I₁.w' 0 (by omega)).1, r₁⟩, ⟨(I₂.w' 0 (by omega)).1, r₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨⟨⟨σ, I⟩, r3⟩, r4⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.addAt_ok hP L ca (I.w' 0 (by omega)).1 r3) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, L.keepRed hP' u5 r4, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases _)]; exact hq.1⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_tr hP cs) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩) fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.subAt_ok hP L cs r4 rw) fun x' ⟨hP', _, hq⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (VG.Proof.MlDsa.AArch64.Sign.pS_bases 4)]; exact hq.1, L.keepRed hP' f6 rw⟩
  · exact RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.hintCall_tr hP hγ ch) (fun x y ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => ⟨R, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩)
      fun _ _ h => h
  · rintro x L ⟨r4, rw⟩
    exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.hintCall_ok hP L hγ ch r4 rw) fun x' ⟨hP', _, _⟩ => ⟨⟨_, hP'⟩, trivial⟩
  · exact VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1) (by taint_decide)

/-! ## The checks -/

omit hP in
theorem onesOk_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (.block (onesOk p)) (.block [])).isSome = true := by
  dsimp only [onesOk]; rfl

omit hP in
theorem kapAdd_taint (p : Params) :
    (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (.block (kapAdd p)) (.block [])).isSome = true := by
  dsimp only [kapAdd]; rfl

theorem checks_tr (hc : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) {E : State → State → Prop} {t : Nat}
    (hE : ∀ σ₁ σ₂, E σ₁ σ₂ → (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₁ (p.ℓ * t))).isSome →
      (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₂ (p.ℓ * t))).isSome → (VG.Proof.MlDsa.AArch64.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.AArch64.Sign.PassV p σ₂ (p.ℓ * t))) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.KA p D σ t s) (checks P p)
      (VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s) := by
  refine VG.Proof.MlDsa.AArch64.Sign.ksChk_spec hc fun c1 _ _ _ _ _ _ hz hr hh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_
  unfold checks
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.KN p D σ t s)
    (VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s cP)) (fun σ s h => ⟨h.c.l.st, h.cc.1⟩)
      (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.cntt_ok hP hc h) (VG.Proof.MlDsa.AArch64.Sign.ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt c1)) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t 0 s)
    (VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.kInit_ok hc h) (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h) (by taint_decide))) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IR p D σ t 0 s) (RelCT.mono (seqR_tr (Q := fun r => VG.Proof.MlDsa.AArch64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r s) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IZ p D σ t r s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.zR_ok hP (hz r (by omega)) h) (VG.Proof.MlDsa.AArch64.Sign.zR_trL hP (hz r (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ir) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IH p D σ t 0 s) (RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IR p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.r0R_ok hP (hr i (by omega)) h) (VG.Proof.MlDsa.AArch64.Sign.r0R_trL hP (hr i (by omega))))
    (fun _ _ h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h => h.ih) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.IH p D σ t p.k s) (RelCT.mono (seqR_tr (Q := fun i => VG.Proof.MlDsa.AArch64.Sign.RS p D E
    fun σ s => VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i s) p.k 0 fun i _ hi => VG.Proof.MlDsa.AArch64.Sign.liftL (T := fun s => ∃ σ, VG.Proof.MlDsa.AArch64.Sign.IH p D σ t i s)
      (fun σ s h => ⟨h.1.b.l.st, σ, h⟩) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.hR_ok hP (hh i (by omega)) h) (VG.Proof.MlDsa.AArch64.Sign.hR_trL hP (hh i (by omega))))
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RS p D E fun σ s => VG.Proof.MlDsa.AArch64.Sign.KO p D σ t s)
    (VG.Proof.MlDsa.AArch64.Sign.liftT (fun _ _ h => h.1.b.l.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.onesOk_ok hc h) (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h) (VG.Proof.MlDsa.AArch64.Sign.onesOk_taint p))) ?_
  refine VG.Proof.MlDsa.AArch64.Sign.liftR (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.kBranch_ok hc h) (VG.Proof.MlDsa.AArch64.Sign.ifOkElse_tr (fun x y h => ?_)
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1.lrel fun _ _ h => h.b.l.st) (by taint_decide))
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1.lrel fun _ _ h => h.b.l.st) (VG.Proof.MlDsa.AArch64.Sign.kapAdd_taint p)))
  obtain ⟨σ₁, σ₂, _, _, _, he, k₁, k₂⟩ := h
  rw [k₁.x24, k₂.x24, VG.Proof.MlDsa.AArch64.Sign.bit_congr (hE σ₁ σ₂ he k₁.b.some k₂.b.some)]

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT`. -/
section

/-!
# ML-DSA signing on AArch64: the loop leaks what `signLeakT` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ))
    ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := VG.Proof.MlDsa.AArch64.Sign.leakL p σ₁ (1000 - t) (p.ℓ * t) = VG.Proof.MlDsa.AArch64.Sign.leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [VG.Proof.MlDsa.AArch64.Sign.map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (VG.Proof.MlDsa.AArch64.Sign.map_toNat_inj h1), VG.Proof.MlDsa.AArch64.Sign.hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : VG.Proof.MlDsa.AArch64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ₁)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ₁)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ₁))
      ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ₁)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ₁) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoopT p maxBounds (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ₂)) ((List.range p.ℓ).map (VG.Proof.MlDsa.AArch64.Sign.S1v p σ₂)) ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.S2v p σ₂))
      ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.T0v p σ₂)) (VG.Proof.MlDsa.AArch64.Sign.muOf σ₂) (VG.Proof.MlDsa.AArch64.Sign.rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : VG.Proof.MlDsa.AArch64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814) : VG.Proof.MlDsa.AArch64.Sign.CTv p σ₁ (p.ℓ * t) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ₂ (p.ℓ * t) := by
  have := (leakT_step (VG.Proof.MlDsa.AArch64.Sign.leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : VG.Proof.MlDsa.AArch64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, VG.Proof.MlDsa.AArch64.Sign.iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : VG.Proof.MlDsa.AArch64.Sign.LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakT_step (VG.Proof.MlDsa.AArch64.Sign.leq_step h ht)).2.1 hr).2
  unfold VG.Proof.MlDsa.AArch64.Sign.LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ)).isSome) :
    outTag (VG.Proof.MlDsa.AArch64.Sign.iterF p σ maxBounds κ) = if VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ then
      1 :: ((List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [VG.Proof.MlDsa.AArch64.Sign.iterF_eq hp, VG.Proof.MlDsa.AArch64.Sign.cV_eq hs, Option.map_some]
  by_cases hv : VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : VG.Proof.MlDsa.AArch64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₂ (p.ℓ * t))).isSome) :
    VG.Proof.MlDsa.AArch64.Sign.PassV p σ₁ (p.ℓ * t) ↔ VG.Proof.MlDsa.AArch64.Sign.PassV p σ₂ (p.ℓ * t) := by
  have e := (leakT_step (VG.Proof.MlDsa.AArch64.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.AArch64.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.AArch64.Sign.outTag_eq hp hs₂] at e
  by_cases h1 : VG.Proof.MlDsa.AArch64.Sign.PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : VG.Proof.MlDsa.AArch64.Sign.PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

theorem leq_hints (hp : ParamsOk p) (h : VG.Proof.MlDsa.AArch64.Sign.LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (VG.Proof.MlDsa.AArch64.Sign.CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : VG.Proof.MlDsa.AArch64.Sign.PassV p σ₁ (p.ℓ * t)) (h2 : VG.Proof.MlDsa.AArch64.Sign.PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (VG.Proof.MlDsa.AArch64.Sign.Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakT_step (VG.Proof.MlDsa.AArch64.Sign.leq_step h ht)).2.2
  rw [VG.Proof.MlDsa.AArch64.Sign.outTag_eq hp hs₁, VG.Proof.MlDsa.AArch64.Sign.outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact VG.Proof.MlDsa.AArch64.Sign.hints_inj (by simp) (List.cons.inj e).2

end

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ₁ → (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre σ₂ → (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.LP p D σ t s) (hz : s.gpr .x9 ≠ 0) :
    VG.Proof.MlDsa.AArch64.Sign.IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h hz

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.LP p D σ t s) (hz : s.gpr .x9 = 0) :
    VG.Proof.MlDsa.AArch64.Sign.XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd hz h
  · exact h

theorem x9_ne {s : State} (h : isa.eval (.nonzero .x .x9) s = some true) : s.gpr .x9 ≠ 0 := by
  rw [VG.Proof.MlDsa.AArch64.Sign.eval_x9] at h; simpa using h

theorem x9_zero {s : State} (h : isa.eval (.nonzero .x .x9) s = some false) : s.gpr .x9 = 0 := by
  rw [VG.Proof.MlDsa.AArch64.Sign.eval_x9] at h; simpa using h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  VG.Proof.MlDsa.AArch64.Sign.RS p D (fun _ _ => True) (VG.Proof.MlDsa.AArch64.Sign.XS p D) x y ∧ x.gpr .x24 = y.gpr .x24 ∧
    (x.gpr .x24 = 1 → bytesAt x.mem (VG.Proof.MlDsa.AArch64.pa x (sc oCT)) (cLen p) = bytesAt y.mem (VG.Proof.MlDsa.AArch64.pa y (sc oCT)) (cLen p) ∧
      ∃ f, VG.Proof.MlDsa.AArch64.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.AArch64.Sign.HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.gpr .x9 = y.gpr .x9 ∧ (x.gpr .x9 ≠ 0 → VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p (t + 1)) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.IL p D σ (t + 1) s) x y) ∧
    (x.gpr .x9 = 0 → VG.Proof.MlDsa.AArch64.Sign.OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s) x y ∧ True)
      (.block cntDec) (VG.Proof.MlDsa.AArch64.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.AArch64.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.AArch64.Sign.dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (VG.Proof.MlDsa.AArch64.Sign.decF hc (h.elim (·.k) (·.k))))
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one]
    have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one]
    refine ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.x24, e₂.x24], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact VG.Proof.MlDsa.AArch64.Sign.leq_ct he e₁.t_lt,
      VG.Proof.MlDsa.AArch64.Sign.Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (VG.Proof.MlDsa.AArch64.Sign.leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((VG.Proof.MlDsa.AArch64.Sign.leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((VG.Proof.MlDsa.AArch64.Sign.leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.gpr .x9 = y'.gpr .x9 := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.AArch64.Sign.leq_succ he f₁.t_lt ⟨_, VG.Proof.MlDsa.AArch64.Sign.iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.x24, f₂.x24], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.x24)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {t : Nat} :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.EB p D σ t s) x y ∧ True) (.block cntDec) (VG.Proof.MlDsa.AArch64.Sign.IX p D t) := by
  refine VG.Proof.MlDsa.AArch64.Sign.liftQ (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.LP p D σ t s) (fun σ s _ h => WP.conj (VG.Proof.MlDsa.AArch64.Sign.dec_end hp hc (.inr (.inr h))) (VG.Proof.MlDsa.AArch64.Sign.decF hc h.k))
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one]
  have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, VG.Proof.MlDsa.AArch64.Sign.one_sub_one]
  exact ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.x24, e₂.x24],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.x24)) (by decide)⟩⟩

theorem x0_one {s : State} (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1)
    (hb : isa.eval (.nonzero .w .x0) s = some true) : (s.gpr .x0).setWidth 32 = 1 := by
  rw [VG.Proof.MlDsa.AArch64.Sign.eval_w0] at hb
  rcases hr with h | h
  · rw [h] at hb; cases hb
  · exact h

theorem x0_zero {s : State} (hb : isa.eval (.nonzero .w .x0) s = some false) : (s.gpr .x0).setWidth 32 = 0 := by
  rw [VG.Proof.MlDsa.AArch64.Sign.eval_w0] at hb; simpa using hb

theorem iter_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (hc1 : VG.Proof.MlDsa.AArch64.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.AArch64.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) fun σ s => VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) (iterWith keccak.callee P p) (VG.Proof.MlDsa.AArch64.Sign.IX p D t) := by
  have hp := VG.Proof.MlDsa.AArch64.Sign.paramsOk h3
  have hc2' := hc2
  simp only [VG.Proof.MlDsa.AArch64.Sign.bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iterWith
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sign.commit_tr hP h3 hc1) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.IB p D σ t s) x y ∧
      (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32)
    (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.liftQ (G := fun _ _ => True) (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (VG.Proof.MlDsa.AArch64.Sign.ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact VG.Proof.MlDsa.AArch64.Sign.leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun x y => (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.EP p D σ t s ∨ VG.Proof.MlDsa.AArch64.Sign.EF p D σ t s) x y ∧ True) ∨
      (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (VG.Proof.MlDsa.AArch64.Sign.relOr (VG.Proof.MlDsa.AArch64.Sign.endPF_tr hp hc4) (VG.Proof.MlDsa.AArch64.Sign.endB_tr hp hc4))
  · rintro x y ⟨_, hg⟩
    rw [VG.Proof.MlDsa.AArch64.Sign.eval_w0, VG.Proof.MlDsa.AArch64.Sign.eval_w0, hg]
  · refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.checks_tr hP hc3 fun σ₁ σ₂ he s₁ s₂ => VG.Proof.MlDsa.AArch64.Sign.leq_pass hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := VG.Proof.MlDsa.AArch64.Sign.x0_one i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.liftT (I := fun σ s => VG.Proof.MlDsa.AArch64.Sign.IB p D σ t s ∧ (s.gpr .x0).setWidth 32 = 0)
      (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.else_ok hc4 h.1 h.2)
      (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h) (by taint_decide)))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := VG.Proof.MlDsa.AArch64.Sign.x0_zero hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (hc1 : VG.Proof.MlDsa.AArch64.Sign.cChk p = true) (hc2 : VG.Proof.MlDsa.AArch64.Sign.bChk p = true)
    (hc3 : VG.Proof.MlDsa.AArch64.Sign.ksChk p = true) (hc4 : VG.Proof.MlDsa.AArch64.Sign.lChk p = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p 0) fun σ s => VG.Proof.MlDsa.AArch64.Sign.IK p D σ s) (Impl.MlDsa.AArch64.Sign.signLoopWith keccak.callee P p) (VG.Proof.MlDsa.AArch64.Sign.OX p D) := by
  unfold Impl.MlDsa.AArch64.Sign.signLoopWith
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sign.liftT (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.loopInit_ok hc4 h)
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p t) (fun σ s => VG.Proof.MlDsa.AArch64.Sign.IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := VG.Proof.MlDsa.AArch64.Sign.iter_tr hP h3 hc1 hc2 hc3 hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [VG.Proof.MlDsa.AArch64.Sign.eval_x9, VG.Proof.MlDsa.AArch64.Sign.eval_x9, hz], fun h => ho (VG.Proof.MlDsa.AArch64.Sign.x9_zero h), fun h =>
    ⟨814 - (t + 1), by omega, t + 1, rfl, hc (VG.Proof.MlDsa.AArch64.Sign.x9_ne h)⟩⟩

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT`. -/
section

/-!
# ML-DSA signing on AArch64: the signature leaks only the hint

Writing the signature leaks its pointers and the hint (`output_tr`), on which
two runs whose loops leaked the same agree (`OX`); so all but `Â` leaks what
`signLeakT` says (`rest_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : VG.Proof.MlDsa.AArch64.Sign.HFam x 5 k f) (hy : VG.Proof.MlDsa.AArch64.Sign.HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (VG.Proof.MlDsa.AArch64.pa x (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (VG.Proof.MlDsa.AArch64.pa y (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s (Impl.MlDsa.AArch64.Sign.hP 0)) i =
      coeffAt s.mem (VG.Proof.MlDsa.AArch64.pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [VG.Proof.MlDsa.AArch64.Sign.pS_hint s (i / 256)]
    simp only [coeffAt]
    rw [BitVec.add_assoc (VG.Proof.MlDsa.AArch64.pa s (Impl.MlDsa.AArch64.Sign.hP 0)) (BitVec.ofNat 64 (1024 * (i / 256))), ← BitVec.ofNat_add,
      show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega]
  have hq : i / 256 < k := by omega
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, VG.Proof.MlDsa.AArch64.Sign.IK p D σ s ∧ bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oCT)) (cLen p) = VG.Proof.MlDsa.AArch64.Sign.CTv p σ κ ∧ VG.Proof.MlDsa.AArch64.Sign.Fam s (VG.Proof.MlDsa.AArch64.Sign.yBase p) p.ℓ (VG.Proof.MlDsa.AArch64.Sign.Zv p σ κ) ∧
    VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k (VG.Proof.MlDsa.AArch64.Sign.Hv p σ κ) ∧ VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ ∧ s.gpr .x24 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, VG.Proof.MlDsa.AArch64.Sign.OS p D σ κ r s ∧ VG.Proof.MlDsa.AArch64.Sign.PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, VG.Proof.MlDsa.AArch64.Sign.HFam x 5 p.k f ∧ VG.Proof.MlDsa.AArch64.Sign.HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (VG.Proof.MlDsa.AArch64.pa s (yP p r)) ∧ VG.Proof.MlDsa.AArch64.Sign.InRange s.mem (VG.Proof.MlDsa.AArch64.pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, VG.Proof.MlDsa.AArch64.Sign.inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) (hc : VG.Proof.MlDsa.AArch64.Sign.oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IOi p D) x y ∧ VG.Proof.MlDsa.AArch64.Sign.HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  unfold output
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IOr p D 0) x y ∧ VG.Proof.MlDsa.AArch64.Sign.HJ p x y) (VG.Proof.MlDsa.AArch64.Sign.liftQ
    (F := fun s s' => ∀ f, VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.AArch64.Sign.HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (VG.Proof.MlDsa.AArch64.Sign.outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (VG.Proof.MlDsa.AArch64.Sign.copy_tr (.inr rfl) rfl fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk.d.im.st)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IOr p D p.ℓ) x y ∧ VG.Proof.MlDsa.AArch64.Sign.HJ p x y) (RelCT.mono (seqR_tr
    (Q := fun r x y => VG.Proof.MlDsa.AArch64.Sign.RS p D E (VG.Proof.MlDsa.AArch64.Sign.IOr p D r) x y ∧ VG.Proof.MlDsa.AArch64.Sign.HJ p x y) p.ℓ 0 fun r _ hr => VG.Proof.MlDsa.AArch64.Sign.liftQ
      (F := fun s s' => ∀ f, VG.Proof.MlDsa.AArch64.Sign.HFam s 5 p.k f → VG.Proof.MlDsa.AArch64.Sign.HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (VG.Proof.MlDsa.AArch64.Sign.packZ_ok hP hc (by omega) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.bpAt_tr hP hbp hzl (cz r (by omega)).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega), i₂.zr (by omega)⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k.d.im.st, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨VG.Proof.MlDsa.AArch64.Sign.hones_ok o₁ a₁, VG.Proof.MlDsa.AArch64.Sign.hones_ok o₂ a₂, VG.Proof.MlDsa.AArch64.Sign.hint_coeffs hx hy⟩

theorem XS.io {σ x : State} (h : VG.Proof.MlDsa.AArch64.Sign.XS p D σ x) (h15 : x.gpr .x24 = 1) : VG.Proof.MlDsa.AArch64.Sign.IOi p D σ x := by
  obtain ⟨t, _, _, _, hpass, hct, hz, hh⟩ := h.pass h15
  exact ⟨p.ℓ * t, h.k, hct, hz, hh, hpass, h15⟩

theorem rest_tr {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p 0) (VG.Proof.MlDsa.AArch64.Sign.IM p D)) (restWith keccak.callee P p) (VG.Proof.MlDsa.AArch64.Sign.RS p D (VG.Proof.MlDsa.AArch64.Sign.LeakEq p 0) (VG.Proof.MlDsa.AArch64.Sign.FS p D)) := by
  refine VG.Proof.MlDsa.AArch64.Sign.liftR (fun σ s _ h => VG.Proof.MlDsa.AArch64.Sign.rest_ok hP h3 h) ?_
  have hc := VG.Proof.MlDsa.AArch64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, -⟩ := hc
  unfold restWith
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sign.decode_tr hP hd) (RelCT.seq (VG.Proof.MlDsa.AArch64.Sign.signLoop_tr hP h3 hc1 hb hks hl) ?_)
  unfold ifOk
  refine VG.Proof.MlDsa.AArch64.Sign.ifOkElse_tr (fun x y h => by rw [h.2.1]) (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.output_tr hP ho (E := fun _ _ => True))
    (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, _, s₁, s₂⟩, h15, hj⟩, hne⟩ => ?_)
    fun _ _ h => h) (RelCT.mono nil_tr (fun _ _ h => h) fun _ _ _ => trivial)
  have e₁ := VG.Proof.MlDsa.AArch64.Sign.x24_one s₁.r01 hne
  have e₂ : y.gpr .x24 = 1 := h15 ▸ e₁
  obtain ⟨_, f, hx, hy⟩ := hj e₁
  exact ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, s₁.io e₁, s₂.io e₂⟩, f, hx, hy⟩

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseACT`. -/
section

/-!
# ML-DSA signing on AArch64: `ExpandA` leaks only `ρ`

Two runs of `ExpandA` with the same `ρ` compute the same results of
`vg_mldsa_rej_ntt_poly`, so they agree on `x24` (`RA`), and leak the same
(`expandA_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Two runs of `ExpandA` after `e` entries, with the same `x24`. -/
abbrev RA (p : Params) (D e : Nat) : State → State → Prop :=
  VG.Proof.MlDsa.AArch64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s) fun x y => x.gpr .x24 = y.gpr .x24

theorem callE_ok' {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) {s : State} (h : VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s) (hs : bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ e) :
    WP isa (callAt ("vg_mldsa_rej_ntt_poly" ++ P.suffix) P.rejNTT [(.x0, .ptr (sc oRS)), (.x1, .ptr (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p + e))),
      (.x2, .ptr (sc oPS))]) s fun s' => VG.Proof.MlDsa.AArch64.Sign.JE p D e σ s' ∧ s'.gpr .x24 = s.gpr .x24 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.AArch64.Sign.eChk_spec he
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sign.rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ =>
    ⟨⟨s, h, hP3, hcs3, hred, ?_, ?_⟩, hcs3⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem blkE_taint (p : Params) (e : Nat) :
    (taint.check (AArch64.Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (.block (VG.Proof.MlDsa.AArch64.Sign.blkE p e)) (.block [])).isSome = true := by
  dsimp only [VG.Proof.MlDsa.AArch64.Sign.blkE, setB]; rfl

theorem sampleE_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {e : Nat} (he : VG.Proof.MlDsa.AArch64.Sign.eChk p e = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RA p D e) (sampleE P p e) (VG.Proof.MlDsa.AArch64.Sign.RA p D (e + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := VG.Proof.MlDsa.AArch64.Sign.eChk_spec he
  rw [VG.Proof.MlDsa.AArch64.Sign.sampleE_eq]
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.AArch64.Sign.IA p D σ e s ∧ bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS)) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ e)
    fun x y => x.gpr .x24 = y.gpr .x24) ?_ (RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.JE p D e)
      fun x y => x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) ?_ ?_)
  · exact VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => VG.Proof.MlDsa.AArch64.Sign.blkE_ok he h)
      (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.lrel fun _ _ h => h.st) (VG.Proof.MlDsa.AArch64.Sign.blkE_taint p e)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2]
  · refine VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (fun σ s _ h => VG.Proof.MlDsa.AArch64.Sign.callE_ok' hP he h.1 h.2)
      ((VG.Proof.MlDsa.AArch64.Sign.rejCall_tr hP hc).mono (fun x y h => ⟨h.lrel fun _ _ h => h.1.st, ?_⟩) fun _ _ h => h)
      fun x y x' y' h fx fy q => ⟨by rw [fx, fy, h.2], q⟩
    obtain ⟨⟨σ₁, σ₂, _, _, hpub, ⟨_, s₁⟩, ⟨_, s₂⟩⟩, _⟩ := h
    rw [s₁, s₂, VG.Proof.MlDsa.AArch64.Sign.seedE, VG.Proof.MlDsa.AArch64.Sign.seedE, VG.Proof.MlDsa.AArch64.Sign.pub_rho hpub]
  · refine VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun s s' => s'.gpr .x24 =
        BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
      (fun σ s _ h => WP.conj (VG.Proof.MlDsa.AArch64.Sign.andE_ok he h) (WP.mono (and24_ok s) fun _ h => h.2))
      (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.lrel fun _ σ h => ?_) (by taint_decide)) fun x y x' y' h fx fy _ => by rw [fx, fy, h.2.1, h.2.2]
    obtain ⟨s₀, h₀, hP₀, -⟩ := h
    exact h₀.st.step hP₀ (VG.Proof.MlDsa.AArch64.Sign.eChk_spec he).2.2.1



end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT`. -/
section

/-! Four-way matrix expansion leaks only the public matrix seed. The batch return is public before signing branches on it. -/

namespace VG.Proof.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem postDepQ {Q R T : State → State → Prop} {c : Prog isa} {F : State → State → Prop}
    (htr : RelCT isa Q c R) (hw : ∀ x y,Q x y → (WP isa c x (F x)) ∧ (WP isa c y (F y)))
    (hq : ∀ x y x' y',Q x y → F x x' → F y y' → R x' y' → T x' y') : RelCT isa Q c T := by
  intro x y tx ty x' y' hp ex ey
  obtain ⟨ht,hr⟩ := htr x y tx ty x' y' hp ex ey
  obtain ⟨hx,hy⟩ := hw x y hp
  obtain ⟨_,u,eu,hu⟩ := hx
  obtain ⟨_,v,ev,hv⟩ := hy
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨ht,hq x y x' y' hp hu hv hr⟩

theorem slot4_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs VG.Proof.MlDsa.AArch64.Sign.bases) (seedSlot4 p e j) (.seq (Taint.ofRegs (.x10::VG.Proof.MlDsa.AArch64.Sign.bases)) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 lea
  rw [ifp (by dsimp only [oRS4]; omega : oRS4+34*j < 4096)]
  with_unfolding_all rfl

theorem slot4_tr {p : Params} {D e j : Nat} (hj : j < 4) (hc : VG.Proof.MlDsa.AArch64.Sign.slotChk p e j = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.AS p D · e j) fun x y => x.gpr .x24 = y.gpr .x24)
      (seedSlot4 p e j) (VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.AS p D · e (j+1)) fun x y => x.gpr .x24 = y.gpr .x24) :=
  VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun s t => t.gpr .x24 = s.gpr .x24) (fun _ _ _ h => VG.Proof.MlDsa.AArch64.Sign.slot4_ok hj hc h)
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun _ _ h => h.lrel fun _ _ h => h.ia.st) (VG.Proof.MlDsa.AArch64.Sign.slot4_taint p e hj))
    fun _ _ _ _ h hx hy _ => by rw [hx,hy,h.2]

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P+BitVec.ofNat 64 34) 34 ++
    bytesAt m (P+BitVec.ofNat 64 68) 34 ++ bytesAt m (P+BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34+102 from rfl,VG.Proof.MlKem.bytesAt_add,show 102=34+68 from rfl,VG.Proof.MlKem.bytesAt_add,
    show 68=34+34 from rfl,VG.Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc,← BitVec.ofNat_add,List.append_assoc,Nat.reduceAdd]

theorem AS.seeds {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : VG.Proof.MlDsa.AArch64.Sign.AS p D σ e 4 s) :
    bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS4)) 136 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+0) ++ VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+1) ++ VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+2) ++ VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+3) := by
  have b : ∀ k < 4,bytesAt s.mem (VG.Proof.MlDsa.AArch64.pa s (sc oRS4)+BitVec.ofNat 64 (34*k)) 34 = VG.Proof.MlDsa.AArch64.Sign.seedE p σ (e+k) :=
    fun k hk => VG.Proof.MlDsa.AArch64.Sign.aseeds_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34*0=0 from rfl,VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [VG.Proof.MlDsa.AArch64.Sign.bytes136,b0,b 1 (by decide),b 2 (by decide),b 3 (by decide)]

theorem batch_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {g : Nat} (hc : VG.Proof.MlDsa.AArch64.Sign.batchChk p g = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.AS p D · (4*g) 4) fun x y => x.gpr .x24 = y.gpr .x24)
      (.seq (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args (sc oRS4) (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g)) (sc (oR4 p)))) (.block and24))
      (VG.Proof.MlDsa.AArch64.Sign.RA p D (4*g+4)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.Sign.batchChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨cr,_⟩,_⟩,_⟩,_⟩ := hc'
  refine VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun _ _ => True) (fun _ _ _ h => WP.mono (VG.Proof.MlDsa.AArch64.Sign.batch_ok hP hc h) fun _ ht => ⟨ht,trivial⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have calltr : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.AS p D · (4*g) 4) fun x y => x.gpr .x24 = y.gpr .x24)
      (callAt ("vg_mldsa_rej_ntt_poly4"++P.suffix) P.rej4 (VG.Proof.MlDsa.AArch64.Sign.rej4Args (sc oRS4) (pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g)) (sc (oR4 p))))
      (fun x y => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y ∧ x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) := by
    refine VG.Proof.MlDsa.AArch64.Sign.postDepQ (fun x y t1 t2 x' y' h e1 e2 =>
      VG.Proof.MlDsa.AArch64.Sign.rej4AtK_trRet hP.rej4 hP.rej4Ret (h.lrel fun _ _ h => h.ia.st).ok cr ?_ x y t1 t2 x' y' h e1 e2)
      (F := fun s t => PPostB D s t [(pS (VG.Proof.MlDsa.AArch64.Sign.aBase p+4*g),4096),(sc (oR4 p),8192)] ∧ t.gpr .x24 = s.gpr .x24)
      ?_ ?_
    · intro x y h
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨L.lx,L.ly,?_,L.same⟩
      obtain ⟨⟨σ1,σ2,_,_,pub,h1,h2⟩,_⟩ := h
      rw [h1.seeds,h2.seeds]
      simp only [VG.Proof.MlDsa.AArch64.Sign.seedE,VG.Proof.MlDsa.AArch64.Sign.pub_rho pub]
    · intro x y h
      obtain ⟨⟨σ1,σ2,_,_,_,h1,h2⟩,_⟩ := h
      exact ⟨WP.mono (VG.Proof.MlDsa.AArch64.Sign.rej4Call_ok hP h1.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩),
        WP.mono (VG.Proof.MlDsa.AArch64.Sign.rej4Call_ok hP h2.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩)⟩
    · intro x y x' y' h hx hy hr
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨⟨L.lx.post hx.1,L.ly.post hy.1,fun r hr => ?_,?_,L.ok⟩,by rw [hx.2,hy.2,h.2],hr⟩
      · rw [hx.1.bs r (VG.Proof.MlDsa.AArch64.Sign.bases_kept r hr),hy.1.bs r (VG.Proof.MlDsa.AArch64.Sign.bases_kept r hr)]; exact L.regs r hr
      · rw [hx.1.sp,hy.1.sp]; exact L.sp
  refine RelCT.seq calltr (RelCT.postDep (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun _ _ h => h.1) (by taint_decide))
    (F := fun s t => t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
    (fun x y _ => ⟨WP.mono (and24_ok x) (fun _ h => h.2),WP.mono (and24_ok y) (fun _ h => h.2)⟩)
    fun x y x' y' h hx hy => by rw [hx,hy,h.2.1,h.2.2])

theorem sample4_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} {g : Nat}
    (hb : VG.Proof.MlDsa.AArch64.Sign.batchChk p g = true) (hs : ∀ j < 4,VG.Proof.MlDsa.AArch64.Sign.slotChk p (4*g) j = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RA p D (4*g)) (sample4 P p g) (VG.Proof.MlDsa.AArch64.Sign.RA p D (4*g+4)) := by
  unfold sample4
  refine RelCT.seq (RelCT.mono (seqR_tr (Q := fun j => VG.Proof.MlDsa.AArch64.Sign.RR p D (VG.Proof.MlDsa.AArch64.Sign.AS p D · (4*g) j) fun x y => x.gpr .x24 = y.gpr .x24) 4 0
    (fun j _ hj => VG.Proof.MlDsa.AArch64.Sign.slot4_tr (by omega) (hs j (by omega)))) ?_ (fun _ _ h => by simpa using h)) (VG.Proof.MlDsa.AArch64.Sign.batch_tr hP hb)
  exact fun x y h => h.mono (fun _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩) (fun h => h)

theorem expandA_tr {P : Prims} {D : Nat} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) (hc : VG.Proof.MlDsa.AArch64.Sign.aChk p = true) :
    RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RR p D (fun σ s => VG.Proof.MlDsa.AArch64.Sign.St p D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.expandA P p) (VG.Proof.MlDsa.AArch64.Sign.RA p D (p.k * p.ℓ)) := by
  have hp : p ∈ [mlDsa44,mlDsa65,mlDsa87] := by rcases h3 with rfl | rfl | rfl <;> simp
  simp only [VG.Proof.MlDsa.AArch64.Sign.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.expandA
  refine RelCT.seq (R := VG.Proof.MlDsa.AArch64.Sign.RA p D 0) (VG.Proof.MlDsa.AArch64.Sign.stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.IA p D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, VG.Proof.MlDsa.AArch64.Sign.rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · unfold sampleAll
    have hB : RelCT isa (VG.Proof.MlDsa.AArch64.Sign.RA p D 0) (seqR (sample4 P p) 0 (p.k*p.ℓ/4)) (VG.Proof.MlDsa.AArch64.Sign.RA p D (4*(p.k*p.ℓ/4))) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (Q := fun g => VG.Proof.MlDsa.AArch64.Sign.RA p D (4*g)) (p.k*p.ℓ/4) 0 (fun g _ hg =>
          VG.Proof.MlDsa.AArch64.Sign.sample4_tr hP (VG.Proof.MlDsa.AArch64.Sign.batchChk_ok p hp g (by omega)) (fun j hj => VG.Proof.MlDsa.AArch64.Sign.slotChk_ok p hp (4*g) (by omega) j hj)))
    have htail := seqR_tr (Q := fun e => VG.Proof.MlDsa.AArch64.Sign.RA p D e) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he' => VG.Proof.MlDsa.AArch64.Sign.sampleE_tr hP (he e (by omega)))
    have eqn : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
    simpa only [eqn] using RelCT.seq hB htail

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT`. -/
section

/-!
# ML-DSA signing on AArch64: constant time

Two runs whose entry states agree on `signK`'s public data (`signLeakT` among
them) leak the same: the prologue and the return only the pointers, `ExpandA`
only `ρ` (`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on
which they agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub σ₁ σ₂)
    (hA₁ : expandA p maxBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ₁) = some (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ₁)))
    (hA₂ : expandA p maxBounds (VG.Proof.MlDsa.AArch64.Sign.rhoOf p σ₂) = some (amat p (VG.Proof.MlDsa.AArch64.Sign.Am p σ₂))) : VG.Proof.MlDsa.AArch64.Sign.LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2
  rw [signLeakT_eq hA₁, signLeakT_eq hA₂] at e
  have hρ : (VG.Proof.MlDsa.AArch64.Sign.skOf p σ₁).take 32 = (VG.Proof.MlDsa.AArch64.Sign.skOf p σ₂).take 32 := VG.Proof.MlDsa.AArch64.Sign.pub_rho hpub
  rw [hρ] at e
  exact List.append_cancel_left e

theorem rr_rs {I E : State → State → Prop} {x y : State} (h : VG.Proof.MlDsa.AArch64.Sign.RR p D I E x y) : VG.Proof.MlDsa.AArch64.Sign.RS p D (fun _ _ => True) I x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, trivial, i₁, i₂⟩

theorem sign_ct {P : Prims} (hP : VG.Proof.MlDsa.AArch64.Sign.PrimsOk P D) (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) :
    ConstantTime isa (VG.Proof.MlDsa.AArch64.Sign.signK p D).pre (VG.Proof.MlDsa.AArch64.Sign.signK p D).pub (Impl.MlDsa.AArch64.Sign.signWith keccak.callee P p) := by
  have hc := VG.Proof.MlDsa.AArch64.Sign.allChk_ok h3
  simp only [VG.Proof.MlDsa.AArch64.Sign.allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.AArch64.Sign.signWith
  refine RelCT.seq (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.relInvE (J := fun σ s => VG.Proof.MlDsa.AArch64.Sign.St p D σ s ∧ s.gpr .x24 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (VG.Proof.MlDsa.AArch64.Sign.pro_ok (VG.Proof.MlDsa.AArch64.Sign.pro_in h3 hp)) fun s₁ ⟨h₁, h15, hf₁⟩ => ⟨VG.Proof.MlDsa.AArch64.Sign.entry_st h3 hp h₁ hf₁, h15⟩)
    (taintRel [.x0, .x1, .x2, .x3, .x4] (fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ => by
      subst h₁ h₂
      obtain ⟨e0, e1, e2, e3, e4, e5, -⟩ := hpub
      refine ⟨e5, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3, e4]) (by taint_decide))) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (VG.Proof.MlDsa.AArch64.Sign.expandA_tr hP h3 ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => VG.Proof.MlDsa.AArch64.Sign.LRel D (VG.Proof.MlDsa.AArch64.Sign.sgR p) (VG.Proof.MlDsa.AArch64.Sign.sgW p) x y) ?_
    (VG.Proof.MlDsa.AArch64.Sign.lrel_tr (fun x y h => h) (by taint_decide))
  unfold ifOk
  refine VG.Proof.MlDsa.AArch64.Sign.ifOkElse_tr (P := VG.Proof.MlDsa.AArch64.Sign.RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (VG.Proof.MlDsa.AArch64.Sign.rest_tr hP h3)
    (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, hne⟩ => ?_) fun x y h => h.lrel fun _ _ h => h.st)
    (RelCT.mono nil_tr (fun _ _ h => h) fun x y h => h.1.lrel fun _ _ h => h.st)
  have e₁ := VG.Proof.MlDsa.AArch64.Sign.x24_one i₁.r01 hne
  have e₂ : y.gpr .x24 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.AArch64.Sign.pub_leq hpub (VG.Proof.MlDsa.AArch64.Sign.expandA_max ok₁) (VG.Proof.MlDsa.AArch64.Sign.expandA_max ok₂), ⟨i₁.st, ok₁, fam₁⟩,
    ⟨i₂.st, ok₂, fam₂⟩⟩

end

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inst`. -/
section

/-!
# ML-DSA signing on AArch64: the primitives it calls

The verified AArch64 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`), with 16 bytes of stack for each
call (the samplers' frames): their contracts (`CalleeOk.of_verified`), and, of
the two samplers whose result signing branches on, that it depends only on
their public data and that they succeed only if the algorithm finishes within
`maxBounds` (from what their own proofs say they return, `RejNtt.correct` and
`Ball.correct`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The AArch64 implementations of the primitives. -/
def primsWith (c : Impl.Sha3.AArch64.Callee) : Prims where
  suffix := c.suffix
  ntt := Impl.MlDsa.AArch64.Arith.Neon.ntt
  invNtt := Impl.MlDsa.AArch64.Arith.Neon.nttInv
  mul := Impl.MlDsa.AArch64.Arith.mul
  mulAdd := Impl.MlDsa.AArch64.Arith.mulAdd
  add := Impl.MlDsa.AArch64.Arith.add
  sub := Impl.MlDsa.AArch64.Arith.sub
  rej4 := Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With c.pairedSha3
  rejNTT := Impl.MlDsa.AArch64.Sample.rejNTTWith c
  expandMask := Impl.MlDsa.AArch64.Sample.expandMaskWith c
  ball := Impl.MlDsa.AArch64.Sample.sampleInBallWith c
  highBits := Impl.MlDsa.AArch64.Round.highBits
  lowBits := Impl.MlDsa.AArch64.Round.lowBits
  normLt := Impl.MlDsa.AArch64.Round.normLt
  makeHint := Impl.MlDsa.AArch64.Round.makeHint
  simpleBitPack := Impl.MlDsa.AArch64.Pack.simpleBitPack
  bitPack := Impl.MlDsa.AArch64.Pack.bitPack
  bitUnpack := Impl.MlDsa.AArch64.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.AArch64.Pack.hintBitPack

def prims := VG.Proof.MlDsa.AArch64.Sign.primsWith .scalar

/-- The stack signing gives each call. -/
abbrev signStack : Nat := 16

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.AArch64.Sample VG.Proof.MlDsa.Sample

theorem rn_pre (s : State) (h : (rejNTTContract AArch64.abi 16).pre s) : rnK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs]

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract AArch64.abi 16).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .x0) 34 = bytesAt s₂.mem (s₂.gpr .x0) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact VG.Proof.MlKem.map_toNat_inj hb

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract AArch64.abi 16).pre s)
    (e : Exec isa (Impl.MlDsa.AArch64.Sample.rejNTTWith keccak.callee) s tr s') :
    (s'.gpr .x0).setWidth 32 =
      if (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := RejNtt.correctWith keccak s (VG.Proof.MlDsa.AArch64.Sign.rn_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem rn4_pre (s : State) (h : (rejNTT4Contract AArch64.abi 16).pre s) : Rej4.r4K.pre s := by
  have hh : Rej4.preProps s := by
    revert s h
    sig_implies_pre [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,Rej4.preProps,
      Rej4.seedsR,Rej4.aR,Rej4.scrR,Rej4.seedP,Rej4.aP,Rej4.scr,AArch64.abi,AArch64.argRegs]
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩

theorem rn4_pub (s₁ s₂ : State) (h : (rejNTT4Contract AArch64.abi 16).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .x0) 136 = bytesAt s₂.mem (s₂.gpr .x0) 136 := by
  sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs] at h
  obtain ⟨_,hb,_⟩ := h
  exact Proof.MlKem.map_toNat_inj hb

theorem rn4_ret {s s' : State} {tr : List Leak} (h : (rejNTT4Contract AArch64.abi 16).pre s)
    (e : Exec isa (Impl.MlDsa.AArch64.Sample.Rej4.rejNTT4With keccak.callee.pairedSha3) s tr s') :
    (s'.gpr .x0).setWidth 32 = rej4Res s.mem (s.gpr .x0) := by
  obtain ⟨_,_,he',_,hq⟩ := Rej4.correct keccak.callee.pairedSha3 s (VG.Proof.MlDsa.AArch64.Sign.rn4_pre s h)
  obtain ⟨_,rfl⟩ := Exec.det e he'
  exact hq.1.trans (Rej4.mask_cast s)

theorem sb_pre (s : State) (h : (sampleInBallContract AArch64.abi 16).pre s) : sbK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi, AArch64.argRegs]

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract AArch64.abi 16).pub s₁ s₂) :
    tauOf s₁ = tauOf s₂ ∧
      bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat = bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨_, hb, _, _, hx2, _, _⟩ := h
  exact ⟨by rw [tauOf, tauOf, hx2], VG.Proof.MlKem.map_toNat_inj hb⟩

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract AArch64.abi 16).pre s)
    (e : Exec isa (Impl.MlDsa.AArch64.Sample.sampleInBallWith keccak.callee) s tr s') :
    (s'.gpr .x0).setWidth 32 =
      if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := Ball.correctWith keccak s (VG.Proof.MlDsa.AArch64.Sign.sb_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_okWith : VG.Proof.MlDsa.AArch64.Sign.PrimsOk (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) VG.Proof.MlDsa.AArch64.Sign.signStack where
  s16 := by decide
  sl := by decide
  ntt := by
    have h := Proof.MlDsa.AArch64.Arith.Neon.ntt_verified
    unfold Spec.MlDsa.nttContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  invNtt := by
    have h := Proof.MlDsa.AArch64.Arith.Neon.nttInv_verified
    unfold Spec.MlDsa.nttInvContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  mul := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Arith.mul_verified (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  mulAdd := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Arith.mulAdd_verified (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  add := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Arith.add_verified (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  sub := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Arith.sub_verified (by decide) (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  rej4 := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide)
    (Proof.MlDsa.AArch64.Sample.Rej4.verified keccak.callee.pairedSha3) (by decide)
    (by simp [VG.Proof.MlDsa.AArch64.Sign.primsWith,VG.Proof.MlDsa.AArch64.Sign.signStack,Proof.MlDsa.AArch64.Sample.Rej4.depth])
  rej4Ret := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁,h₂,hp⟩ e₁ e₂ =>
    ⟨(Proof.MlDsa.AArch64.Sample.Rej4.ct keccak.callee.pairedSha3) s₁ s₂ t₁ t₂ s₁' s₂'
      (VG.Proof.MlDsa.AArch64.Sign.rn4_pre s₁ h₁) (VG.Proof.MlDsa.AArch64.Sign.rn4_pre s₂ h₂) (by
        sig_pub [Spec.MlDsa.rejNTT4Contract,Spec.MlDsa.rejNTT4Sig,AArch64.abi,AArch64.argRegs] at hp
        obtain ⟨hsp,hb,h0,h1,h2⟩ := hp
        exact ⟨h0,h1,h2,hsp,Proof.MlKem.map_toNat_inj hb⟩) e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.AArch64.Sign.rn4_ret h₁ e₁,VG.Proof.MlDsa.AArch64.Sign.rn4_ret h₂ e₂]; exact Proof.MlDsa.Sample.rej4Res_congr (VG.Proof.MlDsa.AArch64.Sign.rn4_pub s₁ s₂ hp)⟩
  rej4Max := fun s t s' h e h1 k hk => by
    rw [VG.Proof.MlDsa.AArch64.Sign.rn4_ret h e] at h1
    exact Proof.MlDsa.Sample.rej4Res_max h1 hk (by decide)
  rejNTT := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) (Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith keccak) (by decide)
    (by simp [VG.Proof.MlDsa.AArch64.Sign.primsWith, VG.Proof.MlDsa.AArch64.Sign.signStack, Sample.rejNTT_depth keccak])
  expandMask := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) (Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith keccak) (by decide)
    (by simp [VG.Proof.MlDsa.AArch64.Sign.primsWith, VG.Proof.MlDsa.AArch64.Sign.signStack, Sample.expandMask_depth keccak])
  ball := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) (Proof.MlDsa.AArch64.Sample.sampleInBall_verifiedWith keccak) (by decide)
    (by simp [VG.Proof.MlDsa.AArch64.Sign.primsWith, VG.Proof.MlDsa.AArch64.Sign.signStack, Sample.ball_depth keccak])
  highBits := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Round.highBits_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  lowBits := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Round.lowBits_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  normLt := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Round.normLt_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  makeHint := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Round.makeHint_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  simpleBitPack := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Pack.simpleBitPack_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  bitPack := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Pack.bitPack_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  bitUnpack := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Pack.bitUnpack_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  hintBitPack := CalleeOk.of_verified (S := VG.Proof.MlDsa.AArch64.Sign.signStack) (by decide) Proof.MlDsa.AArch64.Pack.hintBitPack_verified (by decide)
    (by dsimp only [VG.Proof.MlDsa.AArch64.Sign.primsWith]; decide +kernel)
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨(Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith keccak).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.AArch64.Sign.rn_ret h₁ e₁, VG.Proof.MlDsa.AArch64.Sign.rn_ret h₂ e₂, VG.Proof.MlDsa.AArch64.Sign.rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.AArch64.Sign.rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.AArch64.Sign.one_ne_zero32
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨(Proof.MlDsa.AArch64.Sample.sampleInBall_verifiedWith keccak).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.AArch64.Sign.sb_ret h₁ e₁, VG.Proof.MlDsa.AArch64.Sign.sb_ret h₂ e₂, (VG.Proof.MlDsa.AArch64.Sign.sb_pub s₁ s₂ hp).1, (VG.Proof.MlDsa.AArch64.Sign.sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.AArch64.Sign.sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s)
      (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide)
        (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.AArch64.Sign.one_ne_zero32

theorem prims_ok : VG.Proof.MlDsa.AArch64.Sign.PrimsOk VG.Proof.MlDsa.AArch64.Sign.prims VG.Proof.MlDsa.AArch64.Sign.signStack := VG.Proof.MlDsa.AArch64.Sign.prims_okWith (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Verified`. -/
section

/-!
# ML-DSA signing on AArch64: verified

`vg_mldsa{44,65,87}_sign` (`sign prims p`) is verified against
`signContractT`: `signContract` with `signLeakT`
(`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`, which tags what each iteration
of the loop leaks after its `c̃` with whether it was rejected. The contract's
`signLeak` tags the iterations the same way (`signLeakT_eq_signLeak`), so
`signContractT` is `signContract` (`signContractT_eq`), against which
`sign*_verified'` state it.
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `signContract`, with `signLeakT` for `signLeak`. -/
def signContractT (p : Params) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signSig p).contract A
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32)) r
        (bytesAt m' sig p.sigLen))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeakT p (bytesAt m sk p.skLen) (bytesAt m mu 64) (bytesAt m rnd 32))

/-- A state satisfying `signContractT`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x3100 | .x3 => 0x4000 | .x4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (VG.Proof.MlDsa.AArch64.Sign.signContractT p AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack).pre s) :
    (VG.Proof.MlDsa.AArch64.Sign.signK p VG.Proof.MlDsa.AArch64.Sign.signStack).Implies (VG.Proof.MlDsa.AArch64.Sign.signContractT p AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) where
  pre := by sig_implies_pre [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, VG.Proof.MlDsa.AArch64.Sign.signK, AArch64.abi, AArch64.argRegs]
  post := by sig_implies_post [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, VG.Proof.MlDsa.AArch64.Sign.signK, AArch64.abi, AArch64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, VG.Proof.MlDsa.AArch64.Sign.signK, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨hsp, hb, h0, h1, h2, h3, h4⟩ := h
    exact ⟨h0, h1, h2, h3, h4, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) :
    (VG.Proof.MlDsa.AArch64.Sign.signK p VG.Proof.MlDsa.AArch64.Sign.signStack).Implies (VG.Proof.MlDsa.AArch64.Sign.signContractT p AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) := by
  refine VG.Proof.MlDsa.AArch64.Sign.signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using VG.Proof.MlDsa.AArch64.Sign.signSat mlDsa44
  · sig_implies_sat [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using VG.Proof.MlDsa.AArch64.Sign.signSat mlDsa65
  · sig_implies_sat [VG.Proof.MlDsa.AArch64.Sign.signContractT, signSig, AArch64.abi, AArch64.argRegs] [signSat] using VG.Proof.MlDsa.AArch64.Sign.signSat mlDsa87

theorem sign_verified {p : Params} (h3 : VG.Proof.MlDsa.AArch64.Sign.Ok3 p) :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) p) (VG.Proof.MlDsa.AArch64.Sign.signContractT p AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  Verified.of_correct (VG.Proof.MlDsa.AArch64.Sign.sign_correct (keccak := keccak) (VG.Proof.MlDsa.AArch64.Sign.prims_okWith (keccak := keccak)) h3) (VG.Proof.MlDsa.AArch64.Sign.sign_ct (keccak := keccak) (VG.Proof.MlDsa.AArch64.Sign.prims_okWith (keccak := keccak)) h3) (VG.Proof.MlDsa.AArch64.Sign.signK_implies h3)

theorem sign44_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa44) (VG.Proof.MlDsa.AArch64.Sign.signContractT mlDsa44 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign_verified (.inl rfl)

theorem sign65_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa65) (VG.Proof.MlDsa.AArch64.Sign.signContractT mlDsa65 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign_verified (.inr (.inl rfl))

theorem sign87_verifiedWith :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa87) (VG.Proof.MlDsa.AArch64.Sign.signContractT mlDsa87 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign_verified (.inr (.inr rfl))

/-! Against the contract: `signContractT` is `signContract`, whose leakage
tags each iteration as `signLeakT` does (`signLeakT_eq_signLeak`). -/

theorem signContractT_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    VG.Proof.MlDsa.AArch64.Sign.signContractT p A stack = signContract p A stack := by
  unfold VG.Proof.MlDsa.AArch64.Sign.signContractT signContract
  simp only [Sign.signLeakT_eq_signLeak]

theorem sign44_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa44) (signContract mlDsa44 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.signContractT_eq mlDsa44 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack ▸ VG.Proof.MlDsa.AArch64.Sign.sign44_verifiedWith

theorem sign65_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa65) (signContract mlDsa65 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.signContractT_eq mlDsa65 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack ▸ VG.Proof.MlDsa.AArch64.Sign.sign65_verifiedWith

theorem sign87_verifiedWith' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.signWith keccak.callee (VG.Proof.MlDsa.AArch64.Sign.primsWith keccak.callee) mlDsa87) (signContract mlDsa87 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.signContractT_eq mlDsa87 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack ▸ VG.Proof.MlDsa.AArch64.Sign.sign87_verifiedWith

theorem sign44_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign VG.Proof.MlDsa.AArch64.Sign.prims mlDsa44)
      (signContract mlDsa44 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign44_verifiedWith' (keccak := .scalar)

theorem sign65_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign VG.Proof.MlDsa.AArch64.Sign.prims mlDsa65)
      (signContract mlDsa65 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign65_verifiedWith' (keccak := .scalar)

theorem sign87_verified' :
    Verified AArch64.target (Impl.MlDsa.AArch64.Sign.sign VG.Proof.MlDsa.AArch64.Sign.prims mlDsa87)
      (signContract mlDsa87 AArch64.abi VG.Proof.MlDsa.AArch64.Sign.signStack) :=
  VG.Proof.MlDsa.AArch64.Sign.sign87_verifiedWith' (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Sign

end
