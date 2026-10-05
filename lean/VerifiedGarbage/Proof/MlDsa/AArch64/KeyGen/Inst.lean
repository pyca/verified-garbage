import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Sample
import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.NttInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Power2Round
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejBoundedCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpack

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Base`. -/
section

/-!
# ML-DSA key generation and verification on AArch64: the layout registers

The proofs of `vg_mldsa*_keygen` and `vg_mldsa*_verify` use the framework of
`Proof/MlDsa/AArch64/Call/`: these functions keep the addresses of their
buffers in `bases`, which two runs agree on (`SameB`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64

/-- The registers the functions keep the addresses of their buffers in. -/
abbrev bases : List Reg := [.x25, .x26, .x27, .x28]

theorem bases_pres : ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem bases_kept : ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, r ∈ keptRegs := by decide

/-- The buffers of a layout are in the registers `bases`. -/
abbrev LayOk : List (Reg × Nat) → Prop := LayIn VG.Proof.MlDsa.AArch64.KeyGen.bases

/-- Two states whose layout registers and stack pointer agree. -/
abbrev SameB : State → State → Prop := SameIn VG.Proof.MlDsa.AArch64.KeyGen.bases

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallSample`. -/
section

/-!
# ML-DSA key generation on AArch64: calls of `RejBoundedPoly`

For each call of `vg_mldsa_rej_bounded_poly` (the other samplers are in
`Proof/MlDsa/AArch64/Call/Sample.lean`): what it needs of the layout
(`rejBChk`), what it does (`rejBAt_ok`), and that two runs whose layout
registers agree, and whose sampler leaks the same, leak the same (`rejBAt_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def rejBChk (rbs wbs : List (Reg × Nat)) (seed a ss : Ptr) : Bool :=
  sepB rbs wbs seed 66 a 1024 && sepB rbs wbs seed 66 ss 2048 && sepB rbs wbs a 1024 ss 2048 &&
    VG.CallLay.inB (rbs ++ wbs) seed 66 && VG.CallLay.inB (rbs ++ wbs) a 1024 && VG.CallLay.inB (rbs ++ wbs) ss 2048 && VG.CallLay.inB wbs a 1024 &&
    VG.CallLay.inB wbs ss 2048

abbrev rejBArgs (seed : Ptr) (eta : Nat) (a ss : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr seed), (.x1, .imm eta), (.x2, .ptr a), (.x3, .ptr ss)]

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.KeyGen.rejBChk rbs wbs seed a ss = true)
include L hc

theorem rejB_cov : Covers ([⟨pa s seed, 66⟩] ++ [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rejBChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rejB_pre {eta : Nat} (he : eta = 2 ∨ eta = 4) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.rejBArgs seed eta a ss) s s1) :
    (rejBoundedContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 66⟩] [⟨pa s a, 1024⟩, ⟨pa s ss, 2048⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rejBChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1]
  simp only [Arg.val]
  rw [imm32 (by omega)]
  cpre L
  exact he

end

theorem rejB_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (eta : Nat) (c4 : VG.CallLay.inB bs seed 66 = true)
    (c5 : VG.CallLay.inB bs a 1024 = true) (c6 : VG.CallLay.inB bs ss 2048 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.rejBArgs seed eta a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩,
    ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rejBAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.KeyGen.rejBChk rbs wbs seed a ss = true) {eta : Nat} (he : eta = 2 ∨ eta = 4) :
    WP isa (rejBoundedAt P ss seed eta a) s fun s' => PPostB S s s' [(a, 1024), (ss, 2048)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => (rejBoundedPoly eta b.rejBounded (bytesAt s.mem (pa s seed) 66)).map toRq)
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (pa s a)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rejBChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.rejB_args L.ok eta c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.rejB_pre L hc he h1) (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov L hc).1 (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (by omega)] at hq
  exact hq

theorem rejBAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.KeyGen.rejBChk rbs wbs seed a ss = true)
    {eta : Nat} (he : eta = 2 ∨ eta = 4) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      rejBoundedLeak eta (bytesAt x.mem (pa x seed) 66) = rejBoundedLeak eta (bytesAt y.mem (pa y seed) 66) ∧
      VG.Proof.MlDsa.AArch64.KeyGen.SameB x y) :
    RelCT isa Q (rejBoundedAt P ss seed eta a) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rejBChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.rejB_args hB eta c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.rejB_pre Lx hc he h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.rejB_pre Ly hc he h2
  · sig_pub [rejBoundedContract, rejBoundedSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    rw [imm32 (by omega)]
    exact ⟨e.2, hsd, e.pa hb.1, trivial, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.rejB_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound`. -/
section

/-!
# ML-DSA key generation and verification on AArch64: calls of the rounding primitives

For each call of `vg_mldsa_power2round` and `vg_mldsa_use_hint` (the norm is
in `Proof/MlDsa/AArch64/Call/Round.lean`): what it needs of the layout
(`…Chk`), what it does (`…_ok`), and that two runs whose layout registers
agree leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Power2Round` -/

def p2rChk (rbs wbs : List (Reg × Nat)) (t t1 t0 : Ptr) : Bool :=
  sepB rbs wbs t 1024 t1 1024 && sepB rbs wbs t 1024 t0 1024 && sepB rbs wbs t1 1024 t0 1024 &&
    VG.CallLay.inB (rbs ++ wbs) t 1024 && VG.CallLay.inB (rbs ++ wbs) t1 1024 && VG.CallLay.inB (rbs ++ wbs) t0 1024 && VG.CallLay.inB wbs t1 1024 &&
    VG.CallLay.inB wbs t0 1024

abbrev p2rArgs (t t1 t0 : Ptr) : List (Reg × Arg) := [(.x0, .ptr t), (.x1, .ptr t1), (.x2, .ptr t0)]

theorem p2r_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {t t1 t0 : Ptr} (c4 : VG.CallLay.inB bs t 1024 = true)
    (c5 : VG.CallLay.inB bs t1 1024 = true) (c6 : VG.CallLay.inB bs t0 1024 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.p2rArgs t t1 t0, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.KeyGen.p2rChk rbs wbs t t1 t0 = true)
include L hc

theorem p2r_cov : Covers ([⟨pa s t, 1024⟩] ++ [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem p2r_pre (hr : Reduced s.mem (pa s t)) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.p2rArgs t t1 t0) s s1) :
    (power2RoundContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s t, 1024⟩] [⟨pa s t1, 1024⟩, ⟨pa s t0, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.p2rChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  cpre L
  exact hr

end

theorem p2rAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.KeyGen.p2rChk rbs wbs t t1 t0 = true) (hr : Reduced s.mem (pa s t)) :
    WP isa (power2RoundAt P t t1 t0) s fun s' => PPostB S s s' [(t1, 1024), (t0, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s t1) ((polyAt s.mem (pa s t)).map fun c => (VG.Spec.MlDsa.power2Round c).1.toNat) ∧
      PolyIs s'.mem (pa s t0) ((polyAt s.mem (pa s t)).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.p2r_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.p2r_pre L hc hr h1) (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov L hc).1 (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq

theorem p2rAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {t t1 t0 : Ptr} (hc : VG.Proof.MlDsa.AArch64.KeyGen.p2rChk rbs wbs t t1 t0 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x t) ∧ Reduced y.mem (pa y t) ∧
      VG.Proof.MlDsa.AArch64.KeyGen.SameB x y) :
    RelCT isa Q (power2RoundAt P t t1 t0) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : t.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ t1.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ t0.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.p2r_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.p2r_pre Lx hc rx h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.p2r_pre Ly hc ry h2
  · sig_pub [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.p2r_cov Ly hc).2

/-! ## `UseHint` -/

def useHintChk (rbs wbs : List (Reg × Nat)) (h r out : Ptr) : Bool :=
  sepB rbs wbs h 1024 out 1024 && sepB rbs wbs r 1024 out 1024 &&
    VG.CallLay.inB (rbs ++ wbs) h 1024 && VG.CallLay.inB (rbs ++ wbs) r 1024 && VG.CallLay.inB (rbs ++ wbs) out 1024 && VG.CallLay.inB wbs out 1024

abbrev useHintArgs (h r : Ptr) (g2 : Nat) (out : Ptr) : List (Reg × Arg) :=
  [(.x0, .ptr h), (.x1, .ptr r), (.x2, .imm g2), (.x3, .ptr out)]

theorem useHint_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {h r out : Ptr} (g2 : Nat) (c3 : VG.CallLay.inB bs h 1024 = true)
    (c4 : VG.CallLay.inB bs r 1024 = true) (c5 : VG.CallLay.inB bs out 1024 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.useHintArgs h r g2 out, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c3), by decide⟩, ⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_kept L c5), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h r out : Ptr}
  (hc : VG.Proof.MlDsa.AArch64.KeyGen.useHintChk rbs wbs h r out = true)
include L hc

theorem useHint_cov : Covers ([⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] ++ [⟨pa s out, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s out, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.useHintChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, c3, c4, _, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c3) (L.cR c4)) (Covers.right (L.cW c6)), L.cW c6⟩

theorem useHint_pre {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) {s1 : State}
    (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.useHintArgs h r g2 out) s s1) :
    (useHintContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s h, 1024⟩, ⟨pa s r, 1024⟩] [⟨pa s out, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.useHintChk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, _⟩ := hc
  sig_pre [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.sp h1, Args.mem h1]
  simp only [Arg.val]
  rw [imm32 (gamma2_lt hg)]
  cpre L
  exacts [hg, hr]

end

theorem useHintAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.useHint (useHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {h r out : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.KeyGen.useHintChk rbs wbs h r out = true) {g2 : Nat} (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (pa s r)) :
    WP isa (useHintAt P h r g2 out) s fun s' => PPostB S s s' [(out, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s out) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint g2 hj rj).toNat)
        ((hintAt s.mem (pa s h) 1).headD (Vector.replicate n false)) (polyAt s.mem (pa s r))) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.useHintChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, c3, c4, c5, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.useHint_args L.ok g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.useHint_pre L hc hg hr h1) (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov L hc).1 (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val] at hq
  rw [imm32 (gamma2_lt hg)] at hq
  exact hq

theorem useHintAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.useHint (useHintContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {h r out : Ptr} (hc : VG.Proof.MlDsa.AArch64.KeyGen.useHintChk rbs wbs h r out = true)
    {g2 : Nat} (hg : g2 ∈ gamma2s) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x r) ∧ Reduced y.mem (pa y r) ∧
      VG.Proof.MlDsa.AArch64.KeyGen.SameB x y) :
    RelCT isa Q (useHintAt P h r g2 out) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.useHintChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, c3, c4, c5, _⟩ := hc'
  have hb : h.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ r.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ out.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c3, ptr_bs hB c4, ptr_bs hB c5⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.useHint_args hB g2 c3 c4 c5) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.useHint_pre Lx hc hg rx h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.useHint_pre Ly hc hg ry h2
  · sig_pub [useHintContract, useHintSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.r3 h2,
      Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, trivial, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov Ly hc).1
  · rw [e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.useHint_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallPack`. -/
section

/-!
# ML-DSA key generation and verification on AArch64: calls of the decodings

For each call of `vg_mldsa_unpack_t1` and `vg_mldsa_hint_bit_unpack` (the
other encodings are in `Proof/MlDsa/AArch64/Call/Pack.lean`): what it needs of
the layout (`…Chk`), what it does (`…_ok`), and that two runs whose layout
registers agree (and whose hint agrees) leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `t₁` -/

abbrev t1Args (v f : Ptr) : List (Reg × Arg) := [(.x0, .ptr v), (.x1, .ptr f)]

theorem t1_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {v f : Ptr} (c2 : VG.CallLay.inB bs v 320 = true)
    (c3 : VG.CallLay.inB bs f 1024 = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.t1Args v f, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c2), by decide⟩, ⟨ptr_ok (ptr_kept L c3), by decide⟩⟩

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr}
  (hc : rwChk rbs wbs v 320 f 1024 = true)
include L hc

theorem t1_pre {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.t1Args v f) s s1) :
    (unpackT1Contract AArch64.abi S).pre (s1.callEntry.withRegions [⟨pa s v, 320⟩] [⟨pa s f, 1024⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem t1At_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {v f : Ptr}
    (hc : rwChk rbs wbs v 320 f 1024 = true) :
    WP isa (unpackT1At P v f) s fun s' => PPostB S s s' [(f, 1024)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      PolyIs s'.mem (pa s f) ((simpleBitUnpack (bytesAt s.mem (pa s v) 320) t1Max).map fun c => ofInt (c * 2 ^ VG.Spec.MlDsa.d : Nat)) := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.t1_args L.ok c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.t1_pre L hc h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem t1At_tr {S : Nat} {P : Prims} (C : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {v f : Ptr}
    (hc : rwChk rbs wbs v 320 f 1024 = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ VG.Proof.MlDsa.AArch64.KeyGen.SameB x y) :
    RelCT isa Q (unpackT1At P v f) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : v.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ f.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.t1_args hB c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.t1_pre Lx hc h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.t1_pre Ly hc h2
  · sig_pub [unpackT1Contract, unpackT1Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r0 h2, Args.r1 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hbs.1, e.pa hbs.2⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Ly hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Ly hc).2

/-! ## `HintBitUnpack` -/

abbrev huArgs (y : Ptr) (len omega : Nat) (h : Ptr) (hlen : Nat) : List (Reg × Arg) :=
  [(.x0, .ptr y), (.x1, .imm len), (.x2, .imm omega), (.x3, .ptr h), (.x4, .imm hlen)]

theorem hu_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {y h : Ptr} (len omega hlen : Nat) (c2 : VG.CallLay.inB bs y len = true)
    (c3 : VG.CallLay.inB bs h (hlen * 4) = true) : ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.huArgs y len omega h hlen, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c2), by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, by decide⟩,
    ⟨ptr_ok (ptr_kept L c3), by decide⟩, ⟨trivial, by decide⟩⟩

/-- What `HintBitUnpack` asks of its arguments. -/
structure HuOk (len omega hlen : Nat) : Prop where
  hp : (omega, len - omega) ∈ hintParams
  hle : omega ≤ len
  hhl : hlen = 256 * (len - omega)
  hlt : len < 2 ^ 32 ∧ omega < 2 ^ 32 ∧ hlen < 2 ^ 32

section
variable {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
  (hc : rwChk rbs wbs y len h (hlen * 4) = true)
include L hc

theorem hu_pre (hb : VG.Proof.MlDsa.AArch64.KeyGen.HuOk len omega hlen) {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.huArgs y len omega h hlen) s s1) :
    (hintBitUnpackContract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s y, len⟩] [⟨pa s h, hlen * 4⟩]) := by
  obtain ⟨c1, c2, c3⟩ := rw_parts hc
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.sp h1]
  simp only [Arg.val, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega),
    Nat.mod_eq_of_lt (show hlen < 2 ^ 64 by have := hb.hlt.2.2; omega)]
  cpre L
  exacts [hb.hp, hb.hle, hb.hhl]

end

theorem huAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {y h : Ptr} {len omega hlen : Nat}
    (hc : rwChk rbs wbs y len h (hlen * 4) = true) (hb : VG.Proof.MlDsa.AArch64.KeyGen.HuOk len omega hlen) :
    WP isa (hintUnpackAt P y len omega h hlen) s fun s' => PPostB S s s' [(h, hlen * 4)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      match VG.Spec.MlDsa.hintBitUnpack omega (len - omega) (bytesAt s.mem (pa s y) len) with
      | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (pa s h) (len - omega) hint
      | none => (s'.gpr .x0).setWidth 32 = 0 := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.hu_args L.ok len omega hlen c2 c3)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.hu_pre L hc hb h1) (rw_cov L hc).1 (rw_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.mem h1] at hq
  simp only [Arg.val, imm32 hb.hlt.2.1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega)] at hq
  exact hq

theorem huAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {y h : Ptr} {len omega hlen : Nat}
    (hc : rwChk rbs wbs y len h (hlen * 4) = true) (hb : VG.Proof.MlDsa.AArch64.KeyGen.HuOk len omega hlen) {Q : State → State → Prop}
    (hQ : ∀ x z, Q x z → Lay S rbs wbs x ∧ Lay S rbs wbs z ∧
      bytesAt x.mem (pa x y) len = bytesAt z.mem (pa z y) len ∧ VG.Proof.MlDsa.AArch64.KeyGen.SameB x z) :
    RelCT isa Q (hintUnpackAt P y len omega h hlen) fun _ _ => True := by
  obtain ⟨_, c2, c3⟩ := rw_parts hc
  have hbs : y.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ h.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c2, ptr_bs hB c3⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.hu_args hB len omega hlen c2 c3) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x z x1 z1 hp h1 h2 => ?_
  obtain ⟨Lx, Lz, hy, e⟩ := hQ x z hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.hu_pre Lx hc hb h1, ?_, ?_, (rw_cov Lx hc).1, (rw_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.hu_pre Lz hc hb h2
  · sig_pub [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r3 h1, Args.r4 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2,
      Args.r3 h2, Args.r4 h2, Args.sp h1, Args.sp h2, Args.mem h1, Args.mem h2]
    simp only [Arg.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by have := hb.hlt.1; omega)]
    exact ⟨e.2, by rw [hy], e.pa hbs.1, trivial, trivial, e.pa hbs.2, trivial⟩
  · rw [e.pa hbs.1, e.pa hbs.2]; exact (rw_cov Lz hc).1
  · rw [e.pa hbs.2]; exact (rw_cov Lz hc).2

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks`. -/
section

/-!
# ML-DSA on AArch64: the blocks between calls

Besides those of `Proof/MlDsa/AArch64/Call/Blocks.lean`: the masking of a
sampled polynomial by its sampler's result (`mask_ok`): kept if the sampler
succeeded, zero if it failed.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrw wp_strw wp_addImm wp_subImm
  count_loop)
open VG.Spec.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_sub32 {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sub .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

end

/-! ## Masking a sampled polynomial -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

/-- The coefficients after masking with the 32 bits `r`, 0 or 1. -/
theorem and_mask {r : BitVec 32} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    x &&& (BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [Proof.MlDsa.KeyGen.ifp rfl, show (BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (1 : BitVec 32))).setWidth 32 =
      BitVec.allOnes 32 by decide]
    exact BitVec.and_allOnes

abbrev maskBody : List Instr := [.ldr .w .x9 .x1 0, .logic .and .w .x9 .x9 .x8, .str .w .x9 .x1 0,
  .addImm .x .x1 .x1 4, .subImm .x .x2 .x2 1]

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1) 4) (h1 : InRegions s.wr (s.gpr .x1) 4) :
    WP isa (.block VG.Proof.MlDsa.AArch64.KeyGen.maskBody) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .x1) (s.mem.readW (s.gpr .x1) 32 &&& (s.gpr .x8).setWidth 32) ∧
        s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 4 ∧ s'.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 1) ∧
      VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x9] s s' := by
  have e0 : s.gpr .x1 + BitVec.ofNat 64 0 = s.gpr .x1 := BitVec.add_zero _
  refine wp_ldrw (a := s.gpr .x1) (by decide) e0 h0 fun s₁ h₁ e₁ => wp_and32 fun s₂ h₂ e₂ =>
    wp_strw (a := s.gpr .x1) (by decide) (by rw [h₂.get .x1, h₁.get .x1, e0]) (by rw [h₂.wr, h₁.wr]; exact h1)
      fun s₃ h₃ => wp_addImm (by decide) fun s₄ h₄ e₄ => wp_subImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono (by simp)⟩
  · rw [h₅.mem, h₄.mem, h₃.mem, e₂, h₂.mem, h₁.mem, e₁, h₁.get .x8]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and]
  · rw [h₅.get .x1, e₄, show s₃.gpr .x1 = s₂.gpr .x1 by rw [h₃.gpr], h₂.get .x1, h₁.get .x1]
  · rw [e₅, h₄.get .x2, show s₃.gpr .x2 = s₂.gpr .x2 by rw [h₃.gpr], h₂.get .x2, h₁.get .x2]

theorem off_add4 (b : Addr) (i : Nat) : b + BitVec.ofNat 64 (4 * i) + BitVec.ofNat 64 4 = b + BitVec.ofNat 64 (4 * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2

theorem ofNat_sub1 {i : Nat} (h : i < 256) : BitVec.ofNat 64 (256 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (256 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem mask_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : VG.CallLay.inB wbs a 1024 = true) (hin : VG.CallLay.inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (VG.Impl.MlDsa.AArch64.KeyGen.mask a) s fun s' => PPostB S s s' [(a, 1024)] ∧ VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s' ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i =
        if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 1024 := L.inW hw
  have hn : (pa s a).toNat + 1024 ≤ 2 ^ 64 := L.nwp hin
  have hb : a.1 ∈ keptRegs := L.ptrBs hin
  have h1 : a.1 ≠ .x1 := by intro e; rw [e] at hb; revert hb; decide
  have h8 : a.1 ≠ .x8 := by intro e; rw [e] at hb; revert hb; decide
  unfold VG.Impl.MlDsa.AArch64.KeyGen.mask
  refine WP.seq ?_
  refine wp_movz fun s₁ h₁ e₁ => VG.Proof.MlDsa.AArch64.KeyGen.wp_sub32 fun s₂ h₂ e₂ => lea_ok h1.symm a.2 fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ : VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s₄ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono (by simp)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x8 : s₄.gpr .x8 = BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (s.gpr .x0).setWidth 32) := by
    rw [h₄.get .x8, h₃.get .x8, e₂, e₁, h₁.get .x0]; rfl
  have x1 : s₄.gpr .x1 = pa s a := by
    rw [h₄.get .x1, e₃, h₂.get a.1 (by simpa using h8), h₁.get a.1 (by simpa using h8)]
  refine WP.mono (count_loop (cr := .x2) (n := 256) (by decide) (fun i s' =>
      s'.gpr .x1 = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .x2 = BitVec.ofNat 64 (256 - i) ∧
      s'.gpr .x8 = s₄.gpr .x8 ∧ VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s' ∧ Frame [⟨pa s a, 1024⟩] s.mem s'.mem ∧
      ∀ j < 256, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s₄.gpr .x8).setWidth 32 else coeffAt s.mem (pa s a) j)
    (fun i hi s' ⟨e1, e2, e8, kk, hf, hc⟩ => ?_)
    ⟨by rw [x1, Nat.mul_zero, BitVec.add_zero], by rw [e₄]; rfl, rfl, k₄, by rw [m₄]; exact Frame.refl _ _,
      fun j _ => by rw [Proof.MlDsa.KeyGen.ifn (Nat.not_lt_zero j), m₄]⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨postB_of_keep kk (by decide) hf, kk, fun j hj => ?_⟩
  · have hc4 : (⟨pa s a, 1024⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hinw : InRegions s'.wr (s'.gpr .x1) 4 := by
      rw [kk.wr, e1]; exact VG.CallLay.inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .x1) 4 := VG.Proof.MlKem.AArch64.in_rd_wr hinw
    refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.maskBody_ok s' hin0 hinw) fun s'' ⟨⟨hm, e1', e2'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [k'.get .x8, e8],
      (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [e1', e1, VG.Proof.MlDsa.AArch64.KeyGen.off_add4]
    · rw [e2', e2, VG.Proof.MlDsa.AArch64.KeyGen.ofNat_sub1 hi]
    · rw [hm, e1]; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, e1, VG.Proof.MlDsa.AArch64.KeyGen.coeffAt_writeW32 _ _ hj (by omega), e8]
      by_cases e : i = j
      · subst e
        rw [Proof.MlDsa.KeyGen.ifp rfl, Proof.MlDsa.KeyGen.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [Proof.MlDsa.KeyGen.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [Proof.MlDsa.KeyGen.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [Proof.MlDsa.KeyGen.ifp hji, Proof.MlDsa.KeyGen.ifp (by omega)]
        · rw [Proof.MlDsa.KeyGen.ifn hji, Proof.MlDsa.KeyGen.ifn (by omega)]
    · rw [e2', e2, VG.Proof.MlDsa.AArch64.KeyGen.ofNat_sub1 hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hc j hj, Proof.MlDsa.KeyGen.ifp hj, x8, VG.Proof.MlDsa.AArch64.KeyGen.and_mask hr]

/-! ## After a sampler -/

/-- The result `w0` of a sampler ANDed into `x24`, and its output masked with it. -/
theorem tail_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : VG.CallLay.inB wbs a 1024 = true) (hin : VG.CallLay.inB (rbs ++ wbs) a 1024 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask a)) s fun s' => PPostB S s s' [(a, 1024)] ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 ∧
      ∀ i < 256, coeffAt s'.mem (pa s a) i = if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  refine WP.seq (WP.mono (and24_ok s) fun s₁ ⟨o₁, e₁⟩ => ?_)
  have P₁ : PostB S s s₁ [] := postB_of_keep o₁.keep (by decide) (by rw [o₁.mem]; exact Frame.refl _ _)
  have L₁ := L.post P₁
  have x0 : s₁.gpr .x0 = s.gpr .x0 := o₁.get .x0
  rw [← x0] at hr
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.mask_ok L₁ hw hin hr) fun s' ⟨P', k', hc⟩ => ⟨?_, by rw [k'.get .x24, e₁], ?_⟩
  · refine PostB.trans P₁ ?_ (fun _ h => absurd h List.not_mem_nil) fun _ h => h
    have e : ([(a, 1024)] : List (Ptr × Nat)).map (toR s₁) = [(a, 1024)].map (toR s) :=
      map_toR_post P₁ (fun w hw => by rw [List.mem_singleton.mp hw]; exact L.ptrBs hin)
    rw [← e]; exact P'
  · intro i hi
    rw [← P₁.pa (L.ptrBs hin), hc i hi, x0, o₁.mem]

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4`. -/
section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
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
  (hc : VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk rbs wbs seed a ss = true)
include L hc

theorem rej4_cov : Covers ([⟨pa s seed, 136⟩] ++ [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩] s.wr := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨_, _, _, c4, _, _, c7, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : VG.Proof.MlDsa.AArch64.Args (VG.Proof.MlDsa.AArch64.KeyGen.rej4Args seed a ss) s s1) :
    (rejNTT4Contract AArch64.abi S).pre
      (s1.callEntry.withRegions [⟨pa s seed, 136⟩] [⟨pa s a, 4096⟩, ⟨pa s ss, 8192⟩]) := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk, Bool.and_eq_true, and_assoc] at hc
  obtain ⟨c1, c2, c3, c4, c5, c6, _, _⟩ := hc
  sig_pre [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.sp h1]
  simp only [Arg.val]
  cpre L

end

theorem rej4_args {B : List Reg} {bs : List (Reg × Nat)} (L : LayIn B bs) {seed a ss : Ptr} (c4 : VG.CallLay.inB bs seed 136 = true)
    (c5 : VG.CallLay.inB bs a 4096 = true) (c6 : VG.CallLay.inB bs ss 8192 = true) :
    ∀ x ∈ VG.Proof.MlDsa.AArch64.KeyGen.rej4Args seed a ss, x.2.Ok ∧ x.1 ∈ argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨ptr_ok (ptr_kept L c4), by decide⟩, ⟨ptr_ok (ptr_kept L c5), by decide⟩, ⟨ptr_ok (ptr_kept L c6), by decide⟩⟩

theorem rej4At_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {seed a ss : Ptr}
    (hc : VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk rbs wbs seed a ss = true) :
    WP isa (rej4At P ss seed a) s fun s' => PPostB S s s' [(a, 4096), (ss, 8192)] ∧ s'.gpr .x24 = s.gpr .x24 ∧
      ((s'.gpr .x0).setWidth 32 = 1 → ∀ k < 4,Reduced s'.mem (poly4 (pa s a) k)) ∧
      (((s'.gpr .x0).setWidth 32 = 1 ∧ ∀ k < 4,∃ b : Bounds,rejNTTPoly b.rejNTT
          (seed4 s.mem (pa s seed) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        ((s'.gpr .x0).setWidth 32 = 0 ∧ ∃ k < 4,rejNTTPoly minBounds.rejNTT
          (seed4 s.mem (pa s seed) k) = none)) := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (VG.Proof.MlDsa.AArch64.KeyGen.rej4_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.AArch64.KeyGen.rej4_pre L hc h1) (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov L hc).1 (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.mem h1] at hq
  exact hq

theorem rej4At_tr {S : Nat} {P : Prims} (C : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 136 = bytesAt y.mem (pa y seed) 136 ∧ VG.Proof.MlDsa.AArch64.KeyGen.SameB x y) :
    RelCT isa Q (rej4At P ss seed a) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ a.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases ∧ ss.1 ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (VG.Proof.MlDsa.AArch64.KeyGen.rej4_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, VG.Proof.MlDsa.AArch64.KeyGen.rej4_pre Lx hc h1, ?_, ?_, (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov Lx hc).1, (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact VG.Proof.MlDsa.AArch64.KeyGen.rej4_pre Ly hc h2
  · sig_pub [rejNTT4Contract, rejNTT4Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (VG.Proof.MlDsa.AArch64.KeyGen.rej4_cov Ly hc).2


end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Top`. -/
section

/-!
# ML-DSA on AArch64: entry and exit

What the top-level functions keep from their entry state `σ` on (`Top`): the
permissions and the stack pointer, their four arguments in `x25`–`x28`, the
callee-saved registers they never write, and their caller's `x24`–`x28` and
`x30` saved in `scratch`. The prologue establishes it (`pro_ok`), every piece
keeps it (`Top.step`), and the epilogue restores the caller's registers from
it (`epi_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm wp_ldrx in_rd_wr)
open VG.Spec.Sha3 (bytesAt)

/-- The callee-saved registers the functions never write. -/
abbrev untouched : List Reg := [.x19, .x20, .x21, .x22, .x23]

/-- What the functions keep from their entry state `σ` on. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x25 : s.gpr .x25 = σ.gpr .x0
  x26 : s.gpr .x26 = σ.gpr .x1
  x27 : s.gpr .x27 = σ.gpr .x2
  x28 : s.gpr .x28 = σ.gpr .x3
  cs : ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched, s.gpr r = σ.gpr r
  saved : ∀ k < 6, s.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0)
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

theorem untouched_kept : ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched, r ∈ keptRegs := by decide

/-- The saved registers, in `scratch`. -/
abbrev svP : Ptr := sc SV

/-- `Top` is kept by a piece that keeps the saved registers. -/
theorem Top.step {S : Nat} {rbs wbs : List (Reg × Nat)} {σ s s' : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s) (L : Lay S rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws VG.Proof.MlDsa.AArch64.KeyGen.svP 48 = true) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s' := by
  have hsv : ∀ k < 6, s'.mem.readW (pa s' VG.Proof.MlDsa.AArch64.KeyGen.svP + BitVec.ofNat 64 (8 * k)) 64 =
      s.mem.readW (pa s VG.Proof.MlDsa.AArch64.KeyGen.svP + BitVec.ofNat 64 (8 * k)) 64 := fun k hk => by
    rw [hP.pa (L.keepBs hc)]
    obtain ⟨n, hn, hl⟩ := VG.CallLay.inB_spec (keepB_in hc)
    refine hP.frame.readW (r := ⟨pa s VG.Proof.MlDsa.AArch64.KeyGen.svP, 48⟩) (Offset.contains_base _ (by omega) (by omega))
      (L.fdisj hc) (by decide)
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp, by rw [hP.bs _ (by decide), h.x25],
    by rw [hP.bs _ (by decide), h.x26], by rw [hP.bs _ (by decide), h.x27], by rw [hP.bs _ (by decide), h.x28],
    fun r hr => by rw [hP.cs r (VG.Proof.MlDsa.AArch64.KeyGen.untouched_kept r hr), h.cs r hr], fun k hk => ?_,
    fun r hr => (hP.vcs r hr).trans (h.vcs r hr)⟩
  have e : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s VG.Proof.MlDsa.AArch64.KeyGen.svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e' : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s' VG.Proof.MlDsa.AArch64.KeyGen.svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, hP.bs _ (by decide), h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e', hsv k hk, ← e, h.saved k hk]

/-! ## The prologue -/

theorem pro_eq : VG.Impl.MlDsa.AArch64.KeyGen.pro = (List.range 6).map (fun k => .str .x (savedRegs.getD k .x0) .x3 (SV + 8 * k)) ++
    ([.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0, .addImm .x .x28 .x3 0,
      .movz .x .x24 1 0] : List Instr) := rfl

theorem pro_ok {σ : State} (hin : ∀ k < 6, InRegions σ.wr (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8) :
    WP isa (.block VG.Impl.MlDsa.AArch64.KeyGen.pro) σ fun s => VG.Proof.MlDsa.AArch64.KeyGen.Top σ s ∧ s.gpr .x24 = 1 ∧
      Frame [⟨σ.gpr .x3 + BitVec.ofNat 64 SV, 48⟩] σ.mem s.mem := by
  rw [VG.Proof.MlDsa.AArch64.KeyGen.pro_eq, WP.block_append_iff]
  refine WP.mono (WP.preservedV (Proof.MlKem.AArch64.KeyGen.saves_ok
    (σ.gpr .x3) .x3 SV savedRegs (by decide) (by decide) 6
    (by decide) rfl hin) (by lit_decide)) fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ e₂ => wp_addImm (by decide) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_addImm (by decide) fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have o : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  refine ⟨⟨by rw [o.rd, r₁], by rw [o.wr, w₁], by rw [o.sp, p₁], ?_, ?_, ?_, ?_, fun r hr => ?_, fun k hk => ?_,
    fun r hr => (o.vcs r hr).trans (hv₁ r hr)⟩,
    by rw [e₆]; rfl, by rw [o.mem]; exact f₁⟩
  · rw [h₆.get .x25, h₅.get .x25, h₄.get .x25, h₃.get .x25, e₂, BitVec.add_zero, g₁]
  · rw [h₆.get .x26, h₅.get .x26, h₄.get .x26, e₃, BitVec.add_zero, h₂.get .x1, g₁]
  · rw [h₆.get .x27, h₅.get .x27, e₄, BitVec.add_zero, h₃.get .x2, h₂.get .x2, g₁]
  · rw [h₆.get .x28, e₅, BitVec.add_zero, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]
  · rw [o.get r (by revert r; decide), g₁]
  · rw [o.mem]; exact z₁ k hk

/-! ## The epilogue -/

theorem epi_ok {σ s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s) (hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48) :
    WP isa (.block VG.Impl.MlDsa.AArch64.KeyGen.epi) s fun s' => abiPreserved σ s' ∧ s'.gpr .x0 = s.gpr .x24 ∧ s'.mem = s.mem := by
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 ∧
      w.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by
        rw [hr, hw, show σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 SV +
          BitVec.ofNat 64 (8 * k) by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
        exact VG.CallLay.inRegions_sub hin (by omega) (by decide), by rw [hm]; exact h.saved k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w'.rd = s.rd ∧ w'.wr = s.wr ∧ w'.mem = s.mem ∧ w'.gpr .x28 = σ.gpr .x3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_addImm (by decide) fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, h.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 5)) (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 0)) (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 1)) (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 2)) (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 3)) (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 4)) (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] s s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, h.sp], fun r hr => (o₇.vcs r hr).trans (h.vcs r hr)⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ savedRegs
    · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · have hu : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by revert r ho hr; decide
      rw [o₇.get r (by revert r hu; decide), h.cs r hu]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, BitVec.add_zero]

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk`. -/
section

/-!
# ML-DSA on AArch64: what the proofs need of the primitives

`PrimsOk P S`: each primitive of `P` is correct and constant time under its
shared contract with `S` bytes of stack, and its frames use at most those `S`
bytes (`CalleeOk`, from its `Verified` proof by `CalleeOk.of_verified`); `S`
is at least the 16 bytes the sponge functions' frames use. The proofs of
`vg_mldsa*_keygen` and `vg_mldsa*_verify` hold for any such `P`, with their
contracts' stack `S`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa

/-- Implementations of the primitives, correct and constant time with `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  s16 : 16 ≤ S
  sl : S < 2 ^ 16
  ntt : CalleeOk S P.ntt (nttContract AArch64.abi S)
  invNtt : CalleeOk S P.invNtt (nttInvContract AArch64.abi S)
  mul : CalleeOk S P.mul (mulContract AArch64.abi S)
  mulAdd : CalleeOk S P.mulAdd (mulAddContract AArch64.abi S)
  add : CalleeOk S P.add (addContract AArch64.abi S)
  sub : CalleeOk S P.sub (subContract AArch64.abi S)
  rejNtt : CalleeOk S P.rejNtt (rejNTTContract AArch64.abi S)
  rej4 : CalleeOk S P.rej4 (rejNTT4Contract AArch64.abi S)
  rejBounded : CalleeOk S P.rejBounded (rejBoundedContract AArch64.abi S)
  ball : CalleeOk S P.ball (sampleInBallContract AArch64.abi S)
  power2Round : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S)
  useHint : CalleeOk S P.useHint (useHintContract AArch64.abi S)
  normLt : CalleeOk S P.normLt (normLtContract AArch64.abi S)
  simpleBitPack : CalleeOk S P.simpleBitPack (simpleBitPackContract AArch64.abi S)
  bitPack : CalleeOk S P.bitPack (bitPackContract AArch64.abi S)
  bitUnpack : CalleeOk S P.bitUnpack (bitUnpackContract AArch64.abi S)
  unpackT1 : CalleeOk S P.unpackT1 (unpackT1Contract AArch64.abi S)
  hintUnpack : CalleeOk S P.hintUnpack (hintBitUnpackContract AArch64.abi S)

theorem PrimsOk.s64 {P : Prims} {S : Nat} (h : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) : S < 2 ^ 64 := by have := h.sl; omega

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay`. -/
section

/-!
# ML-DSA key generation on AArch64: parameters and buffers

The facts about the parameter sets the proof uses (`PFacts`), the layout of
the buffers of key generation (`seed` in `x25`, read; `scratch`, `pk` and `sk`
in `x28`, `x26` and `x27`, written: `kgR`, `kgW p`), which the contract's
precondition gives from the prologue on (`kgLay`), and the checks of pointers
into them, for any parameter set, which `lay` proves from the offsets by
`omega`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by simp, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

theorem scr_eq (p : Params) : VG.Proof.MlDsa.AArch64.KeyGen.scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.scrLen, scratchWords]; omega

theorem PFacts.scr {p : Params} (_ : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : VG.Proof.MlDsa.AArch64.KeyGen.scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p

theorem PFacts.small {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : VG.Proof.MlDsa.AArch64.KeyGen.scrLen p < 2 ^ 32 ∧ p.pkLen < 2 ^ 32 ∧ p.skLen < 2 ^ 32 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hls : lenS p * (p.ℓ + p.k) ≤ 128 * 15 := by
    rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by rw [VG.Proof.MlDsa.AArch64.KeyGen.scr_eq]; omega, by rw [hF.pk]; omega, by rw [hF.sk, oT0]; omega⟩

/-! ## The layout -/

/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.x25, 32)]
/-- `scratch`, `pk` and `sk`. -/
abbrev kgW (p : Params) : List (Reg × Nat) := [(.x28, VG.Proof.MlDsa.AArch64.KeyGen.scrLen p), (.x26, p.pkLen), (.x27, p.skLen)]

theorem le_of_wfP {S sp : Nat} (h : wfP S sp) : S ≤ sp := by
  unfold wfP at h; split at h <;> omega

/-- The stack below the stack pointer is apart from the regions, from the
contract's evaluated precondition. -/
theorem below_of_resv {S : Nat} {sp : Addr} {a b c d : Region}
    (h : Sig.conj ((stackBelow sp S).map fun r => [r.Disjoint a, r.Disjoint b, r.Disjoint c, r.Disjoint d]).flatten) :
    (below sp S).Disjoint a ∧ (below sp S).Disjoint b ∧ (below sp S).Disjoint c ∧ (below sp S).Disjoint d := by
  rcases S with _ | S
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> exact fun x h _ => by simp [Region.Contains] at h
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Sig.conj_cons] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem inR_self {X : List Region} {r : Region} (h : r ∈ X) : InRegions X r.base r.len :=
  ⟨r, h, Region.contains_self _ _⟩

theorem kgLay {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} {σ s : State}
    (hp : (Spec.MlDsa.keyGenContract p AArch64.abi S).pre σ) (h : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s) : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) s := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp
  obtain ⟨hwf, hrd, hwr, d01, d02, d03, d12, d13, d23, hres, n0, n1, n2, n3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := VG.Proof.MlDsa.AArch64.KeyGen.below_of_resv hres
  have hS : S ≤ σ.sp.toNat := VG.Proof.MlDsa.AArch64.KeyGen.le_of_wfP hwf
  have hsm := hF.small
  have e25 := h.x25; have e26 := h.x26; have e27 := h.x27; have e28 := h.x28
  have mrd : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr => by
    rw [h.rd, h.wr]; exact VG.Proof.MlDsa.AArch64.KeyGen.inR_self hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [h.sp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl)
    exacts [by decide, hsm.1, hsm.2.1, hsm.2.2]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) b' (rfl | rfl | rfl | rfl) hne hw <;>
      first
        | exact absurd rfl hne
        | simp only [e25, e26, e27, e28]
          first
            | with_reducible assumption
            | exact Region.Disjoint.symm (by assumption)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28, h.sp] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28] <;> with_reducible assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    · exact mrd ⟨σ.gpr .x0, 32⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x3, VG.Proof.MlDsa.AArch64.KeyGen.scrLen p⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x1, p.pkLen⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x2, p.skLen⟩ (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e26, e27, e28, h.wr]
    · exact VG.Proof.MlDsa.AArch64.KeyGen.inR_self (r := ⟨σ.gpr .x3, VG.Proof.MlDsa.AArch64.KeyGen.scrLen p⟩) (by rw [hwr]; simp)
    · exact VG.Proof.MlDsa.AArch64.KeyGen.inR_self (r := ⟨σ.gpr .x1, p.pkLen⟩) (by rw [hwr]; simp)
    · exact VG.Proof.MlDsa.AArch64.KeyGen.inR_self (r := ⟨σ.gpr .x2, p.skLen⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp

theorem kgOk (p : Params) : VG.Proof.MlDsa.AArch64.KeyGen.LayOk (VG.Proof.MlDsa.AArch64.KeyGen.kgR ++ VG.Proof.MlDsa.AArch64.KeyGen.kgW p) := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp

/-! ## Checks of pointers, by `omega` -/

theorem inB_x25 (p : Params) (o l : Nat) : VG.CallLay.inB ((Reg.x25, 32) :: VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x25, o) l = decide (o + l ≤ 32) := rfl
theorem inB_x28 (p : Params) (o l : Nat) : VG.CallLay.inB ((Reg.x25, 32) :: VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x28, o) l = decide (o + l ≤ VG.Proof.MlDsa.AArch64.KeyGen.scrLen p) := rfl
theorem inB_x26 (p : Params) (o l : Nat) : VG.CallLay.inB ((Reg.x25, 32) :: VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27 (p : Params) (o l : Nat) : VG.CallLay.inB ((Reg.x25, 32) :: VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl
theorem inB_x28W (p : Params) (o l : Nat) : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x28, o) l = decide (o + l ≤ VG.Proof.MlDsa.AArch64.KeyGen.scrLen p) := rfl
theorem inB_x26W (p : Params) (o l : Nat) : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27W (p : Params) (o l : Nat) : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl

theorem sepB_kg {p : Params} {r r' : Reg} (h : r ≠ r') (hr : r ∈ [Reg.x25, .x26, .x27, .x28])
    (hr' : r' ∈ [Reg.x25, .x26, .x27, .x28]) (o l o' l' : Nat) :
    sepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (r, o) l (r', o') l' = (VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgR ++ VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (r, o) l && VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgR ++ VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (r', o') l') := by
  refine sepB_ne h ?_ o l o' l'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;> first | exact absurd rfl h | rfl

/-- Unfolds the checks of pointers into the layout into arithmetic, then
`omega` (in each case of `η`). -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlDsa.AArch64.keepB,
        VG.Proof.MlDsa.AArch64.sepB_same, VG.Proof.MlDsa.AArch64.KeyGen.sepB_kg,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x25, VG.Proof.MlDsa.AArch64.KeyGen.inB_x26,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x27, VG.Proof.MlDsa.AArch64.KeyGen.inB_x28,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x26W, VG.Proof.MlDsa.AArch64.KeyGen.inB_x27W,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x28W, List.all_cons, List.all_nil, List.cons_append, List.nil_append,
        List.all_append, Bool.and_self,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true,
        ↓reduceIte, Bool.false_eq_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oR4, VG.Impl.MlDsa.AArch64.KeyGen.oSA4, VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.oSA,
        VG.Impl.MlDsa.AArch64.KeyGen.oSB, VG.Impl.MlDsa.AArch64.KeyGen.oHX, VG.Impl.MlDsa.AArch64.KeyGen.oKL,
        VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.KeyGen.SV, VG.Impl.MlDsa.AArch64.KeyGen.oT0, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv`. -/
section

/-!
# ML-DSA key generation on AArch64: what holds throughout, and pieces

What holds of the state throughout (`KC`: `Top`, and the seed `ξ` at `seed`),
two runs in the layout (`Two`), and a piece of code (`Piece p S I J c`): it
takes each run from `I` to `J` (`ok`), and two runs related by `I` leak the
same (`tr`). Pieces compose (`Piece.seq`, `Piece.seqR`), which proves
correctness and constant time together.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params keyGenSeeds)
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The precondition of the shared contract. -/
abbrev kgPre (p : Params) (S : Nat) (σ : State) : Prop := (Spec.MlDsa.keyGenContract p AArch64.abi S).pre σ
/-- Its public data. -/
abbrev kgPub (p : Params) (S : Nat) (σ₁ σ₂ : State) : Prop := (Spec.MlDsa.keyGenContract p AArch64.abi S).pub σ₁ σ₂

theorem kgPub_eq {p : Params} {S : Nat} {σ₁ σ₂ : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S σ₁ σ₂) :
    σ₁.sp = σ₂.sp ∧ Spec.MlDsa.keyGenLeak p (bytesAt σ₁.mem (σ₁.gpr .x0) 32) =
        Spec.MlDsa.keyGenLeak p (bytesAt σ₂.mem (σ₂.gpr .x0) 32) ∧
      σ₁.gpr .x0 = σ₂.gpr .x0 ∧ σ₁.gpr .x1 = σ₂.gpr .x1 ∧ σ₁.gpr .x2 = σ₂.gpr .x2 ∧ σ₁.gpr .x3 = σ₂.gpr .x3 := by
  unfold VG.Proof.MlDsa.AArch64.KeyGen.kgPub at h
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
  exact h

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ)).2.2

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  top : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s
  xi : bytesAt s.mem (pa s (.x25, 0)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws VG.Proof.MlDsa.AArch64.KeyGen.svP 48 && keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x25, 0) 32

section
variable {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ)
include hF hp

theorem KC.lay {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s) : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) s := VG.Proof.MlDsa.AArch64.KeyGen.kgLay hF hp h.top

theorem KC.step {s s' : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ws = true) : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.kcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP hc.1, by rw [L.keepBytes hP hc.2]; exact h.xi⟩

end

/-! ## Two runs -/

/-- Two runs in the layout, with the same pointers and stack pointer. -/
structure Two (p : Params) (S : Nat) (x y : State) : Prop where
  lx : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x
  ly : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) y
  same : VG.Proof.MlDsa.AArch64.KeyGen.SameB x y

theorem kc_two {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} {σ₁ σ₂ x y : State} (p₁ : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ₁) (p₂ : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ₂)
    (pub : VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S σ₁ σ₂) (h₁ : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ₁ x) (h₂ : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ₂ y) : VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y := by
  obtain ⟨esp, _, e0, e1, e2, e3⟩ := VG.Proof.MlDsa.AArch64.KeyGen.kgPub_eq pub
  refine ⟨h₁.lay hF p₁, h₂.lay hF p₂, fun r hr => ?_, by rw [h₁.top.sp, h₂.top.sp, esp]⟩
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.x25, h₂.top.x25, e0]
  · rw [h₁.top.x26, h₂.top.x26, e1]
  · rw [h₁.top.x27, h₂.top.x27, e2]
  · rw [h₁.top.x28, h₂.top.x28, e3]

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem Two.step {p : Params} {S : Nat} {c : Prog isa} (htr : RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) c fun _ _ => True)
    (hok : ∀ x, Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x → WP isa c x fun x' => ∃ W, PostB S x x' W) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) c (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB S x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun x y x' y' h ⟨_, hx⟩ ⟨_, hy⟩ => ⟨h.lx.post hx, h.ly.post hy,
      fun r hr => by rw [hx.bs r (VG.Proof.MlDsa.AArch64.KeyGen.bases_kept r hr), hy.bs r (VG.Proof.MlDsa.AArch64.KeyGen.bases_kept r hr)]; exact h.same.1 r hr, by rw [hx.sp, hy.sp]; exact h.same.2⟩

theorem Two.x28 {p : Params} {S : Nat} {x y : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ [Reg.x28], x.gpr r = y.gpr r := ⟨h.same.2, fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.same.1 .x28 (by decide)⟩

theorem Two.bases {p : Params} {S : Nat} {x y : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, x.gpr r = y.gpr r := ⟨h.same.2, h.same.1⟩

/-! ## Pieces -/

/-- Two runs of the function, from entry states that satisfy the
precondition and agree on the public data, each related by `I` to its
entry state. -/
abbrev R (p : Params) (S : Nat) (I : State → State → Prop) : State → State → Prop :=
  VG.Proof.MlDsa.AArch64.Rel2 (VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S) (VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S) I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S I) c fun _ _ => True

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S I J c₁) (h₂ : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S J K c₂) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S I J c)
    (hI : ∀ σ s, VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ → J σ s → J' σ s) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (I k) (I (k + 1)) (f k)) →
      VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (I a) (I (a + n)) (VG.Impl.MlDsa.AArch64.Call.seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => VG.Proof.MlDsa.AArch64.KeyGen.R p S (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ₁ → VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ₂ → VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seeds`. -/
section

/-!
# ML-DSA key generation on AArch64: the prologue and the seeds

The prologue saves the caller's registers and keeps the pointers
(`pro_piece`); then `(ρ, ρ′, K) = H(ξ ‖ k ‖ ℓ, 128)` to `HX`, `ρ` to the seed
of `RejNTTPoly` and `ρ′ ‖ 0` to that of `RejBoundedPoly` (`seeds_piece`,
`K1`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep pbytes)
open VG.Spec.MlDsa (Params keyGenSeeds integerToBytes)
open VG.Spec.Sha3 (bytesAt)

theorem PPostB.app {S : Nat} {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : PPostB S s s₁ ws₁)
    (h₂ : PPostB S s₁ s₂ ws₂) (hc : ∀ w ∈ ws₂, w.1.1 ∈ keptRegs) : PPostB S s s₂ (ws₁ ++ ws₂) :=
  PPostB.trans h₁ h₂ hc (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)

theorem sc_bases (ws : List (Ptr × Nat)) (h : ∀ w ∈ ws, w.1.1 = .x28) : ∀ w ∈ ws, w.1.1 ∈ keptRegs :=
  fun w hw => by rw [h w hw]; decide

/-! ## The prologue -/

theorem scr_ge {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : 1024 * 32 ≤ VG.Proof.MlDsa.AArch64.KeyGen.scrLen p := by rw [VG.Proof.MlDsa.AArch64.KeyGen.scr_eq]; have := hF.k; omega

theorem pro_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => s = σ) (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s ∧ s.gpr .x24 = 1) (.block VG.Impl.MlDsa.AArch64.KeyGen.pro) := by
  refine ⟨fun σ s hp hs => ?_, taintRel [.x0, .x1, .x2, .x3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => ?_)
    (by taint_decide)⟩
  · subst hs
    have hp' := hp
    unfold VG.Proof.MlDsa.AArch64.KeyGen.kgPre at hp'
    sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp'
    obtain ⟨_, _, hwr, _, _, d03, _⟩ := hp'
    have hsc : 1024 * 32 ≤ Spec.MlDsa.scratchWords p * 8 := VG.Proof.MlDsa.AArch64.KeyGen.scr_ge hF
    have hin : ∀ k < 6, InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 := fun k hk =>
      ⟨⟨s.gpr .x3, Spec.MlDsa.scratchWords p * 8⟩, by rw [hwr]; simp, Offset.contains_base _ (by simp only [SV]; omega) (by simp only [SV]; omega)⟩
    refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.pro_ok hin) fun s' ⟨ht, h24, hf⟩ => ⟨⟨ht, ?_⟩, h24⟩
    rw [pa, ht.x25, BitVec.add_zero]
    exact Proof.MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact d03.sub_right (Offset.sub_base _ (by simp only [SV]; omega))) (by decide)
  · subst h₁ h₂
    obtain ⟨esp, _, e0, e1, e2, e3⟩ := VG.Proof.MlDsa.AArch64.KeyGen.kgPub_eq pub
    refine ⟨esp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## The seeds -/

/-- `H(ξ ‖ k ‖ ℓ, 128)`. -/
abbrev hxOf (p : Params) (σ : State) : List Byte :=
  Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ ++ integerToBytes p.k 1 ++ integerToBytes p.ℓ 1) 128

/-- After the seeds. -/
structure K1 (p : Params) (σ s : State) : Prop where
  kc : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s
  hx : bytesAt s.mem (pa s (sc oHX)) 128 = VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ
  sa : bytesAt s.mem (pa s (sc oSA)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ
  sb : bytesAt s.mem (pa s (sc oSB)) 64 = VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ
  z : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]

/-- A piece that writes `ws` keeps `K1`. -/
def k1Chk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ws && keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sc oHX) 128 && keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sc oSA) 32 &&
    keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sc oSB) 64 && keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sc (oSB + 65)) 1

theorem K1.step {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {s s' : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.KeyGen.k1Chk p ws = true) : VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s' := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.k1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP h0, by rw [L.keepBytes hP h1]; exact h.hx, by rw [L.keepBytes hP h2]; exact h.sa,
    by rw [L.keepBytes hP h3]; exact h.sb, by rw [L.keepBytes hP h4]; exact h.z⟩

theorem rho_eq (p : Params) (σ : State) : VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ = (VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ).take 32 := rfl
theorem rho'_eq (p : Params) (σ : State) : VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ = ((VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ).drop 32).take 64 := rfl
theorem kOf_eq (p : Params) (σ : State) : VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ = ((VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ).drop 96).take 32 := rfl

theorem bytesAt_two (m : Mem) (a : Addr) (x y : Byte) :
    bytesAt ((m.writeW a x).writeW (a + BitVec.ofNat 64 1) y) a 2 = [x, y] := by
  have hne : a + BitVec.ofNat 64 0 ≠ a + BitVec.ofNat 64 1 :=
    Offset.add_ofNat_ne a (by decide) (by decide) (by decide)
  show [_, _] = _
  dsimp only
  rw [Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply, Proof.MlKem.writeW8_apply,
    Proof.MlDsa.KeyGen.ifn hne, Proof.MlDsa.KeyGen.ifp (Proof.MlKem.AArch64.ptr_zero a),
    Proof.MlDsa.KeyGen.ifp rfl]

theorem setTwo_ok {p : Params} {S : Nat} {s : State} (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) s) {o a b : Nat}
    (ho : o + 1 < 4096) (h1 : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sc o) 1 = true) (h2 : VG.CallLay.inB (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sc (o + 1)) 1 = true) :
    WP isa (.block (setB (sc o) a ++ setB (sc (o + 1)) b)) s fun s' =>
      PPostB S s s' [(sc o, 1), (sc (o + 1), 1)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9] s s' ∧
      bytesAt s'.mem (pa s (sc o)) 2 = [BitVec.ofNat 8 a, BitVec.ofNat 8 b] := by
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok L (p := sc o) (v := a) (by simp only; omega) h1 (show Reg.x28 ∈ keptRegs by decide))
    fun s₁ ⟨hP₁, k₁, m₁⟩ => WP.mono (setB_ok (L.post hP₁) (p := sc (o + 1)) (v := b) ho h2 (show Reg.x28 ∈ keptRegs by decide))
      fun s₂ ⟨hP₂, k₂, m₂⟩ => ⟨PPostB.app hP₁ hP₂ (VG.Proof.MlDsa.AArch64.KeyGen.sc_bases _ (by simp)), (k₁.trans k₂).mono (by simp), ?_⟩
  have e : pa s₁ (sc (o + 1)) = pa s (sc o) + BitVec.ofNat 64 1 := by
    rw [hP₁.pa (show Reg.x28 ∈ keptRegs by decide), pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [m₂, m₁, e]
  exact VG.Proof.MlDsa.AArch64.KeyGen.bytesAt_two _ _ _ _

theorem hx_eq (p : Params) (σ : State) :
    VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ = Spec.MlDsa.H (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ]) 128 := by
  rw [VG.Proof.MlDsa.AArch64.KeyGen.hxOf, Proof.MlDsa.KeyGen.integerToBytes_one, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]; rfl

theorem bytes64 (m : Mem) (a : Addr) : bytesAt m a 64 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 32 :=
  Proof.MlKem.bytesAt_add m a 32 32

theorem sc_pa {S : Nat} {s s' : State} {W : List Region} (hP : PostB S s s' W) (o : Nat) :
    pa s' (sc o) = pa s (sc o) := hP.pa (show Reg.x28 ∈ keptRegs by decide)

theorem seeds_ok {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {σ : State}
    (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s) (h24 : s.gpr .x24 = 1) :
    WP isa ((seedsWith keccak.callee) p) s fun s' => VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s' ∧ s'.gpr .x24 = 1 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.lay hF hp
  unfold seedsWith
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by lay) (by lay))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ := h.step hF hp hP₁ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have L₁ := h₁.lay hF hp
  refine WP.seq (WP.mono (shake_ok h16 hSl L₁ (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
    (by simp) (by unfold hashChk pieceChk; lay)) fun s₂ ⟨hP₂, x₂, ho₂⟩ => ?_)
  have h₂ := h₁.step hF hp hP₂ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have L₂ := h₂.lay hF hp
  have hmsg : ([⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩].map (pbytes s₁) : List (List Byte)).flatten =
      VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ ++ [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
    have e1 : pbytes s₁ ⟨.x25, 0, 32⟩ = VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ := h₁.xi
    have e2 : pbytes s₁ ⟨.x28, oKL, 2⟩ = [BitVec.ofNat 8 p.k, BitVec.ofNat 8 p.ℓ] := by
      show bytesAt s₁.mem (pa s₁ (sc oKL)) 2 = _
      rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₁]; exact hb₁
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, e1, e2]
  rw [hmsg, ← VG.Proof.MlDsa.AArch64.KeyGen.hx_eq] at ho₂
  have ho₂' : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ := by rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₂]; exact ho₂
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyP_ok L₂ (dst := sc oSA) (src := sc oHX) (by unfold copyPChk; lay)) fun s₃ ⟨hP₃, k₃, b₃⟩ => ?_
  have h₃ := h₂.step hF hp hP₃ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have L₃ := h₃.lay hF hp
  have hx3 : bytesAt s₃.mem (pa s₃ (sc oHX)) 128 = VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ := by rw [L₂.keepBytes hP₃ (by lay)]; exact ho₂'
  have sa3 : bytesAt s₃.mem (pa s₃ (sc oSA)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ := by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₃, b₃, VG.Proof.MlDsa.AArch64.KeyGen.rho_eq, ← ho₂', Proof.MlKem.bytesAt_take _ _ (by decide)]
  refine WP.mono (copyP_ok L₃ (dst := sc oSB) (src := sc (oHX + 32)) (by unfold copyPChk; lay))
    fun s₄ ⟨hP₄, k₄, b₄⟩ => ?_
  have h₄ := h₃.step hF hp hP₄ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have L₄ := h₄.lay hF hp
  refine WP.mono (copyP_ok L₄ (dst := sc (oSB + 32)) (src := sc (oHX + 64)) (by unfold copyPChk; lay))
    fun s₅ ⟨hP₅, k₅, b₅⟩ => ?_
  have h₅ := h₄.step hF hp hP₅ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have L₅ := h₅.lay hF hp
  refine WP.mono (setB_ok L₅ (p := sc (oSB + 65)) (v := 0) (by decide) (by lay) (show Reg.x28 ∈ keptRegs by decide))
    fun s₆ ⟨hP₆, k₆, m₆⟩ => ⟨⟨h₅.step hF hp hP₆ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₅.keepBytes hP₆ (by lay), L₄.keepBytes hP₅ (by lay), L₃.keepBytes hP₄ (by lay)]; exact hx3
  · rw [L₅.keepBytes hP₆ (by lay), L₄.keepBytes hP₅ (by lay), L₃.keepBytes hP₄ (by lay)]; exact sa3
  · rw [L₅.keepBytes hP₆ (by lay)]
    have add32 : ∀ (t : State) (o : Nat), pa t (sc o) + BitVec.ofNat 64 32 = pa t (sc (o + 32)) := fun t o => by
      rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]
    have A : bytesAt s₅.mem (pa s₅ (sc oSB)) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 := by
      rw [L₄.keepBytes hP₅ (by lay), VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₄, b₄]
    have B : bytesAt s₅.mem (pa s₅ (sc (oSB + 32))) 32 = bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₅, b₅, L₃.keepBytes hP₄ (by lay)]
    have C : VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ = bytesAt s₃.mem (pa s₃ (sc (oHX + 32))) 32 ++ bytesAt s₃.mem (pa s₃ (sc (oHX + 64))) 32 := by
      rw [VG.Proof.MlDsa.AArch64.KeyGen.rho'_eq, ← hx3, Proof.MlKem.bytesAt_slice _ _ (show 32 + 64 ≤ 128 by decide),
        VG.Proof.MlDsa.AArch64.KeyGen.bytes64, add32, add32]
    rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes64, add32, A, B, C]
  · rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₆, m₆, bytesAt_one, writeW8_self]; rfl
  · rw [k₆.get .x24, k₅.get .x24, k₄.get .x24, k₃.get .x24, x₂, k₁.get .x24, h24]

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_tr {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) ((seedsWith keccak.callee) p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold seedsWith
  refine RelCT.seq (Two.step (taintRel [.x28] (fun x y h => h.x28) (VG.Proof.MlDsa.AArch64.KeyGen.setKL_taint p.k (by omega) p.ℓ (by omega)))
    fun x L => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.setTwo_ok L (o := oKL) (a := p.k) (b := p.ℓ) (by decide) (by lay) (by lay))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (Two.step (VectorTaint.relRegs [.x25, .x26, .x27, .x28] (fun x y h => h.bases) keccak.mldsaSeedsTaint.choose_spec)
    fun x L => WP.mono (shake_ok h16 hSl L (ins := [⟨.x25, 0, 32⟩, ⟨.x28, oKL, 2⟩]) (out := ⟨.x28, oHX, 128⟩)
      (by simp) (by unfold hashChk pieceChk; lay)) fun _ h => ⟨_, h.1⟩) ?_
  exact taintRel [.x28] (fun x y h => h.x28) (by taint_decide)

theorem seeds_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s ∧ s.gpr .x24 = 1) (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s ∧ s.gpr .x24 = 1) ((seedsWith keccak.callee) p) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.seeds_ok hF h16 hSl hp h.1 h.2,
    VG.Proof.MlDsa.AArch64.KeyGen.rel_of (VG.Proof.MlDsa.AArch64.KeyGen.seeds_tr hF h16 hSl) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp`. -/
section

/-!
# ML-DSA key generation on AArch64: the samplers

The entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the
first `e` entries of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is
reduced (and those of `s₁ ‖ s₂` small), and `x24` is 1 if every sampler
succeeded, with the polynomials those of the standard for some bounds, or 0 if
key generation fails within the least bounds (`Good`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Params keyGenSeeds Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly keyGenInternal toRq
  polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Bounds.Le bmax Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## What the samplers leave -/

/-- `x24` after the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`: 1 if they
are those of the standard, `A` and `S`, for some bounds; 0 if key generation
fails within the least bounds. -/
def Good (p : Params) (σ : State) (e r : Nat) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (v : BitVec 64) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, (∀ e' < e, rejNTTPoly b.rejNTT (seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) (e' / p.ℓ) (e' % p.ℓ)) = some (A e')) ∧
      ∀ r' < r, rejBoundedPoly p.η b.rejBounded (seedS (VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ) r') = some (S r')) ∨
    (v = 0 ∧ keyGenInternal p minBounds (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ) = none)

theorem good_01 {p : Params} {σ : State} {e r : Nat} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {v : BitVec 64}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.Good p σ e r A S v) : v = 0 ∨ v = 1 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inr h, .inl h]

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s
  ex : ∃ (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem (pa s (sP p r')) (toRq (S r')) ∧ Small p.η (S r')) ∧ VG.Proof.MlDsa.AArch64.KeyGen.Good p σ e r A S (s.gpr .x24)

theorem KSamp.keep {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {e r : Nat} {s s' : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e r s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : VG.Proof.MlDsa.AArch64.KeyGen.k1Chk p ws = true)
    (ha : ∀ e' < e, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (VG.Impl.MlDsa.AArch64.KeyGen.aP e') 1024 = true)
    (hs : ∀ r' < r, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sP p r') 1024 = true) (h24 : s'.gpr .x24 = s.gpr .x24) :
    VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e r s' := by
  have L := h.k1.kc.lay hF hp
  obtain ⟨A, S', hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.step hF hp hP hc, A, S', fun e' he' => L.keepPoly hP (ha e' he') (hA e' he'),
    fun r' hr' => ⟨L.keepPoly hP (hs r' hr') (hS r' hr').1, (hS r' hr').2⟩, by rw [h24]; exact hG⟩

theorem KSamp.zero {p : Params} {σ s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s) (h24 : s.gpr .x24 = 1) : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ 0 0 s :=
  ⟨h, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _),
    .inl ⟨h24, ⟨0, 0, 0, 0⟩, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem bytes34 (m : Mem) (a : Addr) : bytesAt m a 34 = bytesAt m a 32 ++ bytesAt m (a + BitVec.ofNat 64 32) 2 :=
  Proof.MlKem.bytesAt_add m a 32 2

theorem sc_add (t : State) (o k : Nat) : pa t (sc o) + BitVec.ofNat 64 k = pa t (sc (o + k)) := by
  rw [pa, pa, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## An entry of `Â` -/

theorem expA_ok {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State}
    (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {e : Nat} (he : e < p.k * p.ℓ) {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e 0 s) :
    WP isa (expA P p e) s (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (e + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.k1.kc.lay hF hp
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  unfold expA sampled
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by lay) (by lay))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e 0 s₁ :=
    h.keep hF hp hP₁ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay) (fun e' he' => by lay) (fun _ h => absurd h (Nat.not_lt_zero _))
      (k₁.get .x24)
  have L₁ := h₁.k1.kc.lay hF hp
  have hseed : bytesAt s₁.mem (pa s₁ (sc oSA)) 34 = seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes34, h₁.k1.sa, VG.Proof.MlDsa.AArch64.KeyGen.sc_add, VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₁, hb₁, Proof.MlDsa.KeyGen.seedA_eq]
  refine WP.seq (WP.mono (rejNttAt_ok hP.s64 hP.rejNtt L₁ (seed := sc oSA) (a := VG.Impl.MlDsa.AArch64.KeyGen.aP e) (ss := sc oSS)
    (by unfold rejNttChk; lay)) fun s₂ ⟨hP₂, x₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have L₂ := L₁.post hP₂
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.tail_ok L₂ (a := VG.Impl.MlDsa.AArch64.KeyGen.aP e) (by lay) (by lay) hr01) fun s₃ ⟨hP₃, x₃, hco⟩ => ?_
  have hP₁₃ := PPostB.app hP₂ hP₃ (VG.Proof.MlDsa.AArch64.KeyGen.sc_bases _ (by simp))
  have e₂ : pa s₂ (VG.Impl.MlDsa.AArch64.KeyGen.aP e) = pa s₁ (VG.Impl.MlDsa.AArch64.KeyGen.aP e) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₂ _
  have e₃ : pa s₃ (VG.Impl.MlDsa.AArch64.KeyGen.aP e) = pa s₂ (VG.Impl.MlDsa.AArch64.KeyGen.aP e) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₃ _
  rw [e₂] at hco
  obtain ⟨A, S', hA, _, hG⟩ := h₁.ex
  rw [x₂, Proof.MlDsa.KeyGen.and01 (VG.Proof.MlDsa.AArch64.KeyGen.good_01 hG) hr01] at x₃
  refine ⟨h₁.k1.step hF hp hP₁₃ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay), fun e' => if e' = e then polyAt s₃.mem (pa s₃ (VG.Impl.MlDsa.AArch64.KeyGen.aP e))
    else A e', S', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega)]
      exact L₁.keepPoly hP₁₃ (by lay) (hA e' he')
    · rw [ifp rfl]
      refine ⟨?_, rfl⟩
      rw [e₃, e₂]
      by_cases h1 : (s₂.gpr .x0).setWidth 32 = 1
      · exact (Proof.MlDsa.KeyGen.masked_one h1 hco).2 (hred h1)
      · exact (Proof.MlDsa.KeyGen.masked_zero h1 hco).1
  · rw [x₃]
    have hq' : e = p.ℓ * (e / p.ℓ) + e % p.ℓ := (Nat.div_add_mod e p.ℓ).symm
    rcases hG with ⟨h1, b, hb, _⟩ | ⟨h0, hn⟩
    · rcases hout with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        dsimp only
        rcases (by omega : e' < e ∨ e' = e) with he' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hb e' he')
        · rw [ifp rfl, e₃, e₂, (Proof.MlDsa.KeyGen.masked_one ho hco).1]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejNTT hb'
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_A hq hr hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl, hn⟩

/-! ## Constant time -/

theorem rho_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S σ₁ σ₂) : VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ₁ = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (VG.Proof.MlDsa.AArch64.KeyGen.kgPub_eq pub).2.1).1

theorem rej_pub {p : Params} {S : Nat} {σ₁ σ₂ : State} (pub : VG.Proof.MlDsa.AArch64.KeyGen.kgPub p S σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split (VG.Proof.MlDsa.AArch64.KeyGen.kgPub_eq pub).2.1).2 r hr

theorem Two.post {p : Params} {S : Nat} {x y x' y' : State} (T : VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y) {W₁ W₂ : List Region}
    (hx : PostB S x x' W₁) (hy : PostB S y y' W₂) : VG.Proof.MlDsa.AArch64.KeyGen.Two p S x' y' :=
  ⟨T.lx.post hx, T.ly.post hy, fun r hr => by rw [hx.bs r (VG.Proof.MlDsa.AArch64.KeyGen.bases_kept r hr), hy.bs r (VG.Proof.MlDsa.AArch64.KeyGen.bases_kept r hr)]; exact T.same.1 r hr,
    by rw [hx.sp, hy.sp]; exact T.same.2⟩

/-- A piece that leaks the same, and keeps the layout, leaves two runs in it. -/
theorem RelCT.two {p : Params} {S : Nat} {c : Prog isa} {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y)
    (htr : RelCT isa P c fun _ _ => True)
    (hok : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB S x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB S y y' W)) :
    RelCT isa P c (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB S x x' W) hok fun x y _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => (hP x y h).post hx hy

/-- The check is the same for every offset: its hint is computed once, for offset 0. -/
theorem mask_taint : ∀ j < 80, (taint.check (AArch64.Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.KeyGen.mask (sc (oP j)))
    (VG.Taint.hintOf taint (AArch64.Taint.ofRegs [.x28]) (VG.Impl.MlDsa.AArch64.KeyGen.mask (sc 0)))).isSome = true := by decide +kernel

/-- The AND of a sampler's result and the mask of its output. -/
theorem tail_tr {p : Params} {S : Nat} {j : Nat} (hj : j < 80) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.KeyGen.mask (sc (oP j)))) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by simp only [and24, List.mem_singleton] at hi; subst hi; rfl)
      fun x _ => WP.mono (and24_ok x) fun _ ⟨o, _⟩ =>
        ⟨[], postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (VG.Proof.MlDsa.AArch64.KeyGen.mask_taint j hj))

theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (taint.check (AArch64.Taint.ofRegs [.x28])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

theorem expA_tr {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · e 0)) (expA P p e) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  have hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega)
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 32 = bytesAt y.mem (pa y (sc oSA)) 32)
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, by
      rw [h₁.k1.sa, h₂.k1.sa, VG.Proof.MlDsa.AArch64.KeyGen.rho_pub pub]⟩
  unfold expA sampled
  -- The seed, then the call and the mask.
  let F := fun (x x' : State) => (∃ W, PostB S x x' W) ∧
    bytesAt x'.mem (pa x' (sc oSA)) 34 = bytesAt x.mem (pa x (sc oSA)) 32 ++ [BitVec.ofNat 8 (e % p.ℓ),
      BitVec.ofNat 8 (e / p.ℓ)]
  have hF1 : ∀ x, Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x L =>
    WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.setTwo_ok L (o := oSA + 32) (a := e % p.ℓ) (b := e / p.ℓ) (by decide) (by lay) (by lay))
      fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁⟩, by rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes34, L.keepBytes hP₁ (by lay), VG.Proof.MlDsa.AArch64.KeyGen.sc_add, VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₁, hb]⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.x28] (fun x y h => h.1.x28) (VG.Proof.MlDsa.AArch64.KeyGen.setIJ_taint _ (by omega) _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.lx, hF1 y h.1.ly⟩)
    (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y ∧ bytesAt x.mem (pa x (sc oSA)) 34 = bytesAt y.mem (pa y (sc oSA)) 34)
    fun x y x' y' ⟨T, e32⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ => ⟨T.post hx hy, by rw [bx, by', e32]⟩) ?_
  have hc : rejNttChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sc oSA) (VG.Impl.MlDsa.AArch64.KeyGen.aP e) (sc oSS) = true := by unfold rejNttChk; lay
  have ok := fun x (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x) => WP.mono (rejNttAt_ok (nm := "vg_mldsa_rej_ntt_poly" ++ P.suffix) hP.s64 hP.rejNtt L hc)
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (rejNttAt_tr hP.rejNtt (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) hc fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (VG.Proof.MlDsa.AArch64.KeyGen.tail_tr (j := e) (by omega))

/-! ## An entry of `s₁ ‖ s₂` -/

theorem eta_of {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem bytes66 (m : Mem) (a : Addr) :
    bytesAt m a 66 = bytesAt m a 64 ++ bytesAt m (a + BitVec.ofNat 64 64) 1 ++ bytesAt m (a + BitVec.ofNat 64 65) 1 := by
  rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add]

/-- The seed of `RejBoundedPoly`, once its index is set. -/
theorem sbSeed {p : Params} {S : Nat} {s s' : State} (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) s) {r : Nat} (hr : r < 256)
    (hP : PPostB S s s' [(sc (oSB + 64), 1)]) (hb : s'.mem = s.mem.writeW (pa s (sc (oSB + 64))) (BitVec.ofNat 8 r))
    {ρ' : List Byte} (h64 : bytesAt s.mem (pa s (sc oSB)) 64 = ρ') (h65 : bytesAt s.mem (pa s (sc (oSB + 65))) 1 = [0]) :
    bytesAt s'.mem (pa s' (sc oSB)) 66 = Proof.MlDsa.KeyGen.seedS ρ' r := by
  have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have k64 := L.keepBytes hP (p := sc oSB) (l := 64) (by lay)
  have k65 := L.keepBytes hP (p := sc (oSB + 65)) (l := 1) (by lay)
  rw [VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP] at k64 k65 ⊢
  rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes66, k64, h64, VG.Proof.MlDsa.AArch64.KeyGen.sc_add, VG.Proof.MlDsa.AArch64.KeyGen.sc_add, k65, h65, hb, bytesAt_one, writeW8_self, Proof.MlDsa.KeyGen.seedS_eq _ hr,
    List.append_assoc]
  rfl

theorem expS_ok {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State}
    (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {r : Nat} (hr : r < p.ℓ + p.k) {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) (r + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.k1.kc.lay hF hp
  unfold expS sampled
  refine WP.seq (WP.mono (setB_ok L (p := sc (oSB + 64)) (v := r) (by decide) (by lay)
    (show Reg.x28 ∈ keptRegs by decide)) fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_)
  have h₁ : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) r s₁ :=
    h.keep hF hp hP₁ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay) (fun e' he' => by lay) (fun r' hr' => by lay) (k₁.get .x24)
  have L₁ := h₁.k1.kc.lay hF hp
  have hseed := VG.Proof.MlDsa.AArch64.KeyGen.sbSeed L (by omega) hP₁ hb₁ h.k1.sb h.k1.z
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.rejBAt_ok hP.s64 hP.rejBounded L₁ (seed := sc oSB) (a := sP p r) (ss := sc oSS)
    (by unfold VG.Proof.MlDsa.AArch64.KeyGen.rejBChk; lay) (VG.Proof.MlDsa.AArch64.KeyGen.eta_of hF)) fun s₂ ⟨hP₂, x₂, hred, hout⟩ => ?_)
  rw [hseed] at hout
  have L₂ := L₁.post hP₂
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.tail_ok L₂ (a := sP p r) (by lay) (by lay) hr01) fun s₃ ⟨hP₃, x₃, hco⟩ => ?_
  have hP₁₃ := PPostB.app hP₂ hP₃ (VG.Proof.MlDsa.AArch64.KeyGen.sc_bases _ (by simp))
  have e₂ : pa s₂ (sP p r) = pa s₁ (sP p r) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₂ _
  have e₃ : pa s₃ (sP p r) = pa s₂ (sP p r) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP₃ _
  rw [e₂] at hco
  obtain ⟨A, S', hA, hS, hG⟩ := h₁.ex
  rw [x₂, Proof.MlDsa.KeyGen.and01 (VG.Proof.MlDsa.AArch64.KeyGen.good_01 hG) hr01] at x₃
  have k1 := h₁.k1.step hF hp hP₁₃ (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
  have kA : ∀ e' < p.k * p.ℓ, PolyIs s₃.mem (pa s₃ (VG.Impl.MlDsa.AArch64.KeyGen.aP e')) (A e') := fun e' he' =>
    L₁.keepPoly hP₁₃ (by lay) (hA e' he')
  have kS : ∀ r' < r, PolyIs s₃.mem (pa s₃ (sP p r')) (toRq (S' r')) ∧ Small p.η (S' r') := fun r' hr' =>
    ⟨L₁.keepPoly hP₁₃ (by lay) (hS r' hr').1, (hS r' hr').2⟩
  by_cases ho : (s₂.gpr .x0).setWidth 32 = 1
  · -- The sampler succeeded.
    obtain ⟨b', hb'⟩ : ∃ b' : Bounds, (rejBoundedPoly p.η b'.rejBounded (seedS (VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ) r)).map toRq =
        some (polyAt s₂.mem (pa s₁ (sP p r))) := by
      rcases hout with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rw [h] at ho; exact absurd ho (by decide)
    obtain ⟨x, hx, htx⟩ := Option.map_eq_some_iff.mp hb'
    refine ⟨k1, A, fun r' => if r' = r then x else S' r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂, htx, ← (Proof.MlDsa.KeyGen.masked_one ho hco).1]
        exact ⟨⟨(Proof.MlDsa.KeyGen.masked_one ho hco).2 (hred ho), rfl⟩,
          Proof.MlDsa.KeyGen.rejBoundedPoly_range hx⟩
    · rw [x₃]
      rcases hG with ⟨h1, b, hbA, hbS⟩ | ⟨h0, hn⟩
      · refine .inl ⟨by rw [ifp ⟨h1, ho⟩], bmax b b', fun e' he' =>
          Proof.MlDsa.KeyGen.rejNTTPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejNTT (hbA e' he'),
          fun r' hr' => ?_⟩
        dsimp only
        rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
        · rw [ifn (by omega)]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_left b b').rejBounded
            (hbS r' hr')
        · rw [ifp rfl]
          exact Proof.MlDsa.KeyGen.rejBoundedPoly_mono (Proof.MlDsa.KeyGen.Bounds.le_max_right b b').rejBounded hx
      · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
        exact .inr ⟨rfl, hn⟩
  · -- It failed: the polynomial is zero.
    have hn : rejBoundedPoly p.η minBounds.rejBounded (seedS (VG.Proof.MlDsa.AArch64.KeyGen.rho'Of p σ) r) = none := by
      rcases hout with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h ho
      · exact Option.map_eq_none_iff.mp h
    refine ⟨k1, A, fun r' => if r' = r then Vector.replicate 256 0 else S' r', kA, fun r' hr' => ?_, ?_⟩
    · dsimp only
      rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
      · rw [ifn (by omega)]; exact kS r' hr'
      · rw [ifp rfl, e₃, e₂]
        exact ⟨Proof.MlDsa.KeyGen.masked_zero ho hco, Proof.MlDsa.KeyGen.small_zero _⟩
    · rw [x₃, ifn (fun h => ho h.2)]
      exact .inr ⟨rfl, Proof.MlDsa.KeyGen.keyGenInternal_none_S hr hn⟩

theorem setS_taint : ∀ v < 16, (taint.check (AArch64.Taint.ofRegs [.x28]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

theorem expS_tr {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (p.k * p.ℓ) r)) (expS P p r) fun _ _ => True := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y ∧ ∃ ρ₁ ρ₂ : List Byte, bytesAt x.mem (pa x (sc oSB)) 64 = ρ₁ ∧
      bytesAt x.mem (pa x (sc (oSB + 65))) 1 = [0] ∧ bytesAt y.mem (pa y (sc oSB)) 64 = ρ₂ ∧
      bytesAt y.mem (pa y (sc (oSB + 65))) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₁ r) = Spec.MlDsa.rejBoundedLeak p.η (seedS ρ₂ r))
    ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc, _, _, h₁.k1.sb, h₁.k1.z, h₂.k1.sb,
      h₂.k1.z, VG.Proof.MlDsa.AArch64.KeyGen.rej_pub pub hr⟩
  unfold expS sampled
  let F := fun (x x' : State) => (∃ W, PostB S x x' W) ∧ ∀ ρ' : List Byte, bytesAt x.mem (pa x (sc oSB)) 64 = ρ' →
    bytesAt x.mem (pa x (sc (oSB + 65))) 1 = [0] → bytesAt x'.mem (pa x' (sc oSB)) 66 = seedS ρ' r
  have hF1 : ∀ x, Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x L =>
    WP.mono (setB_ok L (p := sc (oSB + 64)) (v := r) (by decide) (by lay) (show Reg.x28 ∈ keptRegs by decide))
      fun x' ⟨hP₁, _, hb⟩ => ⟨⟨_, hP₁⟩, fun _ h64 h65 => VG.Proof.MlDsa.AArch64.KeyGen.sbSeed L (by omega) hP₁ hb h64 h65⟩
  refine RelCT.seq (RelCT.postDep (taintRel [.x28] (fun x y h => h.1.x28) (VG.Proof.MlDsa.AArch64.KeyGen.setS_taint _ (by omega)))
    (F := F) (fun x y h => ⟨hF1 x h.1.lx, hF1 y h.1.ly⟩)
    (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y ∧ Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem (pa x (sc oSB)) 66) =
      Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem (pa y (sc oSB)) 66))
    fun x y x' y' ⟨T, _, _, a1, a2, a3, a4, a5⟩ ⟨⟨_, hx⟩, bx⟩ ⟨⟨_, hy⟩, by'⟩ =>
      ⟨T.post hx hy, by rw [bx _ a1 a2, by' _ a3 a4, a5]⟩) ?_
  have hc : VG.Proof.MlDsa.AArch64.KeyGen.rejBChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sc oSB) (sP p r) (sc oSS) = true := by unfold VG.Proof.MlDsa.AArch64.KeyGen.rejBChk; lay
  have ok := fun x (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x) => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.rejBAt_ok hP.s64 hP.rejBounded L hc (VG.Proof.MlDsa.AArch64.KeyGen.eta_of hF))
    fun _ h => (⟨_, h.1⟩ : ∃ W, PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1) (VG.Proof.MlDsa.AArch64.KeyGen.rejBAt_tr hP.rejBounded (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) hc (VG.Proof.MlDsa.AArch64.KeyGen.eta_of hF) fun x y h =>
      ⟨h.1.lx, h.1.ly, h.2, h.1.same⟩)
      fun x y h => ⟨ok x h.1.lx, ok y h.1.ly⟩)
    (VG.Proof.MlDsa.AArch64.KeyGen.tail_tr (j := p.k * p.ℓ + r) (by omega))

/-! ## The pieces -/

theorem expA_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {e : Nat}
    (he : e < p.k * p.ℓ) : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · e 0) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (e + 1) 0) (expA P p e) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.expA_ok hP hF hp he h, VG.Proof.MlDsa.AArch64.KeyGen.expA_tr hP hF he⟩

theorem expS_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (p.k * p.ℓ) r) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (p.k * p.ℓ) (r + 1)) (expS P p r) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.expS_ok hP hF hp hr h, VG.Proof.MlDsa.AArch64.KeyGen.expS_tr hP hF hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s ∧ s.gpr .x24 = 1) (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) 0 s)
      (VG.Impl.MlDsa.AArch64.Call.seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => VG.Proof.MlDsa.AArch64.KeyGen.expA_piece hP hF (by omega)) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) 0 s) (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (VG.Impl.MlDsa.AArch64.Call.seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => VG.Proof.MlDsa.AArch64.KeyGen.expS_piece hP hF (by omega)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Mask4`. -/
section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrw wp_strw wp_addImm wp_subImm
  count_loop)
open VG.Spec.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)

theorem coeffAt_writeW32_4 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 1024) (hj : j < 1024) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

theorem ofNat4_sub1 {i : Nat} (h : i < 1024) : BitVec.ofNat 64 (1024 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (1024 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem mask4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : VG.CallLay.inB wbs a 4096 = true) (hin : VG.CallLay.inB (rbs ++ wbs) a 4096 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (mask4 a) s fun s' => PPostB S s s' [(a, 4096)] ∧ VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s' ∧
      ∀ i < 1024, coeffAt s'.mem (pa s a) i =
        if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 4096 := L.inW hw
  have hn : (pa s a).toNat + 4096 ≤ 2 ^ 64 := L.nwp hin
  have hb : a.1 ∈ keptRegs := L.ptrBs hin
  have h1 : a.1 ≠ .x1 := by intro e; rw [e] at hb; revert hb; decide
  have h8 : a.1 ≠ .x8 := by intro e; rw [e] at hb; revert hb; decide
  unfold mask4
  refine WP.seq ?_
  refine wp_movz fun s₁ h₁ e₁ => VG.Proof.MlDsa.AArch64.KeyGen.wp_sub32 fun s₂ h₂ e₂ => lea_ok h1.symm a.2 fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ : VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s₄ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono (by simp)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x8 : s₄.gpr .x8 = BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (s.gpr .x0).setWidth 32) := by
    rw [h₄.get .x8, h₃.get .x8, e₂, e₁, h₁.get .x0]; rfl
  have x1 : s₄.gpr .x1 = pa s a := by
    rw [h₄.get .x1, e₃, h₂.get a.1 (by simpa using h8), h₁.get a.1 (by simpa using h8)]
  refine WP.mono (count_loop (cr := .x2) (n := 1024) (by decide) (fun i s' =>
      s'.gpr .x1 = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .x2 = BitVec.ofNat 64 (1024 - i) ∧
      s'.gpr .x8 = s₄.gpr .x8 ∧ VG.Proof.MlKem.AArch64.Keep [.x1, .x2, .x8, .x9] s s' ∧ Frame [⟨pa s a, 4096⟩] s.mem s'.mem ∧
      ∀ j < 1024, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s₄.gpr .x8).setWidth 32 else coeffAt s.mem (pa s a) j)
    (fun i hi s' ⟨e1, e2, e8, kk, hf, hc⟩ => ?_)
    ⟨by rw [x1, Nat.mul_zero, BitVec.add_zero], by rw [e₄]; rfl, rfl, k₄, by rw [m₄]; exact Frame.refl _ _,
      fun j _ => by rw [Proof.MlDsa.KeyGen.ifn (Nat.not_lt_zero j), m₄]⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨postB_of_keep kk (by decide) hf, kk, fun j hj => ?_⟩
  · have hc4 : (⟨pa s a, 4096⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hinw : InRegions s'.wr (s'.gpr .x1) 4 := by
      rw [kk.wr, e1]; exact VG.CallLay.inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .x1) 4 := VG.Proof.MlKem.AArch64.in_rd_wr hinw
    refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.maskBody_ok s' hin0 hinw) fun s'' ⟨⟨hm, e1', e2'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [k'.get .x8, e8],
      (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [e1', e1, VG.Proof.MlDsa.AArch64.KeyGen.off_add4]
    · rw [e2', e2, VG.Proof.MlDsa.AArch64.KeyGen.ofNat4_sub1 hi]
    · rw [hm, e1]; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, e1, VG.Proof.MlDsa.AArch64.KeyGen.coeffAt_writeW32_4 _ _ hj (by omega), e8]
      by_cases e : i = j
      · subst e
        rw [Proof.MlDsa.KeyGen.ifp rfl, Proof.MlDsa.KeyGen.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [Proof.MlDsa.KeyGen.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [Proof.MlDsa.KeyGen.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [Proof.MlDsa.KeyGen.ifp hji, Proof.MlDsa.KeyGen.ifp (by omega)]
        · rw [Proof.MlDsa.KeyGen.ifn hji, Proof.MlDsa.KeyGen.ifn (by omega)]
    · rw [e2', e2, VG.Proof.MlDsa.AArch64.KeyGen.ofNat4_sub1 hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hc j hj, Proof.MlDsa.KeyGen.ifp hj, x8, VG.Proof.MlDsa.AArch64.KeyGen.and_mask hr]


end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4`. -/
section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa (Params Poly IPoly Reduced PolyIs polyAt poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA)
open VG.Spec.Sha3 (bytesAt)

theorem copySeed4_generic {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {j : Nat} (hsrc : VG.CallLay.inB (rbs++wbs) (sc oSA) 32 = true)
    (hdst : VG.CallLay.inB wbs (sc (oSA4+34*j)) 32 = true)
    (hsep : sepB rbs wbs (sc oSA) 32 (sc (oSA4+34*j)) 32 = true) :
    WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  unfold copySeed4
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc (oSA4+34*j)) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 oSA,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc oSA),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc (oSA4+34*j))+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc (oSA4+34*j))) (sb := .x28) (db := .x10) (so := oSA) (dO := 0) (by decide) (by decide) (by decide) (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc oSA),32⟩ : Region).Disjoint ⟨pa s (sc (oSA4+34*j)),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : VG.Proof.MlKem.AArch64.Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

theorem copySeed4_ok {S : Nat} {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {s : State} (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) s)
    {j : Nat} (hj : j < 4) : WP isa (.block (copySeed4 j)) s fun t =>
      PPostB S s t [(sc (oSA4+34*j),32)] ∧ VG.Proof.MlKem.AArch64.Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc (oSA4+34*j))) 32 = bytesAt s.mem (pa s (sc oSA)) 32 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  exact VG.Proof.MlDsa.AArch64.KeyGen.copySeed4_generic L (by lay) (by lay) (by lay)

structure GS (p : Params) (σ : State) (e j : Nat) (s : State) : Prop where
  ks : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e 0 s
  done : ∀ k < j,bytesAt s.mem (pa s (sc (oSA4+34*k))) 34 =
    seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ)

theorem slot_ok {P : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts P) {S : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre P S σ)
    {e j : Nat} (he : e+4 ≤ P.k*P.ℓ) (hj : j < 4) {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.GS P σ e j s) :
    WP isa (seedSlot4 P e j) s (VG.Proof.MlDsa.AArch64.KeyGen.GS P σ e (j+1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq P
  have L := h.ks.k1.kc.lay hF hp
  unfold seedSlot4
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.copySeed4_ok hF L hj) fun s1 ⟨hP1,hk1,hb1⟩ => ?_)
  have h1 := h.ks.keep hF hp hP1 (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay)
    (fun k hk => by lay) (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk1.get .x24)
  have L1 := h1.k1.kc.lay hF hp
  unfold setSR
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.setTwo_ok L1 (o := oSA4+34*j+32) (a := (e+j)%P.ℓ) (b := (e+j)/P.ℓ)
    (by dsimp only [oSA4]; omega) (by lay) (by lay)) fun t ⟨hP2,hk2,hb2⟩ => ?_
  refine ⟨h1.keep hF hp hP2 (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay) (fun k hk => by lay)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hk2.get .x24),fun k hk => ?_⟩
  by_cases heq : k = j
  · subst k
    rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes34,L1.keepBytes hP2 (by lay),VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP2,VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP1,hb1,h.ks.k1.sa,
      VG.Proof.MlDsa.AArch64.KeyGen.sc_add,← VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP1,hb2,Proof.MlDsa.KeyGen.seedA_eq]
  · rw [L1.keepBytes hP2 (by lay),L.keepBytes hP1 (by lay)]
    exact h.done k (by omega)
end VG.Proof.MlDsa.AArch64.KeyGen

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

theorem slot_taint (p : Params) (e : Nat) {j : Nat} (hj : j < 4) :
    (taint.check (Taint.ofRegs [.x28]) (seedSlot4 p e j) (.seq (Taint.ofRegs [.x28,.x10]) (.block []) (.block []))).isSome = true := by
  unfold seedSlot4 copySeed4 lea
  rw [VG.Proof.MlDsa.KeyGen.ifp (by dsimp only [oSA4]; omega : oSA4+34*j < 4096)]
  with_unfolding_all rfl

theorem slot_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S e j : Nat} (he : e+4 ≤ p.k*p.ℓ) (hj : j < 4) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.GS p · e j) (VG.Proof.MlDsa.AArch64.KeyGen.GS p · e (j+1)) (seedSlot4 p e j) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.slot_ok hF hp he hj h,
    VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := VG.Proof.MlDsa.AArch64.KeyGen.Two p S) (taintRel [.x28] (fun _ _ h => Two.x28 h) (VG.Proof.MlDsa.AArch64.KeyGen.slot_taint p e hj))
      fun _ _ _ _ hp hp' hq h h' => VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF hp hp' hq h.ks.k1.kc h'.ks.k1.kc⟩
end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4`. -/
section

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly coeffAt polyAt Reduced PolyIs poly4 seed4 minBounds)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.GS p σ e 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc oSA4)) k = seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4) + BitVec.ofNat 64 (34 * k) = pa s (sc (oSA4 + 34 * k)) from VG.Proof.MlDsa.AArch64.KeyGen.sc_add _ _ _]
  exact h.done k hk

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds are those of the entries, from `ρ`. -/
theorem GS.seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.GS p σ e 4 s) :
    bytesAt s.mem (pa s (sc oSA4)) 136 = seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (pa s (sc oSA4) + BitVec.ofNat 64 (34 * k)) 34 =
      seedA (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := fun k hk => VG.Proof.MlDsa.AArch64.KeyGen.seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, VG.Proof.MlKem.AArch64.ptr_zero] at b0
  rw [VG.Proof.MlDsa.AArch64.KeyGen.bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-! ## The four polynomials -/

theorem coeffAt_poly4 (m : Mem) (a : Addr) (k j : Nat) : coeffAt m (poly4 a k) j = coeffAt m a (256 * k + j) := by
  unfold coeffAt poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega]

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e)) k = pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (e + k)) := by
  unfold poly4
  rw [show pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e) + BitVec.ofNat 64 (1024 * k) = pa s (sc (oP e + 1024 * k)) from VG.Proof.MlDsa.AArch64.KeyGen.sc_add _ _ _,
    show oP e + 1024 * k = oP (e + k) by simp only [oP]; omega]

/-- One bound for the four polynomials. -/
theorem bound4 {ρ : Nat → List Byte} {x : Nat → VG.Spec.MlDsa.Poly} (h : ∀ k < 4, ∃ b : Spec.MlDsa.Bounds,
    rejNTTPoly b.rejNTT (ρ k) = some (x k)) : ∃ n : Nat, ∀ k < 4, rejNTTPoly n (ρ k) = some (x k) := by
  obtain ⟨b0, h0⟩ := h 0 (by decide)
  obtain ⟨b1, h1⟩ := h 1 (by decide)
  obtain ⟨b2, h2⟩ := h 2 (by decide)
  obtain ⟨b3, h3⟩ := h 3 (by decide)
  refine ⟨max (max b0.rejNTT b1.rejNTT) (max b2.rejNTT b3.rejNTT), fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h1
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h2
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega) h3


theorem call_ok {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p)
    {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.GS p σ (4*g) 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)))
      (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))))) s (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (4*g+4) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (ss := sc (oR4 p)) (by unfold VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk; lay))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩
    exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide)
    (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by
    rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.mask4_ok L20 (a := VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (by lay) (by lay) hr20)
    fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (VG.Proof.MlDsa.AArch64.KeyGen.sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (VG.Proof.MlDsa.AArch64.KeyGen.sc_bases _ (by simp))
  have e2 : pa s2 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) = pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP2 _
  have e20 : pa s20 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) = pa s2 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) := VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4, ∀ i < 256,coeffAt s3.mem (poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [VG.Proof.MlDsa.AArch64.KeyGen.coeffAt_poly4,VG.Proof.MlDsa.AArch64.KeyGen.coeffAt_poly4]; exact hco _ (by omega)
  have e3 : ∀ k,pa s3 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g+k)) = poly4 (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))) k := fun k => by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.pa_poly4,VG.Proof.MlDsa.AArch64.KeyGen.sc_pa hP13]
  obtain ⟨A,S',hA,_,hG⟩ := h.ks.ex
  have h24' : s3.gpr .x24 = if s.gpr .x24 = 1 ∧ (s2.gpr .x0).setWidth 32 = 1 then 1 else 0 := by
    rw [k3.get .x24,e24,h24,Proof.MlDsa.KeyGen.and01 (VG.Proof.MlDsa.AArch64.KeyGen.good_01 hG) hr01]
  refine ⟨h.ks.k1.step hF hp hP13 (by unfold VG.Proof.MlDsa.AArch64.KeyGen.k1Chk VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay),
    fun e' => if e' < 4*g then A e' else polyAt s3.mem (pa s3 (VG.Impl.MlDsa.AArch64.KeyGen.aP e')),S',
    fun e' he' => ?_,fun _ h => False.elim (Nat.not_lt_zero _ h),?_⟩
  · dsimp only
    by_cases hlt : e' < 4*g
    · rw [ifp hlt]
      exact L.keepPoly hP13 (by lay) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_,rfl⟩
      obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega⟩
      rw [e3]
      by_cases h1 : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega))).2 (hred h1 k (by omega))
      · exact (masked_zero h1 (hco4 k (by omega))).1
  · rw [h24']
    rcases hG with ⟨h1,b,hb,_⟩ | ⟨h0,hn⟩
    · rcases hout with ⟨ho,hb4⟩ | ⟨ho,k,hk,hn⟩
      · obtain ⟨n,hn⟩ := VG.Proof.MlDsa.AArch64.KeyGen.bound4 hb4
        refine .inl ⟨by rw [ifp ⟨h1,ho⟩],{ b with rejNTT := max b.rejNTT n },fun e' he' => ?_,
          fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
        dsimp only
        by_cases hlt : e' < 4*g
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega⟩
          have hk : k < 4 := by omega
          rw [e3,(masked_one ho (hco4 k hk)).1,← VG.Proof.MlDsa.AArch64.KeyGen.seed4_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [VG.Proof.MlDsa.AArch64.KeyGen.seed4_eq h hk] at hn
        have hq : (4*g+k)/p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega)
        exact .inr ⟨rfl,Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega)) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl,hn⟩

theorem mask4_taint : ∀ j < 80,(taint.check (Taint.ofRegs [.x28]) (mask4 (sc (oP j)))
    (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (mask4 (sc 0)))).isSome = true := by decide +kernel

theorem tail4_tr {p : Params} {S j : Nat} (hj : j < 80) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.Two p S) (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP j))) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by
    simp only [and24,List.mem_singleton] at hi; subst hi; rfl)
    fun x _ => WP.mono (and24_ok x) fun _ ⟨o,_⟩ =>
      ⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (VG.Proof.MlDsa.AArch64.KeyGen.mask4_taint j hj))

theorem call_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.GS p · (4*g) 4) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (4*g+4) 0)
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)))
        (.seq (.block and24) (mask4 (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g))))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  refine ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.call_ok hP hF hp hg h,
    VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF hp hp' hq h.ks.k1.kc h'.ks.k1.kc,by
        rw [h.seeds,h'.seeds,VG.Proof.MlDsa.AArch64.KeyGen.rho_pub hq]⟩)⟩
  have hc : VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sc oSA4) (VG.Impl.MlDsa.AArch64.KeyGen.aP (4*g)) (sc (oR4 p)) = true := by
    unfold VG.Proof.MlDsa.AArch64.KeyGen.rej4Chk; lay
  have ok := fun x (L : Lay S VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) x) => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (VG.Proof.MlDsa.AArch64.KeyGen.rej4At_tr hP.rej4 (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (VG.Proof.MlDsa.AArch64.KeyGen.tail4_tr (by omega))

theorem expA4_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (4*g) 0) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (4*g+4) 0) (expA4 P p g) := by
  unfold expA4
  refine Piece.seq (Piece.mono
    (Piece.seqR (I := fun j σ s => VG.Proof.MlDsa.AArch64.KeyGen.GS p σ (4*g) j s) 4 0
      (fun j _ hj => VG.Proof.MlDsa.AArch64.KeyGen.slot_piece hF hg (by omega)))
      (fun _ _ _ h => ⟨h,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
      (fun _ _ _ h => by simpa using h)) (VG.Proof.MlDsa.AArch64.KeyGen.call_piece hP hF hg)

theorem sampAll_piece {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.K1 p σ s ∧ s.gpr .x24 = 1) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (p.k*p.ℓ) 0) (expAll P p) := by
  unfold expAll
  have hB : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · 0 0) (VG.Proof.MlDsa.AArch64.KeyGen.KSamp p · (4*(p.k*p.ℓ/4)) 0)
      (VG.Impl.MlDsa.AArch64.Call.seqR (expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (Piece.seqR (I := fun g σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (4*g) 0 s) (p.k*p.ℓ/4) 0
        (fun g _ hg => VG.Proof.MlDsa.AArch64.KeyGen.expA4_piece hP hF (by omega)))
  refine Piece.mono (Piece.seq hB
    (Piece.seqR (I := fun e σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ e 0 s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
      (fun e _ he => VG.Proof.MlDsa.AArch64.KeyGen.expA_piece hP hF (by omega))))
    (fun _ _ _ h => KSamp.zero h.1 h.2) (fun _ _ _ h => ?_)
  have he : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega
  simpa only [he] using h

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestBase`. -/
section

/-!
# ML-DSA key generation on AArch64: after the samplers

Once the samplers are done, with `Â` and `s₁ ‖ s₂` in memory as `A` and `S`
and `x24` as `R` (`Good`), the rest of the function computes the keys from
them, whatever they are (`KR`): after the copies of `ρ` and `K`
(`copies_piece`), the first `np` entries of `s₁ ‖ s₂` packed to `sk`, the
first `nj` of `s₁` in the NTT domain, and the first `nr` rows of `t` packed to
`pk` and `sk`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Proof.MlDsa.KeyGen (t1K t0K Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- After the samplers: the keys from `A`, `S` and `R`, so far. -/
structure KR (p : Params) (σ : State) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (R : BitVec 64) (np nj nr : Nat)
    (s : State) : Prop where
  kc : VG.Proof.MlDsa.AArch64.KeyGen.KC p σ s
  x24 : s.gpr .x24 = R
  good : VG.Proof.MlDsa.AArch64.KeyGen.Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R
  small : ∀ r < p.ℓ + p.k, Small p.η (S r)
  aS : ∀ e < p.k * p.ℓ, PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP e)) (A e)
  s2 : ∀ i < p.k, PolyIs s.mem (pa s (sP p (p.ℓ + i))) (toRq (S (p.ℓ + i)))
  s1 : ∀ j < p.ℓ, PolyIs s.mem (pa s (sP p j)) (if j < nj then VG.Spec.MlDsa.ntt (toRq (S j)) else toRq (S j))
  pk0 : bytesAt s.mem (pa s (.x26, 0)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ
  sk0 : bytesAt s.mem (pa s (.x27, 0)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ
  sk1 : bytesAt s.mem (pa s (.x27, 32)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ
  packs : ∀ r < np, bytesAt s.mem (pa s (.x27, 128 + lenS p * r)) (lenS p) = VG.Spec.MlDsa.bitPack (S r) p.η p.η
  rows : ∀ i < nr, bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 ∧
    bytesAt s.mem (pa s (.x27, oT0 p + 416 * i)) 416 = VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096

/-- A piece that writes `ws` keeps what `KR` says. -/
structure KRChk (p : Params) (np nj nr : Nat) (ws : List (Ptr × Nat)) : Prop where
  kc : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ws = true
  aS : ∀ e < p.k * p.ℓ, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (VG.Impl.MlDsa.AArch64.KeyGen.aP e) 1024 = true
  s2 : ∀ i < p.k, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sP p (p.ℓ + i)) 1024 = true
  s1 : ∀ j < p.ℓ, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (sP p j) 1024 = true
  pk0 : keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x26, 0) 32 = true
  sk0 : keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x27, 0) 32 = true
  sk1 : keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x27, 32) 32 = true
  packs : ∀ r < np, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x27, 128 + lenS p * r) (lenS p) = true
  rows : ∀ i < nr, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x26, 32 + 320 * i) 320 = true ∧
    keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ws (.x27, oT0 p + 416 * i) 416 = true

/-- Proves a `KRChk`, in each case of `η`. -/
syntax "krchk " term:max : tactic
macro_rules
  | `(tactic| krchk $hF) => `(tactic| (
      have := ($hF).k; have := ($hF).l; have := ($hF).kl; have := ($hF).scr
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
      (try unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk) <;>
      first
        | lay [($hF).pk, ($hF).sk]
        | rcases ($hF).eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lay [($hF).pk, ($hF).sk, hlen]))

theorem keepB_append {rbs wbs : List (Reg × Nat)} {ws₁ ws₂ : List (Ptr × Nat)} {q : Ptr} {l : Nat}
    (h₁ : keepB rbs wbs ws₁ q l = true) (h₂ : keepB rbs wbs ws₂ q l = true) :
    keepB rbs wbs (ws₁ ++ ws₂) q l = true := by
  simp only [keepB, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

theorem kcChk_append {p : Params} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ws₁ = true)
    (h₂ : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ws₂ = true) : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p (ws₁ ++ ws₂) = true := by
  simp only [VG.Proof.MlDsa.AArch64.KeyGen.kcChk, Bool.and_eq_true] at *
  exact ⟨VG.Proof.MlDsa.AArch64.KeyGen.keepB_append h₁.1 h₂.1, VG.Proof.MlDsa.AArch64.KeyGen.keepB_append h₁.2 h₂.2⟩

/-- The checks of two pieces of writes, for both. -/
theorem KRChk.append {p : Params} {np nj nr : Nat} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr ws₁)
    (h₂ : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr ws₂) : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr (ws₁ ++ ws₂) :=
  ⟨VG.Proof.MlDsa.AArch64.KeyGen.kcChk_append h₁.kc h₂.kc, fun e he => VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.aS e he) (h₂.aS e he),
    fun i hi => VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.s2 i hi) (h₂.s2 i hi), fun j hj => VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.s1 j hj) (h₂.s1 j hj),
    VG.Proof.MlDsa.AArch64.KeyGen.keepB_append h₁.pk0 h₂.pk0, VG.Proof.MlDsa.AArch64.KeyGen.keepB_append h₁.sk0 h₂.sk0, VG.Proof.MlDsa.AArch64.KeyGen.keepB_append h₁.sk1 h₂.sk1,
    fun r hr => VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.packs r hr) (h₂.packs r hr),
    fun i hi => ⟨VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.rows i hi).1 (h₂.rows i hi).1, VG.Proof.MlDsa.AArch64.KeyGen.keepB_append (h₁.rows i hi).2 (h₂.rows i hi).2⟩⟩

/-! The checks of a write to one region, proved once for any region (`krchk` on a
literal list of writes costs seconds). -/

/-- A write to `scratch` outside the saved registers and the polynomials. -/
theorem KRChk.x28 {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ SV ∨ SV + 48 ≤ o) (h2 : o + n ≤ oP 0 ∨ oP (p.k * p.ℓ + p.ℓ + p.k) ≤ o) (h3 : o + n ≤ VG.Proof.MlDsa.AArch64.KeyGen.scrLen p) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr [((.x28, o), n)] := by
  simp only [SV, oP] at h1 h2
  rw [hF.scr] at h3
  krchk hF

/-- A write to `pk` after the rows so far. -/
theorem KRChk.x26 {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : 32 + 320 * nr ≤ o) (h2 : o + n ≤ p.pkLen) : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr [((.x26, o), n)] := by
  rw [hF.pk] at h2
  krchk hF

/-- A write to `sk` after `ρ` and `K`, outside the entries packed and the rows so far. -/
theorem KRChk.x27 {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {np nj nr : Nat} (hnp : np ≤ p.ℓ + p.k) (hnr : nr ≤ p.k) {o n : Nat}
    (h0 : 64 ≤ o) (hp : o + n ≤ 128 ∨ 128 + lenS p * np ≤ o) (hr : o + n ≤ oT0 p ∨ oT0 p + 416 * nr ≤ o)
    (h2 : o + n ≤ p.skLen) : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr [((.x27, o), n)] := by
  rw [hF.sk] at h2
  simp only [oT0] at hr h2
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> rw [hlen] at hp hr h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (try refine ⟨?_, ?_⟩) <;>
  (try unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk) <;> lay [hF.pk, hF.sk, hlen]

theorem KR.keep {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S' : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S' σ) {A : Nat → VG.Spec.MlDsa.Poly}
    {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat} {s s' : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np nj nr s)
    {ws : List (Ptr × Nat)} (hP : PPostB S' s s' ws) (h24 : s'.gpr .x24 = s.gpr .x24) (hc : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p np nj nr ws) :
    VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np nj nr s' := by
  have L := h.kc.lay hF hp
  exact ⟨h.kc.step hF hp hP hc.kc, h24.trans h.x24, h.good, h.small,
    fun e he => L.keepPoly hP (hc.aS e he) (h.aS e he), fun i hi => L.keepPoly hP (hc.s2 i hi) (h.s2 i hi),
    fun j hj => L.keepPoly hP (hc.s1 j hj) (h.s1 j hj), by rw [L.keepBytes hP hc.pk0]; exact h.pk0,
    by rw [L.keepBytes hP hc.sk0]; exact h.sk0, by rw [L.keepBytes hP hc.sk1]; exact h.sk1,
    fun r hr => by rw [L.keepBytes hP (hc.packs r hr)]; exact h.packs r hr,
    fun i hi => ⟨by rw [L.keepBytes hP (hc.rows i hi).1]; exact (h.rows i hi).1,
      by rw [L.keepBytes hP (hc.rows i hi).2]; exact (h.rows i hi).2⟩⟩

/-! ## `ρ` and `K` to the keys -/

/-- After the copies, for some `A`, `S` and `R`. -/
abbrev KR0 (p : Params) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R 0 0 0 s

theorem b26 (o n : Nat) : ∀ w ∈ [(((.x26, o) : Ptr), n)], w.1.1 ∈ keptRegs := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.x26 ∈ keptRegs; decide

theorem b27 (o n : Nat) : ∀ w ∈ [(((.x27, o) : Ptr), n)], w.1.1 ∈ keptRegs := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; show Reg.x27 ∈ keptRegs; decide

theorem copies_ok {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S' : Nat} {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S' σ) {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) : WP isa (.block copies) s (VG.Proof.MlDsa.AArch64.KeyGen.KR0 p σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.k1.kc.lay hF hp
  unfold copies
  rw [WP.block_append_iff, WP.block_append_iff]
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  refine WP.mono (copyP_ok L (dst := (.x26, 0)) (src := sc oHX) (by unfold copyPChk; lay [hF.pk, hF.sk]))
    fun s₁ ⟨hP₁, k₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁
  refine WP.mono (copyP_ok L₁ (dst := (.x27, 0)) (src := sc oHX) (by unfold copyPChk; lay [hF.pk, hF.sk]))
    fun s₂ ⟨hP₂, k₂, hb₂⟩ => ?_
  have L₂ := L₁.post hP₂
  refine WP.mono (copyP_ok L₂ (dst := (.x27, 32)) (src := sc (oHX + 96))
    (by unfold copyPChk; lay [hF.pk, hF.sk])) fun s₃ ⟨hP₃, k₃, hb₃⟩ => ?_
  have hP := PPostB.app (PPostB.app hP₁ hP₂ (VG.Proof.MlDsa.AArch64.KeyGen.b27 _ _)) hP₃ (VG.Proof.MlDsa.AArch64.KeyGen.b27 _ _)
  have h24 : s₃.gpr .x24 = s.gpr .x24 := by rw [k₃.get .x24, k₂.get .x24, k₁.get .x24]
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  have hc : VG.Proof.MlDsa.AArch64.KeyGen.kcChk p ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)]) = true ∧
      (∀ e < p.k * p.ℓ, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)])
        (VG.Impl.MlDsa.AArch64.KeyGen.aP e) 1024 = true) ∧
      (∀ r < p.ℓ + p.k, keepB VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) ([((.x26, 0), 32)] ++ [((.x27, 0), 32)] ++ [((.x27, 32), 32)])
        (sP p r) 1024 = true) :=
    ⟨by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay [hF.pk, hF.sk], fun _ _ => by lay [hF.pk, hF.sk],
      fun _ _ => by lay [hF.pk, hF.sk]⟩
  have hHX₁ : bytesAt s₁.mem (pa s₁ (sc oHX)) 128 = VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ := by
    rw [L.keepBytes hP₁ (by lay [hF.pk])]; exact h.k1.hx
  have hHX₂ : bytesAt s₂.mem (pa s₂ (sc oHX)) 128 = VG.Proof.MlDsa.AArch64.KeyGen.hxOf p σ := by
    rw [L₁.keepBytes hP₂ (by lay [hF.pk, hF.sk])]; exact hHX₁
  have e1 : bytesAt s.mem (pa s (sc oHX)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ := by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.rho_eq, ← h.k1.hx, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e1' : bytesAt s₁.mem (pa s₁ (sc oHX)) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ := by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.rho_eq, ← hHX₁, Proof.MlKem.bytesAt_take _ _ (show 32 ≤ 128 by decide)]
  have e2 : bytesAt s₂.mem (pa s₂ (sc (oHX + 96))) 32 = VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ := by
    rw [VG.Proof.MlDsa.AArch64.KeyGen.kOf_eq, ← hHX₂, Proof.MlKem.bytesAt_slice _ _ (show 96 + 32 ≤ 128 by decide), VG.Proof.MlDsa.AArch64.KeyGen.sc_add]
  refine ⟨A, S, s.gpr .x24, ⟨h.k1.kc.step hF hp hP hc.1, h24, hG, fun r hr => (hS r hr).2,
    fun e he => L.keepPoly hP (hc.2.1 e he) (hA e he),
    fun i hi => L.keepPoly hP (hc.2.2 _ (by omega)) (hS (p.ℓ + i) (by omega)).1,
    fun j hj => by rw [ifn (Nat.not_lt_zero j)]; exact L.keepPoly hP (hc.2.2 j (by omega)) (hS j (by omega)).1,
    ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  · rw [L₂.keepBytes hP₃ (by lay [hF.pk, hF.sk]), L₁.keepBytes hP₂ (by lay [hF.pk, hF.sk]),
      hP₁.pa (show Reg.x26 ∈ keptRegs by decide), hb₁, e1]
  · rw [L₂.keepBytes hP₃ (by lay [hF.pk, hF.sk]), hP₂.pa (show Reg.x27 ∈ keptRegs by decide), hb₂, e1']
  · rw [hP₃.pa (show Reg.x27 ∈ keptRegs by decide), hb₃, e2]

theorem copies_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S : Nat} :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.AArch64.KeyGen.KR0 p) (.block copies) :=
  ⟨fun _ _ hp h => VG.Proof.MlDsa.AArch64.KeyGen.copies_ok hF hp h,
    VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := VG.Proof.MlDsa.AArch64.KeyGen.Two p S) (taintRel [.x25, .x26, .x27, .x28] (fun x y h => h.bases) (by taint_decide))
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.k1.kc h₂.k1.kc⟩

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack`. -/
section

/-!
# ML-DSA key generation on AArch64: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {q : Addr} {f : VG.Spec.MlDsa.Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : VG.Spec.MlDsa.Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem range_of {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x))
    (hs : Small η x) : BpRange m q η η := by
  intro i hi
  have hx := VG.Proof.MlDsa.AArch64.KeyGen.small_mem hs hi
  rw [VG.Proof.MlDsa.AArch64.KeyGen.coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem bpOk_eta {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) : BpOk p.η p.η (lenS p) := by
  rcases hF.eta with ⟨h, e⟩ | ⟨h, e⟩ <;> exact ⟨by rw [h]; decide, by rw [e, h]; decide, by rw [e, h]; decide⟩

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (pa s (sP p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

/-! ## `BitPack` of `s₁ ‖ s₂` -/

theorem packS_chk {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    rwChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sP p r) 1024 (.x27, 128 + lenS p * r) (lenS p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have hlr : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  unfold rwChk
  lay [hF.pk, hF.sk]

theorem packS_ok {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State}
    (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S' σ) {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R r 0 0 s) : WP isa (packS P p r) s (VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (r + 1) 0 0) := by
  have L := h.kc.lay hF hp
  have hS := h.sPoly hr
  unfold packS
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (VG.Proof.MlDsa.AArch64.KeyGen.packS_chk hF hr) (VG.Proof.MlDsa.AArch64.KeyGen.bpOk_eta hF) hS.1
    (VG.Proof.MlDsa.AArch64.KeyGen.range_of (VG.Proof.MlDsa.AArch64.KeyGen.eta_le hF) hS (h.small r hr))) fun s' ⟨hP', x', hb⟩ => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF hp hP' x' (KRChk.x27 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr)
    (Nat.zero_le _) (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega))
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, hS.2,
      Proof.MlDsa.KeyGen.modPm_toRq (VG.Proof.MlDsa.AArch64.KeyGen.small_big (VG.Proof.MlDsa.AArch64.KeyGen.eta_le hF) (h.small r' hr))]

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np nj nr s

theorem packS_tr {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p r 0 0)) (packS P p r) fun _ _ => True := by
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧ (Reduced x.mem (pa x (sP p r)) ∧ BpRange x.mem (pa x (sP p r)) p.η p.η) ∧
    (Reduced y.mem (pa y (sP p r)) ∧ BpRange y.mem (pa y (sP p r)) p.η p.η)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, VG.Proof.MlDsa.AArch64.KeyGen.range_of (VG.Proof.MlDsa.AArch64.KeyGen.eta_le hF) (h₁.sPoly hr) (h₁.small r hr)⟩,
        ⟨(h₂.sPoly hr).1, VG.Proof.MlDsa.AArch64.KeyGen.range_of (VG.Proof.MlDsa.AArch64.KeyGen.eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩⟩
  unfold packS
  exact bpAt_tr hP.bitPack (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.packS_chk hF hr) (VG.Proof.MlDsa.AArch64.KeyGen.bpOk_eta hF) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem packS_piece {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p r 0 0) (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.packS_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, VG.Proof.MlDsa.AArch64.KeyGen.packS_tr hP hF hr⟩

/-! ## `NTT` of `s₁` -/

theorem nttS_chk {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {j : Nat} (hj : j < p.ℓ) :
    ipChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (sP p j) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold ipChk; lay

theorem nttS_ok {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State}
    (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S' σ) {j : Nat} (hj : j < p.ℓ) {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) j 0 s) : WP isa (nttS P p j) s (VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.kc.lay hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  unfold nttS nttAt
  refine WP.mono (ipAt_ok (t := VG.Spec.MlDsa.ntt) hP.s64 hP.ntt L (VG.Proof.MlDsa.AArch64.KeyGen.nttS_chk hF hj) hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact ⟨h.kc.step hF hp hP' (by unfold VG.Proof.MlDsa.AArch64.KeyGen.kcChk; lay [hF.pk, hF.sk]), x'.trans h.x24, h.good,
    h.small, fun e he => L.keepPoly hP' (by lay [hF.pk, hF.sk]) (h.aS e he),
    fun i hi => L.keepPoly hP' (by lay [hF.pk, hF.sk]) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP'.pa (p := sP p j') (show Reg.x28 ∈ keptRegs by decide), ← hS.2]
        exact hb
      else by
        have := L.keepPoly hP' (by lay [hF.pk, hF.sk]) (h.s1 j' hj')
        by_cases hlt : j' < j
        · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this
        · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (VG.Spec.MlDsa.ntt (toRq (S j'))) (toRq (S j'))] at this,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk])]; exact h.pk0,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk])]; exact h.sk0,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk])]; exact h.sk1,
    fun r hr => by
      have : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      rw [L.keepBytes hP' (by rcases hlen with hlen | hlen <;> lay [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem nttS_tr {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {j : Nat} (hj : j < p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.AArch64.KeyGen.R p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) j 0)) (nttS P p j) fun _ _ => True := by
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧ Reduced x.mem (pa x (sP p j)) ∧ Reduced y.mem (pa y (sP p j))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, (h₁.s1 j hj).1,
      (h₂.s1 j hj).1⟩
  unfold nttS nttAt
  exact ipAt_tr (t := VG.Spec.MlDsa.ntt) hP.ntt (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.nttS_chk hF hj) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem nttS_piece {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {j : Nat}
    (hj : j < p.ℓ) : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) j 0) (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.nttS_ok hP hF hp hj h) fun _ h => ⟨A, S, R, h⟩, VG.Proof.MlDsa.AArch64.KeyGen.nttS_tr hP hF hj⟩

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow`. -/
section

/-!
# ML-DSA key generation on AArch64: the rows of `t`

Row `i` of `t`: the sum of the products `Â[i, j] ŝ₁[j]` in `t` (`mul_ok`,
`mulAdd_ok`), `NTT⁻¹` of it plus `s₂[i]` (`inv_ok`, `addS2_ok`), then
`Power2Round` (`p2r_ok`) and `t₁[i]` packed to `pk` and `t₀[i]` to `sk`
(`sbp_ok`, `bp_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega)
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → VG.Spec.MlDsa.Poly) → (Nat → IPoly) → VG.Spec.MlDsa.Poly) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (pa s (tP p)) (g A S)

theorem KR.polyA {p : Params} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {np nj nr : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (VG.Proof.MlDsa.AArch64.KeyGen.idx_lt hi hj)

theorem KR.polyS {p : Params} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem (pa s (sP p j)) (VG.Spec.MlDsa.ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem range_t0 {m : Mem} {q : Addr} {t : VG.Spec.MlDsa.Poly} (h : PolyIs m q (t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)) :
    BpRange m q 4095 4096 := fun j hj => by
  rw [VG.Proof.MlDsa.AArch64.KeyGen.coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  omega

theorem modPm_t0 (t : VG.Spec.MlDsa.Poly) :
    ((t.map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (VG.Spec.MlDsa.power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The checks of the calls -/

section
variable {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k)
include hF hi

theorem mul_chk {j : Nat} (hj : j < p.ℓ) : mulChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (tP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j)) (sP p j) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have := VG.Proof.MlDsa.AArch64.KeyGen.idx_lt hi hj
  unfold mulChk; lay

theorem inv_chk : ipChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (tP p) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold ipChk; lay

theorem add_chk : accChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (tP p) (sP p (p.ℓ + i)) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold accChk; lay

theorem p2r_chk : VG.Proof.MlDsa.AArch64.KeyGen.p2rChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (tP p) (t1P p) (t0P p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold VG.Proof.MlDsa.AArch64.KeyGen.p2rChk; lay

theorem sbp_chk : rwChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (t1P p) 1024 (.x26, 32 + 320 * i) 320 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  unfold rwChk; lay [hF.pk]

theorem bp_chk : rwChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) (t0P p) 1024 (.x27, oT0 p + 416 * i) 416 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  unfold rwChk; lay [hF.pk, hF.sk]

end

/-! ## The checks of the writes of a row, once each -/

theorem chk_poly {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(sc (oP (p.k * p.ℓ + p.ℓ + p.k + j)), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact KRChk.x28 hF (by omega) (by omega) (.inr (by simp only [SV, oP]; omega))
    (.inr (by simp only [oP]; omega)) (by rw [hF.scr]; simp only [oP]; omega)

theorem chk_t {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024)] := by
  have := VG.Proof.MlDsa.AArch64.KeyGen.chk_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem chk_inv {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024), (sc oSS, 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact (VG.Proof.MlDsa.AArch64.KeyGen.chk_t hF hi).append (ws₁ := [_]) (KRChk.x28 (o := oSS) (n := 1024) hF (by omega)
    (by omega) (.inr (by decide)) (.inl (by decide)) (by rw [hF.scr]; simp only [oSS]; omega))

theorem chk_p2r {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [(t1P p, 1024), (t0P p, 1024)] :=
  (VG.Proof.MlDsa.AArch64.KeyGen.chk_poly hF hi (j := 1) (by decide)).append (ws₁ := [_]) (VG.Proof.MlDsa.AArch64.KeyGen.chk_poly hF hi (j := 2) (by decide))

theorem chk_sbp {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [((.x26, 32 + 320 * i), 320)] :=
  KRChk.x26 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega)

theorem chk_bp {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k) :
    VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ i [((.x27, oT0 p + 416 * i), 416)] := by
  have := hF.k; have := hF.l
  exact KRChk.x27 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega) (.inr (by simp only [oT0]; omega))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega)

theorem sbpOk_t1 : SbpOk 1023 320 := ⟨by decide, by decide, by decide⟩

theorem bpOk_t0 : BpOk 4095 4096 416 := ⟨by decide, by decide, by decide⟩

/-! ## The calls -/

section
variable {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State} (hp : VG.Proof.MlDsa.AArch64.KeyGen.kgPre p S' σ)
  {i : Nat} (hi : i < p.k)
include hP hF hp hi

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem mul_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => dotK p A S i 1) A S s' := by
  have hl := hF.l
  have L := h.kc.lay hF hp
  have hA := h.polyA hi (j := 0) (by omega)
  have hc := VG.Proof.MlDsa.AArch64.KeyGen.mul_chk hF hi (j := 0) (by omega)
  rw [Nat.add_zero] at hA hc
  have hS := h.polyS (j := 0) (by omega)
  refine WP.mono (mulAt_ok hP.s64 hP.mul L hc hA.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.AArch64.KeyGen.tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem mulAdd_ok {j : Nat} (hj : j < p.ℓ) {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => dotK p A S i j) A S s) :
    WP isa (mulAddAt P (tP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => dotK p A S i (j + 1)) A S s' := by
  dsimp only [VG.Proof.MlDsa.AArch64.KeyGen.tIs] at ht
  have L := h.kc.lay hF hp
  have hA := h.polyA hi hj
  have hS := h.polyS hj
  refine WP.mono (mulAddAt_ok hP.s64 hP.mulAdd L (VG.Proof.MlDsa.AArch64.KeyGen.mul_chk hF hi hj) ht.1 hA.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.AArch64.KeyGen.tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hS.2, ← ht.2]
  exact hb

/-- `t = NTT⁻¹(t)`. -/
theorem inv_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => dotK p A S i p.ℓ) A S s) :
    WP isa (invNttAt P (sc oSS) (tP p)) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) A S s' := by
  dsimp only [VG.Proof.MlDsa.AArch64.KeyGen.tIs] at ht
  have L := h.kc.lay hF hp
  unfold invNttAt
  refine WP.mono (ipAt_ok (t := VG.Spec.MlDsa.nttInv) hP.s64 hP.invNtt L (VG.Proof.MlDsa.AArch64.KeyGen.inv_chk hF hi) ht.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_inv hF hi), ?_⟩
  rw [VG.Proof.MlDsa.AArch64.KeyGen.tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), ← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem addS2_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => tK p A S i) A S s' := by
  dsimp only [VG.Proof.MlDsa.AArch64.KeyGen.tIs] at ht
  have L := h.kc.lay hF hp
  have hS := h.s2 i hi
  unfold addAt
  refine WP.mono (accAt_ok (op := VG.Spec.MlDsa.add) hP.s64 hP.add L (VG.Proof.MlDsa.AArch64.KeyGen.add_chk hF hi) ht.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_t hF hi), ?_⟩
  rw [VG.Proof.MlDsa.AArch64.KeyGen.tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : VG.Proof.MlDsa.AArch64.KeyGen.tIs p (fun A S => tK p A S i) A S s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) := by
  dsimp only [VG.Proof.MlDsa.AArch64.KeyGen.tIs] at ht
  have L := h.kc.lay hF hp
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.p2rAt_ok hP.s64 hP.power2Round L (VG.Proof.MlDsa.AArch64.KeyGen.p2r_chk hF hi) ht.1) fun s' ⟨hP', x', h1, h0⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_p2r hF hi), ?_, ?_⟩
  · rw [hP'.pa (p := t1P p) (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP'.pa (p := t0P p) (show Reg.x28 ∈ keptRegs by decide), ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) s fun s' =>
      VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.x26, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L (VG.Proof.MlDsa.AArch64.KeyGen.sbp_chk hF hi) VG.Proof.MlDsa.AArch64.KeyGen.sbpOk_t1 (VG.Proof.MlDsa.AArch64.KeyGen.t1_bound h1))
    fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_sbp hF hi), L.keepPoly hP' (by lay [hF.pk]) h0, ?_⟩
  rw [hP'.pa (show Reg.x26 ∈ keptRegs by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) s
      (VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (VG.Proof.MlDsa.AArch64.KeyGen.bp_chk hF hi) VG.Proof.MlDsa.AArch64.KeyGen.bpOk_t0 h0.1 (VG.Proof.MlDsa.AArch64.KeyGen.range_t0 h0))
    fun s' ⟨hP', x', hb⟩ => ?_
  have hk' := h.keep hF hp hP' x' (VG.Proof.MlDsa.AArch64.KeyGen.chk_bp hF hi)
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by
      have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
      rw [L.keepBytes hP' (by lay [hF.pk, hF.sk])]; exact h1, ?_⟩
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, h0.2, VG.Proof.MlDsa.AArch64.KeyGen.modPm_t0]
    rfl

end

/-! ## The pieces of a row -/

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (i : Nat) (f : (Nat → VG.Spec.MlDsa.Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat} (hi : i < p.k)
include hP hF hi

theorem mul_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => dotK p A S i 1))
    (mulAt P (tP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i)) (sP p 0)) := by
  have hl := hF.l
  have hc := VG.Proof.MlDsa.AArch64.KeyGen.mul_chk hF hi (j := 0) (by omega)
  rw [Nat.add_zero] at hc
  refine ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.mul_ok hP hF hp hi h) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧
    (Reduced x.mem (pa x (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i))) ∧ Reduced x.mem (pa x (sP p 0))) ∧
    (Reduced y.mem (pa y (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i))) ∧ Reduced y.mem (pa y (sP p 0)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => by
      have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
      rw [Nat.add_zero] at a₁ a₂
      exact ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨a₁.1, (h₁.polyS (j := 0) (by omega)).1⟩,
        ⟨a₂.1, (h₂.polyS (j := 0) (by omega)).1⟩⟩
  exact mulAt_tr hP.mul (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) hc fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem mulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => dotK p A S i j)) (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => dotK p A S i (j + 1)))
      (mulAddAt P (tP p) (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j)) (sP p j)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.mulAdd_ok hP hF hp hi hj h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j))) ∧ Reduced x.mem (pa x (sP p j))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (VG.Impl.MlDsa.AArch64.KeyGen.aP (p.ℓ * i + j))) ∧ Reduced y.mem (pa y (sP p j)))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩,
        ⟨t₂.1, (h₂.polyA hi hj).1, (h₂.polyS hj).1⟩⟩
  exact mulAddAt_tr hP.mulAdd (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.mul_chk hF hi hj) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem inv_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => dotK p A S i p.ℓ))
    (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ))) (invNttAt P (sc oSS) (tP p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.inv_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  unfold invNttAt
  exact ipAt_tr (t := VG.Spec.MlDsa.nttInv) hP.invNtt (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.inv_chk hF hi) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem addS2_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => VG.Spec.MlDsa.nttInv (dotK p A S i p.ℓ)))
    (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => tK p A S i)) (addAt P (tP p) (sP p (p.ℓ + i))) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  unfold addAt
  exact accAt_tr (op := VG.Spec.MlDsa.add) hP.add (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.add_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2)

theorem p2r_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => tK p A S i)) (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.p2rIs p i))
    (power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact VG.Proof.MlDsa.AArch64.KeyGen.p2rAt_tr hP.power2Round (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.p2r_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → VG.Spec.MlDsa.Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (VG.Spec.MlDsa.power2Round c).2) ∧
    bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = VG.Spec.MlDsa.simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.p2rIs p i)) (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.sbpIs p i))
    (simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, VG.Proof.MlDsa.AArch64.KeyGen.t1_bound t₁.1, VG.Proof.MlDsa.AArch64.KeyGen.t1_bound t₂.1⟩
  exact sbpAt_tr hP.simpleBitPack (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.sbp_chk hF hi) VG.Proof.MlDsa.AArch64.KeyGen.sbpOk_t1 fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem bp_piece : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.sbpIs p i)) (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := fun x y => VG.Proof.MlDsa.AArch64.KeyGen.Two p S' x y ∧
    (Reduced x.mem (pa x (t0P p)) ∧ BpRange x.mem (pa x (t0P p)) 4095 4096) ∧
    (Reduced y.mem (pa y (t0P p)) ∧ BpRange y.mem (pa y (t0P p)) 4095 4096)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1.1, VG.Proof.MlDsa.AArch64.KeyGen.range_t0 t₁.1⟩, ⟨t₂.1.1, VG.Proof.MlDsa.AArch64.KeyGen.range_t0 t₂.1⟩⟩
  exact bpAt_tr hP.bitPack (VG.Proof.MlDsa.AArch64.KeyGen.kgOk p) (VG.Proof.MlDsa.AArch64.KeyGen.bp_chk hF hi) VG.Proof.MlDsa.AArch64.KeyGen.bpOk_t0 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

end

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main`. -/
section

/-!
# ML-DSA key generation on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The function, piece by piece, for any parameter set of Table 1 and any
verified implementations of the primitives (`keyGen_piece`): it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds; it leaks only
the pointers, `ρ` and what `RejBoundedPoly` leaks; so it meets the shared
contract (`keyGen_verified`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {i : Nat}
    (hi : i < p.k) : VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ (i + 1)) (VG.Impl.MlDsa.AArch64.KeyGen.row P p i) := by
  have hl := hF.l
  unfold VG.Impl.MlDsa.AArch64.KeyGen.row
  refine (VG.Proof.MlDsa.AArch64.KeyGen.mul_piece hP hF hi).seq (Piece.seq ?_ ((VG.Proof.MlDsa.AArch64.KeyGen.inv_piece hP hF hi).seq ((VG.Proof.MlDsa.AArch64.KeyGen.addS2_piece hP hF hi).seq
    ((VG.Proof.MlDsa.AArch64.KeyGen.p2r_piece hP hF hi).seq ((VG.Proof.MlDsa.AArch64.KeyGen.sbp_piece hP hF hi).seq (VG.Proof.MlDsa.AArch64.KeyGen.bp_piece hP hF hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.AArch64.KeyGen.RowI p i (VG.Proof.MlDsa.AArch64.KeyGen.tIs p fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => VG.Proof.MlDsa.AArch64.KeyGen.mulAdd_piece hP hF hi (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      VG.Proof.MlDsa.AArch64.KeyGen.flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pa_zero (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

theorem pk_bytes {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.x26, 0)) p.pkLen = pkK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x26) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ := by rw [← VG.Proof.MlDsa.AArch64.KeyGen.pa_zero]; exact h.pk0
  rw [hF.pk, VG.Proof.MlDsa.AArch64.KeyGen.pa_zero, Proof.MlKem.bytesAt_add, h0,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x26) 32 320 p.k, pkK, VG.Proof.MlDsa.AArch64.KeyGen.t1Max_eq]
  exact congrArg _ (VG.Proof.MlDsa.AArch64.KeyGen.flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.x27, 0)) p.skLen = skK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) (VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x27) 32 = VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ := by rw [← VG.Proof.MlDsa.AArch64.KeyGen.pa_zero]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 32) 32 = VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ)) 64 :=
    htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, VG.Proof.MlDsa.AArch64.KeyGen.pa_zero, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (oT0 p) 416 p.k, skK]
  rw [VG.Proof.MlDsa.AArch64.KeyGen.flatMap_congr_mem (g := fun r => VG.Spec.MlDsa.bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    VG.Proof.MlDsa.AArch64.KeyGen.flatMap_congr_mem (g := fun i => VG.Spec.MlDsa.bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, VG.Proof.MlDsa.AArch64.KeyGen.KR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ)) 64

theorem trHash_chk {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    hashChk VG.Proof.MlDsa.AArch64.KeyGen.kgR (VG.Proof.MlDsa.AArch64.KeyGen.kgW p) [⟨.x26, 0, p.pkLen⟩] ⟨.x27, 64, 64⟩ = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := VG.Proof.MlDsa.AArch64.KeyGen.scr_eq p
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  unfold hashChk pieceChk; lay [hF.pk, hF.sk]

theorem trHash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ VG.Proof.MlDsa.AArch64.KeyGen.bases, x.gpr r = y.gpr r) →
      RelCT isa P ((trHashWith keccak.callee) p) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaTrHashTaint p hp
  exact VectorTaint.relRegs VG.Proof.MlDsa.AArch64.KeyGen.bases hr hh

theorem trHash_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S' : Nat} (h16 : 16 ≤ S') (hSl : S' < 2 ^ 64) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) (VG.Proof.MlDsa.AArch64.KeyGen.KFin p) ((trHashWith keccak.callee) p) := by
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := VG.Proof.MlDsa.AArch64.KeyGen.Two p S') (VG.Proof.MlDsa.AArch64.KeyGen.trHash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHashWith
  refine WP.mono (shake_ok h16 hSl L (by simp) (VG.Proof.MlDsa.AArch64.KeyGen.trHash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨A, S, R, ?_, ?_⟩
  · have hc : VG.Proof.MlDsa.AArch64.KeyGen.KRChk p (p.ℓ + p.k) p.ℓ p.k [((.x28, 0), 200), ((.x28, 200), 640), ((.x27, 64), 64)] :=
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      ((KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega)).append (ws₁ := [_])
      (KRChk.x27 hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega)) (by rw [hF.sk, oT0]; omega)))
    exact h.keep hF hp hP' x' hc
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), ho]
    exact congrArg (Spec.MlDsa.H · 64) (VG.Proof.MlDsa.AArch64.KeyGen.pk_bytes hF h)

/-! ## The return -/

theorem outcome_of {p : Params} {σ : State} {A : Nat → VG.Spec.MlDsa.Poly} {S : Nat → IPoly} {R : BitVec 64}
    (hl : 0 < p.ℓ) (hG : VG.Proof.MlDsa.AArch64.KeyGen.Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ)) (R.setWidth 32)
      (pkK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ), skK p A S (VG.Proof.MlDsa.AArch64.KeyGen.rhoOf p σ) (VG.Proof.MlDsa.AArch64.KeyGen.kOf p σ)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (VG.Proof.MlDsa.AArch64.KeyGen.xiOf σ) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (VG.Proof.MlDsa.AArch64.KeyGen.idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

theorem epi_piece {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) {S' : Nat} :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (VG.Proof.MlDsa.AArch64.KeyGen.KFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s)
      (.block VG.Impl.MlDsa.AArch64.KeyGen.epi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, VG.Proof.MlDsa.AArch64.KeyGen.rel_of (Q := VG.Proof.MlDsa.AArch64.KeyGen.Two p S') (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => VG.Proof.MlDsa.AArch64.KeyGen.kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := VG.Proof.MlDsa.AArch64.KeyGen.svP) (l := 48) (by have := VG.Proof.MlDsa.AArch64.KeyGen.scr_ge hF; lay)
    rwa [pa, h.kc.top.x28] at this
  refine WP.mono (VG.Proof.MlDsa.AArch64.KeyGen.epi_ok h.kc.top hin) fun s' ⟨ha, hr, hm⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  have e26 : pa s (.x26, 0) = σ.gpr .x1 := by rw [VG.Proof.MlDsa.AArch64.KeyGen.pa_zero, h.kc.top.x26]
  have e27 : pa s (.x27, 0) = σ.gpr .x2 := by rw [VG.Proof.MlDsa.AArch64.KeyGen.pa_zero, h.kc.top.x27]
  rw [hr, h.x24, hm, ← e26, ← e27, VG.Proof.MlDsa.AArch64.KeyGen.pk_bytes hF h, VG.Proof.MlDsa.AArch64.KeyGen.sk_bytes hF h htr]
  exact VG.Proof.MlDsa.AArch64.KeyGen.outcome_of (by have := hF.l; omega) h.good

/-! ## The function -/

theorem rest_piece {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (fun σ s => VG.Proof.MlDsa.AArch64.KeyGen.KSamp p σ (p.k * p.ℓ) (p.ℓ + p.k) s) (VG.Proof.MlDsa.AArch64.KeyGen.KFin p) ((restWith keccak.callee) P p) := by
  unfold restWith
  refine (VG.Proof.MlDsa.AArch64.KeyGen.copies_piece hF).seq (Piece.seq (J := VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ p.k) ?_
      (VG.Proof.MlDsa.AArch64.KeyGen.trHash_piece hF hP.s16 hP.s64))))
  · refine Piece.mono (Piece.seqR (I := fun r => VG.Proof.MlDsa.AArch64.KeyGen.KRx p r 0 0) (p.ℓ + p.k) 0 fun r _ hr => VG.Proof.MlDsa.AArch64.KeyGen.packS_piece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => VG.Proof.MlDsa.AArch64.KeyGen.nttS_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => VG.Proof.MlDsa.AArch64.KeyGen.row_piece hP hF (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece {P : Prims} {S' : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S') {p : Params} (hF : VG.Proof.MlDsa.AArch64.KeyGen.PFacts p) :
    VG.Proof.MlDsa.AArch64.KeyGen.Piece p S' (fun σ s => s = σ)
      (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s) ((keyGenWith keccak.callee) P p) :=
  (VG.Proof.MlDsa.AArch64.KeyGen.pro_piece hF).seq ((VG.Proof.MlDsa.AArch64.KeyGen.seeds_piece hF hP.s16 hP.s64).seq ((VG.Proof.MlDsa.AArch64.KeyGen.sampAll_piece hP hF).seq ((VG.Proof.MlDsa.AArch64.KeyGen.sampS_piece hP hF).seq
    ((VG.Proof.MlDsa.AArch64.KeyGen.rest_piece hP hF).seq (VG.Proof.MlDsa.AArch64.KeyGen.epi_piece hF)))))

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls that use at most `S`
bytes of stack, if the contract is satisfiable. -/
theorem keyGen_verified {P : Prims} {S : Nat} (hP : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk P S) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (Spec.MlDsa.keyGenContract p AArch64.abi S).pre s) :
    Verified AArch64.target ((keyGenWith keccak.callee) P p) (Spec.MlDsa.keyGenContract p AArch64.abi S) :=
  ⟨fun σ hσ => (VG.Proof.MlDsa.AArch64.KeyGen.keyGen_piece hP (VG.Proof.MlDsa.AArch64.KeyGen.pfacts hp)).ok σ σ hσ rfl,
    relStart (Q := fun _ _ => True) (VG.Proof.MlDsa.AArch64.KeyGen.keyGen_piece hP (VG.Proof.MlDsa.AArch64.KeyGen.pfacts hp)).tr, hsat⟩

end VG.Proof.MlDsa.AArch64.KeyGen

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst`. -/
section

/-!
# ML-DSA key generation on AArch64, with this library's primitives

The AArch64 implementations of the primitives (`prims`) are verified with at
most 16 bytes of stack, and their frames use at most that (`prims_ok`), so key
generation with them is verified with 16 bytes of stack (`keyGen44_verified`,
…).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen

theorem prims_okWith : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk (primsWith keccak.callee) 16 where
  s16 := Nat.le_refl _
  sl := by decide
  ntt := by
    have h := Arith.Neon.ntt_verified
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide)
  invNtt := by
    have h := Arith.Neon.nttInv_verified
    unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide)
  mul := CalleeOk.of_verified (by decide) Arith.mul_verified (by decide) (by dsimp only [primsWith]; decide)
  mulAdd := CalleeOk.of_verified (by decide) Arith.mulAdd_verified (by decide) (by dsimp only [primsWith]; decide)
  add := CalleeOk.of_verified (by decide) Arith.add_verified (by decide) (by dsimp only [primsWith]; decide)
  sub := CalleeOk.of_verified (by decide) Arith.sub_verified (by decide) (by dsimp only [primsWith]; decide)
  rejNtt := CalleeOk.of_verified (by decide) (Sample.rejNTT_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.rejNTT_depth keccak])
  rej4 := CalleeOk.of_verified (by decide) (Sample.Rej4.verified keccak.callee.pairedSha3) (by decide)
    (by simp only [primsWith,Sample.Rej4.depth,Nat.mul_zero]; decide)
  rejBounded := CalleeOk.of_verified (by decide) (Sample.rejBounded_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.rejBounded_depth keccak])
  ball := CalleeOk.of_verified (by decide) (Sample.sampleInBall_verifiedWith keccak) (by decide) (by simp [primsWith, Sample.ball_depth keccak])
  power2Round := CalleeOk.of_verified (by decide) Round.power2Round_verified (by decide) (by dsimp only [primsWith]; decide)
  useHint := CalleeOk.of_verified (by decide) Round.useHint_verified (by decide) (by dsimp only [primsWith]; decide)
  normLt := CalleeOk.of_verified (by decide) Round.normLt_verified (by decide) (by dsimp only [primsWith]; decide)
  simpleBitPack := CalleeOk.of_verified (by decide) Pack.simpleBitPack_verified (by decide) (by dsimp only [primsWith]; decide)
  bitPack := CalleeOk.of_verified (by decide) Pack.bitPack_verified (by decide) (by dsimp only [primsWith]; decide)
  bitUnpack := CalleeOk.of_verified (by decide) Pack.bitUnpack_verified (by decide) (by dsimp only [primsWith]; decide)
  unpackT1 := CalleeOk.of_verified (by decide) Pack.unpackT1_verified (by decide) (by dsimp only [primsWith]; decide)
  hintUnpack := CalleeOk.of_verified (by decide) Pack.hintBitUnpack_verified (by decide) (by dsimp only [primsWith]; decide)

/-- A state satisfying `keyGenContract`'s precondition. -/
def kgSat (p : Spec.MlDsa.Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x10000 | .x2 => 0x20000 | .x3 => 0x100000 | _ => 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x10000, p.pkLen⟩, ⟨0x20000, p.skLen⟩, ⟨0x100000, VG.Proof.MlDsa.AArch64.KeyGen.scrLen p⟩]

theorem keyGen_sat (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∃ s, (Spec.MlDsa.keyGenContract p AArch64.abi 16).pre s := by
  rcases hp with rfl | rfl | rfl
  · refine ⟨VG.Proof.MlDsa.AArch64.KeyGen.kgSat Spec.MlDsa.mlDsa44, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨VG.Proof.MlDsa.AArch64.KeyGen.kgSat Spec.MlDsa.mlDsa65, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  · refine ⟨VG.Proof.MlDsa.AArch64.KeyGen.kgSat Spec.MlDsa.mlDsa87, ?_⟩
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]

theorem keyGen44_verifiedWith :
    Verified AArch64.target (keyGen44With keccak.callee) (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen_verified (keccak := keccak) (VG.Proof.MlDsa.AArch64.KeyGen.prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa44 (.inl rfl) (VG.Proof.MlDsa.AArch64.KeyGen.keyGen_sat _ (.inl rfl))

theorem keyGen65_verifiedWith :
    Verified AArch64.target (keyGen65With keccak.callee) (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen_verified (keccak := keccak) (VG.Proof.MlDsa.AArch64.KeyGen.prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa65 (.inr (.inl rfl)) (VG.Proof.MlDsa.AArch64.KeyGen.keyGen_sat _ (.inr (.inl rfl)))

theorem keyGen87_verifiedWith :
    Verified AArch64.target (keyGen87With keccak.callee) (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen_verified (keccak := keccak) (VG.Proof.MlDsa.AArch64.KeyGen.prims_okWith (keccak := keccak)) Spec.MlDsa.mlDsa87 (.inr (.inr rfl)) (VG.Proof.MlDsa.AArch64.KeyGen.keyGen_sat _ (.inr (.inr rfl)))

theorem prims_ok : VG.Proof.MlDsa.AArch64.KeyGen.PrimsOk prims 16 := VG.Proof.MlDsa.AArch64.KeyGen.prims_okWith (keccak := .scalar)

theorem keyGen44_verified :
    Verified AArch64.target keyGen44 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa44 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen44_verifiedWith (keccak := .scalar)

theorem keyGen65_verified :
    Verified AArch64.target keyGen65 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa65 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen65_verifiedWith (keccak := .scalar)

theorem keyGen87_verified :
    Verified AArch64.target keyGen87 (Spec.MlDsa.keyGenContract Spec.MlDsa.mlDsa87 AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.KeyGen.keyGen87_verifiedWith (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.KeyGen

end
