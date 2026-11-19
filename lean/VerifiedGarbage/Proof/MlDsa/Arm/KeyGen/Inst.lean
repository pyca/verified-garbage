module

public import VerifiedGarbage.Impl.MlDsa.Arm.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
public import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestRow
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestRow
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.MlKem.Arm.RowSum
meta import VerifiedGarbage.Proof.MlKem.Arm.RowSum
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Call
meta import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Samp
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlKem.Arm.CallsCT
meta import VerifiedGarbage.Proof.MlKem.Arm.Loops
meta import VerifiedGarbage.Proof.MlKem.Arm.NttInv
meta import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.Arm.Stream.Pad
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedBody
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedBody
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlKem.Arm.Common
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic

/-! ### `MlDsa.Arm.Round.Power2Round`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_power2round`

The loop body is symbolically executed once for any state (`body_ok`); its
values are `Power2Round`'s (`t1_val`, `t0_val`, from `power2Round_eq`), and
the loop (`loop_ok`) in the frame that saves `r4` (`wp_saving`) writes them
all.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Round.P2R

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q n Poly Zq power2Round ofInt)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs NatPolyIs natPolyAt)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS fixS_of_lt fixS_of_ge)
open VG.Impl.MlDsa.Arm.Arith (fixupS)

/-! ## Values -/

/-- What the body stores to `t1`. -/
def bt1 (a : BitVec 32) : BitVec 32 := (a + 4096 - 1) >>> 13

/-- What the body stores to `t0`. -/
def bt0 (a : BitVec 32) : BitVec 32 := fixS ((a + 4096 - 1) <<< 19 >>> 19 - 4096 + 1)

theorem t1_val (r : Zq) : (bt1 (BitVec.ofNat 32 r.val)).toNat = (power2Round r).1.toNat := by
  rw [power2Round_eq]
  simp only [Int.toNat_natCast]
  have h := r.isLt
  generalize r.val = v at h ⊢
  rw [q_eq] at h
  unfold bt1
  bv_omega

theorem t0_val (r : Zq) : (bt0 (BitVec.ofNat 32 r.val)).toNat = (ofInt (power2Round r).2).val := by
  rw [power2Round_t0]
  have h := r.isLt
  generalize r.val = v at h ⊢
  rw [q_eq] at h ⊢
  unfold bt0
  split
  · rw [fixS_of_ge (by bv_omega)]; bv_omega
  · rw [fixS_of_lt (by bv_omega)]; bv_omega

/-! ## The body -/

section
variable {s : State} {x y w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = y) (h2 : s.gpr .r2 = w)
  (h3 : s.gpr .r3 = c)
  (iT : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (o1 : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 4)
  (o0 : InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 iT o1 o0

theorem body_ok :
    WP isa (.block p2rBody) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (y + BitVec.ofNat 32 0))
        (bt1 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))).writeW (State.addr (w + BitVec.ofNat 32 0))
        (bt0 (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r1 = y + 4 ∧ s'.gpr .r2 = w + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [p2rBody, fixupS, bt1, bt0, fixS, h0, h1, h2, h3, iT, o1, o0, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

end

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 4 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0)]
  wr : s.wr = [pR (P s .r1), pR (P s .r2)]
  d01 : (pR (P s .r0)).Disjoint (pR (P s .r1))
  d02 : (pR (P s .r0)).Disjoint (pR (P s .r2))
  d12 : (pR (P s .r1)).Disjoint (pR (P s .r2))
  s0 : (belowA s.sp 4).Disjoint (pR (P s .r0))
  s1 : (belowA s.sp 4).Disjoint (pR (P s .r1))
  s2 : (belowA s.sp 4).Disjoint (pR (P s .r2))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (P s .r0)

theorem pre_of {s : State} (h : (Proof.MlDsa.power2RoundContract Arm.abi 4).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The registers the loop keeps. -/
abbrev fixedR : List Reg := [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The values the loop writes, from the memory `m` it starts with. -/
def val (s₁ : State) (o : Reg) (i : Nat) : BitVec 32 :=
  if o = .r1 then bt1 (coeffAt s₁.mem (P s₁ .r0) i) else bt0 (coeffAt s₁.mem (P s₁ .r0) i)

theorem layout {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) : Layout s₁ [.r0] [.r1, .r2] := by
  have g := hE.gpr
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, g]
  refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, ?_, fun p hp' => ?_⟩
  · simp only [List.mem_singleton] at hp'; subst hp'
    rw [e, hE.rd, hp.rd]; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rw [e] <;> exact hE.wr _ (by rw [hp.wr]; simp)
  · simp only [List.mem_singleton] at hp'; subst hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> rw [e, e]
    exacts [hp.d01, hp.d02]
  · exact List.pairwise_pair.mpr (by rw [e, e]; exact hp.d12)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> rw [g]
    exacts [hp.f0, hp.f1, hp.f2]

theorem loop_body {s s₁ : State} (hp : PreE s) (hE : Entry 4 s s₁) :
    ∀ i < 256, ∀ s', Inv s₁ [.r0, .r1, .r2] fixedR [.r1, .r2] .r3 (val s₁) (fun _ _ => True) i s' →
      WP isa (.block p2rBody) s' (Step s₁ [.r0, .r1, .r2] fixedR [.r1, .r2] .r3 (val s₁) (fun _ _ => True) i s') := by
  intro i hi s' hI
  have hL := layout hp hE
  refine WP.mono (body_ok rfl rfl rfl rfl (hI.inR hL hi (by simp) (by simp))
    (hI.inW hL hi (by simp) (by simp)) (hI.inW hL hi (by simp) (by simp)))
    fun s'' ⟨hm, r0, r1, r2, r3, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r3, hz, hf, rd, wr, sp, trivial⟩
  · rw [hm, hI.read hL hi (by simp) (by simp), hI.addr hL hi (p := .r1) (by simp) (by simp),
      hI.addr hL hi (p := .r2) (by simp) (by simp)]
    rfl
  · intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    exacts [r0, r1, r2]

/-- Coefficients stored apart from a frame are what they were, whatever the frame holds. -/
private theorem natPolyIs_lost {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) {f : Vector Nat n} (h : NatPolyIs m p f) : NatPolyIs m' p f := by
  show natPolyAt m' p = f
  rw [← h]
  exact Vector.ext fun i hi => by
    simp only [VG.Proof.MlDsa.natPolyAt, Vector.getElem_ofFn]; rw [coeffAt_frame hf hd hi]

/-- A polynomial stored apart from a frame is what it was, whatever the frame holds. -/
private theorem polyIs_lost {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) {f : Poly} (h : PolyIs m p f) : PolyIs m' p f := by
  refine ⟨fun i hi => by rw [coeffAt_frame hf hd hi]; exact h.1 i hi, ?_⟩
  rw [← h.2]
  exact Vector.ext fun i hi => by
    simp only [VG.Proof.MlDsa.polyAt, Vector.getElem_ofFn]; rw [coeffAt_frame hf hd hi]

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.power2Round s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ NatPolyIs s'.mem (P s .r1) ((polyAt s.mem (P s .r0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (P s .r2) ((polyAt s.mem (P s .r0)).map fun c => ofInt (power2Round c).2) := by
  refine WP.mono (wp_saving [.r4] _ (W := [pR (P s .r1), pR (P s .r2)])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧
      NatPolyIs s₂.mem (P s .r1) ((polyAt s.mem (P s .r0)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s₂.mem (P s .r2) ((polyAt s.mem (P s .r0)).map fun c => ofInt (power2Round c).2))
    s hp.sp (fun R hR => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      exacts [hp.s1, hp.s2])
    (fun _ _ _ hf ⟨hk, h1, h0⟩ => ⟨hk, natPolyIs_lost hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.s1.symm) h1, polyIs_lost hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.s2.symm) h0⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, h1, h0⟩, hm, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, hm ▸ h1, hm ▸ h0⟩
  have g := hE.gpr
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, g]
  have hL := layout hp hE
  have eT : ∀ k < 256, coeffAt s₁.mem (P s₁ .r0) k = coeffAt s.mem (P s .r0) k := fun k hk => by
    rw [e]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hp.s0.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok hL (by decide) (by decide) (fun _ _ _ => trivial) (loop_body hp hE))
    fun s₂ hI => ⟨?_, fun r hr => (hI.fixed r hr).trans (congrFun g r), ?_, ?_⟩
  · have := hI.frame; simp only [List.map_cons, List.map_nil] at this; rwa [e, e] at this
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [← e, hI.done .r1 (by simp) k hk, val, ite_eq_left rfl, map_get _ _ hk, polyAt_get _ _ hk, eT k hk,
      ← t1_val, word_of_reduced (hp.red k hk)]
  · refine polyIs_of_toNat fun k hk => ?_
    rw [← e, hI.done .r2 (by simp) k hk, val, ite_eq_right (by decide), map_get _ _ hk, polyAt_get _ _ hk,
      eT k hk, ← t0_val, word_of_reduced (hp.red k hk)]

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 1024⟩]

theorem verified :
    Verified Arm.target Impl.MlDsa.Arm.Round.power2Round (Proof.MlDsa.power2RoundContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4] _ [.r0, .r1, .r2] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h1, h0⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]
    exact ⟨h1, h0⟩
  · sig_pub [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.power2RoundContract, Proof.MlDsa.power2RoundSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.P2R

end

end

/-! ### `MlDsa.Arm.Sample.RejBounded`, which only this module used -/

section

/-! ### `MlDsa.Arm.Sample.RejBoundedRun`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ, 544)` (`J6`), the branch on `η`, and the loop for `η`, iteration `t` of
which starts from `Base` with the coefficients `rbFold` samples from the first
`t` bytes of output stored (`loop_ok`); then the end returns whether there are 256.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq H_length)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the argument in `r1`. -/
abbrev etaOf (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The call, from its entry state: `seed = r0`, `eta = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- The XOF output the function uses: 544 bytes of `H(ρ)`. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 544

theorem X_length (σ : State) : (X σ).length = 544 := H_length _ _

/-- The prologue. -/
theorem pro_ok {σ : State} (hp : SpOk (spOf σ) σ) :
    WP isa (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0)) σ (J0 (spOf σ) σ) :=
  pro_rb hp rfl rfl rfl rfl rfl

section
variable {P : Sp} {σ : State}

/-- The loop's setup, from the sponge's output. -/
theorem init_ok {s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 544)]) s
      (Base P σ (H (P.msg σ) 544) 0 []) := by
  have e6 := h.env.r6
  refine WP.mono (Q := fun s' : State => s'.gpr .r0 = P.scr + BitVec.ofNat 32 840 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
      s'.gpr .r3 = BitVec.ofNat 32 544 ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by
    run_block [e6, and_true]
    exact ⟨rfl, trivial, trivial, fun r h0 h2 h3 => by simp [h0, h2, h3]⟩)
    fun s' ⟨h0, h2, h3, hg, hm, hrd, hwr, hsp⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide) (by decide)).trans h.env.r5,
      (hg .r6 (by decide) (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
      by rw [hm, h.out, H_eq], h0, h3, h2, by simp, stored_nil _ _⟩

/-- The loop for `η`. -/
theorem loop_ok (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {s : State} (h : J6 136 544 P σ s) :
    WP isa (rbLoop η) s (Base P σ (H (P.msg σ) 544) 544 (Lf η (H (P.msg σ) 544) 544)) :=
  WP.seq (WP.mono (init_ok h) fun _ h0 =>
    wp_loop_ne (fun t s => Base P σ (H (P.msg σ) 544) t (Lf η (H (P.msg σ) 544) t) s) (N := 544) (by decide)
      (fun _ ht _ hs => body_ok hp hη (H_length _ _) ht hs) (fun _ h => h) h0)

end

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok {σ : State} (hp : SpOk (spOf σ) σ) (hη : etaOf σ = 2 ∨ etaOf σ = 4) {s : State}
    (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) s
      (Base (spOf σ) σ (X σ) 544 (Lf (etaOf σ) (X σ) 544)) := by
  have e7 := h.r7
  refine WP.seq (WP.mono (Q := fun s1 => s1 = subFlags s (σ.gpr .r1) 2) (by
    run_block [e7]) fun s1 e1 => ?_)
  subst e1
  have hj : J6 136 544 (spOf σ) σ (subFlags s (σ.gpr .r1) 2) :=
    ⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩
  have hz : isa.eval .eq (subFlags s (σ.gpr .r1) 2) = some (decide (etaOf σ = 2)) := by
    show some (σ.gpr .r1 - BitVec.ofNat 32 2 == 0) = _
    rw [cmp_z _ _ (by decide)]
  refine WP.ite _ hz (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [he]
    exact loop_ok hp (η := 2) (.inl rfl) hj
  · simp only [decide_eq_false_iff_not] at he
    have e4 : etaOf σ = 4 := hη.resolve_left he
    rw [e4]
    exact loop_ok hp (η := 4) (.inr rfl) hj

/-- The whole function: the calling convention, `r0` whether the loop
sampled 256 coefficients, and those stored. -/
theorem correct {σ : State} (hp : SpOk (spOf σ) σ) (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' => abiPreserved σ s' ∧
      s'.gpr .r0 = (if (Lf (etaOf σ) (X σ) 544).length = 256 then 1 else 0) ∧
      Stored s'.mem (spOf σ).A (Lf (etaOf σ) (X σ) 544) :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (sel_ok hp hη h2) fun _ h3 =>
        WP.mono (retEpi_ok hp h3.env h3.r2 h3.len) fun _ ⟨h0, hm, ha⟩ => ⟨ha, h0, by rw [hm]; exact h3.st⟩)))

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

end

/-! ### `MlDsa.Arm.Sample.RejBoundedCT`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: the loop of `vg_mldsa_rej_bounded_poly`, constant time

Two runs of the loop for `η`, whose XOF outputs `X₁` and `X₂` have their
half-bytes accepted alike (`hbOks`, which the leak of the contract
determines), leak the same: at iteration `t`, both runs have sampled as many
coefficients (`rbFold_length_congr`), so the tests of `j ≥ 256` agree, and the
byte to read has its half-bytes accepted alike, so the tests of the tries
agree; the coefficients themselves are computed and stored by code that the
taint analysis proves leaks nothing of them but `j` and the output pointer
(`try_ct`). What each run is at each point comes from the correctness proof
(`relW`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold hbOks ifT ifF hbTry_length rbFold_length_congr)
open VG.Spec.MlDsa (Zq halfByteOk)

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The first block of a try, as the taint analysis sees it. -/
abbrev tsgn (η : Nat) : List Instr :=
  [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) {η : Nat} (hη : η = 2 ∨ η = 4)
  {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
  (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (tsgn η)) h1).isSome = true)
  (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
  (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true)
  {X₁ X₂ : List Byte}

/-- The eval of `.eq` is the flag `Z`. -/
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

include hp₁ hp₂ hη c1 c2 c3 in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) (hL : L₁.length < 256) {b₁ b₂ : Nat}
    (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 32} :
    RelCT isa (fun a c => (Base P σ₁ X₁ t L₁ a ∧ a.gpr .r9 = BitVec.ofNat 32 b₁ ∧ a.gpr .r8 = v₁) ∧
        (Base P σ₂ X₂ t L₂ c ∧ c.gpr .r9 = BitVec.ofNat 32 b₂ ∧ c.gpr .r8 = v₂)) (rbTry η)
      fun a c => (Base P σ₁ X₁ t (hbTry η L₁ b₁) a ∧ a.gpr .r8 = v₁) ∧
        (Base P σ₂ X₂ t (hbTry η L₂ b₂) c ∧ c.gpr .r8 = v₂) := by
  have hbc := bound_congr hη hok
  refine RelCT.seq (R := fun a c => TS η P σ₁ X₁ t L₁ b₁ v₁ a ∧ TS η P σ₂ X₂ t L₂ b₂ v₂ c)
    (relW (taintRel [] nil_regs c1) fun a c h =>
      ⟨tsgn_ok hη hb₁ h.1.1 h.1.2.1 h.1.2.2, tsgn_ok hη hb₂ h.2.1 h.2.2.1 h.2.2.2⟩) ?_
  refine RelCT.ite (fun a c h => by rw [eval_eq, eval_eq, h.1.z, h.2.z, hbc]) ?_ ?_
  · refine relW (taintRel [] nil_regs c3) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    have r₁ : rbBound η ≤ b₁ := by
      rw [eval_eq, t₁.z] at he; simpa using he
    have r₂ : rbBound η ≤ b₂ := by
      rw [eval_eq, t₁.z, hbc] at he; simpa using he
    rw [hbTry_eq hη, hbTry_eq hη, ifF (by omega_using [r₁]), ifF (by omega_using [r₂])]
    exact ⟨WP.block_nil ⟨t₁.base, t₁.r8⟩, WP.block_nil ⟨t₂.base, t₂.r8⟩⟩
  · refine relW (taintRel [.r2, .r5] (fun a c h r hr => ?_) c2) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.base.r2, h.1.2.base.r2, hl]
      · rw [h.1.1.base.env.r5, h.1.2.base.env.r5]
    have r₁ : b₁ < rbBound η := by
      rw [eval_eq, t₁.z] at he; simpa using he
    have r₂ : b₂ < rbBound η := by
      rw [eval_eq, t₁.z, hbc] at he; simpa using he
    rw [hbTry_eq hη, hbTry_eq hη, ifT r₁, ifT r₂]
    exact ⟨acc_ok hp₁ hη t₁ hL r₁, acc_ok hp₂ hη t₂ (by omega) r₂⟩

include hp₁ hp₂ hη c1 c2 c3 in
/-- The tries of an iteration, in two runs with as many coefficients and a
byte whose half-bytes are accepted alike. -/
theorem mid_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length)
    (hok : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t)) :
    RelCT isa (fun a c => LD P σ₁ X₁ t L₁ a ∧ LD P σ₂ X₂ t L₂ c)
      (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η)))))
      fun a c => Base P σ₁ X₁ t (rbStep η L₁ (zAt X₁ t)) a ∧ Base P σ₂ X₂ t (rbStep η L₂ (zAt X₂ t)) c := by
  simp only [hbOks, Prod.mk.injEq] at hok
  rw [rbStep_eq, rbStep_eq]
  have hz : ∀ a c, (LD P σ₁ X₁ t L₁ a ∧ LD P σ₂ X₂ t L₂ c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
    rw [eval_eq, eval_eq, h.1.z, h.2.z, hl]
  by_cases hf : L₁.length < 256
  · rw [ifT hf, ifT (show L₂.length < 256 by omega)]
    refine RelCT.ite hz (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega_using [hf, he]) ?_
    have hm : (hbTry η L₁ ((zAt X₁ t).toNat % 16)).length = (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length := by
      rw [hbTry_length, hbTry_length, hl, hok.1]
    refine RelCT.seq (R := fun (a c : State) =>
        (Base P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧ a.gpr .r8 = BitVec.setWidth 32 (zAt X₁ t)) ∧
        (Base P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c ∧ c.gpr .r8 = BitVec.setWidth 32 (zAt X₂ t)))
      (RelCT.mono (try_ct hp₁ hp₂ hη c1 c2 c3 hl hf (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hok.1)
        (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩) fun _ _ h => h) ?_
    refine RelCT.seq (R := fun (a c : State) => HI P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧
        HI P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c)
      (relW (taintRel [] nil_regs (by native_taint_decide)) fun a c h => ⟨hi_ok h.1.1 h.1.2, hi_ok h.2.1 h.2.2⟩) ?_
    have hz2 : ∀ a c, (HI P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧
        HI P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
      rw [eval_eq, eval_eq, h.1.z, h.2.z, hm]
    by_cases hm1 : (hbTry η L₁ ((zAt X₁ t).toNat % 16)).length < 256
    · rw [ifT hm1, ifT (show (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega_using [hm1, he]) ?_
      refine RelCT.mono (try_ct hp₁ hp₂ hη c1 c2 c3 hm hm1 (b₁ := (zAt X₁ t).toNat / 16)
        (b₂ := (zAt X₂ t).toNat / 16) (by have := (zAt X₁ t).isLt; omega_using []) (by have := (zAt X₂ t).isLt; omega_using [])
        hok.2) (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩)
        fun _ _ h => ⟨h.1.1, h.2.1⟩
    · rw [ifF hm1, ifF (show ¬ (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega_using [hm1, he])
      exact relW (taintRel [] nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩
  · rw [ifF hf, ifF (show ¬ L₂.length < 256 by omega)]
    refine RelCT.ite hz ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega_using [hf, he])
    exact relW (taintRel [] nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩

variable (hX₁ : X₁.length = 544) (hX₂ : X₂.length = 544)
  (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (Lf η X₁ t).length = (Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < 544) : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega_using [hX₁, ht]),
    List.getElem?_eq_getElem (show t < X₂.length by omega_using [hX₂, ht]), Option.map_some, Option.some.injEq] at h
  rw [zAt, zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega_using [hX₁, ht]), List.getElem?_eq_getElem (show t < X₂.length by omega_using [hX₂, ht])]
  exact h

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- An iteration. -/
theorem body_ct {t : Nat} (ht : t < 544) :
    RelCT isa (fun a c => Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c) (rbBody η)
      fun a c => (Base P σ₁ X₁ (t + 1) (Lf η X₁ (t + 1)) a ∧ a.z = decide (t + 1 = 544)) ∧
        (Base P σ₂ X₂ (t + 1) (Lf η X₂ (t + 1)) c ∧ c.z = decide (t + 1 = 544)) := by
  rw [Lf_succ η hX₁ ht, Lf_succ η hX₂ ht]
  refine RelCT.seq (R := fun a c => LD P σ₁ X₁ t (Lf η X₁ t) a ∧ LD P σ₂ X₂ t (Lf η X₂ t) c)
    (relW (taintRel [.r0] (fun a c h r hr => ?_) (by native_taint_decide)) fun a c h =>
      ⟨load_ok hp₁ ht h.1, load_ok hp₂ ht h.2⟩) ?_
  · rw [List.mem_singleton] at hr; subst hr; rw [h.1.r0, h.2.r0]
  refine RelCT.seq (mid_ct hp₁ hp₂ hη c1 c2 c3 (len_eq oks t) (ok_eq hX₁ hX₂ oks ht)) ?_
  exact relW (taintRel [] nil_regs (by native_taint_decide)) fun a c h => ⟨stepB_ok ht h.1, stepB_ok ht h.2⟩

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- The loop. -/
theorem loop_ct :
    RelCT isa (fun a c => Base P σ₁ X₁ 0 (Lf η X₁ 0) a ∧ Base P σ₂ X₂ 0 (Lf η X₂ 0) c) (.loop (rbBody η) .ne)
      fun a c => Base P σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base P σ₂ X₂ 544 (Lf η X₂ 544) c := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .ne)
    (Q := fun a c => Base P σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base P σ₂ X₂ 544 (Lf η X₂ 544) c)
    (fun n a c => ∃ t, t < 544 ∧ n = 544 - t ∧ Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c)
    (fun n => ?_) 544) (fun a c hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun t => ?_
  by_cases ht : t < 544
  · by_cases hn : n = 544 - t
    · refine RelCT.mono (P := fun a c => Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c)
        (body_ct hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a c ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!c.z); rw [z₁, z₂]
      · have : t + 1 = 544 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 544 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨544 - (t + 1), by omega_using [ht, hn], t + 1, by omega_using [ht, this], rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlDsa.Arm.Sample.RejBounded

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, `η`, the
stack pointer, and which half-bytes of the XOF output are accepted,
`rejBoundedLeak`) leak the same trace: the prologue and the blocks around the
loop by the taint analysis, the sponge by `sponge_ct`, the branch on `η`
because `η` is public, and the loop iteration by iteration (`loop_ct`), since
the half-bytes of the first 544 bytes of output are accepted alike
(`leak_hbOks`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs H_length)
open VG.Spec.MlDsa (H rejBoundedLeak)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open VG.Spec.Sha3 (bytesAt)
open RejBounded

namespace RejBounded

/-- The test of `η = 2`. -/
theorem cmp_ok {P : Sp} {σ s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.cmp .r7 (.imm 2)]) s fun s' => J6 136 544 P σ s' ∧ s'.z = decide (P.prm.toNat = 2) := by
  have e7 := h.r7
  refine WP.mono (Q := fun s1 => s1 = subFlags s P.prm 2) (by run_block [e7]) fun s1 e1 => ?_
  subst e1
  refine ⟨⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩,
    ?_⟩
  show (P.prm - BitVec.ofNat 32 2 == 0) = _
  rw [cmp_z _ _ (by decide)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂)
include hp₁ hp₂

/-- The loop for `η`, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4)
    (oks : (H (P.msg σ₁) 544).map (hbOks η) = (H (P.msg σ₂) 544).map (hbOks η)) {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
    (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (tsgn η)) h1).isSome = true)
    (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
    (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b) (rbLoop η) fun a b =>
      Base P σ₁ (H (P.msg σ₁) 544) 544 (Lf η (H (P.msg σ₁) 544) 544) a ∧
        Base P σ₂ (H (P.msg σ₂) 544) 544 (Lf η (H (P.msg σ₂) 544) 544) b :=
  RelCT.seq (relW (taintRel [.r6] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by native_taint_decide))
      fun a b h => ⟨init_ok h.1, init_ok h.2⟩)
    (loop_ct hp₁ hp₂ hη c1 c2 c3 (H_length _ _) (H_length _ _) oks)

/-- The branch on `η`, and the loops. -/
theorem sel_ct (hη : P.prm.toNat = 2 ∨ P.prm.toNat = 4)
    (oks : (H (P.msg σ₁) 544).map (hbOks P.prm.toNat) = (H (P.msg σ₂) 544).map (hbOks P.prm.toNat)) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b)
      (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) fun a b =>
      Base P σ₁ (H (P.msg σ₁) 544) 544 (Lf P.prm.toNat (H (P.msg σ₁) 544) 544) a ∧
        Base P σ₂ (H (P.msg σ₂) 544) 544 (Lf P.prm.toNat (H (P.msg σ₂) 544) 544) b := by
  refine RelCT.seq (relW (taintRel [] nil_regs (by native_taint_decide)) fun a b h => ⟨cmp_ok h.1, cmp_ok h.2⟩) ?_
  rcases hη with e | e
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [eval_eq, eval_eq, h.1.2, h.2.2]) (RelCT.mono (rbLoop_ct hp₁ hp₂ (η := 2) (.inl rfl) oks (by native_taint_decide) (by native_taint_decide)
      (by native_taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [eval_eq, h.1.2] at he; exact absurd he (by decide))
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [eval_eq, eval_eq, h.1.2, h.2.2]) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [eval_eq, h.1.2] at he; exact absurd he (by decide))
      (RelCT.mono (rbLoop_ct hp₁ hp₂ (η := 4) (.inr rfl) oks (by native_taint_decide) (by native_taint_decide)
        (by native_taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)

end

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract Arm.abi 8).pre s) :
    SpOk (spOf s) s ∧ (etaOf s = 2 ∨ etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f2, f3, he⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0, show (66 : Nat) < 2 ^ 32 by decide, f2, f3, h8⟩, he⟩

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (spOf σ₁) σ₁) (hp₂ : SpOk (spOf σ₂) σ₂) (hη : etaOf σ₁ = 2 ∨ etaOf σ₁ = 4)
  (hsp : σ₁.sp = σ₂.sp) (h0 : σ₁.gpr .r0 = σ₂.gpr .r0) (h1 : σ₁.gpr .r1 = σ₂.gpr .r1)
  (h2 : σ₁.gpr .r2 = σ₂.gpr .r2) (h3 : σ₁.gpr .r3 = σ₂.gpr .r3)
  (hl : rejBoundedLeak (etaOf σ₁) ((spOf σ₁).msg σ₁) = rejBoundedLeak (etaOf σ₂) ((spOf σ₂).msg σ₂))
include hp₁ hp₂ hη hsp h0 h1 h2 h3 hl

/-- The whole function, from two entry states that agree on the public data. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) rejBounded fun _ _ => True := by
  have eP : spOf σ₂ = spOf σ₁ := by simp only [spOf, h0, h1, h2, h3]
  rw [eP] at hp₂ hl
  have e1 : etaOf σ₂ = etaOf σ₁ := by rw [etaOf, etaOf, h1]
  rw [e1] at hl
  have oks := leak_hbOks hl (B := 544) (by decide)
  refine RelCT.seq (relW (taintRel [.r0, .r1, .r2, .r3] (fun a b h r hr => ?_) (by native_taint_decide)) fun a b h =>
    ⟨by rw [h.1]; exact pro_ok hp₁, by rw [h.2]; exact pro_rb hp₂ h0.symm h1.symm h2.symm h3.symm rfl⟩) ?_
  · rw [h.1, h.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine RelCT.seq (sponge_ct hp₁ hp₂ hsp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide)
    (by decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine RelCT.seq (sel_ct hp₁ hp₂ hη oks) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by native_taint_decide)

end

end RejBounded

end VG.Proof.MlDsa.Arm.Sample

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Proof.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 2 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejBounded (rejBoundedContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨rbSat, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := pre_of hs
    obtain ⟨t, s', he, ha, h0, hst⟩ := correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have hL : Lf (etaOf s) (X s) 544 = rbFold (etaOf s) [] (X s) := by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    rw [hL] at h0 hst
    sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rbFold (etaOf s) [] (X s)).length = 256
    · rw [ifT hf]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
        exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
        exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := pre_of h₁
    obtain ⟨hp₂, -⟩ := pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3⟩ := hpub
    exact (all_ct hp₁ hp₂ hη hsp h0 h1 h2 h3 hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.Arm.Sample

end

end

/-! ### `MlDsa.Arm.KeyGen.Top`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on 32-bit ARM: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The rows (`row_piece`), the keys in memory (`pk_bytes`, `sk_bytes`), `tr =
H(pk, 64)` (`trHash_piece`), and the whole function, piece by piece, for any
parameter set of Table 1 and any verified implementations of the primitives
(`keyGen_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Impl.MlKem.Arm (topEnd)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK Good)
open VG.Spec.Sha3 (bytesAt)

/-! ## A row -/

theorem row_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat}
    (hS : S + 8 ≤ STK) {i : Nat} (hi : i < p.k) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1)) (row P p i) := by
  have hl := hF.l
  unfold row
  refine (rowMul_piece hP hF hS hi).seq (Piece.seq ?_ ((rowInv_piece hP hF hS hi).seq ((rowAdd_piece hP hF hS hi).seq
    ((rowP2r_piece hP hF hS hi).seq ((rowSbp_piece hP hF hS hi).seq (rowBp_piece hP hF hS hi))))))
  refine Piece.mono (Piece.seqR (I := fun j => RowI p STK i (tIs p STK fun A S => dotK p A S i j)) (p.ℓ - 1) 1
    fun j h1 h2 => rowMulAdd_piece hP hF hS hi (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_arith] at h

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {np nj : Nat} {s : State} (h : KR p STK σ A S R np nj p.k s) :
    bytesAt s.mem ((lay p STK σ).A 3 0) p.pkLen = pkK p A S (rhoOf p σ) := by
  rw [hF.pk, Proof.MlKem.bytesAt_add, h.pk0, Lay.A, add_ofNat_add, Nat.zero_add,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {nj : Nat} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem ((lay p STK σ).A 4 0) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 := h.sk0
  have h1 := h.sk1
  simp only [Lay.A, add_ofNat_zero] at h0 h1 htr ⊢
  have h2 : bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) + BitVec.ofNat 64 (32 + 32)) 64 =
    Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 := htr
  have hp : ∀ r ∈ List.range (p.ℓ + p.k), bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (32 + 32 + 64 + lenS p * r)) (lenS p) = bitPack (S r) p.η p.η := fun r hr =>
    h.packs r (List.mem_range.mp hr)
  have hr : ∀ i ∈ List.range p.k, bytesAt s.mem (State.addr ((lay p STK σ).ptr 4) +
      BitVec.ofNat 64 (oT0 p + 416 * i)) 416 = bitPack (t0K p A S i) 4095 4096 := fun i hi =>
    (h.rows i (List.mem_range.mp hi)).2
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ (oT0 p) 416 p.k, skK, flatMap_congr_mem hp,
    flatMap_congr_mem hr]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem ((lay p STK σ).A 4 64) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trPieces {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (hs : Site (lay p STK σ) kWb STK s) :
    (∀ pc ∈ ([⟨.r5, 0, p.pkLen⟩] : List Impl.MlKem.Arm.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc) ∧
    PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r6, 64, 64⟩ : Impl.MlKem.Arm.Piece) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hpk := hF.lens
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (by decide) (by decide) (by decide) (by decide)
    (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hashLay, Lay.size, hF.sk, hlen, ite_true]) (.inr rfl)
    fun _ => by decide⟩
  rw [List.mem_singleton] at hpc; subst hpc
  exact pieceS hs rfl (show encodable (BitVec.ofNat 32 0) = true by decide) hF.encPk
    (show 0 < p.pkLen by rw [hF.pk]; omega_arith) (show 0 + p.pkLen < 2 ^ 32 by omega_arith)
    (by lsep hF [hashLay, Lay.size, hF.pk, ite_true]) (.inr rfl) fun h => absurd h (by decide)

theorem trHash_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly}
    {R : BitVec 32} {s : State} (h : KR p STK σ A S R (p.ℓ + p.k) p.ℓ p.k s) :
    WP isa (trHash p) s (KFin p STK σ) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  obtain ⟨hin, hq⟩ := trPieces hF hs
  unfold trHash
  refine WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by decide)
    (by simp) hin hq) fun s' ⟨k', o'⟩ => ⟨A, S, R, h.keep hF k' ?_, ?_⟩
  · have := hF.scr
    exact (KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide)) (by omega_arith)).append
      (W₁ := [_]) ((KRChk.c0 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
      (by omega_arith)).append (W₁ := [_]) ((KRChk.stk hF (Nat.le_refl _) (Nat.le_refl _)).append (W₁ := [_])
      (KRChk.c4 (o := 64) (n := 64) hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega_arith)) (by rw [hF.sk, oT0]; omega_arith))))
  have o₃ : bytesAt s'.mem ((lay p STK σ).A 4 64) 64 = _ := o'
  rw [o₃]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
    hashLay_ptr _ _ _ (ix_ne1 _)]
  have e : bytesAt s.mem (State.addr ((lay p STK σ).ptr (ix Reg.r5)) + 0#64) p.pkLen = pkK p A S (rhoOf p σ) :=
    pk_bytes hF h
  rw [e, shake31]
  exact (Proof.MlKem.shake256_eq _ _).symm

theorem trHash_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ p.k) (KFin p STK) (trHash p) :=
  ⟨fun _ _ _ ⟨_, _, _, h⟩ => trHash_ok hF h,
    rel_of (ktwo fun σ => hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by decide) (by simp)
      (fun s hs => (trPieces hF hs).1) (fun s hs => (trPieces hF hs).2) fun _ _ h => h)
      fun _ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The return -/

theorem epi_ok {p : Params} (hF : PFacts p) {STK : Nat} {σ s : State} (h : KFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      Arm.target.abiPreserved σ s' ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s' := by
  obtain ⟨A, S, R, h, htr⟩ := h
  have hs := h.kc.site
  have e0 : ∀ o, (hashLay (lay p STK σ) s fun _ => true).A 0 o = (lay p STK σ).A 0 o := fun o => by
    simp only [Lay.A, hashLay_ptr _ _ _ (show (0 : Nat) ≠ 1 by decide)]
  refine WP.mono (topEnd_ok (hs.ctx ktrue) (by rw [e0]; exact h.kc.sav) (by rw [e0]; exact h.kc.lr))
    fun s' ⟨pr, r0, m', sp'⟩ => ⟨⟨pr, sp'.trans h.kc.sp⟩, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  have e3 : BitVec.setWidth 64 (σ.gpr .r1) = (lay p STK σ).A 3 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  have e4 : BitVec.setWidth 64 (σ.gpr .r2) = (lay p STK σ).A 4 0 := by
    simp only [Lay.A, add_ofNat_zero]; rfl
  rw [setWidth_append32, r0, h.r11, m', e3, e4, pk_bytes hF h, sk_bytes hF h htr]
  exact Proof.MlDsa.KeyGen.outcome_keyGen (by have := hF.l; omega_arith) h.good

theorem ktaint7 {p : Params} {STK : Nat} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r7]) c hc).isSome = true) : RelCT isa (KTwo p STK) c fun _ _ => True :=
  ktwo fun _ => taint7 (fun _ _ h => h) h

theorem epi_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (KFin p STK)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => epi_ok hF h, rel_of (ktaint7 (by native_taint_decide))
    fun _ _ _ _ _ _ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two pub h₁.kc h₂.kc⟩

/-! ## The function -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

theorem rest_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s) (KFin p STK) (rest P p) := by
  unfold rest
  refine (copies_piece hF).seq (Piece.seq (J := KRx p STK (p.ℓ + p.k) 0 0) ?_
    (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ 0) ?_ (Piece.seq (J := KRx p STK (p.ℓ + p.k) p.ℓ p.k) ?_
      (trHash_piece hF))))
  · refine Piece.mono (Piece.seqR (I := fun r => KRx p STK r 0 0) (p.ℓ + p.k) 0
      fun r _ hr => packS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun j => KRx p STK (p.ℓ + p.k) j 0) p.ℓ 0
      fun j _ hj => nttS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun i => KRx p STK (p.ℓ + p.k) p.ℓ i) p.k 0
      fun i _ hi => row_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem keyGen_piece :
    KPiece p STK (fun σ s => s = σ)
      (fun σ s => Arm.target.abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p Arm.abi STK).post σ s)
      (keyGen P p) :=
  (pro_piece hF (by omega_arith)).seq ((seeds_piece hF).seq ((sampA_piece hP hF hS).seq ((sampS_piece hP hF hS).seq
    ((rest_piece hP hF hS).seq (epi_piece hF)))))

end

/-- A state satisfying `keyGenContract`'s precondition. -/
def keyGenSat (p : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x4000 | .r3 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, p.pkLen⟩, ⟨0x4000, p.skLen⟩, ⟨0x10000, scrLen p⟩]

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen (Prims keyGen)

/-- `vg_mldsa*_keygen` of the parameter set `p` meets its contract with
40 bytes of stack (a frame size of the model, which a function that returns
without secret residue wipes: `Arm.Scrub.scrubRegF`), for any verified
implementations `P` of the primitives it calls with at most 28 bytes of
stack. -/
theorem keyGen_verified {P : Prims} (hP : PrimsOk P 28) (p : Spec.MlDsa.Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    Verified Arm.target (keyGen P p) (Spec.MlDsa.keyGenContract p Arm.abi 40) := by
  have hF := pfacts hp
  have hk := keyGen_piece hP hF (STK := 40) (by decide)
  refine ⟨fun s hs => hk.ok s s (pre_of (n := 39) hs) rfl, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3⟩ := hpub
    exact relStart hk.tr s₁ s₂ t₁ t₂ s₁' s₂' (pre_of (n := 39) h₁) (pre_of (n := 39) h₂)
      ⟨hsp, h0, h1, h2, h3, hl⟩ e₁ e₂
  · refine ⟨keyGenSat p, ?_⟩
    rcases hp with rfl | rfl | rfl <;>
    sig_sat_check [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, keyGenSat]

end VG.Proof.MlDsa.Arm.KeyGen

end

end

/-!
# ML-DSA key generation on 32-bit ARM, with this library's primitives

The ARM implementations of the primitives (`prims`) are verified with at most
28 bytes of stack, and their frames use no more (`prims_ok`), so key
generation with them is verified with 40 (`keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm
open VG.Impl.MlDsa.Arm.KeyGen

theorem prims_ok : PrimsOk prims 28 where
  ntt := ⟨⟨28, by decide, Arith.Ntt.verified⟩, by decide +kernel⟩
  invNtt := ⟨⟨28, by decide, Arith.NttInv.verified⟩, by decide +kernel⟩
  mul := ⟨⟨24, by decide, Arith.Mul.mul_verified⟩, by decide +kernel⟩
  mulAdd := ⟨⟨24, by decide, Arith.Mul.mulAdd_verified⟩, by decide +kernel⟩
  add := ⟨⟨0, by decide, Arith.AddSub.add_verified⟩, by decide +kernel⟩
  rejNtt := ⟨⟨8, by decide, Sample.rejNTT_verified⟩, by decide +kernel⟩
  rejBounded := ⟨⟨8, by decide, Sample.rejBounded_verified⟩, by decide +kernel⟩
  power2Round := ⟨⟨4, by decide, Round.P2R.verified⟩, by decide +kernel⟩
  simpleBitPack := ⟨⟨0, by decide, Pack.simpleBitPack_verified⟩, by decide +kernel⟩
  bitPack := ⟨⟨4, by decide, Pack.bitPack_verified⟩, by decide +kernel⟩

end VG.Proof.MlDsa.Arm.KeyGen
