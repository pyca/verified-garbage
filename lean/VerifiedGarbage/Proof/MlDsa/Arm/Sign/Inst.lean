module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball
import VerifiedGarbage.Proof.MlDsa.Sign.Leak
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlKem.Arm.Prf
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlKem.Encode
public import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.MlKem.Arm.SampleCT
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.Sha3.Arith
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.Ball
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Call
public import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.Sample.Mem
public import VerifiedGarbage.Proof.MlDsa.Sign.Iter
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Saving
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
meta import VerifiedGarbage.Proof.MlKem.Arm.Common
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase
public import VerifiedGarbage.Proof.MlDsa.Pack.Mem
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.MlKem.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintBase
meta import VerifiedGarbage.Proof.MlDsa.Pack.Mem
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlKem.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint
public import VerifiedGarbage.Proof.MlDsa.Pack.Hint
import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Impl.MlDsa.Arm.Pack.Hint
meta import VerifiedGarbage.Proof.MlDsa.Pack.Hint
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
public import VerifiedGarbage.Impl.MlDsa.Arm.Sample.ExpandMask
public import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
meta import VerifiedGarbage.Impl.MlDsa.Arm.Sample.ExpandMask
meta import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Sponge
meta import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack

/-! ### `MlDsa.Arm.Sample.ExpandMask`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_expand_mask_poly`

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ′, 640)` (`J6`), the branch on `γ₁`, and the loop of `vg_mldsa_bit_unpack`
for `c = 1 + bitlen (γ₁ - 1)` on the first `32c` bytes of output
(`Pack.unpackLoop_buFin_ok`, run from the state permitted only those bytes and
`a`, and widened to the function's permissions by `Exec.widen`), which are
`H(ρ′, 32c)` (`H_take`). It is constant time: the taint analysis proves each
piece but the sponge, whose proof is `sponge_ct`, from the pointers and `γ₁`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sample.ExpandMask

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.Arm.Pack (unpackLoop buFin)
open VG.Spec.MlDsa (Zq q H toRq bitUnpack bitlen)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- The call, from the entry state: `seed = r0`, `gamma1 = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- `γ₁`. -/
abbrev gam (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) 66

/-- What the proofs need of the entry state. -/
structure Pre (σ : State) : Prop where
  ok : SpOk (spOf σ) σ
  g : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19

/-- What the function writes. -/
abbrev Out (σ : State) : Spec.MlDsa.Poly :=
  toRq (bitUnpack (H (B σ) (32 * (1 + bitlen (gam σ - 1)))) (gam σ - 1) (gam σ))

/-- After the loop. -/
structure EDone (σ : State) (s : State) : Prop where
  env : Env (spOf σ) σ s
  out : PolyIs s.mem (spOf σ).A (Out σ)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop of `BitUnpack` for `(B, d, c, nb)`, from the output of the
sponge. -/
theorem loop_ok {Bv d c nb : Nat} (hs : Pack.Shape d c nb) (hB : encodable (BitVec.ofNat 32 Bv) = true)
    (hB19 : Bv ≤ 2 ^ 19) (hd : bitlen (Bv - 1 + Bv) = d) (h32 : 32 * d ≤ 640) {s : State}
    (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.dp .add .r0 .r6 (.imm 840), .mov .r1 (.reg .r5)]) (unpackLoop (buFin Bv) d c nb)) s
      fun s' => Env (spOf σ) σ s' ∧ PolyIs s'.mem (spOf σ).A (toRq (bitUnpack (H (B σ) (32 * d)) (Bv - 1) Bv)) := by
  have fs := hp.fscr
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.gpr .r0 = s.gpr .r6 + BitVec.ofNat 32 840 ∧ s1.gpr .r1 = s.gpr .r5 ∧
      s1.gpr .r5 = s.gpr .r5 ∧ s1.gpr .r6 = s.gpr .r6 ∧ s1.mem = s.mem ∧ s1.rd = s.rd ∧ s1.wr = s.wr ∧
      s1.sp = s.sp) (by run_block [and_self, and_true, true_and]; rfl) fun s1 ⟨g0, g1, g5, g6, m, rd, wr, sp⟩ => ?_)
  have e1 := h.env.same m g5 g6 rd wr sp
  have a0 : State.addr (s1.gpr .r0) = (spOf σ).at' 840 := by rw [g0, h.env.r6]; exact at_eq hp (by omega_arith)
  have a1 : State.addr (s1.gpr .r1) = (spOf σ).A := by rw [g1, h.env.r5]
  let src : Region := ⟨State.addr (s1.gpr .r0), 32 * d⟩
  let t := s1.withRegions [src] [polyR (State.addr (s1.gpr .r1))]
  have hsep : src.Disjoint (polyR (State.addr (s1.gpr .r1))) := by
    show Region.Disjoint ⟨State.addr (s1.gpr .r0), 32 * d⟩ (polyR (State.addr (s1.gpr .r1)))
    rw [a0, a1]; exact (hp.a_scr.sub_right (sub_scr (a := 840) (n := 32 * d) (by omega_arith))).symm
  have fit0 : (s1.gpr .r0).toNat + 32 * d ≤ 2 ^ 32 := by
    rw [g0, h.env.r6, BitVec.toNat_add, toNat_ofNat32 (by omega_arith)]; omega_arith
  have fit1 : (s1.gpr .r1).toNat + 1024 ≤ 2 ^ 32 := by rw [g1, h.env.r5]; exact hp.fa
  obtain ⟨tr, t', he, hpoly, hf, hk⟩ := Pack.unpackLoop_buFin_ok (s := t) (a := Bv - 1) hs hB hB19 hd
    (List.mem_append_left _ (List.mem_singleton_self _)) (List.mem_singleton_self _) hsep fit0 fit1
  have hc : Covers (t.rd ++ t.wr) (s1.rd ++ s1.wr) := by
    refine Covers.of_sub fun r hr => ?_
    simp only [t, State.withRegions_rd, State.withRegions_wr, List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨(spOf σ).scrR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 840, a0, by show 840 + 32 * d ≤ 2048; omega_arith⟩
    · exact ⟨(spOf σ).aR, List.mem_append_right _ (by rw [e1.wr, hp.wr]; simp), 0,
        by rw [a1]; exact (add_ofNat_zero _).symm, by simp⟩
  have hw : Covers t.wr s1.wr := by
    intro x k ⟨r, hr, hcr⟩
    simp only [t, State.withRegions_wr, List.mem_singleton] at hr
    subst hr
    rw [a1] at hcr
    exact ⟨(spOf σ).aR, by rw [e1.wr, hp.wr]; simp, hcr⟩
  have he' := Exec.widen he hc hw
  simp only [t, State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨tr, _, he', ?_, ?_⟩
  · have hf' : Frame [(spOf σ).aR] s1.mem t'.mem := by
      have := hf
      simp only [t, State.withRegions_gpr, State.withRegions_mem] at this
      rw [a1] at this; exact this
    exact e1.step hp hf' (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact .inr (.inl fun _ h => h))
      (hk.gpr (by decide)) (hk.gpr (by decide)) rfl rfl (hk.2.2.2)
  · show PolyIs t'.mem _ _
    rw [← a1]
    have eb : bytesAt t.mem (State.addr (t.gpr .r0)) (32 * d) = H (B σ) (32 * d) := by
      show bytesAt s1.mem (State.addr (s1.gpr .r0)) (32 * d) = _
      rw [a0, m, ← MlKem.bytesAt_take _ _ (show 32 * d ≤ 640 by omega_arith), h.out, ← H_eq, H_take _ (by omega_arith)]
    rw [eb] at hpoly
    exact hpoly

/-- The branch on `γ₁` and the loop. -/
theorem tail_ok (hg : gam σ = 2 ^ 17 ∨ gam σ = 2 ^ 19) {s : State} (h : J6 136 640 (spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 0x20000)]) (.ite .eq (emLoop 18) (emLoop 20))) s (EDone σ) := by
  refine WP.seq (WP.mono (Q := fun s1 : State => s1.z = decide (gam σ = 2 ^ 17) ∧ s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.sp = s.sp) ?_ fun s1 ⟨z1, g, m, rd, wr, sp⟩ => ?_)
  · have e : (s.gpr .r7 - 0x20000 == 0) = decide (gam σ = 2 ^ 17) := by
      rw [h.r7]
      show (σ.gpr .r1 - BitVec.ofNat 32 131072 == 0) = _
      rw [cmp_z _ 131072 (by decide)]
    run_block [e, and_self, and_true, true_and]
  have h1 : J6 136 640 (spOf σ) σ s1 :=
    ⟨h.env.same m (by rw [g]) (by rw [g]) rd wr sp, by rw [g]; exact h.r7, by rw [m]; exact h.out⟩
  refine WP.ite s1.z rfl (fun e => ?_) (fun e => ?_)
  · have hγ : gam σ = 2 ^ 17 := by rw [z1] at e; simpa using e
    refine WP.mono (loop_ok hp (Bv := 131072) (c := 4) (nb := 9) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo
  · have hγ : gam σ = 2 ^ 19 := by rw [z1] at e; simp at e; omega_arith
    refine WP.mono (loop_ok hp (Bv := 524288) (c := 2) (nb := 5) (by constructor <;> decide) (by decide) (by decide)
      (by decide) (by decide) h1) fun s' ⟨he, hpo⟩ => ⟨he, ?_⟩
    rw [Out, hγ]; exact hpo

end

/-- The function, from an entry state whose regions are those of a call. -/
theorem correct {σ : State} (hp : Pre σ) : WP isa Impl.MlDsa.Arm.Sample.expandMask σ fun s' =>
    PolyIs s'.mem (State.addr (σ.gpr .r2)) (Out σ) ∧ abiPreserved σ s' :=
  WP.seq (WP.mono (pro_rb hp.ok rfl rfl rfl rfl rfl) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp.ok (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (tail_ok hp.ok hp.g h2) fun _ h3 =>
        WP.mono (epi_ok' hp.ok h3.env) fun _ ⟨hm, ha⟩ => ⟨by rw [hm]; exact h3.out, ha⟩)))

/-! ## Constant time -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3

theorem all_ct {σ₁ σ₂ : State} (two : Two σ₁ σ₂) :
    RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.expandMask fun _ _ => True := by
  have hP : spOf σ₁ = spOf σ₂ := by simp only [spOf, two.r0, two.r1, two.r2, two.r3]
  have ok₂ : SpOk (spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relW (taintRel [.r0, .r1, .r2, .r3]
      (fun a b h r hr => by
        rw [h.1, h.2]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [two.r0, two.r1, two.r2, two.r3]) (by native_taint_decide))
    fun a b h => ⟨by rw [h.1]; exact pro_rb two.p₁.ok rfl rfl rfl rfl rfl,
      by rw [h.2]; exact pro_rb ok₂ two.r0.symm two.r1.symm two.r2.symm two.r3.symm rfl⟩) ?_
  refine RelCT.seq (R := fun a b => J6 136 640 (spOf σ₁) σ₁ a ∧ J6 136 640 (spOf σ₂) σ₂ b)
    ((sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 640) (by decide) (by decide) (by decide) (by decide)
      (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)).mono (fun _ _ h => h)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => EDone σ₁ a ∧ EDone σ₂ b) (relW (taintRel [.r5, .r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.env.r5, h.2.env.r5, hP]
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, hP]) (by native_taint_decide))
    fun a b h => ⟨tail_ok two.p₁.ok two.p₁.g h.1, tail_ok two.p₂.ok two.p₂.g h.2⟩) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by native_taint_decide)

/-! ## Verified -/

theorem pre_of {s : State} (h : (Proof.MlDsa.expandMaskContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f1, f2, f3, hg⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f1, by show (66 : Nat) < 2 ^ 32; decide, f2, f3, h8⟩, hg⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x20000 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.ExpandMask

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open ExpandMask

theorem expandMask_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.expandMask (Proof.MlDsa.expandMaskContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, hpoly, hpres⟩ := correct (pre_of hs)
    refine ⟨t, s', he, hpres, ?_⟩
    sig_post [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact hpoly
  · sig_pub [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, h0, h1, h2, h3⟩ := hpub
    exact (all_ct ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Proof.MlDsa.expandMaskContract, Proof.MlDsa.expandMaskSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample

end

end

/-! ### `MlDsa.Arm.Pack.HintPackCT`, which only this module used -/

section

/-! ### `MlDsa.Arm.Pack.HintPack`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, correct

As on x86-64, the code follows the fold form of `HintBitPack`
(`Proof/MlDsa/Pack/Hint.lean`) step by step: the bytes of `y` are the array of
the spec, and `r1` its index, which stays below `ω` because it counts the 1s
before the current coefficient (`hpIdx_lt`). The loops (`main_ok`) run from
any state that permits reading the hint and writing `y`, so that constant time
can narrow the state to those two regions (`HintPackCT.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-! ## The arguments -/

section
variable (s₀ : State)

/-- `h`, `ω`, `y` and `len`. -/
abbrev pH : BitVec 32 := s₀.gpr .r0
abbrev pW : BitVec 32 := s₀.gpr .r2
abbrev pY : BitVec 32 := s₀.gpr .r3
abbrev pL : BitVec 32 := stackArg s₀ 0
abbrev pω : Nat := (pW s₀).toNat
abbrev pLen : Nat := (pL s₀).toNat
abbrev pk : Nat := pLen s₀ - pω s₀
abbrev hR : Region := ⟨State.addr (pH s₀), (s₀.gpr .r1).toNat * 4⟩
abbrev yR : Region := ⟨State.addr (pY s₀), pLen s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The hint. -/
abbrev pHint : List (Vector Bool n) := hintAt s₀.mem (State.addr (pH s₀)) (pk s₀)

end

/-- The precondition, as `sig_pre` states it. -/
structure PPre (s : State) : Prop where
  sp : 8 ≤ s.sp.toNat
  spA : s.sp.toNat + 4 ≤ 2 ^ 32
  rd : s.rd = [hR s, argR s]
  wr : s.wr = [yR s]
  d_hy : (hR s).Disjoint (yR s)
  d_ya : (yR s).Disjoint (argR s)
  b_h : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (hR s)
  b_y : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (yR s)
  b_a : (⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ : Region).Disjoint (argR s)
  fitH : (pH s).toNat + (s.gpr .r1).toNat * 4 ≤ 2 ^ 32
  fitY : (pY s).toNat + pLen s ≤ 2 ^ 32
  par : (pω s, pk s) ∈ hintParams
  ωle : pω s ≤ pLen s
  hlen : (s.gpr .r1).toNat = 256 * pk s
  ones : hintOnes (pHint s) ≤ pω s

section
variable {s₀ : State} (hp : PPre s₀)
include hp

theorem pfacts : 4 ≤ pk s₀ ∧ pk s₀ ≤ 8 ∧ 55 ≤ pω s₀ ∧ pω s₀ ≤ 80 ∧ pω s₀ + pk s₀ = pLen s₀ ∧ pLen s₀ ≤ 88 := by
  have := mem_hintParams hp.par
  have := hp.ωle
  have e : pk s₀ = pLen s₀ - pω s₀ := rfl
  omega_arith

/-! ## Zeroing `y` -/

omit hp in
theorem zeroPro_ok {s : State} :
    WP isa (.block [.dp .sub .r1 .r12 (.reg .r2), .mov .r4 (.reg .r12), .mov .r12 (.imm 0), .mov .r5 (.reg .r3)])
      s fun s' => s'.gpr .r1 = s.gpr .r12 - s.gpr .r2 ∧ s'.gpr .r4 = s.gpr .r12 ∧ s'.gpr .r12 = 0 ∧
        s'.gpr .r5 = s.gpr .r3 ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

omit hp in
theorem zeroStep_ok {s : State} {y c : BitVec 32} (h5 : s.gpr .r5 = y) (h4 : s.gpr .r4 = c)
    (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r12 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) ((s.gpr .r12).setWidth 8) ∧
      s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r1 ∧ s'.gpr .r2 = s.gpr .r2 ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block [h5, h4, o]

/-- Zeroing the `len` bytes of `y`, from the entry values of the registers. -/
theorem zero_ok {s : State} (h0 : s.gpr .r0 = pH s₀) (h2 : s.gpr .r2 = pW s₀) (h3 : s.gpr .r3 = pY s₀)
    (h12 : s.gpr .r12 = pL s₀) (hwr : yR s₀ ∈ s.wr) :
    WP isa hbpZero s fun s' => s'.gpr .r0 = pH s₀ ∧ s'.gpr .r1 = BitVec.ofNat 32 (pk s₀) ∧
      s'.gpr .r2 = pW s₀ ∧ s'.gpr .r3 = pY s₀ ∧
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = List.replicate (pLen s₀) 0 ∧
      Frame [yR s₀] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  obtain hL := (pL s₀).isLt
  unfold hbpZero
  refine WP.seq (WP.mono zeroPro_ok fun s₁ ⟨r1₁, r4₁, r12₁, r5₁, r0₁, r2₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (N := pLen s₀) (fun t s' => s'.gpr .r5 = pY s₀ + BitVec.ofNat 32 t ∧
      s'.gpr .r4 = BitVec.ofNat 32 (1 * (pLen s₀ - t)) ∧ s'.gpr .r12 = 0 ∧ s'.gpr .r0 = pH s₀ ∧
      s'.gpr .r1 = BitVec.ofNat 32 (pk s₀) ∧ s'.gpr .r2 = pW s₀ ∧ s'.gpr .r3 = pY s₀ ∧
      Frame [yR s₀] s.mem s'.mem ∧ (∀ u < t, s'.mem (State.addr (pY s₀) + BitVec.ofNat 64 u) = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by omega_arith)
    (fun t ht s' ⟨i5, i4, i12, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ?_)
    (fun s' ⟨_, _, _, i0, i1, i2, i3, hf, hz, hrd, hwr', hsp⟩ => ⟨i0, i1, i2, i3,
      VG.Proof.MlKem.bytesAt_eq (by simp) fun u hu => by rw [hz u hu]; simp, hf, hrd, hwr', hsp⟩)
    ⟨by rw [r5₁, h3]; simp, by rw [r4₁, h12, Nat.one_mul, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      r12₁, by rw [r0₁, h0], ?_, by rw [r2₁, h2], by rw [r3₁, h3], by rw [m₁]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), rd₁, wr₁, sp₁⟩
  · have ea : State.addr (pY s₀ + BitVec.ofNat 32 t + BitVec.ofNat 32 0) = State.addr (pY s₀) + BitVec.ofNat 64 t :=
      addr_ptr _ _ _ (by omega_arith)
    refine WP.mono (zeroStep_ok i5 i4 (by
        rw [ea, hwr']; exact ⟨_, hwr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
      fun s'' ⟨r5', r4', z', m', r0', r1', r2', r3', r12', rd', wr', sp'⟩ =>
        ⟨⟨by rw [r5', BitVec.add_assoc, ofNat_succ32], by rw [r4']; exact count_sub (k := 1) ht, by rw [r12', i12],
          by rw [r0', i0], by rw [r1', i1], by rw [r2', i2], by rw [r3', i3], ?_, fun u hu => ?_,
          by rw [rd', hrd], by rw [wr', hwr'], by rw [sp', hsp]⟩, by rw [z']; exact count_z (k := 1) ht (by decide) (by omega_arith)⟩
    · rw [m', ea]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [m', ea, VG.Proof.MlKem.Arm.byte_writeW8 _ _ (by omega_arith) (by omega_arith)]
      split
      · rw [i12]; rfl
      · exact hz u (by omega_arith)
  · rw [r1₁, h12, h2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by have := hp.ωle; exact this), toNat_ofNat32 (by omega_arith)]

end

/-! ## The spec, step by step -/

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (pω s₀) (pHint s₀)) (Array.replicate (pω s₀ + pk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((pHint s₀).getD i noHint)) (hpS s₀ i)

theorem hpT_zero (s₀ : State) (i : Nat) : hpT s₀ i 0 = hpS s₀ i := by
  simp only [hpT, List.range_zero, List.foldl_nil]


theorem hpS_idx (s₀ : State) (i : Nat) : (hpS s₀ i).2 = onesBefore (pHint s₀) i 0 := by
  rw [hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (hpT s₀ i j).2 = onesBefore (pHint s₀) i j := by
  rw [hpT, hpSteps_idx, hpS_idx]; unfold onesBefore; rfl

theorem hpT_succ (s₀ : State) (i j : Nat) :
    hpT s₀ i (j + 1) = hpStep ((pHint s₀).getD i noHint) (hpT s₀ i j) j := by
  rw [hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    hpS s₀ (i + 1) = ((hpT s₀ i n).1.set! (pω s₀ + i) (BitVec.ofNat 8 (hpT s₀ i n).2), (hpT s₀ i n).2) := by
  rw [hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

/-! ## The polynomials -/

/-- Before coefficient `j` of polynomial `i`, in the loops that start from `sA`. -/
structure CInv (s₀ sA : State) (i j : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (hpT s₀ i j).2
  r3 : s.gpr .r3 = pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (pk s₀ - i))
  r5 : s.gpr .r5 = pY s₀ + BitVec.ofNat 32 (pω s₀ + i)
  r12 : s.gpr .r12 = BitVec.ofNat 32 j
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (pY s₀)) (pLen s₀) = (hpT s₀ i j).1.toList

/-- What the loops need of the state they start from: permission to read the
hint and write `y`, and the hint of the entry state. -/
structure MainPre (s₀ sA : State) : Prop where
  rd : hR s₀ ∈ sA.rd
  wr : yR s₀ ∈ sA.wr
  hint : ∀ t < 256 * pk s₀, coeffAt sA.mem (State.addr (pH s₀)) t = coeffAt s₀.mem (State.addr (pH s₀)) t

theorem coefLoad_ok {s : State} {x : BitVec 32} (h0 : s.gpr .r0 = x)
    (ia : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block [.ldr .r2 .r0 0, .cmp .r2 (.imm 0)]) s fun s' =>
      s'.z = (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 - 0 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h0, ia]
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem coefSet_ok {s : State} {y i j : BitVec 32} (h1 : s.gpr .r1 = i) (h3 : s.gpr .r3 = y)
    (h12 : s.gpr .r12 = j) (o : InRegions s.wr (State.addr (y + i + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.dp .add .r2 .r3 (.reg .r1), .strb .r12 .r2 0, .dp .add .r1 .r1 (.imm 1)]) s fun s' =>
      s'.gpr .r1 = i + 1 ∧ s'.mem = s.mem.writeW (State.addr (y + i + BitVec.ofNat 32 0)) (j.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r := by
  run_block [h1, h3, h12, o]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h1, ite_neg' h2]

theorem coefNext_ok {s : State} {x j : BitVec 32} (h0 : s.gpr .r0 = x) (h12 : s.gpr .r12 = j) :
    WP isa (.block [.dp .add .r0 .r0 (.imm 4), .dp .add .r12 .r12 (.imm 1), .cmp .r12 (.imm 256)]) s fun s' =>
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r12 = j + 1 ∧ s'.z = (j + 1 - 256 == 0) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block [h0, h12]
  simp only [true_and]; intro r h1 h2; rw [ite_neg' h2, ite_neg' h1]

section
variable {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- A coefficient. -/
theorem coef_ok {i j : Nat} (hi : i < pk s₀) (hj : j < 256) {s : State} (hI : CInv s₀ sA i j s) :
    WP isa hbpCoef s fun s' => CInv s₀ sA i (j + 1) s' ∧ s'.z = decide (j + 1 = 256) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  have fH := hp.fitH
  have fY := hp.fitY
  have hl := hp.hlen
  obtain t_lt : 256 * i + j < 256 * pk s₀ := by omega_arith
  obtain hin : (hR s₀).Contains (coeffAddr (State.addr (pH s₀)) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain ea : State.addr (pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)) + BitVec.ofNat 32 0) =
      coeffAddr (State.addr (pH s₀)) (256 * i + j) := by
    rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
  obtain hw : s.mem.readW (coeffAddr (State.addr (pH s₀)) (256 * i + j)) 32 =
      coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) := by
    rw [← hA.hint _ t_lt, coeffAt_eq]
    exact hI.frame.readW hin (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.d_hy) (by decide)
  obtain hbit := hintAt_get (m := s₀.mem) (p := State.addr (pH s₀)) hi (show j < n from hj)
  obtain hT := hpT_succ s₀ i j
  obtain hidx := hpT_idx s₀ i j
  unfold hbpCoef
  refine WP.seq (WP.mono (coefLoad_ok hI.r0 (by
      rw [ea, hI.rd, hI.wr]; exact ⟨_, List.mem_append_left _ hA.rd, hin⟩))
    fun s₁ ⟨z₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  rw [ea, hw, sub_zero32] at z₁
  refine WP.seq (WP.ite (M := isa) _ (show some s₁.z = _ from rfl) (fun h0 => ?_) (fun h1 => ?_))
  · -- A 0.
    obtain h0 : coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) = 0 := by
      rw [z₁] at h0; exact beq_iff_eq.mp h0
    refine WP.block_nil (WP.mono (coefNext_ok (x := pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₁ _ (by decide), hI.r0])
        (by rw [g₁ _ (by decide), hI.r12])) fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₁, hI.rd], by rw [wr₃, wr₁, hI.wr], by rw [sp₃, sp₁, hI.sp],
        by rw [m₃, m₁]; exact hI.frame, ?_⟩, ?_⟩)
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega_arith]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r1, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, ofNat_succ32]
    · rw [m₃, m₁, hI.y, hT, hpStep, hbit]
      simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    · rw [z₃, ofNat_succ32]; exact cmp_const (by omega_arith) (by decide)
  · -- A 1: `y[index] ← j`.
    obtain h1 : coeffAt s₀.mem (State.addr (pH s₀)) (256 * i + j) ≠ 0 := by
      rw [z₁] at h1; exact fun e => by rw [e] at h1; exact absurd h1 (by decide)
    obtain hlt : (hpT s₀ i j).2 < pω s₀ := by
      have : onesBefore (pHint s₀) i j < hintOnes (pHint s₀) :=
        hpIdx_lt (hintAt_length s₀.mem _ _) hi hj (by rw [hbit]; exact decide_eq_true h1)
      have := hp.ones
      omega_arith
    obtain eb : State.addr (pY s₀ + BitVec.ofNat 32 (hpT s₀ i j).2 + BitVec.ofNat 32 0) =
        State.addr (pY s₀) + BitVec.ofNat 64 (hpT s₀ i j).2 := by
      rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
    obtain hinY : (yR s₀).Contains (State.addr (pY s₀) + BitVec.ofNat 64 (hpT s₀ i j).2) 1 :=
      Offset.contains_base _ (by omega_arith) (by omega_arith)
    refine WP.mono (coefSet_ok (i := BitVec.ofNat 32 (hpT s₀ i j).2) (y := pY s₀) (j := BitVec.ofNat 32 j)
        (by rw [g₁ _ (by decide), hI.r1]) (by rw [g₁ _ (by decide), hI.r3])
        (by rw [g₁ _ (by decide), hI.r12]) (by rw [eb, wr₁, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
      fun s₂ ⟨r1₂, m₂, rd₂, wr₂, sp₂, g₂⟩ => ?_
    refine WP.mono (coefNext_ok (x := pH s₀ + BitVec.ofNat 32 (4 * (256 * i + j)))
        (j := BitVec.ofNat 32 j) (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r0])
        (by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r12]))
      fun s₃ ⟨r0₃, r12₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ =>
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [rd₃, rd₂, rd₁, hI.rd], by rw [wr₃, wr₂, wr₁, hI.wr],
        by rw [sp₃, sp₂, sp₁, hI.sp], ?_, ?_⟩, ?_⟩
    · rw [r0₃, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ptr_add, show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega_arith]
    · rw [g₃ _ (by decide) (by decide), r1₂, hT, hpStep, hbit, ofNat_succ32]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r3]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r4]
    · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), g₁ _ (by decide), hI.r5]
    · rw [r12₃, ofNat_succ32]
    · rw [m₃, m₂, m₁, eb]
      exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
    · rw [m₃, m₂, m₁, eb, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), hI.y, hT, hpStep, hbit,
        setWidth8_ofNat]
      simp only [h1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, Array.set!_eq_setIfInBounds,
        Array.toList_setIfInBounds]
    · rw [z₃, ofNat_succ32]; exact cmp_const (by omega_arith) (by decide)

/-- The coefficients of polynomial `i`. -/
theorem coefs_ok {i : Nat} (hi : i < pk s₀) {s : State} (hI : CInv s₀ sA i 0 s) :
    WP isa (.loop hbpCoef .ne) s (CInv s₀ sA i 256) :=
  wp_loop_ne (CInv s₀ sA i) (N := 256) (by decide) (fun j hj _ h => coef_ok hp hA hi hj h) (fun _ h => h) hI

end

/-- Before polynomial `i`, in the loops that start from `sA`. -/
structure HPInv (s₀ sA : State) (i : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = pH s₀ + BitVec.ofNat 32 (4 * (256 * i))
  r1 : s.gpr .r1 = BitVec.ofNat 32 (hpS s₀ i).2
  r3 : s.gpr .r3 = pY s₀
  r4 : s.gpr .r4 = BitVec.ofNat 32 (1 * (pk s₀ - i))
  r5 : s.gpr .r5 = pY s₀ + BitVec.ofNat 32 (pω s₀ + i)
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  sp : s.sp = sA.sp
  frame : Frame [yR s₀] sA.mem s.mem
  y : bytesAt s.mem (State.addr (pY s₀)) (pLen s₀) = (hpS s₀ i).1.toList

theorem polyStart_ok {s : State} :
    WP isa (.block [.mov .r12 (.imm 0)]) s fun s' => s'.gpr .r12 = 0 ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r := by
  run_block []
  simp only [true_and]; intro r hr; rw [ite_neg' hr]

theorem polyEnd_ok {s : State} {x y c : BitVec 32} (h1 : s.gpr .r1 = x) (h5 : s.gpr .r5 = y)
    (h4 : s.gpr .r4 = c) (o : InRegions s.wr (State.addr (y + BitVec.ofNat 32 0)) 1) :
    WP isa (.block [.strb .r1 .r5 0, .dp .add .r5 .r5 (.imm 1), .subs .r4 .r4 (.imm 1)]) s fun s' =>
      s'.gpr .r5 = y + 1 ∧ s'.gpr .r4 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
      s'.mem = s.mem.writeW (State.addr (y + BitVec.ofNat 32 0)) (x.setWidth 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r := by
  run_block [h1, h5, h4, o]
  simp only [true_and]; intro r h4 h5; rw [ite_neg' h4, ite_neg' h5]

section
variable {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA)
include hp hA

/-- A polynomial. -/
theorem poly_ok {i : Nat} (hi : i < pk s₀) {s : State} (hP : HPInv s₀ sA i s) :
    WP isa hbpPoly s fun s' => HPInv s₀ sA (i + 1) s' ∧ s'.z = decide (i + 1 = pk s₀) := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  have fY := hp.fitY
  unfold hbpPoly
  refine WP.seq (WP.mono polyStart_ok fun s₁ ⟨r12₁, m₁, rd₁, wr₁, sp₁, g₁⟩ => ?_)
  refine WP.seq (WP.mono (coefs_ok hp hA hi (s := s₁) ⟨by rw [g₁ _ (by decide), hP.r0, Nat.add_zero], by rw [g₁ _ (by decide), hP.r1, hpT_zero],
    by rw [g₁ _ (by decide), hP.r3], by rw [g₁ _ (by decide), hP.r4], by rw [g₁ _ (by decide), hP.r5], by rw [r12₁]; rfl,
    by rw [rd₁, hP.rd], by rw [wr₁, hP.wr], by rw [sp₁, hP.sp], by rw [m₁]; exact hP.frame,
    by rw [m₁, hP.y, hpT_zero]⟩) fun s₂ hI => ?_)
  obtain hidx : (hpT s₀ i 256).2 < 256 := by
    have := hpT_idx s₀ i 256
    obtain h1 : onesBefore (pHint s₀) i 256 ≤ hintOnes (pHint s₀) := onesBefore_n_le (hintAt_length _ _ _) hi
    have := hp.ones
    omega_arith
  obtain ea : State.addr (pY s₀ + BitVec.ofNat 32 (pω s₀ + i) + BitVec.ofNat 32 0) =
      State.addr (pY s₀) + BitVec.ofNat 64 (pω s₀ + i) := by
    rw [addr_ptr _ _ _ (by omega_arith), Nat.add_zero]
  obtain hinY : (yR s₀).Contains (State.addr (pY s₀) + BitVec.ofNat 64 (pω s₀ + i)) 1 :=
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine WP.mono (polyEnd_ok hI.r1 hI.r5 hI.r4 (by rw [ea, hI.wr]; exact ⟨_, hA.wr, hinY⟩))
    fun s₃ ⟨r5₃, r4₃, z₃, m₃, rd₃, wr₃, sp₃, g₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [rd₃, hI.rd], by rw [wr₃, hI.wr],
      by rw [sp₃, hI.sp], ?_, ?_⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), hI.r0, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega_arith]
  · rw [g₃ _ (by decide) (by decide), hI.r1, hpS_succ]
  · rw [g₃ _ (by decide) (by decide), hI.r3]
  · rw [r4₃]; exact count_sub (k := 1) hi
  · rw [r5₃, BitVec.add_assoc, ofNat_succ32, Nat.add_assoc]
  · rw [m₃, ea]
    exact hI.frame.writeW (List.mem_singleton_self _) _ hinY
  · rw [m₃, ea, bytesAt_writeW8 _ _ (by omega_arith) (by omega_arith), hI.y, hpS_succ, setWidth8_ofNat,
      Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  · rw [z₃]; exact count_z (k := 1) hi (by decide) (by omega_arith)

end

theorem mainPro_ok {s : State} :
    WP isa (.block [.mov .r4 (.reg .r1), .dp .add .r5 .r3 (.reg .r2), .mov .r1 (.imm 0)]) s fun s' =>
      s'.gpr .r4 = s.gpr .r1 ∧ s'.gpr .r5 = s.gpr .r3 + s.gpr .r2 ∧ s'.gpr .r1 = 0 ∧ s'.gpr .r0 = s.gpr .r0 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  run_block []

/-- The polynomials, from the state after zeroing `y`. -/
theorem main_ok {s₀ : State} (hp : PPre s₀) {sA : State} (hA : MainPre s₀ sA) (h0 : sA.gpr .r0 = pH s₀)
    (h1 : sA.gpr .r1 = BitVec.ofNat 32 (pk s₀)) (h2 : sA.gpr .r2 = pW s₀) (h3 : sA.gpr .r3 = pY s₀)
    (hz : bytesAt sA.mem (State.addr (pY s₀)) (pLen s₀) = List.replicate (pLen s₀) 0) :
    WP isa hbpMain sA fun s' =>
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = hintBitPack (pω s₀) (pk s₀) (pHint s₀) ∧
      Frame [yR s₀] sA.mem s'.mem ∧ s'.rd = sA.rd ∧ s'.wr = sA.wr ∧ s'.sp = sA.sp := by
  obtain ⟨hk4, hk8, hω55, hω80, hsum, hL88⟩ := pfacts hp
  unfold hbpMain
  refine WP.seq (WP.mono mainPro_ok fun s₁ ⟨r4₁, r5₁, r1₁, r0₁, r3₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine wp_loop_ne (HPInv s₀ sA) (N := pk s₀) (by omega_arith) (fun i hi s h => poly_ok hp hA hi h)
    (fun s hP => ⟨hP.y.trans (hintBitPack_eq _ _ _).symm, hP.frame, hP.rd, hP.wr, hP.sp⟩)
    ⟨by rw [r0₁, h0]; simp, by rw [r1₁]; rfl, by rw [r3₁, h3], by rw [r4₁, h1, Nat.one_mul, Nat.sub_zero],
      by rw [r5₁, h3, h2, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq], rd₁, wr₁, sp₁,
      by rw [m₁]; exact Frame.refl _ _, ?_⟩
  rw [m₁, hz]
  show _ = (Array.replicate (pω s₀ + pk s₀) (0 : Byte)).toList
  rw [Array.toList_replicate, hsum]

/-! ## The function -/

theorem ldr5_ok {s : State} (ia : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 4)) 4) :
    WP isa (.block [.ldrSp .r5 4]) s fun s' =>
      s' = s.setReg .r5 (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 4)) 32) := by
  run_block [ia]

theorem frameR2 {s : State} (h : 8 ≤ s.sp.toNat) :
    frameR s [.r4, .r5] = ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ := frameR_eq [.r4, .r5] h

/-- The state the body runs from. -/
abbrev P1 (s₀ : State) : State := pushed [.r4, .r5] (s₀.setReg .r12 (pL s₀))

/-- The state after zeroing `y`. -/
def ZP (s₀ a : State) : Prop :=
  a.gpr .r0 = pH s₀ ∧ a.gpr .r1 = BitVec.ofNat 32 (pk s₀) ∧ a.gpr .r2 = pW s₀ ∧ a.gpr .r3 = pY s₀ ∧
    bytesAt a.mem (State.addr (pY s₀)) (pLen s₀) = List.replicate (pLen s₀) 0 ∧ Frame [yR s₀] (P1 s₀).mem a.mem ∧
    a.rd = (P1 s₀).rd ∧ a.wr = (P1 s₀).wr ∧ a.sp = (P1 s₀).sp

section
variable {s₀ : State} (hp : PPre s₀)
include hp

theorem hsp8 : 4 * [Reg.r4, Reg.r5].length ≤ (s₀.setReg .r12 (pL s₀)).sp.toNat := hp.sp

theorem hfr : frameR (s₀.setReg .r12 (pL s₀)) [.r4, .r5] = ⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩ :=
  frameR2 (s := s₀.setReg .r12 (pL s₀)) hp.sp

theorem zeroP_ok : WP isa hbpZero (P1 s₀) (ZP s₀) :=
  zero_ok hp rfl rfl rfl rfl (by simp [RegUpd.wr_setReg, hp.wr])

/-- The body changes memory only in the frame and `y`. -/
theorem zp_frame {a : State} (hz : ZP s₀ a) :
    Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩, yR s₀] s₀.mem a.mem := by
  obtain hpf := pushed_frame [.r4, .r5] (hsp8 hp)
  rw [hfr hp] at hpf
  exact (hpf.mono (by simp)).trans (hz.2.2.2.2.2.1.mono (by simp))

theorem zp_hint {a : State} (hz : ZP s₀ a) :
    ∀ t < 256 * pk s₀, coeffAt a.mem (State.addr (pH s₀)) t = coeffAt s₀.mem (State.addr (pH s₀)) t := by
  intro t ht
  have fH := hp.fitH
  have hl := hp.hlen
  rw [coeffAt_eq, coeffAt_eq]
  exact (zp_frame hp hz).readW (r := hR s₀) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.b_h.symm
    · exact hp.d_hy) (by decide)

theorem mainPre_of {a : State} (hz : ZP s₀ a) {rd wr : List Region} (hr : hR s₀ ∈ rd) (hw : yR s₀ ∈ wr) :
    MainPre s₀ (a.withRegions rd wr) := ⟨hr, hw, zp_hint hp (a := a) hz⟩

end

/-- The body of the frame: `y`, the reload of `r5`, and the word the pop reloads into `r4`. -/
theorem body_ok {s₀ : State} (hp : PPre s₀) :
    WP isa hintBitPackBody (P1 s₀) fun s₂ => s₂.sp = (P1 s₀).sp ∧ s₂.gpr .r5 = s₀.gpr .r5 ∧
      s₂.mem.readW (State.addr s₂.sp) 32 = s₀.gpr .r4 ∧
      bytesAt s₂.mem (State.addr (pY s₀)) (pLen s₀) = Spec.MlDsa.hintBitPack (pω s₀) (pk s₀) (pHint s₀) := by
  obtain hsp8 := hsp8 hp
  unfold hintBitPackBody
  refine WP.seq (WP.mono (zeroP_ok hp) fun sa hz => ?_)
  obtain ⟨a0, a1, a2, a3, az, af, ard, awr, asp⟩ := id hz
  obtain hA : MainPre s₀ sa := by
    have := mainPre_of hp hz (rd := sa.rd) (wr := sa.wr)
      (by rw [ard]; simp [RegUpd.rd_setReg, hp.rd]) (by rw [awr]; simp [RegUpd.wr_setReg, hp.wr])
    rwa [State.withRegions_self] at this
  refine WP.seq (WP.mono (main_ok hp hA a0 a1 a2 a3 az) fun sb ⟨by', bf, brd, bwr, bsp⟩ => ?_)
  obtain hfb : Frame [yR s₀] (P1 s₀).mem sb.mem := af.trans bf
  obtain hdy : ∀ r ∈ [yR s₀], (frameR (s₀.setReg .r12 (pL s₀)) [.r4, .r5]).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hfr hp]; exact hp.b_y
  obtain hsb : sb.sp = (P1 s₀).sp := by rw [bsp, asp]
  refine WP.mono (ldr5_ok (by
      rw [bwr, awr, pushed_wr, hsb]
      exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..),
        frameR_contains [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 (i := 1) (by decide)⟩))
    fun s₂ e₂ => ?_
  subst e₂
  refine ⟨hsb, ?_, ?_, by' ⟩
  · simp only [RegUpd.gpr_setReg_self]
    rw [hsb, frame_saved [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 hfb hdy (i := 1) (by decide)]
    rfl
  · simp only [RegUpd.mem_setReg, RegUpd.sp_setReg]
    rw [hsb, show State.addr (P1 s₀).sp = State.addr ((P1 s₀).sp + BitVec.ofNat 32 (4 * 0)) by simp,
      frame_saved [.r4, .r5] (s := s₀.setReg .r12 (pL s₀)) hsp8 hfb hdy (i := 0) (by decide)]
    rfl

/-- The whole function: `y`, and the registers it saves and restores (the
others it never writes). -/
theorem correct {s₀ : State} (hp : PPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.hintBitPack s₀ fun s' => s'.gpr .r4 = s₀.gpr .r4 ∧ s'.gpr .r5 = s₀.gpr .r5 ∧
      s'.gpr .lr = s₀.gpr .lr ∧ s'.sp = s₀.sp ∧
      bytesAt s'.mem (State.addr (pY s₀)) (pLen s₀) = Spec.MlDsa.hintBitPack (pω s₀) (pk s₀) (pHint s₀) := by
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine WP.seq (WP.mono (entry_ok (s := s₀) (by
    rw [hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩)) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.frame (rs := [.r4, .r5]) (r := .r4) rfl (hsp8 hp) (by decide)
    (WP.mono (WP.gpr (body_ok hp) (r := .lr) (noWrite (by decide +kernel)))
      fun s₂ ⟨⟨hsp, h5, h4, hy⟩, hlr⟩ mL uL hfl => ?_)
  replace hfl : Frame [⟨State.addr s₀.sp - BitVec.ofNat 64 8, 8⟩] s₂.mem mL := by rw [← hfr hp]; exact hfl
  dsimp only
  refine ⟨?_, by rw [popped_gpr (by decide), h5], by rw [popped_gpr (by decide), hlr]; rfl, ?_, ?_⟩
  · simp only [popped, State.setReg, ite_true]; exact h4
  · simp only [popped_sp, hsp, P1, pushed_sp]
    exact BitVec.sub_add_cancel _ _
  · rw [Proof.MlKem.bytesAt_frame hfl (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.b_y.symm)
      (by have := hp.fitY; omega_arith)]
    exact hy

end VG.Proof.MlDsa.Arm.Pack.Hint

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_hint_bit_pack`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the lengths,
`ω`, the stack pointer and the hint, which the contract lets the function
leak) leak the same trace (`RelCT`), phase by phase: the load of `len` and the
frame's reload of `r5` access only the stack (`RelCT.spBlock`); zeroing `y` is
proved by the taint analysis; the loops by `memTaint`, from the states
narrowed to the hint and `y` (`RelCT.narrow`), on which both runs agree once
`y` is zeroed. What each run is at each point comes from the correctness proof
(`RelCT.wp`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_getD)
open VG.Proof.MlDsa.Pack

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega_using [ha]
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

theorem pre_of {s : State} (h : (hintBitPackContract Arm.abi 8).pre s) : PPre s := by
  sig_pre [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : PPre s₁
  hp₂ : PPre s₂
  sp : s₁.sp = s₂.sp
  leak : (List.range (s₁.gpr .r1).toNat).map (fun i => (coeffAt s₁.mem (State.addr (pH s₁)) i).toNat) =
    (List.range (s₂.gpr .r1).toNat).map (fun i => (coeffAt s₂.mem (State.addr (pH s₂)) i).toNat)
  r0 : s₁.gpr .r0 = s₂.gpr .r0
  r1 : s₁.gpr .r1 = s₂.gpr .r1
  r2 : s₁.gpr .r2 = s₂.gpr .r2
  r3 : s₁.gpr .r3 = s₂.gpr .r3
  arg : stackArg s₁ 0 = stackArg s₂ 0

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem hR_eq : hR s₁ = hR s₂ := by simp only [hR, pH, h.r0, h.r1]

theorem yR_eq : yR s₁ = yR s₂ := by simp only [yR, pY, pLen, pL, h.r3, h.arg]

/-- The hint and the zeroed `y`: the memory both runs agree on. -/
theorem memEq {a b : State} (ha : ZP s₁ a) (hb : ZP s₂ b) : Hint.MemEq ([hR s₁] ++ [yR s₁]) a.mem b.mem := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  obtain ⟨hk4, -, -, -, hsum, hL88⟩ := pfacts hp₁
  intro x ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · -- The hint: as on entry.
    have e₁ := zp_frame hp₁ ha x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₁.b_h x hc' hc
      · exact hp₁.d_hy x hc hc')
    rw [hR_eq h] at hc
    have e₂ := zp_frame hp₂ hb x (fun r hr hc' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp₂.b_h x hc' hc
      · exact hp₂.d_hy x hc hc')
    rw [e₁, e₂]
    rw [← hR_eq h] at hc
    have hl := h.leak
    rw [show State.addr (pH s₂) = State.addr (pH s₁) by simp only [pH, h.r0], ← h.r1] at hl
    exact bytes_of_words hl hc
  · -- `y`: zeros.
    have hlt : (x - State.addr (pY s₁)).toNat < pLen s₁ := by simp only [Region.Contains] at hc; omega_using [hc]
    have ea : x = State.addr (pY s₁) + BitVec.ofNat 64 (x - State.addr (pY s₁)).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have e₁ : (bytesAt a.mem (State.addr (pY s₁)) (pLen s₁)).getD (x - State.addr (pY s₁)).toNat 0 =
        (List.replicate (pLen s₁) (0 : Byte)).getD (x - State.addr (pY s₁)).toNat 0 := by rw [ha.2.2.2.2.1]
    have e₂ : (bytesAt b.mem (State.addr (pY s₂)) (pLen s₂)).getD (x - State.addr (pY s₁)).toNat 0 =
        (List.replicate (pLen s₂) (0 : Byte)).getD (x - State.addr (pY s₁)).toNat 0 := by rw [hb.2.2.2.2.1]
    rw [bytesAt_getD _ _ hlt, ← ea] at e₁
    rw [show pY s₂ = pY s₁ by simp only [pY, h.r3], show pLen s₂ = pLen s₁ by simp only [pLen, pL, h.arg],
      bytesAt_getD _ _ hlt, ← ea] at e₂
    rw [e₁, e₂]

/-- The loops, from the states narrowed to the hint and `y`. -/
theorem main_ct : RelCT isa (fun a b => ZP s₁ a ∧ ZP s₂ b) hbpMain fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine Hint.RelCT.narrow (fun _ => [hR s₁]) (fun _ => [yR s₁]) (fun a b ⟨ha, hb⟩ => ?_) (fun a b ⟨ha, hb⟩ => ?_) ?_
  · have hra : hR s₁ ∈ a.rd := by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd]
    have hwa : yR s₁ ∈ a.wr := by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr]
    have hrb : hR s₁ ∈ b.rd := by rw [hb.2.2.2.2.2.2.1, hR_eq h]; simp [RegUpd.rd_setReg, hp₂.rd]
    have hwb : yR s₁ ∈ b.wr := by rw [hb.2.2.2.2.2.2.2.1, yR_eq h]; simp [RegUpd.wr_setReg, hp₂.wr]
    exact ⟨Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hra
        · exact List.mem_append_right _ hwa,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwa,
      Covers.of_mem fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_append_left _ hrb
        · exact List.mem_append_right _ hwb,
      Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hwb⟩
  · obtain ⟨a0, a1, a2, a3, az, -⟩ := id ha
    obtain ⟨b0, b1, b2, b3, bz, -⟩ := id hb
    obtain ⟨t₁, u₁, e₁, -⟩ := main_ok hp₁ (mainPre_of hp₁ ha (rd := [hR s₁]) (wr := [yR s₁])
      (List.mem_singleton_self _) (List.mem_singleton_self _)) a0 a1 a2 a3 az
    obtain ⟨t₂, u₂, e₂, -⟩ := main_ok hp₂ (mainPre_of hp₂ hb (rd := [hR s₁]) (wr := [yR s₁])
      (by rw [hR_eq h]; exact List.mem_singleton_self _) (by rw [yR_eq h]; exact List.mem_singleton_self _))
      b0 b1 b2 b3 bz
    exact ⟨⟨t₁, u₁, e₁⟩, t₂, u₂, e₂⟩
  · refine RelCT.taint (A := Hint.memTaint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun a' b' ⟨a, b, ⟨ha, hb⟩, ea, eb⟩ => ?_) (by native_taint_decide)
    subst ea eb
    refine ⟨Taint.agree_ofRegs fun r hr => ?_, rfl, rfl, memEq h (a := a) (b := b) ha hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [State.withRegions_gpr, ha.1, hb.1, pH, h.r0]
    · simp only [State.withRegions_gpr, ha.2.1, hb.2.1, pk, pLen, pL, pω, pW, h.r2, h.arg]
    · simp only [State.withRegions_gpr, ha.2.2.1, hb.2.2.1, pW, h.r2]
    · simp only [State.withRegions_gpr, ha.2.2.2.1, hb.2.2.2.1, pY, h.r3]

/-- The body of the frame. -/
theorem body_ct : RelCT isa (fun a b => a = P1 s₁ ∧ b = P1 s₂) hintBitPackBody fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold hintBitPackBody
  refine RelCT.seq (R := fun a b => ZP s₁ a ∧ ZP s₂ b) (relct_wp ?_ fun a b ⟨ea, eb⟩ =>
    ⟨by rw [ea]; exact zeroP_ok hp₁, by rw [eb]; exact zeroP_ok hp₂⟩) ?_
  · refine RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs [.r2, .r3, .r12])
      (fun a b ⟨ea, eb⟩ => Taint.agree_ofRegs fun r hr => ?_) (by native_taint_decide)
    subst ea eb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r2]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, h.r3]; rfl
    · simp only [P1, pushed_gpr, RegUpd.gpr_setReg, pL, h.arg]; rfl
  refine RelCT.seq (R := fun (a b : State) => a.sp = (P1 s₁).sp ∧ b.sp = (P1 s₂).sp)
    (relct_wp (main_ct h) fun a b hab => ⟨?_, ?_⟩) ?_
  · have ha := hab.1
    obtain ⟨a0, a1, a2, a3, az, -, -, -, asp⟩ := id ha
    refine WP.mono (main_ok hp₁ ?_ a0 a1 a2 a3 az) fun s' hs => hs.2.2.2.2.trans asp
    have := mainPre_of hp₁ ha (rd := a.rd) (wr := a.wr) (by rw [ha.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₁.rd])
      (by rw [ha.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₁.wr])
    rwa [State.withRegions_self] at this
  · have hb := hab.2
    obtain ⟨b0, b1, b2, b3, bz, -, -, -, bsp⟩ := id hb
    refine WP.mono (main_ok hp₂ ?_ b0 b1 b2 b3 bz) fun s' hs => hs.2.2.2.2.trans bsp
    have := mainPre_of hp₂ hb (rd := b.rd) (wr := b.wr) (by rw [hb.2.2.2.2.2.2.1]; simp [RegUpd.rd_setReg, hp₂.rd])
      (by rw [hb.2.2.2.2.2.2.2.1]; simp [RegUpd.wr_setReg, hp₂.wr])
    rwa [State.withRegions_self] at this
  · exact Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by
      rw [ea, eb]; simp only [P1, pushed_sp, RegUpd.sp_setReg, h.sp]

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) Impl.MlDsa.Arm.Pack.hintBitPack fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  unfold Impl.MlDsa.Arm.Pack.hintBitPack
  refine RelCT.seq (R := fun a b => a = s₁.setReg .r12 (pL s₁) ∧ b = s₂.setReg .r12 (pL s₂))
    (relct_wp (Hint.RelCT.spBlock (by decide) fun a b ⟨ea, eb⟩ => by rw [ea, eb, h.sp]) fun a b ⟨ea, eb⟩ =>
      ⟨by rw [ea]; exact entry_ok (by rw [hp₁.rd]; exact ⟨argR s₁, by simp, Region.contains_self _ _⟩),
       by rw [eb]; exact entry_ok (by rw [hp₂.rd]; exact ⟨argR s₂, by simp, Region.contains_self _ _⟩)⟩) ?_
  refine RelCT.frame (fun a b ⟨ea, eb⟩ => by rw [ea, eb]; simp only [RegUpd.sp_setReg, h.sp]) ?_
  refine RelCT.mono (body_ct h) (fun a b ⟨x, y, ⟨ex, ey⟩, px, py⟩ => ?_) fun _ _ h => h
  subst ex ey
  exact ⟨(push_pushed' px).1, (push_pushed' py).1⟩

end

/-! ## Verified -/

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := by
  simp [coeffAt, Mem.readW, Mem.read]

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_zero l]

theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, coeffAt_zero, Function.comp_def, filter_false, sum_zero]

theorem hintAt_congr {m m' : Mem} {p : Addr} {k : Nat}
    (h : ∀ t < 256 * k, coeffAt m p t = coeffAt m' p t) : hintAt m p k = hintAt m' p k := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  congr 1; funext j
  have hj : j.val < 256 := j.isLt
  rw [h _ (by omega_using [hi, hj])]

/-- The memory of the satisfying state: `len = 84` on the stack. -/
def satMem : Mem := fun a => if a = 0x8000 then 84 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1024 | .r2 => 80 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0x1000, 4096⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x3000, 84⟩]

theorem satArg : stackArg satState 0 = 84 := by decide +kernel

theorem satHint : hintOnes (hintAt satMem 0x1000 4) = 0 := by
  rw [hintAt_congr (m' := fun _ => 0) fun t ht => ?_, hintOnes_zero]
  rw [coeffAt_eq, coeffAt_eq]
  refine Mem.readW_congr fun b hb => ?_
  simp only [satMem]
  rw [ite_neg' fun e => by bv_omega]

theorem hintBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.hintBitPack (hintBitPackContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h4, h5, hlr, hsp, hy⟩ := correct hp
    refine ⟨t, s', he, ⟨fun r hr => ?_, hsp⟩, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h4
      · exact h5
      rotate_right
      · exact hlr
      all_goals exact Exec.gpr (noWrite (by decide +kernel)) he
    · sig_post [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      exact hy
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hl, h0, h1, h2, h3, ha⟩ := hpub
    exact (all_ct ⟨hp₁, hp₂, hsp, hl, h0, h1, h2, h3, ha⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [hintBitPackContract, hintBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      rotate_right
      · rw [satArg, show (BitVec.setWidth 32 (BitVec.setWidth 64 (84 : BitVec 32))).toNat -
          (BitVec.setWidth 32 (BitVec.setWidth 64 (80 : BitVec 32))).toNat = 4 by decide,
          show BitVec.setWidth 64 (4096 : BitVec 32) = 0x1000 by decide, satHint]
        exact Nat.zero_le _
      all_goals decide +kernel

end VG.Proof.MlDsa.Arm.Pack.Hint

end

end

/-! ### `MlDsa.Arm.Round.MakeHint`, which only this module used -/

section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_make_hint`

The loop body is symbolically executed once for each value of `γ₂`
(`body_ok`): the hint is `(r₁(r) ⊕ r₁(r + z mod q) + 63) >> 6`, 1 exactly when
the two differ, as both are less than 64 (`bmh_val`, from `makeHint_eq`), and
`r4` counts the 1s (`onesFrom`). `γ₂` selects one of two loops, in the frames
that save `r4`–`r6`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Round.MakeHint

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq makeHint)
open VG.Proof.MlDsa (coeffAt polyAt Reduced HintIs hintOnes gamma2s)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS)
open VG.Impl.MlDsa.Arm.Arith (fixupS subQ)
open VG.Proof.MlDsa.Arm.Arith (Entry wp_saving ct_of_saving preserved_of_saving)

/-! ## Values -/

/-- What the body stores, for the words `z` and `r`. -/
def bmh (g : Nat) (z r : BitVec 32) : BitVec 32 :=
  ((bhb g (fixS (r + z - 0x800000 + 0x2000 - 1)) ^^^ bhb g r) + 63) >>> 6

theorem sumq_val {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (fixS (r + z - 0x800000 + 0x2000 - 1)).toNat = (r.toNat + z.toNat) % q := by
  rw [VG.Proof.MlDsa.Arm.Arith.AddSub.fixS_add hr hz]

theorem bmh_val {g : Nat} (hg : G2 g) (z r : Zq) :
    bmh g (BitVec.ofNat 32 z.val) (BitVec.ofNat 32 r.val) = (makeHint g z r).toNat := by
  have hz : z.val < 8380417 := z.isLt
  have hr : r.val < 8380417 := r.isLt
  have ez : (BitVec.ofNat 32 z.val).toNat = z.val := by rw [BitVec.toNat_ofNat]; omega_arith
  have er : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega_arith
  have hs := sumq_val (z := BitVec.ofNat 32 z.val) (r := BitVec.ofNat 32 r.val) (by rw [ez]; exact z.isLt)
    (by rw [er]; exact r.isLt)
  rw [ez, er] at hs
  have hsq : (r.val + z.val) % q < q := Nat.mod_lt _ (by decide)
  have h1 := bhb_toNat hg (a := fixS (BitVec.ofNat 32 r.val + BitVec.ofNat 32 z.val - 0x800000 + 0x2000 - 1))
    (by rw [hs]; exact hsq)
  have h2 := bhb_toNat hg (a := BitVec.ofNat 32 r.val) (by rw [er]; exact r.isLt)
  rw [hs] at h1
  rw [er] at h2
  have hm : hbM g ≤ 44 := by rcases hg with rfl | rfl <;> decide
  have hm0 : 0 < hbM g := by rcases hg with rfl | rfl <;> decide
  rw [makeHint_eq hg.mem]
  unfold bmh
  generalize bhb g (fixS _) = X at h1
  generalize bhb g (BitVec.ofNat 32 r.val) = Y at h2
  have hX : X.toNat < 64 := by rw [h1]; have := Nat.mod_lt (hbF g ((r.val + z.val) % q)) hm0; omega_arith
  have hY : Y.toNat < 64 := by rw [h2]; have := Nat.mod_lt (hbF g r.val) hm0; omega_arith
  have hxy : (X ^^^ Y).toNat < 64 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 6) hX hY
  have e : (X ^^^ Y = 0) ↔ X = Y := by
    constructor
    · intro h
      rw [← BitVec.xor_zero (x := X), ← BitVec.xor_self (x := Y), ← BitVec.xor_assoc, h]; exact BitVec.zero_xor
    · intro h; subst h; simp
  by_cases h : hbF g r.val % hbM g = hbF g ((r.val + z.val) % q) % hbM g
  · have hXY : X = Y := BitVec.eq_of_toNat_eq (by rw [h1, h2, h])
    rw [e.mpr hXY, decide_eq_false (fun h' => h' h)]
    rfl
  · have hXY : X ^^^ Y ≠ 0 := fun h' => h (by rw [← h2, ← h1, e.mp h'])
    rw [decide_eq_true h]
    have : (X ^^^ Y).toNat ≠ 0 := fun h' => hXY (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    generalize X ^^^ Y = W at hxy this
    show _ = (1 : BitVec 32)
    bv_omega

/-! ## The body -/

section
variable {s : State} {x0 x1 x3 c v : BitVec 32} (h0 : s.gpr .r0 = x0) (h1 : s.gpr .r1 = x1) (h2 : s.gpr .r2 = c)
  (h3 : s.gpr .r3 = x3) (h4 : s.gpr .r4 = v)
  (iZ : InRegions (s.rd ++ s.wr) (State.addr (x0 + BitVec.ofNat 32 0)) 4)
  (iR : InRegions (s.rd ++ s.wr) (State.addr (x1 + BitVec.ofNat 32 0)) 4)
  (oH : InRegions s.wr (State.addr (x3 + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 h3 h4 iZ iR oH

theorem body_ok {g : Nat} (hg : G2 g) :
    WP isa (.block (mhBody g)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x3 + BitVec.ofNat 32 0))
        (bmh g (s.mem.readW (State.addr (x0 + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32)) ∧
      s'.gpr .r4 = v + bmh g (s.mem.readW (State.addr (x0 + BitVec.ofNat 32 0)) 32)
          (s.mem.readW (State.addr (x1 + BitVec.ofNat 32 0)) 32) ∧
      s'.gpr .r0 = x0 + 4 ∧ s'.gpr .r1 = x1 + 4 ∧ s'.gpr .r3 = x3 + 4 ∧ s'.gpr .r2 = c - 1 ∧
      s'.z = (c - 1 == 0) ∧ (∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rcases hg with rfl | rfl <;>
  · run_block [mhBody, hb, hbRaw, csubM, addMaskM, subQ, fixupS, tail013, bmh, fixS, bhb, bcsubM, bhbRaw,
      h0, h1, h2, h3, h4, iZ, iR, oH, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_self, and_true]

end

/-! ## The loop -/

/-- The precondition, on entry. -/
structure PreE (s : State) : Prop where
  sp : 12 ≤ s.sp.toNat
  rd : s.rd = [pR (P s .r0), pR (P s .r1)]
  wr : s.wr = [pR (P s .r3)]
  d0 : (pR (P s .r0)).Disjoint (pR (P s .r3))
  d1 : (pR (P s .r1)).Disjoint (pR (P s .r3))
  s0 : (belowA s.sp 12).Disjoint (pR (P s .r0))
  s1 : (belowA s.sp 12).Disjoint (pR (P s .r1))
  s3 : (belowA s.sp 12).Disjoint (pR (P s .r3))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  g : (s.gpr .r2).toNat ∈ gamma2s
  redZ : Reduced s.mem (P s .r0)
  redR : Reduced s.mem (P s .r1)

theorem pre_of {s : State} (h : (Proof.MlDsa.makeHintContract Arm.abi 12).pre s) : PreE s := by
  sig_pre [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- The registers the loops keep. -/
abbrev fixedR : List Reg := [.r7, .r8, .r9, .r10, .r11, .lr]

/-- The hint of the polynomials on entry. -/
abbrev hint (s : State) (g : Nat) : Vector Bool n :=
  Vector.zipWith (makeHint g) (polyAt s.mem (P s .r0)) (polyAt s.mem (P s .r1))

theorem hint_word {s : State} (hp : PreE s) {g : Nat} (hg : G2 g) {k : Nat} (hk : k < 256) :
    bmh g (coeffAt s.mem (P s .r0) k) (coeffAt s.mem (P s .r1) k) = ((hint s g)[k]!).toNat := by
  have hk' : k < n := by rw [n_eq]; exact hk
  rw [zipWith_get _ _ _ hk', polyAt_get _ _ hk', polyAt_get _ _ hk', ← bmh_val hg,
    word_of_reduced (hp.redZ k hk'), word_of_reduced (hp.redR k hk')]

theorem loop {s s₁ s₂ : State} (hp : PreE s) (hE : Entry 12 s s₁) {g : Nat} (hg : G2 g)
    (hg₂ : ∀ r, r ≠ .r4 → s₂.gpr r = s.gpr r) (h4 : s₂.gpr .r4 = 0) (hm : s₂.mem = s₁.mem)
    (hrd : s₂.rd = s₁.rd) (hwr : s₂.wr = s₁.wr) (hsp : s₂.sp = s₁.sp) :
    WP isa (mapLoop .r2 (mhBody g)) s₂ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧
      Frame [pR (P s .r3)] s₁.mem s'.mem ∧ (s'.gpr .r4).toNat = onesFrom (hint s g) 0 ∧
      ∀ k < 256, coeffAt s'.mem (P s .r3) k = ((hint s g)[k]!).toNat := by
  have e : ∀ r, r ≠ .r4 → P s₂ r = P s r := fun r hr => by simp only [P, hg₂ r hr]
  have hL : Layout s₂ [.r0, .r1] [.r3] := by
    refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, List.pairwise_singleton _ _, fun p hp' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e _ (by decide), hrd, hE.rd, hp.rd] <;> simp
    · simp only [List.mem_singleton] at ho; subst ho
      rw [e _ (by decide), hwr]; exact hE.wr _ (by rw [hp.wr]; simp)
    · simp only [List.mem_singleton] at ho; subst ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> rw [e _ (by decide), e _ (by decide)]
      exacts [hp.d0, hp.d1]
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> rw [hg₂ _ (by decide)]
      exacts [hp.f0, hp.f1, hp.f3]
  have eIn : ∀ p, p = .r0 ∨ p = .r1 → ∀ k < 256, coeffAt s₂.mem (P s₂ p) k = coeffAt s.mem (P s p) k := by
    intro p hp' k hk
    have hd : (belowA s.sp 12).Disjoint (pR (P s p)) := by rcases hp' with rfl | rfl; exacts [hp.s0, hp.s1]
    rw [e p (by rcases hp' with rfl | rfl <;> decide), hm]
    exact coeffAt_frame hE.frame (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hd.symm) (by rw [n_eq]; exact hk)
  refine WP.mono (loop_ok (ptrs := [.r0, .r1, .r3]) (fixed := fixedR)
    (V := fun _ i => bmh g (coeffAt s₂.mem (P s₂ .r0) i) (coeffAt s₂.mem (P s₂ .r1) i))
    (J := fun i s' => (s'.gpr .r4).toNat + onesFrom (hint s g) i = onesFrom (hint s g) 0 ∧ (s'.gpr .r4).toNat ≤ i)
    hL (by decide) (by decide) (fun s' hs' _ => ?_) fun i hi s' hI => ?_) fun s' hI => ⟨fun r hr => ?_, ?_, ?_,
      ?_, fun k hk => ?_⟩
  · rw [hs']; simp only [show Reg.r4 ≠ Reg.r2 by decide, ite_false, h4]
    exact ⟨Nat.zero_add _, Nat.zero_le _⟩
  · refine WP.mono (body_ok rfl rfl rfl rfl rfl (hI.inR hL hi (by simp) (by simp)) (hI.inR hL hi (by simp) (by simp))
      (hI.inW hL hi (by simp) (by simp)) hg)
      fun s'' ⟨hm', r4, r0, r1, r3, r2, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r2, hz, hf, rd, wr, sp, ?_⟩
    · rw [hm', hI.read hL hi (by simp) (by simp), hI.read hL hi (p := .r1) (by simp) (by simp),
        hI.addr hL hi (p := .r3) (by simp) (by simp)]; rfl
    · intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl
      exacts [r0, r1, r3]
    · rw [hI.read hL hi (by simp) (by simp), hI.read hL hi (p := .r1) (by simp) (by simp), eIn _ (.inl rfl) i hi,
        eIn _ (.inr rfl) i hi, hint_word hp hg hi] at r4
      obtain ⟨hj, hle⟩ := hI.j
      have hs := onesFrom_step (hint s g) (lo := i) (by rw [n_eq]; exact hi)
      have hb : ((hint s g)[i]!).toNat ≤ 1 := by cases (hint s g)[i]! <;> decide
      have ht : (s''.gpr .r4).toNat = (s'.gpr .r4).toNat + ((hint s g)[i]!).toNat := by
        rw [r4]
        have : ((((hint s g)[i]!).toNat : Nat) : BitVec 32).toNat = ((hint s g)[i]!).toNat := by
          rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]; omega_arith
        rw [BitVec.toNat_add, this]; omega_arith
      exact ⟨by omega_arith, by omega_arith⟩
  · rw [hI.fixed r hr, hg₂ r (by revert r; decide)]
  · rw [hI.sp, hsp]
  · have := hI.frame; simp only [List.map_cons, List.map_nil] at this
    rw [e .r3 (by decide), hm] at this; exact this
  · have := hI.j.1; simp only [onesFrom_n, Nat.add_zero] at this; exact this
  · rw [← e _ (by decide), hI.done .r3 (by simp) k hk, eIn _ (.inl rfl) k hk, eIn _ (.inr rfl) k hk,
      hint_word hp hg hk]

/-- A hint stored apart from a frame is what it was, whatever the frame holds. -/
private theorem hintIs_lost {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) {h : Vector Bool n} (hh : HintIs m p 1 [h]) : HintIs m' p 1 [h] := by
  refine ⟨hh.1, fun i hi j hj => ?_⟩
  rw [coeffAt_frame hf hd (by rw [n_eq] at hj ⊢; omega_using [hi, hj])]
  exact hh.2 i hi j hj

theorem correct {s : State} (hp : PreE s) :
    WP isa Impl.MlDsa.Arm.Round.makeHint s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      HintIs s'.mem (P s .r3) 1 [hint s (s.gpr .r2).toNat] ∧
      (s'.gpr .r0).toNat = hintOnes [hint s (s.gpr .r2).toNat] := by
  have hG : G2 (s.gpr .r2).toNat := (mem_gamma2s hp.g).elim .inr .inl
  refine WP.mono (wp_saving [.r4, .r5, .r6] _ (W := [pR (P s .r3)])
    (fun s₂ => (∀ r ∈ fixedR, s₂.gpr r = s.gpr r) ∧ HintIs s₂.mem (P s .r3) 1 [hint s (s.gpr .r2).toNat] ∧
      (s₂.gpr .r0).toNat = hintOnes [hint s (s.gpr .r2).toNat])
    s hp.sp (fun R hR => by rw [List.mem_singleton] at hR; subst hR; exact hp.s3)
    (fun _ _ _ hf ⟨hk, hh, h0⟩ => ⟨hk, hintIs_lost hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.s3.symm) hh, h0⟩) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨hk, hh, h0⟩, hm, _, hsp, _, hg⟩ =>
      ⟨preserved_of_saving hg fun r hr hn => hk r (by revert r; decide), hsp, hm ▸ hh, by rw [hg .r0]; exact h0⟩
  have he : encodable (BitVec.ofNat 32 g88) = true := by decide
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [gammaCmp, runBlock_cons, runStep_some, exec, Op2.eval, he, ite_true, Option.map_some]
    rfl, ?_⟩)
  have hz := VG.Proof.MlKem.Arm.cmp_z (s₁.gpr .r2) g88 (by decide)
  have hloop : ∀ g, G2 g → g = (s.gpr .r2).toNat → WP isa (mapLoop .r2 (mhBody g))
      ((subFlags s₁ (s₁.gpr .r2) (BitVec.ofNat 32 g88)).setReg .r4 0) fun s' =>
        (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s₁.sp ∧ Frame [pR (P s .r3)] s₁.mem s'.mem ∧
        (s'.gpr .r4).toNat = onesFrom (hint s (s.gpr .r2).toNat) 0 ∧
        ∀ k < 256, coeffAt s'.mem (P s .r3) k = ((hint s (s.gpr .r2).toNat)[k]!).toNat := fun g hg eg => by
    subst eg
    exact loop hp hE hg (fun r hr => by simp [State.setReg, hr, subFlags, hE.gpr]) (by simp [State.setReg])
      rfl rfl rfl rfl
  refine WP.seq (WP.mono
    (WP.ite (decide ((s₁.gpr .r2).toNat = g88)) (by simp only [eval, subFlags, State.setReg, hz])
      (fun h => hloop g88 (.inr rfl) (by rw [← of_decide_eq_true h, hE.gpr]))
      (fun h => hloop g32 (.inl rfl) (by
        have := of_decide_eq_false h
        rw [hE.gpr] at this
        rcases mem_gamma2s hp.g with h' | h'
        · exact absurd h' this
        · exact h'.symm))) fun s₃ ⟨hf, hsp, hfr, h4, hc⟩ => ?_)
  run_block []
  refine ⟨hfr, fun r hr => ?_, ?_, ?_⟩
  · have : r ≠ .r0 := by revert r; decide
    rw [ite_eq_right this]; exact hf r hr
  · exact hintIs_of_toNat fun j hj => hc j (by rw [n_eq] at hj; exact hj)
  · rw [hintOnes_single]; exact h4

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 95232 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Round.makeHint (Proof.MlDsa.makeHintContract Arm.abi 12) := by
  refine ⟨fun s hs => ?_, ct_of_saving [.r4, .r5, .r6] _ [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_)
    (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, hh, h0⟩ := correct (pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [VG.Proof.MlKem.Arm.setWidth_append32]
    exact ⟨hh, h0⟩
  · sig_pub [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1, h2, h3⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.makeHintContract, Proof.MlDsa.makeHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.MakeHint

end

end

/-!
# ML-DSA signing on ARMv7: the primitives it calls

The verified ARMv7 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`), with 28 bytes of stack below the
function's stack pointer: their contracts with the stack of their
registrations (at most 28 bytes, or 20 for the four whose fifth argument
signing pushes), that their frames fit in it, and, of the two samplers whose
result signing branches on, that it depends only on their public data and that
they succeed only if the algorithm finishes within `maxBounds` (from what
their own proofs say they return).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The ARMv7 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.Arm.Arith.ntt
  invNtt := Impl.MlDsa.Arm.Arith.nttInv
  mul := Impl.MlDsa.Arm.Arith.mul
  mulAdd := Impl.MlDsa.Arm.Arith.mulAdd
  add := Impl.MlDsa.Arm.Arith.add
  sub := Impl.MlDsa.Arm.Arith.sub
  rejNTT := Impl.MlDsa.Arm.Sample.rejNTT
  expandMask := Impl.MlDsa.Arm.Sample.expandMask
  ball := Impl.MlDsa.Arm.Sample.sampleInBall
  highBits := Impl.MlDsa.Arm.Round.highBits
  lowBits := Impl.MlDsa.Arm.Round.lowBits
  normLt := Impl.MlDsa.Arm.Round.normLt
  makeHint := Impl.MlDsa.Arm.Round.makeHint
  simpleBitPack := Impl.MlDsa.Arm.Pack.simpleBitPack
  bitPack := Impl.MlDsa.Arm.Pack.bitPack
  bitUnpack := Impl.MlDsa.Arm.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.Arm.Pack.hintBitPack

/-- The stack signing may use below its stack pointer. -/
abbrev signStack : Nat := 28

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.Arm.Sample VG.Proof.MlDsa.Sample

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.rejNTT s tr s') :
    s'.gpr .r0 = if (rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := RejNtt.correct (RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract Arm.abi 8).pub s₁ s₂) :
    bytesAt s₁.mem (State.addr (s₁.gpr .r0)) 34 = bytesAt s₂.mem (State.addr (s₂.gpr .r0)) 34 := by
  sig_pub [Proof.MlDsa.rejNTTContract, Proof.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨_, hb, _⟩ := h
  exact VG.Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.sampleInBall s tr s') :
    s'.gpr .r0 = if (ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Ball.correct (Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract Arm.abi 8).pub s₁ s₂) :
    s₁.gpr .r2 = s₂.gpr .r2 ∧ bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat =
      bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat := by
  sig_pub [Proof.MlDsa.sampleInBallContract, Proof.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨_, hb, _, _, h2, _⟩ := h
  exact ⟨h2, (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : PrimsOk prims signStack where
  ntt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.Ntt.verified, by decide +kernel⟩
  invNtt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.NttInv.verified, by decide +kernel⟩
  mul := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mul_verified, by decide +kernel⟩
  mulAdd := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mulAdd_verified, by decide +kernel⟩
  add := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.add_verified, by decide +kernel⟩
  sub := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.sub_verified, by decide +kernel⟩
  rejNTT := ⟨8, by decide, Proof.MlDsa.Arm.Sample.rejNTT_verified, by decide +kernel⟩
  expandMask := ⟨8, by decide, Proof.MlDsa.Arm.Sample.expandMask_verified, by decide +kernel⟩
  ball := ⟨8, by decide, Proof.MlDsa.Arm.Sample.sampleInBall_verified, by decide +kernel⟩
  highBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.high_verified, by decide +kernel⟩
  lowBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.low_verified, by decide +kernel⟩
  normLt := ⟨4, by decide, Proof.MlDsa.Arm.Round.NormLt.verified, by decide +kernel⟩
  makeHint := ⟨12, by decide, Proof.MlDsa.Arm.Round.MakeHint.verified, by decide +kernel⟩
  simpleBitPack := ⟨0, by decide, Proof.MlDsa.Arm.Pack.simpleBitPack_verified, by decide +kernel⟩
  bitPack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitPack_verified, by decide +kernel⟩
  bitUnpack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitUnpack_verified, by decide +kernel⟩
  hintBitPack := ⟨8, by decide, Proof.MlDsa.Arm.Pack.Hint.hintBitPack_verified, by decide +kernel⟩
  rejRet := by exact (fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩)
  rejMax := fun s t s' h e h1 => by
    rw [rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  ballRet := by exact (fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩)
  ballMax := fun s t s' h e h1 => by
    rw [sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide)
        (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  hD := by decide
  hD' := by decide

end VG.Proof.MlDsa.Arm.Sign
