module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCheckedCT
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCheckedCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCheck
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.RISCV64.GKImplies`, which only this module used -/

section

/-!
# `vg_dsa_generate_key` on RISC-V: the contract on the registers and the stack

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Contract.lean`).
`generate_implies`: `gkContract` implies the shared contract, with
`gkStack` bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Dsa.RISCV64.GK

theorem gkStackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] :=
  rfl

/-- A state meeting `gkContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the domain at `0x1000`, the tape at `0x6000`
and the working space at `0x10000`; the stack's arguments at `0x9000`. -/
def gkSatState : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 424 | .a2 => 0x5000 | .a3 => 0x1000 | .a4 => 276 | .a5 => 128 | .a6 => 20
    | .a7 => 0x6000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x900A then 0x01 else bif Nat.beq a.toNat 0x9011 then 0x24 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x6000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x5000, 8⟩, ⟨0x10000, 73728⟩]

theorem generate_implies : gkContract.Implies (Spec.Dsa.generateKeyContract RISCV64.abi gkStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .a7, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, true), (⟨stackArgAddr s 0, 24⟩, false)]) := by
          with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _⟩ := hx
        sig_reduce [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | skip
        all_goals done
      post := by sig_implies_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, RISCV64.abi, RISCV64.argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [gkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSatState }

end VG.Proof.Dsa.RISCV64

end

end

/-! ### `Dsa.RISCV64.GKCT`, which only this module used -/

section

/-! ### `Dsa.RISCV64.GKCTFin`, which only this module used -/

section

/-! ### `Dsa.RISCV64.GKCTCall`, which only this module used -/

section

/-!
# DSA key generation on RISC-V: constant time, the public data and the calls

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/CT.lean`). `pub_facts`: the
contract's public data fix the call's data, the domain and the result's
status and trace. The calls of `vg_dsa_check_parameters` and
`vg_dsa_derive_key_checked` leak the same trace in two runs (`check_st`,
`dcall_st`) by the callees' constant time (`CT.check_ct`, `CT.deriveChecked_ct`)
through `RelCT.callEx`: their public data at the call, which correctness
fixes, agree.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.Random (sampleStatus)

/-! ## The public data -/

theorem pre_kl {s₀ : State} (h : gkContract.pre s₀) : (glOf s₀).kl = (s₀.gpr .a4).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hkl, -⟩ := h
  simp only [GL.kl, glOf]; omega_using [hkl]

/-- What the public data fix: the call's data, the domain, and the result's
status and trace. -/
theorem pub_facts {s₁ s₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂) (hp : gkContract.pub s₁ s₂) :
    glOf s₁ = glOf s₂ ∧ parOf s₁ = parOf s₂ ∧ (resOf s₁).status = (resOf s₂).status ∧
      (resOf s₁).trace = (resOf s₂).trace := by
  have k₁ := pre_kl h₁
  have k₂ := pre_kl h₂
  obtain ⟨hsp, e0, -, e2, e3, e4, e5, e6, e7, a0, a1, a2, hl⟩ := hp
  have eL : glOf s₁ = glOf s₂ := by
    simp only [glOf, hsp, e0, e2, e3, e5, e6, e7, a0, a1, a2]
  have hlen : ((Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat).map (·.toNat) ++
      [(gkRes s₁).status, (gkRes s₁).used]).length =
      ((Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat).map (·.toNat) ++
      [(gkRes s₂).status, (gkRes s₂).used]).length := by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, e4, List.length_cons,
      List.length_nil]
  obtain ⟨e1, e2⟩ := List.append_inj hl hlen
  obtain ⟨e3, e4⟩ := List.append_inj' e1 rfl
  have est := (List.cons.inj e4).1
  rw [gkRes_eq h₁, gkRes_eq h₂] at est e2
  refine ⟨eL, ?_, est, e2⟩
  show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (glOf s₁).kl = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (glOf s₂).kl
  rw [k₁, k₂]
  exact (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp e3

theorem chk_eq {s₁ s₂ : State} (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) : chkOf s₁ = chkOf s₂ := by
  show Spec.Dsa.checkParametersBytes (glOf s₁).pl (glOf s₁).ql (parOf s₁) =
    Spec.Dsa.checkParametersBytes (glOf s₂).pl (glOf s₂).ql (parOf s₂)
  rw [eL, ep]

/-- q's octets are within the domain. -/
theorem qb_eq {s₁ s₂ : State} (h₁ : gkContract.pre s₁) (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) :
    qbOf (glOf s₁) s₁.mem = qbOf (glOf s₁) s₂.mem := by
  have hL := glOf_ok h₁
  have hq := hL.ql
  have e : Spec.Rsa.bytesAt s₁.mem (glOf s₁).par (glOf s₁).kl = Spec.Rsa.bytesAt s₂.mem (glOf s₁).par (glOf s₁).kl := by
    have := ep
    simp only [parOf, ← eL] at this
    exact this
  have := VG.Proof.Dsa.bytesAt_slice s₁.mem (glOf s₁).par (offset := (glOf s₁).pl) (len := (glOf s₁).ql)
    (total := (glOf s₁).kl) (by simp only [GL.kl]; omega_using [])
  rw [e, VG.Proof.Dsa.bytesAt_slice s₂.mem (glOf s₁).par (by simp only [GL.kl]; omega_using [])] at this
  exact this.symm

/-- The sampler's data and q agree. -/
theorem same_q {s₁ s₂ : State} (eL : glOf s₁ = glOf s₂) (eq : qbOf (glOf s₁) s₁.mem = qbOf (glOf s₁) s₂.mem) :
    qOf s₂ = qOf s₁ ∧ eOf s₂ = eOf s₁ := by
  refine ⟨?_, ?_⟩
  · show Spec.Dsa.decodeBE (qbOf (glOf s₂) s₂.mem) = Spec.Dsa.decodeBE (qbOf (glOf s₁) s₁.mem)
    rw [← eL, ← eq]
  · show seOf (glOf s₂) (qbOf (glOf s₂) s₂.mem) = seOf (glOf s₁) (qbOf (glOf s₁) s₁.mem)
    rw [← eL, ← eq]

/-- A list of sampling decisions then markers, split. -/
theorem split_marker : ∀ {xs ys a b : List Nat}, (∀ x ∈ xs, x < 5) → (∀ y ∈ ys, y < 5) → (∀ x ∈ a, 5 ≤ x) →
    (∀ y ∈ b, 5 ≤ y) → xs ++ a = ys ++ b → xs = ys ∧ a = b
  | [], [], _, _, _, _, _, _, h => ⟨rfl, h⟩
  | [], y :: ys, a, _, _, hy, ha, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    have := ha y (by rw [h]; exact List.mem_cons_self ..)
    have := hy y (List.mem_cons_self ..)
    omega
  | x :: xs, [], _, b, hx, _, _, hb, h => by
    simp only [List.nil_append, List.cons_append] at h
    have := hb x (by rw [← h]; exact List.mem_cons_self ..)
    have := hx x (List.mem_cons_self ..)
    omega
  | x :: xs, y :: ys, a, b, hx, hy, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e, r⟩ := split_marker (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      (fun z hz => hy z (List.mem_cons_of_mem _ hz)) ha hb h.2
    exact ⟨by rw [h.1, e], r⟩

/-- The derivation's marker. -/
abbrev mkOf (s₀ : State) : List Nat :=
  match (drawOf s₀).scalar with
  | none => []
  | some x => [if (dkOf s₀ x).isSome then 5 else 6]

theorem resOf_trace {s₀ : State} (hchk : chkOf s₀ = true) : (resOf s₀).trace = (drawOf s₀).trace ++ mkOf s₀ := by
  simp only [resOf, hchk, ite_true, mkOf]
  split <;> rename_i hd <;> simp [hd]

theorem mkOf_ge (s₀ : State) : ∀ x ∈ mkOf s₀, 5 ≤ x := by
  intro x hx
  simp only [mkOf] at hx
  split at hx
  · simp at hx
  · simp only [List.mem_singleton] at hx; subst hx; split <;> omega_using []

/-- Equal traces: equal draws' traces, and the same success of the derivation. -/
theorem trace_split {s₁ s₂ : State} (c₁ : chkOf s₁ = true) (c₂ : chkOf s₂ = true)
    (ht : (resOf s₁).trace = (resOf s₂).trace) :
    (drawOf s₁).trace = (drawOf s₂).trace ∧ mkOf s₁ = mkOf s₂ := by
  rw [resOf_trace c₁, resOf_trace c₂] at ht
  exact split_marker (VG.Proof.Dsa.random_sample_trace_small _ _ _) (VG.Proof.Dsa.random_sample_trace_small _ _ _)
    (mkOf_ge s₁) (mkOf_ge s₂) ht

/-- Two states of the body with the same call's data agree on its registers. -/
theorem ctx_eq {s₁ s₂ t₁ t₂ : State} (eL : glOf s₁ = glOf s₂) (c₁ : Ctx (glOf s₁) s₁ t₁)
    (c₂ : Ctx (glOf s₂) s₂ t₂) :
    t₁.sp = t₂.sp ∧ EqRegs t₁ t₂ [.s1, .s2, .s3, .s4, .s6] :=
  ⟨by rw [c₁.sp, c₂.sp, eL], by rw [c₁.s1, c₂.s1, eL], by rw [c₁.s2, c₂.s2, eL], by rw [c₁.s3, c₂.s3, eL],
    by rw [c₁.s4, c₂.s4, eL], EqRegs.single (by rw [c₁.s6, c₂.s6, eL])⟩

/-! ## The calls -/

theorem tn64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem check_st {s₁ s₂ w₁ w₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂) (eL : glOf s₁ = glOf s₂)
    (ep : parOf s₁ = parOf s₂) (A₁ : CArgs (glOf s₁) s₁ w₁) (A₂ : CArgs (glOf s₂) s₂ w₂) :
    SameTrace isa (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := pcContract) checkParameters_correct CT.check_ct
    (P := fun a b => a = w₁ ∧ b = w₂) fun _ _ ⟨e₁, e₂⟩ => ?_) ⟨rfl, rfl⟩
  rw [e₁, e₂]
  obtain ⟨c₁, cw₁⟩ := check_cov h₁ A₁.ctx
  obtain ⟨c₂, cw₂⟩ := check_cov h₂ A₂.ctx
  refine ⟨_, _, _, _, check_pre h₁ A₁, check_pre h₂ A₂, ?_, c₁, cw₁, c₂, cw₂⟩
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have q₁ := hL₁.ql
  have q₂ := hL₂.ql
  have p₁ := hL₁.pl
  have p₂ := hL₂.pl
  have g₁ := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr w₁ (r := r) hr
  have g₂ := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr w₂ (r := r) hr
  have b₁ : Spec.Rsa.bytesAt w₁.mem (glOf s₁).par (BitVec.ofNat 64 (glOf s₁).kl).toNat = parOf s₁ := by
    rw [tn64 (by simp only [GL.kl]; omega_using [q₁, p₁])]; exact A₁.ctx.par
  have b₂ : Spec.Rsa.bytesAt w₂.mem (glOf s₂).par (BitVec.ofNat 64 (glOf s₂).kl).toNat = parOf s₂ := by
    rw [tn64 (by simp only [GL.kl]; omega_using [q₂, p₂])]; exact A₂.ctx.par
  refine ⟨(A₁.ctx.sp.trans (by rw [eL])).trans A₂.ctx.sp.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show w₁.callEntry.gpr .a0 = w₂.callEntry.gpr .a0
    rw [g₁ .a0 (by decide), g₂ .a0 (by decide), A₁.a0, A₂.a0, eL]
  · show w₁.callEntry.gpr .a1 = w₂.callEntry.gpr .a1
    rw [g₁ .a1 (by decide), g₂ .a1 (by decide), A₁.a1, A₂.a1, eL]
  · show w₁.callEntry.gpr .a2 = w₂.callEntry.gpr .a2
    rw [g₁ .a2 (by decide), g₂ .a2 (by decide), A₁.a2, A₂.a2, eL]
  · show w₁.callEntry.gpr .a3 = w₂.callEntry.gpr .a3
    rw [g₁ .a3 (by decide), g₂ .a3 (by decide), A₁.a3, A₂.a3, eL]
  · show w₁.callEntry.gpr .a4 = w₂.callEntry.gpr .a4
    rw [g₁ .a4 (by decide), g₂ .a4 (by decide), A₁.a4, A₂.a4, eL]
  · show w₁.callEntry.gpr .a5 = w₂.callEntry.gpr .a5
    rw [g₁ .a5 (by decide), g₂ .a5 (by decide), A₁.a5, A₂.a5, eL]
  · show (Spec.Rsa.bytesAt w₁.mem (w₁.callEntry.gpr .a0) (w₁.callEntry.gpr .a1).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt w₂.mem (w₂.callEntry.gpr .a0) (w₂.callEntry.gpr .a1).toNat).map (·.toNat)
    rw [g₁ .a0 (by decide), g₂ .a0 (by decide), g₁ .a1 (by decide), g₂ .a1 (by decide), A₁.a0, A₂.a0, A₁.a1,
      A₂.a1, b₁, b₂, ep]

/-- The state `vg_dsa_derive_key_checked` is entered in, after `deriveArgs`. -/
theorem dnarrow {s₀ w : State} (A : DArgs (glOf s₀) s₀ w) (rd wr : List Region) :
    (w.callEntry.withRegions rd wr).sp = (glOf s₀).F ∧
      (w.callEntry.withRegions rd wr).gpr .a0 = (glOf s₀).out ∧
      (w.callEntry.withRegions rd wr).gpr .a1 = BitVec.ofNat 64 (glOf s₀).ol ∧
      (w.callEntry.withRegions rd wr).gpr .a2 = (glOf s₀).par ∧
      (w.callEntry.withRegions rd wr).gpr .a3 = BitVec.ofNat 64 (glOf s₀).kl ∧
      (w.callEntry.withRegions rd wr).gpr .a4 = BitVec.ofNat 64 (glOf s₀).pl ∧
      (w.callEntry.withRegions rd wr).gpr .a5 = off (glOf s₀).F oNonce ∧
      (w.callEntry.withRegions rd wr).gpr .a6 = BitVec.ofNat 64 (glOf s₀).ql ∧
      (w.callEntry.withRegions rd wr).gpr .a7 = (glOf s₀).scr ∧
      stackArg (w.callEntry.withRegions rd wr) 0 = BitVec.ofNat 64 (glOf s₀).sl := by
  have hc := A.ctx
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr w (r := r) hr
  refine ⟨hc.sp, (g .a0 (by decide)).trans A.a0, (g .a1 (by decide)).trans A.a1, (g .a2 (by decide)).trans A.a2,
    (g .a3 (by decide)).trans A.a3, (g .a4 (by decide)).trans A.a4, (g .a5 (by decide)).trans A.a5,
    (g .a6 (by decide)).trans A.a6, (g .a7 (by decide)).trans A.a7, ?_⟩
  show w.mem.readW (w.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
  rw [hc.sp]; exact hc.a0

theorem dcall_st {s₁ s₂ w₁ w₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂) (eL : glOf s₁ = glOf s₂)
    (ep : parOf s₁ = parOf s₂) (A₁ : DArgs (glOf s₁) s₁ w₁) (A₂ : DArgs (glOf s₂) s₂ w₂)
    (hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem))
    (c₁ : chkOf s₁ = true) (c₂ : chkOf s₂ = true) :
    SameTrace isa (.call "vg_dsa_derive_key_checked" deriveChecked) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := dcContract) deriveChecked_correct CT.deriveChecked_ct
    (P := fun a b => a = w₁ ∧ b = w₂) fun _ _ ⟨e₁, e₂⟩ => ?_) ⟨rfl, rfl⟩
  rw [e₁, e₂]
  obtain ⟨cv₁, cw₁⟩ := derive_cov h₁ A₁.ctx
  obtain ⟨cv₂, cw₂⟩ := derive_cov h₂ A₂.ctx
  refine ⟨_, _, _, _, derivec_pre h₁ A₁ c₁, derivec_pre h₂ A₂ c₂, ?_, cv₁, cw₁, cv₂, cw₂⟩
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have q₁ := hL₁.ql
  have q₂ := hL₂.ql
  have p₁ := hL₁.pl
  have p₂ := hL₂.pl
  obtain ⟨p0, p3, p4, p5, p6, p7, p8, p9, p10, a0⟩ := dnarrow A₁ (derRd (glOf s₁)) (derWr (glOf s₁))
  obtain ⟨r0, r3, r4, r5, r6, r7, r8, r9, r10, b0⟩ := dnarrow A₂ (derRd (glOf s₂)) (derWr (glOf s₂))
  refine ⟨by rw [p0, r0, eL], by rw [p3, r3, eL], by rw [p4, r4, eL], by rw [p5, r5, eL], by rw [p6, r6, eL],
    by rw [p7, r7, eL], by rw [p8, r8, eL], by rw [p9, r9, eL], by rw [p10, r10, eL], by rw [a0, b0, eL], ?_⟩
  rw [dres_eq h₁ A₁, dres_eq h₂ A₂, hs]
  show (Spec.Rsa.bytesAt w₁.mem _ _).map (·.toNat) ++ _ = (Spec.Rsa.bytesAt w₂.mem _ _).map (·.toNat) ++ _
  rw [p5, p6, r5, r6, tn64 (by simp only [GL.kl]; omega_using [q₁, p₁]), tn64 (by simp only [GL.kl]; omega_using [q₂, p₂]), A₁.ctx.par,
    A₂.ctx.par]
  show (parOf s₁).map (·.toNat) ++ _ = (parOf s₂).map (·.toNat) ++ _
  rw [ep]

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: constant time of the exit

`finish_st`: the exit leaks the same trace in two runs with the same call's
data and status. The taint analysis sees memory secret, so the code that
loads the addresses it then writes through is cut after those loads:
`zeroOut`'s count loop runs from `out`'s address and length (`zblk_ok`),
and the store of the octets consumed from `used`'s address (`usedLd_ok`),
which correctness fixes.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (sub1_beq zeroLoopA_ok)

/-- `zeroOut`'s first block: `out`'s address and length, and 0. -/
theorem zblk_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block (([.addSp .t3 0, .load .d .t4 .t3 oOut] : List Instr) ++ outLen ++ ([.li .a0 0] : List Instr))) t fun t₂ =>
      ((t₂.gpr .a0 = 0 ∧ t₂.gpr .t4 = (glOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (glOf s₀).ol ∧
        t₂.mem = t.mem) ∧ Keep [.t3, .t4, .t5, .a0, .t2, .t1] t t₂) ∧ t₂.sp = t.sp := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨i64, l64⟩ := hc.word hL rfl (d := 64) (by decide) (by decide)
  have o64 := hc.out
  simp only [oOut] at o64
  have e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
  refine wp_sp (WP.keep [.t3, .t4, .t5, .a0, .t2, .t1] ?_ (by decide) (by rfl))
  brun [outLen, lenP, lenQ, hc.sp, hc.s2, e1, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut,
    i64, l64, o64, exec_li_zero, ← BitVec.ofNat_add]
  simp only [GL.ol]; congr 1; omega_using []

/-- `zeroOut`, keeping `Ctx`. -/
theorem zeroOut_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (zeroOut outLen) t fun t' => Ctx (glOf s₀) s₀ t' := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨-, hwr⟩ := regions_eq h
  unfold zeroOut
  refine WP.seq (WP.mono (zblk_ok h hc) fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
  have ho : ∀ i < (glOf s₀).ol, InRegions t₂.wr (off (glOf s₀).out i) 1 := fun i hi =>
    ⟨(glOf s₀).outR, by rw [k2.2.2, hc.wr, hwr]; simp,
      VG.Offset.contains_base _ (by omega_using [hi]) (by have := hL.nwOut; simp only [GL.ol] at hi this ⊢; omega_using [hq, hp, hi])⟩
  refine WP.mono (wp_sp (zeroLoopA_ok (by simp only [GL.ol]; omega_using [hq]) (by simp only [GL.ol]; omega_using [hq, hp]) ho hL.nwOut
    b0 b4 b5)) fun t₃ ⟨⟨⟨_, o3⟩, k3⟩, sp3⟩ => ?_
  have k23 := k2.trans k3
  refine hc.step hL (sp3.trans sp2) k23.2.1 k23.2.2 (fun r hr => k23.1 r (by revert r hr; decide)) ?_
  rw [← m2]
  intro x hx
  refine o3 x ?_
  by_contra hc'
  exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])

theorem zeroOut_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) :
    SameTrace isa (zeroOut outLen) t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  unfold zeroOut
  refine SameTrace.seq (st_taint [.s2] hsp (hr.sub) (by taint_decide)) (zblk_ok h₁ c₁) (zblk_ok h₂ c₂)
    fun u₁ u₂ ⟨⟨⟨_, a4, a5, _⟩, _⟩, sp1⟩ ⟨⟨⟨_, b4, b5, _⟩, _⟩, sp2⟩ => ?_
  exact st_taint [.t4, .t5] (by rw [sp1, sp2, hsp]) ⟨by rw [a4, b4, eL], EqRegs.single (by rw [a5, b5, eL])⟩
    (by taint_decide)

/-- The nonce zeroed and `used`'s address loaded. -/
theorem usedLd_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block (clearNonce ++ ([.load .d .t4 .t0 oUsed] : List Instr))) t fun u =>
      u.gpr .t4 = (glOf s₀).used ∧ u.sp = t.sp := by
  have hL := glOf_ok h
  have hF := hL.fnw
  rw [WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t hF hc.sp (scr_nonce hL rfl hc.wr))) fun x ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  have hc₃ : Ctx (glOf s₀) s₀ x := hc.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep [.t4] (Q := fun u => u.gpr .t4 = (glOf s₀).used)
    (by brun [t0, oUsed, i72, l72, o72]) (by decide) (by rfl))) fun u ⟨⟨a4, _⟩, spu⟩ => ⟨a4, spu.trans sp3⟩

/-- The exit, from the same call's data and status. -/
theorem finish_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) {st : Nat}
    (a10 : t₁.gpr .s10 = BitVec.ofNat 64 st) (b10 : t₂.gpr .s10 = BitVec.ofNat 64 st) :
    SameTrace isa (finish outLen) t₁ t₂ := by
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hsp := (ctx_eq eL c₁ c₂).1
  have W : ∀ {y : State}, WP isa (.block [.addi .a0 .s10 (-1)]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = y.gpr .s10 - BitVec.ofNat 64 1) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  unfold finish
  refine SameTrace.seq (st_taint [] hsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b0⟩, k2⟩, sp2⟩ => ?_
  have cu₁ : Ctx (glOf s₁) s₁ u₁ := c₁.step hL₁ sp1 k1.2.1 k1.2.2 (fun r hr => k1.1 r (by revert r hr; decide))
    (by rw [m1]; exact Frame.refl _ _)
  have cu₂ : Ctx (glOf s₂) s₂ u₂ := c₂.step hL₂ sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide))
    (by rw [m2]; exact Frame.refl _ _)
  have I : ∀ {s₀ u : State}, gkContract.pre s₀ → Ctx (glOf s₀) s₀ u →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut outLen)) u fun v => Ctx (glOf s₀) s₀ v := by
    intro s₀ u h hc
    refine WP.ite _ (Steps.eval_zero u .a0) (fun _ => WP.block_nil hc) (fun _ => zeroOut_ok h hc)
  refine SameTrace.seq ?_ (I h₁ cu₁) (I h₂ cu₂) fun v₁ v₂ cv₁ cv₂ => ?_
  · refine SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, a0, b0, a10, b10])
      (fun _ => SameTrace.block_nil) (fun _ => zeroOut_st h₁ h₂ eL cu₁ cu₂)
  have vsp := (ctx_eq eL cv₁ cv₂).1
  rw [show clearNonce ++ [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0] ++ restoreRegs =
    (clearNonce ++ [.load .d .t4 .t0 oUsed]) ++ ([.store .d .s5 .t4 0, .addi .a0 .s10 0] ++ restoreRegs) by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine SameTrace.block_append (SameTrace.seq (st_taint [] vsp trivial (by taint_decide)) (usedLd_ok h₁ cv₁)
    (usedLd_ok h₂ cv₂) fun x₁ x₂ ⟨a4, xs1⟩ ⟨b4, xs2⟩ => ?_)
  exact st_taint [.t4] (by rw [xs1, xs2, vsp]) (EqRegs.single (by rw [a4, b4, eL])) (by taint_decide)

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: constant time

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/CT.lean`). `generate_ct`: two
runs from states that satisfy `gkContract` and agree on its public data
(the arguments, the domain, and the result's status, octets consumed and
trace) leak the same trace. The runs are followed together
(`SameTrace`), as the correctness proof follows each: the pieces the taint
analysis checks from the registers both runs agree on (`st_taint`), cut
after the loads whose results the code uses as addresses (the scan's
length, `out` and `used`, `GKCTFin.lean`), the calls (`check_st`,
`dcall_st`), and the branches on public data: the domain's validity, q,
the sampling decisions (`sample_st`) and the derivation's success
(`split_marker`), with the callees' `u32` results zero-extended.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.Random (sampleStatus)
open VG.Proof.Dsa.RISCV64.RS (sub1_beq sampleStatus_some nonce_eq zx_beq_zero)

/-! ## The scan of q -/

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block (lenP .t3 ++ ([.add .s7 .s1 .t3] : List Instr) ++ lenQ .s8)) t fun t₁ =>
      ((t₁.gpr .s7 = off (glOf s₀).par (glOf s₀).pl ∧ t₁.gpr .s8 = BitVec.ofNat 64 (glOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.t3, .s7, .s8] t t₁) ∧ t₁.sp = t.sp := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
  exact wp_sp (WP.keep [.t3, .s7, .s8] (by brun [lenP, lenQ, hc.s1, hc.s2, e1, e2]) (by decide) (by rfl))

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    ∀ i ≤ (glOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (glOf s₀).par (glOf s₀).pl) i) 1 := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hk := hL.nwPar
  have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega_using [hp, ekl, hi]) (by omega_using [hq, hp, hi])⟩

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (eq : qbOf (glOf s₁) s₁.mem = qbOf (glOf s₁) s₂.mem)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (glOf_ok h₁).ql
  have hq₂ := (glOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.s1, .s2] hsp hr.sub (by taint_decide)) (qargs_ok h₁ c₁)
    (qargs_ok h₂ c₂) fun u₁ u₂ ⟨⟨⟨a7, a8, m1⟩, k1⟩, sp1⟩ ⟨⟨⟨b7, b8, m2⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  have e7 : u₁.gpr .s7 = u₂.gpr .s7 := by rw [a7, b7, eL]
  have e8 : u₁.gpr .s8 = u₂.gpr .s8 := by rw [a8, b8, eL]
  refine SameTrace.seq (st_taint [.s7, .s8] usp ⟨e7, e8⟩ (by taint_decide))
    (wp_sp (sigLen_ok a7 a8 (by omega_using [hq₁]) (by omega_using [hq₁]) fun i hi => by
      rw [k1.2.1, k1.2.2]; exact q_in h₁ c₁ i (by omega_using [hi])))
    (wp_sp (sigLen_ok b7 b8 (by omega_using [hq₂]) (by omega_using [hq₂]) fun i hi => by
      rw [k2.2.1, k2.2.2]; exact q_in h₂ c₂ i (by omega_using [hi])))
    fun v₁ v₂ ⟨⟨⟨x1, _⟩, kv1⟩, spv1⟩ ⟨⟨⟨y1, _⟩, kv2⟩, spv2⟩ => ?_
  rw [m1, c₁.qb (glOf_ok h₁)] at x1
  rw [m2, c₂.qb (glOf_ok h₂), ← eL, ← eq] at y1
  exact st_taint [.s7, .s8, .a1] (by rw [spv1, spv2, usp])
    ⟨by rw [kv1.gpr (by decide), kv2.gpr (by decide), e7], by rw [kv1.gpr (by decide), kv2.gpr (by decide), e8],
      EqRegs.single (by rw [x1, y1])⟩ (by taint_decide)

/-! ## The derivation -/

theorem deriveFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp) {st₁ st₂ : Nat}
    (h₁ : ((v₁.gpr .a0).setWidth 32).toNat = st₁) (h₂ : ((v₂.gpr .a0).setWidth 32).toNat = st₂)
    (hs : st₁ = st₂) : SameTrace isa deriveFinish v₁ v₂ := by
  have W : ∀ {y : State}, WP isa (.block zx) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = (y.gpr .a0 <<< 32) >>> 32) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun [zx]) (by decide) (by rfl))
  unfold deriveFinish
  refine SameTrace.seq (st_taint [] hsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨_, a0⟩, _⟩, sp1⟩ ⟨⟨⟨_, b0⟩, _⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, hsp]
  exact SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, a0, b0, zx_beq_zero h₁, zx_beq_zero h₂, hs])
    (fun _ => by exact st_taint [] usp trivial (by taint_decide))
    (fun _ => by exact st_taint [] usp trivial (by taint_decide))

/-- The derivation's success, by its marker. -/
theorem isSome_eq {s₁ s₂ : State} {x₁ x₂ : Nat} (hx₁ : (drawOf s₁).scalar = some x₁)
    (hx₂ : (drawOf s₂).scalar = some x₂) (emk : mkOf s₁ = mkOf s₂) :
    (dkOf s₁ x₁).isSome = (dkOf s₂ x₂).isSome := by
  simp only [mkOf, hx₁, hx₂, List.cons.injEq, and_true] at emk
  cases a : (dkOf s₁ x₁).isSome <;> cases b : (dkOf s₂ x₂).isSome <;> simp_all

theorem derive_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) (hq₁ : 1 < qOf s₁) (hq₂ : 1 < qOf s₂)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) (z₁ : NZero s₁ t₁.mem) (z₂ : NZero s₂ t₂.mem)
    (a10 : t₁.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₁)))
    (b10 : t₂.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₂)))
    (k₁ : ∀ x, (drawOf s₁).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₁) t₁.mem) = x)
    (k₂ : ∀ x, (drawOf s₂).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₂) t₂.mem) = x)
    (est : sampleStatus (drawOf s₁) = sampleStatus (drawOf s₂)) (emk : mkOf s₁ = mkOf s₂)
    (ch₁ : chkOf s₁ = true) (ch₂ : chkOf s₂ = true) :
    SameTrace isa Impl.Dsa.RISCV64.Generate.derive t₁ t₂ := by
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hq₁
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have tsp : t₁.sp = t₂.sp := (ctx_eq eL c₁ c₂).1
  have hs₁ := sampleStatus_le (drawOf s₁)
  have hs₂ := sampleStatus_le (drawOf s₂)
  have W : ∀ {y : State}, WP isa (.block [.addi .a0 .s10 (-1)]) y fun z =>
      ((z.mem = y.mem ∧ z.gpr .a0 = y.gpr .s10 - BitVec.ofNat 64 1) ∧ Keep [.a0] y z) ∧ z.sp = y.sp :=
    fun {_} => wp_sp (WP.keep [.a0] (by brun) (by decide) (by rfl))
  unfold Impl.Dsa.RISCV64.Generate.derive
  refine SameTrace.seq (st_taint [] tsp trivial (by taint_decide)) W W
    fun u₁ u₂ ⟨⟨⟨m1, a3⟩, k1⟩, sp1⟩ ⟨⟨⟨m2, b3⟩, k2⟩, sp2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [sp1, sp2, tsp]
  have ev₁ : isa.eval (.zero .a0) u₁ = some (decide (sampleStatus (drawOf s₁) = 1)) := by
    rw [Steps.eval_zero, a3, a10, sub1_beq _ (by omega_using [hs₁])]
  have ev₂ : isa.eval (.zero .a0) u₂ = some (decide (sampleStatus (drawOf s₂) = 1)) := by
    rw [Steps.eval_zero, b3, b10, sub1_beq _ (by omega_using [hs₂])]
  refine SameTrace.ite (by rw [ev₁, ev₂, est]) (fun hc => ?_) (fun _ => SameTrace.block_nil)
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨x₁, hx₁⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hc)
  obtain ⟨x₂, hx₂⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp (est ▸ hc))
  have cz₁ : Ctx (glOf s₁) s₁ u₁ :=
    c₁.step hL₁ sp1 k1.2.1 k1.2.2 (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  have cz₂ : Ctx (glOf s₂) s₂ u₂ :=
    c₂.step hL₂ sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide)) (by rw [m2]; exact Frame.refl _ _)
  have nn₁ : Spec.Rsa.bytesAt u₁.mem (off (glOf s₁).F oNonce) (glOf s₁).ql = Spec.Dsa.encodeBE (glOf s₁).ql x₁ := by
    rw [m1]; exact nonce_eq (W := (eOf s₁).W) hE₁.Wq z₁ (k₁ x₁ hx₁)
  have nn₂ : Spec.Rsa.bytesAt u₂.mem (off (glOf s₂).F oNonce) (glOf s₂).ql = Spec.Dsa.encodeBE (glOf s₂).ql x₂ := by
    rw [m2]; exact nonce_eq (W := (eOf s₂).W) hE₂.Wq z₂ (k₂ x₂ hx₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.s1, .s2, .s6] usp hr.sub (by taint_decide))
    (deriveArgs_ok hL₁ rfl cz₁) (deriveArgs_ok hL₂ rfl cz₂) fun w₁ w₂ ⟨⟨A₁, mw₁, _⟩, _⟩ ⟨⟨A₂, mw₂, _⟩, _⟩ => ?_
  have es₁ : dresOf (glOf s₁) w₁.mem = dkOf s₁ x₁ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₁, cz₁.par, nn₁]
  have es₂ : dresOf (glOf s₂) w₂.mem = dkOf s₂ x₂ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₂, cz₂.par, nn₂]
  have hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem) := by
    rw [es₁, es₂]; simp only [Spec.Dsa.signStatus, isSome_eq hx₁ hx₂ emk]
  refine SameTrace.seq (dcall_st h₁ h₂ eL ep A₁ A₂ hs ch₁ ch₂) (derive_ok h₁ A₁ ch₁) (derive_ok h₂ A₂ ch₂)
    fun v₁ v₂ D₁ D₂ => ?_
  exact deriveFinish_st (by rw [D₁.ctx.sp, D₂.ctx.sp, eL]) D₁.a0 D₂.a0 hs

/-! ## A valid domain, and the function -/

/-- After the draw: `Ctx`, and the nonce's leading zeros. -/
theorem after_sample {s₀ t₃ t₄ : State} {S : Spec.Dsa.Random.Sample} (h : gkContract.pre s₀) (hq : 1 < qOf s₀)
    (sc : Scanned (glOf s₀) s₀ t₃) (nz : ∀ j < 32, t₃.mem (off (glOf s₀).F (oNonce + j)) = 0)
    (so : SampleOut (eOf s₀) (randOf (glOf s₀) s₀.mem) 0 S t₃ t₄) :
    Ctx (glOf s₀) s₀ t₄ ∧ NZero s₀ t₄.mem := by
  have hL := glOf_ok h
  have hql := hL.ql
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
  have hql' : (eOf s₀).ql ≤ 32 := hE.ql
  have hF := hL.fnw
  refine ⟨sc.ctx.step hL (so.env.sp.trans sc.ctx.sp.symm) so.keep.2.1 so.keep.2.2
    (fun r hr => so.keep.1 r (by revert r hr; decide))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql']) so.out), fun j hj => ?_⟩
  have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql, hj])
  have hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
    simp only [SE.o]; omega_using [hj, e2]
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact nz j (by omega_using [hql, hj])

theorem valid_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) (ck₁ : Chk s₁ t₁) (ck₂ : Chk s₂ t₂)
    (c₁ : chkOf s₁ = true) (c₂ : chkOf s₂ = true) (ht : (resOf s₁).trace = (resOf s₂).trace) :
    SameTrace isa valid t₁ t₂ := by
  have eq := qb_eq h₁ eL ep
  obtain ⟨eQ, eE⟩ := same_q eL eq
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  unfold valid
  refine SameTrace.seq (prepareQ_st h₁ h₂ eL eq ck₁.ctx ck₂.ctx) (prepareQ_ok h₁ ck₁.ctx) (prepareQ_ok h₂ ck₂.ctx)
    fun u₁ u₂ ⟨⟨sc₁, z₁, m₁, k₁⟩, _⟩ ⟨⟨sc₂, z₂, m₂, k₂⟩, _⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have z₂' : u₂.gpr .a0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.ite (by rw [Steps.eval_zero, Steps.eval_zero, beq_of_iff z₁, beq_of_iff z₂'])
    (fun _ => by exact st_taint [] usp trivial (by taint_decide)) (fun hc => ?_)
  rw [Steps.eval_zero, beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
  have hq₂ : 1 < qOf s₂ := eQ ▸ hc
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hc
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have hQ₁ := seOf_Q (L := glOf s₁) s₁.mem hc
  have hQ₂ := seOf_Q (L := glOf s₂) s₂.mem hq₂
  have env₁ := sc₁.env h₁ hc
  have env₂ := sc₂.env h₂ hq₂
  have env₂' : SEnv (eOf s₁) (randOf (glOf s₂) s₂.mem) u₂ := eE ▸ env₂
  have r₁ : u₁.gpr .s5 = BitVec.ofNat 64 0 := (k₁.gpr (by decide)).trans ck₁.s5
  have r₂ : u₂.gpr .s5 = BitVec.ofNat 64 0 := (k₂.gpr (by decide)).trans ck₂.s5
  obtain ⟨tD, emk⟩ := trace_split c₁ c₂ ht
  have tS : (Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₁) s₁.mem)).trace =
      (Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₂) s₂.mem)).trace := by
    have e : drawOf s₂ = Spec.Dsa.Random.sample (qOf s₁) 128 (randOf (glOf s₂) s₂.mem) := by
      show Spec.Dsa.Random.sample (qOf s₂) _ _ = _
      rw [eQ]
    rw [← e]; exact tD
  have est : sampleStatus (drawOf s₁) = sampleStatus (drawOf s₂) := by
    have := (VG.Proof.Dsa.Random.sample_trace_agree tS).2.2
    show _ = sampleStatus (Spec.Dsa.Random.sample (qOf s₂) 128 _)
    rw [eQ]; exact this
  have tS' : (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf (glOf s₁) s₁.mem)) 128
      ((randOf (glOf s₁) s₁.mem).drop 0)).trace = (Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf (glOf s₁) s₁.mem))
      128 ((randOf (glOf s₂) s₂.mem).drop 0)).trace := by
    rw [List.drop_zero, List.drop_zero]; exact tS
  refine SameTrace.seq (sample_st hE₁ hQ₁ env₁ env₂' r₁ r₂ (Nat.zero_le _) tS')
    (sample_ok hE₁ hQ₁ env₁ r₁ (Nat.zero_le _)) (sample_ok hE₂ hQ₂ env₂ r₂ (Nat.zero_le _))
    fun y₁ y₂ so₁ so₂ => ?_
  rw [List.drop_zero] at so₁ so₂
  obtain ⟨cy₁, ny₁⟩ := after_sample h₁ hc sc₁ (fun j hj => by rw [m₁]; exact ck₁.nonce j hj) so₁
  obtain ⟨cy₂, ny₂⟩ := after_sample h₂ hq₂ sc₂ (fun j hj => by rw [m₂]; exact ck₂.nonce j hj) so₂
  exact derive_st h₁ h₂ eL ep hc hq₂ cy₁ cy₂ ny₁ ny₂ so₁.s10 so₂.s10 so₁.cand so₂.cand est emk c₁ c₂

theorem generate_ct : ConstantTime isa gkContract.pre gkContract.pub Impl.Dsa.RISCV64.Generate.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ep, est, etr⟩ := pub_facts h₁ h₂ hp
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hsp : s₁.sp = s₂.sp := hp.1
  unfold Impl.Dsa.RISCV64.Generate.code
  refine st_alloc ?_
  unfold Impl.Dsa.RISCV64.Generate.body
  refine SameTrace.seq (st_taint [] (by simp only [allocd, hsp]) trivial (by taint_decide))
    (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  have tsp := (ctx_eq eL E₁.ctx E₂.ctx).1
  have tr := (ctx_eq eL E₁.ctx E₂.ctx).2
  have hck : SameTrace isa (.seq (.block checkArgs)
      (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters)) t₁ t₂ :=
    SameTrace.seq (st_taint [.s1, .s2, .s6] tsp tr.sub (by taint_decide))
      (checkArgs_ok hL₁ rfl E₁.ctx) (checkArgs_ok hL₂ rfl E₂.ctx)
      fun _ _ ⟨⟨A₁, _, _⟩, _⟩ ⟨⟨A₂, _, _⟩, _⟩ => check_st h₁ h₂ eL ep A₁ A₂
  refine SameTrace.seq hck (checked_ok h₁ E₁) (checked_ok h₂ E₂) fun u₁ u₂ ck₁ ck₂ => ?_
  have usp := (ctx_eq eL ck₁.ctx ck₂.ctx).1
  have ec := chk_eq eL ep
  refine SameTrace.assoc_left (SameTrace.seq (st_taint [] usp trivial (by taint_decide)) (zx_ok hL₁ ck₁.ctx)
    (zx_ok hL₂ ck₂.ctx) fun x₁ x₂ ⟨cx₁, z1, mx1, g1⟩ ⟨cx₂, z2, mx2, g2⟩ => ?_)
  have xsp := (ctx_eq eL cx₁ cx₂).1
  have s5₁ : x₁.gpr .s5 = BitVec.ofNat 64 0 := (g1 _ (by decide)).trans ck₁.s5
  have s5₂ : x₂.gpr .s5 = BitVec.ofNat 64 0 := (g2 _ (by decide)).trans ck₂.s5
  refine SameTrace.seq_ite (by rw [Steps.eval_zero, Steps.eval_zero, z1, z2, zx_beq_zero ck₁.a0,
      zx_beq_zero ck₂.a0, ec]) (fun hc => ?_) (fun hc => ?_)
  · -- An invalid domain.
    refine SameTrace.seq (st_taint [] xsp trivial (by taint_decide)) (li0_ok hL₁ cx₁) (li0_ok hL₂ cx₂)
      fun y₁ y₂ ⟨cy₁, a10, _, _⟩ ⟨cy₂, b10, _, _⟩ => ?_
    exact finish_st h₁ h₂ eL cy₁ cy₂ a10 b10
  · -- A valid domain.
    rw [Steps.eval_zero, z1, zx_beq_zero ck₁.a0, Option.some.injEq, decide_eq_false_iff_not] at hc
    have c₁ : chkOf s₁ = true := by cases hc' : chkOf s₁ <;> simp_all
    have c₂ : chkOf s₂ = true := ec ▸ c₁
    have ck₁' : Chk s₁ x₁ := ⟨cx₁, s5₁, fun j hj => by rw [mx1]; exact ck₁.nonce j hj, by
      rw [z1, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck₁.a0⟩
    have ck₂' : Chk s₂ x₂ := ⟨cx₂, s5₂, fun j hj => by rw [mx2]; exact ck₂.nonce j hj, by
      rw [z2, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck₂.a0⟩
    refine SameTrace.seq (valid_st h₁ h₂ eL ep ck₁' ck₂' c₁ c₂ etr) (valid_ok h₁ ck₁' c₁) (valid_ok h₂ ck₂' c₂)
      fun v₁ v₂ V₁ V₂ => ?_
    exact finish_st h₁ h₂ eL V₁.ctx V₂.ctx V₁.s10 (V₂.s10.trans (by rw [est]))

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# `vg_dsa_generate_key` on RISC-V: verified against the shared contract

`gkContract` states the shared contract on the registers and the stack
(`generate_implies`, `GKImplies.lean`); with correctness
(`generate_correct`, `GKFn.lean`) and constant time (`generate_ct`,
`GKCT.lean`), `Generate.code` is verified with its 192 bytes of stack
(`generateKey_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_generate_key`. -/
theorem generateKey_verified :
    Verified RISCV64.target Generate.code (Spec.Dsa.generateKeyContract RISCV64.abi GK.gkStack) :=
  Verified.of_correct GK.generate_correct GK.generate_ct generate_implies

end VG.Proof.Dsa.RISCV64
