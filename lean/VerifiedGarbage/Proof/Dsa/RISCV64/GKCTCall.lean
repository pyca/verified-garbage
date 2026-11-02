module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.GKCTSample
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCTB
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveCTB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: constant time, the public data and the calls

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/CT.lean`). `pub_facts`: the
contract's public data fix the call's data, the domain and the result's
status and trace. The calls of `vg_dsa_check_parameters` and
`vg_dsa_derive_key` leak the same trace in two runs (`check_st`,
`dcall_st`) by the callees' constant time (`CT.check_ct`, `CT.derive_ct`)
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
  simp only [GL.kl, glOf]; omega

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
    (total := (glOf s₁).kl) (by simp only [GL.kl]; omega)
  rw [e, VG.Proof.Dsa.bytesAt_slice s₂.mem (glOf s₁).par (by simp only [GL.kl]; omega)] at this
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
  · simp only [List.mem_singleton] at hx; subst hx; split <;> omega

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
    rw [tn64 (by simp only [GL.kl]; omega)]; exact A₁.ctx.par
  have b₂ : Spec.Rsa.bytesAt w₂.mem (glOf s₂).par (BitVec.ofNat 64 (glOf s₂).kl).toNat = parOf s₂ := by
    rw [tn64 (by simp only [GL.kl]; omega)]; exact A₂.ctx.par
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

/-- The state `vg_dsa_derive_key` is entered in, after `deriveArgs`. -/
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
    (hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem)) :
    SameTrace isa (.call "vg_dsa_derive_key" Impl.Dsa.RISCV64.Derive.derive) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := dContract) deriveKey_correct CT.derive_ct
    (P := fun a b => a = w₁ ∧ b = w₂) fun _ _ ⟨e₁, e₂⟩ => ?_) ⟨rfl, rfl⟩
  rw [e₁, e₂]
  obtain ⟨c₁, cw₁⟩ := derive_cov h₁ A₁.ctx
  obtain ⟨c₂, cw₂⟩ := derive_cov h₂ A₂.ctx
  refine ⟨_, _, _, _, derive_pre h₁ A₁, derive_pre h₂ A₂, ?_, c₁, cw₁, c₂, cw₂⟩
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
  rw [p5, p6, r5, r6, tn64 (by simp only [GL.kl]; omega), tn64 (by simp only [GL.kl]; omega), A₁.ctx.par,
    A₂.ctx.par]
  show (parOf s₁).map (·.toNat) ++ _ = (parOf s₂).map (·.toNat) ++ _
  rw [ep]

end VG.Proof.Dsa.RISCV64.GK
