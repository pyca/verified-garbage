module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Fn
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sizes
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.DeriveCall
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Sampler
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
meta import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Check
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.DeriveCall
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Sampler
public import VerifiedGarbage.Spec.Dsa.Derive

/-!
# DSA key generation on PPC64LE: constant time

`generate_ct`: two runs from states that satisfy `gkContract` and agree on
its public data (the arguments, the domain, and the result's status,
octets consumed and trace) leak the same trace. The runs are followed
together (`SameTrace`), as the correctness proof follows each: the pieces
the taint analysis checks from the registers both runs agree on
(`st_taint`), the calls of `vg_dsa_check_parameters` and
`vg_dsa_derive_key`, whose runs are constant time (`checkParameters_ct`,
`deriveKey_ct`) for the domain and the derivation's success, which the
trace declassifies, and the branches on public data: the domain's
validity, q, the sampling decisions (`sample_st`) and the derivation's
success (`split_marker`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa.Random (sampleStatus)

/-! ## The public data -/

theorem pre_kl {s₀ : State} (h : gkContract.pre s₀) : (glOf s₀).kl = (s₀.gpr .r7).toNat := by
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
  obtain ⟨hsp, h3, -, h5, h6, h7, h8, h9, h10, a0, a1, a2, hl⟩ := hp
  have eL : glOf s₁ = glOf s₂ := by
    simp only [glOf, hsp, h3, h5, h6, h8, h9, h10, a0, a1, a2]
  have hlen : ((Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat).map (·.toNat) ++
      [(gkRes s₁).status, (gkRes s₁).used]).length =
      ((Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat).map (·.toNat) ++
      [(gkRes s₂).status, (gkRes s₂).used]).length := by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h7, List.length_cons,
      List.length_nil]
  obtain ⟨e1, e2⟩ := List.append_inj hl hlen
  obtain ⟨e3, e4⟩ := List.append_inj' e1 rfl
  have est := (List.cons.inj e4).1
  rw [gkRes_eq h₁, gkRes_eq h₂] at est e2
  refine ⟨eL, ?_, est, e2⟩
  show Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (glOf s₁).kl = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (glOf s₂).kl
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
    t₁.sp = t₂.sp ∧ EqRegs t₁ t₂ [.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r30] :=
  ⟨by rw [c₁.sp, c₂.sp, eL], by rw [c₁.r18, c₂.r18, eL], by rw [c₁.r19, c₂.r19, eL], by rw [c₁.r20, c₂.r20, eL],
    by rw [c₁.r21, c₂.r21, eL], by rw [c₁.r22, c₂.r22, eL], by rw [c₁.r23, c₂.r23, eL], by rw [c₁.r24, c₂.r24, eL],
    by rw [c₁.r26, c₂.r26, eL], EqRegs.single (by rw [c₁.r30, c₂.r30, eL])⟩

/-! ## The calls -/

theorem tn64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem check_st {s₁ s₂ w₁ w₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂) (eL : glOf s₁ = glOf s₂)
    (ep : parOf s₁ = parOf s₂) (A₁ : CArgs (glOf s₁) s₁ w₁) (A₂ : CArgs (glOf s₂) s₂ w₂) :
    SameTrace isa (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := pcContract) checkParameters_correct checkParameters_ct
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
  · show w₁.callEntry.gpr .r3 = w₂.callEntry.gpr .r3
    rw [g₁ .r3 (by decide), g₂ .r3 (by decide), A₁.r3, A₂.r3, eL]
  · show w₁.callEntry.gpr .r4 = w₂.callEntry.gpr .r4
    rw [g₁ .r4 (by decide), g₂ .r4 (by decide), A₁.r4, A₂.r4, eL]
  · show w₁.callEntry.gpr .r5 = w₂.callEntry.gpr .r5
    rw [g₁ .r5 (by decide), g₂ .r5 (by decide), A₁.r5, A₂.r5, eL]
  · show w₁.callEntry.gpr .r6 = w₂.callEntry.gpr .r6
    rw [g₁ .r6 (by decide), g₂ .r6 (by decide), A₁.r6, A₂.r6, eL]
  · show w₁.callEntry.gpr .r7 = w₂.callEntry.gpr .r7
    rw [g₁ .r7 (by decide), g₂ .r7 (by decide), A₁.r7, A₂.r7, eL]
  · show w₁.callEntry.gpr .r8 = w₂.callEntry.gpr .r8
    rw [g₁ .r8 (by decide), g₂ .r8 (by decide), A₁.r8, A₂.r8, eL]
  · show (Spec.Rsa.bytesAt w₁.mem (w₁.callEntry.gpr .r3) (w₁.callEntry.gpr .r4).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt w₂.mem (w₂.callEntry.gpr .r3) (w₂.callEntry.gpr .r4).toNat).map (·.toNat)
    rw [g₁ .r3 (by decide), g₂ .r3 (by decide), g₁ .r4 (by decide), g₂ .r4 (by decide), A₁.r3, A₂.r3, A₁.r4,
      A₂.r4, b₁, b₂, ep]

/-- The state `vg_dsa_derive_key` is entered in, after `deriveArgs`. -/
theorem dnarrow {s₀ w : State} (A : DArgs (glOf s₀) s₀ w) (rd wr : List Region) :
    (w.callEntry.withRegions rd wr).sp = (glOf s₀).F ∧
      (w.callEntry.withRegions rd wr).gpr .r3 = (glOf s₀).out ∧
      (w.callEntry.withRegions rd wr).gpr .r4 = BitVec.ofNat 64 (glOf s₀).ol ∧
      (w.callEntry.withRegions rd wr).gpr .r5 = (glOf s₀).par ∧
      (w.callEntry.withRegions rd wr).gpr .r6 = BitVec.ofNat 64 (glOf s₀).kl ∧
      (w.callEntry.withRegions rd wr).gpr .r7 = BitVec.ofNat 64 (glOf s₀).pl ∧
      (w.callEntry.withRegions rd wr).gpr .r8 = off (glOf s₀).F oNonce ∧
      (w.callEntry.withRegions rd wr).gpr .r9 = BitVec.ofNat 64 (glOf s₀).ql ∧
      (w.callEntry.withRegions rd wr).gpr .r10 = (glOf s₀).scr ∧
      stackArg (w.callEntry.withRegions rd wr) 0 = BitVec.ofNat 64 (glOf s₀).sl := by
  have hc := A.ctx
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr w (r := r) hr
  refine ⟨hc.sp, (g .r3 (by decide)).trans A.r3, (g .r4 (by decide)).trans A.r4, (g .r5 (by decide)).trans A.r5,
    (g .r6 (by decide)).trans A.r6, (g .r7 (by decide)).trans A.r7, (g .r8 (by decide)).trans A.r8,
    (g .r9 (by decide)).trans A.r9, (g .r10 (by decide)).trans A.r10, ?_⟩
  rw [dentry_stackArg, hc.sp]; exact hc.a0

theorem dcall_st {s₁ s₂ w₁ w₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂) (eL : glOf s₁ = glOf s₂)
    (ep : parOf s₁ = parOf s₂) (A₁ : DArgs (glOf s₁) s₁ w₁) (A₂ : DArgs (glOf s₂) s₂ w₂)
    (hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem)) :
    SameTrace isa (.call "vg_dsa_derive_key" Impl.Dsa.PPC64LE.Derive.derive) w₁ w₂ := by
  refine SameTrace.of_relCT (RelCT.callEx (k := dContract) deriveKey_correct deriveKey_ct
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

/-! ## The scan of q -/

/-- The first instructions of the scan: q's address and length. -/
theorem qargs_ok {s₀ t : State} (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block [.add .r12 .r19 .r20, .addi .r6 .r21 0]) t fun t₁ =>
      (t₁.gpr .r12 = off (glOf s₀).par (glOf s₀).pl ∧ t₁.gpr .r6 = BitVec.ofNat 64 (glOf s₀).ql ∧
        t₁.mem = t.mem) ∧ Keep [.r6, .r12] t t₁ :=
  WP.keep [.r6, .r12] (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide)

/-- q's octets, and the one after, are readable. -/
theorem q_in {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    ∀ i ≤ (glOf s₀).ql, InRegions (t.rd ++ t.wr) (off (off (glOf s₀).par (glOf s₀).pl) i) 1 := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
  obtain ⟨hrd, -⟩ := regions_eq h
  intro i hi
  rw [hc.rd, off_off]
  exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
    VG.Offset.contains_base _ (by omega) (by omega)⟩

theorem prepareQ_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (eq : qbOf (glOf s₁) s₁.mem = qbOf (glOf s₁) s₂.mem)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) : SameTrace isa prepareQ t₁ t₂ := by
  have hsp := (ctx_eq eL c₁ c₂).1
  have hr := (ctx_eq eL c₁ c₂).2
  have hq₁ := (glOf_ok h₁).ql
  have hq₂ := (glOf_ok h₂).ql
  unfold prepareQ prepare
  refine SameTrace.seq (st_taint [.r19, .r20, .r21] hsp (RS.EqRegs.sub hr) (by taint_decide)) (qargs_ok c₁)
    (qargs_ok c₂) fun u₁ u₂ ⟨⟨a12, a6, m1⟩, k1⟩ ⟨⟨b12, b6, m2⟩, k2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [k1.sp, k2.sp, hsp]
  have e12 : u₁.gpr .r12 = u₂.gpr .r12 := by rw [a12, b12, eL]
  have e6 : u₁.gpr .r6 = u₂.gpr .r6 := by rw [a6, b6, eL]
  refine SameTrace.seq (st_taint [.r12, .r6] usp ⟨e12, e6⟩ (by taint_decide))
    (sigLen_ok a12 a6 (by omega) (by omega) fun i hi => by rw [k1.rd, k1.wr]; exact q_in h₁ c₁ i (by omega))
    (sigLen_ok b12 b6 (by omega) (by omega) fun i hi => by rw [k2.rd, k2.wr]; exact q_in h₂ c₂ i (by omega))
    fun v₁ v₂ ⟨⟨x16, n1⟩, kv1⟩ ⟨⟨y16, n2⟩, kv2⟩ => ?_
  rw [m1, c₁.qb (glOf_ok h₁)] at x16
  rw [m2, c₂.qb (glOf_ok h₂), ← eL, ← eq] at y16
  exact st_taint [.r12, .r6, .r16] (by rw [kv1.sp, kv2.sp, usp])
    ⟨by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e12], by rw [kv1.gpr _ (by decide), kv2.gpr _ (by decide), e6],
      EqRegs.single (by rw [x16, y16])⟩ (by taint_decide)

/-! ## The derivation -/

theorem deriveFinish_st {v₁ v₂ : State} (hsp : v₁.sp = v₂.sp)
    (h3 : ((v₁.gpr .r3).setWidth 32 == 0) = ((v₂.gpr .r3).setWidth 32 == 0)) :
    SameTrace isa deriveFinish v₁ v₂ := by
  unfold deriveFinish
  exact SameTrace.ite (by rw [RS.eval_zero_w, RS.eval_zero_w, h3])
    (fun _ => by exact st_taint [] hsp trivial (by taint_decide))
    (fun _ => by exact st_taint [] hsp trivial (by taint_decide))

/-- The derivation's success, by its marker. -/
theorem isSome_eq {s₁ s₂ : State} {x₁ x₂ : Nat} (hx₁ : (drawOf s₁).scalar = some x₁)
    (hx₂ : (drawOf s₂).scalar = some x₂) (emk : mkOf s₁ = mkOf s₂) :
    (dkOf s₁ x₁).isSome = (dkOf s₂ x₂).isSome := by
  simp only [mkOf, hx₁, hx₂, List.cons.injEq, and_true] at emk
  cases a : (dkOf s₁ x₁).isSome <;> cases b : (dkOf s₂ x₂).isSome <;> simp_all

theorem derive_st {s₁ s₂ t₁ t₂ : State} (h₁ : gkContract.pre s₁) (h₂ : gkContract.pre s₂)
    (eL : glOf s₁ = glOf s₂) (ep : parOf s₁ = parOf s₂) (hq₁ : 1 < qOf s₁) (hq₂ : 1 < qOf s₂)
    (c₁ : Ctx (glOf s₁) s₁ t₁) (c₂ : Ctx (glOf s₂) s₂ t₂) (z₁ : NZero s₁ t₁.mem) (z₂ : NZero s₂ t₂.mem)
    (a31 : t₁.gpr .r31 = BitVec.ofNat 64 (sampleStatus (drawOf s₁)))
    (b31 : t₂.gpr .r31 = BitVec.ofNat 64 (sampleStatus (drawOf s₂)))
    (k₁ : ∀ x, (drawOf s₁).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₁) t₁.mem) = x)
    (k₂ : ∀ x, (drawOf s₂).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₂) t₂.mem) = x)
    (est : sampleStatus (drawOf s₁) = sampleStatus (drawOf s₂)) (emk : mkOf s₁ = mkOf s₂) :
    SameTrace isa Impl.Dsa.PPC64LE.Generate.derive t₁ t₂ := by
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hq₁
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have tsp : t₁.sp = t₂.sp := (ctx_eq eL c₁ c₂).1
  have hs₁ := sampleStatus_le (drawOf s₁)
  have hs₂ := sampleStatus_le (drawOf s₂)
  have W : ∀ {y : State}, WP isa (.block [.subi .r3 .r31 1]) y fun z =>
      (z.mem = y.mem ∧ z.gpr .r3 = y.gpr .r31 - BitVec.ofNat 64 1) ∧ Keep [.r3] y z :=
    fun {_} => WP.keep [.r3] (by prun) (by decide)
  unfold Impl.Dsa.PPC64LE.Generate.derive
  refine SameTrace.seq (st_taint [] tsp trivial (by taint_decide)) W W fun u₁ u₂ ⟨⟨m1, a3⟩, k1⟩ ⟨⟨m2, b3⟩, k2⟩ => ?_
  have usp : u₁.sp = u₂.sp := by rw [k1.sp, k2.sp, tsp]
  have ev₁ : isa.eval (.zero .d .r3) u₁ = some (decide (sampleStatus (drawOf s₁) = 1)) := by
    rw [VG.PPC64LE.eval_zero, a3, a31, RS.sub1_beq _ (by omega)]
  have ev₂ : isa.eval (.zero .d .r3) u₂ = some (decide (sampleStatus (drawOf s₂) = 1)) := by
    rw [VG.PPC64LE.eval_zero, b3, b31, RS.sub1_beq _ (by omega)]
  refine SameTrace.ite (by rw [ev₁, ev₂, est]) (fun hc => ?_) (fun _ => by exact st_taint [] usp trivial (by taint_decide))
  rw [ev₁, Option.some.injEq, decide_eq_true_eq] at hc
  obtain ⟨x₁, hx₁⟩ := Option.isSome_iff_exists.mp (RS.sampleStatus_some.mp hc)
  obtain ⟨x₂, hx₂⟩ := Option.isSome_iff_exists.mp (RS.sampleStatus_some.mp (est ▸ hc))
  have cz₁ : Ctx (glOf s₁) s₁ u₁ :=
    c₁.step hL₁ k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr)) (by rw [m1]; exact Frame.refl _ _)
  have cz₂ : Ctx (glOf s₂) s₂ u₂ :=
    c₂.step hL₂ k2.sp k2.rd k2.wr (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _)
  have nn₁ : Spec.Rsa.bytesAt u₁.mem (off (glOf s₁).F oNonce) (glOf s₁).ql = Spec.Dsa.encodeBE (glOf s₁).ql x₁ := by
    rw [m1]; exact RS.nonce_eq (W := (eOf s₁).W) hE₁.Wq z₁ (k₁ x₁ hx₁)
  have nn₂ : Spec.Rsa.bytesAt u₂.mem (off (glOf s₂).F oNonce) (glOf s₂).ql = Spec.Dsa.encodeBE (glOf s₂).ql x₂ := by
    rw [m2]; exact RS.nonce_eq (W := (eOf s₂).W) hE₂.Wq z₂ (k₂ x₂ hx₂)
  have hr := (ctx_eq eL cz₁ cz₂).2
  refine SameTrace.seq (st_taint [.r18, .r19, .r20, .r21, .r22] usp (RS.EqRegs.sub hr) (by taint_decide))
    (deriveArgs_ok hL₁ cz₁) (deriveArgs_ok hL₂ cz₂) fun w₁ w₂ ⟨A₁, mw₁, _⟩ ⟨A₂, mw₂, _⟩ => ?_
  have es₁ : dresOf (glOf s₁) w₁.mem = dkOf s₁ x₁ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₁, cz₁.par, nn₁]
  have es₂ : dresOf (glOf s₂) w₂.mem = dkOf s₂ x₂ := by
    simp only [dresOf, dkOf, parOf]; rw [mw₂, cz₂.par, nn₂]
  have hs : Spec.Dsa.signStatus (dresOf (glOf s₁) w₁.mem) = Spec.Dsa.signStatus (dresOf (glOf s₂) w₂.mem) := by
    rw [es₁, es₂]; simp only [Spec.Dsa.signStatus, isSome_eq hx₁ hx₂ emk]
  refine SameTrace.seq (dcall_st h₁ h₂ eL ep A₁ A₂ hs) (derive_ok h₁ A₁) (derive_ok h₂ A₂) fun v₁ v₂ D₁ D₂ => ?_
  exact deriveFinish_st (by rw [D₁.ctx.sp, D₂.ctx.sp, eL])
    (by rw [RS.setWidth_beq_zero D₁.r3, RS.setWidth_beq_zero D₂.r3, hs])

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
  refine ⟨sc.ctx.step hL so.keep.sp so.keep.rd so.keep.wr (fun r hr => so.keep.gpr r (ctx_draw r hr))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega) so.out), fun j hj => ?_⟩
  have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega)
  have hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
    simp only [SE.o]; omega
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact nz j (by omega)

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
    fun u₁ u₂ ⟨sc₁, z₁, m₁, k₁⟩ ⟨sc₂, z₂, m₂, k₂⟩ => ?_
  have usp := (ctx_eq eL sc₁.ctx sc₂.ctx).1
  have z₂' : u₂.gpr .r0 = 0 ↔ ¬ 1 < qOf s₁ := by rw [← eQ]; exact z₂
  refine SameTrace.ite (by rw [VG.PPC64LE.eval_zero, VG.PPC64LE.eval_zero, RS.beq_of_iff z₁, RS.beq_of_iff z₂'])
    (fun _ => by exact st_taint [] usp trivial (by taint_decide)) (fun hc => ?_)
  rw [VG.PPC64LE.eval_zero, RS.beq_of_iff z₁, Option.some.injEq, decide_eq_false_iff_not, Decidable.not_not] at hc
  have hq₂ : 1 < qOf s₂ := eQ ▸ hc
  have hE₁ : (eOf s₁).Ok := seOf_ok hL₁ s₁.mem hc
  have hE₂ : (eOf s₂).Ok := seOf_ok hL₂ s₂.mem hq₂
  have hQ₁ := seOf_Q (L := glOf s₁) s₁.mem hc
  have hQ₂ := seOf_Q (L := glOf s₂) s₂.mem hq₂
  have env₁ := sc₁.env h₁ hc
  have env₂ := sc₂.env h₂ hq₂
  have env₂' : SEnv (eOf s₁) (randOf (glOf s₂) s₂.mem) u₂ := eE ▸ env₂
  have r₁ : u₁.gpr .r25 = BitVec.ofNat 64 0 := (k₁.gpr _ (by decide)).trans ck₁.r25
  have r₂ : u₂.gpr .r25 = BitVec.ofNat 64 0 := (k₂.gpr _ (by decide)).trans ck₂.r25
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
  exact derive_st h₁ h₂ eL ep hc hq₂ cy₁ cy₂ ny₁ ny₂ so₁.r31 so₂.r31 so₁.cand so₂.cand est emk

theorem generate_ct : ConstantTime isa gkContract.pre gkContract.pub Impl.Dsa.PPC64LE.Generate.code := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ hp => ?_
  obtain ⟨eL, ep, est, etr⟩ := pub_facts h₁ h₂ hp
  have hL₁ := glOf_ok h₁
  have hL₂ := glOf_ok h₂
  obtain ⟨hsp, e3, -, e5, e6, -, e8, e9, e10, -⟩ := hp
  unfold Impl.Dsa.PPC64LE.Generate.code
  refine RS.st_alloc hsp ?_
  unfold Impl.Dsa.PPC64LE.Generate.body
  refine SameTrace.seq (st_taint [.r3, .r5, .r6, .r8, .r9, .r10] (by simp only [allocated, hsp])
    ⟨e3, e5, e6, e8, e9, e10⟩ (by taint_decide)) (entry_ok h₁) (entry_ok h₂) fun t₁ t₂ E₁ E₂ => ?_
  have tsp := (ctx_eq eL E₁.ctx E₂.ctx).1
  have tr := (ctx_eq eL E₁.ctx E₂.ctx).2
  have hck : SameTrace isa (.seq (.block checkArgs)
      (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters)) t₁ t₂ :=
    SameTrace.seq (st_taint [.r19, .r20, .r21, .r22, .r26] tsp (RS.EqRegs.sub tr) (by taint_decide))
      (checkArgs_ok hL₁ E₁.ctx) (checkArgs_ok hL₂ E₂.ctx) fun _ _ ⟨A₁, _, _⟩ ⟨A₂, _, _⟩ => check_st h₁ h₂ eL ep A₁ A₂
  refine SameTrace.seq hck (checked_ok h₁ E₁) (checked_ok h₂ E₂) fun u₁ u₂ ck₁ ck₂ => ?_
  have usp := (ctx_eq eL ck₁.ctx ck₂.ctx).1
  have ur := (ctx_eq eL ck₁.ctx ck₂.ctx).2
  have ec := chk_eq eL ep
  refine SameTrace.seq_ite (by rw [RS.eval_zero_w, RS.eval_zero_w, RS.setWidth_beq_zero ck₁.r3,
      RS.setWidth_beq_zero ck₂.r3, ec])
    (fun _ => by exact st_taint [.r18, .r20, .r21, .r30] usp (RS.EqRegs.sub ur) (by taint_decide)) (fun hc => ?_)
  rw [RS.eval_zero_w, RS.setWidth_beq_zero ck₁.r3, Option.some.injEq, decide_eq_false_iff_not] at hc
  have c₁ : chkOf s₁ = true := by cases hc' : chkOf s₁ <;> simp_all
  have c₂ : chkOf s₂ = true := ec ▸ c₁
  refine SameTrace.seq (valid_st h₁ h₂ eL ep ck₁ ck₂ c₁ c₂ etr) (valid_ok h₁ ck₁ c₁) (valid_ok h₂ ck₂ c₂)
    fun v₁ v₂ V₁ V₂ => ?_
  have vr := (ctx_eq eL V₁.ctx V₂.ctx).2
  exact st_taint [.r18, .r20, .r21, .r30, .r31] (ctx_eq eL V₁.ctx V₂.ctx).1
    ⟨vr.mem _ (by decide), vr.mem _ (by decide), vr.mem _ (by decide), vr.mem _ (by decide),
      EqRegs.single (by rw [V₁.r31, V₂.r31, est])⟩ (by taint_decide)

end VG.Proof.Dsa.PPC64LE.GK
