module

public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.MlDsa.Sample.Rej4
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Dot
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT

/-! ### `MlDsa.X86_64.Sample.Rej4Verified`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_rej_ntt_poly4_avx2`, verified

The contract of the proofs (`r4K`) implies the shared one of `Spec/`: a seed
with 256 coefficients in the 1008 bytes both implementations sample from has
them within those bounds (`rejNTT_some`), and one without has none within the
least bound (`rejNTT_none`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none)
open VG.Proof.MlDsa.X86_64.Sample (leakBytes_inj)
open VG.Spec.MlDsa (G)
open VG.Spec.Sha3 (bytesAt)

theorem seed4_eq : Proof.MlDsa.seed4 = Proof.MlKem.seed4 := rfl
theorem poly4_eq : Proof.MlDsa.poly4 = Proof.MlKem.poly4 := rfl

theorem r4_post {s s' : State} (h : r4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Proof.MlDsa.Reduced s'.mem (Proof.MlDsa.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ b : Spec.MlDsa.Bounds, Spec.MlDsa.rejNTTPoly b.rejNTT
          (Proof.MlDsa.seed4 s.mem (s.gpr .rdi) k) = some (Proof.MlDsa.polyAt s'.mem (Proof.MlDsa.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Proof.MlDsa.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  simp only [seed4_eq, poly4_eq]
  by_cases hall : ((List.range 4).all fun k =>
      (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, (rnFold [] (G (Proof.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1, .inl ⟨hr, fun k hk => ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    rw [rejNTT_some (hs k hk), (hp k hk (hs k hk)).2]
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall, beq_iff_eq] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

theorem r4_pre (s : State) (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) : r4K.pre s := by
  revert s h
  sig_implies_pre [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
    X86_64.argRegs]

export VG.Proof.MlDsa.Sample (rej4Res seed4_of136 rej4Res_congr rej4Res_max)

/-- The public data of two calls include their seeds. -/
theorem r4_pub {S : Nat} (s₁ s₂ : State) (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi S).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .rdi) 136 = bytesAt s₂.mem (s₂.gpr .rdi) 136 := by
  sig_pub [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact leakBytes_inj hb

/-- The result of code that meets `r4K`. -/
theorem rej4_ret {c : Prog isa}
    (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s') {s s' : State}
    {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s) (e : Exec isa c s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := by
  obtain ⟨_, _, e', _, hq⟩ := hc s (r4_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem rej4_verified (c : Prog isa) (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s')
    (ht : ConstantTime isa r4K.pre r4K.pub c) : Verified X86_64.target c (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := r4_pre
      post := by
        intro s s' _ h
        sig_post [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, X86_64.abi, X86_64.argRegs]
        exact r4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs]
        sig_simp [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact leakBytes_inj ‹_›
      sat := by
        sig_implies_sat [Proof.MlDsa.rejNTT4Contract, Proof.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [MlKem.X86_64.sample4Sat] using MlKem.X86_64.sample4Sat }

theorem rejNTT4_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    (Proof.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ correct_scalar ct_scalar

theorem rejNTT4_ret {s s' : State} {t : List Leak} (h : (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4 s t s') :
    (s'.gpr .rax).setWidth 32 = rej4Res s.mem (s.gpr .rdi) := rej4_ret correct_scalar h e

end VG.Proof.MlDsa.X86_64.Rej4

end

end

/-!
# ML-DSA on x86-64: what the callers of the polynomial arithmetic need of it

An `ArithImpl` is an implementation of the polynomial arithmetic
(`Impl.MlDsa.X86_64.Arith.Backend`) with what key generation, signing and
verification need of each of its functions (`FnOk`): it meets its contract
without using the stack, never writes `rsp`, calls no deeper than twice, and
loads MXCSR only to restore it. Each is a variant of the interface `MlDsaArith`
on x86-64 (`Variants/MlDsaArith/X86_64/`), and the functions that call it are
proven once for all of them (`Generic/MlDsaArith/X86_64/`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith

/-- What a caller needs of a function with the contract `k` (given the
stack its calls use) and the code `c`. -/
structure FnOk (k : Nat → Contract isa) (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (k 0)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 2
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- What a caller needs of `vg_mldsa_rej_ntt_poly4`, which calls three deep
and takes 24 bytes of stack. -/
structure Rej4Ok (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (Proof.MlDsa.rejNTT4Contract X86_64.abi 24)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true
  /-- Its result is whether each seed has 256 coefficients in its first 1008 bytes of output, as
  both implementations', which signing branches on. -/
  ret : ∀ s t s', (Proof.MlDsa.rejNTT4Contract X86_64.abi 24).pre s → Exec isa c s t s' →
    (s'.gpr .rax).setWidth 32 = Rej4.rej4Res s.mem (s.gpr .rdi)

/-- What a caller needs of `vg_mldsa_expand_mask_poly4`, which calls three
deep and takes 24 bytes of stack. -/
structure Mask4Ok (c : Prog isa) : Prop where
  ver : Verified X86_64.target c (Proof.MlDsa.expandMask4Contract X86_64.abi 24)
  nosp : NoSp c
  mx : c.allInstrs (fun i => !touchesMxcsr i) = true
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- Each function of the backend `B` meets its contract, and is safe to call. -/
structure BackendOk (B : Backend) : Prop where
  ntt : FnOk (fun S => Proof.MlDsa.nttContract X86_64.abi S) B.ntt
  invNtt : FnOk (fun S => Proof.MlDsa.Arith.Representation.inverseContract B.montgomery X86_64.abi S) B.invNtt
  mul : FnOk (fun S => Proof.MlDsa.Arith.Representation.productContract B.montgomery X86_64.abi S) B.mul
  mulAdd : FnOk (fun S => Proof.MlDsa.Arith.Representation.accumulateContract B.montgomery X86_64.abi S) B.mulAdd
  add : FnOk (fun S => Proof.MlDsa.addContract X86_64.abi S) B.add
  sub : FnOk (fun S => Proof.MlDsa.subContract X86_64.abi S) B.sub
  highBits : FnOk (fun S => Proof.MlDsa.highBitsContract X86_64.abi S) B.highBits
  lowBits : FnOk (fun S => Proof.MlDsa.lowBitsContract X86_64.abi S) B.lowBits
  normLt : FnOk (fun S => Proof.MlDsa.normLtContract X86_64.abi S) B.normLt
  makeHint : FnOk (fun S => Proof.MlDsa.makeHintContract X86_64.abi S) B.makeHint
  useHint : FnOk (fun S => Proof.MlDsa.useHintContract X86_64.abi S) B.useHint
  rej4 : Rej4Ok B.rej4
  expandMask4 : Mask4Ok B.expandMask4
  dotInv : ∀ c, c = 4 ∨ c = 5 ∨ c = 7 → FnOk (fun S => Proof.MlDsa.dotInverseContract c X86_64.abi S) (B.dotInv c)

/-- An implementation of the polynomial arithmetic on x86-64. -/
structure ArithImpl where
  code : Backend
  ok : BackendOk code
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

/-- `FnOk` of code verified without stack, from evaluating it. -/
theorem FnOk.of {k : Nat → Contract isa} {c : Prog isa} (h : Verified X86_64.target c (k 0))
    (hn : c.allInstrs (fun i => !Taint.clobbers i .rsp && !touchesMxcsr i) = true) (hd : c.depth ≤ 2)
    (hc : ctlOk c = true) (hs : c.allInstrs (fun i => !isa.writesSp i) = true) : FnOk k c :=
  ⟨h, (Proof.MlKem.X86_64.nospMx_of hn).1, (Proof.MlKem.X86_64.nospMx_of hn).2, hd, hc, Code.all_of_allInstrs hs⟩

/-- The tests of code that calls no deeper than `d`, for the kernel: one walk
of the code for the two tests of `rsp` and that of MXCSR, with one match for each instruction
(`Proof/Framework/X86_64/InstrBits.lean`). -/
noncomputable def fnOkB (d : Nat) (c : Prog isa) : Bool :=
  c.allInstrs (hasBits (bMx + bSp + bNs)) && Nat.ble c.depth d && ctlOk c

theorem fnOkB_spec {d : Nat} {c : Prog isa} (h : fnOkB d c = true) :
    NoSp c ∧ c.allInstrs (fun i => !touchesMxcsr i) = true ∧ c.depth ≤ d ∧ ctlOk c = true ∧
      c.all (fun i => !isa.writesSp i) = true := by
  simp only [fnOkB, Bool.and_eq_true, Nat.ble_eq] at h
  exact ⟨Proof.MlKem.X86_64.nosp_of (Code.noRsp_of_bits (m := bMx + bSp + bNs) rfl h.1.1),
    Code.noTouchMx_of_bits (m := bMx + bSp + bNs) rfl h.1.1, h.1.2, h.2,
    Code.spSafe_of_bits (m := bMx + bSp + bNs) rfl h.1.1⟩

/-- `FnOk` of code verified without stack, from `fnOkB`. -/
theorem FnOk.of_bits {k : Nat → Contract isa} {c : Prog isa} (h : Verified X86_64.target c (k 0))
    (hb : fnOkB 2 c = true) : FnOk k c :=
  have h' := fnOkB_spec hb
  ⟨h, h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2⟩

/-- The tests of the SSE2 code's functions, in one declaration: sixteen
functions, of four tests each. -/
theorem sse2_checks :
    fnOkB 2 Backend.sse2.ntt = true ∧ fnOkB 2 Backend.sse2.invNtt = true ∧ fnOkB 2 Backend.sse2.mul = true ∧
    fnOkB 2 Backend.sse2.mulAdd = true ∧ fnOkB 2 Backend.sse2.add = true ∧ fnOkB 2 Backend.sse2.sub = true ∧
    fnOkB 2 Backend.sse2.highBits = true ∧ fnOkB 2 Backend.sse2.lowBits = true ∧
    fnOkB 2 Backend.sse2.normLt = true ∧ fnOkB 2 Backend.sse2.makeHint = true ∧
    fnOkB 2 Backend.sse2.useHint = true ∧ fnOkB 3 Backend.sse2.rej4 = true ∧
    fnOkB 3 Backend.sse2.expandMask4 = true ∧ fnOkB 2 (Backend.sse2.dotInv 4) = true ∧
    fnOkB 2 (Backend.sse2.dotInv 5) = true ∧ fnOkB 2 (Backend.sse2.dotInv 7) = true := by
  decide +kernel

/-- The SSE2 code. -/
def ArithImpl.sse2 : ArithImpl where
  code := .sse2
  ok :=
    { ntt := FnOk.of_bits Arith.ntt_verified sse2_checks.1
      invNtt := FnOk.of_bits Arith.nttInv_verified sse2_checks.2.1
      mul := FnOk.of_bits Arith.mul_verified sse2_checks.2.2.1
      mulAdd := FnOk.of_bits Arith.mulAdd_verified sse2_checks.2.2.2.1
      add := FnOk.of_bits Arith.add_verified sse2_checks.2.2.2.2.1
      sub := FnOk.of_bits Arith.sub_verified sse2_checks.2.2.2.2.2.1
      highBits := FnOk.of_bits Round.highBits_verified sse2_checks.2.2.2.2.2.2.1
      lowBits := FnOk.of_bits Round.lowBits_verified sse2_checks.2.2.2.2.2.2.2.1
      normLt := FnOk.of_bits Round.normLt_verified sse2_checks.2.2.2.2.2.2.2.2.1
      makeHint := FnOk.of_bits Round.makeHint_verified sse2_checks.2.2.2.2.2.2.2.2.2.1
      useHint := FnOk.of_bits Round.useHint_verified sse2_checks.2.2.2.2.2.2.2.2.2.2.1
      rej4 :=
        have h := fnOkB_spec sse2_checks.2.2.2.2.2.2.2.2.2.2.2.1
        ⟨Rej4.rejNTT4_verified, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, fun _ _ _ => Rej4.rejNTT4_ret⟩
      expandMask4 :=
        have h := fnOkB_spec sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.1
        ⟨Mask4.expandMask4_verified, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
      dotInv := fun c hc => by
        rcases hc with rfl | rfl | rfl
        · exact FnOk.of_bits Arith.DotS.verified4 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        · exact FnOk.of_bits Arith.DotS.verified5 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        · exact FnOk.of_bits Arith.DotS.verified7 sse2_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  features := []

end VG.Proof.MlDsa.X86_64
