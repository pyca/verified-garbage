import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT`. -/
section

/-!
# ML-DSA signing on x86-64: constant time

Two runs whose entry states agree on `signK`'s public data (`signLeakT` among
them) leak the same: the prologue and the return only the pointers, `ExpandA`
only `ρ` (`expandA_tr`), and the rest what `signLeakT` says after `ρ`, on
which they agree once `ExpandA` finished (`pub_leq`, `rest_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Rel2 relStart)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

/-- Two runs whose `ExpandA` finished agree on what their loops leak. -/
theorem pub_leq {σ₁ σ₂ : State} (hpub : (signK p D).pub σ₁ σ₂)
    (hA₁ : expandA p maxBounds (rhoOf p σ₁) = some (amat p (Am p σ₁)))
    (hA₂ : expandA p maxBounds (rhoOf p σ₂) = some (amat p (Am p σ₂))) : LeakEq p 0 σ₁ σ₂ := by
  have e := hpub.2.2.2.2.2.2
  rw [signLeakT_eq hA₁, signLeakT_eq hA₂] at e
  have hρ : (skOf p σ₁).take 32 = (skOf p σ₂).take 32 := pub_rho hpub
  rw [hρ] at e
  exact List.append_cancel_left e

theorem rr_rs {I E : State → State → Prop} {x y : State} (h : RR p D I E x y) : RS p D (fun _ _ => True) I x y := by
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, _⟩ := h
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, trivial, i₁, i₂⟩

theorem sign_ct {P : VG.Impl.MlDsa.X86_64.Sign.Prims} (hP : PrimsOk P D) (h3 : Ok3 p) :
    ConstantTime isa (signK p D).pre (signK p D).pub (Impl.MlDsa.X86_64.Sign.sign P p) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsz⟩ := hf'
  refine relStart (Q := fun _ _ => True) ?_
  unfold Impl.MlDsa.X86_64.Sign.sign
  refine RelCT.seq (RelCT.mono (relInvE (J := fun σ s => VG.Proof.MlDsa.X86_64.Sign.St p D σ s ∧ s.gpr .r15 = 1) (E := fun _ _ => True)
    (fun σ s hp hs => by
      subst hs
      exact WP.mono (VG.Proof.MlDsa.X86_64.Sign.pro_ok hp hsz.1) fun s₁ ⟨h₁, _, hf₁, h15⟩ => ⟨entry_st hP h3 hp h₁ hf₁, h15⟩)
    (block_tr (rs := [.r8]) rfl fun x y ⟨⟨σ₁, σ₂, _, _, hpub, h₁, h₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr h₁ h₂
      exact hpub.2.2.2.2.1)) (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (expandA_tr hP ha) ?_
  refine RelCT.seq (Q := fun _ _ => True) (R := fun (x y : State) => ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r) ?_
    (VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y h => h) (by taint_decide))
  unfold VG.Impl.MlDsa.X86_64.Sign.ifOk
  refine ifOkElse_tr (D := D) (P := RA p D (p.k * p.ℓ)) (fun x y h => by rw [h.2]) (RelCT.mono (rest_tr hP h3)
    (fun x y ⟨x₀, y₀, ⟨⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩, h15⟩, ⟨hPx, _, _⟩, ⟨hPy, _, _⟩, hne⟩ => ?_)
    fun x y h => lrel_rbx (h.lrel fun _ _ h => h.st))
    (RelCT.mono VG.Proof.MlDsa.X86_64.Sign.nil_tr (fun _ _ h => h) fun x y h =>
      ifOk_rbx (I := fun σ s => VG.Proof.MlDsa.X86_64.Sign.IA p D σ (p.k * p.ℓ) s) (fun _ _ h => h.st) (E := fun _ _ => True)
        (C := fun x₀ => (x₀.gpr .r15).setWidth 32 = 0)
        (by obtain ⟨x₀, y₀, R, hx, hy, h0⟩ := h; exact ⟨x₀, y₀, VG.Proof.MlDsa.X86_64.Sign.rr_rs R, hx, hy, h0⟩))
  have e₁ := r15_one i₁.r01 hne
  have e₂ : y₀.gpr .r15 = 1 := h15 ▸ e₁
  obtain ⟨ok₁, fam₁⟩ := i₁.ok e₁
  obtain ⟨ok₂, fam₂⟩ := i₂.ok e₂
  exact ⟨σ₁, σ₂, p₁, p₂, hpub, VG.Proof.MlDsa.X86_64.Sign.pub_leq hpub (expandA_max ok₁) (expandA_max ok₂),
    ⟨i₁.st.step hPx st0, ok₁, Fam.keep i₁.st.lay hPx fa0 fam₁⟩,
    ⟨i₂.st.step hPy st0, ok₂, Fam.keep i₂.st.lay hPy fa0 fam₂⟩⟩

end

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst`. -/
section

/-!
# ML-DSA signing on x86-64: the primitives it calls

The verified x86-64 implementations of the primitives (`prims`), and what the
proofs of signing need of them, with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), with 32 bytes of stack for each call: their
contracts, and, of the samplers whose result signing branches on, that it
depends only on their public data and that they succeed only if the algorithm
finishes within `maxBounds` (from what their own proofs say they return,
`rejNTT_correct` and `sampleInBall_correct`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl)

/-- The x86-64 implementations of the primitives. -/
def prims : VG.Impl.MlDsa.X86_64.Sign.Prims where
  ntt := Impl.MlDsa.X86_64.Arith.ntt
  invNtt := Impl.MlDsa.X86_64.Arith.nttInv
  mul := Impl.MlDsa.X86_64.Arith.mul
  mulAdd := Impl.MlDsa.X86_64.Arith.mulAdd
  add := Impl.MlDsa.X86_64.Arith.add
  sub := Impl.MlDsa.X86_64.Arith.sub
  rejNTT := Impl.MlDsa.X86_64.Sample.rejNTT
  expandMask := Impl.MlDsa.X86_64.Sample.expandMask
  ball := Impl.MlDsa.X86_64.Sample.sampleInBall
  highBits := Impl.MlDsa.X86_64.Round.highBits
  lowBits := Impl.MlDsa.X86_64.Round.lowBits
  normLt := Impl.MlDsa.X86_64.Round.normLt
  makeHint := Impl.MlDsa.X86_64.Round.makeHint
  simpleBitPack := Impl.MlDsa.X86_64.Pack.simpleBitPack
  bitPack := Impl.MlDsa.X86_64.Pack.bitPack
  bitUnpack := Impl.MlDsa.X86_64.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.X86_64.Pack.hintBitPack
  rej4 := Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
  expandMask4 := Impl.MlDsa.X86_64.Sample.Mask4.expandMask4

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Impl.MlDsa.X86_64.Arith.Backend) : VG.Impl.MlDsa.X86_64.Sign.Prims :=
  { VG.Proof.MlDsa.X86_64.Sign.prims with
    ntt := B.ntt
    invNtt := B.invNtt
    mul := B.mul
    mulAdd := B.mulAdd
    add := B.add
    sub := B.sub
    rej4 := B.rej4
    expandMask4 := B.expandMask4
    highBits := B.highBits
    lowBits := B.lowBits
    normLt := B.normLt
    makeHint := B.makeHint
    sfx := B.sfx }

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- The stack signing gives each call. -/
abbrev signStack : Nat := 32

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.X86_64.Sample VG.Proof.MlDsa.Sample

theorem rn_pre (s : State) (h : (rejNTTContract X86_64.abi 16).pre s) : rnK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs]

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract X86_64.abi 16).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, hdi, _, _⟩ := h
  exact VG.Proof.MlDsa.Sign.leakBytes_inj hb

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract X86_64.abi 16).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.rejNTT s tr s') :
    (s'.gpr .rax).setWidth 32 =
      if (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := rejNTT_correct s (VG.Proof.MlDsa.X86_64.Sign.rn_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem sb_pre (s : State) (h : (sampleInBallContract X86_64.abi 16).pre s) : sbK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs]

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract X86_64.abi 16).pub s₁ s₂) :
    tauOf s₁ = tauOf s₂ ∧
      bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat = bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, _, _, hdx, _, _⟩ := h
  exact ⟨by rw [tauOf, tauOf, hdx], VG.Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract X86_64.abi 16).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.sampleInBall s tr s') :
    (s'.gpr .rax).setWidth 32 =
      if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := sampleInBall_correct s (VG.Proof.MlDsa.X86_64.Sign.sb_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- A function of the polynomial arithmetic satisfies what the proofs of signing need of it. -/
def calleeOf {k : Nat → Contract isa} {c : Prog isa} (h : FnOk k c) : Callee k VG.Proof.MlDsa.X86_64.Sign.signStack c :=
  ⟨0, by decide, h.ver, h.nosp, by have := h.depth; unfold VG.Proof.MlDsa.X86_64.Sign.signStack; omega⟩

/-- The primitives, with the polynomial arithmetic of `v`, satisfy what the
proofs of signing need of them. -/
def prims_okWith (v : ArithImpl) : PrimsOk (VG.Proof.MlDsa.X86_64.Sign.primsWith v.code) VG.Proof.MlDsa.X86_64.Sign.signStack where
  ntt := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.ntt
  invNtt := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.invNtt
  mul := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.mul
  mulAdd := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.mulAdd
  add := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.add
  sub := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.sub
  rejNTT := (⟨16, by decide, Proof.MlDsa.X86_64.Sample.rejNTT_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.rejNTT)
  expandMask := (⟨16, by decide, Proof.MlDsa.X86_64.Sample.expandMask_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.expandMask)
  ball := (⟨16, by decide, Proof.MlDsa.X86_64.Sample.sampleInBall_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.ball)
  highBits := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.highBits
  lowBits := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.lowBits
  normLt := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.normLt
  makeHint := VG.Proof.MlDsa.X86_64.Sign.calleeOf v.ok.makeHint
  simpleBitPack := (⟨0, by decide, Proof.MlDsa.X86_64.Pack.simpleBitPack_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.simpleBitPack)
  bitPack := (⟨0, by decide, Proof.MlDsa.X86_64.Pack.bitPack_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel), by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.bitPack)
  bitUnpack := (⟨0, by decide, Proof.MlDsa.X86_64.Pack.bitUnpack_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.bitUnpack)
  hintBitPack := (⟨0, by decide, Proof.MlDsa.X86_64.Pack.hintBitPack_verified, VG.Proof.MlDsa.X86_64.Sign.nosp_of (by decide +kernel),
    by decide +kernel⟩ :
    Callee _ VG.Proof.MlDsa.X86_64.Sign.signStack prims.hintBitPack)
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.X86_64.Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.X86_64.Sign.rn_ret h₁ e₁, VG.Proof.MlDsa.X86_64.Sign.rn_ret h₂ e₂, VG.Proof.MlDsa.X86_64.Sign.rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.X86_64.Sign.rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.X86_64.Sign.one_ne_zero32
  rej4 := ⟨24, by decide, v.ok.rej4.ver, v.ok.rej4.nosp, by
    have := v.ok.rej4.depth
    show 8 * (v.code.rej4.depth + 1) ≤ VG.Proof.MlDsa.X86_64.Sign.signStack
    unfold VG.Proof.MlDsa.X86_64.Sign.signStack; omega⟩
  expandMask4 := ⟨24, by decide, v.ok.expandMask4.ver, v.ok.expandMask4.nosp, by
    have := v.ok.expandMask4.depth
    show 8 * (v.code.expandMask4.depth + 1) ≤ VG.Proof.MlDsa.X86_64.Sign.signStack
    unfold VG.Proof.MlDsa.X86_64.Sign.signStack; omega⟩
  rej4Ret := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨v.ok.rej4.ver.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by
        rw [v.ok.rej4.ret _ _ _ h₁ e₁, v.ok.rej4.ret _ _ _ h₂ e₂]
        exact Proof.MlDsa.X86_64.Rej4.rej4Res_congr (Proof.MlDsa.X86_64.Rej4.r4_pub s₁ s₂ hp)⟩
  rej4Max := fun s t s' h e h1 k hk => by
    rw [v.ok.rej4.ret _ _ _ h e] at h1
    exact Proof.MlDsa.X86_64.Rej4.rej4Res_max h1 hk (by decide)
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.X86_64.Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [VG.Proof.MlDsa.X86_64.Sign.sb_ret h₁ e₁, VG.Proof.MlDsa.X86_64.Sign.sb_ret h₂ e₂, (VG.Proof.MlDsa.X86_64.Sign.sb_pub s₁ s₂ hp).1, (VG.Proof.MlDsa.X86_64.Sign.sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [VG.Proof.MlDsa.X86_64.Sign.sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf s)
      (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm VG.Proof.MlDsa.X86_64.Sign.one_ne_zero32
  hD := by decide
  hD' := by decide

end VG.Proof.MlDsa.X86_64.Sign

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified`. -/
section

/-!
# ML-DSA signing on x86-64: verified

`vg_mldsa{44,65,87}_sign` (`sign (primsWith v.code) p`, for an implementation
`v` of the polynomial arithmetic) is verified against `signContractT`:
`signContract` with `signLeakT` (`Proof/MlDsa/Sign/Leak.lean`) for `signLeak`,
which tags what each iteration of the loop leaks after its `c̃` with whether
it was rejected. The contract's `signLeak` tags the iterations the same way
(`signLeakT_eq_signLeak`), so `signContractT` is `signContract`
(`signContractT_eq`), against which `sign*_verified'` state it.
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Impl.MlDsa.X86_64.Arith (Backend)

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
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x3100 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 64⟩, ⟨0x3100, 32⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, 8 * scratchWords p⟩]

theorem signK_implies_of {p : Params} (hsat : ∃ s, (VG.Proof.MlDsa.X86_64.Sign.signContractT p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack).pre s) :
    (signK p VG.Proof.MlDsa.X86_64.Sign.signStack).Implies (VG.Proof.MlDsa.X86_64.Sign.signContractT p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack) where
  pre := by sig_implies_pre [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, signK, X86_64.abi, X86_64.argRegs]
  post := by sig_implies_post [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, signK, X86_64.abi, X86_64.argRegs]
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, signK, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hdi, hsi, hdx, hcx, h8, hsp, hb⟩
  sat := hsat

theorem signK_implies {p : Params} (h3 : Ok3 p) :
    (signK p VG.Proof.MlDsa.X86_64.Sign.signStack).Implies (VG.Proof.MlDsa.X86_64.Sign.signContractT p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack) := by
  refine VG.Proof.MlDsa.X86_64.Sign.signK_implies_of ?_
  rcases h3 with rfl | rfl | rfl
  · sig_implies_sat [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using VG.Proof.MlDsa.X86_64.Sign.signSat mlDsa44
  · sig_implies_sat [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using VG.Proof.MlDsa.X86_64.Sign.signSat mlDsa65
  · sig_implies_sat [VG.Proof.MlDsa.X86_64.Sign.signContractT, signSig, X86_64.abi, X86_64.argRegs] [signSat] using VG.Proof.MlDsa.X86_64.Sign.signSat mlDsa87

/-! ## For any implementation of the polynomial arithmetic

A check that composes over the code (`Comp`) gives the same result on
signing with the polynomial arithmetic `B` as with every function of it
empty, if it holds of `B`'s functions (`sign_same`), so MXCSR (`sign_ctl`)
and the stack pointer (`sign_spSafe`) are checked by evaluating signing
with no implementation of it. -/

theorem sign_same {m mc : Prog isa → Bool} (hm : Comp m mc) {B : Backend} (h1 : mc B.ntt = true)
    (h2 : mc B.invNtt = true) (h3 : mc B.mul = true) (h4 : mc B.mulAdd = true) (h5 : mc B.add = true)
    (h6 : mc B.sub = true) (h7 : mc B.rej4 = true) (h8 : mc B.expandMask4 = true) (h9 : mc B.highBits = true)
    (h10 : mc B.lowBits = true) (h11 : mc B.normLt = true) (h12 : mc B.makeHint = true) (p : Params) :
    Same m (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith B) p) (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith .empty) p) := by
  unfold Impl.MlDsa.X86_64.Sign.sign
  same_tac hm

theorem sign0_ctlC {p : Params} (h3 : Ok3 p) : ctlC (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith .empty) p) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

theorem sign0_sp {p : Params} (h3 : Ok3 p) :
    (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith .empty) p).allInstrs (fun i => !isa.writesSp i) = true := by
  rcases h3 with rfl | rfl | rfl <;> decide +kernel

variable (v : ArithImpl) {p : Params} (h3 : Ok3 p)
include h3

theorem sign_ctl : ctlOk (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith v.code) p) = true :=
  ctlOk_of_ctlC (Same.ok (VG.Proof.MlDsa.X86_64.Sign.sign_same Comp.ctlC v.ok.ntt.ctl v.ok.invNtt.ctl v.ok.mul.ctl v.ok.mulAdd.ctl
    v.ok.add.ctl v.ok.sub.ctl v.ok.rej4.ctl v.ok.expandMask4.ctl v.ok.highBits.ctl v.ok.lowBits.ctl
    v.ok.normLt.ctl v.ok.makeHint.ctl p) (VG.Proof.MlDsa.X86_64.Sign.sign0_ctlC h3))

theorem sign_spSafe : (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith v.code) p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs (Same.ok (VG.Proof.MlDsa.X86_64.Sign.sign_same (Comp.all _) (Code.allInstrs_of_all v.ok.ntt.sp)
    (Code.allInstrs_of_all v.ok.invNtt.sp) (Code.allInstrs_of_all v.ok.mul.sp)
    (Code.allInstrs_of_all v.ok.mulAdd.sp) (Code.allInstrs_of_all v.ok.add.sp)
    (Code.allInstrs_of_all v.ok.sub.sp) (Code.allInstrs_of_all v.ok.rej4.sp)
    (Code.allInstrs_of_all v.ok.expandMask4.sp)
    (Code.allInstrs_of_all v.ok.highBits.sp) (Code.allInstrs_of_all v.ok.lowBits.sp)
    (Code.allInstrs_of_all v.ok.normLt.sp) (Code.allInstrs_of_all v.ok.makeHint.sp) p) (VG.Proof.MlDsa.X86_64.Sign.sign0_sp h3))

theorem sign_verified :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith v.code) p) (VG.Proof.MlDsa.X86_64.Sign.signContractT p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack) :=
  Verified.of_correct (sign_correct (VG.Proof.MlDsa.X86_64.Sign.prims_okWith v) h3 (VG.Proof.MlDsa.X86_64.Sign.sign_ctl v h3)) (VG.Proof.MlDsa.X86_64.Sign.sign_ct (VG.Proof.MlDsa.X86_64.Sign.prims_okWith v) h3)
    (VG.Proof.MlDsa.X86_64.Sign.signK_implies h3)

omit h3 in
/-- Against the contract: `signContractT` is `signContract`, whose leakage
tags each iteration as `signLeakT` does (`signLeakT_eq_signLeak`). -/
theorem signContractT_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    VG.Proof.MlDsa.X86_64.Sign.signContractT p A stack = signContract p A stack := by
  unfold VG.Proof.MlDsa.X86_64.Sign.signContractT signContract
  simp only [Sign.signLeakT_eq_signLeak]

theorem sign_verified' :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.sign (VG.Proof.MlDsa.X86_64.Sign.primsWith v.code) p) (signContract p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack) :=
  VG.Proof.MlDsa.X86_64.Sign.signContractT_eq p X86_64.abi VG.Proof.MlDsa.X86_64.Sign.signStack ▸ VG.Proof.MlDsa.X86_64.Sign.sign_verified v h3

end VG.Proof.MlDsa.X86_64.Sign

end
