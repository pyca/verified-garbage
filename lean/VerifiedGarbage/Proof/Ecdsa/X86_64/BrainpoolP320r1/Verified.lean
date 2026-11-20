module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombGeneral
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.BrainpoolP320r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP320r1.Point
import VerifiedGarbage.Proof.BrainpoolP320r1.Prime
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86_64
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Point
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.RspMxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
meta import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-! ### `Ecdsa.X86_64.BrainpoolP320r1.Contract`, which only this module used -/

section

/-!
# ECDSA over brainpoolP320r1 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP320r1.inst` for x86-64, by name:
`vg_ecdsa_brainpoolp320r1_sign(out = rdi, d = rsi, digest = rdx, k = rcx, scratch = r8)`,
the result in `eax`, with the comb's tables (`brainpoolp320r1S.combConsts`, the
static `VG_BRAINPOOLP320R1_COMB`) readable where the calling convention says.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP320r1

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP320r1.curve (ofBytes (bytesAt m d 40)) (hashToInt Spec.BrainpoolP320r1.curve (bytesAt m digest 40))
    (ofBytes (bytesAt m k 40))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 80⟩
    let d : Region := ⟨s.gpr .rsi, 40⟩
    let digest : Region := ⟨s.gpr .rdx, 40⟩
    let k : Region := ⟨s.gpr .rcx, 40⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ++ Abi.constRegions (fun n => s.syms n) Impl.Ecdsa.X86_64.brainpoolp320r1S.combConsts ∧
      s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
      TblsHeld Impl.Ecdsa.X86_64.brainpoolp320r1S s [out, scratch, ret]
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 80 = encode Spec.BrainpoolP320r1.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 80 = List.replicate 80 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    ∀ c ∈ Impl.Ecdsa.X86_64.brainpoolp320r1S.combConsts, s₁.syms c.1 = s₂.syms c.1

end VG.Proof.Ecdsa.X86_64.BrainpoolP320r1

end

end

/-! # brainpoolP320r1 signing on x86-64: correctness, memory safety and constant time

The general complete-addition ladder works for any `a`. Field and scalar
inversions use the existing divsteps implementation, instantiated with
kernel-checked primality certificates.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP320r1

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp320r1_nBits : Spec.Ecdsa.nBits brainpoolp320r1.C = 320 := by
  show Spec.BrainpoolP320r1.curve.n.log2 + 1 = 320
  have h1 : 319 ≤ Spec.BrainpoolP320r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP320r1.curve.n.log2 < 320 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h1, h2]

/-- No bit of a hash of `40` bytes is dropped. -/
theorem brainpoolp320r1_sh : brainpoolp320r1.sh = 0 := by
  unfold Cfg.sh
  rw [brainpoolp320r1_nBits]
  rfl

theorem brainpoolp320r1_ok (hI : InvSounds) : BaseCfgOk brainpoolp320r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP320r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [brainpoolp320r1_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.BrainpoolP320r1.curve.p
    exact Proof.BrainpoolP320r1.p_prime),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ brainpoolp320r1.C.n_ne_zero Proof.BrainpoolP320r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even h := absurd h (by decide)
  inverse _ := ⟨by decide, rfl⟩

theorem brainpoolp320r1_tbls : CombTbls brainpoolp320r1 := fun _ h => by cases h

/-- ECDH's, verification's and the public key's `[k]G` is a call of
`vg_brainpoolp320r1_mul`, which calls no other function. -/
theorem brainpoolp320r1_mulBase : MulBaseOk brainpoolp320r1 :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨.inr (.inr (.inr rfl)), by lit_decide⟩⟩

theorem brainpoolp320r1S_sh : brainpoolp320r1S.sh = 0 := brainpoolp320r1_sh

/-- `brainpoolp320r1_ok` for the signature's configuration, which only declares
the comb's tables. -/
theorem brainpoolp320r1S_ok (hI : InvSounds) : BaseCfgOk brainpoolp320r1S where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP320r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [brainpoolp320r1S_sh]; decide
  comb _ h := by cases h
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.BrainpoolP320r1.curve.p
    exact Proof.BrainpoolP320r1.p_prime),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ brainpoolp320r1S.C.n_ne_zero Proof.BrainpoolP320r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun h => by cases h
  comb_am3 := fun _ h => by cases h
  even h := absurd h (by decide)
  inverse _ := ⟨by decide, rfl⟩

/-- The comb's digits of 7 bits, 46 of them, cover the scalar's 320 bits. -/
theorem brainpoolp320r1S_comb : CombOk brainpoolp320r1S brainpoolp320r1Comb :=
  ⟨by decide, by decide, by decide⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre brainpoolp320r1S s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, held, fun r hr => ⟨(fit r hr).1, fun w hw => ?_⟩⟩
  rw [h2] at hw
  exact (fit r hr).2 w (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h])

/-- The code's calls can be inlined, and no instruction of it or of what it
calls writes `rsp` or touches MXCSR: one walk of the code, with one match for
the tests of each instruction (`Code.InlineOkB`). -/
theorem sign_inlineOkB : signBrainpoolP320r1.InlineOkB (bMx + bNs) = true := by lit_decide

theorem sign_x86 (hL : Law Spec.BrainpoolP320r1.curve)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signBrainpoolP320r1.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := signG_ok (brainpoolp320r1S_ok hI) hL brainpoolp320r1S_comb
    (Proof.BrainpoolP320r1.combOk7 hL) rfl (pre_of hs)
  obtain ⟨hsp, hmx⟩ := rsp_mxcsr (c := signBrainpoolP320r1) (Code.allInstrs_mono
    (fun i h => by rw [noRsp_of_hasBits rfl h, noMx_of_hasBits rfl h]; rfl)
    (Code.allInstrs_of_inlineOkB sign_inlineOkB))
  have F := (Exec.regions he (Code.noCalls_inline (Code.inlineOk_of_B sign_inlineOkB))).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)

/-- `signBrainpoolP320r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signBrainpoolP320r1Erased : Prog isa := Code.erase signBrainpoolP320r1

materialize_shared signBrainpoolP320r1Erased

theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signBrainpoolP320r1 :=
  VG.Taint.constantTime_mapBlocks (c' := signBrainpoolP320r1Erased)
    (taintSym_eraseInv ["VG_BRAINPOOLP320R1_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn
        exact hsy _ (gtab_mem_consts (c := brainpoolp320r1S) rfl)⟩)
    rfl (by taint_decide)

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 80) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.BrainpoolP320r1.curve) (hI : InvSounds) (s : State) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signBrainpoolP320r1 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (Code.inlineOk_of_B sign_inlineOkB) (sign_x86 hL hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

end VG.Proof.Ecdsa.X86_64.BrainpoolP320r1
