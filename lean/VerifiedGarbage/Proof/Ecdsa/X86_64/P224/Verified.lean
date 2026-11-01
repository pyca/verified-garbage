module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
import VerifiedGarbage.Proof.P224.Point
import VerifiedGarbage.Proof.P224.Prime
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit
meta import VerifiedGarbage.Proof.P224.Point
meta import VerifiedGarbage.Proof.P224.Prime
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ECDSA over P-224 on x86-64: `Verified`

P-224 is a curve the proof supports (`p224_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P224.law`, `Proof.P224.combOk7` and the
variant's `inv`), so `sign_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `out` or `scratch`, which the return address
is apart from (`abiPreserved`). Constant time by taint tracking with the
address of the comb's static public (`taintSym`): the only branches are on
loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.P224

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p224_nBits : Spec.Ecdsa.nBits p224.C = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h1 : 223 ≤ Spec.P224.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P224.curve.n.log2 < 224 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `28` bytes is dropped. -/
theorem p224_sh : p224.sh = 0 := by
  unfold Cfg.sh
  rw [p224_nBits]
  rfl

theorem p224_ok (hI : InvSounds) : CfgOk p224 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P224.onCurve_G
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
  sh := by rw [p224_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P224.curve.p
    rw [show Spec.P224.curve.p = 26959946667150639794667015087019630673557916260026308143510066298881 by decide +kernel]
    exact Proof.P224.prime_26959946667150639794667015087019630673557916260026308143510066298881),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p224.C.n_ne_zero Proof.P224.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun _ => by unfold AM3; decide +kernel
  comb_am3 := fun _ _ => by unfold AM3; decide +kernel
  am3 := by unfold AM3; decide +kernel
  even _ := by decide
  inverse _ := ⟨by decide, rfl⟩

theorem p224_tbls (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start) :
    CombTbls p224 := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p224_combConsts, show p224.C.len = 28 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p224_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

/-- `[k]G` is a call of `vg_p224_mul_base`, which calls no other function. -/
theorem p224_mulBase : MulBaseOk p224 :=
  ⟨fun _ => ⟨_, rfl, by decide, by lit_decide⟩, fun h => absurd h (by decide)⟩

/-- The inlining checks, shared by correctness and the two call wrappers. -/
theorem sign_inlineOk : signP224.InlineOk = true := by lit_decide

theorem sign_x86 (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP224.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p224_ok hI) hL (p224_tbls hT) (pre_of hs) p224_mulBase
  have hok := sign_inlineOk
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : signP224.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]; lit_decide
  have F := (Exec.regions he (Code.noCalls_inline hok)).2.2
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

/-- `signP224` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def signP224Erased : Prog isa := Code.erase signP224

materialize_shared signP224Erased

/-- Constant time by taint tracking, which follows the calls: `rsp` is
public, as the return addresses they store are. -/
theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP224 :=
  VG.Taint.constantTime_mapBlocks (c' := signP224Erased) (taintSym_eraseInv ["VG_P224_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, h5, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

theorem sat_spec8 :
    (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts) 8).pre satState := by
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.P224.inst, Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig,
    Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p224_combConsts,
    Abi.withConsts, p224_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | exact held | (rw [p224W_length]; rfl) | rfl | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    signX86_64.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 56) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

theorem sign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts) 8).pre s)
    (hp : signX86_64.post s b) : signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  post_patch s b hv u (implies8.pre s hs) (Sig.clear_of_pre_consts hs) hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP224 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) sign_inlineOk (sign_x86 hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

theorem sign_verified (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP224
      (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst (X86_64.abi.withConsts p224.combConsts) 8) :=
  Verified.of_inline_ct sign_inlineOk (sign_x86 hL hT hI) sign_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) sign_patch

end VG.Proof.Ecdsa.X86_64.P224
