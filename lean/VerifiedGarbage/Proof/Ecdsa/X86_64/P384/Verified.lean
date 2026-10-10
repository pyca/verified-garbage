import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitErase
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.P384.Prime
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# ECDSA over P-384 on x86-64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, and `Law` for its group law,
its comb's tables and `InvSounds` for its inversions, which the
registration file supplies: `Proof.P384.law`, `Proof.P384.combOk7` and the
variant's `inv`), so `sign_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `out` or `scratch`, which the return address
is apart from (`abiPreserved`). Constant time by taint tracking with the
address of the comb's static public (`taintSym`): the only branches are on
loop counters, and every address is an argument or the static's address
plus a constant or a counter.
-/

namespace VG.Proof.Ecdsa.X86_64.P384

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384_nBits : 64 * p384.n ≤ Spec.Ecdsa.nBits p384.C := by
  show 384 ≤ Spec.P384.curve.n.log2 + 1
  have : 383 ≤ Spec.P384.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `48` bytes is dropped. -/
theorem p384_sh : p384.sh = 0 := by
  have h : 64 * 6 ≤ Spec.Ecdsa.nBits p384.C := p384_nBits
  show 8 * 48 - Spec.Ecdsa.nBits p384.C = 0; omega

theorem p384_ok (hI : InvSounds) : CfgOk p384 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P384.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  red_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  n_len := by decide +kernel
  n_bits := by decide +kernel
  nbits_le := by decide
  mask h := absurd h (by decide)
  sh := by rw [p384_sh]; decide
  comb d h := by cases h; exact ⟨by decide, by decide, by decide⟩
  inv _ := ⟨by decide, @hI _ _ (by
    show Nat.Prime Spec.P384.curve.p
    rw [show Spec.P384.curve.p =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319
      by decide +kernel]
    exact Proof.P384.prime_39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319),
    InvOk.ofMod (by decide +kernel) (by decide)⟩
  inv_n _ _ := ⟨@hI _ p384.C.n_ne_zero Proof.P384.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  window_am3 := fun _ => by unfold AM3; decide +kernel
  comb_am3 := fun _ _ => by unfold AM3; decide +kernel
  am3 := by unfold AM3; decide +kernel
  even _ := by decide

theorem p384_tbls (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) :
    CombTbls p384 := fun d h => by cases h; exact ⟨hT, fun h => absurd h (by decide)⟩

theorem pre_of {s : State} (h : signX86_64.pre s) : Pre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, -, h12, h13, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p384_combConsts, show p384.C.len = 48 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, ?_⟩
  rw [TblsHeld, p384_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h]

theorem sign_x86 (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State)
    (hs : signX86_64.pre s) :
    ∃ t s', Exec isa signP384.inline s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := sign_ok (p384_ok hI) hL (p384_tbls hT) (pre_of hs)
  have hsp : ∀ i ∈ instrs signP384.inline, Taint.clobbers i .rsp = false := by
    have h : signP384.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [← Code.allInstrs_inline, Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (Code.noCalls_inline (by lit_decide))).2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, hro, hrs, -, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he
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

/-- Constant time by taint tracking, which follows the calls: `rsp` is
public, as the return addresses they store are. -/
theorem sign_ct : ConstantTime isa signX86_64.pre signX86_64.pub signP384 :=
  VG.Taint.constantTime_mapBlocks (c' := signErased) (taintSym_eraseInv ["VG_P384_COMB"])
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
    (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts p384.combConsts) 8).pre satState := by
  have held : ∀ i < p384W.length, satState.mem.readW (satState.syms "VG_P384_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384_combConsts,
    Abi.withConsts, p384_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | exact held | (rw [p384W_length]; rfl) | rfl | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    signX86_64.Implies (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts p384.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

/-- The output is apart from the calls' return address. -/
theorem post_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : signX86_64.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : signX86_64.post s b) :
    signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hb := Clear.wr_bytes hc (p := s.gpr .rdi) (n := 96) (by rw [hs.2.1]; simp) (by decide)
  simpa only [signX86_64, State.patch_gpr, bytesAt_patch hb] using hp

theorem sign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts p384.combConsts) 8).pre s)
    (hp : signX86_64.post s b) : signX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  post_patch s b hv u (implies8.pre s hs) (Sig.clear_of_pre_consts hs) hp

/-- The function with its calls, for a caller (RFC 6979's) that keeps its
buffers off the 8 bytes below `rsp`. -/
theorem sign_call_x86 (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) (s : State) (hs : signX86_64.pre s) (hc : Clear (hole (s.gpr .rsp)) s) :
    ∃ t s', Exec isa signP384 s t s' ∧ abiPreserved s s' ∧ signX86_64.post s s' :=
  ok_of_inline (k := signX86_64) (by lit_decide) (sign_x86 hL hT hI)
    (fun s b hv u hs hc hp => post_patch s b hv u hs hc hp) s ⟨hs, hc⟩

theorem sign_verified (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds) :
    Verified X86_64.target signP384
      (Spec.Ecdsa.P384.inst.signContract (X86_64.abi.withConsts p384.combConsts) 8) :=
  Verified.of_inline_ct (by lit_decide) (sign_x86 hL hT hI) sign_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) sign_patch

end VG.Proof.Ecdsa.X86_64.P384
