module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptContract
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Math
import VerifiedGarbage.Proof.Bignum.Math

/-! # FFDH key generation from the context on x86-64: the attempt meets its contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey
open VG.Proof.Rsa.X86_64 (OutOk Apart apart_of)

theorem genWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega

/-- The attempt's precondition: `vg_ffdh_generate_key`'s, the context, and valid parameters. -/
theorem cgCtx_of {s : State} (h : cgPre s) :
    GkCtx s ∧ CtxIn (cgOf s) (stackArg s 5) s ∧ Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true := by
  obtain ⟨hsp, hrd, hwr, dxy, dxd, dxr, dxs, dxc, dxa, dyd, dyr, dys, dyc, dya, dds, drs, dsc, dsa,
    wX, wY, wD, wR, wS, wC, _, _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hxl, hyl, hrl, hsl, hdv, hcl, hcw⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  have hargs : ∀ i < 7, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi => by
    refine ⟨⟨stackArgAddr s 0, 56⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨hk1, hk2, hdl, hxl, hyl, hrl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) drs, fun i hi => hargs i (by omega), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_, hdv⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dxs (contains_byte _ (by omega) (by omega))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega) (by omega))
  · simpa only [hxl, hyl] using (apart_of dxy (by omega) (by omega))
  · simpa only [hxl] using (apart_of dxd (by omega) (by omega))
  · simpa only [hxl, hrl] using (apart_of dxr (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyd (by omega) (by omega))
  · simpa only [hyl, hrl] using (apart_of dyr (by omega) (by omega))
  · have hn : (stackArg s 6).toNat = 3 + 34 * ((cgOf s).w) := by rw [hcl, genWords_eq]; rfl
    have hdl' : (stackArg s 0).toNat ≤ (gkDom s).length := by
      have h2 : (s.gpr .r9).toNat = 2 * (stackArg s 0).toNat ∨ (s.gpr .r9).toNat = 3 * (stackArg s 0).toNat := hdl
      rw [show (gkDom s).length = (s.gpr .r9).toNat from VG.Proof.Bignum.bytesAt_length _ _ _]; omega
    have hmv := VG.Proof.Ffdh.domainValid_mod hdv
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_, by rw [← hn]; omega⟩, fun i hi j hj => ?_, fun i hi j hj => ?_,
      ?_, hargs 5 (by decide), fun b hb => ?_, fun b hb j hj => ?_, fun b hb j hj => ?_, rfl⟩
    · refine ⟨⟨stackArg s 5, (stackArg s 6).toNat * 8⟩, by rw [hrd]; simp, ?_⟩
      exact Offset.contains_base _ (by rw [hn]; omega) (by omega)
    · exact out_scr dsc.symm (contains_byte _ (by rw [hn]; omega) (by omega))
    · have := apart_of dxc.symm (by omega) (by omega) i (by rw [hn]; omega) j (by rw [hxl]; exact hj)
      exact this
    · have := apart_of dyc.symm (by omega) (by omega) i (by rw [hn]; omega) j (by rw [hyl]; exact hj)
      exact this
    · have e := VG.Proof.Ffdh.generationPrecompute_eq hdl' hmv
      rw [hcw, hn] at e
      exact Option.some.inj e
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change (cgOf s).Z ≤ ofs (cgOf s).B (off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b)
      rw [e]
      exact out_scr dsa.symm (contains_byte _ (by omega) (by omega))
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).xp j
      rw [e]
      exact (apart_of dxa (by omega) (by omega) j (by rw [hxl]; exact hj) (40 + b) (by omega)).symm
    · have e : off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b = stackArgAddr s 0 + BitVec.ofNat 64 (40 + b) := by
        simp only [stackArgAddr, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
          show 8 * (0 + 1) + (40 + b) = 8 * 6 + b by omega]
      change off (s.gpr .rsp) (8 * 6) + BitVec.ofNat 64 b ≠ off (cgOf s).yp j
      rw [e]
      exact (apart_of dya (by omega) (by omega) j (by rw [hyl]; exact hj) (40 + b) (by omega)).symm

/-- `vg_ffdh_generate_key`'s inputs, with the scalar of the context's width. -/
theorem _root_.VG.Proof.Ffdh.X86_64.GenerateKey.Base.cached {s t : State} (hb : Base (gkOf s) (gkRand s) t)
    (hv : Spec.Ffdh.domainValid (stackArg s 0).toNat (gkDom s) = true) : Base (cgOf s) (gkRand s) t := by
  have hbits := genBits_facts hv
  have hb1 : 1 ≤ cgBits s := hbits.1
  have hb2 : cgBits s ≤ 8 * (stackArg s 0).toNat := hbits.2
  have hk := hb.k1
  have hrl := hb.rl
  refine ⟨hb.k1, hb.k2, hb.dl, hb.doml, hb.rl, hb.hZ, hb.scr, hb.dom, hb.rand, hb.x, hb.y, hb.xy, hb.xd, hb.xr,
    hb.yd, hb.yr, hb.hdr, rfl, ?_, fun _ => ?_⟩
  · change (stackArg s 0).toNat - cgEl s < (stackArg s 0).toNat
    have : 1 ≤ cgEl s := by unfold cgEl; omega
    change 64 ≤ (stackArg s 0).toNat at hk
    omega
  · change Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (gkRand s) ((stackArg s 0).toNat - cgEl s)
      ((cgMask (cgBits s)).setWidth 8)) = Spec.Ffdh.vettedScalarOfOctets (gkA s) (gkRand s)
    have hl : (gkRand s).length = (stackArg s 0).toNat := hrl
    have hw : ScalarWidth.width (cgBits s) = cgEl s := by unfold ScalarWidth.width cgEl; omega
    rw [cgMask_byte hb1]
    change 64 ≤ (stackArg s 0).toNat at hk
    have := ScalarWidth.cut_value (r := gkRand s) (bits := cgBits s) (by omega) (by omega)
    rw [hl, hw] at this
    exact this

theorem resultStatus_lt' (p : GkP) (rb : List Byte) : resultStatus p rb < 2 ^ 32 := by
  unfold resultStatus
  split
  · decide
  · split <;> decide

/-- The attempt's outputs, by `keyStatus`. -/
theorem attempt_specC {p : GkP} {rb : List Byte} {s u t : State} (hb : Base p rb u)
    (hm : p.mv = true) (ha : Spec.Ffdh.parametersValid p.params = true) (h : AttemptPost p rb s t) :
    ((t.gpr .rax).setWidth 32).toNat = Spec.Ffdh.keyStatus p.params (p.scalar rb) ∧
      if Spec.Ffdh.keyStatus p.params (p.scalar rb) = 1 then
        Spec.Rsa.bytesAt t.mem p.xp p.k = Spec.Rsa.i2osp (p.scalar rb) p.k ∧
          Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (p.scalar rb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hx, hy, _⟩ := h
  have hst := hb.resultStatus_eq hm ha
  have hlt := resultStatus_lt' p rb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : resultStatus p rb = 1
    · simp only [ite_eq_left hs] at hx hy ⊢
      refine ⟨hx.trans (hb.cut_i2osp hm), ?_⟩
      rw [hb.power_value hm] at hy
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hx hy ⊢
      exact ⟨hx, by rw [hy, i2osp_zero']⟩

theorem cgBody_ok (Mo : Mont) (R : R2Impl Mo) {s : State} (hpre : cgPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.body Mo.mm (.seq (.block r2Head) R.code)) s fun t =>
      cgPost s t ∧ t.gpr .rdi = (cgOf s).B ∧ RunFrame (cgOf s) s.mem t.mem ∧
      (∀ i < 6, word t.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  obtain ⟨c, hci, hv⟩ := cgCtx_of hpre
  have hbits := genBits_facts hv
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  have hb₁ : Base (cgOf s) (gkRand s) u := hb.cached hv
  refine WP.mono (dom_base hb₁ hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  have H : InScr (cgOf s).B (cgOf s).Z s.mem v.mem := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (cgOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  have hm : (cgOf s).mv = true := VG.Proof.Ffdh.domainValid_mod hv
  refine WP.ite (!(cgOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun _ => ?_)
  · exfalso
    rw [hm] at hf
    exact absurd hf (by decide)
  · refine WP.mono (mainC_ok Mo R hb' hd' hG hQ hm (hci.keep (.of_scr H) K.2.1 K.2.2)
      ((K.gpr (by decide)).trans rfl) hbits.1 hbits.2 rfl rfl rfl) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, (RunFrame.of_scr H).trans hframe,
      (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    have hp : Spec.Ffdh.parametersValid (cgOf s).params = true := by
      unfold Spec.Ffdh.domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact attempt_specC (p := cgOf s) (rb := gkRand s) (s := v) (u := v) (t := t) hb' hm hp hmain

theorem cg_correct (Mo : Mont) (R : R2Impl Mo)
    (hmx : (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ cgContract.post s t := by
  have hpre := h
  have c := (cgCtx_of h).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hRetX, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Cached.Generate.code Mo.mm (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ cgContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Cached.Generate.code
  refine WP.seq (WP.mono (cgBody_ok Mo R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_ ?_
    · intro j hj he
      exact hRetX _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.xl]; exact hj) (by have := c.k2; omega))
    · intro j hj he
      exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega))
  · change cgPost s t
    unfold cgPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.Cached
