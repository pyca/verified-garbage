module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecPriv
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecOut
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec
import VerifiedGarbage.Proof.RsaOaep.X86_64.EncMain
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall

/-!
# RSAES-OAEP decryption on x86-64: the decoding

`decMain` (`decMain_ok`): from `EM` in our working space and the private-key
operation's result in its slot, the label's hash, the seed and `DB`
unmasked, `lHash'` compared, `T` scanned, copied and shifted, and the
message under the mask `ok` to `out`, its length to `*msg_len`: what
`Spec.RsaOaep.decrypt` writes for the operation's outcome.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.HashFns (StreamingOK)

/-! ## The pieces that keep `rsp`, MXCSR and the stack -/

theorem accLh_good : Good accLh :=
  ⟨rfl, rfl, by simp [accLh, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem scan_good : Good scan :=
  ⟨rfl, rfl, by simp [scan, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem clearBuf_good : Good clearBuf := ⟨rfl, rfl, by simp [clearBuf, Code.depth]⟩
theorem copyT_good : Good copyT := ⟨rfl, rfl, by simp [copyT, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem outLoop_good : Good outLoop := ⟨rfl, rfl, by simp [outLoop, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩
theorem decFail_good : Good decFail :=
  ⟨rfl, rfl, by simp [decFail, zeroOut, Code.depth, Impl.Mgf1.X86_64.byteLoop]⟩

/-! ## The argument slots -/

/-- The slots `decPrologue` and `selPrologue` store to. -/
def decKs : List Nat := [14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50]

theorem decKs_iff {k : Nat} (h : k ∈ decKs) :
    k = 14 ∨ (21 ≤ k ∧ k ≤ 29) ∨ (37 ≤ k ∧ k ≤ 43) ∨ (45 ≤ k ∧ k ≤ 50) := by
  simp only [decKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem decKs_lt : ∀ k ∈ decKs, k < nW := by decide

/-- The argument slots, as the prologues stored them. -/
def ArgsD (s : State) (W : Nat → BitVec 64) : Prop := ∀ k ∈ decKs, W k = decW s k

theorem ArgsD.w {s : State} {W : Nat → BitVec 64} (h : ArgsD s W) :
    W 14 = stackArg s 15 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rcx ∧ W 23 = s.gpr .r8 ∧ W 24 = s.gpr .r9 ∧
    W 25 = stackArg s 0 ∧ W 26 = stackArg s 16 ∧ W 27 = stackArg s 11 ∧ W 28 = stackArg s 12 ∧
    W 29 = s.gpr .rdx := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [h _ (by simp [decKs])]; simp [decW, fnW, selW, decPW, upd])

/-- The selectors' slots, and the lengths of the hash functions they name. -/
theorem ArgsD.sel {s : State} {W : Nat → BitVec 64} (h : ArgsD s W) :
    W 37 = BitVec.ofNat 64 (dselH s) ∧ W 38 = BitVec.ofNat 64 (dselG s) ∧
    W 39 = BitVec.ofNat 64 (lenOf (dselH s)) ∧ W 40 = BitVec.ofNat 64 (lenOf (dselH s) + 1) ∧
    W 41 = BitVec.ofNat 64 (2 * lenOf (dselH s) + 1) ∧ W 42 = BitVec.ofNat 64 (2 * lenOf (dselH s) + 2) ∧
    W 43 = BitVec.ofNat 64 (lenOf (dselG s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [h _ (by simp [decKs])]; simp [decW, fnW, selW, upd])

/-- The slots of the tables' words. -/
theorem ArgsD.fn {s : State} {W : Nat → BitVec 64} (h : ArgsD s W) :
    (W 45 = tw s.mem (dtabH s) 0 ∧ W 46 = tw s.mem (dtabH s) 1 ∧ W 47 = tw s.mem (dtabH s) 2) ∧
    (W 48 = tw s.mem (dtabG s) 0 ∧ W 49 = tw s.mem (dtabG s) 1 ∧ W 50 = tw s.mem (dtabG s) 2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> (rw [h _ (by simp [decKs])]; simp [decW, fnW, upd])

/-- The streaming functions of the table `j` (19 or 20) of the entry `s`. -/
abbrev FnsD (s : State) (T : Spec.HashFns.Streaming) (j : Nat) : Prop :=
  Fns decStack s T (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1) (tw s.mem (stackArg s j) 2)

theorem ArgsD.of {s : State} {W W' : Nat → BitVec 64} (h : ArgsD s W) (hW : ∀ k ∈ decKs, W' k = W k) :
    ArgsD s W' := fun k hk => (hW k hk).trans (h k hk)

/-! ## Bytes and masks -/

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]; exact trunc_zext b

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

/-! ## The outcome -/

/-- The result in its slot (word 30), and `EM` in our working space. -/
def ResD (V : Nat → Byte) (W : Nat → BitVec 64) (k : Nat) : Spec.Rsa.Outcome → Prop
  | .ok em => W 30 = 1 ∧ (List.range k).map (fun i => V (oEm + i)) = em
  | .invalid => W 30 = 0
  | .fault => W 30 = 2

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
theorem decMain_ok {s t : State} (fH : FnsD s TH 19) (fG : FnsD s TG 20)
    (eH : Spec.HashId.mgf1 (dselH s) = some Hh) (eG : Spec.HashId.mgf1 (dselG s) = some Gh) (hp : DPre s) (he : EnvD s t) (L : Lay t (fb s) (stackArg s 15))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 15) V W) (hW : ArgsD s W)
    (hk : 2 * TH.S.digestBytes + 2 ≤ (s.gpr .r8).toNat) {o : Spec.Rsa.Outcome}
    (hres : ResD V W (s.gpr .r8).toNat o) :
    WP isa decMain t fun t' => EnvD s t' ∧
      Spec.RsaOaep.writtenDecrypt t'.mem (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat ((t'.gpr .rax).setWidth 32)
        (decOut Hh Gh (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat) o) := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29⟩ := hW.w
  obtain ⟨-, -, w39, w40, w41, w42, w43⟩ := hW.sel
  obtain ⟨fnH, fnG⟩ := hW.fn
  have hDl : TH.S.digestBytes = lenOf (dselH s) := lenOf_eq hTH eH
  have hGl : TG.S.digestBytes = lenOf (dselG s) := lenOf_eq hTG eG
  rw [← hDl] at w39 w40 w41 w42
  rw [← hGl] at w43
  have hk1 := hp.lv.1; have hk2 := hp.lv.2; have hsl := hp.hsl
  have hz := sizes hTH; have hzG := sizes hTG
  have hD := hTH.pos

  have c0 : oEm = 0 := rfl
  have w23' : W 23 = BitVec.ofNat 64 (s.gpr .r8).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- The label's hash.
  have sS : Region.Sub ⟨stackArg s 15, oRsa⟩ (scrD s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  have A0 : LabAt t (fb s) (stackArg s 15) W (stackArg s 11) (stackArg s 12).toNat :=
    ⟨w27, by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq], (stackArg s 12).isLt,
      Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, he.rd, hp.hrd]; simp),
      hp.dlbs.sub_right sS, hp.dKlb.sub_left (ret_subD s)⟩
  refine WP.seq (WP.mono (wp_good (hashLabel_good oLh)
    (hashLabel_ok hTH fH (Hs := Hh) (congrFun hTH.hash) he.here L R A0 hp.wL
      (rdIn_entry (r := ⟨stackArg s 11, (stackArg s 12).toNat⟩) (by rw [hp.hrd]; simp)) fnH (Or.inr rfl)))
    fun t1 ⟨⟨L1, _, rd1, wr1, cs1, V1, R1, hV1, hV1'⟩, sp1, mx1, f1⟩ => ?_)
  have he1 : EnvD s t1 := he.step rd1 wr1 sp1 (fun r hr _ => cs1 r hr) mx1 f1
  have hlab : Spec.Rsa.bytesAt t.mem (stackArg s 11) (stackArg s 12).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat :=
    FrD.bytes he.fr hp.dKlb hp.dOlb hp.dMlb hp.dlbs.symm (by have := hp.wL; omega_using [])
  rw [hlab] at hV1'
  -- The seed unmasked.
  refine WP.seq (WP.mono (wp_good seedArgs_good (seedArgs_ok L1 R1 w23' w39 w40 (by omega_using [hk])))
    fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ => ?_)
  have he2 : EnvD s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  refine WP.seq (WP.mono (wp_good mgfXor_good (mgfXor_ok hTG fG (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid
        he2.here L2 R2 ⟨by unfold oEm oSt; omega_using [hk2, hz], by unfold oEm oSt; omega_using [hz], by omega_using [], by omega_using [hD], by omega_using [hz]⟩
    (mW_args _ _ _ _ _ _) ⟨(mW_other (by omega_using [])).trans fnG.1, (mW_other (by omega_using [])).trans fnG.2.1,
      (mW_other (by omega_using [])).trans fnG.2.2⟩ ((mW_other (by omega_using [])).trans w43)))
    fun t3 ⟨⟨L3, _, rd3, wr3, cs3, V3, W3, R3, hW3, hV3⟩, sp3, mx3, f3⟩ => ?_)
  have he3 : EnvD s t3 := he2.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3
  have W3e : ∀ k, (k < 15 ∨ 18 < k) → k < nW → k ≠ 19 → k ≠ 20 → W3 k = W k := fun k h1 h2 h3 h4 =>
    (hW3 k h2 h3 h4).trans (mW_other h1)
  -- `DB` unmasked.
  refine WP.seq (WP.mono (wp_good dbArgs_good (dbArgs_ok L3 R3
    ((W3e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23')
    ((W3e 39 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w39)
    ((W3e 40 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w40)
        (by omega_using [hk])))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 : EnvD s t4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  have W3f : ∀ k, 45 ≤ k → k ≤ 50 → W3 k = W k := fun k h1 h2 =>
    W3e k (by omega_using [h1]) (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1])
  refine WP.seq (WP.mono (wp_good mgfXor_good (mgfXor_ok hTG fG (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid
        he4.here L4 R4 ⟨by unfold oEm oSt; omega_using [hz], by unfold oEm oSt; omega_using [hk2, hz], by omega_using [], by omega_using [hk], by omega_using [hk2]⟩
    (mW_args _ _ _ _ _ _)
    ⟨(mW_other (by omega_using [])).trans ((W3f 48 (by omega_using []) (by omega_using [])).trans fnG.1),
      (mW_other (by omega_using [])).trans ((W3f 49 (by omega_using []) (by omega_using [])).trans fnG.2.1),
      (mW_other (by omega_using [])).trans ((W3f 50 (by omega_using []) (by omega_using [])).trans fnG.2.2)⟩
    ((mW_other (by omega_using [])).trans ((W3e 43 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w43)))) fun t5 ⟨⟨L5, _, rd5, wr5, cs5, V5, W5, R5, hW5, hV5⟩, sp5, mx5, f5⟩ => ?_)
  have he5 : EnvD s t5 := he4.step rd5 wr5 sp5 (fun r hr _ => cs5 r hr) mx5 f5
  have W5e : ∀ k, (k < 15 ∨ 18 < k) → k < nW → k ≠ 19 → k ≠ 20 → W5 k = W k := fun k h1 h2 h3 h4 =>
    (hW5 k h2 h3 h4).trans ((mW_other h1).trans (W3e k h1 h2 h3 h4))
  have w5k : W5 23 = BitVec.ofNat 64 (s.gpr .r8).toNat :=
    (W5e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23'
  -- `lHash'` against `lHash`.
  have w5 : ∀ j, (j < 15 ∨ 18 < j) → j < nW → j ≠ 19 → j ≠ 20 → ∀ v, W j = v → W5 j = v :=
    fun j h1 h2 h3 h4 v hv => (W5e j h1 h2 h3 h4).trans hv
  refine WP.seq (WP.mono (wp_good accLh_good (accLh_ok L5 R5
    (w5 39 (by omega_using []) (by decide) (by omega_using []) (by omega_using []) _ w39) hD (by omega_using [hz])))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_)
  have he6 : EnvD s t6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  -- The scan.
  refine WP.seq (WP.mono (wp_good scan_good (scan_ok (D := TH.S.digestBytes) L6 R6
    (by simp only [upd]; rw [ifn (by decide)]; exact w5k)
    (by simp only [upd]; rw [ifn (by decide)]; exact w5 41 (by omega_using []) (by decide) (by omega_using []) (by omega_using []) _ w41)
    (by omega_using [hk]) hk2 (by omega_using [hz])))
    fun t7 ⟨⟨L7, k7, R7⟩, sp7, mx7, f7⟩ => ?_)
  have he7 : EnvD s t7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  have w7k : ∀ j, j ≠ 31 → j ≠ 32 → (upd (upd (upd W5 31 (accL V5 TH.S.digestBytes TH.S.digestBytes)) 31
      ((scanS (tF V5 TH.S.digestBytes) (upd W5 31 (accL V5 TH.S.digestBytes TH.S.digestBytes) 31)
        ((s.gpr .r8).toNat - (2 * TH.S.digestBytes + 1))).2.2 |||
       (scanS (tF V5 TH.S.digestBytes) (upd W5 31 (accL V5 TH.S.digestBytes TH.S.digestBytes) 31)
        ((s.gpr .r8).toNat - (2 * TH.S.digestBytes + 1))).1)) 32
      (scanS (tF V5 TH.S.digestBytes) (upd W5 31 (accL V5 TH.S.digestBytes TH.S.digestBytes) 31)
        ((s.gpr .r8).toNat - (2 * TH.S.digestBytes + 1))).2.1) j = W5 j := fun j h1 h2 => by
    simp only [upd, ifn h1, ifn h2]
  -- The buffer.
  refine WP.seq (WP.mono (wp_good clearBuf_good (clearBuf_ok (D := TH.S.digestBytes) L7 R7 (k := (s.gpr .r8).toNat)
    (by rw [w7k 23 (by decide) (by decide)]; exact w5k)
    (by rw [w7k 41 (by decide) (by decide)]; exact w5 41 (by omega_using []) (by decide) (by omega_using []) (by omega_using []) _ w41)
    (by omega_using [hk])))
    fun t8 ⟨⟨L8, k8, hsi8, h108, hcx8, R8⟩, sp8, mx8, f8⟩ => ?_)
  have he8 : EnvD s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  refine WP.seq (WP.mono (wp_good copyT_good (copyT_ok (D := TH.S.digestBytes) L8 R8 hsi8 h108 hcx8
    (by omega_using [hk]) hk2 (by omega_using [hz])))
    fun t9 ⟨⟨L9, k9, hcx9, R9⟩, sp9, mx9, f9⟩ => ?_)
  have he9 : EnvD s t9 := he8.step k9.2.1 k9.2.2 sp9 (keep_cs3 k9 (by decide)) mx9 f9
  -- The shift.
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V5 TH.S.digestBytes) (upd W5 31 (accL V5 TH.S.digestBytes TH.S.digestBytes) 31)
    ((s.gpr .r8).toNat - (2 * TH.S.digestBytes + 1))
  refine WP.seq (WP.mono (wp_good shift_good (shift_ok L9 R9 hcx9 (idx := idx) (by simp only [upd]; exact hidx)
    (by omega_using [hk2, hidx']) (fun x h1 h2 => by
      simp only [cpV, clrV]
      rw [ifn (by omega_using [hk2, h1]), ifp (by omega_using [h2])])))
    fun t10 ⟨⟨L10, k10, V10, W10, R10, hW10, hB10, hO10⟩, sp10, mx10, f10⟩ => ?_)
  have he10 : EnvD s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  -- `ok`.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (okMask_ok L10 R10))
    fun t11 ⟨⟨L11, k11, h11, R11⟩, sp11, mx11, f11⟩ => ?_)
  have he11 : EnvD s t11 := he10.step k11.2.1 k11.2.2 sp11 (keep_cs3 k11 (by decide)) mx11 f11
  have W11e : ∀ j, j < nW → j ≠ 31 → j ≠ 32 → j ≠ 33 → j ≠ 34 → j ≠ 35 → j ≠ 36 →
      (upd W10 33 (okW W10)) j = W5 j := fun j hj h1 h2 h3 h4 h5 h6 => by
    simp only [upd, ifn h3]
    rw [hW10 j hj h4 h5 h6, w7k j h1 h2]
  have Wk : ∀ j ∈ decKs, (upd W10 33 (okW W10)) j = W j := fun j hj => by
    have hjn := decKs_lt j hj
    have hj := decKs_iff hj
    rw [W11e j hjn (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj]) (by omega_using [hj])
      (by omega_using [hj]) (by omega_using [hj])]
    exact W5e j (by omega_using [hj]) hjn (by omega_using [hj]) (by omega_using [hj])
  have hW11 : ArgsD s (upd W10 33 (okW W10)) := hW.of Wk
  obtain ⟨-, x21, -, x23, -, -, -, -, -, x29⟩ := hW11.w
  obtain ⟨-, -, -, -, -, x42, -⟩ := hW11.sel
  rw [← hDl] at x42
  -- `out`.
  have hout : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by simp [outR, hp.hsi]
  have aO : Apart (fb s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by
    rw [hout]; exact ⟨hp.dKO.sub_left (frame_subD s), hp.dOs.symm.sub_left sS, hp.dKO.sub_left (ret_subD s)⟩
  refine WP.seq (WP.mono (wp_good outLoop_good (outLoop_ok L11 R11 x21
    (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega_using [hk1]) hk2 (by rw [he11.wr, hout]; simp)
    (by have := hp.wO; rw [hp.hsi] at this; exact this) aO))
    fun t12 ⟨⟨L12, k12, R12, ho12, fo12⟩, sp12, mx12, f12⟩ => ?_)
  have he12 : EnvD s t12 := he11.step k12.2.1 k12.2.2 sp12 (keep_cs3 k12 (by decide)) mx12 f12
  -- The length and the result.
  have aM : Apart (fb s) (stackArg s 15) (mlR s) :=
    ⟨hp.dKM.sub_left (frame_subD s), hp.dMs.symm.sub_left sS, hp.dKM.sub_left (ret_subD s)⟩
  refine WP.mono (wp_good (block_good _ rfl rfl) (decRet_ok (D := TH.S.digestBytes) L12 R12 (pm := s.gpr .rdx)
    (k := (s.gpr .r8).toNat) x29 (by rw [x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) x42 (by omega_using [hk])
    (by rw [he12.wr]; simp [mlR]) hp.wM aM)) fun t13 ⟨⟨k13, hm13, hax13⟩, sp13, mx13, f13⟩ => ?_
  have he13 : EnvD s t13 := he12.step k13.2.1 k13.2.2 sp13 (keep_cs3 k13 (by decide)) mx13 f13
  refine ⟨he13, ?_⟩
  -- The bytes: `EM` unmasked, `lHash`, `T` and the buffer.
  have hlen : Hh.len = TH.S.digestBytes := hTH.len
  have hlhl : (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)).length = TH.S.digestBytes := by
    rw [hTH.valid.2, hlen]
  generalize hDD : TH.S.digestBytes = D at *
  generalize hkk : (s.gpr .r8).toNat = k at *
  have nl : ∀ x, x < oSt → ¬ inR (labR oLh) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oLh oW at *; omega_using [hx]
  have v1 : ∀ x < k, V1 x = V x := fun x hx => hV1 x (nl x (by unfold oSt; omega_using [hk2, hx]))
  have v3 : ∀ x < k, V3 x = mixV V1 (Spec.Mgf1.mgf1 Gh (srcB V1 (1 + D) (k - (D + 1))) D) 1 D x :=
    fun x hx => by rw [hV3 x (by unfold oRsa; omega_using [hk2, hx]) ((mOut_iff x).mpr (.inl (by unfold oSt; omega_using [hk2, hx])))]; rfl
  have v5 : ∀ x < k, V5 x = mixV V3 (Spec.Mgf1.mgf1 Gh (srcB V3 1 D) (k - (D + 1))) (1 + D) (k - (D + 1)) x :=
    fun x hx => by rw [hV5 x (by unfold oRsa; omega_using [hk2, hx]) ((mOut_iff x).mpr (.inl (by unfold oSt; omega_using [hk2, hx])))]; rfl
  have hc5 := chain_eq (by omega_using [hk]) v1 v3 v5
  have lh5 : ∀ i < D, V5 (oLh + i) =
      (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)).getD i 0 := fun i hi => by
    have mo : mOut (oLh + i) := (mOut_iff _).mpr (.inr (.inl (by unfold oLh oDig oCtr; omega_using [hz, hi])))
    rw [hV5 _ (by unfold oLh oRsa; omega_using [hk2, hk, hi]) mo, mixV, ifn (by unfold oLh oEm at *; omega_using [hk2]),
      hV3 _ (by unfold oLh oRsa; omega_using [hk2, hk, hi]) mo, mixV, ifn (by unfold oLh oEm at *; omega_using [hk2, hk]), hV1' i hi]
  -- `T` and the scan.
  have hTl : (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).length = k - (2 * D + 1) := by simp [srcB]
  have hTg : ∀ i < k - (2 * D + 1), (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).getD i 0 = tF V5 D i := fun i hi => by
    rw [srcB, map_range_getD' _ hi]; simp only [tF, c0]
  have hsc : scanS (tF V5 D) (upd W5 31 (accL V5 D D) 31) (k - (2 * D + 1)) =
      scanS (fun i => (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).getD i 0) (accL V5 D D)
        (srcB V5 (1 + 2 * D) (k - (2 * D + 1))).length := by
    rw [hTl, show upd W5 31 (accL V5 D D) 31 = accL V5 D D by simp [upd]]
    exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  rw [hsc] at hidx w7k hW10
  generalize hT : srcB V5 (1 + 2 * D) (k - (2 * D + 1)) = T at *
  generalize hsc' : scanS (fun i => T.getD i 0) (accL V5 D D) T.length = sc at *
  -- The frame's words at the end.
  have e30 : (upd W10 33 (okW W10)) 30 = W 30 := by
    rw [W11e 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact W5e 30 (by omega_using []) (by decide) (by decide) (by decide)
  have e31 : W10 31 = sc.2.2 ||| sc.1 := by
    rw [hW10 31 (by decide) (by decide) (by decide) (by decide)]; simp [upd]
  have e32 : (upd W10 33 (okW W10)) 32 = BitVec.ofNat 64 idx := by
    simp only [upd]; rw [ifn (by decide), hW10 32 (by decide) (by decide) (by decide) (by decide)]
    simp [upd, hidx]
  have e33 : (upd W10 33 (okW W10)) 33 = zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) := by
    simp only [upd, ite_true, okW]
    rw [e31, show W10 30 = W 30 from (show W10 30 = (upd W10 33 (okW W10)) 30 by simp [upd]).trans e30]
  -- The outputs.
  have hTl' : T.length = k - (2 * D + 1) := hTl
  have hbuf : ∀ x, bufB (cpV (clrV V5 oBuf 2048) (tF (clrV V5 oBuf 2048) D) oBuf (k - (2 * D + 1))) x =
      T.getD x 0 := fun x => by
    have hge : ∀ y, k - (2 * D + 1) ≤ y → T.getD y 0 = 0 := fun y hy => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show T.length ≤ y by omega_using [hTl', hy])]
    unfold bufB
    by_cases hx : x < 1024
    · rw [ifp hx, cpV]
      by_cases hxt : x < k - (2 * D + 1)
      · rw [ifp (by unfold oBuf; omega_using [hxt]), hTg x hxt, show oBuf + x - oBuf = x by omega_using [], tF, tF, clrV,
          ifn (by unfold oBuf oEm; omega_using [hk2, hxt])]
      · rw [ifn (by unfold oBuf; omega_using [hxt]), clrV, ifp (by unfold oBuf; omega_using [hx]), hge x (by omega_using [hxt])]
    · rw [ifn hx, hge x (by omega_using [hk2, hx])]
  have okv := zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)
  have hfm : Frame [⟨s.gpr .rdx, 8⟩] t12.mem t13.mem := by
    rw [hm13]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dom : Region.Disjoint ⟨s.gpr .rdi, k⟩ ⟨s.gpr .rdx, 8⟩ := by
    have := hp.dOM; rw [hp.hsi, hkk] at this; exact this
  have hout : ∀ i < k, t13.mem (s.gpr .rdi + BitVec.ofNat 64 i) =
      andB (T.getD (i + (idx + 1)) 0) (zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) := fun i hi => by
    rw [hfm.bytes (R := ⟨s.gpr .rdi, k⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dom)
      (show k ≤ 2 ^ 64 by omega_using [hsl]) hi, ho12 i hi, hB10 i (by omega_using [hk2, hi]), hbuf, e33]
  have hml : t13.mem.readW (s.gpr .rdx) 64 =
      (BitVec.ofNat 64 (k - (2 * D + 2)) - BitVec.ofNat 64 idx) &&& (zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) := by
    rw [hm13, Mem.readW_writeW_self64, e32, e33]
  have hrax : t13.gpr .rax = (zM (W 30 ^^^ 2) &&& 2) ||| ((zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1)) &&& 1) := by
    rw [hax13, faultW, e30, e33]
  -- The accumulator.
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) (accL V5 D D) T.length
  rw [hsc'] at i1 i4
  have hacc : sc.2.2 ||| sc.1 = 0 ↔
      accL V5 D D = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧ ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  have zero_out : zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) = 0 →
      Spec.Rsa.bytesAt t13.mem (s.gpr .rdi) k = Spec.RsaOaep.zeros k ∧ t13.mem.readW (s.gpr .rdx) 64 = 0 ∧
      (t13.gpr .rax).setWidth 32 = (zM (W 30 ^^^ 2) &&& 2).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml, h0]; exact BitVec.and_zero,
      by rw [hrax, h0, show (0 : BitVec 64) &&& 1 = 0 by decide,
        show ∀ x : BitVec 64, x ||| 0 = x from fun x => by simp]⟩
  cases o with
  | fault =>
    have h2 : W 30 = 2 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h2, show zM ((2 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.zero_and)
    exact ⟨by rw [c, h2]; decide, a, b⟩
  | invalid =>
    have h0 : W 30 = 0 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h0, show zM ((0 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.zero_and)
    exact ⟨by rw [c, h0]; decide, a, b⟩
  | ok em =>
    obtain ⟨h1, hem⟩ := hres
    subst hem
    have hV : (fun i => V (oEm + i)) = V := funext fun i => by rw [c0, Nat.zero_add]
    rw [hV]
    have hok : zM (W 30 ^^^ 1) &&& zM (sc.2.2 ||| sc.1) = zM (sc.2.2 ||| sc.1) := by
      rw [h1, show zM ((1 : BitVec 64) ^^^ 1) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
    have hf2 : zM (W 30 ^^^ 2) &&& 2 = 0 := by rw [h1]; decide
    rw [hok] at zero_out hout hml hrax
    rw [hf2, show ∀ x : BitVec 64, 0 ||| x = x from fun x => by simp] at hrax
    simp only [decOut]
    rw [decode_eq (H := Hh) hTG.valid _ (by omega_using [hk]) hlen hc5, hT]
    have hz : ∀ (hne : sc.2.2 ||| sc.1 ≠ 0), _ := fun hne => zero_out (by simp only [zM]; rw [ifn hne])
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T (accL V5 D D) hfd.1 hfd.2
      rw [hsc'] at hsj
      have hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsl, hidx']),
          Nat.mod_eq_of_lt (by omega_using [hsl, hTl', hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      have hV0 : V5 0 = V 0 := by
        rw [hc5 0 (by omega_using [hTl', hj₀]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      have htake : ((List.range k).map V).take 1 = [V 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hTl', hj₀], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V).take 1 = [0x00] ∧ srcB V5 (1 + D) D =
          Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 12).toNat)
      · rw [ifp hc]
        have hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨(accL_eq_zero V5 D D).mpr ⟨by
            rw [c0, hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            rw [lh5 i hi, ← hc.2, srcB, map_range_getD' _ hi, c0]⟩, hfd.2, hfd.1⟩
        have hzm : zM (sc.2.2 ||| sc.1) = BitVec.allOnes 64 := by simp only [zM]; rw [ifp hacc0]
        rw [hzm] at hout hml hrax
        refine ⟨by rw [hrax]; decide, out_list (by omega_using [hTl']) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_using [hTl', hj₀]), List.length_drop]
        congr 1; omega_using [hTl']
      · rw [ifn hc]
        have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hc ⟨by
            rw [htake, ← hV0, show (0 : Nat) = oEm from rfl, ((accL_eq_zero V5 D D).mp (hacc.mp h0).1).1],
          by
            refine srcB_eq hlhl fun i hi => ?_
            rw [← lh5 i hi, ((accL_eq_zero V5 D D).mp (hacc.mp h0).1).2 i hi, c0]⟩
        obtain ⟨a, b, c⟩ := hz hne
        exact ⟨by rw [c, hf2]; rfl, a, b⟩
    · have hfail := scan_fail T (by
        by_contra hc; exact hfd ⟨fun h => hc (.inl h), fun h => hc (.inr h)⟩)
      have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => hfd ⟨(hacc.mp h0).2.2, (hacc.mp h0).2.1⟩
      obtain ⟨a, b, c⟩ := hz hne
      split
      · rename_i m heq
        split at heq
        · rename_i m' hm; exact absurd hm (hfail m')
        · cases heq
      · exact ⟨by rw [c, hf2]; rfl, a, b⟩

end VG.Proof.RsaOaep.X86_64
