module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
public import VerifiedGarbage.Proof.RsaOaep.Encode
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub

/-!
# RSAES-OAEP encryption on x86-64: after the checks

`EM` written and masked in our working space (`encMask_ok`), before the
public operation's call (`PcCorrect`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)
open VG.Proof.HashFns (StreamingOK)

/-- In the frame, from the entry state `s`: what the calls need of the
state too (`World`, and what the function writes being the entry's own). -/
structure EnvE (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, outR s, scrR s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrE s t.mem
  world : World encStack s t
  own : Owned encStack s [frR s, outR s, scrR s, below (fb s) 16]
  scr : Owned encStack s [⟨stackArg s 6, oRsa⟩]
  sp16 : 16 ≤ (fb s).toNat

theorem EnvE.step {s t t' : State} (he : EnvE s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (hf : StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t') : EnvE s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    hmx.trans he.mx, FrE.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf.frame),
    he.world.step hf.funs hf.syms hf.frame (by rw [he.wr, he.rsp]; exact he.own), he.own, he.scr, he.sp16⟩

/-- What the calls of the streaming functions need. -/
theorem EnvE.here {s t : State} (he : EnvE s t) : Here encStack s t (fb s) (stackArg s 6) :=
  ⟨he.world, fun r hr => he.own r (List.subset_append_left _ [below (fb s) 16] (he.wr ▸ hr)), he.scr,
    fun r hr => he.own r (List.subset_append_right [frR s, outR s, scrR s] _ hr), he.sp16⟩

theorem keep_cs3 {u v : State} {rs : List Reg} (k : Keep rs u v)
    (h : rs.all (fun r => !calleeSaved.contains r) = true) : ∀ r ∈ calleeSaved, r ≠ .rsp → v.gpr r = u.gpr r :=
  fun r hr _ => k.gpr (cs_disj rs h r hr)

theorem ne_of_disjoint {A B : Region} (hd : A.Disjoint B) {a b : Addr} (ha : A.Contains a 1) (hb : B.Contains b 1) :
    a ≠ b := fun h => hd a ha (h ▸ hb)

/-- A byte of a region apart from what the function writes, as on entry. -/
theorem FrE.byte {s : State} {m : Mem} (h : FrE s m) {p : Addr} {n : Nat} (hk : (stkR s).Disjoint ⟨p, n⟩)
    (ho : (outR s).Disjoint ⟨p, n⟩) (hs : (scrR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
  have := congrArg (fun l => l.getD i 0) (FrE.bytes h hk ho hs hn)
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] using this

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The function's argument slots, as the prologues stored them. -/
def ArgsW (s : State) (W : Nat → BitVec 64) : Prop :=
  ∀ k, k = 14 ∨ (21 ≤ k ∧ k ≤ 31) ∨ (37 ≤ k ∧ k ≤ 43) ∨ (45 ≤ k ∧ k ≤ 50) → W k = encW s k

theorem ArgsW.w {s : State} {W : Nat → BitVec 64} (h : ArgsW s W) :
    W 14 = stackArg s 6 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rdx ∧ W 23 = s.gpr .rcx ∧ W 24 = s.gpr .r8 ∧
    W 25 = s.gpr .r9 ∧ W 26 = stackArg s 7 ∧ W 27 = stackArg s 0 ∧ W 28 = stackArg s 1 ∧
    W 29 = stackArg s 2 ∧ W 30 = stackArg s 3 ∧ W 31 = stackArg s 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by omega_using [])]; simp [encW, fnW, selW, encPW, upd])

/-- The selectors' slots, and the lengths of the hash functions they name. -/
theorem ArgsW.sel {s : State} {W : Nat → BitVec 64} (h : ArgsW s W) :
    W 37 = BitVec.ofNat 64 (selH s) ∧ W 38 = BitVec.ofNat 64 (selG s) ∧
    W 39 = BitVec.ofNat 64 (lenOf (selH s)) ∧ W 40 = BitVec.ofNat 64 (lenOf (selH s) + 1) ∧
    W 41 = BitVec.ofNat 64 (2 * lenOf (selH s) + 1) ∧ W 42 = BitVec.ofNat 64 (2 * lenOf (selH s) + 2) ∧
    W 43 = BitVec.ofNat 64 (lenOf (selG s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by omega_using [])]; simp [encW, fnW, selW, upd])

/-- The slots of the tables' words. -/
theorem ArgsW.fn {s : State} {W : Nat → BitVec 64} (h : ArgsW s W) :
    (W 45 = tw s.mem (tabH s) 0 ∧ W 46 = tw s.mem (tabH s) 1 ∧ W 47 = tw s.mem (tabH s) 2) ∧
    (W 48 = tw s.mem (tabG s) 0 ∧ W 49 = tw s.mem (tabG s) 1 ∧ W 50 = tw s.mem (tabG s) 2) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by omega_using [])]; simp [encW, fnW, upd])

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

/-- The streaming functions of the table `j` (12 or 13) of the entry `s`. -/
abbrev FnsOf (s : State) (T : Spec.HashFns.Streaming) (j : Nat) : Prop :=
  Fns encStack s T (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1) (tw s.mem (stackArg s j) 2)

theorem lenOf_eq {i : Nat} {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)
    (e : Spec.HashId.mgf1 i = some Hh) : T.S.digestBytes = lenOf i := by
  simp [lenOf, e, hT.len]

include hTH in
theorem encEm_ok {s t : State} (fH : FnsOf s TH 12) (eH : Spec.HashId.mgf1 (selH s) = some Hh)
    (hp : EPre Hh s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 6))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * TH.S.digestBytes + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa encEm t fun t' => EnvE s t' ∧ Lay t' (fb s) (stackArg s 6) ∧
      ∃ V', Rep t'.mem (fb s) (stackArg s 6) V' W ∧
        EmAt V' (s.gpr .rcx).toNat TH.S.digestBytes (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len)
          (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) (stackArg s 3).toNat := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  obtain ⟨-, -, w39, -, -, -, -⟩ := hW.sel
  obtain ⟨fn, -⟩ := hW.fn
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have hD := hTH.pos; have hDN := hTH.digest; have hN := hTH.out
  have hlen : Hh.len = TH.S.digestBytes := hTH.len
  have hDl : TH.S.digestBytes = lenOf (selH s) := lenOf_eq hTH eH
  rw [← hDl] at w39
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  have cD : oDig = 3328 := rfl
  have cW : oW = 4096 := rfl
  -- What reads the caller's buffers needs.
  have scrC : ∀ {o : Nat}, o < oRsa → (scrR s).Contains (off (stackArg s 6) o) 1 := fun ho =>
    Offset.contains_base _ (by unfold oRsa at ho; omega_using [hsl, ho]) (by unfold oRsa at ho; omega_using [ho])
  unfold encEm seqs seqs seqs seqs
  -- `EM`'s place cleared.
  refine WP.seq (WP.mono (wp_good clearEm_good (clearEm_ok L R)) fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_)
  have he1 : EnvE s t1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  -- The seed.
  refine WP.seq (WP.mono (wp_good copySeed_good (copySeed_ok L1 R1 w31 w39 hD (by omega_using [hDN, hN])
    (fun i hi => hp.rd_in he1.rd (by simp [rdL]) (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := Hh.len) (by omega_using [hlen, hi]) (by omega_using [hDN, hN, hi])))
    (fun i hi j hj => ne_of_disjoint hp.d_sd_scr (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := Hh.len) (by omega_using [hlen, hi]) (by omega_using [hDN, hN, hi])) (scrC
          (by unfold oRsa; omega_using [hDN, hN, c0, hj])))))
    fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ => ?_)
  have he2 : EnvE s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  -- The label's hash.
  have hll : W 28 = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sS : Region.Sub ⟨stackArg s 6, oRsa⟩ (scrR s) := Region.sub_prefix (by unfold oRsa; omega_using [hsl])
  have A2 : LabAt t2 (fb s) (stackArg s 6) W (stackArg s 0) (stackArg s 1).toNat :=
    ⟨w27, hll, (stackArg s 1).isLt, Covers.left (by
        rw [he2.rd]; exact (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [rdL]).trans hp.hrd),
      (hp.d_lb_scr.sub_right sS), (hp.d_stk_lb.sub_left (ret_sub s))⟩
  refine WP.seq (WP.mono (wp_good (hashLabel_good oDig)
    (hashLabel_ok hTH fH (Hs := Hh) (congrFun hTH.hash) he2.here L2 R2 A2 hp.wL
      (hp.rdIn (r := ⟨stackArg s 0, (stackArg s 1).toNat⟩) (by simp [rdL])) fn (Or.inl rfl)))
    fun t3 ⟨⟨L3, _, rd3, wr3, cs3, V3, R3, hV3, hV3'⟩, sp3, mx3, f3⟩ => ?_)
  have he3 : EnvE s t3 := he2.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3
  have hlab : Spec.Rsa.bytesAt t2.mem (stackArg s 0) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat :=
    FrE.bytes he2.fr hp.d_stk_lb hp.d_out_lb hp.d_lb_scr.symm (by have := hp.wL; omega_using [])
  rw [hlab] at hV3'
  -- `lHash` after the seed.
  refine WP.seq (WP.mono (wp_good copyLh_good (copyLh_ok L3 R3 w39 hD (by omega_using [hDN, hN])))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 : EnvE s t4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  -- `0x01` and the message.
  have hmA : ∀ i < (stackArg s 3).toNat, (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Contains
      (stackArg s 2 + BitVec.ofNat 64 i) 1 := fun i hi => Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  refine WP.mono (wp_good putMsg_good (putMsg_ok L4 R4 (k := (s.gpr .rcx).toNat) (mLen := (stackArg s 3).toNat)
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w29
    (by omega_using [hk]) hk2 (fun i hi => hp.rd_in he4.rd (by simp [rdL]) (hmA i hi))
    (fun i hi j hj => ne_of_disjoint hp.d_ms_scr (hmA i hi) (scrC (by unfold oRsa; omega_using [hk, hk2, hj])))))
    fun t5 ⟨⟨L5, k5, R5⟩, sp5, mx5, f5⟩ => ?_
  have he5 : EnvE s t5 := he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5
  have nl : ∀ x, x < oSt → ¬ inR (labR oDig) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; omega_using [cS, cD, cW, hx]
  refine ⟨he5, L5, _, R5, ?_⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · simp only [cpV, upd]
    rw [ifn (by omega_using []), ifn (by omega_using [hk]), ifn (by unfold oEm; omega_using []), hV3 _ (nl _ (by omega_using [cS]))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega_using []), ifp (by unfold oEm; omega_using [])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [hk, hi]), ifn (by omega_using [hk, hi]), ifn (by unfold oEm; omega_using [hi]),
        hV3 _ (nl _ (by omega_using [hDN, hN, cS, hi]))]
    simp only [cpV]
    rw [ifp (by unfold oEm; omega_using [hi]), show 1 + i - (oEm + (oEm + 1)) = i by unfold oEm; omega_using [],
      FrE.byte he1.fr hp.d_stk_sd hp.d_out_sd hp.d_sd_scr.symm (by have := hp.wSd; omega_using [this]) (by omega_using [hlen, hi]),
      bytesAt_getD _ _ (by omega_using [hlen, hi])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [hk, hi]), ifn (by omega_using [hk, hi]), ifp (by unfold oEm; omega_using [hi]),
      show 1 + TH.S.digestBytes + i - (oEm + (oEm + 1 + TH.S.digestBytes)) = i by unfold oEm; omega_using [], hV3' i (by omega_using [hi])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [h2]), ifn (by omega_using [h2]), ifn (by unfold oEm; omega_using [h1]),
        hV3 _ (nl _ (by omega_using [hk2, cS, h2]))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega_using [h1]), ifp (by unfold oEm; omega_using [hk2, h2])]
  · simp only [cpV, upd]
    rw [ifn (by omega_using [])]; rfl
  · simp only [cpV]
    rw [ifp (by omega_using [hk, hi]), show (s.gpr .rcx).toNat - (stackArg s 3).toNat + i -
      ((s.gpr .rcx).toNat - (stackArg s 3).toNat - 1 + 1) = i by omega_using [hk],
      FrE.byte he4.fr hp.d_stk_ms hp.d_out_ms hp.d_ms_scr.symm (by have := hp.wM; omega_using []) hi,
      bytesAt_getD _ _ hi]

include hTH hTG in
/-- `EM` built and masked, then `rest`, from the state with the arguments of
the public operation's call to make: `EnvE`, the slots, and `EM` in the
working space. -/
theorem encMask_ok {s t : State} (fH : FnsOf s TH 12) (fG : FnsOf s TG 13)
    (eH : Spec.HashId.mgf1 (selH s) = some Hh) (eG : Spec.HashId.mgf1 (selG s) = some Gh)
    (hp : EPre Hh s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 6))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 6) V W) (hW : ArgsW s W)
    (hk : 2 * TH.S.digestBytes + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) {rest : Prog isa} {Q : State → Prop}
    (hrest : ∀ t9 V9 W9, EnvE s t9 → Lay t9 (fb s) (stackArg s 6) → Rep t9.mem (fb s) (stackArg s 6) V9 W9 →
      (∀ k, 21 ≤ k → k ≤ 26 → W9 k = encW s k) →
      (List.range (s.gpr .rcx).toNat).map (fun i => V9 (oEm + i)) =
        emOf Gh TH.S.digestBytes (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len)
          (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) → WP isa rest t9 Q) :
    WP isa (.seq encEm (.seq (.block dbArgs) (.seq (mgfXor lay)
      (.seq (.block seedArgs) (.seq (mgfXor lay) rest))))) t Q := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  obtain ⟨-, -, w39, w40, -, -, w43⟩ := hW.sel
  obtain ⟨-, fn⟩ := hW.fn
  have hDl : TH.S.digestBytes = lenOf (selH s) := lenOf_eq hTH eH
  have hGl : TG.S.digestBytes = lenOf (selG s) := lenOf_eq hTG eG
  rw [← hDl] at w39 w40
  rw [← hGl] at w43
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hTH.pos
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  have w23' : W 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- `EM` before masking.
  refine WP.seq (WP.mono (encEm_ok hTH fH eH hp he L R hW hk) fun t5 ⟨he5, L5, V5, R5, E⟩ => ?_)
  -- `DB` masked.
  refine WP.seq (WP.mono (wp_good dbArgs_good (dbArgs_ok L5 R5 w23' w39 w40 (by omega_using [hk])))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_)
  have he6 : EnvE s t6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  refine WP.seq (WP.mono (wp_good mgfXor_good (mgfXor_ok hTG fG (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid
        he6.here L6 R6 ⟨by unfold oEm oSt; omega_using [hk, hk2], by unfold oEm oSt; omega_using [hk, hk2], by omega_using [], by omega_using [hk], by omega_using [hk2]⟩
    (mW_args _ _ _ _ _ _) ⟨(mW_other (by omega_using [])).trans fn.1, (mW_other (by omega_using [])).trans fn.2.1,
      (mW_other (by omega_using [])).trans fn.2.2⟩ ((mW_other (by omega_using [])).trans w43)))
    fun t7 ⟨⟨L7, _, rd7, wr7, cs7, V7, W7, R7, hW7, hV7⟩, sp7, mx7, f7⟩ => ?_)
  have he7 : EnvE s t7 := he6.step rd7 wr7 sp7 (fun r hr _ => cs7 r hr) mx7 f7
  have W7e : ∀ k, (k < 15 ∨ 18 < k) → k < nW → k ≠ 19 → k ≠ 20 → W7 k = W k := fun k h1 h2 h3 h4 =>
    (hW7 k h2 h3 h4).trans (mW_other h1)
  -- The seed masked.
  refine WP.seq (WP.mono (wp_good seedArgs_good (seedArgs_ok L7 R7
    ((W7e 23 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w23')
        ((W7e 39 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w39)
        ((W7e 40 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w40)
        (by omega_using [hk])))
    fun t8 ⟨⟨L8, k8, R8⟩, sp8, mx8, f8⟩ => ?_)
  have he8 : EnvE s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  have W7f : ∀ k, 45 ≤ k → k ≤ 50 → W7 k = W k := fun k h1 h2 =>
    W7e k (by omega_using [h1]) (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1])
  refine WP.seq (WP.mono (wp_good mgfXor_good (mgfXor_ok hTG fG (Gs := Gh) (congrFun hTG.hash) hTG.len hTG.valid
        he8.here L8 R8 ⟨by unfold oEm oSt; omega_using [hk, hk2], by unfold oEm oSt; omega_using [hk, hk2], by omega_using [], by omega_using [hD], by omega_using [hk, hk2]⟩
    (mW_args _ _ _ _ _ _)
    ⟨(mW_other (by omega_using [])).trans ((W7f 48 (by omega_using []) (by omega_using [])).trans fn.1),
      (mW_other (by omega_using [])).trans ((W7f 49 (by omega_using []) (by omega_using [])).trans fn.2.1),
      (mW_other (by omega_using [])).trans ((W7f 50 (by omega_using []) (by omega_using [])).trans fn.2.2)⟩
    ((mW_other (by omega_using [])).trans ((W7e 43 (by omega_using []) (by decide) (by omega_using []) (by omega_using [])).trans w43)))) fun t9 ⟨⟨L9, _, rd9, wr9, cs9, V9, W9, R9, hW9, hV9⟩, sp9, mx9, f9⟩ => ?_)
  have he9 : EnvE s t9 := he8.step rd9 wr9 sp9 (fun r hr _ => cs9 r hr) mx9 f9
  -- The call.
  have W9e : ∀ k, 21 ≤ k → k ≤ 26 → W9 k = encW s k := fun k h1 h2 => by
    rw [hW9 k (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1]), mW_other (by omega_using [h1]),
      W7e k (by omega_using [h1]) (by unfold nW frameBytes; omega_using [h2]) (by omega_using [h1]) (by omega_using [h1])]
    exact hW k (.inr (.inl ⟨h1, by omega_using [h2]⟩))
  have e1 : (s.gpr .rcx).toNat - (TH.S.digestBytes + 1) = (s.gpr .rcx).toNat - TH.S.digestBytes - 1 := by omega_using []
  rw [e1] at hV7 hV9
  have hm : ∀ o, o < (s.gpr .rcx).toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by omega_using [hk2, cS, ho]))
  have hlen : Hh.len = TH.S.digestBytes := hTH.len
  have hsdl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len).length = TH.S.digestBytes := by simp [Spec.Rsa.bytesAt, hlen]
  have hlhl : (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).length = TH.S.digestBytes := by
    rw [hTH.valid.2, hlen]
  have hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hsrc : srcB V7 (oEm + 1 + TH.S.digestBytes) ((s.gpr .rcx).toNat - TH.S.digestBytes - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 Gh (srcB V5 1 TH.S.digestBytes) ((s.gpr .rcx).toNat - TH.S.digestBytes - 1)) (1 + TH.S.digestBytes)
        ((s.gpr .rcx).toNat - TH.S.digestBytes - 1)) (1 + TH.S.digestBytes) ((s.gpr .rcx).toNat - TH.S.digestBytes - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega_using [hk2, c0, this]) (hm _ (by unfold oEm; omega_using [this]))
  have hlist : (List.range (s.gpr .rcx).toNat).map (fun i => V9 (oEm + i)) =
      emOf Gh TH.S.digestBytes (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) Hh.len)
        (Hh.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) := by
    unfold emOf
    rw [← em_mask hTG.valid (V₁ := V5) (by omega_using [hk]) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega_using [hk])
      E.z0 E.sd (E.db hlhl hml hk)]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [show oEm + i = i by unfold oEm; omega_using [], hV9 _ (by unfold oRsa; omega_using [hk2, hi']) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by unfold oRsa; omega_using [hk2, hi']) (hm _ hi'))
  exact hrest t9 V9 W9 he9 L9 R9 W9e hlist

end VG.Proof.RsaOaep.X86_64
