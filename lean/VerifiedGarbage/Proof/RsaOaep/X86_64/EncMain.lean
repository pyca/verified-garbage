import VerifiedGarbage.Proof.RsaOaep.X86_64.EncCall
import VerifiedGarbage.Proof.RsaOaep.X86_64.Good
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.Decode

/-!
# RSAES-OAEP encryption on x86-64: after the checks

`encMain` (`encMain_ok`): `EM` written and masked in our working space, then
`vg_rsa_public_checked` of it into `out`: the encryption.
-/

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp ix at_ step byteLoop seqs mgfXor)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.RsaPkcs1Sig.X86_64 (pubChecked)

theorem valid_of_link {H : Hash} (hH : HashOK H) (l : MgfLink H hH) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact hH.hD0, fun x => by
    rw [l.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, l.len]
    exact Nat.min_eq_left hH.hDN⟩

/-- In the frame, from the entry state `s`. -/
structure EnvE (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = [frR s, outR s, scrR s]
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : FrE s t.mem

theorem EnvE.step {s t t' : State} (he : EnvE s t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t'.gpr r = t.gpr r)
    (hmx : t'.mxcsr = t.mxcsr) (hf : Frame (t.wr ++ [below (t.gpr .rsp) 16]) t.mem t'.mem) : EnvE s t' :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, fun r hr h => (hcs r hr h).trans (he.cs r hr h),
    by rw [hmx]; exact he.mx, FrE.step he.fr (ws := t.wr) he.wr (by rw [he.rsp] at hf; exact hf)⟩

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

/-- The function's argument slots, as the prologue stored them. -/
def ArgsW (s : State) (W : Nat → BitVec 64) : Prop := ∀ k, k = 14 ∨ (21 ≤ k ∧ k ≤ 31) → W k = encW s k

theorem ArgsW.w {s : State} {W : Nat → BitVec 64} (h : ArgsW s W) :
    W 14 = stackArg s 5 ∧ W 21 = s.gpr .rdi ∧ W 22 = s.gpr .rdx ∧ W 23 = s.gpr .rcx ∧ W 24 = s.gpr .r8 ∧
    W 25 = s.gpr .r9 ∧ W 26 = stackArg s 6 ∧ W 27 = stackArg s 0 ∧ W 28 = stackArg s 1 ∧
    W 29 = stackArg s 2 ∧ W 30 = stackArg s 3 ∧ W 31 = stackArg s 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by omega)]; simp [encW, upd])

variable {Hl Gm : Hash} (hH : HashOK Hl) (KH : Callees Hl) (hG : HashOK Gm) (KG : Callees Gm)
  (mH : MgfLink Hl hH) (mG : MgfLink Gm hG)

/-- `EM` before masking: `0x00 ‖ seed ‖ lHash ‖ 0…0 ‖ 0x01 ‖ M`, in our working space. -/
structure EmAt (V : Nat → Byte) (k D : Nat) (sd lh m : List Byte) (mLen : Nat) : Prop where
  z0 : V 0 = 0
  sd : ∀ i < D, V (1 + i) = sd.getD i 0
  lh : ∀ i < D, V (1 + D + i) = lh.getD i 0
  ps : ∀ i, 1 + 2 * D ≤ i → i < k - mLen - 1 → V i = 0
  one : V (k - mLen - 1) = 1
  msg : ∀ i < mLen, V (k - mLen + i) = m.getD i 0

include hH KH mH in
theorem encEm_ok {s t : State} (hp : EPre mH.G s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 5))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 5) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (encEm Hl.stream) t fun t' => EnvE s t' ∧ Lay t' (fb s) (stackArg s 5) ∧
      ∃ V', Rep t'.mem (fb s) (stackArg s 5) V' W ∧
        EmAt V' (s.gpr .rcx).toNat Hl.D (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
          (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) (stackArg s 3).toNat := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  have hk1 := hp.k1; have hk2 := hp.k2; have hsl := hp.hsl; have wS := hp.wS
  have hD := hH.hD0; have hDN := hH.hDN; have hN := hH.N_le
  have hlen : mH.G.len = Hl.D := mH.len
  have hsD : Hl.stream.D = Hl.D := rfl
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  have cD : oDig = 3328 := rfl
  have cW : oW = 4096 := rfl
  -- What reads the caller's buffers needs.
  have inRd : ∀ {t' : State} {r : Region}, t'.rd = s.rd → r ∈ s.rd → ∀ {a : Addr} {n : Nat}, r.Contains a n →
      InRegions (t'.rd ++ t'.wr) a n := fun h1 h2 _ _ h3 => ⟨_, List.mem_append_left _ (by rw [h1]; exact h2), h3⟩
  have scrC : ∀ {o : Nat}, o < oRsa → (scrR s).Contains (off (stackArg s 5) o) 1 := fun ho =>
    Offset.contains_base _ (by unfold oRsa at ho; omega) (by unfold oRsa at ho; omega)
  unfold encEm seqs seqs seqs seqs
  -- `EM`'s place cleared.
  refine WP.seq (WP.mono (wp_good clearEm_good (clearEm_ok L R)) fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_)
  have he1 : EnvE s t1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  -- The seed.
  refine WP.seq (WP.mono (wp_good (copySeed_good _) (copySeed_ok (H := Hl.stream) L1 R1 w31 hD (by omega)
    (fun i hi => inRd he1.rd (by rw [hp.hrd]; simp) (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := mH.G.len) (by omega) (by omega)))
    (fun i hi j hj => ne_of_disjoint hp.d_sd_scr (Offset.contains_base (stackArg s 4) (d := i) (n := 1)
      (k := mH.G.len) (by omega) (by omega)) (scrC (by unfold oRsa; omega)))))
    fun t2 ⟨⟨L2, k2, R2⟩, sp2, mx2, f2⟩ => ?_)
  have he2 : EnvE s t2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  -- The label's hash.
  have hll : W 28 = BitVec.ofNat 64 (stackArg s 1).toNat := by rw [w28, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sS : Region.Sub ⟨stackArg s 5, oRsa⟩ (scrR s) := Region.sub_prefix (by unfold oRsa; omega)
  have A2 : LabAt t2 (fb s) (stackArg s 5) W (stackArg s 0) (stackArg s 1).toNat :=
    ⟨w27, hll, (stackArg s 1).isLt, Covers.left (Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr, he2.rd, hp.hrd]; simp),
      (hp.d_lb_scr.sub_right sS), (hp.d_stk_lb.sub_left (ret_sub s))⟩
  refine WP.seq (WP.mono (wp_good (hashLabel_good (HGood.of hH KH) oDig)
    (hashLabel_ok hH.stream (Hs := mH.G) mH.hash L2 R2 A2 (Or.inl rfl)))
    fun t3 ⟨⟨L3, rd3, wr3, cs3, V3, R3, hV3, hV3'⟩, sp3, mx3, f3⟩ => ?_)
  have he3 : EnvE s t3 := he2.step rd3 wr3 sp3 (fun r hr _ => cs3 r hr) mx3 f3
  have hlab : Spec.Rsa.bytesAt t2.mem (stackArg s 0) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat :=
    FrE.bytes he2.fr hp.d_stk_lb hp.d_out_lb hp.d_lb_scr.symm (by have := hp.wL; omega)
  rw [hlab] at hV3'
  -- `lHash` after the seed.
  refine WP.seq (WP.mono (wp_good (copyLh_good _) (copyLh_ok (H := Hl.stream) L3 R3 hD (by omega)))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 : EnvE s t4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  -- `0x01` and the message.
  have hmA : ∀ i < (stackArg s 3).toNat, (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Contains
      (stackArg s 2 + BitVec.ofNat 64 i) 1 := fun i hi => Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (wp_good putMsg_good (putMsg_ok L4 R4 (k := (s.gpr .rcx).toNat) (mLen := (stackArg s 3).toNat)
    (by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by rw [w30, BitVec.ofNat_toNat, BitVec.setWidth_eq]) w29
    (by omega) hk2 (fun i hi => inRd he4.rd (by rw [hp.hrd]; simp) (hmA i hi))
    (fun i hi j hj => ne_of_disjoint hp.d_ms_scr (hmA i hi) (scrC (by unfold oRsa; omega)))))
    fun t5 ⟨⟨L5, k5, R5⟩, sp5, mx5, f5⟩ => ?_
  have he5 : EnvE s t5 := he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5
  have nl : ∀ x, x < oSt → ¬ inR (labR oDig) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; omega
  refine ⟨he5, L5, _, R5, ?_⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_, ?_, fun i hi => ?_⟩
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by omega))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega), ifp (by unfold oEm; omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by omega))]
    simp only [cpV]
    rw [ifp (by unfold oEm; omega), show 1 + i - (oEm + (oEm + 1)) = i by unfold oEm; omega,
      FrE.byte he1.fr hp.d_stk_sd hp.d_out_sd hp.d_sd_scr.symm (by have := hp.wSd; omega) (by omega),
      bytesAt_getD _ _ (by omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifp (by unfold oEm; omega),
      show 1 + Hl.D + i - (oEm + (oEm + 1 + Hl.stream.D)) = i by unfold oEm; omega, hV3' i (by omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega), ifn (by omega), ifn (by unfold oEm; omega), hV3 _ (nl _ (by omega))]
    simp only [cpV, clrV]
    rw [ifn (by unfold oEm; omega), ifp (by unfold oEm; omega)]
  · simp only [cpV, upd]
    rw [ifn (by omega)]; rfl
  · simp only [cpV]
    rw [ifp (by omega), show (s.gpr .rcx).toNat - (stackArg s 3).toNat + i -
      ((s.gpr .rcx).toNat - (stackArg s 3).toNat - 1 + 1) = i by omega,
      FrE.byte he4.fr hp.d_stk_ms hp.d_out_ms hp.d_ms_scr.symm (by have := hp.wM; omega) hi,
      bytesAt_getD _ _ hi]

/-- `DB`, from `EM` before masking. -/
theorem EmAt.db {V : Nat → Byte} {k D : Nat} {sd lh m : List Byte} {mLen : Nat} (h : EmAt V k D sd lh m mLen)
    (hlh : lh.length = D) (hm : m.length = mLen) (hk : 2 * D + 2 + mLen ≤ k) :
    ∀ i < k - D - 1, V (1 + D + i) = (lh ++ Spec.RsaOaep.zeros (k - mLen - 2 * D - 2) ++ 0x01 :: m).getD i 0 := by
  intro i hi
  have hz : (Spec.RsaOaep.zeros (k - mLen - 2 * D - 2)).length = k - mLen - 2 * D - 2 := by
    simp [Spec.RsaOaep.zeros]
  rw [Proof.Mgf1.getD_append, List.length_append, hlh, hz]
  by_cases h1 : i < D + (k - mLen - 2 * D - 2)
  · rw [ifp h1, Proof.Mgf1.getD_append, hlh]
    by_cases h2 : i < D
    · rw [ifp h2]; exact h.lh i h2
    · rw [ifn h2, h.ps _ (by omega) (by omega)]
      simp only [Spec.RsaOaep.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      rw [ifp (by omega)]; rfl
  · rw [ifn h1]
    by_cases h3 : i = D + (k - mLen - 2 * D - 2)
    · subst h3; rw [Nat.sub_self, show 1 + D + (D + (k - mLen - 2 * D - 2)) = k - mLen - 1 by omega, h.one]; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = D + (k - mLen - 2 * D - 2) + 1 + j := ⟨i - (D + (k - mLen - 2 * D - 2) + 1), by omega⟩
      rw [show D + (k - mLen - 2 * D - 2) + 1 + j - (D + (k - mLen - 2 * D - 2)) = j + 1 by omega,
        show 1 + D + (D + (k - mLen - 2 * D - 2) + 1 + j) = k - mLen + j by omega, h.msg j (by omega)]
      simp [List.getD_eq_getElem?_getD]

/-- `EM`: `0x00 ‖ maskedSeed ‖ maskedDB`. -/
def emOf (G : Spec.Mgf1.Hash) (D k mLen : Nat) (sd lh m : List Byte) : List Byte :=
  let db := lh ++ Spec.RsaOaep.zeros (k - mLen - 2 * D - 2) ++ 0x01 :: m
  let mdb := Spec.Mgf1.xorBytes db (Spec.Mgf1.mgf1 G sd (k - D - 1))
  0 :: Spec.Mgf1.xorBytes sd (Spec.Mgf1.mgf1 G mdb D) ++ mdb

include hH KH hG KG mH mG in
theorem encMain_ok {s t : State} (hp : EPre mH.G s) (he : EnvE s t) (L : Lay t (fb s) (stackArg s 5))
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep t.mem (fb s) (stackArg s 5) V W) (hW : ArgsW s W)
    (hk : 2 * Hl.D + 2 + (stackArg s 3).toNat ≤ (s.gpr .rcx).toNat) :
    WP isa (encMain Hl.stream Gm.stream pubChecked.name pubChecked.code) t fun t' => EnvE s t' ∧
      Spec.Rsa.written t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
            (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
            (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat))) := by
  obtain ⟨w14, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hW.w
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD := hH.hD0
  have hsD : Hl.stream.D = Hl.D := rfl
  have hgD : Gm.stream.D = Gm.D := rfl
  have c0 : oEm = 0 := rfl
  have cS : oSt = 3072 := rfl
  have w23' : W 23 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by rw [w23, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold encMain seqs seqs seqs seqs seqs seqs
  -- `EM` before masking.
  refine WP.seq (WP.mono (encEm_ok hH KH mH hp he L R hW hk) fun t5 ⟨he5, L5, V5, R5, E⟩ => ?_)
  -- `DB` masked.
  refine WP.seq (WP.mono (wp_good (dbArgs_good _) (dbArgs_ok (H := Hl.stream) L5 R5 w23' (by omega) (by omega)))
    fun t6 ⟨⟨L6, k6, R6⟩, sp6, mx6, f6⟩ => ?_)
  have he6 : EnvE s t6 := he5.step k6.2.1 k6.2.2 sp6 (keep_cs3 k6 (by decide)) mx6 f6
  refine WP.seq (WP.mono (wp_good (mgfXor_good (HGood.of hG KG)) (mgfXor_ok hG.stream mG.hash mG.len
    (valid_of_link hG mG) L6 R6 ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩
    (mW_args _ _ _ _ _ _))) fun t7 ⟨⟨L7, rd7, wr7, cs7, V7, W7, R7, hW7, hV7⟩, sp7, mx7, f7⟩ => ?_)
  have he7 : EnvE s t7 := he6.step rd7 wr7 sp7 (fun r hr _ => cs7 r hr) mx7 f7
  have W7e : ∀ k, (k < 15 ∨ 18 < k) → k < nW → k ≠ 19 → k ≠ 20 → W7 k = W k := fun k h1 h2 h3 h4 =>
    (hW7 k h2 h3 h4).trans (mW_other h1)
  -- The seed masked.
  refine WP.seq (WP.mono (wp_good (seedArgs_good _) (seedArgs_ok (H := Hl.stream) L7 R7
    ((W7e 23 (by omega) (by decide) (by omega) (by omega)).trans w23') (by omega) (by omega)))
    fun t8 ⟨⟨L8, k8, R8⟩, sp8, mx8, f8⟩ => ?_)
  have he8 : EnvE s t8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  refine WP.seq (WP.mono (wp_good (mgfXor_good (HGood.of hG KG)) (mgfXor_ok hG.stream mG.hash mG.len
    (valid_of_link hG mG) L8 R8 ⟨by unfold oEm oSt; omega, by unfold oEm oSt; omega, by omega, by omega, by omega⟩
    (mW_args _ _ _ _ _ _))) fun t9 ⟨⟨L9, rd9, wr9, cs9, V9, W9, R9, hW9, hV9⟩, sp9, mx9, f9⟩ => ?_)
  have he9 : EnvE s t9 := he8.step rd9 wr9 sp9 (fun r hr _ => cs9 r hr) mx9 f9
  -- The call.
  have W9e : ∀ k, 21 ≤ k → k ≤ 26 → W9 k = encW s k := fun k h1 h2 => by
    rw [hW9 k (by unfold nW frameBytes; omega) (by omega) (by omega), mW_other (by omega),
      W7e k (by omega) (by unfold nW frameBytes; omega) (by omega) (by omega)]
    exact hW k (.inr ⟨h1, by omega⟩)
  refine WP.seq (WP.mono (wp_good pubArgs_good (pubArgs_ok L9 R9 W9e))
    fun t10 ⟨⟨L10, k10, R10, hdi, hsi, hdx, hcx, h8, h9⟩, sp10, mx10, f10⟩ => ?_)
  have he10 : EnvE s t10 := he9.step k10.2.1 k10.2.2 sp10 (keep_cs3 k10 (by decide)) mx10 f10
  refine WP.mono (encPub_call hp L10 R10 (he10.rd) he10.wr he10.fr (by simp [upd]) (by simp [upd]) (by simp [upd])
    (by simp [upd]) hdi hsi hdx hcx h8 h9) fun t11 ⟨hout, rd11, wr11, cs11, mx11, f11⟩ => ?_
  refine ⟨⟨(cs11 .rsp (by decide)).trans he10.rsp, rd11.trans he10.rd, wr11.trans he10.wr,
    fun r hr h => (cs11 r hr).trans (he10.cs r hr h), mx11.trans he10.mx, f11⟩, ?_⟩
  have e1 : (s.gpr .rcx).toNat - (Hl.D + 1) = (s.gpr .rcx).toNat - Hl.D - 1 := by omega
  rw [hsD, e1] at hV7 hV9
  have hm : ∀ o, o < (s.gpr .rcx).toNat → mOut o := fun o ho => (mOut_iff o).mpr (.inl (by omega))
  have hlen : mH.G.len = Hl.D := mH.len
  have hsdl : (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len).length = Hl.D := by simp [Spec.Rsa.bytesAt, hlen]
  have hlhl : (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)).length = Hl.D := by
    rw [(valid_of_link hH mH).2, hlen]
  have hml : (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat).length = (stackArg s 3).toNat := by
    simp [Spec.Rsa.bytesAt]
  have hsrc : srcB V7 (oEm + 1 + Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1) =
      srcB (mixV V5 (Spec.Mgf1.mgf1 mG.G (srcB V5 1 Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1)) (1 + Hl.D)
        ((s.gpr .rcx).toNat - Hl.D - 1)) (1 + Hl.D) ((s.gpr .rcx).toNat - Hl.D - 1) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hV7 _ (by unfold oRsa; omega) (hm _ (by unfold oEm; omega))
  have hlist : (List.range (s.gpr .rcx).toNat).map (fun i => V9 (oEm + i)) =
      emOf mG.G Hl.D (s.gpr .rcx).toNat (stackArg s 3).toNat (Spec.Rsa.bytesAt s.mem (stackArg s 4) mH.G.len)
        (mH.G.hash (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) := by
    unfold emOf
    rw [← em_mask (valid_of_link hG mG) (V₁ := V5) (by omega) hsdl (by
        simp only [List.length_append, List.length_cons, hlhl, hml, Spec.RsaOaep.zeros, List.length_replicate]; omega)
      E.z0 E.sd (E.db hlhl hml hk)]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [show oEm + i = i by unfold oEm; omega, hV9 _ (by unfold oRsa; omega) (hm _ hi'), hsrc]
    exact mixV_congr _ _ _ (hV7 _ (by unfold oRsa; omega) (hm _ hi'))
  rw [hlist] at hout
  exact hout

end VG.Proof.RsaOaep.X86_64
