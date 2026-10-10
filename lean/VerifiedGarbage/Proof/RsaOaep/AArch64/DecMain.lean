import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
import VerifiedGarbage.Proof.RsaOaep.Decode
import VerifiedGarbage.Spec.RsaOaep.Contract

/-!
# RSAES-OAEP decryption on AArch64: the decoding

As on x86-64 (`Proof/RsaOaep/X86_64/DecMain.lean`): `decMain`
(`decMain_ok`), from `EM` in our working space and the private-key
operation's result in its slot, hashes the label, unmasks the seed and `DB`,
compares `lHash'`, scans, copies and shifts `T`, and writes the message
under the mask `ok` to `out` and its length to `*msg_len`: what
`Spec.RsaOaep.decrypt` writes for the operation's outcome.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.RsaOaep.AArch64.Mgf1 (seqs)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK)

theorem andB_ones (b : Byte) : andB b (BitVec.allOnes 64) = b := by
  simp only [andB, BitVec.and_allOnes]; exact byte_rt64 b

theorem andB_zero (b : Byte) : andB b 0 = 0 := by
  simp only [andB]; rw [show BitVec.setWidth 64 b &&& 0 = 0 from BitVec.and_zero]; rfl

/-- The private-key operation's result in its slot (word 28), and `EM` in
our working space. -/
def ResD (V : Nat → Byte) (W : Nat → BitVec 64) (k : Nat) : Spec.Rsa.Outcome → Prop
  | .ok em => W 28 = 1 ∧ (List.range k).map (fun i => V (oEm + i)) = em
  | .invalid => W 28 = 0
  | .fault => W 28 = 2

/-- Where `out` and `*msg_len` are: in their slots, writable, and apart
from the frame, our working space and each other. -/
structure OutAt (u : State) (F S : Addr) (W : Nat → BitVec 64) (o ml : Addr) (k : Nat) : Prop where
  ho : W 19 = o
  hml : W 27 = ml
  hw : Covers [⟨o, k⟩] u.wr
  hwm : Covers [⟨ml, 8⟩] u.wr
  hnw : o.toNat + k ≤ 2 ^ 64
  ha : Apart F S ⟨o, k⟩
  ham : Apart F S ⟨ml, 8⟩
  hom : Region.Disjoint ⟨o, k⟩ ⟨ml, 8⟩

theorem OutAt.congr {u u' : State} {F S : Addr} {W W' : Nat → BitVec 64} {o ml : Addr} {k : Nat}
    (h : OutAt u F S W o ml k) (hwr : u'.wr = u.wr) (h19 : W' 19 = W 19) (h27 : W' 27 = W 27) :
    OutAt u' F S W' o ml k :=
  ⟨h19.trans h.ho, h27.trans h.hml, hwr ▸ h.hw, hwr ▸ h.hwm, h.hnw, h.ha, h.ham, h.hom⟩

theorem Step.nil {F S : Addr} {ws : List Region} {t t' : State} (h : Step F S [] t t') : Step F S ws t t' :=
  h.weaken fun _ h => absurd h List.not_mem_nil

variable {Hl Gm : Hash} (hH : StreamOK Hl.stream) (hG : StreamOK Gm.stream)

include hH hG in
theorem decMain_ok {Hs Gs : Spec.Mgf1.Hash} (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = Hl.D)
    (hHv : Proof.Mgf1.Valid Hs) (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = Gm.D)
    (hGv : Proof.Mgf1.Valid Gs) {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte}
    {W : Nat → BitVec 64} (R : Rep u.mem F S V W) {k : Nat} (hk : W 21 = BitVec.ofNat 64 k)
    (hD : 2 * Hl.D + 2 ≤ k) (hk' : k ≤ 1024) {lab : Addr} {labLen : Nat} (A : LabAt u F S W lab labLen)
    {o ml : Addr} (O : OutAt u F S W o ml k) {res : Spec.Rsa.Outcome} (hres : ResD V W k res) :
    WP isa (decMain Hl Gm) u fun u' => Lay u' F S ∧ Step F S [⟨o, k⟩, ⟨ml, 8⟩] u u' ∧
      Spec.RsaOaep.writtenDecrypt u'.mem o ml k ((u'.gpr .x0).setWidth 32)
        (decOut Hs Gs (Spec.Rsa.bytesAt u.mem lab labLen) res) := by
  obtain ⟨-, hzF, -, hzDF, hD0⟩ := sizes hH
  have hD64 : Hl.D ≤ 64 := Nat.le_trans hzDF hzF
  replace hD0 : 0 < Hl.D := hD0
  have cSt : oSt = 3072 := rfl
  have cR : oRsa = 8192 := rfl
  unfold decMain seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- The label's hash.
  refine WP.seq (WP.mono (hashLabel_ok hH hHh L R A (Or.inr rfl)) fun u1 ⟨L1, S1, V1, R1, hV1, hV1'⟩ => ?_)
  -- The seed unmasked.
  refine WP.seq (WP.mono (seedArgs_ok L1 R1 hk hD (by omega_using [hD64]) hk' []) fun u2 ⟨L2, S2, R2⟩ => ?_)
  have f2 : MFit (1 + Hl.D) (k - Hl.D - 1) 1 Hl.D :=
    ⟨by rw [cSt]; omega_using [hk', hD64], by rw [cSt]; omega_using [hD64], by omega_using [], by omega_using [hD0], by omega_using [hD64]⟩
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv L2 R2 f2 (mW_args _ _ _ _ _ _))
    fun u3 ⟨L3, S3, V3, W3, R3, hW3, hV3⟩ => ?_)
  have W3e : ∀ j < nW, (j < 13 ∨ 18 < j) → W3 j = W j := fun j hj h =>
    (hW3 j hj (by omega_using [h]) (by omega_using [h])).trans (mW_eq _ _ _ _ _ _ (by omega_using [h]))
  -- `DB` unmasked.
  refine WP.seq (WP.mono (dbArgs_ok L3 R3 ((W3e 21 (by decide) (by omega_using [])).trans hk) hD (by omega_using [hD64]) hk' [])
    fun u4 ⟨L4, S4, R4⟩ => ?_)
  have f4 : MFit 1 Hl.D (1 + Hl.D) (k - Hl.D - 1) :=
    ⟨by rw [cSt]; omega_using [hD64], by rw [cSt]; omega_using [hk', hD64], by omega_using [], by omega_using [hD], by omega_using [hk']⟩
  refine WP.seq (WP.mono (mgfXor_ok hG hGh hGl hGv L4 R4 f4 (mW_args _ _ _ _ _ _))
    fun u5 ⟨L5, S5, V5, W5, R5, hW5, hV5⟩ => ?_)
  have W5e : ∀ j < nW, (j < 13 ∨ 18 < j) → W5 j = W j := fun j hj h =>
    (hW5 j hj (by omega_using [h]) (by omega_using [h])).trans ((mW_eq _ _ _ _ _ _ (by omega_using [h])).trans (W3e j hj h))
  -- `lHash'` against `lHash`, and the scan.
  refine WP.seq (WP.mono (accLh_ok L5 R5 (by omega_using [hD64]) hD0) fun u6 ⟨L6, S6, R6⟩ => ?_)
  have w6k : upd W5 29 (accL V5 Hl.D Hl.D) 21 = BitVec.ofNat 64 k := by
    simp only [upd]; rw [ifn (by decide)]; exact (W5e 21 (by decide) (by omega_using [])).trans hk
  refine WP.seq (WP.mono (scan_ok L6 R6 w6k hD hk') fun u7 ⟨L7, S7, R7⟩ => ?_)
  generalize hsc : scanS (tF V5 Hl.D) (upd W5 29 (accL V5 Hl.D Hl.D) 29) (k - 2 * Hl.D - 1) = sc at R7
  obtain ⟨W7, R7, w7e, w729, w730⟩ : ∃ W7, Rep u7.mem F S V5 W7 ∧ (∀ j, j ≠ 29 → j ≠ 30 → W7 j = W5 j) ∧
      W7 29 = sc.2.2 ||| sc.1 ∧ W7 30 = sc.2.1 :=
    ⟨_, R7, fun j h1 h2 => by simp only [upd, ifn h1, ifn h2], by simp [upd], by simp [upd]⟩
  have W7e : ∀ j < nW, (j < 13 ∨ 18 < j) → j ≠ 29 → j ≠ 30 → W7 j = W j := fun j hj h h1 h2 =>
    (w7e j h1 h2).trans (W5e j hj h)
  have w7k : W7 21 = BitVec.ofNat 64 k := (W7e 21 (by decide) (by omega_using []) (by omega_using []) (by omega_using [])).trans hk
  -- The buffer.
  refine WP.seq (WP.mono (clearBuf_ok L7 R7) fun u8 ⟨L8, S8, R8⟩ => ?_)
  refine WP.seq (WP.mono (copyT_ok L8 R8 w7k hD hk') fun u9 ⟨L9, S9, R9⟩ => ?_)
  -- The shift.
  obtain ⟨idx, hidx, hidx'⟩ := scan_idx (tF V5 Hl.D) (upd W5 29 (accL V5 Hl.D Hl.D) 29) (k - 2 * Hl.D - 1)
  rw [hsc] at hidx
  refine WP.seq (WP.mono (shift_ok L9 R9 (idx := idx) (w730.trans hidx) (by omega_using [hk', hidx']) fun x h1 h2 => by
      simp only [cpV, zV]
      rw [ifn (by omega_using [hk', h1]), ifp (by omega_using [h2])])
    fun u10 ⟨L10, S10, V10, R10, hB10, _⟩ => ?_)
  -- `ok`.
  refine WP.seq (WP.mono (okMask_ok L10 R10) fun u11 ⟨L11, S11, R11⟩ => ?_)
  have W11e : ∀ j < nW, (j < 13 ∨ 18 < j) → j ≠ 29 → j ≠ 30 → j ≠ 31 → upd W7 31 (okW W7) j = W j :=
    fun j hj h h1 h2 h3 => by simp only [upd, ifn h3]; exact W7e j hj h h1 h2
  have S11 : Step F S [] u u11 := S1.trans (S2.trans (S3.trans (S4.trans (S5.trans (S6.trans (S7.trans
    (S8.trans (S9.trans (S10.trans S11)))))))))
  have O11 : OutAt u11 F S (upd W7 31 (okW W7)) o ml k :=
    O.congr S11.wr (W11e 19 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []))
      (W11e 27 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using []))
  have w11k : upd W7 31 (okW W7) 21 = BitVec.ofNat 64 k :=
    (W11e 21 (by decide) (by omega_using []) (by omega_using []) (by omega_using []) (by omega_using [])).trans hk
  -- `out`.
  refine WP.seq (WP.mono (outLoop_ok L11 R11 O11.ho w11k (by omega_using [hD]) hk' O11.hw O11.hnw O11.ha)
    fun u12 ⟨L12, S12, R12, ho12⟩ => ?_)
  -- The length and the result.
  refine WP.mono (decRet_ok L12 R12 O11.hml w11k (by omega_using [hD64]) (S12.wr ▸ O11.hwm) O11.ham)
    fun u13 ⟨L13, S13, _, hml13, hx13⟩ => ?_
  refine ⟨L13, (S11.nil.trans (S12.weaken fun r h => by
    rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..)).trans (S13.weaken fun r h => by
    rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
  -- The bytes: `EM` unmasked, `lHash`, `T` and the buffer.
  have hlhl : (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).length = Hl.D := by rw [hHv.2, hHl]
  have e28 : upd W7 31 (okW W7) 28 = W 28 := W11e 28 (by decide) (by omega_using []) (by omega_using [])
      (by omega_using []) (by omega_using [])
  have e31 : upd W7 31 (okW W7) 31 = zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) := by
    simp only [upd, ite_true, okW]
    rw [w729, W7e 28 (by decide) (by omega_using []) (by omega_using []) (by omega_using [])]
  have e30 : upd W7 31 (okW W7) 30 = BitVec.ofNat 64 idx := by
    simp only [upd]; rw [ifn (by decide), w730, hidx]
  rw [e31, e30] at hml13
  rw [e31] at ho12 hx13
  simp only [fltW, e28] at hx13
  generalize hDD : Hl.D = D at *
  have nl : ∀ x, x < oSt → ¬ inR (labR oLh) x := fun x hx => by
    simp only [labR, inR_cons, inR_nil, or_false]; unfold oSt oLh oW at *; omega_using [hx]
  have v1 : ∀ x < k, V1 x = V x := fun x hx => hV1 x (nl x (by omega_using [hk', cSt, hx]))
  have v3 : ∀ x < k, V3 x = mixV V1 (Spec.Mgf1.mgf1 Gs (srcB V1 (1 + D) (k - (D + 1))) D) 1 D x :=
    fun x hx => by
      rw [hV3 x (by omega_using [hk', cR, hx]) ((mOut_iff x).mpr (.inl (by omega_using [hk', cSt, hx]))),
          show k - D - 1 = k - (D + 1) by omega_using []]
  have v5 : ∀ x < k, V5 x = mixV V3 (Spec.Mgf1.mgf1 Gs (srcB V3 1 D) (k - (D + 1))) (1 + D) (k - (D + 1)) x :=
    fun x hx => by
      rw [hV5 x (by omega_using [hk', cR, hx]) ((mOut_iff x).mpr (.inl (by omega_using [hk', cSt, hx]))),
          show k - D - 1 = k - (D + 1) by omega_using []]
  have hc5 := chain_eq (by omega_using [hD]) v1 v3 v5
  have lh5 : ∀ i < D, V5 (oLh + i) = (Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)).getD i 0 := fun i hi => by
    have mo : mOut (oLh + i) := (mOut_iff _).mpr (.inr (.inl (by unfold oLh oDig oCtr; omega_using [hD64, hi])))
    rw [hV5 _ (by unfold oLh; omega_using [cR, hD64, hi]) mo, mixV, ifn (by unfold oLh; omega_using [hk']),
      hV3 _ (by unfold oLh; omega_using [cR, hD64, hi]) mo, mixV, ifn (by unfold oLh; omega_using [hD64]), hV1' i hi]
  -- `T` and the scan.
  have hTl : (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).length = k - 2 * D - 1 := by simp [srcB]
  have hTg : ∀ i < k - 2 * D - 1, (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).getD i 0 = tF V5 D i := fun i hi => by
    rw [srcB, map_range_getD' _ hi]; rfl
  have hsc2 : sc = scanS (fun i => (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).getD i 0) (accL V5 D D)
      (srcB V5 (1 + 2 * D) (k - 2 * D - 1)).length := by
    rw [← hsc, hTl, show upd W5 29 (accL V5 D D) 29 = accL V5 D D by simp [upd]]
    exact scanS_congr _ _ fun i hi => (hTg i hi).symm
  generalize hT : srcB V5 (1 + 2 * D) (k - 2 * D - 1) = T at *
  -- The outputs.
  have hbuf : ∀ x, bufB (cpV (zV V5 oBuf 2048) oBuf (k - 2 * D - 1) (tF (zV V5 oBuf 2048) D)) x =
      T.getD x 0 := fun x => by
    have hge : ∀ y, k - 2 * D - 1 ≤ y → T.getD y 0 = 0 := fun y hy => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show T.length ≤ y by omega_using [hTl, hy])]
    unfold bufB
    by_cases hx : x < 1024
    · rw [ifp hx, cpV]
      by_cases hxt : x < k - 2 * D - 1
      · rw [ifp (by unfold oBuf; omega_using [hxt]), hTg x hxt, show oBuf + x - oBuf = x by omega_using [], tF, tF, zV,
          ifn (by unfold oBuf; omega_using [hk', hxt])]
      · rw [ifn (by unfold oBuf; omega_using [hxt]), zV, ifp (by unfold oBuf; omega_using [hx]), hge x (by omega_using [hxt])]
    · rw [ifn hx, hge x (by omega_using [hk', hx])]
  have dO : ∀ r ∈ (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: [⟨ml, 8⟩] : List Region),
      Region.Disjoint ⟨o, k⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [O.ha.dF, O.ha.dS, O.ha.dK, O.hom]
  have hout : ∀ i < k, u13.mem (o + BitVec.ofNat 64 i) =
      andB (T.getD (i + (idx + 1)) 0) (zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1)) := fun i hi =>
    (S13.frame.bytes (R := ⟨o, k⟩) dO (by show k ≤ 2 ^ 64; omega_using [hk']) hi).trans
      ((ho12 i hi).trans (by rw [hB10 i (by omega_using [hk', hi]), hbuf]))
  -- The accumulator.
  obtain ⟨i1, -, -, i4⟩ := scanS_inv (fun i => T.getD i 0) (accL V5 D D) T.length
  rw [← hsc2] at i1 i4
  have hacc : sc.2.2 ||| sc.1 = 0 ↔
      accL V5 D D = 0 ∧ ¬ bad (fun i => T.getD i 0) T.length ∧ ¬ lk (fun i => T.getD i 0) T.length := by
    rw [i4, i1, or_eq_zero, or_eq_zero, mk_eq_zero, mk_eq_zero, and_assoc]
  have zero_out : zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) = 0 →
      Spec.Rsa.bytesAt u13.mem o k = Spec.RsaOaep.zeros k ∧ u13.mem.readW ml 64 = 0 ∧
      (u13.gpr .x0).setWidth 32 = (zM (W 28 ^^^ 2) &&& 2).setWidth 32 := fun h0 =>
    ⟨out_zero fun i hi => by rw [hout i hi, h0, andB_zero], by rw [hml13, h0]; exact BitVec.and_zero,
      by rw [hx13, h0, show (0 : BitVec 64) &&& 1 = 0 by decide,
        show ∀ x : BitVec 64, x ||| 0 = x from fun x => by simp]⟩
  cases res with
  | fault =>
    have h2 : W 28 = 2 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h2, show zM ((2 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.and_zero)
    exact ⟨by rw [c, h2]; decide, a, b⟩
  | invalid =>
    have h0 : W 28 = 0 := hres
    obtain ⟨a, b, c⟩ := zero_out (by rw [h0, show zM ((0 : BitVec 64) ^^^ 1) = 0 by decide]; exact BitVec.and_zero)
    exact ⟨by rw [c, h0]; decide, a, b⟩
  | ok em =>
    obtain ⟨h1, hem⟩ := hres
    subst hem
    have c0 : oEm = 0 := rfl
    have hV : (fun i => V (oEm + i)) = V := funext fun i => by rw [c0, Nat.zero_add]
    rw [hV]
    have hok : zM (sc.2.2 ||| sc.1) &&& zM (W 28 ^^^ 1) = zM (sc.2.2 ||| sc.1) := by
      rw [h1, show zM ((1 : BitVec 64) ^^^ 1) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    have hf2 : zM (W 28 ^^^ 2) &&& 2 = 0 := by rw [h1]; decide
    rw [hok] at zero_out hout hml13 hx13
    rw [hf2, show ∀ x : BitVec 64, 0 ||| x = x from fun x => by simp] at hx13
    simp only [decOut]
    rw [decode_eq hGv _ (by omega_using [hD]) hHl hc5, show k - (2 * D + 1) = k - 2 * D - 1 by omega_using [], hT]
    have hz : ∀ (hne : sc.2.2 ||| sc.1 ≠ 0), _ := fun hne => zero_out (by simp only [zM]; rw [ifn hne])
    by_cases hfd : ¬ lk (fun i => T.getD i 0) T.length ∧ ¬ bad (fun i => T.getD i 0) T.length
    · obtain ⟨j₀, hj₀, hsj, hdw⟩ := scan_found T (accL V5 D D) hfd.1 hfd.2
      rw [← hsc2] at hsj
      have hij : idx = j₀ := by
        have := hidx.symm.trans hsj
        have := congrArg BitVec.toNat this
        rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk', hidx']),
          Nat.mod_eq_of_lt (by omega_using [hk', hTl, hj₀])] at this
      subst hij
      rw [hdw, show (1 : Byte) = 1#8 from rfl]
      simp only []
      have hV0 : V5 0 = V 0 := by
        rw [hc5 0 (by omega_using [hTl, hj₀]), mixV, ifn (by omega_using []), mixV, ifn (by omega_using [])]
      have htake : ((List.range k).map V).take 1 = [V 0] := by
        rw [show k = (k - 1) + 1 by omega_using [hTl, hj₀], List.range_succ_eq_map]; simp
      by_cases hc : ((List.range k).map V).take 1 = [0x00] ∧ srcB V5 (1 + D) D =
          Hs.hash (Spec.Rsa.bytesAt u.mem lab labLen)
      · rw [ifp hc]
        have hacc0 : sc.2.2 ||| sc.1 = 0 := hacc.mpr ⟨(accG_eq_zero _ _ _ D).mpr ⟨by
            rw [c0, hV0]; rw [htake] at hc; exact List.head_eq_of_cons_eq hc.1, fun i hi => by
            show V5 (oLh + i) = V5 (1 + D + i)
            rw [lh5 i hi, ← hc.2, srcB, map_range_getD' _ hi]⟩, hfd.2, hfd.1⟩
        have hzm : zM (sc.2.2 ||| sc.1) = BitVec.allOnes 64 := by simp only [zM]; rw [ifp hacc0]
        rw [hzm] at hout hml13 hx13
        refine ⟨by rw [hx13]; decide, out_list (by omega_using [hTl]) hj₀ fun i hi => by rw [hout i hi, andB_ones], ?_⟩
        rw [hml13, BitVec.and_allOnes, VG.Offset.ofNat_sub_ofNat (by omega_arith), VG.Offset.ofNat_sub_ofNat (by omega_using [hTl, hj₀]),
          List.length_drop]
        congr 1; omega_using [hTl]
      · rw [ifn hc]
        have hne : sc.2.2 ||| sc.1 ≠ 0 := fun h0 => by
          obtain ⟨e0, e1⟩ := (accG_eq_zero _ _ _ D).mp (hacc.mp h0).1
          refine hc ⟨by rw [htake, ← hV0, show (0 : Nat) = oEm from rfl, e0], ?_⟩
          refine srcB_eq hlhl fun i hi => ?_
          rw [← lh5 i hi]; exact (e1 i hi).symm
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

end VG.Proof.RsaOaep.AArch64
