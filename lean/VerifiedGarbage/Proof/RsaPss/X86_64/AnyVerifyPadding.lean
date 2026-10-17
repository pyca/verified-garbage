module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyMid
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyFront
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyPadding
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyDispatch
public import VerifiedGarbage.Proof.RsaPss.AnyHash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.RsaPss.X86_64.SignCall

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: correctness

`vlogicA`: what the code computes is zero exactly when the encoding is
valid, for the digest's hash function `H` and MGF1's `G`
(`Proof/RsaPss/AnyHash.lean`). `vpadding_doneA`: after the public-key
operation, the code returns 1 exactly when the encoding is valid, with
MGF1 by the `g`th hash function and the rest by the `kh`th.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

/-- What the code computes, against the checks of `verifyEncoding`, for the
digest's hash function `H` and MGF1's `G`. -/
theorem vlogicA (H G : Spec.Mgf1.Hash) (hH : Proof.Mgf1.Valid H) (x mHash : List Byte) {k lo z : Nat}
    (fixed : Bool) (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : H.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - H.len - 1
    let dbL := RsaPss.Any.vDb H G em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < H.len, (H.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 =
        (RsaPss.Any.vH H em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ RsaPss.Any.EncOk H G mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (RsaPss.Any.vH H (x.drop lo) (k - lo - H.len - 1)).length = H.len := by
    simp [RsaPss.Any.vH]; omega
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold RsaPss.Any.EncOk
  rw [← list_eq_iff_getD (hH.2 _) hvH]
  generalize RsaPss.Any.vDb H G (x.drop lo) (k - lo - H.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - H.len - 1
  · rw [ifp hf, ifp hf, decide_eq_true hf, ofNat_eq_iff (by omega)]
    subst hsl
    constructor
    · rintro ⟨⟨⟨hA, hP, hB⟩, hC, -, hS⟩, hH⟩
      refine ⟨hP, hA, hB, hf, hC, ?_, hH⟩
      cases fixed
      · exact .inl rfl
      · exact .inr (by rw [ifp rfl]; congr 1; have := hS rfl; omega)
    · rintro ⟨hP, hA, hB, -, hC, hS, hH⟩
      refine ⟨⟨⟨hA, hP, hB⟩, hC, rfl, fun hfx => ?_⟩, hH⟩
      subst hfx
      rw [ifp rfl] at hS
      rcases hS with h | h
      · cases h
      · have := Option.some.inj h; omega
  · rw [decide_eq_false hf]
    constructor
    · rintro ⟨⟨_, _, h, _⟩, _⟩; cases h
    · rintro ⟨_, _, _, h, _⟩; exact absurd h hf

/-- What `verifyAnyK.post` asks of `rax`, for the hash functions `H` and `G`. -/
def verifyOutA (H G : Spec.Mgf1.Hash) (s : State) : Bool :=
  Spec.RsaPss.verify H G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) H.len)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32))

/-- The padding result and the state needed by the epilogue. -/
structure PaddingDoneA (result : Bool) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if result then 1 else 0

theorem posCheck_safe (H : Hash) : (posCheck H).allInstrs safeI = true := by
  simp only [posCheck, Code.allInstrs, Bool.and_true]
  rfl

theorem posCheck_xd (H : Hash) : (posCheck H).x86_64Depth ≤ 8 := by
  simp only [posCheck, Code.x86_64Depth]; decide

/-- Padding verification depends only on the recovered bytes, not on how
RSA produced them: MGF1 with `hs[g]`, the rest with `hs[kh] = H`. -/
theorem vpadding_doneA {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H)
    (lk : MgfLink H hH) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG)
    {s u3 : State} (hp : VPreA lk.G s) {V1 : Nat → Byte} {W1 : Nat → BitVec 64}
    (L3 : Lay u3 (fb s) (stackArg s 4)) (R1 : Rep u3.mem (fb s) (stackArg s 4) V1 W1)
    (hw : u3.wr = frR s :: s.wr) (hrd : u3.rd = s.rd)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u3.gpr r = s.gpr r) (hM3 : Frame (vwrRA s) s.mem u3.mem)
    {lo z : Nat} {fixed result : Bool} (x : List Byte) (hxl : x.length = (s.gpr .rsi).toNat)
    (hV1 : ∀ i < (s.gpr .rsi).toNat, V1 (oEm + i) = x.getD i 0)
    (h15 : W1 15 = BitVec.ofNat 64 H.D)
    (h17 : W1 17 = s.gpr .rsi) (h23 : W1 23 = off (stackArg s 4) (oEm + lo))
    (h24 : W1 24 = BitVec.ofNat 64 ((s.gpr .rsi).toNat - lo - lk.G.len - 1))
    (h25 : W1 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (h26 : W1 26 = BitVec.ofNat 64 lo)
    (h35 : W1 35 = if fixed then 0 else 1) (h36 : W1 36 = stackArg s 3) (h37 : W1 37 = s.gpr .r8)
    (h41 : W1 41 = s.gpr .rbx) (h42 : W1 42 = s.gpr .rbp) (h43 : W1 43 = s.gpr .r12)
    (h47 : W1 47 = BitVec.ofNat 64 kh) (h48 : W1 48 = BitVec.ofNat 64 g)
    (hlo : lo ≤ 1) (hfit : H.D + 2 ≤ (s.gpr .rsi).toNat - lo)
    (hspec : result = true ↔ (lo = 1 → x.getD 0 0 = 0) ∧
      RsaPss.Any.EncOk lk.G lkG.G (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) (x.drop lo)
        ((s.gpr .rsi).toNat - lo) z (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)))
    (hsl : Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32) =
      if fixed then some (stackArg s 3).toNat else none) :
    WP isa (seqs [.block acc0, mgfXorAny hs, .block clearTop, posScan, dispatch sHsel verifyTail hs]) u3
      (PaddingDoneA result s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hHv := validG hH lk.hash lk.len
  have hGv := validG hG lkG.hash lkG.len
  have hD0 := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  rw [show [Code.block acc0, mgfXorAny hs, .block clearTop, posScan, dispatch sHsel verifyTail hs] =
    [Code.block acc0, mgfXorAny hs, .block clearTop, posScan] ++ [dispatch sHsel verifyTail hs] from rfl]
  set k := (s.gpr .rsi).toNat with hk
  set db := k - lo - lk.G.len - 1 with hdb
  -- `acc`, `DB` and its first nonzero byte.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (WP.keepIn (vmidA_safe ht) (vmidA_xd ht)
    (vmidA_ok hg hl hG KG lkG.hash lkG.len hGv hD0 (by omega) L3 R1 (k := k) (lo := lo) (db := db) (z := z)
      (by rw [h17, hk, BitVec.ofNat_toNat, BitVec.setWidth_eq]) h23 h24 h25 h26 h15 h48 hlo (by omega) (by omega)
      hk2))
    fun u4 ⟨⟨L4, rd4, wr4, cs4, hdx4, hsi4, h114, V3, W3, R3, h33, hW3, hV3, hO3⟩, f4⟩ => ?_)
  have hM4 := vframe_keepA hp hw L3.rsp hM3 f4
  -- `DB` as the specification's.
  have hm1 : (List.range db).map (fun i => V1 (oEm + lo + i)) = (x.drop lo).take db :=
    map_range_drop (by omega) fun i hi => by rw [Nat.add_assoc, hV1 _ (by omega)]
  have hm2 : (List.range H.D).map (fun i => V1 (oEm + lo + db + i)) = RsaPss.Any.vH lk.G (x.drop lo) db := by
    have hl : db + H.D ≤ (x.drop lo).length := by rw [List.length_drop, hxl]; omega
    have h := map_range_drop (x := x.drop lo) (lo := db) (n := H.D) (f := fun i => V1 (oEm + lo + db + i)) hl
      (fun i hi => by
        rw [show oEm + lo + db + i = oEm + (lo + (db + i)) by omega, hV1 _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop])
    rw [h, RsaPss.Any.vH, hD]
  rw [hm1, hm2] at hdx4 hsi4 h114 hV3
  have hvdb : Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((x.drop lo).take db)
      (Spec.Mgf1.mgf1 lkG.G (RsaPss.Any.vH lk.G (x.drop lo) db) db)) = RsaPss.Any.vDb lk.G lkG.G (x.drop lo) db z := rfl
  rw [hvdb] at hdx4 hsi4 h114 hV3
  set dbL := RsaPss.Any.vDb lk.G lkG.G (x.drop lo) db z with hdbL
  set fd := decide (lz dbL < db)
  set pos := if lz dbL < db then lz dbL else 0 with hpos
  set val := if lz dbL < db then dbL.getD (lz dbL) 0 else 0 with hval
  have hpd : pos < db := by simp only [pos]; split <;> omega
  have hrd4 : u4.rd = s.rd := by rw [rd4, hrd]
  have hwr4 : u4.wr = frR s :: s.wr := by rw [wr4, hw]
  have g3 : ∀ j, j < nW → 32 < j → j ≠ 33 → W3 j = W1 j := fun j hj h h' => hW3 j hj (.inr h) h'
  -- The digest's hash function.
  refine dispatch_ok L4 R3 (j := 47) rfl (by decide) (by rw [g3 47 (by decide) (by decide) (by decide), h47]) hl hkh
    fun v kv hmv hav => ?_
  rw [hkH]
  have Lv : Lay v (fb s) (stackArg s 4) := L4.congr (kv.gpr (by decide)) kv.2.2 (by rw [hmv])
  have Rv : Rep v.mem (fb s) (stackArg s 4) V3 W3 := hmv ▸ R3
  have hMv : Frame (vwrRA s) s.mem v.mem := hmv ▸ hM4
  have h35' : W3 35 = if fixed then 0 else 1 := by rw [g3 35 (by decide) (by decide) (by decide), h35]
  have h24' : W3 24 = BitVec.ofNat 64 db := by rw [hW3 24 (by decide) (.inl (by decide)) (by decide), h24]
  have h23' : W3 23 = off (stackArg s 4) (oEm + lo) := by
    rw [hW3 23 (by decide) (.inl (by decide)) (by decide), h23]
  -- `acc`'s checks.
  refine WP.seq (WP.mono (WP.keepIn (posCheck_safe H) (posCheck_xd H)
    (posCheck_ok hH Lv Rv (db := db) (pos := pos) (fd := fd) (val := val) h24' h35' hpd
      (by rw [kv.gpr (by decide), hdx4]; simp only [fd]; by_cases hc : lz dbL < db <;> simp [hc])
      (by rw [kv.gpr (by decide), hsi4])
      (by rw [kv.gpr (by decide), h114])))
    fun u5 ⟨⟨L5, k5, R5⟩, f5⟩ => ?_)
  have hM5 := vframe_keepA hp (kv.2.2.trans hwr4) Lv.rsp hMv f5
  have hrd5 : u5.rd = s.rd := by rw [k5.2.1, kv.2.1, hrd4]
  have hwr5 : u5.wr = frR s :: s.wr := by rw [k5.2.2, kv.2.2, hwr4]
  set W5 := upd (upd (upd W3 34 (BitVec.ofNat 64 pos)) 33
    (acc1V (W3 33) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W3 36))) 27
    (BitVec.ofNat 64 (db - pos - 1 + (8 + H.D))) with hW5
  have g5 : ∀ j, j ≠ 27 → j ≠ 33 → j ≠ 34 → W5 j = W3 j := fun j a b c => by simp [hW5, upd, a, b, c]
  have h36' : W3 36 = stackArg s 3 := by rw [g3 36 (by decide) (by decide) (by decide), h36]
  have h37' : W5 37 = s.gpr .r8 := by
    rw [g5 37 (by decide) (by decide) (by decide), g3 37 (by decide) (by decide) (by decide), h37]
  have wDg := hp.wDg
  -- The salt, its hash, and the comparison.
  refine WP.mono (saltBack_ok hH K lk L5 R5 (lo := lo) (db := db) (pos := pos) (dig := s.gpr .r8)
      (by rw [g5 23 (by decide) (by decide) (by decide), h23'])
      (by rw [g5 24 (by decide) (by decide) (by decide), h24']) (by simp [hW5, upd]) (by simp [hW5, upd])
      h37' hlo (by omega) hpd (by omega)
      (fun i hi => by
        rw [hrd5]
        exact hp.hrd.left _ _ ⟨⟨s.gpr .r8, lk.G.len⟩, by simp,
          Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside (G := lk.G) hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hwr5] at this)
      (fun hany hacc => by
        have hfixed : fixed = true := by
          rw [g5 35 (by decide) (by decide) (by decide), h35'] at hany
          cases fixed <;> first | rfl | simp at hany
        have hacc' : acc1V (W3 33) fd val fixed (BitVec.ofNat 64 (db - pos - 1)) (W3 36) = 0 := by
          simpa [hW5, upd] using hacc
        rw [acc1V_eq_zero] at hacc'
        rw [g5 36 (by decide) (by decide) (by decide)]
        exact (hacc'.2.2.2 hfixed).symm))
    fun u6 ⟨L6, rd6, wr6, cs6, ⟨V6, W6, R6, hW6⟩, hax6⟩ => ?_
  have g6 : ∀ j, j < nW → 34 < j → j ≠ 44 → j ≠ 45 → j ≠ 46 → W6 j = W1 j := fun j hj h a b c => by
    rw [hW6 j hj (by omega) (by omega) (by omega) (by omega) a b c, g5 j (by omega) (by omega) (by omega),
      g3 j hj (by omega) (by omega)]
  refine ⟨L6, by rw [wr6, hwr5], fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [cs6 r hr', keep_cs k5 (by decide) r hr', keep_cs kv (by decide) r hr', cs4 r hr', hcs r hr]
  · rw [R6.rd (d := sRbx) 41 rfl (by decide), g6 41 (by decide) (by decide) (by decide) (by decide) (by decide), h41]
  · rw [R6.rd (d := sRbp) 42 rfl (by decide), g6 42 (by decide) (by decide) (by decide) (by decide) (by decide), h42]
  · rw [R6.rd (d := sR12) 43 rfl (by decide), g6 43 (by decide) (by decide) (by decide) (by decide) (by decide), h43]
  -- The result.
  have hmsg1 : (List.range H.D).map (bytesF u5.mem (s.gpr .r8)) = Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len := by
    rw [hD]; exact bytesAt_frame hM5 (vin_apartA hp.dKdg hp.ddgs) (by omega)
  have hdbl : dbL.length = db := by
    rw [hdbL, RsaPss.Any.vDb, clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hGv]; simp; omega
  have hmsg2 : (List.range db).map (fun i => V3 (oEm + lo + i)) = dbL :=
    (eq_range_map hdbl (fun i hi => (hV3 i hi).symm)).symm
  have hHb : ∀ i < H.D, V3 (oEm + lo + db + i) = (RsaPss.Any.vH lk.G (x.drop lo) db).getD i 0 := fun i hi => by
    rw [hO3 _ (by omega) ⟨by unfold oLen; omega, by unfold oY; omega⟩ (by omega),
      show oEm + lo + db + i = oEm + (lo + (db + i)) by omega, hV1 _ (by omega)]
    simp only [RsaPss.Any.vH, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      ifp (show i < lk.G.len by omega)]
  have hV := vlogicA lk.G lkG.G hHv x (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) (z := z) fixed (stackArg s 3)
    hsl hxl hlo (by omega) hk2
  simp only [← hdb, ← hdbL] at hV
  have h33' : W5 33 = acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val
      fixed (BitVec.ofNat 64 (db - pos - 1)) (stackArg s 3) := by
    have h0 := hV1 0 (by omega)
    rw [Nat.add_zero] at h0
    simp only [hW5, upd, Nat.reduceEqDiff, ite_true, ite_false]
    rw [h33, h36', hV1 lo (by omega), show oEm + k - 1 = oEm + (k - 1) by omega, hV1 _ (by omega), h0]
  rw [hax6, h33', hmsg1, hmsg2]
  refine ite_setWidth ((Iff.trans (and_congr Iff.rfl ?_) hV).trans hspec.symm)
  rw [← hD]
  exact forall_congr' fun i => imp_congr_right fun hi => by rw [hHb i hi]

end VG.Proof.RsaPss.X86_64.Any
