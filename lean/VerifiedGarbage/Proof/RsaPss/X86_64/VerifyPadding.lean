import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyMain

/-!
# RSASSA-PSS verification on x86-64: correctness

`vlogic`: what the code computes is zero exactly when the encoding is
valid, byte by byte (`VerifyCases.lean`). `verify_body`: from the entry
state, the body of the frame returns 1 exactly when `RsaPss.verify` holds,
with the callee-saved registers restored.
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)

theorem list_eq_iff_getD {a b : List Byte} {n : Nat} (ha : a.length = n) (hb : b.length = n) :
    a = b ↔ ∀ i < n, a.getD i 0 = b.getD i 0 := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    apply List.ext_getElem (by omega)
    intro i h₁ h₂
    have := h i (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
      List.getElem?_eq_getElem h₂] at this

theorem ofNat_eq_iff {a : Nat} (ha : a < 2 ^ 64) (b : BitVec 64) : BitVec.ofNat 64 a = b ↔ a = b.toNat := by
  constructor
  · rintro rfl; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  · rintro rfl; simp

/-- What the code computes, against the checks of `verifyEncoding`. -/
theorem vlogic (G : Spec.Mgf1.Hash) (hG : Proof.Mgf1.Valid G) (x mHash : List Byte) {k lo z : Nat} (fixed : Bool)
    (slen : BitVec 64) {sLen : Option Nat} (hsl : sLen = if fixed then some slen.toNat else none)
    (hx : x.length = k) (hlo : lo ≤ 1) (hfit : G.len + 2 ≤ k - lo) (hk : k ≤ 1024) :
    let em := x.drop lo
    let L := k - lo - G.len - 1
    let dbL := vDb G em L z
    let fd := decide (lz dbL < L)
    let pos := if lz dbL < L then lz dbL else 0
    let val := if lz dbL < L then dbL.getD (lz dbL) 0 else 0
    (acc1V (acc0V (x.getD (k - 1) 0) (x.getD 0 0) (x.getD lo 0) ((0xFF : Byte) >>> z) lo) fd val fixed
        (BitVec.ofNat 64 (L - pos - 1)) slen = 0 ∧
      ∀ i < G.len, (G.hash (Spec.RsaPss.zeros 8 ++ mHash ++ dbL.drop (pos + 1))).getD i 0 = (vH G em L).getD i 0) ↔
    ((lo = 1 → x.getD 0 0 = 0) ∧ EncOk G mHash em (k - lo) z sLen) := by
  dsimp only
  have hvH : (vH G (x.drop lo) (k - lo - G.len - 1)).length = G.len := by simp [vH]; omega
  rw [acc1V_eq_zero, acc0V_eq_zero _ _ _ _ hlo]
  have e1 : x.getD (k - 1) 0 = (x.drop lo).getD (k - lo - 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]; congr 2; omega
  have e2 : x.getD lo 0 = (x.drop lo).getD 0 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero]
  rw [e1, e2]
  unfold EncOk
  rw [← list_eq_iff_getD (hG.2 _) hvH]
  generalize vDb G (x.drop lo) (k - lo - G.len - 1) z = dbL
  by_cases hf : lz dbL < k - lo - G.len - 1
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

variable {G : Spec.Mgf1.Hash}

variable (G) in
/-- What `verifyK.post` asks of `rax`. -/
def verifyOut (s : State) : Bool :=
  Spec.RsaPss.verify G G (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat)
    (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32))

variable (G) in
/-- Before the epilogue: the result in `rax`, the saved registers in their
slots. -/
structure VDone (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 3)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if verifyOut G s then 1 else 0

variable {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : Pbkdf2.Md.X86_64.HashOK H) (K : Pbkdf2.Md.X86_64.Callees H)

include hH K in
theorem vmid_safe : (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck H]).allInstrs safeI = true := by
  simp only [seqs, posScan, posCheck, Code.allInstrs, mgfXor_safe hH K, rec_all, List.all_append, byteLoop, step,
    Bool.and_true, Bool.true_and]
  rfl

include K in
theorem vmid_xd : (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck H]).x86_64Depth = 8 := by
  simp only [seqs, posScan, posCheck, byteLoop, Code.x86_64Depth, mgfXor_xd K]
  rfl

include hH K in
theorem vback_safe : (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]).allInstrs
    safeI = true := by
  simp only [seqs, clearY, copyDigest, copyDb, shift, shiftPass, cmpH, Code.allInstrs, ctHash_safe hH K, rec_all,
    List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem vback_xd : (seqs [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]).x86_64Depth
    = 8 := by
  simp only [seqs, clearY, copyDigest, copyDb, shift, shiftPass, cmpH, byteLoop, Code.x86_64Depth, ctHash_xd K]
  rfl

theorem ite_setWidth {p : Prop} [Decidable p] {b : Bool} (h : p ↔ b = true) :
    ((if p then 1 else 0 : BitVec 64).setWidth 32) = if b then 1 else 0 := by
  by_cases hb : b = true
  · rw [ifp (h.mpr hb), ifp hb]; rfl
  · rw [ifn (fun hp => hb (h.mp hp)), ifn hb]; rfl

theorem map_range_drop {x : List Byte} {lo n : Nat} (hn : lo + n ≤ x.length) {f : Nat → Byte}
    (hf : ∀ i < n, f i = x.getD (lo + i) 0) : (List.range n).map f = (x.drop lo).take n := by
  rw [list_eq_iff_getD (n := n) (by simp) (by simp; omega)]
  intro i hi
  rw [getD_map_range, ifp hi, hf i hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ifp hi, List.getElem?_drop]

/-- The padding result and the state needed by the epilogue. -/
structure PaddingDone (result : Bool) (s t : State) : Prop where
  L : Lay t (fb s) (stackArg s 3)
  wr : t.wr = frR s :: s.wr
  cs : ∀ r ∈ [Reg.r13, .r14, .r15], t.gpr r = s.gpr r
  rbx : t.mem.readW (off (fb s) sRbx) 64 = s.gpr .rbx
  rbp : t.mem.readW (off (fb s) sRbp) 64 = s.gpr .rbp
  r12 : t.mem.readW (off (fb s) sR12) 64 = s.gpr .r12
  out : (t.gpr .rax).setWidth 32 = if result then 1 else 0

include hH K in
/-- Padding verification depends only on the recovered bytes, not on how
RSA produced them. -/
theorem vpadding_done (lk : Pbkdf2.Md.X86_64.MgfLink H hH)
    {s u3 : State} (hp : VPre lk.G s) {V1 : Nat → Byte} {W1 : Nat → BitVec 64}
    (L3 : Lay u3 (fb s) (stackArg s 3)) (R1 : Rep u3.mem (fb s) (stackArg s 3) V1 W1)
    (hw : u3.wr = frR s :: s.wr) (hrd : u3.rd = s.rd)
    (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u3.gpr r = s.gpr r) (hM3 : Frame (vwrR s) s.mem u3.mem)
    {lo z : Nat} {fixed result : Bool} (x : List Byte) (hxl : x.length = (s.gpr .rsi).toNat)
    (hV1 : ∀ i < (s.gpr .rsi).toNat, V1 (oEm + i) = x.getD i 0)
    (h17 : W1 17 = s.gpr .rsi) (h23 : W1 23 = off (stackArg s 3) (oEm + lo))
    (h24 : W1 24 = BitVec.ofNat 64 ((s.gpr .rsi).toNat - lo - lk.G.len - 1))
    (h25 : W1 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z)) (h26 : W1 26 = BitVec.ofNat 64 lo)
    (h35 : W1 35 = if fixed then 0 else 1) (h36 : W1 36 = stackArg s 1) (h37 : W1 37 = s.gpr .r8)
    (h41 : W1 41 = s.gpr .rbx) (h42 : W1 42 = s.gpr .rbp) (h43 : W1 43 = s.gpr .r12)
    (hlo : lo ≤ 1) (hfit : H.D + 2 ≤ (s.gpr .rsi).toNat - lo)
    (hspec : result = true ↔ (lo = 1 → x.getD 0 0 = 0) ∧
      EncOk lk.G (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) (x.drop lo) ((s.gpr .rsi).toNat - lo) z
        (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)))
    (hsl : Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32) =
      if fixed then some (stackArg s 1).toNat else none) :
    WP isa (seqs [.block acc0, mgfXor H, .block clearTop, posScan, posCheck H,
      clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]) u3 (PaddingDone result s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hG := validG hH lk.hash lk.len
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  rw [show [Code.block acc0, mgfXor H, .block clearTop, posScan, posCheck H,
      clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H] =
    [Code.block acc0, mgfXor H, .block clearTop, posScan, posCheck H] ++
    [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H] from rfl]
  set k := (s.gpr .rsi).toNat with hk
  set db := k - lo - lk.G.len - 1 with hdb
  -- `acc` and the first nonzero byte of `DB`.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (WP.keepIn (vmid_safe hH K) (by rw [vmid_xd K])
    (vmid_ok hH K lk L3 R1 (k := k) (lo := lo) (db := db) (z := z) (fixed := fixed)
      (by rw [h17, hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      h23 h24 (by rw [h25])
      (by rw [h26])
      (by rw [h35]) hlo (by omega) (by omega) hk2))
    fun u4 ⟨⟨L4, rd4, wr4, cs4, V3, W3, R3, h33, h34, h27, hW3, hV3, hO3⟩, f4⟩ => ?_)
  have hM4 := vframe_keep hp hw L3.rsp hM3 f4
  -- `DB` as the specification's.
  have hm1 : (List.range db).map (fun i => V1 (oEm + lo + i)) = (x.drop lo).take db :=
    map_range_drop (by omega) fun i hi => by rw [Nat.add_assoc, hV1 _ (by omega)]
  have hm2 : (List.range H.D).map (fun i => V1 (oEm + lo + db + i)) = vH lk.G (x.drop lo) db := by
    have hl : db + H.D ≤ (x.drop lo).length := by rw [List.length_drop, hxl]; omega
    have h := map_range_drop (x := x.drop lo) (lo := db) (n := H.D) (f := fun i => V1 (oEm + lo + db + i)) hl
      (fun i hi => by
        rw [show oEm + lo + db + i = oEm + (lo + (db + i)) by omega, hV1 _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_drop])
    rw [h, vH, hD]
  rw [hm1, hm2] at h33 hV3
  rw [hm1, hm2] at h34 h27
  have hvdb : Spec.RsaPss.clearTop z (Spec.Mgf1.xorBytes ((x.drop lo).take db)
      (Spec.Mgf1.mgf1 lk.G (vH lk.G (x.drop lo) db) db)) = vDb lk.G (x.drop lo) db z := rfl
  rw [hvdb] at h33 hV3 h34 h27
  set dbL := vDb lk.G (x.drop lo) db z with hdbL
  have h23' : W3 23 = off (stackArg s 3) (oEm + lo) := by rw [hW3 23 (by decide) (.inl (by decide)), h23]
  have h24' : W3 24 = BitVec.ofNat 64 db := by rw [hW3 24 (by decide) (.inl (by decide)), h24]
  have h37' : W3 37 = s.gpr .r8 := by
    rw [hW3 37 (by decide) (.inr (by decide)), h37]
  have hpd : (if lz dbL < db then lz dbL else 0) < db := by split <;> omega
  have hrd4 : u4.rd = s.rd := by rw [rd4, hrd]
  have hwr4 : u4.wr = frR s :: s.wr := by rw [wr4, hw]
  have wDg := hp.wDg
  -- The salt, its hash, and the comparison.
  refine WP.mono (WP.keepIn (vback_safe hH K) (by rw [vback_xd K])
    (vback_ok hH K lk L4 R3 (lo := lo) (db := db) (pos := if lz dbL < db then lz dbL else 0) (dig := s.gpr .r8)
      h23' h24' h34 h27 h37' hlo (by omega) hpd (by omega)
      (fun i hi => by
        rw [hrd4]
        exact hp.hrd.left _ _ ⟨⟨s.gpr .r8, lk.G.len⟩, by simp,
          Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hwr4] at this)))
    fun u5 ⟨⟨L5, rd5, wr5, cs5, ⟨V5, W5, R5, hW5⟩, hax5⟩, f5⟩ => ?_
  have g3 : ∀ j, j < nW → 34 < j → W3 j = W1 j := fun j hj h => hW3 j hj (.inr h)
  have g5 : ∀ j, j < nW → 34 < j → j ≠ 44 → j ≠ 45 → j ≠ 46 → W5 j = W1 j := fun j hj h a b c =>
    (hW5 j hj (by omega) (by omega) (by omega) a b c).trans (g3 j hj h)
  refine ⟨L5, by rw [wr5, hwr4], fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [cs5 r hr', cs4 r hr', hcs r hr]
  · rw [R5.rd (d := sRbx) 41 rfl (by decide), g5 41 (by decide) (by decide) (by decide) (by decide) (by decide), h41]
  · rw [R5.rd (d := sRbp) 42 rfl (by decide), g5 42 (by decide) (by decide) (by decide) (by decide) (by decide), h42]
  · rw [R5.rd (d := sR12) 43 rfl (by decide), g5 43 (by decide) (by decide) (by decide) (by decide) (by decide), h43]
  -- The result.
  have hmsg1 : (List.range H.D).map (bytesF u4.mem (s.gpr .r8)) = Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len := by
    rw [hD]; exact bytesAt_frame hM4 (vin_apart hp.dKdg hp.ddgs) (by omega)
  have hdbl : dbL.length = db := by
    rw [hdbL, vDb, clearTop_length, Proof.Mgf1.xorBytes_length, Proof.Mgf1.mgf1_length hG]; simp; omega
  have hmsg2 : (List.range db).map (fun i => V3 (oEm + lo + i)) = dbL :=
    (eq_range_map hdbl (fun i hi => (hV3 i hi).symm)).symm
  have hHb : ∀ i < H.D, V3 (oEm + lo + db + i) = (vH lk.G (x.drop lo) db).getD i 0 := fun i hi => by
    rw [hO3 _ (by omega) ⟨by unfold oLen; omega, by unfold oY; omega⟩ (by omega),
      show oEm + lo + db + i = oEm + (lo + (db + i)) by omega, hV1 _ (by omega)]
    simp only [vH, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, ifp (show i < lk.G.len by omega)]
  have hV := vlogic lk.G hG x (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) (z := z) fixed (stackArg s 1) hsl hxl hlo
    (by omega) hk2
  simp only [← hdb, ← hdbL] at hV
  rw [hax5, h33, hmsg1, hmsg2, h36]
  refine ite_setWidth ((Iff.trans (and_congr ?_ ?_) hV).trans hspec.symm)
  · have h0 := hV1 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [hV1 lo (by omega), show oEm + k - 1 = oEm + (k - 1) by omega, hV1 _ (by omega), h0]
  · rw [← hD]
    exact forall_congr' fun i => imp_congr_right fun hi => by rw [hHb i hi]

end VG.Proof.RsaPss.X86_64
