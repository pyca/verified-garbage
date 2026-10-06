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

include hH K in
theorem vmain_done (lk : Pbkdf2.Md.X86_64.MgfLink H hH) {pubN : String} {pubC : Prog isa}
    (hv : ∀ s, pubContract.pre s → ∃ t s', Exec isa pubC s t s' ∧ abiPreserved s s' ∧ pubChkContract.post s s')
    (hspC : SpSafe pubC) (hdC : pubC.x86_64Depth = 0)
    {s u : State} (hp : VPre lk.G s) {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay u (fb s) (stackArg s 3)) (R : Rep u.mem (fb s) (stackArg s 3) V W) (hw : u.wr = frR s :: s.wr)
    (hrd : u.rd = s.rd) (hcs : ∀ r ∈ [Reg.r13, .r14, .r15], u.gpr r = s.gpr r) (hM : Frame (vwrR s) s.mem u.mem)
    {lo z : Nat} {fixed : Bool}
    (h17 : W 17 = s.gpr .rsi) (h18 : W 18 = s.gpr .rdi) (h19 : W 19 = s.gpr .rdx) (h20 : W 20 = s.gpr .rcx)
    (h22 : W 22 = stackArg s 4) (h25 : W 25 = BitVec.setWidth 64 ((0xFF : Byte) >>> z))
    (h26 : W 26 = BitVec.ofNat 64 lo) (h35 : W 35 = if fixed then 0 else 1) (h36 : W 36 = stackArg s 1)
    (h37 : W 37 = s.gpr .r8) (h38 : W 38 = s.gpr .r9) (h41 : W 41 = s.gpr .rbx) (h42 : W 42 = s.gpr .rbp)
    (h43 : W 43 = s.gpr .r12)
    (hlo : lo ≤ 1) (hfit : H.D + 2 ≤ (s.gpr .rsi).toNat - lo)
    (hax : u.gpr .rax = BitVec.ofNat 64 ((s.gpr .rsi).toNat - lo - (H.D + 2)))
    (hspec : verifyOut lk.G s = true ↔ (lo = 1 → (vx s).getD 0 0 = 0) ∧
      EncOk lk.G (Spec.Rsa.bytesAt s.mem (s.gpr .r8) lk.G.len) ((vx s).drop lo) ((s.gpr .rsi).toNat - lo) z
        (Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32)))
    (hsl : Spec.RsaPss.expectedSaltLen (stackArg s 1) ((stackArg s 2).setWidth 32) =
      if fixed then some (stackArg s 1).toNat else none) :
    WP isa (verifyMain H pubN pubC) u (VDone lk.G s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D = lk.G.len := lk.len.symm
  have hG := validG hH lk.hash lk.len
  have c1 : oEm = 2560 := rfl
  have c5 : oRsa = 8192 := rfl
  rw [verifyMain, show [Code.block dbSlots, .block pubArgs, .call pubN pubC, .block acc0, mgfXor H, .block clearTop,
      posScan, posCheck H, clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H] =
    [Code.block dbSlots, .block pubArgs, .call pubN pubC] ++ ([.block acc0, mgfXor H, .block clearTop, posScan,
      posCheck H] ++ [clearY, copyDigest H, copyDb H, shift H, .block (verifyNb H), ctHash H, cmpH H]) from rfl]
  -- The public-key operation.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (vfront_ok hv hspC hdC hp L R hw hrd hM h17 h18 h19 h20 h22
    h26 h38 hax) fun u3 ⟨L3, wr3, rd3, cs3, hM3, V1, W1, R1, hW1, h23, h24, hV1, hO1⟩ => ?_)
  set k := (s.gpr .rsi).toNat with hk
  set db := k - lo - lk.G.len - 1 with hdb
  rw [show k - lo - (H.D + 2) + 1 = db by omega] at h24
  have g1 : ∀ j, j < nW → 4 ≤ j → j ≠ 23 → j ≠ 24 → W1 j = W j := fun j a b c d => hW1 j a b c d
  -- `acc` and the first nonzero byte of `DB`.
  refine WP.seqs_append (by simp) (by simp) (WP.mono (WP.keepIn (vmid_safe hH K) (by rw [vmid_xd K])
    (vmid_ok hH K lk L3 R1 (k := k) (lo := lo) (db := db) (z := z) (fixed := fixed)
      (by rw [g1 17 (by decide) (by decide) (by decide) (by decide), h17, hk, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      h23 h24 (by rw [g1 25 (by decide) (by decide) (by decide) (by decide), h25])
      (by rw [g1 26 (by decide) (by decide) (by decide) (by decide), h26])
      (by rw [g1 35 (by decide) (by decide) (by decide) (by decide), h35]) hlo (by omega) (by omega) hk2))
    fun u4 ⟨⟨L4, rd4, wr4, cs4, V3, W3, R3, h33, h34, h27, hW3, hV3, hO3⟩, f4⟩ => ?_)
  have hM4 := vframe_keep hp (wr3.trans hw) L3.rsp hM3 f4
  set x := vx s with hx
  have hxl : x.length = k := by
    simp only [hx, vx]
    cases hpo : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .rsi).toNat) with
    | none => simp only [Option.getD_none, RsaPss.zeros_length, hk]
    | some y => rw [Option.getD_some, publicOpChecked_length' hpo, bytesAt_length]
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
    rw [hW3 37 (by decide) (.inr (by decide)), g1 37 (by decide) (by decide) (by decide) (by decide), h37]
  have hpd : (if lz dbL < db then lz dbL else 0) < db := by split <;> omega
  have hrd4 : u4.rd = s.rd := by rw [rd4, rd3, hrd]
  have hwr4 : u4.wr = frR s :: s.wr := by rw [wr4, wr3, hw]
  have wDg := hp.wDg
  -- The salt, its hash, and the comparison.
  refine WP.mono (WP.keepIn (vback_safe hH K) (by rw [vback_xd K])
    (vback_ok hH K lk L4 R3 (lo := lo) (db := db) (pos := if lz dbL < db then lz dbL else 0) (dig := s.gpr .r8)
      h23' h24' h34 h27 h37' hlo (by omega) hpd (by omega)
      (fun i hi => ⟨⟨s.gpr .r8, lk.G.len⟩, List.mem_append_left _ (by rw [hrd4, hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => by
        have := hp.outside lk.G hp.ddgs hp.dKdg (a := s.gpr .r8 + BitVec.ofNat 64 i)
          (Offset.contains_base _ (by omega) (by omega))
        rwa [← hwr4] at this)))
    fun u5 ⟨⟨L5, rd5, wr5, cs5, ⟨V5, W5, R5, hW5⟩, hax5⟩, f5⟩ => ?_
  have g3 : ∀ j, j < nW → 34 < j → W3 j = W j := fun j hj h =>
    (hW3 j hj (.inr h)).trans (g1 j hj (by omega) (by omega) (by omega))
  have g5 : ∀ j, j < nW → 34 < j → j ≠ 44 → j ≠ 45 → j ≠ 46 → W5 j = W j := fun j hj h a b c =>
    (hW5 j hj (by omega) (by omega) (by omega) a b c).trans (g3 j hj h)
  refine ⟨L5, by rw [wr5, hwr4], fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ [Reg.r13, .r14, .r15, .rsp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp
    rw [cs5 r hr', cs4 r hr', cs3 r hr, hcs r hr]
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
  rw [hax5, h33, hmsg1, hmsg2, g1 36 (by decide) (by decide) (by decide) (by decide), h36]
  refine ite_setWidth ((Iff.trans (and_congr ?_ ?_) hV).trans hspec.symm)
  · have h0 := hV1 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [hV1 lo (by omega), show oEm + k - 1 = oEm + (k - 1) by omega, hV1 _ (by omega), h0]
  · rw [← hD]
    exact forall_congr' fun i => imp_congr_right fun hi => by rw [hHb i hi]

end VG.Proof.RsaPss.X86_64
