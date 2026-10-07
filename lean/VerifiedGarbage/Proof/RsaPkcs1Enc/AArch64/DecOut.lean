import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecSel

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: writing the output

`*msg_len` (`outInit_ok`) and the output, byte by byte (`selBody_ok`,
`selLoop_ok`): byte `i` of `out` is `outByte v ok kl i EM[i] AM[i]`.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.RsaPkcs1Enc (outByte)

theorem outInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : InRegions t.wr (slot t Q oML + BitVec.ofNat 64 0) 8) :
    WP isa (.block outInit) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (slot t Q oML) (t.gpr .x13) ∧
      u.gpr .x10 = (t.mem.writeW (slot t Q oML) (t.gpr .x13)).readW (Q + BitVec.ofNat 64 oScr) 64 +
        BitVec.ofNat 64 sAM ∧ u.gpr .x9 = 0 ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → u.gpr r = t.gpr r) := by
  have h104 := h 104 (by decide)
  have h168 := h 168 (by decide)
  have hw' : InRegions t.wr (t.mem.read (Q + BitVec.ofNat 64 104) 8 + BitVec.ofNat 64 0) 8 := hw
  apply WP.of_runBlock
  simp only [outInit, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oML, oScr, sAM, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, reduceCtorEq, ite_false, h104, h168, hw']
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    by rw [BitVec.add_zero]; rfl, by rw [BitVec.add_zero]; rfl, rfl,
    fun r h9 h10 => by simp only [h9, h10, ite_false]⟩

/-- The byte `selBody` stores, from its registers and the two bytes it loads. -/
def outB (m15 m14 kl i : BitVec 64) (e a : Byte) : Byte :=
  BitVec.setWidth 8 (BitVec.setWidth 32 ((((e.setWidth 64 ^^^ a.setWidth 64) &&& m15) ^^^ a.setWidth 64) &&&
    (m14 &&& ~~~(if kl.toNat ≤ i.toNat then (0 : BitVec 64) else BitVec.allOnes 64))))

theorem selBody_ok {t : State} (he : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1)
    (ha : InRegions (t.rd ++ t.wr) (t.gpr .x10 + BitVec.ofNat 64 0) 1)
    (hw : InRegions t.wr (t.gpr .x11 + BitVec.ofNat 64 0) 1) :
    WP isa (.block selBody) t fun u => SameR t u ∧
      u.mem = t.mem.write (t.gpr .x11) 1 (outB (t.gpr .x15) (t.gpr .x14) (t.gpr .x16) (t.gpr .x9)
        (t.mem (t.gpr .x11)) (t.mem (t.gpr .x10))) ∧
      u.gpr .x9 = t.gpr .x9 + BitVec.ofNat 64 1 ∧ u.gpr .x11 = t.gpr .x11 + BitVec.ofNat 64 1 ∧
      u.gpr .x10 = t.gpr .x10 + BitVec.ofNat 64 1 ∧ u.gpr .x12 = t.gpr .x12 - BitVec.ofNat 64 1 ∧
      u.gpr .x14 = t.gpr .x14 ∧ u.gpr .x15 = t.gpr .x15 ∧ u.gpr .x16 = t.gpr .x16 := by
  apply WP.of_runBlock
  simp only [selBody, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load, State.store,
    State.addWithCarry, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, ite_true, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.v_write, reduceCtorEq, ite_false,
    he, ha, hw]
  refine ⟨⟨rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, ?_, trivial⟩
  simp only [BitVec.add_zero, Bytes.read_one, Bytes.byte64, sbc_self, Bytes.rotateRight_zero]
  rfl

theorem outB_eq (v ok : Bool) {kl i : Nat} (hkl : kl < 2 ^ 64) (hi : i < 2 ^ 64) (e a : Byte) :
    outB (bm v) (bm ok) (BitVec.ofNat 64 kl) (BitVec.ofNat 64 i) e a = outByte v ok kl i e a := by
  have sel : ((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64 =
      (if v then e else a).setWidth 64 := by
    cases v
    · simp [bm]
    · simp only [bm, ite_true, BitVec.and_allOnes]
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  simp only [outB, sel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkl, Nat.mod_eq_of_lt hi, outByte]
  by_cases hk : kl ≤ i
  · cases ok
    · simp only [hk, ↓reduceIte, bm, Bool.false_eq_true, and_false]
      apply BitVec.eq_of_toNat_eq; simp
    · simp only [hk, ↓reduceIte, bm, and_self]
      rw [show (~~~(0 : BitVec 64)) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, BitVec.and_allOnes,
        Bytes.byte_rt64]
  · simp only [hk, ↓reduceIte, false_and, BitVec.not_allOnes, BitVec.and_zero]
    apply BitVec.eq_of_toNat_eq; simp

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- After `i` bytes of the output. -/
structure OInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R MLV : BitVec 64)
    (EM AM : List Byte) (v ok : Bool) (kl : Nat) (i : Nat) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  r : t.mem.readW (L.Q + BitVec.ofNat 64 oR) 64 = R
  ml : t.mem.readW L.ml 64 = MLV
  x9 : t.gpr .x9 = BitVec.ofNat 64 i
  x11 : t.gpr .x11 = L.out + BitVec.ofNat 64 i
  x10 : t.gpr .x10 = scA L sAM + BitVec.ofNat 64 i
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - i)
  x14 : t.gpr .x14 = bm ok
  x15 : t.gpr .x15 = bm v
  x16 : t.gpr .x16 = BitVec.ofNat 64 kl
  done : ∀ j < i, t.mem (L.out + BitVec.ofNat 64 j) = outByte v ok kl j (EM.getD j 1) (AM.getD j 0)
  todo : ∀ j, i ≤ j → j < L.k.toNat → t.mem (L.out + BitVec.ofNat 64 j) = EM.getD j 1
  am : ∀ j < L.k.toNat, t.mem (scA L sAM + BitVec.ofNat 64 j) = AM.getD j 0

theorem selLoop_ok (hL : L.Ok) {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 64) {t : State} (h : OInv L g vv m₀ R MLV EM AM v ok kl 0 t) :
    WP isa selLoop t (OInv L g vv m₀ R MLV EM AM v ok kl L.k.toNat) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hbO := hL.bO
  have hs := hL.s8192
  have hbS := hL.bS
  refine Bytes.count_loop (by omega) (OInv L g vv m₀ R MLV EM AM v ok kl) (fun i hi u hu => ?_) h
  have hc := hu.ctx
  have he : InRegions (u.rd ++ u.wr) (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]; exact hc.outR hi
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .x10 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x10, BitVec.add_zero, Enc.add_add]
    exact (Covers.right (scCov hL hc (a := sAM + i) (n := 1) (by unfold sAM scrBytes; omega))) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hw : InRegions u.wr (u.gpr .x11 + BitVec.ofNat 64 0) 1 := by
    rw [hu.x11, BitVec.add_zero]
    exact ⟨L.OUT, by rw [hc.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (selBody_ok he ha hw) fun w ⟨S, hm, w9, w11, w10, w12, w14, w15, w16⟩ => ?_
  have hb : outB (u.gpr .x15) (u.gpr .x14) (u.gpr .x16) (u.gpr .x9) (u.mem (u.gpr .x11)) (u.mem (u.gpr .x10)) =
      outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
    rw [hu.x15, hu.x14, hu.x16, hu.x9, hu.x11, hu.x10, hu.todo i (Nat.le_refl _) hi, hu.am i hi,
      outB_eq _ _ hkl (by omega)]
  rw [hb, hu.x11] at hm
  have hf : Frame [⟨L.out + BitVec.ofNat 64 i, 1⟩] u.mem w.mem := by
    rw [hm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hsub : Region.Sub ⟨L.out + BitVec.ofNat 64 i, 1⟩ L.OUT := Offset.sub_base _ (by omega)
  have hne : ∀ j, j ≠ i → j < L.k.toNat → L.out + BitVec.ofNat 64 j ≠ L.out + BitVec.ofNat 64 i :=
    fun j hj hjk => Offset.add_ofNat_ne _ (by omega) (by omega) hj
  have hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - (i + 1)) := by
    rw [w12, hu.x12, Bytes.counter_step hi L.k.isLt]
  refine ⟨⟨hc.store hL S.rd S.wr S.sp S.v (fun r hr _ => S.cs r hr) hf fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (.inl hsub), ?_, ?_, ?_, ?_, ?_, hx12, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
      rw [List.mem_singleton.mp hX]
      exact hL.stk_buf (by decide) (.inl hsub)) (by decide), hu.r]
  · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
      rw [List.mem_singleton.mp hX]
      exact (hL.oM.sub_left hsub).symm) (by decide), hu.ml]
  · rw [w9, hu.x9, ← BitVec.ofNat_add]
  · rw [w11, hu.x11, Enc.add_add]
  · rw [w10, hu.x10, Enc.add_add]
  · rw [w14, hu.x14]
  · rw [w15, hu.x15]
  · rw [w16, hu.x16]
  · intro j hj
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Bytes.write1_ne _ _ (hne j (by omega) (by omega)), hu.done j hj]
    · exact Bytes.write1_self _ _ _
  · intro j hj hjk
    rw [hm, Bytes.write1_ne _ _ (hne j (by omega) hjk), hu.todo j (by omega) hjk]
  · intro j hj
    rw [hf.bytes (R := ⟨scA L sAM, L.k.toNat⟩) (fun X hX => by
      rw [List.mem_singleton.mp hX]
      exact (hL.oS.sub_left hsub).symm.sub_left (sub_trans (scSub (by unfold sAM scrBytes; omega)) hL.sc_sub))
      (by show L.k.toNat ≤ 2 ^ 64; omega) hj, hu.am j hj]
  · rw [hx12]; exact Bytes.counter_ne hi L.k.isLt

end

theorem retR_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block [.ldrSp .x0 oR]) t fun u => SameR t u ∧ u.mem = t.mem ∧ u.gpr .x0 = slot t Q oR := by
  have h176 := h 176 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oR, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, BitVec.setWidth_eq,
    h176]
  exact ⟨⟨rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl⟩

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64} {EM : List Byte}
  {kd : List Byte}

/-- At the end of the body: the output and `*msg_len` written, the result in `x0`. -/
structure Fin (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM AM : List Byte) (v ok : Bool) (len : Nat) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = R
  out : ∀ i < L.k.toNat, t.mem (L.out + BitVec.ofNat 64 i) =
    outByte v ok (L.k.toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : t.mem.readW L.ml 64 = BitVec.ofNat 64 len &&& bm ok

/-- `AM`. -/
abbrev amOf (L : Lay) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") L.k.toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (L : Lay) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM L.k.toNat

/-- The selected length. -/
abbrev lenOf (L : Lay) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM L EM) ((firstZero EM L.k.toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength L.k.toNat (clOf kd)) L.k.toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- After the validity and `*msg_len`: the selection's loop from byte 0. -/
theorem selInit_ok (hL : L.Ok) {t : State} (h : SC L g vv m₀ R EM kd t) :
    WP isa (.seq (.block validBlock) (.block outInit)) t (OInv L g vv m₀ R
      (BitVec.ofNat 64 (lenOf L EM kd) &&& bm (decide (R = 1))) EM (amOf L kd) (vOfEM L EM) (decide (R = 1))
      (L.k.toNat - lenOf L EM kd) 0) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hnQ := hL.nQ
  have hc := h.amr.post
  have hsep := sep_lt EM (k := L.k.toNat) (by omega)
  have hal := Proof.RsaPkcs1Enc.altLength_le L.k.toNat (clOf kd)
  have hK : slot t L.Q oK = BitVec.ofNat 64 L.k.toNat := by
    rw [slot, hc.ctx.kept.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hO : slot t L.Q oOut = L.out := hc.ctx.kept.out
  refine WP.seq (WP.mono (validBlock_ok hc.ctx.sp hc.slots (by rw [hO]; exact hc.ctx.outR (by omega))
    (by rw [hO]; exact hc.ctx.outR (by omega)) h.x17 h.x15 h.x16 h.al hK (by omega))
    fun t₁ ⟨S₁, x11, x12, x17, x15, x14, x13, x16⟩ => ?_)
  have hc₁ := hc.same S₁
  -- The values the block computed.
  have e0 : t.mem (slot t L.Q oOut) = EM.getD 0 1 := by rw [hO, ← hc.em, bytes_getD' _ _ (by omega), BitVec.add_zero]
  have e1 : t.mem (slot t L.Q oOut + BitVec.ofNat 64 1) = EM.getD 1 1 := by
    rw [hO, ← hc.em, bytes_getD' _ _ (by omega)]
  have eR : slot t L.Q oR = R := hc.r
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM L.k.toNat).isSome
      ((firstZero EM L.k.toNat).getD 0) then BitVec.ofNat 64 L.k.toNat - BitVec.ofNat 64 ((firstZero EM L.k.toNat).getD 0) - 1
      else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength L.k.toNat (clOf kd))) = BitVec.ofNat 64 (lenOf L EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · rw [Offset.ofNat_sub_ofNat (by omega), show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        Offset.ofNat_sub_ofNat (by omega)]
    · rfl
  have hlen : lenOf L EM kd ≤ L.k.toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega
  simp only [e0, e1, eR] at x15 x14 x13 x16
  rw [eL] at x13
  rw [eL, Offset.ofNat_sub_ofNat hlen] at x16
  rw [hO] at x11
  -- `*msg_len`.
  have hml : slot t₁ L.Q oML = L.ml := by rw [slot, S₁.mem]; exact hc.ctx.kept.ml
  refine WP.mono (outInit_ok hc₁.ctx.sp hc₁.slots (by
    rw [hml, BitVec.add_zero]
    exact ⟨L.ML, by rw [hc₁.ctx.wr]; simp, Region.contains_self _ _⟩)) fun t₂ ⟨S₂, m₂, x10, x9, o₂⟩ => ?_
  rw [hml, x13] at m₂ x10
  have F₂ : Frame [L.ML] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have frm : ∀ d, d + 8 ≤ 224 → t₂.mem.readW (L.Q + BitVec.ofNat 64 d) 64 = t₁.mem.readW (L.Q + BitVec.ofNat 64 d) 64 :=
    fun d hd => F₂.readW (Region.contains_self _ _) (fun X hX => by
      rw [List.mem_singleton.mp hX]; exact hL.stk_buf hd (.inr (.inl fun _ h => h))) (by decide)
  rw [show (t₁.mem.writeW L.ml (BitVec.ofNat 64 (lenOf L EM kd) &&& bm (decide (R = 1)))).readW
      (L.Q + BitVec.ofNat 64 oScr) 64 = L.scr by rw [← m₂, frm _ (by decide), S₁.mem]; exact hc.ctx.kept.scr] at x10
  have hc₂ : Ctx L g vv m₀ t₂ := hc₁.ctx.store hL S₂.rd S₂.wr S₂.sp S₂.v (fun r hr _ => S₂.cs r hr) F₂ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (.inr (.inl fun _ h => h))
  have bk : ∀ (X : Region), X.Disjoint L.ML → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY => by rw [List.mem_singleton.mp hY]; exact hX) hl hi, S₁.mem]
  exact
    { ctx := hc₂
      r := by rw [frm _ (by decide), S₁.mem]; exact hc.r
      ml := by rw [m₂, Mem.readW_writeW_self64]
      x9 := by rw [x9]; rfl
      x11 := by rw [o₂ .x11 (by decide) (by decide), x11, BitVec.add_zero]
      x10 := by rw [x10, BitVec.add_zero]
      x12 := by rw [o₂ .x12 (by decide) (by decide), x12, Nat.sub_zero]
      x14 := by rw [o₂ .x14 (by decide) (by decide), x14]
      x15 := by rw [o₂ .x15 (by decide) (by decide), x15]
      x16 := by rw [o₂ .x16 (by decide) (by decide), x16]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [bk L.OUT hL.oM (by show L.k.toNat ≤ 2 ^ 64; omega) j hj, ← hc.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [bk ⟨scA L sAM, L.k.toNat⟩ ((hL.mS.symm.sub_left (sub_trans (scSub (by unfold sAM scrBytes; omega))
          hL.sc_sub)).symm |>.symm) (by show L.k.toNat ≤ 2 ^ 64; omega) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA L sAM) L.k.toNat = amOf L kd := h.amr.am
        rw [← ham, bytes_getD' _ _ hj] }

theorem selPart_ok (hL : L.Ok) {t : State} (h : SC L g vv m₀ R EM kd t) :
    WP isa selPart t (Fin L g vv m₀ R EM (amOf L kd) (vOfEM L EM) (decide (R = 1)) (lenOf L EM kd)) := by
  have hk64 := hL.k64
  refine WP.assoc (WP.seq (WP.mono (selInit_ok hL h) fun t₂ hOi => ?_))
  refine WP.seq (WP.mono (selLoop_ok hL (by omega) hOi) fun t₃ h₃ => ?_)
  refine WP.mono (retR_ok h₃.ctx.sp (fun d hd => h₃.ctx.inFrR (by unfold frameBytes; omega))) fun t₄ ⟨S₄, m₄, x0⟩ => ?_
  refine ⟨h₃.ctx.regs S₄.rd S₄.wr S₄.sp m₄ S₄.v fun r hr _ => S₄.cs r hr, by rw [x0]; exact h₃.r,
    fun i hi => by rw [m₄]; exact h₃.done i hi, by rw [m₄]; exact h₃.ml⟩

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
