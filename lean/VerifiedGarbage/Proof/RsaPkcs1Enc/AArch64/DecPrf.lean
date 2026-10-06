import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecMsg

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: a block of IRPRF

The blocks of `prfBody` that set registers and the counter, and one block of
IRPRF (`prfBody_ok`): `HMAC(KDK, I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2))` to
`scratch + dst + 32 i`, the counter `i` in its slot advanced.
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

theorem imm16 {n : Nat} (hn : n < 65536) : BitVec.setWidth 64 (BitVec.ofNat 16 n) <<< 0 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem prfHead_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block (scr .x9 sMsg ++ ([.ldrSp .x11 oI, .ldrSp .x12 oK] : List Instr))) t fun u => Same t u ∧
      u.gpr .x9 = slot t Q oScr + BitVec.ofNat 64 sMsg ∧ u.gpr .x11 = slot t Q oI ∧ u.gpr .x12 = slot t Q oK := by
  have h168 := h 168 (by decide)
  have h184 := h 184 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oI, oK, sMsg, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h184, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl⟩

theorem prfUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) {n : Nat} (hn : n < 65536) :
    WP isa (.block (prfUpdArgs n)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = BitVec.ofNat 64 64 ∧ u.gpr .x2 = slot t Q oScr + BitVec.ofNat 64 sMsg ∧
      u.gpr .x3 = BitVec.ofNat 64 n ∧ u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  apply WP.of_runBlock
  simp only [prfUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, sSt, sMsg, sWork, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    imm16 hn, rfl⟩

theorem prfFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) {n dst : Nat} (hn : 64 + n < 65536)
    (hd : dst < 4096) :
    WP isa (.block (prfFinArgs n dst)) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oScr + BitVec.ofNat 64 sOuter ∧ u.gpr .x2 = BitVec.ofNat 64 (64 + n) ∧
      u.gpr .x3 = (slot t Q oI <<< 5) + (slot t Q oScr + BitVec.ofNat 64 dst) ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [prfFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oI, sSt, sOuter, sWork, hd, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h184]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl,
    imm16 hn, rfl, rfl⟩

/-- Same, but memory: the regions, the stack pointer, the vector registers and the callee-saved ones. -/
structure SameR (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  cs : ∀ r ∈ preserved, u.gpr r = t.gpr r

theorem incrCL_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 184) 8) :
    WP isa (.block (incr [.movz .x .x12 8 0])) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (slot t Q oI + 1) ∧
      u.gpr .x12 = BitVec.ofNat 64 8 - (slot t Q oI + 1) := by
  have h184 := h 184 (by decide)
  apply WP.of_runBlock
  simp only [incr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oI, BitVec.add_zero, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq, ite_false, h184, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl⟩

theorem incrAM_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : InRegions t.wr (Q + BitVec.ofNat 64 184) 8) :
    WP isa (.block (incr [.ldrSp .x12 oNB])) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (slot t Q oI + 1) ∧
      u.gpr .x12 = slot t Q oNB - (slot t Q oI + 1) := by
  have h184 := h 184 (by decide)
  have h192 := h 192 (by decide)
  have e : (t.mem.writeW (Q + BitVec.ofNat 64 184) (slot t Q oI + 1)).readW (Q + BitVec.ofNat 64 192) 64 =
      slot t Q oNB :=
    Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)
  apply WP.of_runBlock
  simp only [incr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.read, State.load, State.store, Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp, oI, oNB, BitVec.add_zero, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq, ite_false, h184, h192, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl,
    congrArg (fun x => x - (slot t Q 184 + 1)) e⟩

/-! ## A block -/

section
variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- After block `i` of IRPRF from `t`: the block `blk` at `scratch + o`, the counter advanced, the blocks
left in `x12` (from `C`), and every other range of `scratch` from 1040 on as in `t`. -/
structure PrfStep (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (nbv : BitVec 64) (o : Nat) (blk : List Byte) (C : BitVec 64) (i : Nat) (t w : State) :
    Prop where
  post : Post L g vv m₀ R EM w
  ctr : slot w L.Q oI = BitVec.ofNat 64 (i + 1)
  nb : slot w L.Q oNB = nbv
  out : Spec.Rsa.bytesAt w.mem (scA L o) 32 = blk
  x12 : w.gpr .x12 = C - BitVec.ofNat 64 (i + 1)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + 32 ≤ a) →
    Spec.Rsa.bytesAt w.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l

theorem Post.sameR {t : State} (hc : Post L g vv m₀ R EM t) {u : State} (h : SameR t u) (hm : u.mem = t.mem) :
    Post L g vv m₀ R EM u :=
  hc.regs h.rd h.wr h.sp hm h.v fun r hr _ => h.cs r hr

theorem shl5 (i dst : Nat) (scr : Addr) :
    (BitVec.ofNat 64 i <<< 5) + (scr + BitVec.ofNat 64 dst) = scr + BitVec.ofNat 64 (dst + 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem prfBody_ok (hL : L.Ok) (hP : 16 ≤ L.P) {label : List Nat} {len count : List Instr} {dst : Nat}
    {t : State} {i : Nat} {kd text : List Byte} {nbv C : BitVec 64} (hc : Post L g vv m₀ R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd) (hctr : slot t L.Q oI = BitVec.ofNat 64 i)
    (hnb : slot t L.Q oNB = nbv) (hi : i < 256) (hd1 : 1040 ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes)
    (hdst : dst < 4096) (hn : label.length + 4 ≤ 16) (htl : text.length = label.length + 4)
    (hmsg : ∀ u, Post L g vv m₀ R EM u → u.gpr .x9 = scA L sMsg → u.gpr .x11 = BitVec.ofNat 64 i →
      u.gpr .x12 = L.k → WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧
        Frame [⟨scA L sMsg, 16⟩] u.mem w.mem ∧ Spec.Rsa.bytesAt w.mem (scA L sMsg) (label.length + 4) = text)
    (hcount : ∀ u, Post L g vv m₀ R EM u → slot u L.Q oNB = nbv → WP isa (.block (incr count)) u fun w =>
      SameR u w ∧ w.mem = u.mem.writeW (L.Q + BitVec.ofNat 64 oI) (slot u L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u L.Q oI + 1)) :
    WP isa (prfBody (HH v) label len dst count) t
      (PrfStep L g vv m₀ R EM nbv (dst + 32 * i) (Spec.Hmac.hmac Spec.Hmac.sha256 kd text) C i t) := by
  have hs := hL.s8192
  have hnQ := hL.nQ
  -- The message.
  refine WP.seq (WP.mono (prfHead_ok hc.ctx.sp hc.slots) fun t₁ ⟨S₁, x9, x11, x12⟩ => ?_)
  have hc₁ := hc.same S₁
  simp only [hc.ctx.kept.scr, hc.ctx.kept.k] at x9 x12
  rw [hctr] at x11
  refine WP.seq (WP.mono (hmsg t₁ hc₁ x9 x11 x12) fun t₂ ⟨R₂, F₂, hm₂⟩ => ?_)
  have msgSafe : ∀ r ∈ [(⟨scA L sMsg, 16⟩ : Region)], Safe L r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (scSub (by decide))
  have hc₂ := hc₁.step hL R₂.rd R₂.wr R₂.sp (fun r _ => by rw [R₂.v]) (fun r hr _ => R₂.cs r hr) F₂ msgSafe
  have k₂ : ∀ a l, 1040 ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₂.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₁ h₂ => by
    rw [bytes_keep F₂ (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scD hL (.inr (by unfold sMsg; omega)) h₂ (by decide))
      (by unfold scrBytes at h₂; omega), S₁.mem]
  have sl₂ : ∀ d, d + 8 ≤ frameBytes → slot t₂ L.Q d = slot t L.Q d := fun d hd => by
    show t₂.mem.readW _ 64 = t.mem.readW _ 64
    rw [F₂.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hL.stk_buf (by unfold frameBytes at hd; omega) (.inr (.inr (sub_trans (scSub (by decide))
        hL.sc_sub)))) (by decide), S₁.mem]
  -- HMAC's `init` with `KDK`.
  refine mac_init hL hP hc₂ (key := sKDK) (by decide) (by decide) fun u hu => ?_
  have hkd₂ : Spec.Rsa.bytesAt t₂.mem (scA L sKDK) 32 = kd := by rw [k₂ _ _ (by decide) (by decide), hkd]
  rw [hkd₂] at hu
  have hk0 := blockKey_length (key := kd) (by rw [← hkd]; simp [Spec.Rsa.bytesAt])
  -- `update` with the message.
  refine WP.seq (WP.mono (prfUpdArgs_ok hu.post.ctx.sp hu.post.slots (n := label.length + 4) (by omega))
    fun t₄ ⟨S₄, y0, y1, y2, y3, y4⟩ => ?_)
  have hc₄ := hu.post.same S₄
  simp only [hu.post.ctx.kept.scr] at y0 y2 y4
  have hmsg₄ : Spec.Rsa.bytesAt t₄.mem (scA L sMsg) (label.length + 4) = text := by
    rw [S₄.mem, hu.keep.scr _ _ (by decide) (by unfold sMsg scrBytes; omega) (.inr (Nat.zero_le _)), hm₂]
  refine WP.seq (WP.mono (mac_upd hL hP hc₄ (n := label.length + 4) y0 y1 y2 (by rw [y3, BitVec.toNat_ofNat]; omega) y4
    (Covers.right (scCov hL hc₄.ctx (by unfold sMsg scrBytes; omega)))
    (fun a l hal => scD hL (.inr (by unfold sMsg; omega)) (by unfold sMsg scrBytes; omega)
      (by unfold scrBytes; omega))
    (stkD hL hP (by unfold sMsg scrBytes; omega)) hk0 (by rw [S₄.mem]; exact hu.inner)
    (by rw [S₄.mem]; exact hu.outer)) fun t₅ ⟨hc₅, hi₅, ho₅, kp₅⟩ => ?_)
  rw [hmsg₄] at hi₅
  -- HMAC's `finalize` to the block.
  refine WP.seq (WP.mono (prfFinArgs_ok hc₅.ctx.sp hc₅.slots (n := label.length + 4) (dst := dst) (by omega) hdst)
    fun t₆ ⟨S₆, z0, z1, z2, z3, z4⟩ => ?_)
  have hc₆ := hc₅.same S₆
  have sl₅ : slot t₅ L.Q oI = BitVec.ofNat 64 i := by
    show t₅.mem.readW _ 64 = _
    rw [kp₅.slot _ (Nat.le_refl _) (by decide), S₄.mem, hu.keep.slot _ (Nat.le_refl _) (by decide)]
    exact (sl₂ oI (by decide)).trans hctr
  simp only [hc₅.ctx.kept.scr, sl₅] at z0 z1 z3 z4
  rw [shl5 i dst] at z3
  refine WP.seq (WP.mono (mac_fin hL hP hc₆ (o := dst + 32 * i) (by omega) hd2 hk0 (text := text)
    (by rw [htl]; omega) z0 z1 (by rw [z2, htl]) z3 z4 (by rw [S₆.mem]; exact hi₅)
    (by rw [S₆.mem]; exact ho₅)) fun t₇ ⟨hc₇, hb₇, kp₇⟩ => ?_)
  -- The counter.
  have nb₇ : slot t₇ L.Q oNB = nbv := by
    show t₇.mem.readW _ 64 = _
    rw [kp₇.slot _ (by decide) (by decide), S₆.mem, kp₅.slot _ (by decide) (by decide), S₄.mem,
      hu.keep.slot _ (by decide) (by decide)]
    exact (sl₂ oNB (by decide)).trans hnb
  have ct₇ : slot t₇ L.Q oI = BitVec.ofNat 64 i := by
    show t₇.mem.readW _ 64 = _
    rw [kp₇.slot _ (Nat.le_refl _) (by decide), S₆.mem]
    exact sl₅
  refine WP.mono (hcount t₇ hc₇ nb₇) fun w ⟨Sw, mw, xw⟩ => ?_
  have Fw : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩] t₇.mem w.mem := by
    rw [mw]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hcw := hc₇.step hL Sw.rd Sw.wr Sw.sp (fun r _ => by rw [Sw.v]) (fun r hr _ => Sw.cs r hr) Fw
    fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
  have one : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add]
  have kw : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt w.mem (scA L a) l = Spec.Rsa.bytesAt t₇.mem (scA L a) l := fun a l h₂ =>
    bytes_keep Fw (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ((hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub))))).symm)
      (by unfold scrBytes at h₂; omega)
  refine ⟨hcw, ?_, ?_, ?_, ?_, fun a l h₁ h₂ h₃ => ?_⟩
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_self64, ct₇, one]
  · show w.mem.readW _ 64 = _
    rw [mw, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
    exact nb₇
  · rw [kw _ _ hd2, hb₇]; rfl
  · rw [xw, ct₇, one]
  · rw [kw _ _ h₂, kp₇.scr _ _ (by omega) h₂ h₃, S₆.mem, kp₅.scr _ _ (by omega) h₂ (.inr (Nat.zero_le _)),
      S₄.mem, hu.keep.scr _ _ (by omega) h₂ (.inr (Nat.zero_le _)), k₂ _ _ h₁ h₂]

end

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
