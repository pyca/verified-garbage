import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecPrf

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `CL` and `AM`

The loops of IRPRF's blocks (`prfLoop_ok`): `CL = IRPRF(KDK, "length", 256)`
at `scratch + sCL` (`clLoop_ok`) and `AM = IRPRF(KDK, "message", k)` at
`scratch + sAM` (`amLoop_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

/-- After `i` blocks of IRPRF to `scratch + dst` from `t₀`, with the messages `textF`. -/
structure PInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (nbv : BitVec 64) (dst : Nat) (textF : Nat → List Byte) (t₀ : State)
    (i : Nat) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd
  ctr : slot t L.Q oI = BitVec.ofNat 64 i
  nb : slot t L.Q oNB = nbv
  out : ∀ j < i, Spec.Rsa.bytesAt t.mem (scA L (dst + 32 * j)) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 kd (textF j)
  keep : ∀ a l, 1040 ≤ a → a + l ≤ dst → Spec.Rsa.bytesAt t.mem (scA L a) l = Spec.Rsa.bytesAt t₀.mem (scA L a) l

theorem prfLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {label : List Nat} {len count : List Instr} {dst N : Nat}
    {kd : List Byte} {nbv C : BitVec 64} {textF : Nat → List Byte} {t₀ : State} (hN0 : 0 < N) (hN : N ≤ 256)
    (hd1 : 1136 ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 4096) (hn : label.length + 4 ≤ 16)
    (htl : ∀ i, (textF i).length = label.length + 4)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, ∀ u, Post L g vv m₀ R EM u → u.gpr .x9 = scA L sMsg → u.gpr .x11 = BitVec.ofNat 64 i →
      u.gpr .x12 = L.k → WP isa (.block (msgBytes label len)) u fun w => SameR u w ∧
        Frame [⟨scA L sMsg, 16⟩] u.mem w.mem ∧
        Spec.Rsa.bytesAt w.mem (scA L sMsg) (label.length + 4) = textF i)
    (hcount : ∀ u, Post L g vv m₀ R EM u → slot u L.Q oNB = nbv → WP isa (.block (incr count)) u fun w =>
      SameR u w ∧ w.mem = u.mem.writeW (L.Q + BitVec.ofNat 64 oI) (slot u L.Q oI + 1) ∧
        w.gpr .x12 = C - (slot u L.Q oI + 1))
    (h : PInv L g vv m₀ R EM kd nbv dst textF t₀ 0 t₀) :
    WP isa (.loop (prfBody (HH v) label len dst count) (.nonzero .x .x12)) t₀
      (PInv L g vv m₀ R EM kd nbv dst textF t₀ N) := by
  refine Bytes.count_loop hN0 (PInv L g vv m₀ R EM kd nbv dst textF t₀) (fun i hi u hu => ?_) h
  refine WP.mono (prfBody_ok hL hP hu.post hu.kdk hu.ctr hu.nb (by omega) (by omega) (by omega) hdst hn (htl i)
    (hmsg i hi) hcount) fun w hw => ⟨⟨hw.post, ?_, hw.ctr, hw.nb, fun j hj => ?_, fun a l h₁ h₂ => ?_⟩, ?_⟩
  · rw [hw.keep _ _ (by decide) (by unfold scrBytes at hd2; decide) (.inl (by unfold sKDK; omega)), hu.kdk]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.keep _ _ (by omega) (by omega) (.inl (by omega)), hu.out j hj]
    · exact hw.out
  · rw [hw.keep _ _ h₁ (by omega) (.inl (by omega)), hu.keep a l h₁ h₂]
  · rw [hw.x12, hC i hi]; exact Bytes.counter_ne hi (by omega)

/-! ## The bytes of the blocks -/

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} (n : Nat) (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun j hj => h j (by omega)),
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil, h n (by omega)]

theorem bytes_blocks (m : Mem) (o : Nat) : ∀ n, Spec.Rsa.bytesAt m (scA L o) (32 * n) =
    (List.range n).flatMap fun j => Spec.Rsa.bytesAt m (scA L (o + 32 * j)) 32
  | 0 => rfl
  | n + 1 => by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega, Enc.bytesAt_add, bytes_blocks m o n, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Enc.add_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-! ## The counters -/

theorem clInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q)
    (hw : ∀ d, 184 ≤ d → d + 8 ≤ 208 → InRegions t.wr (Q + BitVec.ofNat 64 d) 8) :
    WP isa (.block clInit) t fun u => SameR t u ∧
      u.mem = (t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64)).writeW (Q + BitVec.ofNat 64 oNB)
        (((t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64)).readW (Q + BitVec.ofNat 64 oK) 64 + 31) >>> 5) := by
  have h120 := h 120 (by decide)
  have w184 := hw 184 (by decide) (by decide)
  have w192 := hw 192 (by decide) (by decide)
  apply WP.of_runBlock
  simp only [clInit, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.load, State.store,
    Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    oI, oK, oNB, BitVec.add_zero, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq,
    ite_false, h120, w184, w192]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

theorem amInit_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (hw : InRegions t.wr (Q + BitVec.ofNat 64 184) 8) :
    WP isa (.block [.addSp .x9 0, .movz .x .x10 0 0, .str .x .x10 .x9 oI]) t fun u => SameR t u ∧
      u.mem = t.mem.writeW (Q + BitVec.ofNat 64 oI) (0 : BitVec 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.read, State.store,
    Size.bits, Size.bytes, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, ite_true, hsp,
    oI, BitVec.add_zero, Option.bind_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, reduceCtorEq,
    ite_false, hw]
  exact ⟨⟨rfl, rfl, hsp.symm, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl⟩

/-! ## The loops -/

theorem irprf_bytes {m : Mem} {kd label : List Byte} {length dst N : Nat} (hN : N = (length + 31) / 32)
    (hout : ∀ j < N, Spec.Rsa.bytesAt m (scA L (dst + 32 * j)) 32 = Proof.RsaPkcs1Enc.prfBlock kd label length j)
    (hl : length ≤ 32 * N) :
    Spec.Rsa.bytesAt m (scA L dst) length = Spec.RsaPkcs1Enc.irprf kd label length := by
  rw [Proof.RsaPkcs1Enc.irprf_eq, ← hN, ← flatMap_range_congr N hout, ← bytes_blocks, ← bytesAt_take _ _ hl]

theorem nb_eq {k : BitVec 64} (hk : k.toNat ≤ 1024) : (k + 31) >>> 5 = BitVec.ofNat 64 ((k.toNat + 31) / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (31 : BitVec 64).toNat = 31 from rfl]
  omega

/-- `CL` after its loop. -/
structure CLR (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd
  nb : slot t L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32)
  cl : Spec.Rsa.bytesAt t.mem (scA L sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- A byte of the message buffer is writable. -/
theorem Post.msgW (hL : L.Ok) {t : State} (hc : Post L g vv m₀ R EM t) :
    ∀ d < 16, InRegions t.wr (scA L sMsg + BitVec.ofNat 64 d) 1 := fun d hd => by
  rw [Enc.add_add]
  exact (scCov hL hc.ctx (a := sMsg + d) (n := 1) (by unfold sMsg scrBytes; omega)) _ _
    ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem clLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {kd : List Byte} (hc : Post L g vv m₀ R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = kd) :
    WP isa (clLoop (HH v)) t (CLR L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hnQ := hL.nQ
  refine WP.seq (WP.mono (clInit_ok hc.ctx.sp hc.slots fun d _ h₂ => hc.ctx.inFr (by unfold frameBytes; omega))
    fun t₁ ⟨S₁, m₁⟩ => ?_)
  have F₁ : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩, ⟨L.Q + BitVec.ofNat 64 oNB, 8⟩] t.mem t₁.mem := by
    rw [m₁]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_cons_self ..) _ ?_)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_ <;> exact Region.contains_self _ _
  have hc₁ := hc.step hL S₁.rd S₁.wr S₁.sp (fun r _ => by rw [S₁.v]) (fun r hr _ => S₁.cs r hr) F₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
    · exact .inr (.inr ⟨oNB, by decide, by show oNB + 8 ≤ frameBytes; decide, rfl⟩)
  have kp₁ : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₂ =>
    bytes_keep F₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm
      · exact (hL.stk_buf (d := oNB) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm)
      (by unfold scrBytes at h₂; omega)
  have sep : ∀ a b, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 344 → b + 8 ≤ 344 → Mem.Sep (L.Q + BitVec.ofNat 64 a) 8
      (L.Q + BitVec.ofNat 64 b) 8 := fun a b h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
  have ct₁ : slot t₁ L.Q oI = BitVec.ofNat 64 0 := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (sep _ _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64]; rfl
  have nb₁ : slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64, Mem.readW_writeW_sep (sep _ _ (by decide) (by decide) (by decide)) (by decide),
      hc.ctx.kept.k, nb_eq hk]
  refine WP.mono (prfLoop_ok (v := v) hL hP (label := lengthLabel) (len := clLen) (count := [.movz .x .x12 8 0])
    (dst := sCL) (N := 8) (C := BitVec.ofNat 64 8) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_length, lengthLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x9 x11 x12 => WP.mono (msgCL_ok x9 x11 (by omega) (hu.msgW hL))
      fun w ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e⟩, f, g⟩)
    (fun u hu _ => WP.mono (incrCL_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 184) (by decide)))
      fun w hw => hw)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), hkd], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, h₂.kdk, h₂.nb, ?_⟩
  exact irprf_bytes (N := 8) (by decide) (fun j hj => h₂.out j hj) (by decide)

/-- `AM` after its loop, and `CL` still. -/
structure AMR (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (kd : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA L sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA L sAM) L.k.toNat =
    Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") L.k.toNat

theorem amLoop_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} {kd : List Byte} (h : CLR L g vv m₀ R EM kd t) :
    WP isa (amLoop (HH v)) t (AMR L g vv m₀ R EM kd) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hnQ := hL.nQ
  have hc := h.post
  refine WP.seq (WP.mono (amInit_ok hc.ctx.sp (hc.ctx.inFr (d := 184) (by decide))) fun t₁ ⟨S₁, m₁⟩ => ?_)
  have F₁ : Frame [⟨L.Q + BitVec.ofNat 64 oI, 8⟩] t.mem t₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₁ := hc.step hL S₁.rd S₁.wr S₁.sp (fun r _ => by rw [S₁.v]) (fun r hr _ => S₁.cs r hr) F₁ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inr (.inr ⟨oI, Nat.le_refl _, by show oI + 8 ≤ frameBytes; decide, rfl⟩)
  have kp₁ : ∀ a l, a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₁.mem (scA L a) l = Spec.Rsa.bytesAt t.mem (scA L a) l := fun a l h₂ =>
    bytes_keep F₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hL.stk_buf (d := oI) (n := 8) (by decide) (.inr (.inr (sub_trans (scSub h₂) hL.sc_sub)))).symm)
      (by unfold scrBytes at h₂; omega)
  have ct₁ : slot t₁ L.Q oI = BitVec.ofNat 64 0 := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_self64]; rfl
  have nb₁ : slot t₁ L.Q oNB = BitVec.ofNat 64 ((L.k.toNat + 31) / 32) := by
    show t₁.mem.readW _ 64 = _
    rw [m₁, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by unfold oNB; omega) (by unfold oI; omega))
      (by decide)]
    exact h.nb
  have hN0 : 0 < (L.k.toNat + 31) / 32 := by omega
  refine WP.mono (prfLoop_ok (v := v) hL hP (label := messageLabel) (len := amLen) (count := [.ldrSp .x12 oNB])
    (dst := sAM) (N := (L.k.toNat + 31) / 32) (C := BitVec.ofNat 64 ((L.k.toNat + 31) / 32)) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * L.k.toNat) 2)
    hN0 (by omega) (by decide) (by unfold sAM scrBytes; omega) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_message, messageLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega))
    (fun i hi u hu x9 x11 x12 => WP.mono (msgAM_ok x9 x11 x12 (by omega) hk (hu.msgW hL))
      fun w ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e⟩, f, g⟩)
    (fun u hu hnb' => WP.mono (incrAM_ok hu.ctx.sp hu.slots (hu.ctx.inFr (d := 184) (by decide)))
      fun w ⟨a, b, c⟩ => ⟨a, b, by rw [c, hnb']⟩)
    ⟨hc₁, by rw [kp₁ _ _ (by decide), h.kdk], ct₁, nb₁, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.post, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide), kp₁ _ _ (by decide), h.cl]
  · exact irprf_bytes rfl (fun j hj => h₂.out j hj) (by omega)

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
