import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecMac

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: `KDK = HMAC(DH, C)`

HMAC-SHA-256 keyed with `DH` of the ciphertext, to `scratch + sKDK`
(`kdkMac_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt
open VG.Proof.Sha256.AArch64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
  {EM : List Byte}

theorem kdkUpdArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block kdkUpdArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = BitVec.ofNat 64 64 ∧ u.gpr .x2 = slot t Q oIn ∧ u.gpr .x3 = slot t Q oK ∧
      u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  have h160 := h 160 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [kdkUpdArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oIn, oK, sSt, sWork, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h160, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

theorem kdkFinArgs_ok {t : State} {Q : Addr} (hsp : t.sp = Q) (h : Slots t Q) :
    WP isa (.block kdkFinArgs) t fun u => Same t u ∧ u.gpr .x0 = slot t Q oScr + BitVec.ofNat 64 sSt ∧
      u.gpr .x1 = slot t Q oScr + BitVec.ofNat 64 sOuter ∧ u.gpr .x2 = slot t Q oK + BitVec.ofNat 64 64 ∧
      u.gpr .x3 = slot t Q oScr + BitVec.ofNat 64 sKDK ∧ u.gpr .x4 = slot t Q oScr + BitVec.ofNat 64 sWork := by
  have h168 := h 168 (by decide)
  have h120 := h 120 (by decide)
  apply WP.of_runBlock
  simp only [kdkFinArgs, scr, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.read, State.load, Size.bits, BitVec.setWidth_eq, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self,
    ite_true, hsp, oScr, oK, sSt, sOuter, sKDK, sWork, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, h168, h120]
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, preserved_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩, rfl, rfl, rfl,
    rfl, rfl⟩

/-- The ciphertext. -/
abbrev cOf (L : Lay) (m₀ : Mem) : List Byte := Spec.Rsa.bytesAt m₀ L.inp L.k.toNat

/-- The private exponent. -/
abbrev dOf (L : Lay) (m₀ : Mem) : List Byte := Spec.Rsa.bytesAt m₀ L.d L.dl.toNat

/-- After `kdkMac`: `KDK` at `scratch + sKDK`. -/
structure KD (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (R : BitVec 64)
    (EM : List Byte) (t : State) : Prop where
  post : Post L g vv m₀ R EM t
  kdk : Spec.Rsa.bytesAt t.mem (scA L sKDK) 32 = Spec.RsaPkcs1Enc.kdk L.k.toNat (dOf L m₀) (cOf L m₀)

theorem below_low (hL : L.Ok) (hP : 16 ≤ L.P) : Region.Sub (below L.Q 16) L.STK :=
  sub_trans (Offset.sub_below _ hP (by have := hL.pQ; omega)) Lay.Ok.low_stk

theorem kdkMac_ok (hL : L.Ok) (hP : 16 ≤ L.P) {t : State} (h : HD L g vv m₀ R EM t) :
    WP isa (kdkMac (HH v)) t (KD L g vv m₀ R EM) := by
  have hk := hL.k1024
  have hs := hL.s8192
  refine mac_init hL hP h.post (key := sDH) (by decide) (by decide) fun u hu => ?_
  have hc := hu.post
  refine WP.seq (WP.mono (kdkUpdArgs_ok hc.ctx.sp hc.slots) fun t₂ ⟨S₂, x0, x1, x2, x3, x4⟩ => ?_)
  have hc₂ := hc.same S₂
  simp only [hc.ctx.kept.scr, hc.ctx.kept.inp, hc.ctx.kept.k] at x0 x2 x3 x4
  have hk0 := blockKey_length (key := Spec.Rsa.bytesAt t.mem (scA L sDH) 32) (by simp [Spec.Rsa.bytesAt])
  refine WP.seq (WP.mono (mac_upd hL hP hc₂ x0 x1 x2 (by rw [x3]) x4
    (Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hc₂.ctx.rd]; simp))
    (fun a l hal => (hL.sR _ (ro_INP L)).symm.sub_right (sub_trans (scSub (by unfold scrBytes; omega)) hL.sc_sub))
    ((hL.kR _ (ro_INP L)).sub_left (below_low hL hP)) hk0 (by rw [S₂.mem]; exact hu.inner)
    (by rw [S₂.mem]; exact hu.outer)) fun t₃ ⟨hc₃, hi₃, ho₃, _⟩ => ?_)
  refine WP.seq (WP.mono (kdkFinArgs_ok hc₃.ctx.sp hc₃.slots) fun t₄ ⟨S₄, y0, y1, y2, y3, y4⟩ => ?_)
  have hc₄ := hc₃.same S₄
  simp only [hc₃.ctx.kept.scr, hc₃.ctx.kept.k] at y0 y1 y2 y3 y4
  have hC : Spec.Rsa.bytesAt t₂.mem L.inp L.k.toNat = cOf L m₀ := hc₂.ctx.bytes_ro hL (ro_INP L)
  refine WP.mono (mac_fin hL hP hc₄ (o := sKDK) (by decide) (by decide) hk0
    (text := Spec.Rsa.bytesAt t₂.mem L.inp L.k.toNat) (by simp [Spec.Rsa.bytesAt]; omega) y0 y1 ?_ y3 y4
    (by rw [S₄.mem]; exact hi₃) (by rw [S₄.mem]; exact ho₃)) fun t₅ ⟨hc₅, hb₅, _⟩ => ⟨hc₅, ?_⟩
  · rw [y2]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    omega
  · rw [hb₅, h.dh, hC]
    rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
