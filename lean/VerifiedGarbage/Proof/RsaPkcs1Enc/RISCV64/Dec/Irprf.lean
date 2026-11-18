module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Kdk
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPkcs1Enc.RISCV64.Dec.Prf`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: a block of IRPRF

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecMsg.lean`, `DecPrf.lean`): the message of
block `i`, `I2OSP(i, 2) ‖ label ‖ I2OSP(8 length, 2)`, at `scratch + sMsg`
(`msgCL_ok`, `msgAM_ok`), and one block of IRPRF (`prfBody_ok`):
`HMAC(KDK, message)` to `scratch + dst + 32 i`, the counter `i` (in `s8`)
advanced.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

variable {pc : Bool}

/-! ## The messages -/

theorem add_ofNat_inj (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (p + BitVec.ofNat 64 a = p + BitVec.ofNat 64 b) ↔ a = b :=
  ⟨fun e => Classical.byContradiction fun h => Offset.add_ofNat_ne p ha hb h e, fun e => e ▸ rfl⟩

theorem write1_eq (m : Mem) (b x : Addr) (v : BitVec (8 * 1)) :
    m.write b 1 v x = if x = b then v else m x := by
  by_cases h : x = b
  · simp only [h, ite_true]; exact VG.Proof.Bignum.RISCV64.write1_self _ _ _
  · simp only [h, ite_false]; exact Mem.write_apply fun h' => h (by bv_omega)

theorem byte_ofNat (x : Nat) : BitVec.setWidth 8 (BitVec.ofNat 64 x) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem ascii_length : Spec.RsaPkcs1Enc.ascii "length" = [0x6c, 0x65, 0x6e, 0x67, 0x74, 0x68] := by decide

theorem ascii_message : Spec.RsaPkcs1Enc.ascii "message" = [0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65] := by
  decide

theorem bytes10 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 10 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9)] :=
  rfl

theorem bytes11 (m : Mem) (B : Addr) : Spec.Rsa.bytesAt m B 11 = [m (B + BitVec.ofNat 64 0), m (B + BitVec.ofNat 64 1),
    m (B + BitVec.ofNat 64 2), m (B + BitVec.ofNat 64 3), m (B + BitVec.ofNat 64 4), m (B + BitVec.ofNat 64 5),
    m (B + BitVec.ofNat 64 6), m (B + BitVec.ofNat 64 7), m (B + BitVec.ofNat 64 8), m (B + BitVec.ofNat 64 9),
    m (B + BitVec.ofNat 64 10)] :=
  rfl

theorem am_lo (K : BitVec 64) : BitVec.setWidth 8 (K <<< 3) = BitVec.ofNat 8 (8 * K.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

theorem am_hi (K : BitVec 64) (hK : K.toNat ≤ 1024) :
    BitVec.setWidth 8 (K <<< 3 >>> 8) = BitVec.ofNat 8 (8 * K.toNat / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The writes of a message: `Frame` for each of its bytes. -/
theorem frame_bytes {m : Mem} {B : Addr} {d : Nat} (hd : d + 1 ≤ 16) {m' : Mem} (h : Frame [⟨B, 16⟩] m m')
    (v : BitVec (8 * 1)) : Frame [⟨B, 16⟩] m (m'.write (B + BitVec.ofNat 64 d) 1 v) :=
  h.write (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega_using [hd]))

theorem frame_bytes0 {m : Mem} {B : Addr} {m' : Mem} (h : Frame [⟨B, 16⟩] m m')
    (v : BitVec (8 * 1)) : Frame [⟨B, 16⟩] m (m'.write B 1 v) :=
  h.write (List.mem_singleton_self _) _ (by
    have := Offset.contains_base B (d := 0) (n := 1) (k := 16) (by decide) (by decide)
    rwa [BitVec.add_zero] at this)

theorem self_eq_add_ofNat (p : Addr) {k : Nat} (hk : k < 2 ^ 64) : (p = p + BitVec.ofNat 64 k) ↔ k = 0 := by
  have := add_ofNat_inj p (a := 0) (b := k) (by decide) hk
  rwa [BitVec.add_zero, eq_comm (a := 0)] at this

theorem add_ofNat_eq_self (p : Addr) {k : Nat} (hk : k < 2 ^ 64) : (p + BitVec.ofNat 64 k = p) ↔ k = 0 := by
  rw [eq_comm]; exact self_eq_add_ofNat p hk

theorem msgCL_ok {t : State} {B : Addr} {i : Nat} (h0 : t.gpr .s0 + BitVec.ofNat 64 sMsg = B)
    (h8 : t.gpr .s8 = BitVec.ofNat 64 i) (hi : i < 256) (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes lengthLabel clLen)) t fun u => (Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 10 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2) ∧
      Kept [.t1, .t2] t u := by
  simp only [msgBytes, lengthLabel, clLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
  have h0' : t.gpr .s0 + BitVec.ofNat 64 192 = B := h0
  obtain w0 : InRegions t.wr B 1 := by simpa using hw 0 (by decide)
  mrun [sMsg, h0', w0, hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide),
    hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide)]
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · refine frame_bytes (d := 9) (by decide) ?_ _
    refine frame_bytes (d := 8) (by decide) ?_ _
    refine frame_bytes (d := 7) (by decide) ?_ _
    refine frame_bytes (d := 6) (by decide) ?_ _
    refine frame_bytes (d := 5) (by decide) ?_ _
    refine frame_bytes (d := 4) (by decide) ?_ _
    refine frame_bytes (d := 3) (by decide) ?_ _
    refine frame_bytes (d := 2) (by decide) ?_ _
    refine frame_bytes (d := 1) (by decide) ?_ _
    exact frame_bytes0 (Frame.refl _ _) _
  · rw [bytes10]
    simp only [write1_eq, add_ofNat_inj, self_eq_add_ofNat, add_ofNat_eq_self, BitVec.add_zero, Nat.reducePow,
      Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, byte_ofNat, h8,
      Proof.RsaPkcs1Enc.i2osp_two, ascii_length, Nat.div_eq_of_lt hi]
    rfl
  · obtain ⟨a, b⟩ : r ≠ .t1 ∧ r ≠ .t2 := by simpa using hr
    simp only [a, b, ite_false]

theorem msgAM_ok {t : State} {B : Addr} {i : Nat} {K : BitVec 64} (h0 : t.gpr .s0 + BitVec.ofNat 64 sMsg = B)
    (h8 : t.gpr .s8 = BitVec.ofNat 64 i) (h1 : t.gpr .s1 = K) (hi : i < 256) (hK : K.toNat ≤ 1024)
    (hw : ∀ d < 16, InRegions t.wr (B + BitVec.ofNat 64 d) 1) :
    WP isa (.block (msgBytes messageLabel amLen)) t fun u => (Frame [⟨B, 16⟩] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem B 11 =
        Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++ Spec.Rsa.i2osp (8 * K.toNat) 2) ∧
      Kept [.t1, .t2] t u := by
  simp only [msgBytes, messageLabel, amLen, putByte, List.zipIdx, List.zipIdx_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
  have h0' : t.gpr .s0 + BitVec.ofNat 64 192 = B := h0
  obtain w0 : InRegions t.wr B 1 := by simpa using hw 0 (by decide)
  mrun [sMsg, h0', h1, w0, hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
    hw 5 (by decide), hw 6 (by decide), hw 7 (by decide), hw 8 (by decide), hw 9 (by decide), hw 10 (by decide)]
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  · refine frame_bytes (d := 9) (by decide) ?_ _
    refine frame_bytes (d := 10) (by decide) ?_ _
    refine frame_bytes (d := 8) (by decide) ?_ _
    refine frame_bytes (d := 7) (by decide) ?_ _
    refine frame_bytes (d := 6) (by decide) ?_ _
    refine frame_bytes (d := 5) (by decide) ?_ _
    refine frame_bytes (d := 4) (by decide) ?_ _
    refine frame_bytes (d := 3) (by decide) ?_ _
    refine frame_bytes (d := 2) (by decide) ?_ _
    refine frame_bytes (d := 1) (by decide) ?_ _
    exact frame_bytes0 (Frame.refl _ _) _
  · rw [bytes11]
    simp only [write1_eq, add_ofNat_inj, self_eq_add_ofNat, add_ofNat_eq_self, BitVec.add_zero, Nat.reducePow,
      Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, byte_ofNat, h8, am_lo, am_hi K hK,
      Proof.RsaPkcs1Enc.i2osp_two, ascii_message, Nat.div_eq_of_lt hi]
    rfl
  · obtain ⟨a, b⟩ : r ≠ .t1 ∧ r ≠ .t2 := by simpa using hr
    simp only [a, b, ite_false]

/-! ## A block -/

/-- After block `i` of IRPRF from `t`: the block `blk` at `scratch + o`, the
counter advanced, the blocks left in `t1` (from `C`), and every other range
of `scratch` from `sDH` on as in `t`. -/
structure PrfStep (s : State) (R : BitVec 64) (EM : List Byte) (o : Nat) (blk : List Byte) (C : BitVec 64)
    (i : Nat) (t w : State) : Prop extends Post s R EM w where
  ctr : w.gpr .s8 = BitVec.ofNat 64 (i + 1)
  nb : w.gpr .s9 = t.gpr .s9
  out : Spec.Rsa.bytesAt w.mem (scA s o) 32 = blk
  left : w.gpr .t1 = C - BitVec.ofNat 64 (i + 1)
  keep : ∀ a l, sDH ≤ a → a + l ≤ scrBytes → (a + l ≤ o ∨ o + 32 ≤ a) →
    Spec.Rsa.bytesAt w.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l

theorem shl5 (i dst : Nat) (scr : Addr) :
    (BitVec.ofNat 64 i <<< 5) + scr + BitVec.ofNat 64 dst = scr + BitVec.ofNat 64 (dst + 32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
include h

theorem keep_init {m m' : Mem} {X : Nat} (hX : X ≤ callX)
    (hf : Frame ([scR s sSt 96, scR s sOuter 96] ++ [below (fb s) X]) m m') {a l : Nat} (ha : 192 ≤ a)
    (hal : a + l ≤ scrBytes) : Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  keep_call h (ws := [(sSt, 96), (sOuter, 96)]) hX hf hal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> exact ⟨.inr (by dsimp only [sSt, sOuter]; omega_using [ha]), by decide⟩)

theorem keep_upd {m m' : Mem} {X : Nat} (hX : X ≤ callX)
    (hf : Frame ([scR s sSt 96] ++ [below (fb s) X]) m m') {a l : Nat} (ha : 96 ≤ a)
    (hal : a + l ≤ scrBytes) : Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  keep_call h (ws := [(sSt, 96)]) hX hf hal (by
    simp only [List.mem_singleton]
    rintro _ rfl; exact ⟨.inr (by dsimp only [sSt]; omega_using [ha]), by decide⟩)

theorem keep_fin {m m' : Mem} {X o : Nat} (hX : X ≤ callX) (ho : o + 32 ≤ scrBytes)
    (hf : Frame ([scR s sSt 96, scR s o 32] ++ [below (fb s) X]) m m') {a l : Nat} (ha : 96 ≤ a)
    (hal : a + l ≤ scrBytes) (hao : a + l ≤ o ∨ o + 32 ≤ a) :
    Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  keep_call h (ws := [(sSt, 96), (o, 32)]) hX hf hal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl)
    · exact ⟨.inr (by dsimp only [sSt]; omega_using [ha]), by decide⟩
    · exact ⟨hao, ho⟩)

theorem prfBody_ok {label : List Nat} {len count : List Instr} {dst : Nat} {t : State} {i : Nat}
    {kd text : List Byte} {C : BitVec 64} (hp : Post s R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd) (h8 : t.gpr .s8 = BitVec.ofNat 64 i)
    (hi : i < 256) (hd1 : sCL ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes) (hdst : dst < 2048)
    (hn : label.length + 4 ≤ 16) (htl : text.length = label.length + 4)
    (hmsg : ∀ u, Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w =>
        (Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧
          Spec.Rsa.bytesAt w.mem (scA s sMsg) (label.length + 4) = text) ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ u : State, u.gpr .s9 = t.gpr .s9 →
      WP isa (.block (count ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C - u.gpr .s8) :
    WP isa (prfBody label len dst count) t
      (PrfStep s R EM (dst + 32 * i) (Spec.Hmac.hmac Spec.Hmac.sha256 kd text) C i t) := by
  have zz := hmac_sizes
  unfold prfBody
  -- The message.
  refine WP.seq (WP.mono (hmsg t hp h8) fun t₁ ⟨⟨F₁, hm₁⟩, K₁⟩ => ?_)
  obtain P₁ : Post s R EM t₁ := hp.keep h K₁ F₁ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (scSub h (by decide)))
  obtain k₁ : ∀ a l, sDH ≤ a → a + l ≤ scrBytes →
      Spec.Rsa.bytesAt t₁.mem (scA s a) l = Spec.Rsa.bytesAt t.mem (scA s a) l := fun a l h₁ h₂ =>
    keep_sc F₁ h₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact scDisj (.inr (by unfold sMsg sDH at *; omega)) h₂ (by decide)
  obtain e8₁ : t₁.gpr .s8 = BitVec.ofNat 64 i := (K₁.gpr _ (by decide)).trans h8
  obtain e9₁ : t₁.gpr .s9 = t.gpr .s9 := K₁.gpr _ (by decide)
  -- HMAC's `init` with `KDK`.
  refine WP.seq (macInitArgs_ok h P₁ (key := sKDK) (by decide) fun u₁ P₂ a0 a1 a2 a3 m₂ K₂ => ?_)
  refine WP.seq (macInit_ok h P₂ (i := sSt) (u := sOuter) (k := sKDK) (by decide) (by decide) (by decide)
    (.inl (by decide)) (.inr (by decide)) (.inr (by decide)) a0 a1 a2 a3 fun u₂ P₃ A₂ hI hO => ?_)
  obtain hkd₂ : Spec.Sha256.bytesAt u₁.mem (scA s sKDK) 32 = kd := by
    show Spec.Rsa.bytesAt _ _ _ = _
    rw [m₂, k₁ _ _ (by decide) (by decide), hkd]
  rw [hkd₂] at hI hO
  obtain hk0 : (Spec.Hmac.blockKey hH.SH.H kd).length = 64 :=
    blockKey_length (by rw [← hkd]; simp [Spec.Rsa.bytesAt])
  have fr₂ := A₂.frame
  rw [P₂.sp] at fr₂
  obtain e8₂ : u₂.gpr .s8 = BitVec.ofNat 64 i := by rw [A₂.cs _ (by decide), K₂.gpr _ (by decide), e8₁]
  obtain e9₂ : u₂.gpr .s9 = t.gpr .s9 := by rw [A₂.cs _ (by decide), K₂.gpr _ (by decide), e9₁]
  -- `update` with the message.
  unfold prfUpdArgs
  refine WP.seq (wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
    wp_addi (imm := sMsg) (fun v₃ p₃ f₃ => wp_li (imm := label.length + 4) (by omega) fun v₄ p₄ f₄ =>
      wp_nil ?_) (by decide)) (by decide))
  obtain O : Only [.a0, .a1, .a2, .a3] u₂ v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  obtain P₄ : Post s R EM v₄ := P₃.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  obtain c0 : v₄.gpr .a0 = scA s sSt := by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P₃.s0]
  obtain c1 : v₄.gpr .a1 = BitVec.ofNat 64 64 := by rw [p₄.get .a1, p₃.get .a1, f₂]
  obtain c2 : v₄.gpr .a2 = scA s sMsg := by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P₃.s0]
  obtain c3 : (v₄.gpr .a3).toNat = label.length + 4 := by rw [f₄, BitVec.toNat_ofNat]; omega
  obtain hm₄ : Spec.Rsa.bytesAt v₄.mem (scA s sMsg) (label.length + 4) = text := by
    rw [O.mem, keep_init h zz.1 fr₂ (by decide) (by unfold sMsg scrBytes; omega), m₂, hm₁]
  refine WP.seq (shaUpd_ok h P₄ (a := sSt) (by decide) (dat := scA s sMsg) (len := label.length + 4) c0 c2 c3
    (Covers.right (scCov h P₄.wr (by unfold sMsg scrBytes; omega)))
    (scDisj (.inr (by decide)) (by unfold sMsg scrBytes; omega) (by decide))
    (lowSc h (by decide) (by unfold sMsg scrBytes; omega)) fun u₃ P₅ A₃ r₃ => ?_)
  have fr₃ := A₃.frame
  rw [P₄.sp] at fr₃
  obtain hI₃ := r₃ _ (by rw [O.mem]; exact hI) (by rw [c1, xorPad_length, hk0])
  rw [show Spec.Sha256.bytesAt v₄.mem (scA s sMsg) (label.length + 4) = text from hm₄] at hI₃
  obtain hO₃ : hH.SH.Repr u₃.mem (scA s sOuter) (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H kd) Spec.Hmac.opad) :=
    repr_call h (ws := [(sSt, 96)]) (X := sha256.F) (by decide) fr₃ (by decide)
      (by simp only [List.mem_singleton]; rintro _ rfl; exact ⟨.inr (by decide), by decide⟩) (by rw [O.mem]; exact hO)
  obtain e8₃ : u₃.gpr .s8 = BitVec.ofNat 64 i := by rw [A₃.cs _ (by decide), O.get .s8, e8₂]
  obtain e9₃ : u₃.gpr .s9 = t.gpr .s9 := by rw [A₃.cs _ (by decide), O.get .s9, e9₂]
  -- HMAC's `finalize` to the block.
  unfold prfFinArgs
  refine WP.seq (wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
    wp_li (imm := 64 + (label.length + 4)) (by omega) fun w₃ q₃ g₃ => wp_sll (sh := 5) (fun w₄ q₄ g₄ =>
    wp_add fun w₅ q₅ g₅ => wp_addi (imm := dst) (fun w₆ q₆ g₆ => wp_nil ?_) hdst)) (by decide)) (by decide))
  obtain O' : Only [.a0, .a1, .a2, .a3] u₃ w₆ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans q₆))))).mono
  obtain P₆ : Post s R EM w₆ := P₅.keep h O'.keep (ws := []) (by rw [O'.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  obtain d0 : w₆.gpr .a0 = scA s sSt := by
    rw [q₆.get .a0, q₅.get .a0, q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P₅.s0]
  obtain d1 : w₆.gpr .a1 = scA s sOuter := by
    rw [q₆.get .a1, q₅.get .a1, q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P₅.s0]
  obtain d2 : w₆.gpr .a2 = BitVec.ofNat 64 (64 + (label.length + 4)) := by
    rw [q₆.get .a2, q₅.get .a2, q₄.get .a2, g₃]
  obtain d3 : w₆.gpr .a3 = scA s (dst + 32 * i) := by
    rw [g₆, g₅, g₄, q₃.get .s8, q₂.get .s8, q₁.get .s8, e8₃, q₄.get .s0, q₃.get .s0, q₂.get .s0, q₁.get .s0,
      P₅.s0, shl5]
  refine WP.seq (macFin_ok h P₆ (i := sSt) (u := sOuter) (o := dst + 32 * i) (by decide) (by decide) hd2
    (.inl (by decide)) (.inl (by unfold sSt sCL at *; omega)) (.inl (by unfold sOuter sCL at *; omega))
    d0 d1 d3 fun u₄ P₇ A₄ hmac => ?_)
  have fr₄ := A₄.frame
  rw [P₆.sp] at fr₄
  obtain hb₄ := hmac _ text hk0 (by rw [hk0, htl]; omega) (by rw [O'.mem]; exact hI₃) (by rw [d2, htl])
    (by rw [O'.mem]; exact hO₃)
  obtain e8₄ : u₄.gpr .s8 = BitVec.ofNat 64 i := by rw [A₄.cs _ (by decide), O'.get .s8, e8₃]
  obtain e9₄ : u₄.gpr .s9 = t.gpr .s9 := by rw [A₄.cs _ (by decide), O'.get .s9, e9₃]
  -- The counter.
  simp only [incr, List.cons_append, List.nil_append]
  refine wp_addi (imm := 1) (fun x₁ r₁ i₁ => WP.mono (hcount x₁ (by rw [r₁.get .s9, e9₄]))
    fun w ⟨Ow, xw⟩ => ?_) (by decide)
  obtain Ow' : Only [.s8, .t1] u₄ w := (r₁.trans Ow).mono
  obtain Pw : Post s R EM w := P₇.keep h Ow'.keep (ws := []) (by rw [Ow'.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  obtain one : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := BitVec.ofNat_add _ _ |>.symm
  obtain c8 : w.gpr .s8 = BitVec.ofNat 64 (i + 1) := by rw [Ow.get .s8, i₁, e8₄, one]
  refine ⟨Pw, c8, by rw [Ow'.get .s9, e9₄], ?_, by rw [xw, i₁, e8₄, one], fun a l h₁ h₂ h₃ => ?_⟩
  · rw [Ow'.mem]; exact hb₄
  · have hd : sDH ≤ a := h₁
    rw [Ow'.mem, keep_fin h zz.2.1 hd2 fr₄ (by unfold sDH at hd; omega) h₂ h₃, O'.mem,
      keep_upd h (by decide) fr₃ (by unfold sDH at hd; omega) h₂, O.mem,
      keep_init h zz.1 fr₂ (by unfold sDH at hd; omega) h₂, m₂, k₁ _ _ h₁ h₂]

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: `CL` and `AM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecIrprf.lean`): the loops of IRPRF's blocks
(`prfLoop_ok`): `CL = IRPRF(KDK, "length", 256)` at `scratch + sCL`
(`clLoop_ok`) and `AM = IRPRF(KDK, "message", k)` at `scratch + sAM`
(`amLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

variable {pc : Bool}

/-- After `i` blocks of IRPRF to `scratch + dst` from `t₀`, with the messages `textF`. -/
structure PInv (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (dst : Nat)
    (textF : Nat → List Byte) (t₀ : State) (i : Nat) (t : State) : Prop extends Post s R EM t where
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  ctr : t.gpr .s8 = BitVec.ofNat 64 i
  nb : t.gpr .s9 = t₀.gpr .s9
  out : ∀ j < i, Spec.Rsa.bytesAt t.mem (scA s (dst + 32 * j)) 32 = Spec.Hmac.hmac Spec.Hmac.sha256 kd (textF j)
  keep : ∀ a l, sDH ≤ a → a + l ≤ dst → Spec.Rsa.bytesAt t.mem (scA s a) l = Spec.Rsa.bytesAt t₀.mem (scA s a) l

theorem counter_ne {n k : Nat} (hk : k + 1 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1))).toNat ≠ 0 ↔ k + 1 ≠ n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]; omega_using [hk]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
include h

theorem prfLoop_ok {label : List Nat} {len count : List Instr} {dst N : Nat}
    {kd : List Byte} {C : BitVec 64} {textF : Nat → List Byte} {t₀ : State} (hN0 : 0 < N) (hN : N ≤ 256)
    (hd1 : sCL ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 2048) (hn : label.length + 4 ≤ 16)
    (htl : ∀ i, (textF i).length = label.length + 4)
    (hC : ∀ i < N, C - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hmsg : ∀ i < N, ∀ u, Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w =>
        (Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧
          Spec.Rsa.bytesAt w.mem (scA s sMsg) (label.length + 4) = textF i) ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ u : State, u.gpr .s9 = t₀.gpr .s9 →
      WP isa (.block (count ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C - u.gpr .s8)
    (h0 : PInv s R EM kd dst textF t₀ 0 t₀) :
    WP isa (.loop (prfBody label len dst count) (.nonzero .t1)) t₀ (PInv s R EM kd dst textF t₀ N) := by
  refine VG.Proof.Bignum.RISCV64.count_loop hN0 (PInv s R EM kd dst textF t₀) (fun i hi u hu => ?_) h0
  refine WP.mono (prfBody_ok h hu.toPost hu.kdk hu.ctr (by omega_using [hN, hi]) hd1 (by omega_using [hd2, hi]) hdst hn (htl i)
    (hmsg i hi) (fun v hv => hcount v (hv.trans hu.nb))) fun w hw =>
    ⟨⟨hw.toPost, ?_, hw.ctr, hw.nb.trans hu.nb, fun j hj => ?_, fun a l h₁ h₂ => ?_⟩, ?_⟩
  · rw [hw.keep _ _ (by decide) (by unfold scrBytes at hd2; decide) (.inl (by unfold sKDK sCL at *; omega_using [hd1])),
      hu.kdk]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw.keep _ _ (by unfold sDH sCL at *; omega_using [hd1]) (by omega_arith) (.inl (by omega_using [hj])), hu.out j hj]
    · exact hw.out
  · rw [hw.keep _ _ h₁ (by omega_using [hd2, h₂]) (.inl (by omega_using [h₂])), hu.keep a l h₁ h₂]
  · rw [hw.left, hC i hi]; exact counter_ne hi (by omega_using [hN])

end

/-! ## The bytes of the blocks -/

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} (n : Nat) (h : ∀ j < n, f j = g j) :
    (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun j hj => h j (by omega_using [hj])),
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil, h n (by omega_using [])]

theorem bytes_blocks (s : State) (m : Mem) (o : Nat) : ∀ n, Spec.Rsa.bytesAt m (scA s o) (32 * n) =
    (List.range n).flatMap fun j => Spec.Rsa.bytesAt m (scA s (o + 32 * j)) 32
  | 0 => rfl
  | n + 1 => by
    rw [show 32 * (n + 1) = 32 * n + 32 by omega_using [], bytesAt_add, bytes_blocks s m o n, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Offset.add_add]

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) :
    Spec.Rsa.bytesAt m p k = (Spec.Rsa.bytesAt m p n).take k := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem irprf_bytes {s : State} {m : Mem} {kd label : List Byte} {length dst N : Nat} (hN : N = (length + 31) / 32)
    (hout : ∀ j < N, Spec.Rsa.bytesAt m (scA s (dst + 32 * j)) 32 = Proof.RsaPkcs1Enc.prfBlock kd label length j)
    (hl : length ≤ 32 * N) :
    Spec.Rsa.bytesAt m (scA s dst) length = Spec.RsaPkcs1Enc.irprf kd label length := by
  rw [Proof.RsaPkcs1Enc.irprf_eq, ← hN, ← flatMap_range_congr N hout, ← bytes_blocks, ← bytesAt_take _ _ hl]

theorem nb_eq {k : BitVec 64} (hk : k.toNat ≤ 1024) :
    (k + BitVec.ofNat 64 31) >>> 5 = BitVec.ofNat 64 ((k.toNat + 31) / 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [hk]

/-! ## The loops -/

theorem count_ok (u : State) {c : Reg} (C : BitVec 64) (hc : u.gpr c = C) :
    WP isa (.block (([mov .t1 c] : List Instr) ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C - u.gpr .s8 := by
  show WP isa (.block [mov .t1 c, .sub .t1 .t1 .s8]) u _
  exact wp_mov fun v₁ p₁ f₁ => wp_sub fun w p₂ f₂ => wp_nil
    ⟨(p₁.trans p₂).mono, by rw [f₂, f₁, hc, p₁.get .s8]⟩

theorem count8_ok (u : State) :
    WP isa (.block (([.li .t1 8] : List Instr) ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w =>
      Only [.t1] u w ∧ w.gpr .t1 = BitVec.ofNat 64 8 - u.gpr .s8 := by
  show WP isa (.block [.li .t1 (8 : Nat), .sub .t1 .t1 .s8]) u _
  exact wp_li (by decide) fun v₁ p₁ f₁ => wp_sub fun w p₂ f₂ => wp_nil
    ⟨(p₁.trans p₂).mono, by rw [f₂, f₁, p₁.get .s8]⟩

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte}
include h

/-- A byte of the message buffer is writable. -/
theorem Post.msgW {t : State} (hp : Post s R EM t) :
    ∀ d < 16, InRegions t.wr (scA s sMsg + BitVec.ofNat 64 d) 1 :=
  scByte h hp.wr (a := sMsg) (n := 16) (by decide)

/-- `CL` after its loop. -/
structure CLR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends Post s R EM t where
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd
  nb : t.gpr .s9 = BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32)
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

theorem clLoop_ok {t : State} {kd : List Byte} (hp : Post s R EM t)
    (hkd : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kd) : WP isa clLoop t (CLR s R EM kd) := by
  have hk := h.k2
  unfold clLoop clInit
  refine WP.seq (wp_li (imm := 0) (by decide) fun v₁ p₁ f₁ => wp_addi (imm := 31) (fun v₂ p₂ f₂ =>
    wp_srl (sh := 5) fun t₁ p₃ f₃ => wp_nil ?_) (by decide))
  have O : Only [.s8, .s9] t t₁ := (p₁.trans (p₂.trans p₃)).mono
  have P₁ : Post s R EM t₁ := hp.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have nb₁ : t₁.gpr .s9 = BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32) := by
    rw [f₃, f₂, p₁.get .s1, hp.s1, nb_eq hk]
  refine WP.mono (prfLoop_ok h (label := lengthLabel) (len := clLen) (count := [.li .t1 8])
    (dst := sCL) (N := 8) (C := BitVec.ofNat 64 8) (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "length" ++ Spec.Rsa.i2osp (8 * 256) 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_length, lengthLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi]))
    (fun i hi u hu x8 => msgCL_ok (by rw [hu.s0]) x8 (by omega_using [hi]) (hu.msgW h))
    (fun u _ => count8_ok u)
    ⟨P₁, by rw [O.mem, hkd], f₁ ▸ (p₂.get .s8 ▸ p₃.get .s8 ▸ rfl), rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩) fun t₂ h₂ =>
    ⟨h₂.toPost, h₂.kdk, h₂.nb.trans nb₁, ?_⟩
  exact irprf_bytes (N := 8) (by decide) (fun j hj => h₂.out j hj) (by decide)

/-- `AM` after its loop, and `CL` still. -/
structure AMR (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends Post s R EM t where
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .a4).toNat =
    Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .a4).toNat

theorem amLoop_ok {t : State} {kd : List Byte} (hl : CLR s R EM kd t) : WP isa amLoop t (AMR s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold amLoop
  refine WP.seq (wp_li (imm := 0) (by decide) fun t₁ p₁ f₁ => wp_nil ?_)
  have P₁ : Post s R EM t₁ := hl.toPost.keep h p₁.keep (ws := []) (by rw [p₁.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have hN0 : 0 < ((s.gpr .a4).toNat + 31) / 32 := by omega_using [hk64]
  refine WP.mono (prfLoop_ok h (label := messageLabel) (len := amLen) (count := [mov .t1 .s9])
    (dst := sAM) (N := ((s.gpr .a4).toNat + 31) / 32) (C := BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32))
    (t₀ := t₁)
    (textF := fun i => Spec.Rsa.i2osp i 2 ++ Spec.RsaPkcs1Enc.ascii "message" ++
      Spec.Rsa.i2osp (8 * (s.gpr .a4).toNat) 2)
    hN0 (by omega_using [hk]) (by decide) (by unfold sAM scrBytes; omega_using [hk]) (by decide) (by decide)
    (fun i => by simp [Proof.RsaPkcs1Enc.i2osp_length, ascii_message, messageLabel])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi]))
    (fun i hi u hu x8 => msgAM_ok (by rw [hu.s0]) x8 hu.s1 (by omega_using [hk, hi]) hk (hu.msgW h))
    (fun u hu => count_ok u _ (by rw [hu, p₁.get .s9, hl.nb]))
    ⟨P₁, by rw [p₁.mem, hl.kdk], f₁, rfl, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩) fun t₂ h₂ => ⟨h₂.toPost, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide), p₁.mem, hl.cl]
  · exact irprf_bytes rfl (fun j hj => h₂.out j hj) (by omega_using [])

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
