module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: `DH = SHA256(D)` and `KDK = HMAC(DH, C)`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecHash.lean`, `DecKdk.lean`): the calls of
SHA-256's streaming `init`, `update` and `finalize` on `D` (`hashD_ok`, from
`DB` to `DHS`), then HMAC-SHA-256 keyed with `DH` of the ciphertext, to
`scratch + sKDK` (`kdkMac_ok`, from `DHS` to `KD`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

/-- The ciphertext. -/
abbrev cOf (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .a4).toNat

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure DHS (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Post s R EM t where
  dh : Spec.Rsa.bytesAt t.mem (scA s sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (dBytes s)) (s.gpr .a4).toNat)

/-- After `kdkMac`: `KDK` at `scratch + sKDK`. -/
structure KD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop extends Post s R EM t where
  kdk : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = Spec.RsaPkcs1Enc.kdk (s.gpr .a4).toNat (dBytes s) (cOf s)

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length := by
  simp [Spec.Hmac.xorPad]

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ (64 < key.length) := by omega
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega

section
variable {s : State} (h : DPre s) {R : BitVec 64} {EM : List Byte}
include h

omit h in
/-- A range of `scratch` that writes elsewhere leave as it was. -/
theorem keep_sc {m m' : Mem} {ws : List Region} (hf : Frame ws m m') {a l : Nat} (ha : a + l ≤ scrBytes)
    (hs : ∀ r ∈ ws, Region.Disjoint (scR s a l) r) :
    Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := scR s a l) hs (show l ≤ 2 ^ 64 by unfold scrBytes at ha; omega)
    (List.mem_range.mp hi)

/-- What a call writing parts `ws` of `scratch` and the callees' stack leaves
of another part. -/
theorem keep_call {m m' : Mem} {ws : List (Nat × Nat)} {X : Nat} (hX : X ≤ callX)
    (hf : Frame (ws.map (fun p => scR s p.1 p.2) ++ [below (fb s) X]) m m') {a l : Nat} (ha : a + l ≤ scrBytes)
    (hws : ∀ p ∈ ws, (a + l ≤ p.1 ∨ p.1 + p.2 ≤ a) ∧ p.1 + p.2 ≤ scrBytes) :
    Spec.Rsa.bytesAt m' (scA s a) l = Spec.Rsa.bytesAt m (scA s a) l :=
  keep_sc hf ha fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact scDisj (hws p hp).1 ha (hws p hp).2
    · rw [List.mem_singleton.mp hr]; exact (lowSc h hX ha).symm

/-- A streaming state in `scratch` that a call leaves as it was represents
what it did. -/
theorem repr_call {m m' : Mem} {ws : List (Nat × Nat)} {X : Nat} (hX : X ≤ callX)
    (hf : Frame (ws.map (fun p => scR s p.1 p.2) ++ [below (fb s) X]) m m') {a : Nat} (ha : a + 96 ≤ scrBytes)
    (hws : ∀ p ∈ ws, (a + 96 ≤ p.1 ∨ p.1 + p.2 ≤ a) ∧ p.1 + p.2 ≤ scrBytes) {x : List Byte}
    (hr : hH.SH.Repr m (scA s a) x) : hH.SH.Repr m' (scA s a) x := by
  refine hH.congr m m' _ x (fun i hi => ?_) hr
  have e := keep_call h hX hf ha hws
  simp only [Spec.Rsa.bytesAt] at e
  have := congrArg (·[i]?) e
  simp only [List.getElem?_map, List.getElem?_range (show i < 96 from hi), Option.map_some] at this
  exact Option.some.inj this

/-! ## `DH` -/

theorem hashD_ok {t : State} (hd : DB s R EM t) : WP isa hashD t (DHS s R EM) := by
  have hk := h.k2
  have lk : sD + (s.gpr .a4).toNat ≤ scrBytes := by unfold sD scrBytes; omega
  unfold hashD shaInitArgs
  refine WP.seq (wp_addi (imm := sSt) fun u₁ o₁ e₁ => wp_nil ?_)
  have P₁ : Post s R EM u₁ := hd.toPost.keep h o₁.keep (ws := []) (by rw [o₁.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  refine WP.seq (shaInit_ok h P₁ (a := sSt) (by decide) (by rw [e₁, hd.s0]) fun u₂ P₂ A₂ r₂ => ?_)
  have hD₂ : Spec.Rsa.bytesAt u₂.mem (scA s sD) (s.gpr .a4).toNat = Spec.Rsa.bytesAt t.mem (scA s sD) (s.gpr .a4).toNat := by
    rw [← o₁.mem]
    exact keep_call h (ws := [(sSt, 96)]) (X := sha256.F) (by decide) (by rw [← P₁.sp]; exact A₂.frame) lk
      (by simp only [List.mem_singleton]; rintro _ rfl; exact ⟨.inr (by decide), by decide⟩)
  unfold shaUpdArgs
  refine WP.seq (wp_addi (imm := sSt) fun v₁ p₁ f₁ => wp_li (imm := 0) (by decide) fun v₂ p₂ f₂ =>
    wp_addi (imm := sD) (fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide))
  have O : Only [.a0, .a1, .a2, .a3] u₂ v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  have P₃ : Post s R EM v₄ := P₂.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have a0 : v₄.gpr .a0 = scA s sSt := by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P₂.s0]
  have a1 : v₄.gpr .a1 = BitVec.ofNat 64 0 := by rw [p₄.get .a1, p₃.get .a1, f₂]
  have a2 : v₄.gpr .a2 = scA s sD := by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P₂.s0]
  have a3 : (v₄.gpr .a3).toNat = (s.gpr .a4).toNat := by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P₂.s1]
  refine WP.seq (shaUpd_ok h P₃ (a := sSt) (by decide) (dat := scA s sD) (len := (s.gpr .a4).toNat) a0 a2 a3
    (Covers.right (scCov h P₃.wr lk)) (scDisj (.inr (by decide)) lk (by decide)) (lowSc h (by decide) lk)
    fun u₃ P₄ A₃ r₃ => ?_)
  unfold shaFinArgs
  refine WP.seq (wp_addi (imm := sSt) fun w₁ q₁ g₁ => wp_mov fun w₂ q₂ g₂ =>
    wp_addi (imm := sDH) (fun w₃ q₃ g₃ => wp_nil ?_) (by decide))
  have O' : Only [.a0, .a1, .a2] u₃ w₃ := (q₁.trans (q₂.trans q₃)).mono
  have P₅ : Post s R EM w₃ := P₄.keep h O'.keep (ws := []) (by rw [O'.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have b0 : w₃.gpr .a0 = scA s sSt := by rw [q₃.get .a0, q₂.get .a0, g₁, P₄.s0]
  have b1 : w₃.gpr .a1 = s.gpr .a4 := by rw [q₃.get .a1, g₂, q₁.get .s1, P₄.s1]
  have b2 : w₃.gpr .a2 = scA s sDH := by rw [g₃, q₂.get .s0, q₁.get .s0, P₄.s0]
  refine shaFin_ok h P₅ (a := sSt) (o := sDH) (by decide) (by decide) (.inl (by decide)) b0 b2
    fun u₄ P₆ A₄ r₄ => ⟨P₆, ?_⟩
  have hm := r₃ [] (by rw [O.mem]; exact r₂) (by rw [a1]; rfl)
  rw [List.nil_append] at hm
  have e := r₄ _ (by rw [O'.mem]; exact hm) (by simp [Spec.Sha256.bytesAt]; omega)
    (by rw [b1]; simp [Spec.Sha256.bytesAt])
  show Spec.Sha256.bytesAt u₄.mem (scA s sDH) 32 = _
  rw [e]
  show Spec.Sha256.hash (Spec.Rsa.bytesAt v₄.mem (scA s sD) (s.gpr .a4).toNat) = _
  rw [O.mem, hD₂, hd.D]

/-! ## `KDK` -/

/-- HMAC's `init` arguments, for the key at `scratch + key`. -/
theorem macInitArgs_ok {t : State} (hp : Post s R EM t) {key : Nat} (hk : key < 2048) {Q : State → Prop}
    (hQ : ∀ u, Post s R EM u → u.gpr .a0 = scA s sSt → u.gpr .a1 = scA s sOuter → u.gpr .a2 = scA s key →
      u.gpr .a3 = BitVec.ofNat 64 32 → u.mem = t.mem → Q u) :
    WP isa (.block (macInitArgs key)) t Q := by
  unfold macInitArgs
  refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_addi (imm := sOuter) (fun v₂ p₂ f₂ =>
    wp_addi (imm := key) (fun v₃ p₃ f₃ => wp_li (imm := 32) (by decide) fun v₄ p₄ f₄ => wp_nil ?_) hk)
    (by decide)) (by decide)
  have O : Only [.a0, .a1, .a2, .a3] t v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  refine hQ v₄ (hp.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr))
    ?_ ?_ ?_ f₄ O.mem
  · rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, hp.s0]
  · rw [p₄.get .a1, p₃.get .a1, f₂, p₁.get .s0, hp.s0]
  · rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, hp.s0]

theorem cR_eq : (⟨stackArg s 1, (s.gpr .a4).toNat⟩ : Region) = iR s := by simp only [iR, h.hi]

/-- The ciphertext misses `scratch` and the stack. -/
theorem c_sc {a l : Nat} (ha : a + l ≤ scrBytes) : Region.Disjoint ⟨stackArg s 1, (s.gpr .a4).toNat⟩ (scR s a l) := by
  rw [cR_eq h]; exact h.is.sub_right (scSub h ha)

theorem c_low {X : Nat} (hX : X ≤ callX) : (below (fb s) X).Disjoint ⟨stackArg s 1, (s.gpr .a4).toNat⟩ := by
  rw [cR_eq h]; exact h.ki.sub_left (sub_trans (low_sub hX) (callee_sub s))

theorem c_cov {t : State} (hp : Post s R EM t) : Covers [⟨stackArg s 1, (s.gpr .a4).toNat⟩] (t.rd ++ t.wr) := by
  rw [cR_eq h]
  exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, hp.rd, h.hrd]; simp)

theorem c_bytes {t : State} (hp : Post s R EM t) :
    Spec.Rsa.bytesAt t.mem (stackArg s 1) (s.gpr .a4).toNat = cOf s :=
  bytes_of_frame hp.mem (fun r hr => by
    rw [cR_eq h]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.ki.symm
    · exact h.oi.symm
    · exact h.is) (by have := h.k2; omega)

theorem kdkMac_ok {t : State} (hd : DHS s R EM t) : WP isa kdkMac t (KD s R EM) := by
  have hk := h.k2
  unfold kdkMac
  refine WP.seq (macInitArgs_ok h hd.toPost (key := sDH) (by decide) fun u₁ P₁ a0 a1 a2 a3 m₁ => ?_)
  refine WP.seq (macInit_ok h P₁ (i := sSt) (u := sOuter) (k := sDH) (by decide) (by decide) (by decide)
    (.inl (by decide)) (.inr (by decide)) (.inr (by decide)) a0 a1 a2 a3 fun u₂ P₂ A₂ hI hO => ?_)
  unfold kdkUpdArgs
  refine WP.seq (wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
    wp_mov fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide))
  have O : Only [.a0, .a1, .a2, .a3] u₂ v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  have P₃ : Post s R EM v₄ := P₂.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have c0 : v₄.gpr .a0 = scA s sSt := by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P₂.s0]
  have c1 : v₄.gpr .a1 = BitVec.ofNat 64 64 := by rw [p₄.get .a1, p₃.get .a1, f₂]
  have c2 : v₄.gpr .a2 = stackArg s 1 := by rw [p₄.get .a2, f₃, p₂.get .s6, p₁.get .s6, P₂.s6]
  have c3 : (v₄.gpr .a3).toNat = (s.gpr .a4).toNat := by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P₂.s1]
  refine WP.seq (shaUpd_ok h P₃ (a := sSt) (by decide) c0 c2 c3 (c_cov h P₃) (c_sc h (by decide))
    (c_low h (by decide)) fun u₃ P₄ A₃ r₃ => ?_)
  unfold kdkFinArgs
  refine WP.seq (wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
    wp_addi (imm := 64) (fun w₃ q₃ g₃ => wp_addi (imm := sKDK) (fun w₄ q₄ g₄ => wp_nil ?_) (by decide))
    (by decide)) (by decide)) (by decide))
  have O' : Only [.a0, .a1, .a2, .a3] u₃ w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
  have P₅ : Post s R EM w₄ := P₄.keep h O'.keep (ws := []) (by rw [O'.mem]; exact Frame.refl _ _)
    (fun r hr => nomatch hr)
  have d0 : w₄.gpr .a0 = scA s sSt := by rw [q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P₄.s0]
  have d1 : w₄.gpr .a1 = scA s sOuter := by rw [q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P₄.s0]
  have d2 : w₄.gpr .a2 = s.gpr .a4 + BitVec.ofNat 64 64 := by rw [q₄.get .a2, g₃, q₂.get .s1, q₁.get .s1, P₄.s1]
  have d3 : w₄.gpr .a3 = scA s sKDK := by rw [g₄, q₃.get .s0, q₂.get .s0, q₁.get .s0, P₄.s0]
  refine macFin_ok h P₅ (i := sSt) (u := sOuter) (o := sKDK) (by decide) (by decide) (by decide)
    (.inl (by decide)) (.inl (by decide)) (.inl (by decide)) d0 d1 d3 fun u₄ P₆ A₄ hmac => ⟨P₆, ?_⟩
  -- the key
  have k0l : (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u₁.mem (scA s sDH) 32)).length = 64 :=
    blockKey_length (by simp [Spec.Sha256.bytesAt])
  -- the outer state, across the update
  have hO' : hH.SH.Repr w₄.mem (scA s sOuter)
      (Spec.Hmac.xorPad (Spec.Hmac.blockKey hH.SH.H (Spec.Sha256.bytesAt u₁.mem (scA s sDH) 32)) Spec.Hmac.opad) := by
    rw [O'.mem]
    refine repr_call h (ws := [(sSt, 96)]) (X := sha256.F) (by decide) (by rw [← P₃.sp]; exact A₃.frame)
      (by decide) (by simp only [List.mem_singleton]; rintro _ rfl; exact ⟨.inr (by decide), by decide⟩) ?_
    rw [O.mem]; exact hO
  have hl : (Spec.Rsa.bytesAt v₄.mem (stackArg s 1) (s.gpr .a4).toNat).length = (s.gpr .a4).toNat := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have e := hmac _ (Spec.Rsa.bytesAt v₄.mem (stackArg s 1) (s.gpr .a4).toNat) k0l (by rw [k0l, hl]; omega)
    (by
      rw [O'.mem]
      have := r₃ _ (by rw [O.mem]; exact hI) (by rw [c1, xorPad_length, k0l])
      exact this)
    (by
      rw [d2, hl]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) hO'
  rw [c_bytes h P₃, m₁] at e
  show Spec.Sha256.bytesAt u₄.mem (scA s sKDK) 32 = _
  rw [e]
  show Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 (Spec.Hmac.blockKey Spec.Hmac.sha256 (Spec.Rsa.bytesAt t.mem (scA s sDH) 32))
    (cOf s) = _
  rw [hd.dh]; rfl

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
