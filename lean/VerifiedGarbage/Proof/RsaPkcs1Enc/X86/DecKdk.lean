module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecHash
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `KDK = HMAC(DH, C)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecKdk.lean`): HMAC-SHA-256's `init`
with a 32-byte key in `scratch` (`macInit_vp`), SHA-256's `update` of its
inner state (`macUpd_vp`) and HMAC's `finalize` to `scratch`
(`macFin_vp`), as IRPRF uses them too; and with them the key derivation
key of the draft's step 3.1 (`kdk_vp`, `kdkV`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)

variable {P : EP}

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega

theorem hash_length (x : List Byte) : (Spec.Sha256.hash x).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

/-- `K₀` for the key `k`. -/
abbrev k0Of (k : List Byte) : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 k

/-- HMAC's states after `init` with the key `k`, and the inner one after
`text`. -/
def Macd (m : Mem) (P : EP) (k text : List Byte) : Prop :=
  Spec.Sha256.Repr m (sr P sSt 96).base (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.ipad ++ text) ∧
    Spec.Sha256.Repr m (sr P sOuter 96).base (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.opad)

/-! ## The calls -/

/-- What HMAC's `init` writes. -/
abbrev hiWs (P : EP) : List Region := [sr P sSt 96, sr P sOuter 96, sr P sW (104 * 8)]
/-- What SHA-256's `update` writes. -/
abbrev updWs (P : EP) : List Region := [sr P sSt 96, sr P sW 160]
/-- What HMAC's `finalize` to `scratch + o` writes. -/
abbrev hfWs (P : EP) (o : Nat) : List Region := [sr P sSt 96, sr P o 32, sr P sW (104 * 8)]

theorem hiWs_scr : InScr P (hiWs P) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨sOuter, 96, by decide, by decide, rfl⟩
  · exact ⟨sW, 104 * 8, by decide, by decide, rfl⟩

theorem updWs_scr : InScr P (updWs P) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨sW, 160, by decide, by decide, rfl⟩

theorem hfWs_scr {o : Nat} (ho : o + 32 ≤ 2576) : InScr P (hfWs P o) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sSt, 96, by decide, by decide, rfl⟩
  · exact ⟨o, 32, by omega, by omega, rfl⟩
  · exact ⟨sW, 104 * 8, by decide, by decide, rfl⟩

/-- HMAC's `init` with the 32 bytes of key at `scratch + key`. -/
theorem macInit_vp (v : Backend) {key : Nat} (hk₁ : 192 ≤ key) (hk₂ : key + 32 ≤ 2576) {F G : State → State → Prop}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 key ∧
      s.gpr .ecx = BitVec.ofNat 32 32 ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW)
    (hG : ∀ σ s t, F σ s → Called s t (hiWs P) 76 →
      Macd t.mem P (Spec.Rsa.bytesAt s.mem (sr P key 32).base 32) [] → G σ t) :
    VP F (callHi v.F) G :=
  VP.macInit v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, d, e⟩ := hF σ s h
      exact ⟨hiA hs v hk₁ hk₂ (by decide) a b c d e, hs.2.sp⟩)
    fun σ s h t a hi ho => hG σ s t h (Called.ofWhole a) ⟨by rw [List.append_nil]; exact hi, ho⟩

/-- What `update` needs of the data, `len` bytes at `d`. -/
structure DataOk (P : EP) (s : State) (d : BitVec 32) (len : Nat) : Prop where
  hlen : len < 2 ^ 32
  cd : Covers [⟨d.setWidth 64, len⟩] (s.rd ++ s.wr)
  d_st : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sSt 96)
  d_sc : Region.Disjoint ⟨d.setWidth 64, len⟩ (sr P sW 160)
  b_d : (below P.B 48).Disjoint ⟨d.setWidth 64, len⟩
  nd : d.toNat + len ≤ 2 ^ 32

/-- SHA-256's `update` of HMAC's inner state, after `init`, with the `len`
bytes at `d`. -/
theorem macUpd_vp (v : Backend) {d : BitVec 32} {len : Nat} {F G : State → State → Prop}
    {key : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧ s.gpr .ecx = BitVec.ofNat 32 len ∧ s.gpr .edx = d ∧
      s.gpr .ebp = P.scr + BitVec.ofNat 32 sW ∧ Macd s.mem P (key σ s) [] ∧ (key σ s).length ≤ 64 ∧
      DataOk P s d len)
    (hG : ∀ σ s t, F σ s → Called s t (updWs P) 48 →
      Macd t.mem P (key σ s) (Spec.Rsa.bytesAt s.mem (d.setWidth 64) len) → G σ t) :
    VP F (callUpd v.F) G :=
  VP.shaUpd v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, e, f, g, -, -, dk⟩ := hF σ s h
      exact ⟨updA hs v a b c e f g dk.hlen dk.cd dk.d_st dk.d_sc dk.b_d dk.nd, hs.2.sp⟩)
    fun σ s h t a hp => by
      obtain ⟨hs, -, -, -, -, -, -, md, hk, -⟩ := hF σ s h
      have c := Called.ofStream a
      refine hG σ s t h c ⟨?_, c.repr hs (by decide) (o := sOuter) (by decide) (fun r hr => ?_) md.2⟩
      · have := hp _ (by have := md.1; rwa [List.append_nil] at this)
          (by rw [Proof.Hmac.Common.xorPad_length, blockKey_length hk]
              exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by decide))
        exact this
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.1.sr_sep (by decide) (by decide) (by decide) (by decide) (by decide)
        · exact hs.1.sr_sep (by decide) (by decide) (by decide) (by decide) (by decide)

/-- HMAC's `finalize` to the 32 bytes at `scratch + o`, after `tl` bytes of text. -/
theorem macFin_vp (v : Backend) {o tl : Nat} (ho₁ : 192 ≤ o) (ho₂ : o + 32 ≤ 2576)
    {F G : State → State → Prop} {key text : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧
      s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ s.gpr .eax = BitVec.ofNat 32 (64 + tl) ∧ s.gpr .ecx = 0 ∧
      s.gpr .edi = P.scr + BitVec.ofNat 32 o ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW ∧
      Macd s.mem P (key σ s) (text σ s) ∧ (key σ s).length ≤ 64 ∧ (text σ s).length = tl ∧ 64 + tl < 2 ^ 32)
    (hG : ∀ σ s t, F σ s → Called s t (hfWs P o) 76 →
      Spec.Rsa.bytesAt t.mem (sr P o 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 (key σ s) (text σ s) →
      G σ t) :
    VP F (callHf v.F) G :=
  VP.macFin v (sp := P.B) (fun σ s h => by
      obtain ⟨hs, a, b, c, e, f, g, -⟩ := hF σ s h
      exact ⟨hfA hs v ho₁ ho₂ a b c e f g, hs.2.sp⟩)
    fun σ s h t a hp => by
      obtain ⟨hs, -, -, -, -, -, -, md, hk, ht, htl⟩ := hF σ s h
      refine hG σ s t h (Called.ofWhole a) ?_
      exact hp _ _ (blockKey_length hk) (by rw [blockKey_length hk, ht]; omega) md.1
        (by rw [ht]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat htl) md.2

/-! ## The blocks of arguments -/

theorem macInitArgs_wp {σ s : State} (hs : S P σ s) (key : Nat) {Q : State → Prop}
    (k : ∀ t, S P σ t → t.mem = s.mem → t.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧
      t.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧ t.gpr .edx = P.scr + BitVec.ofNat 32 key ∧
      t.gpr .ecx = BitVec.ofNat 32 32 ∧ t.gpr .ebp = P.scr + BitVec.ofNat 32 sW → Q t) :
    WP isa (.block (macInitArgs key)) s Q := by
  simp only [macInitArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
  refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
  refine St.scrW s2 (d := .edx) (by decide) key fun t3 s3 u3 => ?_
  refine St.movi s3 (d := .ecx) (by decide) 32 fun t4 s4 u4 => ?_
  rw [← List.append_nil (scr _ _)]
  refine St.scrW s4 (d := .ebp) (by decide) sW fun t5 s5 u5 => WP.block_nil (k t5 s5 ?_ ?_)
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · simp (disch := decide) only [u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
      u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

/-! ## `KDK` -/

/-- The key derivation key. -/
abbrev kdkV (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.kdk P.K (dB P σ) (cB P σ)

/-- `DH`. -/
abbrev dhV (P : EP) (σ : State) : List Byte := Spec.Sha256.hash (Dfull P σ)

/-- Before `init`. -/
def K1 (P : EP) (σ s : State) : Prop :=
  H6 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sDH ∧ s.gpr .ecx = BitVec.ofNat 32 32 ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `init`. -/
def K2 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) []

/-- Before `update`. -/
def K3 (P : EP) (σ s : State) : Prop :=
  K2 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .edx = P.inp ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `update`. -/
def K4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) (cB P σ)

/-- Before `finalize`. -/
def K5 (P : EP) (σ s : State) : Prop :=
  K4 P σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .eax = BitVec.ofNat 32 (64 + P.K) ∧ s.gpr .ecx = 0 ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sKDK ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- `KDK`. -/
def K6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sr P sKDK 32).base 32 = kdkV P σ

theorem sp_agree {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp], s₁.gpr r = s₂.gpr r := fun _ _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).2.sp, (hF _ _ h₂).2.sp]

theorem kdkInitArgs_vp : VP (H6 P) (.block (macInitArgs sDH)) (K1 P) :=
  VP.taint [.esp] macInitDH_taint (sp_agree fun _ _ h => h.1.1) fun σ s h =>
    macInitArgs_wp h.1.1 sDH fun t st hm r =>
      ⟨⟨h.1.regs st.2 hm, by rw [hm]; exact h.2⟩, r⟩

theorem kdkInit_vp (v : Backend) : VP (K1 P) (callHi v.F) (K2 P) :=
  macInit_vp v (key := sDH) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1, h.2⟩) fun σ s t h c md => by
    obtain ⟨⟨hb, dh⟩, -⟩ := h
    exact ⟨c.base hb (by decide) hiWs_scr, by rw [dh] at md; exact md⟩

theorem kdkUpdArgs_vp : VP (K2 P) (.block kdkUpdArgs) (K3 P) :=
  VP.taint [.esp] kdkUpdArgs_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    simp only [kdkUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.movi s1 (d := .esi) (by decide) 64 fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.argv s3 (j := 9) (by decide) (d := .edx) (by decide) fun t4 s4 u4 => ?_
    refine St.argv s4 (j := 4) (by decide) (d := .ecx) (by decide) fun t5 s5 u5 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
    have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨h.1.regs s6.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
      u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem dataINP {σ s : State} (hs : S P σ s) : DataOk P s P.inp P.K :=
  { hlen := by have := hs.1.k1024; omega
    cd := St.cov_ro hs (R := P.INP) (by simp)
    d_st := (hs.1.sr_ro (by decide) (by decide) (R := P.INP) (by simp)).symm
    d_sc := (hs.1.sr_ro (by decide) (by decide) (R := P.INP) (by simp)).symm
    b_d := hs.1.below_ro (by decide) (R := P.INP) (by simp)
    nd := by
      have := hs.1.ok.fits P.INP (by simp)
      simp only [BitVec.toNat_setWidth] at this
      rwa [Nat.mod_eq_of_lt (by have := P.inp.isLt; omega)] at this }

theorem kdkUpd_vp (v : Backend) : VP (K3 P) (callUpd v.F) (K4 P) :=
  macUpd_vp v (key := fun σ _ => dhV P σ) (fun _ _ h => by
      obtain ⟨⟨hb, md⟩, a, b, c, e, f, g⟩ := h
      exact ⟨hb.1, a, b, c, e, f, g, md, by rw [hash_length]; decide, dataINP hb.1⟩)
    fun σ s t h c md => by
      obtain ⟨⟨hb, -⟩, -⟩ := h
      have hs := hb.1
      refine ⟨c.base hb (by decide) updWs_scr, ?_⟩
      rw [show Spec.Rsa.bytesAt s.mem (P.inp.setWidth 64) P.K = cB P σ from hs.2.ro (R := P.INP) (by simp)]
        at md
      exact md

theorem kdkFinArgs_vp : VP (K4 P) (.block kdkFinArgs) (K5 P) :=
  VP.taint [.esp] kdkFinArgs_taint (sp_agree fun _ _ h => h.1.1) fun σ s h => by
    have hs := h.1.1
    have hK := hs.1.k1024
    simp only [kdkFinArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edx) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
    refine St.argv s2 (j := 4) (by decide) (d := .eax) (by decide) fun t3 s3 u3 => ?_
    refine wp_addi fun t4 u4 => ?_
    have s4 : S P σ t4 := ⟨hs.1, s3.2.upd u4 (by decide)⟩
    refine St.movi s4 (d := .ecx) (by decide) 0 fun t5 s5 u5 => ?_
    refine St.scrW s5 (d := .edi) (by decide) sKDK fun t6 s6 u6 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s6 (d := .ebp) (by decide) sW fun t7 s7 u7 => WP.block_nil ?_
    have mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨h.1.regs s7.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u7.gpr, u7.other, u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other,
      u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | skip
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    apply BitVec.eq_of_toNat_eq
    have e64 : (64 : BitVec 32).toNat = 64 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e64]
    omega

theorem kdkV_eq (P : EP) {σ : State} (h : In P σ) :
    kdkV P σ = Spec.Hmac.hmac Spec.Hmac.sha256 (dhV P σ) (cB P σ) := by
  simp only [kdkV, Spec.RsaPkcs1Enc.kdk, dhV, Dfull]
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [Proof.RsaPkcs1Sig.bytesAt_len]; exact h.dlK),
    Proof.RsaPkcs1Sig.bytesAt_len]

theorem kdkFin_vp (v : Backend) : VP (K5 P) (callHf v.F) (K6 P) :=
  macFin_vp v (o := sKDK) (tl := P.K) (key := fun σ _ => dhV P σ) (text := fun σ _ => cB P σ) (by decide)
    (by decide)
    (fun _ _ h => by
      obtain ⟨⟨hb, md⟩, a, b, c, e, f, g⟩ := h
      exact ⟨hb.1, a, b, c, e, f, g, md, by rw [hash_length]; decide, Proof.RsaPkcs1Sig.bytesAt_len _ _ _,
        by have := hb.1.1.k1024; omega⟩)
    fun σ s t h c hk => by
      obtain ⟨⟨hb, -⟩, -⟩ := h
      exact ⟨c.base hb (by decide) (hfWs_scr (by decide)), by rw [hk, kdkV_eq P hb.1.1]⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
