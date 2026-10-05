import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecD
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCalls

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `DH = SHA256(D)`

SHA-256's functions, with an implementation `v` of its compression function
(`HH v`), and what is proven of them; the regions of `scratch` the calls use
(`scD`, `stkD`, `scS`), and the hash of `D` (`hashD_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin core_hmacInit_depth
  core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)

variable (v : Compress)

/-- SHA-256's functions, and what is proven of them. -/
abbrev HH : Impl.Pbkdf2.Md.X86_64.Hash := Proof.Pbkdf2.Md.X86_64.Sha256.hash v
abbrev OK : HashOK (HH v) := Proof.Pbkdf2.Md.X86_64.Sha256.ok v

theorem hI : Verified X86_64.target (HH v).hmacInit (initG (OK v).SH (HH v).W) :=
  hmacInit_ok (OK v) Proof.Pbkdf2.Md.X86_64.Sha256.coreOK (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    Proof.Pbkdf2.Md.X86_64.Sha256.satI

theorem hIsp : NoSp (HH v).hmacInit :=
  nosp_of (core_hmacInit (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iNs Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hinitNs)

theorem hId : (HH v).hmacInit.depth ≤ 2 :=
  core_hmacInit_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cD (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iD
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hinitD

theorem hF : Verified X86_64.target (HH v).hmacFin (finG (OK v).SH (HH v).W) :=
  hmacFin_ok (OK v) Proof.Pbkdf2.Md.X86_64.Sha256.coreOK (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    Proof.Pbkdf2.Md.X86_64.Sha256.satF

theorem hFsp : NoSp (HH v).hmacFin :=
  nosp_of (core_hmacFin (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cNs Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hfinNs)

theorem hFd : (HH v).hmacFin.depth ≤ 2 :=
  core_hmacFin_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cD Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.hfinD

/-- The sizes. -/
theorem sizes : (HH v).S = 96 ∧ (HH v).W = 104 ∧ (HH v).D = 32 ∧ (HH v).P.B = 64 ∧ (HH v).stream.S = 96 ∧
    (HH v).stream.F = 32 ∧ (HH v).stream.D = 32 ∧ (OK v).stream.Wb = 608 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show Impl.Sha256.X86_64.Stream.params.so + 48 = 608
  decide

theorem sh_hash : (OK v).SH.H = Spec.Hmac.sha256 := rfl
theorem stream_sh : (OK v).stream.SH = (OK v).SH := rfl

/-! ## Regions of `scratch` -/

variable {v}

theorem scD {s : State} {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint ⟨scA s a, n⟩ ⟨scA s b, m⟩ :=
  Offset.disjoint (sc s) h (by unfold scrBytes at ha; omega) (by unfold scrBytes at hb; omega)

theorem scSub {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA s a, n⟩ ⟨sc s, scrBytes⟩ :=
  Offset.sub_base _ ha

theorem stkD {s : State} (hp : DPre s) {n a m : Nat} (hn : n ≤ 8 + privStack) (ha : a + m ≤ scrBytes) :
    (below (fb s) n).Disjoint ⟨scA s a, m⟩ := by
  obtain ⟨h1, _⟩ := scr_len hp
  exact (hp.dKs.sub_left (below_sub s hn)).sub_right (sub_trans (scSub ha) (Region.sub_prefix h1))

theorem scS {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Safe s ⟨scA s a, n⟩ := .inl (scSub ha)

theorem belowS {s : State} (hp : DPre s) {n : Nat} (hn : n ≤ 8 + privStack) : Safe s (below (fb s) n) :=
  .inr (.inl (VG.X86_64.below_sub hn (by have := (fb_toNat hp).2.2; unfold privStack at *; omega)))

theorem scCov {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {a n : Nat} (ha : a + n ≤ scrBytes) : Covers [⟨scA s a, n⟩] t.wr := by
  obtain ⟨h1, _⟩ := scr_len hp
  exact Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨scrR s, by rw [hc.wr, hp.hwr]; simp [scrR], a, rfl, by dsimp only [scrR]; omega⟩

/-- `(BitVec.ofNat 32 d).signExtend 64`, for `d < 2³¹`. -/
theorem sx {d : Nat} (h : d < 2 ^ 31) : (BitVec.ofNat 32 d).signExtend 64 = BitVec.ofNat 64 d := by
  have hm : (BitVec.ofNat 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## The hash of `D` -/

/-- Code that changes only registers but `rsp` keeps `Ctx`. -/
theorem Ctx.regs {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    (hm : t'.mem = t.mem) {rs : List Reg} (k : Keep rs t t') (hr : ∀ r ∈ calleeSaved, r ∉ rs) : Ctx s R EM t' :=
  hc.step hp k.2.1 k.2.2 (k.cs hr) (ws := []) (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil)

/-- What a call leaves, from `Calls.After`, for writes in `scratch` and below the frame. -/
theorem Ctx.after {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    {ws : List Region} (h : Proof.Pbkdf2.Md.X86_64.Calls.After t ws t') (hs : ∀ r ∈ ws, Safe s r) :
    Ctx s R EM t' :=
  hc.step hp h.rd h.wr h.cs h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · rw [List.mem_singleton.mp hr, hc.rsp]; exact belowS hp (by decide)

theorem scA_zero (s : State) : scA s 0 = sc s := off_zero _

theorem shaInitArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaInitArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi] (c := .block shaInitArgs) (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h.1, h.2⟩
  xrun [shaInitArgs, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide), hc.slots.sScr, scA_zero]

theorem shaUpdArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaUpdArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = scA s sD ∧ t'.gpr .rcx = s.gpr .r8 ∧
      t'.gpr .r8 = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block shaUpdArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = scA s sD ∧ t'.gpr .rcx = s.gpr .r8 ∧
    t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [shaUpdArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide), hs.ld (d := oK) (by decide),
    hc.slots.sScr, hc.slots.sK, scA_zero, sx (d := sD) (by decide), sx (d := sWork) (by decide)]


theorem shaFinArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaFinArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = s.gpr .r8 ∧ t'.gpr .rdx = scA s sDH ∧ t'.gpr .rcx = scA s sWork := by
  have hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx] (c := .block shaFinArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = s.gpr .r8 ∧ t'.gpr .rdx = scA s sDH ∧ t'.gpr .rcx = scA s sWork) ?_
    rfl).mono fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [shaFinArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hs.ld (d := oK) (by decide), hc.slots.sScr, hc.slots.sK, scA_zero, sx (d := sDH) (by decide),
    sx (d := sWork) (by decide)]

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure HD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA s sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s))

/-- `below (fb s) 16`, as the calls see it. -/
theorem below_rsp {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) (n : Nat) :
    below (t.gpr .rsp) n = below (fb s) n := by rw [hc.rsp]

theorem hashD_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : DB s R EM t) :
    WP isa (hashD (HH v)) t (HD s R EM) := by
  have hk2 := hp.k2
  have hk1 := hp.k1
  have hkk : kOf s ≤ 1024 := hk2
  obtain ⟨hW, -, -, -, hS, hF, hD, hWb⟩ := sizes v
  have so := (OK v).stream
  -- `init`
  refine WP.seq (WP.mono (shaInitArgs_run hp h.ctx) fun t₁ ⟨hc₁, hm₁, hdi₁⟩ => ?_)
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Calls.init_call (OK v).stream hdi₁
    (by rw [hS]; exact scCov hp hc₁ (by decide))
    (by rw [below_rsp hc₁, hS]; exact stkD hp (by decide) (by decide)) fun t₂ a₂ hr₂ => ?_)
  have hc₂ := hc₁.after hp a₂ fun r hr => by
    rw [List.mem_singleton.mp hr, hS]; exact scS (by decide)
  have hD₂ : Spec.Rsa.bytesAt t₂.mem (scA s sD) (kOf s) = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s) := by
    rw [bytes_keep a₂.frame (fun r hr => ?_) (by omega), hm₁]
    · exact h.D
    · rcases List.mem_append.mp hr with hr | hr
      · rw [List.mem_singleton.mp hr, hS]; exact scD (.inr (by decide)) (by unfold sD scrBytes; omega) (by decide)
      · rw [List.mem_singleton.mp hr, below_rsp hc₁]
        exact (stkD hp (by decide) (by unfold sD scrBytes; omega)).symm
  -- `update`
  refine WP.seq (WP.mono (shaUpdArgs_run hp hc₂) fun t₃ ⟨hc₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃⟩ => ?_)
  have hD₃ := hm₃ ▸ hD₂
  have hr₃ : (OK v).stream.SH.Repr t₃.mem (scA s 0) [] := by rw [hm₃]; exact hr₂
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Calls.upd_call (OK v).stream (len := kOf s)
    { rdi := hdi₃, rdx := hdx₃, rcx := by rw [hcx₃], r8 := h8₃
      cd := Covers.right (scCov hp hc₃ (by unfold sD scrBytes; omega))
      cw := by rw [hS, hWb]; exact Covers.pair (scCov hp hc₃ (by decide)) (scCov hp hc₃ (by decide))
      st_sc := by rw [hS, hWb]; exact scD (.inl (by decide)) (by decide) (by decide)
      d_st := by rw [hS]; exact scD (.inr (by decide)) (by unfold sD scrBytes; omega) (by decide)
      d_sc := by rw [hWb]; exact scD (.inr (by decide)) (by unfold sD scrBytes; omega) (by decide)
      stk_st := by rw [below_rsp hc₃, hS]; exact stkD hp (by decide) (by decide)
      stk_d := by rw [below_rsp hc₃]; exact stkD hp (by decide) (by unfold sD scrBytes; omega)
      stk_sc := by rw [below_rsp hc₃, hWb]; exact stkD hp (by decide) (by decide) } (by omega)
    fun t₄ a₄ hu₄ => ?_)
  have hc₄ := hc₃.after hp a₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hS]; exact scS (by decide)
    · rw [hWb]; exact scS (by decide)
  have hr₄ := hu₄ [] hr₃ (by rw [hsi₃]; rfl)
  -- `finalize`
  refine WP.seq (WP.mono (shaFinArgs_run hp hc₄) fun t₅ ⟨hc₅, hm₅, hdi₅, hsi₅, hdx₅, hcx₅⟩ => ?_)
  have cw₅ : Covers [⟨scA s 0, 96⟩, ⟨scA s sDH, 32⟩, ⟨scA s sWork, 608⟩] t₅.wr :=
    (scCov hp hc₅ (by decide)).cons ((scCov hp hc₅ (by decide)).cons ((scCov hp hc₅ (by decide)).cons Covers.nil))
  refine Proof.Pbkdf2.Md.X86_64.Calls.fin_call (OK v).stream
    { rdi := hdi₅, rdx := hdx₅, rcx := hcx₅
      cw := by rw [hS, hF, hWb]; exact cw₅
      st_o := by rw [hS, hF]; exact scD (.inl (by decide)) (by decide) (by decide)
      st_sc := by rw [hS, hWb]; exact scD (.inl (by decide)) (by decide) (by decide)
      o_sc := by rw [hF, hWb]; exact scD (.inr (by decide)) (by decide) (by decide)
      stk_st := by rw [below_rsp hc₅, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc₅, hF]; exact stkD hp (by decide) (by decide)
      stk_sc := by rw [below_rsp hc₅, hWb]; exact stkD hp (by decide) (by decide) } fun t₆ a₆ hf₆ => ?_
  have hc₆ := hc₅.after hp a₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hS]; exact scS (by decide)
    · rw [hF]; exact scS (by decide)
    · rw [hWb]; exact scS (by decide)
  refine ⟨hc₆, ?_⟩
  have := hf₆ _ (by rw [hm₅]; exact hr₄) (by simp [Spec.Sha256.bytesAt]; omega)
    (by rw [hsi₅]; simp [Spec.Sha256.bytesAt])
  rw [hF, hD] at this
  rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])] at this
  rw [show Spec.Rsa.bytesAt t₆.mem (scA s sDH) 32 = Spec.Sha256.bytesAt t₆.mem (scA s sDH) 32 from rfl, this]
  show Spec.Sha256.hash ([] ++ Spec.Sha256.bytesAt t₃.mem (scA s sD) (kOf s)) = _
  rw [List.nil_append, show Spec.Sha256.bytesAt t₃.mem (scA s sD) (kOf s) =
    Spec.Rsa.bytesAt t₃.mem (scA s sD) (kOf s) from rfl, hD₃]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
