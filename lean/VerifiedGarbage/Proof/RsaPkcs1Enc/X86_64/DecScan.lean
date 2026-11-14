module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPrf
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecKdk
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `RsaPkcs1Enc.X86_64.DecAl`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecLoops`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `CL` and `AM`

The candidate lengths `CL = IRPRF(KDK, "length", 256)` (`clLoop_step`) and
the alternative message `AM = IRPRF(KDK, "message", k)` (`amLoop_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress}

/-- The key derivation key of the entry state. -/
abbrev kdkOf (s : State) : List Byte := Spec.RsaPkcs1Enc.kdk (kOf s) (dB s) (cB s)

theorem clInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block clInit) t fun t' => Ctx s R EM t' ∧ word t'.mem (fb s) oI = BitVec.ofNat 64 0 ∧
      word t'.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s) ∧ KeepHi s [] t.mem t'.mem := by
  have hs := hc.frm hp
  have hk2 := hp.k2
  refine (WP.keep [.rax] (c := .block clInit) (Q := fun t' =>
    t'.mem = (t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 0)).writeW (off (fb s) oNB)
      (BitVec.ofNat 64 (nbOf s))) ?_ rfl).mono fun t' ⟨hm, k⟩ => ?_
  · xrun [clInit, ea_sp, hc.rsp, hs.ld (d := oK) (by decide), hs.st (d := oI) (by decide),
      hs.st (d := oNB) (by decide), word_ww _ _ _ (show oK + 8 ≤ oI ∨ oI + 8 ≤ oK by decide) (by decide) (by decide),
      hc.slots.sK]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow,
      show (BitVec.signExtend 64 (31 : BitVec 32)).toNat = 31 from rfl]
    unfold nbOf kOf; omega_using [hk2]
  · have hfw : Frame [⟨off (fb s) oI, 16⟩] t.mem t'.mem := by
      rw [hm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains (fb s) (d := oI) (n := 8) (e := oI) (k := 16) (by decide) (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains (fb s) (d := oNB) (n := 8) (e := oI) (k := 16) (by decide)
          (by decide) (by decide))
    refine ⟨hc.step hp k.2.1 k.2.2 (k.cs (by decide)) hfw fun r hr => by
        rw [List.mem_singleton.mp hr]; exact .inr (.inr fun _ h => h), ?_, ?_, ?_⟩
    · rw [hm, word_ww _ _ _ (by decide) (by decide) (by decide)]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact (keepHi_of_slot hp (by decide) _).trans (keepHi_of_slot hp (by decide) _)


/-- After `clLoop`: `CL` at `scratch + sCL`. -/
structure CLd (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256
  key : Spec.Rsa.bytesAt t.mem (scA s sKDK) 32 = kdkOf s
  sNB : word t.mem (fb s) oNB = BitVec.ofNat 64 (nbOf s)

theorem kdk_len {s : State} {m : Mem} (h : Spec.Rsa.bytesAt m (scA s sKDK) 32 = kdkOf s) : (kdkOf s).length = 32 := by
  rw [← h, blen]

theorem clLoop_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : KD s R EM t) :
    WP isa (clLoop (HH v)) t (CLd s R EM) := by
  refine WP.seq (WP.mono (clInit_run hp h.ctx) fun t₁ ⟨hc₁, hI₁, hNB₁, kh₁⟩ => ?_)
  have hk₁ : Spec.Rsa.bytesAt t₁.mem (scA s sKDK) 32 = kdkOf s := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.kdk
  refine WP.mono (prf_loop (v := v) hp (msg := msgCL) (L := 10) (N := 8) (dst := sCL) rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (kdk_len hk₁) msgCL_len
    (fun _ _ hc hi hdi hax _ => msgCL_run hp hc (by omega_using [hi]) hdi hax)
    (fun _ _ hc hi hI _ => incr8_ok hp hc hi hI) (pinv0 hc₁ hI₁ hNB₁ hk₁)) fun t₂ h₂ => ⟨h₂.ctx, ?_, h₂.key, h₂.sNB⟩
  have hb := h₂.blk
  rw [irprf_eq, show (256 + 31) / 32 = 8 from rfl]
  refine Eq.trans hb (List.take_of_length_le ?_).symm
  rw [← hb, blen]


theorem amInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (sp oI) .rax]) t fun t' => Ctx s R EM t' ∧
      word t'.mem (fb s) oI = BitVec.ofNat 64 0 ∧ word t'.mem (fb s) oNB = word t.mem (fb s) oNB ∧
      KeepHi s [] t.mem t'.mem := by
  have hs := hc.frm hp
  refine (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem.writeW (off (fb s) oI) (BitVec.ofNat 64 0)) ?_ rfl).mono
    fun t' ⟨hm, k⟩ => ?_
  · xrun [ea_sp, hc.rsp, hs.st (d := oI) (by decide)]
    rfl
  · have hfw : Frame [⟨off (fb s) oI, 8⟩] t.mem t'.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hc.step hp k.2.1 k.2.2 (k.cs (by decide)) hfw fun r hr => by
        rw [List.mem_singleton.mp hr]; exact .inr (.inr (Region.sub_prefix (by decide))), ?_, ?_, ?_⟩
    · rw [hm]; exact word_writeW_self _ _ _ _
    · rw [hm]; exact word_ww _ _ _ (by decide) (by decide) (by decide)
    · rw [hm]; exact keepHi_of_slot hp (by decide) _

/-- After `amLoop`: `AM` at `scratch + sAM`, and `CL` still at `scratch + sCL`. -/
structure AMd (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  cl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (kOf s) =
    Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)

theorem amLoop_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : CLd s R EM t) :
    WP isa (amLoop (HH v)) t (AMd s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hk64 : 64 ≤ kOf s := hk1
  have hnb : nbOf s ≤ 32 := by unfold nbOf; omega_using [hkk]
  have hnb0 : 0 < nbOf s := by unfold nbOf; omega_using [hk64]
  refine WP.seq (WP.mono (amInit_run hp h.ctx) fun t₁ ⟨hc₁, hI₁, hNB₁, kh₁⟩ => ?_)
  have hk₁ : Spec.Rsa.bytesAt t₁.mem (scA s sKDK) 32 = kdkOf s := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.key
  have hcl₁ : Spec.Rsa.bytesAt t₁.mem (scA s sCL) 256 =
      Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256 := by
    rw [kh₁ _ _ (by decide) (by decide) (by simp)]; exact h.cl
  refine WP.mono (prf_loop (v := v) hp (msg := msgAM (kOf s)) (L := 11) (N := nbOf s) (dst := sAM) rfl (by decide)
    (by decide) (by unfold sAM scrBytes; omega_using [hnb]) hnb0 hnb (kdk_len hk₁) (msgAM_len _)
    (fun _ _ hc hi hdi hax h9 => msgAM_run hp hc (by omega_using [hnb, hi]) hdi hax h9)
    (fun _ _ hc hi hI hNB => incrNB_ok hp hc hi hI hNB) (pinv0 hc₁ hI₁ (hNB₁.trans h.sNB) hk₁))
    fun t₂ h₂ => ⟨h₂.ctx, ?_, ?_⟩
  · rw [h₂.keep _ _ (by decide) (by decide) (by simp; unfold sCL sMsg sAM; omega_using [])]; exact hcl₁
  · have hb := h₂.blk
    rw [irprf_eq, show (kOf s + 31) / 32 = nbOf s from rfl]
    have hl : (List.flatMap (fun j => Spec.Hmac.hmac Spec.Hmac.sha256 (kdkOf s) (msgAM (kOf s) j))
        (List.range (nbOf s))).length = 32 * nbOf s := by rw [← hb, blen]
    rw [show (32 * nbOf s) = kOf s + (32 * nbOf s - kOf s) by unfold nbOf; omega_using [], bytesAt_add] at hb
    have := congrArg (List.take (kOf s)) hb
    rw [List.take_left' (blen _ _ _)] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the alternative length

The mask of the candidates, `2^bitLength(k - 11) - 1`, by doublings
(`maskPart_step`), and `AL` from `CL` without branches (`alPart_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

theorem maskInit_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block maskInit) t fun t' => t'.mem = t.mem ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s - 11) ∧
      t'.gpr .r8 = BitVec.ofNat 64 0 ∧ Keep [.r8, .r9] t t' := by
  have hs := hc.frm hp
  have hk1 := hp.k1
  refine WP.keep [.r8, .r9] (c := .block maskInit) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .r9 = BitVec.ofNat 64 (kOf s - 11) ∧ t'.gpr .r8 = BitVec.ofNat 64 0) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  xrun [maskInit, ea_sp, hc.rsp, hs.ld (d := oK) (by decide), hc.slots.sK]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (BitVec.signExtend 64 (11 : BitVec 32)).toNat = 11 from rfl, BitVec.toNat_ofNat]
  unfold kOf at *; omega_arith


theorem maskBody_run {t : State} {x j : Nat} (hx : x < 2 ^ 32) (hj : 2 ^ j - 1 < x)
    (h8 : t.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1)) (h9 : t.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (.block [.alu .add .r8 (.reg .r8), .alu .add .r8 (.imm 1), .alu .cmp .r8 (.reg .r9)]) t fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1) ∧
      t'.cf = some (decide (2 ^ (j + 1) - 1 < x)) ∧ Keep [.r8] t t' := by
  have hp := Nat.one_le_two_pow (n := j)
  have hs : 2 * (2 ^ j - 1) + 1 = 2 ^ (j + 1) - 1 := by rw [Nat.pow_succ]; omega_arith
  refine WP.keep [.r8] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (2 ^ (j + 1) - 1) ∧
      t'.cf = some (decide (2 ^ (j + 1) - 1 < x))) ?_ rfl |>.mono fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  have hb1 : 2 ^ j ≤ 2 ^ 32 := by omega_arith
  have hb2 : 2 ^ (j + 1) = 2 * 2 ^ j := Nat.pow_succ'
  generalize 2 ^ j = a at *
  generalize 2 ^ (j + 1) = b at *
  subst hb2
  have e : BitVec.ofNat 64 (a - 1) + BitVec.ofNat 64 (a - 1) + 1 = BitVec.ofNat 64 (2 * a - 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]; omega_arith
  xrun [h8, h9, e]
  simp only [BitVec.toNat_ofNat]
  congr 1
  apply propext
  rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]


theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h8 : t₀.gpr .r8 = BitVec.ofNat 64 0)
    (h9 : t₀.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun t' => t'.mem = t₀.mem ∧ t'.gpr .r8 = BitVec.ofNat 64 (bitMask x) ∧ Keep [.r8] t₀ t' := by
  refine WP.loop (M := isa) (fun n (u : State) => ∃ j, n = x - (2 ^ j - 1) ∧ 2 ^ j - 1 < x ∧ u.gpr .r8 = BitVec.ofNat 64 (2 ^ j - 1) ∧
      u.mem = t₀.mem ∧ Keep [.r8] t₀ u) ?_ x t₀ ⟨0, by simp, by simp; omega_arith, by simpa using h8, rfl, Keep.refl _ _⟩
  rintro n u ⟨j, rfl, hj, hr8, hm, k⟩
  refine WP.mono (maskBody_run hx hj hr8 ((k.gpr (by decide)).trans h9)) fun u' ⟨hm', hr8', hcf, k'⟩ => ?_
  have hb := bitMask_step hx1 hj
  by_cases hc : 2 ^ (j + 1) - 1 < x
  · refine .inr ⟨by simp [eval, hcf, hc], _, ?_, j + 1, rfl, hc, hr8', hm'.trans hm, (k.trans k').mono (by decide)⟩
    omega_arith
  · refine .inl ⟨by simp [eval, hcf, hc], hm'.trans hm, by rw [hr8', hb.2 (by omega_arith)], (k.trans k').mono (by decide)⟩


theorem zx (b : Byte) : BitVec.setWidth 64 b = BitVec.ofNat 64 b.toNat := BitVec.eq_of_toNat_eq (by simp)

theorem addN (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem andN {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left ha)).symm

/-- Selection by a borrow mask. -/
theorem sel_mask (r c : BitVec 64) (b : Bool) :
    (r ^^^ c) &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool b)) ^^^ c = if b then r else c := by
  cases b
  · simp
  · rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 by decide]
    simp only [BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, ite_true]

theorem alBody_run {t : State} {p : Addr} {j M x al : Nat} (hj : j < 128) (hM : M < 2 ^ 16) (hx : x < 2 ^ 16)
    (hsi : t.gpr .rsi = p) (hcx : t.gpr .rcx = BitVec.ofNat 64 (2 * j)) (h8 : t.gpr .r8 = BitVec.ofNat 64 M)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 x) (h11 : t.gpr .r11 = BitVec.ofNat 64 al)
    (hin : ∀ i < 256, InRegions (t.rd ++ t.wr) (off p i) 1) :
    WP isa (.block [.movzx8 .rax (bx .rsi .rcx), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .movzx8 .rdx (bx .rsi .rcx 1), .alu .add .rax (.reg .rdx),
    .alu .and .rax (.reg .r8), .mov .rdx (.reg .r9), .alu .cmp .rdx (.reg .rax), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .r11 (.reg .rax), .alu .and .r11 (.reg .rdx), .alu .xor .r11 (.reg .rax), .alu .add .rcx (.imm 2),
    .alu .cmp .rcx (.imm 256)]) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = BitVec.ofNat 64 (let c := (256 * (t.mem (off p (2 * j))).toNat + (t.mem (off p (2 * j + 1))).toNat) &&& M
        if c ≤ x then c else al) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (2 * (j + 1)) ∧ t'.zf = some (decide (j + 1 = 128)) ∧
      Keep [.rax, .rdx, .r11, .rcx] t t' := by
  refine WP.keep [.rax, .rdx, .r11, .rcx] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = BitVec.ofNat 64 (let c := (256 * (t.mem (off p (2 * j))).toNat + (t.mem (off p (2 * j + 1))).toNat) &&& M
        if c ≤ x then c else al) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (2 * (j + 1)) ∧ t'.zf = some (decide (j + 1 = 128))) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  have e1 : 0 + 2 * j = 2 * j := Nat.zero_add _
  have e2 : 1 + 2 * j = 2 * j + 1 := Nat.add_comm _ _
  xrun [ea_bxd (p := p) (j := 2 * j), hsi, hcx, e1, e2, hin (2 * j) (by omega_arith), hin (2 * j + 1) (by omega_arith), h8, h9,
    h11, zx, addN, ← Nat.two_mul]
  have ha := (t.mem (off p (2 * j))).isLt
  have hb := (t.mem (off p (2 * j + 1))).isLt
  generalize (t.mem (off p (2 * j))).toNat = a at *
  generalize (t.mem (off p (2 * j + 1))).toNat = b at *
  have hc : 256 * a + b &&& M ≤ M := Nat.and_le_right
  have e2 : BitVec.ofNat 64 (2 * j) + 2 = BitVec.ofNat 64 (2 * (j + 1)) := BitVec.eq_of_toNat_eq (by simp; omega_arith)
  rw [show 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * a))))))) = 256 * a by omega_arith, andN (by omega_arith) (by omega_arith), sel_mask,
    e2, show BitVec.signExtend 64 (256 : BitVec 32) = BitVec.ofNat 64 256 by decide,
    ofNat_sub_beq (by omega_arith) (by decide)]
  refine ⟨?_, rfl, by simp only [decide_eq_decide]; omega_arith⟩
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show 256 * a + b &&& M < 2 ^ 64 by omega_arith)]
  by_cases h : 256 * a + b &&& M ≤ x
  · simp [h, show ¬ x < 256 * a + b &&& M by omega_arith]
  · simp [h, show x < 256 * a + b &&& M by omega_arith]


theorem altFold_le (k : Nat) (CL : List Byte) (j : Nat) :
    (List.range j).foldl (altStep k CL) 0 ≤ k - 11 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [foldl_range_succ]
    simp only [altStep]
    split <;> omega_arith

/-- The candidate, as the loop computes it. -/
theorem altStep_eq (k : Nat) (CL : List Byte) (al i : Nat) (h : 2 * i + 1 < CL.length) :
    altStep k CL al i = (let c := (256 * (CL[2 * i]'(by omega_arith)).toNat + (CL[2 * i + 1]'h).toNat) &&& bitMask (k - 11)
      if c ≤ k - 11 then c else al) := by
  simp only [altStep, cand_eq, bitMask, Nat.and_two_pow_sub_one_eq_mod, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show 2 * i < CL.length by omega_arith), List.getElem?_eq_getElem h, Option.getD_some]

/-- After the mask: `bitMask (k - 11)` in `r8` and `k - 11` in `r9`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  am : AMd s R EM t
  r8 : t.gpr .r8 = BitVec.ofNat 64 (bitMask (kOf s - 11))
  r9 : t.gpr .r9 = BitVec.ofNat 64 (kOf s - 11)

theorem maskPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State}
    (h : AMd s R EM t) : WP isa maskPart t (MK s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  refine WP.seq (WP.mono (maskInit_run hp h.ctx) fun t₁ ⟨hm₁, h9₁, h8₁, k₁⟩ => ?_)
  refine WP.mono (maskLoop_ok (x := kOf s - 11) (by unfold kOf; omega_arith) (by unfold kOf; omega_arith) h8₁ h9₁)
    fun t₂ ⟨hm₂, h8₂, k₂⟩ => ?_
  have hm : t₂.mem = t.mem := hm₂.trans hm₁
  have k := k₁.trans k₂
  exact ⟨⟨h.ctx.regs hp hm k (by decide), hm ▸ h.cl, hm ▸ h.am⟩, h8₂, (k₂.gpr (by decide)).trans h9₁⟩


theorem bitMask_le {x : Nat} (hx : x ≠ 0) : bitMask x ≤ 2 * x := by
  simp only [bitMask, Spec.RsaPkcs1Enc.bitLength, hx, ↓reduceIte, Nat.pow_succ]
  have := Nat.log2_self_le hx
  omega_arith

/-- `CL`. -/
abbrev clOf (s : State) : List Byte := Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After `alPart`: `AL` in `r11`. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  mkd : MK s R EM t
  r11 : t.gpr .r11 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s))

theorem alPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : MK s R EM t) :
    WP isa alPart t (AL s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hc := h.am.ctx
  have hs := hc.frm hp
  have hsc := hc.scr hp
  -- `alInit`
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .r11] (c := .block alInit) (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rsi = scA s sCL ∧ t'.gpr .rcx = BitVec.ofNat 64 0 ∧ t'.gpr .r11 = BitVec.ofNat 64 0) (by
    xrun [alInit, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
      hc.slots.sScr, sx (d := sCL) (by decide)]) rfl) fun t₁ ⟨⟨hm₁, hsi₁, hcx₁, h11₁⟩, k₁⟩ => ?_)
  have hCL : Spec.Rsa.bytesAt t₁.mem (scA s sCL) 256 = clOf s := hm₁ ▸ h.am.cl
  have hlen : (clOf s).length = 256 := by rw [← hCL, blen]
  have hin : ∀ i < 256, InRegions (t₁.rd ++ t₁.wr) (off (scA s sCL) i) 1 := fun i hi => by
    obtain ⟨r, hr, hcr⟩ := (hsc.congr k₁.2.2).region (d := sCL + i) (n := 1) (by unfold sCL scrBytes; omega_arith)
      (by decide)
    exact ⟨r, List.mem_append_right _ hr, by rw [scA, off_off]; exact hcr⟩
  have hM : bitMask (kOf s - 11) < 2 ^ 16 := by
    have := bitMask_le (x := kOf s - 11) (by unfold kOf; omega_arith); unfold kOf at *; omega_arith
  have hget : ∀ i (hi : i < 256), (clOf s)[i]'(by omega_arith) = t₁.mem (off (scA s sCL) i) := fun i hi => by
    have := bget t₁.mem (scA s sCL) (n := 256) (i := i) (by rw [blen]; exact hi)
    simp only [hCL] at this; rw [this, off]
  refine WP.mono (wp_upto (a := 0) (N := 128) (by decide) (fun j u => Keep [.rax, .rdx, .r11, .rcx] t₁ u ∧
      u.mem = t₁.mem ∧ u.gpr .r11 = BitVec.ofNat 64 ((List.range j).foldl (altStep (kOf s) (clOf s)) 0) ∧
      u.gpr .rcx = BitVec.ofNat 64 (2 * j)) (fun j _ hj u ⟨ku, hmu, h11u, hcxu⟩ => ?_) (fun _ h => h)
      ⟨Keep.refl _ _, rfl, h11₁, hcx₁⟩) fun t₂ ⟨k₂, hm₂, h11₂, _⟩ => ?_
  · have hin' : ∀ i < 256, InRegions (u.rd ++ u.wr) (off (scA s sCL) i) 1 := by
      rw [ku.2.1, ku.2.2]; exact hin
    refine WP.mono (alBody_run (p := scA s sCL) hj hM (by unfold kOf; omega_arith) ((ku.gpr (by decide)).trans hsi₁)
      hcxu ((ku.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r8))
      ((ku.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r9)) h11u hin')
      fun u' ⟨hm', h11', hcx', hz, k'⟩ => ⟨hz, (ku.trans k').mono (by decide), hm'.trans hmu, ?_, hcx'⟩
    rw [h11', foldl_range_succ, altStep_eq _ _ _ _ (by omega_arith), hget _ (by omega_arith), hget _ (by omega_arith), hmu]
  · have hm : t₂.mem = t.mem := hm₂.trans hm₁
    have k := k₁.trans k₂
    refine ⟨⟨⟨h.am.ctx.regs hp hm k (by decide), hm ▸ h.am.cl, hm ▸ h.am.am⟩,
      (k.gpr (by decide)).trans h.r8, (k.gpr (by decide)).trans h.r9⟩, ?_⟩
    rw [h11₂, altLength_eq]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the scan of `EM`

The first zero of `EM` from index 2, found without branches on its bytes:
whether there is one as a mask (`rdx`) and where (`r10`) (`scanPart_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- A mask: all ones or zero. -/
def bmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem lit_and (x : BitVec 64) : 18446744073709551615#64 &&& x = x := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]

theorem borrow_mask (b : Bool) : 0#64 - BitVec.setWidth 64 (BitVec.ofBool b) = bmask b := by
  cases b <;> decide

theorem scanBody_run {t : State} {p : Addr} {EM : List Byte} {k j : Nat} (hj : j < k) (hk : k < 2 ^ 32)
    (hEM : ∀ i < k, t.mem (off p i) = EM.getD i 1) (hin : ∀ i < k, InRegions (t.rd ++ t.wr) (off p i) 1)
    (hdi : t.gpr .rdi = p) (h9 : t.gpr .r9 = BitVec.ofNat 64 k) (hcx : t.gpr .rcx = BitVec.ofNat 64 j)
    (hdx : t.gpr .rdx = bmask (firstZero EM j).isSome)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 ((firstZero EM j).getD 0)) (h2 : 2 ≤ j) :
    WP isa (.block [.movzx8 .rax (bx .rdi .rcx), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .mov .rsi (.reg .rdx), .alu .xor .rsi (.imm (BitVec.ofInt 32 (-1))), .alu .and .rsi (.reg .rax),
    .alu .and .rsi (.reg .rcx), .alu .or .r10 (.reg .rsi), .alu .or .rdx (.reg .rax), .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .r9)]) t fun t' => t'.mem = t.mem ∧ t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      t'.zf = some (decide (j + 1 = k)) ∧ t'.gpr .rdx = bmask (firstZero EM (j + 1)).isSome ∧
      t'.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (j + 1)).getD 0) ∧ Keep [.rax, .rsi, .r10, .rdx, .rcx] t t' := by
  refine WP.keep [.rax, .rsi, .r10, .rdx, .rcx] (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      t'.zf = some (decide (j + 1 = k)) ∧ t'.gpr .rdx = bmask (firstZero EM (j + 1)).isSome ∧
      t'.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (j + 1)).getD 0)) ?_ rfl |>.mono
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  have e1 : 0 + j = j := Nat.zero_add _
  xrun [ea_bxd (p := p) (j := j), hdi, hcx, e1, hin j hj, hEM j hj, h9, hdx, h10, ofNat_add_one, borrow_mask,
    ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_using [hj, hk]) (show k < 2 ^ 64 by omega_using [hk])]
  have hz : ∀ b : Byte, decide ((BitVec.setWidth 64 b).toNat < BitVec.toNat (1 : BitVec 64)) =
      decide (b = 0) := by
    intro b
    rw [zext_toNat, one64_toNat]
    exact decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by simp; omega_using [h]), fun h => by simp [h]⟩
  rw [hz, show BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 by decide]
  rw [show firstZero EM (j + 1) = (match firstZero EM j with
    | some i => some i
    | none => if 2 ≤ j ∧ EM.getD j 1 = 0 then some j else none) from rfl]
  generalize EM.getD j 1 = b
  by_cases hb : b = 0#8 <;> cases firstZero EM j <;> simp [hb, h2, bmask, lit_and]


/-- After the scan. -/
structure SC (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  am : Spec.Rsa.bytesAt t.mem (scA s sAM) (kOf s) =
    Spec.RsaPkcs1Enc.irprf (kdkOf s) (Spec.RsaPkcs1Enc.ascii "message") (kOf s)
  r11 : t.gpr .r11 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (kOf s) (clOf s))
  rdi : t.gpr .rdi = s.gpr .rdi
  r9 : t.gpr .r9 = BitVec.ofNat 64 (kOf s)
  rdx : t.gpr .rdx = bmask (firstZero EM (kOf s)).isSome
  r10 : t.gpr .r10 = BitVec.ofNat 64 ((firstZero EM (kOf s)).getD 0)

/-- `EM`'s bytes, in a state of `Ctx`. -/
theorem Ctx.em {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) {i : Nat}
    (hi : i < kOf s) : t.mem (off (s.gpr .rdi) i) = EM.getD i 1 := by
  rw [← hc.out, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blen]; exact hi), Option.getD_some, bget]

theorem Ctx.outIn {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {i n : Nat} (hi : i + n ≤ kOf s) : InRegions t.wr (off (s.gpr .rdi) i) n := by
  have hsi := hp.hsi
  have hw := hp.wO
  refine ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by rw [hc.wr, hp.hwr]; simp, ?_⟩
  exact Offset.contains_base _ (by unfold kOf at hi; omega_using [hi, hsi]) (by unfold kOf at hi; omega_using [hi])

theorem scanPart_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : AL s R EM t) :
    WP isa scanPart t (SC s R EM) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hkk1 : 64 ≤ kOf s := hk1
  have hc := h.mkd.am.ctx
  have hs := hc.frm hp
  have h8 : s.gpr .r8 = BitVec.ofNat 64 (kOf s) := by simp [kOf]
  refine WP.seq (WP.mono (WP.keep [.rdi, .r9, .rcx, .rdx, .r10] (c := .block scanInit) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .r9 = BitVec.ofNat 64 (kOf s) ∧
      t'.gpr .rcx = BitVec.ofNat 64 2 ∧ t'.gpr .rdx = BitVec.ofNat 64 0 ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [scanInit, ea_sp, hc.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), hc.slots.sOut,
      hc.slots.sK, h8]) rfl) fun t₁ ⟨⟨hm₁, hdi₁, h9₁, hcx₁, hdx₁, h10₁⟩, k₁⟩ => ?_)
  have hc₁ : Ctx s R EM t₁ := hc.regs hp hm₁ k₁ (by decide)
  refine WP.mono (wp_upto (a := 2) (N := kOf s) (by omega_using [hkk1]) (fun j u => Keep [.rax, .rsi, .r10, .rdx, .rcx] t₁ u ∧
      u.mem = t₁.mem ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧ u.gpr .rdx = bmask (firstZero EM j).isSome ∧
      u.gpr .r10 = BitVec.ofNat 64 ((firstZero EM j).getD 0))
      (fun j h2 hj u ⟨ku, hmu, hcxu, hdxu, h10u⟩ => ?_) (fun _ h => h)
      ⟨Keep.refl _ _, rfl, hcx₁, by rw [hdx₁]; rfl, by rw [h10₁]; rfl⟩) fun t₂ ⟨k₂, hm₂, _, hdx₂, h10₂⟩ => ?_
  · refine WP.mono (scanBody_run (p := s.gpr .rdi) hj (by omega_using [hkk]) (fun i hi => by rw [hmu]; exact hc₁.em hi)
      (fun i hi => by
        obtain ⟨r, hr, hcr⟩ := hc₁.outIn hp (i := i) (n := 1) (by omega_using [hi])
        exact ⟨r, List.mem_append_right _ (by rw [ku.2.2]; exact hr), hcr⟩)
      ((ku.gpr (by decide)).trans hdi₁) ((ku.gpr (by decide)).trans h9₁) hcxu hdxu h10u h2)
      fun u' ⟨hm', hcx', hz, hdx', h10', k'⟩ => ⟨hz, (ku.trans k').mono (by decide), hm'.trans hmu, hcx', hdx', h10'⟩
  · have hm : t₂.mem = t.mem := hm₂.trans hm₁
    exact ⟨hc₁.regs hp hm₂ k₂ (by decide), hm ▸ h.mkd.am.am, (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h.r11),
      (k₂.gpr (by decide)).trans hdi₁, (k₂.gpr (by decide)).trans h9₁, hdx₂, h10₂⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
