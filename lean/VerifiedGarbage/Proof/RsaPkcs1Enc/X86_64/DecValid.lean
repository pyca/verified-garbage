import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecScan

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the checks of the padding

The validity mask, the selected length and the mask of the private-key
operation's success, from the scan, without branches (`validBlock_run`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

theorem zero_test (b : Byte) : decide ((BitVec.setWidth 64 b).toNat < BitVec.toNat (1 : BitVec 64)) =
    decide (b = 0) := by
  rw [zext_toNat, one64_toNat]
  exact decide_eq_decide.mpr ⟨fun h => BitVec.eq_of_toNat_eq (by simp; omega), fun h => by simp [h]⟩

theorem two_test (b : Byte) : decide ((BitVec.setWidth 64 b ^^^ 2).toNat < BitVec.toNat (1 : BitVec 64)) =
    decide (b = 2) := by
  rw [one64_toNat]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by subst h; decide⟩
  have h0 : BitVec.setWidth 64 b ^^^ 2 = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  have : BitVec.setWidth 64 b = 2 := by
    have := congrArg (· ^^^ (2 : BitVec 64)) h0
    simpa [BitVec.xor_assoc] using this
  have := congrArg (BitVec.setWidth 8) this
  rwa [trunc_zext] at this

theorem ten_test {sep : Nat} (h : sep < 2 ^ 64) :
    decide ((BitVec.ofNat 64 sep).toNat < (BitVec.signExtend 64 (10 : BitVec 32)).toNat) = decide (sep < 10) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (BitVec.signExtend 64 (10 : BitVec 32)).toNat = 10 from rfl]

theorem ok_test (R : BitVec 64) :
    decide ((BitVec.setWidth 64 (BitVec.setWidth 32 R) ^^^ 1).toNat < BitVec.toNat (1 : BitVec 64)) = decide (R.setWidth 32 = 1) := by
  rw [one64_toNat]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]; decide⟩
  have h0 : BitVec.setWidth 64 (BitVec.setWidth 32 R) ^^^ 1 = 0 :=
    BitVec.eq_of_toNat_eq (by rw [show (0 : BitVec 64).toNat = 0 from rfl]; omega)
  have : BitVec.setWidth 64 (BitVec.setWidth 32 R) = 1 := by
    have := congrArg (· ^^^ (1 : BitVec 64)) h0
    simpa [BitVec.xor_assoc] using this
  have := congrArg (BitVec.setWidth 32) this
  rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this

theorem bmask_not (a : Bool) : bmask a ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = bmask (!a) := by
  cases a <;> decide

theorem bmask_and (a b : Bool) : bmask a &&& bmask b = bmask (a && b) := by
  cases a <;> cases b <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : (x ^^^ y) &&& bmask v ^^^ x = if v then y else x := by
  cases v
  · simp [bmask]
  · simp only [bmask, ite_true]
    rw [BitVec.and_allOnes, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Whether the padding is valid, from the scan. -/
abbrev vOf (b0 b1 : Byte) (f : Bool) (sep : Nat) : Bool := decide (b0 = 0 ∧ b1 = 2 ∧ f = true ∧ 10 ≤ sep)

/-- The selected length. -/
abbrev lenOf (v : Bool) (sep al k : Nat) : BitVec 64 :=
  if v then BitVec.ofNat 64 (k - sep - 1) else BitVec.ofNat 64 al

/-- Whether the private-key operation succeeded. -/
abbrev okOf (R : BitVec 64) : Bool := decide (R.setWidth 32 = 1)

/-- What `validBlock` leaves. -/
def VOut (b0 b1 : Byte) (f : Bool) (sep al k : Nat) (R : BitVec 64) (t t' : State) : Prop :=
  t'.mem = t.mem ∧ t'.gpr .r10 = bmask (vOf b0 b1 f sep) ∧
    t'.gpr .rdx = lenOf (vOf b0 b1 f sep) sep al k &&& bmask (okOf R) ∧ t'.gpr .r11 = bmask (okOf R) ∧
    t'.gpr .rsi = BitVec.ofNat 64 k - lenOf (vOf b0 b1 f sep) sep al k

theorem validBlock_run {t : State} {p F : Addr} {b0 b1 : Byte} {f : Bool} {sep al k : Nat} {R : BitVec 64}
    (hdi : t.gpr .rdi = p) (h0 : t.mem p = b0) (h1 : t.mem (off p 1) = b1)
    (hi0 : InRegions (t.rd ++ t.wr) p 1) (hi1 : InRegions (t.rd ++ t.wr) (off p 1) 1)
    (hdx : t.gpr .rdx = bmask f) (h10 : t.gpr .r10 = BitVec.ofNat 64 sep) (h11 : t.gpr .r11 = BitVec.ofNat 64 al)
    (h9 : t.gpr .r9 = BitVec.ofNat 64 k) (hsp : t.gpr .rsp = F) (hR : t.mem.readW (F + BitVec.ofNat 64 oR) 64 = R)
    (hiR : InRegions (t.rd ++ t.wr) (F + BitVec.ofNat 64 oR) 8) (hsk : sep < k) (hk : k < 2 ^ 32) :
    WP isa (.block validBlock) t fun t' => VOut b0 b1 f sep al k R t t' ∧ Keep [.rax, .rsi, .rdx, .r10, .r11] t t' := by
  refine WP.keep [.rax, .rsi, .rdx, .r10, .r11] (c := .block validBlock) (Q := VOut b0 b1 f sep al k R t) ?_ rfl
  xrun [VOut, validBlock, ea_atd (p := p), hdi, h0, h1, hi0, hi1, hdx, h10, h11, h9, ea_sp, hsp, hR, hiR, borrow_mask,
    zero_test, two_test, ten_test (show sep < 2 ^ 64 by omega), ok_test, bmask_not, bmask_and]
  have e : BitVec.ofNat 64 k - BitVec.ofNat 64 sep - 1 = BitVec.ofNat 64 (k - sep - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  have hv : (decide (b0 = 0) && decide (b1 = 2) && f && !decide (sep < 10)) = vOf b0 b1 f sep := by
    simp only [vOf]
    by_cases h₂ : sep < 10
    · simp [h₂, show ¬ 10 ≤ sep by omega]
    · simp [h₂, show 10 ≤ sep by omega, Bool.and_assoc]
  rw [e, sel_xor, hv]
  exact ⟨rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
