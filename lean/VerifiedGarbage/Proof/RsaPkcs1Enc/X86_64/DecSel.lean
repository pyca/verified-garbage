import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecValid

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the output

`*msg_len` and each byte of `out` selected without branches, reading both
`EM` and `AM` (`selLoop_ok`), and the result (`selPart_step`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- Byte `i` of the output. -/
def outByte (v ok : Bool) (kl i : Nat) (e a : Byte) : Byte :=
  if kl ≤ i ∧ ok = true then (if v then e else a) else 0

theorem selBody_run {t : State} {p q : Addr} {i k kl : Nat} {v ok : Bool} {e a : Byte} (hi : i < k)
    (hk : k < 2 ^ 32) (hkl : kl ≤ k) (hdi : t.gpr .rdi = p) (hsi : t.gpr .rsi = q)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) (hdx : t.gpr .rdx = BitVec.ofNat 64 kl) (h9 : t.gpr .r9 = BitVec.ofNat 64 k)
    (h10 : t.gpr .r10 = bmask v) (h11 : t.gpr .r11 = bmask ok) (he : t.mem (off p i) = e) (ha : t.mem (off q i) = a)
    (hie : InRegions (t.rd ++ t.wr) (off p i) 1) (hia : InRegions (t.rd ++ t.wr) (off q i) 1)
    (hw : InRegions t.wr (off p i) 1) :
    WP isa (.block selBody) t fun t' => t'.mem = t.mem.writeW (off p i) (outByte v ok kl i e a) ∧
      t'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧ t'.zf = some (decide (i + 1 = k)) ∧ Keep [.rax, .r8, .rcx] t t' := by
  refine WP.keep [.rax, .r8, .rcx] (c := .block selBody) (Q := fun t' =>
    t'.mem = t.mem.writeW (off p i) (outByte v ok kl i e a) ∧ t'.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧
      t'.zf = some (decide (i + 1 = k))) ?_ rfl |>.mono fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  have e1 : 0 + i = i := Nat.zero_add _
  xrun [selBody, ea_bxd (p := p) (j := i), ea_bxd (p := q) (j := i), hdi, hsi, hcx, e1, hie, hia, hw, he, ha,
    hdx, h9, h10, h11, borrow_mask, bmask_not, bmask_and, ofNat_add_one,
    ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega), sel_xor]
  congr 1
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show kl < 2 ^ 64 by omega)]
  unfold outByte
  have and255 : ∀ x : Byte, x &&& 255#8 = x := fun x => by
    rw [show (255#8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]
  by_cases h : kl ≤ i
  · cases ok <;> cases v <;> simp [h, Nat.not_lt.mpr h, bmask, and255, BitVec.xor_assoc]
  · cases ok <;> cases v <;> simp [h, Nat.lt_of_not_le h, bmask]


theorem selLoop_ok {t₀ : State} {p q : Addr} {k kl : Nat} {v ok : Bool} (hk0 : 0 < k) (hk : k < 2 ^ 32)
    (hkl : kl ≤ k) (hdi : t₀.gpr .rdi = p) (hsi : t₀.gpr .rsi = q) (hcx : t₀.gpr .rcx = BitVec.ofNat 64 0)
    (hdx : t₀.gpr .rdx = BitVec.ofNat 64 kl) (h9 : t₀.gpr .r9 = BitVec.ofNat 64 k) (h10 : t₀.gpr .r10 = bmask v)
    (h11 : t₀.gpr .r11 = bmask ok) (hie : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (off p i) 1)
    (hia : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (off q i) 1) (hw : ∀ i < k, InRegions t₀.wr (off p i) 1)
    (hpq : ∀ i < k, k ≤ ofs p (off q i)) :
    WP isa selLoop t₀ fun t => Keep [.rax, .r8, .rcx] t₀ t ∧ Outside p 0 k t₀.mem t.mem ∧
      ∀ i < k, byte t.mem p i = outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i)) := by
  refine wp_upto (a := 0) (N := k) hk0 (fun j u => Keep [.rax, .r8, .rcx] t₀ u ∧ Outside p 0 j t₀.mem u.mem ∧
      (∀ i < j, byte u.mem p i = outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i))) ∧
      u.gpr .rcx = BitVec.ofNat 64 j) (fun j _ hj u ⟨ku, ho, hb, hcxu⟩ => ?_)
    (fun _ ⟨k, ho, hb, _⟩ => ⟨k, ho, hb⟩) ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega), hcx⟩
  have g : ∀ r, r ∉ [Reg.rax, .r8, .rcx] → u.gpr r = t₀.gpr r := fun r hr => ku.gpr hr
  have he : u.mem (off p j) = t₀.mem (off p j) := ho _ (.inr (by rw [ofs_off0 _ (by omega)]; omega))
  have ha : u.mem (off q j) = t₀.mem (off q j) := ho _ (.inr (by have := hpq j hj; omega))
  refine WP.mono (selBody_run hj hk hkl ((g .rdi (by decide)).trans hdi) ((g .rsi (by decide)).trans hsi) hcxu
    ((g .rdx (by decide)).trans hdx) ((g .r9 (by decide)).trans h9) ((g .r10 (by decide)).trans h10)
    ((g .r11 (by decide)).trans h11) he ha (by rw [ku.2.1, ku.2.2]; exact hie j hj)
    (by rw [ku.2.1, ku.2.2]; exact hia j hj) (by rw [ku.2.2]; exact hw j hj))
    fun u' ⟨hm, hcx', hz, k'⟩ => ⟨hz, (ku.trans k').mono (by decide), ?_, ?_, hcx'⟩
  · rw [hm]; exact Outside.wb (Outside.mono ho (by omega) (by omega)) _ (by omega) (by omega) (by omega)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega) (by omega) (by omega)]; exact hb i hi
    · rw [show off p i = off p (0 + i) by rw [Nat.zero_add]]
      have := byte_wb_self u.mem p i (outByte v ok kl i (t₀.mem (off p i)) (t₀.mem (off q i)))
      simpa using this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
