module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcBase
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on ARMv7: building `EM`

The pieces up to the call, correct (`*_wp`): `EM` written byte by byte
(`EMok`), as `Spec.RsaPkcs1Enc.encode` of the message and the padding
string (`enc`), and the zero test of the padding string (`zf`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Pc

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Precomputed VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_ldrb wp_strb wp_subs wp_cmp op2_imm op2_reg op2_lsr)

/-- Whether a string of bytes has a zero byte, as the code computes it: 1 if
it has one, 0 if not. -/
def zf (bs : List Byte) : BitVec 32 := if bs.all (· != 0) = true then 0 else 1

theorem zf_nil : zf [] = 0 := rfl

/-- The top bit of `b - 1`: 1 exactly when the byte `b` is zero. -/
theorem top_sub_one (b : Byte) : (b.setWidth 32 - 1) >>> 31 = if b = 0 then 1 else 0 := by
  have hb := b.isLt
  by_cases h : b = 0
  · subst h; decide
  · have h1 : 1 ≤ b.toNat := by
      rcases Nat.eq_zero_or_pos b.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using e)) h
      · exact e
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have e1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [e1, Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
    rw [show 2 ^ 32 - 1 + b.toNat = (b.toNat - 1) + 2 ^ 32 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    rw [Nat.div_eq_of_lt (by omega)]; rfl

theorem zf_snoc (bs : List Byte) (b : Byte) :
    zf (bs ++ [b]) = zf bs ||| (b.setWidth 32 - 1) >>> 31 := by
  rw [top_sub_one]
  unfold zf
  rw [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (bs.all (· != 0)) <;> by_cases hb : b = 0 <;> simp [hb] <;> split <;> decide

/-- `EM`, as the specification encodes it. -/
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.msg) P.ml
abbrev psB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.ps) P.pl
abbrev enc (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.encode (msgB P σ) (psB P σ)

theorem enc_length (P : EP) (σ : State) : (enc P σ).length = P.pl + P.ml + 3 := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.length_append, bytesAt_length]; simp; omega

theorem enc_getD_ps (P : EP) (σ : State) {i : Nat} (hi : i < P.pl) :
    (enc P σ).getD (2 + i) 0 = σ.mem (State.addr P.ps + BitVec.ofNat 64 i) := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp), getD_append_left _ _ _ (by simp [bytesAt_length]; omega)]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_sub_cancel_left]
  exact bytesAt_getD hi 0

theorem enc_getD_sep (P : EP) (σ : State) : (enc P σ).getD (2 + P.pl) 0 = 0 := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp), getD_append_right _ _ _ (by simp [bytesAt_length])]
  simp [bytesAt_length]

theorem enc_getD_msg (P : EP) (σ : State) {i : Nat} (hi : i < P.ml) :
    (enc P σ).getD (3 + P.pl + i) 0 = σ.mem (State.addr P.msg + BitVec.ofNat 64 i) := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [getD_append_right _ _ _ (by simp; omega),
    getD_append_right _ _ _ (by simp [bytesAt_length]; omega),
    getD_append_right _ _ _ (by simp [bytesAt_length]; omega)]
  simp only [List.length_cons, List.length_nil, bytesAt_length]
  rw [show 3 + P.pl + i - (0 + 1 + 1) - P.pl - (0 + 1) = i by omega]
  exact bytesAt_getD hi 0

/-- `EM`'s first `n` bytes written. -/
def EMok (P : EP) (σ s : State) (n : Nat) : Prop :=
  ∀ i < n, s.mem (P.lay.fr (oEM + i)) = (enc P σ).getD i 0

/-! ## Stores of bytes into `EM` -/

theorem em_ne (P : EP) {i j : Nat} (hij : i ≠ j) (hi : oEM + i < 2 ^ 64) (hj : oEM + j < 2 ^ 64) :
    P.lay.fr (oEM + i) ≠ P.lay.fr (oEM + j) :=
  Offset.add_ofNat_ne _ hi hj (by omega)

/-- `EMok` after a byte stored at index `n`. -/
theorem EMok.store {P : EP} {σ s : State} {n : Nat} (h : EMok P σ s n) {m : Mem} (hn : n < 1024)
    (hm : m = s.mem.writeW (P.lay.fr (oEM + n)) ((enc P σ).getD n 0)) :
    ∀ i < n + 1, m (P.lay.fr (oEM + i)) = (enc P σ).getD i 0 := by
  intro i hi
  subst hm
  rw [WriteBytes.writeW8_apply]
  by_cases e : i = n
  · subst e; simp
  · simp only [em_ne P e (by simp only [oEM]; omega) (by simp only [oEM]; omega), ↓reduceIte]
    exact h i (by omega)

theorem EMok.zero {P : EP} {σ s : State} : EMok P σ s 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem EMok.mono {P : EP} {σ s : State} {n m : Nat} (h : EMok P σ s n) (hm : m ≤ n) : EMok P σ s m :=
  fun i hi => h i (by omega)

/-- `EMok` of memory that changed apart from `EM`'s first `n` bytes. -/
theorem EMok.frame {P : EP} {σ s t : State} {n : Nat} (h : EMok P σ s n) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ i < n, ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr (oEM + i), 1⟩ r) :
    EMok P σ t n := fun i hi => by rw [hf.byte1 (hd i hi)]; exact h i hi

/-- A byte of `EM` stored through `rb + off = B + oEM + n` with the byte in `rt`. -/
theorem wp_strbEM {P : EP} {σ s : State} (hs : S P σ s) {rt rb : Reg} {off n : Nat} (hoff : off < 4096)
    (hn : n < P.K) (hb : s.gpr rb + BitVec.ofNat 32 off = P.B + BitVec.ofNat 32 (oEM + n))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → t.gpr = s.gpr → t.mem = s.mem.writeW (P.lay.fr (oEM + n)) ((s.gpr rt).setWidth 8) →
      WP isa (.block is) t Q) :
    WP isa (.block (.strb rt rb off :: is)) s Q := by
  have hk := hs.1.k1024
  have hF : oEM + n + 1 ≤ P.lay.F := by show oEM + n + 1 ≤ frameBytes; simp only [oEM, frameBytes]; omega
  refine wp_strb hoff (a := P.lay.fr (oEM + n)) ?_ (hs.2.inFr hF)
    fun t u => k t ⟨hs.1, hs.2.frameW hF ?_ u.rd u.wr u.sp⟩ u.gpr u.mem
  · rw [hb]
    exact hs.2.ok.addrB (by omega)
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

theorem bytesAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Rsa.bytesAt m p (j + 1) = Spec.Rsa.bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ]

end VG.Proof.RsaPkcs1Enc.Arm.Pc
