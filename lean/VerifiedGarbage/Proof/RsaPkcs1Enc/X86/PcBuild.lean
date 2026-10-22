module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcBase
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Isa

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: building `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcBuild.lean`): the mask of a zero
byte in `PS`, as the code computes it (`zm`), `EM` as the specification
encodes it (`enc`), and its first bytes in the frame (`EMok`), stored one at
a time (`wp_st8EM`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- Whether a string of bytes has a zero byte, as the mask the code computes. -/
def zm (bs : List Byte) : BitVec 32 := if bs.all (· != 0) = true then 0#32 else BitVec.allOnes 32

theorem zm_nil : zm [] = 0 := rfl

theorem zm_snoc (bs : List Byte) (b : Byte) :
    zm (bs ++ [b]) = zm bs |||
      (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  have hb : (b.toNat < 1) = (b = 0) := by
    apply propext; constructor
    · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega)
    · intro h; subst h; decide
  simp only [hb]
  unfold zm
  rw [List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (bs.all (· != 0)) <;> by_cases h : b = 0 <;> simp [h] <;> (try split) <;> (try decide)

/-- `EM`, as the specification encodes it. -/
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.msg.setWidth 64) P.ml
abbrev psB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (P.ps.setWidth 64) P.pl
abbrev enc (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.encode (msgB P σ) (psB P σ)

theorem enc_length (P : EP) (σ : State) : (enc P σ).length = P.pl + P.ml + 3 := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.length_append, Proof.RsaPkcs1Sig.bytesAt_len]; simp; omega

theorem enc0 (P : EP) (σ : State) : (enc P σ).getD 0 0 = 0 := rfl
theorem enc1 (P : EP) (σ : State) : (enc P σ).getD 1 0 = 2 := rfl

theorem enc_getD_ps (P : EP) (σ : State) {i : Nat} (hi : i < P.pl) :
    (enc P σ).getD (2 + i) 0 = σ.mem (P.ps.setWidth 64 + BitVec.ofNat 64 i) := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp),
    Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega)]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.add_sub_cancel_left]
  exact Proof.RsaPkcs1Sig.bytesAt_getD hi 0

theorem enc_getD_sep (P : EP) (σ : State) : (enc P σ).getD (2 + P.pl) 0 = 0 := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp),
    Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len])]
  simp [Proof.RsaPkcs1Sig.bytesAt_len]

theorem enc_getD_msg (P : EP) (σ : State) {i : Nat} (hi : i < P.ml) :
    (enc P σ).getD (3 + P.pl + i) 0 = σ.mem (P.msg.setWidth 64 + BitVec.ofNat 64 i) := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp; omega),
    Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega),
    Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega)]
  simp only [List.length_cons, List.length_nil, Proof.RsaPkcs1Sig.bytesAt_len]
  rw [show 3 + P.pl + i - (0 + 1 + 1) - P.pl - (0 + 1) = i by omega]
  exact Proof.RsaPkcs1Sig.bytesAt_getD hi 0

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

theorem frame_byte1 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 1⟩ r) : m' a = m a := by
  have := hf.bytes (R := ⟨a, 1⟩) hd (by show (1 : Nat) ≤ 2 ^ 64; decide) (i := 0) (by show 0 < 1; decide)
  simpa using this

/-- `EMok` of memory that changed apart from `EM`'s first `n` bytes. -/
theorem EMok.frame {P : EP} {σ s t : State} {n : Nat} (h : EMok P σ s n) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ i < n, ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr (oEM + i), 1⟩ r) :
    EMok P σ t n := fun i hi => by rw [frame_byte1 hf (hd i hi)]; exact h i hi

theorem EMok.of_mem {P : EP} {σ s t : State} {n : Nat} (h : EMok P σ s n) (hm : t.mem = s.mem) :
    EMok P σ t n := fun i hi => by rw [hm]; exact h i hi

/-- A byte of `EM` stored through `rb + off = B + oEM + n` from the low byte `r`. -/
theorem wp_st8EM {P : EP} {σ s : State} (hs : S P σ s) {r : Reg8} {rb : Reg} {off n : Nat}
    (hn : n < P.K) (hb : s.gpr rb + BitVec.ofNat 32 off = P.B + BitVec.ofNat 32 (oEM + n))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → t.gpr = s.gpr →
      t.mem = s.mem.writeW (P.lay.fr (oEM + n)) ((s.gpr r.reg).setWidth 8) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 ⟨rb, off⟩ r :: is)) s Q := by
  have hk := hs.1.k1024
  have hF : oEM + n + 1 ≤ P.lay.F := by show oEM + n + 1 ≤ frameBytes; simp only [oEM, frameBytes]; omega
  refine wp_store8 (a := P.lay.fr (oEM + n)) ?_ (hs.2.inFr hF)
    fun t u => k t ⟨hs.1, hs.2.frameW hF ?_ u.rd u.wr (by rw [u.gpr])⟩ u.gpr u.mem
  · have hd : oEM + n < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, oEM, frameBytes] at hF ⊢; omega
    rw [ea_at, addr, hb]
    exact hs.2.ok.addrB hd
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

end VG.Proof.RsaPkcs1Enc.X86.Pc
