module

import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.PcTaint
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Precomputed
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
public import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Entry
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.Sig

/-! ### `RsaPkcs1Enc.X86.PcBuild`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.PcBase`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: where everything is

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcBase.lean`): `EP`, what two runs
share (the frame's base `B`, the pointers, the lengths, `e`'s bytes and
`pre`'s words), and its layout (`EP.lay`), with the 100 bytes below the frame
that `vg_rsa_public_precomputed_checked` and its return address use.
`In P σ`: the state `σ` the body starts from; `S P σ s`: a state of the
body. The shared contract, with the stack of the frames and of the call,
gives `In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  n : BitVec 32
  e : BitVec 32
  msg : BitVec 32
  ps : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  ml : Nat
  pl : Nat
  sl : Nat
  rl : Nat
  eB : List Byte
  pw : List (BitVec 64)

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨P.out.setWidth 64, P.K⟩
abbrev N : Region := ⟨P.n.setWidth 64, P.K⟩
abbrev E : Region := ⟨P.e.setWidth 64, P.el⟩
abbrev MSG : Region := ⟨P.msg.setWidth 64, P.ml⟩
abbrev PS : Region := ⟨P.ps.setWidth 64, P.pl⟩
abbrev SCR : Region := ⟨P.scr.setWidth 64, P.sl * 8⟩
abbrev PRE : Region := ⟨P.pre.setWidth 64, P.rl * 8⟩

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.msg,
    BitVec.ofNat 32 P.ml, P.ps, BitVec.ofNat 32 P.pl, P.scr, BitVec.ofNat 32 P.sl, P.pre,
    BitVec.ofNat 32 P.rl]

abbrev ro : List Region := [P.N, P.E, P.MSG, P.PS, P.PRE]
abbrev rw : List Region := [P.OUT, P.SCR]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  argv := P.argv
  ro := P.ro
  rw := P.rw
  C := 100

end EP

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  mlK : P.ml + 11 ≤ P.K
  plK : P.pl = P.K - P.ml - 3
  slK : Spec.Rsa.publicScratchWords P.K ≤ P.sl
  sl32 : P.sl < 2 ^ 32
  rlK : P.rl = Spec.Rsa.precomputedWords P.K
  eB : Spec.Rsa.bytesAt σ.mem (P.e.setWidth 64) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (P.pre.setWidth 64) P.rl = P.pw

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2
theorem pl8 : 8 ≤ P.pl := by have := h.plK; have := h.mlK; omega_arith
theorem em_len : P.pl + P.ml + 3 = P.K := by have := h.plK; have := h.mlK; omega_arith

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 16 + frameBytes + 100

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Proof.RsaPkcs1Enc.encryptPrecomputedContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 frameBytes
  out := arg s 0
  n := arg s 2
  e := arg s 4
  msg := arg s 6
  ps := arg s 8
  scr := arg s 10
  pre := arg s 12
  K := (arg s 3).toNat
  el := (arg s 5).toNat
  ml := (arg s 7).toNat
  pl := (arg s 9).toNat
  sl := (arg s 11).toNat
  rl := (arg s 13).toNat
  eB := Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat
  pw := Spec.Rsa.wordsAt s.mem ((arg s 12).setWidth 64) (arg s 13).toNat

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes (ep s).argv (ep s).ro (ep s).rw s 100 := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  sig_split h
  rename_i hsp hsa hrd hwr oN oE oM oP oS oR oA nS nA eS eA mS mA pS pA sR sA rA rO rN rE rM rP rS rR rAr kO kN
    kE kM kP kS kR kA fO fN fE fM fP fS fR kv olk el1 elK mlK plK slK
  have rlK := h
  simp only [stackBytes, frameBytes, Nat.reduceAdd] at hsp kO kN kE kM kP kS kR kA
  have a1 : arg s 1 = arg s 3 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oN oE oM oP oS oR oA rO kO fO
  have h16 : 4 * Impl.RsaPkcs1Sig.X86.savedRegs.length ≤ (s.gpr .esp).toNat := by
    simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_arith
  have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
      (entered frameBytes s).mem :=
    pushed_frame (by decide) h16
  have below16 : Region.Sub (below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length))
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 1188, 1188⟩ := by
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have sl32 : (arg s 11).toNat < 2 ^ 32 := (arg s 11).isLt
  refine
    { ok := ?_
      kv := kv, el1 := el1, elK := elK, mlK := mlK, plK := plK, slK := slK, sl32 := sl32, rlK := rlK
      eB := Proof.RsaPkcs1Sig.bytesAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kE.sub_left below16).symm)
        (by show (arg s 5).toNat ≤ 2 ^ 64; omega_arith)
      pw := Proof.RsaPkcs1Sig.wordsAt_frame' hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kR.sub_left below16).symm)
        (by show (arg s 13).toNat * 8 ≤ 2 ^ 64; have := (arg s 13).isLt; omega_arith) }
  rw [ep_lay]
  refine ok_entered (S := 1188) rfl (by decide) hsp (by simp) (by simp; omega_arith) hrd
    (by rw [hwr]; rfl) ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [kN, kE, kM, kP, kR, kO, kS]
  · intro r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rO, rS]
  · intro w hw r hr
    simp only [EP.rw, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [EP.ro, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [oN, oE, oM, oP, oR, oA, nS.symm, eS.symm, mS.symm, pS.symm, sR, sA]
  · exact List.pairwise_pair.mpr oS
  · intro r hr
    simp only [EP.ro, EP.rw, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [ep, BitVec.toNat_setWidth]
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 2).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 4).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 6).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 8).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 12).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega_arith)]; omega_arith)
      | (rw [Nat.mod_eq_of_lt (by have := (arg s 10).isLt; omega_arith)]; omega_arith)
  · intro j hj
    have : j < 14 := hj
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep, a1]

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: building `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcVerified.lean`): the mask of a zero
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

theorem zm_snoc (bs : List Byte) (b : Byte) :
    zm (bs ++ [b]) = zm bs |||
      (if decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]
  have hb : (b.toNat < 1) = (b = 0) := by
    apply propext; constructor
    · intro h; exact BitVec.eq_of_toNat_eq (by simp; omega_using [h])
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
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.length_append, Proof.RsaPkcs1Sig.bytesAt_len]; simp; omega_using []

theorem enc_getD_ps (P : EP) (σ : State) {i : Nat} (hi : i < P.pl) :
    (enc P σ).getD (2 + i) 0 = σ.mem (P.ps.setWidth 64 + BitVec.ofNat 64 i) := by
  simp only [enc, Spec.RsaPkcs1Enc.encode, List.append_assoc]
  rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp),
    Proof.RsaPkcs1Sig.getD_append_left _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega_using [hi])]
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
  rw [Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp; omega_using []),
    Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega_using []),
    Proof.RsaPkcs1Sig.getD_append_right _ _ _ (by simp [Proof.RsaPkcs1Sig.bytesAt_len]; omega_using [])]
  simp only [List.length_cons, List.length_nil, Proof.RsaPkcs1Sig.bytesAt_len]
  rw [show 3 + P.pl + i - (0 + 1 + 1) - P.pl - (0 + 1) = i by omega_using []]
  exact Proof.RsaPkcs1Sig.bytesAt_getD hi 0

/-- `EM`'s first `n` bytes written. -/
def EMok (P : EP) (σ s : State) (n : Nat) : Prop :=
  ∀ i < n, s.mem (P.lay.fr (oEM + i)) = (enc P σ).getD i 0

/-! ## Stores of bytes into `EM` -/

theorem em_ne (P : EP) {i j : Nat} (hij : i ≠ j) (hi : oEM + i < 2 ^ 64) (hj : oEM + j < 2 ^ 64) :
    P.lay.fr (oEM + i) ≠ P.lay.fr (oEM + j) :=
  Offset.add_ofNat_ne _ hi hj (by omega_using [hij])

/-- `EMok` after a byte stored at index `n`. -/
theorem EMok.store {P : EP} {σ s : State} {n : Nat} (h : EMok P σ s n) {m : Mem} (hn : n < 1024)
    (hm : m = s.mem.writeW (P.lay.fr (oEM + n)) ((enc P σ).getD n 0)) :
    ∀ i < n + 1, m (P.lay.fr (oEM + i)) = (enc P σ).getD i 0 := by
  intro i hi
  subst hm
  rw [WriteBytes.writeW8_apply]
  by_cases e : i = n
  · subst e; simp
  · simp only [em_ne P e (by simp only [oEM]; omega_using [hn, hi]) (by simp only [oEM]; omega_using [hn]), ↓reduceIte]
    exact h i (by omega_using [hi, e])

theorem EMok.zero {P : EP} {σ s : State} : EMok P σ s 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem EMok.mono {P : EP} {σ s : State} {n m : Nat} (h : EMok P σ s n) (hm : m ≤ n) : EMok P σ s m :=
  fun i hi => h i (by omega_using [hm, hi])

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
  have hF : oEM + n + 1 ≤ P.lay.F := by show oEM + n + 1 ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hn, hk]
  refine wp_store8 (a := P.lay.fr (oEM + n)) ?_ (hs.2.inFr hF)
    fun t u => k t ⟨hs.1, hs.2.frameW hF ?_ u.rd u.wr (by rw [u.gpr])⟩ u.gpr u.mem
  · have hd : oEM + n < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, oEM, frameBytes] at hF ⊢; omega_using [hF]
    rw [ea_at, addr, hb]
    exact hs.2.ok.addrB hd
  · rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_using []

theorem bytesAt_succ (m : Mem) (p : Addr) (j : Nat) :
    Spec.Rsa.bytesAt m p (j + 1) = Spec.Rsa.bytesAt m p j ++ [m (p + BitVec.ofNat 64 j)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ]

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end

/-! ### `RsaPkcs1Enc.X86.PcBody`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.PcMask`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.PcCall`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86.PcPieces`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcPieces.lean`): `0x00 ‖ 0x02`
(`head_vp`), `PS` copied with the mask of a zero byte (`psLoop_vp`), the
separator and the mask to its slot (`sep_vp`), and `M` (`msgCopy_vp`):
`EM`, in the frame (`G6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- `PS` with `k` of its bytes left: `EM`'s first `2 + (pl - k)` bytes. -/
def PsI (P : EP) (k : Nat) (σ s : State) : Prop :=
  S P σ s ∧ k ≤ P.pl ∧ s.gpr .edi = P.B + BitVec.ofNat 32 (oEM + (2 + (P.pl - k))) ∧
    s.gpr .esi = P.ps + BitVec.ofNat 32 (P.pl - k) ∧ s.gpr .ecx = BitVec.ofNat 32 k ∧
    s.gpr .ebx = zm (Spec.Rsa.bytesAt σ.mem (P.ps.setWidth 64) (P.pl - k)) ∧ EMok P σ s (2 + (P.pl - k))

/-- The zero mask in its slot. -/
abbrev Zs (P : EP) (σ s : State) : Prop := s.mem.readW (P.lay.fr oZ) 32 = zm (psB P σ)

/-- Before `M`, and whether it is empty. -/
def G5 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .ebx = P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) ∧ s.gpr .esi = P.msg ∧
    s.gpr .ecx = BitVec.ofNat 32 P.ml ∧ Zs P σ s ∧ EMok P σ s (3 + P.pl) ∧ s.zf = some (decide (P.ml = 0))

/-- `EM` written. -/
def G6 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ EMok P σ s P.K

theorem off_add (B : BitVec 32) (a b c : Nat) (h : a + b = c) :
    B + BitVec.ofNat 32 a + BitVec.ofNat 32 b = B + BitVec.ofNat 32 c := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, h]

theorem sp_agree {F : State → State → Prop} (hF : ∀ σ s, F σ s → S P σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp], s₁.gpr r = s₂.gpr r := fun _ _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hF _ _ h₁).2.sp, (hF _ _ h₂).2.sp]

theorem head_vp : VP (S P) (.block head) (PsI P P.pl) :=
  VP.taint [.esp] head_taint (sp_agree fun _ _ h => h) fun σ s hs => by
    have hk := hs.1.k64
    simp only [head]
    refine wp_mov fun t1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    obtain s2 : S P σ t2 := ⟨hs.1, (hs.2.upd u1 (by decide)).upd u2 (by decide)⟩
    obtain di2 : t2.gpr .edi = P.B + BitVec.ofNat 32 oEM := by rw [u2.gpr, u1.gpr, hs.2.sp]
    refine s2.2.wp_arg (j := 8) (r := .esi) (by simp) (by decide) fun t3 st3 u3 => ?_
    refine st3.wp_arg (j := 9) (r := .ecx) (by simp) (by decide) fun t4 st4 u4 => ?_
    refine wp_movi fun t5 u5 => ?_
    obtain s5 : S P σ t5 := ⟨hs.1, st4.upd u5 (by decide)⟩
    obtain di5 : t5.gpr .edi = P.B + BitVec.ofNat 32 oEM := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), di2]
    refine wp_st8EM s5 (off := 0) (n := 0) (by omega_arith) (by rw [di5]; exact off_add _ _ _ _ rfl) fun t6 s6 g6 m6 => ?_
    refine wp_movi fun t7 u7 => ?_
    obtain s7 : S P σ t7 := ⟨hs.1, s6.2.upd u7 (by decide)⟩
    refine wp_st8EM s7 (off := 1) (n := 1) (by omega_arith)
      (by rw [u7.other _ (by decide), g6, di5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]) fun t8 s8 g8 m8 => ?_
    refine wp_addi fun t9 u9 => ?_
    refine wp_movi fun t10 u10 => WP.block_nil ?_
    obtain st10 := (s8.2.upd u9 (by decide)).upd u10 (by decide)
    refine ⟨⟨hs.1, st10⟩, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u10.other _ (by decide), u9.gpr, g8, u7.other _ (by decide), g6, di5, Nat.sub_self]
      exact off_add _ _ _ _ rfl
    · rw [u10.other _ (by decide), u9.other _ (by decide), g8, u7.other _ (by decide), g6,
        u5.other _ (by decide), u4.other _ (by decide), u3.gpr, Nat.sub_self]; simp
    · rw [u10.other _ (by decide), u9.other _ (by decide), g8, u7.other _ (by decide), g6,
        u5.other _ (by decide), u4.gpr]; rfl
    · rw [u10.gpr, Nat.sub_self]; rfl
    · rw [Nat.sub_self]
      obtain e6 := EMok.store (EMok.zero (P := P) (σ := σ) (s := t5)) (by decide) (m := t6.mem)
        (by rw [m6, show Reg8.al.reg = .eax from rfl, u5.gpr]; rfl)
      obtain e8 := EMok.store (n := 1) (s := t7) (fun i hi => by rw [u7.mem]; exact e6 i hi) (by decide)
        (m := t8.mem) (by rw [m8, show Reg8.al.reg = .eax from rfl, u7.gpr]; rfl)
      intro i hi
      rw [u10.mem, u9.mem]
      exact e8 i hi

/-- One byte of `PS`, `n + 1` of them left. -/
theorem psBody_vp (n : Nat) : VP (PsI P (n + 1)) (.block psBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → PsI P 0 σ s) ∧ (0 < n → PsI P n σ s) := by
  refine VP.taint [.esi, .edi, .ecx] psBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  obtain ⟨hs, hk, di, si, cx, bx, em⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  obtain hfp := hs.1.ok.fits P.PS (by simp)
  simp only [BitVec.toNat_setWidth] at hfp
  rw [Nat.mod_eq_of_lt (by have := P.ps.isLt; omega_arith)] at hfp
  obtain hbyte : s.mem (P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1))) =
      σ.mem (P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1))) := by
    have := congrArg (fun l => l.getD (P.pl - (n + 1)) 0) (hs.2.ro (R := P.PS) (by simp))
    simp only at this
    rwa [Proof.RsaPkcs1Sig.bytesAt_getD (by omega_arith), Proof.RsaPkcs1Sig.bytesAt_getD (by omega_arith)] at this
  simp only [psBody]
  refine wp_movzx8 (a := P.ps.setWidth 64 + BitVec.ofNat 64 (P.pl - (n + 1)))
    (by show s.ea ⟨.esi, 0⟩ = _
        rw [ea_at, si, addr, BitVec.add_zero]; exact addr_eq (by omega_arith))
    ⟨P.PS, hs.2.inRo (by simp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  obtain s1 : S P σ t1 := ⟨hs.1, hs.2.upd u1 (by decide)⟩
  refine wp_st8EM s1 (off := 0) (n := 2 + (P.pl - (n + 1))) (by omega_arith)
    (by rw [u1.other _ (by decide), di, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_subi fun t3 u3 c3 _ => ?_
  refine wp_sbb_self c3 fun t4 u4 => ?_
  refine wp_or fun t5 u5 => ?_
  refine wp_addi fun t6 u6 => ?_
  refine wp_addi fun t7 u7 => ?_
  refine wp_subi fun t8 u8 _ z8 => WP.block_nil ?_
  obtain st8 := ((((((s2.2.upd u3 (by decide)).upd u4 (by decide)).upd u5 (by decide)).upd u6 (by decide)).upd
    u7 (by decide)).upd u8 (by decide))
  obtain cx7 : t7.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other]
    rw [g2, u1.other _ (by decide), cx]
  obtain inv : PsI P n σ t8 := by
    refine ⟨⟨hs.1, st8⟩, by omega_arith, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u8.other, u7.gpr, u6.other, u5.other, u4.other, u3.other]
      rw [g2, u1.other _ (by decide), di]
      exact off_add _ _ 1 _ (by omega_arith)
    · simp (disch := decide) only [u8.other, u7.other, u6.gpr, u5.other, u4.other, u3.other]
      rw [g2, u1.other _ (by decide), si]
      exact off_add _ _ 1 _ (by omega_arith)
    · rw [u8.gpr, cx7]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_arith)
    · simp (disch := decide) only [u8.other, u7.other, u6.other, u5.gpr, u4.gpr, u3.other, u4.other]
      simp only [g2]
      rw [u1.other _ (by decide), bx, u1.gpr, hbyte,
        show P.pl - n = P.pl - (n + 1) + 1 by omega_arith, bytesAt_succ, zm_snoc]
    · rw [show 2 + (P.pl - n) = 2 + (P.pl - (n + 1)) + 1 by omega_arith]
      obtain e := EMok.store em (by omega_arith) (m := t2.mem) (by
        rw [m2, show Reg8.al.reg = .eax from rfl, u1.gpr, u1.mem, setWidth_byte, hbyte,
          enc_getD_ps P σ (by omega_arith)])
      intro i hi
      rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem]
      exact e i hi
  refine ⟨?_, fun h0 => h0 ▸ inv, fun _ => inv⟩
  show eval .ne t8 = _
  rw [cx7, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
    Offset.ofNat_sub_ofNat (d := 1) (by omega_arith)] at z8
  have : (BitVec.ofNat 32 n == 0) = decide (n = 0) := by
    by_cases h0 : n = 0
    · subst h0; rfl
    · have : BitVec.ofNat 32 n ≠ 0 := fun e => h0 (by
        have := congrArg BitVec.toNat e; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this; exact this)
      rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h0]
  rw [this] at z8
  simp only [eval, z8]
  by_cases h0 : n = 0 <;> simp [h0] <;> omega_arith

theorem psLoop_vp : VP (PsI P P.pl) psLoop (PsI P 0) := by
  refine (VP.loop (I := fun m => PsI P m) psBody_vp (P.pl - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have := h.1.1.pl8
  rw [show P.pl - 1 + 1 = P.pl by omega_arith]; exact h

theorem sep_wp {σ s : State} (h : PsI P 0 σ s) : WP isa (.block sep) s (G5 P σ) := by
  obtain ⟨hs, -, di, -, -, bx, em⟩ := h
  have hpl := hs.1.em_len
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  rw [Nat.sub_zero] at di bx em
  simp only [sep]
  refine wp_movi fun t1 u1 => ?_
  obtain s1 : S P σ t1 := ⟨hs.1, hs.2.upd u1 (by decide)⟩
  refine wp_st8EM s1 (off := 0) (n := 2 + P.pl) (by omega_arith)
    (by rw [u1.other _ (by decide), di, BitVec.add_zero]) fun t2 s2 g2 m2 => ?_
  refine wp_addi fun t3 u3 => ?_
  obtain s3 : P.lay.St σ t3 := s2.2.upd u3 (by decide)
  refine s3.wp_strFr (d := oZ) (by show oZ + 4 ≤ frameBytes; decide) fun t4 s4 m4 => ?_
  refine wp_mov fun t5 u5 => ?_
  obtain s5 := s4.upd u5 (by decide)
  refine s5.wp_arg (j := 6) (r := .esi) (by simp) (by decide) fun t6 s6 u6 => ?_
  refine s6.wp_arg (j := 7) (r := .ecx) (by simp) (by decide) fun t7 s7 u7 => ?_
  refine wp_cmpi fun t8 u8 _ z8 => WP.block_nil ?_
  obtain s8 := s7.fupd u8
  obtain mm : t8.mem = t3.mem.writeW (P.lay.fr oZ) (t3.gpr .ebx) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4.mem]
  obtain em3 : EMok P σ t3 (3 + P.pl) := by
    obtain e := EMok.store (em.of_mem u1.mem) (by omega_arith) (m := t2.mem) (by
      rw [m2, show Reg8.al.reg = .eax from rfl, u1.gpr, enc_getD_sep]; rfl)
    intro i hi
    rw [u3.mem]
    exact e i (by omega_arith)
  refine ⟨⟨hs.1, s8⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u8.gpr, u7.other _ (by decide), u6.other _ (by decide), u5.gpr, m4.gpr, u3.gpr, g2,
      u1.other _ (by decide), di]
    exact off_add _ _ 1 _ (by omega_arith)
  · rw [u8.gpr, u7.other _ (by decide), u6.gpr]; rfl
  · rw [u8.gpr, u7.gpr]; rfl
  · rw [Zs, mm, Mem.readW_writeW_self32, u3.other _ (by decide), g2, u1.other _ (by decide), bx]
  · refine EMok.frame em3 (rs := [⟨P.lay.fr oZ, 4⟩]) ?_ fun i hi r hr => ?_
    · rw [mm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oZ]; omega_arith)
  · rw [z8, u7.gpr]
    simp only [EP.argv, List.getD_cons_succ, List.getD_cons_zero]
    obtain e := ofNat_beq_zero (k := P.ml) (by omega_arith)
    exact congrArg some ((congrArg (· == (0 : BitVec 32)) (BitVec.sub_zero (BitVec.ofNat 32 P.ml))).trans e)

theorem sep_vp : VP (PsI P 0) (.block sep) (G5 P) :=
  VP.taint [.esp, .edi] sep_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.2.sp, h₂.1.2.sp]
      · rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => sep_wp h

theorem copy_wp {σ s : State} (h : G5 P σ s) (h0 : P.ml ≠ 0) :
    WP isa Impl.Bignum.X86.copyBytes s (G6 P σ) := by
  obtain ⟨hs, bx, si, cx, zs, em, -⟩ := h
  have hK := hs.1.k1024
  have hpl := hs.1.em_len
  obtain hfm := hs.1.ok.fits P.MSG (by simp)
  simp only [BitVec.toNat_setWidth] at hfm
  rw [Nat.mod_eq_of_lt (by have := P.msg.isLt; omega_arith)] at hfm
  have hfit := hs.2.ok.fit
  obtain hF : oEM + (3 + P.pl) + P.ml ≤ P.lay.F := by
    show _ ≤ frameBytes; simp only [oEM, frameBytes]; omega_arith
  have hA : P.lay.F + 20 + P.lay.A = frameBytes + 20 + 56 := rfl
  obtain hb : P.B.toNat + (frameBytes + 20 + 56) ≤ 2 ^ 32 := by rw [← hA]; omega_arith
  obtain hoff : oEM + (3 + P.pl) < 2 ^ 32 := by simp only [oEM]; omega_arith
  obtain hdn : (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))).toNat = P.B.toNat + (oEM + (3 + P.pl)) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
    exact Nat.mod_eq_of_lt (by simp only [oEM, frameBytes] at hb ⊢; omega_arith)
  obtain hdj : ∀ j ≤ P.ml, Proof.Bignum.X86.byteAddr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl)) + BitVec.ofNat 32 j) =
      P.lay.fr (oEM + (3 + P.pl) + j) := fun j hj => by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact hs.2.ok.addrB (by rw [hA]; simp only [oEM, frameBytes]; omega_arith)
  obtain hdst : Proof.Bignum.X86.byteAddr (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) =
      P.lay.fr (oEM + (3 + P.pl)) := by
    have := hdj 0 (Nat.zero_le _); rwa [BitVec.add_zero, Nat.add_zero] at this
  obtain ctx := Proof.Bignum.X86.copyCtx_of_regions s P.msg (P.B + BitVec.ofNat 32 (oEM + (3 + P.pl))) (n := P.ml)
    (by omega_arith) hfm (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
    ⟨P.MSG, hs.2.inRo (by simp), Region.contains_self _ _⟩
    (by rw [hdst]; exact hs.2.inFr hF)
    (by rw [hdst]; exact (hs.2.ok.stk_fr (R := P.MSG) (Or.inl (by simp))
      (by show _ ≤ frameBytes + 16; simp only [oEM, frameBytes]; omega_arith)).symm)
  refine WP.mono (Proof.Bignum.X86.copyBytes_ok s ctx (Nat.pos_of_ne_zero h0) si bx cx) fun t ht => ?_
  obtain fr := ht.frame (by rw [hdn]; simp only [oEM, frameBytes] at hb ⊢; omega_arith)
  rw [hdst] at fr
  obtain st : P.lay.St σ t := hs.2.frameW hF fr ht.rest.2.1 ht.rest.2.2 (ht.rest.1 .esp (by decide))
  refine ⟨⟨hs.1, st⟩, ?_, fun i hi => ?_⟩
  · rw [Zs, fr.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM, oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by simp only [oEM]; omega_arith))
      (by decide)]
    exact zs
  · rcases (by omega_arith : i < 3 + P.pl ∨ 3 + P.pl ≤ i) with hi' | hi'
    · rw [frame_byte1 fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.fr_sep (by omega_arith) (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith))]
      exact em i hi'
    · obtain ⟨j, rfl⟩ : ∃ j, i = 3 + P.pl + j := ⟨i - (3 + P.pl), by omega_arith⟩
      obtain hj : j < P.ml := by omega_arith
      rw [show oEM + (3 + P.pl + j) = oEM + (3 + P.pl) + j by omega_arith, ← hdj j (Nat.le_of_lt hj), ht.copied j hj,
        enc_getD_msg P σ hj]
      have := congrArg (fun l => l.getD j 0) (hs.2.ro (R := P.MSG) (by simp))
      simp only at this
      rw [Proof.RsaPkcs1Sig.bytesAt_getD hj, Proof.RsaPkcs1Sig.bytesAt_getD hj] at this
      simp only [Proof.Bignum.X86.byteAddr]
      rw [show (P.msg + BitVec.ofNat 32 j).setWidth 64 = P.msg.setWidth 64 + BitVec.ofNat 64 j from
        addr_eq (by omega_arith)]
      exact this

theorem msgCopy_vp : VP (G5 P) msgCopy (G6 P) := by
  refine VP.ite (fun _ _ h => ⟨_, h.2.2.2.2.2.2⟩) (fun _ _ _ _ h₁ h₂ => by
      show _ = _; simp only [eval]; rw [h₁.2.2.2.2.2.2, h₂.2.2.2.2.2.2])
    (VP.block_nil fun σ s ⟨h, he⟩ => ?_)
    (VP.taint [.esi, .ebx, .ecx] copy_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1.2.2.1, h₂.1.2.2.1]
      · rw [h₁.1.2.1, h₂.1.2.1]
      · rw [h₁.1.2.2.2.1, h₂.1.2.2.2.1]) fun σ s ⟨h, he⟩ => copy_wp h fun h0 => by
        have := h.2.2.2.2.2.2; simp only [eval] at he; rw [he, h0] at this; simp at this)
  obtain ⟨hs, -, -, -, zs, em, z⟩ := h
  simp only [eval] at he
  rw [he] at z
  obtain h0 : P.ml = 0 := by simpa using z.symm
  exact ⟨hs, zs, em.mono (by have := hs.1.em_len; omega_arith)⟩

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the call

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcCall.lean`): the call's ten
arguments at the frame's base (`Slots`, `callArgs_wp`), and the call of
`vg_rsa_public_precomputed_checked` (`call_vp`, correct and constant time:
its arguments and the public data it reads are the same in two runs), which
writes `EM^e mod n` or zeros to `out` (`CR`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The call's arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  pubArgv P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.rl P.el P.sl

/-- The first `k` of them in place. -/
def Slots (P : EP) (m : Mem) (k : Nat) : Prop :=
  ∀ i < k, m.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def G7 (P : EP) (σ s : State) : Prop := G6 P σ s ∧ Slots P s.mem 10

/-- What the call writes and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r (Spec.Rsa.publicOpChecked nB P.eB (enc P σ))

/-- After the call. -/
def G8 (P : EP) (σ s : State) : Prop := S P σ s ∧ Zs P σ s ∧ CR P σ s.mem (s.gpr .eax)

theorem G6.upd {σ s t : State} (h : G6 P σ s) {d : Reg} {v : BitVec 32} (u : Upd s t d v) (hd : d ≠ .esp) :
    G6 P σ t :=
  ⟨⟨h.1.1, h.1.2.upd u hd⟩, by rw [Zs, u.mem]; exact h.2.1, h.2.2.of_mem u.mem⟩

/-- `mov [esp + 4 i], eax`: the call's argument `i`. -/
theorem slotStore {σ s : State} {i : Nat} (h : G6 P σ s) (hs : Slots P s.mem i) (hi : i < 10)
    (hv : s.gpr .eax = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, G6 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (.store (Impl.RsaPkcs1Sig.X86.stk (4 * i)) .eax :: is)) s Q := by
  have hK := h.1.1.k1024
  refine h.1.2.wp_strFr (d := 4 * i) (by show 4 * i + 4 ≤ frameBytes; simp only [frameBytes]; omega_arith)
    fun t s2 m2 => kk t ⟨⟨h.1.1, s2⟩, ?_, ?_⟩ ?_
  · rw [Zs, m2.mem, Lay.readW_fr_other _ _ _ (by simp only [oZ]; omega_arith) (by simp only [oZ]; omega_arith) (by omega_arith)]
    exact h.2.1
  · refine EMok.frame h.2.2 (rs := [⟨P.lay.fr (4 * i), 4⟩]) ?_ fun k hk r hr => ?_
    · rw [m2.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Lay.fr_sep (by simp only [oEM]; omega_arith) (by simp only [oEM]; omega_arith) (by omega_arith)
  · intro k hk
    rw [m2.mem]
    rcases (by omega_arith : k = i ∨ k < i) with rfl | hki
    · rw [Mem.readW_writeW_self32, hv]
    · rw [Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hs k hki

/-- `mov eax, [arg j]; mov [esp + 4 i], eax`: argument `j` to the call's argument `i`. -/
theorem copySlot {σ s : State} {i j : Nat} (h : G6 P σ s) (hs : Slots P s.mem i) (hi : i < 10)
    (hj : j < 14) (hv : P.argv.getD j 0 = (outv P).getD i 0) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, G6 P σ t → Slots P t.mem (i + 1) → WP isa (.block is) t Q) :
    WP isa (.block (copyArg j i ++ is)) s Q :=
  h.1.2.wp_arg (j := j) (by simp only [EP.argv, List.length_cons, List.length_nil]; omega_arith) (by decide)
    fun t1 _ u1 => slotStore (h.upd u1 (by decide)) (fun k hk => by rw [u1.mem]; exact hs k hk) hi
      (by rw [u1.gpr, hv]) kk

theorem callArgs_wp {σ s : State} (h : G6 P σ s) : WP isa (.block callArgs) s (G7 P σ) := by
  simp only [callArgs, List.append_assoc, List.cons_append, List.nil_append]
  obtain z0 : Slots P s.mem 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)
  refine copySlot h z0 (by decide) (j := 0) (by decide) rfl fun t1 h1 z1 => ?_
  refine copySlot h1 z1 (by decide) (j := 3) (by decide) rfl fun t2 h2 z2 => ?_
  refine copySlot h2 z2 (by decide) (j := 12) (by decide) rfl fun t3 h3 z3 => ?_
  refine copySlot h3 z3 (by decide) (j := 13) (by decide) rfl fun t4 h4 z4 => ?_
  refine copySlot h4 z4 (by decide) (j := 4) (by decide) rfl fun t5 h5 z5 => ?_
  refine copySlot h5 z5 (by decide) (j := 5) (by decide) rfl fun t6 h6 z6 => ?_
  refine wp_mov fun t7 u7 => wp_addi fun t8 u8 => ?_
  obtain h8 := (h6.upd u7 (by decide)).upd u8 (by decide)
  refine slotStore (i := 6) h8 (fun k hk => by rw [u8.mem, u7.mem]; exact z6 k hk) (by decide)
    (by rw [u8.gpr, u7.gpr, h6.1.2.sp]; rfl) fun t9 h9 z9 => ?_
  refine copySlot h9 z9 (by decide) (j := 3) (by decide) rfl fun t10 h10 z10 => ?_
  refine copySlot h10 z10 (by decide) (j := 10) (by decide) rfl fun t11 h11 z11 => ?_
  refine copySlot h11 z11 (by decide) (j := 11) (by decide) rfl fun t12 h12 z12 => ?_
  exact WP.block_nil ⟨h12, z12⟩

theorem In.fit {σ : State} (h : In P σ) : P.B.toNat + frameBytes + 76 ≤ 2 ^ 32 := by
  have := h.ok.fit
  simp only [Lay.A, EP.argv, List.length_cons, List.length_nil] at this
  omega_arith

theorem In.BC {σ : State} (h : In P σ) : 100 ≤ P.B.toNat := h.ok.BC

/-- `EM`, as the call reads it. -/
theorem In.emA {σ : State} (h : In P σ) : (P.B + BitVec.ofNat 32 oEM).setWidth 64 = P.lay.fr oEM :=
  h.ok.addrB (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, oEM, frameBytes]; omega_arith)

/-- The call's arguments, at the frame's base. -/
theorem argsA (P : EP) : (⟨P.B.setWidth 64, 40⟩ : Region) = ⟨P.lay.fr 0, 40⟩ := by
  simp

theorem G7.pubArgs {σ s : State} (h : G7 P σ s) :
    PubArgs s P.out P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.scr P.K P.rl P.el P.sl := by
  obtain ⟨⟨hs, -, -⟩, sl⟩ := h
  have fit := hs.1.fit
  refine ⟨fun i hi => ?_, ?_, ?_, hs.1.kv, hs.1.rlK, hs.1.el1, hs.1.elK, hs.1.slK, hs.1.sl32⟩
  · have hd : 4 * i < P.lay.F + 20 + P.lay.A := by
      simp only [Lay.A, EP.argv, List.length_cons, List.length_nil, frameBytes] at fit ⊢; omega_arith
    rw [hs.2.sp, hs.1.ok.addrB hd]
    exact sl i hi
  · rw [show s.gpr .esp = P.B from hs.2.sp]; exact hs.1.BC
  · rw [show s.gpr .esp = P.B from hs.2.sp]; simp only [frameBytes] at fit; omega_arith

theorem S.eB {σ s : State} (hs : S P σ s) : Spec.Rsa.bytesAt s.mem (P.e.setWidth 64) P.el = P.eB :=
  (hs.2.ro (R := P.E) (by simp)).trans hs.1.eB

/-- `pre`'s words, in a state of the body. -/
theorem S.pw {σ s : State} (hs : S P σ s) : Spec.Rsa.wordsAt s.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hs.1.ok
  obtain hR : P.PRE ∈ P.lay.ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' hs.2.frame (fun r hr => ?_) (by omega_arith)).trans hs.1.pw
  simp only [Lay.W, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    false_or] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.FR_stk).symm
  · exact (ok.wro P.OUT (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact (ok.wro P.SCR (by simp) P.PRE (List.mem_append_left _ hR)).symm
  · exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

/-- `pre`'s words, in a callee's entry state. -/
theorem S.callPw {σ s : State} (hs : S P σ s) :
    Spec.Rsa.wordsAt s.callEntry.mem (P.pre.setWidth 64) P.rl = P.pw := by
  have ok := hs.1.ok
  obtain hR : P.PRE ∈ P.lay.ro := by simp
  obtain hf : (P.pre.setWidth 64).toNat + P.rl * 8 ≤ 2 ^ 32 := ok.fits P.PRE (List.mem_append_left _ hR)
  refine (Proof.RsaPkcs1Sig.wordsAt_frame' (hs.2.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
    (by omega_arith)).trans hs.pw
  simp only [List.mem_singleton] at hr; subst hr
  exact ((ok.stk P.PRE (List.mem_append_left _ hR)).sub_left Lay.low_stk).symm

theorem EMok.bytes {σ s : State} (h : EMok P σ s P.K) (hK : P.pl + P.ml + 3 = P.K) :
    Spec.Rsa.bytesAt s.mem (P.lay.fr oEM) P.K = enc P σ := by
  obtain hl := enc_length P σ
  rw [show P.K = (enc P σ).length by omega_arith]
  exact Proof.RsaPkcs1Sig.bytesAt_eq fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]; exact h i (by omega_arith)

theorem call_vp (c : Ver.PublicImpl) : VP (G7 P) (.call c.name c.code) (G8 P) := by
  refine VP.call c.verified.1 c.verified.2.1 c.noSp
    (pubRd P.pre P.e (P.B + BitVec.ofNat 32 oEM) P.K P.rl P.el) (pubWr P.B P.out P.scr P.K P.sl)
    (fun σ s h => ?_) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_)
    (fun σ s s' h rd wr cs fr po => ?_)
  · -- The callee's precondition.
    have hs := h.1.1
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have fit := hs.1.fit
    have hsp : s.gpr .esp = P.B := hs.2.sp
    have em := hs.1.emA
    obtain ar := argsA P
    have := pub_pre h.pubArgs ?_ ?_ ?_ ?_
    · rw [hsp] at this; exact this
    all_goals rw [hsp]
    · intro w hw r hr
      simp only [pubWr, pubRd, List.mem_cons, List.not_mem_nil, or_false] at hw hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.PRE) (by simp)
      · exact ok.rw_ro (w := P.OUT) (by simp) (r := P.E) (by simp)
      · rw [em]; exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.PRE) (by simp)
      · exact ok.rw_ro (w := P.SCR) (by simp) (r := P.E) (by simp)
      · rw [em]; exact (ok.stk_fr (R := P.SCR) (.inr (by simp)) (by simp only [oEM, frameBytes]; omega_arith)).symm
      · rw [ar]; exact ok.stk_fr (R := P.PRE) (.inl (by simp)) (by simp only [frameBytes]; omega_arith)
      · rw [ar]; exact ok.stk_fr (R := P.E) (.inl (by simp)) (by simp only [frameBytes]; omega_arith)
      · rw [ar, em]; exact Lay.fr_sep (by simp only [oEM]; omega_arith) (by omega_arith) (by simp only [oEM]; omega_arith)
    · simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, List.Pairwise.nil, and_true]
      have ww := ok.wrw
      simp only [EP.rw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq] at ww
      refine ⟨⟨ww.1, ?_⟩, ?_⟩
      · rw [ar]; exact (ok.stk_fr (R := P.OUT) (d := 0) (n := 40) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega_arith)).symm
      · rw [ar]; exact ⟨(ok.stk_fr (R := P.SCR) (d := 0) (n := 40) (.inr (by simp))
          (by show _ ≤ frameBytes + 16; simp only [frameBytes]; omega_arith)).symm, fun _ h => h.elim⟩
    · intro r hr
      rw [show below P.B 100 = P.lay.LOW from ok.low_eq]
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.low_buf (R := P.OUT) (.inr (by simp))
      · exact ok.low_buf (R := P.SCR) (.inr (by simp))
      · rw [ar]; exact (Lay.fr_low (by omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm
      · exact ok.low_buf (R := P.PRE) (.inl (by simp))
      · exact ok.low_buf (R := P.E) (.inl (by simp))
      · rw [em]; exact (Lay.fr_low (by simp only [oEM]; omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)).symm
    · intro r hr
      simp only [pubWr, pubRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      obtain hfr : ∀ d, d ≤ frameBytes → (P.lay.fr d).toNat = P.B.toNat + d := fun d hd =>
        Lay.fr_toNat (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil] at fit ⊢; omega_arith)
          (by simp only [Lay.A, EP.argv, List.length_cons, List.length_nil]; omega_arith)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ok.fits P.OUT (by simp)
      · exact ok.fits P.SCR (by simp)
      · rw [ar]; show (P.lay.fr 0).toNat + 40 ≤ _; rw [hfr 0 (by decide)]; simp only [frameBytes] at fit; omega_arith
      · exact ok.fits P.PRE (by simp)
      · exact ok.fits P.E (by simp)
      · rw [em]; show (P.lay.fr oEM).toNat + P.K ≤ _
        rw [hfr oEM (by decide)]; simp only [oEM, frameBytes] at fit ⊢; omega_arith
  · -- What the callee is given is ours.
    have hs := h.1.1
    have hK := hs.1.k1024
    have em := hs.1.emA
    obtain ar := argsA P
    obtain hro : ∀ R ∈ P.lay.ro, Covers [R] (s.rd ++ s.wr) := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRo hR
    obtain hrw : ∀ R ∈ P.lay.rw, Covers [R] s.wr := fun R hR =>
      Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs.2.inRw hR
    obtain hA : Covers [⟨P.B.setWidth 64, 40⟩] s.wr := by
      rw [ar]; exact Covers.one (hs.2.inFr (by simp only [frameBytes]; omega_arith))
    obtain hE : Covers [⟨(P.B + BitVec.ofNat 32 oEM).setWidth 64, P.K⟩] (s.rd ++ s.wr) := by
      rw [em]; exact Covers.one (hs.2.inFrR (by simp only [oEM, frameBytes]; omega_arith))
    obtain wr : Covers (pubWr P.B P.out P.scr P.K P.sl) s.wr :=
      (hrw P.OUT (by simp)).cons ((hrw P.SCR (by simp)).cons (hA.cons Covers.nil))
    exact ⟨Covers.append_left ((hro P.PRE (by simp)).cons ((hro P.E (by simp)).cons (hE.cons Covers.nil)))
      wr.right, wr⟩
  · rw [show s.gpr .esp = P.B from h.1.1.2.sp]
    have := h.1.1.1.BC
    have := c.stack
    omega_arith
  · refine pub_pub h₁.pubArgs h₂.pubArgs (by rw [h₁.1.1.2.sp, h₂.1.1.2.sp]) ?_ ?_ ?_ ?_ _ _
    · rw [h₁.1.1.pw, h₂.1.1.pw]
    · rw [h₁.1.1.eB, h₂.1.1.eB]
    · rw [h₁.1.1.2.sp, show below P.lay.B 100 = P.lay.LOW from h₁.1.1.1.ok.low_eq]
      exact h₁.1.1.1.ok.low_buf (R := P.PRE) (.inl (by simp))
    · rw [h₁.1.1.2.sp, show below P.lay.B 100 = P.lay.LOW from h₁.1.1.1.ok.low_eq]
      exact h₁.1.1.1.ok.low_buf (R := P.E) (.inl (by simp))
  · -- After the call.
    have hh := h
    obtain ⟨⟨hs, zs, emk⟩, -⟩ := h
    have ok := hs.1.ok
    have hK := hs.1.k1024
    have hpl := hs.1.em_len
    have hsp := hs.2.sp
    obtain ar := argsA P
    obtain low : Region.Sub (below (s.gpr .esp) (stackUse c.code + 4)) P.lay.LOW := by
      rw [hsp, ← ok.low_eq]
      exact below_sub (by have := c.stack; show _ ≤ 100; omega_arith) ok.BC
    obtain hw : ∀ r ∈ pubWr P.B P.out P.scr P.K P.sl ++ [below (s.gpr .esp) (stackUse c.code + 4)],
        ∃ R ∈ P.lay.W, Region.Sub r R := fun r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨P.OUT, by simp, fun _ h => h⟩
      · exact ⟨P.SCR, by simp, fun _ h => h⟩
      · refine ⟨P.lay.FR, by simp, ?_⟩
        rw [ar]; exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)
      · exact ⟨P.lay.LOW, by simp, low⟩
    obtain st : P.lay.St σ s' := hs.2.write fr hw rd wr (cs .esp (by simp [calleeSaved]))
    obtain apart : ∀ {d n : Nat}, 40 ≤ d → d + n ≤ frameBytes →
        ∀ r ∈ pubWr P.B P.out P.scr P.K P.sl ++ [below (s.gpr .esp) (stackUse c.code + 4)],
        Region.Disjoint ⟨P.lay.fr d, n⟩ r := fun h0 hd r hr => by
      simp only [pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 16; omega_arith)
      · exact ok.stk_fr (.inr (by simp)) (by show _ ≤ frameBytes + 16; omega_arith)
      · rw [ar]; exact Lay.fr_sep (by omega_arith) (by simp only [frameBytes] at hd; omega_arith) (by decide)
      · exact (Lay.fr_low (by simp only [frameBytes] at hd; omega_arith)
          (by show (100 : Nat) ≤ 2 ^ 32; decide)).sub_right low
    refine ⟨⟨hs.1, st⟩, ?_, fun nB hn hp => ?_⟩
    · rw [Zs, fr.readW (r := ⟨P.lay.fr oZ, 4⟩) (Region.contains_self _ _)
        (apart (by simp only [oZ]; omega_arith) (by simp only [oZ, frameBytes]; omega_arith)) (by decide)]
      exact zs
    · obtain ⟨s₂, m₂, g₂, po⟩ := po
      have := pub_post hh.pubArgs po nB hn (by rw [hs.callPw]; exact hp)
      rw [m₂, g₂ .eax (by decide)] at this
      obtain eE : Spec.Rsa.bytesAt s.callEntry.mem (P.e.setWidth 64) P.el = P.eB :=
        (hs.2.callEntry_ro (by show 4 ≤ 100; decide) (R := P.E) (by simp)).trans hs.1.eB
      obtain eM : Spec.Rsa.bytesAt s.callEntry.mem ((P.B + BitVec.ofNat 32 oEM).setWidth 64) P.K = enc P σ := by
        rw [hs.1.emA]
        refine (Proof.RsaPkcs1Sig.bytesAt_frame (hs.2.callEntry_frame (by show 4 ≤ 100; decide)) (fun r hr => ?_)
          (by omega_arith)).trans (emk.bytes hpl)
        simp only [List.mem_singleton] at hr; subst hr
        exact Lay.fr_low (by simp only [oEM]; omega_arith) (by show (100 : Nat) ≤ 2 ^ 32; decide)
      rw [eE, eM] at this
      exact this

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the masks

After the call, as on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcCall.lean`): the mask
`keep` (all ones unless `PS` had a zero byte), the result masked with it
(`maskArgs_wp`), `out` masked with it one byte at a time (`maskLoop_vp`),
`EM` overwritten with zeros (`wipeArgs_wp`, `zero_wp`), and the result
returned (`ret_wp`): what the function writes and returns (`Res`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp

variable {P : EP}

/-- The mask of the result: all ones unless `PS` has a zero byte. -/
abbrev keep (P : EP) (σ : State) : BitVec 32 := zm (psB P σ) ^^^ BitVec.allOnes 32

/-- What the function writes and returns. -/
def Res (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  ∀ nB : List Byte, nB.length = P.K → Spec.Rsa.publicPrecompute nB = some P.pw →
    Spec.Rsa.written m (P.out.setWidth 64) P.K r
      (if zm (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none)

/-- `out` with `k` of its bytes left to mask. -/
def MI (P : EP) (k : Nat) (σ s : State) : Prop :=
  S P σ s ∧ k ≤ P.K ∧ s.gpr .esi = P.out + BitVec.ofNat 32 (P.K - k) ∧ s.gpr .ecx = BitVec.ofNat 32 k ∧
    s.gpr .ebx = keep P σ ∧ ∃ m0 rc, CR P σ m0 rc ∧ s.gpr .edi = rc &&& keep P σ ∧
      ∀ i < P.K, s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) =
        if i < P.K - k then m0 (P.out.setWidth 64 + BitVec.ofNat 64 i) &&& (keep P σ).setWidth 8
        else m0 (P.out.setWidth 64 + BitVec.ofNat 64 i)

/-- `out` masked. -/
def G10 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .edi)

/-- Before the wipe of `EM`. -/
def G11 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ Res P σ s.mem (s.gpr .edi) ∧ s.gpr .esi = P.B + BitVec.ofNat 32 oEM ∧
    s.gpr .ecx = BitVec.ofNat 32 P.K ∧ s.gpr .eax = 0

/-- The end of the body. -/
def G13 (P : EP) (σ s : State) : Prop := S P σ s ∧ Res P σ s.mem (s.gpr .eax)

theorem zm_cases (bs : List Byte) : zm bs = 0 ∨ zm bs = BitVec.allOnes 32 := by
  unfold zm; split <;> simp

theorem masked {m m' : Mem} {a : Addr} {K : Nat} {r z : BitVec 32} {o : Option (List Byte)}
    (hz : z = 0 ∨ z = BitVec.allOnes 32) (hw : Spec.Rsa.written m a K r o)
    (hb : Spec.Rsa.bytesAt m' a K = (Spec.Rsa.bytesAt m a K).map (· &&& (z ^^^ BitVec.allOnes 32).setWidth 8)) :
    Spec.Rsa.written m' a K (r &&& (z ^^^ BitVec.allOnes 32)) (if z = 0 then o else none) := by
  rcases hz with rfl | rfl
  · simp only [ite_true]
    have e1 : (0 : BitVec 32) ^^^ BitVec.allOnes 32 = BitVec.allOnes 32 := BitVec.zero_xor
    obtain e8 : (BitVec.allOnes 32).setWidth 8 = BitVec.allOnes 8 := by decide
    obtain hb' : Spec.Rsa.bytesAt m' a K = Spec.Rsa.bytesAt m a K := by
      rw [hb, e1, e8]
      exact (List.map_congr_left (g := id) fun x _ => BitVec.and_allOnes).trans (List.map_id _)
    rw [e1, BitVec.and_allOnes]
    cases o with
    | some y => exact ⟨hw.1, hb'.trans hw.2⟩
    | none => exact ⟨hw.1, hb'.trans hw.2⟩
  · simp only [show BitVec.allOnes 32 = 0 ↔ False by decide, ite_false]
    have e1 : BitVec.allOnes 32 ^^^ BitVec.allOnes 32 = 0 := BitVec.xor_self
    obtain e0 : r &&& (0 : BitVec 32) = 0 := by simp
    rw [e1, e0]
    refine ⟨rfl, ?_⟩
    rw [hb, e1]
    apply List.ext_getElem (by simp [Proof.RsaPkcs1Sig.bytesAt_len])
    intro i h₁ h₂
    simp

theorem maskArgs_wp {σ s : State} (h : G8 P σ s) : WP isa (.block maskArgs) s (MI P P.K σ) := by
  obtain ⟨hs, zs, cr⟩ := h
  simp only [maskArgs]
  refine hs.2.wp_slot (d := oZ) (r := .ebx) (by show oZ + 4 ≤ frameBytes; decide) (by decide) fun t1 s1 u1 => ?_
  refine wp_xorI fun t2 u2 => ?_
  refine wp_mov fun t3 u3 => ?_
  refine wp_and fun t4 u4 => ?_
  obtain s4 : P.lay.St σ t4 := ((s1.upd u2 (by decide)).upd u3 (by decide)).upd u4 (by decide)
  refine s4.wp_arg (j := 0) (r := .esi) (by simp) (by decide) fun t5 s5 u5 => ?_
  refine s5.wp_arg (j := 3) (r := .ecx) (by simp) (by decide) fun t6 s6 u6 => WP.block_nil ?_
  obtain mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain b2 : t2.gpr .ebx = keep P σ := by rw [u2.gpr, u1.gpr, zs]
  refine ⟨⟨hs.1, s6⟩, Nat.le_refl _, ?_, ?_, ?_, s.mem, s.gpr .eax, cr, ?_, fun i _ => ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, Nat.sub_self]; simp
  · rw [u6.gpr]; rfl
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), b2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u3.other _ (by decide), b2,
      u2.other _ (by decide), u1.other _ (by decide)]
  · rw [mm, Nat.sub_self]; simp

theorem maskBody_vp (m : Nat) : VP (MI P (m + 1)) (.block maskBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < m)) ∧ (m = 0 → MI P 0 σ s) ∧ (0 < m → MI P m σ s) := by
  refine VP.taint [.esi, .ecx] maskBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  obtain ⟨hs, hk, si, cx, bx, m0, rc, cr, di, mem⟩ := h
  have hK := hs.1.k1024
  obtain hfo : P.out.toNat + P.K ≤ 2 ^ 32 := by
    have := hs.1.ok.fits P.OUT (by simp)
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega_using [])] at this
  obtain hi : P.K - (m + 1) < P.K := by omega_using [hk]
  obtain ha : ∀ t : State, t.gpr .esi = s.gpr .esi →
      t.ea ⟨.esi, 0⟩ = P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1)) := fun t e => by
    rw [ea_at, e, si, addr, BitVec.add_zero]; exact addr_eq (by omega_using [hfo])
  obtain hc : (P.OUT : Region).Contains (P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1))) 1 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hK])
  simp only [maskBody]
  refine wp_movzx8 (ha s rfl) ⟨P.OUT, List.mem_append_right _ (hs.2.inRw (by simp)), hc⟩ fun t1 u1 => ?_
  refine wp_and fun t2 u2 => ?_
  refine wp_store8 (ha t2 (by rw [u2.other _ (by decide), u1.other _ (by decide)]))
    ⟨P.OUT, by rw [u2.wr, u1.wr]; exact hs.2.inRw (by simp), hc⟩ fun t3 u3 => ?_
  refine wp_addi fun t4 u4 => ?_
  refine wp_subi fun t5 u5 _ z5 => WP.block_nil ?_
  obtain fr : Frame [⟨P.out.setWidth 64 + BitVec.ofNat 64 (P.K - (m + 1)), 1⟩] s.mem t5.mem := by
    rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain st : P.lay.St σ t5 := hs.2.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨P.OUT, by simp, Offset.sub_base _ (by omega_using [hk])⟩)
    (by rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]) (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide)])
  obtain cx4 : t4.gpr .ecx = BitVec.ofNat 32 (m + 1) := by
    rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide), cx]
  obtain inv : MI P m σ t5 := by
    refine ⟨⟨hs.1, st⟩, by omega_using [hk], ?_, ?_, ?_, m0, rc, cr, ?_, fun i hi' => ?_⟩
    · rw [u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide), u1.other _ (by decide), si]
      exact off_add _ _ 1 _ (by omega_using [hk])
    · rw [u5.gpr, cx4]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega_using [])
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), bx]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), di]
    · rw [u5.mem, u4.mem, u3.mem, WriteBytes.writeW8_apply, u2.mem, u1.mem]
      by_cases e : i = P.K - (m + 1)
      · subst e
        obtain hm := mem _ hi
        simp only [Nat.lt_irrefl, ↓reduceIte] at hm
        simp only [show P.K - (m + 1) < P.K - m from by omega_using [hk], ↓reduceIte]
        rw [show Reg8.dl.reg = .edx from rfl, u2.gpr, u1.gpr, u1.other _ (by decide), bx, ← hm,
          BitVec.setWidth_and, setWidth_byte]
      · have hne := Offset.add_ofNat_ne (P.out.setWidth 64) (by omega_using [hK, hi'] : i < 2 ^ 64)
          (by omega_using [hK] : P.K - (m + 1) < 2 ^ 64) e
        simp only [hne, ↓reduceIte]
        rw [mem i hi']
        by_cases h1 : i < P.K - (m + 1)
        · simp only [h1, show i < P.K - m from by omega_using [h1], ↓reduceIte]
        · simp only [h1, show ¬ i < P.K - m from by omega_using [e, h1], ↓reduceIte]
  refine ⟨?_, fun h0 => h0 ▸ inv, fun _ => inv⟩
  show eval .ne t5 = _
  rw [cx4, show BitVec.ofNat 32 (m + 1) - 1 = BitVec.ofNat 32 m from
    Offset.ofNat_sub_ofNat (d := 1) (by omega_using []), ofNat_beq_zero (by omega_using [hk, hK])] at z5
  simp only [eval, z5]
  by_cases h0 : m = 0 <;> simp [h0] <;> omega_using [h0]

theorem maskLoop_vp : VP (MI P P.K) maskLoop (MI P 0) := by
  refine (VP.loop (I := fun m => MI P m) maskBody_vp (P.K - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have := h.1.1.k64
  rw [show P.K - 1 + 1 = P.K by omega_using [this]]; exact h

theorem masked_g10 {σ s : State} (h : MI P 0 σ s) : G10 P σ s := by
  obtain ⟨hs, -, -, -, -, m0, rc, cr, di, mem⟩ := h
  refine ⟨hs, fun nB hn hp => ?_⟩
  rw [di]
  refine masked (zm_cases _) (cr nB hn hp) ?_
  apply List.ext_getElem (by simp [Proof.RsaPkcs1Sig.bytesAt_len])
  intro i h₁ h₂
  simp only [Proof.RsaPkcs1Sig.bytesAt_len] at h₁
  simp only [List.getElem_map, Spec.Rsa.bytesAt, List.getElem_range]
  rw [mem i h₁]
  simp only [Nat.sub_zero, h₁, ↓reduceIte]
  rfl

theorem wipeArgs_wp {σ s : State} (h : G10 P σ s) : WP isa (.block wipeArgs) s (G11 P σ) := by
  obtain ⟨hs, res⟩ := h
  simp only [wipeArgs]
  refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => ?_
  obtain s2 : P.lay.St σ t2 := (hs.2.upd u1 (by decide)).upd u2 (by decide)
  refine s2.wp_arg (j := 3) (r := .ecx) (by simp) (by decide) fun t3 s3 u3 => ?_
  refine wp_movi fun t4 u4 => WP.block_nil ⟨⟨hs.1, s3.upd u4 (by decide)⟩, ?_, ?_, ?_, u4.gpr⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
    exact res
  · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr, hs.2.sp]
  · rw [u4.other _ (by decide), u3.gpr]; rfl

theorem zero_wp {σ s : State} (h : G11 P σ s) : WP isa zeroLoop s (G10 P σ) := by
  obtain ⟨hs, res, si, cx, ax⟩ := h
  have ok := hs.1.ok
  have hK := hs.1.k1024
  have fit := hs.1.fit
  have em := hs.1.emA
  obtain hF : oEM + P.K ≤ P.lay.F := by show _ ≤ frameBytes; simp only [oEM, frameBytes]; omega_using [hK]
  obtain hpt : (P.B + BitVec.ofNat 32 oEM).toNat + P.K ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oEM) (by decide)]
    simp only [oEM, frameBytes] at fit ⊢
    rw [Nat.mod_eq_of_lt (by omega_using [fit])]; omega_using [hK, fit]
  refine WP.mono (zero_ok (p := P.B + BitVec.ofNat 32 oEM) (n := P.K) (by have := hs.1.k64; omega_using [this]) (by omega_using [hK])
    hpt si cx ax (by rw [em]; exact hs.2.inFr hF)) fun t ht => ?_
  obtain fr : Frame [⟨P.lay.fr oEM, P.K⟩] s.mem t.mem := by
    rw [ht.mem, em]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (P.lay.fr oEM) (List.replicate P.K 0)
    simpa using this
  obtain st : P.lay.St σ t := hs.2.frameW hF fr ht.rd ht.wr (ht.other _ (by decide) (by decide))
  refine ⟨⟨hs.1, st⟩, fun nB hn hp => ?_⟩
  obtain hd : oEM + P.K ≤ P.lay.F + 16 := by show _ ≤ frameBytes + 16; simp only [oEM, frameBytes]; omega_using [hK]
  obtain hb : Spec.Rsa.bytesAt t.mem (P.out.setWidth 64) P.K = Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K :=
    Proof.RsaPkcs1Sig.bytesAt_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (ok.stk_fr (R := P.OUT) (.inr (by simp)) hd).symm) (by omega_using [hK])
  obtain w := res nB hn hp
  rw [ht.other _ (by decide) (by decide)]
  revert w
  generalize (if zm (psB P σ) = 0 then Spec.Rsa.publicOpChecked nB P.eB (enc P σ) else none) = o
  intro w
  cases o with
  | some y => exact ⟨w.1, hb.trans w.2⟩
  | none => exact ⟨w.1, hb.trans w.2⟩

theorem ret_wp {σ s : State} (h : G10 P σ s) : WP isa (.block [.mov .eax (.reg .edi)]) s (G13 P σ) :=
  wp_mov fun t u => WP.block_nil ⟨⟨h.1.1, h.1.2.upd u (by decide)⟩, by
    rw [u.mem, u.gpr]; exact h.2⟩

/-! ## Constant time -/

theorem maskArgs_vp : VP (G8 P) (.block maskArgs) (MI P P.K) :=
  VP.taint [.esp] maskArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => maskArgs_wp h

theorem wipeArgs_vp : VP (G10 P) (.block wipeArgs) (G11 P) :=
  VP.taint [.esp] wipeArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => wipeArgs_wp h

theorem zero_vp : VP (G11 P) zeroLoop (G10 P) :=
  VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.2.2.2.1, h₂.2.2.2.1]) fun _ _ h => zero_wp h

theorem ret_vp : VP (G10 P) (.block [.mov .eax (.reg .edi)]) (G13 P) :=
  VP.taint [.esp] ret_taint (sp_agree fun _ _ h => h.1) fun _ _ h => ret_wp h

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: the body

The pieces in order (`body_vp`): `EM` (`Proof/RsaPkcs1Enc/X86/PcPieces.lean`),
the call (`PcCall.lean`) and the masks (`PcMask.lean`), and the body keeps
`esp` (`body_noSp`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

variable {P : EP}

theorem callArgs_vp : VP (G6 P) (.block callArgs) (G7 P) :=
  VP.taint [.esp] callArgs_taint (sp_agree fun _ _ h => h.1) fun _ _ h => callArgs_wp h

theorem body_vp (c : Ver.PublicImpl) : VP (S P) (body c.name c.code) (G13 P) :=
  head_vp.seq (psLoop_vp.seq (sep_vp.seq (msgCopy_vp.seq (callArgs_vp.seq ((call_vp c).seq
    (maskArgs_vp.seq ((maskLoop_vp.mono (fun _ _ h => h) fun _ _ h => masked_g10 h).seq
      (wipeArgs_vp.seq (zero_vp.seq ret_vp)))))))))

theorem body_noSp (c : Ver.PublicImpl) : NoSp (body c.name c.code) :=
  noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel))
    (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (.of_all (by decide +kernel))
      (noSp_seq (.of_all (by decide +kernel)) (noSp_seq (noSp_call c.noSp) (.of_all (by decide +kernel)))))))

end VG.Proof.RsaPkcs1Enc.X86.Pc

end

end


/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86: verified

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/PcVerified.lean`): the frames around
the body (`wrap_ok`, `wrap_ct`), the result as the shared contract states
it, and a state that meets it (`sat`): `vg_rsa_pkcs1_encrypt_precomputed`,
calling any implementation `c` of `vg_rsa_public_precomputed_checked`, is
verified (`code_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Pc

open VG VG.Impl.RsaPkcs1Enc.X86.Precomputed VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- Encryption, once the lengths are as the contract has them. -/
theorem encrypt_eq {nB eB M PS : List Byte} (hM : M.length + 11 ≤ nB.length)
    (hPS : PS.length = nB.length - M.length - 3) :
    Spec.RsaPkcs1Enc.encrypt nB eB M PS =
      if zm PS = 0 then Spec.Rsa.publicOpChecked nB eB (Spec.RsaPkcs1Enc.encode M PS) else none := by
  simp only [Spec.RsaPkcs1Enc.encrypt, hM, hPS, true_and, zm]
  split <;> simp_all

theorem spec_sp {s : State} (h : spec.pre s) :
    stackBytes ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 ≤ 2 ^ 32 := by
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes, stackBelow] at h
  obtain ⟨hsp, hsa, -⟩ := h
  exact ⟨hsp, by omega_using [hsa]⟩

theorem entered_state {s : State} (h : spec.pre s) :
    S (ep s) (entered frameBytes s) (entered frameBytes s) :=
  ⟨in_of_pre h, ⟨(in_of_pre h).ok, (in_of_pre h).ok.sp, rfl, rfl, Frame.refl _ _⟩⟩

theorem code_ok (c : Ver.PublicImpl) {s : State} (h : spec.pre s) :
    WP isa (code c.name c.code) s fun t => abiPreserved s t ∧ spec.post s t := by
  obtain hin := in_of_pre h
  obtain ⟨hs, hfit⟩ := spec_sp h
  obtain hsp : 16 + frameBytes ≤ (s.gpr .esp).toNat := by simp only [stackBytes, frameBytes] at hs ⊢; omega_using [hs]
  obtain hb := (body_vp (P := ep s) c).wp _ _ (entered_state h)
  refine WP.mono (wrap_ok (F := frameBytes) (by decide) (body_noSp c) hsp hfit (W := (ep s).lay.W)
    (Q := fun r m => Res (ep s) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono hb fun u hu => ⟨hu.1.2.frame, hu.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · have ok := hin.ok
    rw [ep_lay] at ok hr
    rw [save_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 100) hsp,
      ret_eq (argv := (ep s).argv) (ro := (ep s).ro) (rw := (ep s).rw) (C := 100) hsp]
    exact ⟨ok.save_apart r hr, ok.ret_apart r hr⟩
  · have ok := hin.ok
    rw [ep_lay] at ok
    obtain ro := fun {R : Region} (hR : R ∈ (ep s).ro) => entered_ro hsp ok hR
    sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
      argVal, argBytes]
    rw [BitVec.setWidth_append_eq_right]
    intro hp
    obtain hn : (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).length = (arg s 3).toNat :=
      Proof.RsaPkcs1Sig.bytesAt_len _ _ _
    obtain w := res _ hn hp
    obtain hM : msgB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 6).setWidth 64)
        (arg s 7).toNat := ro (R := (ep s).MSG) (by simp)
    obtain hP : psB (ep s) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem ((arg s 8).setWidth 64)
        (arg s 9).toNat := ro (R := (ep s).PS) (by simp)
    have hml := hin.mlK
    have hpl := hin.plK
    rw [encrypt_eq (by simp only [Proof.RsaPkcs1Sig.bytesAt_len]; exact hml)
      (by simp only [Proof.RsaPkcs1Sig.bytesAt_len]; exact hpl)]
    simp only [enc] at w
    rw [hM, hP] at w
    exact w

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (h : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h

/-- Two entry states with the same public data have the same public parameters. -/
theorem ep_eq {s₁ s₂ : State} (hp : spec.pub s₁ s₂) : ep s₁ = ep s₂ := by
  sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes] at hp
  obtain ⟨hsp, hl, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hp
  obtain ⟨hab, hc⟩ := List.append_inj hl (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a3, a5])
  obtain ⟨-, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [Proof.RsaPkcs1Sig.bytesAt_len, a3])
  obtain hw := map_toNat_inj hc
  simp only [ep]
  rw [hsp, a0, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
  rw [a4, a5] at he
  rw [a12, a13] at hw
  rw [he, hw]

theorem code_ct (c : Ver.PublicImpl) : ConstantTime isa spec.pre spec.pub (code c.name c.code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain hep := ep_eq hp
  obtain hsp : s₁.gpr .esp = s₂.gpr .esp := by
    sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
      argVal, argBytes] at hp
    exact hp.1
  refine (wrap_ct (F := frameBytes) (body_noSp c) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp) ?_ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp (P := ep s₁) c).ct.mono ?_ fun _ _ _ => trivial
  rintro a b ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩
  exact ⟨_, _, entered_state h₁, by rw [hep]; exact entered_state h₂⟩

/-- A state that meets the shared contract: a modulus of 64 bytes, `e` of one,
an empty message, the padding string of 61 bytes, and the stack arguments
above `0x20000`. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 0x10 else if a = 131080 then 64 else if a = 131085 then 0x20 else
    if a = 131088 then 64 else if a = 131093 then 0x21 else if a = 131096 then 1 else
    if a = 131101 then 0x30 else if a = 131109 then 0x31 else if a = 131112 then 61 else
    if a = 131117 then 0x40 else if a = 131120 then 0x20 else if a = 131121 then 4 else
    if a = 131125 then 0x70 else if a = 131128 then 16 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 61⟩, ⟨0x7000, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8448⟩, ⟨0x20004, 56⟩]

theorem sat : ∃ s, spec.pre s := by
  obtain a0 : arg satState 0 = 0x1000 := by decide
  obtain a1 : arg satState 1 = 64 := by decide
  obtain a2 : arg satState 2 = 0x2000 := by decide
  obtain a3 : arg satState 3 = 64 := by decide
  obtain a4 : arg satState 4 = 0x2100 := by decide
  obtain a5 : arg satState 5 = 1 := by decide
  obtain a6 : arg satState 6 = 0x3000 := by decide
  obtain a7 : arg satState 7 = 0 := by decide
  obtain a8 : arg satState 8 = 0x3100 := by decide
  obtain a9 : arg satState 9 = 61 := by decide
  obtain a10 : arg satState 10 = 0x4000 := by decide
  obtain a11 : arg satState 11 = 1056 := by decide
  obtain a12 : arg satState 12 = 0x7000 := by decide
  obtain a13 : arg satState 13 = 16 := by decide
  obtain e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi,
    argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, e, esp, satState, stackBytes, frameBytes,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.scratchWords, Spec.Rsa.precomputedWords,
      Spec.Rsa.modulusWords] using satState

theorem code_noSp (c : Ver.PublicImpl) : NoSp (code c.name c.code) :=
  noSp_frame rfl rfl (noSp_seq (noSp_frame rfl rfl (body_noSp c)) restore_noSp)

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling `c`, meets the shared contract. -/
theorem code_verified (c : Ver.PublicImpl) : Verified target (code c.name c.code) spec :=
  ⟨fun _ h => let ⟨t, s', he, hq⟩ := code_ok c h; ⟨t, s', he, hq.1, hq.2⟩, code_ct c, sat⟩

end VG.Proof.RsaPkcs1Enc.X86.Pc
