module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecMsg
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: the stages of an IRPRF block

An IRPRF loop (`Prf`): its label, the code of its bit length, its output's
length and place in `scratch`, its number of blocks, and bytes of `scratch`
it keeps. Before block `i` (`CI`): the call's result, `KDK`, the bytes kept,
the number of blocks in its slot, and the first `i` blocks. The stages of a
block (`B0` … `B9`), and the blocks of code between its calls.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg op2_lsl dpVal)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP}

/-- An IRPRF loop: the label's bytes `vs`, the code `len` of the bit length,
the output's length `L`, its place `dst` in `scratch`, its number `nb` of
blocks, and the `xn` bytes `xv` at `scratch + xo` it keeps. -/
structure Prf (P : EP) where
  vs : List Nat
  len : List Instr
  L : Nat
  dst : Nat
  nb : Nat
  xo : Nat
  xn : Nat
  xv : State → List Byte
  vs_lt : ∀ v ∈ vs, v < 256
  vs_len : vs.length + 4 ≤ 16
  nb1 : 1 ≤ nb
  nb_le : nb ≤ 256
  dst_lo : 272 ≤ dst
  dst_hi : dst + 32 * nb ≤ 8448
  dst_enc : VG.Arm.encodable (BitVec.ofNat 32 dst) = true
  x_lo : 208 ≤ xo
  x_hi : xo + xn ≤ 8448
  x_sep : xo + xn ≤ dst ∨ dst + 32 * nb ≤ xo
  lenOk : ∀ {σ s t : State} {i : Nat}, S P σ s → s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg →
    s.gpr .r3 = BitVec.ofNat 32 P.K → MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
    ∀ {Q : State → Prop}, (∀ t', MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 4) t' → Q t') →
      WP isa (.block len) t Q

namespace Prf

variable (R : Prf P)

/-- The label. -/
abbrev lab : List Byte := R.vs.map (BitVec.ofNat 8)

/-- The length of a block's message. -/
abbrev tl : Nat := R.vs.length + 4

end Prf

/-- Before block `i`. -/
structure CI (P : EP) (R : Prf P) (i : Nat) (σ s : State) : Prop where
  hi : i ≤ R.nb
  base : Base P σ s
  kdk : Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ
  x : Spec.Rsa.bytesAt s.mem (sc P R.xo R.xn).base R.xn = R.xv σ
  sNB : s.mem.readW (P.lay.fr oNB) 32 = BitVec.ofNat 32 R.nb
  blk : Spec.Rsa.bytesAt s.mem (sc P R.dst (32 * i)).base (32 * i) =
    (List.range i).flatMap (prfBlock (kdkV P σ) R.lab R.L)

/-- What the loop's writes stay apart from. -/
structure Keep (P : EP) (R : Prf P) (i : Nat) (r : Region) : Prop where
  safe : Safe P r
  kdk : (sc P sKDK 32).Disjoint r
  x : (sc P R.xo R.xn).Disjoint r
  blk : (sc P R.dst (32 * i)).Disjoint r
  nb : Region.Disjoint ⟨P.lay.fr oNB, 4⟩ r

section
variable {R : Prf P} {i : Nat} {σ s t : State}

theorem CI.keep (h : CI P R i σ s) (st : P.lay.St σ t) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hk : ∀ r ∈ rs, Keep P R i r) : CI P R i σ t where
  hi := h.hi
  base := h.base.frame st hf fun r hr => (hk r hr).safe
  kdk := (bytes_frame hf (R := sc P sKDK 32) (fun r hr => (hk r hr).kdk) (by show 32 ≤ 2 ^ 64; decide)).trans h.kdk
  x := (bytes_frame hf (R := sc P R.xo R.xn) (fun r hr => (hk r hr).x)
    (by have := R.x_hi; show R.xn ≤ 2 ^ 64; omega)).trans h.x
  sNB := by
    rw [hf.readW (r := ⟨P.lay.fr oNB, 4⟩) (Region.contains_self _ _) (fun r hr => (hk r hr).nb) (by decide)]
    exact h.sNB
  blk := (bytes_frame hf (R := sc P R.dst (32 * i)) (fun r hr => (hk r hr).blk)
    (by have := R.dst_hi; have := h.hi; show 32 * i ≤ 2 ^ 64; omega)).trans h.blk

theorem CI.of_mem (h : CI P R i σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : CI P R i σ t :=
  h.keep st (rs := []) (by rw [hm]; exact Frame.refl _ _) fun _ h => absurd h List.not_mem_nil

theorem CI.S (h : CI P R i σ s) : S P σ s := h.base.1

/-- A slot of the frame kept. -/
theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr d, 4⟩ r) : m'.readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

namespace In
variable (h : In P σ)
include h

theorem keep_sc {o n : Nat} (hn : o + n ≤ 8448) (hk : o + n ≤ sKDK ∨ sKDK + 32 ≤ o)
    (hx : o + n ≤ R.xo ∨ R.xo + R.xn ≤ o) (hb : o + n ≤ R.dst ∨ R.dst + 32 * i ≤ o) (hi : i ≤ R.nb) :
    Keep P R i (sc P o n) where
  safe := h.safe_sc hn
  kdk := sc_sep (by simp only [sKDK] at hk ⊢; omega) (by decide) hn
  x := sc_sep (by omega) R.x_hi hn
  blk := sc_sep (by omega) (by have := R.dst_hi; omega) hn
  nb := h.fr_sc (by simp only [oNB, frameBytes]; decide) hn

theorem keep_low (hi : i ≤ R.nb) : Keep P R i P.lay.LOW where
  safe := h.safe_low
  kdk := (h.low_sc (by decide)).symm
  x := (h.low_sc R.x_hi).symm
  blk := (h.low_sc (by have := R.dst_hi; omega)).symm
  nb := Lay.fr_low (by simp only [oNB]; decide)

theorem keep_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d)
    (hnb : d + n ≤ oNB ∨ oNB + 4 ≤ d) (hi : i ≤ R.nb) : Keep P R i ⟨P.lay.fr d, n⟩ where
  safe := h.safe_fr hd ho
  kdk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) (by decide)).symm
  x := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) R.x_hi).symm
  blk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) (by have := R.dst_hi; omega)).symm
  nb := Lay.fr_sep (by simp only [oNB] at hnb ⊢; omega) (by decide) (by simp only [frameBytes] at hd; omega)

/-- The data of `update` in `scratch`. -/
theorem dataSc {s : State} (hs : S P σ s) {o n : Nat} (hn : o + n ≤ 8448) (ho : 96 ≤ o) (ho8 : o < 8448) :
    DataOk P s (P.scr + BitVec.ofNat 32 o) n where
  cov := (In.scW hs hn (by omega)).right
  dS := h.sc0_sepW ho (by decide) hn (by omega)
  lo := h.lowR_sc (by decide) hn (by omega)
  fit := h.fit_sc hn (by omega)

end In

end

/-! ## The stages of block `i` -/

section
variable (P : EP) (R : Prf P) (i : Nat) (σ s : State)

/-- Block `i` begins: its counter in its slot. -/
def B0 : Prop := CI P R i σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The message's place, `i` and `k`. -/
def B1 : Prop :=
  B0 P R i σ s ∧ s.gpr .r0 = P.scr + BitVec.ofNat 32 sMsg ∧ s.gpr .r1 = BitVec.ofNat 32 i ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K

/-- The message written. -/
def B2 : Prop := B0 P R i σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L

/-- Before HMAC's `init`. -/
def B3 : Prop := B2 P R i σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sKDK) 32

/-- After it. -/
def B4 : Prop := B2 P R i σ s ∧ Macd s.mem P (kdkV P σ) []

/-- Before `update`. -/
def B5 : Prop := B4 P R i σ s ∧ UpdArgs s P.scr (P.scr + BitVec.ofNat 32 sMsg) R.tl 64

/-- After it. -/
def B6 : Prop := B0 P R i σ s ∧ Macd s.mem P (kdkV P σ) (msgV i R.lab R.L)

/-- Before `finalize`. -/
def B7 : Prop :=
  B6 P R i σ s ∧ HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 (R.dst + 32 * i))
    (64 + R.tl)

/-- Block `i` written. -/
def B8 : Prop := CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The counter incremented. -/
def B9 : Prop :=
  CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 (i + 1) ∧
    s.gpr .r1 = BitVec.ofNat 32 (i + 1) ∧ s.gpr .r2 = BitVec.ofNat 32 R.nb

end

/-! ## The blocks of code -/

section
variable {R : Prf P} {i : Nat} {σ s : State}

theorem msgPtr_wp (h : B0 P R i σ s) : WP isa (.block msgPtr) s (B1 P R i σ) := by
  have hs := h.1.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r0]) (by simp)) u3.mem
  refine s3.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => WP.block_nil ?_
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, m3]
  refine ⟨⟨h.1.of_mem s5 mm, by rw [mm]; exact h.2⟩, ?_, ?_, u5.gpr⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr, m3, h.2]

theorem msgBytes_b2 (h : B1 P R i σ s) (hi : i < 256) :
    WP isa (.block (msgBytes R.vs R.len)) s (B2 P R i σ) := by
  obtain ⟨⟨hc, sI⟩, r0, r1, r3⟩ := h
  have hs := hc.S
  refine WP.mono (msgBytes_wp (L := R.L) hs r0 r1 hi R.vs_len R.vs_lt (R.lenOk hs r0 r3)) fun t ⟨st, fr, _, hb⟩ => ?_
  have hk : ∀ r ∈ [sc P sMsg 16], Keep P R i r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.keep_sc (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sMsg]; omega))
      (.inl (by have := R.dst_lo; simp only [sMsg]; omega)) hc.hi
  refine ⟨⟨hc.keep st.2 fr hk, ?_⟩, hb⟩
  rw [slot_keep fr fun r hr => ?_]
  · exact sI
  · simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.fr_sc (by simp only [oI, frameBytes]; decide) (by decide)

theorem B2.msg_frame (h : B2 P R i σ s) {t : State} {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (sc P sMsg R.tl).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L :=
  (bytes_frame hf hd (by have := R.vs_len; show R.vs.length + 4 ≤ 2 ^ 64; omega)).trans h.2

theorem B0.keep (h : B0 P R i σ s) {t : State} (st : P.lay.St σ t) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hk : ∀ r ∈ rs, Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) : B0 P R i σ t :=
  ⟨h.1.keep st hf fun r hr => (hk r hr).1, by rw [slot_keep hf fun r hr => (hk r hr).2]; exact h.2⟩

theorem prfUpdArgs_wp (h : B4 P R i σ s) : WP isa (.block (prfUpdArgs (R.vs.length + 4))) s (B5 P R i σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1.1.S
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)))
    fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_strFr (d := 4) (by show 4 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = (s.mem.writeW (P.lay.fr 0) (t3.gpr .r1)).writeW (P.lay.fr 4) (t5.gpr .r1) := by
    rw [u8.mem, u7.mem, m6.mem, u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr := frame8 mm
  have hfr : ∀ r ∈ [(⟨P.lay.fr 0, 8⟩ : Region)], Region.Disjoint (sc P 0 192) r ∧ (sc P sMsg R.tl).Disjoint r ∧
      (Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hs.1.fr_sc (by decide) (by decide)).symm, (hs.1.fr_sc (by decide) (by simp only [sMsg]; omega)).symm,
      hs.1.keep_fr (by decide) (by simp only [oR]; decide) (by simp only [oNB]; decide) hb.1.1.hi,
      Lay.fr_sep (by simp only [oI]; decide) (by decide) (by decide)⟩
  have r1v : t3.gpr .r1 = P.scr + BitVec.ofNat 32 sMsg := by rw [u3.gpr, dpVal, u2.gpr]; rfl
  refine ⟨⟨⟨hb.1.keep s8 fr fun r hr => (hfr r hr).2.2, hb.msg_frame fr fun r hr => (hfr r hr).2.1⟩,
    macd_frame hs.1 fr (fun r hr => (hfr r hr).1) md⟩, ?_, ?_, u8.gpr, ?_, ?_, by omega, by decide⟩
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, r1v]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]

theorem shl5 (i : Nat) : BitVec.ofNat 32 i <<< 5 = BitVec.ofNat 32 (32 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem prfFinArgs_wp (h : B6 P R i σ s) :
    WP isa (.block (prfFinArgs (R.vs.length + 4) R.dst)) s (B7 P R i σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1.S
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t3 s3 u3 => ?_
  refine wp_dp (op2_imm R.dst_enc) fun t4 u4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := (s3.of_rest (u4.rest (ws := [.r1]) (by simp)) u4.mem).of_rest
    (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)))
    fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => WP.block_nil ?_
  have s9 : P.lay.St σ t9 := ((s6.of_rest (u7.rest (ws := [.r1]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r2]) (by simp)) u8.mem).of_rest (u9.rest (ws := [.r3]) (by simp)) u9.mem
  have m3 : t3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have mm : t9.mem = s.mem.writeW (P.lay.fr 0) (t5.gpr .r1) := by
    rw [u9.mem, u8.mem, u7.mem, m6.mem, u5.mem, u4.mem, m3]
  have fr := frame4 mm
  have r0v : t2.gpr .r0 = P.scr := by rw [u2.gpr]; rfl
  have hfr : ∀ r ∈ [(⟨P.lay.fr 0, 4⟩ : Region)], Region.Disjoint (sc P 0 192) r ∧
      (Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(hs.1.fr_sc (by decide) (by decide)).symm,
      hs.1.keep_fr (by decide) (by simp only [oR]; decide) (by simp only [oNB]; decide) hb.1.hi,
      Lay.fr_sep (by simp only [oI]; decide) (by decide) (by decide)⟩
  have r1v : t5.gpr .r1 = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) := by
    rw [u5.gpr, dpVal, u4.gpr, dpVal, u3.other _ (by decide), r0v, u4.other _ (by decide), u3.gpr, u2.mem, u1.mem, hb.2,
      shl5, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨⟨hb.keep s9 fr fun r hr => (hfr r hr).2, macd_frame hs.1 fr (fun r hr => (hfr r hr).1) md⟩, ?_, ?_, ?_,
    u9.gpr, ?_, by omega⟩
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), r0v]
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, dpVal, m6.gpr, u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), r0v]
  · rw [u9.other _ (by decide), u8.gpr]
  · rw [stackArg_fr ⟨hs.1, s9⟩ (by decide), mm, Mem.readW_writeW_self32, r1v]

theorem incr_wp (h : B8 P R i σ s) : WP isa (.block incr) s (B9 P R i σ) := by
  obtain ⟨hc, sI⟩ := h
  have hs := hc.S
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_slot (d := oNB) (by show oNB + 4 ≤ frameBytes; decide) (by decide) fun t5 s5 u5 => WP.block_nil ?_
  have r1v : t3.gpr .r1 = BitVec.ofNat 32 (i + 1) := by
    rw [u3.gpr, dpVal, u2.gpr, u1.mem, sI, BitVec.ofNat_add_ofNat]
  have mm : t5.mem = s.mem.writeW (P.lay.fr oI) (t3.gpr .r1) := by
    rw [u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr : Frame [⟨P.lay.fr oI, 4⟩] s.mem t5.mem := by
    rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc' := hc.keep s5 fr fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.keep_fr (by decide) (by simp only [oR, oI]; decide) (by simp only [oNB, oI]; decide) hc.hi
  refine ⟨hc', by rw [mm, Mem.readW_writeW_self32, r1v], by rw [u5.other _ (by decide), m4.gpr, r1v], ?_⟩
  rw [u5.gpr, ← u5.mem]; exact hc'.sNB

end

end VG.Proof.RsaPkcs1Enc.Arm.Dec
