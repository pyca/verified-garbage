module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecKdk
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMsg
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: an IRPRF loop

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecPrf.lean`,
`Proof/RsaPkcs1Enc/Arm/DecPrfLoop.lean`): a loop (`Prf`) writes block `i`
of IRPRF, `HMAC(KDK, msgV i label L)`, to `scratch + dst + 32 i`
(`prfBody_vp`), keeping `KDK` and `xn` bytes of `scratch` at `xo`; the
whole loop (`loop_vp`) writes its `nb` blocks (`CI`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Mont.X86 (wp_addS wp_cmpS)
open VG.Proof.Sha256.X86.Variants (Backend)
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
  vs_len : vs.length + 4 ≤ 16
  nb1 : 1 ≤ nb
  nb_le : nb ≤ 256
  dst_lo : 272 ≤ dst
  dst_hi : dst + 32 * nb ≤ 2576
  x_lo : 208 ≤ xo
  x_hi : xo + xn ≤ 2576
  x_sep : xo + xn ≤ dst ∨ dst + 32 * nb ≤ xo
  lenOk : ∀ {σ s t : State} {i : Nat}, S P σ s → s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg →
    s.gpr .edx = BitVec.ofNat 32 P.K → MW P σ s (msgV i (vs.map (BitVec.ofNat 8)) L) (vs.length + 2) t →
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
  kdk := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).kdk) (by decide)).trans h.kdk
  x := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).x)
    (by have := R.x_hi; omega)).trans h.x
  sNB := by
    rw [hf.readW (r := ⟨P.lay.fr oNB, 4⟩) (Region.contains_self _ _) (fun r hr => (hk r hr).nb) (by decide)]
    exact h.sNB
  blk := (Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => (hk r hr).blk)
    (by have := R.dst_hi; have := h.hi; omega)).trans h.blk

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

theorem keep_sr {o n : Nat} (ho : o < 8448) (hn : o + n ≤ 8448) (hk : o + n ≤ sKDK ∨ sKDK + 32 ≤ o)
    (hx : o + n ≤ R.xo ∨ R.xo + R.xn ≤ o) (hb : o + n ≤ R.dst ∨ R.dst + 32 * i ≤ o) (hi : i ≤ R.nb) :
    Keep P R i (sr P o n) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (sr P o n) := by
  rw [h.sr_eq ho]
  exact ⟨{ safe := h.safe_sc hn
           kdk := sc_sep (by simp only [sKDK] at hk ⊢; omega) (by decide) hn
           x := sc_sep (by omega) (by have := R.x_hi; omega) hn
           blk := sc_sep (by omega) (by have := R.dst_hi; omega) hn
           nb := h.fr_sc (by simp only [oNB, frameBytes]; decide) hn },
    h.fr_sc (by simp only [oI, frameBytes]; decide) hn⟩

theorem keep_below {k : Nat} (hk : k ≤ 3392) (hi : i ≤ R.nb) :
    Keep P R i (below P.B k) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (below P.B k) := by
  have hl := h.low_of hk
  exact ⟨{ safe := h.below_safe hk
           kdk := (h.low_sc (by decide)).symm.sub_right hl
           x := (h.low_sc (by have := R.x_hi; omega)).symm.sub_right hl
           blk := (h.low_sc (by have := R.dst_hi; omega)).symm.sub_right hl
           nb := (Lay.fr_low (by simp only [oNB]; decide) (by show (3392 : Nat) ≤ 2 ^ 32; decide)).sub_right hl },
    (Lay.fr_low (by simp only [oI]; decide) (by show (3392 : Nat) ≤ 2 ^ 32; decide)).sub_right hl⟩

theorem keep_fr {d n : Nat} (hd : d + n ≤ frameBytes) (ho : d + n ≤ oR ∨ oR + 4 ≤ d)
    (hnb : d + n ≤ oNB ∨ oNB + 4 ≤ d) (hi : i ≤ R.nb) : Keep P R i ⟨P.lay.fr d, n⟩ where
  safe := h.safe_fr hd ho
  kdk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) (by decide)).symm
  x := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) (by have := R.x_hi; omega)).symm
  blk := (h.fr_sc (by simp only [frameBytes] at hd ⊢; omega) (by have := R.dst_hi; omega)).symm
  nb := Lay.fr_sep (by simp only [oNB] at hnb ⊢; omega) (by decide) (by simp only [frameBytes] at hd; omega)

end In

/-- Through a call. -/
theorem CI.call (h : CI P R i σ s) {ws : List Region} {k : Nat} (c : Called s t ws k) (hk : k ≤ 3392)
    (hws : InScr P ws) (hkp : ∀ r ∈ ws, Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r) :
    CI P R i σ t ∧ t.mem.readW (P.lay.fr oI) 32 = s.mem.readW (P.lay.fr oI) 32 := by
  have hs := h.S
  have hf := c.frame
  rw [hs.2.sp] at hf
  have kp : ∀ r ∈ ws ++ [below P.B k], Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r := fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hkp r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.keep_below hk h.hi
  exact ⟨h.keep (c.st hs hk hws).2 hf fun r hr => (kp r hr).1, slot_keep hf fun r hr => (kp r hr).2⟩

end

/-! ## The stages of block `i` -/

section
variable (P : EP) (R : Prf P) (i : Nat) (σ s : State)

/-- Block `i` begins: its counter in its slot. -/
def B0 : Prop := CI P R i σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

/-- The message's place, `i` and `k`. -/
def B1 : Prop :=
  B0 P R i σ s ∧ s.gpr .ebx = P.scr + BitVec.ofNat 32 sMsg ∧ s.gpr .ecx = BitVec.ofNat 32 i ∧
    s.gpr .edx = BitVec.ofNat 32 P.K

/-- The message written. -/
def B2 : Prop := B0 P R i σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L

/-- Before HMAC's `init`. -/
def B3 : Prop :=
  B2 P R i σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sKDK ∧ s.gpr .ecx = BitVec.ofNat 32 32 ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After it. -/
def B4 : Prop := B2 P R i σ s ∧ Macd s.mem P (kdkV P σ) []

/-- Before `update`. -/
def B5 : Prop :=
  B4 P R i σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = BitVec.ofNat 32 64 ∧ s.gpr .eax = 0 ∧
    s.gpr .ecx = BitVec.ofNat 32 R.tl ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sMsg ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After it. -/
def B6 : Prop := B0 P R i σ s ∧ Macd s.mem P (kdkV P σ) (msgV i R.lab R.L)

/-- Before `finalize`. -/
def B7 : Prop :=
  B6 P R i σ s ∧ s.gpr .edx = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = P.scr + BitVec.ofNat 32 sOuter ∧
    s.gpr .eax = BitVec.ofNat 32 (64 + R.tl) ∧ s.gpr .ecx = 0 ∧
    s.gpr .edi = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- Block `i` written. -/
def B8 : Prop := CI P R (i + 1) σ s ∧ s.mem.readW (P.lay.fr oI) 32 = BitVec.ofNat 32 i

end

/-- Before block `nb - m`, `m` blocks left. -/
def LI (P : EP) (R : Prf P) (m : Nat) (σ s : State) : Prop := m ≤ R.nb ∧ B0 P R (R.nb - m) σ s

/-! ## The pieces -/

section
variable {R : Prf P} {i : Nat}

theorem hmac_len (k t : List Byte) : (Spec.Hmac.hmac Spec.Hmac.sha256 k t).length = 32 := by
  simp only [Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, Spec.Hmac.sha256]; exact hash_length _

theorem kdkV_length {σ : State} : (kdkV P σ).length = 32 := hmac_len _ _

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp, Offset.add_add]

theorem sub_beq_zero {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      replace this : (2 ^ 32 - b + a) % 2 ^ 32 = 0 := this
      omega
    rw [beq_eq_false_iff_ne.mpr this, decide_eq_false h]

theorem msgPtr_vp : VP (B0 P R i) (.block msgPtr) (B1 P R i) :=
  VP.taint [.esp] msgPtr_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    have hs := h.1.S
    simp only [msgPtr, List.cons_append, List.nil_append, scr]
    refine St.argv hs (j := 21) (by decide) (d := .ebx) (by decide) fun t1 s1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    have s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine s2.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .ecx) (by decide)
      fun t3 st3 u3 => ?_
    refine St.argv ⟨hs.1, st3⟩ (j := 4) (by decide) (d := .edx) (by decide) fun t4 s4 u4 => WP.block_nil ?_
    have m2 : t2.mem = s.mem := by rw [u2.mem, u1.mem]
    have mm : t4.mem = s.mem := by rw [u4.mem, u3.mem, m2]
    refine ⟨⟨h.1.of_mem s4.2 mm, by rw [mm]; exact h.2⟩, ?_, ?_, u4.gpr⟩
    · rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr]; rfl
    · rw [u4.other _ (by decide), u3.gpr, m2, h.2]

theorem msg_vp (cert : TaintOk [.ebx] (.block (msgBytes R.vs R.len))) (hi : i < 256) :
    VP (B1 P R i) (.block (msgBytes R.vs R.len)) (B2 P R i) :=
  VP.taint [.ebx] cert (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) fun σ s h => by
    obtain ⟨⟨hc, sI⟩, bx, cx, dx⟩ := h
    have hs := hc.S
    refine WP.mono (msgBytes_wp (L := R.L) hs bx cx hi R.vs_len (R.lenOk hs bx dx)) fun t ⟨st, fr, _, hb⟩ => ?_
    have hk : ∀ r ∈ [sc P sMsg 16], Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [← hs.1.sr_eq (by decide)]
      exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sMsg]; omega))
        (.inl (by have := R.dst_lo; simp only [sMsg]; omega)) hc.hi
    exact ⟨⟨hc.keep st.2 fr fun r hr => (hk r hr).1, by rw [slot_keep fr fun r hr => (hk r hr).2]; exact sI⟩, hb⟩

theorem initArgs_vp : VP (B2 P R i) (.block (macInitArgs sKDK)) (B3 P R i) :=
  VP.taint [.esp] macInitKDK_taint (sp_agree fun _ _ h => h.1.1.S) fun σ s h =>
    macInitArgs_wp h.1.1.S sKDK fun t st hm r =>
      ⟨⟨⟨h.1.1.of_mem st.2 hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2⟩, r⟩

/-- The message, through a call that writes elsewhere. -/
theorem msg_keep {σ s t : State} {ws : List Region} {k : Nat} (h : B2 P R i σ s) (c : Called s t ws k)
    (hk : k ≤ 3392) (hd : ∀ r ∈ ws, (sr P sMsg R.tl).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (sc P sMsg R.tl).base R.tl = msgV i R.lab R.L := by
  have hs := h.1.1.S
  have := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  rw [← hs.1.sr_eq (by decide), c.keep hs hk (by decide) (by simp only [sMsg]; omega) hd, hs.1.sr_eq (by decide)]
  exact h.2

theorem init_vp (v : Backend) : VP (B3 P R i) (callHi v.F) (B4 P R i) :=
  macInit_vp v (key := sKDK) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1.S, h.2⟩) fun σ s t h c md => by
    obtain ⟨hb, -⟩ := h
    have hs := hb.1.1.S
    have hi := hb.1.1.hi
    have := R.vs_len
    have htl : R.tl = R.vs.length + 4 := rfl
    have ci := hb.1.1.call c (by decide) hiWs_scr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega))
          (.inl (by have := R.dst_lo; simp only [sSt]; omega)) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sOuter]; omega))
          (.inl (by have := R.dst_lo; simp only [sOuter]; omega)) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega))
          (.inr (by have := R.dst_hi; simp only [sW]; omega)) hi
    refine ⟨⟨⟨ci.1, by rw [ci.2]; exact hb.1.2⟩, msg_keep hb c (by decide) fun r hr => ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hs.1.sr_sep (by simp only [sMsg, sSt, sOuter, sW]; omega) (by decide) (by decide)
          (by simp only [sMsg]; omega) (by decide)
    · rw [show Spec.Rsa.bytesAt s.mem (sr P sKDK 32).base 32 = kdkV P σ by
        rw [hs.1.sr_eq (by decide)]; exact hb.1.1.kdk] at md
      exact md

theorem updArgs_vp (cert : TaintOk [.esp] (.block (prfUpdArgs R.tl))) :
    VP (B4 P R i) (.block (prfUpdArgs R.tl)) (B5 P R i) :=
  VP.taint [.esp] cert (sp_agree fun _ _ h => h.1.1.1.S) fun σ s h => by
    have hs := h.1.1.1.S
    simp only [prfUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.movi s1 (d := .esi) (by decide) 64 fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
    refine St.scrW s3 (d := .edx) (by decide) sMsg fun t4 s4 u4 => ?_
    refine St.movi s4 (d := .ecx) (by decide) R.tl fun t5 s5 u5 => ?_
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
    have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨⟨h.1.1.1.of_mem s6.2 mm, by rw [mm]; exact h.1.1.2⟩, by rw [mm]; exact h.1.2⟩,
      by rw [mm]; exact h.2⟩, ?_⟩
    simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
      u2.gpr, u2.other, u1.gpr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem upd_vp (v : Backend) : VP (B5 P R i) (callUpd v.F) (B6 P R i) := by
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  refine macUpd_vp (P := P) v (d := P.scr + BitVec.ofNat 32 sMsg) (len := R.tl) (key := fun σ _ => kdkV P σ)
    (fun _ _ h => ?_) fun σ s t h c md => ?_
  · obtain ⟨⟨hb, md⟩, a, b, e, f, g, k⟩ := h
    have hs := hb.1.1.S
    exact ⟨hs, a, b, e, f, g, k, md, by rw [kdkV_length]; decide,
      { hlen := by omega
        cd := Covers.right (St.cov_sr hs (by decide) (by simp only [sMsg]; omega))
        d_st := hs.1.sr_sep (by simp only [sMsg, sSt]; omega) (by decide) (by decide)
          (by simp only [sMsg]; omega) (by decide)
        d_sc := hs.1.sr_sep (by simp only [sMsg, sW]; omega) (by decide) (by decide)
          (by simp only [sMsg]; omega) (by decide)
        b_d := hs.1.below_sr (by decide) (by decide) (by simp only [sMsg]; omega)
        nd := hs.1.sr_fit (by decide) (by simp only [sMsg]; omega) }⟩
  · obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1.1.S
    have hi := hb.1.1.hi
    have ci := hb.1.1.call c (by decide) updWs_scr fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega))
          (.inl (by have := R.dst_lo; simp only [sSt]; omega)) hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega))
          (.inr (by have := R.dst_hi; simp only [sW]; omega)) hi
    refine ⟨⟨ci.1, by rw [ci.2]; exact hb.1.2⟩, ?_⟩
    have e : Spec.Rsa.bytesAt s.mem ((P.scr + BitVec.ofNat 32 sMsg).setWidth 64) R.tl = msgV i R.lab R.L := by
      rw [show (P.scr + BitVec.ofNat 32 sMsg).setWidth 64 = (sc P sMsg R.tl).base from hs.1.scrA (by decide)]
      exact hb.2
    rw [e] at md
    exact md

theorem add_self_ofNat (n : Nat) : BitVec.ofNat 32 n + BitVec.ofNat 32 n = BitVec.ofNat 32 (2 * n) := by
  rw [BitVec.ofNat_add_ofNat, Nat.two_mul]

theorem finArgs_vp (cert : TaintOk [.esp] (.block (prfFinArgs R.tl R.dst))) :
    VP (B6 P R i) (.block (prfFinArgs R.tl R.dst)) (B7 P R i) :=
  VP.taint [.esp] cert (sp_agree fun _ _ h => h.1.1.S) fun σ s h => by
    have hs := h.1.1.S
    have hi := h.1.1.hi
    have := R.nb_le
    have := R.dst_hi
    simp only [prfFinArgs, List.append_assoc, List.cons_append, List.nil_append]
    refine St.scrW hs (d := .edx) (by decide) sSt fun t1 s1 u1 => ?_
    refine St.scrW s1 (d := .esi) (by decide) sOuter fun t2 s2 u2 => ?_
    refine St.movi s2 (d := .eax) (by decide) (64 + R.tl) fun t3 s3 u3 => ?_
    refine St.movi s3 (d := .ecx) (by decide) 0 fun t4 s4 u4 => ?_
    refine s4.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .edi) (by decide)
      fun t5 st5 u5 => ?_
    refine wp_add fun t6 u6 _ => ?_
    refine wp_add fun t7 u7 _ => ?_
    refine wp_add fun t8 u8 _ => ?_
    refine wp_add fun t9 u9 _ => ?_
    refine wp_add fun t10 u10 _ => ?_
    have s10 : S P σ t10 := ⟨hs.1, ((((st5.upd u6 (by decide)).upd u7 (by decide)).upd u8 (by decide)).upd u9
      (by decide)).upd u10 (by decide)⟩
    refine wp_addS (s10.2.readArg (j := 21) (by simp)) fun t11 u11 _ => ?_
    refine wp_addi fun t12 u12 => ?_
    have s12 : S P σ t12 := ⟨hs.1, (s10.2.upd u11 (by decide)).upd u12 (by decide)⟩
    rw [← List.append_nil (scr _ _)]
    refine St.scrW s12 (d := .ebp) (by decide) sW fun t13 s13 u13 => WP.block_nil ?_
    have mm : t13.mem = s.mem := by
      rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
        u1.mem]
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨⟨⟨h.1.1.of_mem s13.2 mm, by rw [mm]; exact h.1.2⟩, by rw [mm]; exact h.2⟩, ?_⟩
    have di : t13.gpr .edi = P.scr + BitVec.ofNat 32 (R.dst + 32 * i) := by
      rw [u13.other _ (by decide), u12.gpr, u11.gpr, u10.gpr, u9.gpr, u8.gpr, u7.gpr, u6.gpr, u5.gpr, m4, h.1.2]
      simp only [add_self_ofNat, EP.argv, List.getD_cons_succ, List.getD_cons_zero]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine ⟨?_, ?_, ?_, ?_, di, ?_⟩
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.other, u2.other, u1.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.other, u2.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.other, u3.gpr]
    · simp (disch := decide) only [u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other,
        u6.other, u5.other, u4.gpr]; rfl
    · exact u13.gpr

theorem fin_vp (v : Backend) (hi : i < R.nb) : VP (B7 P R i) (callHf v.F) (B8 P R i) := by
  have hd := R.dst_hi
  have hd' := R.dst_lo
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  refine macFin_vp (P := P) v (o := R.dst + 32 * i) (tl := R.tl) (key := fun σ _ => kdkV P σ)
    (text := fun _ _ => msgV i R.lab R.L) (by omega) (by omega)
    (fun _ _ h => ?_) fun σ s t h c hk => ?_
  · obtain ⟨⟨hb, md⟩, a, b, e, f, g, k⟩ := h
    exact ⟨hb.1.S, a, b, e, f, g, k, md, by rw [kdkV_length]; decide, by rw [msgV_length]; simp, by omega⟩
  · obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1.S
    have hx := R.x_sep
    have ci := hb.1.call c (by decide) (hfWs_scr (by omega)) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inl (by have := R.x_lo; simp only [sSt]; omega))
          (.inl (by simp only [sSt]; omega)) hb.1.hi
      · exact hs.1.keep_sr (by omega) (by omega) (.inr (by simp only [sKDK]; omega))
          (by rcases hx with hx | hx
              · exact .inr (by omega)
              · exact .inl (by omega)) (.inr (by omega)) hb.1.hi
      · exact hs.1.keep_sr (by decide) (by decide) (by decide) (.inr (by have := R.x_hi; simp only [sW]; omega))
          (.inr (by simp only [sW]; omega)) hb.1.hi
    have c' := ci.1
    refine ⟨⟨by omega, c'.base, c'.kdk, c'.x, c'.sNB, ?_⟩, by rw [ci.2]; exact hb.2⟩
    rw [show 32 * (i + 1) = 32 * i + 32 by omega, bytesAt_add, c'.blk, Offset.add_add, List.range_succ,
      List.flatMap_append, List.flatMap_singleton]
    refine congrArg _ ?_
    rw [hs.1.sr_eq (by omega)] at hk
    exact hk

/-- The counter incremented, and whether there is another block, `n` left after this one. -/
theorem incr_vp {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B8 P R i) (.block incr) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) :=
  VP.taint [.esp] incr_taint (sp_agree fun _ _ h => h.1.S) fun σ s h => by
    obtain ⟨hc, sI⟩ := h
    have hs := hc.S
    have hnb := R.nb_le
    simp only [incr]
    refine hs.2.wp_slot (d := oI) (by show oI + 4 ≤ frameBytes; decide) (r := .eax) (by decide)
      fun t1 st1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    have st2 := st1.upd u2 (by decide)
    refine st2.wp_strFr (d := oI) (by show oI + 4 ≤ frameBytes; decide) fun t3 st3 m3 => ?_
    refine wp_cmpS (st3.readSlot (d := oNB) (by show oNB + 4 ≤ frameBytes; decide)) fun t4 u4 hz => WP.block_nil ?_
    have st4 : P.lay.St σ t4 := st3.fupd u4
    have ax : t2.gpr .eax = BitVec.ofNat 32 (i + 1) := by
      rw [u2.gpr, u1.gpr, sI]; exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 i
    have mm : t4.mem = s.mem.writeW (P.lay.fr oI) (BitVec.ofNat 32 (i + 1)) := by
      rw [u4.mem, m3.mem, ax, u2.mem, u1.mem]
    have fr : Frame [⟨P.lay.fr oI, 4⟩] s.mem t4.mem := by
      rw [mm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hc' := hc.keep st4 fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.1.keep_fr (by decide) (by simp only [oR, oI]; decide) (by simp only [oNB, oI]; decide) hc.hi
    have nb : t3.mem.readW (P.lay.fr oNB) 32 = BitVec.ofNat 32 R.nb := by
      rw [← u4.mem]; exact hc'.sNB
    rw [m3.gpr, ax, nb, sub_beq_zero (by omega) (by omega)] at hz
    have e : (!decide (i + 1 = R.nb)) = decide (0 < n) := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [decide_eq_true (by omega : i + 1 = R.nb), decide_eq_false (by omega : ¬ 0 < n)]; rfl
      · rw [decide_eq_false (by omega : ¬ i + 1 = R.nb), decide_eq_true h0]; rfl
    refine ⟨by show eval .ne t4 = _; simp only [eval, hz]; rw [← e]; rfl, fun h0 => ?_, fun h0 => ?_⟩
    · rw [show R.nb = i + 1 by omega]; exact hc'
    · refine ⟨by omega, ?_⟩
      rw [show R.nb - n = i + 1 by omega]
      exact ⟨hc', by rw [mm, Mem.readW_writeW_self32]⟩

/-- The certificates of the taint analysis a loop needs. -/
structure Certs (R : Prf P) : Prop where
  msg : TaintOk [.ebx] (.block (msgBytes R.vs R.len))
  upd : TaintOk [.esp] (.block (prfUpdArgs R.tl))
  fin : TaintOk [.esp] (.block (prfFinArgs R.tl R.dst))

theorem prfBody_vp (v : Backend) (ce : Certs R) {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B0 P R i) (prfBody v.F R.vs R.len R.dst) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) := by
  have hnb := R.nb_le
  exact (msgPtr_vp.block_append (msg_vp ce.msg (by omega))).seq (initArgs_vp.seq ((init_vp v).seq
    ((updArgs_vp ce.upd).seq ((upd_vp v).seq ((finArgs_vp ce.fin).seq ((fin_vp v (by omega)).seq
      (incr_vp hn)))))))

/-- A piece no state reaches. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  VP.of_ct (fun _ _ _ _ _ _ _ _ hh => absurd hh.1 (h _ _)) fun σ s hs => absurd hs (h σ s)

/-- The loop, from block 0. -/
theorem loop_vp (v : Backend) (ce : Certs R) :
    VP (B0 P R 0) (.loop (prfBody v.F R.vs R.len R.dst) .ne) (CI P R R.nb) := by
  have h1 := R.nb1
  refine (VP.loop (I := LI P R) (fun n => ?_) (R.nb - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  · by_cases hn : n + 1 ≤ R.nb
    · exact (prfBody_vp (i := R.nb - (n + 1)) v ce (by omega)).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact VP.of_false fun _ _ h => hn h.1
  · refine ⟨by omega, ?_⟩
    rw [show R.nb - (R.nb - 1 + 1) = 0 by omega]; exact h

end

end VG.Proof.RsaPkcs1Enc.X86.Dec
