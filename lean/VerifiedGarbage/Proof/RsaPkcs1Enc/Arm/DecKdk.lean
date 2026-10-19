module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecHash
public import Mathlib.Data.Fintype.Card
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `KDK = HMAC(DH, C)`

HMAC-SHA-256's `init` with the key `DH`, SHA-256's `update` of the inner
state with the ciphertext, and HMAC's `finalize` to `scratch + sKDK`
(`K6`): the key derivation key of the draft's step 3.1 (`kdkV`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem blockKey_length {key : List Byte} (h : key.length ≤ 64) :
    (Spec.Hmac.blockKey Spec.Hmac.sha256 key).length = 64 := by
  have : ¬ 64 < key.length := by omega
  simp only [Spec.Hmac.blockKey, Spec.Hmac.sha256, this, ite_false, List.length_append, List.length_replicate]
  omega

/-- The key derivation key. -/
abbrev kdkV (P : EP) (σ : State) : List Byte := Spec.RsaPkcs1Enc.kdk P.K (dB P σ) (cB P σ)

/-- `K₀` for the key `k`. -/
abbrev k0Of (k : List Byte) : List Byte := Spec.Hmac.blockKey Spec.Hmac.sha256 k

/-- HMAC's states after `init` with the key `k`, and the inner one after
`text`. -/
def Macd (m : Mem) (P : EP) (k text : List Byte) : Prop :=
  Spec.Sha256.Repr m (State.addr P.scr) (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.ipad ++ text) ∧
    Spec.Sha256.Repr m (State.addr (P.scr + BitVec.ofNat 32 sOuter)) (Spec.Hmac.xorPad (k0Of k) Spec.Hmac.opad)

/-- `DH`. -/
abbrev dhV (P : EP) (σ : State) : List Byte := Spec.Sha256.hash (Dfull P σ)

/-! ## The stages -/

/-- Before `init`. -/
def K1 (P : EP) (σ s : State) : Prop :=
  H6 P σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sDH) 32

/-- After `init`. -/
def K2 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) []

/-- Before `update`. -/
def K3 (P : EP) (σ s : State) : Prop := K2 P σ s ∧ UpdArgs s P.scr P.inp P.K 64

/-- After `update`. -/
def K4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Macd s.mem P (dhV P σ) (cB P σ)

/-- Before `finalize`. -/
def K5 (P : EP) (σ s : State) : Prop :=
  K4 P σ s ∧ HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sKDK) (64 + P.K)

/-- `KDK`. -/
def K6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sKDK 32).base 32 = kdkV P σ

/-! ## Memory kept -/

theorem macd_frame {σ : State} (h : In P σ) {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (sc P 0 192).Disjoint r) {k text : List Byte} (hm : Macd m P k text) : Macd m' P k text := by
  have s0 : Region.Sub ⟨State.addr P.scr, 96⟩ (sc P 0 192) := by
    rw [← sc0R]; exact Offset.sub _ (by decide) (by decide)
  have s1 : Region.Sub ⟨State.addr (P.scr + BitVec.ofNat 32 sOuter), 96⟩ (sc P 0 192) := by
    rw [h.scrA (by decide)]; exact Offset.sub _ (by decide) (by decide)
  exact ⟨repr_frame hf (fun r hr => (hd r hr).sub_left s0) hm.1, repr_frame hf (fun r hr => (hd r hr).sub_left s1) hm.2⟩

/-- The calls' stack arguments are in the frame's first 8 bytes. -/
theorem frame8 {s t : State} {va vb : BitVec 32}
    (h : t.mem = (s.mem.writeW (P.lay.fr 0) va).writeW (P.lay.fr 4) vb) :
    Frame [⟨P.lay.fr 0, 8⟩] s.mem t.mem := by
  rw [h]
  refine Frame.sub (rs := [⟨P.lay.fr 0, 4⟩, ⟨P.lay.fr 4, 4⟩]) ?_ fun r hr => ?_
  · exact ((Frame.refl _ _).writeW List.mem_cons_self va (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) vb (Region.contains_self _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩

theorem frame4 {s t : State} {va : BitVec 32} (h : t.mem = s.mem.writeW (P.lay.fr 0) va) :
    Frame [⟨P.lay.fr 0, 4⟩] s.mem t.mem := by
  rw [h]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## The pieces -/

theorem macInitArgs_wp {σ s : State} {key : Nat} (hk : key < 256) {G : State → State → Prop}
    (hs : S P σ s) (hG : ∀ t, P.lay.St σ t → t.mem = s.mem →
      HiArgs t P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 key) 32 → G σ t) :
    WP isa (.block (macInitArgs key)) s (G σ) := by
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_dp (op2_imm (Proof.RsaPkcs1Sig.Arm.encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)))
    fun t4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun t5 u5 => WP.block_nil ?_
  have s5 : P.lay.St σ t5 := ((s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem).of_rest
    (u4.rest (ws := [.r2]) (by simp)) u4.mem).of_rest (u5.rest (ws := [.r3]) (by simp)) u5.mem
  refine hG t5 s5 (by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]) ⟨?_, ?_, ?_, u5.gpr, by decide⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, dpVal, u2.gpr]; rfl
  · rw [u5.other _ (by decide), u4.gpr, dpVal, u3.other _ (by decide), u2.gpr]; rfl

/-- HMAC's `init` with the 32-byte key at `scratch + key`, keeping what `keep`
says of the memory outside HMAC's states and the stack below. -/
theorem macInit_vp {key : Nat} (hk : 192 ≤ key) (hk' : key + 32 ≤ 8448) {F G : State → State → Prop}
    (hF : ∀ σ s, F σ s → S P σ s ∧ HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 key) 32)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 192, P.lay.LOW] s.mem t.mem →
      Macd t.mem P (Spec.Rsa.bytesAt s.mem (sc P key 32).base 32) [] → G σ t) :
    VP F (.call decFns.hiN decFns.hiC) G := by
  refine hashCall hiV (Nat.le_trans hiS (by decide)) (hiRd (P.scr + BitVec.ofNat 32 key) 32)
    (hiWr P.scr (P.scr + BitVec.ofNat 32 sOuter)) (fun σ s h => (hF σ s h).1) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ s h r hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => hi_pub (hF _ _ h₁).2 (hF _ _ h₂).2 (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ha⟩ := hF σ s h
    refine hi_pre ha hs.2.sp (Nat.le_trans (by decide : 1656 ≤ 3440) hs.1.ok.B56)
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_sepW (by omega) (by decide) hk' (by omega))
      (hs.1.sc_sepW (.inl (by simp only [sOuter]; omega)) (by decide) hk' (by decide) (by omega)) (fun r hr => ?_)
      (scr96 hs.1)
      (hs.1.fit_sc (by decide) (by decide)) (hs.1.fit_sc hk' (by omega))
    simp only [hiWr, hiRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) hk' (by omega)
  · have hs := (hF σ s h).1
    have w : Covers (hiWr P.scr (P.scr + BitVec.ofNat 32 sOuter)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs (by decide) (by decide))
    exact ⟨Covers.append_left (Covers.cons (In.scW hs hk' (by omega)).right Covers.nil) w.right, w⟩
  · have hs := (hF σ s h).1
    simp only [hiWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW (by decide) (by decide)
  · obtain ⟨hs, ha⟩ := hF σ s h
    have fr' : Frame [sc P 0 192, P.lay.LOW] s.mem s'.mem := fr.sub fun r hr => by
      simp only [hiWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by rw [sc0R]; exact Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., by rw [hs.1.scrA (by decide)]; exact Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    refine hG σ s s' h st fr' ?_
    have := hi_post ha po
    rw [hs.1.scrA (by omega)] at this
    exact ⟨by rw [List.append_nil]; exact this.1, this.2⟩

/-- What `update` needs of the data, `dl` bytes at `dp`. -/
structure DataOk (P : EP) (s : State) (dp : BitVec 32) (dl : Nat) : Prop where
  cov : Covers [⟨State.addr dp, dl⟩] (s.rd ++ s.wr)
  dS : Region.Disjoint ⟨State.addr P.scr, 96⟩ ⟨State.addr dp, dl⟩
  lo : (lowR P.B 624).Disjoint ⟨State.addr dp, dl⟩
  fit : dp.toNat + dl ≤ 2 ^ 32

/-- SHA-256's `update` of HMAC's inner state, after `init`, with the `dl`
bytes at `dp`. -/
theorem macUpd_vp {dp : BitVec 32} {dl : Nat} {F G : State → State → Prop} {k : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧ UpdArgs s P.scr dp dl 64 ∧ Macd s.mem P (k σ s) [] ∧ DataOk P s dp dl ∧
      (k σ s).length ≤ 64)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 96, P.lay.LOW] s.mem t.mem →
      Macd t.mem P (k σ s) (Spec.Rsa.bytesAt s.mem (State.addr dp) dl) → G σ t) :
    VP F (.call decFns.updN decFns.updC) G := by
  refine hashCall updV (Nat.le_trans updS (by decide)) (updRd P.B dp dl) (updWr P.scr)
    (fun σ s h => (hF σ s h).1) (fun σ s h => ?_) (fun σ s h => ?_)
    (fun σ s h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (hF σ s h).1.1.subW0 (by decide))
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => upd_pub (hF _ _ h₁).2.1 (hF _ _ h₂).2.1
      (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ua, -, dk, -⟩ := hF σ s h
    refine upd_pre ua hs.2.sp (Nat.le_trans (by decide : 624 ≤ 3440) hs.1.ok.B56)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega) dk.dS
      (hs.1.sc0_fr0 (by decide) (by decide)) (fun r hr => ?_) (scr96 hs.1) dk.fit
    simp only [updWr, updRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact dk.lo
    · exact hs.1.lowR_fr (by decide) (by decide)
  · obtain ⟨hs, -, -, dk, -⟩ := hF σ s h
    have w := In.scW0 hs (n := 96) (by decide)
    exact ⟨Covers.append_left (dk.cov.cons (Covers.cons (In.frW hs (n := 8) (by decide)).right Covers.nil))
      w.right, w⟩
  · obtain ⟨hs, ua, md, -, hk⟩ := hF σ s h
    have fr' : Frame [sc P 0 96, P.lay.LOW] s.mem s'.mem := by rw [sc0R]; exact fr
    refine hG σ s s' h st fr' ⟨?_, ?_⟩
    · have := upd_post ua po (iv := Spec.Sha256.H0) (msg := Spec.Hmac.xorPad (k0Of (k σ s)) Spec.Hmac.ipad)
        (by have := md.1; rwa [List.append_nil] at this)
        (by rw [Proof.Hmac.Common.xorPad_length, blockKey_length hk])
      exact this
    · refine repr_frame fr' (fun r hr => ?_) md.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hs.1.scrA (by decide)]; exact sc_sep (.inr (by decide)) (by decide) (by decide)
      · rw [hs.1.scrA (by decide)]; exact (hs.1.low_sc (by decide)).symm

/-- HMAC's `finalize` to the 32 bytes at `scratch + o`. -/
theorem macFin_vp {o tl : Nat} (ho : 192 ≤ o) (ho' : o + 32 ≤ 8448) {F G : State → State → Prop}
    {k text : State → State → List Byte}
    (hF : ∀ σ s, F σ s → S P σ s ∧
      HfArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 o) (64 + tl) ∧
      Macd s.mem P (k σ s) (text σ s) ∧ (k σ s).length ≤ 64 ∧ (text σ s).length = tl)
    (hG : ∀ σ s t, F σ s → P.lay.St σ t → Frame [sc P 0 96, sc P o 32, P.lay.LOW] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (sc P o 32).base 32 = Spec.Hmac.hmac Spec.Hmac.sha256 (k σ s) (text σ s) → G σ t) :
    VP F (.call decFns.hfN decFns.hfC) G := by
  refine hashCall hfV (Nat.le_trans hfS (by decide)) (hfRd P.B (P.scr + BitVec.ofNat 32 sOuter))
    (hfWr P.scr (P.scr + BitVec.ofNat 32 o)) (fun σ s h => (hF σ s h).1) (fun σ s h => ?_)
    (fun σ s h => ?_) (fun σ s h r hr => ?_)
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => hf_pub (hF _ _ h₁).2.1 (hF _ _ h₂).2.1 (by rw [(hF _ _ h₁).1.2.sp, (hF _ _ h₂).1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · obtain ⟨hs, ha, -, -, -⟩ := hF σ s h
    refine hf_pre ha hs.2.sp (Nat.le_trans (by decide : 880 ≤ 3440) hs.1.ok.B56)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega)
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_sepW (by omega) (by decide) ho' (by omega)) (hs.1.sc0_fr0 (by decide) (by decide))
      (hs.1.sc_sepW (.inl (by simp only [sOuter]; omega)) (by decide) ho' (by decide) (by omega))
      (hs.1.sc_fr0 ho' (by omega) (by decide)) (fun r hr => ?_) (scr96 hs.1)
      (hs.1.fit_sc (by decide) (by decide)) (hs.1.fit_sc ho' (by omega))
    simp only [hfWr, hfRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) ho' (by omega)
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := (hF σ s h).1
    have w : Covers (hfWr P.scr (P.scr + BitVec.ofNat 32 o)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs ho' (by omega))
    exact ⟨Covers.append_left ((In.scW hs (by decide) (by decide)).right.cons
      (Covers.cons (In.frW hs (n := 4) (by decide)).right Covers.nil)) w.right, w⟩
  · have hs := (hF σ s h).1
    simp only [hfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW ho' (by omega)
  · obtain ⟨hs, ha, md, hk, ht⟩ := hF σ s h
    have fr' : Frame [sc P 0 96, sc P o 32, P.lay.LOW] s.mem s'.mem := by
      rw [sc0R, show sc P o 32 = ⟨State.addr (P.scr + BitVec.ofNat 32 o), 32⟩ by rw [hs.1.scrA (by omega)]]
      exact fr
    refine hG σ s s' h st fr' ?_
    have := hf_post ha po (blockKey_length hk) (by rw [ht]) md.1 md.2
    rw [hs.1.scrA (by omega)] at this
    exact this

/-! ## `KDK` -/

theorem dhKey {σ s : State} (h : H6 P σ s) :
    Spec.Rsa.bytesAt s.mem (sc P sDH 32).base 32 = dhV P σ := h.2

theorem kdkUpdArgs_wp {σ s : State} (h : K2 P σ s) : WP isa (.block kdkUpdArgs) s (K3 P σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 9) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
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
  refine ⟨⟨hb.frame s8 fr fun r hr => ?_, macd_frame hs.1 fr (fun r hr => ?_) md⟩, ?_, ?_, ?_, ?_, ?_,
    by have := hs.1.k1024; omega, by decide⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.fr_sc (by decide) (by decide)).symm
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, u3.gpr]; rfl
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]; rfl

theorem kdkFinArgs_wp {σ s : State} (h : K4 P σ s) : WP isa (.block kdkFinArgs) s (K5 P σ) := by
  obtain ⟨hb, md⟩ := h
  have hs := hb.1
  have hK := hs.1.k1024
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  have r12 : t1.gpr .r12 = P.B := by rw [u1.gpr, hs.2.sp, BitVec.add_zero]
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  have s3 : P.lay.St σ t3 := s2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  refine s3.wp_strFr (d := 0) (by show 0 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), r12]) fun t4 s4 m4 => ?_
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r1]) (by simp)) u5.mem
  refine s5.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t6 s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = s.mem.writeW (P.lay.fr 0) (t3.gpr .r1) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem, m4.mem, u3.mem, u2.mem, u1.mem]
  have fr := frame4 mm
  have r0v : t2.gpr .r0 = P.scr := by rw [u2.gpr]; rfl
  refine ⟨⟨hb.frame s8 fr fun r hr => ?_, macd_frame hs.1 fr (fun r hr => ?_) md⟩, ?_, ?_, ?_, ?_, ?_,
    by omega⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hs.1.fr_sc (by decide) (by decide)).symm
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), r0v]
  · rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.gpr, dpVal, m4.gpr,
      u3.other _ (by decide), r0v]
  · rw [u8.other _ (by decide), u7.gpr, dpVal, u6.gpr]
    apply BitVec.eq_of_toNat_eq
    simp only [EP.argv, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u3.gpr, dpVal, r0v]

theorem hash_length (x : List Byte) : (Spec.Sha256.hash x).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

theorem K1.of {σ s : State} (h : H6 P σ s)
    (ha : HiArgs s P.scr (P.scr + BitVec.ofNat 32 sOuter) (P.scr + BitVec.ofNat 32 sDH) 32) : K1 P σ s := ⟨h, ha⟩

theorem kdkInit_vp : VP (K1 P) (.call decFns.hiN decFns.hiC) (K2 P) :=
  macInit_vp (key := sDH) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1, h.2⟩) fun σ s t h st fr md => by
    obtain ⟨⟨hb, dh⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, by rw [dh] at md; exact md⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_low

theorem In.dataINP {σ s : State} (hs : S P σ s) : DataOk P s P.inp P.K :=
  { cov := In.roR hs (R := P.INP) (by simp)
    dS := by rw [← sc0R]; exact hs.1.sc_ro (by decide) (R := P.INP) (by simp)
    lo := (hs.1.ok.low_buf (R := P.INP) (.inl (by simp))).sub_left (hs.1.lowR_sub (by decide))
    fit := by have := hs.1.ok.fits P.INP (by simp); simpa [Proof.X25519.Arm.addr_toNat] using this }

theorem kdkUpd_vp : VP (K3 P) (.call decFns.updN decFns.updC) (K4 P) :=
  macUpd_vp (k := fun σ _ => dhV P σ) (fun _ _ h => ⟨h.1.1.1, h.2, h.1.2, In.dataINP h.1.1.1,
    by rw [hash_length]; decide⟩) fun σ s t h st fr md => by
    obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.safe_sc (by decide)
      · exact hs.1.safe_low
    · rw [hs.2.ro (R := P.INP) (by simp)] at md; exact md

theorem kdkV_eq (P : EP) {σ : State} (h : In P σ) :
    kdkV P σ = Spec.Hmac.hmac Spec.Hmac.sha256 (dhV P σ) (cB P σ) := by
  simp only [kdkV, Spec.RsaPkcs1Enc.kdk, dhV, Dfull]
  rw [VG.Proof.RsaPkcs1Enc.i2osp_os2ip_pad _ (by rw [bytesAt_length]; exact h.dlK), bytesAt_length]

theorem kdkFin_vp : VP (K5 P) (.call decFns.hfN decFns.hfC) (K6 P) :=
  macFin_vp (o := sKDK) (tl := P.K) (k := fun σ _ => dhV P σ) (text := fun σ _ => cB P σ) (by decide) (by decide)
    (fun _ _ h => ⟨h.1.1.1, h.2, h.1.2, by rw [hash_length]; decide, bytesAt_length _ _ _⟩)
    fun σ s t h st fr hk => by
    obtain ⟨⟨hb, -⟩, -⟩ := h
    have hs := hb.1
    refine ⟨hb.frame st fr fun r hr => ?_, by rw [hk, kdkV_eq P hs.1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_sc (by decide)
    · exact hs.1.safe_low

end VG.Proof.RsaPkcs1Enc.Arm.Dec
