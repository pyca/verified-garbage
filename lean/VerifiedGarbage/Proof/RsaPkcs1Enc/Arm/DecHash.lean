module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.HashCalls
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecFns
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: `DH = SHA256(D)`

SHA-256's `init`, `update` with `D` and `finalize` to `scratch + sDH`, each
after the block of its arguments (`hashD_vp`): `DH`, the SHA-256 digest of
`D` (`H6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

/-- A stack argument of a call, in the frame's word `4 i`. -/
theorem stackArg_fr {σ s : State} (hs : S P σ s) {i : Nat} (hi : i < 16) :
    stackArg s i = s.mem.readW (P.lay.fr (4 * i)) 32 := by
  simp only [stackArg, stackArgAddr, hs.2.sp]
  rw [hs.1.ok.addrB (by show 4 * i < frameBytes + 56 + 76; simp only [frameBytes]; omega)]

theorem stackArgAddr_B {σ s : State} (hs : S P σ s) : stackArgAddr s 0 = State.addr P.B := by
  simp [stackArgAddr, hs.2.sp]

/-- The bytes of a region of `scratch` kept while memory changes in the frame. -/
theorem sc_keep_fr {σ : State} (h : In P σ) {m m' : Mem} {d k o n : Nat} (hd : d + k ≤ frameBytes)
    (hn : o + n ≤ 8448) (hf : Frame [⟨P.lay.fr d, k⟩] m m') :
    Spec.Rsa.bytesAt m' (sc P o n).base n = Spec.Rsa.bytesAt m (sc P o n).base n :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.fr_sc (by show d + k ≤ frameBytes + 56; omega) hn).symm) (by omega)

theorem repr_keep_fr {σ : State} (h : In P σ) {m m' : Mem} {d k o : Nat} (hd : d + k ≤ frameBytes)
    (ho : o + 96 ≤ 8448) (hf : Frame [⟨P.lay.fr d, k⟩] m m') {msg : List Byte}
    (hr : Spec.Sha256.Repr m (sc P o 96).base msg) : Spec.Sha256.Repr m' (sc P o 96).base msg :=
  repr_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.fr_sc (by show d + k ≤ frameBytes + 56; omega) ho).symm) hr

theorem sc0 (P : EP) : (sc P 0 96).base = State.addr P.scr := BitVec.add_zero _

theorem sc0R (P : EP) (n : Nat) : sc P 0 n = ⟨State.addr P.scr, n⟩ := by simp [sc]

/-! ## The stages -/

/-- Before `init`. -/
def H1 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ s.gpr .r0 = P.scr

/-- After `init`. -/
def H2 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ Spec.Sha256.Repr s.mem (sc P 0 96).base []

/-- Before `update`. -/
def H3 (P : EP) (σ s : State) : Prop :=
  H2 P σ s ∧ UpdArgs s P.scr (P.scr + BitVec.ofNat 32 sD) P.K 0

/-- After `update`. -/
def H4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Sha256.Repr s.mem (sc P 0 96).base (Dfull P σ)

/-- Before `finalize`. -/
def H5 (P : EP) (σ s : State) : Prop := H4 P σ s ∧ FinArgs s P.scr (P.scr + BitVec.ofNat 32 sDH) P.K

/-- `DH`. -/
def H6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sc P sDH 32).base 32 = Spec.Sha256.hash (Dfull P σ)

theorem shaInitArgs_wp {σ s : State} (h : D4 P σ s) : WP isa (.block shaInitArgs) s (H1 P σ) := by
  have hs := h.1.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 21) (by simp) (by dsimp only; decide) fun t2 s2 u2 => WP.block_nil ⟨?_, ?_⟩
  · have mm : t2.mem = s.mem := by rw [u2.mem, u1.mem]
    obtain ⟨⟨_, rc, pr, sl⟩, dd⟩ := h
    exact ⟨⟨⟨hs.1, s2⟩, rc, by rw [Priv, mm]; exact pr, by rw [mm]; exact sl⟩, by rw [mm]; exact dd⟩
  · rw [u2.gpr]; rfl

theorem scr96 {σ : State} (h : In P σ) : (P.scr.toNat + 96 ≤ 2 ^ 32) := by
  have := h.scr_fit; have := h.sl8; omega

theorem shaInit_vp : VP (H1 P) (.call decFns.initN decFns.initC) (H2 P) := by
  refine hashCall initV (Nat.le_trans initS (by decide)) [] [⟨State.addr P.scr, 96⟩] (fun _ _ h => h.1.1.1)
    (fun _ s h => shInit_pre h.2 (scr96 h.1.1.1.1)) (fun _ s h => ?_)
    (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.1.1.subW0 (by decide))
    (fun _ _ _ _ h₁ h₂ => shInit_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have w := In.scW0 h.1.1.1 (n := 96) (by decide)
    exact ⟨w.right, w⟩
  · obtain ⟨⟨hb, dd⟩, hr0⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨⟨hb.after st fr fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.subW0 (by decide)
    · rw [← dd]
      refine bytesAt_frame fr (fun r hr => ?_) (by omega)
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := sc_sep (P := P) (o := sD) (n := P.K) (o' := 0) (n' := 96) (by simp only [sD]; omega)
          (by simp only [sD]; omega) (by decide)
        rwa [sc0R] at this
      · exact (hs.1.low_sc (by simp only [sD]; omega)).symm
    · rw [sc0]; exact shInit_post hr0 po
theorem In.lowR_sub {σ : State} (_h : In P σ) {S : Nat} (hS : S ≤ 3440) :
    Region.Sub (lowR P.B S) P.lay.LOW :=
  Offset.sub_below _ (by show S ≤ 3440; omega) (by show 3440 - S + S ≤ 3440; omega)

theorem In.lowR_sc {σ : State} (h : In P σ) {S o n : Nat} (hS : S ≤ 3440) (hn : o + n ≤ 8448) (ho : o < 8448) :
    (lowR P.B S).Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ := by
  rw [h.scrA ho]; exact (h.low_sc hn).sub_left (h.lowR_sub hS)

theorem In.lowR_sc0 {σ : State} (h : In P σ) {S n : Nat} (hS : S ≤ 3440) (hn : n ≤ 8448) :
    (lowR P.B S).Disjoint ⟨State.addr P.scr, n⟩ := by
  rw [← sc0R]; exact (h.low_sc (by omega)).sub_left (h.lowR_sub hS)

theorem In.lowR_fr {σ : State} (h : In P σ) {S n : Nat} (hS : S ≤ 3440) (hn : n ≤ frameBytes) :
    (lowR P.B S).Disjoint ⟨State.addr P.B, n⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0]; exact (Lay.fr_low (by simp only [frameBytes] at hn; omega)).symm.sub_left (h.lowR_sub hS)

theorem In.sc_fr0 {σ : State} (h : In P σ) {o n k : Nat} (hn : o + n ≤ 8448) (ho : o < 8448) (hk : k ≤ frameBytes) :
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ ⟨State.addr P.B, k⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0, h.scrA ho]; exact (h.fr_sc (by show 0 + k ≤ frameBytes + 56; omega) hn).symm

theorem In.sc0_fr0 {σ : State} (h : In P σ) {n k : Nat} (hn : n ≤ 8448) (hk : k ≤ frameBytes) :
    Region.Disjoint ⟨State.addr P.scr, n⟩ ⟨State.addr P.B, k⟩ := by
  have q0 : State.addr P.B = P.lay.fr 0 := by simp
  rw [q0, ← sc0R]; exact (h.fr_sc (by show 0 + k ≤ frameBytes + 56; omega) (by omega)).symm

theorem In.sc_sepW {σ : State} (h : In P σ) {o n o' n' : Nat} (hs : o + n ≤ o' ∨ o' + n' ≤ o)
    (h₁ : o + n ≤ 8448) (h₂ : o' + n' ≤ 8448) (ho : o < 8448) (ho' : o' < 8448) :
    Region.Disjoint ⟨State.addr (P.scr + BitVec.ofNat 32 o), n⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 o'), n'⟩ := by
  rw [h.scrA ho, h.scrA ho']; exact sc_sep hs h₁ h₂

theorem In.sc0_sepW {σ : State} (h : In P σ) {n o' n' : Nat} (hs : n ≤ o') (h₁ : n ≤ 8448)
    (h₂ : o' + n' ≤ 8448) (ho' : o' < 8448) :
    Region.Disjoint ⟨State.addr P.scr, n⟩ ⟨State.addr (P.scr + BitVec.ofNat 32 o'), n'⟩ := by
  rw [← sc0R, h.scrA ho']; exact sc_sep (.inl (by omega)) (by omega) h₂

theorem shaUpdArgs_wp {σ s : State} (h : H2 P σ s) : WP isa (.block shaUpdArgs) s (H3 P σ) := by
  obtain ⟨⟨hb, dd⟩, rp⟩ := h
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
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine s5.wp_strFr (d := 4) (by show 4 + 4 ≤ frameBytes; decide) (by decide)
    (by rw [u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.other _ (by decide), r12])
    fun t6 s6 m6 => ?_
  refine wp_mov (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun t8 u8 => WP.block_nil ?_
  have s8 : P.lay.St σ t8 := (s6.of_rest (u7.rest (ws := [.r2]) (by simp)) u7.mem).of_rest
    (u8.rest (ws := [.r3]) (by simp)) u8.mem
  have mm : t8.mem = (t1.mem.writeW (P.lay.fr 0) (t3.gpr .r1)).writeW (P.lay.fr 4) (t5.gpr .r1) := by
    rw [u8.mem, u7.mem, m6.mem, u5.mem, m4.mem, u3.mem, u2.mem]
  have fr : Frame [⟨P.lay.fr 0, 8⟩] s.mem t8.mem := by
    rw [mm, u1.mem]
    refine Frame.sub (rs := [⟨P.lay.fr 0, 4⟩, ⟨P.lay.fr 4, 4⟩]) ?_ fun r hr => ?_
    · exact ((Frame.refl _ _).writeW List.mem_cons_self (t3.gpr .r1) (Region.contains_self _ _)).writeW
        (List.mem_cons_of_mem _ List.mem_cons_self) (t5.gpr .r1) (Region.contains_self _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have r1v : t3.gpr .r1 = P.scr + BitVec.ofNat 32 sD := by rw [u3.gpr, dpVal, u2.gpr]; rfl
  refine ⟨⟨⟨hb.frame s8 fr fun r hr => ?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, by have := hs.1.k64; omega, by decide⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · rw [sc_keep_fr hs.1 (by decide) (by simp only [sD]; omega) fr]; exact dd
  · exact repr_keep_fr hs.1 (by decide) (by decide) fr rp
  · rw [u8.other _ (by decide), u7.other _ (by decide), m6.gpr, u5.other _ (by decide), m4.gpr,
      u3.other _ (by decide), u2.gpr]; rfl
  · rw [u8.other _ (by decide), u7.gpr]
  · exact u8.gpr
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Lay.readW_fr_other _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, r1v]
  · rw [stackArg_fr ⟨hs.1, s8⟩ (by decide), mm, Mem.readW_writeW_self32, u5.gpr]; rfl

theorem shaUpd_vp : VP (H3 P) (.call decFns.updN decFns.updC) (H4 P) := by
  refine hashCall updV (Nat.le_trans updS (by decide)) (updRd P.B (P.scr + BitVec.ofNat 32 sD) P.K)
    (updWr P.scr) (fun _ _ h => h.1.1.1.1) (fun _ s h => ?_) (fun _ s h => ?_)
    (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.1.1.1.1.1.subW0 (by decide))
    (fun _ _ _ _ h₁ h₂ => upd_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.1.2.sp, h₂.1.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have hs := h.1.1.1.1
    have hK := hs.1.k1024
    have q0 : State.addr P.B = P.lay.fr 0 := by simp
    refine upd_pre h.2 hs.2.sp (by have := hs.1.ok.B56; simp only at this; omega)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega)
      (hs.1.sc0_sepW (by decide) (by decide) (by simp only [sD]; omega) (by decide))
      (hs.1.sc0_fr0 (by decide) (by decide)) (fun r hr => ?_) (scr96 hs.1)
      (hs.1.fit_sc (by simp only [sD]; omega) (by decide))
    simp only [updWr, updRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by simp only [sD]; omega) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := h.1.1.1.1
    have hK := hs.1.k1024
    have w := In.scW0 hs (n := 96) (by decide)
    refine ⟨Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) w.right, w⟩
    · exact (In.scW hs (by simp only [sD]; omega) (by decide)).right
    · exact (In.frW hs (n := 8) (by decide)).right
  · obtain ⟨⟨⟨hb, dd⟩, rp⟩, ua⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨hb.after st fr fun r hr => ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.subW0 (by decide)
    · have := upd_post ua po (iv := Spec.Sha256.H0) (msg := []) (by rw [← sc0]; exact rp) rfl
      rw [hs.1.scrA (by decide), show State.addr P.scr + BitVec.ofNat 64 sD = (sc P sD P.K).base from rfl, dd,
        List.nil_append] at this
      rw [sc0]; exact this

theorem shaFinArgs_wp {σ s : State} (h : H4 P σ s) : WP isa (.block shaFinArgs) s (H5 P σ) := by
  obtain ⟨hb, rp⟩ := h
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
  refine s4.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun t6 u6 => WP.block_nil ?_
  have s6 : P.lay.St σ t6 := s5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem
  have mm : t6.mem = t1.mem.writeW (P.lay.fr 0) (t3.gpr .r1) := by rw [u6.mem, u5.mem, m4.mem, u3.mem, u2.mem]
  have fr : Frame [⟨P.lay.fr 0, 4⟩] s.mem t6.mem := by
    rw [mm, u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨⟨hb.frame s6 fr fun r hr => ?_, repr_keep_fr hs.1 (by decide) (by decide) fr rp⟩, ?_, ?_, ?_, ?_, by omega⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hs.1.safe_fr (by decide) (by simp only [oR]; decide)
  · rw [u6.other _ (by decide), u5.other _ (by decide), m4.gpr, u3.other _ (by decide), u2.gpr]; rfl
  · rw [u6.other _ (by decide), u5.gpr]; rfl
  · exact u6.gpr
  · rw [stackArg_fr ⟨hs.1, s6⟩ (by decide), mm, Mem.readW_writeW_self32, u3.gpr, dpVal, u2.gpr]; rfl

theorem shaFin_vp : VP (H5 P) (.call decFns.finN decFns.finC) (H6 P) := by
  refine hashCall finV (Nat.le_trans finS (by decide)) (finRd P.B)
    (finWr P.scr (P.scr + BitVec.ofNat 32 sDH)) (fun _ _ h => h.1.1.1) (fun _ s h => ?_) (fun _ s h => ?_)
    (fun _ _ h r hr => ?_)
    (fun _ _ _ _ h₁ h₂ => fin_pub h₁.2 h₂.2 (by rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp]) _ _)
    (fun σ s s' h st fr _ po => ?_)
  · have hs := h.1.1.1
    have hK := hs.1.k1024
    refine fin_pre h.2 hs.2.sp (by have := hs.1.ok.B56; simp only at this; omega)
      (by have := hs.1.ok.fit; simp only [frameBytes] at this; omega)
      (hs.1.sc0_sepW (by decide) (by decide) (by decide) (by decide))
      (hs.1.sc0_fr0 (by decide) (by decide)) (hs.1.sc_fr0 (by decide) (by decide) (by decide))
      (fun r hr => ?_) (scr96 hs.1) (hs.1.fit_sc (by decide) (by decide))
    simp only [finWr, finRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.lowR_sc0 (by decide) (by decide)
    · exact hs.1.lowR_sc (by decide) (by decide) (by decide)
    · exact hs.1.lowR_fr (by decide) (by decide)
  · have hs := h.1.1.1
    have w : Covers (finWr P.scr (P.scr + BitVec.ofNat 32 sDH)) s.wr :=
      (In.scW0 hs (n := 96) (by decide)).cons (In.scW hs (by decide) (by decide))
    exact ⟨Covers.append_left (Covers.cons (In.frW hs (n := 4) (by decide)).right Covers.nil) w.right, w⟩
  · have hs := h.1.1.1
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.subW0 (by decide)
    · exact hs.1.subW (by decide) (by decide)
  · obtain ⟨⟨hb, rp⟩, fa⟩ := h
    have hs := hb.1
    have hK := hs.1.k1024
    refine ⟨hb.after st fr fun r hr => ?_, ?_⟩
    · simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.subW0 (by decide)
      · exact hs.1.subW (by decide) (by decide)
    · have hl : (Dfull P σ).length = P.K := by simp [bytesAt_length]; have := hs.1.dlK; omega
      have := fin_post fa po (iv := Spec.Sha256.H0) (by rw [← sc0]; exact rp) hl
      rw [hs.1.scrA (by decide)] at this
      exact this

end VG.Proof.RsaPkcs1Enc.Arm.Dec
