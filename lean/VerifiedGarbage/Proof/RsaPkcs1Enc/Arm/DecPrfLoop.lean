module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrf
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecTaint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSAES-PKCS1-v1_5 decryption on ARMv7: an IRPRF loop

Block `i` of an IRPRF loop (`body_vp`): its message, HMAC's `init` with
`KDK`, `update` with the message and `finalize` to the block's place, and
the counter; then the loop (`loop_vp`), from block 0 to all `nb` blocks.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Dec

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Decrypt VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg op2_lsl dpVal eval_ne)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.RsaPkcs1Enc (prfBlock)

variable {P : EP} {R : Prf P} {i : Nat}

theorem S_sp {σ₁ σ₂ s₁ s₂ : State} (h₁ : S P σ₁ s₁) (h₂ : S P σ₂ s₂) : s₁.sp = s₂.sp := by
  rw [h₁.2.sp, h₂.2.sp]

/-- A piece no state reaches. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  VP.of_ct (fun _ _ _ _ _ _ _ _ hh => absurd hh.1 (h _ _)) fun σ s hs => absurd hs (h σ s)

theorem hmac_len (k t : List Byte) : (Spec.Hmac.hmac Spec.Hmac.sha256 k t).length = 32 := by
  simp only [Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, Spec.Hmac.sha256]; exact hash_length _

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

theorem kdkV_length {σ : State} : (kdkV P σ).length = 32 := hmac_len _ _

/-! ## What the calls keep -/

namespace In
variable {σ : State} (h : In P σ)
include h

theorem keepI_sc {o n : Nat} (hn : o + n ≤ 8448) (hk : o + n ≤ sKDK ∨ sKDK + 32 ≤ o)
    (hx : o + n ≤ R.xo ∨ R.xo + R.xn ≤ o) (hb : o + n ≤ R.dst ∨ R.dst + 32 * i ≤ o) (hi : i ≤ R.nb) :
    Keep P R i (sc P o n) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (sc P o n) :=
  ⟨h.keep_sc hn hk hx hb hi, h.fr_sc (by simp only [oI, frameBytes]; decide) hn⟩

theorem keepI_low (hi : i ≤ R.nb) : Keep P R i P.lay.LOW ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ P.lay.LOW :=
  ⟨h.keep_low hi, Lay.fr_low (by simp only [oI]; decide)⟩

/-- The states of HMAC. -/
theorem keepI_st {n : Nat} (hn : n ≤ 192) (hi : i ≤ R.nb) :
    Keep P R i (sc P 0 n) ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ (sc P 0 n) :=
  h.keepI_sc (by omega) (.inl (by simp only [sKDK]; omega)) (.inl (by have := R.x_lo; omega))
    (.inl (by have := R.dst_lo; omega)) hi

omit h in
theorem msg_st {n : Nat} (hn : n ≤ 192) : (sc P sMsg R.tl).Disjoint (sc P 0 n) :=
  have : R.tl = R.vs.length + 4 := rfl
  sc_sep (.inr (by simp only [sMsg]; omega)) (by have := R.vs_len; simp only [sMsg]; omega) (by omega)

theorem msg_low : (sc P sMsg R.tl).Disjoint P.lay.LOW :=
  have : R.tl = R.vs.length + 4 := rfl
  (h.low_sc (by have := R.vs_len; simp only [sMsg]; omega)).symm

end In

/-! ## The pieces -/

theorem msgPtr_vp : VP (B0 P R i) (.block msgPtr) (B1 P R i) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => msgPtr_wp h

theorem msg_vp
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r3]) (.block (msgBytes R.vs R.len))
      hc).isSome = true) (hi : i < 256) :
    VP (B1 P R i) (.block (msgBytes R.vs R.len)) (B2 P R i) :=
  VP.taint [.r0, .r1, .r3] cert (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) fun _ _ h => msgBytes_b2 h hi

theorem initArgs_vp : VP (B2 P R i) (.block (macInitArgs sKDK)) (B3 P R i) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.S h₂.1.1.S)
    fun _ _ h => macInitArgs_wp (by decide) h.1.1.S fun t st hm ha =>
      ⟨⟨⟨h.1.1.of_mem st hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2⟩, ha⟩

theorem init_vp : VP (B3 P R i) (.call decFns.hiN decFns.hiC) (B4 P R i) :=
  macInit_vp (key := sKDK) (by decide) (by decide) (fun _ _ h => ⟨h.1.1.1.S, h.2⟩) fun σ s t h st fr md => by
    obtain ⟨hb, -⟩ := h
    have hs := hb.1.1.S
    have hi := hb.1.1.hi
    refine ⟨⟨hb.1.keep st fr fun r hr => ?_, hb.msg_frame fr fun r hr => ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.keepI_st (by decide) hi
      · exact hs.1.keepI_low hi
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact In.msg_st (by decide)
      · exact hs.1.msg_low
    · rw [hb.1.1.kdk] at md; exact md

theorem updArgs_vp : VP (B4 P R i) (.block (prfUpdArgs (R.vs.length + 4))) (B5 P R i) :=
  VP.stk (code := [_, _, _, _, _, _, _]) (by rfl) (by rfl) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.1.S h₂.1.1.1.S)
    fun _ _ h => prfUpdArgs_wp h

theorem upd_vp : VP (B5 P R i) (.call decFns.updN decFns.updC) (B6 P R i) := by
  have hl := R.vs_len
  have htl : R.tl = R.vs.length + 4 := rfl
  refine macUpd_vp (dp := P.scr + BitVec.ofNat 32 sMsg) (dl := R.tl) (k := fun σ _ => kdkV P σ)
    (fun _ _ h => ⟨h.1.1.1.1.S, h.2, h.1.2, h.1.1.1.1.S.1.dataSc h.1.1.1.1.S (by simp only [sMsg]; omega)
      (by decide) (by decide), by rw [kdkV_length]; decide⟩) fun σ s t h st fr md => ?_
  obtain ⟨⟨hb, -⟩, -⟩ := h
  have hs := hb.1.1.S
  have hi := hb.1.1.hi
  have e : Spec.Rsa.bytesAt s.mem (State.addr (P.scr + BitVec.ofNat 32 sMsg)) R.tl = msgV i R.lab R.L := by
    rw [hs.1.scrA (by decide)]; exact hb.2
  rw [e] at md
  refine ⟨hb.1.keep st fr fun r hr => ?_, md⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.keepI_st (by decide) hi
  · exact hs.1.keepI_low hi

theorem finArgs_vp : VP (B6 P R i) (.block (prfFinArgs (R.vs.length + 4) R.dst)) (B7 P R i) :=
  VP.stk (code := [_, _, _, _, _, _, _, _]) (by rfl) (by rfl) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.1.S h₂.1.1.S)
    fun _ _ h => prfFinArgs_wp h

theorem fin_vp (hi : i < R.nb) : VP (B7 P R i) (.call decFns.hfN decFns.hfC) (B8 P R i) := by
  have hd := R.dst_hi
  have hd' := R.dst_lo
  refine macFin_vp (o := R.dst + 32 * i) (tl := R.tl) (k := fun σ _ => kdkV P σ)
    (text := fun _ _ => msgV i R.lab R.L) (by omega) (by omega)
    (fun _ _ h => ⟨h.1.1.1.S, h.2, h.1.2, by rw [kdkV_length]; decide, by rw [msgV_length]; simp⟩)
    fun σ s t h st fr hk => ?_
  obtain ⟨⟨hb, -⟩, -⟩ := h
  have hs := hb.1.S
  have hx := R.x_sep
  have kp : ∀ r ∈ [sc P 0 96, sc P (R.dst + 32 * i) 32, P.lay.LOW],
      Keep P R i r ∧ Region.Disjoint ⟨P.lay.fr oI, 4⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.keepI_st (by decide) hb.1.hi
    · exact hs.1.keepI_sc (by omega) (.inr (by simp only [sKDK]; omega))
        (by rcases hx with hx | hx
            · exact .inr (by omega)
            · exact .inl (by omega)) (.inr (by omega)) hb.1.hi
    · exact hs.1.keepI_low hb.1.hi
  have c := hb.1.keep st fr fun r hr => (kp r hr).1
  refine ⟨⟨by omega, c.base, c.kdk, c.x, c.sNB, ?_⟩, by rw [slot_keep fr fun r hr => (kp r hr).2]; exact hb.2⟩
  rw [show 32 * (i + 1) = 32 * i + 32 by omega, bytesAt_add, c.blk, Offset.add_add, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]
  exact congrArg _ hk

theorem incr_vp : VP (B8 P R i) (.block incr) (B9 P R i) :=
  VP.stk (code := [_, _, _, _]) (by decide) (by decide) (fun _ _ _ _ h₁ h₂ => S_sp h₁.1.S h₂.1.S)
    fun _ _ h => incr_wp h

/-- Before block `nb - m`, `m` blocks left. -/
def LI (P : EP) (R : Prf P) (m : Nat) (σ s : State) : Prop := m ≤ R.nb ∧ B0 P R (R.nb - m) σ s

/-- Whether there is another block, `n` left after this one. -/
theorem cmp_vp {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B9 P R i) (.block [.cmp .r1 (.reg .r2)]) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) := by
  refine VP.taint [.r1, .r2] cmp12_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]) fun σ s h => ?_
  obtain ⟨hc, sI, r1, r2⟩ := h
  have hnb := R.nb_le
  refine wp_cmp (op2_reg _ _) fun t u hz => WP.block_nil ?_
  have st : P.lay.St σ t := hc.S.2.of_rest (u.rest []) u.mem
  have hc' := hc.of_mem st u.mem
  rw [r1, r2, sub_beq_zero (by omega) (by omega)] at hz
  have e : (!decide (i + 1 = R.nb)) = decide (0 < n) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [decide_eq_true (by omega : i + 1 = R.nb), decide_eq_false (by omega : ¬ 0 < n)]; rfl
    · rw [decide_eq_false (by omega : ¬ i + 1 = R.nb), decide_eq_true h0]; rfl
  refine ⟨by rw [eval_ne, hz, e], fun h0 => ?_, fun h0 => ?_⟩
  · rw [show R.nb = i + 1 by omega]; exact hc'
  · refine ⟨by omega, ?_⟩
    rw [show R.nb - n = i + 1 by omega]
    exact ⟨hc', by rw [u.mem]; exact sI⟩

theorem body_vp
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r3]) (.block (msgBytes R.vs R.len))
      hc).isSome = true) {n : Nat} (hn : i + 1 + n = R.nb) :
    VP (B0 P R i) (prfBody decFns R.vs R.len R.dst) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → CI P R R.nb σ s) ∧ (0 < n → LI P R n σ s) := by
  have hnb := R.nb_le
  exact msgPtr_vp.seq ((msg_vp cert (by omega)).seq ((initArgs_vp.seq init_vp).seq ((updArgs_vp.seq upd_vp).seq
    ((finArgs_vp.seq (fin_vp (by omega))).seq (incr_vp.seq (cmp_vp hn))))))

/-- The loop, from block 0. -/
theorem loop_vp
    (cert : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .r3]) (.block (msgBytes R.vs R.len))
      hc).isSome = true) :
    VP (B0 P R 0) (.loop (prfBody decFns R.vs R.len R.dst) .ne) (CI P R R.nb) := by
  have h1 := R.nb1
  refine (VP.loop (I := LI P R) (fun n => ?_) (R.nb - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  · by_cases hn : n + 1 ≤ R.nb
    · exact (body_vp (i := R.nb - (n + 1)) cert (by omega)).mono (fun _ _ h => h.2) fun _ _ h => h
    · exact VP.of_false fun _ _ h => hn h.1
  · refine ⟨by omega, ?_⟩
    rw [show R.nb - (R.nb - 1 + 1) = 0 by omega]; exact h

end VG.Proof.RsaPkcs1Enc.Arm.Dec
