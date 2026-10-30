module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomInRange
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# One draw (32-bit ARM)

`draw` checks that the tape has a complete draw left (status 2 if not),
copies it into the nonce, consumes it, and either accepts it (status 1) or
spends a draw of the budget (status 0 once it is spent): the step of
`Spec.Dsa.Random.sample` (`draw_ok`). The sampler's state is `Smp`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_subs op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Proof.Dsa (maskValue copied copiedList copiedList_length copiedList_getD)

/-! ## The candidate -/

theorem rWidth_eq (s₀ : State) : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ :=
  VG.Proof.Dsa.random_drawBytes_scan _

theorem accepts_candidate {s₀ : State} {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    accepts s₀ (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      decide (0 < Spec.Dsa.Random.candidate (rq s₀) bs ∧ Spec.Dsa.Random.candidate (rq s₀) bs < rq s₀) :=
  VG.Proof.Dsa.accepts_candidate _ hl hpos

/-- The whole nonce, its padding and the candidate's bytes, encodes the candidate. -/
theorem nonce_encodes {s₀ : State} (A : RandomABI s₀) {m : Mem} {bs : List Byte}
    (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀)
    (hpad : ∀ i < (rQBytes s₀).length - rWidth s₀, m (off (rBase s₀) (oNonce + i)) = 0)
    (hc : ∀ i < rWidth s₀, m (off (rBase s₀) (drawPlace s₀ + i)) = copied bs (maskValue (rLead s₀).toNat) i) :
    Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length (Spec.Dsa.Random.candidate (rq s₀) bs) := by
  have hfit := rWidth_le s₀
  have hql := rQBytes_le A
  let cs := copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)
  let pad := (rQBytes s₀).length - rWidth s₀
  let padded := List.replicate pad (0 : Byte) ++ cs
  have hpLen : padded.length = (rQBytes s₀).length := by
    simp only [padded, cs, List.length_append, List.length_replicate, copiedList_length]; omega_arith
  have hpBytes : Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have he : off (rBase s₀) oNonce + BitVec.ofNat 64 i = off (rBase s₀) (oNonce + i) := by
        simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
      rw [he]
      by_cases hip : i < pad
      · rw [hpad i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := cs)
          (i := i) (by simpa only [List.length_replicate] using hip), List.getElem_replicate]
      · have hk : i - pad < rWidth s₀ := by simp only [hpLen] at hj; omega_arith
        rw [show oNonce + i = drawPlace s₀ + (i - pad) by unfold drawPlace; omega_arith, hc _ hk]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := cs) (i := i)
          (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip), List.length_replicate]
        simp only [cs, copiedList, List.getElem_map, List.getElem_range]
  rw [hpBytes, ← hpLen, ← VG.Proof.Dsa.copied_candidate _ hl hpos, ← VG.Proof.Dsa.decode_padding cs pad,
    VG.Proof.Dsa.encodeBE_decodeBE]

/-! ## The sampler's state -/

/-- The sampler's state. -/
structure Smp (s₀ : State) (used draws : Nat) (t : State) : Prop where
  ready : RReady s₀ t
  q : slot t.mem (rBase s₀) oQ = rQ s₀ + BitVec.ofNat 32 ((rQBytes s₀).length - rWidth s₀)
  width : slot t.mem (rBase s₀) oWidth = BitVec.ofNat 32 (rWidth s₀)
  mask : slot t.mem (rBase s₀) oMask = maskValue (rLead s₀).toNat
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 used
  drawsW : slot t.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws
  pad : ∀ i < (rQBytes s₀).length - rWidth s₀, t.mem (off (rBase s₀) (oNonce + i)) = 0
  usedBound : used ≤ (rInput s₀).rand.length

/-- Where the sampler writes. -/
def sampleRanges : List (Nat × Nat) := [(oUsed, 4), (oDraws, 4), (oStatus, 4), (oNonce, 32)]

/-- The slots and bytes a draw changes. -/
abbrev drawRanges (s₀ : State) : List (Nat × Nat) :=
  [(oUsed, 4), (oDraws, 4), (oStatus, 4), (drawPlace s₀, rWidth s₀)]

/-- A memory change apart from the rest of the sampler's state. -/
theorem Smp.of {s₀ t u : State} (A : RandomABI s₀) {used draws used' draws' : Nat}
    (S : Smp s₀ used draws t) (hr : RReady s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = BitVec.ofNat 32 used')
    (hdw : slot u.mem (rBase s₀) oDraws = BitVec.ofNat 32 draws')
    (hub : used' ≤ (rInput s₀).rand.length) : Smp s₀ used' draws' u := by
  have hfit := rWidth_le s₀
  have hql := rQBytes_le A
  have hd : ∀ d, oDraws + 4 ≤ d → d + 4 ≤ oStatus → slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d :=
    fun d h₁ h₂ => slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      unfold oDraws oStatus at *
      rcases hr with rfl | rfl | rfl | rfl
      · right; unfold oUsed; omega_arith
      · right; omega_arith
      · left; omega_arith
      · left; unfold drawPlace oNonce; omega_arith) (by unfold oStatus at h₂; omega_arith)
  refine ⟨hr, (hd _ (by decide) (by decide)).trans S.q, (hd _ (by decide) (by decide)).trans S.width,
    (hd _ (by decide) (by decide)).trans S.mask, hu, hdw, fun i hi => ?_, hub⟩
  rw [hm _ fun r hr => ?_]
  · exact S.pad i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [ofs_off0 _ (by unfold oNonce; omega_arith)]
  rcases hr with rfl | rfl | rfl | rfl
  · right; unfold oUsed oNonce; omega_arith
  · right; unfold oDraws oNonce; omega_arith
  · right; unfold oStatus oNonce; omega_arith
  · left; unfold drawPlace; omega_arith

theorem Smp.congr {s₀ t u : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hr : RReady s₀ u) (hm : Outs (rBase s₀) (drawRanges s₀) t.mem u.mem)
    (hu : slot u.mem (rBase s₀) oUsed = slot t.mem (rBase s₀) oUsed)
    (hdw : slot u.mem (rBase s₀) oDraws = slot t.mem (rBase s₀) oDraws) : Smp s₀ used draws u :=
  S.of A hr hm (hu.trans S.usedW) (hdw.trans S.drawsW) S.usedBound

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- Spend a draw of the budget. -/
theorem drawDec_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) :
    WP isa (.block [ld .r0 oDraws, .subs .r0 .r0 (.imm 1), st .r0 oDraws]) t fun u =>
      Rest [.r0] t u ∧ u.gpr .r0 = BitVec.ofNat 32 (draws - 1) ∧
      u.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) ∧ RReady s₀ u ∧
      u.z = decide (draws - 1 = 0) ∧ Smp s₀ used (draws - 1) u := by
  have h := S.ready
  refine wp_ld h (by decide) fun t₁ u₁ => wp_dec fun t₂ u₂ z₂ =>
    wp_stF ((h.upd u₁).upd u₂) (by decide) fun t₃ m₃ h₃ zz₃ _ => WP.block_nil ?_
  have v₂ : t₂.gpr .r0 = BitVec.ofNat 32 (draws - 1) := by rw [u₂.gpr, u₁.gpr, S.drawsW, ofNat_sub_one hd]
  have hm₃ : t₃.mem = t.mem.writeW (off (rBase s₀) oDraws) (BitVec.ofNat 32 (draws - 1)) := by
    rw [m₃.mem, v₂, u₂.mem, u₁.mem]
  have S₃ : Smp s₀ used (draws - 1) t₃ :=
    S.of A h₃ (by rw [hm₃]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true]))
      (by rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.usedW)
      (by rw [hm₃, slot_write_self]) S.usedBound
  exact ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (m₃.rest _)), by rw [m₃.gpr, v₂], hm₃, h₃,
    by rw [zz₃, z₂, u₁.gpr, S.drawsW, ofNat_sub_one hd, ofNat_beq_zero (by omega_arith)], S₃⟩

/-- Accept, or spend a draw. -/
theorem drawFinish_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hd : 1 ≤ draws) (hdb : draws ≤ 128) {acc : Bool} (hz : t.z = !acc) :
    WP isa drawFinish t fun u => Rest [.r0] t u ∧ RReady s₀ u ∧
      Outs (rBase s₀) [(oDraws, 4), (oStatus, 4)] t.mem u.mem ∧
      (acc → Smp s₀ used draws u ∧ slot u.mem (rBase s₀) oStatus = 1) ∧
      (acc = false → Smp s₀ used (draws - 1) u ∧
        slot u.mem (rBase s₀) oStatus = (if draws - 1 = 0 then 0 else slot t.mem (rBase s₀) oStatus)) := by
  have h := S.ready
  unfold drawFinish
  cases acc with
  | true =>
    refine WP.ite true (by rw [eval_ne, hz]; rfl)
      (fun _ => wp_mov (op2_imm (by decide)) fun t₁ u₁ => ?_) (fun e => Bool.noConfusion e)
    refine wp_st (h.upd u₁) (by decide) fun t₂ m₂ h₂ => WP.block_nil ?_
    have hm : t₂.mem = t.mem.writeW (off (rBase s₀) oStatus) (1 : BitVec 32) := by rw [m₂.mem, u₁.gpr, u₁.mem]
    refine ⟨(u₁.rest (by decide)).trans (m₂.rest _), h₂, by rw [hm]; exact store_outs _ _ _ (by decide),
      fun _ => ⟨S.congr A h₂ ?_ ?_ ?_, ?_⟩, fun e => Bool.noConfusion e⟩
    · rw [hm]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
    · rw [hm, slot_write_self]
  | false =>
    refine WP.ite false (by rw [eval_ne, hz]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    refine WP.seq (WP.mono (drawDec_ok A S hd hdb) fun t₃ ⟨k₃, v₃, hm₃, h₃, z₃, S₃⟩ => ?_)
    by_cases h0 : draws - 1 = 0
    · refine WP.ite true (by rw [eval_eq, z₃, decide_eq_true h0]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine wp_st h₃ (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
      have hm₄ : t₄.mem = t₃.mem.writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := by
        rw [m₄.mem, v₃, h0]; rfl
      refine ⟨k₃.trans (m₄.rest _), h₄, ?_, fun e => Bool.noConfusion e, fun _ => ⟨S₃.congr A h₄ ?_ ?_ ?_, ?_⟩⟩
      · rw [hm₄, hm₃]
        exact (store_outs _ _ _ (by decide)).trans (store_outs _ _ _ (by decide))
      · rw [hm₄]; exact store_outs _ _ _ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      · rw [hm₄, slot_write_self, h0]; rfl
    · refine WP.ite false (by rw [eval_eq, z₃, decide_eq_false h0]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨k₃, h₃, by rw [hm₃]; exact store_outs _ _ _ (by decide), fun e => Bool.noConfusion e,
        fun _ => ⟨S₃, ?_⟩⟩
      rw [hm₃, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]
      simp only [h0, ↓reduceIte]

/-! ## The draw -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs d, n, op2`, and its carry: no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [reduceExec, ho, Option.map_some]) (k _ (Upd.subs _ _ _ _ _) rfl)

/-- `mov d, op2`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', Upd s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [reduceExec, ho, Option.map_some])
    (k _ (Upd.setReg _ _ _) rfl)

/-- `adc d, n, op2`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [reduceExec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

end

/-- The specification's sampling from `used` on, with `draws` draws. -/
abbrev spl (s₀ : State) (draws used : Nat) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (rq s₀) draws ((rInput s₀).rand.drop used)

/-- A sampling `S` that started at `base` is the one from `used` on. -/
structure SampleRel (s₀ : State) (S : Spec.Dsa.Random.Sample) (base used draws : Nat) : Prop where
  scalarEq : S.scalar = (spl s₀ draws used).scalar
  usedEq : base + S.used = used + (spl s₀ draws used).used
  statusEq : VG.Proof.Dsa.Random.sampleStatus S = VG.Proof.Dsa.Random.sampleStatus (spl s₀ draws used)

/-- What a sampling `S` that started at `base` leaves. -/
structure SampleOut (s₀ : State) (base : Nat) (S : Spec.Dsa.Random.Sample) (u : State) : Prop where
  smp : ∃ d, Smp s₀ (base + S.used) d u
  status : slot u.mem (rBase s₀) oStatus = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus S)
  nonce : ∀ k, S.scalar = some k → Spec.Rsa.bytesAt u.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
    Spec.Dsa.encodeBE (rQBytes s₀).length k

theorem sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

abbrev sampleRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7]

/-- The tape's remaining bytes against the width. -/
theorem drawHead_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t) :
    WP isa (.block drawHead) t fun u => Smp s₀ used draws u ∧ u.mem = t.mem ∧
      Rest sampleRegs t u ∧ u.z = decide ((rInput s₀).rand.length - used < rWidth s₀) := by
  have h := S.ready
  have hub := S.usedBound
  have hfit := rWidth_le s₀
  have hql := rQBytes_le A
  have hrl : (rInput s₀).rand.length = (stackArg s₀ 6).toNat := by simp only [rInput, rBytes_length]
  have e6 : stackArg s₀ 6 = BitVec.ofNat 32 (rInput s₀).rand.length := by
    rw [hrl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold drawHead
  refine wp_ldArg A h (j := 6) (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_ld (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ u₄ =>
    wp_subsC (op2_reg _ _) fun t₅ u₅ c₅ => wp_movC (op2_imm (by decide)) fun t₆ u₆ c₆ =>
    wp_adc (op2_imm (by decide)) fun t₇ u₇ => wp_cmp0 fun t₈ f₈ z₈ => WP.block_nil ?_
  have h₈ := ((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).fupd f₈)
  have R : Rest sampleRegs t t₈ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    (f₈.rest _)))))))
  have m₈ : t₈.mem = t.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r0₄ : t₄.gpr .r0 = BitVec.ofNat 32 ((rInput s₀).rand.length - used) := by
    rw [u₄.other _ (by decide), u₃.gpr]
    show t₂.gpr .r0 - t₂.gpr .r7 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, S.usedW, e6, sub_ofNat32 hub (by omega_arith)]
  have r7₄ : t₄.gpr .r7 = BitVec.ofNat 32 (rWidth s₀) := by
    rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, S.width]
  rw [r0₄, r7₄, toNat_imm (by omega_arith), toNat_imm (by omega_arith)] at c₅
  have r0₇ : t₇.gpr .r0 = if decide (rWidth s₀ ≤ (rInput s₀).rand.length - used) then 1 else 0 := by
    rw [u₇.gpr, u₆.gpr, c₆, c₅]
    split <;> rfl
  refine ⟨S.congr A h₈ (by rw [m₈]; exact Outs.refl _ _ _) (by rw [m₈]) (by rw [m₈]), m₈, R, ?_⟩
  rw [z₈, r0₇]
  by_cases hs : (rInput s₀).rand.length - used < rWidth s₀
  · rw [decide_eq_false (by omega_arith), decide_eq_true hs]; rfl
  · rw [decide_eq_true (by omega_arith), decide_eq_false hs]; rfl

/-- Consume a complete draw. -/
theorem drawUsed_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) :
    WP isa (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed]) t
      fun u => Smp s₀ (used + rWidth s₀) draws u ∧
        u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) ∧
        Rest sampleRegs t u := by
  have h := S.ready
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_dp (op2_reg _ _) fun t₃ u₃ => wp_st (((h.upd u₁).upd u₂).upd u₃) (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
  have v₃ : t₃.gpr .r0 = BitVec.ofNat 32 (used + rWidth s₀) := by
    rw [u₃.gpr]
    show t₂.gpr .r0 + t₂.gpr .r7 = _
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.mem, S.usedW, S.width, BitVec.ofNat_add]
  have hm₄ : t₄.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 (used + rWidth s₀)) := by
    rw [m₄.mem, v₃, u₃.mem, u₂.mem, u₁.mem]
  have o₄ : Outs (rBase s₀) [(oUsed, 4)] t.mem t₄.mem := by rw [hm₄]; exact store_outs _ _ _ (by decide)
  exact ⟨S.of A h₄ (o₄.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [drawRanges])
    (by rw [hm₄, slot_write_self]) (by rw [hm₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact S.drawsW)
    hfull, hm₄, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans (m₄.rest _)))⟩

/-- The copy, apart from the rest of the sampler's state. -/
theorem drawCopy_ok {s₀ t : State} (A : RandomABI s₀) {used draws : Nat} (S : Smp s₀ used draws t)
    (hfull : used + rWidth s₀ ≤ (rInput s₀).rand.length) (hw1 : 1 ≤ rWidth s₀) :
    WP isa copy t fun u => Smp s₀ used draws u ∧
      (∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
        copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) ∧
      Outside (rBase s₀) (drawPlace s₀) (rWidth s₀) t.mem u.mem ∧
      Rest sampleRegs t u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  refine WP.mono (copy_ok A S.ready S.usedW S.width S.mask hfull hw1) fun t₄ ⟨h₄, hc₄, ho₄, k₄⟩ => ?_
  have o₄ : Outs (rBase s₀) (drawRanges s₀) t.mem t₄.mem :=
    Outs.of_outside ho₄ (by simp only [drawRanges, List.mem_cons, true_or, or_true])
  have sl₄ : ∀ d, d + 4 ≤ oNonce → slot t₄.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd' =>
    slot_outs (Outs.of_outside ho₄ (List.mem_singleton_self _)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; left; unfold drawPlace; omega_arith) (by unfold oNonce at hd'; omega_arith)
  exact ⟨S.congr A h₄ o₄ (sl₄ _ (by decide)) (sl₄ _ (by decide)), hc₄, ho₄, k₄.mono (by decide)⟩

/-- The nonce's bytes survive the store of `used`. -/
theorem drawUsed_bytes {s₀ : State} (A : RandomABI s₀) {t u : State} {used v : Nat}
    (hm : u.mem = t.mem.writeW (off (rBase s₀) oUsed) (BitVec.ofNat 32 v))
    (hc : ∀ i < rWidth s₀, t.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i) :
    ∀ i < rWidth s₀, u.mem (off (rBase s₀) (drawPlace s₀ + i)) =
      copied (drawBytes s₀ used) (maskValue (rLead s₀).toNat) i := fun i hi => by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have o₇ : Outs (rBase s₀) [(oUsed, 4)] t.mem u.mem := by rw [hm]; exact store_outs _ _ _ (by decide)
  rw [o₇ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [ofs_off0 _ (by unfold drawPlace oNonce; omega_arith)]; right; unfold drawPlace oNonce oUsed; omega_arith]
  exact hc i hi

end VG.Proof.Dsa.Arm
