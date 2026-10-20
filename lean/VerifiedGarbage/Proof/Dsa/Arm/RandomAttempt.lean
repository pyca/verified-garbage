module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomCall
public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
public import VerifiedGarbage.Proof.Dsa.Arm.RandomDraw
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# One signing attempt (32-bit ARM)

`attempt` samples a nonce and, if one is accepted, calls the signer with it
and records its status, spending an attempt on a zero result: a step of
`Spec.Dsa.randomSignLoop` (`attempt_ok`). Between attempts the state is
`Att`, after them `Done`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-! ## Between and after the attempts -/

/-- The spec's signing from `used` on, with `fuel` attempts left, gives the
overall result. -/
abbrev RRel (s₀ : State) (used fuel : Nat) : Prop :=
  VG.Proof.Dsa.RandomSignResultRel (rInput s₀) 0 (rResult s₀) used fuel

/-- Between attempts. -/
structure Att (s₀ : State) (used fuel : Nat) (t : State) : Prop where
  smp : ∃ d, Smp s₀ used d t
  attempts : slot t.mem (rBase s₀) oAttempts = BitVec.ofNat 32 fuel
  saved : Saved s₀ t.mem
  rel : RRel s₀ used fuel

/-- After the attempts. -/
structure Done (s₀ : State) (t : State) : Prop where
  smp : ∃ d, Smp s₀ (rResult s₀).used d t
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
    (rResult s₀).signature.getD (List.replicate (s₀.gpr .r1).toNat 0)
  saved : Saved s₀ t.mem

/-! ## What the call keeps -/

/-- The frame is apart from where the call writes. -/
theorem call_frame_byte {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₂ : d < frameBytes) : m' (off (rBase s₀) d) = m (off (rBase s₀) d) := by
  have hF : frameBytes = 112 := rfl
  rw [rBase_off]
  have hs : (rStack s₀).Contains (off (rLow s₀) (32 + d)) 1 := Offset.contains_base _ (by omega) (by omega)
  refine hf _ fun r hr => ?_
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut _ hs
  · exact A.stackScratch _ hs
  · exact (Offset.disjoint_base (rLow s₀) (d := 32 + d) (n := 1) (k := 32) (by omega) (by omega)) _
      (Region.contains_self _ _)

theorem call_frame_slot {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₂ : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega)

/-- The call keeps the sampler's state. -/
theorem Smp.after_call {s₀ t u : State} (A : RandomABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : RReady s₀ u) (hf : Frame (callWrites s₀) t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, S.usedBound⟩
  · rw [call_frame_slot A hf (by decide)]; exact S.q
  · rw [call_frame_slot A hf (by decide)]; exact S.width
  · rw [call_frame_slot A hf (by decide)]; exact S.mask
  · rw [call_frame_slot A hf (by decide)]; exact S.usedW
  · rw [call_frame_slot A hf (by decide)]; exact S.drawsW
  · rw [call_frame_byte A hf (by unfold oNonce frameBytes; omega)]; exact S.pad i hi

theorem Saved.after_call {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (sv : Saved s₀ m)
    (hf : Frame (callWrites s₀) m m') : Saved s₀ m' :=
  sv.of_slots fun _ _ hd => call_frame_slot A hf hd

/-- Bytes of the frame, after the call. -/
theorem call_frame_bytes {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d n : Nat} (hd : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt m' (off (rBase s₀) d) n = Spec.Rsa.bytesAt m (off (rBase s₀) d) n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
    rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
  exact call_frame_byte A hf (by omega)

/-! ## The status -/

/-- Record the signer's status `st`, and test it. -/
theorem finHead_ok {s₀ u : State} (h : RReady s₀ u) {k : Nat} (hst : k ≤ 1)
    (he : u.gpr .r0 = BitVec.ofNat 32 k) :
    WP isa (.block [st .r0 oStatus, .cmp .r0 (.imm 0)]) u fun v => RReady s₀ v ∧
      Rest [] u v ∧ v.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 k) ∧
      v.z = decide (k = 0) := by
  refine wp_st h (by decide) fun v₁ m₁ h₁ => wp_cmp0 fun v₂ f₂ z₂ => WP.block_nil ?_
  refine ⟨h₁.fupd f₂, (m₁.rest _).trans (f₂.rest _), by rw [f₂.mem, m₁.mem, he], ?_⟩
  rw [z₂, m₁.gpr, he, ofNat_beq_zero (by omega)]

/-- Spend an attempt. -/
theorem finDec_ok {s₀ v₂ : State} (h₂ : RReady s₀ v₂) {f : Nat}
    (ha : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) (hf : f + 1 ≤ 8) :
    WP isa (.block [ld .r0 oAttempts, .subs .r0 .r0 (.imm 1), st .r0 oAttempts]) v₂
      fun v₅ => RReady s₀ v₅ ∧ Rest [.r0] v₂ v₅ ∧
        v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) ∧ v₅.z = decide (f = 0) := by
  refine wp_ld h₂ (by decide) fun v₃ u₃ => wp_dec fun v₄ u₄ z₄ =>
    wp_stF ((h₂.upd u₃).upd u₄) (by decide) fun v₅ m₅ h₅ zz₅ _ => WP.block_nil ?_
  have e₄ : v₄.gpr .r0 = BitVec.ofNat 32 f := by rw [u₄.gpr, u₃.gpr, ha, ofNat_sub_one (by omega)]; rfl
  refine ⟨h₅, (u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (m₅.rest _)), by
    rw [m₅.mem, e₄, u₄.mem, u₃.mem], ?_⟩
  rw [zz₅, z₄, u₃.gpr, ha, ofNat_sub_one (by omega), Nat.add_sub_cancel, ofNat_beq_zero (by omega)]

/-- Record the signer's status `st`, and spend an attempt on a failure. -/
theorem callFinish_ok {s₀ u : State} (h : RReady s₀ u) {k f : Nat} (hst : k ≤ 1)
    (he : u.gpr .r0 = BitVec.ofNat 32 k) (ha : slot u.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1))
    (hf : f + 1 ≤ 8) :
    WP isa callFinish u fun v => RReady s₀ v ∧ Rest [.r0] u v ∧
      Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v.mem ∧
      (k = 1 → slot v.mem (rBase s₀) oStatus = 1 ∧ slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) ∧
      (k = 0 → slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 f ∧
        slot v.mem (rBase s₀) oStatus = (if f = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (finHead_ok h hst he) fun v₂ ⟨h₂, k₂, m₂, z₂⟩ => ?_)
  have o₂ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₂.mem := by
    rw [m₂]; exact store_outs _ _ _ (by decide)
  by_cases h0 : k = 0
  · subst h0
    refine WP.ite true (by rw [eval_eq, z₂]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e)
    have ha₂ : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha
    refine WP.seq (WP.mono (finDec_ok h₂ ha₂ hf) fun v₅ ⟨h₅, k₅', hm₅, z₅⟩ => ?_)
    have k₅ : Rest [.r0] u v₅ := (k₂.mono (by decide)).trans k₅'
    have o₅ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₅.mem := by
      rw [hm₅]; exact o₂.trans (store_outs _ _ _ (by decide))
    by_cases hf0 : f = 0
    · refine WP.ite false (by rw [eval_ne, z₅, decide_eq_true hf0]; rfl)
        (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨h₅, k₅, o₅, fun e => absurd e (by decide), fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₅, slot_write_self]
      · rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide), m₂, slot_write_self, hf0]; rfl
    · refine WP.ite true (by rw [eval_ne, z₅, decide_eq_false hf0]; rfl)
        (fun _ => wp_mov (op2_imm (by decide)) fun v₆ u₆ => wp_st (h₅.upd u₆) (by decide)
          fun v₇ m₇ h₇ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      have hm₇ : v₇.mem = v₅.mem.writeW (off (rBase s₀) oStatus) (4 : BitVec 32) := by
        rw [m₇.mem, u₆.gpr, u₆.mem]
      refine ⟨h₇, k₅.trans ((u₆.rest (by decide)).trans (m₇.rest _)),
        by rw [hm₇]; exact o₅.trans (store_outs _ _ _ (by decide)), fun e => absurd e (by decide),
        fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide), hm₅, slot_write_self]
      · rw [hm₇, slot_write_self]; simp only [hf0, ↓reduceIte]
  · have h1 : k = 1 := by omega
    subst h1
    refine WP.ite false (by rw [eval_eq, z₂]; rfl) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
    refine ⟨h₂, k₂.mono (by decide), o₂, fun _ => ⟨?_, ?_⟩, fun e => absurd e (by decide)⟩
    · rw [m₂, slot_write_self]; rfl
    · rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha

/-- Slot stores keep the sampler's state. -/
theorem Smp.after_finish {s₀ t u : State} (A : RandomABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : RReady s₀ u) (hm : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hs : ∀ d, d ≤ 112 → (d + 4 ≤ oAttempts ∨ oAttempts + 4 ≤ d) → (d + 4 ≤ oStatus ∨ oStatus + 4 ≤ d) →
      slot u.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d h₀ h₁ h₂ =>
    slot_outs hm (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂) (by omega)
  refine ⟨hr, (hs _ (by decide) (by decide) (by decide)).trans S.q,
    (hs _ (by decide) (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  have hle : ∀ r ∈ ([(oAttempts, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
  rw [hm _ fun r hr => by
    have := hle r hr
    rw [ofs_off0 _ (by unfold oNonce; omega)]
    right; omega]
  exact S.pad i hi

/-- Stores to the frame keep bytes apart from the stack. -/
theorem frameOuts_bytes {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (hm : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ frameBytes) {p : Addr} {n : Nat}
    (hd : (rStack s₀).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  refine hm _ fun r hr => ?_
  have hb := hrs r hr
  unfold frameBytes at hb
  by_cases hx : ofs (rBase s₀) (p + BitVec.ofNat 64 i) < 112
  · exfalso
    refine hd _ ?_ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega))
    have he : p + BitVec.ofNat 64 i = off (rBase s₀) (ofs (rBase s₀) (p + BitVec.ofNat 64 i)) := by
      simp only [ofs, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm (rBase s₀), BitVec.sub_add_cancel]
    rw [he, rBase_off]
    exact Offset.contains_base _ (by omega) (by omega)
  · right; omega

/-- The key's bytes, while the frame is allocated. -/
theorem callKey {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) :
    Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-- The signer's input is the specification's, with the sampled nonce. -/
theorem callResult_eq {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length k) :
    callResult s₀ t = Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest := by
  have hqn := rQBytes_length A
  have hkey := callKey A h
  have hdig : Spec.Rsa.bytesAt t.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat = (rInput s₀).digest := by
    refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.stackDigest.symm
    · exact A.outDigest.symm
    · exact A.digestScratch
    · exact A.usedDigest.symm
  have hnon : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat =
      Spec.Dsa.encodeBE (rInput s₀).qLen k := by
    rw [← hqn, hn, hqn]; rfl
  unfold callResult
  rw [hkey, hdig, hnon]; rfl

/-- Slots below the ranges that changed. -/
theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

theorem one_beq {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 1 == 0) = decide (k = 1) := by
  by_cases h : k = 1
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega

/-- What an attempt from `used` with `f + 1` attempts left leaves: another
attempt to make after a retry, which its signing trace records, or the result. -/
def AttemptOut (s₀ : State) (used f : Nat) (u : State) : Prop :=
  (slot u.mem (rBase s₀) oStatus = 4 ∧ 1 ≤ f ∧ Att s₀ (used + (spl s₀ 128 used).used) f u ∧
    VG.Proof.Dsa.randomSigningTrace (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace =
      6 :: (VG.Proof.Dsa.randomSignRemaining (rInput s₀) (used + (spl s₀ 128 used).used) f).trace) ∨
    (slot u.mem (rBase s₀) oStatus ≠ 4 ∧ Done s₀ u ∧
      ¬ ((VG.Proof.Dsa.randomSigningTrace
        (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace).head? = some 6 ∧ 1 ≤ f))

theorem attempt_ok (name : String) {s₀ t : State} (A : RandomABI s₀) {used f : Nat}
    (T : Att s₀ used (f + 1) t) (hf : f + 1 ≤ 8) (hq : 1 < rq s₀) :
    WP isa (attempt name (Entry.operation true)) t fun u => AttemptOut s₀ used f u := by
  have hql := rQBytes_le A
  obtain ⟨d₀, Sm⟩ := T.smp
  unfold attempt
  refine WP.seq (WP.mono (sample_ok A Sm hq) fun u₁ ⟨O, r0₁, h₁, o₁, _⟩ => ?_)
  have sv₁ : Saved s₀ u₁.mem := T.saved.of_outs o₁ (by decide)
  have at₁ : slot u₁.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) :=
    (slot_outs o₁ (by decide) (by decide)).trans T.attempts
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u₂ fv₂ z₂ => WP.block_nil ?_)
  have h₂ := h₁.fupd fv₂
  have m₂ : u₂.mem = u₁.mem := fv₂.mem
  have hle := sampleStatus_le (spl s₀ 128 used)
  rw [r0₁, one_beq (by omega)] at z₂
  cases hsc : (spl s₀ 128 used).scalar with
  | none =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]; split <;> simp
    refine WP.ite false (by rw [eval_eq, z₂, decide_eq_false hst]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    obtain ⟨-, hstat, hused⟩ := T.rel.sample_none hsc
    obtain ⟨d', S'⟩ := O.smp
    refine .inr ⟨?_, ⟨⟨d', ?_⟩, ?_, fun e => absurd (hstat ▸ e) hst, (by rw [m₂]; exact sv₁)⟩,
      by rw [VG.Proof.Dsa.random_sign_trace_none _ _ _ hsc]; simp⟩
    · rw [m₂, O.status]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_imm (by omega)] at this
      exact absurd this (by show _ ≠ 4; omega)
    · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
      rw [e]; exact S'.mem A h₂ m₂
    · rw [m₂, O.status]; exact congrArg (BitVec.ofNat 32) hstat.symm
  | some k =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]
    refine WP.ite true (by rw [eval_eq, z₂, decide_eq_true hst]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    obtain ⟨d', S'⟩ := O.smp
    have S₂ := S'.mem A h₂ m₂
    refine WP.seq (WP.mono (callArgs_ok A h₂ (by rw [m₂]; exact sv₁)) fun u₃ ⟨h₃, m₃, C₃, _⟩ => ?_)
    have hk : Spec.Rsa.bytesAt u₃.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
        Spec.Dsa.encodeBE (rQBytes s₀).length k := by
      rw [m₃, m₂]; exact O.nonce k hsc
    have hres := callResult_eq A h₃ hk
    refine WP.seq (WP.mono (callSigner_ok A h₃ C₃ name) fun u₄ ⟨h₄, f₄, _, r0₄, out₄⟩ => ?_)
    have at₄ : slot u₄.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [call_frame_slot A f₄ (by decide), m₃, m₂]; exact at₁
    have S₄ := (S₂.mem A h₃ m₃).after_call A h₄ f₄
    have sv₄ : Saved s₀ u₄.mem := Saved.after_call A (by rw [m₃, m₂]; exact sv₁) f₄
    rw [hres] at r0₄ out₄
    refine WP.mono (callFinish_ok h₄ (Nat.le_of_lt_succ (status_lt _)) r0₄ at₄ hf)
      fun u₅ ⟨h₅, _, o₅, hT1, hT0⟩ => ?_
    have S₅ := S₄.after_finish A h₅ o₅
    have sv₅ : Saved s₀ u₅.mem := sv₄.of_outs o₅ (by decide)
    cases hsb : Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest with
    | some sig =>
      obtain ⟨st₅, -⟩ := hT1 (by rw [hsb]; rfl)
      obtain ⟨hsig, hstat, hused⟩ := T.rel.success hsc hsb
      refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun _ => ?_, sv₅⟩,
        by rw [VG.Proof.Dsa.random_sign_trace_success _ _ _ _ hsc hsb]; simp⟩
      · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · rw [frameOuts_bytes o₅ (by decide) A.stackOut (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _)
          (by decide))), out₄, hsb, hsig]
    | none =>
      obtain ⟨at₅, st₅⟩ := hT0 (by rw [hsb]; rfl)
      have R' := T.rel.retry hsc hsb
      by_cases hf0 : f = 0
      · subst hf0
        obtain ⟨-, hstat, hused⟩ := R'.exhausted
        refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun e => absurd e (by omega), sv₅⟩,
          fun h => absurd h.2 (by decide)⟩
        have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · refine .inl ⟨by rw [st₅]; simp only [hf0, ↓reduceIte], by omega, ⟨⟨d', S₅⟩, at₅, sv₅, R'⟩,
          ?_⟩
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
        exact VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hsc hsb

end VG.Proof.Dsa.Arm
