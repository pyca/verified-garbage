module

public import VerifiedGarbage.Proof.Dsa.X86.RandomAttemptState
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# One signing attempt (x86)

`attempt` samples a nonce and, if one is accepted, calls the signer with it
(`call_ok`): a signature ends the attempts, a failure spends one. As the
specification's `randomSignLoop` does (`RandomSignResultRel`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

/-- Record the signer's status `st`, and test it. -/
theorem finHead_ok {s₀ u : State} (h : Ready s₀ u) {st : Nat} (hst : st ≤ 1)
    (he : u.gpr .eax = BitVec.ofNat 32 st) :
    WP isa (.block [.store (sp oStatus) .eax, .alu .cmp .eax (.imm 0)]) u fun v => Ready s₀ v ∧
      Keeps [.eax] u v ∧ v.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 st) ∧
      v.zf = some (decide (st = 0)) := by
  refine wp_slot h.rf (by decide) he fun v₁ f₁ m₁ g₁ r₁ w₁ _ _ => wp_cmpi fun v₂ fv₂ _ z₂ => WP.block_nil ?_
  have k₂ : Keeps [.eax] u v₂ := Keeps.trans (⟨fun r _ => by rw [g₁], r₁, w₁⟩ : Keeps [.eax] u v₁) (fv₂.keeps _)
  have m₂ : v₂.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 st) := by rw [fv₂.mem, m₁]
  have h₂ : Ready s₀ v₂ := h.congr k₂ (by rw [m₂]; exact frame_store s₀ _ (by decide) _)
  rw [g₁, he, show (BitVec.ofNat 32 st - 0 : BitVec 32) = BitVec.ofNat 32 st - BitVec.ofNat 32 0 from rfl,
    sub_beq (by omega) (by decide)] at z₂
  exact ⟨h₂, k₂, m₂, z₂⟩

/-- Spend an attempt. -/
theorem finDec_ok {s₀ v₂ : State} (h₂ : Ready s₀ v₂) {f : Nat}
    (ha : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) (hf : f + 1 ≤ 8) :
    WP isa (.block [.mov .eax (.mem (sp oAttempts)), .alu .sub .eax (.imm 1), .store (sp oAttempts) .eax]) v₂
      fun v₅ => Ready s₀ v₅ ∧ Keeps [.eax] v₂ v₅ ∧
        v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) ∧ v₅.zf = some (decide (f = 0)) := by
  refine wp_movS (v := BitVec.ofNat 32 (f + 1)) (by rw [h₂.rf.readSlot (by decide)]; exact congrArg some ha)
    fun v₃ u₃ _ => wp_subi fun v₄ u₄ _ z₄ => ?_
  have e₄ : v₄.gpr .eax = BitVec.ofNat 32 f := by
    rw [u₄.gpr, u₃.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have f₄ := h₂.rf.of_keeps ((u₃.keeps.mono (by decide)).trans u₄.keeps)
  refine wp_slot f₄ (by decide) e₄ fun v₅ f₅ m₅ g₅ r₅ w₅ zf₅ _ => WP.block_nil ?_
  have k₅ : Keeps [.eax] v₂ v₅ := ((u₃.keeps.mono (by decide)).trans u₄.keeps).trans
    ⟨fun r _ => by rw [g₅], r₅, w₅⟩
  have hm₅ : v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) := by
    rw [m₅, u₄.mem, u₃.mem]
  have h₅ : Ready s₀ v₅ := h₂.congr (rs := [.eax]) ((u₃.keeps.trans u₄.keeps).trans ⟨fun r _ => by rw [g₅], r₅, w₅⟩)
    (by rw [hm₅]; exact frame_store s₀ _ (by decide) _)
  have z₅ : v₅.zf = some (decide (f = 0)) := by
    rw [zf₅, z₄, u₃.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  exact ⟨h₅, k₅, hm₅, z₅⟩

/-- Record the signer's status `st`, and spend an attempt on a failure. -/
theorem callFinish_ok {s₀ u : State} (h : Ready s₀ u) {st f : Nat} (hst : st ≤ 1)
    (he : u.gpr .eax = BitVec.ofNat 32 st) (ha : slot u.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1))
    (hf : f + 1 ≤ 8) :
    WP isa callFinish u fun v => Ready s₀ v ∧ Keeps [.eax] u v ∧
      Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v.mem ∧
      (st = 1 → slot v.mem (rBase s₀) oStatus = 1 ∧ slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) ∧
      (st = 0 → slot v.mem (rBase s₀) oAttempts = BitVec.ofNat 32 f ∧
        slot v.mem (rBase s₀) oStatus = (if f = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (finHead_ok h hst he) fun v₂ ⟨h₂, k₂, m₂, z₂⟩ => ?_)
  have o₂ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₂.mem := by
    rw [m₂]; exact store_outs _ _ _ (by decide)
  by_cases h0 : st = 0
  · subst h0
    refine WP.ite true (by simp only [eval, z₂, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    have ha₂ : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha
    refine WP.seq (WP.mono (finDec_ok h₂ ha₂ hf) fun v₅ ⟨h₅, k₅', hm₅, z₅⟩ => ?_)
    have k₅ : Keeps [.eax] u v₅ := k₂.trans k₅'
    have o₅ : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] u.mem v₅.mem := by
      rw [hm₅]; exact o₂.trans (store_outs _ _ _ (by decide))
    by_cases hf0 : f = 0
    · refine WP.ite false (by simp only [eval, z₅, hf0, decide_true, Option.map_some, Bool.not_true])
        (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨h₅, k₅, o₅, fun e => absurd e (by decide), fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₅, slot_write_self]
      · rw [hm₅, slot_write_ne _ _ _ (by decide) (by decide) (by decide), m₂, slot_write_self, hf0]; rfl
    · refine WP.ite true (by simp only [eval, z₅, hf0, decide_false, Option.map_some, Bool.not_false])
        (fun _ => wp_movS rfl fun v₆ u₆ _ => wp_slot (h₅.rf.of_keeps u₆.keeps) (by decide) u₆.gpr
          fun v₇ f₇ m₇ g₇ r₇ w₇ _ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      have hm₇ : v₇.mem = v₅.mem.writeW (off (rBase s₀) oStatus) (4 : BitVec 32) := by rw [m₇, u₆.mem]
      refine ⟨h₅.congr (rs := [.eax]) (u₆.keeps.trans ⟨fun r _ => by rw [g₇], r₇, w₇⟩)
          (by rw [hm₇]; exact frame_store s₀ _ (by decide) _),
        (k₅.trans u₆.keeps).trans ⟨fun r _ => by rw [g₇], r₇, w₇⟩,
        by rw [hm₇]; exact o₅.trans (store_outs _ _ _ (by decide)), fun e => absurd e (by decide),
        fun _ => ⟨?_, ?_⟩⟩
      · rw [hm₇, slot_write_ne _ _ _ (by decide) (by decide) (by decide), hm₅, slot_write_self]
      · rw [hm₇, slot_write_self]; simp only [hf0, ↓reduceIte]
  · have h1 : st = 1 := by omega
    subst h1
    refine WP.ite false (by simp only [eval, z₂]; rfl) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
    refine ⟨h₂, k₂, o₂, fun _ => ⟨?_, ?_⟩, fun e => absurd e (by decide)⟩
    · rw [m₂, slot_write_self]; rfl
    · rw [m₂, slot_write_ne _ _ _ (by decide) (by decide) (by decide)]; exact ha

/-- Slot stores keep the sampler's state. -/
theorem Smp.after_finish {s₀ t u : State} (A : RandomSignABI s₀) {used d : Nat} (S : Smp s₀ used d t)
    (hr : Ready s₀ u) (hm : Outs (rBase s₀) [(oAttempts, 4), (oStatus, 4)] t.mem u.mem) : Smp s₀ used d u := by
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hs : ∀ d, d ≤ 120 → (d + 4 ≤ oAttempts ∨ oAttempts + 4 ≤ d) → (d + 4 ≤ oStatus ∨ oStatus + 4 ≤ d) →
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
    (hm : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ 120) {p : Addr} {n : Nat}
    (hd : (rStack s₀).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  refine hm _ fun r hr => ?_
  have hb := hrs r hr
  by_cases hx : ofs (rBase s₀) (p + BitVec.ofNat 64 i) < 120
  · exfalso
    refine hd _ ?_ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega))
    have he : p + BitVec.ofNat 64 i = off (rBase s₀) (ofs (rBase s₀) (p + BitVec.ofNat 64 i)) := by
      simp only [ofs, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm (rBase s₀), BitVec.sub_add_cancel]
    rw [he, rBase_off]
    exact Offset.contains_base _ (by omega) (by omega)
  · right; omega

/-- The key's bytes, while the frame is allocated. -/
theorem callKey {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) :
    Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 3) (X86.arg s₀ 4).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-- The signer's input is the specification's, with the sampled nonce. -/
theorem callResult_eq {s₀ t : State} (A : RandomSignABI s₀) (h : Ready s₀ t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length k) :
    callResult s₀ t = Spec.Dsa.signBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
      (Spec.Dsa.encodeBE (rInput s₀).qLen k) (rInput s₀).digest := by
  have hqn := rQBytes_length A
  have hkey := callKey A h
  have hdig : Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 7) (X86.arg s₀ 8).toNat = (rInput s₀).digest := by
    refine rBytes_frame h.frame (fun r hr => ?_) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
    simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.stackDigest.symm
    · exact A.outDigest.symm
    · exact A.digestScratch
    · exact A.usedDigest.symm
  have hnon : Spec.Rsa.bytesAt t.mem (off (rLow s₀) 112) (X86.arg s₀ 6).toNat =
      Spec.Dsa.encodeBE (rInput s₀).qLen k := by
    rw [show off (rLow s₀) 112 = off (rBase s₀) oNonce from (rBase_off s₀ oNonce).symm, ← hqn, hn, hqn]; rfl
  unfold callResult
  rw [hkey, hdig, hnon]; rfl

/-- Slots below the ranges that changed. -/
theorem outs_low {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, e ≤ r.1) {d : Nat} (hd : d + 4 ≤ e) (hd' : d + 4 < 2 ^ 64) : slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inl (Nat.le_trans hd (hrs r hr))) hd'

/-- Slots above the ranges that changed. -/
theorem outs_high {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {e : Nat}
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ e) {d : Nat} (hd : e ≤ d) (hd' : d + 4 < 2 ^ 64) :
    slot m' B d = slot m B d :=
  slot_outs h (fun r hr => .inr (Nat.le_trans (hrs r hr) hd)) hd'

/-- Bytes of the frame above the ranges that changed. -/
theorem outs_frame_bytes {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m') {d n : Nat}
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ d) (hd : d + n < 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off B d) n = Spec.Rsa.bytesAt m (off B d) n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact h _ fun r hr => by
    have := hrs r hr
    rw [ofs_off B (by omega)]; right; omega

/-- What an attempt from `used` with `f + 1` attempts left leaves: another
attempt to make after a retry, which its signing trace records, or the result. -/
def AttemptOut (s₀ : State) (used f : Nat) (u : State) : Prop :=
  (slot u.mem (rBase s₀) oStatus = 4 ∧ 1 ≤ f ∧ Att s₀ (used + (spl s₀ 128 used).used) f u ∧
    VG.Proof.Dsa.randomSigningTrace (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace =
      6 :: (VG.Proof.Dsa.randomSignRemaining (rInput s₀) (used + (spl s₀ 128 used).used) f).trace) ∨
    (slot u.mem (rBase s₀) oStatus ≠ 4 ∧ Done s₀ u ∧
      ¬ ((VG.Proof.Dsa.randomSigningTrace
        (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace).head? = some 6 ∧ 1 ≤ f))

theorem attempt_ok (F : SignFn) {s₀ t : State} (A : RandomSignABI s₀) {used f : Nat}
    (T : Att s₀ used (f + 1) t) (hf : f + 1 ≤ 8) (hq : 1 < rq s₀) :
    WP isa (attempt F.name F.code) t fun u => AttemptOut s₀ used f u := by
  have hql := rQBytes_le A
  obtain ⟨d₀, Sm⟩ := T.smp
  unfold attempt
  refine WP.seq (WP.mono (sample_ok A Sm hq) fun u₁ ⟨O, eax₁, h₁, o₁, _⟩ => ?_)
  have sv₁ : Saved s₀ u₁.mem := T.saved.of_slots fun d _ hd => outs_low o₁ (by decide) hd (by omega)
  have at₁ : slot u₁.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) :=
    (slot_outs o₁ (by decide) (by decide)).trans T.attempts
  refine WP.seq (wp_cmpi fun u₂ fv₂ _ z₂ => WP.block_nil ?_)
  have h₂ := h₁.fupd fv₂
  have m₂ : u₂.mem = u₁.mem := fv₂.mem
  have hle := sampleStatus_le (spl s₀ 128 used)
  rw [eax₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)] at z₂
  cases hsc : (spl s₀ 128 used).scalar with
  | none =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]; split <;> simp
    refine WP.ite false (by simp only [eval, z₂, hst, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    obtain ⟨-, hstat, hused⟩ := T.rel.sample_none hsc
    obtain ⟨d', S'⟩ := O.smp
    refine .inr ⟨?_, ⟨⟨d', ?_⟩, ?_, fun e => absurd (hstat ▸ e) hst, (by rw [m₂]; exact sv₁)⟩,
      by rw [VG.Proof.Dsa.random_sign_trace_none _ _ _ hsc]; simp⟩
    · rw [m₂, O.status]
      intro e
      have := congrArg BitVec.toNat e
      rw [toNat_ofNat_lt (by omega)] at this
      exact absurd this (by show _ ≠ 4; omega)
    · have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
      rw [e]; exact S'.mem A h₂ m₂
    · rw [m₂, O.status]; exact congrArg (BitVec.ofNat 32) hstat.symm
  | some k =>
    have hst : VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 used) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hsc]
    refine WP.ite true (by simp only [eval, z₂, hst, decide_true]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    obtain ⟨d', S'⟩ := O.smp
    have S₂ := S'.mem A h₂ m₂
    refine WP.seq (?_ : WP isa (.block (callArgs ++ [])) u₂ _)
    refine callArgs_ok A h₂ fun u₃ h₃ m₃ k₃ => WP.block_nil ?_
    have o₃ := argsMem_outs s₀ u₂.mem (u₂.gpr .esp)
    rw [← m₃] at o₃
    have C₃ : CallSlots s₀ u₃ := fun i hi => by
      rw [m₃, k₃.1 .esp (by decide)]; exact argsMem_slots s₀ _ _ i hi
    have hk : Spec.Rsa.bytesAt u₃.mem (off (rBase s₀) oNonce) (rQBytes s₀).length =
        Spec.Dsa.encodeBE (rQBytes s₀).length k := by
      rw [outs_frame_bytes o₃ (by decide) (by unfold oNonce; omega), m₂]; exact O.nonce k hsc
    have hres := callResult_eq A h₃ hk
    refine WP.seq (WP.mono (call_ok F A h₃ C₃) fun u₄ ⟨h₄, f₄, _, eax₄, out₄⟩ => ?_)
    have at₄ : slot u₄.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1) := by
      rw [call_frame_slot A f₄ (by decide) (by decide), outs_high o₃ (e := 44) (by decide) (by decide) (by decide), m₂]
      exact at₁
    have S₄ := (S₂.after_args A h₃ o₃).after_call A h₄ f₄
    have sv₄ : Saved s₀ u₄.mem := sv₁.of_slots fun d h₁ hd => by
      rw [call_frame_slot A f₄ h₁ (by omega), outs_high o₃ (e := 44) (by decide) h₁ (by omega), m₂]
    rw [hres] at eax₄ out₄
    refine WP.mono (callFinish_ok h₄ (by unfold Spec.Dsa.signStatus; split <;> decide) eax₄ at₄ hf)
      fun u₅ ⟨h₅, _, o₅, hT1, hT0⟩ => ?_
    have S₅ := S₄.after_finish A h₅ o₅
    have sv₅ : Saved s₀ u₅.mem := sv₄.of_slots fun d _ hd => outs_low o₅ (by decide) hd (by omega)
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

end VG.Proof.Dsa.X86
