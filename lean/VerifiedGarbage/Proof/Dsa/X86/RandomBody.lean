module

public import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# The randomized signer's body (x86)

The entry saves the callee-saved registers and starts the count of
attempts; `prepare` checks q; the attempts run until one ends the
signing (`Done`), as the specification's `randomSignLoop` does; `finish`
writes the results (`Finished`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random VG.Impl.Dsa.X86.RandomSign

/-- With valid lengths, the result is the signing loop's. -/
theorem rResult_loop {s₀ : State} (A : RandomSignABI s₀) :
    rResult s₀ = Spec.Dsa.randomSignLoop (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest 8
      (rInput s₀).rand := by
  have hk : (rInput s₀).key.length = 3 * (rInput s₀).pLen + 2 * (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  simp only [rResult, Spec.Dsa.randomSignBytes, hk, hl, decide_true, Bool.not_true, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- q ≤ 1 fails without consuming input. -/
theorem rResult_small {s₀ : State} (A : RandomSignABI s₀) (hq : ¬ 1 < rq s₀) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_loop A, Spec.Dsa.randomSignLoop]
  have hs : Spec.Dsa.Random.sample (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen
      (rInput s₀).key).params.q 128 (rInput s₀).rand = ⟨none, 0, [4]⟩ := by
    have h1 : (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q ≤ 1 := by
      rw [← rQ_decode]; exact Nat.le_of_not_lt hq
    rw [Spec.Dsa.Random.sample]; simp only [h1, ↓reduceIte]
  simp only [hs]
  rfl

theorem rResult_status_le {s₀ : State} (A : RandomSignABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_loop A]; exact VG.Proof.Dsa.randomSignLoop_status_le _ _ _ _ _ _

theorem rResult_signature {s₀ : State} (A : RandomSignABI s₀) :
    (rResult s₀).status ≠ 1 → (rResult s₀).signature = none := by
  rw [rResult_loop A]
  intro h
  have := (VG.Proof.Dsa.randomSignLoop_success _ _ _ _ _ _).not.mp h
  simpa using this

theorem rResult_used_le {s₀ : State} : (rResult s₀).used ≤ (rInput s₀).rand.length :=
  VG.Proof.Dsa.randomSignBytes_used_le _ _ _ _ _

/-- Save the callee-saved registers, and start the counts. -/
theorem entry_ok {s₀ t : State} (h : Ready s₀ t) (hb : t.gpr .ebx = s₀.gpr .ebx) (hs : t.gpr .esi = s₀.gpr .esi)
    (hd : t.gpr .edi = s₀.gpr .edi) (hp : t.gpr .ebp = s₀.gpr .ebp) :
    WP isa (.block entry) t fun u => Ready s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oAttempts = 8 ∧
      Outs (rBase s₀) [(oSaveEbx, 24)] t.mem u.mem := by
  unfold entry
  refine wp_slot h.rf (by decide) hb fun t₁ f₁ m₁ g₁ r₁ w₁ _ _ => ?_
  refine wp_slot f₁ (by decide) (v := s₀.gpr .esi) (by rw [g₁]; exact hs) fun t₂ f₂ m₂ g₂ r₂ w₂ _ _ => ?_
  refine wp_slot f₂ (by decide) (v := s₀.gpr .edi) (by rw [g₂, g₁]; exact hd) fun t₃ f₃ m₃ g₃ r₃ w₃ _ _ => ?_
  refine wp_slot f₃ (by decide) (v := s₀.gpr .ebp) (by rw [g₃, g₂, g₁]; exact hp) fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => ?_
  refine wp_movS rfl fun t₅ u₅ _ => wp_slot (f₄.of_keeps u₅.keeps) (by decide) u₅.gpr
    fun t₆ f₆ m₆ g₆ r₆ w₆ _ _ => wp_movS rfl fun t₇ u₇ _ => wp_slot (f₆.of_keeps u₇.keeps) (by decide) u₇.gpr
    fun t₈ f₈ m₈ g₈ r₈ w₈ _ _ => WP.block_nil ?_
  have hm : t₈.mem = (((((((t.mem.writeW (off (rBase s₀) oSaveEbx) (s₀.gpr .ebx)).writeW
      (off (rBase s₀) oSaveEsi) (s₀.gpr .esi)).writeW (off (rBase s₀) oSaveEdi) (s₀.gpr .edi)).writeW
      (off (rBase s₀) oSaveEbp) (s₀.gpr .ebp)).writeW (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW
      (off (rBase s₀) oAttempts) (8 : BitVec 32))) := by
    rw [m₈, u₇.mem, m₆, u₅.mem, m₄, m₃, m₂, m₁]
  have kk : Keeps [.eax] t t₈ :=
    (((((Keeps.trans (⟨fun r _ => by rw [g₁], r₁, w₁⟩ : Keeps [.eax] t t₁) ⟨fun r _ => by rw [g₂], r₂, w₂⟩).trans
      ⟨fun r _ => by rw [g₃], r₃, w₃⟩).trans ⟨fun r _ => by rw [g₄], r₄, w₄⟩).trans u₅.keeps).trans
      ⟨fun r _ => by rw [g₆], r₆, w₆⟩).trans (u₇.keeps.trans ⟨fun r _ => by rw [g₈], r₈, w₈⟩)
  have e := fun {m : Mem} {d : Nat} (v : BitVec 32) (h₁ : oSaveEbx ≤ d) (h₂ : d + 4 ≤ oSaveEbx + 24) =>
    store_in (rBase s₀) m (rs := [(oSaveEbx, 24)]) v (List.mem_singleton_self _) h₁ h₂ (by unfold oSaveEbx at h₂; omega)
  refine ⟨h.congr kk (by
      rw [hm]
      exact (((((frame_store s₀ _ (by decide) _).trans (frame_store s₀ _ (by decide) _)).trans
        (frame_store s₀ _ (by decide) _)).trans (frame_store s₀ _ (by decide) _)).trans
        (frame_store s₀ _ (by decide) _)).trans (frame_store s₀ _ (by decide) _)),
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | (rw [hm]; exact (((((e _ (by decide) (by decide)).trans (e _ (by decide) (by decide))).trans
        (e _ (by decide) (by decide))).trans (e _ (by decide) (by decide))).trans
        (e _ (by decide) (by decide))).trans (e _ (by decide) (by decide)))

theorem Att.mem {s₀ t u : State} (A : RandomSignABI s₀) {used f : Nat} (T : Att s₀ used f t) (hr : Ready s₀ u)
    (hm : u.mem = t.mem) : Att s₀ used f u :=
  let ⟨d, S⟩ := T.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact T.attempts, by rw [hm]; exact T.saved, T.rel⟩

theorem Done.mem {s₀ t u : State} (A : RandomSignABI s₀) (D : Done s₀ t) (hr : Ready s₀ u) (hm : u.mem = t.mem) :
    Done s₀ u :=
  let ⟨d, S⟩ := D.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact D.status, by rw [hm]; exact D.out, by rw [hm]; exact D.saved⟩

theorem body_ok (F : SignFn) {s₀ : State} (A : RandomSignABI s₀) :
    WP isa (body F.name F.code) (allocated Random.frameBytes s₀) fun u => Finished s₀ u := by
  have h₀ := alloc_ready A
  have hql := rQBytes_le A
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  unfold body
  refine WP.seq (WP.mono (entry_ok h₀ (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide))
    (allocated_gpr _ _ (by decide)) (allocated_gpr _ _ (by decide))) fun t₁ ⟨h₁, sv₁, us₁, at₁, _⟩ => ?_)
  refine WP.seq (WP.mono (prepare_ok A h₁) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_)
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega)
  refine WP.seq (wp_cmpi fun t₃ f₃ _ z₃ => WP.block_nil ?_)
  have h₃ := h₂.fupd f₃
  have m₃ : t₃.mem = t₂.mem := f₃.mem
  have sv₃ : Saved s₀ t₃.mem := by rw [m₃]; exact sv₁.of_slots fun d _ hd => lo₂ d (by unfold oQ; omega)
  have us₃ : slot t₃.mem (rBase s₀) oUsed = 0 := by rw [m₃, lo₂ _ (by decide)]; exact us₁
  have at₃ : slot t₃.mem (rBase s₀) oAttempts = 8 := by rw [m₃, lo₂ _ (by decide)]; exact at₁
  rw [ax₂] at z₃
  by_cases hq : 1 < rq s₀
  · simp only [hq, ↓reduceIte] at z₃
    have P := P₂ hq
    refine WP.seq (WP.ite false (by simp only [eval, z₃]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_))
    have T₀ : Att s₀ 0 8 t₃ := by
      refine ⟨⟨(slot t₃.mem (rBase s₀) oDraws).toNat, ⟨h₃, by rw [m₃]; exact P.q, by rw [m₃]; exact P.width,
        by rw [m₃]; exact P.mask, us₃, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => by rw [m₃]; exact P.nonce i (by omega), Nat.zero_le _⟩⟩, at₃, sv₃, ?_⟩
      have e : VG.Proof.Dsa.randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by
        rw [rResult_loop A]; rfl
      exact ⟨by rw [e], by rw [e], by rw [e]⟩
    refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used, 1 ≤ n ∧ n ≤ 8 ∧ Att s₀ used n u)
      (fun n u hu => ?_) 8 t₃ ⟨0, by decide, by decide, T₀⟩
    obtain ⟨used, hn1, hn8, T⟩ := hu
    obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
    refine WP.seq (WP.mono (attempt_ok F A T hn8 hq) fun v hv => ?_)
    have hrv : Ready s₀ v := by
      rcases hv with ⟨_, _, T', _⟩ | ⟨_, D, _⟩
      · obtain ⟨_, S⟩ := T'.smp; exact S.ready
      · obtain ⟨_, S⟩ := D.smp; exact S.ready
    refine wp_movS (hrv.rf.readSlot (by decide)) fun v₁ uv₁ _ => wp_cmpi fun v₂ fv₂ _ zv₂ => WP.block_nil ?_
    have hv₂ := (hrv.upd uv₁ (by decide)).fupd fv₂
    have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
    rw [uv₁.gpr] at zv₂
    rcases hv with ⟨st, h1f, T', _⟩ | ⟨st, D, _⟩
    · right
      have st' : v.mem.readW (off (rBase s₀) oStatus) 32 = 4 := st
      refine ⟨by simp only [eval, zv₂, st']; rfl, f, by omega, _, h1f, by omega, T'.mem A hv₂ mv₂⟩
    · left
      refine ⟨?_, finish_ok A ((D.mem A hv₂ mv₂).fin) (rResult_status_le A) (rResult_signature A)⟩
      have hle := rResult_status_le A
      have st' : v.mem.readW (off (rBase s₀) oStatus) 32 = BitVec.ofNat 32 (rResult s₀).status := D.status
      have hz : (v.mem.readW (off (rBase s₀) oStatus) 32 - 4 == 0) = false := by
        rw [st', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_beq (by omega) (by decide)]
        simp only [decide_eq_false_iff_not]; omega
      simp only [eval, zv₂, hz]
  · simp only [hq, ↓reduceIte] at z₃
    have hR := rResult_small A hq
    refine WP.seq (WP.ite true (by simp only [eval, z₃]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e))
    have ax₃ : t₃.gpr .eax = BitVec.ofNat 32 (rResult s₀).status := by
      rw [f₃.gpr, ax₂, hR]; simp only [hq, ↓reduceIte]; rfl
    refine wp_slot h₃.rf (by decide) ax₃ fun t₄ f₄ m₄ g₄ r₄ w₄ _ _ => WP.block_nil ?_
    have h₄ : Ready s₀ t₄ := h₃.congr (rs := []) ⟨fun r _ => by rw [g₄], r₄, w₄⟩
      (by rw [m₄]; exact frame_store s₀ _ (by decide) _)
    refine finish_ok A ⟨h₄, ?_, by rw [m₄, slot_write_self], fun e => by rw [hR] at e; exact absurd e (by decide),
      sv₃.of_slots fun d _ hd => by rw [m₄, slot_write_ne _ _ _ (by unfold oStatus; omega) (by omega) (by decide)]⟩
      (rResult_status_le A) (rResult_signature A)
    rw [m₄, slot_write_ne _ _ _ (by decide) (by decide) (by decide), us₃, hR]; rfl

end VG.Proof.Dsa.X86
