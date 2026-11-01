module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Call
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Finish
import VerifiedGarbage.Proof.Dsa.Arm.Key.Sample
import VerifiedGarbage.Proof.Dsa.Arm.Key.Scan
import VerifiedGarbage.Proof.Dsa.Arm.GenerateCheck
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Draw
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# DSA key generation on 32-bit ARM: the body

The entry saves the registers (`entry_ok`); the domain check's call
(`callCheck_ok`) decides whether to sample; one budget of draws
(`sample_ok`) gives x or the status; with x, the derivation's call
(`callDerive_ok`) writes the key and its status. Every path leaves what
`rfinish_ok` needs: the specification's status, consumption and key.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-! ## The specification's result -/

/-- The checks of the domain, as the specification makes them. -/
abbrev rChecked (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key

/-- With valid lengths, the result is the check, the sampling and the derivation's. -/
theorem rResult_eq {s₀ : State} (A : KeyABI s₀) :
    rResult s₀ = if rChecked s₀ then
        match (spl s₀ 128 0).scalar with
        | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (spl s₀ 128 0), (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace⟩
        | some x =>
          let res := Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
            (Spec.Dsa.encodeBE (rInput s₀).qLen x)
          ⟨res, Spec.Dsa.signStatus res, (spl s₀ 128 0).used,
            (spl s₀ 128 0).trace ++ [if res.isSome then 5 else 6]⟩
      else ⟨none, 0, 0, [4]⟩ := by
  have hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  rw [rResult, VG.Proof.Dsa.generateKeyBytes_eq hl hk, spl, List.drop_zero, ← rQ_decode]
  cases h : (Spec.Dsa.Random.sample (rq s₀) 128 (rInput s₀).rand).scalar <;>
    simp [VG.Proof.Dsa.Random.sampleStatus, h]

/-- A checked domain has q > 1. -/
theorem rq_of_checked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = true) : 1 < rq s₀ := by
  have hk : (rInput s₀).key.length = 2 * (rInput s₀).pLen + (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  have := (VG.Proof.Dsa.Arm.checkParametersBytes_iff hl hk).mp hc
  have B := VG.Proof.Dsa.supported_bounds this.1.1
  rw [rQ_decode]; omega_arith

theorem rResult_unchecked {s₀ : State} (A : KeyABI s₀) (hc : rChecked s₀ = false) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_eq A, hc]; rfl

/-! ## Memory the calls keep -/

abbrev frameR (s₀ : State) : Region := ⟨rBase s₀, frameBytes⟩

theorem frameR_sub (s₀ : State) : Region.Sub (frameR s₀) (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 32) (n := frameBytes) (k := 144) (by decide)
  exact this

/-- The frame's slots, apart from what a call wrote. -/
theorem slot_keep {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (frameR s₀) r) {d : Nat} (hd' : d + 4 ≤ frameBytes) :
    slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have : frameBytes = 112 := rfl; omega_arith))) (by decide)

theorem frame_low (s₀ : State) : Region.Disjoint (frameR s₀) ⟨rLow s₀, 32⟩ :=
  Offset.disjoint_base _ (Nat.le_refl 32) (by decide)

theorem check_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ checkWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [checkWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

theorem derive_keeps {s₀ : State} (A : KeyABI s₀) : ∀ r ∈ deriveWrites s₀, Region.Disjoint (frameR s₀) r := by
  intro r hr
  simp only [deriveWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut.sub_left (frameR_sub s₀)
  · exact A.stackScratch.sub_left (frameR_sub s₀)
  · exact frame_low s₀

/-- The domain's bytes, which nothing writes. -/
theorem key_bytes {s₀ t : State} (A : KeyABI s₀) (h : RReady s₀ t) :
    Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat = (rInput s₀).key := by
  refine rBytes_frame h.frame (fun r hr => ?_) (by have := (stackArg s₀ 0).isLt; omega_arith)
  simp only [rWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact A.stackKey.symm
  · exact A.outKey.symm
  · exact A.keyScratch
  · exact A.usedKey.symm

/-! ## The entry -/

/-- Before `r11` holds the frame's base, `r12` does. -/
structure PreR (s₀ t : State) : Prop where
  r12 : t.gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- `str r, [r12, #d]`, a slot of the frame. -/
theorem wp_strP {s₀ t : State} (A : KeyABI s₀) (P : PreR s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, PreR s₀ u → u.mem = t.mem.writeW (off (rBase s₀) d) (t.gpr r) → u.gpr = t.gpr →
      WP isa (.block is) u Q) :
    WP isa (.block (.str r .r12 d :: is)) t Q := by
  have hb := rBase_toNat A
  have hs := A.stackBound
  have hl := A.stackLow
  have ha : State.addr (t.gpr .r12 + BitVec.ofNat 32 d) = off (rBase s₀) d := by
    rw [P.r12, VG.Arm.addr_add (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_arith),
      alloc_base A]
  refine wp_str (by unfold frameBytes at hd; omega_arith) ha
    ⟨_, by rw [P.wr]; exact List.mem_cons_self, Offset.contains_base _ hd (by unfold frameBytes at *; omega_arith)⟩
    fun u m => k u ⟨by rw [m.gpr]; exact P.r12, m.sp.trans P.sp, m.rd.trans P.rd, m.wr.trans P.wr,
      P.frame.trans (by
        rw [m.mem]
        exact (frame_store s₀ t.mem hd (t.gpr r)).mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [rWrites])⟩ m.mem m.gpr

theorem entry_eq : GenerateKey.entry = [.addSp .r12 0, .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12,
    .str .r8 .r12 16, .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28, .str .lr .r12 32,
    .mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, st .r0 oStatus] := rfl

/-- Save the callee-saved registers and the register arguments, and start the counts. -/
theorem entry_ok {s₀ : State} (A : KeyABI s₀) :
    WP isa (.block GenerateKey.entry) (allocated frameBytes s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oStatus = 0 ∧
      (∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s₀.gpr r) := by
  rw [entry_eq]
  refine VG.Proof.X25519.Arm.WP.cons (s' := (allocated frameBytes s₀).setReg .r12
    ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) (by simp [exec]) ?_
  have P₀ : PreR s₀ ((allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) :=
    ⟨by simp [State.setReg, allocated], rfl, rfl, by
      show ⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ :: s₀.wr = _; rw [alloc_base A],
      Frame.refl _ _⟩
  have g₀ : ∀ r, r ≠ .r12 → ((allocated frameBytes s₀).setReg .r12
      ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)).gpr r = s₀.gpr r := fun r h => by
    simp [State.setReg, allocated, h]
  refine wp_strP A P₀ (by decide) fun t₁ P₁ m₁ g₁ => wp_strP A P₁ (by decide) fun t₂ P₂ m₂ g₂ =>
    wp_strP A P₂ (by decide) fun t₃ P₃ m₃ g₃ => wp_strP A P₃ (by decide) fun t₄ P₄ m₄ g₄ =>
    wp_strP A P₄ (by decide) fun t₅ P₅ m₅ g₅ => wp_strP A P₅ (by decide) fun t₆ P₆ m₆ g₆ =>
    wp_strP A P₆ (by decide) fun t₇ P₇ m₇ g₇ => wp_strP A P₇ (by decide) fun t₈ P₈ m₈ g₈ =>
    wp_strP A P₈ (by decide) fun t₉ P₉ m₉ g₉ => wp_mov (op2_reg _ _) fun t₁₀ u₁₀ => ?_
  have gg : ∀ r, r ≠ .r12 → t₉.gpr r = s₀.gpr r := fun r h => by
    rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact g₀ r h
  have nw : (rBase s₀).toNat + frameBytes + 28 ≤ 2 ^ 32 := by
    rw [rBase_toNat A]; have := A.stackBound; have := A.stackLow; unfold frameBytes; omega_arith
  have h₁₀ : RReady s₀ t₁₀ :=
    ⟨⟨by rw [u₁₀.gpr, P₉.r12, alloc_base A], by rw [u₁₀.wr, P₉.wr]; exact List.mem_cons_self,
      by rw [u₁₀.rd, P₉.rd, A.rd, rBase_args A]; simp, nw⟩,
      u₁₀.sp.trans P₉.sp, u₁₀.rd.trans P₉.rd, u₁₀.wr.trans P₉.wr, by rw [u₁₀.mem]; exact P₉.frame⟩
  refine wp_st h₁₀ (by decide) fun t₁₁ m₁₁ h₁₁ => wp_st h₁₁ (by decide) fun t₁₂ m₁₂ h₁₂ =>
    wp_st h₁₂ (by decide) fun t₁₃ m₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ m₁₄ h₁₄ =>
    wp_mov (op2_imm (by decide)) fun t₁₅ u₁₅ => wp_st (h₁₄.upd u₁₅) (by decide) fun t₁₆ m₁₆ h₁₆ =>
    wp_st h₁₆ (by decide) fun t₁₈ m₁₈ h₁₈ => WP.block_nil ?_
  have e₁₄ : ∀ r, r ≠ .r11 → r ≠ .r12 → t₁₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [m₁₄.gpr, m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ h]; exact gg r h'
  have hm : t₁₈.mem = ((((((((((((((s₀.mem.writeW (off (rBase s₀) 0) (s₀.gpr .r4)).writeW
      (off (rBase s₀) 4) (s₀.gpr .r5)).writeW (off (rBase s₀) 8) (s₀.gpr .r6)).writeW
      (off (rBase s₀) 12) (s₀.gpr .r7)).writeW (off (rBase s₀) 16) (s₀.gpr .r8)).writeW
      (off (rBase s₀) 20) (s₀.gpr .r9)).writeW (off (rBase s₀) 24) (s₀.gpr .r10)).writeW
      (off (rBase s₀) 28) (s₀.gpr .r11)).writeW (off (rBase s₀) 32) (s₀.gpr .lr)).writeW
      (off (rBase s₀) oOut) (s₀.gpr .r0)).writeW (off (rBase s₀) oOutLen) (s₀.gpr .r1)).writeW
      (off (rBase s₀) oUsedPtr) (s₀.gpr .r2)).writeW (off (rBase s₀) oKey) (s₀.gpr .r3)).writeW
      (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW (off (rBase s₀) oStatus) (0 : BitVec 32) := by
    have v0 : t₁₀.gpr .r0 = s₀.gpr .r0 := by rw [u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v1 : t₁₁.gpr .r1 = s₀.gpr .r1 := by rw [m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v2 : t₁₂.gpr .r2 = s₀.gpr .r2 := by
      rw [m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v3 : t₁₃.gpr .r3 = s₀.gpr .r3 := by
      rw [m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    rw [m₁₈.mem, m₁₆.gpr, u₁₅.gpr, m₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄.mem, m₁₃.mem, m₁₂.mem, m₁₁.mem, v0, v1, v2, v3,
      u₁₀.mem, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    simp only [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, g₀ _ (by decide : Reg.r4 ≠ .r12), g₀ _ (by decide : Reg.r5 ≠ .r12),
      g₀ _ (by decide : Reg.r6 ≠ .r12), g₀ _ (by decide : Reg.r7 ≠ .r12), g₀ _ (by decide : Reg.r8 ≠ .r12),
      g₀ _ (by decide : Reg.r9 ≠ .r12), g₀ _ (by decide : Reg.r10 ≠ .r12), g₀ _ (by decide : Reg.r11 ≠ .r12),
      g₀ _ (by decide : Reg.lr ≠ .r12)]
    rfl
  refine ⟨h₁₈, ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h0 h11 h12 => ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by omega_arith
    all_goals (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; rfl)
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | skip
  rw [m₁₈.gpr, m₁₆.gpr, u₁₅.other _ h0]; exact e₁₄ r h11 h12


/-! ## The results -/

theorem sampleStatus_none {S : Spec.Dsa.Random.Sample} (h : S.scalar = none) :
    VG.Proof.Dsa.Random.sampleStatus S ≠ 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; simp only [h]; split <;> omega_arith

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} {k : Nat} (h : S.scalar = some k) :
    VG.Proof.Dsa.Random.sampleStatus S = 1 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; rw [h]

theorem rResult_status_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_eq A]
  split
  · split
    · exact sampleStatus_le _
    · have := status_lt (Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
        (Spec.Dsa.encodeBE (rInput s₀).qLen ‹_›)); dsimp only; omega_arith
  · decide

theorem rResult_key {s₀ : State} (A : KeyABI s₀) : (rResult s₀).status ≠ 1 → (rResult s₀).key = none := by
  rw [rResult_eq A]
  split
  · split
    · intro _; rfl
    · dsimp only; unfold Spec.Dsa.signStatus; split
      · intro h; exact absurd rfl h
      · next h => intro _; simpa using h
  · intro _; rfl

/-! ## The body -/

theorem body_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (body check derive Generate.checkParameters Generate.deriveKey) (allocated frameBytes s₀)
      fun u => Finished s₀ u := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hfit := rWidth_le s₀
  have hF : frameBytes = 112 := rfl
  unfold body
  refine WP.seq (WP.mono (entry_ok A) fun t₁ ⟨h₁, sv₁, us₁, st₁, _⟩ => ?_)
  refine WP.seq (WP.mono (checkArgs_ok A h₁ sv₁) fun t₂ ⟨h₂, m₂, C₂, _⟩ => ?_)
  refine WP.seq (WP.mono (callCheck_ok A h₂ C₂ check) fun t₃ ⟨h₃, f₃, _, r0₃⟩ => ?_)
  have sl₃ : ∀ d, d + 4 ≤ frameBytes → slot t₃.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd => by
    rw [slot_keep f₃ (check_keeps A) hd, m₂]
  have hck : checkResult s₀ t₂ = rChecked s₀ := by
    unfold checkResult; rw [key_bytes A h₂]; rfl
  rw [hck] at r0₃
  have sv₃ : Saved s₀ t₃.mem := sv₁.of_slots fun d _ hd => sl₃ d hd
  refine WP.seq (wp_cmp0 fun t₄ f₄ z₄ => WP.block_nil ?_)
  have h₄ := h₃.fupd f₄
  have m₄ : t₄.mem = t₃.mem := f₄.mem
  rw [r0₃] at z₄
  suffices H : WP isa (.ite .eq (.block []) (generate derive Generate.deriveKey)) t₄ (RFin s₀) from
    WP.seq (WP.mono H fun u hu => rfinish_ok A hu (rResult_status_le A) (rResult_key A))
  by_cases hc : rChecked s₀ = true
  · rw [hc] at z₄
    refine WP.ite false (by rw [eval_eq, z₄]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    have hq := rq_of_checked A hc
    have sv₄ : Saved s₀ t₄.mem := by rw [m₄]; exact sv₃
    unfold generate
    refine WP.seq (WP.mono (prepare_ok A h₄ sv₄.2.2.2.2) fun t₅ ⟨_, P₅, h₅, o₅, _⟩ => ?_)
    have P := P₅ hq
    have lo₅ : ∀ d, d + 4 ≤ oQ → slot t₅.mem (rBase s₀) d = slot t₄.mem (rBase s₀) d := fun d hd =>
      outs_low o₅ (by decide) hd (by unfold oQ at hd; omega_arith)
    have us₅ : slot t₅.mem (rBase s₀) oUsed = BitVec.ofNat 32 0 := by
      rw [lo₅ _ (by decide), m₄, sl₃ _ (by decide)]; exact us₁
    have S₅ : Smp s₀ 0 (slot t₅.mem (rBase s₀) oDraws).toNat t₅ :=
      ⟨h₅, P.q, P.width, P.mask, us₅, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => P.nonce i (by omega_arith), Nat.zero_le _⟩
    have sv₅ : Saved s₀ t₅.mem := sv₄.of_outs o₅ (by decide)
    refine WP.seq (WP.mono (sample_ok A S₅ hq) fun t₆ ⟨O₆, r0₆, h₆, o₆, _⟩ => ?_)
    have sv₆ : Saved s₀ t₆.mem := sv₅.of_outs o₆ (by decide)
    obtain ⟨d₆, Sm₆⟩ := O₆.smp
    have hR := rResult_eq A
    simp only [hc, ↓reduceIte] at hR
    unfold derived
    refine WP.seq (wp_cmp (op2_imm (by decide)) fun t₇ f₇ z₇ => WP.block_nil ?_)
    have h₇ := h₆.fupd f₇
    have m₇ : t₇.mem = t₆.mem := f₇.mem
    rw [r0₆, one_beq (by have := sampleStatus_le (spl s₀ 128 0); omega_arith)] at z₇
    cases hk : (spl s₀ 128 0).scalar with
    | none =>
      simp only [hk] at hR
      have hn := sampleStatus_none hk
      refine WP.ite false (by rw [eval_eq, z₇, decide_eq_false hn]) (fun e => Bool.noConfusion e)
        (fun _ => WP.block_nil ?_)
      refine ⟨h₇, ?_, ?_, fun e => by rw [hR] at e; exact absurd e hn, by rw [m₇]; exact sv₆⟩
      · rw [m₇, Sm₆.usedW, hR]; simp
      · rw [m₇, O₆.status, hR]
    | some k =>
      simp only [hk] at hR
      have h1 := sampleStatus_some hk
      refine WP.ite true (by rw [eval_eq, z₇, decide_eq_true h1]) (fun _ => ?_) (fun e => Bool.noConfusion e)
      refine WP.seq (WP.mono (deriveArgs_ok A h₇ (by rw [m₇]; exact sv₆)) fun t₈ ⟨h₈, m₈, C₈, _⟩ => ?_)
      refine WP.seq (WP.mono (callDerive_ok A h₈ C₈ derive) fun t₉ ⟨h₉, f₉, _, r0₉, out₉⟩ => ?_)
      refine wp_st h₉ (by decide) fun t₁₀ mm₁₀ h₁₀ => WP.block_nil ?_
      -- What the derivation read.
      have hres : deriveResult s₀ t₈ = Spec.Dsa.deriveKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key
          (Spec.Dsa.encodeBE (rInput s₀).qLen k) := by
        unfold deriveResult
        rw [key_bytes A h₈, m₈, m₇, ← hqn, O₆.nonce k hk, hqn]
        rfl
      rw [hres] at r0₉ out₉
      have sl₉ : ∀ d, d + 4 ≤ frameBytes → slot t₉.mem (rBase s₀) d = slot t₆.mem (rBase s₀) d := fun d hd => by
        rw [slot_keep f₉ (derive_keeps A) hd, m₈, m₇]
      have mem₁₀ : t₁₀.mem = t₉.mem.writeW (off (rBase s₀) oStatus) (t₉.gpr .r0) := mm₁₀.mem
      refine ⟨h₁₀, ?_, ?_, fun _ => ?_, ?_⟩
      · rw [mem₁₀, slot_write_ne _ _ _ (by decide) (by decide) (by decide), sl₉ _ (by decide), Sm₆.usedW, hR]
        simp
      · rw [mem₁₀, slot_write_self, r0₉, hR]
      · rw [mem₁₀, rBytes_frame (frame_store s₀ t₉.mem (by decide) _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact A.stackOut.symm)
          (by have := (s₀.gpr .r1).isLt; omega_arith), out₉, hR]
      · exact sv₆.of_slots fun d hd hd' => by
          rw [mem₁₀, slot_write_ne _ _ _ (by unfold oStatus; omega_arith) (by omega_arith) (by decide), sl₉ d hd']
  · have hc' : rChecked s₀ = false := by simpa using hc
    rw [hc'] at z₄
    refine WP.ite true (by rw [eval_eq, z₄]; rfl) (fun _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    have hR := rResult_unchecked A hc'
    refine ⟨h₄, ?_, ?_, fun e => by rw [hR] at e; exact absurd e (by decide), by rw [m₄]; exact sv₃⟩
    · rw [m₄, sl₃ _ (by decide), us₁, hR]; rfl
    · rw [m₄, sl₃ _ (by decide), st₁, hR]; rfl

end VG.Proof.Dsa.Arm.Key
