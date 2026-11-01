module

import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Dsa.Arm.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Dsa.Arm.RandomFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Calling the supplied-nonce signer (32-bit ARM)

`callArgs` loads the signer's register arguments and the seven words of its
stack arguments into `r0`–`r10` (`CallRegs`), and `callSigner` pushes those
words, as a frame of `r4`–`r11` below ours, and calls `vg_dsa_sign`
(`Entry.operation true`) under its own contract (`signArm`): it returns its
status in `r0` and writes `out` (`callSigner_ok`), changing only `out`,
`scratch` and the pushed words (`callWrites`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Arm.FrameStack (armStack belowA)

/-! ## The frame's saved words -/

/-- The callee-saved registers and the register arguments, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 9, slot m (rBase s₀) (4 * i) = s₀.gpr (savedRegs.getD i .r0)) ∧
    slot m (rBase s₀) oOut = s₀.gpr .r0 ∧ slot m (rBase s₀) oOutLen = s₀.gpr .r1 ∧
    slot m (rBase s₀) oUsedPtr = s₀.gpr .r2 ∧ slot m (rBase s₀) oKey = s₀.gpr .r3

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, d + 4 ≤ 36 ∨ 96 ≤ d → d + 4 ≤ 112 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨fun i hi => (he _ (.inl (by omega)) (by omega)).trans (h.1 i hi), (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.2.2⟩

/-- Memory changed only in ranges of `[36, 96)` keeps the saved words. -/
theorem Saved.of_outs {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)} (h : Saved s₀ m)
    (ho : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, 36 ≤ r.1 ∧ r.1 + r.2 ≤ 96) : Saved s₀ m' :=
  h.of_slots fun d hd hd' => slot_outs ho (fun r hr => by have := hrs r hr; omega) (by omega)

/-! ## The arguments -/

/-- The signer's arguments: `out`, `out_len`, `key`, `key_len` in `r0`–`r3`,
and `p_len`, `nonce`, `q_len`, `digest`, `digest_len`, `scratch`,
`scratch_len` in `r4`–`r10`. -/
structure CallRegs (s₀ u : State) : Prop where
  r0 : u.gpr .r0 = s₀.gpr .r0
  r1 : u.gpr .r1 = s₀.gpr .r1
  r2 : u.gpr .r2 = s₀.gpr .r3
  r3 : u.gpr .r3 = stackArg s₀ 0
  r4 : u.gpr .r4 = stackArg s₀ 1
  r5 : u.gpr .r5 = u.gpr .r11 + BitVec.ofNat 32 oNonce
  r6 : u.gpr .r6 = stackArg s₀ 2
  r7 : u.gpr .r7 = stackArg s₀ 3
  r8 : u.gpr .r8 = stackArg s₀ 4
  r9 : u.gpr .r9 = stackArg s₀ 7
  r10 : u.gpr .r10 = stackArg s₀ 8

abbrev callRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

theorem callArgs_ok {s₀ t : State} (A : RandomABI s₀) (h : RReady s₀ t) (sv : Saved s₀ t.mem) :
    WP isa (.block callArgs) t fun u => RReady s₀ u ∧ u.mem = t.mem ∧ CallRegs s₀ u ∧ Rest callRegs t u := by
  obtain ⟨-, s0, s1, -, s3⟩ := sv
  unfold callArgs
  refine wp_ld h (by decide) fun t₁ u₁ => wp_ld (h.upd u₁) (by decide) fun t₂ u₂ =>
    wp_ld ((h.upd u₁).upd u₂) (by decide) fun t₃ u₃ =>
    wp_ldArg A (((h.upd u₁).upd u₂).upd u₃) (j := 0) (by decide) fun t₄ u₄ =>
    wp_ldArg A ((((h.upd u₁).upd u₂).upd u₃).upd u₄) (j := 1) (by decide) fun t₅ u₅ =>
    wp_dp (op2_imm (by decide)) fun t₆ u₆ =>
    wp_ldArg A ((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆) (j := 2) (by decide) fun t₇ u₇ =>
    wp_ldArg A (((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇) (j := 3) (by decide) fun t₈ u₈ =>
    wp_ldArg A ((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈) (j := 4) (by decide)
      fun t₉ u₉ =>
    wp_ldArg A (((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉) (j := 7)
      (by decide) fun t₁₀ u₁₀ =>
    wp_ldArg A ((((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀)
      (j := 8) (by decide) fun t₁₁ u₁₁ => WP.block_nil ?_
  have h₁₁ := (((((((((((h.upd u₁).upd u₂).upd u₃).upd u₄).upd u₅).upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀).upd u₁₁)
  have R : Rest callRegs t t₁₁ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
    ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans ((u₁₀.rest (by decide)).trans
    (u₁₁.rest (by decide)))))))))))
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨h₁₁, by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, R⟩
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq,
      ↓reduceIte, u₁.gpr, s0]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, reduceCtorEq,
      ↓reduceIte, u₂.gpr, u₁.mem, s1]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, reduceCtorEq,
      ↓reduceIte, u₃.gpr, m₂, s3]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, u₅.get, reduceCtorEq, ↓reduceIte, u₄.gpr]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆.get, reduceCtorEq, ↓reduceIte, u₅.gpr]
  · rw [R.gpr .r11 (by decide)]
    simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, reduceCtorEq, ↓reduceIte, u₆.gpr]
    show t₅.gpr .r11 + _ = _
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, u₈.get, reduceCtorEq, ↓reduceIte, u₇.gpr]
  · simp only [u₁₁.get, u₁₀.get, u₉.get, reduceCtorEq, ↓reduceIte, u₈.gpr]
  · simp only [u₁₁.get, u₁₀.get, reduceCtorEq, ↓reduceIte, u₉.gpr]
  · simp only [u₁₁.get, reduceCtorEq, ↓reduceIte, u₁₀.gpr]
  · exact u₁₁.gpr

/-! ## The call -/

/-- The words the call pushes, as the signer's stack arguments. -/
abbrev callPush : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The nonce, in the frame. -/
abbrev nonceR (s₀ : State) : Region := ⟨off (rBase s₀) oNonce, (stackArg s₀ 2).toNat⟩

/-- The regions the signer is given, and where the call may write. -/
def callRd (s₀ : State) : List Region := [rKeyR s₀, nonceR s₀, rDigestR s₀, ⟨rLow s₀, 28⟩]
def callWr (s₀ : State) : List Region := [rOut s₀, rScratch s₀]
def callWrites (s₀ : State) : List Region := [rOut s₀, rScratch s₀, ⟨rLow s₀, 32⟩]

/-- The signer's entry state, from the state `u` before the push. -/
abbrev callEntryOf (s₀ u : State) : State := (pushed callPush u).callEntry.withRegions (callRd s₀) (callWr s₀)

/-- What the signer returns, from the bytes of the state `t` it is called in. -/
def callResult (s₀ t : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (stackArg s₀ 1).toNat (stackArg s₀ 2).toNat
    (Spec.Rsa.bytesAt t.mem (State.addr (s₀.gpr .r3)) (stackArg s₀ 0).toNat)
    (Spec.Rsa.bytesAt t.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat)
    (Spec.Rsa.bytesAt t.mem (State.addr (stackArg s₀ 3)) (stackArg s₀ 4).toNat)

theorem rBytes_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  unfold Spec.Rsa.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

/-- Word `i` a push stored. -/
theorem storeWords_read : ∀ (vs : List (BitVec 32)) (m : Mem) (a : BitVec 32), a.toNat + 4 * vs.length ≤ 2 ^ 32 →
    ∀ i (hi : i < vs.length), (storeWords m a vs).readW (State.addr (a + BitVec.ofNat 32 (4 * i))) 32 = vs[i]
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | v :: vs, m, a, h, 0, _ => by
    simp only [List.length_cons] at h
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 ∨ vs.length = 0 := by omega
    have hd : ∀ r ∈ [(⟨State.addr (a + 4), 4 * vs.length⟩ : Region)], Region.Disjoint ⟨State.addr a, 4⟩ r := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      rcases h4 with h4 | h4
      · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add h4]
        exact (Offset.disjoint_base _ (Nat.le_refl 4) (by have := VG.Proof.X25519.Arm.addr_toNat a; omega)).symm
      · rw [h4]; intro x _ h2; simp only [Region.Contains] at h2; omega
    rw [show 4 * 0 = 0 from rfl, BitVec.add_zero,
      (FrameStack.storeWords_frame vs (m.writeW (State.addr a) v) (a + 4) (by
        rcases h4 with h4 | h4
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (a := 4) (by omega), Nat.mod_eq_of_lt h4]; omega
        · rw [h4]; exact Nat.le_of_lt (BitVec.isLt _))).readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) hd (by decide), Mem.readW_writeW_self32]
    rfl
  | v :: vs, m, a, h, j + 1, hi => by
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 := by omega
    have ha : (a + 4).toNat = a.toNat + 4 := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 4) (by omega), Nat.mod_eq_of_lt h4]
    rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega]
    exact storeWords_read vs _ (a + 4) (by omega) j (by omega)

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u)
include A h

theorem call_sp_toNat : (u.sp - BitVec.ofNat 32 32).toNat = s₀.sp.toNat - 144 := by
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := s₀.sp.isLt
  unfold frameBytes; omega

theorem call_sp : State.addr (u.sp - BitVec.ofNat 32 32) = rLow s₀ := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.addr_toNat, call_sp_toNat A h, rLow_toNat A]

/-- The signer's stack argument `i`: the pushed register. -/
theorem callEntry_arg {i : Nat} (hi : i < 8) : stackArg (callEntryOf s₀ u) i = u.gpr callPush[i] := by
  have hs := call_sp_toNat A h
  have hb := A.stackBound
  have := storeWords_read (callPush.map u.gpr) u.mem (u.sp - BitVec.ofNat 32 32)
    (by rw [List.length_map]; show (u.sp - BitVec.ofNat 32 32).toNat + 4 * 8 ≤ 2 ^ 32; omega) i
    (by rw [List.length_map]; exact hi)
  simpa only [List.getElem_map, stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp, pushed, List.length_cons, List.length_nil] using this

/-- The push changes memory only in its words. -/
theorem call_sp_le : 4 * callPush.length ≤ u.sp.toNat := by
  have := s₀.sp.isLt
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [callPush, List.length_cons, List.length_nil]
  unfold frameBytes; omega

theorem call_push_frame : Frame [⟨rLow s₀, 32⟩] u.mem (pushed callPush u).mem := by
  have := FrameStack.pushed_frameA (rs := callPush) (s := u) (call_sp_le A h)
  rw [show 4 * callPush.length = 32 from rfl] at this
  simpa only [belowA, call_sp A h] using this

end

/-! ## The signer's precondition -/

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
include A h C

omit A h in
theorem ce_r0 : (callEntryOf s₀ u).gpr .r0 = s₀.gpr .r0 := (State.callEntry_gpr _ (by decide)).trans C.r0
omit A h in
theorem ce_r1 : (callEntryOf s₀ u).gpr .r1 = s₀.gpr .r1 := (State.callEntry_gpr _ (by decide)).trans C.r1
omit A h in
theorem ce_r2 : (callEntryOf s₀ u).gpr .r2 = s₀.gpr .r3 := (State.callEntry_gpr _ (by decide)).trans C.r2
omit A h in
theorem ce_r3 : (callEntryOf s₀ u).gpr .r3 = stackArg s₀ 0 := (State.callEntry_gpr _ (by decide)).trans C.r3
theorem ce_a0 : stackArg (callEntryOf s₀ u) 0 = stackArg s₀ 1 := (callEntry_arg A h (by decide)).trans C.r4
theorem ce_a1 : State.addr (stackArg (callEntryOf s₀ u) 1) = off (rBase s₀) oNonce := by
  rw [callEntry_arg A h (by decide)]
  show State.addr (u.gpr .r5) = _
  rw [C.r5]; exact h.rf.ea (by decide)
theorem ce_a2 : stackArg (callEntryOf s₀ u) 2 = stackArg s₀ 2 := (callEntry_arg A h (by decide)).trans C.r6
theorem ce_a3 : stackArg (callEntryOf s₀ u) 3 = stackArg s₀ 3 := (callEntry_arg A h (by decide)).trans C.r7
theorem ce_a4 : stackArg (callEntryOf s₀ u) 4 = stackArg s₀ 4 := (callEntry_arg A h (by decide)).trans C.r8
theorem ce_a5 : stackArg (callEntryOf s₀ u) 5 = stackArg s₀ 7 := (callEntry_arg A h (by decide)).trans C.r9
theorem ce_a6 : stackArg (callEntryOf s₀ u) 6 = stackArg s₀ 8 := (callEntry_arg A h (by decide)).trans C.r10

end

theorem nonce_sub {s₀ : State} (A : RandomABI s₀) : Region.Sub (nonceR s₀) (rStack s₀) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  rw [nonceR, rBase_off]; exact Offset.sub_base _ (by unfold oNonce; omega)

theorem low_sub (s₀ : State) {n : Nat} (hn : n ≤ 144) : Region.Sub (⟨rLow s₀, n⟩ : Region) (rStack s₀) := by
  have := Offset.sub_base (rLow s₀) (d := 0) (n := n) (k := 144) (by omega)
  rwa [BitVec.add_zero] at this

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
include A h C

theorem call_pre : signPre (callEntryOf s₀ u) := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hsp : State.addr (callEntryOf s₀ u).sp = rLow s₀ := call_sp A h
  have hspn : (callEntryOf s₀ u).sp.toNat = s₀.sp.toNat - 144 := call_sp_toNat A h
  unfold signPre
  simp only [State.withRegions_rd, State.withRegions_wr, ce_r0 C, ce_r1 C, ce_r2 C, ce_r3 C,
    ce_a0 A h C, ce_a1 A h C, ce_a2 A h C, ce_a3 A h C, ce_a4 A h C, ce_a5 A h C, ce_a6 A h C, hsp, hspn]
  refine ⟨by have := A.stackLow; omega, rfl, rfl, A.outKey, A.stackOut.symm.sub_right (nonce_sub A),
    A.outDigest, A.outScratch, A.stackOut.symm.sub_right (low_sub s₀ (by decide)), A.keyScratch,
    A.stackScratch.sub_left (nonce_sub A), A.digestScratch, A.stackScratch.symm.sub_right (low_sub s₀ (by decide)),
    A.outBound, A.keyBound, ?_, A.digestBound, A.scratchBound, A.lengths, A.outLength, A.keyLength, ?_⟩
  · show (stackArg (callEntryOf s₀ u) 1).toNat + _ ≤ _
    rw [← VG.Proof.X25519.Arm.addr_toNat, ce_a1 A h C, rBase_off, off_rLow_toNat A (by unfold oNonce; omega),
      rLow_toNat A]
    have := A.stackLow; have := A.stackBound; unfold oNonce; omega
  · have := A.scratchLength; unfold Spec.Dsa.randomSignScratchWords at this; omega

/-- The bytes the signer reads are those of `u`, which the push leaves. -/
theorem signRes_call : signRes (callEntryOf s₀ u) = callResult s₀ u := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hf := call_push_frame A h
  have e : ∀ {p : Addr} {n : Nat}, (rStack s₀).Disjoint ⟨p, n⟩ → n ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt (pushed callPush u).mem p n = Spec.Rsa.bytesAt u.mem p n := fun hd hn =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left (low_sub s₀ (by decide))).symm) hn
  unfold signRes callResult
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C, ce_a0 A h C, ce_a1 A h C,
    ce_a2 A h C, ce_a3 A h C, ce_a4 A h C]
  have en : Spec.Rsa.bytesAt (pushed callPush u).mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat =
      Spec.Rsa.bytesAt u.mem (off (rBase s₀) oNonce) (stackArg s₀ 2).toNat := by
    refine rBytes_frame hf (fun r hr => ?_) (by have := (stackArg s₀ 2).isLt; omega)
    simp only [List.mem_singleton] at hr; subst hr
    rw [rBase_off]
    exact Offset.disjoint_base _ (by unfold oNonce; omega) (by unfold oNonce; omega)
  rw [e A.stackKey (by have := (stackArg s₀ 0).isLt; omega), e A.stackDigest (by have := (stackArg s₀ 4).isLt; omega),
    en]

omit C in
theorem call_covers :
    Covers (callRd s₀ ++ callWr s₀) ((pushed callPush u).rd ++ (pushed callPush u).wr) ∧
      Covers (callWr s₀) (pushed callPush u).wr := by
  have hql := rQBytes_le A
  have hqn := rQBytes_length A
  have hpw : (pushed callPush u).wr = ⟨rLow s₀, 32⟩ :: ⟨rBase s₀, frameBytes⟩ :: s₀.wr := by
    rw [pushed_wr, h.wr, show 4 * callPush.length = 32 from rfl, call_sp A h]
  have hpr : (pushed callPush u).rd = s₀.rd := by rw [pushed_rd, h.rd]
  have hw : Covers (callWr s₀) (pushed callPush u).wr := by
    rw [hpw, A.wr]; exact Covers.of_mem fun r hr => by
      simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> simp
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) hw.right, hw⟩
  rw [hpr, hpw, A.rd]
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · refine ⟨⟨rBase s₀, frameBytes⟩, by simp, oNonce, rfl, ?_⟩
    show oNonce + (stackArg s₀ 2).toNat ≤ frameBytes
    unfold oNonce frameBytes; omega
  · exact ⟨_, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · exact ⟨⟨rLow s₀, 32⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩

end

/-- `vg_dsa_sign` uses no stack of its own. -/
theorem sign_armStack : armStack (Entry.operation true) = 0 := by decide +kernel

theorem status_lt (r : Option (List Byte)) : Spec.Dsa.signStatus r < 2 := by
  unfold Spec.Dsa.signStatus; split <;> decide

/-- The call of the signer, its stack arguments pushed. -/
theorem callSigner_ok {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u) (name : String) :
    WP isa (callSigner name (Entry.operation true)) u fun v => RReady s₀ v ∧ Frame (callWrites s₀) u.mem v.mem ∧
      (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], v.gpr r = u.gpr r) ∧
      v.gpr .r0 = BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ u)) ∧
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (callResult s₀ u).getD (List.replicate (s₀.gpr .r1).toNat 0) := by
  obtain ⟨hc, hcw⟩ := call_covers A h
  unfold callSigner
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (call_sp_le A h) (by decide) ?_
  refine FrameStack.WP.callF (k := signArm) (fun s hs => ?_) (call_pre A h C) hc hcw
    (by rw [sign_armStack]; exact Nat.zero_le _) fun s' hrd hwr hsp hf hpres hpost => ?_
  · obtain ⟨t, s', e, ha, hp⟩ := sign_correct hs
    exact ⟨t, s', e, ha, hp⟩
  rw [sign_armStack] at hf
  have hpu : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = u.gpr r := fun r hr hl => by rw [hpres r hr hl, pushed_gpr]
  -- Where the call wrote.
  have Fc : Frame (callWrites s₀) u.mem s'.mem := by
    refine ((call_push_frame A h).mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; simp [callWrites]
    · simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp [callWrites], fun _ h => h⟩
      · exact ⟨_, by simp [callWrites], fun _ h => h⟩
      · exact ⟨⟨rLow s₀, 32⟩, by simp [callWrites], fun _ hc => absurd hc (by simp [Region.Contains])⟩
  have hspv : s'.sp + BitVec.ofNat 32 (4 * callPush.length) = u.sp := by
    rw [hsp, pushed_sp, BitVec.sub_add_cancel]
  have hv : RReady s₀ (popped .r4 (4 * callPush.length) s') := by
    refine ⟨⟨?_, ?_, ?_, h.rf.nowrap⟩, ?_, ?_, ?_, ?_⟩
    · rw [popped_gpr (by decide), hpu .r11 (by decide) (by decide)]; exact h.rf.base
    · rw [popped_wr, hwr, pushed_wr, List.tail_cons]; exact h.rf.wr
    · rw [popped_rd, hrd, pushed_rd]; exact h.rf.args
    · rw [popped_sp, hspv]; exact h.sp
    · rw [popped_rd, hrd, pushed_rd]; exact h.rd
    · rw [popped_wr, hwr, pushed_wr, List.tail_cons]; exact h.wr
    · rw [popped_mem]
      refine h.frame.trans (Fc.sub fun r hr => ?_)
      simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp [rWrites], fun _ h => h⟩
      · exact ⟨_, by simp [rWrites], fun _ h => h⟩
      · exact ⟨rStack s₀, by simp [rWrites], low_sub s₀ (by decide)⟩
  obtain ⟨hr, hb⟩ := hpost
  rw [State.withRegions_gpr, BitVec.setWidth_append_eq_right, signRes_call A h C] at hr
  rw [State.withRegions_mem, ce_r0 C, ce_r1 C, signRes_call A h C] at hb
  refine ⟨hv, by rw [popped_mem]; exact Fc, fun r hr' => ?_, ?_, by rw [popped_mem]; exact hb⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (popped_gpr (by decide) _ _).trans (hpu _ (by decide) (by decide))
  · rw [popped_gpr (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [hr, toNat_imm (by have := status_lt (callResult s₀ u); omega)]

end VG.Proof.Dsa.Arm
