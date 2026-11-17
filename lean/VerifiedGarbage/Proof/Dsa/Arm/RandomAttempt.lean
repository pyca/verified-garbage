module

public import VerifiedGarbage.Proof.Dsa.RandomSignTrace
public import VerifiedGarbage.Proof.Dsa.Arm.RandomDraw
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
public import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! ### `Dsa.Arm.RandomCall`, which this module and modules that import it used -/

section

/-!
# Calling the supplied-nonce signer (32-bit ARM)

`callArgs` loads the signer's register arguments and the seven words of its
stack arguments into `r0`–`r10` (`CallRegs`), and `callSigner` pushes those
words, as a frame of `r4`–`r11` below ours, and calls `vg_dsa_sign`
(a `Signer`, such as `Entry.operation true`) under its contract (`signArmWith`): it returns its
status in `r0` and writes `out` (`callSigner_ok`), changing only `out`,
`scratch` and the pushed words (`callWrites`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)
open VG.Arm.FrameStack (armStack belowA)

variable {umaal : Bool}

/-! ## The frame's saved words -/

/-- The callee-saved registers and the register arguments, in their slots. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 9, slot m (rBase s₀) (4 * i) = s₀.gpr (savedRegs.getD i .r0)) ∧
    slot m (rBase s₀) oOut = s₀.gpr .r0 ∧ slot m (rBase s₀) oOutLen = s₀.gpr .r1 ∧
    slot m (rBase s₀) oUsedPtr = s₀.gpr .r2 ∧ slot m (rBase s₀) oKey = s₀.gpr .r3

theorem Saved.of_slots {s₀ : State} {m m' : Mem} (h : Saved s₀ m)
    (he : ∀ d, d + 4 ≤ 36 ∨ 96 ≤ d → d + 4 ≤ 112 → slot m' (rBase s₀) d = slot m (rBase s₀) d) : Saved s₀ m' :=
  ⟨fun i hi => (he _ (.inl (by omega_using [hi])) (by omega_using [hi])).trans (h.1 i hi), (he _ (by decide) (by decide)).trans h.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.1, (he _ (by decide) (by decide)).trans h.2.2.2.1,
    (he _ (by decide) (by decide)).trans h.2.2.2.2⟩

/-- Memory changed only in ranges of `[36, 96)` keeps the saved words. -/
theorem Saved.of_outs {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)} (h : Saved s₀ m)
    (ho : Outs (rBase s₀) rs m m') (hrs : ∀ r ∈ rs, 36 ≤ r.1 ∧ r.1 + r.2 ≤ 96) : Saved s₀ m' :=
  h.of_slots fun d hd hd' => slot_outs ho (fun r hr => by have := hrs r hr; omega_using [hd, this]) (by omega_using [hd'])

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
    have h4 : a.toNat + 4 < 2 ^ 32 ∨ vs.length = 0 := by omega_using [h]
    have hd : ∀ r ∈ [(⟨State.addr (a + 4), 4 * vs.length⟩ : Region)], Region.Disjoint ⟨State.addr a, 4⟩ r := by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      rcases h4 with h4 | h4
      · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add h4]
        exact (Offset.disjoint_base _ (Nat.le_refl 4) (by have := VG.Proof.X25519.Arm.addr_toNat a; omega_using [h])).symm
      · rw [h4]; intro x _ h2; simp only [Region.Contains] at h2; omega_using [h2]
    rw [show 4 * 0 = 0 from rfl, BitVec.add_zero,
      (FrameStack.storeWords_frame vs (m.writeW (State.addr a) v) (a + 4) (by
        rcases h4 with h4 | h4
        · rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]; omega_using [h]
        · rw [h4]; exact Nat.le_of_lt (BitVec.isLt _))).readW (r := ⟨State.addr a, 4⟩)
        (Region.contains_self _ _) hd (by decide), Mem.readW_writeW_self32]
    rfl
  | v :: vs, m, a, h, j + 1, hi => by
    simp only [List.length_cons] at h hi
    simp only [storeWords]
    have h4 : a.toNat + 4 < 2 ^ 32 := by omega_using [h, hi]
    have ha : (a + 4).toNat = a.toNat + 4 := by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 4) (by omega_using []), Nat.mod_eq_of_lt h4]
    rw [show a + BitVec.ofNat 32 (4 * (j + 1)) = a + 4 + BitVec.ofNat 32 (4 * j) by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_using []]
    exact storeWords_read vs _ (a + 4) (by omega_using [h, ha]) j (by omega_using [hi])

section
variable {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u)
include A h

theorem call_sp_toNat : (u.sp - BitVec.ofNat 32 32).toNat = s₀.sp.toNat - 144 := by
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := s₀.sp.isLt
  unfold frameBytes; omega_arith

theorem call_sp : State.addr (u.sp - BitVec.ofNat 32 32) = rLow s₀ := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.addr_toNat, call_sp_toNat A h, rLow_toNat A]

/-- The signer's stack argument `i`: the pushed register. -/
theorem callEntry_arg {i : Nat} (hi : i < 8) : stackArg (callEntryOf s₀ u) i = u.gpr callPush[i] := by
  have hs := call_sp_toNat A h
  have hb := A.stackBound
  have := storeWords_read (callPush.map u.gpr) u.mem (u.sp - BitVec.ofNat 32 32)
    (by rw [List.length_map]; show (u.sp - BitVec.ofNat 32 32).toNat + 4 * 8 ≤ 2 ^ 32; omega_using [hs]) i
    (by rw [List.length_map]; exact hi)
  simpa only [List.getElem_map, stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp, pushed, List.length_cons, List.length_nil] using this

/-- The push changes memory only in its words. -/
theorem call_sp_le : 4 * callPush.length ≤ u.sp.toNat := by
  have := s₀.sp.isLt
  have := A.stackLow
  rw [h.sp, BitVec.toNat_sub, BitVec.toNat_ofNat]
  simp only [callPush, List.length_cons, List.length_nil]
  unfold frameBytes; omega_using [this]

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
  have := Offset.sub_base (rLow s₀) (d := 0) (n := n) (k := 144) (by omega_using [hn])
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
  refine ⟨by have := A.stackLow; omega_using [], rfl, rfl, A.outKey, A.stackOut.symm.sub_right (nonce_sub A),
    A.outDigest, A.outScratch, A.stackOut.symm.sub_right (low_sub s₀ (by decide)), A.keyScratch,
    A.stackScratch.sub_left (nonce_sub A), A.digestScratch, A.stackScratch.symm.sub_right (low_sub s₀ (by decide)),
    A.outBound, A.keyBound, ?_, A.digestBound, A.scratchBound, A.lengths, A.outLength, A.keyLength, ?_⟩
  · show (stackArg (callEntryOf s₀ u) 1).toNat + _ ≤ _
    rw [← VG.Proof.X25519.Arm.addr_toNat, ce_a1 A h C, rBase_off, off_rLow_toNat A (by unfold oNonce; omega_using []),
      rLow_toNat A]
    have := A.stackLow; have := A.stackBound; unfold oNonce; omega
  · have := A.scratchLength; unfold Spec.Dsa.randomSignScratchWords at this; omega_using [this]

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
    refine rBytes_frame hf (fun r hr => ?_) (by have := (stackArg s₀ 2).isLt; omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    rw [rBase_off]
    exact Offset.disjoint_base _ (by unfold oNonce; omega_using []) (by unfold oNonce; omega_using [])
  rw [e A.stackKey (by have := (stackArg s₀ 0).isLt; omega_using []), e A.stackDigest (by have := (stackArg s₀ 4).isLt; omega_using []),
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

/-- `vg_dsa_sign` uses no stack of its own. -/
theorem sign_armStack : armStack (Entry.operation umaal true) = 0 := by cases umaal <;> decide +kernel

open VG.Spec.Rsa (bytesAt) in
/-- `signArm` under an extra precondition `valid` on the exact packed key
bytes: with `fun _ _ _ => true` it is `signArm`, with
`validatePrivateKeyBytes` the contract of a signing attempt for a validated
private key. -/
def signArmWith (valid : Nat → Nat → List Byte → Bool) : Contract isa where
  pre s := signPre s ∧
    valid (arg s 0).toNat (arg s 2).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) = true
  post := signArm.post
  pub := signArm.pub

/-- A supplied-nonce signer the randomized wrapper calls: the fully checked
signer (`valid` always true), or the signer for a validated private key
(`valid` is `validatePrivateKeyBytes`). -/
structure Signer where
  code : Prog isa
  valid : Nat → Nat → List Byte → Bool
  correct : ∀ s, (signArmWith valid).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ signArm.post s s'
  constantTime : ConstantTime isa (signArmWith valid).pre signArm.pub code
  stack : armStack code = 0

/-- The signer's validity of the wrapper's key. -/
def RValid (S : Signer) (s₀ : State) : Prop :=
  S.valid (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key = true

/-- The key the signer reads at its entry is the wrapper's. -/
theorem entry_key {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u) :
    Spec.Rsa.bytesAt (callEntryOf s₀ u).mem (State.addr ((callEntryOf s₀ u).gpr .r2))
      ((callEntryOf s₀ u).gpr .r3).toNat = (rInput s₀).key := by
  have hql := rQBytes_le A
  simp only [State.withRegions_mem, State.callEntry_mem, ce_r2 C, ce_r3 C]
  rw [rBytes_frame (call_push_frame A h) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (A.stackKey.sub_left (low_sub s₀ (by decide))).symm)
      (by have := (stackArg s₀ 0).isLt; omega_using []), callKey A h]

/-- The signer's contract at the wrapper's call, for a key it accepts. -/
theorem call_pre_with (S : Signer) {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
    (V : RValid S s₀) : (signArmWith S.valid).pre (callEntryOf s₀ u) := by
  refine ⟨call_pre A h C, ?_⟩
  show S.valid (stackArg (callEntryOf s₀ u) 0).toNat (stackArg (callEntryOf s₀ u) 2).toNat _ = true
  rw [entry_key A h C, ce_a0 A h C, ce_a2 A h C]
  exact V

theorem status_lt (r : Option (List Byte)) : Spec.Dsa.signStatus r < 2 := by
  unfold Spec.Dsa.signStatus; split <;> decide

/-- The call of the signer, its stack arguments pushed. -/
theorem callSigner_ok (S : Signer) {s₀ u : State} (A : RandomABI s₀) (h : RReady s₀ u) (C : CallRegs s₀ u)
    (V : RValid S s₀) (name : String) :
    WP isa (callSigner name S.code) u fun v => RReady s₀ v ∧ Frame (callWrites s₀) u.mem v.mem ∧
      (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], v.gpr r = u.gpr r) ∧
      v.gpr .r0 = BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ u)) ∧
      Spec.Rsa.bytesAt v.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat =
        (callResult s₀ u).getD (List.replicate (s₀.gpr .r1).toNat 0) := by
  obtain ⟨hc, hcw⟩ := call_covers A h
  unfold callSigner
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (call_sp_le A h) (by decide) ?_
  refine FrameStack.WP.callF (k := signArmWith S.valid) (fun s hs => S.correct s hs) (call_pre_with S A h C V)
    hc hcw (by rw [S.stack]; exact Nat.zero_le _) fun s' hrd hwr hsp hf hpres hpost => ?_
  rw [S.stack] at hf
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
    rw [hr, toNat_imm (by have := status_lt (callResult s₀ u); omega_using [hr])]

end VG.Proof.Dsa.Arm

end

end

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
  have hs : (rStack s₀).Contains (off (rLow s₀) (32 + d)) 1 := Offset.contains_base _ (by omega_using [h₂, hF]) (by omega_using [h₂, hF])
  refine hf _ fun r hr => ?_
  simp only [callWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.stackOut _ hs
  · exact A.stackScratch _ hs
  · exact (Offset.disjoint_base (rLow s₀) (d := 32 + d) (n := 1) (k := 32) (by omega_using []) (by omega_using [h₂, hF])) _
      (Region.contains_self _ _)

theorem call_frame_slot {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (hf : Frame (callWrites s₀) m m')
    {d : Nat} (h₂ : d + 4 ≤ frameBytes) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  Mem.readW_congr fun i hi => by
    have : i < 4 := hi
    rw [show off (rBase s₀) d + BitVec.ofNat 64 i = off (rBase s₀) (d + i) by
      rw [off, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact call_frame_byte A hf (by omega_using [h₂, hi])

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
  · rw [call_frame_byte A hf (by unfold oNonce frameBytes; omega_using [hql, hi])]; exact S.pad i hi

theorem Saved.after_call {s₀ : State} (A : RandomABI s₀) {m m' : Mem} (sv : Saved s₀ m)
    (hf : Frame (callWrites s₀) m m') : Saved s₀ m' :=
  sv.of_slots fun _ _ hd => call_frame_slot A hf hd

/-! ## The status -/

/-- Record the signer's status `st`, and test it. -/
theorem finHead_ok {s₀ u : State} (h : RReady s₀ u) {k : Nat} (hst : k ≤ 1)
    (he : u.gpr .r0 = BitVec.ofNat 32 k) :
    WP isa (.block [st .r0 oStatus, .cmp .r0 (.imm 0)]) u fun v => RReady s₀ v ∧
      Rest [] u v ∧ v.mem = u.mem.writeW (off (rBase s₀) oStatus) (BitVec.ofNat 32 k) ∧
      v.z = decide (k = 0) := by
  refine wp_st h (by decide) fun v₁ m₁ h₁ => wp_cmp0 fun v₂ f₂ z₂ => WP.block_nil ?_
  refine ⟨h₁.fupd f₂, (m₁.rest _).trans (f₂.rest _), by rw [f₂.mem, m₁.mem, he], ?_⟩
  rw [z₂, m₁.gpr, he, ofNat_beq_zero (by omega_using [hst])]

/-- Spend an attempt. -/
theorem finDec_ok {s₀ v₂ : State} (h₂ : RReady s₀ v₂) {f : Nat}
    (ha : slot v₂.mem (rBase s₀) oAttempts = BitVec.ofNat 32 (f + 1)) (hf : f + 1 ≤ 8) :
    WP isa (.block [ld .r0 oAttempts, .subs .r0 .r0 (.imm 1), st .r0 oAttempts]) v₂
      fun v₅ => RReady s₀ v₅ ∧ Rest [.r0] v₂ v₅ ∧
        v₅.mem = v₂.mem.writeW (off (rBase s₀) oAttempts) (BitVec.ofNat 32 f) ∧ v₅.z = decide (f = 0) := by
  refine wp_ld h₂ (by decide) fun v₃ u₃ => wp_dec fun v₄ u₄ z₄ =>
    wp_stF ((h₂.upd u₃).upd u₄) (by decide) fun v₅ m₅ h₅ zz₅ _ => WP.block_nil ?_
  have e₄ : v₄.gpr .r0 = BitVec.ofNat 32 f := by rw [u₄.gpr, u₃.gpr, ha, ofNat_sub_one (by omega_using [])]; rfl
  refine ⟨h₅, (u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (m₅.rest _)), by
    rw [m₅.mem, e₄, u₄.mem, u₃.mem], ?_⟩
  rw [zz₅, z₄, u₃.gpr, ha, ofNat_sub_one (by omega_using []), Nat.add_sub_cancel, ofNat_beq_zero (by omega_using [hf])]

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
  · have h1 : k = 1 := by omega_using [hst, h0]
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
      · exact h₂) (by omega_using [h₀])
  refine ⟨hr, (hs _ (by decide) (by decide) (by decide)).trans S.q,
    (hs _ (by decide) (by decide) (by decide)).trans S.width,
    (hs _ (by decide) (by decide) (by decide)).trans S.mask, (hs _ (by decide) (by decide) (by decide)).trans S.usedW,
    (hs _ (by decide) (by decide) (by decide)).trans S.drawsW, fun i hi => ?_, S.usedBound⟩
  have hle : ∀ r ∈ ([(oAttempts, 4), (oStatus, 4)] : List (Nat × Nat)), r.1 + r.2 ≤ oNonce := by decide
  rw [hm _ fun r hr => by
    have := hle r hr
    rw [ofs_off0 _ (by unfold oNonce; omega_using [hql, hi])]
    right; omega_using [this]]
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
    refine hd _ ?_ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_using [hi]) (by omega_using [hn, hi]))
    have he : p + BitVec.ofNat 64 i = off (rBase s₀) (ofs (rBase s₀) (p + BitVec.ofNat 64 i)) := by
      simp only [ofs, off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm (rBase s₀), BitVec.sub_add_cancel]
    rw [he, rBase_off]
    exact Offset.contains_base _ (by omega_using [hx]) (by omega_using [hx])
  · right; omega_using [hb, hx]

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
    omega_using [hk, h, this]

/-- What an attempt from `used` with `f + 1` attempts left leaves: another
attempt to make after a retry, which its signing trace records, or the result. -/
def AttemptOut (s₀ : State) (used f : Nat) (u : State) : Prop :=
  (slot u.mem (rBase s₀) oStatus = 4 ∧ 1 ≤ f ∧ Att s₀ (used + (spl s₀ 128 used).used) f u ∧
    VG.Proof.Dsa.randomSigningTrace (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace =
      6 :: (VG.Proof.Dsa.randomSignRemaining (rInput s₀) (used + (spl s₀ 128 used).used) f).trace) ∨
    (slot u.mem (rBase s₀) oStatus ≠ 4 ∧ Done s₀ u ∧
      ¬ ((VG.Proof.Dsa.randomSigningTrace
        (VG.Proof.Dsa.randomSignRemaining (rInput s₀) used (f + 1)).trace).head? = some 6 ∧ 1 ≤ f))

theorem attempt_ok (S : Signer) (name : String) {s₀ t : State} (A : RandomABI s₀) {used f : Nat}
    (T : Att s₀ used (f + 1) t) (hf : f + 1 ≤ 8) (hq : 1 < rq s₀) (V : RValid S s₀) :
    WP isa (attempt name S.code) t fun u => AttemptOut s₀ used f u := by
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
  rw [r0₁, one_beq (by omega_using [hle])] at z₂
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
      rw [toNat_imm (by omega_using [hle])] at this
      exact absurd this (by show _ ≠ 4; omega_using [hle])
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
    refine WP.seq (WP.mono (callSigner_ok S A h₃ C₃ V name) fun u₄ ⟨h₄, f₄, _, r0₄, out₄⟩ => ?_)
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
        refine .inr ⟨by rw [st₅]; decide, ⟨⟨d', ?_⟩, by rw [st₅, hstat]; rfl, fun e => absurd e (by omega_using [hstat]), sv₅⟩,
          fun h => absurd h.2 (by decide)⟩
        have e : (rResult s₀).used = used + (spl s₀ 128 used).used := (Nat.zero_add _).symm.trans hused
        rw [e]; exact S₅
      · refine .inl ⟨by rw [st₅]; simp only [hf0, ↓reduceIte], by omega_using [hf0], ⟨⟨d', S₅⟩, at₅, sv₅, R'⟩,
          ?_⟩
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega_using [hf0]⟩
        exact VG.Proof.Dsa.random_sign_trace_retry _ _ _ _ hsc hsb

end VG.Proof.Dsa.Arm
