module

public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.AttemptRun
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Writes
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # After an attempt: the key, or one fewer scalar or key (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search

theorem exec_addImm_w {s : State} {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .w d n imm) s = some (s.write .w d ((s.gpr n).setWidth 32 + BitVec.ofNat 32 imm)) := by
  simp [exec, h, State.read]

theorem sub_beq : ∀ st < 4, ∀ k < 4,
    ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide

/-- The status `x9` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h9 : s.gpr .x9 = BitVec.ofNat 64 st) (hst : st < 4)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .x .x10) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.x10] s t := by
  have hk4 : k < 4 := by omega
  rcases hk with rfl | rfl | rfl <;>
  · refine WP.keep [.x10] ?_ (by decide) (by decide) (by decide +kernel)
    unfold test
    brun [h9]
    have hb := sub_beq st hst _ hk4
    simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
      Option.some.injEq] at hb ⊢
    exact hb

/-- The controller's word-only writes keep `x` and `y`. -/
theorem output_frame {p : KeyPublic} {original : State} (hi : KeyInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.xp p.len = Spec.Rsa.bytesAt m p.xp p.len ∧
      Spec.Rsa.bytesAt m' p.yp p.len = Spec.Rsa.bytesAt m p.yp p.len := by
  have hk := hi.len_lt
  have hpw := hi.writes_pairwise
  have hx : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    have := hpw.1.2.2.2
    rwa [hi.x_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← hi.2]; rfl] at this
  have hy : (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    have := hpw.2.1.2.2
    rwa [hi.y_eq, show inCtl original = ⟨p.control, 128⟩ by rw [← hi.2]; rfl] at this
  constructor <;> simp only [Spec.Rsa.bytesAt] <;> refine List.map_congr_left fun i hi => ?_
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hx)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hy)
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)

/-- The octets consumed by an attempt. -/
def advanceValues (p : KeyPublic) (used : Nat) : List (Nat × BitVec 64) :=
  [(9, p.rp + BitVec.ofNat 64 (used + p.len)), (10, BitVec.ofNat 64 (p.randLen - (used + p.len))),
    (11, BitVec.ofNat 64 (used + p.len))]

theorem advanceValues_bound (p : KeyPublic) (used : Nat) : ∀ e ∈ advanceValues p used, e.1 < 16 := by
  simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_advance_ok {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (.block advance) s fun t =>
      (t.mem = writeController s.mem p.control (advanceValues p used) ∧
        t.gpr .x9 = ((s.gpr .x0).setWidth 32).setWidth 64) ∧
        Keep [.x9, .x11, .x12, .x13, .x14] s t := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  have hv9 := h.header (j := 9) (v := p.rp + BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  have hv10 := h.header (j := 10) (v := BitVec.ofNat 64 (p.randLen - used)) (by simp [KeyPublic.headers])
  have hv11 := h.header (j := 11) (v := BitVec.ofNat 64 used) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2 hv9 hv10 hv11
  have hlen : p.randLen < 2 ^ 64 := by
    rw [← h.input.2]; exact BitVec.isLt _
  have e9 : p.rp + BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = p.rp + BitVec.ofNat 64 (used + p.len) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e10 : BitVec.ofNat 64 (p.randLen - used) - BitVec.ofNat 64 p.len =
      BitVec.ofNat 64 (p.randLen - (used + p.len)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by
      simp only [BitVec.le_def, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have e11 : BitVec.ofNat 64 used + BitVec.ofNat 64 p.len = BitVec.ofNat 64 (used + p.len) := by
    rw [← BitVec.ofNat_add]
  refine WP.keep [.x9, .x11, .x12, .x13, .x14] ?_ (by decide) (by decide) (by decide +kernel)
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, h.x19, exec_addImm_w (show 0 < 4096 by decide), hv2, hv9, hv10, hv11,
    a.ld 16 (by decide), a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide),
    a.st 72 (by decide), a.st 80 (by decide), a.st 88 (by decide), e9, e10, e11]
  rw [BitVec.add_zero]

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (advance ++ test 1)) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptPost p (keyRand original) used t ∧
      t.gpr .x9 = BitVec.ofNat 64 (attemptStatus p.a p.len ((keyRand original).drop used)) ∧
      isa.eval (.zero .x .x10) t =
        some (decide (attemptStatus p.a p.len ((keyRand original).drop used) = 1)) := by
  have hst : attemptStatus p.a p.len ((keyRand original).drop used) < 4 := by
    rcases attemptStatus_cases p.a p.len ((keyRand original).drop used) with he | he | he <;> omega
  rw [WP.block_append_iff]
  refine WP.mono (key_advance_ok h hroom) fun v ⟨⟨hmv, h9⟩, kv⟩ => ?_
  have hb := advanceValues_bound p used
  have hh : Slots v.mem p.control (p.headers (used + p.len) keys scalars) := by
    refine headers_after _ hb hmv ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, advanceValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  have hv := h.update (u := used + p.len) (k := keys) (c := scalars) hroom h.keys_le h.scalars_le _
    hb (by simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
           rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hmv kv.mono hh
  have hout := output_frame h.input (hmv ▸ writeController_frame s.mem p.control _ hb)
  have hpv : AttemptPost p (keyRand original) used v := by
    unfold AttemptPost at hp ⊢
    rw [hout.1, hout.2, kv.gpr .x0 (by decide)]
    exact hp
  have h9' : v.gpr .x9 = BitVec.ofNat 64 (attemptStatus p.a p.len ((keyRand original).drop used)) := by
    rw [h9]
    apply BitVec.eq_of_toNat_eq
    have := hp.1
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this ⊢
    omega
  refine WP.mono (test_ok h9' hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt⟩ => ?_
  exact ⟨hv.keep kt hmt, hpv.keep hmt (by rw [kt.gpr .x0 (by decide)]),
    (kt.gpr .x9 (by decide)).trans h9', he⟩

/-- The scalar of the attempt at `used`. -/
abbrev KeyPublic.scalarAt (p : KeyPublic) (rand : List Byte) (used : Nat) : Nat :=
  Spec.Ffdh.scalarOfOctets p.a ((rand.drop used).take p.len)

/-- The key search's result for an accepted attempt at `used`. -/
def acceptedResult (p : KeyPublic) (rand : List Byte) (used : Nat) : Spec.Ffdh.KeySearchResult :=
  ⟨.accepted (p.scalarAt rand used) (Spec.Rsa.powMod p.a.g (p.scalarAt rand used) p.a.p),
    used + p.len, [1]⟩

/-- Where an attempt at `used` leads. -/
def KeyClassified (p : KeyPublic) (original : State) (used keys scalars : Nat) (t : State) : Prop :=
  let st := attemptStatus p.a p.len ((keyRand original).drop used)
  if st = 1 then KeyDone p original (acceptedResult p (keyRand original) used) t
  else if st = 2 then KeyLive p original (used + p.len) keys (scalars - 1) t ∧ word t.mem p.control 112 = 4
  else KeyLive p original (used + p.len) (keys - 1) 128 t ∧ word t.mem p.control 112 = 4

/-- A terminal status written over a loop state, whose outputs are already
the result's. -/
theorem key_terminal_done {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : Nat) (hst : status = 1 ∨ status = 3)
    {r : Spec.Ffdh.KeySearchResult} (hu : r.used = used) (hs : r.status = status)
    (hr : r.retries = ⟨0, 0⟩) (ho : KeyOutput p r s.mem) :
    WP isa (.block (terminal status)) s (KeyDone p original r) := by
  refine WP.mono (key_terminal_live h hst) fun t ⟨ht, hm⟩ => ?_
  have hb := terminalValues_bound status
  have hst0 : status ≠ 0 := by omega
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  have hout := output_frame h.input (hm ▸ writeController_frame s.mem p.control _ hb)
  refine ht.done hu ?_ ?_ ?_
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false, hs]
  · change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
      word t.mem p.control (8 * 3)] = _
    rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_false, KeyPublic.policy, hr, hs, hst0]
    rw [h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
    rfl
  · unfold KeyOutput at ho ⊢
    rw [hout.1, hout.2]
    exact ho

theorem key_classify {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hk : 0 < keys) (hs : 0 < scalars) (hp : AttemptPost p (keyRand original) used s) :
    WP isa classify s (KeyClassified p original used keys scalars) := by
  unfold classify
  refine WP.seq (WP.mono (key_classify_head h hroom hp) fun u ⟨hu, hpu, hax, he⟩ => ?_)
  rcases attemptStatus_cases p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · rw [h1] at he
    refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_terminal_done (r := acceptedResult p (keyRand original) used) hu 1 (.inl rfl)
      rfl rfl rfl ?_) fun t ht => ?_
    rotate_left
    · dsimp only [KeyClassified]; rw [ite_eq_left h1]; exact ht
    have hpu' := hpu
    unfold AttemptPost at hpu'
    simp only [h1, ite_true] at hpu'
    exact hpu'.2
  · rw [h2] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv
    refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_scalar hv hs) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left h2]
    exact ht
  · rw [h3] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok hax (by decide) (.inr (.inl rfl)))
      fun v ⟨⟨he2, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (test_ok ((kv.gpr .x9 (by decide)).trans hax) (by decide) (.inr (.inr rfl)))
      fun w ⟨⟨he3, hmw⟩, kw⟩ => ?_)
    have hw := hv.keep kw hmw
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

end VG.Proof.Ffdh.AArch64.KeyGeneration
