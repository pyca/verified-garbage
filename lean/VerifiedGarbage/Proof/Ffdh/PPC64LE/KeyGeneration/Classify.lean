module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Call
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Classify
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-! # After an attempt: the key, or one fewer scalar or key (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.PPC64LE.Generation (Slots low32)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- The status `r9` minus `k`, compared with zero. -/
theorem test_ok {s : State} {st k : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 st) (hst : st < 4)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    WP isa (.block (test k)) s fun t =>
      (isa.eval (.zero .d .r10) t = some (decide (st = k)) ∧ t.mem = s.mem) ∧ Keep [.r10] s t := by
  have hb : ∀ st < 4, ∀ k < 4,
      ((BitVec.ofNat 64 st - BitVec.ofNat 64 k) == 0) = decide (st = k) := by decide
  rcases hk with rfl | rfl | rfl <;>
  · refine WP.keep [.r10] ?_ (by decide)
    unfold test
    prun [h9]
    refine (eval_zero _ _).trans ?_
    rw [RegUpd.gpr_write_self, hb st hst _ (by decide)]

/-- An attempt's outputs: the key, or zeros. -/
def AttemptOut (p : KeyPublic) (rand : List Byte) (used : Nat) (m : Mem) : Prop :=
  let st := attemptStatus p.a p.len (rand.drop used)
  let x := Spec.Ffdh.scalarOfOctets p.a ((rand.drop used).take p.len)
  if st = 1 then
    Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.i2osp x p.len ∧
      Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.i2osp (Spec.Rsa.powMod p.a.g x p.a.p) p.len
  else Spec.Rsa.bytesAt m p.xp p.len = List.replicate p.len 0 ∧
    Spec.Rsa.bytesAt m p.yp p.len = List.replicate p.len 0

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

theorem AttemptOut.frame {p : KeyPublic} {original : State} (hi : KeyInput p original)
    {rand : List Byte} {used : Nat} {m m' : Mem} (h : AttemptOut p rand used m)
    (hf : Frame [⟨p.control, 128⟩] m m') : AttemptOut p rand used m' := by
  have hout := output_frame hi hf
  unfold AttemptOut at h ⊢
  rw [hout.1, hout.2]
  exact h

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
        t.gpr .r9 = (s.gpr .r3 <<< 32) >>> 32) ∧
        Keep [.r3, .r4, .r9, .r11, .r12] s t := by
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
  refine WP.keep [.r3, .r4, .r9, .r11, .r12] ?_ (by decide)
  unfold advance writeController advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, h.r31, hv2, hv9, hv10, hv11,
    a.ld 16 (by decide), a.ld 72 (by decide), a.ld 80 (by decide), a.ld 88 (by decide),
    a.st 72 (by decide), a.st 80 (by decide), a.st 88 (by decide), e9, e10, e11]

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (advance ++ test 1)) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptOut p (keyRand original) used t.mem ∧
      t.gpr .r9 = BitVec.ofNat 64 (attemptStatus p.a p.len ((keyRand original).drop used)) ∧
      isa.eval (.zero .d .r10) t =
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
  have hpv : AttemptOut p (keyRand original) used v.mem :=
    AttemptOut.frame h.input (by unfold AttemptOut; exact hp.2)
      (hmv ▸ writeController_frame s.mem p.control _ hb)
  have h9' : v.gpr .r9 = BitVec.ofNat 64 (attemptStatus p.a p.len ((keyRand original).drop used)) :=
    h9.trans (low32 hp.1)
  refine WP.mono (test_ok h9' hst (.inl rfl)) fun t ⟨⟨he, hmt⟩, kt⟩ => ?_
  exact ⟨hv.keep kt hmt, hmt ▸ hpv, (kt.gpr .r9 (by decide)).trans h9', he⟩

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
    unfold AttemptOut at hpu
    simp only [h1, ite_true] at hpu
    exact hpu
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
    refine WP.seq (WP.mono (test_ok ((kv.gpr .r9 (by decide)).trans hax) (by decide) (.inr (.inr rfl)))
      fun w ⟨⟨he3, hmw⟩, kw⟩ => ?_)
    have hw := hv.keep kw hmw
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
