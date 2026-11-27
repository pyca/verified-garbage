module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptRun
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Exits
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Data
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Ffdh.X86_64.Cached.SearchProof.Rejects`, which this module and modules that import it used -/

section

/-! # The key-generation controller's rejections: one fewer scalar or key -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue
  controllerValue_unchanged)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- `rax`, a status, compared with 1, 2 or 3. -/
theorem rax_guard {s : State} {status : Nat} (hs : s.gpr .rax = BitVec.ofNat 64 status)
    (h64 : status < 2 ^ 64) (n : BitVec 32) (k : Nat) (hn : BitVec.signExtend 64 n = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) :
    WP isa (.block [.alu .cmp .rax (.imm n)]) s fun t =>
      (eval .e t = some (decide (status = k)) ∧ t.mem = s.mem ∧ t.gpr .rax = s.gpr .rax) ∧
        Keep [.rax] s t := by
  have he : (BitVec.ofNat 64 status == BitVec.ofNat 64 k) = decide (status = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hk]
  refine WP.keep [.rax] ?_ rfl
  xrun [hs, eval, sub_beq_zero, hn, he]

def scalarValues (scalars : Nat) : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 (scalars - 1)), (14, 4)]

def publicValues (keys : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (keys - 1)), (1, 128), (14, 4)]

theorem scalarValues_bound (scalars : Nat) : ∀ e ∈ scalarValues scalars, e.1 < 16 := by
  simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem publicValues_bound (keys : Nat) : ∀ e ∈ publicValues keys, e.1 < 16 := by
  simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_rejected_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : 0 < scalars) :
    WP isa (.block rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ word t.mem p.control 112 = 4 := by
  have scr := h.input.control_scr (t := s) h.wr
  have hst : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv1
  have e1 : BitVec.ofNat 64 scalars - BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (scalars - 1) := by
    have := h.scalars_le
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from by decide,
      BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega_using [])]; omega_using [hs, this])]
    simp only [BitVec.toNat_ofNat]
    omega_using [this]
  have e1' : BitVec.ofNat 64 scalars - 1 = BitVec.ofNat 64 (scalars - 1) := by
    rw [← e1]; rfl
  have h4 : BitVec.setWidth 64 (4 : BitVec 32) = 4 := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = writeController s.mem p.control (scalarValues scalars)) ?_ rfl) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedScalar writeController scalarValues
    simp only [List.foldl_cons, List.foldl_nil]
    xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, hv1, e1, e1', h4,
      hl 8 (by decide), hst 8 (by decide), hst 112 (by decide)]
  have hh : Slots t.mem p.control (p.headers used keys (scalars - 1)) := by
    refine headers_after _ (scalarValues_bound scalars) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le h.keys_le (by have := h.scalars_le; omega_using [this]) _ (scalarValues_bound scalars)
    (by simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (scalarValues_bound scalars) 14 (by decide)]
  simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

theorem key_rejected_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hk : 0 < keys) :
    WP isa (.block rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ word t.mem p.control 112 = 4 := by
  have scr := h.input.control_scr (t := s) h.wr
  have hst : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hl0 : InRegions (s.rd ++ s.wr) p.control 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hs0 : InRegions s.wr p.control 8 := by simpa only [BitVec.add_zero] using hst 0 (by decide)
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hv0
  have e0 : BitVec.ofNat 64 keys - BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (keys - 1) := by
    have := h.keys_le
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from by decide,
      BitVec.toNat_sub_of_le (by
        simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega_using [])]; omega_using [hk, this])]
    simp only [BitVec.toNat_ofNat]
    omega_using [this]
  have e0' : BitVec.ofNat 64 keys - 1 = BitVec.ofNat 64 (keys - 1) := by
    rw [← e0]; rfl
  have h4 : BitVec.setWidth 64 (4 : BitVec 32) = 4 := by decide
  have h128 : BitVec.setWidth 64 (128 : BitVec 32) = 128 := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = writeController s.mem p.control (publicValues keys)) ?_ rfl) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedPublic writeController publicValues
    simp only [List.foldl_cons, List.foldl_nil]
    xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, Nat.mul_zero,
      BitVec.add_zero, hv0, e0, e0', h4, h128, hl0, hs0, hst 8 (by decide), hst 112 (by decide)]
  have hh : Slots t.mem p.control (p.headers used (keys - 1) 128) := by
    refine headers_after _ (publicValues_bound keys) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le (by have := h.keys_le; omega_using [this]) (by decide) _ (publicValues_bound keys)
    (by simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (publicValues_bound keys) 14 (by decide)]
  simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! # After an attempt: the key, or one fewer scalar or key -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged normalized_status)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The scalar of the attempt at `used`. -/
abbrev KeyPublic.scalarAt (p : KeyPublic) (rand : List Byte) (used : Nat) : Nat :=
  Spec.Ffdh.vettedScalarOfOctets p.a ((rand.drop used).take p.len)

/-- The key search's result for an accepted attempt at `used`. -/
def acceptedResult (p : KeyPublic) (rand : List Byte) (used : Nat) : Spec.Ffdh.KeySearchResult :=
  ⟨.accepted (p.scalarAt rand used) (Spec.Rsa.powMod p.a.g (p.scalarAt rand used) p.a.p),
    used + p.len, [1]⟩

/-- Where an attempt at `used` leads. -/
def KeyClassified (p : KeyPublic) (original : State) (used keys scalars : Nat) (t : State) : Prop :=
  let st := attemptStatus .cached p.a p.len ((keyRand original).drop used)
  if st = 1 then KeyDone p original (acceptedResult p (keyRand original) used) t
  else if st = 2 then KeyLive p original (used + p.len) keys (scalars - 1) t ∧ word t.mem p.control 112 = 4
  else KeyLive p original (used + p.len) (keys - 1) 128 t ∧ word t.mem p.control 112 = 4

theorem output_frame {p : KeyPublic} {original : State} (hi : KeyInput p original) {m m' : Mem}
    (hf : Frame [⟨p.control, 128⟩] m m') :
    Spec.Rsa.bytesAt m' p.xp p.len = Spec.Rsa.bytesAt m p.xp p.len ∧
      Spec.Rsa.bytesAt m' p.yp p.len = Spec.Rsa.bytesAt m p.yp p.len := by
  have hk := hi.len_lt
  have hc : p.control = (inCtl original).base := by rw [← hi.2]; rfl
  have hpw := hi.writes_pairwise
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrsi, hrcx, -, -, -, -, -⟩ := hi.1
  have hx : (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    rw [← hi.2]; simpa only [inX, inCtl, keyOfState, hrsi] using hpw.1.2.2.2
  have hy : (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.control, 128⟩ := by
    simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpw
    rw [← hi.2]; simpa only [inY, inCtl, keyOfState, hrcx] using hpw.2.1.2.2
  constructor <;> simp only [Spec.Rsa.bytesAt] <;> refine List.map_congr_left fun i hi => ?_
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hx)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  · exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hy)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)

/-- The status, normalized, and the attempt's octets consumed. -/
theorem key_classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hp : AttemptPost p (keyRand original) used s) :
    WP isa (.block (([.mov32 .rax (.reg .rax)] : List Instr) ++ advance ++
      ([.alu .cmp .rax (.imm 1)] : List Instr))) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ AttemptPost p (keyRand original) used t ∧
      t.gpr .rax = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) ∧
      eval .e t = some (decide (attemptStatus .cached p.a p.len ((keyRand original).drop used) = 1)) := by
  have hst : attemptStatus .cached p.a p.len ((keyRand original).drop used) < 4 := by
    rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with he | he | he <;> omega_using [he]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun u =>
    u.gpr .rax = ((s.gpr .rax).setWidth 32).setWidth 64 ∧ u.mem = s.mem) (by xrun []) rfl)
    fun u ⟨⟨hax, hmu⟩, ku⟩ => ?_
  have hu := h.keep ku hmu (by decide)
  have hpu := hp.keep hmu (by rw [hax]; simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_eq])
  have hax' : u.gpr .rax = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) :=
    normalized_status hp.1 hax
  refine WP.mono (key_advance_ok hu hroom) fun v ⟨hmv, kv⟩ => ?_
  have hb := advanceValues_bound p used
  have hh : Slots v.mem p.control (p.headers (used + p.len) keys scalars) := by
    refine headers_after _ hb hmv ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, advanceValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact hu.header (by simp [KeyPublic.headers])
  have hv := hu.update (u := used + p.len) (k := keys) (c := scalars) hroom h.keys_le h.scalars_le _
    hb (by simp only [advanceValues, List.mem_cons, List.not_mem_nil, or_false]
           rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hmv kv.2.1 kv.2.2
    (fun r hr => kv.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh
  have hout := output_frame h.input (hmv ▸ writeController_frame u.mem p.control _ hb)
  have hpv : AttemptPost p (keyRand original) used v := by
    unfold AttemptPost at hpu ⊢
    rw [hout.1, hout.2, kv.gpr (by decide)]
    exact hpu
  have hraxv : v.gpr .rax = BitVec.ofNat 64 (attemptStatus .cached p.a p.len ((keyRand original).drop used)) :=
    (kv.gpr (by decide)).trans hax'
  refine WP.mono (rax_guard hraxv (by omega_using [hst]) 1 1 (by decide) (by decide)) fun t ⟨⟨he, hmt, hrt⟩, kt⟩ => ?_
  exact ⟨hv.keep kt hmt (by decide), hpv.keep hmt (by rw [hrt]), hrt.trans hraxv, he⟩

/-- A terminal status written over a loop state, whose outputs are already
the result's. -/
theorem key_terminal_done {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : Nat) (hst : status < 2 ^ 32) (hst0 : status ≠ 0)
    {r : Spec.Ffdh.KeySearchResult} (hu : r.used = used) (hs : r.status = status)
    (hr : r.retries = ⟨0, 0⟩) (ho : KeyOutput p r s.mem) :
    WP isa (.block (terminal status)) s (KeyDone p original r) := by
  have scr := h.input.control_scr (t := s) h.wr
  refine WP.mono (key_terminal_ok scr h.r12 status) fun t ⟨_, hm, k⟩ => ?_
  have hb := terminalValues_bound status
  have hh : Slots t.mem p.control (p.headers used 0 0) := by
    refine headers_after _ hb hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  have ht := h.update (u := used) (k := 0) (c := 0) h.used_le (by decide) (by decide) _ hb (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh
  have hw (j : Nat) (hj : j < 16) : word t.mem p.control (8 * j) =
      controllerValue (terminalValues status) j (word s.mem p.control (8 * j)) := by
    rw [hm, writeController_word _ _ _ hb j hj]
  have hout := output_frame h.input (hm ▸ writeController_frame s.mem p.control _ hb)
  refine ht.done hu ?_ ?_ ?_
  · rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false, hs]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hst,
      Nat.mod_eq_of_lt (show status < 2 ^ 64 by omega_using [hst])]
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
  rcases attemptStatus_cases (policy := .cached) p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · rw [h1] at he
    refine WP.ite true he (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_terminal_done (r := acceptedResult p (keyRand original) used) hu 1 (by decide)
      (by decide) rfl rfl rfl ?_) fun t ht => ?_
    rotate_left
    · dsimp only [KeyClassified]; rw [ite_eq_left h1]; exact ht
    have hpu' := hpu
    unfold AttemptPost at hpu'
    simp only [h1, ite_true] at hpu'
    exact hpu'.2
  · rw [h2] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (rax_guard hax (by decide) 2 2 (by decide) (by decide))
      fun v ⟨⟨he2, hmv, _⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv (by decide)
    refine WP.ite true he2 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_scalar hv hs) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h2]; decide), ite_eq_left h2]
    exact ht
  · rw [h3] at he hax
    refine WP.ite false he (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (rax_guard hax (by decide) 2 2 (by decide) (by decide))
      fun v ⟨⟨he2, hmv, hrv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv (by decide)
    refine WP.ite false he2 (fun hf => by cases hf) fun _ => ?_
    refine WP.seq (WP.mono (rax_guard (hrv.trans hax) (by decide) 3 3 (by decide) (by decide))
      fun w ⟨⟨he3, hmw, _⟩, kw⟩ => ?_)
    have hw := hv.keep kw hmw (by decide)
    refine WP.ite true he3 (fun _ => ?_) (fun hf => by cases hf)
    refine WP.mono (key_rejected_public hw hk) fun t ht => ?_
    dsimp only [KeyClassified]
    rw [ite_eq_right (by rw [h3]; decide), ite_eq_right (by rw [h3]; decide)]
    exact ht

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
