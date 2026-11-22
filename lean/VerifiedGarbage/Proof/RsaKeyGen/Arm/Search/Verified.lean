module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Implies
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Verified
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
meta import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! ### `RsaKeyGen.Arm.Search.CT`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Search.Correct`, which this module and modules that import it used -/

section

/-! # The whole search (ARMv7): its results stored, and the contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- The state's eight halves, for a finished search. -/
def stateWords (p : SearchPublic) (r : PrimeSearchResult) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 r.remaining), (1, 0), (2, BitVec.ofNat 32 p.len), (3, 0),
    (4, BitVec.ofNat 32 (32769 * p.len)), (5, 0), (6, BitVec.ofNat 32 (requested p.len r)), (7, 0)]

/-- The results stored: the state's words, then `used`. -/
def finished (p : SearchPublic) (m : Mem) (r : PrimeSearchResult) : Mem :=
  writeSlots (writeSlots m (State.addr p.stp) (stateWords p r)) (State.addr p.up)
    [(0, BitVec.ofNat 32 r.used), (1, 0)]

theorem results_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} (h : SearchDone p o final s) :
    WP isa (.block results) s fun t =>
      (t.gpr .r0 = BitVec.ofNat 32 final.status ∧ t.mem = finished p s.mem final) ∧
        Rest [.r0, .r1, .r12] s t := by
  have hi := h.input
  have f := hi.facts
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  obtain ⟨-, eU, -, -, -, -, eT⟩ := hi.regions
  refine withRest_all [.r0, .r1, .r12] ?_ (by rfl) (by rfl)
  have aT (d : Nat) (hd : d < 32) : State.addr (p.stp + BitVec.ofNat 32 d) = off (State.addr p.stp) d :=
    VG.Arm.addr_add (by have := f.nT; omega_using [hd, this])
  have aU (d : Nat) (hd : d < 8) : State.addr (p.up + BitVec.ofNat 32 d) = off (State.addr p.up) d :=
    VG.Arm.addr_add (by have := f.nU; omega_using [hd, this])
  have wT (d : Nat) (hd : d + 4 ≤ 32) : InRegions s.wr (off (State.addr p.stp) d) 4 :=
    ⟨inState o, by rw [h.wr, hi.wr]; simp [inWrites], by rw [eT]; exact Offset.contains_base _ hd (by omega_using [hd])⟩
  have wU (d : Nat) (hd : d + 4 ≤ 8) : InRegions s.wr (off (State.addr p.up) d) 4 :=
    ⟨inUsed o, by rw [h.wr, hi.wr]; simp [inWrites], by rw [eU]; exact Offset.contains_base _ hd (by omega_using [hd])⟩
  have c7 : pushBytes + 0 + 4 * 7 < 4096 := by decide
  have stp : stackArg o 7 = p.stp := by rw [← hi.2]; rfl
  unfold results arg finished stateWords writeSlots
  ffrun [h.arg_addr 7, h.arg_read (j := 7) (by decide), h.arg_value (j := 7) (by decide), stp, c7,
    h.r5, h.r6, h.r8, h.r9, h.r10, h.r11, aT 0 (by decide), aT 4 (by decide), aT 8 (by decide), aT 12 (by decide),
    aT 16 (by decide), aT 20 (by decide), aT 24 (by decide), aT 28 (by decide), aU 0 (by decide), aU 4 (by decide),
    wT 0 (by decide), wT 4 (by decide), wT 8 (by decide), wT 12 (by decide), wT 16 (by decide), wT 20 (by decide),
    wT 24 (by decide), wT 28 (by decide), wU 0 (by decide), wU 4 (by decide), shl32' p.len 15 (by omega_using [hv]),
    add_ofNat32, show p.len * 2 ^ 15 + p.len = 32769 * p.len by omega_using []]
  rfl

theorem stateWords_bound (p : SearchPublic) (r : PrimeSearchResult) : ∀ e ∈ stateWords p r, e.1 < 8 := by
  simp only [stateWords, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem usedWords_bound (r : PrimeSearchResult) : ∀ e ∈ [(0, BitVec.ofNat 32 r.used), (1, (0 : BitVec 32))], e.1 < 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl) <;> dsimp only <;> decide

/-- The results change only the state and `used`. -/
theorem finished_frame {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult) :
    Frame [inState o, inUsed o] m (finished p m r) := by
  obtain ⟨-, eU, -, -, -, -, eT⟩ := h.regions
  rw [eT, eU]
  exact ((writeSlots_frame m _ (N := 8) (by decide) _ (stateWords_bound p r)).mono (by simp)).trans
    ((writeSlots_frame _ _ (N := 2) (by decide) _ (usedWords_bound r)).mono (by simp))

theorem finished_bytes {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult) :
    Spec.Rsa.bytesAt (finished p m r) (State.addr p.op) p.len = Spec.Rsa.bytesAt m (State.addr p.op) p.len := by
  have pw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at pw
  obtain ⟨⟨dOU, -, dOT⟩, -, -⟩ := pw
  have eO := h.regions.1
  have nO := h.facts.nO
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine (finished_frame h m r).bytes (R := inOut o) (fun q hq => ?_) (by rw [eO]; simp only; omega_using [nO])
    (by rw [eO]; exact List.mem_range.mp hi) |> fun e => by rw [eO] at e; exact e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [dOT, dOU]

theorem finished_used {p : SearchPublic} (m : Mem) (r : PrimeSearchResult) (hr : r.used < 2 ^ 32) :
    Spec.Rsa.wordsAt (finished p m r) (State.addr p.up) 1 = [BitVec.ofNat 64 r.used] := by
  have hs := slot_writeSlots (writeSlots m (State.addr p.stp) (stateWords p r)) (State.addr p.up) (N := 2) (by decide)
    _ (usedWords_bound r)
  have w := pair_word (finished p m r) (State.addr p.up) 0
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
  change [(finished p m r).readW (off (State.addr p.up) (8 * 0)) 64] = _
  rw [w]
  unfold finished
  rw [hs 1 (by decide), hs 0 (by decide)]
  simp only [List.cons.injEq, and_true]
  exact pair_ofNat hr

theorem finished_state {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult)
    (h0 : r.remaining < 2 ^ 32) (h1 : p.len < 2 ^ 32) (h2 : 32769 * p.len < 2 ^ 32) (h3 : (requested p.len r) < 2 ^ 32) :
    Spec.Rsa.wordsAt (finished p m r) (State.addr p.stp) 4 = [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
      BitVec.ofNat 64 (32769 * p.len), BitVec.ofNat 64 (requested p.len r)] := by
  have pw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at pw
  obtain ⟨-, ⟨-, dUT⟩, -⟩ := pw
  obtain ⟨-, eU, -, -, -, -, eT⟩ := h.regions
  have fT := h.facts.nT
  have hs := slot_writeSlots m (State.addr p.stp) (N := 8) (by decide) _ (stateWords_bound p r)
  have past (j : Nat) (hj : j < 8) : slot (finished p m r) (State.addr p.stp) j =
      slot (writeSlots m (State.addr p.stp) (stateWords p r)) (State.addr p.stp) j := by
    refine (writeSlots_frame _ (State.addr p.up) (N := 2) (by decide) _ (usedWords_bound r)).readW
      (r := inState o) ?_ (fun q hq => ?_) (by decide)
    · rw [eT]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
    · obtain rfl := List.mem_singleton.mp hq
      change (inState o).Disjoint (rU p)
      rw [← eU]; exact dUT.symm
  refine wordsAt_slots _ _ h0 h1 h2 h3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [past 0 (by decide), hs 0 (by decide)]; rfl
  · rw [past 1 (by decide), hs 1 (by decide)]; rfl
  · rw [past 2 (by decide), hs 2 (by decide)]; rfl
  · rw [past 3 (by decide), hs 3 (by decide)]; rfl
  · rw [past 4 (by decide), hs 4 (by decide)]; rfl
  · rw [past 5 (by decide), hs 5 (by decide)]; rfl
  · rw [past 6 (by decide), hs 6 (by decide)]; rfl
  · rw [past 7 (by decide), hs 7 (by decide)]; rfl

/-- The callee-saved registers but `r4`, from the frame. -/
theorem restore_ok {p : SearchPublic} {o s : State} (hi : SearchInput p o) (hsp : s.sp = p.S1)
    (hw : ⟨State.addr p.S1, 40⟩ ∈ s.wr) (hs : Saved s.mem p.S1 o) :
    WP isa (.block restore) s fun t =>
      ((∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], t.gpr r = o.gpr r) ∧ t.mem = s.mem) ∧
        Rest [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s t := by
  have room := hi.facts.room
  have top := hi.facts.top
  have S1n : p.S1.toNat = p.sp.toNat - 40 := FrameStack.sub_toNat' (by omega_using [room])
  have a (d : Nat) (hd : d < 40) : State.addr (s.sp + BitVec.ofNat 32 d) = State.addr p.S1 + BitVec.ofNat 64 d := by
    rw [hsp]; exact VG.Arm.addr_add (by omega_using [S1n, hd])
  have r (d : Nat) (hd : d + 4 ≤ 40) : InRegions (s.rd ++ s.wr) (State.addr p.S1 + BitVec.ofNat 64 d) 4 :=
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega_using [hd])⟩
  have v (q : Reg × Nat) (hq : q ∈ slots) : s.mem.readW (State.addr p.S1 + BitVec.ofNat 64 q.2) 32 = o.gpr q.1 :=
    hs q hq
  refine withRest_all [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] ?_ (by rfl) (by rfl)
  unfold restore
  ffrun [a 4 (by decide), a 8 (by decide), a 12 (by decide), a 16 (by decide), a 20 (by decide), a 24 (by decide),
    a 28 (by decide), a 36 (by decide), r 4 (by decide), r 8 (by decide), r 12 (by decide), r 16 (by decide),
    r 20 (by decide), r 24 (by decide), r 28 (by decide), r 36 (by decide),
    v (.r5, 4) (by simp), v (.r6, 8) (by simp), v (.r7, 12) (by simp), v (.r8, 16) (by simp), v (.r9, 20) (by simp),
    v (.r10, 24) (by simp), v (.r11, 28) (by simp), v (.lr, 36) (by simp)]
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem push_apart {p : SearchPublic} {o : State} (h : SearchInput p o) :
    ∀ q ∈ inWrites o, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ q := by
  have room := h.facts.room
  have push : Region.Sub ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ (inStack o) := by
    rw [BitVec.add_zero, SearchPublic.S1, FrameStack.addr_sub' (by omega_using [room]), h.sp_eq]
    exact h.stack_sub (by decide) (by decide)
  exact fun q hq => SearchInput.disj_sub (h.stack_disjoint (List.mem_append_left _ hq)) push

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  have f := hp.facts
  have room : 232 ≤ s.sp.toNat := h.1
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  have rl := f.randLen
  unfold primeEntropy at rl
  have rem := hp.remaining_le
  unfold Impl.RsaKeyGen.Arm.Search.code body
  refine WP.frame (rs := pushRegs) (r := .r4) (by decide) (by simp; omega_using [room]) (by decide) ?_
  refine WP.seq (WP.mono (entry_ok hp) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (search_loop c (final := searchResult s) (tr := []) h1 (consume_zero _).symm) fun s2 hd => ?_)
  unfold finish
  refine WP.block_append (WP.mono (results_ok hd) fun s3 ⟨⟨h0, hm3⟩, k3⟩ => ?_)
  have hsv : Saved s3.mem p.S1 s := by
    rw [hm3]
    refine Spill.Saved.frame hd.saved (lo := 0) (hi := 40) (by decide) (finished_frame hp _ _) fun q hq => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact push_apart hp _ (by simp [inWrites])
    · exact push_apart hp _ (by simp [inWrites])
  have hw3 : ⟨State.addr p.S1, 40⟩ ∈ s3.wr := by rw [k3.wr, hd.wr]; exact List.mem_cons_self ..
  refine WP.mono (restore_ok hp (k3.sp.trans hd.sp) hw3 hsv) fun s4 ⟨⟨hr, hm4⟩, k4⟩ ml ul hfl => ?_
  have sp4 : s4.sp = p.S1 := k4.sp.trans (k3.sp.trans hd.sp)
  change Frame [⟨State.addr p.S1, 40⟩] s4.mem ml at hfl
  rw [hm4, hm3] at hfl
  have apart : ∀ q ∈ inWrites s, Region.Disjoint ⟨State.addr p.S1, 40⟩ q := fun q hq => by
    have := push_apart hp q hq
    simpa only [BitVec.add_zero, Nat.sub_zero] using this
  obtain ⟨eO, eU, -, -, -, -, eSt⟩ := hp.regions
  have sepOf {q : Region} (hq : q ∈ inWrites s) : ∀ r ∈ [(⟨State.addr p.S1, 40⟩ : Region)], q.Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact (apart q hq).symm
  have g0 : (popped .r4 (4 * pushRegs.length) s4).gpr .r0 = BitVec.ofNat 32 (searchResult s).status := by
    rw [popped_gpr (by decide), k4.gpr .r0 (by decide), h0]
  have g4 : (popped .r4 (4 * pushRegs.length) s4).gpr .r4 = s.gpr .r4 := by
    simp only [popped, RegUpd.gpr_setReg, ite_true]
    rw [sp4, hm4, ← BitVec.add_zero (State.addr p.S1)]
    exact hsv (.r4, 0) (by simp)
  obtain ⟨bu, br, bq⟩ := hd.bounds
  have st := status_lt (searchResult s)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun r hr' => ?_, ?_⟩
  · rw [BitVec.setWidth_append_eq_right, g0, toNat_small (by omega_using [st])]
  · change Spec.Rsa.bytesAt ml (State.addr p.op) p.len = _
    rw [VG.Proof.Rsa.rsa_bytes_frame hfl (by omega_using [hv]) (sepOf (q := rO p) (by rw [← eO]; simp [inWrites])),
      finished_bytes hp]
    exact hd.output
  · change Spec.Rsa.wordsAt ml (State.addr p.up) 1 = _
    rw [Proof.Rsa.wordsAt_frame hfl (by decide) (sepOf (q := rU p) (by rw [← eU]; simp [inWrites])),
      finished_used _ _ (by omega_using [hv, rl, bu])]
  · refine ⟨_, ?_, Search.search_requests (searchLen s) (searchE s) (searchP s)
      (searchRemaining s) (searchRand s)⟩
    change Spec.Rsa.wordsAt ml (State.addr p.stp) 4 = _
    rw [Proof.Rsa.wordsAt_frame hfl (by decide)
        (sepOf (q := ⟨State.addr p.stp, 32⟩) (by rw [← eSt]; simp [inWrites])), finished_state hp _ _ (by omega_using [rem, br]) (by omega_using [hv]) (by omega_using [hv]) (by unfold primeEntropy at bq; omega_using [hv, bq])]
    rfl
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g4
    all_goals rw [popped_gpr (by decide)]; exact hr _ (by simp)
  · change s4.sp + BitVec.ofNat 32 (4 * pushRegs.length) = s.sp
    rw [sp4, SearchPublic.S1, show 4 * pushRegs.length = 40 from rfl, BitVec.sub_add_cancel]
    rfl

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! ### `RsaKeyGen.Arm.Search.CTLoop`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Search.CTStep`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Search.CTCall`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Search.CTLeaf`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Search.CTBase`, which only this module used -/

section

/-! # The search's constant time (ARMv7): its public points

Two runs with the same public arguments (`searchPub`) have the same public
data `p` and the same trace `T`. A loop state of either is at a point
`(used, k, tr)`: `used` octets consumed, `k` counted candidates left, after
the trace `tr` of its candidates so far. The next candidate's leak, and so
its status and consumption, are read from `T` past `tr` (`nextLeak`), so
both runs take the same branches and reach the same next point.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult candidateOp)

/-- A block's head, then its tail and what follows. -/
theorem RelCT.seq_block_append {M : ISA} {P Q : M.State → M.State → Prop} {l₁ l₂ : List M.Instr} {c : Prog M}
    (h : RelCT M P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT M P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ c₁ =>
    cases e₂ with
    | seq b₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨d₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨d₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-- A point of the loop: octets consumed, counted candidates left, trace so far. -/
abbrev Pt := Nat × Nat × List Nat

/-- A loop state of a run whose public data is `p` and whose search's trace is `T`. -/
def LiveCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2

/-- The next candidate's leak, from the trace. -/
def nextLeak (T tr : List Nat) : List Nat :=
  ((T.drop tr.length).drop 1).take ((T.drop tr.length).headD 0)

def pubStatus (T tr : List Nat) : Nat := Search.statusOfLeak (nextLeak T tr)
def pubUsed (p : SearchPublic) (T tr : List Nat) : Nat := Search.usedOfLeak p.len (nextLeak T tr)

/-- Whether the search goes on past the next candidate, from public data. -/
def pubCont (p : SearchPublic) (T : List Nat) (q : Pt) : Prop :=
  q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧ (pubStatus T q.2.2 = 2 ∨ pubStatus T q.2.2 = 3) ∧
    pubUsed p T q.2.2 ≠ 0

instance (p : SearchPublic) (T : List Nat) (q : Pt) : Decidable (pubCont p T q) := by
  unfold pubCont; infer_instance

/-- The point past the next candidate. -/
def nextPt (p : SearchPublic) (T : List Nat) (q : Pt) : Pt :=
  (q.1 + pubUsed p T q.2.2, if pubStatus T q.2.2 = 3 then q.2.1 - 1 else q.2.1,
    q.2.2 ++ ((nextLeak T q.2.2).length :: nextLeak T q.2.2))

/-- With candidates left, the next leak is the candidate's. -/
theorem leak_of {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) :
    nextLeak T q.2.2 = Spec.RsaKeyGen.candidateLeak p.len p.eB (searchP o) ((searchRand o).drop q.1) := by
  obtain ⟨rest, hr⟩ := Search.search_trace (L := p.len) (eB := p.eB) (pB := searchP o) hk
    ((searchRand o).drop q.1)
  have e : T = q.2.2 ++ (Search.entry p.len p.eB (searchP o) ((searchRand o).drop q.1) ++ rest) := by
    rw [← hT, hfin]
    change q.2.2 ++ (tailOf p o q.1 q.2.1).trace = _
    rw [tailOf, hr]
  unfold nextLeak
  rw [e, List.drop_left]
  simp only [Search.entry, List.cons_append, List.drop_succ_cons, List.drop_zero, List.headD_cons]
  exact List.take_left' rfl

theorem status_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candStatus p o q.1 = pubStatus T q.2.2 := by
  rw [pubStatus, leak_of hT hfin hk, candStatus, candOp, Search.status_of_leak]

theorem used_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candUsed p o q.1 = pubUsed p T q.2.2 := by
  rw [pubUsed, leak_of hT hfin hk, ← Search.used_of_leak, List.length_drop, rand_length hi]
  rfl

theorem cont_iff {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2) :
    Cont p o q.1 q.2.1 ↔ pubCont p T q := by
  by_cases hk : q.2.1 = 0
  · exact ⟨fun h => absurd hk h.1, fun h => absurd hk h.1⟩
  · unfold Cont pubCont
    rw [status_eq hT hfin hk, used_eq hi hT hfin hk]

/-- The registers a loop state fixes. -/
theorem live_pins (p : SearchPublic) (T : List Nat) :
    Pins (LiveCT p T) [.r4, .r5, .r6, .r7, .r8, .r9, .r11] := by
  rintro q s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h₁.r4.trans h₂.r4.symm, h₁.r5.trans h₂.r5.symm, h₁.r6.trans h₂.r6.symm, h₁.r7.trans h₂.r7.symm,
    h₁.r8.trans h₂.r8.symm, h₁.r9.trans h₂.r9.symm, h₁.r11.trans h₂.r11.symm]

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # The search's leaves are constant time (ARMv7)

Zeros at `out`, the terminal states and the request depend only on the
width and the pointers; `short` reads the tape's length, a stack argument,
then branches on public values.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

variable {α : Type} {Φ : α → State → Prop}

theorem zeroOut_ct (h : Pins Φ [.r4, .r5]) : RelCT isa (Two Φ) zeroOut (fun _ _ => True) :=
  two_taint _ h (by taint_decide)

theorem exhausted_ct (h : Pins Φ [.r4, .r5]) : RelCT isa (Two Φ) exhausted (fun _ _ => True) :=
  two_taint _ h (by taint_decide)

theorem accept_ct : RelCT isa (Two Φ) (.block accept) (fun _ _ => True) :=
  two_taint [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide)

theorem ldrSp_ct {Ψ : α → State → Prop} {r : Reg} {d : Nat} (hw : ∀ a s, Φ a s → WP isa (.block [.ldrSp r d]) s (Ψ a)) :
    RelCT isa (Two Φ) (.block [.ldrSp r d]) (Two Ψ) :=
  two_post ((VG.Proof.Bignum.Arm.loadStack_ct r d).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) fun _ _ _ => trivial) hw

/-- A state from which `short` runs: `used` octets consumed. -/
def ShortCT (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  ∃ o, SearchBase p o s ∧ s.gpr .r8 = BitVec.ofNat 32 used

/-- After its load of the tape's length. -/
def ShortCT' (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  ShortCT p used s ∧ s.gpr .r0 = BitVec.ofNat 32 p.randLen

theorem short_load (p : SearchPublic) (used : Nat) (s : State) (h : ShortCT p used s) :
    WP isa (.block [arg .r0 0 4]) s (ShortCT' p used) := by
  obtain ⟨o, hb, h8⟩ := h
  refine WP.mono (withRest_all [.r0] (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 p.randLen ∧ t.mem = s.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h0, hm⟩, k⟩ => ⟨⟨o, hb.keep k hm, (k.gpr .r8 (by decide)).trans h8⟩, h0⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hb.arg_addr 4, hb.arg_read (j := 4) (by decide), hb.arg_value (j := 4) (by decide), randLen_arg hb.input, c]

theorem short_pins (p : SearchPublic) : Pins (ShortCT' p) [.r0, .r4, .r5, .r8] := by
  rintro a s₁ s₂ ⟨⟨_, h₁, e₁⟩, f₁⟩ ⟨⟨_, h₂, e₂⟩, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [f₁.trans f₂.symm, h₁.r4.trans h₂.r4.symm, h₁.r5.trans h₂.r5.symm, e₁.trans e₂.symm]

theorem short_ct (p : SearchPublic) : RelCT isa (Two (ShortCT p)) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq_block_append (RelCT.seq (ldrSp_ct (short_load p)) ?_)
  exact two_taint _ (short_pins p) (by taint_decide)

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # A candidate call is constant time (ARMv7)

Its arguments are the public data's, and its leak is the next one of the
trace (`leak_of`): the candidate's own constant time gives the same trace
in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The candidate's inputs, from its arguments. -/
theorem call_inputs {p : SearchPublic} {o s a u : State} {used k : Nat} (h : SearchLive p o used k s)
    (ha : a = allocated 32 s) (hd : ArgDone p o a used u) (hroom : used < p.randLen) :
    Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.ep) p.elen = p.eB ∧
      Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.pp) p.plen = searchP o ∧
      Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) =
        (searchRand o).drop used := by
  have hi := h.input
  have f := hi.facts
  have hargs : Frame [⟨State.addr p.S2, 32⟩] s.mem u.mem := by
    rw [hd.1.mem, ha]
    exact writeSlots_frame _ _ (N := 8) (by decide) _ fun e he => callArgs_bound p used e (List.mem_of_mem_take he)
  have hfu : Frame (changes o) o.mem u.mem := h.frame.trans (hargs.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp [changes], S2_sub hi⟩)
  refine ⟨?_, ?_, ?_⟩
  · change Spec.Rsa.bytesAt u.mem (State.addr p.ep) p.elen = _
    rw [hi.e_frame hfu, ← hi.2]; rfl
  · change Spec.Rsa.bytesAt u.mem (State.addr p.pp) p.plen = _
    rw [hi.p_frame hfu, ← hi.2]; rfl
  · change Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) = _
    rw [VG.Arm.addr_add (by have := f.nR; omega_using [hroom, this]), bytesAt_drop, hi.random_frame hfu, ← hi.2]; rfl

/-- A state about to call the candidate, at the point `q`. -/
def CallCT (p : SearchPublic) (T : List Nat) (q : Pt) (u : State) : Prop :=
  ∃ o s, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    ArgDone p o (allocated 32 s) q.1 u

theorem call_pub {p : SearchPublic} {T : List Nat} {q : Pt} {u₁ u₂ : State}
    (h₁ : CallCT p T q u₁) (h₂ : CallCT p T q u₂) (sp : u₁.sp = u₂.sp) :
    (Proof.RsaKeyGen.candidateContract abi 160).pub (u₁.callEntry.withRegions (callRd p q.1) (callWr p))
      (u₂.callEntry.withRegions (callRd p q.1) (callWr p)) := by
  obtain ⟨o₁, s₁, T₁, l₁, f₁, hk, hroom, d₁⟩ := h₁
  obtain ⟨o₂, s₂, T₂, l₂, f₂, -, -, d₂⟩ := h₂
  have hl := l₁.input.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  have e1 := l₁.input.facts.e8
  have rl := l₁.input.facts.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  obtain ⟨eB₁, pB₁, rB₁⟩ := call_inputs l₁ rfl d₁ (by omega_using [hroom, hl])
  obtain ⟨eB₂, pB₂, rB₂⟩ := call_inputs l₂ rfl d₂ (by omega_using [hroom, hl])
  have lk₁ := leak_of T₁ f₁ hk
  have lk₂ := leak_of T₂ f₂ hk
  sig_pub [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val]
  simp only [d₁.sa0, d₁.sa1, d₁.sa2, d₁.sa3, d₁.sa4, d₁.sa5, d₁.sa6, d₂.sa0, d₂.sa1, d₂.sa2, d₂.sa3, d₂.sa4,
    d₂.sa5, d₂.sa6, d₁.2.1, d₁.2.2.1, d₁.2.2.2.1, d₁.2.2.2.2, d₂.2.1, d₂.2.2.1, d₂.2.2.2.1, d₂.2.2.2.2,
    toNat_small (n := p.len) (by omega_using [hl]), toNat_small (n := p.elen) (by omega_using [e1]),
    toNat_small (n := p.plen) (by rcases l₁.input.facts.plen with e | e <;> omega_arith),
    toNat_diff (a := p.randLen) (b := q.1) (by omega_using [hroom]) (by omega_using [hl, rl]), eB₁, pB₁, rB₁, eB₂, pB₂, rB₂, ← lk₁, ← lk₂]
  exact ⟨sp, by simp only [and_self]⟩

/-- A state before the candidate, at the point `q`. -/
def CandCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  LiveCT p T q s ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen

/-- The candidate's frame allocated. -/
def AllocCT (p : SearchPublic) (T : List Nat) (q : Pt) (a : State) : Prop :=
  ∃ s, CandCT p T q s ∧ a = allocated 32 s

/-- `j` of the candidate's arguments stored. -/
def ArgCT (p : SearchPublic) (T : List Nat) (j : Nat) (q : Pt) (u : State) : Prop :=
  ∃ o s, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    ArgCtx p o (allocated 32 s) q.1 j u ∧ ArgRegs p u

theorem arg_pins (p : SearchPublic) (T : List Nat) (j : Nat) : Pins (ArgCT p T j) [.lr] := by
  rintro q s₁ s₂ ⟨_, _, _, _, _, _, _, c₁, _⟩ ⟨_, _, _, _, _, _, _, c₂, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact c₁.lr.trans c₂.lr.symm

theorem argHead_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AllocCT p T)) (.block argHead) (Two (ArgCT p T 0)) :=
  two_piece [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide) fun q a ⟨s, ⟨⟨o, hT, hl, hf⟩, hk, hr⟩, ha⟩ => by
    subst ha
    exact WP.mono (argHead_ok hl) fun u ⟨⟨c, r⟩, _⟩ => ⟨o, s, hT, hl, hf, hk, hr, c, r⟩

theorem argWord_ct (p : SearchPublic) (T : List Nat) {j : Nat} (hj : j < 7) {adjust : List Instr}
    {f : Nat → BitVec 32 → BitVec 32}
    (hadj : ∀ used t, t.gpr .r8 = BitVec.ofNat 32 used →
      WP isa (.block adjust) t fun t' => (t'.gpr .r12 = f used (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t')
    (hv : ∀ o used, SearchInput p o → (callArgs p used)[j]? = some (j, f used (stackArg o j)))
    {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (htaint : (taint.check (Taint.ofRegs [.lr]) (.block (adjust ++ ([.str .r12 .lr (4 * j)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ArgCT p T j)) (.block (argWord j adjust)) (Two (ArgCT p T (j + 1))) := by
  refine two_post ?_ fun q u ⟨o, s, hT, hl, hf, hk, hr, c, r⟩ =>
    WP.mono (argWord_ok hj (hadj q.1) (hv o q.1 hl.input) c) fun t ⟨c', k⟩ => ⟨o, s, hT, hl, hf, hk, hr, c', r.keep k⟩
  change RelCT isa _ (.block ([arg .r12 32 j] ++ (adjust ++ [.str .r12 .lr (4 * j)]))) _
  refine RelCT.block_append (RelCT.seq (ldrSp_ct (Ψ := ArgCT p T j) fun q u ⟨o, s, hT, hl, hf, hk, hr, c, r⟩ => ?_)
    (two_taint _ (arg_pins p T j) htaint))
  have c1 : pushBytes + 32 + 4 * j < 4096 := by unfold pushBytes; omega_using [hj]
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.mem = u.mem) ?_ (by rfl) (by rfl))
    fun t ⟨hm, k⟩ => ⟨o, s, hT, hl, hf, hk, hr, c.keep k hm, r.keep k⟩
  ffrun [c.arg_addr j, c.arg_read (j := j) (by omega_using [hj]), c1]

theorem args_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AllocCT p T)) (.block arguments) (Two (ArgCT p T 7)) := by
  have w0 := argWord_ct p T (j := 0) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 0 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w1 := argWord_ct p T (j := 1) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 1 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w2 := argWord_ct p T (j := 2) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 2 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w3 := argWord_ct p T (j := 3) (f := fun used => (· + BitVec.ofNat 32 used)) (by decide) adjust_add
    (fun o used hi => hv_of hi used 3 (· + BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) (by taint_decide)
  have w4 := argWord_ct p T (j := 4) (f := fun used => (· - BitVec.ofNat 32 used)) (by decide) adjust_sub
    (fun o used hi => hv_of hi used 4 (· - BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) (by taint_decide)
  have w5 := argWord_ct p T (j := 5) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 5 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w6 := argWord_ct p T (j := 6) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 6 id (by simp [callArgs, searchOfState])) (by taint_decide)
  rw [arguments_eq]
  exact RelCT.block_append ((argHead_ct p T).seq (RelCT.block_append (w0.seq (RelCT.block_append (w1.seq
    (RelCT.block_append (w2.seq (RelCT.block_append (w3.seq (RelCT.block_append (w4.seq
      (RelCT.block_append (w5.seq w6)))))))))))))

theorem call_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (ArgCT p T 7)) c.call (fun _ _ => True) := by
  intro s t traceS traceT u v ⟨q, hs, ht, sp⟩ runS runT
  have ready {w : State} (hw : ArgCT p T 7 q w) : CallCT p T q w := by
    obtain ⟨o, s', hT, hl, hf, hk, hr, cx, rg⟩ := hw
    exact ⟨o, s', hT, hl, hf, hk, hr, cx, rg⟩
  have ct : RelCT isa (fun a b => ArgCT p T 7 q a ∧ ArgCT p T 7 q b ∧ a.sp = s.sp ∧ b.sp = s.sp) c.call
      (fun _ _ => True) := by
    refine VG.Arm.RelCT.call c.verified.1 c.verified.2.1 (callRd p q.1) (callWr p) ?_
    intro a b ⟨ha, hb, spA, spB⟩
    obtain ⟨oa, sa, _, la, _, _, hra, da, ra⟩ := ha
    obtain ⟨ob, sb, _, lb, _, _, hrb, db, rb⟩ := hb
    have hla := la.input.facts.valid
    unfold Spec.RsaKeyGen.primeLenValid at hla
    obtain ⟨cova, covWa⟩ := call_covers la rfl ⟨da, ra⟩ (by omega_using [hra, hla])
    obtain ⟨covb, covWb⟩ := call_covers lb rfl ⟨db, rb⟩ (by omega_using [hra, hla])
    exact ⟨call_pre ⟨da, ra⟩ la.used_le, call_pre ⟨db, rb⟩ lb.used_le,
      call_pub (ready ⟨oa, sa, by assumption, la, by assumption, by assumption, hra, da, ra⟩)
        (ready ⟨ob, sb, by assumption, lb, by assumption, by assumption, hrb, db, rb⟩) (spA.trans spB.symm),
      cova, covWa, covb, covWb⟩
  exact ct _ _ _ _ _ _ ⟨hs, ht, rfl, sp.symm⟩ runS runT

/-- After the candidate: what it left. -/
def AfterCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 t ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    CandPost p (searchP o) (searchRand o) q.1 t

theorem candidateRun_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (CandCT p T)) (candidateRun c.call) (Two (AfterCT p T)) := by
  refine two_post ?_ fun q s ⟨⟨o, hT, hl, hf⟩, hk, hr⟩ =>
    WP.mono (candidateRun_ok c hl hr) fun t ⟨ht, hp⟩ => ⟨o, hT, ht, hf, hk, hr, hp⟩
  unfold candidateRun
  refine VG.Proof.Ffdh.Arm.KeySearch.alloc_ct (R := fun _ _ => True) ?_
  refine (RelCT.seq (args_ct p T) (call_ct c p T)).mono ?_ fun _ _ h => h
  rintro _ _ ⟨s, t, ⟨q, hs, ht, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩, ?_⟩
  change s.sp - BitVec.ofNat 32 32 = t.sp - BitVec.ofNat 32 32
  rw [sp]

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # An iteration of the search is constant time (ARMv7)

Each branch is on the point's public values, or on the candidate's status
and consumption, which the trace gives (`status_eq`, `used_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- Code that touches no memory leaks nothing, from any states. -/
theorem quiet_ct {P : State → State → Prop} {c : Prog isa} {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (h : (taint.check (Taint.ofRegs []) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ h => nomatch h) h

/-! ## After the candidate -/

/-- The candidate's status and consumption in `r0` and `r12`, and the
first comparison. -/
def RegsCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  AfterCT p T q t ∧ t.gpr .r0 = BitVec.ofNat 32 (pubStatus T q.2.2) ∧
    t.gpr .r12 = BitVec.ofNat 32 (pubUsed p T q.2.2)

def HeadCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  RegsCT p T q t ∧ isa.eval .eq t = some (decide (pubStatus T q.2.2 = 1))

theorem AfterCT.keep {p : SearchPublic} {T : List Nat} {q : Pt} {s t : State} (h : AfterCT p T q s)
    {ws : List Reg} (k : Rest ws s t) (hm : t.mem = s.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r11], r ∉ ws := by decide) (h0 : t.gpr .r0 = s.gpr .r0) :
    AfterCT p T q t := by
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  refine ⟨o, hT, hl.keep k hm hws, hf, hk, hr, ?_⟩
  obtain ⟨p0, p1, p2⟩ := hp
  exact ⟨by rw [h0]; exact p0, by rw [hm]; exact p1, by rw [hm]; exact p2⟩

theorem after_r0 {p : SearchPublic} {T : List Nat} {q : Pt} {t : State} (h : AfterCT p T q t) :
    t.gpr .r0 = BitVec.ofNat 32 (pubStatus T q.2.2) := by
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  rw [status_ofNat hp.1, ← status_eq hT hf hk]; rfl

theorem head_ready (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) (h : AfterCT p T q t) :
    WP isa (.block [.ldr .r12 .r6 0, .cmp .r0 (.imm 1)]) t (HeadCT p T q) := by
  have h0 := after_r0 h
  obtain ⟨o, hT, hl, hf, hk, hr, hp⟩ := h
  have hw : Spec.Rsa.wordsAt t.mem (State.addr p.up) 1 = [BitVec.ofNat 64 (candUsed p o q.1)] := hp.2.2
  rw [used_eq hl.input hT hf hk] at hw
  have st : pubStatus T q.2.2 < 4 := by
    rw [← status_eq hT hf hk]; unfold candStatus Spec.RsaKeyGen.candidateStatus; split <;> decide
  refine WP.mono (head_ok hl hw st h0) fun u ⟨⟨h12, he, hm⟩, k⟩ => ⟨⟨?_, ?_, h12⟩, he⟩
  · exact AfterCT.keep ⟨o, hT, hl, hf, hk, hr, hp⟩ k hm (h0 := k.gpr .r0 (by decide))
  · rw [k.gpr .r0 (by decide), h0]

theorem after_pins (p : SearchPublic) (T : List Nat) : Pins (AfterCT p T) [.r0, .r6] := by
  intro q s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (after_r0 h₁).trans (after_r0 h₂).symm
  · obtain ⟨_, _, l₁, _⟩ := h₁; obtain ⟨_, _, l₂, _⟩ := h₂; exact l₁.r6.trans l₂.r6.symm

/-- After the second comparison. -/
def Head2CT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  RegsCT p T q t ∧ isa.eval .eq t = some (decide (pubStatus T q.2.2 = 0))

theorem head2_ready (p : SearchPublic) (T : List Nat) (q : Pt) (t : State)
    (h : HeadCT p T q t ∧ isa.eval .eq t = some false) :
    WP isa (.block [.cmp .r0 (.imm 0)]) t (Head2CT p T q) := by
  obtain ⟨⟨⟨ha, h0, h12⟩, -⟩, -⟩ := h
  have st : pubStatus T q.2.2 < 2 ^ 32 := by
    obtain ⟨o, hT, hl, hf, hk, -⟩ := ha
    rw [← status_eq hT hf hk]; unfold candStatus Spec.RsaKeyGen.candidateStatus; split <;> decide
  refine WP.mono (cmp0_ok h0 st) fun u ⟨⟨he, hm⟩, k⟩ => ⟨⟨?_, ?_, ?_⟩, he⟩
  · exact AfterCT.keep ha k hm (h0 := k.gpr .r0 (by decide))
  · rw [k.gpr .r0 (by decide), h0]
  · rw [k.gpr .r12 (by decide), h12]

theorem regs_pins (p : SearchPublic) (T : List Nat) : Pins (RegsCT p T) [.r0, .r4, .r5, .r8, .r9, .r12] := by
  intro q s₁ s₂ ⟨a₁, z₁, w₁⟩ ⟨a₂, z₂, w₂⟩ r hr
  obtain ⟨_, _, l₁, _⟩ := a₁
  obtain ⟨_, _, l₂, _⟩ := a₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [z₁.trans z₂.symm, l₁.r4.trans l₂.r4.symm, l₁.r5.trans l₂.r5.symm, l₁.r8.trans l₂.r8.symm,
    l₁.r9.trans l₂.r9.symm, w₁.trans w₂.symm]

theorem classify_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AfterCT p T)) Impl.RsaKeyGen.Arm.Search.classify (fun _ _ => True) := by
  unfold Impl.RsaKeyGen.Arm.Search.classify
  refine RelCT.seq (two_piece [.r0, .r6] (after_pins p T) (by taint_decide) (head_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) (accept_ct.mono (fun _ _ h => h) fun _ _ h => h) ?_
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide) (head2_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · refine two_map (fun q => q.1) (fun q s h => ?_) (short_ct p)
    rcases h with ⟨⟨⟨⟨o, -, hl, -⟩, -, -⟩, -⟩, -⟩
    exact ⟨o, hl.toSearchBase, hl.r8⟩
  · exact two_taint _ (fun q s₁ s₂ h₁ h₂ => regs_pins p T q s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)

/-! ## A candidate, or a short tape -/

/-- A loop state with candidates left. -/
def Live0 (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop := LiveCT p T q s ∧ q.2.1 ≠ 0

def Live0' (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  Live0 p T q s ∧ s.gpr .r0 = BitVec.ofNat 32 p.randLen

def GuardCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  Live0 p T q s ∧ isa.eval .eq s = some (decide (p.randLen - q.1 < p.len))

theorem guard_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : Live0 p T q s) :
    WP isa (.block [arg .r0 0 4]) s (Live0' p T q) := by
  obtain ⟨⟨o, hT, hl, hf⟩, hk⟩ := h
  refine WP.mono (withRest_all [.r0] (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 p.randLen ∧ t.mem = s.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h0, hm⟩, k⟩ => ⟨⟨⟨o, hT, hl.keep k hm, hf⟩, hk⟩, h0⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hl.arg_addr 4, hl.arg_read (j := 4) (by decide), hl.arg_value (j := 4) (by decide), randLen_arg hl.input, c]

theorem guard_ready (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : Live0 p T q s) :
    WP isa (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5), .mov .r12 (.imm 0),
      .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]) s (GuardCT p T q) := by
  obtain ⟨⟨o, hT, hl, hf⟩, hk⟩ := h
  have hi := hl.input
  have f := hi.facts
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  have rl := f.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  have hu := hl.used_le
  refine WP.mono (withRest_all [.r0, .r12]
    (Q := fun t => isa.eval .eq t = some (decide (p.randLen - q.1 < p.len)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨⟨o, hT, hl.keep k hm, hf⟩, hk⟩, he⟩
  unfold arg
  have c4 : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hl.arg_addr 4, hl.arg_read (j := 4) (by decide), hl.arg_value (j := 4) (by decide), randLen_arg hi,
    hl.r8, hl.r5, BitVec.ofNat_sub_ofNat_of_le _ _ (show q.1 < 2 ^ 32 by omega_using [hv, rl, hu]) hu, c4,
    toNat_small (n := p.len) (by omega_using [hv]), toNat_small (n := p.randLen - q.1) (by omega_using [hv, rl])]
  exact carry_eval (P := p.randLen - q.1 < p.len) (not_decide_le _ _)

theorem live0'_pins (p : SearchPublic) (T : List Nat) : Pins (Live0' p T) [.r0, .r5, .r8] := by
  intro q s₁ s₂ ⟨⟨⟨_, _, l₁, _⟩, _⟩, z₁⟩ ⟨⟨⟨_, _, l₂, _⟩, _⟩, z₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [z₁.trans z₂.symm, l₁.r5.trans l₂.r5.symm, l₁.r8.trans l₂.r8.symm]

theorem live_pins45 {p : SearchPublic} {T : List Nat} {Φ : Pt → State → Prop} (h : ∀ q s, Φ q s → LiveCT p T q s) :
    Pins Φ [.r4, .r5] := fun q s₁ s₂ h₁ h₂ r hr =>
  live_pins p T q s₁ s₂ (h q s₁ h₁) (h q s₂ h₂) r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp)

theorem candidateStep_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (Live0 p T)) (candidateStep c.call) (fun _ _ => True) := by
  unfold candidateStep
  have gt : RelCT isa (Two (Live0 p T)) (.block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]) (fun _ _ => True) := by
    change RelCT isa _ (.block ([arg .r0 0 4] ++ [.dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)])) _
    exact RelCT.block_append (RelCT.seq (ldrSp_ct (guard_load p T)) (two_taint _ (live0'_pins p T) (by taint_decide)))
  refine RelCT.seq (two_post gt (guard_ready p T)) ?_
  refine two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun q t => ShortCT p q.1 t)
      (zeroOut_ct (live_pins45 fun q s h => h.1.1.1)) fun q s h => ?_) (two_map (fun q => q.1) (fun _ _ h => h) (short_ct p))
    obtain ⟨⟨⟨⟨o, _, hl, _⟩, _⟩, _⟩, _⟩ := h
    exact WP.mono (zeroOut_ok hl.toSearchBase) fun t ⟨⟨_, hf⟩, k⟩ =>
      ⟨o, hl.toSearchBase.step k (by decide) hf (out_changes hl.input) (out_apart hl.input),
        (k.gpr .r8 (by decide)).trans hl.r8⟩
  · refine RelCT.seq ((candidateRun_ct c p T).mono (fun s₁ s₂ ⟨q, h₁, h₂, sp⟩ => ⟨q, ?_, ?_, sp⟩) fun _ _ h => h)
      (classify_ct p T)
    · rcases h₁ with ⟨⟨⟨lv, hk⟩, eg⟩, ef⟩
      refine ⟨lv, hk, ?_⟩
      obtain ⟨o, -, hl, -⟩ := lv
      have := hl.used_le
      rw [eg] at ef
      have := of_decide_eq_false (Option.some.inj ef)
      omega_arith
    · rcases h₂ with ⟨⟨⟨lv, hk⟩, eg⟩, ef⟩
      refine ⟨lv, hk, ?_⟩
      obtain ⟨o, -, hl, -⟩ := lv
      have := hl.used_le
      rw [eg] at ef
      have := of_decide_eq_false (Option.some.inj ef)
      omega_arith

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # The search's loop is constant time (ARMv7)

Both runs go on or stop together, to the same next point (`ct_step`),
which consumes more of the tape: the loop rule's measure is the tape left.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.RsaKeyGen.Arm.Search

/-- A finished search of a run whose trace is `T`. -/
def DoneCT (p : SearchPublic) (T : List Nat) (_q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchDone p o (searchResult o) s

def ZeroCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  LiveCT p T q s ∧ isa.eval .eq s = some (decide (q.2.1 = 0))

theorem zero_ready (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (.block [.cmp .r9 (.imm 0)]) s (ZeroCT p T q) := by
  obtain ⟨o, hT, hl, hf⟩ := h
  have := hl.input.remaining_le
  have := hl.remaining_le
  exact WP.mono (cmp0_ok hl.r9 (by omega_arith)) fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨o, hT, hl.keep k hm, hf⟩, he⟩

theorem iteration_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.r9] (fun q s₁ s₂ h₁ h₂ r hr => live_pins p T q s₁ s₂ h₁ h₂ r (by
    obtain rfl := List.mem_singleton.mp hr; simp)) (by taint_decide) (zero_ready p T)) ?_
  refine RelCT.seq (two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (exhausted_ct (live_pins45 fun q s h => h.1.1)) ((candidateStep_ct c p T).mono
      (fun s₁ s₂ ⟨q, h₁, h₂, sp⟩ => ⟨q, ⟨h₁.1.1, ?_⟩, ⟨h₂.1.1, ?_⟩, sp⟩) fun _ _ h => h)) (quiet_ct (by taint_decide))
  · have := h₁.1.2; rw [h₁.2] at this; exact of_decide_eq_false (Option.some.inj this.symm)
  · have := h₂.1.2; rw [h₂.2] at this; exact of_decide_eq_false (Option.some.inj this.symm)

/-- What an iteration leaves, at the point `q`, in public terms. -/
def CTStep (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  if pubCont p T q then isa.eval .eq t = some true ∧ LiveCT p T (nextPt p T q) t
  else isa.eval .eq t = some false ∧ DoneCT p T q t

theorem ct_step (c : Cand) (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (iteration c.call) s (CTStep p T q) := by
  obtain ⟨o, hT, hl, hf⟩ := h
  refine WP.mono (iteration_ok c hl hf) fun t ht => ?_
  unfold IterPost at ht
  unfold CTStep
  have hc := cont_iff hl.input hT hf
  by_cases e : Cont p o q.1 q.2.1
  · rw [ite_eq_left e] at ht
    rw [ite_eq_left (hc.mp e)]
    obtain ⟨he, ht', hf'⟩ := ht
    have hk := e.1
    have eu := used_eq hl.input hT hf hk
    have es := status_eq hT hf hk
    have el := leak_of hT hf hk
    refine ⟨he, o, hT, ?_, ?_⟩
    · unfold nextPt; unfold nextK at ht'; rw [← eu, ← es]; exact ht'
    · unfold nextPt; unfold nextK at hf'; rw [hf', ← eu, ← es, el]
  · rw [ite_eq_right e] at ht
    rw [ite_eq_right (fun h => e (hc.mpr h))]
    exact ⟨ht.1, o, hT, ht.2⟩

/-- Pairs of loop states at the same point, the tape left `n`. -/
def LoopPair (p : SearchPublic) (T : List Nat) (n : Nat) (s t : State) : Prop :=
  ∃ q : Pt, n = p.randLen - q.1 ∧ LiveCT p T q s ∧ LiveCT p T q t ∧ s.sp = t.sp

theorem iteration_pair (c : Cand) (p : SearchPublic) (T : List Nat) (n : Nat) :
    RelCT isa (LoopPair p T n) (iteration c.call) fun s t =>
      isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → Two (DoneCT p T) s t) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair p T m s t) := by
  have wp (q : Pt) (s : State) (h : n = p.randLen - q.1 ∧ LiveCT p T q s) :
      WP isa (iteration c.call) s fun t => n = p.randLen - q.1 ∧ CTStep p T q t :=
    WP.mono (ct_step c p T q s h.2) fun _ r => ⟨h.1, r⟩
  have ct := two_post ((iteration_ct c p T).mono
    (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.2, ht.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, m, hs, ht, sp⟩ => ⟨q, ⟨m, hs⟩, ⟨m, ht⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨m, hs⟩, ⟨_, ht⟩, sp⟩
  unfold CTStep at hs ht
  by_cases e : pubCont p T q
  · rw [ite_eq_left e] at hs ht
    refine ⟨hs.1.trans ht.1.symm, fun h => (by rw [hs.1] at h; cases h), fun _ => ?_⟩
    obtain ⟨o, -, hl, -⟩ := hs.2
    have hb := hl.used_le
    refine ⟨p.randLen - (nextPt p T q).1, ?_, nextPt p T q, rfl, hs.2, ht.2, sp⟩
    have := e.2.2.2
    unfold nextPt at hb ⊢
    omega
  · rw [ite_eq_right e] at hs ht
    refine ⟨hs.1.trans ht.1.symm, fun _ => ⟨q, hs.2, ht.2, sp⟩, fun h => (by rw [hs.1] at h; cases h)⟩

theorem loop_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (.loop (iteration c.call) .eq) (Two (DoneCT p T)) := by
  intro s t ts tt u v ⟨q, hs, ht, sp⟩ es et
  exact RelCT.loop (LoopPair p T) (iteration_pair c p T) (p.randLen - q.1) s t ts tt u v
    ⟨q, rfl, hs, ht, sp⟩ es et

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # The search is constant time (ARMv7) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The loop's first point. -/
def startPt (p : SearchPublic) : Pt := (0, p.remaining, [])

/-- A run's state after the push, at the first point. -/
def StartCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  q = startPt p ∧ ∃ o, s = pushed pushRegs o ∧ SearchInput p o ∧ (searchResult o).trace = T

/-- After the load of the state's pointer. -/
def Start' (p : SearchPublic) (_T : List Nat) (_q : Pt) (t : State) : Prop :=
  ∃ o, SearchInput p o ∧ t.gpr .r12 = p.stp ∧ ∀ r ∈ [Reg.r0, .r1, .r2, .r3], t.gpr r = o.gpr r

theorem start_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : StartCT p T q s) :
    WP isa (.block [arg .r12 0 7]) s (Start' p T q) := by
  obtain ⟨-, o, rfl, hi, -⟩ := h
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) hi.1.1
  have top := hi.1.2.1
  have a68 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 (pushBytes + 0 + 4 * 7)) = stackArgAddr o 7 := by
    rw [show pushBytes + 0 + 4 * 7 = 40 + 4 * 7 from rfl, sub_add_ofNat]; rfl
  have r68 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 7) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [hi.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 7 = stackArgAddr o 0 + BitVec.ofNat 64 28 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega_using [top])
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v68 : (pushed pushRegs o).mem.readW (stackArgAddr o 7) 32 = p.stp := by
    rw [hi.arg_frame (push_frame hi) (by decide), ← hi.2]; rfl
  have c : pushBytes + 0 + 4 * 7 < 4096 := by decide
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.gpr .r12 = p.stp) ?_ (by rfl) (by rfl))
    fun t ⟨h12, k⟩ => ⟨o, hi, h12, fun r hr => by
      rw [k.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl <;> decide)]; rfl⟩
  unfold arg
  ffrun [pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a68, r68, v68, c, show 4 * pushRegs.length = 40 from rfl]

theorem start_pins (p : SearchPublic) (T : List Nat) : Pins (Start' p T) [.r0, .r1, .r2, .r3, .r12] := by
  rintro q s₁ s₂ ⟨o₁, h₁, a₁, g₁⟩ ⟨o₂, h₂, a₂, g₂⟩ r hr
  have e (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) : o₁.gpr r = o₂.gpr r := by
    have b₁ := h₁.2
    have b₂ := h₂.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (congrArg SearchPublic.op b₁).trans (congrArg SearchPublic.op b₂).symm
    · have := (congrArg SearchPublic.len b₁).trans (congrArg SearchPublic.len b₂).symm
      exact BitVec.eq_of_toNat_eq this
    · exact (congrArg SearchPublic.up b₁).trans (congrArg SearchPublic.up b₂).symm
    · exact (congrArg SearchPublic.ep b₁).trans (congrArg SearchPublic.ep b₂).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact (g₁ _ (by simp)).trans ((e _ (by simp)).trans (g₂ _ (by simp)).symm)
  · exact a₁.trans a₂.symm

theorem entry_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (StartCT p T)) (.block entry) (Two (LiveCT p T)) := by
  refine two_post ?_ fun q s ⟨hq, o, hs, hi, hT⟩ => ?_
  · change RelCT isa _ (.block ([arg .r12 0 7] ++ entry.drop 1)) _
    exact RelCT.block_append (RelCT.seq (ldrSp_ct (start_load p T)) (two_taint _ (start_pins p T) (by taint_decide)))
  · subst hq hs
    refine WP.mono (entry_ok hi) fun t ht => ⟨o, hT, ht, ?_⟩
    obtain ⟨-, rfl⟩ := id hi
    exact (consume_zero _).symm

/-- A finished run after the load of the state's pointer. -/
def Fin' (p : SearchPublic) (T : List Nat) (_q : Pt) (t : State) : Prop :=
  t.gpr .r12 = p.stp ∧ t.gpr .r6 = p.up ∧ ∃ o, (searchResult o).trace = T

theorem fin_load (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : DoneCT p T q s) :
    WP isa (.block [arg .r12 0 7]) s (Fin' p T q) := by
  obtain ⟨o, hT, hd⟩ := h
  have hb := hd.toSearchBase
  have v : stackArg o 7 = p.stp := by rw [← hb.input.2]; rfl
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.gpr .r12 = p.stp) ?_ (by rfl) (by rfl))
    fun t ⟨h12, k⟩ => ⟨h12, (k.gpr .r6 (by decide)).trans hb.r6, o, hT⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 7 < 4096 := by decide
  ffrun [hb.arg_addr 7, hb.arg_read (j := 7) (by decide), hb.arg_value (j := 7) (by decide), v, c]

theorem fin_pins (p : SearchPublic) (T : List Nat) : Pins (Fin' p T) [.r6, .r12] := by
  rintro q s₁ s₂ ⟨a₁, b₁, -⟩ ⟨a₂, b₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [b₁.trans b₂.symm, a₁.trans a₂.symm]

theorem finish_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (DoneCT p T)) (.block finish) (fun _ _ => True) := by
  change RelCT isa _ (.block ([arg .r12 0 7] ++ (results.drop 1 ++ restore))) _
  refine RelCT.block_append (RelCT.seq (ldrSp_ct (fin_load p T)) (RelCT.block_append (RelCT.seq
    (VG.Proof.Bignum.Arm.relCT_keep_sp (two_taint _ (fin_pins p T) (by taint_decide)) fun _ _ ⟨_, _, _, sp⟩ => sp) ?_)))
  exact (VG.Proof.Bignum.Arm.stackLoads_ct [(.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20),
    (.r10, 24), (.r11, 28), (.lr, 36)]).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The whole search -/

theorem body_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (StartCT p T)) (body c.call) (fun _ _ => True) := by
  unfold body
  exact RelCT.seq (entry_ct p T) (RelCT.seq (loop_ct c p T) (finish_ct p T))

theorem pub_same {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨hsp, r0, r1, r2, r3, ha, he, hw, -⟩ := h
  have h0 : s.mem.readW (State.addr (stackArg t 7)) 64 = t.mem.readW (State.addr (stackArg t 7)) 64 := by
    have := congrArg List.head? hw
    rw [ha 7 (by decide)] at this
    simpa [Spec.Rsa.wordsAt, List.range_succ] using this
  unfold searchOfState
  simp only [searchRemaining, searchLen, hsp, r0, r1, r2, r3, he, ha 0 (by decide), ha 1 (by decide),
    ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide),
    ha 7 (by decide), h0]

theorem code_ct (c : Cand) :
    RelCT isa (fun s t => searchPre s ∧ searchPre t ∧ searchPub s t) (code c.call) (fun _ _ => True) := by
  unfold Impl.RsaKeyGen.Arm.Search.code
  refine RelCT.frame (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb u v ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ e1 e2
  have rs : 232 ≤ s.sp.toNat := hs.1
  have rt : 232 ≤ t.sp.toNat := ht.1
  rw [push_pushed (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith)] at ea eb
  cases ea
  cases eb
  have hpt := pub_same hp
  exact body_ct c (searchOfState s) (searchResult s).trace _ _ ta tb u v
    ⟨startPt _, ⟨rfl, s, rfl, ⟨hs, rfl⟩, rfl⟩, ⟨by rw [hpt], t, rfl, ⟨ht, hpt.symm⟩,
      hp.2.2.2.2.2.2.2.2.2.2.2.symm⟩, by simp only [pushed_sp, hp.1]⟩ e1 e2

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) :=
  RelCT.constantTime (code_ct c)

end VG.Proof.RsaKeyGen.Arm.Search

end

end

/-! # The verified prime search (ARMv7)

For any candidate within 160 bytes of stack (`search_verified_of`), and for
the candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/Arm/RsaKeyGen.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

/-- The candidate's frame, 56 bytes, above the round's 56. -/
theorem cand_stack (v : RoundImpl) :
    FrameStack.armStack (Impl.RsaKeyGen.Arm.Candidate.code v.name v.code v.mont.callOp.op v.mont.dbl) ≤ 160 := by
  have h1 := v.stack
  have h2 := v.mont.stackOk
  have h3 := v.mont.dblOk.1
  simp only [Impl.RsaKeyGen.Arm.Candidate.foL, Impl.RsaKeyGen.Arm.Candidate.foUsed, Impl.RsaKeyGen.Arm.Candidate.foE,
    Impl.RsaKeyGen.Arm.Candidate.foOut, Impl.RsaKeyGen.Arm.Candidate.aoEl, Impl.RsaKeyGen.Arm.Candidate.aoP,
    Impl.RsaKeyGen.Arm.Candidate.aoPl, Impl.RsaKeyGen.Arm.Candidate.aoR, Impl.RsaKeyGen.Arm.Candidate.aoRl,
    Impl.RsaKeyGen.Arm.Candidate.aoS, Impl.RsaKeyGen.Arm.Candidate.aoSl, Impl.RsaKeyGen.Arm.Candidate.mBase,
    Impl.RsaKeyGen.Arm.Candidate.aC, Impl.RsaKeyGen.Arm.Candidate.aTab, Impl.RsaKeyGen.Arm.Candidate.aE,
    Impl.RsaKeyGen.Arm.Candidate.aPr, Impl.RsaKeyGen.Arm.Candidate.aD1, Impl.RsaKeyGen.Arm.Candidate.aD2,
    Impl.RsaKeyGen.Arm.Candidate.aAbs, Impl.RsaKeyGen.Arm.Candidate.aBnd, Impl.RsaKeyGen.Arm.Candidate.aTmp,
    Impl.RsaKeyGen.Arm.Candidate.aOne, Impl.RsaKeyGen.Arm.Candidate.aTwo, Impl.RsaKeyGen.Arm.Candidate.aCm1,
    Impl.RsaKeyGen.Arm.Candidate.aX, Impl.RsaKeyGen.Arm.Candidate.aXf, Impl.RsaKeyGen.Arm.Candidate.aH1,
    Impl.RsaKeyGen.Arm.Candidate.aH2, Impl.RsaKeyGen.Arm.Candidate.aHm, Impl.RsaKeyGen.Arm.Candidate.aEx,
    Impl.RsaKeyGen.Arm.Candidate.nArr, Impl.RsaKeyGen.Arm.Candidate.sUsed, Impl.RsaKeyGen.Arm.Candidate.sCl,
    Impl.RsaKeyGen.Arm.Candidate.sLt, Impl.RsaKeyGen.Arm.Candidate.sTr, Impl.RsaKeyGen.Arm.Candidate.sEo,
    Impl.RsaKeyGen.Arm.Candidate.sE1, Impl.RsaKeyGen.Arm.Candidate.sG, Impl.RsaKeyGen.Arm.Candidate.sI,
    Impl.RsaKeyGen.Arm.Candidate.sUni, Impl.RsaKeyGen.Arm.Candidate.sU, Impl.RsaKeyGen.Arm.Candidate.sA,
    Impl.RsaKeyGen.Arm.Candidate.sBb, Impl.RsaKeyGen.Arm.Candidate.sTc, Impl.RsaKeyGen.Arm.Candidate.sBit,
    Impl.RsaKeyGen.Arm.Candidate.sCnt, Impl.RsaKeyGen.Arm.Candidate.sS1, Impl.RsaKeyGen.Arm.Candidate.sS2,
    Impl.RsaKeyGen.Arm.Candidate.sS3, Impl.RsaKeyGen.Arm.Candidate.sLo, Impl.RsaKeyGen.Arm.Candidate.sHi,
    Impl.RsaKeyGen.Arm.Candidate.sF, Impl.RsaKeyGen.Arm.Candidate.sStat, Impl.RsaKeyGen.Arm.Candidate.sChk,
    Impl.RsaKeyGen.Arm.Candidate.sMask, Impl.RsaKeyGen.Arm.Candidate.ctxB, Impl.RsaKeyGen.Arm.Candidate.ctxW,
    Impl.RsaKeyGen.Arm.Candidate.ctx, Impl.RsaKeyGen.Arm.Candidate.ltS, Impl.RsaKeyGen.Arm.Candidate.setS,
    Impl.RsaKeyGen.Arm.Candidate.invOf, Impl.RsaKeyGen.Arm.Candidate.finish, Impl.RsaKeyGen.Arm.Candidate.finNone,
    Impl.RsaKeyGen.Arm.Candidate.finUsed, Impl.RsaKeyGen.Arm.Candidate.finPrime, Impl.RsaKeyGen.Arm.Candidate.entry,
    Impl.RsaKeyGen.Arm.Candidate.lenCheck, Impl.RsaKeyGen.Arm.Candidate.setupC, Impl.RsaKeyGen.Arm.Candidate.topBits,
    Impl.RsaKeyGen.Arm.Candidate.candBits, Impl.RsaKeyGen.Arm.Candidate.loadC,
    Impl.RsaKeyGen.Arm.Candidate.closeCalc, Impl.RsaKeyGen.Arm.Candidate.closeCheck,
    Impl.RsaKeyGen.Arm.Candidate.tabStore, Impl.RsaKeyGen.Arm.Candidate.tabWrite, Impl.RsaKeyGen.Arm.Candidate.bigW,
    Impl.RsaKeyGen.Arm.Candidate.table, Impl.RsaKeyGen.Arm.Candidate.newton, Impl.RsaKeyGen.Arm.Candidate.entryS,
    Impl.RsaKeyGen.Arm.Candidate.redc, Impl.RsaKeyGen.Arm.Candidate.trialWord,
    Impl.RsaKeyGen.Arm.Candidate.trialFlag, Impl.RsaKeyGen.Arm.Candidate.trialPrime,
    Impl.RsaKeyGen.Arm.Candidate.trialStep, Impl.RsaKeyGen.Arm.Candidate.trial,
    Impl.RsaKeyGen.Arm.Candidate.gcdCheck, Impl.RsaKeyGen.Arm.Candidate.montSet,
    Impl.RsaKeyGen.Arm.Candidate.strideW, Impl.RsaKeyGen.Arm.Candidate.mont0, Impl.RsaKeyGen.Arm.Candidate.clrTop,
    Impl.RsaKeyGen.Arm.Candidate.montA, Impl.RsaKeyGen.Arm.Candidate.montB, Impl.RsaKeyGen.Arm.Candidate.cnt8,
    Impl.RsaKeyGen.Arm.Candidate.halfInit, Impl.RsaKeyGen.Arm.Candidate.halfBit,
    Impl.RsaKeyGen.Arm.Candidate.cntNext, Impl.RsaKeyGen.Arm.Candidate.halfBody,
    Impl.RsaKeyGen.Arm.Candidate.halving, Impl.RsaKeyGen.Arm.Candidate.sigMasks,
    Impl.RsaKeyGen.Arm.Candidate.powWord, Impl.RsaKeyGen.Arm.Candidate.halfIf, Impl.RsaKeyGen.Arm.Candidate.expTop,
    Impl.RsaKeyGen.Arm.Candidate.expSetup, Impl.RsaKeyGen.Arm.Candidate.ltAdd, Impl.RsaKeyGen.Arm.Candidate.checksC,
    Impl.RsaKeyGen.Arm.Candidate.mrInit, Impl.RsaKeyGen.Arm.Candidate.avFlag,
    Impl.RsaKeyGen.Arm.Candidate.witnessLoad, Impl.RsaKeyGen.Arm.Candidate.orTwo,
    Impl.RsaKeyGen.Arm.Candidate.clrTopBit, Impl.RsaKeyGen.Arm.Candidate.witnessFix,
    Impl.RsaKeyGen.Arm.Candidate.wsLen, Impl.RsaKeyGen.Arm.Candidate.mrCall, Impl.RsaKeyGen.Arm.Candidate.goFlag,
    Impl.RsaKeyGen.Arm.Candidate.onPass, Impl.RsaKeyGen.Arm.Candidate.mrBody,
    Impl.RsaKeyGen.Arm.Candidate.millerRabin, Impl.RsaKeyGen.Arm.Candidate.mrResult,
    Impl.RsaKeyGen.Arm.Candidate.mrPart, Impl.RsaKeyGen.Arm.Candidate.main, Impl.RsaKeyGen.Arm.Candidate.body,
    Impl.RsaKeyGen.Arm.Candidate.code, Impl.Bignum.Arm.TrialDivision16.newton, Impl.Bignum.Arm.TrialDivision16.redc,
    Impl.Bignum.Arm.TwoPower.code, Proof.Bignum.Arm.MontBackend.callOp, Impl.Bignum.Arm.MontCall.op,
    Impl.Bignum.Arm.MontCall.opArgs, Impl.Bignum.Arm.r2WithDbl, Impl.Bignum.Arm.DoubleCall.loop,
    Proof.Bignum.Arm.MontBackend.dbl, Impl.Bignum.Arm.r2SquaresWith, Impl.Bignum.Arm.r2SquareStepWith,
    Impl.Bignum.Arm.precomputeInverse, Impl.Bignum.Arm.setup, Impl.Bignum.Arm.store64, Impl.Bignum.Arm.zero,
    Impl.Rsa.Arm.CrtValues.load, Impl.Rsa.Arm.CrtValues.store, Impl.Rsa.Arm.Keys.aM, Impl.Rsa.Arm.Keys.aNM,
    Impl.Rsa.Arm.Keys.aZero, Impl.Rsa.Arm.Keys.bitOf, Impl.Rsa.Arm.Keys.copy, Impl.Rsa.Arm.Keys.eqS,
    Impl.Rsa.Arm.Keys.half, Impl.Rsa.Arm.Keys.hdr, Impl.Rsa.Arm.Keys.inverse, Impl.Rsa.Arm.Keys.orOne,
    Impl.Rsa.Arm.Keys.ptr, Impl.Rsa.Arm.Keys.sel, Impl.Rsa.Arm.Keys.seqs, Impl.Rsa.Arm.Keys.stride,
    Impl.Rsa.Arm.Keys.sub3, Impl.Rsa.Arm.Keys.subN, Impl.Rsa.Arm.Keys.selN, Impl.Rsa.Arm.Keys.copyN,
    Impl.Rsa.Arm.Recover.clrTop, Impl.RsaKeyGen.Arm.Key.andNotS, Impl.RsaKeyGen.Arm.Key.isOne,
    Impl.RsaKeyGen.Arm.Key.notS, Impl.RsaKeyGen.Arm.Key.setHi, Impl.RsaKeyGen.Arm.Key.setWd,
    Impl.RsaKeyGen.Arm.Key.zeroOut, Impl.RsaKeyGen.tabEntry, Impl.Bignum.Arm.TwoPower.step,
    Impl.Bignum.Arm.compareWords, Impl.Bignum.Arm.copyWords, Impl.Bignum.Arm.loadBE, Impl.Bignum.Arm.maskBytes,
    Impl.Bignum.Arm.selectRow, Impl.Bignum.Arm.subRow, Impl.Rsa.Arm.Keys.Inv.batch, Impl.Rsa.Arm.Keys.Inv.finish,
    Impl.Rsa.Arm.Keys.Inv.init, Impl.Rsa.Arm.Keys.eqNormalize, Impl.Rsa.Arm.shiftRight,
    Impl.Bignum.Arm.TrialDivision16.redcAt, Impl.Bignum.Arm.compareWordStep, Impl.Bignum.Arm.copyWordBody,
    Impl.Bignum.Arm.loadBEreverseArgs, Impl.Bignum.Arm.maskByteStep, Impl.Bignum.Arm.reverseBytes,
    Impl.Bignum.Arm.selectBody, Impl.Bignum.Arm.selectMask, Impl.Bignum.Arm.subBody, Impl.Bignum.Arm.zeroStep,
    Impl.Rsa.Arm.Keys.Inv.bA1, Impl.Rsa.Arm.Keys.Inv.bD, Impl.Rsa.Arm.Keys.Inv.bE, Impl.Rsa.Arm.Keys.Inv.bF,
    Impl.Rsa.Arm.Keys.Inv.bG, Impl.Rsa.Arm.Keys.Inv.bP, Impl.Rsa.Arm.Keys.Inv.bT1, Impl.Rsa.Arm.Keys.Inv.bT2,
    Impl.Rsa.Arm.Keys.Inv.bZ, Impl.Rsa.Arm.Keys.Inv.copy1, Impl.Rsa.Arm.Keys.Inv.divsteps,
    Impl.Rsa.Arm.Keys.Inv.fSign, Impl.Rsa.Arm.Keys.Inv.negInv, Impl.Rsa.Arm.Keys.Inv.sel1,
    Impl.Rsa.Arm.Keys.Inv.start, Impl.Rsa.Arm.Keys.Inv.sub1, Impl.Rsa.Arm.Keys.Inv.topZero,
    Impl.Rsa.Arm.Keys.Inv.update, Impl.Rsa.Arm.Keys.Inv.fgPass, Impl.Rsa.Arm.Keys.Inv.dePass,
    Impl.Rsa.Arm.Keys.Inv.spill, Impl.Rsa.Arm.Keys.Inv.rowPrep, Impl.Rsa.Arm.Keys.Inv.topMask,
    Impl.Rsa.Arm.Keys.Inv.ldCoef, Impl.Rsa.Arm.Keys.Inv.coefStore, Impl.Rsa.Arm.Keys.Inv.absMask,
    Impl.Rsa.Arm.Keys.Inv.corrAdd, Impl.Rsa.Arm.Keys.Inv.fgTerms, Impl.Rsa.Arm.Keys.Inv.deTerms,
    Impl.Rsa.Arm.Keys.Inv.term, Impl.Rsa.Arm.Keys.Inv.out0, Impl.Rsa.Arm.Keys.Inv.outW, Impl.Rsa.Arm.Keys.Inv.outTop,
    Impl.Rsa.Arm.Keys.Inv.wordDone, Impl.Rsa.Arm.Keys.Inv.restore, Impl.Rsa.Arm.Keys.Inv.mdPrep,
    Impl.Rsa.Arm.Keys.Inv.signTop, Impl.Rsa.Arm.Keys.Inv.zero1, Impl.Rsa.Arm.Keys.Inv.zeroW,
    Impl.Rsa.Arm.Keys.setOne, Impl.Rsa.Arm.shiftRightStep, Impl.Bignum.Arm.copyWord, Impl.Bignum.Arm.reverseByteStep,
    Impl.Bignum.Arm.selectStep, Impl.Bignum.Arm.subAdvance, Impl.Bignum.Arm.subStep, Impl.Rsa.Arm.Keys.Inv.cnt1,
    Impl.Bignum.Arm.rowAdvance, Impl.Bignum.Arm.selectWord, Impl.Bignum.Arm.subBorrow, Impl.Bignum.Arm.initInverse,
    Impl.Bignum.Arm.r2Init, Impl.Bignum.Arm.setBases, Impl.Rsa.Arm.Keys.Inv.bA2, Impl.Bignum.Arm.r2Constants,
    Impl.Bignum.Arm.smallConst, Impl.Bignum.Arm.setSmallFn, Impl.Bignum.Arm.setSmallFnBody, Impl.Bignum.Arm.setSmall,
    FrameStack.armStack, List.cons_append, List.nil_append, Nat.max_zero, Nat.zero_max, Nat.max_self,
    List.length_cons, List.length_nil] at h3 ⊢
  omega_using [h1, h2, h3]

theorem search_verified_of (c : Cand) :
    Verified target (Impl.RsaKeyGen.Arm.Search.code c.call)
      (Proof.RsaKeyGen.primeSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

/-- `vg_rsa_keygen_candidate` calling the shared round `v`, as the search
calls it. -/
def Cand.ofRound [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : Cand where
  name := "vg_rsa_keygen_candidate" ++ v.suffix
  code := Impl.RsaKeyGen.Arm.Candidate.code v.name v.code v.mont.callOp.op v.mont.dbl
  verified := Proof.RsaKeyGen.Arm.Cand.cand_verified v v.mont.callOp v.mont.callDbl
  stack := cand_stack v

/-- The search calling it. -/
abbrev searchCode [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : Prog isa :=
  Impl.RsaKeyGen.Arm.Search.code (Cand.ofRound v).call

theorem search_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    Verified target (searchCode v) (Proof.RsaKeyGen.primeSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)

end VG.Proof.RsaKeyGen.Arm.Search
