module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # The whole search (ARMv7): its results stored, and the contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)

/-- The state's eight halves, for a finished search. -/
def stateWords (p : SearchPublic) (r : PrimeSearchResult) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 r.remaining), (1, 0), (2, BitVec.ofNat 32 p.len), (3, 0),
    (4, BitVec.ofNat 32 (32769 * p.len)), (5, 0), (6, BitVec.ofNat 32 r.requested), (7, 0)]

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
    VG.Arm.addr_add (by have := f.nT; omega)
  have aU (d : Nat) (hd : d < 8) : State.addr (p.up + BitVec.ofNat 32 d) = off (State.addr p.up) d :=
    VG.Arm.addr_add (by have := f.nU; omega)
  have wT (d : Nat) (hd : d + 4 ≤ 32) : InRegions s.wr (off (State.addr p.stp) d) 4 :=
    ⟨inState o, by rw [h.wr, hi.wr]; simp [inWrites], by rw [eT]; exact Offset.contains_base _ hd (by omega)⟩
  have wU (d : Nat) (hd : d + 4 ≤ 8) : InRegions s.wr (off (State.addr p.up) d) 4 :=
    ⟨inUsed o, by rw [h.wr, hi.wr]; simp [inWrites], by rw [eU]; exact Offset.contains_base _ hd (by omega)⟩
  have c7 : pushBytes + 0 + 4 * 7 < 4096 := by decide
  have stp : stackArg o 7 = p.stp := by rw [← hi.2]; rfl
  unfold results arg finished stateWords writeSlots
  ffrun [h.arg_addr 7, h.arg_read (j := 7) (by decide), h.arg_value (j := 7) (by decide), stp, c7,
    h.r5, h.r6, h.r8, h.r9, h.r10, h.r11, aT 0 (by decide), aT 4 (by decide), aT 8 (by decide), aT 12 (by decide),
    aT 16 (by decide), aT 20 (by decide), aT 24 (by decide), aT 28 (by decide), aU 0 (by decide), aU 4 (by decide),
    wT 0 (by decide), wT 4 (by decide), wT 8 (by decide), wT 12 (by decide), wT 16 (by decide), wT 20 (by decide),
    wT 24 (by decide), wT 28 (by decide), wU 0 (by decide), wU 4 (by decide), shl32' p.len 15 (by omega),
    add_ofNat32, show p.len * 2 ^ 15 + p.len = 32769 * p.len by omega]
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
  refine (finished_frame h m r).bytes (R := inOut o) (fun q hq => ?_) (by rw [eO]; simp only; omega)
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
    (h0 : r.remaining < 2 ^ 32) (h1 : p.len < 2 ^ 32) (h2 : 32769 * p.len < 2 ^ 32) (h3 : r.requested < 2 ^ 32) :
    Spec.Rsa.wordsAt (finished p m r) (State.addr p.stp) 4 = [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
      BitVec.ofNat 64 (32769 * p.len), BitVec.ofNat 64 r.requested] := by
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
    · rw [eT]; exact Offset.contains_base _ (by omega) (by omega)
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
  have S1n : p.S1.toNat = p.sp.toNat - 40 := FrameStack.sub_toNat' (by omega)
  have a (d : Nat) (hd : d < 40) : State.addr (s.sp + BitVec.ofNat 32 d) = State.addr p.S1 + BitVec.ofNat 64 d := by
    rw [hsp]; exact VG.Arm.addr_add (by omega)
  have r (d : Nat) (hd : d + 4 ≤ 40) : InRegions (s.rd ++ s.wr) (State.addr p.S1 + BitVec.ofNat 64 d) 4 :=
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ hd (by omega)⟩
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
    rw [BitVec.add_zero, SearchPublic.S1, FrameStack.addr_sub' (by omega), h.sp_eq]
    exact h.stack_sub (by decide) (by decide)
  exact fun q hq => SearchInput.disj_sub (h.stack_disjoint (List.mem_append_left _ hq)) push

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  have f := hp.facts
  have room : 184 ≤ s.sp.toNat := h.1
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  have rl := f.randLen
  unfold primeEntropy at rl
  have rem := hp.remaining_le
  unfold code body
  refine WP.frame (rs := pushRegs) (r := .r4) (by decide) (by simp; omega) (by decide) ?_
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
  refine WP.mono (restore_ok hp (k3.sp.trans hd.sp) hw3 hsv) fun s4 ⟨⟨hr, hm4⟩, k4⟩ => ?_
  have sp4 : s4.sp = p.S1 := k4.sp.trans (k3.sp.trans hd.sp)
  have mem : (popped .r4 (4 * pushRegs.length) s4).mem = finished p s2.mem (searchResult s) := by
    rw [popped_mem, hm4, hm3]
  have g0 : (popped .r4 (4 * pushRegs.length) s4).gpr .r0 = BitVec.ofNat 32 (searchResult s).status := by
    rw [popped_gpr (by decide), k4.gpr .r0 (by decide), h0]
  have g4 : (popped .r4 (4 * pushRegs.length) s4).gpr .r4 = s.gpr .r4 := by
    simp only [popped, RegUpd.gpr_setReg, ite_true]
    rw [sp4, hm4, ← BitVec.add_zero (State.addr p.S1)]
    exact hsv (.r4, 0) (by simp)
  obtain ⟨bu, br, bq⟩ := hd.bounds
  have st := status_lt (searchResult s)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun r hr' => ?_, ?_⟩
  · rw [BitVec.setWidth_append_eq_right, g0, toNat_small (by omega)]
  · change Spec.Rsa.bytesAt _ (State.addr p.op) p.len = _
    rw [mem, finished_bytes hp]
    exact hd.output
  · change Spec.Rsa.wordsAt _ (State.addr p.up) 1 = _
    rw [mem, finished_used _ _ (by omega)]
  · change Spec.Rsa.wordsAt _ (State.addr p.stp) 4 = _
    rw [mem, finished_state hp _ _ (by omega) (by omega) (by omega) (by unfold primeEntropy at bq; omega)]
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
