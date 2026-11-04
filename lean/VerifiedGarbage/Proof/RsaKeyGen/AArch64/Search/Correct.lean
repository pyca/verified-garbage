module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The RSA prime search's correctness (AArch64)

The entry, the loop in its frame saving `x30` (`search_body`), and the
return: the four public words to the state, the octets consumed to `used`,
the status and the caller's `x19` (`search_finish`), all in the search's
frame.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy PrimeSearchResult)

/-! ## Returning -/

/-- The state's four words. -/
def stateWords (m : Mem) (stp : Addr) (r : PrimeSearchResult) (len : Nat) : Mem :=
  (((m.writeW (off stp (8 * 0)) (BitVec.ofNat 64 r.remaining)).writeW (off stp (8 * 1)) (BitVec.ofNat 64 len)).writeW
    (off stp (8 * 2)) (BitVec.ofNat 64 (primeEntropy len))).writeW (off stp (8 * 3))
    (BitVec.ofNat 64 r.requested)

/-- The state's four words, then the octets consumed. -/
def returned (m : Mem) (stp up : Addr) (r : PrimeSearchResult) (len : Nat) : Mem :=
  (stateWords m stp r len).writeW up (BitVec.ofNat 64 r.used)

theorem search_finish_values {p : SPub} {original s : State} {result : PrimeSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 result.status ∧ t.gpr .x19 = original.gpr .x19 ∧
        t.mem = returned s.mem p.stp p.up result p.len) ∧
      Keep [.x0, .x1, .x2, .x9, .x10, .x11, .x12, .x13, .x19] s t := by
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hw : ∀ r ∈ inWrites original, r ∈ s.wr := fun r hr => by
    rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ hr
  have hst : ∀ d, d + 8 ≤ 32 → InRegions s.wr (p.stp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨⟨p.stp, 32⟩, hw _ (by rw [← h.input.state_eq]; simp [inWrites]), Offset.contains_base _ hd (by omega)⟩
  have hst0 : InRegions s.wr p.stp 8 := by simpa only [BitVec.add_zero] using hst 0 (by decide)
  have hup : InRegions s.wr p.up 8 :=
    ⟨⟨p.up, 8⟩, hw _ (by rw [← h.input.used_eq]; simp [inWrites]), by
      simpa only [BitVec.add_zero] using Offset.contains_base p.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)⟩
  have h0 := h.remaining
  have h1 := h.len
  have h2 := h.cap
  have h3 := h.request
  have h7 := h.usedPtr
  have h12 := h.used
  have h14 := h.status
  have h18 := h.stp
  have hx := h.savedX19
  simp only [Bignum.word, off, Nat.reduceMul] at h0 h1 h2 h3 h7 h12 h14 h18 hx
  refine WP.keep [.x0, .x1, .x2, .x9, .x10, .x11, .x12, .x13, .x19] ?_ (by decide) (by decide)
    (by decide +kernel)
  unfold finish returned stateWords
  brun [ldf, h.x19, h0, h1, h2, h3, h7, h12, h14, h18, hx, hl 0 (by decide), hl 8 (by decide), hl 16 (by decide),
    hl 24 (by decide), hl 32 (by decide), hl 56 (by decide), hl 96 (by decide), hl 112 (by decide),
    hl 144 (by decide), hst0, hst 8 (by decide), hst 16 (by decide), hst 24 (by decide), hup]
  simp only [off, Nat.reduceMul, BitVec.add_zero]

/-- What the search returns, for its result. -/
def SReturned (p : SPub) (result : PrimeSearchResult) (t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = result.status ∧
    Spec.Rsa.bytesAt t.mem p.op p.len =
      (match result.outcome with
        | .accepted c => Spec.Rsa.i2osp c p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used] ∧
    Spec.Rsa.wordsAt t.mem p.stp 4 = [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.len,
      BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 result.requested]

theorem stateWords_frame (m : Mem) (stp : Addr) (r : PrimeSearchResult) (len : Nat) :
    Frame [⟨stp, 32⟩] m (stateWords m stp r len) := by
  have hc (j : Nat) (hj : j < 4) : (⟨stp, 32⟩ : Region).Contains (off stp (8 * j)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  exact (((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (hc 0 (by decide))).writeW
    (List.mem_singleton_self _) _ (hc 1 (by decide))).writeW (List.mem_singleton_self _) _
    (hc 2 (by decide))).writeW (List.mem_singleton_self _) _ (hc 3 (by decide))

theorem stateWords_words (m : Mem) (stp : Addr) (r : PrimeSearchResult) (len : Nat) :
    Spec.Rsa.wordsAt (stateWords m stp r len) stp 4 = [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 len,
      BitVec.ofNat 64 (primeEntropy len), BitVec.ofNat 64 r.requested] := by
  change [word (stateWords m stp r len) stp (8 * 0), word (stateWords m stp r len) stp (8 * 1),
    word (stateWords m stp r len) stp (8 * 2), word (stateWords m stp r len) stp (8 * 3)] = _
  unfold stateWords
  simp only [frame_store_word _ _ _ (i := 3) (by decide) (by decide : (0 : Nat) < 20),
    frame_store_word _ _ _ (i := 3) (by decide) (by decide : (1 : Nat) < 20),
    frame_store_word _ _ _ (i := 3) (by decide) (by decide : (2 : Nat) < 20),
    frame_store_word _ _ _ (i := 3) (by decide) (by decide : (3 : Nat) < 20),
    frame_store_word _ _ _ (i := 2) (by decide) (by decide : (0 : Nat) < 20),
    frame_store_word _ _ _ (i := 2) (by decide) (by decide : (1 : Nat) < 20),
    frame_store_word _ _ _ (i := 2) (by decide) (by decide : (2 : Nat) < 20),
    frame_store_word _ _ _ (i := 1) (by decide) (by decide : (0 : Nat) < 20),
    frame_store_word _ _ _ (i := 1) (by decide) (by decide : (1 : Nat) < 20),
    frame_store_word _ _ _ (i := 0) (by decide) (by decide : (0 : Nat) < 20),
    Nat.reduceEqDiff, ite_true, ite_false]

theorem returned_words {p : SPub} {original : State} (hi : SInput p original) (m : Mem)
    (r : PrimeSearchResult) :
    Spec.Rsa.bytesAt (returned m p.stp p.up r p.len) p.op p.len = Spec.Rsa.bytesAt m p.op p.len ∧
    Spec.Rsa.wordsAt (returned m p.stp p.up r p.len) p.up 1 = [BitVec.ofNat 64 r.used] ∧
    Spec.Rsa.wordsAt (returned m p.stp p.up r p.len) p.stp 4 = [BitVec.ofNat 64 r.remaining,
      BitVec.ofNat 64 p.len, BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 r.requested] := by
  have hpw := hi.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  obtain ⟨⟨dou, -, dost⟩, ⟨-, dust⟩, -⟩ := hpw
  rw [hi.out_eq, hi.used_eq] at dou
  rw [hi.out_eq, hi.state_eq] at dost
  rw [hi.used_eq, hi.state_eq] at dust
  have hk := hi.len_bounds
  have hfs := stateWords_frame m p.stp r p.len
  have hfu : Frame [⟨p.up, 8⟩] (stateWords m p.stp r p.len) (returned m p.stp p.up r p.len) :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi' => ?_
    have hi'' := List.mem_range.mp hi'
    have e1 : returned m p.stp p.up r p.len (p.op + BitVec.ofNat 64 i) =
        stateWords m p.stp r p.len (p.op + BitVec.ofNat 64 i) :=
      hfu.bytes (R := ⟨p.op, p.len⟩) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dou)
        (show p.len ≤ 2 ^ 64 by omega) hi''
    have e2 : stateWords m p.stp r p.len (p.op + BitVec.ofNat 64 i) = m (p.op + BitVec.ofNat 64 i) :=
      hfs.bytes (R := ⟨p.op, p.len⟩) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dost)
        (show p.len ≤ 2 ^ 64 by omega) hi''
    exact e1.trans e2
  · change [word (returned m p.stp p.up r p.len) p.up 0] = [_]
    refine congrArg (fun x => [x]) ?_
    simp only [Bignum.word, off, BitVec.add_zero, returned]
    exact Mem.readW_writeW_self64 _ _ _
  · have hu (j : Nat) (hj : j < 4) : word (returned m p.stp p.up r p.len) p.stp (8 * j) =
        word (stateWords m p.stp r p.len) p.stp (8 * j) :=
      hfu.readW (r := ⟨p.stp, 32⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dust.symm) (by decide)
    have hw := stateWords_words m p.stp r p.len
    change [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    change [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _ at hw
    rw [hu 0 (by decide), hu 1 (by decide), hu 2 (by decide), hu 3 (by decide)]
    exact hw

theorem search_finish {p : SPub} {original s : State} {result : PrimeSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t => SReturned p result t ∧
      (∀ reg ∈ preserved, reg ≠ .x30 → t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.gpr .x30 = s.gpr .x30 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64) := by
  refine WP.mono (search_finish_values h) fun t ⟨⟨ha, hr19, hm⟩, k⟩ => ?_
  obtain ⟨hb, hu, hs⟩ := returned_words h.input s.mem result
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.gpr .x30 (by decide), k.rd, k.wr,
    fun r hr => (k.vcs r hr).trans (h.vcs r hr)⟩
  · rw [ha]
    have := result_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [hm, hb]; exact h.output
  · rw [hm]; exact hu
  · rw [hm]; exact hs
  · intro reg hreg h30
    by_cases he : reg = .x19
    · subst he; exact hr19
    · exact (k.gpr reg (by revert reg hreg he; decide)).trans (h.saved reg hreg he h30)

/-! ## The search's frames -/

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem iteration_depth (c : Cand) : (iteration c.call).aarch64Depth = 2 := by
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, rejected,
    Impl.Bignum.AArch64.countLoop, Code.aarch64Depth, Cand.call, depth_of_noFrames c.noFrames,
    Instr.frameUnits]
  rfl

/-- After the frame saving `x30`: a finished search, with `x30` back. -/
theorem SDone.popped {p : SPub} {original s : State} {r : PrimeSearchResult}
    (h : SDone p original r s) (v sp : BitVec 64) :
    SDone p original r { s.write .x .x30 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h19 h30 => ?_, h.vcs, h.savedX19, h.usedPtr, h.stp, h.len,
    h.cap, h.remaining, h.request, h.used, h.status, h.output⟩
  · show (s.write .x .x30 v).gpr .x19 = _
    rw [RegUpd.gpr_write]; exact h.x19
  · show (s.write .x .x30 v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right h30]; exact h.saved reg hr h19 h30

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp only [Spec.Entropy.Result.consume, Nat.zero_add, List.nil_append]

theorem SInput.result_eq {p : SPub} {s : State} (h : SInput p s) :
    searchResult s = (tailOf p s 0 p.remaining).consume 0 [] := by
  rw [consume_zero]
  cases h.2
  simp only [searchResult, tailOf, SPub.tail, sOfState, List.drop_zero]

/-- The push of `x30`, below the frame, is apart from every writable region. -/
theorem push_disjoint {p : SPub} {s t : State} (h : SInput p s) (hw : t.wr = p.frame :: s.wr)
    (hsp : t.sp = p.F) : ∀ R ∈ t.wr, Region.Disjoint ⟨t.sp - 16, 16⟩ R := by
  have hsub : Region.Sub ⟨t.sp - 16, 16⟩ ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩ := by
    rw [hsp, ← h.sp_eq]
    have e : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by rw [SPub.F, BitVec.sub_sub]; rfl
    rw [e]
    exact Offset.sub_below p.sp (a := 176) (b := 208) (by decide) (by decide)
  have hbelow : Region.Sub ⟨s.sp - BitVec.ofNat 64 stackUse, 48⟩ (below s.sp stackUse) :=
    Offset.sub_below s.sp (a := 208) (b := 208) (by decide) (by decide)
  intro R hR
  rw [hw] at hR
  rcases List.mem_cons.mp hR with rfl | hR
  · exact (h.frame_disjoint _ (by simp [SInput.callChanges])).symm.sub_left hsub
  · have hd := h.stack_disjoint (r := R) (List.mem_append_left _ (by rw [← h.1.2.2.2.1]; exact hR))
    exact (hd.sub_left hbelow).sub_left hsub

theorem search_body {p : SPub} {s t : State} (c : Cand) (h : SInput p s)
    (hx : t.gpr .x19 = p.F)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated frameBytes s) t) :
    WP isa (search c.call) t fun u =>
      SDone p s (searchResult s) u ∧ u.gpr .x30 = s.gpr .x30 ∧ u.sp = p.F ∧ u.rd = s.rd ∧
        u.wr = p.frame :: s.wr := by
  have hl := search_start h hx hm k
  have htsp : t.sp = p.F := by rw [k.sp]; exact F_eq h
  have htw : t.wr = p.frame :: s.wr := by
    rw [k.wr]; show (⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr) = _; rw [← h.sp_eq]
  have hsp : 16 ≤ t.sp.toNat := by rw [htsp, h.F_toNat]; have : 208 ≤ p.sp.toNat := h.room; omega
  unfold search
  refine WP.frameReg hsp (push_disjoint h htw htsp) ?_ ?_
  · refine WP.mono (search_loop c (final := searchResult s) (n := p.randLen - 0 + 1)
      ⟨0, p.remaining, rfl, hl, [], h.result_eq⟩) fun u hu => ?_
    refine ⟨hu.popped _ _, ?_, htsp, hu.rd, hu.wr⟩
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (iteration c.call).aarch64Depth + 16 < 2 ^ 64
    rw [iteration_depth c]; decide

theorem SReturned.post {s t : State} (h : SReturned (sOfState s) (searchResult s) t) : searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := sOfState s
  have hp : SInput p s := ⟨h, rfl⟩
  have hroom : frameBytes ≤ s.sp.toNat := by
    have : 208 ≤ p.sp.toNat := hp.room; rw [hp.sp_eq] at this; show 160 ≤ _; omega
  unfold code
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (search_body c hp hx hm k) fun u ⟨hd, h30, hsp, hrd, hwr⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨hr, hg, hqsp, hq30, hqr, hqw, hv⟩ => ?_
  refine ⟨hr.post, fun reg hreg => ?_, ?_, hv⟩
  · by_cases h30 : reg = .x30
    · subst h30; exact hq30.trans h30
    · exact hg reg hreg h30
  · show q.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hqsp, hsp, ← hp.sp_eq]
    exact BitVec.sub_add_cancel _ _

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Search
