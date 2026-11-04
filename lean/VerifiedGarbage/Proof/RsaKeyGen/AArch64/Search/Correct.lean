module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with the constant-time ones, `CT`

/-! # The search's results, and the whole search's correctness (AArch64) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 (st)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)

/-- A read of a region past a store to a disjoint one. -/
theorem read_past {m : Mem} {R W : Region} (hd : R.Disjoint W) {a b : Addr} (ha : R.Contains a 8)
    (hb : W.Contains b 8) (hW : W.len ≤ 2 ^ 64) (v : BitVec 64) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  (Frame.writeW (Frame.refl [W] m) (List.mem_singleton_self _) v hb).readW ha
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd) (by decide)

namespace SearchInput

variable {p : SearchPublic} {s : State}

theorem state_used (h : SearchInput p s) : (inState s).Disjoint (inUsed s) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.2.1.2.symm

theorem out_state (h : SearchInput p s) : (inOut s).Disjoint (inState s) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.2.2

theorem out_used (h : SearchInput p s) : (inOut s).Disjoint (inUsed s) := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.1

end SearchInput

/-- The public words to the state, and the octets consumed to `used`. -/
def finished (p : SearchPublic) (m : Mem) (r : PrimeSearchResult) : Mem :=
  (SearchInit.written m p.stp [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
    BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 r.requested]).writeW p.up (BitVec.ofNat 64 r.used)

/-- The registers `finish` writes. -/
abbrev finishRegs : List Reg := [.x0, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19]

theorem search_finish {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    (h : SearchDone p original final s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 final.status ∧ t.gpr .x19 = original.gpr .x19 ∧
        t.mem = finished p s.mem final) ∧ Keep finishRegs s t := by
  have hi := h.input
  have scr := hi.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have hst : inState original = ⟨p.stp, 32⟩ := by rw [← hi.2]; rfl
  have hus : inUsed original = ⟨p.up, 8⟩ := by rw [← hi.2]; rfl
  have hsw : ∀ d, d + 8 ≤ 32 → InRegions s.wr (p.stp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨inState original, by rw [h.wr, hi.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      by rw [hst]; exact Offset.contains_base _ hd (by omega)⟩
  have hsw0 : InRegions s.wr p.stp 8 := by simpa only [BitVec.add_zero] using hsw 0 (by decide)
  have huw : InRegions s.wr p.up 8 :=
    ⟨inUsed original, by rw [h.wr, hi.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      by rw [hus]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; decide⟩
  have w0 := h.remaining
  have w1 := h.len
  have w2 := h.cap
  have w3 := h.request
  have w4 := h.savedX19
  have w7 := h.usedPtr
  have w16 := h.used
  have w17 := h.status
  have w18 := h.stp
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at w0 w1 w2 w3 w4 w7 w16 w17 w18
  refine WP.keep finishRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold finish finished SearchInit.written
  brun [ldf, st, h.x19, Nat.mul_zero, Nat.reduceMul, BitVec.add_zero, hl0, hl 8 (by decide),
    hl 16 (by decide), hl 24 (by decide), hl 32 (by decide), hl 56 (by decide), hl 128 (by decide),
    hl 136 (by decide), hl 144 (by decide), w0, w1, w2, w3, w4, w7, w16, w17, w18,
    hsw0, hsw 8 (by decide), hsw 16 (by decide), hsw 24 (by decide), huw]
  simp only [List.getD_cons_zero, List.getD_cons_succ]

theorem finished_bytes {p : SearchPublic} {original : State} (h : SearchInput p original) (m : Mem)
    (r : PrimeSearchResult) : Spec.Rsa.bytesAt (finished p m r) p.op p.len = Spec.Rsa.bytesAt m p.op p.len := by
  have hst : inState original = ⟨p.stp, 32⟩ := by rw [← h.2]; rfl
  have hus : inUsed original = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hot : inOut original = ⟨p.op, p.len⟩ := by rw [← h.2]; rfl
  have hos := h.out_state
  have hou := h.out_used
  rw [hst, hot] at hos
  rw [hus, hot] at hou
  have hn := h.nowrap (r := inOut original) (by simp [inWrites])
  rw [hot] at hn
  have hf : Frame [⟨p.stp, 32⟩, ⟨p.up, 8⟩] m (finished p m r) := by
    unfold finished SearchInit.written
    refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
      (List.mem_cons_self ..) _ ?_) (List.mem_cons_self ..) _ ?_) (List.mem_cons_self ..) _ ?_)
      (List.mem_cons_self ..) _ ?_) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_
    · simpa only [BitVec.add_zero] using Offset.contains_base p.stp (d := 0) (n := 8) (k := 32) (by decide) (by decide)
    · exact Offset.contains_base p.stp (d := 8) (by decide) (by decide)
    · exact Offset.contains_base p.stp (d := 16) (by decide) (by decide)
    · exact Offset.contains_base p.stp (d := 24) (by decide) (by decide)
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; decide
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨p.op, p.len⟩) (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [hos, hou]) (by simp only at hn ⊢; omega) (List.mem_range.mp hi)

theorem finished_used {p : SearchPublic} (m : Mem) (r : PrimeSearchResult) :
    Spec.Rsa.wordsAt (finished p m r) p.up 1 = [BitVec.ofNat 64 r.used] := by
  change [word (finished p m r) p.up 0] = _
  simp only [Bignum.word, off, BitVec.add_zero, finished, Mem.readW_writeW_self64]

theorem finished_state {p : SearchPublic} {original : State} (h : SearchInput p original) (m : Mem)
    (r : PrimeSearchResult) :
    Spec.Rsa.wordsAt (finished p m r) p.stp 4 = [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
      BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 r.requested] := by
  have hst : inState original = ⟨p.stp, 32⟩ := by rw [← h.2]; rfl
  have hus : inUsed original = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hsu := h.state_used
  rw [hst, hus] at hsu
  have hpast (d : Nat) (hd : d + 8 ≤ 32) : word (finished p m r) p.stp d =
      word (SearchInit.written m p.stp [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
        BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 r.requested]) p.stp d :=
    read_past hsu (Offset.contains_base _ hd (by omega))
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; decide)
      (by show 8 ≤ 2 ^ 64; decide) _
  change [word (finished p m r) p.stp 0, word (finished p m r) p.stp 8, word (finished p m r) p.stp 16,
    word (finished p m r) p.stp 24] = _
  rw [hpast 0 (by decide), hpast 8 (by decide), hpast 16 (by decide), hpast 24 (by decide)]
  exact SearchInit.written_words _ _ _ _ _ _

/-! ## The whole search -/

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_initial {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hl : SearchLive p s 0 p.remaining t) : SearchIter p s (searchResult s) 0 p.remaining t := by
  refine ⟨hl, [], ?_⟩
  rw [consume_zero]
  rw [← h.2]
  simp only [searchResult, tailOf, searchOfState, List.drop_zero]

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem iteration_depth (c : Cand) : (iteration c.call).aarch64Depth = 2 := by
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, reject,
    Impl.Bignum.AArch64.countLoop, Code.aarch64Depth, Cand.call, depth_of_noFrames c.noFrames,
    Instr.frameUnits]
  rfl

/-- After the frame saving `x30`: a finished search, with `x30` and the stack
pointer back. -/
theorem SearchDone.popped {p : SearchPublic} {original s : State} {r : PrimeSearchResult}
    (h : SearchDone p original r s) (v sp : BitVec 64) :
    SearchDone p original r { s.write .x .x30 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h19 h30 => ?_, h.vcs, h.savedX19, h.usedPtr, h.stp,
    h.len, h.cap, h.remaining, h.request, h.used, h.status, h.output⟩
  · show (s.write .x .x30 v).gpr .x19 = _
    rw [RegUpd.gpr_write]; exact h.x19
  · show (s.write .x .x30 v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right h30]; exact h.saved reg hr h19 h30

theorem search_body (c : Cand) {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep entryRegs (allocated 160 s) t) :
    WP isa (search c.call) t fun u =>
      SearchDone p s (searchResult s) u ∧ u.gpr .x30 = s.gpr .x30 ∧ u.sp = p.F := by
  have hl := search_start h hx hm k
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hroom : 208 ≤ p.sp.toNat := h.room
  have hF := h.F_toNat
  have hsp : 16 ≤ t.sp.toNat := by rw [htsp, hF]; omega
  unfold search
  refine WP.frameReg hsp ?_ ?_ ?_
  · intro R hR
    rw [k.wr, alloc_wr h] at hR
    rw [htsp]
    rcases List.mem_cons.mp hR with rfl | hR
    · rw [F_16]
      have hs := Offset.sep_below p.sp 208 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
        (Or.inl (by decide)) (by decide) (by decide)
      exact fun x hx hy => hs x (by simp only [Region.Contains] at hx; omega)
        (by simp only [Region.Contains, SearchPublic.F] at hy; omega)
    · rw [h.1.2.2.2.1] at hR
      have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
      refine hd.sub_left ?_
      rw [F_16, h.sp_eq]
      exact Offset.sub_below s.sp (a := 176) (b := 208) (by decide) (by decide)
  · refine WP.mono (search_loop c (search_initial h hl)) fun u hu => ?_
    refine ⟨hu.popped _ _, ?_, htsp⟩
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (Code.loop (iteration c.call) (.zero .x .x9)).aarch64Depth + 16 < 2 ^ 64
    simp only [Code.aarch64Depth, iteration_depth c]
    decide

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  have hroom : 160 ≤ s.sp.toNat := Nat.le_trans (by decide) h.2.1
  unfold code
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (search_body c hp hx hm k) fun u ⟨hd, h30, hsp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨⟨hr, hg, hmq⟩, kq⟩ => ?_
  have hlen : searchLen s = p.len := rfl
  have hst : (searchResult s).status < 4 := by
    unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change ((q.gpr .x0).setWidth 32).toNat = _
    rw [hr, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · change Spec.Rsa.bytesAt q.mem p.op p.len = _
    rw [hmq, finished_bytes hp]
    exact hd.output
  · change Spec.Rsa.wordsAt q.mem p.up 1 = _
    rw [hmq, finished_used]
  · change Spec.Rsa.wordsAt q.mem p.stp 4 = _
    rw [hmq, finished_state hp]
    rfl
  · intro reg hreg
    change q.gpr reg = s.gpr reg
    by_cases h19 : reg = .x19
    · subst h19; exact hg
    · by_cases h30 : reg = .x30
      · subst h30; rw [kq.gpr .x30 (by decide)]; exact h30
      · exact (kq.gpr reg (by revert reg hreg h19 h30; decide)).trans (hd.saved reg hreg h19 h30)
  · change q.sp + BitVec.ofNat 64 160 = s.sp
    rw [kq.sp, hsp]
    show p.sp - _ + _ = _
    rw [BitVec.sub_add_cancel]
    rfl
  · intro r hr
    exact (kq.vcs r hr).trans (hd.vcs r hr)

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Search
