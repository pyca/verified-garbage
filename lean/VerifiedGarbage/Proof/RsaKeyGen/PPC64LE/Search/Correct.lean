module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with the constant-time ones, `CT`

/-! # The search's results, and the whole search's correctness (PPC64LE) -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Search
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
abbrev finishRegs : List Reg := [.r3, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r31]

theorem search_finish {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    (h : SearchDone p original final s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 final.status ∧ t.gpr .r31 = original.gpr .r31 ∧
        t.mem = finished p s.mem final) ∧ Keep finishRegs s t := by
  have hi := h.input
  have scr := hi.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hst : inState original = ⟨p.stp, 32⟩ := by rw [← hi.2]; rfl
  have hus : inUsed original = ⟨p.up, 8⟩ := by rw [← hi.2]; rfl
  have hsw : ∀ d, d + 8 ≤ 32 → InRegions s.wr (p.stp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨inState original, by rw [h.wr, hi.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      by rw [hst]; exact Offset.contains_base _ hd (by omega)⟩
  have huw : InRegions s.wr (p.up + BitVec.ofNat 64 0) 8 :=
    ⟨inUsed original, by rw [h.wr, hi.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites]),
      by rw [hus]; exact Offset.contains_base _ (by decide) (by decide)⟩
  have w0 := h.remaining
  have w1 := h.len
  have w2 := h.cap
  have w3 := h.request
  have w4 := h.savedR31
  have w7 := h.usedPtr
  have w16 := h.used
  have w17 := h.status
  have w18 := h.stp
  simp only [Bignum.word, off, Nat.reduceMul] at w0 w1 w2 w3 w4 w7 w16 w17 w18
  refine WP.keep finishRegs ?_ (by decide)
  unfold finish finished SearchInit.written
  prun [ldf, h.r31, hl 0 (by decide), hl 8 (by decide), hl 16 (by decide), hl 24 (by decide),
    hl 32 (by decide), hl 56 (by decide), hl 128 (by decide), hl 136 (by decide), hl 144 (by decide),
    w0, w1, w2, w3, w4, w7, w16, w17, w18, hsw 0 (by decide), hsw 8 (by decide), hsw 16 (by decide),
    hsw 24 (by decide), huw, off]
  simp only [List.getD_cons_zero, List.getD_cons_succ, BitVec.add_zero]

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

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  have hroom : 192 ≤ s.sp.toNat := alloc_room h.1.2.1
  unfold code
  refine WP.alloc (by decide) hroom ?_
  refine WP.seq (VG.PPC64LE.WP.mono_syms (entrySave_ok hp) fun u ⟨⟨hx, hmu⟩, ku⟩ hyu => ?_)
  refine WP.seq (VG.PPC64LE.WP.mono_syms (entryLoad_ok hp hx hmu ku) fun t ⟨hmt, kt⟩ hyt => ?_)
  have hx' : t.gpr .r31 = p.F := (kt.gpr .r31 (by decide)).trans hx
  have hm : t.mem = writeFrame (allocated 192 s).mem p.F (entryValues s) := by
    rw [hmt, hmu, entryValues, writeFrame_append]
  refine WP.seq (WP.mono (search_body c hp hx' hm (ku.trans kt) (hyt.trans hyu)) fun u ⟨hd, hlr, hsp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨⟨hr, hg, hmq⟩, kq⟩ => ?_
  have hst : (searchResult s).status < 4 := by
    unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change ((q.gpr .r3).setWidth 32).toNat = _
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
    by_cases h31 : reg = .r31
    · subst h31; exact hg
    · exact (kq.gpr reg (by revert reg hreg h31; decide)).trans (hd.saved reg hreg h31)
  · change q.sp + BitVec.ofNat 64 192 = s.sp
    rw [kq.sp, hsp, BitVec.sub_add_cancel]
  · change q.lr = s.lr
    rw [kq.lr, hlr]

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.PPC64LE.Search
