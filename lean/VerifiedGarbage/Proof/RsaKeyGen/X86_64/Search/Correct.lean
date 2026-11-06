module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SearchInit

/-! # The search's results, and the whole search's correctness, stack and calling convention -/

-- separate module: its proofs build in parallel with the constant-time ones, `CT`

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search
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
    BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 (requested p.len r)]).writeW p.up (BitVec.ofNat 64 r.used)

theorem search_finish {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    (h : SearchDone p original final s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 final.status ∧ t.gpr .r12 = original.gpr .r12 ∧
        t.mem = finished p s.mem final) ∧ Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12] s t := by
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
  have w4 := h.savedR12
  have w7 := h.usedPtr
  have w16 := h.used
  have w17 := h.status
  have w18 := h.stp
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at w0 w1 w2 w3 w4 w7 w16 w17 w18
  refine WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12] ?_ rfl
  unfold finish finished SearchInit.written
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), hl 16 (by decide), hl 24 (by decide), hl 32 (by decide), hl 56 (by decide),
    hl 128 (by decide), hl 136 (by decide), hl 144 (by decide), w0, w1, w2, w3, w4, w7, w16, w17, w18,
    hsw0, hsw 8 (by decide), hsw 16 (by decide), hsw 24 (by decide), huw]
  rfl

/-! ## The whole search -/

open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg freed freed_rsp freed_reg frame_alloc)

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_initial {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hl : SearchLive p s 0 p.remaining t) : SearchIter p s (searchResult s) 0 p.remaining t := by
  refine ⟨hl, [], ?_⟩
  rw [consume_zero]
  rw [← h.2]
  simp only [searchResult, tailOf, searchOfState, List.drop_zero]

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
      BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 (requested p.len r)] := by
  have hst : inState original = ⟨p.stp, 32⟩ := by rw [← h.2]; rfl
  have hus : inUsed original = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hsu := h.state_used
  rw [hst, hus] at hsu
  have hpast (d : Nat) (hd : d + 8 ≤ 32) : word (finished p m r) p.stp d =
      word (SearchInit.written m p.stp [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
        BitVec.ofNat 64 (primeEntropy p.len), BitVec.ofNat 64 (requested p.len r)]) p.stp d :=
    read_past hsu (Offset.contains_base _ hd (by omega))
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; decide)
      (by show 8 ≤ 2 ^ 64; decide) _
  change [word (finished p m r) p.stp 0, word (finished p m r) p.stp 8, word (finished p m r) p.stp 16,
    word (finished p m r) p.stp 24] = _
  rw [hpast 0 (by decide), hpast 8 (by decide), hpast 16 (by decide), hpast 24 (by decide)]
  exact SearchInit.written_words _ _ _ _ _ _

theorem search_correct_ok (v : RoundImpl) {s : State} (h : searchPre s) :
    WP isa (searchCode v) s fun t => searchPost s t ∧ ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  have hi : SearchInput (searchOfState s) s := ⟨h, rfl⟩
  have hroom : 160 ≤ (s.gpr .rsp).toNat := Nat.le_trans (by decide) h.2.1
  unfold searchCode code
  apply frame_alloc (by decide) (by decide) (by decide) hroom
  change WP isa (.seq _ (.seq _ _)) _ _
  refine WP.seq (WP.mono (search_start hi) fun u hu => ?_)
  refine WP.seq (WP.mono (search_loop v (search_initial hi hu)) fun w hw => ?_)
  refine WP.mono (search_finish hw) fun t ⟨⟨hra, hr12, hm⟩, kt⟩ => ?_
  have hsp : t.gpr .rsp = (allocated 160 s).gpr .rsp := by
    rw [kt.gpr (by decide), hw.rsp, alloc_rsp hi]
  refine ⟨hsp, kt.2.2.trans (hw.wr.trans (alloc_wr hi).symm), ?_, ?_⟩
  · -- The results.
    have hlen : searchLen s = (searchOfState s).len := rfl
    have hst : (searchResult s).status < 4 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [freed_reg _ _ _ (by decide), hra, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    · change Spec.Rsa.bytesAt t.mem (searchOfState s).op (searchOfState s).len = _
      rw [hm, finished_bytes hi]
      exact hw.output
    · change Spec.Rsa.wordsAt t.mem (searchOfState s).up 1 = _
      rw [hm, finished_used]
    · refine ⟨_, ?_, Search.search_requests (searchLen s) (searchE s) (searchP s)
        (searchRemaining s) (searchRand s)⟩
      change Spec.Rsa.wordsAt t.mem (searchOfState s).stp 4 = _
      rw [hm, finished_state hi]
      rfl
  · -- The callee-saved registers.
    intro r hr
    by_cases hs : r = .rsp
    · subst hs
      rw [freed_rsp, hsp, allocated_rsp]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ hs]
      by_cases h12 : r = .r12
      · subst h12; exact hr12
      · rw [kt.gpr (by revert r; decide)]
        exact hw.saved r hr h12 hs

/-! ## The instructions, the stack and the calling convention -/

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_instrs (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).allInstrs p = true) (hc : c.allInstrs p = true) :
    (code c).allInstrs p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.allInstrs, hc, Bool.and_true] at hp ⊢
  exact hp

theorem candidateCall_sp (v : RoundImpl) : (candidateCall v).all (fun i => !isa.writesSp i) = true :=
  sharedCandidate_sp v

theorem searchCode_sp (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true :=
  controller_all _ _ (by decide +kernel) (candidateCall_sp v)

theorem searchCode_mx (v : RoundImpl) : (searchCode v).allInstrs (fun i => !loadsMxcsr i) = true :=
  controller_instrs _ _ (by decide +kernel) (sharedCandidate_mx v)

theorem searchCode_depth (v : RoundImpl) : (searchCode v).x86_64Depth ≤ stackUse := by
  have hc := sharedCandidate_depth v
  have he : exhausted.x86_64Depth = 0 := rfl
  have hk : classify.x86_64Depth = 0 := rfl
  unfold searchCode code iteration candidateRun candidateCall
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.x86_64Depth, Instr.frameBytes, he, hk, Nat.zero_max,
    Nat.max_zero, stackUse, frameBytes]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hc 8) 40) 160

theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨-, -, -, hwr, -, -, -, hstk, -⟩ := h
  have hd : (searchCode v).x86_64Depth ≤ 336 := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega)
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    exact (hstk r (List.mem_append_left _ hr)).1
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega)

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_exec (searchCode_mx v) he ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.RsaKeyGen.X86_64.Search
