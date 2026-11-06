module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.SearchCall
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The prime search, run

`searchRun`: in a frame of its stack arguments, the search's arguments and its
call. It leaves the search's status, its prime or zeros at its output, the
octets it consumed at `used`, and its counted candidates left and request in
the state; it writes nothing else but the working space and the stack.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf)

/-- The prime search, as the controller calls it. -/
def searchCall (v : RoundImpl) : Prog isa :=
  .call ("vg_rsa_prime_search" ++ v.suffix) (Search.searchCode v)

/-- What the search may write, as the controller sees it. -/
def searchChanges (p : GenPublic) (st : KeyProgress) : List Region :=
  [rO p st, rU p, rS p, rT p, ⟨p.sp - BitVec.ofNat 64 552, 392⟩]

/-- What the search of the progress' prime at `used` leaves. -/
structure AfterSearch (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress)
    (s t : State) : Prop where
  frame : GenFrame p original used ⟨st.left, st.phase, (primeOf p.L p.eB st ((genRand original).drop used)).remaining⟩ t
  status : ((t.gpr .rax).setWidth 32).toNat = (primeOf p.L p.eB st ((genRand original).drop used)).status
  usedw : word t.mem p.up 0 = BitVec.ofNat 64 (primeOf p.L p.eB st ((genRand original).drop used)).used
  out : Spec.Rsa.bytesAt t.mem (outOf p st) p.L =
    (match (primeOf p.L p.eB st ((genRand original).drop used)).outcome with
      | .accepted c => Spec.Rsa.i2osp c p.L
      | _ => List.replicate p.L 0)
  req : ∃ requested, word t.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (primeOf p.L p.eB st ((genRand original).drop used)).Requests (primeEntropy p.L) requested
  mem : Frame (searchChanges p st) s.mem t.mem

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem GenLive.regions (h : GenLive p original used st s) :
    inKey original = ⟨p.kp, 9 * p.L⟩ ∧ inUsed original = rU p ∧ inScr original = rS p ∧
      inState original = cS p ∧ inRand original = cR p := by
  refine ⟨h.key_region, ?_, ?_, ?_, ?_⟩ <;> rw [← h.input.2] <;> rfl

theorem search_covers_writes (h : GenLive p original used st s) {u : State}
    (hw : u.wr = (allocated 48 s).wr) : Covers (sWrites p st) u.wr := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, ht, -⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  rw [hk, hu, hs, ht] at hwo
  rw [hw]
  refine Covers.of_sub fun r hr => ?_
  have hin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), rU p, rS p, cS p], q ∈ (allocated 48 s).wr := by
    intro q hq
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hL := hf.len.1
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨⟨p.kp, 9 * p.L⟩, hin _ (by simp), if phaseWord st.phase = 0 then 4 * p.L else 5 * p.L, ?_, ?_⟩
    · simp only [outOf]; split <;> rfl
    · show _ + p.L ≤ 9 * p.L
      split <;> omega
  · exact ⟨rU p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨rS p, hin _ (by simp), 0, by simp, by simp⟩
  · exact ⟨cS p, hin _ (by simp), 0, by simp, by simp⟩

theorem search_covers_reads (h : GenLive p original used st s) {u : State}
    (hrd : u.rd = (allocated 48 s).rd) (hw : u.wr = (allocated 48 s).wr) :
    Covers (sReads p used st ++ sWrites p st) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (search_covers_writes h hw).right
  have hf := h.input.cfacts
  obtain ⟨hk, -, -, ht, hr⟩ := h.regions
  have hwo : original.wr = [inKey original, inUsed original, inScr original, inState original] :=
    h.input.1.2.2.2.1
  have hro : original.rd = [inRand original, inArgs original] := h.input.1.2.2.1
  rw [hk, ht] at hwo
  rw [hr] at hro
  have hul := h.used_le
  have hL := hf.len.1
  rw [hrd, hw]
  refine Covers.of_sub fun r hr' => ?_
  simp only [sReads, List.mem_cons, List.not_mem_nil, or_false] at hr'
  have hwin : ∀ q ∈ [(⟨p.kp, 9 * p.L⟩ : Region), cS p], q ∈ (allocated 48 s).rd ++ (allocated 48 s).wr := by
    intro q hq
    refine List.mem_append_right _ ?_
    show q ∈ _ :: s.wr
    rw [h.wr, hwo]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with rfl | rfl <;> simp
  rcases hr' with rfl | rfl | rfl | rfl
  · exact ⟨cS p, hwin _ (by simp), 48, rfl, by simp⟩
  · exact ⟨⟨p.kp, 9 * p.L⟩, hwin _ (by simp), 4 * p.L, rfl, by
      show _ + plenOf p st ≤ 9 * p.L; have := plen_le (p := p) (st := st); omega⟩
  · refine ⟨cR p, List.mem_append_left _ ?_, used, rfl, by simp; omega⟩
    show cR p ∈ s.rd
    rw [h.rd, hro]; simp
  · refine ⟨⟨s.gpr .rsp - BitVec.ofNat 64 48, 48⟩, List.mem_append_right _ (List.mem_cons_self ..), 0, ?_, by simp⟩
    rw [h.rsp, F_48, BitVec.add_zero]

end

/-- The search's result, from the controller's loop state. -/
theorem callS_result {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s)
    (hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208) (ha : SearchRegs p st u)
    (hm : u.mem = writeFrame s.mem (p.F - BitVec.ofNat 64 48) (callValues p used st)) :
    Search.searchResult (callS p used st u) = primeOf p.L p.eB st ((genRand original).drop used) := by
  have hf := h.input.cfacts
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  have hfr := callS_frame hu hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, sR⟩ := hst
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hL := hf.len
  obtain ⟨hL1, hL2, -⟩ := hL
  have tl : (BitVec.ofNat 64 p.L).toNat = p.L := toNat_ofNat_lt (by omega)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p) ∨ Region.Sub R (cR p))
      (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt (callS p used st u).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun r hr => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hr
    rcases hR with hR | hR | hR
    exacts [sK.sub_left hR, sT.sub_left hR, sR.sub_left hR]
  have hlim : st.remaining < 2 ^ 64 := by
    have := h.state.remaining_le
    unfold KeySearch.limitOf primeLimit at this
    split at this <;> omega
  unfold Search.searchResult
  congr 1
  · simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), hsi, tl]
  · simp only [Search.searchE, callS_gpr (show Reg.rcx ≠ .rsp by decide), callS_gpr (show Reg.r8 ≠ .rsp by decide),
      hcx, h8, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    exact hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr (.inl rE_sub)) (by show 8 ≤ 2 ^ 64; decide)
  · simp only [Search.searchP, callS_gpr (show Reg.r9 ≠ .rsp by decide), h9, a0,
      toNat_ofNat_lt (show plenOf p st < 2 ^ 64 by have := plen_le (p := p) (st := st); omega)]
    have hk := h.key.other
    unfold plenOf
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => simp [phaseWord, KeyPhase.other, Spec.Rsa.bytesAt]
    | q pB =>
      simp only [phaseWord, Nat.one_ne_zero, ↓reduceIte, KeyPhase.other]
      rw [← hk pB rfl]
      exact hbytes (R := ⟨p.slot 4, p.L⟩) (.inl (slot_sub _ (by omega))) (by show p.L ≤ 2 ^ 64; omega)
  · simp only [Search.searchRemaining, a5]
    have h0 := h.state.remaining
    simp only [Bignum.word, off, BitVec.add_zero] at h0
    have := hfr.readW (r := cS p) (a := p.stp) (w := 64)
      (by simpa only [BitVec.add_zero] using Offset.contains_base p.stp (d := 0) (n := 8) (k := 56) (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sT) (by decide)
    rw [this, h0, toNat_ofNat_lt hlim]
  · simp only [Search.searchRand, a1, a2, toNat_ofNat_lt (show p.randLen - used < 2 ^ 64 by have := hf.rand64; omega)]
    have := hbytes (R := rR p used) (.inr (.inr (rR_sub h.used_le))) (by have := hf.rand64; simp; omega)
    simp only at this
    rw [this, Search.bytesAt_drop, h.random]

theorem stack_mem (p : GenPublic) (st : KeyProgress) :
    (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) ∈ searchChanges p st := by
  simp [searchChanges]

theorem below_sub (sp : Addr) {n : Nat} (hn : n ≤ 344) :
    Region.Sub (below (sp - BitVec.ofNat 64 208) n) ⟨sp - BitVec.ofNat 64 552, 392⟩ := by
  simp only [below, BitVec.sub_sub]
  rw [← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem searchChanges_sub {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    ∀ r ∈ searchChanges p st, ∃ q ∈ GenInput.callChanges original, Region.Sub r q := by
  have hf := h.input.cfacts
  obtain ⟨hk, hu, hs, -, -⟩ := h.regions
  have hT : (⟨stackArg original 1, 32⟩ : Region) = rT p := by rw [← h.input.2]; rfl
  have hS : (⟨original.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩ : Region) =
      ⟨p.sp - BitVec.ofNat 64 552, 392⟩ := by rw [← h.input.2]; rfl
  intro r hr
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [GenInput.callChanges, hk, hu, hs, hT, hS]
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., rO_sub hf⟩
  all_goals exact ⟨_, by simp, fun _ h => h⟩

theorem search_run (v : RoundImpl) {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) :
    WP isa (searchRun (searchCall v)) s (AfterSearch p original used st s) := by
  have hf := h.input.cfacts
  have hF := h.input.F_toNat
  have hroom := h.input.room
  unfold searchRun searchCall
  apply frame_alloc (by decide) (by decide) (by decide) (by rw [h.rsp, hF]; have : 552 ≤ p.sp.toNat := hroom; omega)
  refine WP.seq (WP.mono (search_args_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - BitVec.ofNat 64 208 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp, F_48]
  have hd : (Search.searchCode v).x86_64Depth ≤ 336 := Search.searchCode_depth v
  refine WP.callF (k := Search.searchContract) (Search.search_correct v) (SpSafe.of_all (Search.searchCode_sp v))
    (by omega) (callS_pre h hu ha hm) (search_covers_reads h k.2.1 k.2.2) (search_covers_writes h k.2.2)
    fun t htr htw hg hfr ⟨s₂, hm₂, hg₂, hpost⟩ _ => ?_
  have hres := callS_result h hu ha hm
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  have hlen : Search.searchLen (callS p used st u) = p.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.rsi ≠ .rsp by decide), hsi]
    exact toNat_ofNat_lt (by have := hf.len.2.1; omega)
  obtain ⟨hst, hout, hused, req, hwords, hreq⟩ := hpost
  have hdi' : (callS p used st u).gpr .rdi = outOf p st := by rw [callS_gpr (by decide)]; exact hdi
  have hdx' : (callS p used st u).gpr .rdx = p.up := by rw [callS_gpr (by decide)]; exact hdx
  simp only [hres, hlen, hm₂, a5, hdi', hdx'] at hst hout hused hwords hreq
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, show List.range 1 = [0] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hwords hused
  simp only [Nat.reduceMul] at hwords hused
  obtain ⟨w0, w1, w2, w3⟩ := hwords
  -- The memory: the stack arguments, then the search.
  have f₀ : Frame (searchChanges p st) s.mem u.mem := by
    rw [hm, F_48]
    apply (Search.writeFrame_frame_size _ _ (callValues p used st) (size := 48) (by decide) (by
      simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide)).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, stack_mem p st, Offset.sub_below _ (by decide) (by decide)⟩
  have f₁ : Frame (searchChanges p st) u.mem t.mem := by
    refine hfr.sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · refine ⟨r, ?_, fun _ h => h⟩
      simp only [sWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, stack_mem p st, by rw [hu]; exact below_sub _ (by omega)⟩
  have hframe := f₀.trans f₁
  have hrem := KeySearch.primeSearch_remaining_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
  have hle := h.state.remaining_le
  have htsp : t.gpr .rsp = (allocated 48 s).gpr .rsp := by rw [hg _ (by decide), k.gpr (by decide)]
  refine ⟨htsp, htw.trans k.2.2, h.toGenFrame.restore (htr.trans k.2.1) (show t.wr.tail = s.wr by rw [htw, k.2.2]; rfl)
      (fun r hr => ?_) (hframe.sub (searchChanges_sub h)) ?_ w1 w2 (.inl rfl) rfl (Nat.le_trans hrem hle), ?_, ?_, ?_,
      ⟨req, ?_, hreq⟩, hframe⟩
  · have hnot : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] := by revert r; decide
    by_cases he : r = .rsp
    · subst he
      rw [freed_rsp, htsp, allocated_rsp]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ he, hg r hr, k.gpr hnot, allocated_reg _ _ _ he]
  · exact w0
  · rw [freed_reg _ _ _ (by decide), ← hg₂ _ (by decide)]; exact hst
  · exact hused
  · exact hout
  · exact w3

end VG.Proof.RsaKeyGen.X86_64.Generate
