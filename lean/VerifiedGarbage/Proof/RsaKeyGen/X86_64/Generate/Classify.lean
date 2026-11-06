module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.SearchRun
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # The controller's blocks after a search

The octets the search consumed added to the frame's count, and the stores
that start the next prime's search (`nextPrime`) or end the key search
(`finishWith`), each with the frame and the state they leave.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

namespace GenFrame

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

theorem scr (h : GenFrame p original used st s) : Scr s p.F 160 := h.input.frame_scr h.wr

theorem state_region (h : GenFrame p original used st s) : inState original = ⟨p.stp, 56⟩ := by
  rw [← h.input.2]; rfl

theorem used_region (h : GenFrame p original used st s) : inUsed original = ⟨p.up, 8⟩ := by
  rw [← h.input.2]; rfl

theorem stateScr (h : GenFrame p original used st s) : Scr s p.stp 56 := by
  have hn := h.input.nowrap (r := inState original) (by simp [inWrites])
  rw [h.state_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.2.1, ← h.state_region]
  simp [inWrites]

theorem usedScr (h : GenFrame p original used st s) : Scr s p.up 8 := by
  have hn := h.input.nowrap (r := inUsed original) (by simp [inWrites])
  rw [h.used_region] at hn
  refine Scr.of_mem ?_ hn
  rw [h.wr, h.input.1.2.2.2.1, ← h.used_region]
  simp [inWrites]

/-- A header word of the frame. -/
theorem header (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) :
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v := h.headers (j, v) hj

end GenFrame

/-- The frame's headers after the octets consumed are `u`. -/
theorem slots_used {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (u : Nat) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20)
    (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (p.headers u) := by
  have hb' : ∀ e ∈ (8, BitVec.ofNat 64 u) :: values, e.1 < 20 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · show 8 < 20; decide
    · exact hb e he
  have hw (j : Nat) (hj : j < 20) (hj8 : j ≠ 8) (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [writeFrame_word _ _ _ hb' j hj]
    show frameValue values j (if j = 8 then _ else _) = _
    rw [ite_eq_right hj8]
    exact frameValue_unchanged _ _ _ hv
  have hw8 : word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * 8) = BitVec.ofNat 64 u := by
    rw [writeFrame_word _ _ _ hb' 8 (by decide)]
    show frameValue values 8 (if 8 = 8 then _ else _) = _
    rw [ite_eq_left rfl]
    exact frameValue_unchanged _ _ _ fun e he heq => (hnot e he).2.2.2.2.2.2.2.2.1 heq.symm
  have hk (j : Nat) (v : BitVec 64) (hj : j < 20) (hj8 : j ≠ 8) (hjv : (j, v) ∈ p.headers used)
      (hv : ∀ e ∈ values, j ≠ e.1) :
      word (writeFrame s.mem p.F ((8, BitVec.ofNat 64 u) :: values)) p.F (8 * j) = v := by
    have hh := h.headers (j, v) hjv
    dsimp only at hh
    rw [hw j hj hj8 hv]; exact hh
  simp only [Slots, GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨hk 0 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).1 q.symm,
    hk 1 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.1 q.symm,
    hk 2 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.1 q.symm,
    hk 3 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.1 q.symm,
    hk 4 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.1 q.symm,
    hk 5 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q => (hnot e he).2.2.2.2.2.1 q.symm,
    hk 6 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.1 q.symm,
    hk 7 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.1 q.symm,
    hw8,
    hk 11 _ (by decide) (by decide) (by simp [GenPublic.headers]) fun e he => fun q =>
      (hnot e he).2.2.2.2.2.2.2.2.2 q.symm⟩

/-- The status, the octets the search consumed and the count of those
consumed so far. -/
theorem head_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {n status : Nat}
    (hs : ((s.gpr .rax).setWidth 32).toNat = status) (hn : word s.mem p.up 0 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)), .mov .rcx (.mem { base := .rcx }),
      .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx), .store (field 8) .rdx,
      .alu .test .rax (.reg .rax)]) s fun t =>
      (eval .e t = some (decide (status = 0)) ∧ t.gpr .rax = BitVec.ofNat 64 status ∧
        t.gpr .rcx = BitVec.ofNat 64 n ∧
        t.mem = writeFrame s.mem p.F [(8, BitVec.ofNat 64 used + BitVec.ofNat 64 n)]) ∧
      Keep [.rax, .rcx, .rdx] s t := by
  have scr := h.scr
  have hu := h.usedScr
  have h2 := h.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := h.header (j := 8) (v := BitVec.ofNat 64 used) (by simp [GenPublic.headers])
  have hl2 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 16) 8 := scr.ld (d := 16) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 64) 8 := scr.ld (d := 64) (by decide)
  have hs8 : InRegions s.wr (p.F + BitVec.ofNat 64 64) 8 := scr.st (d := 64) (by decide)
  have hlu : InRegions (s.rd ++ s.wr) p.up 8 := by simpa only [off, BitVec.add_zero] using hu.ld (d := 0) (by decide)
  have hn' : s.mem.readW p.up 64 = BitVec.ofNat 64 n := by simpa only [Bignum.word, off, BitVec.add_zero] using hn
  simp only [Nat.reduceMul] at h2 h8
  have hax : ((s.gpr .rax).setWidth 32).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, hs, BitVec.toNat_ofNat]
  have he : (BitVec.ofNat 64 status &&& BitVec.ofNat 64 status == (0 : BitVec 64)) = decide (status = 0) := by
    apply Bool.eq_iff_iff.mpr
    have := ((s.gpr .rax).setWidth 32).isLt
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  refine WP.keep [.rax, .rcx, .rdx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl2, hl8, hs8, hlu, h2, h8, hn', hax, eval, he]

/-! ## Stores to the state and the frame -/

/-- The state's words `0`, `4` and `5` and the frame's status or region to
zero stored. -/
def StateStores (sv fv : List (Nat × BitVec 64)) : Prop :=
  (∀ e ∈ sv, e.1 = 0 ∨ e.1 = 4 ∨ e.1 = 5) ∧ (∀ e ∈ fv, e.1 = 10 ∨ e.1 = 12 ∨ e.1 = 13)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem state_frame (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.stp, 56⟩ := h.input.frame_state

/-- What stores to the state's first six words and to the frame keep: the
memory outside them. -/
theorem _root_.VG.Proof.RsaKeyGen.X86_64.Generate.stores_frame (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) :
    Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame (writeFrame m p.stp sv) p.F fv) := by
  have h1 : Frame [⟨p.stp, 48⟩, p.frame] m (writeFrame m p.stp sv) :=
    (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  have h2 : Frame [⟨p.stp, 48⟩, p.frame] (writeFrame m p.stp sv) (writeFrame (writeFrame m p.stp sv) p.F fv) :=
    (writeFrame_frame _ _ fv fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide).sub
      fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp, fun _ h => h⟩
  exact h1.trans h2

theorem stores_changes (h : GenFrame p original used st s) :
    ∀ r ∈ [(⟨p.stp, 48⟩ : Region), p.frame], ∃ q ∈ GenInput.changes original, Region.Sub r q := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨inState original, by simp [GenInput.changes, inWrites], by
      rw [h.state_region]; exact Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩

/-- A region apart from the state's first six words and the frame is kept. -/
theorem _root_.VG.Proof.RsaKeyGen.X86_64.Generate.stores_bytes (p : GenPublic) (m : Mem)
    {sv fv : List (Nat × BitVec 64)} (hv : StateStores sv fv) {R : Region} (hs : (⟨p.stp, 48⟩ : Region).Disjoint R) (hf : p.frame.Disjoint R)
    (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (writeFrame (writeFrame m p.stp sv) p.F fv) R.base R.len =
      Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine (stores_frame p m hv).bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [hs.symm, hf.symm]

/-- Through stores to the state's words `0`, `4` and `5` and to the frame's
status or region to zero, for the progress `st'` those words hold. -/
theorem setState (h : GenFrame p original used st s) {st' : KeyProgress} {sv fv : List (Nat × BitVec 64)}
    (hv : StateStores sv fv) (hm : t.mem = writeFrame (writeFrame s.mem p.stp sv) p.F fv)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (h0 : frameValue sv 0 (word s.mem p.stp (8 * 0)) = BitVec.ofNat 64 st'.remaining)
    (h4 : frameValue sv 4 (word s.mem p.stp (8 * 4)) = BitVec.ofNat 64 (phaseWord st'.phase))
    (h5 : frameValue sv 5 (word s.mem p.stp (8 * 5)) = BitVec.ofNat 64 st'.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) (hlt : st'.left < 2 ^ 64) :
    GenFrame p original used st' t := by
  have hsb : ∀ e ∈ sv, e.1 < 20 := fun e he => by rcases hv.1 e he with h | h | h <;> rw [h] <;> decide
  have hfb : ∀ e ∈ fv, e.1 < 20 := fun e he => by rcases hv.2 e he with h | h | h <;> rw [h] <;> decide
  have hsd := h.state_frame
  have hnst : p.stp.toNat + 56 ≤ 2 ^ 64 := by
    have := h.input.nowrap (r := inState original) (by simp [inWrites])
    rwa [h.state_region] at this
  -- The frame's words through the state's stores.
  have hF (j : Nat) (hj : j < 20) (hnot : ∀ e ∈ fv, j ≠ e.1) :
      word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    rw [hm, writeFrame_word _ _ _ hfb j hj, frameValue_unchanged _ _ _ hnot]
    refine (Search.writeFrame_frame_size _ _ sv (size := 48) (by decide) fun e he => by
      rcases hv.1 e he with h | h | h <;> rw [h] <;> decide).readW (r := p.frame)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => ?_) (by decide)
    obtain rfl := List.mem_singleton.mp hq
    exact hsd.sub_right (Region.sub_prefix (by decide))
  -- The state's words through the frame's stores.
  have hS (j : Nat) (hj : j < 7) :
      word t.mem p.stp (8 * j) = frameValue sv j (word s.mem p.stp (8 * j)) := by
    rw [hm, ← writeFrame_word _ _ _ hsb j (by omega)]
    exact (writeFrame_frame _ _ fv hfb).readW (r := ⟨p.stp, 56⟩)
      (Offset.contains_base _ (by omega) (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsd.symm) (by decide)
  have hnf : ∀ j, j ≠ 10 → j ≠ 12 → j ≠ 13 → ∀ e ∈ fv, j ≠ e.1 := fun j h10 h12 h13 e he heq => by
    rcases hv.2 e he with h | h | h <;> omega
  have hns : ∀ j, j ≠ 0 → j ≠ 4 → j ≠ 5 → ∀ e ∈ sv, j ≠ e.1 := fun j h0 h4 h5 e he heq => by
    rcases hv.1 e he with h | h | h <;> omega
  have hfr : Frame (GenInput.changes original) s.mem t.mem := by
    rw [hm]; exact (stores_frame p s.mem hv).sub h.stores_changes
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun reg hreg hne hsp => (hg reg hreg).trans (h.saved reg hreg hne hsp),
    ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, hrem, hlt⟩⟩
  · exact (hF 9 (by decide) (hnf 9 (by decide) (by decide) (by decide))).trans h.savedR12
  · exact (h.input.random_frame hfr).trans h.random
  · intro e he
    have hj := GenPublic.headers_bound _ _ e he
    rw [hF e.1 hj (hnf _ ?_ ?_ ?_)]
    · exact h.headers e he
    all_goals
      simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · have := hS 0 (by decide); rw [h0] at this; exact this
  · have := hS 1 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 1 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.len
  · have := hS 2 (by decide)
    rw [frameValue_unchanged _ _ _ (hns 2 (by decide) (by decide) (by decide))] at this
    exact this.trans h.state.cap
  · have := hS 4 (by decide); rw [h4] at this; exact this
  · have := hS 5 (by decide); rw [h5] at this; exact this
  · rw [← h.state.e, hm]
    refine stores_bytes p s.mem (R := ⟨p.stp + 48, 8⟩) hv ?_ ?_ (by show 8 ≤ 2 ^ 64; decide)
    · intro x hx hy
      exact Offset.sep p.stp (d := 0) (n := 48) (e := 48) (k := 8) (.inl (by omega)) (by omega) (by omega) x
        (by rw [BitVec.add_zero]; simp only [Region.Contains] at hx; omega)
        (by
          have e48 : (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 := rfl
          simp only [Region.Contains, e48] at hy; omega)
    · exact hsd.sub_right (Offset.sub_base _ (by decide))

end GenFrame

/-! ## The blocks -/

theorem imm32_ofNat {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section

variable {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}

/-- The next prime's search, in `phase`: all its counted candidates, and the
status that goes on. -/
theorem nextPrime_ok (h : GenFrame p original used st s) {phase : Nat} (hph : phase < 2) :
    WP isa (.block (nextPrime phase)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(0, BitVec.ofNat 64 (limitOf p.L p.eB)),
        (4, BitVec.ofNat 64 phase)]) p.F [(10, (4 : BitVec 64))] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have h11 := h.header (j := 11) (v := BitVec.ofNat 64 (limitOf p.L p.eB)) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl11 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 88) 8 := scr.ld (d := 88) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs0 : InRegions s.wr p.stp 8 := by simpa only [off, BitVec.add_zero] using sst.st (d := 0) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  simp only [Nat.reduceMul] at h7 h11
  have hi := imm32_ofNat (n := phase) (by omega)
  have h4 : (4 : BitVec 32).setWidth 64 = (4 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame nextPrime
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl11, hs10, hs0, hs4, h7, h11, hi, h4]

/-- The end of the key search with `status`: no phase or generations left. -/
theorem finishWith_ok (h : GenFrame p original used st s) {status : Nat} (hs : status < 4) :
    WP isa (.block (finishWith status)) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp [(4, (0 : BitVec 64)), (5, (0 : BitVec 64))]) p.F
        [(10, BitVec.ofNat 64 status)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := scr.st (d := 80) (by decide)
  have hs4 : InRegions s.wr (p.stp + BitVec.ofNat 64 32) 8 := sst.st (d := 32) (by decide)
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  simp only [Nat.reduceMul] at h7
  have hi := imm32_ofNat (n := status) (by omega)
  have h0 : (0 : BitVec 32).setWidth 64 = (0 : BitVec 64) := by decide
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame finishWith
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hs10, hs4, hs5, h7, hi, h0]

/-- The status, stored. -/
theorem storeStatus_ok (h : GenFrame p original used st s) {status : Nat}
    (hs : s.gpr .rax = BitVec.ofNat 64 status) :
    WP isa (.block [.store (field 10) .rax]) s fun t =>
      t.mem = writeFrame (writeFrame s.mem p.stp []) p.F [(10, BitVec.ofNat 64 status)] ∧ Keep [] s t := by
  have hs10 : InRegions s.wr (p.F + BitVec.ofNat 64 80) 8 := h.scr.st (d := 80) (by decide)
  refine WP.keep [] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, h.r12, hs10, hs]

/-- The generations left, compared with 2. -/
theorem left_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 5)), .alu .cmp .rcx (.imm 2)]) s fun t =>
      (eval .b t = some (decide (st.left < 2)) ∧ t.gpr .rax = p.stp ∧ t.gpr .rcx = BitVec.ofNat 64 st.left ∧
        t.mem = s.mem) ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl5 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 40) 8 := sst.ld (d := 40) (by decide)
  have h5 : s.mem.readW (p.stp + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 st.left := h.state.left
  simp only [Nat.reduceMul] at h7
  have hlt := h.state.left_lt
  have hb : decide ((BitVec.ofNat 64 st.left).toNat < BitVec.toNat (2 : BitVec 64)) = decide (st.left < 2) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rfl
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl5, h7, h5, eval, hb]

/-- The phase, tested. -/
theorem phase_ok (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 7)), .mov .rcx (.mem (stw 4)), .alu .test .rcx (.reg .rcx)]) s fun t =>
      (eval .e t = some (decide (phaseWord st.phase = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax, .rcx] s t := by
  have scr := h.scr
  have sst := h.stateScr
  have h7 := h.header (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  have hl7 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 56) 8 := scr.ld (d := 56) (by decide)
  have hl4 : InRegions (s.rd ++ s.wr) (p.stp + BitVec.ofNat 64 32) 8 := sst.ld (d := 32) (by decide)
  have h4 : s.mem.readW (p.stp + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 (phaseWord st.phase) := h.state.phase
  simp only [Nat.reduceMul] at h7
  have he : (BitVec.ofNat 64 (phaseWord st.phase) &&& BitVec.ofNat 64 (phaseWord st.phase) == (0 : BitVec 64)) =
      decide (phaseWord st.phase = 0) := by
    have := phaseWord_le st.phase
    apply Bool.eq_iff_iff.mpr
    simp only [BitVec.and_self, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl7, hl4, h7, h4, eval, he]

end

end VG.Proof.RsaKeyGen.X86_64.Generate
