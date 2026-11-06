module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Restore
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.InitWords

/-! # Zeros in the key's buffer

`clear` writes zeros to the region in frame words 12 and 13, which is in the
key's buffer: the frame, the state and everything else is kept.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.Rsa.X86_64 (OutOk)

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

theorem key_region (h : GenFrame p original used st s) : inKey original = ⟨p.kp, 9 * p.L⟩ := by
  have := h.input.1.2.2.2.2.2.2.2.2.2.1
  rw [← h.input.2]
  simp only [inKey, genOfState, this]

theorem key_state (h : GenFrame p original used st s) : (inKey original).Disjoint (inState original) := by
  have hpw := h.input.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  exact hpw.1.2.2

/-- Through a step that changes only the key's buffer. -/
theorem restoreKey (h : GenFrame p original used st s)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame [inKey original] s.mem t.mem) : GenFrame p original used st t := by
  have hst : inState original = ⟨p.stp, 56⟩ := by rw [← h.input.2]; rfl
  have hd := h.key_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word t.mem p.stp d = word s.mem p.stp d :=
    hf.readW (r := inState original) (by rw [hst]; exact Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine h.restore hr hw hg (hf.sub fun r hr => ?_) ?_ ?_ ?_ (.inl rfl) rfl h.state.remaining_le
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩
  · rw [hword 0 (by decide)]; exact h.state.remaining
  · rw [hword 8 (by decide)]; exact h.state.len
  · rw [hword 16 (by decide)]; exact h.state.cap

theorem outOk (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (hn : op.toNat + len ≤ 2 ^ 64) :
    OutOk s p.F 160 op len := by
  have hin : inKey original ∈ s.wr := by
    rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
  have hd := h.input.frame_disjoint_writes (r := inKey original) (by simp [inWrites])
  refine ⟨fun i hi => ⟨_, hin, hsub _ (contains_byte _ hi (by omega))⟩, fun i hi => Nat.le_of_not_lt fun hlt =>
    hd _ (by simp only [ofs] at hlt; simp only [Region.Contains]; omega)
      (hsub _ (contains_byte _ hi (by omega)))⟩

end GenFrame

/-- `clear`: zeros at the region in frame words 12 and 13. -/
theorem clear_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {op : Addr} {len : Nat}
    (h12 : word s.mem p.F (8 * 12) = op) (h13 : word s.mem p.F (8 * 13) = BitVec.ofNat 64 len)
    (hsub : Region.Sub ⟨op, len⟩ (inKey original)) (hn : op.toNat + len ≤ 2 ^ 64) (h1 : 1 ≤ len)
    (hlt : len < 2 ^ 31) :
    WP isa clear s fun t => GenFrame p original used st t ∧ (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      Frame [⟨op, len⟩] s.mem t.mem ∧ (∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j)) ∧
      Keep [.rdi, .rsi, .rcx, .rax] s t := by
  unfold clear
  refine WP.seq (WP.mono (WP.keep [.rdi] (Q := fun u => u.gpr .rdi = p.F ∧ u.mem = s.mem) (by xrun [h.r12]) rfl)
    fun u ⟨⟨hdi, hm⟩, ku⟩ => ?_)
  have hu : GenFrame p original used st u :=
    h.restoreKey ku.2.1 ku.2.2 (fun r hr => ku.gpr (by revert r; decide)) (by rw [hm]; exact Frame.refl _ _)
  have scr := h.input.frame_scr (ku.2.2.trans h.wr)
  refine WP.mono (VG.Proof.Ffdh.X86_64.Generation.controller_zero_out (sPtr := 12) (sLen := 13) (op := op)
    (len := len) scr hdi (by decide) (by decide) (by decide) (by rw [hm]; exact h12) (by rw [hm]; exact h13)
    h1 hlt (hu.outOk hsub hn)) fun t ⟨hv, hfr, k⟩ => ?_
  have hframe : Frame [⟨op, len⟩] s.mem t.mem := by
    intro a ha
    rw [hfr a ?_, hm]
    intro i hi he
    apply ha _ (List.mem_singleton_self _)
    rw [he]
    exact contains_byte _ hi (by omega)
  have hkey : Frame [inKey original] u.mem t.mem := by
    intro a ha
    rw [← hm] at hframe
    refine hframe a fun r hr => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact fun hc => ha _ (List.mem_singleton_self _) (hsub _ hc)
  have hfw : ∀ j < 20, word t.mem p.F (8 * j) = word s.mem p.F (8 * j) := by
    intro j hj
    rw [← hm]
    exact hu.input.frame_words (hkey.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inKey original, by simp [GenInput.callChanges], fun _ h => h⟩) j hj
  exact ⟨hu.restoreKey k.2.1 k.2.2 (fun r hr => k.gpr (by revert r; decide)) hkey, hv, hframe, hfw,
    (ku.trans k).mono (by decide)⟩

/-! ## Stores to the frame -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem frame_state (h : GenInput p s) : p.frame.Disjoint ⟨p.stp, 56⟩ := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [← hst]; exact h.frame_disjoint_writes (by simp [inWrites])

/-- The state through stores to the frame. -/
theorem stateOk_frame (h : GenInput p s) {m m' : Mem} (hf : Frame [p.frame] m m') {st : KeyProgress}
    (hs : StateOk p st m) : StateOk p st m' := by
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  rw [hst] at hn
  have hd := h.frame_state
  have hword (d : Nat) (hd' : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d :=
    hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd' (by omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hs.remaining_le, hs.left_lt⟩
  · rw [hword 0 (by decide)]; exact hs.remaining
  · rw [hword 8 (by decide)]; exact hs.len
  · rw [hword 16 (by decide)]; exact hs.cap
  · rw [hword 32 (by decide)]; exact hs.phase
  · rw [hword 40 (by decide)]; exact hs.left
  · rw [← hs.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
    obtain rfl := List.mem_singleton.mp hq
    refine (hd.sub_right ?_).symm
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]
    exact Offset.sub_base _ (by decide)

end GenInput

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through stores to the frame but its saved r12, with the words for the
octets consumed `u`. -/
theorem store (h : GenFrame p original used st s) {u : Nat} (hu : u ≤ p.randLen)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 20) (h9 : ∀ e ∈ values, 9 ≠ e.1)
    (hm : t.mem = writeFrame s.mem p.F values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.F (p.headers u)) : GenFrame p original u st t := by
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F values hb
  have hf : Frame (GenInput.changes original) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.input.frame_sub⟩
  refine ⟨h.input, hu, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hreg hne hs => (hg reg hreg).trans (h.saved reg hreg hne hs), ?_, ?_, hh,
    h.input.stateOk_frame hfr h.state⟩
  · rw [hm]
    change word (writeFrame s.mem p.F values) p.F (8 * 9) = _
    rw [writeFrame_word _ _ _ hb 9 (by decide), frameValue_unchanged _ _ _ h9]
    exact h.savedR12
  · exact (h.input.random_frame hf).trans h.random

/-- The words of the frame's headers but `used`, kept through stores of others. -/
theorem slots_kept (h : GenFrame p original used st s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) (hnot : ∀ e ∈ values, e.1 ≠ 0 ∧ e.1 ≠ 1 ∧ e.1 ≠ 2 ∧ e.1 ≠ 3 ∧ e.1 ≠ 4 ∧
      e.1 ≠ 5 ∧ e.1 ≠ 6 ∧ e.1 ≠ 7 ∧ e.1 ≠ 8 ∧ e.1 ≠ 11) :
    Slots (writeFrame s.mem p.F values) p.F (p.headers used) := by
  intro e he
  have hj := GenPublic.headers_bound _ _ e he
  rw [writeFrame_word _ _ _ hb e.1 hj, frameValue_unchanged _ _ _ ?_]
  · exact h.headers e he
  · intro x hx heq
    have := hnot x hx
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

end GenFrame

/-! ## The key's buffer but `p` -/

theorem bytes_zero {m : Mem} {op : Addr} {len : Nat} (h : ∀ i < len, m (op + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m op len = List.replicate len 0 := by
  refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i (List.mem_range.mp hi)

theorem bytes_kept {m m' : Mem} {R : Region} {a : Addr} {n : Nat} (hf : Frame [R] m m')
    (hd : R.Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' a n = Spec.Rsa.bytesAt m a n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, n⟩) (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hd.symm) hn
    (List.mem_range.mp hi)

theorem slot_disjoint (kp : Addr) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2 ^ 64)
    (he : e + k ≤ 2 ^ 64) : Region.Disjoint ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp + BitVec.ofNat 64 e, k⟩ :=
  fun x hx hy => Offset.sep kp h hd he x (by simp only [Region.Contains] at hx; omega)
    (by simp only [Region.Contains] at hy; omega)

theorem slot_sub (kp : Addr) {d n k : Nat} (h : d + n ≤ k) :
    Region.Sub ⟨kp + BitVec.ofNat 64 d, n⟩ ⟨kp, k⟩ := Offset.sub_base kp h

theorem kp_zero (kp : Addr) : kp = kp + BitVec.ofNat 64 0 := (BitVec.add_zero kp).symm

/-- A read below a store of the frame sees what was there. -/
theorem read_below_store (m : Mem) (B : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := d) (n := 8) (e := e) (k := 8) (Or.inl h) (by omega) he)
    (by decide)

theorem read_below_store0 (m : Mem) (B : Addr) (v : BitVec 64) {e : Nat} (h : 8 ≤ e)
    (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW B 64 = m.readW B 64 := by
  have := read_below_store m B v (d := 0) h he
  rwa [BitVec.add_zero] at this

theorem setLow_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .store (field 12) .rax, .mov .rcx (.mem (field 1)),
      .shift .shl .rcx 2, .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, p.kp), (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hs : ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem setHigh_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) :
    WP isa (.block [.mov .rax (.mem (field 1)), .mov .rcx (.reg .rax), .shift .shl .rcx 2,
      .alu .add .rax (.reg .rcx), .alu .add .rax (.mem (field 0)), .store (field 12) .rax,
      .mov .rcx (.mem (field 1)), .shift .shl .rcx 2, .store (field 13) .rcx]) s fun t =>
      t.mem = writeFrame s.mem p.F [(12, BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2 + p.kp),
        (13, BitVec.ofNat 64 p.L <<< 2)] ∧ Keep [.rax, .rcx] s t := by
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hs : ∀ d, d + 8 ≤ 160 → InRegions s.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.headers (0, p.kp) (by simp [GenPublic.headers])
  have h1 := h.headers (1, BitVec.ofNat 64 p.L) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0 h1
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeFrame
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), read_below_store _ _ _ (d := 8) (e := 96) (by decide) (by decide),
    read_below_store0 _ _ _ (e := 96) (by decide) (by decide), h0, h1, hs 96 (by decide), hs 104 (by decide)]

theorem twelve_thirteen : ∀ e ∈ [(12, (0 : BitVec 64)), (13, (0 : BitVec 64))], e.1 < 20 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> decide

theorem store_region {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {a b : BitVec 64}
    (hm : t.mem = writeFrame s.mem p.F [(12, a), (13, b)]) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs) :
    GenFrame p original used st t ∧ word t.mem p.F (8 * 12) = a ∧ word t.mem p.F (8 * 13) = b ∧
      Frame [p.frame] s.mem t.mem := by
  have hb : ∀ e ∈ [(12, a), (13, b)], e.1 < 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.store h.used_le _ hb (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro _ (rfl | rfl) <;> dsimp only <;> decide)
    hm k.2.1 k.2.2
    (fun r hr => k.gpr (hrs r hr)) (by
      rw [hm]; exact h.slots_kept _ hb (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide)), ?_, ?_, ?_⟩
  · rw [hm, writeFrame_word _ _ _ hb 12 (by decide)]; rfl
  · rw [hm, writeFrame_word _ _ _ hb 13 (by decide)]; rfl
  · rw [hm]; exact writeFrame_frame s.mem p.F _ hb

theorem GenFrame.key_nowrap {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : p.kp.toNat + 9 * p.L ≤ 2 ^ 64 := by
  have := h.input.nowrap (r := inKey original) (by simp [inWrites])
  rw [h.key_region] at this
  exact this

theorem GenFrame.len_valid {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : primeLenValid p.L := by
  rw [← h.input.2]; exact h.input.1.2.2.2.2.2.2.2.2.1

theorem GenFrame.frame_key {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) : p.frame.Disjoint ⟨p.kp, 9 * p.L⟩ := by
  rw [← h.key_region]; exact h.input.frame_disjoint_writes (by simp [inWrites])

/-- `clearAround`: zeros at the key's buffer but `p`'s slot. -/
theorem clearAround_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s)
    (hp : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB) :
    WP isa clearAround s (GenLive p original used st) := by
  have hn := h.key_nowrap
  have hv := h.len_valid
  obtain ⟨hL1, hL2, -⟩ := hv
  have hkr := h.key_region
  have hfk := h.frame_key
  have h4 : BitVec.ofNat 64 p.L <<< 2 = BitVec.ofNat 64 (4 * p.L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
  have h5 : BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2 + p.kp = p.slot 5 := by
    rw [h4, SearchInit.add_ofNat, BitVec.add_comm]; congr 2; omega
  unfold clearAround
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (setLow_ok h) fun t1 ⟨hm1, k1⟩ => ?_)
  obtain ⟨g1, w12, w13, f1⟩ := store_region h hm1 k1 (by decide)
  rw [h4] at w13
  refine WP.seq (WP.mono (clear_ok g1 w12 w13 (by rw [hkr]; exact Region.sub_prefix (by omega))
    (by omega) (by omega) (by omega)) fun t2 ⟨g2, z2, f2, _, _⟩ => ?_)
  refine WP.seq (WP.mono (setHigh_ok g2) fun t3 ⟨hm3, k3⟩ => ?_)
  obtain ⟨g3, w12', w13', f3⟩ := store_region g2 hm3 k3 (by decide)
  rw [h4] at w13'
  rw [h5] at w12'
  refine WP.mono (clear_ok g3 w12' w13' (by rw [hkr]; exact slot_sub _ (by omega)) (by
      have : (p.slot 5).toNat = p.kp.toNat + 5 * p.L := by
        rw [GenPublic.slot, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      omega) (by omega) (by omega)) fun t4 ⟨g4, z4, f4, _, _⟩ => ?_
  have hd0 : Region.Disjoint ⟨p.slot 5, 4 * p.L⟩ ⟨p.kp, 4 * p.L⟩ := by
    have := slot_disjoint p.kp (d := 5 * p.L) (n := 4 * p.L) (e := 0) (k := 4 * p.L) (.inr (by omega))
      (by omega) (by omega)
    rwa [← kp_zero] at this
  have hfs : p.frame.Disjoint ⟨p.slot 4, p.L⟩ := hfk.sub_right (slot_sub _ (by omega))
  have hf0 : p.frame.Disjoint ⟨p.kp, 4 * p.L⟩ := hfk.sub_right (Region.sub_prefix (by omega))
  refine ⟨g4, ⟨?_, ?_, ?_⟩⟩
  · rw [bytes_kept f4 hd0 (by omega), bytes_kept f3 hf0 (by omega)]
    exact bytes_zero z2
  · exact bytes_zero z4
  · intro pB hpB
    rw [bytes_kept f4 (slot_disjoint _ (.inr (by omega)) (by omega) (by omega)) (by omega),
      bytes_kept f3 hfs (by omega), bytes_kept f2 ?_ (by omega), bytes_kept f1 hfs (by omega)]
    · exact hp pB hpB
    · have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := 4 * p.L) (k := p.L) (.inl (by omega))
        (by omega) (by omega)
      rwa [← kp_zero] at this

end VG.Proof.RsaKeyGen.X86_64.Generate
