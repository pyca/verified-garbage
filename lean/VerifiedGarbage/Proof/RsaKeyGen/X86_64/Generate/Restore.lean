module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Entry
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # What the controller's steps keep

The callees and the controller's own stores change only the key's buffer,
`used`, the working space, the state's first four words and the stack below
the frame (`callChanges`); through such changes a loop state keeps its frame,
its tape and the state's last three words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

namespace GenInput

variable {p : GenPublic} {s : State}

/-- What a step may write: the key's buffer, `used`, the working space, the
state's first four words, and the stack below the frame. -/
def callChanges (s : State) : List Region :=
  [inKey s, inUsed s, inScr s, ⟨stackArg s 1, 32⟩, ⟨s.gpr .rsp - BitVec.ofNat 64 stackUse, 392⟩]

theorem state32_sub (s : State) : Region.Sub ⟨stackArg s 1, 32⟩ (inState s) := by
  unfold inState
  exact Region.sub_prefix (by decide)

theorem callChanges_sub (s : State) : ∀ r ∈ callChanges s, ∃ q ∈ changes s, Region.Sub r q := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], fun _ hi => hi⟩
  · exact ⟨_, by simp [changes, inWrites], state32_sub s⟩
  · exact ⟨below (s.gpr .rsp) stackUse, by simp [changes], Region.sub_prefix (by decide)⟩

theorem frame_of_callChanges (s : State) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Frame (changes s) m m' := hf.sub (callChanges_sub s)

/-- The frame is disjoint from what a step writes. -/
theorem frame_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, p.frame.Disjoint r := by
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact h.frame_disjoint_writes (by simp [inWrites])
  · exact (h.frame_disjoint_writes (r := inState s) (by simp [inWrites])).sub_right (state32_sub s)
  · rw [← h.sp_eq]
    have hs := Offset.sep_below p.sp 552 (a := 160) (n := 160) (b := 552) (k := 392) (by decide) (by decide)
      (Or.inr (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (by simp only [Region.Contains, GenPublic.F] at hx; omega)
      (by simp only [Region.Contains] at hy; exact hy)

theorem frame_words (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m')
    (j : Nat) (hj : j < 20) : word m' p.F (8 * j) = word m p.F (8 * j) :=
  hf.readW (r := p.frame) (Offset.contains_base _ (by omega) (by omega)) h.frame_disjoint (by decide)

/-- The state's last three words. -/
abbrev stateTail (p : GenPublic) : Region := ⟨p.stp + BitVec.ofNat 64 32, 24⟩

theorem tail_disjoint (h : GenInput p s) : ∀ r ∈ callChanges s, (stateTail p).Disjoint r := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hstp : stackArg s 1 = p.stp := by rw [← h.2]; rfl
  have hsub : Region.Sub (stateTail p) (inState s) := by rw [hst]; exact Offset.sub_base _ (by decide)
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hpw.1.2.2.symm).sub_left hsub
  · exact (hpw.2.1.2.symm).sub_left hsub
  · exact (hpw.2.2.1.symm).sub_left hsub
  · rw [hstp]
    exact fun x hx hy => by
      simp only [Region.Contains] at hx hy
      have := Offset.sep p.stp (d := 32) (n := 24) (e := 0) (k := 32) (Or.inr (by decide)) (by decide) (by decide)
      rw [BitVec.add_zero] at this
      exact this x (by omega) (by omega)
  · exact fun x hx hy => (h.stack_disjoint (r := inState s) (by simp [inWrites])).2 x
      (Region.sub_prefix (base := s.gpr .rsp - BitVec.ofNat 64 stackUse) (by decide) x hy) (hsub x hx)

theorem tail_word (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') {d : Nat}
    (hd₁ : 32 ≤ d) (hd₂ : d + 8 ≤ 56) : word m' p.stp d = word m p.stp d := by
  have hc : (stateTail p).Contains (off p.stp d) 8 := by
    rw [show off p.stp d = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 (d - 32) by
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  exact hf.readW hc h.tail_disjoint (by decide)

theorem tail_bytes (h : GenInput p s) {m m' : Mem} (hf : Frame (callChanges s) m m') :
    Spec.Rsa.bytesAt m' (p.stp + 48) 8 = Spec.Rsa.bytesAt m (p.stp + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hsub : Region.Sub ⟨p.stp + 48, 8⟩ (stateTail p) := by
    rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 32 + BitVec.ofNat 64 16 by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl]
    exact Offset.sub_base _ (by decide)
  exact hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => (h.tail_disjoint r hr).sub_left hsub)
    (by show 8 ≤ 2 ^ 64; decide) hi

end GenInput

namespace GenFrame

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- Through a step that keeps r12, the stack pointer, the regions and the
callee-saved registers, and writes only what a step may, with the state's
first three words for the progress `st'`, whose phase and generations are
`st`'s. -/
theorem restore (h : GenFrame p original used st s) {st' : KeyProgress}
    (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r)
    (hf : Frame (GenInput.callChanges original) s.mem t.mem)
    (h0 : word t.mem p.stp 0 = BitVec.ofNat 64 st'.remaining)
    (h1 : word t.mem p.stp 8 = BitVec.ofNat 64 p.L)
    (h2 : word t.mem p.stp 16 = BitVec.ofNat 64 (primeEntropy p.L))
    (hph : st'.phase = st.phase ∨ phaseWord st'.phase = phaseWord st.phase) (hl : st'.left = st.left)
    (hrem : st'.remaining ≤ limitOf p.L p.eB) :
    GenFrame p original used st' t := by
  have hc := h.input.frame_words hf
  have hf' := GenInput.frame_of_callChanges original hf
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun r hr hn hs => (hg r hr).trans (h.saved r hr hn hs), ?_, ?_, ?_,
    ⟨h0, h1, h2, ?_, ?_, ?_, hrem, by rw [hl]; exact h.state.left_lt⟩⟩
  · exact (hc 9 (by decide)).trans h.savedR12
  · exact (h.input.random_frame hf').trans h.random
  · intro e he
    exact (hc e.1 (GenPublic.headers_bound _ _ e he)).trans (h.headers e he)
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.phase]
    rcases hph with hph | hph <;> rw [hph]
  · rw [h.input.tail_word hf (by decide) (by decide), h.state.left, hl]
  · rw [h.input.tail_bytes hf, h.state.e]

end GenFrame

end VG.Proof.RsaKeyGen.X86_64.Generate
