import VerifiedGarbage.Proof.Modes.X86.Seq

/-!
# The modes on x86 (32-bit), for any core

`seq_wp` for each mode of `Impl/Modes/Ops.lean`, with the result as the mode's
specification (SP 800-38A, `Spec/Cbc.lean`, `Spec/Ofb.lean`, `Spec/Cfb.lean`,
`Spec/Cfb8.lean`) under the core's cipher. Each cipher's contracts follow
from these.
-/

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The data in steps of a byte, as bytes. -/
theorem chunksAt_one (m : Mem) (p : Addr) (n : Nat) : chunksAt 1 m p n = bytesSteps (bytesAt m p n) := by
  simp [chunksAt, bytesSteps, bytesAt]

theorem blk_bounds {c : Core} {st : Nat} (hst : st = 4 * c.bw) (l : Loc) : 4 * c.bw ≤ lens c st l := by
  cases l <;> simp [lens, hst]

section
variable (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

/-- The data on entry, in blocks. -/
abbrev blocks0 (s₀ : State) : List (List Byte) := chunksAt (4 * c.bw) s₀.mem ((Dp s₀).setWidth 64) (N s₀)

theorem cbcEnc_wp (hp : SeqPre c (Mode.cbcEnc c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cbcEnc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Cbc.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcEnc c.bw).step) rfl
  exact WP.mono (seq_wp cs hp (xorBlk_inBounds (b _) (b _) (b _))
    (fun o ho => (List.mem_append.mp ho).elim (copyBlk_inBounds (b _) (b _) o) (copyBlk_inBounds (b _) (b _) o))
    (cbcEnc_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, _⟩ => ⟨h1, h2.trans (by rw [encrypt_run]; rfl)⟩

theorem cbcDec_wp (hp : SeqPre c (Mode.cbcDec c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cbcDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDec c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (b _) (b _)) (fun o ho => ?_)
    (cbcDec_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, _⟩ => ⟨h1, h2.trans (by rw [decrypt_run]; rfl)⟩
  simp only [Mode.cbcDec, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact xorBlk_inBounds (b _) (b _) (b _) o ho
  · exact copyBlk_inBounds (b _) (b _) o ho
  · exact copyBlk_inBounds (b _) (b _) o ho

theorem ofb_wp (hp : SeqPre c (Mode.ofb c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.ofb c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Ofb.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) = Spec.Ofb.next (cs.cipher k) (iv0 c s₀) (N s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.ofb c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (b _) (b _))
    (fun o ho => (List.mem_append.mp ho).elim (copyBlk_inBounds (b _) (b _) o) (xorBlk_inBounds (b _) (b _) (b _) o))
    (ofb_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(ofb_run _ _ _).1]; rfl)
  · rw [h3 rfl, ← (ofb_run _ _ _).2, chunksAt_length]

theorem cfbEnc_wp (hp : SeqPre c (Mode.cfbEnc c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cfbEnc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Cfb.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) =
        Spec.Cbc.next (iv0 c s₀) (Spec.Cfb.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀)) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbEnc c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (b _) (b _))
    (fun o ho => (List.mem_append.mp ho).elim (xorBlk_inBounds (b _) (b _) (b _) o) (copyBlk_inBounds (b _) (b _) o))
    (cfbEnc_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(cfbEnc_run _ _ _).1]; rfl)
  · rw [h3 rfl, (cfbEnc_run _ _ _).2]; rfl

theorem cfbDec_wp (hp : SeqPre c (Mode.cfbDec c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cfbDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDec c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (b _) (b _))
    (fun o ho => (List.mem_append.mp ho).elim (copyBlk_inBounds (b _) (b _) o) (xorBlk_inBounds (b _) (b _) (b _) o))
    (cfbDec_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl)
  · rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl

/-- The data on entry, as bytes. -/
abbrev bytes0 (s₀ : State) : List Byte := bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)

theorem cfb8_bounds {l : Loc} : (l = .dat → 1 ≤ lens c 1 l) ∧ (l ≠ .dat → 4 * c.bw ≤ lens c 1 l) := by
  cases l <;> simp [lens]

theorem cfb8Enc_wp (hp : SeqPre c (Mode.cfb8Enc c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cfb8Enc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem ((Dp s₀).setWidth 64) (N s₀) = Spec.Cfb8.encrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀) ∧
      bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) =
        Spec.Cfb8.next (iv0 c s₀) (Spec.Cfb8.encrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀)) := by
  have hbw : 0 < c.bw := by rcases hp.layout.bw with h | h <;> omega
  have hne : iv0 c s₀ ≠ [] := by
    intro h; have := congrArg List.length h; simp [bytesAt] at this; omega
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (by simp [lens]) (by simp [lens]))
    (fun o ho => ?_) (cfb8Enc_computes hbw) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cfb8Enc, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact xorByte_inBounds (by simp [lens, Mode.cfb8Enc]) (by simp [lens]; omega)
    · exact shiftIn_inBounds hbw (by simp [lens]) (by simp [lens, Mode.cfb8Enc]) o ho
  · have h2' : chunksAt 1 s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        (run (cfb8EncF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem ((Dp s₀).setWidth 64) (N s₀))).1 := h2
    rw [← bytesSteps_flatten (bytesAt s'.mem _ _), ← chunksAt_one, h2', chunksAt_one, (cfb8Enc_run _ _ _ hne).1]
  · have h3' : bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) =
        (run (cfb8EncF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem ((Dp s₀).setWidth 64) (N s₀))).2 := h3 rfl
    rw [h3', chunksAt_one, (cfb8Enc_run _ _ _ hne).2]

theorem cfb8Dec_wp (hp : SeqPre c (Mode.cfb8Dec c.bw) s₀) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq (Mode.cfb8Dec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem ((Dp s₀).setWidth 64) (N s₀) = Spec.Cfb8.decrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀) ∧
      bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) = Spec.Cfb8.next (iv0 c s₀) (bytes0 s₀) := by
  have hbw : 0 < c.bw := by rcases hp.layout.bw with h | h <;> omega
  have hne : iv0 c s₀ ≠ [] := by
    intro h; have := congrArg List.length h; simp [bytesAt] at this; omega
  refine WP.mono (seq_wp cs hp (copyBlk_inBounds (by simp [lens]) (by simp [lens]))
    (fun o ho => ?_) (cfb8Dec_computes hbw) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cfb8Dec, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact shiftIn_inBounds hbw (by simp [lens]) (by simp [lens, Mode.cfb8Dec]) o ho
    · exact xorByte_inBounds (by simp [lens, Mode.cfb8Dec]) (by simp [lens]; omega)
  · have h2' : chunksAt 1 s'.mem ((Dp s₀).setWidth 64) (N s₀) =
        (run (cfb8DecF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem ((Dp s₀).setWidth 64) (N s₀))).1 := h2
    rw [← bytesSteps_flatten (bytesAt s'.mem _ _), ← chunksAt_one, h2', chunksAt_one, (cfb8Dec_run _ _ _ hne).1]
  · have h3' : bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) =
        (run (cfb8DecF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem ((Dp s₀).setWidth 64) (N s₀))).2 := h3 rfl
    rw [h3', chunksAt_one, (cfb8Dec_run _ _ _ hne).2]

end

end VG.Proof.Modes.X86
