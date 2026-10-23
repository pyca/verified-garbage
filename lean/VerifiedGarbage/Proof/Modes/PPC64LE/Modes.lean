module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Seq
public import VerifiedGarbage.Impl.Modes.CbcChained
import VerifiedGarbage.Proof.Modes.StepsChained

/-!
# The modes on PPC64LE, for any core

`seq_wp` for OFB, CFB and CFB8 (`Impl/Modes/Ops.lean`) and CBC that updates
the chaining value (`Impl/Modes/CbcChained.lean`), with the result as the
mode's specification (SP 800-38A, `Spec/Cbc.lean`, `Spec/Ofb.lean`,
`Spec/Cfb.lean`, `Spec/Cfb8.lean`) under the core's cipher. Each cipher's
contracts follow from these.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-! ## The operations are copies and XORs -/

theorem copyBlk_plain {bw : Nat} {dst src : Loc} : ∀ o ∈ copyBlk bw dst src, Plain o := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨_, _, rfl⟩ := ho
  exact ⟨rfl, rfl⟩

theorem xorBlk_plain {bw : Nat} {dst x y : Loc} : ∀ o ∈ xorBlk bw dst x y, Plain o := by
  intro o ho
  simp only [xorBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨_, _, rfl⟩ := ho
  exact ⟨rfl, rfl⟩

theorem shiftIn_plain {bw : Nat} : ∀ o ∈ Mode.shiftIn bw, Plain o := by
  intro o ho
  simp only [Mode.shiftIn, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ho
  rcases ho with ⟨_, _, rfl⟩ | rfl <;> exact ⟨rfl, rfl⟩

theorem both {len : Loc → Nat} {os : List Op} (hp : ∀ o ∈ os, Plain o) (hb : ∀ o ∈ os, o.InBounds len) :
    ∀ o ∈ os, Plain o ∧ o.InBounds len := fun o ho => ⟨hp o ho, hb o ho⟩

theorem append_ok {P : Op → Prop} {os os' : List Op} (h : ∀ o ∈ os, P o) (h' : ∀ o ∈ os', P o) :
    ∀ o ∈ os ++ os', P o := fun o ho => (List.mem_append.mp ho).elim (h o) (h' o)

/-- The data in steps of a byte, as bytes. -/
theorem chunksAt_one (m : Mem) (p : Addr) (n : Nat) : chunksAt 1 m p n = bytesSteps (bytesAt m p n) := by
  simp [chunksAt, bytesSteps, bytesAt]

theorem blk_bounds {c : Core} {st : Nat} (hst : st = 4 * c.bw) (l : Loc) : 4 * c.bw ≤ lens c st l := by
  cases l <;> simp [lens, hst]

section
variable (cs : CoreSpec c) {s₀ : State} {k : cs.Key}

/-- The data on entry, in blocks. -/
abbrev blocks0 (s₀ : State) : List (List Byte) := chunksAt (4 * c.bw) s₀.mem (Dp s₀) (N s₀)

theorem ofb_wp (hp : SeqPre c (Mode.ofb c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.ofb c.bw) s₀) k) :
    WP isa (c.seq (Mode.ofb c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Ofb.crypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Ofb.next (cs.cipher k) (iv0 c s₀) (N s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.ofb c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (b _) (b _)))
    (both (append_ok copyBlk_plain xorBlk_plain)
      (append_ok (copyBlk_inBounds (b _) (b _)) (xorBlk_inBounds (b _) (b _) (b _))))
    (ofb_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(ofb_run _ _ _).1]; rfl)
  · rw [h3 rfl, ← (ofb_run _ _ _).2, chunksAt_length]

theorem cfbEnc_wp (hp : SeqPre c (Mode.cfbEnc c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbEnc c.bw) s₀) k) :
    WP isa (c.seq (Mode.cfbEnc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) =
        Spec.Cbc.next (iv0 c s₀) (Spec.Cfb.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀)) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbEnc c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (b _) (b _)))
    (both (append_ok xorBlk_plain copyBlk_plain)
      (append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _))))
    (cfbEnc_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(cfbEnc_run _ _ _).1]; rfl)
  · rw [h3 rfl, (cfbEnc_run _ _ _).2]; rfl

theorem cfbDec_wp (hp : SeqPre c (Mode.cfbDec c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfbDec c.bw) s₀) k) :
    WP isa (c.seq (Mode.cfbDec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cfb.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cfbDec c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (b _) (b _)))
    (both (append_ok copyBlk_plain xorBlk_plain)
      (append_ok (copyBlk_inBounds (b _) (b _)) (xorBlk_inBounds (b _) (b _) (b _))))
    (cfbDec_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [(cfbDec_run _ _ _).1]; rfl)
  · rw [h3 rfl, (cfbDec_run _ _ _).2]; rfl

/-- The data on entry, as bytes. -/
abbrev bytes0 (s₀ : State) : List Byte := bytesAt s₀.mem (Dp s₀) (N s₀)

theorem cfb8Enc_wp (hp : SeqPre c (Mode.cfb8Enc c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfb8Enc c.bw) s₀) k) :
    WP isa (c.seq (Mode.cfb8Enc c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem (Dp s₀) (N s₀) = Spec.Cfb8.encrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) =
        Spec.Cfb8.next (iv0 c s₀) (Spec.Cfb8.encrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀)) := by
  have hbw : 0 < c.bw := by rcases hp.layout.bw with h | h <;> omega
  have hne : iv0 c s₀ ≠ [] := by
    intro h; have := congrArg List.length h; simp [bytesAt] at this; omega
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (by simp [lens]) (by simp [lens])))
    (fun o ho => ⟨?_, ?_⟩) (cfb8Enc_computes hbw) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cfb8Enc, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact ⟨rfl, rfl⟩
    · exact shiftIn_plain o ho
  · simp only [Mode.cfb8Enc, List.mem_cons] at ho
    rcases ho with rfl | ho
    · exact xorByte_inBounds (by simp [lens, Mode.cfb8Enc]) (by simp [lens]; omega)
    · exact shiftIn_inBounds hbw (by simp [lens]) (by simp [lens, Mode.cfb8Enc]) o ho
  · have h2' : chunksAt 1 s'.mem (Dp s₀) (N s₀) =
        (run (cfb8EncF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem (Dp s₀) (N s₀))).1 := h2
    rw [← bytesSteps_flatten (bytesAt s'.mem _ _), ← chunksAt_one, h2', chunksAt_one, (cfb8Enc_run _ _ _ hne).1]
  · have h3' : bytesAt s'.mem (P s₀) (4 * c.bw) =
        (run (cfb8EncF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem (Dp s₀) (N s₀))).2 := h3 rfl
    rw [h3', chunksAt_one, (cfb8Enc_run _ _ _ hne).2]

theorem cfb8Dec_wp (hp : SeqPre c (Mode.cfb8Dec c.bw) s₀) (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cfb8Dec c.bw) s₀) k) :
    WP isa (c.seq (Mode.cfb8Dec c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem (Dp s₀) (N s₀) = Spec.Cfb8.decrypt (cs.cipher k) (iv0 c s₀) (bytes0 s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cfb8.next (iv0 c s₀) (bytes0 s₀) := by
  have hbw : 0 < c.bw := by rcases hp.layout.bw with h | h <;> omega
  have hne : iv0 c s₀ ≠ [] := by
    intro h; have := congrArg List.length h; simp [bytesAt] at this; omega
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (by simp [lens]) (by simp [lens])))
    (fun o ho => ⟨?_, ?_⟩) (cfb8Dec_computes hbw) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · simp only [Mode.cfb8Dec, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact shiftIn_plain o ho
    · exact ⟨rfl, rfl⟩
  · simp only [Mode.cfb8Dec, List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact shiftIn_inBounds hbw (by simp [lens]) (by simp [lens, Mode.cfb8Dec]) o ho
    · exact xorByte_inBounds (by simp [lens, Mode.cfb8Dec]) (by simp [lens]; omega)
  · have h2' : chunksAt 1 s'.mem (Dp s₀) (N s₀) =
        (run (cfb8DecF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem (Dp s₀) (N s₀))).1 := h2
    rw [← bytesSteps_flatten (bytesAt s'.mem _ _), ← chunksAt_one, h2', chunksAt_one, (cfb8Dec_run _ _ _ hne).1]
  · have h3' : bytesAt s'.mem (P s₀) (4 * c.bw) =
        (run (cfb8DecF (cs.cipher k)) (iv0 c s₀) (chunksAt 1 s₀.mem (Dp s₀) (N s₀))).2 := h3 rfl
    rw [h3', chunksAt_one, (cfb8Dec_run _ _ _ hne).2]

theorem cbcEncChained_wp (hp : SeqPre c (Mode.cbcEncChained c.bw) s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcEncChained c.bw) s₀) k) :
    WP isa (c.seq (Mode.cbcEncChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) =
        Spec.Cbc.next (iv0 c s₀) (Spec.Cbc.encrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀)) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcEncChained c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (both xorBlk_plain (xorBlk_inBounds (b _) (b _) (b _)))
    (both (append_ok copyBlk_plain copyBlk_plain)
      (append_ok (copyBlk_inBounds (b _) (b _)) (copyBlk_inBounds (b _) (b _))))
    (cbcEncChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [encrypt_run]; rfl)
  · rw [h3 rfl, encrypt_run_next]; rfl

theorem cbcDecChained_wp (hp : SeqPre c (Mode.cbcDecChained c.bw) s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c (Mode.cbcDecChained c.bw) s₀) k) :
    WP isa (c.seq (Mode.cbcDecChained c.bw)) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt (4 * c.bw) s'.mem (Dp s₀) (N s₀) = Spec.Cbc.decrypt (cs.cipher k) (iv0 c s₀) (blocks0 (c := c) s₀) ∧
      bytesAt s'.mem (P s₀) (4 * c.bw) = Spec.Cbc.next (iv0 c s₀) (blocks0 (c := c) s₀) := by
  have b := blk_bounds (c := c) (st := (Mode.cbcDecChained c.bw).step) rfl
  refine WP.mono (seq_wp cs hp (both copyBlk_plain (copyBlk_inBounds (b _) (b _)))
    (both (append_ok (append_ok xorBlk_plain copyBlk_plain) copyBlk_plain)
      (append_ok (append_ok (xorBlk_inBounds (b _) (b _) (b _)) (copyBlk_inBounds (b _) (b _)))
        (copyBlk_inBounds (b _) (b _))))
    (cbcDecChained_computes (cs.cipher_len k)) hk) fun s' ⟨h1, h2, h3⟩ => ⟨h1, ?_, ?_⟩
  · exact h2.trans (by rw [decrypt_run]; rfl)
  · rw [h3 rfl, decrypt_run_next]; rfl

end

end VG.Proof.Modes.PPC64LE
