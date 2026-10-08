import VerifiedGarbage.Proof.Camellia.X86_64.KeyPair
import VerifiedGarbage.Proof.Camellia.KeySched

/-!
# `KA` and `KB` on x86-64

`kaKb_wp`: from the halves of `KL` and `KR` as words in their slots, the
loop of three pairs of rounds (`pairPlain_ok`), with the XORs and copies
between them on the plain words (`xorWords_ok`, `copyWords_ok`), leaves the
halves of `KA` and `KB` in theirs (`Spec.Camellia.kakb`, by `kakb_halves`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st xorS)
open VG.Proof.Camellia (HalfRel WordRel pair hiW loW)

/-! ## Moving words between slots -/

/-- `xor d, [sb + 8 k]`. -/
theorem xorS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [xorS d k] s = some s' ∧ s'.gpr d = s.gpr d ^^^ slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hr' : InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 (8 * k)) 8 := hr
  refine ⟨_, by simp only [xorS, Impl.Aes.X86_64.slotAt, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.load64, State.ea, ofInt_nat, hb, hr', ite_true, Option.bind_some]; rfl, ?_, fun r h => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self, slotW, hb, wordAddr]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags]

theorem slotW_eq_of {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr sb = s.gpr sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [slotW, hm, hb]

theorem scr_in {s : State} {b : Addr} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < slots) :
    InRegions s.wr (wordAddr b k) 8 :=
  ⟨_, hscr, by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < slots) :
    Frame [⟨b, 8 * slots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.sub_base _ (by rw [slots_eq]; omega))

theorem ite_swap2 {α : Type} {k w : Nat} (A B C : α) :
    (if k = w + 1 then A else if k = w then B else C) = if k = w then B else if k = w + 1 then A else C := by
  by_cases h1 : k = w <;> by_cases h2 : k = w + 1 <;> simp [h1, h2] <;> omega

/-- `copyWords w x`: the two words at slot `x` to slot `w`. -/
theorem copyWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x else if k = w + 1 then slotW s (x + 1) else slotW s k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := x) .rax hb (inRd (scr_in hscr (by omega)))
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stReg_ok (k := w) .rax hb₁ (scr_in (by rw [wr₁]; exact hscr) (by omega))
  have hb₂ : s₂.gpr sb = b := by rw [g₂, hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := movS_ok (k := x + 1) .rax hb₂
    (inRd (scr_in (by rw [wr₂, wr₁]; exact hscr) hx))
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (k := w + 1) .rax hb₃
    (scr_in (by rw [wr₃, wr₂, wr₁]; exact hscr) hw)
  have h₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ (hb₁.trans hb.symm)
  have h₂ : ∀ k < slots, slotW s₂ k = if k = w then slotW s x else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₂, hb₁]) g₂ hk (by omega), a₁, h₁]
  have h₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of m₃ (hb₃.trans hb₂.symm)
  refine ⟨s₄, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show copyWords w x = [movS .rax x] ++ ([st w .rax] ++ ([movS .rax (x + 1)] ++ [st (w + 1) .rax]))
      from rfl, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [slotW_store (by rw [m₄, hb₃]) g₄ hk hw, a₃, h₂ (x + 1) hx, ite_eq_right hxw, h₃, h₂ k hk]
    exact ite_swap2 _ _ _
  · rw [g₄, o₃ r hr, g₂, o₁ r hr]
  · rw [m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega)).trans (frame_slot _ hw)

/-- `xorWords w x`: the two words at slot `x` XORed into those at slot `w`. -/
theorem xorWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (xorWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x ^^^ slotW s w
        else if k = w + 1 then slotW s (x + 1) ^^^ slotW s (w + 1) else slotW s k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := x) .rax hb (inRd (scr_in hscr (by omega)))
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := xorS_ok (k := w) .rax hb₁
    (inRd (scr_in (by rw [wr₁]; exact hscr) (by omega)))
  have hb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), hb₁]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stReg_ok (k := w) .rax hb₂
    (scr_in (by rw [wr₂, wr₁]; exact hscr) (by omega))
  have hb₃ : s₃.gpr sb = b := by rw [g₃, hb₂]
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := movS_ok (k := x + 1) .rax hb₃
    (inRd (scr_in (by rw [wr₃, wr₂, wr₁]; exact hscr) hx))
  have hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := xorS_ok (k := w + 1) .rax hb₄
    (inRd (scr_in (by rw [wr₄, wr₃, wr₂, wr₁]; exact hscr) hw))
  have hb₅ : s₅.gpr sb = b := by rw [o₅ _ (by decide), hb₄]
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := stReg_ok (k := w + 1) .rax hb₅
    (scr_in (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hw)
  have h₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by
    rw [slotW_eq_of m₂ (hb₂.trans hb₁.symm), slotW_eq_of m₁ (hb₁.trans hb.symm)]
  have h₃ : ∀ k < slots, slotW s₃ k = if k = w then slotW s x ^^^ slotW s w else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₃, hb₂]) g₃ hk (by omega), a₂, a₁, h₂,
      slotW_eq_of m₁ (hb₁.trans hb.symm)]
  have h₅ : ∀ k, slotW s₅ k = slotW s₃ k := fun k => by
    rw [slotW_eq_of m₅ (hb₅.trans hb₄.symm), slotW_eq_of m₄ (hb₄.trans hb₃.symm)]
  refine ⟨s₆, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show xorWords w x = [movS .rax x] ++ ([xorS .rax w] ++ ([st w .rax] ++ ([movS .rax (x + 1)] ++
      ([xorS .rax (w + 1)] ++ [st (w + 1) .rax])))) from rfl, runBlock_append', e₁, Option.bind_some,
      runBlock_append', e₂, Option.bind_some, runBlock_append', e₃, Option.bind_some,
      runBlock_append', e₄, Option.bind_some, runBlock_append', e₅, Option.bind_some, e₆]
  · rw [slotW_store (by rw [m₆, hb₅]) g₆ hk hw, a₅, a₄, slotW_eq_of m₄ (hb₄.trans hb₃.symm),
      h₃ (x + 1) hx, ite_eq_right hxw, h₃ (w + 1) hw, ite_eq_right (show ¬ w + 1 = w by omega), h₅, h₃ k hk]
    exact ite_swap2 _ _ _
  · rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega)).trans (frame_slot _ hw)

/-! ## The values -/

/-- The subkeys of the pairs, `Sigma1 … Sigma6`. -/
def sigE (i : Nat) : BitVec 64 := sigmas.getD i 0

section
variable (KL KR : BitVec 64 × BitVec 64)

/-- The value after each pair: `KA` after the second, `KB` after the third. -/
def kaD1 : BitVec 64 × BitVec 64 := pair (sigE 0) (sigE 1) (KL.1 ^^^ KR.1, KL.2 ^^^ KR.2)
def kaD2 : BitVec 64 × BitVec 64 := pair (sigE 2) (sigE 3) ((kaD1 KL KR).1 ^^^ KL.1, (kaD1 KL KR).2 ^^^ KL.2)
def kaD3 : BitVec 64 × BitVec 64 := pair (sigE 4) (sigE 5) ((kaD2 KL KR).1 ^^^ KR.1, (kaD2 KL KR).2 ^^^ KR.2)

/-- The running value before pair `i`, and `KB` after the last. -/
def kaW : Nat → BitVec 64 × BitVec 64
  | 0 => (KL.1 ^^^ KR.1, KL.2 ^^^ KR.2)
  | 1 => ((kaD1 KL KR).1 ^^^ KL.1, (kaD1 KL KR).2 ^^^ KL.2)
  | 2 => ((kaD2 KL KR).1 ^^^ KR.1, (kaD2 KL KR).2 ^^^ KR.2)
  | _ => kaD3 KL KR
end

/-- The words at slots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 377 ∧ krSlot = 379 ∧ wSlot = 381 ∧ kaSlot = 383 ∧ kbSlot = 385 ∧
    endSlot = 368 ∧ keySlot = 96 ∧ slots = 393 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KeyCtx` moves to a state with the same base, blocks, regions and slots below the table's end. -/
theorem KeyCtx.of_slots {s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hb : s'.gpr sb = s.gpr sb) (hdx : s'.gpr .rdx = s.gpr .rdx) (hwr : s'.wr = s.wr)
    (hs : ∀ k < endSlot, slotW s' k = slotW s k) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine hp.transfer hb hdx hwr (fun kv hkv => ?_) (fun i hi j hj => ?_)
  · have := mask_lt hkv
    rw [hs _ (by rw [endSlot_eq]; rw [keySlot_eq] at this; omega)]; exact hp.masks kv hkv
  · have := hs (keySlot + 8 * i + j) (by rw [endSlot_eq, keySlot_eq]; omega)
    simp only [slotW, hb, wordAddr] at this
    simp only [entryW]
    rw [show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega]
    exact this

/-! ## The moves between the pairs -/

/-- What the moves keep: the slots but the running value's, `KA`'s and `KB`'s, and the registers but `rax`. -/
structure MoveOk (s s' : State) : Prop where
  keep : ∀ k < slots, (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem MoveOk.trans {s₁ s₂ s₃ : State} (h₁ : MoveOk s₁ s₂) (h₂ : MoveOk s₂ s₃) : MoveOk s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r hr := (h₂.regs r hr).trans (h₁.regs r hr)
  frame := by have := h₂.frame; rw [h₁.regs sb (by decide)] at this; exact h₁.frame.trans this
  rd := h₂.rd.trans h₁.rd
  wr := h₂.wr.trans h₁.wr

/-- `copyWords w x`, for `w` the running value's, `KA`'s or `KB`'s slot. -/
theorem copyW_ok {s : State} {w x : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hw1 : wSlot ≤ w) (hw2 : w ≤ kbSlot) (hx : x + 1 < slots) (hxw : x + 1 ≠ w)
    {v : BitVec 64 × BitVec 64} (hv : WordsAt s x v) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧ MoveOk s s' ∧ WordsAt s' w v ∧
      (∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k) := by
  obtain ⟨-, -, hW, -, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := copyWords_ok rfl hscr (by omega) hx hxw
  have hk : ∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega) (by omega), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs w (by omega), ite_eq_left rfl]; exact hv.1
  · rw [hs (w + 1) (by omega), ite_eq_right (by omega), ite_eq_left rfl]; exact hv.2

/-- `xorWords w x`, for `w` the running value's slot. -/
theorem xorW_ok {s : State} {x : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hx : x + 1 < slots) (hxw : x + 1 ≠ wSlot)
    {u v : BitVec 64 × BitVec 64} (hu : WordsAt s wSlot u) (hv : WordsAt s x v) :
    ∃ s', runBlock isa (xorWords wSlot x) s = some s' ∧ MoveOk s s' ∧
      WordsAt s' wSlot (u.1 ^^^ v.1, u.2 ^^^ v.2) ∧
      (∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k) := by
  obtain ⟨-, -, hW, -, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := xorWords_ok rfl hscr (by omega) hx hxw
  have hk : ∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega) (by omega), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs wSlot (by omega), ite_eq_left rfl, BitVec.xor_comm]; exact hu.1.xor hv.1
  · rw [hs (wSlot + 1) (by omega), ite_eq_right (by omega), ite_eq_left rfl, BitVec.xor_comm]
    exact hu.2.xor hv.2

/-! ## The loop -/

/-- What `kaKb` needs: the table of `Sigma1 … Sigma6`, `kp` at its start, and `KL` and `KR` in their slots. -/
structure KaPre (s₀ : State) (KL KR : BitVec 64 × BitVec 64) : Prop where
  ctx : KeyCtx s₀ 6 sigE
  sx : Region.Disjoint ⟨s₀.gpr .rdx, 128⟩ ⟨s₀.gpr sb, 8 * slots⟩
  kp : AtEntry s₀ (s₀.gpr sb) 0
  kl : WordsAt s₀ klSlot KL
  kr : WordsAt s₀ krSlot KR

/-- The loop's state: `kp` at entry `m`, `i` pairs done (`KA` after two,
`KB` after three), `c` in `r8`, the running value `W`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (m i c : Nat) (W : BitVec 64 × BitVec 64)
    (s : State) : Prop where
  ctx : KeyCtx s 6 sigE
  base : s.gpr sb = s₀.gpr sb
  rdx : s.gpr .rdx = s₀.gpr .rdx
  ent : AtEntry s (s₀.gpr sb) m
  rdi : s.gpr .rdi = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot)
  cnt : s.gpr .r8 = BitVec.ofNat 64 c
  w : WordsAt s wSlot W
  ka : 2 ≤ i → WordsAt s kaSlot (kaD2 KL KR)
  kb : 3 ≤ i → WordsAt s kbSlot (kaD3 KL KR)
  keep : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s k = slotW s₀ k
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → r ≠ .r8 → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * slots⟩, ⟨s₀.gpr .rdx, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem KaInv.kl {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s klSlot KL := by
  obtain ⟨hl, -, hW, -, -, -, hK, hS⟩ := kaKb_slots
  exact hp.kl.congr (h.keep _ (by omega) (by omega) (by omega)) (h.keep _ (by omega) (by omega) (by omega))

theorem KaInv.kr {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s krSlot KR := by
  obtain ⟨-, hr, hW, -, -, -, hK, hS⟩ := kaKb_slots
  exact hp.kr.congr (h.keep _ (by omega) (by omega) (by omega)) (h.keep _ (by omega) (by omega) (by omega))

theorem KaInv.move {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i i' c : Nat}
    {W W' : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hm : MoveOk s s')
    (hw : WordsAt s' wSlot W') (hka : 2 ≤ i' → WordsAt s' kaSlot (kaD2 KL KR))
    (hkb : 3 ≤ i' → WordsAt s' kbSlot (kaD3 KL KR)) : KaInv s₀ KL KR m i' c W' s' := by
  obtain ⟨-, -, hW, -, -, hE, -, hS⟩ := kaKb_slots
  refine ⟨h.ctx.of_slots (hm.regs _ (by decide)) (hm.regs _ (by decide)) hm.wr
      (fun k hk => hm.keep k (by omega) (Or.inl (by omega))), (hm.regs _ (by decide)).trans h.base,
    (hm.regs _ (by decide)).trans h.rdx, by rw [AtEntry, hm.regs _ (by decide)]; exact h.ent,
    (hm.regs _ (by decide)).trans h.rdi, (hm.regs _ (by decide)).trans h.cnt, hw, hka, hkb,
    fun k h1 h2 h3 => (hm.keep k h2 h3).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hm.regs r (fun e => h1 (by subst e; decide))).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans ?_, hm.rd.trans h.rd, hm.wr.trans h.wr⟩
  have := hm.frame
  rw [h.base] at this
  exact this.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]

/-- A step that writes only `r8` and the flags. -/
theorem KaInv.regs8 {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i c c' : Nat}
    {W : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hg : ∀ r, r ≠ .r8 → s'.gpr r = s.gpr r)
    (hmem : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.gpr .r8 = BitVec.ofNat 64 c') : KaInv s₀ KL KR m i c' W s' := by
  have hs : ∀ k, slotW s' k = slotW s k := slotW_eq_of hmem (hg _ (by decide))
  refine ⟨h.ctx.of_slots (hg _ (by decide)) (hg _ (by decide)) hwr (fun k _ => hs k),
    (hg _ (by decide)).trans h.base, (hg _ (by decide)).trans h.rdx,
    by rw [AtEntry, hg _ (by decide)]; exact h.ent, (hg _ (by decide)).trans h.rdi, hc,
    h.w.congr (hs _) (hs _), fun hi => (h.ka hi).congr (hs _) (hs _), fun hi => (h.kb hi).congr (hs _) (hs _),
    fun k h1 h2 h3 => (hs k).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hg r h4).trans (h.regs r h1 h2 h3 h4), by rw [hmem]; exact h.frame,
    hrd.trans h.rd, hwr.trans h.wr⟩

/-- A pair of rounds. -/
theorem KaInv.pair_ok {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR (2 * i) i c W s) (hi : i < 3) :
    ∃ s', runBlock isa pairPlain s = some s' ∧
      KaInv s₀ KL KR (2 * i + 2) i c (pair (sigE (2 * i)) (sigE (2 * i + 1)) W) s' := by
  obtain ⟨-, -, hW, hA, hB, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s', e, ctx', kp', regs', rdi', w1, w2, keep', frame', rd', wr'⟩ :=
    pairPlain_ok h.ctx (by rw [h.rdx, h.base]; exact hp.sx) (by rw [h.base]; exact h.ent) (by omega)
      (by rw [h.rdi, h.base]) h.w.1 h.w.2
  have hr : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s'.gpr r = s.gpr r := regs'
  have hk : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k ∨ k = kaSlot ∨ k = kaSlot + 1 ∨
      k = kbSlot ∨ k = kbSlot + 1) → slotW s' k = slotW s k := fun k h1 h2 h3 =>
    keep' k h1 h2 (by omega) (by omega)
  refine ⟨s', e, ⟨ctx', (hr _ (by decide) (by decide) (by decide)).trans h.base,
    (hr _ (by decide) (by decide) (by decide)).trans h.rdx, by rw [h.base] at kp'; exact kp',
    rdi'.trans h.rdi, (hr _ (by decide) (by decide) (by decide)).trans h.cnt, ⟨w1, w2⟩,
    fun hi => (h.ka hi).congr (hk _ (by omega) (by omega) (by omega)) (hk _ (by omega) (by omega) (by omega)),
    fun hi => (h.kb hi).congr (hk _ (by omega) (by omega) (by omega)) (hk _ (by omega) (by omega) (by omega)),
    fun k h1 h2 h3 => (hk k h1 h2 (by omega)).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans (by rw [h.base, h.rdx] at frame'; exact frame'), rd'.trans h.rd, wr'.trans h.wr⟩⟩

/-- `KL ^ KR` to the running value's slots, `r8 := 3`, `rdi` at them. -/
theorem kaPrefix_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    ∃ s', runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ [.movImm64 .r8 3, movR .rdi sb,
      .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * wSlot)))]) s₀ = some s' ∧
      KaInv s₀ KL KR 0 0 3 (kaW KL KR 0) s' := by
  obtain ⟨hl, hr, hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, mv₁, w₁, -⟩ := copyW_ok (w := wSlot) (x := klSlot) hp.ctx.scr (by omega) (by omega)
    (by omega) (by omega) hp.kl
  have hscr₁ : (⟨s₁.gpr sb, 8 * slots⟩ : Region) ∈ s₁.wr := by
    rw [mv₁.regs _ (by decide), mv₁.wr]; exact hp.ctx.scr
  obtain ⟨s₂, e₂, mv₂, w₂, -⟩ := xorW_ok hscr₁ (by omega) (by omega) w₁
    (hp.kr.congr (mv₁.keep _ (by omega) (Or.inl (by omega))) (mv₁.keep _ (by omega) (Or.inl (by omega))))
  have mv := mv₁.trans mv₂
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := movImm_ok s₂ .r8 3
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdi sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdi (BitVec.ofNat 32 (8 * wSlot))
  have hg : ∀ r, r ≠ .r8 → r ≠ .rdi → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by rw [o₅ r h2, o₄ r h2, o₃ r h1]
  have hb : s₅.gpr sb = s₀.gpr sb := by rw [hg _ (by decide) (by decide), mv.regs _ (by decide)]
  have hs : ∀ k, slotW s₅ k = slotW s₂ k := slotW_eq_of (by rw [m₅, m₄, m₃]) (hg _ (by decide) (by decide))
  refine ⟨s₅, ?_, ⟨hp.ctx.of_slots hb (by rw [hg _ (by decide) (by decide), mv.regs _ (by decide)])
      (by rw [wr₅, wr₄, wr₃, mv.wr]) (fun k hk => by rw [hs, mv.keep k (by omega) (Or.inl (by omega))]), hb,
    by rw [hg _ (by decide) (by decide), mv.regs _ (by decide)], ?_, ?_,
    (o₅ _ (by decide)).trans ((o₄ _ (by decide)).trans c₃), w₂.congr (hs _) (hs _),
    fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun k _ h2 h3 => by rw [hs, mv.keep k h2 h3],
    fun r h1 _ h3 h4 => by rw [hg r h4 h3, mv.regs r (fun e => h1 (by subst e; decide))], ?_,
    by rw [rd₅, rd₄, rd₃, mv.rd], by rw [wr₅, wr₄, wr₃, mv.wr]⟩⟩
  · rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.movImm64 .r8 3, movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * wSlot)))] : List Instr) =
        [.movImm64 .r8 3] ++ ([movR .rdi sb] ++ [.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * wSlot)))]) from rfl,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅]
  · rw [AtEntry, hg _ (by decide) (by decide), mv.regs _ (by decide)]; exact hp.kp
  · rw [r₅, r₄, o₃ _ (by decide), mv.regs _ (by decide),
      show (BitVec.ofNat 32 (8 * wSlot)).signExtend 64 = BitVec.ofNat 64 (8 * wSlot) from rfl]
  · rw [m₅, m₄, m₃]; exact mv.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]

/-- `kaKb`: the three pairs, leaving `KA` and `KB` in their slots. -/
theorem kaKb_wp {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    WP isa kaKb s₀ (KaInv s₀ KL KR 6 3 0 (kaD3 KL KR)) := by
  obtain ⟨hl, hr, hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  unfold kaKb
  refine WP.seq (WP.mono (WP.of_runBlock (kaPrefix_ok hp)) fun s h => ?_)
  refine WP.loop (M := isa)
    (fun n s => ∃ i, n = 3 - i ∧ i < 3 ∧ KaInv s₀ KL KR (2 * i) i (3 - i) (kaW KL KR i) s)
    (fun n s hs => ?_) 3 s ⟨0, rfl, by decide, h⟩
  obtain ⟨i, rfl, hi, hI⟩ := hs
  obtain ⟨s₁, e₁, h₁⟩ := hI.pair_ok hp hi
  obtain ⟨s₂, e₂, cf₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 2 (v := 3 - i) h₁.cnt (by omega) rfl
  have h₂ := h₁.regs8 (fun r _ => by rw [g₂]) m₂ rd₂ wr₂ (by rw [g₂]; exact h₁.cnt)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)⟩)
  refine WP.seq (WP.mono (Q := KaInv s₀ KL KR (2 * i + 2) (i + 1) (3 - i) (kaW KL KR (i + 1))) ?_
    fun s₃ h₃ => ?_)
  · refine WP.ite (!decide (3 - i < 2)) (by simp [X86_64.eval, cf₂]) (fun ht => ?_) (fun hf => ?_)
    · have hi1 : i ≤ 1 := by simp at ht; omega
      obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := cmpImmZ_ok s₂ .r8 3
      have h₃ := h₂.regs8 (fun r _ => by rw [g₃]) m₃ rd₃ wr₃ (by rw [g₃]; exact h₂.cnt)
      refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
      refine WP.ite (decide (i = 0)) (by
        show s₃.zf = _
        rw [z₃, h₂.cnt]
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide) (fun h0 => ?_) (fun h0 => ?_)
      · obtain rfl : i = 0 := by simpa using h0
        obtain ⟨s₄, e₄, mv₄, w₄, -⟩ := xorW_ok h₃.ctx.scr (by omega) (by omega) h₃.w (h₃.kl hp)
        exact WP.of_runBlock ⟨s₄, e₄, h₃.move mv₄ w₄ (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))⟩
      · obtain rfl : i = 1 := by simp at h0; omega
        obtain ⟨s₄, e₄, mv₄, w₄, o₄⟩ := copyW_ok (w := kaSlot) (x := wSlot) h₃.ctx.scr (by omega) (by omega)
          (by omega) (by omega) h₃.w
        have hscr₄ : (⟨s₄.gpr sb, 8 * slots⟩ : Region) ∈ s₄.wr := by
          rw [mv₄.regs _ (by decide), mv₄.wr]; exact h₃.ctx.scr
        obtain ⟨s₅, e₅, mv₅, w₅, o₅⟩ := xorW_ok hscr₄ (by omega) (by omega)
          (h₃.w.congr (o₄ _ (by omega) (by omega) (by omega)) (o₄ _ (by omega) (by omega) (by omega)))
          ((h₃.kr hp).congr (mv₄.keep _ (by omega) (Or.inl (by omega)))
            (mv₄.keep _ (by omega) (Or.inl (by omega))))
        refine WP.of_runBlock ⟨s₅, by rw [runBlock_append', e₄, Option.bind_some, e₅],
          h₃.move (mv₄.trans mv₅) w₅ (fun _ => w₄.congr (o₅ _ (by omega) (by omega) (by omega))
            (o₅ _ (by omega) (by omega) (by omega))) (fun h => absurd h (by decide))⟩
    · obtain rfl : i = 2 := by simp at hf; omega
      obtain ⟨s₃, e₃, mv₃, w₃, o₃⟩ := copyW_ok (w := kbSlot) (x := wSlot) h₂.ctx.scr (by omega) (by omega)
        (by omega) (by omega) h₂.w
      exact WP.of_runBlock ⟨s₃, e₃, h₂.move mv₃
        (h₂.w.congr (o₃ _ (by omega) (by omega) (by omega)) (o₃ _ (by omega) (by omega) (by omega)))
        (fun _ => (h₂.ka (by decide)).congr (o₃ _ (by omega) (by omega) (by omega))
          (o₃ _ (by omega) (by omega) (by omega))) (fun _ => w₃)⟩
  · obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃ .r8 1
    have hsub : s₃.gpr .r8 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (3 - (i + 1)) := by
      rw [h₃.cnt, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
        VG.Offset.ofNat_sub_ofNat (by omega), show 3 - i - 1 = 3 - (i + 1) by omega]
    have h₄ := h₃.regs8 o₄ m₄ rd₄ wr₄ (by rw [c₄, hsub])
    have hz : s₄.zf = some (decide (3 - (i + 1) = 0)) := by
      rw [z₄, h₃.cnt, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
      simp only [Option.some.injEq, decide_eq_decide]; omega
    refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
    by_cases hl : i + 1 = 3
    · obtain rfl : i = 2 := by omega
      exact .inl ⟨by simp [X86_64.eval, hz], h₄⟩
    · exact .inr ⟨by simp [X86_64.eval, hz]; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega,
        by rw [Nat.mul_add, Nat.mul_one]; exact h₄⟩

/-- The values are the specification's `KA` and `KB` (`Spec.Camellia.kakb`). -/
theorem kaD_eq (kl kr : BitVec 128) :
    kaD2 (hiW kl, loW kl) (hiW kr, loW kr) = (hiW (Spec.Camellia.kakb kl kr).1, loW (Spec.Camellia.kakb kl kr).1) ∧
    kaD3 (hiW kl, loW kl) (hiW kr, loW kr) = (hiW (Spec.Camellia.kakb kl kr).2, loW (Spec.Camellia.kakb kl kr).2) := by
  obtain ⟨h1, h2, h3, h4⟩ := Proof.Camellia.kakb_halves kl kr
  rw [h1, h2, h3, h4]
  exact ⟨rfl, rfl⟩

end VG.Proof.Camellia.X86_64
