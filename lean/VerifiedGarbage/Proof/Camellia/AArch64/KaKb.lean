import VerifiedGarbage.Proof.Camellia.AArch64.KeyPair
import VerifiedGarbage.Proof.Camellia.KeySched

/-!
# `KA` and `KB` on AArch64

As on x86-64: `kaKb_wp`: from the halves of `KL` and `KR` as words in their
slots, the loop of three pairs of rounds (`pairPlain_ok`), with the XORs and
copies between them on the plain words (`xorWords_ok`, `copyWords_ok`),
leaves the halves of `KA` and `KB` in theirs (`Spec.Camellia.kakb`, by
`kakb_halves`).
-/

namespace VG.Proof.Camellia.AArch64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR ldS stS eorR lsrI)
open VG.Proof.Camellia (HalfRel WordRel pair hiW loW)

/-! ## Moving words between slots -/

theorem slotW_eq_of {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr sb = s.gpr sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [slotW, hm, hb]

theorem scr_in {s : State} {b : Addr} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < slots) :
    InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨_, hscr, by rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < slots) :
    Frame [⟨b, 8 * slots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.sub_base _ (by rw [slots_eq]; omega))

/-- `ldr d, [sb, #8 k]`. -/
theorem ldS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [ldS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ldMask_ok (by rw [slots_eq] at hk; omega) (inRd this) rfl

/-- `str r, [sb, #8 k]`. -/
theorem stS_slot {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ⟨_, stS_ok s r (by rw [slots_eq] at hk; omega) this, by rw [hb], rfl, rfl, rfl⟩

theorem eor_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [eorR d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n ^^^ s.gpr m), by
    simp only [eorR, runBlock_cons, runStep_some, runBlock_nil, exec_logic, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

/-- `copyWords w x`: the two words at slot `x` to slot `w`. -/
theorem copyWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x else if k = w + 1 then slotW s (x + 1) else slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hscr (by omega)
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_slot (k := w) t0 hb₁ (by rw [wr₁]; exact hscr) (by omega)
  have hb₂ : s₂.gpr sb = b := by rw [g₂, hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (k := x + 1) t0 hb₂ (by rw [wr₂, wr₁]; exact hscr) hx
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w + 1) t0 hb₃ (by rw [wr₃, wr₂, wr₁]; exact hscr) hw
  have h₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ (hb₁.trans hb.symm)
  have h₂ : ∀ k < slots, slotW s₂ k = if k = w then slotW s x else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₂, hb₁]) g₂ hk (by omega), a₁, h₁]
  have h₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of m₃ (hb₃.trans hb₂.symm)
  refine ⟨s₄, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show copyWords w x = [ldS t0 x] ++ ([stS w t0] ++ ([ldS t0 (x + 1)] ++ [stS (w + 1) t0]))
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
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hscr (by omega)
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (k := w) t1 hb₁ (by rw [wr₁]; exact hscr) (by omega)
  have hb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ t0 t0 t1
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w) t0 hb₃ (by rw [wr₃, wr₂, wr₁]; exact hscr) (by omega)
  have hb₄ : s₄.gpr sb = b := by rw [g₄, hb₃]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := x + 1) t0 hb₄
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact hscr) hx
  have hb₅ : s₅.gpr sb = b := by rw [o₅ _ (by decide), hb₄]
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := ldS_ok (k := w + 1) t1 hb₅
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hw
  have hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), hb₅]
  obtain ⟨s₇, e₇, a₇, o₇, m₇, rd₇, wr₇⟩ := eor_ok s₆ t0 t0 t1
  have hb₇ : s₇.gpr sb = b := by rw [o₇ _ (by decide), hb₆]
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_slot (k := w + 1) t0 hb₇
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hw
  have h₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by
    rw [slotW_eq_of m₃ (hb₃.trans hb₂.symm), slotW_eq_of m₂ (hb₂.trans hb₁.symm),
      slotW_eq_of m₁ (hb₁.trans hb.symm)]
  have v₃ : s₃.gpr t0 = slotW s x ^^^ slotW s w := by
    rw [a₃, o₂ _ (by decide), a₁, a₂, slotW_eq_of m₁ (hb₁.trans hb.symm)]
  have h₄ : ∀ k < slots, slotW s₄ k = if k = w then slotW s x ^^^ slotW s w else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ hk (by omega), v₃, h₃]
  have h₆ : ∀ k, slotW s₆ k = slotW s₄ k := fun k => by
    rw [slotW_eq_of m₆ (hb₆.trans hb₅.symm), slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  have v₇ : s₇.gpr t0 = slotW s₄ (x + 1) ^^^ slotW s₄ (w + 1) := by
    rw [a₇, o₆ _ (by decide), a₅, a₆, slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  refine ⟨s₈, ?_, fun k hk => ?_, fun r h0 h1 => ?_, ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show xorWords w x = [ldS t0 x] ++ ([ldS t1 w] ++ ([eorR t0 t0 t1] ++ ([stS w t0] ++
      ([ldS t0 (x + 1)] ++ ([ldS t1 (w + 1)] ++ ([eorR t0 t0 t1] ++ [stS (w + 1) t0])))))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some,
      runBlock_append', e₇, Option.bind_some, e₈]
  · rw [slotW_store (by rw [m₈, hb₇]) g₈ hk hw, v₇, slotW_eq_of m₇ (hb₇.trans hb₆.symm), h₆,
      h₄ (x + 1) hx, ite_eq_right hxw, h₄ (w + 1) hw, ite_eq_right (show ¬ w + 1 = w by omega), h₄ k hk]
    exact ite_swap2 _ _ _
  · rw [g₈, o₇ r h0, o₆ r h1, o₅ r h0, g₄, o₃ r h0, o₂ r h1, o₁ r h0]
  · rw [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega)).trans (frame_slot _ hw)

/-! ## The values -/


/-- The words at slots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 378 ∧ krSlot = 380 ∧ wSlot = 382 ∧ kaSlot = 384 ∧ kbSlot = 386 ∧
    endSlot = 368 ∧ keySlot = 96 ∧ slots = 394 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KeyCtx` moves to a state with the same base, regions and slots below the table's end. -/
theorem KeyCtx.of_slots {s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hb : s'.gpr sb = s.gpr sb) (hwr : s'.wr = s.wr)
    (hs : ∀ k < endSlot, slotW s' k = slotW s k) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine hp.transfer hb hwr (fun kv hkv => ?_) (fun i hi j hj => ?_)
  · have := mask_lt hkv
    rw [hs _ (by rw [endSlot_eq]; rw [keySlot_eq] at this; omega)]; exact hp.masks kv hkv
  · have := hs (keySlot + 8 * i + j) (by rw [endSlot_eq, keySlot_eq]; omega)
    simp only [slotW, hb, wordAddr] at this
    simp only [entryW]
    rw [show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega]
    exact this

/-! ## The moves between the pairs -/

/-- What the moves keep: the slots but the running value's, `KA`'s and `KB`'s, and the registers but `t0`, `t1`. -/
structure MoveOk (s s' : State) : Prop where
  keep : ∀ k < slots, (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem MoveOk.trans {s₁ s₂ s₃ : State} (h₁ : MoveOk s₁ s₂) (h₂ : MoveOk s₂ s₃) : MoveOk s₁ s₃ where
  keep k hk h := (h₂.keep k hk h).trans (h₁.keep k hk h)
  regs r h0 h1 := (h₂.regs r h0 h1).trans (h₁.regs r h0 h1)
  frame := by have := h₂.frame; rw [h₁.regs sb (by decide) (by decide)] at this; exact h₁.frame.trans this
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
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega) (by omega), fun r h0 _ => g r h0, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
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
  kp : AtEntry s₀ (s₀.gpr sb) 0
  kl : WordsAt s₀ klSlot KL
  kr : WordsAt s₀ krSlot KR

/-- The loop's state: `kp` at entry `m`, `i` pairs done (`KA` after two,
`KB` after three), `c` in `x4`, the running value `W`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (m i c : Nat) (W : BitVec 64 × BitVec 64)
    (s : State) : Prop where
  ctx : KeyCtx s 6 sigE
  base : s.gpr sb = s₀.gpr sb
  ent : AtEntry s (s₀.gpr sb) m
  x0 : s.gpr .x0 = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot)
  cnt : s.gpr .x4 = BitVec.ofNat 64 c
  w : WordsAt s wSlot W
  ka : 2 ≤ i → WordsAt s kaSlot (kaD2 KL KR)
  kb : 3 ≤ i → WordsAt s kbSlot (kaD3 KL KR)
  keep : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s k = slotW s₀ k
  regs : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → r ≠ .x4 → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem
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

theorem t_layer : t0 ∈ layerWrites ∧ t1 ∈ layerWrites := by decide

theorem KaInv.move {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i i' c : Nat}
    {W W' : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hm : MoveOk s s')
    (hw : WordsAt s' wSlot W') (hka : 2 ≤ i' → WordsAt s' kaSlot (kaD2 KL KR))
    (hkb : 3 ≤ i' → WordsAt s' kbSlot (kaD3 KL KR)) : KaInv s₀ KL KR m i' c W' s' := by
  obtain ⟨-, -, hW, -, -, hE, -, hS⟩ := kaKb_slots
  have hg : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    hm.regs r (fun e => hr (e ▸ t_layer.1)) (fun e => hr (e ▸ t_layer.2))
  refine ⟨h.ctx.of_slots (hg _ (by decide)) hm.wr
      (fun k hk => hm.keep k (by omega) (Or.inl (by omega))), (hg _ (by decide)).trans h.base,
    by rw [AtEntry, hg _ (by decide)]; exact h.ent,
    (hg _ (by decide)).trans h.x0, (hg _ (by decide)).trans h.cnt, hw, hka, hkb,
    fun k h1 h2 h3 => (hm.keep k h2 h3).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hg r h1).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans ?_, hm.rd.trans h.rd, hm.wr.trans h.wr⟩
  have := hm.frame
  rw [h.base] at this
  exact this

/-- A step that writes only `r` (not `sb`, `kp` or `x0`). -/
theorem KaInv.regs1 {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i c c' : Nat}
    {W : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) {r₀ : Reg} (hr₀ : r₀ ∈ [t1, Reg.x4])
    (hg : ∀ r, r ≠ r₀ → s'.gpr r = s.gpr r)
    (hmem : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.gpr .x4 = BitVec.ofNat 64 c') : KaInv s₀ KL KR m i c' W s' := by
  have hn : sb ≠ r₀ ∧ kp ≠ r₀ ∧ Reg.x0 ≠ r₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₀; rcases hr₀ with rfl | rfl <;> decide
  have hs : ∀ k, slotW s' k = slotW s k := slotW_eq_of hmem (hg _ hn.1)
  refine ⟨h.ctx.of_slots (hg _ hn.1) hwr (fun k _ => hs k),
    (hg _ hn.1).trans h.base, by rw [AtEntry, hg _ hn.2.1]; exact h.ent, (hg _ hn.2.2).trans h.x0, hc,
    h.w.congr (hs _) (hs _), fun hi => (h.ka hi).congr (hs _) (hs _), fun hi => (h.kb hi).congr (hs _) (hs _),
    fun k h1 h2 h3 => (hs k).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => ?_, by rw [hmem]; exact h.frame,
    hrd.trans h.rd, hwr.trans h.wr⟩
  have : r ≠ r₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₀
    rcases hr₀ with rfl | rfl
    · exact fun e => h1 (e ▸ t_layer.2)
    · exact h4
  exact (hg r this).trans (h.regs r h1 h2 h3 h4)

/-- A pair of rounds. -/
theorem KaInv.pair_ok {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {i c : Nat} {W : BitVec 64 × BitVec 64}
    (h : KaInv s₀ KL KR (2 * i) i c W s) (hi : i < 3) :
    ∃ s', runBlock isa pairPlain s = some s' ∧
      KaInv s₀ KL KR (2 * i + 2) i c (pair (sigE (2 * i)) (sigE (2 * i + 1)) W) s' := by
  obtain ⟨-, -, hW, hA, hB, -, hK, hS⟩ := kaKb_slots
  obtain ⟨s', e, ctx', kp', regs', x0', w1, w2, keep', frame', rd', wr'⟩ :=
    pairPlain_ok h.ctx (by rw [h.base]; exact h.ent) (by omega) (by rw [h.x0, h.base]) h.w.1 h.w.2
  have hr : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → s'.gpr r = s.gpr r := regs'
  have hk : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k ∨ k = kaSlot ∨ k = kaSlot + 1 ∨
      k = kbSlot ∨ k = kbSlot + 1) → slotW s' k = slotW s k := fun k h1 h2 h3 =>
    keep' k h1 h2 (by omega) (by omega)
  refine ⟨s', e, ⟨ctx', (hr _ (by decide) (by decide) (by decide)).trans h.base,
    by rw [h.base] at kp'; exact kp',
    x0'.trans h.x0, (hr _ (by decide) (by decide) (by decide)).trans h.cnt, ⟨w1, w2⟩,
    fun hi => (h.ka hi).congr (hk _ (by omega) (by omega) (by omega)) (hk _ (by omega) (by omega) (by omega)),
    fun hi => (h.kb hi).congr (hk _ (by omega) (by omega) (by omega)) (hk _ (by omega) (by omega) (by omega)),
    fun k h1 h2 h3 => (hk k h1 h2 (by omega)).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans (by rw [h.base] at frame'; exact frame'), rd'.trans h.rd, wr'.trans h.wr⟩⟩

/-- `KL ^ KR` to the running value's slots, `x4 := 3`, `x0` at them. -/
theorem kaPrefix_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    ∃ s', runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ ([.movz .x .x4 3 0, movR .x0 sb,
      .addImm .x .x0 .x0 (8 * wSlot)] : List Instr)) s₀ = some s' ∧
      KaInv s₀ KL KR 0 0 3 (kaW KL KR 0) s' := by
  obtain ⟨hl, hr, hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, mv₁, w₁, -⟩ := copyW_ok (w := wSlot) (x := klSlot) hp.ctx.scr (by omega) (by omega)
    (by omega) (by omega) hp.kl
  have hscr₁ : (⟨s₁.gpr sb, 8 * slots⟩ : Region) ∈ s₁.wr := by
    rw [mv₁.regs _ (by decide) (by decide), mv₁.wr]; exact hp.ctx.scr
  obtain ⟨s₂, e₂, mv₂, w₂, -⟩ := xorW_ok hscr₁ (by omega) (by omega) w₁
    (hp.kr.congr (mv₁.keep _ (by omega) (Or.inl (by omega))) (mv₁.keep _ (by omega) (Or.inl (by omega))))
  have mv := mv₁.trans mv₂
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := movz_ok s₂ .x4 (v := 3) (by decide)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .x0 sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .x0 .x0 (imm := 8 * wSlot) (by decide)
  have hg : ∀ r, r ≠ .x4 → r ≠ .x0 → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by rw [o₅ r h2, o₄ r h2, o₃ r h1]
  have hb : s₅.gpr sb = s₀.gpr sb := by rw [hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]
  have hs : ∀ k, slotW s₅ k = slotW s₂ k := slotW_eq_of (by rw [m₅, m₄, m₃]) (hg _ (by decide) (by decide))
  refine ⟨s₅, ?_, ⟨hp.ctx.of_slots hb (by rw [wr₅, wr₄, wr₃, mv.wr])
      (fun k hk => by rw [hs, mv.keep k (by omega) (Or.inl (by omega))]), hb, ?_, ?_,
    (o₅ _ (by decide)).trans ((o₄ _ (by decide)).trans c₃), w₂.congr (hs _) (hs _),
    fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun k _ h2 h3 => by rw [hs, mv.keep k h2 h3],
    fun r h1 _ h3 h4 => by
      rw [hg r h4 h3, mv.regs r (fun e => h1 (e ▸ t_layer.1)) (fun e => h1 (e ▸ t_layer.2))], ?_,
    by rw [rd₅, rd₄, rd₃, mv.rd], by rw [wr₅, wr₄, wr₃, mv.wr]⟩⟩
  · rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.movz .x .x4 3 0, movR .x0 sb, .addImm .x .x0 .x0 (8 * wSlot)] : List Instr) =
        [.movz .x .x4 (BitVec.ofNat 16 3) 0] ++ ([movR .x0 sb] ++ [.addImm .x .x0 .x0 (8 * wSlot)]) from rfl,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅]
  · rw [AtEntry, hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]; exact hp.kp
  · rw [r₅, r₄, o₃ _ (by decide), mv.regs _ (by decide) (by decide)]
  · rw [m₅, m₄, m₃]; exact mv.frame

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
  obtain ⟨s₁, e₁, h₁⟩ := hI.pair_ok hi
  -- `t1 := x4 >>> 1`.
  let s₂ := s₁.write .x t1 (s₁.gpr .x4 >>> 1)
  have e₂ : runBlock isa [lsrI t1 .x4 1] s₁ = some s₂ := by
    simp only [lsrI, runBlock_cons, runStep_some, runBlock_nil, exec_lsr_x (show 1 < 64 by decide), read_x']; rfl
  have t₂ : s₂.gpr t1 = BitVec.ofNat 64 (3 - i) >>> 1 := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, h₁.cnt]
  have h₂ := h₁.regs1 (s' := s₂) (r₀ := t1) (by simp) (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl rfl rfl
    ((RegUpd.gpr_write_of_ne s₁ .x (s₁.gpr .x4 >>> 1) (show Reg.x4 ≠ t1 by decide)).trans h₁.cnt)
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (Q := KaInv s₀ KL KR (2 * i + 2) (i + 1) (3 - i) (kaW KL KR (i + 1))) ?_
    fun s₃ h₃ => ?_)
  · have ht : (s₂.gpr t1 == 0) = decide (2 ≤ i) := by
      rw [t₂]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;> decide
    refine WP.ite (decide (i ≤ 1)) ((eval_nonzero s₂ t1).trans (by rw [ht]; by_cases h : i ≤ 1 <;> simp [h] <;> omega))
      (fun ht => ?_) (fun hf => ?_)
    · have hi1 : i ≤ 1 := by simpa using ht
      obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t1 .x4 (imm := 3) (by decide)
      have h₃ := h₂.regs1 (r₀ := t1) (by simp) o₃ m₃ rd₃ wr₃ (by rw [o₃ _ (by decide)]; exact h₂.cnt)
      have hz : (s₃.gpr t1 == 0) = decide (i = 0) := by
        rw [r₃, h₂.cnt]
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> decide
      refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
      refine WP.ite (decide (i = 0)) ((eval_zero s₃ t1).trans (by rw [hz])) (fun h0 => ?_) (fun h0 => ?_)
      · obtain rfl : i = 0 := by simpa using h0
        obtain ⟨s₄, e₄, mv₄, w₄, -⟩ := xorW_ok h₃.ctx.scr (by omega) (by omega) h₃.w (h₃.kl hp)
        exact WP.of_runBlock ⟨s₄, e₄, h₃.move mv₄ w₄ (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))⟩
      · obtain rfl : i = 1 := by simp at h0; omega
        obtain ⟨s₄, e₄, mv₄, w₄, o₄⟩ := copyW_ok (w := kaSlot) (x := wSlot) h₃.ctx.scr (by omega) (by omega)
          (by omega) (by omega) h₃.w
        have hscr₄ : (⟨s₄.gpr sb, 8 * slots⟩ : Region) ∈ s₄.wr := by
          rw [mv₄.regs _ (by decide) (by decide), mv₄.wr]; exact h₃.ctx.scr
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
  · obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ .x4 .x4 (imm := 1) (by decide)
    have hsub : s₃.gpr .x4 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (3 - (i + 1)) := by
      rw [h₃.cnt, VG.Offset.ofNat_sub_ofNat (by omega), show 3 - i - 1 = 3 - (i + 1) by omega]
    have h₄ := h₃.regs1 (r₀ := .x4) (by simp) o₄ m₄ rd₄ wr₄ (by rw [c₄, hsub])
    have hz : (s₄.gpr .x4 == 0) = decide (3 - (i + 1) = 0) := by
      rw [c₄, hsub, ofNat_beq_zero (by omega)]
    refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
    by_cases hl : i + 1 = 3
    · obtain rfl : i = 2 := by omega
      exact .inl ⟨(eval_nonzero s₄ .x4).trans (by rw [hz]; rfl), h₄⟩
    · exact .inr ⟨(eval_nonzero s₄ .x4).trans (by rw [hz]; simp; omega), 3 - (i + 1), by omega, i + 1, rfl,
        by omega, by rw [Nat.mul_add, Nat.mul_one]; exact h₄⟩

end VG.Proof.Camellia.AArch64
