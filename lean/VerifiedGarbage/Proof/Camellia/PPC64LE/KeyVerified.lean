module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Core
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyPair
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Camellia.PPC64LE.Group
import VerifiedGarbage.Proof.Camellia.PPC64LE.Crypt8
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyChecks2
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Prologue
import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyStore
import VerifiedGarbage.Proof.Camellia.PPC64LE.Keys
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.PPC64LE.KeyContract
public import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Camellia.PPC64LE.ExpandKey`, which only this module used -/

section

/-! ### `Camellia.PPC64LE.KeySetup`, which only this module used -/

section

/-! ### `Camellia.PPC64LE.KaKb`, which only this module used -/

section

/-!
# `KA` and `KB` on PPC64LE

As on x86-64: `kaKb_wp`: from the halves of `KL` and `KR` as words in their
slots, the loop of three pairs of rounds (`pairPlain_ok`), with the XORs and
copies between them on the plain words (`xorWords_ok`, `copyWords_ok`),
leaves the halves of `KA` and `KB` in theirs (`Spec.Camellia.kakb`, by
`kakb_halves`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 kp movR ldS stS xorR shrI)
open VG.Proof.Camellia (HalfRel WordRel pair hiW loW)

/-! ## Moving words between slots -/

theorem slotW_eq_of {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr sb = s.gpr sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [slotW, hm, hb]

theorem scr_in {s : State} {b : Addr} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < slots) :
    InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨_, hscr, by rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < slots) :
    Frame [⟨b, 8 * slots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.sub_base _ (by rw [slots_eq]; omega_arith))

/-- `ldr d, [sb, #8 k]`. -/
theorem ldS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [ldS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ldMask_ok (by rw [slots_eq] at hk; omega_arith) (inRd this) rfl

/-- `str r, [sb, #8 k]`. -/
theorem stS_slot {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ⟨_, stS_ok s r (by rw [slots_eq] at hk; omega_arith) this, by rw [hb], rfl, rfl, rfl⟩

theorem eor_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [xorR d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n ^^^ s.gpr m), by
    simp only [xorR, runBlock_cons, runStep_some, runBlock_nil, exec_logic],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `copyWords w x`: the two words at slot `x` to slot `w`. -/
theorem copyWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x else if k = w + 1 then slotW s (x + 1) else slotW s k) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_slot (k := w) t0 hb₁ (by rw [wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = b := by rw [g₂, hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (k := x + 1) t0 hb₂ (by rw [wr₂, wr₁]; exact hscr) hx
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w + 1) t0 hb₃ (by rw [wr₃, wr₂, wr₁]; exact hscr) hw
  obtain h₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ (hb₁.trans hb.symm)
  obtain h₂ : ∀ k < slots, slotW s₂ k = if k = w then slotW s x else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₂, hb₁]) g₂ hk (by omega_arith), a₁, h₁]
  obtain h₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of m₃ (hb₃.trans hb₂.symm)
  refine ⟨s₄, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show copyWords w x = [ldS t0 x] ++ ([stS w t0] ++ ([ldS t0 (x + 1)] ++ [stS (w + 1) t0]))
      from rfl, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [slotW_store (by rw [m₄, hb₃]) g₄ hk hw, a₃, h₂ (x + 1) hx, ite_eq_right hxw, h₃, h₂ k hk]
    exact ite_swap2 _ _ _
  · rw [g₄, o₃ r hr, g₂, o₁ r hr]
  · rw [m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega_arith)).trans (frame_slot _ hw)

/-- `xorWords w x`: the two words at slot `x` XORed into those at slot `w`. -/
theorem xorWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (xorWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x ^^^ slotW s w
        else if k = w + 1 then slotW s (x + 1) ^^^ slotW s (w + 1) else slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := x) t0 hb hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (k := w) t1 hb₁ (by rw [wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ t0 t0 t1
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stS_slot (k := w) t0 hb₃ (by rw [wr₃, wr₂, wr₁]; exact hscr) (by omega_arith)
  obtain hb₄ : s₄.gpr sb = b := by rw [g₄, hb₃]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅⟩ := ldS_ok (k := x + 1) t0 hb₄
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact hscr) hx
  obtain hb₅ : s₅.gpr sb = b := by rw [o₅ _ (by decide), hb₄]
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := ldS_ok (k := w + 1) t1 hb₅
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hw
  obtain hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), hb₅]
  obtain ⟨s₇, e₇, a₇, o₇, m₇, rd₇, wr₇⟩ := eor_ok s₆ t0 t0 t1
  obtain hb₇ : s₇.gpr sb = b := by rw [o₇ _ (by decide), hb₆]
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_slot (k := w + 1) t0 hb₇
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hscr) hw
  obtain h₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by
    rw [slotW_eq_of m₃ (hb₃.trans hb₂.symm), slotW_eq_of m₂ (hb₂.trans hb₁.symm),
      slotW_eq_of m₁ (hb₁.trans hb.symm)]
  obtain v₃ : s₃.gpr t0 = slotW s x ^^^ slotW s w := by
    rw [a₃, o₂ _ (by decide), a₁, a₂, slotW_eq_of m₁ (hb₁.trans hb.symm)]
  obtain h₄ : ∀ k < slots, slotW s₄ k = if k = w then slotW s x ^^^ slotW s w else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ hk (by omega_arith), v₃, h₃]
  obtain h₆ : ∀ k, slotW s₆ k = slotW s₄ k := fun k => by
    rw [slotW_eq_of m₆ (hb₆.trans hb₅.symm), slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  obtain v₇ : s₇.gpr t0 = slotW s₄ (x + 1) ^^^ slotW s₄ (w + 1) := by
    rw [a₇, o₆ _ (by decide), a₅, a₆, slotW_eq_of m₅ (hb₅.trans hb₄.symm)]
  refine ⟨s₈, ?_, fun k hk => ?_, fun r h0 h1 => ?_, ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show xorWords w x = [ldS t0 x] ++ ([ldS t1 w] ++ ([xorR t0 t0 t1] ++ ([stS w t0] ++
      ([ldS t0 (x + 1)] ++ ([ldS t1 (w + 1)] ++ ([xorR t0 t0 t1] ++ [stS (w + 1) t0])))))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some,
      runBlock_append', e₇, Option.bind_some, e₈]
  · rw [slotW_store (by rw [m₈, hb₇]) g₈ hk hw, v₇, slotW_eq_of m₇ (hb₇.trans hb₆.symm), h₆,
      h₄ (x + 1) hx, ite_eq_right hxw, h₄ (w + 1) hw, ite_eq_right (show ¬ w + 1 = w by omega_arith), h₄ k hk]
    exact ite_swap2 _ _ _
  · rw [g₈, o₇ r h0, o₆ r h1, o₅ r h0, g₄, o₃ r h0, o₂ r h1, o₁ r h0]
  · rw [m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega_arith)).trans (frame_slot _ hw)

/-! ## The values -/


/-- The words at slots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 386 ∧ krSlot = 388 ∧ wSlot = 390 ∧ kaSlot = 392 ∧ kbSlot = 394 ∧
    endSlot = 368 ∧ keySlot = 96 ∧ slots = 414 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KeyCtx` moves to a state with the same base, regions and slots below the table's end. -/
theorem KeyCtx.of_slots {s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hb : s'.gpr sb = s.gpr sb) (hwr : s'.wr = s.wr)
    (hs : ∀ k < endSlot, slotW s' k = slotW s k) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine hp.transfer hb hwr (fun kv hkv => ?_) (fun i hi j hj => ?_)
  · have := mask_lt hkv
    rw [hs _ (by rw [endSlot_eq]; rw [keySlot_eq] at this; omega_arith)]; exact hp.masks kv hkv
  · have := hs (keySlot + 8 * i + j) (by rw [endSlot_eq, keySlot_eq]; omega_arith)
    simp only [slotW, hb, wordAddr] at this
    simp only [entryW]
    rw [show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega_arith]
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
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := copyWords_ok rfl hscr (by omega_arith) hx hxw
  obtain hk : ∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), fun r h0 _ => g r h0, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs w (by omega_arith), ite_eq_left rfl]; exact hv.1
  · rw [hs (w + 1) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left rfl]; exact hv.2

/-- `xorWords w x`, for `w` the running value's slot. -/
theorem xorW_ok {s : State} {x : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hx : x + 1 < slots) (hxw : x + 1 ≠ wSlot)
    {u v : BitVec 64 × BitVec 64} (hu : WordsAt s wSlot u) (hv : WordsAt s x v) :
    ∃ s', runBlock isa (xorWords wSlot x) s = some s' ∧ MoveOk s s' ∧
      WordsAt s' wSlot (u.1 ^^^ v.1, u.2 ^^^ v.2) ∧
      (∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k) := by
  obtain ⟨-, -, hW, -, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := xorWords_ok rfl hscr (by omega_arith) hx hxw
  obtain hk : ∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs wSlot (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]; exact hu.1.xor hv.1
  · rw [hs (wSlot + 1) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]
    exact hu.2.xor hv.2

/-! ## The loop -/

/-- What `kaKb` needs: the table of `Sigma1 … Sigma6`, `kp` at its start, and `KL` and `KR` in their slots. -/
structure KaPre (s₀ : State) (KL KR : BitVec 64 × BitVec 64) : Prop where
  ctx : KeyCtx s₀ 6 sigE
  kp : AtEntry s₀ (s₀.gpr sb) 0
  kl : WordsAt s₀ klSlot KL
  kr : WordsAt s₀ krSlot KR

/-- The loop's state: `kp` at entry `m`, `i` pairs done (`KA` after two,
`KB` after three), `c` in `r7`, the running value `W`. -/
structure KaInv (s₀ : State) (KL KR : BitVec 64 × BitVec 64) (m i c : Nat) (W : BitVec 64 × BitVec 64)
    (s : State) : Prop where
  ctx : KeyCtx s 6 sigE
  base : s.gpr sb = s₀.gpr sb
  ent : AtEntry s (s₀.gpr sb) m
  r3 : s.gpr .r3 = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot)
  cnt : s.gpr .r7 = BitVec.ofNat 64 c
  w : WordsAt s wSlot W
  ka : 2 ≤ i → WordsAt s kaSlot (kaD2 KL KR)
  kb : 3 ≤ i → WordsAt s kbSlot (kaD3 KL KR)
  keep : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k) → slotW s k = slotW s₀ k
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .r3 → r ≠ .r7 → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem KaInv.kl {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s klSlot KL := by
  obtain ⟨hl, -, hW, -, -, -, hK, hS⟩ := kaKb_slots
  exact hp.kl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem KaInv.kr {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s krSlot KR := by
  obtain ⟨-, hr, hW, -, -, -, hK, hS⟩ := kaKb_slots
  exact hp.kr.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem t_layer : t0 ∈ sboxWrites ∧ t1 ∈ sboxWrites := by decide

theorem KaInv.move {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i i' c : Nat}
    {W W' : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hm : MoveOk s s')
    (hw : WordsAt s' wSlot W') (hka : 2 ≤ i' → WordsAt s' kaSlot (kaD2 KL KR))
    (hkb : 3 ≤ i' → WordsAt s' kbSlot (kaD3 KL KR)) : KaInv s₀ KL KR m i' c W' s' := by
  obtain ⟨-, -, hW, -, -, hE, -, hS⟩ := kaKb_slots
  obtain hg : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    hm.regs r (fun e => hr (e ▸ t_layer.1)) (fun e => hr (e ▸ t_layer.2))
  refine ⟨h.ctx.of_slots (hg _ (by decide)) hm.wr
      (fun k hk => hm.keep k (by omega_arith) (Or.inl (by omega_arith))), (hg _ (by decide)).trans h.base,
    by rw [AtEntry, hg _ (by decide)]; exact h.ent,
    (hg _ (by decide)).trans h.r3, (hg _ (by decide)).trans h.cnt, hw, hka, hkb,
    fun k h1 h2 h3 => (hm.keep k h2 h3).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hg r h1).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans ?_, hm.rd.trans h.rd, hm.wr.trans h.wr⟩
  have := hm.frame
  rw [h.base] at this
  exact this

/-- A step that writes only `r` (not `sb`, `kp` or `r3`). -/
theorem KaInv.regs1 {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i c c' : Nat}
    {W : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) {r₀ : Reg} (hr₀ : r₀ ∈ [t1, Reg.r7])
    (hg : ∀ r, r ≠ r₀ → s'.gpr r = s.gpr r)
    (hmem : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hc : s'.gpr .r7 = BitVec.ofNat 64 c') : KaInv s₀ KL KR m i c' W s' := by
  obtain hn : sb ≠ r₀ ∧ kp ≠ r₀ ∧ Reg.r3 ≠ r₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr₀; rcases hr₀ with rfl | rfl <;> decide
  obtain hs : ∀ k, slotW s' k = slotW s k := slotW_eq_of hmem (hg _ hn.1)
  refine ⟨h.ctx.of_slots (hg _ hn.1) hwr (fun k _ => hs k),
    (hg _ hn.1).trans h.base, by rw [AtEntry, hg _ hn.2.1]; exact h.ent, (hg _ hn.2.2).trans h.r3, hc,
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
  obtain ⟨s', e, ctx', kp', regs', r3', w1, w2, keep', frame', rd', wr'⟩ :=
    pairPlain_ok h.ctx (by rw [h.base]; exact h.ent) (by omega_arith) (by rw [h.r3, h.base]) h.w.1 h.w.2
  have hr : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .r3 → s'.gpr r = s.gpr r := regs'
  obtain hk : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k ∨ k = kaSlot ∨ k = kaSlot + 1 ∨
      k = kbSlot ∨ k = kbSlot + 1) → slotW s' k = slotW s k := fun k h1 h2 h3 =>
    keep' k h1 h2 (by omega_arith) (by omega_arith)
  refine ⟨s', e, ⟨ctx', (hr _ (by decide) (by decide) (by decide)).trans h.base,
    by rw [h.base] at kp'; exact kp',
    r3'.trans h.r3, (hr _ (by decide) (by decide) (by decide)).trans h.cnt, ⟨w1, w2⟩,
    fun hi => (h.ka hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun hi => (h.kb hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun k h1 h2 h3 => (hk k h1 h2 (by omega_arith)).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans (by rw [h.base] at frame'; exact frame'), rd'.trans h.rd, wr'.trans h.wr⟩⟩

/-- `KL ^ KR` to the running value's slots, `r7 := 3`, `r3` at them. -/
theorem kaPrefix_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    ∃ s', runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ ([.li .r7 3,
      .addi .r3 sb (8 * wSlot)] : List Instr)) s₀ = some s' ∧
      KaInv s₀ KL KR 0 0 3 (kaW KL KR 0) s' := by
  obtain ⟨hl, hr, hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, mv₁, w₁, -⟩ := copyW_ok (w := wSlot) (x := klSlot) hp.ctx.scr (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hp.kl
  obtain hscr₁ : (⟨s₁.gpr sb, 8 * slots⟩ : Region) ∈ s₁.wr := by
    rw [mv₁.regs _ (by decide) (by decide), mv₁.wr]; exact hp.ctx.scr
  obtain ⟨s₂, e₂, mv₂, w₂, -⟩ := xorW_ok hscr₁ (by omega_arith) (by omega_arith) w₁
    (hp.kr.congr (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))) (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))))
  obtain mv := mv₁.trans mv₂
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := li_ok s₂ .r7 (v := 3) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₃ .r3 sb (imm := 8 * wSlot) (by decide)
  obtain hg : ∀ r, r ≠ .r7 → r ≠ .r3 → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by rw [o₅ r h2, o₃ r h1]
  obtain hb : s₅.gpr sb = s₀.gpr sb := by rw [hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]
  obtain hs : ∀ k, slotW s₅ k = slotW s₂ k := slotW_eq_of (by rw [m₅, m₃]) (hg _ (by decide) (by decide))
  refine ⟨s₅, ?_, ⟨hp.ctx.of_slots hb (by rw [wr₅, wr₃, mv.wr])
      (fun k hk => by rw [hs, mv.keep k (by omega_arith) (Or.inl (by omega_arith))]), hb, ?_, ?_,
    (o₅ _ (by decide)).trans c₃, w₂.congr (hs _) (hs _),
    fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun k _ h2 h3 => by rw [hs, mv.keep k h2 h3],
    fun r h1 _ h3 h4 => by
      rw [hg r h4 h3, mv.regs r (fun e => h1 (e ▸ t_layer.1)) (fun e => h1 (e ▸ t_layer.2))], ?_,
    by rw [rd₅, rd₃, mv.rd], by rw [wr₅, wr₃, mv.wr]⟩⟩
  · rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.li .r7 3, .addi .r3 sb (8 * wSlot)] : List Instr) =
        [.li .r7 3] ++ [.addi .r3 sb (8 * wSlot)] from rfl,
      runBlock_append', e₃, Option.bind_some, e₅]
  · rw [AtEntry, hg _ (by decide) (by decide), mv.regs _ (by decide) (by decide)]; exact hp.kp
  · rw [r₅, o₃ _ (by decide), mv.regs _ (by decide) (by decide)]
  · rw [m₅, m₃]; exact mv.frame

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
  -- `t1 := r7 >>> 1`.
  let s₂ := s₁.write t1 (s₁.gpr .r7 >>> 1)
  obtain e₂ : runBlock isa [shrI t1 .r7 1] s₁ = some s₂ := by
    simp only [shrI, runBlock_cons, runStep_some, runBlock_nil, exec_lsr_d (show 1 < 64 by decide)]; rfl
  obtain t₂ : s₂.gpr t1 = BitVec.ofNat 64 (3 - i) >>> 1 := by
    rw [RegUpd.gpr_write_self, h₁.cnt]
  obtain h₂ := h₁.regs1 (s' := s₂) (r₀ := t1) (by simp) (fun r hr => RegUpd.gpr_write_of_ne _ _ hr) rfl rfl rfl
    ((RegUpd.gpr_write_of_ne s₁ (s₁.gpr .r7 >>> 1) (show Reg.r7 ≠ t1 by decide)).trans h₁.cnt)
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  refine WP.seq (WP.mono (Q := KaInv s₀ KL KR (2 * i + 2) (i + 1) (3 - i) (kaW KL KR (i + 1))) ?_
    fun s₃ h₃ => ?_)
  · have ht : (s₂.gpr t1 == 0) = decide (2 ≤ i) := by
      rw [t₂]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl <;> decide
    refine WP.ite (decide (i ≤ 1)) ((eval_nonzero s₂ t1).trans (by rw [ht]; by_cases h : i ≤ 1 <;> simp [h] <;> omega_arith))
      (fun ht => ?_) (fun hf => ?_)
    · have hi1 : i ≤ 1 := by simpa using ht
      obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t1 .r7 (imm := 3) (by decide)
      obtain h₃ := h₂.regs1 (r₀ := t1) (by simp) o₃ m₃ rd₃ wr₃ (by rw [o₃ _ (by decide)]; exact h₂.cnt)
      obtain hz : (s₃.gpr t1 == 0) = decide (i = 0) := by
        rw [r₃, h₂.cnt]
        rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl <;> decide
      refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
      refine WP.ite (decide (i = 0)) ((eval_zero s₃ t1).trans (by rw [hz])) (fun h0 => ?_) (fun h0 => ?_)
      · obtain rfl : i = 0 := by simpa using h0
        obtain ⟨s₄, e₄, mv₄, w₄, -⟩ := xorW_ok h₃.ctx.scr (by omega_arith) (by omega_arith) h₃.w (h₃.kl hp)
        exact WP.of_runBlock ⟨s₄, e₄, h₃.move mv₄ w₄ (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))⟩
      · obtain rfl : i = 1 := by simp at h0; omega_arith
        obtain ⟨s₄, e₄, mv₄, w₄, o₄⟩ := copyW_ok (w := kaSlot) (x := wSlot) h₃.ctx.scr (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith) h₃.w
        obtain hscr₄ : (⟨s₄.gpr sb, 8 * slots⟩ : Region) ∈ s₄.wr := by
          rw [mv₄.regs _ (by decide) (by decide), mv₄.wr]; exact h₃.ctx.scr
        obtain ⟨s₅, e₅, mv₅, w₅, o₅⟩ := xorW_ok hscr₄ (by omega_arith) (by omega_arith)
          (h₃.w.congr (o₄ _ (by omega_arith) (by omega_arith) (by omega_arith)) (o₄ _ (by omega_arith) (by omega_arith) (by omega_arith)))
          ((h₃.kr hp).congr (mv₄.keep _ (by omega_arith) (Or.inl (by omega_arith)))
            (mv₄.keep _ (by omega_arith) (Or.inl (by omega_arith))))
        refine WP.of_runBlock ⟨s₅, by rw [runBlock_append', e₄, Option.bind_some, e₅],
          h₃.move (mv₄.trans mv₅) w₅ (fun _ => w₄.congr (o₅ _ (by omega_arith) (by omega_arith) (by omega_arith))
            (o₅ _ (by omega_arith) (by omega_arith) (by omega_arith))) (fun h => absurd h (by decide))⟩
    · obtain rfl : i = 2 := by simp at hf; omega_arith
      obtain ⟨s₃, e₃, mv₃, w₃, o₃⟩ := copyW_ok (w := kbSlot) (x := wSlot) h₂.ctx.scr (by omega_arith) (by omega_arith)
        (by omega_arith) (by omega_arith) h₂.w
      exact WP.of_runBlock ⟨s₃, e₃, h₂.move mv₃
        (h₂.w.congr (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith)) (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith)))
        (fun _ => (h₂.ka (by decide)).congr (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith))
          (o₃ _ (by omega_arith) (by omega_arith) (by omega_arith))) (fun _ => w₃)⟩
  · obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := subI_ok s₃ .r7 .r7 (imm := 1) (by decide)
    obtain hsub : s₃.gpr .r7 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (3 - (i + 1)) := by
      rw [h₃.cnt, VG.Offset.ofNat_sub_ofNat (by omega_arith), show 3 - i - 1 = 3 - (i + 1) by omega_arith]
    obtain h₄ := h₃.regs1 (r₀ := .r7) (by simp) o₄ m₄ rd₄ wr₄ (by rw [c₄, hsub])
    obtain hz : (s₄.gpr .r7 == 0) = decide (3 - (i + 1) = 0) := by
      rw [c₄, hsub, ofNat_beq_zero (by omega_arith)]
    refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
    by_cases hl : i + 1 = 3
    · obtain rfl : i = 2 := by omega_arith
      exact .inl ⟨(eval_nonzero s₄ .r7).trans (by rw [hz]; rfl), h₄⟩
    · exact .inr ⟨(eval_nonzero s₄ .r7).trans (by rw [hz]; simp; omega_arith), 3 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, by rw [Nat.mul_add, Nat.mul_one]; exact h₄⟩

end VG.Proof.Camellia.PPC64LE

end

end


/-!
# The Camellia key schedule on PPC64LE: its parts

As on x86-64: the prologue saves the callee-saved registers, sets the masks
and stores the planes of `Sigma1 … Sigma6` as a table of subkeys
(`ekPrologue_ok`, the planes by evaluation: `sigmaStores_ok`);
`loadKey_wp` loads `KL` and `KR` into their slots, and `loadValues_ok`
byte-swaps the four values into registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Bitslice VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 t2 u7 kp movR ldS stS xorR imm64)
open VG.Proof.Camellia (HalfRel pair hiW loW pos)

/-! ## Single instructions -/

/-- `str r, [sb, #8 k]`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k < slots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk, rd, wr⟩
  · rw [slotW_store m g hk hk, ite_eq_left rfl]
  · rw [slotW_store m g hj hk, ite_eq_right hjk]

/-- `ld d, k(r)`. -/
theorem ldAt_ok (s : State) (d r : Reg) {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 k) 8) (hr0 : r ≠ .r0 := by decide) :
    ∃ s', runBlock isa [.load .d d r k] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ld hk hr hr0],
    RegUpd.gpr_write_self _ _ _,
    fun r' h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩

/-! ## The table of `Sigma1 … Sigma6` -/

theorem sigmaStores_dst :
    (sigmas.all fun x => (sigmaStores x).all fun i => dstOf i == none || dstOf i == some t0) = true := by
  decide +kernel

/-- The stores of `sigmaOne x`: the planes of `x` to the entry at `kp`. -/
theorem sigmaStores_ok {x : BitVec 64} (hx : x ∈ sigmas) (s : State) {r : Region} (hr : r ∈ s.wr) {off : Nat}
    (hb : s.gpr kp = r.base + BitVec.ofNat 64 off) (hlen : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa (sigmaStores x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (wordAddr (s.gpr kp) j) 64 = keyPlane x j) ∧
      Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧ (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain hchk := List.all_eq_true.mp sigma_checks x hx
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain hok : Ok sigCfg s := Ok.of_off hr hb hlen hn rfl
  obtain hrel : Rel (LaneRel 1 0) sigCfg (fun _ => none) (linEnvG [] [] []) s := by
    refine ⟨fun r a h => ?_, fun k a _ h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩ <;>
      simp [linEnvG] at h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  obtain hdst := List.all_eq_true.mp sigmaStores_dst x hx
  obtain hall : ∀ r, r ≠ t0 → ((sigmaStores x).all fun i => dstOf i != some r) = true := fun r hr => by
    refine List.all_eq_true.mpr fun i hi => ?_
    obtain h := List.all_eq_true.mp hdst i hi
    rcases hd : dstOf i with _ | d
    · rfl
    · rw [hd] at h
      obtain hdt : d = t0 := by simpa using h
      subst hdt
      simpa using fun h' => hr h'.symm
  refine ⟨s', hs', fun j hj => ?_, ?_, fun r hr => p.other r (by simp [hall r hr]), p.rd, p.wr⟩
  · have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at h
    obtain hr := p.rel.slot j _ (by simp only [sigCfg]; omega_arith) h
    simp only [sigCfg] at hr
    have hb' : s'.gpr kp = s.gpr kp := p.base
    rw [hb'] at hr
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [hr.2 q hq, par_zero, Bool.xor_false]
    rfl
  · have := p.frame
    simpa [slotRegion, sigCfg] using this

/-- `sigmaOne x`: the planes of `x` to the entry at `kp`, and `kp` to the next. -/
theorem sigmaOne_ok {x : BitVec 64} (hx : x ∈ sigmas) (s : State) {r : Region} (hr : r ∈ s.wr) {off : Nat}
    (hb : s.gpr kp = r.base + BitVec.ofNat 64 off) (hlen : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr kp, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigmaStores_ok hx s hr hb hlen hn
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 64 (by decide)
  refine ⟨s₂, by rw [sigmaOne_eq, runBlock_append', e₁, Option.bind_some, e₂], fun j hj => by
      rw [m₂]; exact v₁ j hj,
    by rw [a₂, g₁ _ (by decide)], by rw [m₂]; exact f₁, fun r h1 h2 => by rw [o₂ r h2, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (∀ x ∈ xs, x ∈ sigmas) → (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ t0 → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hxs, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok (hxs x List.mem_cons_self) s hscr
      (off := 8 * keySlot + 64 * e) hr (by simp only [slots_eq]; omega_arith) (by show 8 * slots < 2 ^ 64; rw [slots_eq]; decide)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit xs (e + 1) s₁
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith])
      (by omega_arith)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega_arith],
      fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW, Nat.add_zero, ← addr_add, ← hr]
        refine (f'.readW (Region.contains_self _ _) (fun r hr' => ?_) (by decide)).trans (v₁ j hj)
        simp only [List.mem_singleton] at hr'; subst hr'
        rw [hr, addr_add]
        exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
      · rw [show e + (i + 1) = e + 1 + i by omega_arith]
        exact v' i (by simpa using hi) j hj
    · refine Frame.trans (f₁.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩)
        (f'.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr'; subst hr')
      · rw [hr]; exact Region.sub_prefix (by simp only [List.length_cons]; omega_arith)
      · exact VG.Offset.sub b (by omega_arith) (by simp only [List.length_cons]; omega_arith)

/-- The table's entries `0 … 5` hold `Sigma1 … Sigma6`, as `KeyCtx` reads them. -/
theorem sigmas_rel {m : Mem} {b : Addr}
    (h : ∀ i < 6, ∀ j < 8, entryW m b i j = keyPlane (sigmas.getD i 0) j) :
    ∀ i < 6, HalfRel (entryW m b i) fun _ => sigE i := fun i hi bb hb c hc j hj => by
  rw [h i hi j hj]; exact sigma_planes _ hb hc hj

/-! ## Loading the key -/

/-- A step that writes only `t0`, `t1` and `u7`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Pure.refl (s : State) : Pure s s := ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem Pure.trans {s₁ s₂ s₃ : State} (h₁ : Pure s₁ s₂) (h₂ : Pure s₂ s₃) : Pure s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, fun r h0 h1 h2 => (h₂.regs r h0 h1 h2).trans (h₁.regs r h0 h1 h2), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem Pure.of1 {s s' : State} {d : Reg} (hd : d = t0 ∨ d = t1 ∨ d = u7) (hm : s'.mem = s.mem)
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pure s s' :=
  ⟨hm, fun r h0 h1 h2 => hg r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), hrd, hwr⟩

/-- A store of `t0` to slot `k`. -/
structure StOk (s s' : State) (k : Nat) : Prop where
  val : slotW s' k = s.gpr t0
  keep : ∀ j < slots, j ≠ k → slotW s' j = slotW s j
  gpr : s'.gpr = s.gpr
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stOk {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [stS k t0] s = some s' ∧ StOk s s' k := by
  obtain ⟨s', e, v, kp, g, f, rd, wr⟩ := st_ok (k := k) t0 hscr hk
  exact ⟨s', e, v, kp, g, f, rd, wr⟩

/-- `KR`'s words stored: what each branch of `loadKey` leaves. -/
structure KrPost (s s' : State) (V : BitVec 64 × BitVec 64) : Prop where
  kr : WordsAt s' krSlot V
  keep : ∀ k < slots, k ≠ krSlot → k ≠ krSlot + 1 → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem StOk.frame' {s₀ s s' : State} {k : Nat} (hf : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem)
    (hb : s.gpr sb = s₀.gpr sb) (h : StOk s s' k) : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s'.mem :=
  hf.trans (by have := h.frame; rw [hb] at this; exact this)

theorem krPost_of {s s₁ s₂ s₃ s₄ : State} {V : BitVec 64 × BitVec 64}
    (p₁ : Pure s s₁) (h₂ : StOk s₁ s₂ krSlot) (p₃ : Pure s₂ s₃) (h₄ : StOk s₃ s₄ (krSlot + 1))
    (hu : WordOf (s₁.gpr t0) V.1) (hv : WordOf (s₃.gpr t0) V.2) : KrPost s s₄ V := by
  obtain ⟨-, hr, -, -, -, -, -, hS⟩ := kaKb_slots
  obtain hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, hb₁]
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (by rw [p₃.regs _ (by decide) (by decide) (by decide)])
  obtain f₂ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₂.mem :=
    StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  refine ⟨⟨?_, ?_⟩, fun k hk h1 h2 => by rw [h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁],
    fun r h0 h1 h2 => by rw [h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2],
    StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄,
    by rw [h₄.rd, p₃.rd, h₂.rd, p₁.rd], by rw [h₄.wr, p₃.wr, h₂.wr, p₁.wr]⟩
  · rw [h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val]; exact hu
  · rw [h₄.val]; exact hv

theorem allOnes_eq : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .r3, len⟩ : Region) ∈ s.rd) (hfit : (s.gpr .r3).toNat + len ≤ 2 ^ 64)
    (hks : Region.Disjoint ⟨s.gpr .r3, len⟩ ⟨s.gpr sb, 8 * slots⟩)
    (hlen : s.gpr .r6 = BitVec.ofNat 64 len) (hl : len = 16 ∨ len = 24 ∨ len = 32) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).1,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).1) ∧
      WordsAt s' krSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).2,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).2) ∧
      (∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl', hr', -, -, -, -, -, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .r3) hl
  -- The key's words, read after stores to the scratch buffer.
  obtain hkw : ∀ {t : State}, t.rd = s.rd → t.gpr .r3 = s.gpr .r3 →
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem t.mem → ∀ d, d % 8 = 0 → d + 8 ≤ len →
      ∃ t', runBlock isa [.load .d t0 .r3 d] t = some t' ∧ Pure t t' ∧
        WordOf (t'.gpr t0) (Spec.Camellia.wordAt s.mem (s.gpr .r3 + BitVec.ofNat 64 d)) := by
    intro t hrd hdi hf d hd8 hd
    obtain ⟨t', e, a, o, m, rd, wr⟩ := ldAt_ok t t0 .r3 (k := d) ⟨hd8, by omega_arith⟩ (by
      rw [hrd, hdi]; exact ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    refine ⟨t', e, Pure.of1 (Or.inl rfl) m o rd wr, ?_⟩
    rw [a, hdi, hf.readW (r := ⟨s.gpr .r3 + BitVec.ofNat 64 d, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hks.sub_left (VG.Offset.sub_base _ (by omega_arith))) (by decide)]
    exact wordOf_readW _ _
  obtain hz : s.gpr .r3 + BitVec.ofNat 64 0 = s.gpr .r3 := by simp
  obtain hscrOf : ∀ {t : State}, t.gpr sb = s.gpr sb → t.wr = s.wr → (⟨t.gpr sb, 8 * slots⟩ : Region) ∈ t.wr :=
    fun hb hw => by rw [hb, hw]; exact hscr
  obtain hn : ∀ {r : Reg}, r = t0 ∨ r = t1 ∨ r = u7 → sb ≠ r ∧ Reg.r3 ≠ r ∧ Reg.r6 ≠ r := by
    intro r hr; rcases hr with rfl | rfl | rfl <;> decide
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, p₁, w₁⟩ := hkw rfl rfl (Frame.refl _ _) 0 (by decide) (by omega_arith)
  obtain hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, h₂⟩ := stOk (k := klSlot) (hscrOf hb₁ p₁.wr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [h₂.gpr, hb₁]
  obtain f₂ := StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  obtain ⟨s₃, e₃, p₃, w₃⟩ := hkw (by rw [h₂.rd, p₁.rd]) (by rw [h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide)])
    f₂ 8 (by decide) (by omega_arith)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), hb₂]
  obtain ⟨s₄, e₄, h₄⟩ := stOk (k := klSlot + 1) (hscrOf hb₃ (by rw [p₃.wr, h₂.wr, p₁.wr])) (by omega_arith)
  obtain f₄ := StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ t1 .r6 (imm := 16) (by decide)
  obtain p₅ : Pure s₄ s₅ := Pure.of1 (Or.inr (Or.inl rfl)) m₅ g₅ rd₅ wr₅
  obtain hg₅ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s₅.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [p₅.regs r h0 h1 h2, h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2]
  obtain hb₅ : s₅.gpr sb = s.gpr sb := hg₅ _ (by decide) (by decide) (by decide)
  obtain hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := slotW_eq_of m₅ (p₅.regs _ (by decide) (by decide) (by decide))
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (p₃.regs _ (by decide) (by decide) (by decide))
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  obtain f₅ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₅.mem := by rw [m₅]; exact f₄
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, h₄.rd, p₃.rd, h₂.rd, p₁.rd]
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, h₄.wr, p₃.wr, h₂.wr, p₁.wr]
  obtain hkl : WordsAt s₅ klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).1,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).1) := by
    refine ⟨?_, ?_⟩
    · rw [hs₅, h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val, hK0, ← hz]; exact w₁
    · rw [hs₅, h₄.val, hK1]; exact w₃
  obtain hother : ∀ k < slots, k ≠ klSlot → k ≠ klSlot + 1 → slotW s₅ k = slotW s k := fun k hk h1 h2 => by
    rw [hs₅, h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁]
  obtain hr6 : s₄.gpr .r6 = BitVec.ofNat 64 len := by
    rw [h₄.gpr, p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide),
      hlen]
  obtain hz₅ : (s₅.gpr t1 == 0) = decide (len = 16) := by
    rw [z₅, hr6, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([.load .d t0 .r3 0, stS klSlot t0, .load .d t0 .r3 8, stS (klSlot + 1) t0,
        .subi t1 .r6 16] : List Instr) =
        [.load .d t0 .r3 0] ++ ([stS klSlot t0] ++ ([.load .d t0 .r3 8] ++
          ([stS (klSlot + 1) t0] ++ [.subi t1 .r6 16]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩)
  refine WP.mono (Q := fun s' => KrPost s₅ s' (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).2,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .r3) len)).2))
    (WP.ite (decide (len = 16)) ((eval_zero s₅ t1).trans (by rw [hz₅])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => ?_
  · -- A key of 16 bytes: `KR = 0`.
    obtain h16 : len = 16 := by simpa using h16
    obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := li_ok s₅ t0 (v := 0) (by decide)
    obtain p₆ : Pure s₅ s₆ := Pure.of1 (Or.inl rfl) m₆ o₆ rd₆ wr₆
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf (by rw [o₆ _ (by decide), hb₅]) (by rw [wr₆, wr₅']))
      (by omega_arith)
    obtain ⟨s₈, e₈, h₈⟩ := stOk (k := krSlot + 1)
      (hscrOf (by rw [h₇.gpr, o₆ _ (by decide), hb₅]) (by rw [h₇.wr, wr₆, wr₅'])) (by omega_arith)
    refine WP.of_runBlock ⟨s₈, by
      rw [show ([.li t0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
          [.li t0 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈],
      krPost_of p₆ h₇ (Pure.refl _) h₈ (by rw [a₆, hK2, ite_eq_left h16]; exact WordOf.zero)
        (by rw [h₇.gpr, a₆, hK3, ite_eq_left h16]; exact WordOf.zero)⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₆, e₆, p₆, w₆⟩ := hkw (by rw [rd₅']) (hg₅ _ (by decide) (by decide) (by decide)) f₅ 16
      (by decide) (by omega_arith)
    obtain hb₆ : s₆.gpr sb = s.gpr sb := by rw [p₆.regs _ (by decide) (by decide) (by decide), hb₅]
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf hb₆ (by rw [p₆.wr, wr₅'])) (by omega_arith)
    obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₇ t1 .r6 (imm := 24) (by decide)
    obtain p₈ : Pure s₇ s₈ := Pure.of1 (Or.inr (Or.inl rfl)) m₈ g₈ rd₈ wr₈
    obtain hb₈ : s₈.gpr sb = s.gpr sb := by rw [p₈.regs _ (by decide) (by decide) (by decide), h₇.gpr, hb₆]
    obtain f₈ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₈.mem := by
      rw [m₈]; exact StOk.frame' (by rw [p₆.mem]; exact f₅) hb₆ h₇
    obtain hz₈ : (s₈.gpr t1 == 0) = decide (len = 24) := by
      rw [z₈, h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide), hg₅ _ (by decide) (by decide) (by decide),
        hlen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    refine WP.seq (WP.of_runBlock ⟨s₈, by
      rw [show ([.load .d t0 .r3 16, stS krSlot t0, .subi t1 .r6 24] : List Instr) =
          [.load .d t0 .r3 16] ++ ([stS krSlot t0] ++ [.subi t1 .r6 24]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
    refine WP.ite (decide (len = 24)) ((eval_zero s₈ t1).trans (by rw [hz₈])) (fun h24 => ?_) (fun h24 => ?_)
    · have h24 : len = 24 := by simpa using h24
      obtain ⟨s₉a, e₉a, a₉a, o₉a, m₉a, rd₉a, wr₉a⟩ := li_ok s₈ u7 (v := 0) (by decide)
      obtain ⟨s₉b, e₉b, a₉b, o₉b, m₉b, rd₉b, wr₉b⟩ := subI_ok s₉a u7 u7 (imm := 1) (by decide)
      obtain ⟨s₉, e₉, a₉, o₉, m₉, rd₉, wr₉⟩ := eor_ok s₉b t0 t0 u7
      obtain p₉ : Pure s₈ s₉ := (Pure.of1 (Or.inr (Or.inr rfl)) m₉a o₉a rd₉a wr₉a).trans
        ((Pure.of1 (Or.inr (Or.inr rfl)) m₉b o₉b rd₉b wr₉b).trans (Pure.of1 (Or.inl rfl) m₉ o₉ rd₉ wr₉))
      obtain hnot : s₉.gpr t0 = ~~~ s₈.gpr t0 := by
        rw [a₉, o₉b _ (by decide), o₉a _ (by decide), a₉b, a₉a, allOnes_eq, BitVec.xor_allOnes]
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.li u7 0, .subi u7 u7 1, xorR t0 t0 u7, stS (krSlot + 1) t0] : List Instr) =
            [.li u7 0] ++ ([.subi u7 u7 1] ++ ([xorR t0 t0 u7] ++
              [stS (krSlot + 1) t0])) from rfl,
          runBlock_append', e₉a, Option.bind_some, runBlock_append', e₉b, Option.bind_some,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hnot, g₈ _ (by decide), h₇.gpr, hK3, ite_eq_right h16, ite_eq_left h24]; exact w₆.not)⟩
    · have h24 : len ≠ 24 := by simpa using h24
      obtain ⟨s₉, e₉, p₉, w₉⟩ := hkw (by rw [rd₈, h₇.rd, p₆.rd, rd₅'])
        (by rw [g₈ _ (by decide), h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide),
          hg₅ _ (by decide) (by decide) (by decide)]) f₈ 24 (by decide) (by omega_arith)
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.load .d t0 .r3 24, stS (krSlot + 1) t0] : List Instr) =
            [.load .d t0 .r3 24] ++ [stS (krSlot + 1) t0] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact w₉)⟩
  · -- Both.
    refine ⟨hkl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)),
      h.kr, fun k hk h1 => by rw [h.keep k hk (by omega_arith) (by omega_arith), hother k hk (by omega_arith) (by omega_arith)],
      fun r h0 h1 h2 => by rw [h.regs r h0 h1 h2, hg₅ r h0 h1 h2],
      f₅.trans (by have := h.frame; rw [hb₅] at this; exact this),
      by rw [h.rd, rd₅'], by rw [h.wr, wr₅']⟩

/-! ## The schedule's bytes -/

/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  [.li .r12 (8 * k), .loadRev .d (hiReg v) sb .r12, .li .r12 (8 * (k + 1)), .loadRev .d (loReg v) sb .r12]

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v ∧
    hiReg v ≠ .r12 ∧ loReg v ≠ .r12 := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

/-- `li r12, 8 k; ldbrx t, sb, r12`: slot `k`, byte-swapped. -/
theorem ldRev_ok {s : State} {k : Nat} (t : Reg)
    (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [.li .r12 (8 * k), .loadRev .d t sb .r12] s = some s' ∧ s'.gpr t = rev64 (slotW s k) ∧
      (∀ r, r ≠ t → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .r12 (BitVec.ofNat 64 (8 * k))
  obtain h12 : s₁.gpr .r12 = BitVec.ofNat 64 (8 * k) := RegUpd.gpr_write_self _ _ _
  obtain hsb : s₁.gpr sb = s.gpr sb := RegUpd.gpr_write_of_ne _ _ (by decide)
  obtain hin : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr sb + s₁.gpr .r12) 8 := by
    rw [hsb, h12]; obtain ⟨r, hr, hc⟩ := scr_in hscr hk; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine ⟨s₁.write t (rev64 (s₁.mem.readW (s₁.gpr sb + s₁.gpr .r12) 64)), ?_, ?_, fun r h1 h2 => ?_, rfl, rfl,
    rfl⟩
  · simp only [runBlock_cons, exec_li (show 8 * k < 2 ^ 15 by rw [slots_eq] at hk; omega_arith), runStep_some]
    rw [exec_loadRev_d (by decide) hin, runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_write_self, hsb, h12]; rfl
  · rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < slots) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = rev64 (slotW s k) ∧
      s'.gpr (loReg v) = rev64 (slotW s (k + 1)) ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, -, n3, n4, -⟩ := regs_lt4 hv
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := ldRev_ok (k := k) (hiReg v) hscr (by omega_arith)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := o₂ _ n1.symm (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := ldRev_ok (s := s₂) (k := k + 1) (loReg v)
    (by rw [hb₂, wr₂]; exact hscr) hk
  refine ⟨s₄, ?_, ?_, ?_, fun r h1 h2 h3 => by rw [o₄ r h2 h3, o₂ r h1 h3],
    by rw [m₄, m₂], by rw [rd₄, rd₂], by rw [wr₄, wr₂]⟩
  · rw [lvChunk, show ([.li .r12 (8 * k), .loadRev .d (hiReg v) sb .r12, .li .r12 (8 * (k + 1)),
        .loadRev .d (loReg v) sb .r12] : List Instr) = [.li .r12 (8 * k), .loadRev .d (hiReg v) sb .r12] ++
          [.li .r12 (8 * (k + 1)), .loadRev .d (loReg v) sb .r12] from rfl,
      runBlock_append', e₂, Option.bind_some, e₄]
  · rw [o₄ _ n3 n4, a₂]
  · rw [a₄, slotW_eq_of m₂ hb₂]

/-- `loadValues`: the four values' halves, byte-swapped into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide) (by decide)
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide) (by decide), hb₁]
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide) (by decide), hb₂]
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith)
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr h12 => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3 h12, o₃ r a2 b2 h12, o₂ r a1 b1 h12, o₁ r a0 b0 h12],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · have w := hw 0 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide) (by decide) (by decide), h₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide) (by decide) (by decide), l₁]
      exact rev_of_wordOf w.2
  · have w := hw 1 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), h₂, hs₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide) (by decide), o₃ _ (by decide) (by decide) (by decide), l₂, hs₁]
      exact rev_of_wordOf w.2
  · have w := hw 2 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide) (by decide), h₃, hs₂]; exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide) (by decide), l₃, hs₂]; exact rev_of_wordOf w.2
  · have w := hw 3 (by decide)
    exact ⟨by rw [h₄, hs₃]; exact rev_of_wordOf w.1, by rw [l₄, hs₃]; exact rev_of_wordOf w.2⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) (hi : i < 18) : sreg i ≠ sb ∧ sreg i ≠ .r6 := by
  revert i; decide

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .r6 = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∃ s, runBlock isa ([movR sb .r6, movR .r6 .r4] ++ saveRegs ++ setSlots layerMasks ++ tableSetup ++
        sigmas.flatMap sigmaOne) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r6 = s₀.gpr .r4 ∧
      (∀ r, r ≠ sb → r ≠ .r6 → r ≠ t0 → r ≠ kp → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * tailSlot⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  have hS := slots_eq
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .r6
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₁a .r6 .r4
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), r₁a, hb]
  obtain g₁ : ∀ r, r ≠ sb → r ≠ .r6 → s₁.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁ r h2, o₁a r h1]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁, wr₁a]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) (by rw [wr₂, wr₁, wr₁a]; exact hw)
    (by rw [g₂, hb₁])
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, k₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₃
  obtain hb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), hb₃]
  obtain ⟨s₅, e₅, v₅, f₅, r₅, g₅, rd₅, wr₅⟩ := sigmaList_ok hfit sigmas 0 s₄ (fun x hx => hx)
    (by rw [wr₄, wr₃, wr₂, wr₁, wr₁a]; exact hw)
    (by rw [k₄, hb₃]; simp) (by decide)
  obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide), hb₄]
  -- The slots outside the table keep their values.
  obtain hs₅ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₅ k = slotW s₃ k := fun k h1 h2 => by
    simp only [slotW, hb₅, hb₃]
    rw [← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  refine ⟨s₅, ?_, hb₅, ?_, fun r h1 h2 h3 h4 => ?_, fun i hi => ?_, fun kv hkv => ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁, rd₁a],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁, wr₁a]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      show ([movR sb .r6, movR .r6 .r4] : List Instr) = [movR sb .r6] ++ [movR .r6 .r4] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · rw [g₅ _ (by decide) (by decide), o₄ _ (by decide), g₃ _ (by decide), g₂, r₁, o₁a _ (by decide)]
  · rw [g₅ r h3 h4, o₄ r h4, g₃ r h3, g₂, g₁ r h1 h2]
  · have n := sreg_ne' i hi
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from g₁ _ n.1 n.2] at this
    rw [← this]
    obtain h' := hs₅ (savedSlot + i) (Or.inr (by omega_arith)) (by omega_arith)
    simp only [slotW, hb₅, hb₃] at h'
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega_arith) (by omega_arith)
  · have := mask_lt hkv
    rw [hs₅ _ (Or.inl this) (by omega_arith)]
    exact v₃ kv hkv
  · have := v₅ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    exact this
  · have f₂' : Frame [⟨b, 8 * tailSlot⟩] s₁.mem s₂.mem := f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base b (by omega_arith)⟩
    obtain f₃' : Frame [⟨b, 8 * tailSlot⟩] s₂.mem s₃.mem := f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_arith)⟩
    obtain f₅' : Frame [⟨b, 8 * tailSlot⟩] s₄.mem s₅.mem := f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega_arith)⟩
    rw [m₁, m₁a] at f₂'
    rw [m₄] at f₅'
    exact f₂'.trans (f₃'.trans f₅')

end VG.Proof.Camellia.PPC64LE

end

end


/-!
# The Camellia key schedule on PPC64LE: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyPPC64LE`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` byte-swaps them into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (hiW loW)

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega_using []]

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ .r12 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hS : s₈.gpr .r5 = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
    (hks : ks.length ≤ 34)
    (hg : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := storeSubkeys_ok ks hv 0 s₈ (fun i hi => ⟨_, hw, by
    rw [hS]; exact VG.Offset.contains_base _ (by omega_using [hks, hi]) (by omega_using [hks, hi])⟩) (by omega_using [hks])
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
  · rw [hlen, schedule_of_stores (H := fun v => s₈.gpr (hiReg v)) (L := fun v => s₈.gpr (loReg v)) hv hg (by rw [← hS]; exact b₉), Spec.Camellia.scheduleBytes,
      Proof.Camellia.scheduleWords_expandKey, ← hks']
  · rw [hS] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega_using [hks])⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyPPC64LE.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyPPC64LE.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  obtain hwB : (⟨s₀.gpr .r6, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hwS : (⟨s₀.gpr .r5, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hrK : (⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r6₁, g₁, sv₁, mk₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .r6) rfl hwB fitB
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain r3₁ : s₁.gpr .r3 = s₀.gpr .r3 := g₁ _ (by decide) (by decide) (by decide) (by decide)
  obtain r5₁ : s₁.gpr .r5 = s₀.gpr .r5 := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  obtain hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .r3) (s₀.gpr .r4).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat := by
    rw [r3₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .r3, (s₀.gpr .r4).toNat⟩)
      (fun r hr => ?_) (by simp only; omega_using []) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega_using [hS, ht]))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .r4).toNat) (s := s₁) (by rw [b₁, wr₁]; exact hwB)
    (by rw [r3₁, rd₁]; exact hrK) (by rw [r3₁]; exact fitK) (by rw [r3₁, b₁]; exact dKB)
    (by rw [r6₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hlen) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, sl₂, g₂, f₂, rd₂, wr₂⟩ := h₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat = key at kl₂ kr₂
  obtain hb₂ : s₂.gpr sb = s₀.gpr .r6 := by rw [g₂ _ (by decide) (by decide) (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := o₄
  obtain hb₄ : s₄.gpr sb = s₀.gpr .r6 := by rw [hg₄ _ (by decide), hb₂]
  obtain hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of m₄ (hg₄ _ (by decide))
  obtain r5₄ : s₄.gpr .r5 = s₀.gpr .r5 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide) (by decide), r5₁]
  obtain r6₄ : s₄.gpr .r6 = s₀.gpr .r4 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide) (by decide), r6₁]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₂, wr₁]
  obtain hlow : ∀ k < klSlot, slotW s₄ k = slotW s₁ k := fun k hk => by
    rw [hs₄, sl₂ k (by omega_using [hl', hS, hk]) (Or.inl hk)]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  obtain hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · rw [hb₄]; exact fitB
    · have := mask_lt hkv
      rw [hlow _ (by omega_using [hl', hK, this])]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega_using [hl', hK, hi, hj]), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [AtEntry, a₄, hb₄, hb₂]; simp
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  obtain hb₅ : s₅.gpr sb = s₀.gpr .r6 := h₅.base.trans hb₄
  obtain wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  obtain hscr₅ : (⟨s₀.gpr .r6, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
  -- The values, byte-swapped into registers.
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₅) (by rw [hb₅]; exact hscr₅)
    [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2] (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
      · exact h₅.kl hpre
      · exact h₅.kr hpre
      · have := h₅.ka (by decide); rw [hKA'] at this; exact this
      · have := h₅.kb (by decide); rw [hKB'] at this; exact this)
  obtain hnv : ∀ r : Reg, r ∈ [sb, Reg.r5, Reg.r6] → ∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v := by decide
  obtain hb₆ : s₆.gpr sb = s₀.gpr .r6 := by rw [o₆ _ (hnv _ (by simp)) (by decide), hb₅]
  obtain r6₅ : s₅.gpr .r6 = s₀.gpr .r4 := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), r6₄]
  -- The key's length.
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₆ t0 .r6 (imm := 16) (by decide)
  obtain hz₈ : (s₈.gpr t0 == 0) = decide ((s₀.gpr .r4).toNat = 16) := by
    rw [z₈, o₆ _ (hnv _ (by simp)) (by decide), r6₅]
    conv => lhs; rw [show s₀.gpr .r4 = BitVec.ofNat 64 (s₀.gpr .r4).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega_using []) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₆, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  obtain hx2₈ : s₈.gpr .r5 = s₀.gpr .r5 := by
    rw [g₈ _ (by decide), o₆ _ (hnv _ (by simp)) (by decide), h₅.regs _ (by decide) (by decide) (by decide) (by decide), r5₄]
  obtain hwS₈ : (⟨s₀.gpr .r5, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₆, wr₅]; exact hwS
  obtain hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈ _ n1, g₈ _ n3]; exact v₆ v hv
  obtain hklen : key.length = (s₀.gpr .r4).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .r5) (s₀.gpr .r4).toNat key)
    (WP.ite (decide ((s₀.gpr .r4).toNat = 16)) ((eval_zero s₈ t0).trans (by rw [hz₈])) (fun h16 => ?_)
      (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .r4).toNat = 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega_using []) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .r4).toNat ≠ 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  obtain hb₉ : s₉.gpr sb = s₀.gpr .r6 := by rw [h₉.regs _ (by decide) (by decide) (by decide), g₈ _ (by decide), hb₆]
  obtain hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 18 →
      s₉.mem.readW (wordAddr (s₀.gpr .r6) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .r6) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_using [hS, hsv, h2]))).symm) (by decide)]
    have := h₅.keep k (by omega_using [hK, hsv, h1]) (by omega_using [hS, hsv, h2]) (Or.inl (by omega_using [hW, hsv, h2]))
    rw [hs₄, sl₂ k (by omega_using [hS, hsv, h2]) (Or.inl (by omega_using [hl', hsv, h2]))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, -, m₁₀, -, -⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .r6)
    (by rw [h₉.wr, wr₈, wr₆, wr₅]; exact hwB) hb₉ (fun i hi => by
      rw [hSB _ (by omega_using []) (by omega_using [hi])]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, rg₁₀, ?_⟩
  show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .r5) _ = _
  rw [hkey, m₁₀, ← h₉.bytes]

end VG.Proof.Camellia.PPC64LE

end

end


/-!
# The Camellia key schedule on PPC64LE meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time (`expandKey_ct`). `expandKey_framed` runs it with its working space on
the stack, zeroed on return: 3344 bytes, for the 414 words of the scratch
buffer.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE

/-- The registers the key schedule writes. -/
def expandKeyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem expandKey_correct (s : State) (hs : expandKeyPPC64LE.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyPPC64LE.post s s' := by
  obtain hn : expandKey.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hk.gpr (by decide)
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])
  · exact h₁ 9 (by omega_using [])
  · exact h₁ 10 (by omega_using [])
  · exact h₁ 11 (by omega_using [])
  · exact h₁ 12 (by omega_using [])
  · exact h₁ 13 (by omega_using [])
  · exact h₁ 14 (by omega_using [])
  · exact h₁ 15 (by omega_using [])
  · exact h₁ 16 (by omega_using [])
  · exact h₁ 17 (by omega_using [])

/-- A state satisfying the precondition (a key of 16 bytes). -/
def expandKeySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩, ⟨0x4000, 8 * 414⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Camellia.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyPPC64LE,
      abi, argRegs, slots, tailSlot, savedSlot, endSlot, keySlot] [expandKeySat]
      using expandKeySat)

/-- A state satisfying the key schedule's precondition: a key of 16 bytes at
`0x1000`, the schedule at `0x3000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract abi 3344).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, abi, argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3344 .r6 414 expandKey)
      (Spec.Camellia.expandKeyContract abi 3344) :=
  Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 414) (pre := Spec.Camellia.expandKeyPre abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3344) (words := 414) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.expandKeyPre_local _) (Proof.Camellia.expandKeyPost_local _)
    (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.PPC64LE
