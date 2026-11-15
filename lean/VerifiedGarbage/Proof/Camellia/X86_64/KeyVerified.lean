module

public import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.X86_64.Core
import VerifiedGarbage.Proof.Camellia.X86_64.KeyPair
import VerifiedGarbage.Proof.Camellia.X86_64.Group
import VerifiedGarbage.Proof.Camellia.X86_64.Crypt8
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Camellia.X86_64.Prologue
import VerifiedGarbage.Proof.Camellia.X86_64.KeyStore
import VerifiedGarbage.Proof.Camellia.X86_64.KeyWords
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.X86_64.KeyContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Camellia.X86_64.ExpandKey`, which only this module used -/

section

/-! ### `Camellia.X86_64.KeySetup`, which only this module used -/

section

/-! ### `Camellia.X86_64.KaKb`, which only this module used -/

section

/-!
# `KA` and `KB` on x86-64

`kaKb_wp`: from the halves of `KL` and `KR` as words in their slots, the
loop of three pairs of rounds (`pairPlain_ok`), with the XORs and copies
between them on the plain words (`xorWords_ok`, `copyWords_ok`), leaves the
halves of `KA` and `KB` in theirs (`Spec.Camellia.kakb`, by `kakb_halves`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
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
  ⟨_, hscr, by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < slots) :
    Frame [⟨b, 8 * slots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.sub_base _ (by rw [slots_eq]; omega_arith))

/-- `copyWords w x`: the two words at slot `x` to slot `w`. -/
theorem copyWords_ok {s : State} {b : Addr} {w x : Nat} (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hw : w + 1 < slots) (hx : x + 1 < slots) (hxw : x + 1 ≠ w) :
    ∃ s', runBlock isa (copyWords w x) s = some s' ∧
      (∀ k < slots, slotW s' k = if k = w then slotW s x else if k = w + 1 then slotW s (x + 1) else slotW s k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := x) .rax hb (inRd (scr_in hscr (by omega_arith)))
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stReg_ok (k := w) .rax hb₁ (scr_in (by rw [wr₁]; exact hscr) (by omega_arith))
  have hb₂ : s₂.gpr sb = b := by rw [g₂, hb₁]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := movS_ok (k := x + 1) .rax hb₂
    (inRd (scr_in (by rw [wr₂, wr₁]; exact hscr) hx))
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), hb₂]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (k := w + 1) .rax hb₃
    (scr_in (by rw [wr₃, wr₂, wr₁]; exact hscr) hw)
  have h₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ (hb₁.trans hb.symm)
  have h₂ : ∀ k < slots, slotW s₂ k = if k = w then slotW s x else slotW s k := fun k hk => by
    rw [slotW_store (by rw [m₂, hb₁]) g₂ hk (by omega_arith), a₁, h₁]
  have h₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of m₃ (hb₃.trans hb₂.symm)
  refine ⟨s₄, ?_, fun k hk => ?_, fun r hr => ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [show copyWords w x = [movS .rax x] ++ ([st w .rax] ++ ([movS .rax (x + 1)] ++ [st (w + 1) .rax]))
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
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨b, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := x) .rax hb (inRd (scr_in hscr (by omega_arith)))
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := xorS_ok (k := w) .rax hb₁
    (inRd (scr_in (by rw [wr₁]; exact hscr) (by omega_arith)))
  have hb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), hb₁]
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stReg_ok (k := w) .rax hb₂
    (scr_in (by rw [wr₂, wr₁]; exact hscr) (by omega_arith))
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
    rw [slotW_store (by rw [m₃, hb₂]) g₃ hk (by omega_arith), a₂, a₁, h₂,
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
      h₃ (x + 1) hx, ite_eq_right hxw, h₃ (w + 1) hw, ite_eq_right (show ¬ w + 1 = w by omega_arith), h₅, h₃ k hk]
    exact ite_swap2 _ _ _
  · rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    exact (frame_slot _ (by omega_arith)).trans (frame_slot _ hw)

/-! ## The values -/


/-- The words at slots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 377 ∧ krSlot = 379 ∧ wSlot = 381 ∧ kaSlot = 383 ∧ kbSlot = 385 ∧
    endSlot = 368 ∧ keySlot = 96 ∧ slots = 401 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `KeyCtx` moves to a state with the same base, blocks, regions and slots below the table's end. -/
theorem KeyCtx.of_slots {s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hb : s'.gpr sb = s.gpr sb) (hdx : s'.gpr .rdx = s.gpr .rdx) (hwr : s'.wr = s.wr)
    (hs : ∀ k < endSlot, slotW s' k = slotW s k) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine hp.transfer hb hdx hwr (fun kv hkv => ?_) (fun i hi j hj => ?_)
  · have := mask_lt hkv
    rw [hs _ (by rw [endSlot_eq]; rw [keySlot_eq] at this; omega_arith)]; exact hp.masks kv hkv
  · have := hs (keySlot + 8 * i + j) (by rw [endSlot_eq, keySlot_eq]; omega_arith)
    simp only [slotW, hb, wordAddr] at this
    simp only [entryW]
    rw [show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega_arith]
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
  obtain ⟨s', e, hs, g, f, rd, wr⟩ := copyWords_ok rfl hscr (by omega_arith) hx hxw
  have hk : ∀ k < slots, k ≠ w → k ≠ w + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
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
  have hk : ∀ k < slots, k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k := fun k hk h1 h2 => by
    rw [hs k hk, ite_eq_right h1, ite_eq_right h2]
  refine ⟨s', e, ⟨fun k hkk h => hk k hkk (by omega_arith) (by omega_arith), g, f, rd, wr⟩, ⟨?_, ?_⟩, hk⟩
  · rw [hs wSlot (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]; exact hu.1.xor hv.1
  · rw [hs (wSlot + 1) (by omega_arith), ite_eq_right (by omega_arith), ite_eq_left rfl, BitVec.xor_comm]
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
  exact hp.kl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem KaInv.kr {s₀ s : State} {KL KR : BitVec 64 × BitVec 64} {m i c : Nat} {W : BitVec 64 × BitVec 64}
    (hp : KaPre s₀ KL KR) (h : KaInv s₀ KL KR m i c W s) : WordsAt s krSlot KR := by
  obtain ⟨-, hr, hW, -, -, -, hK, hS⟩ := kaKb_slots
  exact hp.kr.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem KaInv.move {s₀ s s' : State} {KL KR : BitVec 64 × BitVec 64} {m i i' c : Nat}
    {W W' : BitVec 64 × BitVec 64} (h : KaInv s₀ KL KR m i c W s) (hm : MoveOk s s')
    (hw : WordsAt s' wSlot W') (hka : 2 ≤ i' → WordsAt s' kaSlot (kaD2 KL KR))
    (hkb : 3 ≤ i' → WordsAt s' kbSlot (kaD3 KL KR)) : KaInv s₀ KL KR m i' c W' s' := by
  obtain ⟨-, -, hW, -, -, hE, -, hS⟩ := kaKb_slots
  refine ⟨h.ctx.of_slots (hm.regs _ (by decide)) (hm.regs _ (by decide)) hm.wr
      (fun k hk => hm.keep k (by omega_arith) (Or.inl (by omega_arith))), (hm.regs _ (by decide)).trans h.base,
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
    pairPlain_ok h.ctx (by rw [h.rdx, h.base]; exact hp.sx) (by rw [h.base]; exact h.ent) (by omega_arith)
      (by rw [h.rdi, h.base]) h.w.1 h.w.2
  have hr : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s'.gpr r = s.gpr r := regs'
  have hk : ∀ k, keySlot ≤ k → k < slots → (k < wSlot ∨ kbSlot + 2 ≤ k ∨ k = kaSlot ∨ k = kaSlot + 1 ∨
      k = kbSlot ∨ k = kbSlot + 1) → slotW s' k = slotW s k := fun k h1 h2 h3 =>
    keep' k h1 h2 (by omega_arith) (by omega_arith)
  refine ⟨s', e, ⟨ctx', (hr _ (by decide) (by decide) (by decide)).trans h.base,
    (hr _ (by decide) (by decide) (by decide)).trans h.rdx, by rw [h.base] at kp'; exact kp',
    rdi'.trans h.rdi, (hr _ (by decide) (by decide) (by decide)).trans h.cnt, ⟨w1, w2⟩,
    fun hi => (h.ka hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun hi => (h.kb hi).congr (hk _ (by omega_arith) (by omega_arith) (by omega_arith)) (hk _ (by omega_arith) (by omega_arith) (by omega_arith)),
    fun k h1 h2 h3 => (hk k h1 h2 (by omega_arith)).trans (h.keep k h1 h2 h3),
    fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.regs r h1 h2 h3 h4),
    h.frame.trans (by rw [h.base, h.rdx] at frame'; exact frame'), rd'.trans h.rd, wr'.trans h.wr⟩⟩

/-- `KL ^ KR` to the running value's slots, `r8 := 3`, `rdi` at them. -/
theorem kaPrefix_ok {s₀ : State} {KL KR : BitVec 64 × BitVec 64} (hp : KaPre s₀ KL KR) :
    ∃ s', runBlock isa (copyWords wSlot klSlot ++ xorWords wSlot krSlot ++ ([.movImm64 .r8 3, movR .rdi sb,
      .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * wSlot)))] : List Instr)) s₀ = some s' ∧
      KaInv s₀ KL KR 0 0 3 (kaW KL KR 0) s' := by
  obtain ⟨hl, hr, hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, mv₁, w₁, -⟩ := copyW_ok (w := wSlot) (x := klSlot) hp.ctx.scr (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hp.kl
  have hscr₁ : (⟨s₁.gpr sb, 8 * slots⟩ : Region) ∈ s₁.wr := by
    rw [mv₁.regs _ (by decide), mv₁.wr]; exact hp.ctx.scr
  obtain ⟨s₂, e₂, mv₂, w₂, -⟩ := xorW_ok hscr₁ (by omega_arith) (by omega_arith) w₁
    (hp.kr.congr (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))) (mv₁.keep _ (by omega_arith) (Or.inl (by omega_arith))))
  have mv := mv₁.trans mv₂
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := movImm_ok s₂ .r8 3
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movR_ok s₃ .rdi sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addImm_ok s₄ .rdi (BitVec.ofNat 32 (8 * wSlot))
  have hg : ∀ r, r ≠ .r8 → r ≠ .rdi → s₅.gpr r = s₂.gpr r := fun r h1 h2 => by rw [o₅ r h2, o₄ r h2, o₃ r h1]
  have hb : s₅.gpr sb = s₀.gpr sb := by rw [hg _ (by decide) (by decide), mv.regs _ (by decide)]
  have hs : ∀ k, slotW s₅ k = slotW s₂ k := slotW_eq_of (by rw [m₅, m₄, m₃]) (hg _ (by decide) (by decide))
  refine ⟨s₅, ?_, ⟨hp.ctx.of_slots hb (by rw [hg _ (by decide) (by decide), mv.regs _ (by decide)])
      (by rw [wr₅, wr₄, wr₃, mv.wr]) (fun k hk => by rw [hs, mv.keep k (by omega_arith) (Or.inl (by omega_arith))]), hb,
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
  obtain ⟨s₂, e₂, cf₂, g₂, m₂, rd₂, wr₂⟩ := cmpImm_ok s₁ .r8 2 (v := 3 - i) h₁.cnt (by omega_arith) rfl
  have h₂ := h₁.regs8 (fun r _ => by rw [g₂]) m₂ rd₂ wr₂ (by rw [g₂]; exact h₁.cnt)
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)⟩)
  refine WP.seq (WP.mono (Q := KaInv s₀ KL KR (2 * i + 2) (i + 1) (3 - i) (kaW KL KR (i + 1))) ?_
    fun s₃ h₃ => ?_)
  · refine WP.ite (!decide (3 - i < 2)) (by simp [X86_64.eval, cf₂]) (fun ht => ?_) (fun hf => ?_)
    · have hi1 : i ≤ 1 := by simp at ht; omega_arith
      obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := cmpImmZ_ok s₂ .r8 3
      have h₃ := h₂.regs8 (fun r _ => by rw [g₃]) m₃ rd₃ wr₃ (by rw [g₃]; exact h₂.cnt)
      refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
      refine WP.ite (decide (i = 0)) (by
        show s₃.zf = _
        rw [z₃, h₂.cnt]
        rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl <;> decide) (fun h0 => ?_) (fun h0 => ?_)
      · obtain rfl : i = 0 := by simpa using h0
        obtain ⟨s₄, e₄, mv₄, w₄, -⟩ := xorW_ok h₃.ctx.scr (by omega_arith) (by omega_arith) h₃.w (h₃.kl hp)
        exact WP.of_runBlock ⟨s₄, e₄, h₃.move mv₄ w₄ (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))⟩
      · obtain rfl : i = 1 := by simp at h0; omega_arith
        obtain ⟨s₄, e₄, mv₄, w₄, o₄⟩ := copyW_ok (w := kaSlot) (x := wSlot) h₃.ctx.scr (by omega_arith) (by omega_arith)
          (by omega_arith) (by omega_arith) h₃.w
        have hscr₄ : (⟨s₄.gpr sb, 8 * slots⟩ : Region) ∈ s₄.wr := by
          rw [mv₄.regs _ (by decide), mv₄.wr]; exact h₃.ctx.scr
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
  · obtain ⟨s₄, e₄, c₄, z₄, o₄, m₄, rd₄, wr₄⟩ := subImm_ok s₃ .r8 1
    have hsub : s₃.gpr .r8 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (3 - (i + 1)) := by
      rw [h₃.cnt, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show 3 - i - 1 = 3 - (i + 1) by omega_arith]
    have h₄ := h₃.regs8 o₄ m₄ rd₄ wr₄ (by rw [c₄, hsub])
    have hz : s₄.zf = some (decide (3 - (i + 1) = 0)) := by
      rw [z₄, h₃.cnt, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
      simp only [Option.some.injEq, decide_eq_decide]; omega_arith
    refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
    by_cases hl : i + 1 = 3
    · obtain rfl : i = 2 := by omega_arith
      exact .inl ⟨by simp [X86_64.eval, hz], h₄⟩
    · exact .inr ⟨by simp [X86_64.eval, hz]; omega_arith, 3 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
        by rw [Nat.mul_add, Nat.mul_one]; exact h₄⟩

end VG.Proof.Camellia.X86_64

end

end


/-!
# The Camellia key schedule on x86-64: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyX86_64`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
planes of `Sigma1 … Sigma6` as a table of subkeys (`sigmas_ok`), loads `KL`
and `KR` (`loadKey_wp`), computes `KA` and `KB` (`kaKb_wp`), and stores the
subkeys, halves of their rotations (`storeSubkeys_ok`), before restoring the
registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_ slotAt setMasks)
open VG.Proof.Camellia (HalfRel pair hiW loW)

/-! ## Single instructions -/

/-- `mov [sb + 8 k], r`, as slots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k < slots) :
    ∃ s', runBlock isa [st k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < slots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := stReg_ok (k := k) r rfl (scr_in hscr hk)
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk, rd, wr⟩
  · rw [slotW_store m g hk hk, ite_eq_left rfl]
  · rw [slotW_store m g hj hk, ite_eq_right hjk]

/-- `mov d, [r + k]`. -/
theorem ldAt_ok (s : State) (d r : Reg) (k : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ r k))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat,
    hr, ite_true, Option.map_some]

/-- `mov32 rax, 0`. -/
theorem zeroRax_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .rax (.imm 0)] s = some s' ∧ s'.gpr .rax = 0 ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg .rax ((0 : BitVec 32).setWidth 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32],
    by simp only [RegUpd.gpr_setReg_self]; rfl, fun r' h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h],
    rfl, rfl, rfl⟩

/-- `xor rax, 0xFFFFFFFF`: all its bits flipped. -/
theorem notRax_ok (s : State) :
    ∃ s', runBlock isa [.alu .xor .rax (.imm 0xFFFFFFFF)] s = some s' ∧ s'.gpr .rax = ~~~ s.gpr .rax ∧
      (∀ r', r' ≠ .rax → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
    rw [show (0xFFFFFFFF : BitVec 32).signExtend 64 = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-! ## The table of `Sigma1 … Sigma6` -/

/-- The first `n` stores of `sigmaOne x`. -/
def sigPairs (x : BitVec 64) (n : Nat) : List Instr :=
  (List.range n).flatMap fun j => [.movImm64 .rax (keyPlane x j), .store (slotAt .rsi j) .rax]

theorem sigPairs_ok (x : BitVec 64) : ∀ n ≤ 8, ∀ s : State,
    (∀ j < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8) →
    ∃ s', runBlock isa (sigPairs x n) s = some s' ∧
      (∀ j < n, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      Frame [⟨s.gpr .rsi, 64⟩] s.mem s'.mem ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _ => ⟨s, rfl, fun j hj => absurd hj (by omega_arith), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, hn, s, hw => by
    obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigPairs_ok x n (by omega_arith) s hw
    obtain ⟨s₂, e₂, c₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s₁ .rax (keyPlane x n)
    have hsi : s₂.gpr .rsi = s.gpr .rsi := by rw [o₂ _ (by decide), g₁ _ (by decide)]
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeAt_ok s₂ .rsi (8 * n) .rax
      (by rw [wr₂, wr₁, hsi]; exact hw n (by omega_arith))
    have e₃' : runBlock isa [.store (slotAt .rsi n) .rax] s₂ = some s₃ := e₃
    refine ⟨s₃, ?_, fun j hj => ?_, ?_, fun r hr => by rw [g₃, o₂ r hr, g₁ r hr], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
    · rw [sigPairs, List.range_succ, List.flatMap_append, runBlock_append', ← sigPairs, e₁, Option.bind_some,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        show ([.movImm64 .rax (keyPlane x n), .store (slotAt .rsi n) .rax] : List Instr) =
          [.movImm64 .rax (keyPlane x n)] ++ [.store (slotAt .rsi n) .rax] from rfl,
        runBlock_append', e₂, Option.bind_some, e₃']
    · rw [m₃, hsi]
      by_cases hjn : j = n
      · subst hjn; rw [Mem.readW_writeW_self64, c₂]
      · rw [Mem.readW_writeW_sep (VG.Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m₂,
          v₁ j (by omega_arith)]
    · refine f₁.trans ?_
      rw [m₃, m₂, hsi]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- `sigmaOne x`: the planes of `x` to the entry at `rsi`, and `rsi` to the next. -/
theorem sigmaOne_ok (x : BitVec 64) (s : State)
    (hw : ∀ j < 8, InRegions s.wr (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 8) :
    ∃ s', runBlock isa (sigmaOne x) s = some s' ∧
      (∀ j < 8, s'.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * j)) 64 = keyPlane x j) ∧
      s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 64 ∧ Frame [⟨s.gpr .rsi, 64⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := sigPairs_ok x 8 (Nat.le_refl 8) s hw
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rsi 64
  refine ⟨s₂, by rw [show sigmaOne x = sigPairs x 8 ++ [.alu .add .rsi (.imm 64)] from rfl, runBlock_append',
      e₁, Option.bind_some, e₂], fun j hj => by rw [m₂]; exact v₁ j hj,
    by rw [a₂, g₁ _ (by decide)]; rfl, by rw [m₂]; exact f₁, fun r h1 h2 => by rw [o₂ r h2, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-- Entry `i` of the table at `b`, as an address from `rsi`. -/
theorem entryW_eq (m : Mem) (b : Addr) (i j : Nat) :
    entryW m b i j = m.readW (b + BitVec.ofNat 64 (8 * keySlot + 64 * i) + BitVec.ofNat 64 (8 * j)) 64 := by
  rw [entryW, addr_add]

theorem sigmaList_ok {b : Addr} (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∀ (xs : List (BitVec 64)) (e : Nat) (s : State), (⟨b, 8 * slots⟩ : Region) ∈ s.wr →
      s.gpr .rsi = b + BitVec.ofNat 64 (8 * keySlot + 64 * e) → e + xs.length ≤ 34 →
      ∃ s', runBlock isa (xs.flatMap sigmaOne) s = some s' ∧
        (∀ i < xs.length, ∀ j < 8, entryW s'.mem b (e + i) j = keyPlane (xs.getD i 0) j) ∧
        Frame [⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64 * xs.length⟩] s.mem s'.mem ∧
        s'.gpr .rsi = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + xs.length)) ∧
        (∀ r, r ≠ .rax → r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], e, s, _, hr, _ => ⟨s, rfl, fun i hi => absurd hi (by simp), Frame.refl _ _, by simpa using hr,
      fun _ _ _ => rfl, rfl, rfl⟩
  | x :: xs, e, s, hscr, hr, hl => by
    rw [slots_eq] at hfit
    have hk := keySlot_eq
    simp only [List.length_cons] at hl
    obtain ⟨s₁, e₁, v₁, r₁, f₁, g₁, rd₁, wr₁⟩ := sigmaOne_ok x s (fun j hj => ⟨_, hscr, by
      rw [hr, addr_add]; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega_arith) (by omega_arith)⟩)
    obtain ⟨s', e', v', f', r', g', rd', wr'⟩ := sigmaList_ok hfit xs (e + 1) s₁ (by rw [wr₁]; exact hscr)
      (by rw [r₁, hr, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith])
      (by omega_arith)
    refine ⟨s', by rw [List.flatMap_cons, runBlock_append', e₁, Option.bind_some, e'], fun i hi j hj => ?_,
      ?_, by rw [r', List.length_cons, show e + 1 + xs.length = e + (xs.length + 1) by omega_arith],
      fun r h1 h2 => by rw [g' r h1 h2, g₁ r h1 h2], by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rcases i with _ | i
      · rw [entryW_eq, Nat.add_zero, ← hr]
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

/-- A step that writes only `rax` and the flags. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Pure.refl (s : State) : Pure s s := ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Pure.trans {s₁ s₂ s₃ : State} (h₁ : Pure s₁ s₂) (h₂ : Pure s₂ s₃) : Pure s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, fun r hr => (h₂.regs r hr).trans (h₁.regs r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

/-- A store of `rax` to slot `k`. -/
structure StOk (s s' : State) (k : Nat) : Prop where
  val : slotW s' k = s.gpr .rax
  keep : ∀ j < slots, j ≠ k → slotW s' j = slotW s j
  gpr : s'.gpr = s.gpr
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stOk {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (hk : k < slots) :
    ∃ s', runBlock isa [st k .rax] s = some s' ∧ StOk s s' k := by
  obtain ⟨s', e, v, kp, g, f, rd, wr⟩ := st_ok (k := k) .rax hscr hk
  exact ⟨s', e, v, kp, g, f, rd, wr⟩

/-- `KR`'s words stored: what each branch of `loadKey` leaves. -/
structure KrPost (s s' : State) (V : BitVec 64 × BitVec 64) : Prop where
  kr : WordsAt s' krSlot V
  keep : ∀ k < slots, k ≠ krSlot → k ≠ krSlot + 1 → slotW s' k = slotW s k
  regs : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem StOk.frame' {s₀ s s' : State} {k : Nat} (hf : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s.mem)
    (hb : s.gpr sb = s₀.gpr sb) (h : StOk s s' k) : Frame [⟨s₀.gpr sb, 8 * slots⟩] s₀.mem s'.mem :=
  hf.trans (by have := h.frame; rw [hb] at this; exact this)

theorem krPost_of {s s₁ s₂ s₃ s₄ : State} {V : BitVec 64 × BitVec 64}
    (p₁ : Pure s s₁) (h₂ : StOk s₁ s₂ krSlot) (p₃ : Pure s₂ s₃) (h₄ : StOk s₃ s₄ (krSlot + 1))
    (hu : WordOf (s₁.gpr .rax) V.1) (hv : WordOf (s₃.gpr .rax) V.2) : KrPost s s₄ V := by
  obtain ⟨-, hr, -, -, -, -, -, hS⟩ := kaKb_slots
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide), h₂.gpr, hb₁]
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of p₃.mem (by rw [p₃.regs _ (by decide)])
  have f₂ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₂.mem :=
    StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  refine ⟨⟨?_, ?_⟩, fun k hk h1 h2 => by rw [h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁],
    fun r hr => by rw [h₄.gpr, p₃.regs r hr, h₂.gpr, p₁.regs r hr],
    StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄,
    by rw [h₄.rd, p₃.rd, h₂.rd, p₁.rd], by rw [h₄.wr, p₃.wr, h₂.wr, p₁.wr]⟩
  · rw [h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val]; exact hu
  · rw [h₄.val]; exact hv

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their slots. -/
theorem loadKey_wp {s : State} {len : Nat} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .rdi, len⟩ : Region) ∈ s.rd) (hfit : (s.gpr .rdi).toNat + len ≤ 2 ^ 64)
    (hks : Region.Disjoint ⟨s.gpr .rdi, len⟩ ⟨s.gpr sb, 8 * slots⟩)
    (hlen : s.gpr .rsi = BitVec.ofNat 64 len) (hl : len = 16 ∨ len = 24 ∨ len = 32) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1) ∧
      WordsAt s' krSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2) ∧
      (∀ k < slots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl', hr', -, -, -, -, -, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .rdi) hl
  -- The key's words, read after stores to the scratch buffer.
  have hkw : ∀ {t : State}, t.rd = s.rd → t.gpr .rdi = s.gpr .rdi →
      Frame [⟨s.gpr sb, 8 * slots⟩] s.mem t.mem → ∀ d, d + 8 ≤ len →
      ∃ t', runBlock isa [.mov .rax (.mem (at_ .rdi d))] t = some t' ∧ Pure t t' ∧
        WordOf (t'.gpr .rax) (Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
    intro t hrd hdi hf d hd
    obtain ⟨t', e, a, o, m, rd, wr⟩ := ldAt_ok t .rax .rdi d (by
      rw [hrd, hdi]; exact ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    refine ⟨t', e, ⟨m, o, rd, wr⟩, ?_⟩
    rw [a, hdi, hf.readW (r := ⟨s.gpr .rdi + BitVec.ofNat 64 d, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hks.sub_left (VG.Offset.sub_base _ (by omega_arith))) (by decide)]
    exact wordOf_readW _ _
  have hz : s.gpr .rdi + BitVec.ofNat 64 0 = s.gpr .rdi := by simp
  have hscrOf : ∀ {t : State}, t.gpr sb = s.gpr sb → t.wr = s.wr → (⟨t.gpr sb, 8 * slots⟩ : Region) ∈ t.wr :=
    fun hb hw => by rw [hb, hw]; exact hscr
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, p₁, w₁⟩ := hkw rfl rfl (Frame.refl _ _) 0 (by omega_arith)
  have hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide)
  obtain ⟨s₂, e₂, h₂⟩ := stOk (k := klSlot) (hscrOf hb₁ p₁.wr) (by omega_arith)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [h₂.gpr, hb₁]
  have f₂ := StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  obtain ⟨s₃, e₃, p₃, w₃⟩ := hkw (by rw [h₂.rd, p₁.rd]) (by rw [h₂.gpr, p₁.regs _ (by decide)]) f₂ 8 (by omega_arith)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide), hb₂]
  obtain ⟨s₄, e₄, h₄⟩ := stOk (k := klSlot + 1) (hscrOf hb₃ (by rw [p₃.wr, h₂.wr, p₁.wr])) (by omega_arith)
  have f₄ := StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := cmpImmZ_ok s₄ .rsi 16
  have hg₅ : ∀ r, r ≠ .rax → s₅.gpr r = s.gpr r := fun r hr => by
    rw [g₅, h₄.gpr, p₃.regs r hr, h₂.gpr, p₁.regs r hr]
  have hb₅ : s₅.gpr sb = s.gpr sb := hg₅ _ (by decide)
  have hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := slotW_eq_of m₅ (by rw [g₅])
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := slotW_eq_of p₃.mem (p₃.regs _ (by decide))
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  have f₅ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₅.mem := by rw [m₅]; exact f₄
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, h₄.rd, p₃.rd, h₂.rd, p₁.rd]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, h₄.wr, p₃.wr, h₂.wr, p₁.wr]
  have hkl : WordsAt s₅ klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).1) := by
    refine ⟨?_, ?_⟩
    · rw [hs₅, h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val, hK0, ← hz]; exact w₁
    · rw [hs₅, h₄.val, hK1]; exact w₃
  have hother : ∀ k < slots, k ≠ klSlot → k ≠ klSlot + 1 → slotW s₅ k = slotW s k := fun k hk h1 h2 => by
    rw [hs₅, h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁]
  have hz₅ : s₅.zf = some (decide (len = 16)) := by
    rw [z₅, h₄.gpr, p₃.regs _ (by decide), h₂.gpr, p₁.regs _ (by decide), hlen,
      show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([.mov .rax (.mem (at_ .rdi 0)), st klSlot .rax, .mov .rax (.mem (at_ .rdi 8)),
        st (klSlot + 1) .rax, .alu .cmp .rsi (.imm 16)] : List Instr) =
        [.mov .rax (.mem (at_ .rdi 0))] ++ ([st klSlot .rax] ++ ([.mov .rax (.mem (at_ .rdi 8))] ++
          ([st (klSlot + 1) .rax] ++ [.alu .cmp .rsi (.imm 16)]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩)
  refine WP.mono (Q := fun s' => KrPost s₅ s' (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .rdi) len)).2))
    (WP.ite (decide (len = 16)) (by simp [X86_64.eval, hz₅]) (fun h16 => ?_) (fun h16 => ?_)) fun s' h => ?_
  · -- A key of 16 bytes: `KR = 0`.
    have h16 : len = 16 := by simpa using h16
    obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := zeroRax_ok s₅
    have p₆ : Pure s₅ s₆ := ⟨m₆, o₆, rd₆, wr₆⟩
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf (by rw [o₆ _ (by decide), hb₅]) (by rw [wr₆, wr₅']))
      (by omega_arith)
    obtain ⟨s₈, e₈, h₈⟩ := stOk (k := krSlot + 1)
      (hscrOf (by rw [h₇.gpr, o₆ _ (by decide), hb₅]) (by rw [h₇.wr, wr₆, wr₅'])) (by omega_arith)
    refine WP.of_runBlock ⟨s₈, by
      rw [show ([.mov32 .rax (.imm 0), st krSlot .rax, st (krSlot + 1) .rax] : List Instr) =
          [.mov32 .rax (.imm 0)] ++ ([st krSlot .rax] ++ [st (krSlot + 1) .rax]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈],
      krPost_of p₆ h₇ (Pure.refl _) h₈ (by rw [a₆, hK2, ite_eq_left h16]; exact WordOf.zero)
        (by rw [h₇.gpr, a₆, hK3, ite_eq_left h16]; exact WordOf.zero)⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₆, e₆, p₆, w₆⟩ := hkw (by rw [rd₅']) (hg₅ _ (by decide)) f₅ 16 (by omega_arith)
    have hb₆ : s₆.gpr sb = s.gpr sb := by rw [p₆.regs _ (by decide), hb₅]
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf hb₆ (by rw [p₆.wr, wr₅'])) (by omega_arith)
    obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := cmpImmZ_ok s₇ .rsi 24
    have p₈ : Pure s₇ s₈ := ⟨m₈, fun r _ => by rw [g₈], rd₈, wr₈⟩
    have hb₈ : s₈.gpr sb = s.gpr sb := by rw [g₈, h₇.gpr, hb₆]
    have f₈ : Frame [⟨s.gpr sb, 8 * slots⟩] s.mem s₈.mem := by
      rw [m₈]; exact StOk.frame' (by rw [p₆.mem]; exact f₅) hb₆ h₇
    have hz₈ : s₈.zf = some (decide (len = 24)) := by
      rw [z₈, h₇.gpr, p₆.regs _ (by decide), hg₅ _ (by decide), hlen,
        show (24 : BitVec 32).signExtend 64 = BitVec.ofNat 64 24 from rfl,
        VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    refine WP.seq (WP.of_runBlock ⟨s₈, by
      rw [show ([.mov .rax (.mem (at_ .rdi 16)), st krSlot .rax, .alu .cmp .rsi (.imm 24)] : List Instr) =
          [.mov .rax (.mem (at_ .rdi 16))] ++ ([st krSlot .rax] ++ [.alu .cmp .rsi (.imm 24)]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
    refine WP.ite (decide (len = 24)) (by simp [X86_64.eval, hz₈]) (fun h24 => ?_) (fun h24 => ?_)
    · have h24 : len = 24 := by simpa using h24
      obtain ⟨s₉, e₉, a₉, o₉, m₉, rd₉, wr₉⟩ := notRax_ok s₈
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [o₉ _ (by decide), hb₈]) (by rw [wr₉, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.alu .xor .rax (.imm 0xFFFFFFFF), st (krSlot + 1) .rax] : List Instr) =
            [.alu .xor .rax (.imm 0xFFFFFFFF)] ++ [st (krSlot + 1) .rax] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans ⟨m₉, o₉, rd₉, wr₉⟩) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [a₉, g₈, h₇.gpr, hK3, ite_eq_right h16, ite_eq_left h24]; exact w₆.not)⟩
    · have h24 : len ≠ 24 := by simpa using h24
      obtain ⟨s₉, e₉, p₉, w₉⟩ := hkw (by rw [rd₈, h₇.rd, p₆.rd, rd₅'])
        (by rw [g₈, h₇.gpr, p₆.regs _ (by decide), hg₅ _ (by decide)]) f₈ 24 (by omega_arith)
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide), hb₈]) (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.mov .rax (.mem (at_ .rdi 24)), st (krSlot + 1) .rax] : List Instr) =
            [.mov .rax (.mem (at_ .rdi 24))] ++ [st (krSlot + 1) .rax] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact w₉)⟩
  · -- Both.
    refine ⟨hkl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)),
      h.kr, fun k hk h1 => by rw [h.keep k hk (by omega_arith) (by omega_arith), hother k hk (by omega_arith) (by omega_arith)],
      fun r hr => by rw [h.regs r hr, hg₅ r hr], f₅.trans (by have := h.frame; rw [hb₅] at this; exact this),
      by rw [h.rd, rd₅'], by rw [h.wr, wr₅']⟩

/-! ## The schedule's bytes -/

/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  [movS (hiReg v) k, .bswap (hiReg v), movS (loReg v) (k + 1), .bswap (loReg v)]

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < slots) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = bswap64 (slotW s k) ∧
      s'.gpr (loReg v) = bswap64 (slotW s (k + 1)) ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3⟩ := regs_lt4 hv
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := movS_ok (k := k) (hiReg v) rfl (inRd (scr_in hscr (by omega_arith)))
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ (hiReg v)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ n1.symm, o₁ _ n1.symm]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := movS_ok (k := k + 1) (loReg v) hb₂
    (inRd (scr_in (by rw [wr₂, wr₁]; exact hscr) hk))
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := bswap_ok s₃ (loReg v)
  refine ⟨s₄, ?_, ?_, ?_, fun r h1 h2 => by rw [o₄ r h2, o₃ r h2, o₂ r h1, o₁ r h1],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [lvChunk, show ([movS (hiReg v) k, .bswap (hiReg v), movS (loReg v) (k + 1), .bswap (loReg v)] :
        List Instr) = [movS (hiReg v) k] ++ ([.bswap (hiReg v)] ++ ([movS (loReg v) (k + 1)] ++
          [.bswap (loReg v)])) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [o₄ _ n3, o₃ _ n3, a₂, a₁]
  · rw [a₄, a₃, slotW_eq_of (by rw [m₂, m₁]) hb₂]

/-- `loadValues`: the four values' halves, byte-swapped into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
  have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide)
  have hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith)
  have hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), hb₁]
  have hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith)
  have hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide), hb₂]
  have hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith)
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3, o₃ r a2 b2, o₂ r a1 b1, o₁ r a0 b0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · have w := hw 0 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), h₁]
      exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), l₁]
      exact bswap_of_wordOf w.2
  · have w := hw 1 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), h₂, hs₁]
      exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), l₂, hs₁]
      exact bswap_of_wordOf w.2
  · have w := hw 2 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), h₃, hs₂]; exact bswap_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), l₃, hs₂]; exact bswap_of_wordOf w.2
  · have w := hw 3 (by decide)
    exact ⟨by rw [h₄, hs₃]; exact bswap_of_wordOf w.1, by rw [l₄, hs₃]; exact bswap_of_wordOf w.2⟩

/-! ## The prologue -/

theorem sreg_ne' (i : Nat) : sreg i ≠ .r9 ∧ sreg i ≠ .rax ∧ sreg i ≠ .rsi := by
  unfold sreg; split <;> decide

/-- A frame of slots below the tail buffer's. -/
theorem frame_tail {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < tailSlot) :
    Frame [⟨b, 8 * tailSlot⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [tailSlot_eq] at hk; exact VG.Offset.sub_base _ (by rw [tailSlot_eq]; omega_arith))

theorem ekPrologue_ok {s₀ : State} {b : Addr} (hb : s₀.gpr .rcx = b) (hw : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr)
    (hfit : b.toNat + 8 * slots ≤ 2 ^ 64) :
    ∃ s, runBlock isa ([movR .r9 .rcx] ++ saveRegs ++ setMasks layerMasks ++ [st dataSlot .rsi] ++
        [movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] ++
        sigmas.flatMap sigmaOne ++ [movS .rsi dataSlot]) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .rsi = s₀.gpr .rsi ∧
      (∀ r, r ≠ .r9 → r ≠ .rax → r ≠ t0 → r ≠ .rsi → s.gpr r = s₀.gpr r) ∧
      Saved s₀ b s.mem ∧ MasksOk s ∧ slotW s dataSlot = s₀.gpr .rsi ∧
      (∀ i < 6, ∀ j < 8, entryW s.mem b i j = keyPlane (sigmas.getD i 0) j) ∧
      Frame [⟨b, 8 * tailSlot⟩] s₀.mem s.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hk := keySlot_eq
  have hd : dataSlot = 369 := rfl
  have ht := tailSlot_eq
  have hsv : savedSlot = 371 := rfl
  have hS := slots_eq
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ .r9 .rcx
  have hb₁ : s₁.gpr sb = b := by rw [show sb = .r9 from rfl, r₁, hb]
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_ok (b := b) (by rw [wr₁]; exact hw) hb₁
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := setMasks_ok (b := b) layerMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁]; exact hw) (fun kv hkv => mask_lt hkv) (by decide)
  have hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), g₂, hb₁]
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := stReg_ok (k := dataSlot) .rsi hb₃
    (scr_in (by rw [wr₃, wr₂, wr₁]; exact hw) (by omega_arith))
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₄ .rsi sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₅ .rsi (BitVec.ofNat 32 (8 * keySlot))
  have hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₅ _ (by decide), g₄, hb₃]
  obtain ⟨s₇, e₇, v₇, f₇, r₇, g₇, rd₇, wr₇⟩ := sigmaList_ok hfit sigmas 0 s₆
    (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw)
    (by rw [r₆, r₅, g₄, hb₃, show (BitVec.ofNat 32 (8 * keySlot)).signExtend 64 = BitVec.ofNat 64 (8 * keySlot)
      from rfl]; rfl) (by decide)
  have hb₇ : s₇.gpr sb = b := by rw [g₇ _ (by decide) (by decide), hb₆]
  -- The slots outside the table keep their values.
  have hs₇ : ∀ k, k < keySlot ∨ keySlot + 48 ≤ k → k < slots → slotW s₇ k = slotW s₄ k := fun k h1 h2 => by
    simp only [slotW, hb₇, g₄, hb₃]
    rw [← m₅, ← m₆]
    refine f₇.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [wordAddr, Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
    exact VG.Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  obtain ⟨s₈, e₈, a₈, o₈, m₈, rd₈, wr₈⟩ := movS_ok (k := dataSlot) .rsi hb₇
    (inRd (scr_in (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hw) (by omega_arith)))
  have hb₈ : s₈.gpr sb = b := by rw [o₈ _ (by decide), hb₇]
  have hs₈ : ∀ k, slotW s₈ k = slotW s₇ k := slotW_eq_of m₈ (by rw [hb₈, hb₇])
  have hs₄ : ∀ k < slots, k ≠ dataSlot → slotW s₄ k = slotW s₃ k := fun k hk' hkd => by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ hk' (by omega_arith), ite_eq_right hkd]
  have hds : slotW s₄ dataSlot = s₀.gpr .rsi := by
    rw [slotW_store (by rw [m₄, hb₃]) g₄ (by omega_arith) (by omega_arith), ite_eq_left rfl, g₃ _ (by decide), g₂,
      o₁ _ (by decide)]
  refine ⟨s₈, ?_, hb₈, ?_, fun r h1 h2 h3 h4 => ?_, fun i hi => ?_, fun kv hkv => ?_, ?_,
    fun i hi j hj => ?_, ?_, by rw [rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      e₄, Option.bind_some,
      show ([movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) =
        [movR .rsi sb] ++ [.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl,
      runBlock_append', e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some, e₈]
  · rw [a₈, hs₇ _ (Or.inr (by omega_arith)) (by omega_arith), hds]
  · rw [o₈ r h4, g₇ r h2 h4, o₆ r h4, o₅ r h4, g₄, g₃ r h3, g₂, o₁ r h1]
  · obtain ⟨n1, n2, n3⟩ := sreg_ne' i
    have := sv₂ i hi
    rw [show s₁.gpr (sreg i) = s₀.gpr (sreg i) from o₁ _ n1] at this
    rw [← this]
    have h' := hs₇ (savedSlot + i) (Or.inr (by omega_arith)) (by omega_arith)
    rw [hs₄ _ (by omega_arith) (by omega_arith)] at h'
    simp only [slotW, hb₇, hb₃, m₈] at h' ⊢
    rw [h']
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega_arith) (by omega_arith)
  · have := mask_lt hkv
    rw [hs₈, hs₇ _ (Or.inl this) (by omega_arith), hs₄ _ (by omega_arith) (by omega_arith)]
    exact v₃ kv hkv
  · rw [hs₈, hs₇ _ (Or.inr (by omega_arith)) (by omega_arith), hds]
  · rw [m₈, ← hb₆]
    have := v₇ i (by simpa [sigmas] using hi) j hj
    rw [Nat.zero_add] at this
    rw [hb₆]; exact this
  · rw [m₈]
    have f₄ : Frame [⟨b, 8 * tailSlot⟩] s₃.mem s₄.mem := by rw [m₄]; exact frame_tail _ (by omega_arith)
    have f₇' : Frame [⟨b, 8 * tailSlot⟩] s₆.mem s₇.mem := f₇.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero, Nat.add_zero, sigmas, List.length_cons, List.length_nil]
      exact VG.Offset.sub_base b (by omega_arith)⟩
    have f₃' : Frame [⟨b, 8 * tailSlot⟩] s₂.mem s₃.mem := f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by omega_arith)⟩
    rw [m₁] at f₂
    exact f₂.trans (f₃'.trans (f₄.trans (by rw [← m₅, ← m₆]; exact f₇')))

end VG.Proof.Camellia.X86_64

end

end


/-!
# The Camellia key schedule on x86-64: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyX86_64`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` byte-swaps them into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st)
open VG.Proof.Camellia (hiW loW)

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega_using []]

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hS : s₈.gpr .rdx = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
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

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86_64.pre s₀) :
    WP isa expandKey s₀ fun s' => gprPreserved s₀ s' ∧ expandKeyX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dRS, dRB, fitK, fitS, fitB, hlen⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hd : dataSlot = 369 := rfl
  have hsv : savedSlot = 371 := rfl
  have hwB : (⟨s₀.gpr .rcx, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .rdx, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrK : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, rsi₁, g₁, sv₁, mk₁, ds₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .rcx) rfl hwB fitB
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have rdx₁ : s₁.gpr .rdx = s₀.gpr .rdx := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  have hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .rdi) (s₀.gpr .rsi).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat := by
    rw [rdi₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩)
      (fun r hr => ?_) (by simp only; omega_arith) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega_arith))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .rsi).toNat) (s := s₁) (by rw [b₁, wr₁]; exact hwB)
    (by rw [rdi₁, rd₁]; exact hrK) (by rw [rdi₁]; exact fitK) (by rw [rdi₁, b₁]; exact dKB)
    (by rw [rsi₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hlen) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, sl₂, g₂, f₂, rd₂, wr₂⟩ := h₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat = key at kl₂ kr₂
  have hb₂ : s₂.gpr sb = s₀.gpr .rcx := by rw [g₂ _ (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ kp sb
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ kp (BitVec.ofNat 32 (8 * keySlot))
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) =
      [movR kp sb] ++ [.alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl, runBlock_append', e₃,
      Option.bind_some, e₄], ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := fun r hr => by rw [o₄ r hr, o₃ r hr]
  have hb₄ : s₄.gpr sb = s₀.gpr .rcx := by rw [hg₄ _ (by decide), hb₂]
  have hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of (by rw [m₄, m₃]) (hg₄ _ (by decide))
  have rdx₄ : s₄.gpr .rdx = s₀.gpr .rdx := by rw [hg₄ _ (by decide), g₂ _ (by decide), rdx₁]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have hlow : ∀ k < klSlot, slotW s₄ k = slotW s₁ k := fun k hk => by
    rw [hs₄, sl₂ k (by omega_arith) (Or.inl hk)]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  have hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, fun k hk => ?_, ?_, ?_, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · refine ⟨_, by rw [wr₄']; exact hwS, ?_⟩
      rw [rdx₄, wordAddr]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [rdx₄, hb₄]
      exact (dSB.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
    · rw [hb₄]; exact fitB
    · rw [rdx₄]; omega_arith
    · have := mask_lt hkv
      rw [hlow _ (by omega_arith)]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega_arith), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [rdx₄, hb₄]; exact dSB.sub_left (Region.sub_prefix (by omega_arith))
    · rw [AtEntry, a₄, r₃, hb₄, hb₂, show (BitVec.ofNat 32 (8 * keySlot)).signExtend 64 =
        BitVec.ofNat 64 (8 * keySlot + 64 * 0) from rfl]
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  have hb₅ : s₅.gpr sb = s₀.gpr .rcx := h₅.base.trans hb₄
  have wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  have hscr₅ : (⟨s₀.gpr .rcx, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
  -- The values, byte-swapped into registers.
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₅) (by rw [hb₅]; exact hscr₅)
    [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2] (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
      · exact h₅.kl hpre
      · exact h₅.kr hpre
      · have := h₅.ka (by decide); rw [hKA'] at this; exact this
      · have := h₅.kb (by decide); rw [hKB'] at this; exact this)
  have hsb₆ : ∀ v < 4, sb ≠ hiReg v ∧ sb ≠ loReg v := fun v hv =>
    ⟨(regs_lt4 hv).1.symm, (regs_lt4 hv).2.1.symm⟩
  have hb₆ : s₆.gpr sb = s₀.gpr .rcx := by rw [o₆ _ hsb₆, hb₅]
  -- The key's length.
  obtain ⟨s₇, e₇, a₇, o₇, m₇, rd₇, wr₇⟩ := movS_ok (k := dataSlot) t0 hb₆
    (inRd (scr_in (by rw [wr₆]; exact hscr₅) (by omega_arith)))
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := cmpImmZ_ok s₇ t0 16
  have hds : slotW s₆ dataSlot = s₀.gpr .rsi := by
    rw [slotW_eq_of m₆ (o₆ _ hsb₆), h₅.keep _ (by omega_arith) (by omega_arith) (Or.inl (by omega_arith)), hs₄,
      sl₂ _ (by omega_arith) (Or.inl (by omega_arith)), ds₁]
  have hz₈ : s₈.zf = some (decide ((s₀.gpr .rsi).toNat = 16)) := by
    rw [z₈, a₇, hds, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl]
    conv => lhs; rw [show s₀.gpr .rsi = BitVec.ofNat 64 (s₀.gpr .rsi).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_append', e₆, Option.bind_some,
      show ([movS t0 dataSlot, .alu .cmp t0 (.imm 16)] : List Instr) =
        [movS t0 dataSlot] ++ [.alu .cmp t0 (.imm 16)] from rfl,
      runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  have hrdx₈ : s₈.gpr .rdx = s₀.gpr .rdx := by
    rw [g₈, o₇ _ (by decide), o₆ _ (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide),
      h₅.rdx, rdx₄]
  have hwS₈ : (⟨s₀.gpr .rdx, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₇, wr₆, wr₅]; exact hwS
  have hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈, o₇ _ n1, o₇ _ n3]; exact v₆ v hv
  have hklen : key.length = (s₀.gpr .rsi).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .rdx) (s₀.gpr .rsi).toNat key)
    (WP.ite (decide ((s₀.gpr .rsi).toNat = 16)) (by simp [X86_64.eval, hz₈]) (fun h16 => ?_) (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .rsi).toNat = 16 := by simpa using h16
    exact stores_wp hrdx₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega_arith) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .rsi).toNat ≠ 16 := by simpa using h16
    exact stores_wp hrdx₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  have hb₉ : s₉.gpr sb = s₀.gpr .rcx := by rw [h₉.regs _ (by decide) (by decide), g₈, o₇ _ (by decide), hb₆]
  have hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 6 →
      s₉.mem.readW (wordAddr (s₀.gpr .rcx) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .rcx) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_arith))).symm) (by decide)]
    have := h₅.keep k (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))
    rw [hs₄, sl₂ k (by omega_arith) (Or.inl (by omega_arith))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₇, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, o₁₀, f₁₀, rd₁₀, wr₁₀⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .rcx)
    (by rw [h₉.wr, wr₈, wr₇, wr₆, wr₅]; exact hwB) hb₉ (fun i hi => by
      rw [hSB _ (by omega_arith) (by omega_arith)]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hsp : s₁₀.gpr .rsp = s₀.gpr .rsp := by
      rw [o₁₀ _ (fun i hi => by unfold sreg; split <;> decide), h₉.regs _ (by decide) (by decide), g₈,
        o₇ _ (by decide), o₆ _ (fun v hv => by
          rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide),
        h₅.regs _ (by decide) (by decide) (by decide) (by decide), hg₄ _ (by decide), g₂ _ (by decide),
        g₁ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₁₀ 0 (by omega_arith)
    · exact rg₁₀ 1 (by omega_arith)
    · exact hsp
    · exact rg₁₀ 2 (by omega_arith)
    · exact rg₁₀ 3 (by omega_arith)
    · exact rg₁₀ 4 (by omega_arith)
    · exact rg₁₀ 5 (by omega_arith)
  · -- The return address is untouched.
    have fr : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₀.mem s₁₀.mem := by
      have F₁ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₀.mem s₁.mem :=
        f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
      have F₂ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₁.mem s₄.mem := by
        rw [m₄, m₃]; rw [b₁] at f₂
        exact f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
      have F₅ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₄.mem s₅.mem := by
        have := h₅.frame; rw [hb₄, rdx₄] at this
        exact this.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega_arith)⟩
      have F₉ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₅.mem s₉.mem := by
        rw [← m₆, ← m₇, ← m₈]
        exact h₉.frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
      have F₁₀ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₉.mem s₁₀.mem :=
        f₁₀.sub fun r hr => ⟨_, List.mem_cons_self, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
      exact F₁.trans (F₂.trans (F₅.trans (F₉.trans F₁₀)))
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRB
    · exact dRS
  · show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .rdx) _ = _
    rw [hkey, ← h₉.bytes]
    have hle := Proof.Camellia.scheduleLength_rounds_le (s₀.gpr .rsi).toNat
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁₀.bytes (R := ⟨s₀.gpr .rdx, 272⟩) (fun r hr => ?_)
      (by simp only; omega_arith) (by simp only; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact dSB.sub_right (Region.sub_prefix (by omega_arith))

end VG.Proof.Camellia.X86_64

end

end


/-!
# The Camellia key schedule on x86-64 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time (`expandKey_ct`). `expandKey_framed` runs it with its working space on
the stack, zeroed on return: 3216 bytes, the 401 words of the scratch
buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

theorem expandKey_correct (s : State) (hs : expandKeyX86_64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := expandKey_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := expandKey) (by lit_decide) he hg, hpost⟩

/-- A state satisfying the precondition (a key of 16 bytes). -/
def expandKeySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩, ⟨0x4000, 8 * 401⟩]

theorem expandKey_verified :
    Verified X86_64.target expandKey (Proof.Camellia.expandKeyScratchContract X86_64.abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyX86_64,
      X86_64.abi, X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: a key of 16 bytes at
`0x1000`, the schedule at `0x3000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract X86_64.abi 3216).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, X86_64.abi, X86_64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3216 .rcx 401 expandKey)
      (Spec.Camellia.expandKeyContract X86_64.abi 3216) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 401) (pre := Spec.Camellia.expandKeyPre X86_64.abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3216) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (Code.all_of_spTest (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.X86_64
