module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
public import VerifiedGarbage.Proof.Seed.KeySchedule
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Seed.X86.SseCore
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.Straight
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Seed.KeyRot
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.X86.ExpandKeyLit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Impl.Seed.X86.ExpandKey
meta import VerifiedGarbage.Proof.Seed.X86.SseCore
meta import VerifiedGarbage.Proof.Seed.X86.ExpandKeyLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# SEED's key schedule on x86 (32-bit)

`expandKey_wp`: with the working space as an argument (`expandKeyX86`),
`expandKey` saves the callee-saved registers, loads the key's words
(`keyWords_ok`), computes the 32 inputs of `G` (`keyRounds_ok`: a round
writes its two inputs, `gInput`, to their slots, and rotates
`Key0 || Key1` or `Key2 || Key3` as one 64-bit word: each word rotated by
eight or 24 bits, and their bytes exchanged under a mask, `xr_hi`, …, which
is two shifts of each word, as `keyStep` has it), and writes `G` of sixteen
at a time to the schedule (`keyChunk_wp`, by the core's `Sse.gCall_wp'`); RFC
4269 §2.3's schedule is `G` of these inputs (`expandKey_eq`).

`expandKey_ct` is constant time by the taint analysis, which starts with
`esp` public and knows which argument words are the base addresses of the
schedule and the scratch buffer. `expandKey_framed` runs it with its working
space on the stack, zeroed on return, and `expandKey_scrubbed` is the
function as emitted, which returns without secret residue (`X86.rtaint`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG VG.X86 VG.Impl.Seed.X86

/-- The key schedule on x86 with its working space as the third argument,
and four bytes of stack below the return address. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 128⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 4 * kSlots⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 4 * kSlots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧
    stack.Disjoint sched ∧ stack.Disjoint scratch ∧ 4 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.Seed.scheduleAt s'.mem ((arg s 1).setWidth 64) =
      Spec.Seed.expandKey (Spec.Seed.blockAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.Seed

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86 VG.Proof.Seed
open VG.Impl.Aes.X86 (sb slotAt movS st movR xorR rorI andI at_ argOp addI subI)
open VG.X86.Straight (wordAddr slot_sep slot_contains)

/-! ## The slots -/

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some]; exact ih s'

/-- Slot `k` of the scratch buffer. -/
def slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) k) 32

theorem slots_eq : kSlots = 184 := rfl

/-- The scratch buffer. -/
def scratchR (s : State) : Region := ⟨(s.gpr sb).setWidth 64, 4 * kSlots⟩

/-- The scratch buffer is writable, and does not wrap around. -/
structure Room (s : State) : Prop where
  mem : ∃ n, kSlots ≤ n ∧ (s.gpr sb).toNat + 4 * n ≤ 2 ^ 32 ∧
    (⟨(s.gpr sb).setWidth 64, 4 * n⟩ : Region) ∈ s.wr
  fit : (s.gpr sb).toNat + 4 * kSlots ≤ 2 ^ 32

theorem Room.congr {s s' : State} (h : Room s) (hb : s'.gpr sb = s.gpr sb) (hw : s'.wr = s.wr) :
    Room s' :=
  ⟨by rw [hb, hw]; exact h.mem, by rw [hb]; exact h.fit⟩

theorem toNat_addr (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_using [])]

/-- Slot `k`, as a 64-bit offset from the base. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_using [hfit])

theorem slot_in {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) :
    (scratchR s).Contains (wordAddr (s.gpr sb) k) 4 :=
  slot_contains (s.gpr sb) hk h.fit

/-- Slot `k` is writable. -/
theorem Room.inR {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) :
    InRegions s.wr (wordAddr (s.gpr sb) k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  ⟨_, hr, slot_contains (s.gpr sb) (Nat.lt_of_lt_of_le hk hn) hf⟩

/-- Slot `k` of the scratch buffer. -/
abbrev slotA (s : State) (k : Nat) : Addr := wordAddr (s.gpr sb) k

/-- `s` with the memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

theorem mem_setMem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
theorem gpr_setMem (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
theorem ea_slot (s : State) (k : Nat) : s.ea (slotAt sb k) = slotA s k := rfl

theorem load_slot {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) :
    s.load32 (slotA s k) = some (slotW s k) := by
  simp only [State.load32, show InRegions (s.rd ++ s.wr) (slotA s k) 4 from
    let ⟨_, hr, hc⟩ := h.inR hk; ⟨_, List.mem_append_right _ hr, hc⟩, ↓reduceIte]; rfl

theorem exec_movS {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) (d : Reg) :
    exec (movS d k) s = some (s.setReg d (slotW s k)) := by
  simp only [movS, exec, readSrc, ea_slot, load_slot h hk, Option.map_some]

theorem exec_st {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) (r : Reg) :
    exec (st k r) s = some (setMem s (s.mem.writeW (slotA s k) (s.gpr r))) := by
  simp only [st, exec, ea_slot, State.store32, show InRegions s.wr (slotA s k) 4 from h.inR hk,
    ↓reduceIte]; rfl

theorem exec_addS {s : State} (h : Room s) {k : Nat} (hk : k < kSlots) (d : Reg) :
    exec (addS d k) s =
      some ((arithFlags s (s.gpr d + slotW s k) (2 ^ 32 ≤ (s.gpr d).toNat + (slotW s k).toNat)
        (addOverflow (s.gpr d) (slotW s k) (s.gpr d + slotW s k))).setReg d (s.gpr d + slotW s k)) := by
  simp only [addS, exec, execAlu, readSrc, ea_slot, load_slot h hk, Option.bind_some]

theorem exec_xorR (s : State) (d r : Reg) :
    exec (xorR d r) s = some ((arithFlags s (s.gpr d ^^^ s.gpr r) false false).setReg d (s.gpr d ^^^ s.gpr r)) :=
  rfl

theorem slotW_setMem_write {s : State} (h : Room s) {k j : Nat} (hk : k < kSlots) (hj : j < kSlots)
    (v : BitVec 32) :
    slotW (setMem s (s.mem.writeW (slotA s k) v)) j = if j = k then v else slotW s j := by
  have hf := h.fit
  rw [slots_eq] at hf hk hj
  show (s.mem.writeW (slotA s k) v).readW (slotA s j) 32 = _
  split
  · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
  · rename_i e; exact Mem.readW_writeW_sep (slot_sep _ (by omega_using [hj, hf]) (by omega_using [hk, hf]) e) (by decide)

theorem slotA_setReg (s : State) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) (k : Nat) :
    slotA (s.setReg r v) k = slotA s k := by
  simp only [slotA, gpr_setReg_of_ne _ _ (Ne.symm hr)]

theorem slotW_setReg (s : State) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) (j : Nat) :
    slotW (s.setReg r v) j = slotW s j := by
  simp only [slotW, gpr_setReg_of_ne _ _ (Ne.symm hr), mem_setReg]

theorem room_setReg {s : State} (h : Room s) {r : Reg} (hr : r ≠ sb) (v : BitVec 32) :
    Room (s.setReg r v) := h.congr (gpr_setReg_of_ne _ _ (Ne.symm hr)) rfl

/-- `mov d, s`. -/
theorem movR_ok (s : State) (d r₀ : Reg) :
    ∃ s', runBlock isa [movR d r₀] s = some s' ∧ s'.gpr d = s.gpr r₀ ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf :=
  ⟨s.setReg d (s.gpr r₀), rfl, gpr_setReg_self _ _ _, fun _ hr => gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl, rfl, rfl⟩

theorem savedSlot_eq : savedSlot = 180 := rfl

/-! ## The stack's arguments, and the callee-saved registers -/

/-- The scratch buffer at `b`, of `kSlots` slots or more, in the regions `rs`. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : ∃ n, kSlots ≤ n ∧ b.toNat + 4 * n ≤ 2 ^ 32 ∧ (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs
  fit : b.toNat + 4 * kSlots ≤ 2 ^ 32

/-- Slot `k` is in the scratch buffer. -/
theorem slot_inR {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := toNat_addr b
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A scratch buffer of exactly `kSlots` slots. -/
theorem ScrIn.exact {rs : List Region} {b : BitVec 32} (hr : (⟨b.setWidth 64, 4 * kSlots⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * kSlots ≤ 2 ^ 32) : ScrIn rs b := ⟨⟨kSlots, Nat.le_refl _, hfit, hr⟩, hfit⟩

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < kSlots) :
    InRegions rs (wordAddr b k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  slot_inR hr hf (Nat.lt_of_lt_of_le hk hn)

theorem ldArg_ok (s : State) (d : Reg) (i : Nat) (h : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov d (.mem (argOp i))] s = some s' ∧ s'.gpr d = s.mem.readW (s.ea (argOp i)) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.ea (argOp i)) 32), by
    rw [runBlock_cons, show exec (.mov d (.mem (argOp i))) s = some (s.setReg d (s.mem.readW (s.ea (argOp i)) 32)) by
      simp [exec, readSrc, State.load32, h], runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * kSlots ≤ 2 ^ 32) {k : Nat} (hk : k < kSlots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * kSlots⟩ := by
  rw [slot_addr (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * kSlots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < kSlots) (hk : k < kSlots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-- `mov d, [n + 4 k]`, `n` holding `b`, a slot of the scratch buffer. -/
theorem lptrSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < kSlots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (hw.slot hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, `n` holding `b`, a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < kSlots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, hw.slot hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < kSlots) →
    ∃ s', runBlock isa (L.map fun x => .store (slotAt n x.1) x.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * kSlots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < kSlots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < kSlots) →
    ∃ s', runBlock isa (L.map fun x => .mov x.1 (.mem (slotAt n x.2))) s = some s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := lptrSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .ebx

theorem savedRegs_eq : savedRegs = (List.range 4).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : BitVec 32} {k : Nat} (hw : ScrIn s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegs k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ Saved s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * kSlots⟩] s.mem s'.mem ∧
      ∀ k, (k < savedSlot ∨ savedSlot + 4 ≤ k) → k < kSlots →
        s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax k ha
  rw [hb] at v₁
  let L : List (Nat × Reg) := (List.range 4).map fun i => (savedSlot + i, sreg i)
  have hL : savedRegs.map (fun (r, j) => Instr.store (slotAt .eax j) r) =
      L.map fun x => .store (slotAt .eax x.1) x.2 := by
    rw [savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 4).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, o₂, v₂⟩ := stW_list_ok .eax L s₁ v₁ (by rw [wr₁]; exact hw)
    (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega_arith)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, -, -⟩ := movR_ok s₂ .edi .eax
  refine ⟨s₃, ?_, by rw [r₃, g₂, v₁], fun r h0 h7 => by rw [o₃ r h7, g₂, o₁ r h0], fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, ← m₁]; exact f₂, fun j hj hjs => ?_⟩
  · rw [saveRegs, runBlock_append, runBlock_append, e₁, Option.bind_some, hL, e₂, Option.bind_some, e₃]
  · rw [m₃, v₂ (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩),
      o₁ _ (by revert i; decide)]
  · rw [m₃, o₂ j ?_ hjs, m₁]
    rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; rcases hj with hj | hj <;> omega_arith

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .edi = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.ebx, savedSlot), (.esi, savedSlot + 1), (.ebp, savedSlot + 3)]
  obtain ⟨s₁, e₁, m₁, rd₁, wr₁, o₁, v₁⟩ := ldW_list_ok .edi L s hb hw (by decide) (by decide)
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only [savedSlot_eq, slots_eq] <;> omega_arith)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := lptrSlot_ok s₁ .edi .edi (k := savedSlot + 2)
    (by rw [o₁ _ (by decide), hb]) (by rw [savedSlot_eq, slots_eq]; omega_arith) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show restoreRegs = (L.map fun x => .mov x.1 (.mem (slotAt .edi x.2))) ++
        [.mov .edi (.mem (slotAt .edi (savedSlot + 2)))] from rfl, runBlock_append, e₁, Option.bind_some, e₂]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · show s₂.gpr .ebx = _
      rw [o₂ _ (by decide), v₁ (.ebx, savedSlot) (by simp [L])]; exact hs 0 (by decide)
    · show s₂.gpr .esi = _
      rw [o₂ _ (by decide), v₁ (.esi, savedSlot + 1) (by simp [L])]; exact hs 1 (by decide)
    · rw [show sreg 2 = .edi from rfl, v₂, m₁]; exact hs 2 (by decide)
    · show s₂.gpr .ebp = _
      rw [o₂ _ (by decide), v₁ (.ebp, savedSlot + 3) (by simp [L])]; exact hs 3 (by decide)
  · rw [o₂ r (hr 2 (by decide)), o₁ r (by
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 3 (by decide)⟩)]

theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-! ## The rotations, bit by bit -/

theorem maskHi_bit : ∀ i < 32, ((0xFF000000 : BitVec 32)).getLsbD i = decide (24 ≤ i) := by decide
theorem maskLo_bit : ∀ i < 32, ((0x000000FF : BitVec 32)).getLsbD i = decide (i < 8) := by decide

theorem xr_hi (a b : BitVec 32) :
    a.rotateRight 8 ^^^ ((a.rotateRight 8 ^^^ b.rotateRight 8) &&& (0xFF000000 : BitVec 32)) = a >>> 8 ||| b <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskHi_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · simp [h, show ¬ 24 ≤ i by omega_arith]
  · simp only [show 24 ≤ i by omega_arith, show ¬ i < 24 by omega_arith, decide_true,
      decide_false, ite_false, Bool.and_true, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr b (show i - (32 - 8 % 32) = i - 24 by omega_arith), BitVec.getLsbD_of_ge a (8 + i) (by omega_arith)]
    cases a.getLsbD (i - (32 - 8 % 32)) <;> cases b.getLsbD (i - 24) <;> rfl

theorem xr_lo (a b : BitVec 32) :
    b.rotateRight 8 ^^^ ((a.rotateRight 8 ^^^ b.rotateRight 8) &&& (0xFF000000 : BitVec 32)) = b >>> 8 ||| a <<< 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskHi_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 24 with h | h
  · simp [h, show ¬ 24 ≤ i by omega_arith]
  · simp only [show 24 ≤ i by omega_arith, show ¬ i < 24 by omega_arith, decide_true,
      decide_false, ite_false, Bool.and_true, Bool.not_false, Bool.true_and]
    rw [getLsbD_congr a (show i - (32 - 8 % 32) = i - 24 by omega_arith), BitVec.getLsbD_of_ge b (8 + i) (by omega_arith)]
    cases a.getLsbD (i - 24) <;> cases b.getLsbD (i - (32 - 8 % 32)) <;> rfl

theorem xl_hi (a b : BitVec 32) :
    a.rotateRight 24 ^^^ ((a.rotateRight 24 ^^^ b.rotateRight 24) &&& (0x000000FF : BitVec 32)) = a <<< 8 ||| b >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskLo_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp only [h, decide_true, ite_true, Bool.and_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    rw [getLsbD_congr b (show 24 % 32 + i = 24 + i by omega_arith)]
    cases a.getLsbD (24 % 32 + i) <;> cases b.getLsbD (24 + i) <;> rfl
  · simp [show ¬ i < 8 by omega_arith,
      BitVec.getLsbD_of_ge b (24 + i) (by omega_arith)]

theorem xl_lo (a b : BitVec 32) :
    b.rotateRight 24 ^^^ ((a.rotateRight 24 ^^^ b.rotateRight 24) &&& (0x000000FF : BitVec 32)) = b <<< 8 ||| a >>> 24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, maskLo_bit i hi, hi, decide_true, Bool.true_and]
  rcases Nat.lt_or_ge i 8 with h | h
  · simp only [h, decide_true, ite_true, Bool.and_true, Bool.not_true,
      Bool.false_and, Bool.false_or]
    rw [getLsbD_congr a (show 24 % 32 + i = 24 + i by omega_arith)]
    cases a.getLsbD (24 + i) <;> cases b.getLsbD (24 % 32 + i) <;> rfl
  · simp [show ¬ i < 8 by omega_arith,
      BitVec.getLsbD_of_ge a (24 + i) (by omega_arith)]

/-! ## Instructions -/

theorem exec_movS' {k : Nat} (hk : k < kSlots) (d : Reg) {s : State} (h : Room s) :
    exec (movS d k) s = some (s.setReg d (slotW s k)) := exec_movS h hk d

theorem exec_st' {k : Nat} (hk : k < kSlots) (r : Reg) {s : State} (h : Room s) :
    exec (st k r) s = some (setMem s (s.mem.writeW (slotA s k) (s.gpr r))) := exec_st h hk r

theorem exec_addS' {k : Nat} (hk : k < kSlots) (d : Reg) {s : State} (h : Room s) :
    exec (addS d k) s =
      some ((arithFlags s (s.gpr d + slotW s k) (2 ^ 32 ≤ (s.gpr d).toNat + (slotW s k).toNat)
        (addOverflow (s.gpr d) (slotW s k) (s.gpr d + slotW s k))).setReg d (s.gpr d + slotW s k)) :=
  exec_addS h hk d

theorem exec_subS' {k : Nat} (hk : k < kSlots) (d : Reg) {s : State} (h : Room s) :
    exec (subS d k) s =
      some ((arithFlags s (s.gpr d - slotW s k) ((s.gpr d).toNat < (slotW s k).toNat)
        (subOverflow (s.gpr d) (slotW s k) (s.gpr d - slotW s k))).setReg d (s.gpr d - slotW s k)) := by
  simp only [subS, exec, execAlu, readSrc, ea_slot, load_slot h hk, Option.bind_some]

/-- The flags `ror d, n` sets. -/
def rorF (s : State) (d : Reg) (n : Nat) : State :=
  s.setFlags (some ((s.gpr d).rotateRight n).msb)
    (if n = 1 then some (((s.gpr d).rotateRight n).msb ^^ ((s.gpr d).rotateRight n).getMsbD 1) else none) s.zf s.sf

theorem gpr_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).gpr = s.gpr := rfl
theorem mem_rorF (s : State) (d : Reg) (n : Nat) : (rorF s d n).mem = s.mem := rfl
theorem exec_rorI {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) (s : State) (d : Reg) :
    exec (rorI d n) s = some ((rorF s d n).setReg d ((s.gpr d).rotateRight n)) := by
  simp only [rorI, exec, execShift, h1, h2, and_self, ite_true]; rfl

theorem exec_andI (s : State) (d : Reg) (v : BitVec 32) :
    exec (andI d v) s = some ((arithFlags s (s.gpr d &&& v) false false).setReg d (s.gpr d &&& v)) := rfl

theorem exec_movR (s : State) (d r : Reg) : exec (movR d r) s = some (s.setReg d (s.gpr r)) := rfl

theorem exec_addI (s : State) (d : Reg) (v : BitVec 32) :
    exec (addI d v) s = some ((arithFlags s (s.gpr d + v) (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)
      (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d (s.gpr d + v)) := rfl

theorem exec_subI (s : State) (d : Reg) (v : BitVec 32) :
    exec (subI d v) s = some ((arithFlags s (s.gpr d - v) ((s.gpr d).toNat < v.toNat)
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v)) := rfl

/-- Room through the writes of registers other than `sb`. -/
tactic_template "room" : tactic => `(tactic|
  (refine Room.congr ‹Room _› ?_ ?_
   · simp only [gpr_setReg, gpr_arithFlags, gpr_rorF, gpr_setMem, sb, reduceCtorEq, ↓reduceIte]
   · rfl))

/-- The key's words. -/
def kwS (s : State) : Quad := (slotW s (keySlot 0), slotW s (keySlot 1), slotW s (keySlot 2), slotW s (keySlot 3))

theorem keySlot_lt {w : Nat} (hw : w < 4) : keySlot w < kSlots := by simp [keySlot, slots_eq]; omega_arith

/-! ## The rotations -/

theorem rot64_ok {k n : Nat} (hk : k ≤ 2) (h1 : 1 ≤ n) (h2 : n ≤ 31) (m : BitVec 32) {s : State} (h : Room s) :
    ∃ s', runBlock isa (rot64 k n m) s = some s' ∧
      slotW s' (keySlot k) = (slotW s (keySlot k)).rotateRight n ^^^
        (((slotW s (keySlot k)).rotateRight n ^^^ (slotW s (keySlot (k + 1))).rotateRight n) &&& m) ∧
      slotW s' (keySlot (k + 1)) = (slotW s (keySlot (k + 1))).rotateRight n ^^^
        (((slotW s (keySlot k)).rotateRight n ^^^ (slotW s (keySlot (k + 1))).rotateRight n) &&& m) ∧
      (∀ j < kSlots, j ≠ keySlot k → j ≠ keySlot (k + 1) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hk0 := keySlot_lt (w := k) (by omega_arith)
  have hk1 := keySlot_lt (w := k + 1) (by omega_arith)
  rw [rot64, runBlock_cons, exec_movS' hk0 .eax, runStep_some, runBlock_cons, exec_rorI h1 h2, runStep_some,
    runBlock_cons, exec_movS' hk1 .ebx, runStep_some, runBlock_cons, exec_rorI h1 h2, runStep_some,
    runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_xorR, runStep_some, runBlock_cons, exec_andI,
    runStep_some, runBlock_cons, exec_xorR, runStep_some, runBlock_cons, exec_xorR, runStep_some,
    runBlock_cons, exec_st' hk0 .eax, runStep_some, runBlock_cons, exec_st' hk1 .ebx, runStep_some, runBlock_nil]
  have hf : (s.gpr .edi).toNat + 4 * kSlots ≤ 2 ^ 32 := h.fit
  have hne : keySlot k ≠ keySlot (k + 1) := by simp [keySlot]
  refine ⟨_, rfl, ?_, ?_, fun j hj h1 h2 => ?_, fun r h1 h2 h3 => ?_, rfl, rfl, ?_⟩
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk0 hk1, ite_eq_right hne, readW_slot_write hf _ hk0 hk0, ite_eq_left rfl]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk1 hk1, ite_eq_left rfl]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hj hk1, ite_eq_right h2, readW_slot_write hf _ hj hk0, ite_eq_right h1]
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2, gpr_setReg_of_ne _ _ h3,
      gpr_arithFlags, gpr_rorF]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags, mem_rorF,
      gpr_rorF, slotA, sb, reduceCtorEq, ↓reduceIte]
    have hc : ∀ w, w ≤ 3 → (scratchR s).Contains (wordAddr (s.gpr .edi) (keySlot w)) 4 := fun w hw =>
      slot_in h (keySlot_lt (by omega_arith))
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (hc k (by omega_arith))).writeW List.mem_cons_self _
      (hc (k + 1) (by omega_arith))
  all_goals room

/-! ## A round -/

/-- A round's inputs of `G`, before the rotation. -/
def keyIn (j : Nat) : List Instr :=
  [movS .eax (keySlot 0), addS .eax (keySlot 2), subI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j)) .eax,
   movS .eax (keySlot 1), subS .eax (keySlot 3), addI .eax (Spec.Seed.kc.getD j 0), st (uSlot (2 * j + 1)) .eax]

theorem keyRound_eq (j : Nat) :
    keyRound j = keyIn j ++ (if j % 2 = 0 then rot64 0 8 0xFF000000 else rot64 2 24 0x000000FF) := rfl

theorem uSlot_lt {i : Nat} (hi : i < 32) : uSlot i < kSlots := by simp [uSlot, slots_eq]; omega_arith

theorem keyIn_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyIn j) s = some s' ∧
      slotW s' (uSlot (2 * j)) = (kwS s).1 + (kwS s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kwS s).2.1 - (kwS s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < kSlots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hu0 := uSlot_lt (i := 2 * j) (by omega_arith)
  have hu1 := uSlot_lt (i := 2 * j + 1) (by omega_arith)
  have hk : ∀ w < 4, keySlot w < kSlots := fun w hw => keySlot_lt hw
  have hf : (s.gpr .edi).toNat + 4 * kSlots ≤ 2 ^ 32 := h.fit
  have hne : ∀ w, keySlot w ≠ uSlot (2 * j) := fun w => by simp [keySlot, uSlot]; omega_arith
  have hne' : uSlot (2 * j + 1) ≠ uSlot (2 * j) := by simp [uSlot]
  rw [keyIn, runBlock_cons, exec_movS' (hk 0 (by decide)) .eax, runStep_some, runBlock_cons,
    exec_addS' (hk 2 (by decide)) .eax, runStep_some, runBlock_cons, exec_subI, runStep_some, runBlock_cons,
    exec_st' hu0 .eax, runStep_some, runBlock_cons, exec_movS' (hk 1 (by decide)) .eax, runStep_some,
    runBlock_cons, exec_subS' (hk 3 (by decide)) .eax, runStep_some, runBlock_cons, exec_addI, runStep_some,
    runBlock_cons, exec_st' hu1 .eax, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, fun k hk' h1 h2 => ?_, fun r hr => ?_, rfl, rfl, ?_⟩
  · simp only [slotW, kwS, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hu0 hu1, ite_eq_right hne'.symm, readW_slot_write hf _ hu0 hu0, ite_eq_left rfl]
  · simp only [slotW, kwS, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hu1 hu1, ite_eq_left rfl, readW_slot_write hf _ (hk 1 (by decide)) hu0,
      ite_eq_right (hne 1), readW_slot_write hf _ (hk 3 (by decide)) hu0, ite_eq_right (hne 3)]
  · simp only [slotW, mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    rw [readW_slot_write hf _ hk' hu1, ite_eq_right h2, readW_slot_write hf _ hk' hu0, ite_eq_right h1]
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ hr, gpr_arithFlags]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, gpr_setReg, mem_arithFlags, gpr_arithFlags,
      slotA, sb, reduceCtorEq, ↓reduceIte]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (slot_in h hu0)).writeW List.mem_cons_self _
      (slot_in h hu1)
  all_goals room

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧ kwS s' = keyStep j (kwS s) ∧
      slotW s' (uSlot (2 * j)) = (kwS s).1 + (kwS s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kwS s).2.1 - (kwS s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < kSlots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → (k < keySlot 0 ∨ keySlot 4 ≤ k) →
        slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, e₁, a₁, b₁, o₁, g₁, rd₁, wr₁, f₁⟩ := keyIn_ok hj h
  have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
  have h₁ : Room s₁ := h.congr sb₁ wr₁
  have hne : ∀ w < 4, keySlot w ≠ uSlot (2 * j) ∧ keySlot w ≠ uSlot (2 * j + 1) := fun w hw => by
    simp [keySlot, uSlot]; omega_arith
  have k₁ : ∀ w < 4, slotW s₁ (keySlot w) = slotW s (keySlot w) := fun w hw =>
    o₁ _ (keySlot_lt hw) (hne w hw).1 (hne w hw).2
  have rot : ∃ s₂, runBlock isa (if j % 2 = 0 then rot64 0 8 0xFF000000 else rot64 2 24 0x000000FF) s₁ = some s₂ ∧
      kwS s₂ = keyStep j (kwS s) ∧
      (∀ k < kSlots, (k < keySlot 0 ∨ keySlot 4 ≤ k) → slotW s₂ k = slotW s₁ k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      Frame [scratchR s₁] s₁.mem s₂.mem := by
    by_cases he : j % 2 = 0
    · rw [ite_eq_left he]
      obtain ⟨s₂, e₂, x₂, y₂, o₂, rest⟩ := rot64_ok (k := 0) (n := 8) (by decide) (by decide) (by decide) 0xFF000000 h₁
      refine ⟨s₂, e₂, ?_, fun k hk hk' => o₂ k hk (by simp only [keySlot] at hk' ⊢; omega_arith)
        (by simp only [keySlot] at hk' ⊢; omega_arith), rest⟩
      rw [keyStep, ite_eq_left he]; unfold kwS; dsimp only
      rw [x₂, y₂, o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]),
        o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]), k₁ 0 (by decide),
        k₁ 1 (by decide), k₁ 2 (by decide), k₁ 3 (by decide), xr_hi, xr_lo, rotr8_hi, rotr8_lo]
    · rw [ite_eq_right he]
      obtain ⟨s₂, e₂, x₂, y₂, o₂, rest⟩ := rot64_ok (k := 2) (n := 24) (by decide) (by decide) (by decide) 0x000000FF h₁
      refine ⟨s₂, e₂, ?_, fun k hk hk' => o₂ k hk (by simp only [keySlot] at hk' ⊢; omega_arith)
        (by simp only [keySlot] at hk' ⊢; omega_arith), rest⟩
      rw [keyStep, ite_eq_right he]; unfold kwS; dsimp only
      rw [x₂, y₂, o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]),
        o₂ _ (keySlot_lt (by decide)) (by simp [keySlot]) (by simp [keySlot]), k₁ 0 (by decide),
        k₁ 1 (by decide), k₁ 2 (by decide), k₁ 3 (by decide), xl_hi, xl_lo, rotl8_hi, rotl8_lo]
  obtain ⟨s₂, e₂, k₂, o₂, g₂, rd₂, wr₂, f₂⟩ := rot
  have hu0 : uSlot (2 * j) < keySlot 0 := by simp [keySlot, uSlot]; omega_arith
  have hu1 : uSlot (2 * j + 1) < keySlot 0 := by simp [keySlot, uSlot]; omega_arith
  refine ⟨s₂, by rw [keyRound_eq, runBlock_append, e₁, Option.bind_some, e₂], k₂,
    by rw [o₂ _ (uSlot_lt (by omega_arith)) (.inl hu0), a₁], by rw [o₂ _ (uSlot_lt (by omega_arith)) (.inl hu1), b₁],
    fun k hk h1 h2 h3 => by rw [o₂ k hk h3, o₁ k hk h1 h2], fun r h1 h2 h3 => by rw [g₂ r h1 h2 h3, g₁ r h1],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁], f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩

/-- The inputs of `G` from round `j + 1`'s key words. -/
theorem gInput_even (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j) = (keyWords key j).1 + (keyWords key j).2.2.1 - Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith, ite_true]

theorem gInput_odd (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j + 1) = (keyWords key j).2.1 - (keyWords key j).2.2.2 + Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith]; rfl

/-- The first `n` rounds of the key schedule. -/
theorem keyRounds_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hk : kwS s = keyWords key 0) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap keyRound) s = some s' ∧ Room s' ∧
      kwS s' = keyWords key n ∧ (∀ i < 2 * n, slotW s' (uSlot i) = gInput key i) ∧
      (∀ k < kSlots, (k < uSlot 0 ∨ uSlot (2 * n) ≤ k) → (k < keySlot 0 ∨ keySlot 4 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, h, hk, fun i hi => by omega_arith, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, h₁, k₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega_arith)
    obtain ⟨s₂, e₂, k₂, a₂, b₂, o₂, g₂, rd₂, wr₂, f₂⟩ := keyRound_ok (j := n) (by omega_arith) h₁
    have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide) (by decide) (by decide)
    have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide) (by decide) (by decide), sb₁]
    have hK : uSlot 32 ≤ keySlot 0 := by decide
    refine ⟨s₂, ?_, h.congr sb₂ (by rw [wr₂, wr₁]), by rw [k₂, k₁]; rfl, fun i hi => ?_, fun k hk1 hk2 hk3 => ?_,
      fun r h1 h2 h3 => by rw [g₂ r h1 h2 h3, g₁ r h1 h2 h3], by rw [rd₂, rd₁], by rw [wr₂, wr₁],
      f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega_arith) with hi' | rfl | rfl
      · rw [o₂ _ (uSlot_lt (by omega_arith)) (by simp [uSlot]; omega_arith) (by simp [uSlot]; omega_arith)
          (.inl (by simp [uSlot, keySlot]; omega_arith)), v₁ i hi']
      · rw [a₂, k₁, gInput_even]
      · rw [b₂, k₁, gInput_odd]
    · rw [o₂ k hk1 (by simp [uSlot] at hk2 ⊢; omega_arith) (by simp [uSlot] at hk2 ⊢; omega_arith) hk3,
        o₁ k hk1 (by simp [uSlot] at hk2 ⊢; omega_arith) hk3]

/-- A word of a buffer of `n` words is inside it. -/
theorem word_sub {b : BitVec 32} {n k : Nat} (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * n⟩ := by
  rw [slot_addr (by omega_arith)]
  exact Offset.sub_base _ (by omega_arith)

/-! ## The key's words -/

/-- `mov eax, [ecx + 4 w]; bswap eax; mov [edi + 4 keySlot w], eax` for each `w < n`. -/
def keyWordsCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .bswap .eax, st (keySlot w) .eax]

theorem keyLoad_eq : keyLoad = ([.mov .ecx (.mem (argOp 0))] : List Instr) ++ keyWordsCode 4 := rfl

/-- The key at `K` (in `ecx`), readable and apart from the scratch buffer. -/
structure KeyPre (s : State) (K : BitVec 32) : Prop where
  room : Room s
  ecx : s.gpr .ecx = K
  mem : (⟨K.setWidth 64, 16⟩ : Region) ∈ s.rd ++ s.wr
  fit : K.toNat + 16 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨K.setWidth 64, 16⟩ (scratchR s)

theorem ldKey_ok {w : Nat} (hw : w < 4) {s : State} {K : BitVec 32} (hs : KeyPre s K) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx (4 * w))), .bswap .eax, st (keySlot w) .eax] s = some s' ∧
      (∀ j < kSlots, slotW s' j =
        if j = keySlot w then byteRev32 (s.mem.readW (wordAddr K w) 32) else slotW s j) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hK := hs.fit
  obtain hk := keySlot_lt hw
  let v := s.mem.readW (wordAddr K w) 32
  obtain hea : s.ea (at_ .ecx (4 * w)) = wordAddr K w := by
    show addr (s.gpr .ecx) (4 * w) = _; rw [hs.ecx]
  obtain hin : InRegions (s.rd ++ s.wr) (wordAddr K w) 4 := ⟨_, hs.mem, slot_contains K (n := 4) hw (by omega_arith)⟩
  let s₁ := s.setReg .eax v
  let s₂ := s₁.setReg .eax (bswap v)
  obtain h₂ : Room s₂ := room_setReg (room_setReg hs.room (by decide) _) (by decide) _
  obtain e : runBlock isa [.mov .eax (.mem (at_ .ecx (4 * w))), .bswap .eax, st (keySlot w) .eax] s =
      some (setMem s₂ (s₂.mem.writeW (slotA s₂ (keySlot w)) (s₂.gpr .eax))) := by
    rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx (4 * w)))) s = some s₁ by
        simp only [exec, readSrc, hea, State.load32, hin, ↓reduceIte, Option.map_some]; rfl,
      runStep_some, runBlock_cons,
      show exec (.bswap .eax) s₁ = some s₂ by
        simp only [exec, s₂, s₁, gpr_setReg_self],
      runStep_some, runBlock_cons, exec_st h₂ hk, runStep_some, runBlock_nil]
  obtain sl : slotA s₂ (keySlot w) = slotA s (keySlot w) := by
    simp only [s₂, s₁, slotA_setReg _ (show Reg.eax ≠ sb by decide)]
  refine ⟨_, e, fun j hj => ?_, fun r hr => ?_, rfl, rfl, ?_⟩
  · rw [slotW_setMem_write h₂ hk hj, slotW_setReg _ (by decide), slotW_setReg _ (by decide)]
    simp only [s₂, gpr_setReg_self]; rfl
  · simp only [gpr_setMem, s₂, s₁, gpr_setReg_of_ne _ _ hr]
  · show Frame _ s.mem (s₂.mem.writeW _ _)
    rw [sl]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in hs.room hk)

theorem keyWords_ok {s : State} {K : BitVec 32} (hs : KeyPre s K) :
    ∀ n ≤ 4, ∃ s', runBlock isa (keyWordsCode n) s = some s' ∧
      (∀ w < n, slotW s' (keySlot w) = byteRev32 (s.mem.readW (wordAddr K w) 32)) ∧
      (∀ j < kSlots, (j < keySlot 0 ∨ keySlot n ≤ j) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun w hw => by omega_arith, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega_arith)
    obtain sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
    obtain hs₁ : KeyPre s₁ K := ⟨hs.room.congr sb₁ wr₁, by rw [g₁ _ (by decide)]; exact hs.ecx,
      by rw [rd₁, wr₁]; exact hs.mem, hs.fit, by unfold scratchR; rw [sb₁]; exact hs.sep⟩
    obtain ⟨s₂, e₂, v₂, g₂, rd₂, wr₂, f₂⟩ := ldKey_ok (w := n) (by omega_arith) hs₁
    have hK := hs.fit
    obtain key₁ : s₁.mem.readW (wordAddr K n) 32 = s.mem.readW (wordAddr K n) 32 :=
      f₁.readW (r := ⟨wordAddr K n, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hs.sep.sub_left (word_sub (n := 4) (by omega_arith) (by omega_arith))) (by decide)
    refine ⟨s₂, ?_, fun w hw => ?_, fun j hj hj' => ?_, fun r hr => by rw [g₂ r hr, g₁ r hr],
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩
    · rw [keyWordsCode, List.range_succ, List.flatMap_append, runBlock_append]
      rw [keyWordsCode] at e₁
      rw [e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rw [v₂ _ (keySlot_lt (by omega_arith))]
      by_cases hwn : w = n
      · subst hwn; rw [ite_eq_left rfl, key₁]
      · rw [ite_eq_right (by simp [keySlot]; omega_arith), v₁ w (by omega_arith)]
    · rw [v₂ j hj, ite_eq_right (by simp [keySlot] at hj' ⊢; omega_arith),
        o₁ j hj (by simp [keySlot] at hj' ⊢; omega_arith)]

/-! ## `G` of sixteen inputs -/

section

open VG.X86.StraightSse VG.Impl.Seed.X86.Sse
open VG.Proof.Seed.X86.Sse (QW GOk gCall_wp')

/-- The scratch buffer's slots of 16 bytes, for the copies to `G`'s. -/
def cfgI : Cfg := ⟨sb, 46, .esi, 0, tbr, tableName, table⟩
/-- The schedule's, with the scratch buffer's to read. -/
def cfgO : Cfg := ⟨.esi, 8, sb, 46, tbr, tableName, table⟩

def atoms : Env XE := { reg := fun _ => none, slot := fun k => some (.atom k) }

theorem copyIn_chk : ((List.range 2).all fun h => check exprs cfgI (fun _ => none) (copyIn h) atoms fun e =>
    (List.range 4).all fun k => e.slot (gS + k) == some (.atom (36 + 4 * h + k))) = true := by kernel_rfl

theorem copyOut_chk : ((List.range 2).all fun h => check exprs cfgO (fun n => some (.atom (100 + n))) (copyOut h) atoms fun e =>
    (List.range 4).all fun k => e.slot (4 * h + k) == some (.atom (100 + (gS + k)))) = true := by kernel_rfl

theorem copy_stores : ((List.range 2).all fun h => (stored cfgI (copyIn h)).all (fun k => 32 ≤ k && k < 36) &&
    (stored cfgO (copyOut h)).all (fun k => k / 4 == h)) = true := by kernel_rfl

/-- What a chunk needs of the state, with the scratch buffer at `b` and the schedule at `P`. -/
structure KEnv (s : State) (b P : BitVec 32) : Prop where
  base : s.gpr sb = b
  esi : s.gpr .esi = P
  tb : s.gpr tbr = s.syms tableName
  scr : (⟨b.setWidth 64, 4 * kSlots⟩ : Region) ∈ s.wr
  sch : (⟨P.setWidth 64, 128⟩ : Region) ∈ s.wr
  fitB : b.toNat + 4 * kSlots ≤ 2 ^ 32
  fitP : P.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨P.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * kSlots⟩
  stkB : Region.Disjoint (below (s.gpr .esp) 4) ⟨b.setWidth 64, 4 * kSlots⟩
  stkP : Region.Disjoint (below (s.gpr .esp) 4) ⟨P.setWidth 64, 128⟩

variable {s : State} {b P : BitVec 32}

theorem KEnv.congr (h : KEnv s b P) {s' : State} (hg : s'.gpr = s.gpr) (hw : s'.wr = s.wr) (hs : s'.syms = s.syms) :
    KEnv s' b P :=
  ⟨by rw [hg]; exact h.base, by rw [hg]; exact h.esi, by rw [hg, hs]; exact h.tb, by rw [hw]; exact h.scr,
    by rw [hw]; exact h.sch, h.fitB, h.fitP, h.sep, by rw [hg]; exact h.stkB, by rw [hg]; exact h.stkP⟩

theorem KEnv.fit (h : KEnv s b P) : b.toNat + 16 * 46 ≤ 2 ^ 32 := by
  have := h.fitB
  rw [slots_eq] at this; omega_arith

theorem KEnv.acc (h : KEnv s b P) {k : Nat} (hk : k < 46) : InRegions s.wr (addr b (16 * k)) 16 := by
  have := h.fit
  refine ⟨_, h.scr, ?_⟩
  rw [addr_eq (by omega_arith), slots_eq]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem KEnv.accP (h : KEnv s b P) {k : Nat} (hk : k < 8) : InRegions s.wr (addr P (16 * k)) 16 := by
  have := h.fitP
  refine ⟨_, h.sch, ?_⟩
  rw [addr_eq (by omega_arith)]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem KEnv.okI (h : KEnv s b P) : Ok cfgI s := by
  have hf := h.fit
  refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero _), ?_, fun k hk j hj => absurd hj (Nat.not_lt_zero _), h.tb⟩
  · show InRegions s.wr (addr (s.gpr sb) (16 * k)) 16
    rw [h.base]; exact h.acc hk
  · show (s.gpr sb).toNat + 16 * 46 ≤ _
    rw [h.base]; exact hf

theorem KEnv.okO (h : KEnv s b P) : Ok cfgO s := by
  have hf := h.fit
  have hp := h.fitP
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_, h.tb⟩
  · show InRegions s.wr (addr (s.gpr .esi) (16 * k)) 16
    rw [h.esi]; exact h.accP hk
  · show InRegions (s.rd ++ s.wr) (addr (s.gpr sb) (16 * k)) 16
    rw [h.base]
    obtain ⟨r, hr, hc⟩ := h.acc hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · show (s.gpr .esi).toNat + 16 * 8 ≤ _
    rw [h.esi]; omega_arith
  · have hk : k < 8 := hk
    have hj : j < 46 := hj
    show Mem.Sep (addr (s.gpr .esi) (16 * k)) 16 (addr (s.gpr sb) (16 * j)) 16
    rw [h.esi, h.base, addr_eq (by omega_arith), addr_eq (by omega_arith)]
    intro x h1 h2
    exact (h.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right
      (Offset.sub_base _ (by rw [slots_eq]; omega_arith)) x h1 h2

/-- The inputs of `G`, in their slots of 16 bytes. -/
def UW (m : Mem) (b : BitVec 32) (U : Nat → BitVec 32) : Prop := ∀ r < 8, ∀ l < 4, dword (W m b (36 + r)) l = U (4 * r + l)

theorem copyIn_ok (h : KEnv s b P) {i : Nat} (hi : i < 2) {U : Nat → BitVec 32} (hU : UW s.mem b U) :
    ∃ s', runBlock isa (copyIn i) s = some s' ∧ Runs cfgI (copyIn i) s s' ∧ QW s'.mem b gS (fun j => U (16 * i + j)) := by
  have hc := List.all_eq_true.mp copyIn_chk i (List.mem_range.mpr hi)
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hc
  have hsl : ∀ m : Mem, ∀ k, m.readW (xAddr (s.gpr cfgI.base) k) 128 = W m b k := fun m k => by
    show m.readW (addr (s.gpr sb) _) 128 = _
    rw [h.base]; rfl
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => W s.mem b n) cfgI (fun _ => none) atoms s :=
    ⟨(fun r a ha => by cases ha), (fun k a hk ha => by cases ha; exact hsl _ k), fun k a hk ha => by cases ha⟩
  obtain ⟨s', hs', p'⟩ := run (exprs_sound fun n => W s.mem b n) h.okI hrel he
  refine ⟨s', hs', p'.runs, fun r hr l hl => ?_⟩
  have := p'.rel.slot (gS + r) _ (show gS + r < 46 by unfold gS; omega_arith)
    (eq_of_beq (List.all_eq_true.mp hpost r (List.mem_range.mpr hr)))
  rw [p'.gpr, hsl, XE.eval] at this
  rw [this, Nat.add_assoc, hU _ (by omega_arith) l hl, show 4 * (4 * i + r) + l = 16 * i + (4 * r + l) by omega_arith]

theorem copyOut_ok (h : KEnv s b P) {i : Nat} (hi : i < 2) {X : Nat → BitVec 32} (hX : QW s.mem b gS X) :
    ∃ s', runBlock isa (copyOut i) s = some s' ∧ Runs cfgO (copyOut i) s s' ∧
      (∀ r < 4, ∀ l < 4, dword (W s'.mem P (4 * i + r)) l = X (4 * r + l)) ∧
      ∀ k < 8, k / 4 ≠ i → W s'.mem P k = W s.mem P k := by
  have hc := List.all_eq_true.mp copyOut_chk i (List.mem_range.mpr hi)
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hc
  have hsl : ∀ m : Mem, ∀ k, m.readW (xAddr (s.gpr cfgO.base) k) 128 = W m P k := fun m k => by
    show m.readW (addr (s.gpr .esi) _) 128 = _
    rw [h.esi]; rfl
  have hrel : Rel (fun (e : XE) x => x = e.eval fun n => if n < 100 then W s.mem P n else W s.mem b (n - 100)) cfgO
      (fun n => some (.atom (100 + n))) atoms s := by
    refine ⟨(fun r a ha => by cases ha), (fun k a hk ha => ?_), fun k a hk ha => ?_⟩
    · cases ha
      have hk : k < 8 := hk
      rw [hsl, XE.eval, ite_eq_left (by omega_arith)]
    · cases ha
      rw [XE.eval, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left]
      show s.mem.readW (addr (s.gpr sb) _) 128 = _
      rw [h.base]; rfl
  obtain ⟨s', hs', p'⟩ := run (exprs_sound _) h.okO hrel he
  refine ⟨s', hs', p'.runs, fun r hr l hl => ?_, fun k hk hki => ?_⟩
  · have := p'.rel.slot (4 * i + r) _ (show 4 * i + r < 8 by omega_arith)
      (eq_of_beq (List.all_eq_true.mp hpost r (List.mem_range.mpr hr)))
    rw [p'.gpr, hsl, XE.eval, ite_eq_right (by omega_arith), Nat.add_sub_cancel_left] at this
    rw [this, hX r hr l hl]
  · rw [← hsl, ← hsl]
    refine p'.runs.kept k hk fun hm => ?_
    have st := List.all_eq_true.mp copy_stores i (List.mem_range.mpr hi)
    rw [Bool.and_eq_true] at st
    exact hki (eq_of_beq (List.all_eq_true.mp st.2 k hm))

/-- What chunks change. -/
abbrev chunkR (s : State) (b P : BitVec 32) : List Region :=
  [⟨b.setWidth 64, 4 * kSlots⟩, ⟨P.setWidth 64, 128⟩, below (s.gpr .esp) 4]

theorem keyChunk_wp (h : KEnv s b P) {i : Nat} (hi : i < 2) {U : Nat → BitVec 32} (hU : UW s.mem b U) :
    WP isa (keyChunk i) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame (chunkR s b P) s.mem s'.mem ∧
      (∀ r < 4, ∀ l < 4, dword (W s'.mem P (4 * i + r)) l = Spec.Seed.g (U (16 * i + (4 * r + l)))) ∧
      (∀ k < 8, k / 4 ≠ i → W s'.mem P k = W s.mem P k) ∧ ∀ k, 36 ≤ k → k < 46 → W s'.mem b k = W s.mem b k := by
  have hf := h.fit
  have hp := h.fitP
  have hsl := slots_eq
  obtain ⟨s₁, r₁, p₁, x₁⟩ := copyIn_ok h hi hU
  have h₁ := h.congr p₁.gpr p₁.wr p₁.syms
  have f₁ : Frame [⟨b.setWidth 64, 4 * kSlots⟩] s.mem s₁.mem := by
    have := p₁.frame
    simp only [slotRegion, show s.gpr cfgI.base = b from h.base] at this
    rw [hsl]
    exact this
  have hst : Region.Disjoint (below (s.gpr .esp) 4) (slotsR b 0 36) := h.stkB.sub_right (Offset.sub_base _ (by omega_arith))
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, WP.seq (gCall_wp' ⟨h₁.base, h₁.tb, ⟨fun k hk => h₁.acc (by omega_arith), by omega_arith⟩⟩
    (by rw [p₁.gpr]; exact hst) x₁ fun s₂ g₂ rd₂ wr₂ sy₂ f₂ _ x₂ => ?_)⟩)
  rw [p₁.gpr] at f₂
  have h₂ := h₁.congr g₂ wr₂ sy₂
  obtain ⟨s₃, r₃, p₃, v₃, k₃⟩ := copyOut_ok h₂ hi x₂
  have f₃ : Frame [⟨P.setWidth 64, 128⟩] s₂.mem s₃.mem := by
    have := p₃.frame
    simp only [slotRegion, show s₂.gpr cfgO.base = P from h₂.esi] at this
    exact this
  have fr : Frame (chunkR s b P) s.mem s₂.mem := by
    refine (f₁.sub fun r hr => ⟨_, List.mem_cons_self, ?_⟩).trans (f₂.sub fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact fun _ h => h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  have disP : ∀ k < 8, Region.Disjoint (slotsR P k 1) ⟨b.setWidth 64, 4 * kSlots⟩ ∧
      Region.Disjoint (slotsR P k 1) (below (s.gpr .esp) 4) := fun k hk =>
    ⟨h.sep.sub_left (Offset.sub_base _ (by omega_arith)), (h.stkP.sub_right (Offset.sub_base _ (by omega_arith))).symm⟩
  have keepP : ∀ k < 8, W s₂.mem P k = W s.mem P k := fun k hk => by
    rw [W_frame f₂ (by omega_arith) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (disP k hk).1.sub_right (Offset.sub_base _ (by omega_arith))
        · exact (disP k hk).2,
      W_frame f₁ (by omega_arith) fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact (disP k hk).1]
  have keepB : ∀ k, 36 ≤ k → k < 46 → W s₃.mem b k = W s.mem b k := fun k hk1 hk2 => by
    rw [W_frame f₃ (by omega_arith) fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (h.sep.sub_right (Offset.sub_base _ (by omega_arith))).symm,
      W_frame f₂ (by omega_arith) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint (b.setWidth 64) (.inr (by omega_arith)) (by omega_arith) (by decide)
        · exact (h.stkB.sub_right (Offset.sub_base _ (by omega_arith))).symm]
    have hsl' : ∀ m : Mem, m.readW (xAddr (s.gpr cfgI.base) k) 128 = W m b k := fun m => by
      show m.readW (addr (s.gpr sb) _) 128 = _
      rw [h.base]; rfl
    rw [← hsl', ← hsl']
    refine p₁.kept k hk2 fun hm => ?_
    have st := List.all_eq_true.mp copy_stores i (List.mem_range.mpr hi)
    rw [Bool.and_eq_true] at st
    have := List.all_eq_true.mp st.1 k hm
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at this
    omega_arith
  refine WP.of_runBlock ⟨s₃, r₃, by rw [p₃.gpr, g₂, p₁.gpr], by rw [p₃.rd, rd₂, p₁.rd], by rw [p₃.wr, wr₂, p₁.wr],
    by rw [p₃.syms, sy₂, p₁.syms], fr.trans (f₃.sub fun r hr => ⟨r, ?_, fun _ h => h⟩), v₃,
    fun k hk hki => by rw [k₃ k hk hki, keepP k hk], keepB⟩
  rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A doubleword of a slot of 16 bytes. -/
theorem word_W (m : Mem) {b : BitVec 32} {k : Nat} (hf : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m.readW (wordAddr b k) 32 = dword (W m b (k / 4)) (k % 4) := by
  rw [W, dword_readW _ _ (Nat.mod_lt _ (by decide)), addr_eq (by omega_arith), slot_addr (by omega_arith),
    Offset.add_ofNat_add_ofNat, show 16 * (k / 4) + 4 * (k % 4) = 4 * k by omega_arith]

/-- The two chunks: `G` of every input, to the schedule. -/
theorem keyChunks_wp (h : KEnv s b P) {U : Nat → BitVec 32} (hU : ∀ i < 32, s.mem.readW (wordAddr b (uSlot i)) 32 = U i)
    {c : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', (∀ o < 32, s'.mem.readW (wordAddr P o) 32 = Spec.Seed.g (U o)) →
      (∀ j, savedSlot ≤ j → j < kSlots → s'.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32) → s'.gpr = s.gpr →
      s'.rd = s.rd → s'.wr = s.wr → Frame (chunkR s b P) s.mem s'.mem → WP isa c s' Q) :
    WP isa (.seq (keyChunk 0) (.seq (keyChunk 1) c)) s Q := by
  have hf := h.fit
  have hp := h.fitP
  have hsl := slots_eq
  have hsv := savedSlot_eq
  have hU' : UW s.mem b U := fun r hr l hl => by
    rw [← hU (4 * r + l) (by omega_arith), word_W _ (by unfold uSlot; omega_arith)]
    unfold uSlot
    rw [show (144 + (4 * r + l)) / 4 = 36 + r by omega_arith, show (144 + (4 * r + l)) % 4 = l by omega_arith]
  refine WP.seq (WP.mono (keyChunk_wp h (i := 0) (by decide) hU') fun s₁ ⟨g₁, rd₁, wr₁, sy₁, f₁, v₁, _, k₁⟩ => ?_)
  refine WP.seq (WP.mono (keyChunk_wp (h.congr g₁ wr₁ sy₁) (i := 1) (by decide) (U := U) fun r hr l hl => by
    rw [k₁ _ (by omega_arith) (by omega_arith)]; exact hU' r hr l hl) fun s₂ ⟨g₂, rd₂, wr₂, sy₂, f₂, v₂, o₂, k₂⟩ => ?_)
  refine hQ s₂ (fun o ho => ?_) (fun j h1 h2 => ?_) (g₂.trans g₁) (rd₂.trans rd₁) (wr₂.trans wr₁) (f₁.trans (by
    unfold chunkR at f₂; rw [show s₁.gpr .esp = s.gpr .esp from congrFun g₁ _] at f₂; exact f₂))
  · by_cases hlo : o < 16
    · rw [word_W _ (by omega_arith), o₂ _ (by omega_arith) (by omega_arith)]
      have := v₁ (o / 4) (by omega_arith) (o % 4) (by omega_arith)
      rw [show 4 * 0 + o / 4 = o / 4 by omega_arith, show 16 * 0 + (4 * (o / 4) + o % 4) = o by omega_arith] at this
      exact this
    · rw [word_W _ (by omega_arith)]
      have := v₂ (o / 4 - 4) (by omega_arith) (o % 4) (by omega_arith)
      rw [show 4 * 1 + (o / 4 - 4) = o / 4 by omega_arith, show 16 * 1 + (4 * (o / 4 - 4) + o % 4) = o by omega_arith] at this
      exact this
  · rw [word_W _ (by omega_arith), word_W _ (by omega_arith), k₂ _ (by omega_arith) (by omega_arith), k₁ _ (by omega_arith) (by omega_arith)]

end

/-! ## The whole function -/

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains3 (s : State) (hfit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) {i : Nat} (hi : i < 3) :
    (⟨argAddr s 0, 12⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := toNat_addr (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega_arith),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega_arith)]
  exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)

theorem slotW_of {s : State} {b : BitVec 32} (h : s.gpr sb = b) (j : Nat) :
    slotW s j = s.mem.readW (wordAddr b j) 32 := by
  simp only [slotW, h]

theorem below_eq {E : BitVec 32} (h : 4 ≤ E.toNat) : below E 4 = ⟨E.setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
  show (⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- The return address is apart from the four bytes below it. -/
theorem ret_below {E : BitVec 32} (h : 4 ≤ E.toNat) : Region.Disjoint ⟨E.setWidth 64, 4⟩ (below E 4) := by
  have := VG.Offset.disjoint_below_above (E.setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  rw [below_eq h]; exact this.symm

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86.pre s₀) :
    WP isa expandKey s₀ fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, dkS, dkB, fLo⟩ := hp
  rw [← below_eq fLo] at dkS dkB
  let K := arg s₀ 0
  let P := arg s₀ 1
  let b := arg s₀ 2
  have fitK' : K.toNat + 16 ≤ 2 ^ 32 := fitK
  have fitS' : P.toNat + 128 ≤ 2 ^ 32 := fitS
  have fitB' : b.toNat + 4 * kSlots ≤ 2 ^ 32 := fitB
  obtain hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  obtain hwP : (⟨P.setWidth 64, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [P]
  obtain hrK : (⟨K.setWidth 64, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [K]
  obtain hrA : (⟨argAddr s₀ 0, 12⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * kSlots⟩] s₀.mem m → ∀ i < 3,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains3 s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 3,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains3 s₀ fitE hi⟩
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 2) hwS (argIn rfl rfl rfl 2 (by decide))
    (by rw [ea_arg rfl]; rfl)
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  -- The key's words.
  obtain ⟨s₂, e₂, c₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .ecx 0 (argIn rd₁ wr₁ esp₁ 0 (by decide))
  obtain sb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide)]; exact b₁
  obtain h₂ : Room s₂ := ⟨by rw [sb₂, wr₂, wr₁]; exact hwS.mem, by rw [sb₂]; exact fitB'⟩
  obtain kp₂ : KeyPre s₂ K :=
    ⟨h₂, by rw [c₂, ea_arg esp₁]; exact argR f₁ 0 (by decide),
      List.mem_append_left _ (by rw [rd₂, rd₁]; exact hrK), fitK', by unfold scratchR; rw [sb₂]; exact dKB⟩
  obtain ⟨s₃, e₃, v₃, o₃, g₃, rd₃, wr₃, f₃⟩ := keyWords_ok kp₂ 4 (Nat.le_refl _)
  obtain sb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), sb₂]
  obtain f₀₃ : Frame [⟨b.setWidth 64, 4 * kSlots⟩] s₀.mem s₃.mem :=
    f₁.trans (by rw [← m₂]; unfold scratchR at f₃; rw [sb₂] at f₃; exact f₃)
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), o₂ _ (by decide), esp₁]
  -- The key, as on entry.
  let key := Spec.Seed.blockAt s₀.mem (K.setWidth 64)
  obtain kw₃ : kwS s₃ = keyWords key 0 := by
    obtain hk : ∀ w < 4, s₂.mem.readW (wordAddr K w) 32 = s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * w)) 32 :=
      fun w hw => by
        rw [m₂, slot_addr (by omega_arith)]
        exact f₁.readW (r := ⟨K.setWidth 64 + BitVec.ofNat 64 (4 * w), 4⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact dKB.sub_left (Offset.sub_base _ (by omega_arith))) (by decide)
    simp only [kwS, keyWords]
    rw [v₃ 0 (by decide), v₃ 1 (by decide), v₃ 2 (by decide), v₃ 3 (by decide), hk 0 (by decide),
      hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide)]
  -- The schedule's pointer.
  obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := ldArg_ok s₃ .esi 1
    (argIn (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) esp₃ 1 (by decide))
  obtain sb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), sb₃]
  obtain h₄ : Room s₄ := h₂.congr (by rw [sb₄, sb₂]) (by rw [wr₄, wr₃])
  obtain esi₄ : s₄.gpr .esi = P := by rw [c₄, ea_arg esp₃]; exact argR f₀₃ 1 (by decide)
  -- The inputs of `G`.
  obtain ⟨s₅, e₅, h₅, -, v₅, o₅, g₅, rd₅, wr₅, f₅⟩ := keyRounds_ok key h₄
    (by rw [← kw₃]; simp only [kwS, slotW, m₄, sb₄, sb₃]) 16 (Nat.le_refl _)
  obtain sb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide), sb₄]
  have esp₅ : s₅.gpr .esp = s₀.gpr .esp := by
    rw [g₅ _ (by decide) (by decide) (by decide), o₄ _ (by decide), esp₃]
  have wr₀₅ : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, wr₂, wr₁]
  have f₀₅ : Frame [⟨b.setWidth 64, 4 * kSlots⟩] s₀.mem s₅.mem := by
    rw [← m₄] at f₀₃
    unfold scratchR at f₅; rw [sb₄] at f₅
    exact f₀₃.trans f₅
  -- The table's address, and `G`.
  refine WP.seq (WP.of_runBlock ⟨s₅, ?_, WP.seq (WP.mono (symFrame_ok Sse.tableName s₅ (by rw [esp₅]; exact fLo)) fun s₆ a₆ => ?_)⟩)
  · rw [runBlock_append, runBlock_append, runBlock_append,
      e₁, Option.bind_some, keyLoad_eq, runBlock_append, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅]
  have f₆ : Frame [below (s₀.gpr .esp) 4] s₅.mem s₆.mem := by rw [← esp₅]; exact a₆.frame
  refine WP.seq (Sse.ownTable_wp (by rw [a₆.addr, a₆.syms]) fun t gt mt rdt wrt syt _ _ => Wp.wp_mov fun s₇ v₇ => WP.block_nil ?_)
  have u₇ : Wp.Upd s₆ s₇ Sse.tbr (s₆.gpr .eax) := ⟨by rw [v₇.gpr, gt], fun r hr => by rw [v₇.other r hr, gt], v₇.mem.trans mt,
    v₇.rd.trans rdt, v₇.wr.trans wrt, v₇.syms.trans syt⟩
  have sb₇ : s₇.gpr sb = b := by rw [u₇.other _ (by decide), a₆.gpr _ (by decide), sb₅]
  have esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [u₇.other _ (by decide), a₆.gpr _ (by decide), esp₅]
  have hst : ∀ {k : Nat}, k < kSlots → Region.Disjoint ⟨wordAddr b k, 4⟩ (below (s₀.gpr .esp) 4) := fun hk =>
    (dkB.sub_right (slot_sub fitB' hk)).symm
  have m₇ : ∀ k < kSlots, s₇.mem.readW (wordAddr b k) 32 = s₅.mem.readW (wordAddr b k) 32 := fun k hk => by
    rw [u₇.mem]
    exact f₆.readW (Region.contains_self _ 4) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hst hk) (by decide)
  have he : KEnv s₇ b P := ⟨sb₇, by rw [u₇.other _ (by decide), a₆.gpr _ (by decide), g₅ _ (by decide) (by decide) (by decide), esi₄],
    by rw [u₇.gpr, a₆.addr, u₇.syms, a₆.syms], by rw [u₇.wr, a₆.wr, wr₀₅, hwr]; simp [b],
    by rw [u₇.wr, a₆.wr, wr₀₅]; exact hwP, fitB', fitS', dSB, by rw [esp₇]; exact dkB, by rw [esp₇]; exact dkS⟩
  refine keyChunks_wp he (U := fun i => slotW s₅ (uSlot i)) (fun i hi => by rw [m₇ _ (uSlot_lt hi), slotW_of sb₅])
    fun s₈ v₈ k₈ g₈ rd₈ wr₈ f₈ => ?_
  have edi₈ : s₈.gpr .edi = b := by rw [g₈]; exact sb₇
  -- The epilogue.
  obtain sv₈ : Saved s₀ b s₈.mem := by
    intro i hi
    obtain hs : savedSlot + i < kSlots := by rw [savedSlot_eq, slots_eq]; omega_arith
    rw [k₈ _ (by omega_arith) hs, m₇ _ hs, ← slotW_of sb₅,
      o₅ _ hs (.inr (by unfold uSlot savedSlot; omega_arith)) (.inr (by unfold keySlot savedSlot; omega_arith)),
      slotW_of sb₄, m₄, ← slotW_of sb₃, o₃ _ hs (.inr (by unfold keySlot savedSlot; omega_arith)),
      slotW_of sb₂, m₂]
    exact sv₁ i hi
  obtain ⟨s₉, e₉, rg₉, o₉, m₉, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [wr₈, u₇.wr, a₆.wr, wr₀₅]; exact hwS) edi₈ sv₈
  have f₀₈ : Frame [⟨b.setWidth 64, 4 * kSlots⟩, ⟨P.setWidth 64, 128⟩, below (s₀.gpr .esp) 4] s₀.mem s₈.mem := by
    refine (f₀₅.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans ((f₆.sub fun r hr => ⟨r, ?_, fun _ h => h⟩).trans ?_)
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self
    · rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · unfold chunkR at f₈
      rw [esp₇, u₇.mem] at f₈
      exact f₈
  refine WP.of_runBlock ⟨s₉, e₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₉ 0 (by decide)
    · exact rg₉ 1 (by decide)
    · exact rg₉ 2 (by decide)
    · exact rg₉ 3 (by decide)
    · rw [o₉ _ (fun i hi => by revert i; decide), g₈, esp₇]
  · rw [m₉]
    exact f₀₈.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dRB
      · exact dRS
      · exact ret_below fLo) (by decide)
  · show Spec.Seed.scheduleAt s₉.mem (P.setWidth 64) = Spec.Seed.expandKey key
    rw [Proof.Seed.expandKey_eq]
    apply Vector.ext; intro i hi
    rw [Proof.Seed.scheduleAt_readW _ _ i hi, Vector.getElem_ofFn, m₉, ← slot_addr (by omega_arith), v₈ i (by omega_arith),
      v₅ i (by omega_arith)]

/-! ## The contract, and constant time -/

/-- `expandKeyX86.pre`, by name. -/
structure KPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 16⟩, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 128⟩, ⟨(arg s 2).setWidth 64, 4 * Impl.Seed.X86.kSlots⟩]
  dSB : Region.Disjoint ⟨(arg s 1).setWidth 64, 128⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Seed.X86.kSlots⟩
  aS : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨(arg s 1).setWidth 64, 128⟩
  aB : Region.Disjoint ⟨argAddr s 0, 12⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Seed.X86.kSlots⟩
  rS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 128⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Seed.X86.kSlots⟩
  fS : (arg s 1).toNat + 128 ≤ 2 ^ 32
  fB : (arg s 2).toNat + 4 * Impl.Seed.X86.kSlots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  kS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ ⟨(arg s 1).setWidth 64, 128⟩
  kB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ ⟨(arg s 2).setWidth 64, 4 * Impl.Seed.X86.kSlots⟩
  fLo : 4 ≤ (s.gpr .esp).toNat

theorem KPre.of {s : State} (h : expandKeyX86.pre s) : KPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13, h14, h15, h16⟩

/-- The initial taint: `esp` public, and the words holding `schedule` and
`scratch` known to be the base addresses of the writable regions. -/
def expandKeyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128, 4 * Impl.Seed.X86.kSlots], argLen := 16,
    argBases := [(8, 0), (12, 1)], room := 4 }

theorem expandKeyTaint_wf {s : State} (hp : KPre s) : VG.X86.Taint.Wf expandKeyTaint s := by
  have hS := hp.fS; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [expandKeyTaint]; omega_using [hs], ?_⟩, ?_⟩ fun _ => ⟨hp.fLo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dSB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.rS hp.aS
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.rB hp.aB
  · intro p hp'
    simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.kS
    · exact hp.kB

theorem expandKeyTaint_agree {s₁ s₂ : State} (h₁ : expandKeyX86.pre s₁) (h₂ : expandKeyX86.pre s₂)
    (hpub : expandKeyX86.pub s₁ s₂) : VG.X86.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := KPre.of h₁; have hp₂ := KPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf hp₁, expandKeyTaint_wf hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 1 (by omega_using []), ha 2 (by omega_using [])]
  · simp only [expandKeyTaint] at hk
    rw [show VG.X86.Taint.depth expandKeyTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 16) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 16) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem expandKey_ct : ConstantTime isa expandKeyX86.pre expandKeyX86.pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) expandKeyTaint
    (fun _ _ h₁ h₂ hp => expandKeyTaint_agree h₁ h₂ hp) (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyX86.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyX86.post s s' :=
  expandKey_wp hs

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000` at `0x8004`. -/
def ekSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0

/-- A state satisfying the precondition. -/
def ekSat : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ekSatMem
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 736⟩]

theorem expandKey_verified :
    Verified X86.target expandKey (Proof.Seed.expandKeyScratchContract X86.abi 92 4) :=
  Verified.of_correct expandKey_correct expandKey_ct
    (by
      have a0 : arg ekSat 0 = 0x1000 := by decide
      have a1 : arg ekSat 1 = 0x2000 := by decide
      have a2 : arg ekSat 2 = 0x3000 := by decide
      have e : argAddr ekSat 0 = 0x8004 := by decide
      have esp : ekSat.gpr .esp = 0x8000 := rfl
      sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, expandKeyX86, Impl.Seed.X86.kSlots]
        [a0, a1, a2, e, esp] using ekSat)

/-- A state satisfying `vg_seed_expand_key`'s precondition: the key at
`0x1000` and the schedule at `0x2000`, as stack arguments at `0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 8⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Seed.expandKeyContract X86.abi 768).pre s := by
  implies_sat [Spec.Seed.expandKeyContract, Spec.Seed.expandKeySig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 764 2 184 expandKey)
      (Spec.Seed.expandKeyContract X86.abi 768) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 92) (post := Proof.Seed.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 4)
    (bytes := 764) expandKey_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.expandKeyPost_local _) (Proof.Seed.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- `vg_seed_expand_key` as emitted (`Impl.Seed.X86.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.Fn.expandKey (Spec.Seed.expandKeyContract X86.abi 768) 0 :=
  X86.Scrub.verifiedScrubbedSel (api := Spec.Seed.expandKeyApi) (W := 768)
    { code := Impl.StackScratch.X86.withStackScratchWiped 764 2 184 expandKey
      verified := expandKey_framed }
    Impl.Seed.X86.Fn.expandKeyWords (X86.Scrub.postOut_of_local (leak := none) X86.Scrub.ScrubAbi.plain
      (Proof.Seed.expandKeyPostOut_local _)) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.X86
