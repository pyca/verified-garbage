module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.X86.Straight
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Impl.Camellia.X86.ExpandKey
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Camellia.Layout32
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia's key schedule on x86 (32-bit)

`expandKey_wp`: `expandKey` (`Impl/Camellia/X86/ExpandKey.lean`) meets
`expandKeyC`, with the working space as the fourth argument and four bytes of
stack, for any block `mid` that leaves `KA` and `KB` in their slots (`MidOk`).
`loadKey_wp` leaves `KL` and `KR` in theirs; `revs_ok` byte-swaps the four
values into numbers (`NumOf`), and `stores_ok` stores the subkeys, which are
the specification's (`scheduleWords_expandKey`, `schedule_of_stores`).
`taint_agree` is what the taint analysis of an implementation starts from.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movS movR movI at_ rorI shrI andI argOp notR)
open VG.Proof.Camellia (byteOf getLsbD_byteOf hiW loW rotHalf hi_split lo_split hiW_append loW_append byteOf_wordAt
  hi_eq lo_eq sigE kaD2 kaD3 kaD_eq klkr_halves schedule_of_stores subkeys_length keyVals valNum)
open VG.Spec.Camellia (wordAt)

/-! ## The scratch buffer -/

/-- Slot `j`. -/
abbrev slotW (s : State) (j : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr sb) j) 32

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

/-- The scratch buffer at `b`, of `N` slots or more, the key schedule's values' at least, in the regions `rs`. -/
structure ScrInN (N : Nat) (rs : List Region) (b : BitVec 32) : Prop where
  mem : ∃ n, N ≤ n ∧ b.toNat + 4 * n ≤ 2 ^ 32 ∧ (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs
  fit : b.toNat + 4 * N ≤ 2 ^ 32
  min : 96 ≤ N

theorem setWidth_toNat (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega_arith)]

/-- Slot `k` of the scratch buffer at `b`, as a 64-bit offset. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_arith)

/-- Slot `k` is in the scratch buffer. -/
theorem slot_in {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega_arith)]
    have := setWidth_toNat b
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- A scratch buffer of exactly `N` slots. -/
theorem ScrInN.exact {N : Nat} {rs : List Region} {b : BitVec 32} (hr : (⟨b.setWidth 64, 4 * N⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * N ≤ 2 ^ 32) (hmin : 96 ≤ N := by decide) : ScrInN N rs b :=
  ⟨⟨N, Nat.le_refl _, hfit, hr⟩, hfit, hmin⟩

theorem ScrInN.slot {N : Nat} {rs : List Region} {b : BitVec 32} (h : ScrInN N rs b) {k : Nat} (hk : k < N) :
    InRegions rs (wordAddr b k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  slot_in hr hf (Nat.lt_of_lt_of_le hk hn)

/-- `mov d, s`. -/
theorem movR_ok (s : State) (d r₀ : Reg) :
    ∃ s', runBlock isa [movR d r₀] s = some s' ∧ s'.gpr d = s.gpr r₀ ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf :=
  ⟨s.setReg d (s.gpr r₀), rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl, rfl, rfl⟩

/-- `mov d, v`. -/
theorem movI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [movI d v] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d v, rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem eval_e (s : State) : isa.eval .e s = s.zf := rfl

theorem itePos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  by simp only [h, ↓reduceIte]

theorem iteNeg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp only [h, ↓reduceIte]

/-- Argument `i`'s address, while `esp` is as on entry. -/
theorem ea_arg {s₀ s : State} (h : s.gpr .esp = s₀.gpr .esp) (i : Nat) : s.ea (argOp i) = argAddr s₀ i := by
  show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = _
  rw [h]; rfl

/-- `mov d, [esp + 4 + 4 i]`: argument `i`. -/
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
theorem slot_sub {N : Nat} {b : BitVec 32} (hfit : b.toNat + 4 * N ≤ 2 ^ 32) {k : Nat} (hk : k < N) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * N⟩ := by
  rw [slot_addr (by omega_using [hfit, hk])]
  exact VG.Offset.sub_base _ (by omega_using [hk])

/-- A slot after a store to a slot. -/
theorem readW_slot_write {N : Nat} {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * N ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < N) (hk : k < N) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_using [hfit, hj]) (by omega_using [hfit, hk]) h) (by decide)

/-- `mov d, [n + 4 k]`, `n` holding `b`, a slot of the scratch buffer. -/
theorem ldSlot_ok {N : Nat} (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < N)
    (hw : ScrInN N s.wr b) :
    ∃ s', runBlock isa [.mov d (.mem (slotAt n k))] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov d (.mem (slotAt n k))) s = some (s.setReg d (s.mem.readW (wordAddr b k) 32)) by
    simp [exec, readSrc, State.load32, he, inRd (hw.slot hk)], runStep_some, runBlock_nil]

/-- `mov [n + 4 k], t`, `n` holding `b`, a slot of the scratch buffer. -/
theorem stSlot_ok {N : Nat} (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < N)
    (hw : ScrInN N s.wr b) :
    ∃ s', runBlock isa [.store (slotAt n k) t] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧ s'.cf = s.cf ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem := by
  have he : s.ea (slotAt n k) = wordAddr b k := by rw [slotAt, ea_mk, hn]
  refine ⟨{ s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) }, ?_, rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩
  rw [runBlock_cons]
  simp only [exec, State.store32, he, hw.slot hk, ↓reduceIte, runStep_some, runBlock_nil]

/-- Stores of registers to distinct N, through `n`, which none of them is. -/
theorem stW_list_ok {N : Nat} (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrInN N s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < N) →
    ∃ s', runBlock isa (L.map fun x => .store (slotAt n x.1) x.2) s = some s' ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < N → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
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
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct N into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok {N : Nat} (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrInN N s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < N) →
    ∃ s', runBlock isa (L.map fun x => .mov x.1 (.mem (slotAt n x.2))) s = some s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_app, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegsAt`. -/
def sreg (i : Nat) : Reg := (([.ebx, .esi, .edi, .ebp] : List Reg)[i]?).getD .ebx

theorem savedRegsAt_eq (j : Nat) : savedRegsAt j = (List.range 4).map fun i => (sreg i, j + i) := rfl

/-- The saved registers are in their N, from `j`. -/
def SavedAt (j : Nat) (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (wordAddr b (j + i)) 32 = s₀.gpr (sreg i)

theorem saveAt_ok {N : Nat} {s : State} {b : BitVec 32} {j k : Nat} (hj : j + 4 ≤ N) (hw : ScrInN N s.wr b)
    (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp k)) 4) (hb : s.mem.readW (s.ea (argOp k)) 32 = b) :
    ∃ s', runBlock isa (saveRegsAt j k) s = some s' ∧ s'.gpr .edi = b ∧
      (∀ r, r ≠ .eax → r ≠ .edi → s'.gpr r = s.gpr r) ∧ SavedAt j s b s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem ∧
      ∀ i, i < N → (i < j ∨ j + 4 ≤ i) → s'.mem.readW (wordAddr b i) 32 = s.mem.readW (wordAddr b i) 32 := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax k ha
  rw [hb] at v₁
  let L : List (Nat × Reg) := (List.range 4).map fun i => (j + i, sreg i)
  have hL : (savedRegsAt j).map (fun (r, i) => Instr.store (slotAt .eax i) r) =
      L.map fun x => .store (slotAt .eax x.1) x.2 := by
    rw [savedRegsAt_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 4).map fun i => j + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s₂, e₂, g₂, rd₂, wr₂, f₂, o₂, v₂⟩ := stW_list_ok .eax L s₁ v₁ (by rw [wr₁]; exact hw)
    (by rw [hslots]; exact List.pairwise_map.mpr (List.nodup_range.imp fun h e => h (Nat.add_left_cancel e)))
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      omega)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, -, -⟩ := movR_ok s₂ .edi .eax
  refine ⟨s₃, ?_, by rw [r₃, g₂, v₁], fun r h0 h7 => by rw [o₃ r h7, g₂, o₁ r h0], fun i hi => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [m₃, ← m₁]; exact f₂, fun i hi hji => ?_⟩
  · rw [saveRegsAt, runBlock_app, runBlock_app, e₁, Option.bind_some, hL, e₂, Option.bind_some, e₃]
  · rw [m₃, v₂ (j + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩),
      o₁ _ (show sreg i ≠ .eax by revert i; decide)]
  · rw [m₃, o₂ i ?_ hi, m₁]
    rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i' hi' h; omega_using [hji, hi', h]

theorem restoreAt_ok {N : Nat} {s₀ s : State} {b : BitVec 32} {j : Nat} (hj : j + 4 ≤ N) (hw : ScrInN N s.wr b)
    (hb : s.gpr .edi = b) (hs : SavedAt j s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegsAt j) s = some s' ∧ (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 4, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := [(.ebx, j), (.esi, j + 1), (.ebp, j + 3)]
  have hLr : L.map (·.1) = [.ebx, .esi, .ebp] := rfl
  obtain ⟨s₁, e₁, m₁, rd₁, wr₁, o₁, v₁⟩ := ldW_list_ok .edi L s hb hw
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only <;> decide) (by rw [hLr]; decide)
    (by intro x hx; simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp only <;> omega_using [hj])
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok (N := N) s₁ .edi .edi (k := j + 2)
    (by rw [o₁ _ (by rw [hLr]; decide), hb]) (by omega_using [hj]) (by rw [wr₁]; exact hw)
  refine ⟨s₂, ?_, fun i hi => ?_, fun r hr => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [show restoreRegsAt j = (L.map fun x => .mov x.1 (.mem (slotAt .edi x.2))) ++
        [.mov .edi (.mem (slotAt .edi (j + 2)))] from rfl, runBlock_app, e₁, Option.bind_some, e₂]
  · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using [hi]) with rfl | rfl | rfl | rfl
    · show s₂.gpr .ebx = _
      rw [o₂ _ (by decide), v₁ (.ebx, j) (by simp [L])]; exact hs 0 (by decide)
    · show s₂.gpr .esi = _
      rw [o₂ _ (by decide), v₁ (.esi, j + 1) (by simp [L])]; exact hs 1 (by decide)
    · rw [show sreg 2 = .edi from rfl, v₂, m₁]; exact hs 2 (by decide)
    · show s₂.gpr .ebp = _
      rw [o₂ _ (by decide), v₁ (.ebp, j + 3) (by simp [L])]; exact hs 3 (by decide)
  · rw [o₂ r (hr 2 (by decide)), o₁ r (by
      simp only [hLr, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr 0 (by decide), hr 1 (by decide), hr 3 (by decide)⟩)]

/-! ## The values -/

/-- The four words at slot `a` hold the value `v`: byte `c` of `v.1 ++ v.2`
(the most significant first) is byte `c % 4` of word `c / 4`. -/
def VW (s : State) (a : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  ∀ c < 16, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) =
    (byteOf (if c < 8 then v.1 else v.2) (c % 8)).getLsbD j

theorem VW.congr {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h : VW s a v)
    (hs : ∀ i < 4, slotW s' (a + i) = slotW s (a + i)) : VW s' a v := fun c hc j hj => by
  rw [hs _ (by omega_arith)]; exact h c hc j hj

/-! ## Bytes -/

theorem bswap_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first | omega_arith | (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun hx => h x (Region.contains_self _ _) (by simp only [Region.Contains]; omega_arith)

/-! ## Words of 128-bit values -/

/-- Word `j` (0–3, the most significant first) of `x`. -/
def numWord (x : BitVec 128) (j : Nat) : BitVec 32 := (x >>> (96 - 32 * j)).setWidth 32

theorem numWord_bit (x : BitVec 128) {j p : Nat} (_hj : j < 4) (hp : p < 32) :
    (numWord x j).getLsbD p = x.getLsbD (96 - 32 * j + p) := by
  simp only [numWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hp, decide_true, Bool.true_and]

theorem rotl_bit (x : BitVec 128) {r k : Nat} (hr : r < 128) (hk : k < 128) :
    (x.rotateLeft r).getLsbD k = x.getLsbD ((k + 128 - r) % 128) := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [show r % 128 = r by omega_arith]
  split
  · congr 1; omega_arith
  · rw [decide_eq_true hk, Bool.true_and]; congr 1; omega_arith

/-- The four words at slot `a` are those of `x`. -/
def NumOf (s : State) (a : Nat) (x : BitVec 128) : Prop := ∀ j < 4, slotW s (a + j) = numWord x j

theorem NumOf.congr {s s' : State} {a : Nat} {x : BitVec 128} (h : NumOf s a x)
    (hs : ∀ j < 4, slotW s' (a + j) = slotW s (a + j)) : NumOf s' a x := fun j hj => by
  rw [hs j hj]; exact h j hj

/-- Byte-swapping the words of a value gives the words of its number. -/
theorem num_of_rev {s s' : State} {a : Nat} {v : BitVec 64 × BitVec 64} (hv : VW s a v)
    (h : ∀ j < 4, slotW s' (a + j) = bswap (slotW s (a + j))) : NumOf s' a (v.1 ++ v.2) := by
  intro j hj
  rw [h j hj]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  obtain ⟨k, t, hk, ht, rfl⟩ : ∃ k t, k < 4 ∧ t < 8 ∧ p = 8 * k + t := ⟨p / 8, p % 8, by omega_arith, by omega_arith, by omega_arith⟩
  rw [bswap_bit _ hk ht, numWord_bit _ hj hp]
  have := hv (4 * j + (3 - k)) (by omega_arith) t ht
  rw [show (4 * j + (3 - k)) / 4 = j by omega_arith, show (4 * j + (3 - k)) % 4 = 3 - k by omega_arith] at this
  rw [this, BitVec.getLsbD_append]
  by_cases h8 : 4 * j + (3 - k) < 8
  · rw [itePos h8, getLsbD_byteOf _ (by omega_arith) ht, iteNeg (show ¬ 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith
  · rw [iteNeg h8, getLsbD_byteOf _ (by omega_arith) ht, itePos (show 96 - 32 * j + (8 * k + t) < 64 by omega_arith)]
    congr 1; omega_arith

/-! ## Byte swaps in place -/

/-- `mov eax, [edi + 4 k]; bswap eax; mov [edi + 4 k], eax` for each `k` of `L`. -/
theorem revs_ok {N : Nat} {b : BitVec 32} : ∀ (L : List Nat) {s : State}, s.gpr sb = b → ScrInN N s.wr b → L.Nodup →
    (∀ k ∈ L, k < N) →
    ∃ s', runBlock isa (L.flatMap fun k => [movS .eax k, .bswap .eax, st k .eax]) s = some s' ∧
      (∀ k ∈ L, s'.mem.readW (wordAddr b k) 32 = bswap (s.mem.readW (wordAddr b k) 32)) ∧
      (∀ k < N, k ∉ L → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    obtain hx := hin x List.mem_cons_self
    have hfit := hw.fit
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := x) hb hx hw
    let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .eax .edi (b := b) (k := x)
      (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide)]; exact hb) hx
      (by rw [RegUpd.wr_setReg, wr₁]; exact hw)
    rw [List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := revs_ok (b := b) L (s := s₃)
      (by rw [show s₃.gpr sb = s₂.gpr sb from congrFun g₃ sb, RegUpd.gpr_setReg_of_ne _ _ (by decide),
        o₁ _ (by decide)]; exact hb)
      (by rw [wr₃, RegUpd.wr_setReg, wr₁]; exact hw) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    obtain hslot : ∀ j < N, s₃.mem.readW (wordAddr b j) 32 = if j = x then
        bswap (s.mem.readW (wordAddr b x) 32) else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₃, readW_slot_write hfit _ hj hx, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₃, RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr],
      by rw [rd', rd₃, RegUpd.rd_setReg, rd₁], by rw [wr', wr₃, RegUpd.wr_setReg, wr₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, show ([movS .eax x, .bswap .eax, st x .eax] : List Instr) =
        [.mov .eax (.mem (slotAt .edi x))] ++ ([.bswap .eax] ++ [.store (slotAt .edi x) .eax]) from rfl,
        runBlock_app, e₁, Option.bind_some, runBlock_app, runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil, Option.bind_some, e₃, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rw [k' _ hx hnd.1, hslot _ hx, ite_eq_left rfl]
      · rw [v' y hy', hslot _ (hin y (List.mem_cons_of_mem _ hy')), ite_eq_right (fun h => hnd.1 (by rw [← h]; exact hy'))]
    · simp only [List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [RegUpd.mem_setReg, m₁] at f₃
      exact (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

theorem valSlot_lt {N : Nat} (hN : 96 ≤ N) (v : Nat) (hv : v < 4) : valSlot v + 4 ≤ N :=
  Nat.le_trans (by rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide) hN

/-- The values' slots. -/
def revSlots : List Nat := [0, 1, 2, 3].flatMap fun v => (List.range 4).map (valSlot v + ·)

theorem revValues_eq : revValues = revSlots.flatMap fun k => [movS .eax k, .bswap .eax, st k .eax] := rfl

theorem revSlots_facts {N : Nat} (hN : 96 ≤ N) : revSlots.Nodup ∧ (∀ k ∈ revSlots, k < N) :=
  ⟨by decide, fun k hk => Nat.lt_of_lt_of_le (show k < 96 by revert k; decide) hN⟩

theorem mem_revSlots {v k : Nat} (hv : v < 4) (hk : k < 4) : valSlot v + k ∈ revSlots := by
  simp only [revSlots, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨v, by omega_arith, k, hk, rfl⟩

/-! ## Rotations -/

theorem rotr_mask (x : BitVec 32) {s : Nat} (h1 : 1 ≤ s) (h2 : s ≤ 31) :
    x.rotateRight (32 - s) &&& (BitVec.allOnes 32 <<< s) = x <<< s := by
  apply BitVec.eq_of_getLsbD_eq; intro p hp
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight]
  simp only [hp, decide_true, Bool.true_and, show (32 - s) % 32 = 32 - s by omega_arith]
  by_cases hps : p < s
  · simp [hps]
  · simp only [hps, decide_false, Bool.not_false, Bool.true_and, show ¬ p < 32 - (32 - s) by omega_arith, ↓reduceIte,
      decide_eq_true (show p - s < 32 by omega_arith), Bool.and_true]
    congr 1; omega_arith

/-- Word `o` of value `v` rotated left by `r`, in `eax`. -/
theorem rotWord_ok {N : Nat} {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hw : ScrInN N s.wr b) {v r o : Nat}
    (hv : v < 4) (hr : r < 128) (ho : o < 4) {x : BitVec 128} (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o) s = some s' ∧ s'.gpr .eax = numWord (x.rotateLeft r) o ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain hvs : valSlot v + 4 ≤ N := valSlot_lt hw.min v hv
  obtain hW : ∀ j < 4, s.mem.readW (wordAddr b (valSlot v + j)) 32 = numWord x j := fun j hj => by
    rw [← hb]; exact hx j hj
  unfold rotWord
  dsimp only
  split
  · rename_i h0
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok (N := N) s .eax .edi (k := valSlot v + (o + r / 32) % 4) hb
      (by omega_arith) hw
    refine ⟨s₁, e₁, ?_, fun r' h1 _ => o₁ r' h1, m₁, rd₁, wr₁⟩
    rw [v₁, hW _ (by omega_arith)]
    apply BitVec.eq_of_getLsbD_eq; intro p hp
    rw [numWord_bit _ (by omega_arith) hp, numWord_bit _ ho hp, rotl_bit _ hr (by omega_arith)]
    congr 1; omega_arith
  · rename_i h0
    obtain hs1 : 1 ≤ r % 32 ∧ r % 32 ≤ 31 := by omega_arith
    obtain hs2 : 1 ≤ 32 - r % 32 ∧ 32 - r % 32 ≤ 31 := by omega_arith
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok (N := N) s .eax .edi (k := valSlot v + (o + r / 32) % 4) hb
      (by omega_arith) hw
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, -, -⟩ := ldSlot_ok (N := N) s₁ .ebx .edi (b := b)
      (k := valSlot v + (o + r / 32 + 1) % 4) (by rw [o₁ _ (by decide)]; exact hb) (by omega_arith) (by rw [wr₁]; exact hw)
    let W1 := s₂.gpr .eax
    let W2 := s₂.gpr .ebx
    let a₃ := W1.rotateRight (32 - r % 32)
    let s₃ := (s₂.setFlags (some a₃.msb) (if 32 - r % 32 = 1 then some (a₃.msb ^^ a₃.getMsbD 1) else none)
      s₂.zf s₂.sf).setReg .eax a₃
    obtain e₃ : runBlock isa [rorI .eax (32 - r % 32)] s₂ = some s₃ := by
      simp only [rorI, runBlock_cons, exec, execShift, hs2, and_self, ↓reduceIte, runStep_some, runBlock_nil]
      rfl
    let a₄ := s₃.gpr .eax &&& (BitVec.allOnes 32 <<< (r % 32))
    let s₄ := (arithFlags s₃ a₄ false false).setReg .eax a₄
    have e₄ : runBlock isa [andI .eax (BitVec.allOnes 32 <<< (r % 32))] s₃ = some s₄ := rfl
    let a₅ := s₄.gpr .ebx >>> (32 - r % 32)
    let s₅ := (s₄.setFlags (some ((s₄.gpr .ebx).getLsbD (32 - r % 32 - 1)))
      (if 32 - r % 32 = 1 then some (s₄.gpr .ebx).msb else none) (some (a₅ == 0)) (some a₅.msb)).setReg .ebx a₅
    obtain e₅ : runBlock isa [shrI .ebx (32 - r % 32)] s₄ = some s₅ := by
      simp only [shrI, runBlock_cons, exec, execShift, hs2, and_self, ↓reduceIte, runStep_some, runBlock_nil]
      rfl
    let a₆ := s₅.gpr .eax ||| s₅.gpr .ebx
    let s₆ := (arithFlags s₅ a₆ false false).setReg .eax a₆
    have e₆ : runBlock isa [.alu .or .eax (.reg .ebx)] s₅ = some s₆ := rfl
    obtain hg : ∀ r', r' ≠ .eax → r' ≠ .ebx → s₆.gpr r' = s₂.gpr r' := fun r' h1 h2 => by
      simp only [s₆, s₅, s₄, s₃, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2,
        RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags]
    refine ⟨s₆, ?_, ?_, fun r' h1 h2 => by rw [hg r' h1 h2, o₂ r' h2, o₁ r' h1],
      by show s₂.mem = _; rw [m₂, m₁], by show s₂.rd = _; rw [rd₂, rd₁], by show s₂.wr = _; rw [wr₂, wr₁]⟩
    · rw [show ([movS .eax (valSlot v + (o + r / 32) % 4), movS .ebx (valSlot v + (o + r / 32 + 1) % 4),
          rorI .eax (32 - r % 32), andI .eax (BitVec.allOnes 32 <<< (r % 32)), shrI .ebx (32 - r % 32),
          .alu .or .eax (.reg .ebx)] : List Instr) =
          [.mov .eax (.mem (slotAt .edi (valSlot v + (o + r / 32) % 4)))] ++
            ([.mov .ebx (.mem (slotAt .edi (valSlot v + (o + r / 32 + 1) % 4)))] ++ ([rorI .eax (32 - r % 32)] ++
            ([andI .eax (BitVec.allOnes 32 <<< (r % 32))] ++ ([shrI .ebx (32 - r % 32)] ++
              [.alu .or .eax (.reg .ebx)])))) from rfl,
        runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
        runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
    · have h6 : s₆.gpr .eax = (W1 <<< (r % 32)) ||| (W2 >>> (32 - r % 32)) := by
        show s₅.gpr .eax ||| s₅.gpr .ebx = _
        rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setFlags, RegUpd.gpr_setReg_self]
        show (s₄.gpr .eax ||| s₄.gpr .ebx >>> (32 - r % 32)) = _
        rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_arithFlags]
        show (s₃.gpr .eax &&& _) ||| s₃.gpr .ebx >>> _ = _
        rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setFlags,
          rotr_mask _ hs1.1 hs1.2]
      rw [h6]
      show (s₂.gpr .eax <<< (r % 32)) ||| (s₂.gpr .ebx >>> (32 - r % 32)) = _
      rw [o₂ _ (by decide), v₁, v₂, m₁, hW _ (by omega_arith), hW _ (by omega_arith)]
      apply BitVec.eq_of_getLsbD_eq; intro p hp
      rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, numWord_bit _ ho hp,
        rotl_bit _ hr (by omega_arith)]
      by_cases hps : p < r % 32
      · have hlt : 32 - r % 32 + p < 32 := by omega_arith
        simp only [hp, decide_true, Bool.true_and, hps, Bool.not_true, Bool.false_and, Bool.false_or]
        rw [numWord_bit _ (by omega_arith) hlt]
        congr 1; omega_arith
      · rw [BitVec.getLsbD_of_ge (numWord x ((o + r / 32 + 1) % 4)) (32 - r % 32 + p) (by omega_arith)]
        simp only [hp, decide_true, Bool.true_and, hps, decide_false, Bool.not_false, Bool.or_false]
        rw [numWord_bit _ (by omega_arith) (by omega_arith)]
        congr 1; omega_arith

/-! ## Stores -/

/-- The schedule at `S` (in `edx`), writable, apart from the scratch buffer at `b`. -/
structure SchedOut (N : Nat) (s : State) (b S : BitVec 32) : Prop where
  edx : s.gpr .edx = S
  wr : (⟨S.setWidth 64, 272⟩ : Region) ∈ s.wr
  fit : S.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨S.setWidth 64, 272⟩ ⟨b.setWidth 64, 4 * N⟩

theorem SchedOut.congr {N : Nat} {s s' : State} {b S : BitVec 32} (h : SchedOut N s b S) (h2 : s'.gpr .edx = s.gpr .edx)
    (hwr : s'.wr = s.wr) : SchedOut N s' b S := ⟨h2.trans h.edx, hwr ▸ h.wr, h.fit, h.sep⟩

/-- A slot, kept by a frame of the schedule. -/
theorem SchedOut.slot {N : Nat} {s : State} {b S : BitVec 32} (h : SchedOut N s b S) (hfit : b.toNat + 4 * N ≤ 2 ^ 32)
    {m m' : Mem} {R : Region} (hf : Frame [R] m m') (hR : Region.Sub R ⟨S.setWidth 64, 272⟩) {k : Nat}
    (hk : k < N) : m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((h.sep.sub_left hR).symm.sub_left (slot_sub hfit hk))) (by decide)

/-- Word `o` of value `v` rotated left by `r`, byte-swapped and stored at `S + off`. -/
theorem wordStore_ok {N : Nat} {s : State} {b S : BitVec 32} (hb : s.gpr sb = b) (hw : ScrInN N s.wr b) (hS : SchedOut N s b S)
    {v r o off : Nat} (hv : v < 4) (hr : r < 128) (ho : o < 4) (hoff : off + 4 ≤ 272) {x : BitVec 128}
    (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (rotWord v r o ++ ([.bswap .eax, .store (at_ .edx off) .eax] : List Instr)) s = some s' ∧
      s'.mem = s.mem.writeW (S.setWidth 64 + BitVec.ofNat 64 off) (bswap (numWord (x.rotateLeft r) o)) ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := rotWord_ok hb hw hv hr ho hx
  let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
  obtain ea : s₂.ea (at_ .edx off) = S.setWidth 64 + BitVec.ofNat 64 off := by
    rw [at_, ea_mk, RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide) (by decide), hS.edx,
      addr_eq (by have := hS.fit; omega_arith)]
  obtain hin : InRegions s₂.wr (s₂.ea (at_ .edx off)) 4 := by
    rw [ea]
    exact ⟨_, by rw [RegUpd.wr_setReg, wr₁]; exact hS.wr,
      VG.Offset.contains_base _ (by omega_arith) (by have := hS.fit; have := setWidth_toNat S; omega_arith)⟩
  refine ⟨{ s₂ with mem := s₂.mem.writeW (s₂.ea (at_ .edx off)) (s₂.gpr .eax) }, ?_, ?_,
    fun r' h1 h2 => by
      show (s₁.setReg .eax _).gpr r' = _
      rw [RegUpd.gpr_setReg_of_ne _ _ h1, o₁ r' h1 h2], by rw [← rd₁]; rfl, by rw [← wr₁]; rfl⟩
  · rw [runBlock_app, e₁, Option.bind_some, runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl,
      runStep_some, runBlock_cons, show exec (.store (at_ .edx off) .eax) s₂ =
        some { s₂ with mem := s₂.mem.writeW (s₂.ea (at_ .edx off)) (s₂.gpr .eax) } by
        show s₂.store32 _ _ = _; simp only [State.store32, hin, ↓reduceIte], runStep_some, runBlock_nil]
  · show s₂.mem.writeW _ _ = _
    rw [ea, RegUpd.gpr_setReg_self, v₁, RegUpd.mem_setReg, m₁]

/-- The bytes of a stored word: the half's bytes `4 k … 4 k + 3`. -/
theorem stored_byte (x : BitVec 128) (r : Nat) (hi : Bool) {k q : Nat} (hk : k < 2) (hq : q < 4) :
    (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + k))).extractLsb' (8 * q) 8 =
      byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) (4 * k + q) := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  rw [BitVec.getLsbD_extractLsb', getLsbD_byteOf _ (by omega_arith) ht, bswap_bit _ hq ht,
    numWord_bit _ (by split <;> omega_arith) (by omega_arith)]
  simp only [ht, decide_true, Bool.true_and]
  cases hi
  · simp only [Bool.false_eq_true, ↓reduceIte, Spec.Camellia.lo, BitVec.getLsbD_setWidth,
      show 56 - 8 * (4 * k + q) + t < 64 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith
  · simp only [↓reduceIte, Spec.Camellia.hi, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      show 56 - 8 * (4 * k + q) + t < 64 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith

/-- A subkey: the high or low half of value `v` rotated left by `r`, stored at `S + 8 i`. -/
theorem subkey_ok {N : Nat} {s : State} {b S : BitVec 32} (hb : s.gpr sb = b) (hw : ScrInN N s.wr b) (hS : SchedOut N s b S)
    {i v r : Nat} {hi : Bool} (hv : v < 4) (hr : r < 128) (hi8 : 8 * i + 8 ≤ 272) {x : BitVec 128}
    (hx : NumOf s (valSlot v) x) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      (∀ j < 8, s'.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + j)) =
        byteOf (if hi then Spec.Camellia.hi x r else Spec.Camellia.lo x r) j) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i), 8⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit := hw.fit
  have hSf := hS.fit
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := wordStore_ok hb hw hS hv hr (o := (if hi then 0 else 2) + 0)
    (off := 8 * i + 4 * 0) (by split <;> omega_arith) (by omega_arith) hx
  obtain sub0 : Region.Sub ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩ ⟨S.setWidth 64, 272⟩ :=
    VG.Offset.sub_base _ (by omega_arith)
  obtain hx₁ : NumOf s₁ (valSlot v) x := hx.congr fun j hj => by
    simp only [slotW]
    rw [g₁ _ (by decide) (by decide), hb, m₁]
    obtain hj' : valSlot v + j < N := by have := valSlot_lt hw.min v hv; omega_arith
    exact hS.slot hfit ((Frame.refl _ s.mem).writeW (r := ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0), 4⟩)
      (List.mem_singleton_self _) (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0)))
      (Region.contains_self _ _)) sub0 hj'
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := wordStore_ok (by rw [g₁ _ (by decide) (by decide), hb])
    (by rw [wr₁]; exact hw) (hS.congr (g₁ _ (by decide) (by decide)) wr₁) hv hr
    (o := (if hi then 0 else 2) + 1) (off := 8 * i + 4 * 1) (by split <;> omega_arith) (by omega_arith) hx₁
  refine ⟨s₂, ?_, fun j hj => ?_, ?_, fun r' h1 h2 => by rw [g₂ r' h1 h2, g₁ r' h1 h2],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [subkey, show ([0, 1] : List Nat).flatMap (fun k => rotWord v r ((if hi then 0 else 2) + k) ++
        [.bswap .eax, .store (at_ .edx (8 * i + 4 * k)) .eax]) =
        (rotWord v r ((if hi then 0 else 2) + 0) ++ [.bswap .eax, .store (at_ .edx (8 * i + 4 * 0)) .eax]) ++
        (rotWord v r ((if hi then 0 else 2) + 1) ++ [.bswap .eax, .store (at_ .edx (8 * i + 4 * 1)) .eax]) by simp,
      runBlock_app, e₁, Option.bind_some, e₂]
  · rw [m₂]
    by_cases h4 : j < 4
    · rw [writeW32_other _ (VG.Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), m₁]
      obtain h0 := st_byte s.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 0))
        (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 0))) h4
      rw [VG.Offset.add_add, show 8 * i + 4 * 0 + j = 8 * i + j by omega_arith] at h0
      rw [h0, stored_byte x r hi (k := 0) (q := j) (by decide) h4, show 4 * 0 + j = j by omega_arith]
    · have h1 := st_byte s₁.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * i + 4 * 1))
        (bswap (numWord (x.rotateLeft r) ((if hi then 0 else 2) + 1))) (t := j - 4) (by omega_arith)
      rw [VG.Offset.add_add, show 8 * i + 4 * 1 + (j - 4) = 8 * i + j by omega_arith] at h1
      rw [h1, stored_byte x r hi (k := 1) (q := j - 4) (by decide) (by omega_arith), show 4 * 1 + (j - 4) = j by omega_arith]
  · rw [m₂, m₁]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub
      fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
      (simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub _ (by omega_arith) (by omega_arith))

/-- The half a subkey stores. -/
def subHalf (X : Nat → BitVec 128) (k : Nat × Nat × Bool) : BitVec 64 :=
  if k.2.2 then Spec.Camellia.hi (X k.1) k.2.1 else Spec.Camellia.lo (X k.1) k.2.1

/-- The subkeys `ks`, from entry `n` of the schedule. -/
theorem stores_ok {N : Nat} {b S : BitVec 32} {X : Nat → BitVec 128} : ∀ (ks : List (Nat × Nat × Bool)) (n : Nat) (s : State),
    s.gpr sb = b → ScrInN N s.wr b → SchedOut N s b S → (∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128) →
    8 * (n + ks.length) ≤ 272 → (∀ v < 4, NumOf s (valSlot v) (X v)) →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8, s'.mem (S.setWidth 64 + BitVec.ofNat 64 (8 * (n + i) + j)) =
        byteOf (subHalf X (ks.getD i (0, 0, true))) j) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ .eax → r' ≠ .ebx → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, s, _, _, _, _, _, _ => ⟨s, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _,
      fun _ _ _ => rfl, rfl, rfl⟩
  | (v, r, hi) :: ks, n, s, hb, hw, hS, hks, hlen, hX => by
    have hfit := hw.fit
    have hSf := hS.fit
    simp only [List.length_cons] at hlen
    obtain ⟨hv, hr⟩ := hks _ List.mem_cons_self
    obtain ⟨s₁, e₁, b₁, f₁, g₁, rd₁, wr₁⟩ := subkey_ok (i := n) (hi := hi) hb hw hS hv hr (by omega_arith) (hX v hv)
    obtain hsub : Region.Sub ⟨S.setWidth 64 + BitVec.ofNat 64 (8 * n), 8⟩ ⟨S.setWidth 64, 272⟩ :=
      VG.Offset.sub_base _ (by omega_arith)
    obtain hX₁ : ∀ u < 4, NumOf s₁ (valSlot u) (X u) := fun u hu => (hX u hu).congr fun j hj => by
      simp only [slotW]
      rw [g₁ _ (by decide) (by decide), hb]
      exact hS.slot hfit f₁ hsub (by have := valSlot_lt hw.min u hu; omega_arith)
    obtain hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide) (by decide), hb]
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := stores_ok (b := b) ks (n + 1) s₁ hb₁ (by rw [wr₁]; exact hw)
      (hS.congr (g₁ _ (by decide) (by decide)) wr₁) (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      (by omega_arith) hX₁
    refine ⟨s', ?_, fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    · rw [List.zipIdx_cons, List.flatMap_cons, runBlock_app, e₁, Option.bind_some]
      exact e'
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [f' _ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          intro hc
          rcases Nat.eq_zero_or_pos ks.length with h0 | hpos
          · simp only [Region.Contains, h0, Nat.mul_zero] at hc; omega_arith
          · exact VG.Proof.Camellia.not_contains_off _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith) hc),
          Nat.add_zero, b₁ j hj]
        simp only [subHalf, List.getD_cons_zero]
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega_arith⟩
        have := b' i' (by simp only [List.length_cons] at hi; omega_arith) j hj
        rw [show n + 1 + i' = n + (i' + 1) by omega_arith] at this
        rw [this, List.getD_cons_succ]
    · refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩) <;>
        (simp only [List.mem_singleton] at hr; subst hr; simp only [List.length_cons]
         exact VG.Offset.sub _ (by omega_arith) (by omega_arith))

/-! ## Halves in words -/

/-- The two words at slot `a` hold `x`: its byte `c` (the most significant
first) is byte `c % 4` of word `c / 4`. -/
def HW (s : State) (a : Nat) (x : BitVec 64) : Prop :=
  ∀ c < 8, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) = (byteOf x c).getLsbD j

theorem VW_of_HW {s : State} {a : Nat} {v : BitVec 64 × BitVec 64} (h1 : HW s a v.1) (h2 : HW s (a + 2) v.2) :
    VW s a v := fun c hc j hj => by
  by_cases h8 : c < 8
  · rw [itePos h8, Nat.mod_eq_of_lt h8]; exact h1 c h8 j hj
  · rw [iteNeg h8, show a + c / 4 = a + 2 + (c - 8) / 4 by omega_arith, show c % 4 = (c - 8) % 4 by omega_arith,
      show c % 8 = c - 8 by omega_arith]
    exact h2 (c - 8) (by omega_arith) j hj

/-- Two words loaded from `A` and `A + 4`. -/
theorem HW_words {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32) : HW s a (wordAt m A) := by
  intro c hc j hj
  obtain hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, W32.readW32_bit _ _ (by omega_arith) hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega_arith]

/-- The complements of two words loaded from `A` and `A + 4`. -/
theorem HW_not {s : State} {a : Nat} {m : Mem} {A : Addr} (h0 : slotW s a = m.readW A 32 ^^^ BitVec.allOnes 32)
    (h1 : slotW s (a + 1) = m.readW (A + BitVec.ofNat 64 4) 32 ^^^ BitVec.allOnes 32) :
    HW s a (~~~ wordAt m A) := by
  intro c hc j hj
  obtain hw : slotW s (a + c / 4) = m.readW (A + BitVec.ofNat 64 (4 * (c / 4))) 32 ^^^ BitVec.allOnes 32 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]; simp
    · exact h1
  rw [hw, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, getLsbD_byteOf _ hc hj, BitVec.getLsbD_not,
    W32.readW32_bit _ _ (by omega_arith) hj, ← getLsbD_byteOf _ hc hj, byteOf_wordAt _ _ hc, VG.Offset.add_add,
    show 4 * (c / 4) + c % 4 = c by omega_arith]
  simp [show 8 * (c % 4) + j < 32 by omega_arith, show 56 - 8 * c + j < 64 by omega_arith]

theorem HW_zero {s : State} {a : Nat} (h0 : slotW s a = 0) (h1 : slotW s (a + 1) = 0) : HW s a 0 := by
  intro c hc j hj
  obtain hw : slotW s (a + c / 4) = 0 := by
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h <;> rw [h]
    · rw [Nat.add_zero, h0]
    · exact h1
  rw [hw, getLsbD_byteOf _ hc hj]; simp

/-! ## Loads -/

/-- The key at `K` (in `ecx`), apart from the scratch buffer at `b`, and its
length `len` in the second argument's word at `A`. -/
structure KeyIn (N : Nat) (s : State) (b K : BitVec 32) (A : Addr) (len : Nat) : Prop where
  base : s.gpr sb = b
  scr : ScrInN N s.wr b
  ecx : s.gpr .ecx = K
  rd : (⟨K.setWidth 64, len⟩ : Region) ∈ s.rd
  fit : K.toNat + len ≤ 2 ^ 32
  sep : Region.Disjoint ⟨K.setWidth 64, len⟩ ⟨b.setWidth 64, 4 * N⟩
  le : len ≤ 32
  argEa : s.ea (argOp 1) = A
  argIn : InRegions (s.rd ++ s.wr) A 4
  argV : s.mem.readW A 32 = BitVec.ofNat 32 len
  argSep : Region.Disjoint ⟨A, 4⟩ ⟨b.setWidth 64, 4 * N⟩

theorem KeyIn.congr {N : Nat} {s s' : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn N s b K A len)
    (hb : s'.gpr sb = s.gpr sb) (hc : s'.gpr .ecx = s.gpr .ecx) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem) :
    KeyIn N s' b K A len :=
  ⟨hb.trans h.base, ⟨hwr ▸ h.scr.mem, h.scr.fit, h.scr.min⟩, hc.trans h.ecx, hrd ▸ h.rd, h.fit, h.sep, h.le,
    by rw [← h.argEa]; show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hsp],
    hrd ▸ hwr ▸ h.argIn,
    by rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.argSep) (by decide)]; exact h.argV, h.argSep⟩

/-- The key's word at offset `o`. -/
theorem KeyIn.word {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn N s b K A len) {o : Nat}
    (ho : o + 4 ≤ len) :
    s.ea (at_ .ecx o) = K.setWidth 64 + BitVec.ofNat 64 o ∧
      InRegions (s.rd ++ s.wr) (s.ea (at_ .ecx o)) 4 := by
  obtain e : s.ea (at_ .ecx o) = K.setWidth 64 + BitVec.ofNat 64 o := by
    rw [at_, ea_mk, h.ecx, addr_eq (by have := h.fit; omega_arith)]
  refine ⟨e, ⟨_, List.mem_append_left _ h.rd, ?_⟩⟩
  have := setWidth_toNat K
  rw [e]; exact VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; omega_arith)

/-- A word of the key, kept by a frame of the scratch buffer. -/
theorem KeyIn.keep {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn N s b K A len) {m m' : Mem}
    (hf : Frame [⟨b.setWidth 64, 4 * N⟩] m m') {o : Nat} (ho : o + 4 ≤ len) :
    m'.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 = m.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 :=
  hf.readW (VG.Offset.contains_base _ (by omega_arith) (by have := h.fit; have := setWidth_toNat K; omega_arith))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sep) (by decide)

/-- `mov eax, [ecx + o]`. -/
theorem ldKey_ok {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn N s b K A len) {o : Nat}
    (ho : o + 4 ≤ len) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx o))] s = some s' ∧
      s'.gpr .eax = s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨ea, ei⟩ := h.word ho
  refine ⟨s.setReg .eax (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32), ?_, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx o))) s =
      some (s.setReg .eax (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32)) by
    show (s.load32 (s.ea (at_ .ecx o))).map (s.setReg .eax) = _
    rw [ea] at ei ⊢
    simp only [State.load32, ei, ↓reduceIte, Option.map_some], runStep_some, runBlock_nil]

/-- `mov eax, [ecx + o]; mov [edi + 4 k], eax` for each `(o, k)` of `L`. -/
theorem loads_ok {N : Nat} {b K : BitVec 32} {A : Addr} {len : Nat} : ∀ (L : List (Nat × Nat)) {s : State},
    KeyIn N s b K A len → (L.map (·.2)).Nodup → (∀ x ∈ L, x.1 + 4 ≤ len ∧ x.2 < N) →
    ∃ s', runBlock isa (L.flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.2) 32 = s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 x.1) 32) ∧
      (∀ k < N, k ∉ L.map (·.2) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hk, hnd, hin => by
    obtain ⟨hx1, hx2⟩ := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldKey_ok hk hx1
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, -, -, f₂⟩ := stSlot_ok s₁ .eax .edi (b := b) (k := x.2)
      (by rw [o₁ _ (by decide)]; exact hk.base) hx2 (by rw [wr₁]; exact hk.scr)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfit := hk.scr.fit
    obtain f₂' : Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s₂.mem := by
      rw [← m₁]
      exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx2⟩
    obtain hk₂ : KeyIn N s₂ b K A len := hk.congr (by rw [show s₂.gpr sb = s₁.gpr sb from congrFun g₂ sb,
      o₁ _ (by decide)]) (by rw [g₂, o₁ _ (by decide)]) (by rw [g₂, o₁ _ (by decide)])
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) f₂'
    obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := loads_ok L hk₂ hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    obtain hslot : ∀ j < N, s₂.mem.readW (wordAddr b j) 32 = if j = x.2 then
        s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 x.1) 32 else s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx2, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by
        rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], f₂'.trans f'⟩
    · rw [List.flatMap_cons, show ([.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax] : List Instr) =
        [.mov .eax (.mem (at_ .ecx x.1))] ++ [.store (slotAt .edi x.2) .eax] from rfl, runBlock_app,
        runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.2 ∈ L.map (·.2)
        · exact absurd hin' hnd.1
        · rw [k' _ hx2 hin', hslot _ hx2, ite_eq_left rfl]
      · rw [v' y hy', hk.keep f₂' (hin y (List.mem_cons_of_mem _ hy')).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]

/-- `mov eax, [esp + 8]; cmp eax, v`: the key's length against `v`. -/
theorem cmpLen_ok {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (h : KeyIn N s b K A len) (v : Nat)
    (hv : v < 2 ^ 32) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 v))] s = some s' ∧
      s'.zf = some (decide (len = v)) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax 1 (by rw [h.argEa]; exact h.argIn)
  let a := s₁.gpr .eax
  let c : BitVec 32 := BitVec.ofNat 32 v
  refine ⟨arithFlags s₁ (a - c) (a.toNat < c.toNat) (subOverflow a c (a - c)), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr], by rw [RegUpd.mem_arithFlags, m₁],
    by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  · rw [show ([.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 v))] : List Instr) =
      [.mov .eax (.mem (argOp 1))] ++ [.alu .cmp .eax (.imm (BitVec.ofNat 32 v))] from rfl, runBlock_app, e₁,
      Option.bind_some]
    rfl
  · rw [RegUpd.zf_arithFlags, show a = _ from v₁, h.argEa, h.argV, ofNat32_sub_beq (by have := h.le; omega_arith) hv]

/-- `mov [edi + 4 k], eax` for each `k` of `ks`. -/
theorem storeAll_ok {N : Nat} {b : BitVec 32} : ∀ (ks : List Nat) {s : State}, s.gpr sb = b →
    ScrInN N s.wr b → (∀ k ∈ ks, k < N) →
    ∃ s', runBlock isa (ks.map fun k => st k .eax) s = some s' ∧
      (∀ k ∈ ks, s'.mem.readW (wordAddr b k) 32 = s.gpr .eax) ∧
      (∀ k < N, k ∉ ks → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, hb, hw, hk => by
    obtain hk0 : k < N := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, -, -, f₁⟩ := stSlot_ok s .eax .edi (b := b) (k := k) hb hk0 hw
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok ks (s := s₁)
      (by rw [show s₁.gpr sb = s.gpr sb from congrFun g₁ sb, hb]) (by rw [wr₁]; exact hw)
      fun k h => hk k (List.mem_cons_of_mem _ h)
    have hfit := hw.fit
    obtain hslot : ∀ j < N, s₁.mem.readW (wordAddr b j) 32 = if j = k then s.gpr .eax else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by rw [m₁, readW_slot_write hfit _ hj hk0]
    refine ⟨s', by rw [List.map_cons, ← List.singleton_append, runBlock_app,
        show ([st k .eax] : List Instr) = [.store (slotAt .edi k) .eax] from rfl, e₁, Option.bind_some]; exact e',
      fun j hj => ?_, fun j hj hn => ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin, g₁]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj', g₁]
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hk0⟩).trans f'

/-! ## The key -/

/-- `KR` as `klkr_halves` gives its halves. -/
def krOf (m : Mem) (A : Addr) (len : Nat) : BitVec 64 × BitVec 64 :=
  (if len = 16 then 0 else wordAt m (A + BitVec.ofNat 64 16),
   if len = 16 then 0 else if len = 24 then ~~~ wordAt m (A + BitVec.ofNat 64 16) else wordAt m (A + BitVec.ofNat 64 24))

/-- What a branch of `loadKey` leaves, from `s`: `KR` in its N. -/
structure KrPost (N : Nat) (s : State) (b : BitVec 32) (m₀ : Mem) (K : Addr) (len : Nat) (s' : State) : Prop where
  kr : VW s' krSlot (krOf m₀ K len)
  keep : ∀ k < N, k < krSlot ∨ krSlot + 4 ≤ k →
    s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem

theorem klSlot_eq : klSlot = 72 := rfl
theorem krSlot_eq : krSlot = 76 := rfl

theorem slotW_of {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (k : Nat) :
    slotW s k = s.mem.readW (wordAddr b k) 32 := by rw [slotW, hb]

/-- The key's words in `s` are those of `m₀`. -/
def KeySame (s : State) (m₀ : Mem) (K : Addr) (len : Nat) : Prop :=
  ∀ o, o + 4 ≤ len → s.mem.readW (K + BitVec.ofNat 64 o) 32 = m₀.readW (K + BitVec.ofNat 64 o) 32

theorem KeySame.frame {N : Nat} {s s' : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn N s b K A len)
    (h : KeySame s m₀ (K.setWidth 64) len) (hf : Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem) :
    KeySame s' m₀ (K.setWidth 64) len := fun o ho => by rw [hk.keep hf ho]; exact h o ho

/-- A key of 16 bytes: `KR` is zero. -/
theorem kr16_ok {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn N s b K A len)
    (h16 : len = 16) :
    ∃ s', runBlock isa (([movI .eax 0] : List Instr) ++ (List.range 4).map fun k => st (krSlot + k) .eax) s =
      some s' ∧ KrPost N s b m₀ (K.setWidth 64) len s' := by
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := movI_ok s .eax 0
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, f₄⟩ := storeAll_ok (b := b) ((List.range 4).map fun k => krSlot + k)
    (s := s₃) (by rw [o₃ _ (by decide)]; exact hk.base) (by rw [wr₃]; exact hk.scr)
    (fun k hk' => by simp only [List.mem_map, List.mem_range] at hk'; obtain ⟨k, hk', rfl⟩ := hk'
                     have := hk.scr.min; rw [krSlot_eq]; omega_arith)
  obtain hb₄ : s₄.gpr sb = b := by rw [g₄, o₃ _ (by decide)]; exact hk.base
  obtain hz : ∀ k < 4, slotW s₄ (krSlot + k) = 0 := fun k hk' => by
    rw [slotW_of hb₄, v₄ (krSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩), v₃]
  obtain e : krOf m₀ (K.setWidth 64) len = (0, 0) := by simp [krOf, h16]
  refine ⟨s₄, ?_, ⟨?_, fun k hk' h => ?_, fun r h1 => by rw [g₄, o₃ r h1],
    by rw [rd₄, rd₃], by rw [wr₄, wr₃], by rw [← m₃]; exact f₄⟩⟩
  · rw [runBlock_app, e₃, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e₄
  · rw [e]
    exact VW_of_HW (HW_zero (hz 0 (by decide)) (hz 1 (by decide))) (HW_zero (hz 2 (by decide)) (hz 3 (by decide)))
  · rw [k₄ k hk' (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; intro j hj h'; omega_arith), m₃]

/-- `mov eax, [ecx + o]; not eax; mov [edi + 4 k], eax`. -/
theorem ldNotSt_ok {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} (hk : KeyIn N s b K A len) {o k : Nat}
    (ho : o + 4 ≤ len) (hks : k < N) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx o)), notR .eax, st k .eax] s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b k) (s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 o) 32 ^^^
        BitVec.allOnes 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldKey_ok hk ho
  let x := s₁.gpr .eax ^^^ BitVec.allOnes 32
  let s₂ := (arithFlags s₁ x false false).setReg .eax x
  have e₂ : runBlock isa [notR .eax] s₁ = some s₂ := rfl
  obtain hb₂ : s₂.gpr sb = b := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_arithFlags, o₁ _ (by decide)]; exact hk.base
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, -, -, f₃⟩ := stSlot_ok s₂ .eax .edi (b := b) (k := k) hb₂ hks
    (by show ScrInN N s₁.wr b; rw [wr₁]; exact hk.scr)
  refine ⟨s₃, ?_, ?_, fun r hr => ?_, by rw [rd₃]; exact rd₁, by rw [wr₃]; exact wr₁, ?_⟩
  · rw [show ([.mov .eax (.mem (at_ .ecx o)), notR .eax, st k .eax] : List Instr) =
      [.mov .eax (.mem (at_ .ecx o))] ++ ([notR .eax] ++ [.store (slotAt .edi k) .eax]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [m₃, RegUpd.gpr_setReg_self]; show s₁.mem.writeW _ (s₁.gpr .eax ^^^ _) = _; rw [v₁, m₁]
  · rw [g₃, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, o₁ r hr]
  · rw [← m₁]
    exact f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hk.scr.fit hks⟩

/-- Keys of 24 or 32 bytes. -/
theorem krNot16_wp {N : Nat} {s : State} {b K : BitVec 32} {A : Addr} {len : Nat} {m₀ : Mem} (hk : KeyIn N s b K A len)
    (hm : KeySame s m₀ (K.setWidth 64) len) (hlen : len = 24 ∨ len = 32) :
    WP isa (.seq (.block [.mov .eax (.mem (at_ .ecx 16)), st krSlot .eax, .mov .eax (.mem (at_ .ecx 20)),
          st (krSlot + 1) .eax, .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 24)])
        (.ite .e
          (.block [.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax,
            .mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax])
          (.block [.mov .eax (.mem (at_ .ecx 24)), st (krSlot + 2) .eax, .mov .eax (.mem (at_ .ecx 28)),
            st (krSlot + 3) .eax]))) s
      (KrPost N s b m₀ (K.setWidth 64) len) := by
  have hfit := hk.scr.fit
  obtain h16 : len ≠ 16 := by omega_arith
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := loads_ok [(16, krSlot), (20, krSlot + 1)] hk (by decide)
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact ⟨by omega_arith, Nat.lt_of_lt_of_le (by decide) hk.scr.min⟩)
  obtain hk₃ : KeyIn N s₃ b K A len := hk.congr (g₃ _ (by decide)) (g₃ _ (by decide)) (g₃ _ (by decide)) rd₃ wr₃ f₃
  obtain ⟨s₄, e₄, z₄, g₄, m₄, rd₄, wr₄⟩ := cmpLen_ok hk₃ 24 (by decide)
  obtain hk₄ : KeyIn N s₄ b K A len := hk₃.congr (g₄ _ (by decide)) (g₄ _ (by decide)) (g₄ _ (by decide)) rd₄ wr₄
    (by rw [m₄]; exact Frame.refl _ _)
  obtain hm₄ : KeySame s₄ m₀ (K.setWidth 64) len := by
    have := hm.frame hk f₃; intro o ho; rw [m₄]; exact this o ho
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([.mov .eax (.mem (at_ .ecx 16)), st krSlot .eax, .mov .eax (.mem (at_ .ecx 20)),
        st (krSlot + 1) .eax, .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 24)] : List Instr) =
        ([(16, krSlot), (20, krSlot + 1)].flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]) ++
          [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm (BitVec.ofNat 32 24))] from rfl, runBlock_app, e₃,
      Option.bind_some, e₄], ?_⟩)
  obtain hl0 : s₄.mem.readW (wordAddr b krSlot) 32 = m₀.readW (K.setWidth 64 + BitVec.ofNat 64 16) 32 := by
    rw [m₄, v₃ (16, krSlot) (by simp), hm 16 (by omega_arith)]
  obtain hl1 : s₄.mem.readW (wordAddr b (krSlot + 1)) 32 = m₀.readW (K.setWidth 64 + BitVec.ofNat 64 20) 32 := by
    rw [m₄, v₃ (20, krSlot + 1) (by simp), hm 20 (by omega_arith)]
  obtain ho₄ : ∀ j < N, j ≠ krSlot → j ≠ krSlot + 1 →
      s₄.mem.readW (wordAddr b j) 32 = s.mem.readW (wordAddr b j) 32 := fun j hj h1 h2 => by
    rw [m₄]; exact k₃ j hj (by simp [h1, h2])
  obtain f₃₄ : Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s₄.mem := by rw [m₄]; exact f₃
  -- The right half, from `s₄` to `s'`.
  obtain tail : ∀ s' : State, s'.gpr sb = b → (∀ r, r ≠ .eax → s'.gpr r = s₄.gpr r) →
      s'.rd = s₄.rd → s'.wr = s₄.wr → Frame [⟨b.setWidth 64, 4 * N⟩] s₄.mem s'.mem →
      (∀ j < N, j ≠ krSlot + 2 → j ≠ krSlot + 3 →
        s'.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32) →
      HW s' (krSlot + 2) (krOf m₀ (K.setWidth 64) len).2 → KrPost N s b m₀ (K.setWidth 64) len s' := by
    intro s' hb hg hrd hwr hf ho hR
    obtain e : (krOf m₀ (K.setWidth 64) len).1 = wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 16) := by
      simp [krOf, h16]
    refine ⟨VW_of_HW (e ▸ HW_words ?_ ?_) hR, fun k hk' h => ?_, fun r h1 => by
        rw [hg r h1, g₄ r h1, g₃ r h1],
      by rw [hrd, rd₄, rd₃], by rw [hwr, wr₄, wr₃], f₃₄.trans hf⟩
    · rw [slotW_of hb, ho _ (Nat.lt_of_lt_of_le (by decide) hk.scr.min) (by decide) (by decide), hl0]
    · rw [slotW_of hb, ho _ (Nat.lt_of_lt_of_le (by decide) hk.scr.min) (by decide) (by decide), hl1, VG.Offset.add_add]
    · rw [ho k hk' (by omega_arith) (by omega_arith), ho₄ k hk' (by omega_arith) (by omega_arith)]
  refine WP.ite (decide (len = 24)) ((eval_e s₄).trans z₄) (fun h24 => ?_) (fun h24 => ?_)
  · have h24 : len = 24 := by simpa using h24
    obtain ⟨s₅, e₅, m₅, o₅, rd₅, wr₅, f₅⟩ := ldNotSt_ok hk₄ (o := 16) (k := krSlot + 2) (by omega_arith)
      (Nat.lt_of_lt_of_le (by decide) hk.scr.min)
    obtain hk₅ : KeyIn N s₅ b K A len := hk₄.congr (o₅ _ (by decide)) (o₅ _ (by decide)) (o₅ _ (by decide)) rd₅ wr₅ f₅
    obtain ⟨s₆, e₆, m₆, o₆, rd₆, wr₆, f₆⟩ := ldNotSt_ok hk₅ (o := 20) (k := krSlot + 3) (by omega_arith)
      (Nat.lt_of_lt_of_le (by decide) hk.scr.min)
    obtain hb₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₅ _ (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s₆, by
      rw [show ([.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax,
          .mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax] : List Instr) =
        [.mov .eax (.mem (at_ .ecx 16)), notR .eax, st (krSlot + 2) .eax] ++
          [.mov .eax (.mem (at_ .ecx 20)), notR .eax, st (krSlot + 3) .eax] from rfl, runBlock_app, e₅,
        Option.bind_some, e₆],
      tail s₆ hb₆ (fun r h => by rw [o₆ r h, o₅ r h]) (by rw [rd₆, rd₅]) (by rw [wr₆, wr₅]) (f₅.trans f₆)
        (fun j hj h1 h2 => by
          rw [m₆, readW_slot_write hfit _ hj (Nat.lt_of_lt_of_le (by decide) hk.scr.min), ite_eq_right h2, m₅,
            readW_slot_write hfit _ hj (Nat.lt_of_lt_of_le (by decide) hk.scr.min), ite_eq_right h1]) ?_⟩
    obtain e : (krOf m₀ (K.setWidth 64) len).2 = ~~~ wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 16) := by
      simp [krOf, h24]
    rw [e]
    refine HW_not ?_ ?_
    · rw [slotW_of hb₆, m₆, readW_slot_write hfit _ (Nat.lt_of_lt_of_le (by decide) hk.scr.min)
          (Nat.lt_of_lt_of_le (by decide) hk.scr.min), ite_eq_right (by decide), m₅,
        Mem.readW_writeW_self32, hm₄ 16 (by omega_arith)]
    · rw [slotW_of hb₆, m₆, show krSlot + 2 + 1 = krSlot + 3 from rfl, Mem.readW_writeW_self32,
        hk₄.keep f₅ (by omega_arith), hm₄ 20 (by omega_arith), VG.Offset.add_add]
  · have h24 : len ≠ 24 := by simpa using h24
    obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loads_ok [(24, krSlot + 2), (28, krSlot + 3)] hk₄
      (by decide) (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact ⟨by omega_arith, Nat.lt_of_lt_of_le (by decide) hk.scr.min⟩)
    obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide)]; exact hk₄.base
    refine WP.of_runBlock ⟨s₅, by
      rw [show ([.mov .eax (.mem (at_ .ecx 24)), st (krSlot + 2) .eax, .mov .eax (.mem (at_ .ecx 28)),
          st (krSlot + 3) .eax] : List Instr) =
        [(24, krSlot + 2), (28, krSlot + 3)].flatMap fun x => [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax]
        from rfl]
      exact e₅, tail s₅ hb₅ (fun r h1 => g₅ r h1) rd₅ wr₅ f₅
        (fun j hj h1 h2 => k₅ j hj (by simp [h1, h2])) ?_⟩
    obtain e : (krOf m₀ (K.setWidth 64) len).2 = wordAt m₀ (K.setWidth 64 + BitVec.ofNat 64 24) := by
      simp [krOf, h16, h24]
    rw [e]
    refine HW_words ?_ ?_
    · rw [slotW_of hb₅, v₅ (24, krSlot + 2) (by simp), hm₄ 24 (by omega_arith)]
    · rw [slotW_of hb₅, v₅ (28, krSlot + 3) (by simp), hm₄ 28 (by omega_arith), VG.Offset.add_add]

/-- What `loadKey` leaves. -/
structure LoadPost (N : Nat) (s₀ : State) (b K : BitVec 32) (len : Nat) (s : State) : Prop where
  kl : VW s klSlot (wordAt s₀.mem (K.setWidth 64), wordAt s₀.mem (K.setWidth 64 + BitVec.ofNat 64 8))
  kr : VW s krSlot (krOf s₀.mem (K.setWidth 64) len)
  keep : ∀ k < N, k < klSlot ∨ klSlot + 8 ≤ k →
    s.mem.readW (wordAddr b k) 32 = s₀.mem.readW (wordAddr b k) 32
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨b.setWidth 64, 4 * N⟩] s₀.mem s.mem

/-- What `loadKey` needs: the key's address in the first argument, its
length in the second. -/
structure LoadPre (N : Nat) (s : State) (b K : BitVec 32) (len : Nat) : Prop where
  base : s.gpr sb = b
  scr : ScrInN N s.wr b
  rd : (⟨K.setWidth 64, len⟩ : Region) ∈ s.rd
  fit : K.toNat + len ≤ 2 ^ 32
  sep : Region.Disjoint ⟨K.setWidth 64, len⟩ ⟨b.setWidth 64, 4 * N⟩
  hlen : len = 16 ∨ len = 24 ∨ len = 32
  arg0 : InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4
  arg0V : s.mem.readW (s.ea (argOp 0)) 32 = K
  arg1 : InRegions (s.rd ++ s.wr) (s.ea (argOp 1)) 4
  arg1V : s.mem.readW (s.ea (argOp 1)) 32 = BitVec.ofNat 32 len
  arg1Sep : Region.Disjoint ⟨s.ea (argOp 1), 4⟩ ⟨b.setWidth 64, 4 * N⟩

theorem loadKey_wp {N : Nat} {s₀ : State} {b K : BitVec 32} {len : Nat} (hp : LoadPre N s₀ b K len) :
    WP isa loadKey s₀ (LoadPost N s₀ b K len) := by
  have hfit := hp.scr.fit
  have hlen := hp.hlen
  unfold loadKey
  obtain ⟨s₀', e₀, c₀, o₀, m₀, rd₀, wr₀⟩ := ldArg_ok s₀ .ecx 0 hp.arg0
  obtain hk : KeyIn N s₀' b K (s₀.ea (argOp 1)) len :=
    ⟨by rw [o₀ _ (by decide)]; exact hp.base, by rw [wr₀]; exact hp.scr, by rw [c₀, hp.arg0V],
      by rw [rd₀]; exact hp.rd, hp.fit, hp.sep, by omega_arith,
      by show (s₀'.gpr .esp + _).setWidth 64 = (s₀.gpr .esp + _).setWidth 64; rw [o₀ _ (by decide)],
      by rw [rd₀, wr₀]; exact hp.arg1, by rw [m₀]; exact hp.arg1V, hp.arg1Sep⟩
  -- `KL`.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, f₁⟩ := loads_ok ((List.range 4).map fun k => (4 * k, klSlot + k)) hk
    (by decide) (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx; obtain ⟨k, hk', rfl⟩ := hx
      exact ⟨by rcases hlen with rfl | rfl | rfl <;> omega_arith, by have := hk.scr.min; rw [klSlot_eq]; omega_arith⟩)
  obtain hk₁ : KeyIn N s₁ b K (s₀.ea (argOp 1)) len :=
    hk.congr (g₁ _ (by decide)) (g₁ _ (by decide)) (g₁ _ (by decide)) rd₁ wr₁ f₁
  obtain ⟨s₂, e₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmpLen_ok hk₁ 16 (by decide)
  obtain hk₂ : KeyIn N s₂ b K (s₀.ea (argOp 1)) len :=
    hk₁.congr (g₂ _ (by decide)) (g₂ _ (by decide)) (g₂ _ (by decide)) rd₂ wr₂ (by rw [m₂]; exact Frame.refl _ _)
  obtain f₀₂ : Frame [⟨b.setWidth 64, 4 * N⟩] s₀'.mem s₂.mem := by rw [m₂]; exact f₁
  obtain hm₂ : KeySame s₂ s₀.mem (K.setWidth 64) len := by
    have := KeySame.frame hk (fun _ _ => by rw [m₀]) f₁; intro o ho; rw [m₂]; exact this o ho
  obtain hkl : ∀ k < 4, s₂.mem.readW (wordAddr b (klSlot + k)) 32 =
      s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
    rw [m₂, v₁ (4 * k, klSlot + k) (by simp only [List.mem_map, List.mem_range]; exact ⟨k, hk', rfl⟩), m₀]
  obtain hklo : ∀ j < N, j < klSlot ∨ klSlot + 4 ≤ j →
      s₂.mem.readW (wordAddr b j) 32 = s₀.mem.readW (wordAddr b j) 32 := fun j hj h => by
    rw [m₂, k₁ j hj (by
      simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range, not_exists, not_and]
      intro k hk' h'; omega_arith), m₀]
  obtain hcode : (List.range 4).flatMap (fun k => [Instr.mov .eax (.mem (at_ .ecx (4 * k))), st (klSlot + k) .eax]) =
      ((List.range 4).map fun k => (4 * k, klSlot + k)).flatMap fun x =>
        [.mov .eax (.mem (at_ .ecx x.1)), st x.2 .eax] := by
    simp only [List.flatMap_map]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_app, runBlock_app, e₀, Option.bind_some, hcode, e₁, Option.bind_some]; exact e₂, ?_⟩)
  obtain post : ∀ s : State, KrPost N s₂ b s₀.mem (K.setWidth 64) len s → LoadPost N s₀ b K len s := by
    intro s h
    obtain hb : s.gpr sb = b := by rw [h.regs _ (by decide)]; exact hk₂.base
    obtain ho : ∀ k < 4, s.mem.readW (wordAddr b (klSlot + k)) 32 =
        s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * k)) 32 := fun k hk' => by
      rw [h.keep _ (by have := hk.scr.min; rw [klSlot_eq]; omega_arith) (.inl (by rw [klSlot_eq, krSlot_eq]; omega_arith)), hkl k hk']
    refine ⟨VW_of_HW (HW_words ?_ ?_) (HW_words ?_ ?_), h.kr, fun k hk' hk2 => ?_,
      fun r h1 h2 => by rw [h.regs r h1, g₂ r h1, g₁ r h1, o₀ r h2], by rw [h.rd, rd₂, rd₁, rd₀],
      by rw [h.wr, wr₂, wr₁, wr₀], ?_⟩
    · rw [slotW_of hb, show klSlot = klSlot + 0 from rfl, ho 0 (by decide)]; simp
    · rw [slotW_of hb, ho 1 (by decide)]
    · rw [slotW_of hb, ho 2 (by decide)]
    · rw [slotW_of hb, show klSlot + 2 + 1 = klSlot + 3 from rfl, ho 3 (by decide), VG.Offset.add_add]
    · rw [h.keep k hk' (by rw [klSlot_eq] at hk2; rw [krSlot_eq]; omega_arith), hklo k hk' (by omega_arith)]
    · rw [← m₀]; exact f₀₂.trans h.frame
  refine WP.ite (decide (len = 16)) ((eval_e s₂).trans z₂) (fun h16 => ?_) (fun h16 => ?_)
  · have h16 : len = 16 := by simpa using h16
    obtain ⟨s', e', h'⟩ := kr16_ok (m₀ := s₀.mem) hk₂ h16
    exact WP.of_runBlock ⟨s', e', post s' h'⟩
  · have h16 : len ≠ 16 := by simpa using h16
    exact WP.mono (krNot16_wp hk₂ hm₂ (by omega_arith)) post

/-- The key schedule on x86 with its working space, of `N` slots, as the fourth argument. -/
def expandKeyX86N (N : Nat) : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sched : Region := ⟨(arg s 2).setWidth 64, 272⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * N⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 272 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * N ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)
  post s s' :=
    Spec.Camellia.bytesAt s'.mem ((arg s 2).setWidth 64)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (arg s 1).toNat)) =
      Spec.Camellia.scheduleBytes
        (Spec.Camellia.expandKey (Spec.Camellia.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-! ## The arguments -/

theorem ekArg_eq (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) (i : Nat) (hi : i < 4) :
    argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  exact addr_eq (by omega_using [hfit, hi])

/-- Argument `i` is in the arguments' region. -/
theorem ekArg_contains (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  obtain hs := setWidth_toNat (s.gpr .esp)
  rw [ekArg_eq s hfit i hi, ekArg_eq s hfit 0 (by decide)]
  exact VG.Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

theorem ekArg_sub (s : State) (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat} (hi : i < 4) :
    Region.Sub ⟨argAddr s i, 4⟩ ⟨argAddr s 0, 16⟩ := by
  rw [ekArg_eq s hfit i hi, ekArg_eq s hfit 0 (by decide)]
  exact VG.Offset.sub _ (by omega_using []) (by omega_using [hi])

/-- `mov eax, [esp + 4 + 4 i]; cmp eax, 16`. -/
theorem cmpArg16_ok (s : State) (i : Nat) (ha : InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 16)] s = some s' ∧
      s'.zf = some (s.mem.readW (s.ea (argOp i)) 32 - 16 == 0) ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s .eax i ha
  let a := s₁.gpr .eax
  refine ⟨arithFlags s₁ (a - 16) (a.toNat < (16 : BitVec 32).toNat) (subOverflow a 16 (a - 16)), ?_,
    by rw [RegUpd.zf_arithFlags, show a = _ from v₁], fun r hr => by rw [RegUpd.gpr_arithFlags, o₁ r hr],
    by rw [RegUpd.mem_arithFlags, m₁], by rw [RegUpd.rd_arithFlags, rd₁], by rw [RegUpd.wr_arithFlags, wr₁]⟩
  rw [show ([.mov .eax (.mem (argOp i)), .alu .cmp .eax (.imm 16)] : List Instr) =
    [.mov .eax (.mem (argOp i))] ++ [.alu .cmp .eax (.imm 16)] from rfl, runBlock_app, e₁, Option.bind_some]
  rfl

/-! ## The subkeys' stores -/

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : BitVec 32) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem (S.setWidth 64) (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S.setWidth 64, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ .eax → r ≠ .ebx → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {N : Nat} {s₈ : State} {b S : BitVec 32} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hb : s₈.gpr sb = b) (hw : ScrInN N s₈.wr b) (hS : SchedOut N s₈ b S) (hks : ∀ k ∈ ks, k.1 < 4 ∧ k.2.1 < 128)
    (hkl : ks.length ≤ 34) (hX : ∀ v < 4, NumOf s₈ (valSlot v) (valNum key v))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := stores_ok (X := valNum key) ks 0 s₈ hb hw hS hks (by omega_using [hkl]) hX
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
  · rw [hlen, schedule_of_stores (vs := keyVals key) (H := fun v => hiW ((keyVals key).getD v 0))
      (L := fun v => loW ((keyVals key).getD v 0)) (fun k hk => (hks k hk).1) (fun v _ => ⟨rfl, rfl⟩)
      (fun i hi j hj => by
        rw [b₉ i hi j hj]
        obtain hmem : ks.getD i (0, 0, true) ∈ ks := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
          exact List.getElem_mem hi
        obtain hk := hks _ hmem
        simp only [subHalf, valNum]
        split
        · rename_i h; rw [hi_eq _ _ hk.2, h]
        · rename_i h; rw [lo_eq _ _ hk.2]; simp only [Bool.not_eq_true] at h; rw [h]),
      Spec.Camellia.scheduleBytes, Proof.Camellia.scheduleWords_expandKey, ← hks']
    rfl
  · exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Nat.mul_zero]
      exact VG.Offset.sub_base _ (by omega_using [hkl])⟩

/-! ## The function -/

/-- After `KA` and `KB`: the four values in their slots. -/
structure KeyMid (N j : Nat) (s₀ : State) (b : BitVec 32) (key : List Byte) (s : State) : Prop where
  base : s.gpr sb = b
  esp : s.gpr .esp = s₀.gpr .esp
  scr : ScrInN N s.wr b
  vals : ∀ v < 4, VW s (valSlot v) (hiW ((keyVals key).getD v 0), loW ((keyVals key).getD v 0))
  saved : SavedAt j s₀ b s.mem
  frame : Frame [⟨b.setWidth 64, 4 * N⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem saved_not_rev : ∀ i < 4, savedSlot + i ∉ revSlots := by decide +kernel

/-- The values byte-swapped, the subkeys stored, the registers restored. -/
theorem ekTail_wp {N j₀ : Nat} {s₀ s : State} (hp : (expandKeyX86N N).pre s₀) (hj : j₀ + 4 ≤ N)
    (hnr : ∀ i < 4, j₀ + i ∉ revSlots) (h : KeyMid N j₀ s₀ (arg s₀ 3) (Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat) s) :
    WP isa (.seq (.block (revValues ++ ([.mov .edx (.mem (argOp 2)), .mov .eax (.mem (argOp 1)),
        .alu .cmp .eax (.imm 16)] : List Instr)))
      (.seq (.ite .e (.block (storeSubkeys Impl.Camellia.subkeys128)) (.block (storeSubkeys Impl.Camellia.subkeys256)))
        (.block (restoreRegsAt j₀)))) s fun s' => abiPreserved s₀ s' ∧ (expandKeyX86N N).post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩ := hp
  let key := Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat
  let len := (arg s₀ 1).toNat
  let S := arg s₀ 2
  let b := arg s₀ 3
  obtain hkl : key.length = len := by simp [key, len, Spec.Camellia.bytesAt]
  have hfit := h.scr.fit
  obtain hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, ekArg_contains s₀ fitE hi⟩
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * N⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (ekArg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  obtain ⟨hnd, hlt⟩ := revSlots_facts h.scr.min
  -- The values, byte-swapped.
  obtain ⟨s₁, e₁, v₁, k₁, g₁, rd₁, wr₁, f₁⟩ := revs_ok revSlots (s := s) h.base h.scr hnd hlt
  obtain hb₁ : s₁.gpr sb = b := by rw [g₁ _ (by decide), h.base]
  obtain esp₁ : s₁.gpr .esp = s₀.gpr .esp := by rw [g₁ _ (by decide), h.esp]
  obtain hX₁ : ∀ v < 4, NumOf s₁ (valSlot v) (valNum key v) := fun v hv => by
    have := num_of_rev (s' := s₁) (h.vals v hv) fun j hj => by
      simp only [slotW]
      rw [hb₁, h.base, v₁ (valSlot v + j) (mem_revSlots hv hj)]
    dsimp only at this
    exact this
  obtain F₁ : Frame [⟨b.setWidth 64, 4 * N⟩] s₀.mem s₁.mem := h.frame.trans f₁
  -- The schedule's pointer and the key's length.
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .edx 2
    (argIn (rd₁.trans h.rd) (wr₁.trans h.wr) esp₁ 2 (by decide))
  obtain esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [o₂ _ (by decide), esp₁]
  obtain ⟨s₃, e₃, z₃, o₃, m₃, rd₃, wr₃⟩ := cmpArg16_ok s₂ 1
    (argIn (rd₂.trans (rd₁.trans h.rd)) (wr₂.trans (wr₁.trans h.wr)) esp₂ 1 (by decide))
  obtain hz₃ : s₃.zf = some (decide (len = 16)) := by
    rw [z₃, ea_arg esp₂, m₂, argR F₁ 1 (by decide), show arg s₀ 1 = BitVec.ofNat 32 len by simp [len],
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ofNat32_sub_beq (by omega_using []) (by decide)]
  obtain hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), o₂ _ (by decide), hb₁]
  obtain hm₃ : s₃.mem = s₁.mem := by rw [m₃, m₂]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁, h.wr]
  obtain hw₃ : ScrInN N s₃.wr b := .exact (by rw [wr₃', hwr]; simp [b]) hfit h.scr.min
  obtain hS₃ : SchedOut N s₃ b S := ⟨by rw [o₃ _ (by decide), v₂, ea_arg esp₁, argR F₁ 2 (by decide)],
    by rw [wr₃', hwr]; simp [S], fitS, dSB⟩
  obtain hX₃ : ∀ v < 4, NumOf s₃ (valSlot v) (valNum key v) := fun v hv => (hX₁ v hv).congr fun j hj => by
    simp only [slotW, hb₃, hb₁, hm₃]
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, revValues_eq, e₁, Option.bind_some, show ([.mov .edx (.mem (argOp 2)),
      .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 16)] : List Instr) = [.mov .edx (.mem (argOp 2))] ++
      [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 16)] from rfl, runBlock_app, e₂, Option.bind_some, e₃], ?_⟩)
  -- The subkeys.
  obtain hk128 : ∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4 ∧ k.2.1 < 128 := by decide
  obtain hk256 : ∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4 ∧ k.2.1 < 128 := by decide
  refine WP.seq (WP.mono (Q := StoresPost s₃ S len key)
    (WP.ite (decide (len = 16)) ((eval_e s₃).trans hz₃) (fun h16 => ?_) (fun h16 => ?_))
    fun s₅ h₅ => ?_)
  · have h16 : len = 16 := by simpa using h16
    exact stores_wp hb₃ hw₃ hS₃ hk128 (by rw [subkeys_length.1]; omega_using []) hX₃
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hkl, ite_eq_left h16])
  · have h16 : len ≠ 16 := by simpa using h16
    exact stores_wp hb₃ hw₃ hS₃ hk256 (by rw [subkeys_length.2]) hX₃
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hkl, ite_eq_right h16])
  -- The epilogue.
  obtain hb₅ : s₅.gpr sb = b := by rw [h₅.regs _ (by decide) (by decide), hb₃]
  obtain hsv : SavedAt j₀ s₀ b s₅.mem := fun i hi => by
    rw [hS₃.slot hfit h₅.frame (fun _ h => h) (by omega_using [hi, hj]), hm₃,
      k₁ (j₀ + i) (by omega_using [hi, hj]) (hnr i hi)]
    exact h.saved i hi
  obtain ⟨s₆, e₆, rg₆, o₆, m₆, -, -⟩ := restoreAt_ok (s₀ := s₀) (b := b) hj
    (.exact (by rw [h₅.wr, wr₃', hwr]; simp [b]) hfit h.scr.min) hb₅ hsv
  refine WP.of_runBlock ⟨s₆, e₆, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₆ 0 (by decide)
    · exact rg₆ 1 (by decide)
    · exact rg₆ 2 (by decide)
    · exact rg₆ 3 (by decide)
    · rw [o₆ _ (fun i hi => by revert i; decide), h₅.regs _ (by decide) (by decide), o₃ _ (by decide), esp₂]
  · rw [m₆, h₅.frame.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRS) (by decide), hm₃]
    exact F₁.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dRB) (by decide)
  · show Spec.Camellia.bytesAt s₆.mem (S.setWidth 64) _ = _
    rw [m₆]
    exact h₅.bytes

/-- What `mid` needs of the table's address in `edx`, and leaves: `KA` and
`KB`, from `KL` and `KR`, in their slots, the other values and the saved
registers as they were. -/
def MidOk (N : Nat) (table : String) (mid : List Instr) : Prop :=
  ∀ {s : State} {b : BitVec 32} {KL KR : BitVec 64 × BitVec 64}, s.gpr sb = b → s.gpr .edx = s.syms table →
    ScrInN N s.wr b → VW s klSlot KL → VW s krSlot KR → WP isa (.block mid) s fun s' =>
      s'.gpr sb = b ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VW s' klSlot KL ∧ VW s' krSlot KR ∧ VW s' kaSlot (kaD2 KL KR) ∧ VW s' kbSlot (kaD3 KL KR) ∧
      (∀ k, 92 ≤ k → k < 96 → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      Frame [⟨b.setWidth 64, 4 * N⟩] s.mem s'.mem

section
variable {N : Nat} {table : String} {mid : List Instr} {s₀ : State}

/-- The function after the table's address is in `edx`. -/
theorem main_wp (hN : 96 ≤ N) (hmid : MidOk N table mid) (hp : (expandKeyX86N N).pre s₀) (ht : s₀.gpr .edx = s₀.syms table) :
    WP isa (expandKeyMain mid) s₀ fun s' => abiPreserved s₀ s' ∧ (expandKeyX86N N).post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩ := id hp
  let K := arg s₀ 0
  let len := (arg s₀ 1).toNat
  let b := arg s₀ 3
  obtain hw : ScrInN N s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB hN
  obtain hrA : (⟨argAddr s₀ 0, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 4,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, ekArg_contains s₀ fitE hi⟩
  obtain argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * N⟩] s₀.mem m → ∀ i < 4,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (ekArg_contains s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  -- The registers saved.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, k₁⟩ := saveAt_ok (j := savedSlot) (Nat.le_trans (by decide) hN) hw
    (argIn rfl rfl rfl 3 (by decide)) (by rw [ea_arg rfl]; rfl)
  refine WP.seq (WP.mono_syms (WP.of_runBlock (Q := fun s => s = s₁) ⟨s₁, e₁, rfl⟩) fun s h y₁ => ?_)
  subst h
  obtain esp₁ : s.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  obtain hkey : Spec.Camellia.bytesAt s.mem (K.setWidth 64) len = Spec.Camellia.bytesAt s₀.mem (K.setWidth 64) len :=
    Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨K.setWidth 64, len⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega_using []) hi
  -- `KL` and `KR`.
  obtain hl₁ : LoadPre N s b K len :=
    { base := b₁, scr := by rw [wr₁]; exact hw, rd := by rw [rd₁, hrd]; simp [K, len],
      fit := fitK, sep := dKB, hlen := hlen,
      arg0 := argIn rd₁ wr₁ esp₁ 0 (by decide), arg0V := by rw [ea_arg esp₁, argR f₁ 0 (by decide)],
      arg1 := argIn rd₁ wr₁ esp₁ 1 (by decide),
      arg1V := by rw [ea_arg esp₁, argR f₁ 1 (by decide)]; simp [len],
      arg1Sep := by rw [ea_arg esp₁]; exact dAB.sub_left (ekArg_sub s₀ fitE (by decide)) }
  refine WP.seq (WP.mono_syms (loadKey_wp hl₁) fun s₂ h₂ y₂ => ?_)
  obtain hb₂ : s₂.gpr sb = b := by rw [h₂.regs _ (by decide) (by decide)]; exact b₁
  -- `KA` and `KB`.
  let key := Spec.Camellia.bytesAt s.mem (K.setWidth 64) len
  obtain ⟨hKL1, hKL2, hKR1, hKR2⟩ := Proof.Camellia.klkr_halves s.mem (K.setWidth 64) hlen
  obtain vl : VW s₂ klSlot (Proof.Camellia.hiW (Spec.Camellia.klkr key).1, Proof.Camellia.loW (Spec.Camellia.klkr key).1) := by
    rw [hKL1, hKL2]; exact h₂.kl
  obtain vr : VW s₂ krSlot (Proof.Camellia.hiW (Spec.Camellia.klkr key).2, Proof.Camellia.loW (Spec.Camellia.klkr key).2) := by
    rw [hKR1, hKR2]; exact h₂.kr
  refine WP.seq (WP.mono (hmid hb₂ ?_ (by rw [h₂.wr, wr₁]; exact hw) vl vr)
    fun s₃ ⟨b₃, e₃, rd₃, wr₃, kl₃, kr₃, ka₃, kb₃, sv₃, f₃⟩ => ?_)
  · rw [h₂.regs _ (by decide) (by decide), g₁ _ (by decide) (by decide), ht, y₂, y₁]
  obtain hka := Proof.Camellia.kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  refine ekTail_wp hp (Nat.le_trans (by decide) hN) saved_not_rev ?_
  rw [← show key = Spec.Camellia.bytesAt s₀.mem (K.setWidth 64) len from hkey]
  refine ⟨b₃, by rw [e₃, h₂.regs _ (by decide) (by decide), esp₁], by rw [wr₃, h₂.wr, wr₁]; exact hw, fun v hv => ?_,
    fun i hi => ?_, f₁.trans (h₂.frame.trans f₃), by rw [rd₃, h₂.rd, rd₁], by rw [wr₃, h₂.wr, wr₁]⟩
  · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
    · exact kl₃
    · exact kr₃
    · rw [hka.1] at ka₃; exact ka₃
    · rw [hka.2] at kb₃; exact kb₃
  · have h92 : savedSlot = 92 := rfl
    rw [sv₃ _ (by omega_arith) (by omega_arith), h₂.keep _ (by omega_arith) (.inr (by rw [klSlot_eq]; omega_arith))]
    exact sv₁ i hi

end

/-! ## The contract, and constant time -/

/-- What the frame that gets the table's address needs: the four bytes below
`esp` apart from everything else. -/
structure Below (N : Nat) (s : State) : Prop where
  key : Region.Disjoint (below (s.gpr .esp) 4) ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  sched : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ ⟨(arg s 2).setWidth 64, 272⟩
  scr : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ ⟨(arg s 3).setWidth 64, 4 * N⟩
  esp : 4 ≤ (s.gpr .esp).toNat

/-- The key schedule with its working space as the fourth argument, and four
bytes of stack. -/
def expandKeyC (N : Nat) : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sched : Region := ⟨(arg s 2).setWidth 64, 272⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * N⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 272 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 4 * N ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32) ∧
    stk.Disjoint key ∧ stk.Disjoint sched ∧ stk.Disjoint scratch ∧ 4 ≤ (s.gpr .esp).toNat
  post := (expandKeyX86N N).post
  pub := (expandKeyX86N N).pub

theorem below_eq {s : State} (h : 4 ≤ (s.gpr .esp).toNat) :
    below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
  rw [below, VG.X86.Taint.sub_setWidth h]

theorem pre_split {N : Nat} {s : State} (h : (expandKeyC N).pre s) : (expandKeyX86N N).pre s ∧ Below N s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, k, d, b, e⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩, ⟨by rw [below_eq e]; exact k, d, b, e⟩⟩

theorem expandKey_wp {N : Nat} {table : String} {mid : List Instr} (hN : 96 ≤ N) (hmid : MidOk N table mid) {s₀ : State}
    (h : (expandKeyC N).pre s₀) :
    WP isa (expandKey table mid) s₀ fun s' => abiPreserved s₀ s' ∧ (expandKeyC N).post s₀ s' := by
  obtain ⟨hp, hB⟩ := pre_split h
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩ := id hp
  unfold expandKey
  refine WP.seq (WP.mono (symFrame_ok table s₀ hB.esp) fun s₁ a₁ => ?_)
  have args : ∀ i < 4, arg s₁ i = arg s₀ i := fun i hi => a₁.arg hB.esp (by omega_arith)
  refine WP.seq (Wp.wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.other _ (by decide), a₁.gpr _ (by decide)]
  have args₂ : ∀ i < 4, arg s₂ i = arg s₀ i := fun i hi => by
    rw [← args i hi, arg, arg, argAddr, argAddr, u₂.mem, u₂.other _ (by decide)]
  have adr₂ : argAddr s₂ 0 = argAddr s₀ 0 := by rw [argAddr, argAddr, esp₂]
  have hp₂ : (expandKeyX86N N).pre s₂ := by
    simp only [expandKeyX86N, args₂ 0 (by decide), args₂ 1 (by decide), args₂ 2 (by decide), args₂ 3 (by decide), adr₂, esp₂,
      u₂.rd, u₂.wr, a₁.rd, a₁.wr]
    exact hp
  refine WP.mono (main_wp hN hmid hp₂ (by rw [u₂.gpr, a₁.addr, u₂.syms, a₁.syms])) fun s' ⟨⟨hr, hm⟩, hpost⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
  · rw [hr r hr']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> rw [u₂.other _ (by decide), a₁.gpr _ (by decide)]
  · rw [esp₂, u₂.mem, a₁.ret hB.esp (by omega_arith)] at hm
    exact hm
  · have hkey : Spec.Camellia.bytesAt s₂.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat =
        Spec.Camellia.bytesAt s₀.mem ((arg s₀ 0).setWidth 64) (arg s₀ 1).toNat := by
      rw [u₂.mem]
      exact Proof.Camellia.bytesAt_congr fun i hi => a₁.frame.bytes (R := ⟨(arg s₀ 0).setWidth 64, (arg s₀ 1).toNat⟩)
        (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hB.key.symm) (by simp only; omega_arith) hi
    simp only [expandKeyX86N, args₂ 0 (by decide), args₂ 1 (by decide), args₂ 2 (by decide), hkey] at hpost
    exact hpost

/-- The initial taint: `esp` public, and the words holding `schedule` and
`scratch` known to be the base addresses of the writable regions. -/
def ekTaint (N : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [272, 4 * N], argLen := 20, argBases := [(12, 0), (16, 1)], room := 4 }

theorem ekTaint_wf {N : Nat} {s : State} (h : (expandKeyC N).pre s) : VG.X86.Taint.Wf (ekTaint N) s := by
  obtain ⟨⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE, hlen⟩, hB⟩ := pre_split h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ekTaint]; omega_using [fitE], ?_⟩, ?_⟩ fun _ => ⟨hB.esp, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dSB, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fitE]) dRS dAS
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [fitE]) dRB dAB
  · intro p hp'
    simp only [ekTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp only [ekTaint]; decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hB.sched
    · exact hB.scr

theorem ekTaint_agree {N : Nat} {s₁ s₂ : State} (h₁ : (expandKeyC N).pre s₁) (h₂ : (expandKeyC N).pre s₂)
    (hpub : (expandKeyC N).pub s₁ s₂) : VG.X86.Taint.Agree (ekTaint N) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hwr₁ := (pre_split h₁).1.2.1; have hwr₂ := (pre_split h₂).1.2.1
  have fE₁ := (pre_split h₁).1.2.2.2.2.2.2.2.2.2.2.2.2.1; have fE₂ := (pre_split h₂).1.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ekTaint_wf h₁, ekTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp, fun k h4 hk => ?_⟩
  · simp only [ekTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega_using []), ha 3 (by omega_using [])]
  · simp only [ekTaint] at hk
    rw [show VG.X86.Taint.depth (ekTaint N).stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 20) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

/-- A state satisfying `vg_camellia_expand_key`'s precondition: a key of 16
bytes at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 272⟩]

end VG.Proof.Camellia.X86
