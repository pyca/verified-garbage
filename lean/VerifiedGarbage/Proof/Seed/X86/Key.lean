module
public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Seed.X86.Lanes
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Seed.X86.KeyRound
import VerifiedGarbage.Proof.Seed.X86.Ecb
import VerifiedGarbage.Proof.Seed.X86.Crypt8
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# SEED key expansion on x86 (32-bit): the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyX86`),
`expandKey` saves the callee-saved registers, loads the key's words
(`keyLoad_ok`), computes the 32 inputs of `G` (`keyRounds_ok`), and `G` of
eight at a time to the schedule, at `esi` (`keyChunk_ok`); RFC 4269 §2.3's
schedule is `G` of these inputs (`expandKey_eq`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG VG.X86 VG.Impl.Seed.X86

/-- The key schedule on x86 with its working space as the third argument. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let sched : Region := ⟨(arg s 1).setWidth 64, 128⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 4 * slots⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 4 * slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' :=
    Spec.Seed.scheduleAt s'.mem ((arg s 1).setWidth 64) =
      Spec.Seed.expandKey (Spec.Seed.blockAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.Seed

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Seed.X86 VG.Proof.Seed
open VG.Impl.Aes.X86 (sb slotAt movS st movR at_ argOp addI subI)
open VG.X86.Straight (wordAddr slot_sep slot_contains)

/-- A word of a buffer of `n` words is inside it. -/
theorem word_sub {b : BitVec 32} {n k : Nat} (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨b.setWidth 64, 4 * n⟩ := by
  rw [slot_addr (by omega)]
  exact Offset.sub_base _ (by omega)

/-! ## The schedule's words at `esi` -/

/-- The schedule at `P`, writable and apart from the scratch buffer, with
`esi` at its word `d`. -/
structure OutPre (s : State) (P : BitVec 32) (d : Nat) : Prop where
  room : Room s
  esi : s.gpr .esi = P + BitVec.ofNat 32 (4 * d)
  mem : (⟨P.setWidth 64, 128⟩ : Region) ∈ s.wr
  fit : P.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨P.setWidth 64, 128⟩ (scratchR s)

/-- Word `o` at `esi`, at word `d` of the schedule, is its word `d + o`. -/
theorem esi_addr (P : BitVec 32) (d o : Nat) : addr (P + BitVec.ofNat 32 (4 * d)) (4 * o) = wordAddr P (d + o) := by
  simp only [wordAddr, addr, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem OutPre.congr {s s' : State} {P : BitVec 32} {d : Nat} (h : OutPre s P d) (hsb : s'.gpr sb = s.gpr sb)
    (hesi : s'.gpr .esi = s.gpr .esi) (hwr : s'.wr = s.wr) : OutPre s' P d :=
  ⟨h.room.congr hsb hwr, by rw [hesi]; exact h.esi, by rw [hwr]; exact h.mem, h.fit,
    by unfold scratchR; rw [hsb]; exact h.sep⟩

/-- A word of the schedule is apart from every slot. -/
theorem OutPre.word_sep {s : State} {P : BitVec 32} {d : Nat} (hs : OutPre s P d) {o : Nat} (ho : o < 32)
    {j : Nat} (hj : j < slots) : Mem.Sep (slotA s j) 4 (wordAddr P o) 4 := fun x h1 h2 =>
  ((hs.sep.sub_left (word_sub (n := 32) (by have := hs.fit; omega) ho)).sub_right
    (slot_sub hs.room.fit hj)) x h2 h1

/-- `mov eax, [edi + 4 a]; mov [esi + 4 o], eax` for each `(a, o)`. -/
def storesCode (L : List (Nat × Nat)) : List Instr :=
  L.flatMap fun p => [movS .eax p.1, .store (at_ .esi (4 * p.2)) .eax]

theorem stores_ok {P : BitVec 32} {d : Nat} :
    ∀ (L : List (Nat × Nat)) (s : State), OutPre s P d → (∀ p ∈ L, p.1 < slots ∧ d + p.2 < 32) →
      (L.map (d + ·.2)).Nodup →
      ∃ s', runBlock isa (storesCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (wordAddr P (d + p.2)) 32 = slotW s p.1) ∧
        (∀ o < 32, o ∉ L.map (d + ·.2) → s'.mem.readW (wordAddr P o) 32 = s.mem.readW (wordAddr P o) 32) ∧
        (∀ j < slots, slotW s' j = slotW s j) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [⟨P.setWidth 64, 128⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    have hp := hL p List.mem_cons_self
    have hP := hs.fit
    have hc : ∀ o < 32, (⟨P.setWidth 64, 128⟩ : Region).Contains (wordAddr P o) 4 :=
      fun o ho => slot_contains P (n := 32) ho (by omega)
    let s₁ := s.setReg .eax (slotW s p.1)
    let s₂ := setMem s₁ (s.mem.writeW (wordAddr P (d + p.2)) (slotW s p.1))
    have e₁ : runBlock isa [movS .eax p.1, .store (at_ .esi (4 * p.2)) .eax] s = some s₂ := by
      have hea : s₁.ea (at_ .esi (4 * p.2)) = wordAddr P (d + p.2) := by
        show addr (s₁.gpr .esi) (4 * p.2) = _
        rw [show s₁.gpr .esi = P + BitVec.ofNat 32 (4 * d) by
          simp only [s₁, gpr_setReg_of_ne _ _ (show Reg.esi ≠ .eax by decide), hs.esi], esi_addr]
      rw [runBlock_cons, exec_movS hs.room hp.1, runStep_some, runBlock_cons]
      simp only [exec, hea, State.store32, show InRegions s₁.wr (wordAddr P (d + p.2)) 4 from ⟨_, hs.mem, hc _ hp.2⟩,
        ↓reduceIte, runStep_some, runBlock_nil, s₂, s₁, gpr_setReg_self, mem_setReg]
      rfl
    have sl₂ : ∀ j < slots, slotW s₂ j = slotW s j := by
      intro j hj
      show (s.mem.writeW _ _).readW (wordAddr (s₁.gpr sb) j) 32 = _
      rw [show s₁.gpr sb = s.gpr sb from gpr_setReg_of_ne _ _ (by decide)]
      exact Mem.readW_writeW_sep (hs.word_sep hp.2 hj) (by decide)
    have sb₂ : s₂.gpr sb = s.gpr sb := by
      show (s.setReg .eax (slotW s p.1)).gpr sb = _; exact gpr_setReg_of_ne _ _ (by decide)
    have hs₂ : OutPre s₂ P d := hs.congr sb₂
      (by simp only [s₂, gpr_setMem, s₁, gpr_setReg_of_ne _ _ (show Reg.esi ≠ .eax by decide)]) rfl
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', sl', g', rd', wr', f'⟩ := stores_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    have hw : ∀ o < 32, s₂.mem.readW (wordAddr P o) 32 =
        if o = d + p.2 then slotW s p.1 else s.mem.readW (wordAddr P o) 32 := by
      intro o ho
      show (s.mem.writeW _ _).readW _ 32 = _
      split
      · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
      · rename_i e
        exact Mem.readW_writeW_sep (slot_sep P (by omega) (by omega) e) (by decide)
    refine ⟨s', ?_, fun q hq => ?_, fun o ho hoL => ?_, fun j hj => by rw [sl' j hj, sl₂ j hj],
      fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl, ?_⟩
    · rw [storesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, hw _ hp.2, ite_eq_left rfl]
      · rw [v' q hq, sl₂ _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hoL
      rw [o' o ho hoL.2, hw o ho, ite_eq_right hoL.1]
    · rw [g' r hr]; exact gpr_setReg_of_ne _ _ hr
    · refine Frame.trans ?_ f'
      show Frame _ s.mem (s.mem.writeW _ (slotW s p.1))
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (hc _ hp.2)

/-- `mov eax, [esi + 4 o]; mov [edi + 4 a], eax` for each `(o, a)`. -/
def esiLoadsCode (L : List (Nat × Nat)) : List Instr :=
  L.flatMap fun p => [.mov .eax (.mem (at_ .esi (4 * p.1))), st p.2 .eax]

theorem esiLoads_ok {P : BitVec 32} {d : Nat} :
    ∀ (L : List (Nat × Nat)) (s : State), OutPre s P d → (∀ p ∈ L, d + p.1 < 32 ∧ p.2 < slots) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (esiLoadsCode L) s = some s' ∧
        (∀ p ∈ L, slotW s' p.2 = s.mem.readW (wordAddr P (d + p.1)) 32) ∧
        (∀ j < slots, j ∉ L.map (·.2) → slotW s' j = slotW s j) ∧
        (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        Frame [scratchR s] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    have hp := hL p List.mem_cons_self
    have hP := hs.fit
    let v := s.mem.readW (wordAddr P (d + p.1)) 32
    let s₁ := s.setReg .eax v
    let s₂ := setMem s₁ (s₁.mem.writeW (slotA s₁ p.2) (s₁.gpr .eax))
    have h₁ : Room s₁ := room_setReg hs.room (by decide) _
    have e₁ : runBlock isa [.mov .eax (.mem (at_ .esi (4 * p.1))), st p.2 .eax] s = some s₂ := by
      have hea : s.ea (at_ .esi (4 * p.1)) = wordAddr P (d + p.1) := by
        show addr (s.gpr .esi) (4 * p.1) = _; rw [hs.esi, esi_addr]
      have hin : InRegions (s.rd ++ s.wr) (wordAddr P (d + p.1)) 4 :=
        ⟨_, List.mem_append_right _ hs.mem, slot_contains P (n := 32) hp.1 (by omega)⟩
      rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .esi (4 * p.1)))) s = some s₁ by
          simp only [exec, readSrc, hea, State.load32, hin, ↓reduceIte, Option.map_some]; rfl,
        runStep_some, runBlock_cons, exec_st h₁ hp.2, runStep_some, runBlock_nil]
    have sb₂ : s₂.gpr sb = s.gpr sb := by
      simp only [s₂, s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show sb ≠ Reg.eax by decide)]
    have sl₂ : ∀ j < slots, slotW s₂ j = if j = p.2 then v else slotW s j := by
      intro j hj
      rw [slotW_setMem_write h₁ hp.2 hj, slotW_setReg _ (by decide)]
      simp only [s₁, gpr_setReg_self]
    have hs₂ : OutPre s₂ P d := hs.congr sb₂
      (by simp only [s₂, s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show Reg.esi ≠ .eax by decide)]) rfl
    have fr₂ : Frame [scratchR s] s.mem s₂.mem := by
      show Frame _ s.mem (s.mem.writeW (slotA s₁ p.2) _)
      rw [slotA_setReg _ (show Reg.eax ≠ sb by decide)]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (slot_in hs.room hp.2)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := esiLoads_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl, ?_⟩
    · rw [esiLoadsCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, sl₂ _ hp.2, ite_eq_left rfl]
      · have hq' := hL q (List.mem_cons_of_mem _ hq)
        rw [v' q hq]
        refine fr₂.readW (r := ⟨wordAddr P (d + q.1), 4⟩) (Region.contains_self _ _) ?_ (by decide)
        intro r hr
        simp only [List.mem_singleton] at hr; subst hr
        exact hs.sep.sub_left (word_sub (n := 32) (by omega) hq'.1)
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, sl₂ j hj, ite_eq_right hjL.1]
    · rw [g' r hr]
      simp only [s₂, s₁, gpr_setMem, gpr_setReg_of_ne _ _ hr]
    · exact fr₂.trans (by unfold scratchR at f' ⊢; rw [sb₂] at f'; exact f')

/-! ## `G` of eight words of the schedule, in place -/

theorem nodup_map_range {f : Nat → Nat} (hf : ∀ a b, f a = f b → a = b) (n : Nat) :
    ((List.range n).map f).Nodup :=
  List.Pairwise.map f (fun a b hab h => hab (hf a b h)) List.nodup_range

def chunkIn : List (Nat × Nat) := (List.range 8).map fun w => (w, tSlot w)
def chunkOut : List (Nat × Nat) := (List.range 8).map fun w => (tSlot w, w)

/-- `esi` on to the next eight words, and compared with the schedule's end. -/
def endCode : List Instr := [addI .esi 32, .mov .eax (.mem (argOp 1)), addI .eax 128, .alu .cmp .esi (.reg .eax)]

/-- The schedule's address `P` is argument 1, at `a`, which the writes of the
scratch buffer and the schedule leave alone. -/
structure ArgAt (s : State) (a : Addr) (P : BitVec 32) : Prop where
  ea : s.ea (argOp 1) = a
  inR : InRegions (s.rd ++ s.wr) a 4
  val : s.mem.readW a 32 = P
  keep : ∀ {m m' : Mem}, Frame [scratchR s, ⟨P.setWidth 64, 128⟩] m m' → m'.readW a 32 = m.readW a 32

theorem ArgAt.congr {s s' : State} {a : Addr} {P : BitVec 32} (h : ArgAt s a P) (hesp : s'.gpr .esp = s.gpr .esp)
    (hsb : s'.gpr sb = s.gpr sb) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hm : s'.mem.readW a 32 = s.mem.readW a 32) : ArgAt s' a P :=
  ⟨by show addr (s'.gpr .esp) _ = _; rw [hesp]; exact h.ea, by rw [hrd, hwr]; exact h.inR, by rw [hm]; exact h.val,
    fun hf => h.keep (by unfold scratchR at hf ⊢; rw [hsb] at hf; exact hf)⟩

theorem end_ok {c : Nat} (hc : c < 4) {s : State} {P : BitVec 32} {a : Addr} (hO : OutPre s P (8 * c))
    (hA : ArgAt s a P) :
    ∃ s', runBlock isa endCode s = some s' ∧ OutPre s' P (8 * (c + 1)) ∧
      s'.zf = some (decide (c + 1 = 4)) ∧ s'.mem = s.mem ∧ s'.gpr sb = s.gpr sb ∧
      (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hP := hO.fit
  obtain ⟨s₁, e₁, r₁, -, o₁, m₁, rd₁, wr₁⟩ := addI_ok s .esi 32
  have ea₁ : s₁.ea (argOp 1) = a := by
    show addr (s₁.gpr .esp) _ = _; rw [o₁ _ (by decide)]; exact hA.ea
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .eax 1 (by rw [ea₁, rd₁, wr₁]; exact hA.inR)
  obtain ⟨s₃, e₃, r₃, -, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .eax 128
  let s₄ := arithFlags s₃ (s₃.gpr .esi - s₃.gpr .eax) ((s₃.gpr .esi).toNat < (s₃.gpr .eax).toNat)
    (subOverflow (s₃.gpr .esi) (s₃.gpr .eax) (s₃.gpr .esi - s₃.gpr .eax))
  have e₄ : runBlock isa [.alu .cmp .esi (.reg .eax)] s₃ = some s₄ := rfl
  have esi₃ : s₃.gpr .esi = P + BitVec.ofNat 32 (4 * (8 * (c + 1))) := by
    rw [o₃ _ (by decide), o₂ _ (by decide), r₁, hO.esi, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl,
      Offset.add_add, show 4 * (8 * c) + 32 = 4 * (8 * (c + 1)) by omega]
  have eax₃ : s₃.gpr .eax = P + BitVec.ofNat 32 128 := by
    rw [r₃, v₂, ea₁, m₁, hA.val]; rfl
  have g₄ : ∀ r, r ≠ .eax → s₄.gpr r = s₃.gpr r := fun r _ => by simp only [s₄, gpr_arithFlags]
  have sb₄ : s₄.gpr sb = s.gpr sb := by
    rw [g₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  have wr₄ : s₄.wr = s.wr := by simp only [s₄, wr_arithFlags]; rw [wr₃, wr₂, wr₁]
  refine ⟨s₄, ?_, ⟨hO.room.congr sb₄ wr₄, by rw [g₄ _ (by decide)]; exact esi₃, by rw [wr₄]; exact hO.mem, hP,
      by unfold scratchR; rw [sb₄]; exact hO.sep⟩, ?_, by simp only [s₄, mem_arithFlags]; rw [m₃, m₂, m₁], sb₄,
    fun r h1 h2 => by rw [g₄ r h1, o₃ r h1, o₂ r h1, o₁ r h2],
    by simp only [s₄, rd_arithFlags]; rw [rd₃, rd₂, rd₁], wr₄⟩
  · rw [show endCode = [addI .esi 32] ++ ([.mov .eax (.mem (argOp 1))] ++ ([addI .eax 128] ++
        [.alu .cmp .esi (.reg .eax)])) from rfl,
      runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
      Option.bind_some, e₄]
  · simp only [s₄, zf_arithFlags]
    rw [esi₃, eax₃, Offset.add_sub_add_left, ofNat32_sub_beq (by omega) (by omega)]
    congr 1; exact decide_eq_decide.mpr (by omega)

theorem keyInputs_eq : keyInputs = storesCode ((List.range 32).map fun i => (uSlot i, i)) := by
  simp only [keyInputs, storesCode, List.flatMap_map]

theorem keyChunk_eq : keyChunk = esiLoadsCode chunkIn ++ g8 ++ storesCode chunkOut ++ endCode := by
  simp only [keyChunk, esiLoadsCode, storesCode, chunkIn, chunkOut, endCode, List.flatMap_map]

theorem keyChunk_ok {c : Nat} (hc : c < 4) {s : State} {P : BitVec 32} {a : Addr} (hO : OutPre s P (8 * c))
    (hA : ArgAt s a P) :
    ∃ s', runBlock isa keyChunk s = some s' ∧
      (∀ w < 8, s'.mem.readW (wordAddr P (8 * c + w)) 32 = Spec.Seed.g (s.mem.readW (wordAddr P (8 * c + w)) 32)) ∧
      (∀ o < 32, (o < 8 * c ∨ 8 * c + 8 ≤ o) → s'.mem.readW (wordAddr P o) 32 = s.mem.readW (wordAddr P o) 32) ∧
      (∀ j, 80 ≤ j → j < slots → slotW s' j = slotW s j) ∧ s'.zf = some (decide (c + 1 = 4)) ∧
      OutPre s' P (8 * (c + 1)) ∧ ArgAt s' a P ∧ s'.gpr sb = s.gpr sb ∧
      (∀ r, r ∉ VG.Impl.Aes.X86.tmpRegs → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s, ⟨P.setWidth 64, 128⟩] s.mem s'.mem := by
  have hS := slots_eq
  have hP := hO.fit
  -- The words to `G`'s inputs.
  obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := esiLoads_ok chunkIn s hO
    (by intro p hp; simp only [chunkIn, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [tSlot, slots_eq]; omega)
    (by simp only [chunkIn, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa [tSlot] using hab) 8)
  have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
  have esi₁ : s₁.gpr .esi = s.gpr .esi := g₁ _ (by decide)
  have h₁ : Room s₁ := hO.room.congr sb₁ wr₁
  have k₁ : ∀ j, 80 ≤ j → j < slots → slotW s₁ j = slotW s j := fun j h1 h2 => o₁ j h2 (by
    simp only [chunkIn, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro w hw he; simp [tSlot] at he; omega)
  -- `G`.
  obtain ⟨s₂, e₂, gv₂, k₂, h₂, rd₂, wr₂, g₂, f₂⟩ := g8_lanes h₁
  have sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), sb₁]
  have hO₂ : OutPre s₂ P (8 * c) := hO.congr sb₂ (by rw [g₂ _ (by decide), esi₁]) (by rw [wr₂, wr₁])
  -- The stores.
  obtain ⟨s₃, e₃, v₃, o₃, sl₃, g₃, rd₃, wr₃, f₃⟩ := stores_ok chunkOut s₂ hO₂
    (by intro p hp; simp only [chunkOut, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [tSlot, slots_eq]; omega)
    (by simp only [chunkOut, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa using hab) 8)
  have sb₃ : s₃.gpr sb = s.gpr sb := by rw [g₃ _ (by decide), sb₂]
  have hO₃ : OutPre s₃ P (8 * c) := hO₂.congr (by rw [sb₃, sb₂]) (g₃ _ (by decide)) wr₃
  -- The end.
  have hA₃ : ArgAt s₃ a P := by
    refine hA.congr (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]) (by rw [sb₃])
      (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) (hA.keep ?_)
    exact (f₁.trans (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      have := workR_sub_scratch s₁; unfold scratchR at this ⊢; rw [sb₁] at this; exact this⟩) |>.sub
        fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  obtain ⟨s', e', hO', z', m', sb', g', rd', wr'⟩ := end_ok hc hO₃ hA₃
  -- `s`'s memory outside the scratch buffer through the first two steps.
  have fr₂ : Frame [scratchR s] s.mem s₂.mem :=
    f₁.trans (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      have := workR_sub_scratch s₁; unfold scratchR at this ⊢; rw [sb₁] at this; exact this⟩)
  have sched₂ : ∀ o < 32, s₂.mem.readW (wordAddr P o) 32 = s.mem.readW (wordAddr P o) 32 := fun o ho =>
    fr₂.readW (r := ⟨wordAddr P o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hO.sep.sub_left (word_sub (n := 32) (by omega) ho)) (by decide)
  have sched' : ∀ o < 32, s'.mem.readW (wordAddr P o) 32 = s₃.mem.readW (wordAddr P o) 32 := fun o _ => by
    rw [m']
  refine ⟨s', ?_, fun w hw => ?_, fun o ho ho' => ?_, fun j h1 h2 => ?_, z', hO',
    hA₃.congr (by rw [g' _ (by decide) (by decide)]) (by rw [sb', sb₃]) rd' wr' (by rw [m']), by rw [sb', sb₃],
    fun r hr hr' => ?_, by rw [rd', rd₃, rd₂, rd₁], by rw [wr', wr₃, wr₂, wr₁], ?_⟩
  · rw [keyChunk_eq, runBlock_append, runBlock_append, runBlock_append, e₁, Option.bind_some, e₂,
      Option.bind_some, e₃, Option.bind_some, e']
  · rw [sched' _ (by omega), v₃ (tSlot w, w) (by simp only [chunkOut, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩),
      tSlot_lane, show slotW s₂ (tSlot 0 + w) = lv s₂ (tSlot 0) w from rfl, gv₂ w hw, lv, ← tSlot_lane,
      v₁ (w, tSlot w) (by simp only [chunkIn, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩)]
  · rw [sched' o ho, o₃ o ho (by
      simp only [chunkOut, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
      intro w hw he; omega), sched₂ o ho]
  · rw [slotW, sb', m', ← slotW, sl₃ j h2, k₂ j h1 h2, k₁ j h1 h2]
  · have hr₁ : r ≠ .eax := fun h => hr (by subst h; decide)
    rw [g' r hr₁ hr', g₃ r hr₁, g₂ r hr, g₁ r hr₁]
  · have fs₃ : Frame [scratchR s, ⟨P.setWidth 64, 128⟩] s.mem s₃.mem :=
      (fr₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
        (f₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
    rw [m']; exact fs₃

/-- The loop of `keyChunk`, from the inputs `U` in the schedule's words and
the count 4: `G` of each. -/
theorem keyChunks_wp {s : State} {P : BitVec 32} {a : Addr} {U : Nat → BitVec 32} (hO : OutPre s P 0)
    (hA : ArgAt s a P) (hU : ∀ o < 32, s.mem.readW (wordAddr P o) 32 = U o) {Q : State → Prop}
    (hQ : ∀ s', (∀ o < 32, s'.mem.readW (wordAddr P o) 32 = Spec.Seed.g (U o)) →
      (∀ j, 80 ≤ j → j < slots → slotW s' j = slotW s j) → s'.gpr sb = s.gpr sb →
      (∀ r, r ∉ VG.Impl.Aes.X86.tmpRegs → r ≠ .esi → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Frame [scratchR s, ⟨P.setWidth 64, 128⟩] s.mem s'.mem → Q s') :
    WP isa (.loop (.block keyChunk) .ne) s Q := by
  let Inv : Nat → State → Prop := fun n t => ∃ c, c < 4 ∧ n = 4 - c ∧ OutPre t P (8 * c) ∧ ArgAt t a P ∧
    (∀ o < 8 * c, t.mem.readW (wordAddr P o) 32 = Spec.Seed.g (U o)) ∧
    (∀ o, 8 * c ≤ o → o < 32 → t.mem.readW (wordAddr P o) 32 = U o) ∧
    (∀ j, 80 ≤ j → j < slots → slotW t j = slotW s j) ∧ t.gpr sb = s.gpr sb ∧
    (∀ r, r ∉ VG.Impl.Aes.X86.tmpRegs → r ≠ .esi → t.gpr r = s.gpr r) ∧
    t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [scratchR s, ⟨P.setWidth 64, 128⟩] s.mem t.mem
  refine WP.loop (M := isa) Inv (fun n t ht => ?_) 4 s
    ⟨0, by decide, rfl, hO, hA, fun o ho => by omega, fun o _ ho => hU o ho, fun _ _ _ => rfl, rfl,
      fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  obtain ⟨c, hc, rfl, hO₁, hA₁, done₁, todo₁, k₁, sb₁, g₁, rd₁, wr₁, f₁⟩ := ht
  obtain ⟨t', e', v', o', k', z', hO', hA', sb', g', rd', wr', f'⟩ := keyChunk_ok hc hO₁ hA₁
  refine WP.of_runBlock ⟨t', e', ?_⟩
  have hP := hO.fit
  have done' : ∀ o < 8 * (c + 1), t'.mem.readW (wordAddr P o) 32 = Spec.Seed.g (U o) := fun o ho => by
    by_cases hlo : o < 8 * c
    · rw [o' o (by omega) (.inl hlo), done₁ o hlo]
    · rw [show o = 8 * c + (o - 8 * c) by omega, v' _ (by omega), todo₁ _ (by omega) (by omega)]
  have k₂ : ∀ j, 80 ≤ j → j < slots → slotW t' j = slotW s j := fun j h1 h2 => by
    rw [k' j h1 h2, k₁ j h1 h2]
  have g₂ : ∀ r, r ∉ VG.Impl.Aes.X86.tmpRegs → r ≠ .esi → t'.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g' r h1 h2, g₁ r h1 h2]
  have f₂ : Frame [scratchR s, ⟨P.setWidth 64, 128⟩] s.mem t'.mem :=
    f₁.trans (by unfold scratchR at f' ⊢; rw [sb₁] at f'; exact f')
  by_cases h3 : c = 3
  · subst h3
    exact .inl ⟨by rw [eval_ne, z']; rfl, hQ t' done' k₂ (by rw [sb', sb₁]) g₂ (by rw [rd', rd₁])
      (by rw [wr', wr₁]) f₂⟩
  · refine .inr ⟨by rw [eval_ne, z']; simp; omega, 4 - (c + 1), by omega, c + 1, by omega, rfl, hO', hA', done',
      fun o h1 h2 => by rw [o' o h2 (.inr (by omega)), todo₁ o (by omega) h2], k₂, by rw [sb', sb₁],
      g₂, by rw [rd', rd₁], by rw [wr', wr₁], f₂⟩

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
      (∀ j < slots, slotW s' j =
        if j = keySlot w then byteRev32 (s.mem.readW (wordAddr K w) 32) else slotW s j) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  have hK := hs.fit
  have hk := keySlot_lt hw
  let v := s.mem.readW (wordAddr K w) 32
  have hea : s.ea (at_ .ecx (4 * w)) = wordAddr K w := by
    show addr (s.gpr .ecx) (4 * w) = _; rw [hs.ecx]
  have hin : InRegions (s.rd ++ s.wr) (wordAddr K w) 4 := ⟨_, hs.mem, slot_contains K (n := 4) hw (by omega)⟩
  let s₁ := s.setReg .eax v
  let s₂ := s₁.setReg .eax (bswap v)
  have h₂ : Room s₂ := room_setReg (room_setReg hs.room (by decide) _) (by decide) _
  have e : runBlock isa [.mov .eax (.mem (at_ .ecx (4 * w))), .bswap .eax, st (keySlot w) .eax] s =
      some (setMem s₂ (s₂.mem.writeW (slotA s₂ (keySlot w)) (s₂.gpr .eax))) := by
    rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .ecx (4 * w)))) s = some s₁ by
        simp only [exec, readSrc, hea, State.load32, hin, ↓reduceIte, Option.map_some]; rfl,
      runStep_some, runBlock_cons,
      show exec (.bswap .eax) s₁ = some s₂ by
        simp only [exec, s₂, s₁, gpr_setReg_self],
      runStep_some, runBlock_cons, exec_st h₂ hk, runStep_some, runBlock_nil]
  have sl : slotA s₂ (keySlot w) = slotA s (keySlot w) := by
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
      (∀ j < slots, (j < keySlot 0 ∨ keySlot n ≤ j) → slotW s' j = slotW s j) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [scratchR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun w hw => by omega, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, f₁⟩ := ih (by omega)
    have sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
    have hs₁ : KeyPre s₁ K := ⟨hs.room.congr sb₁ wr₁, by rw [g₁ _ (by decide)]; exact hs.ecx,
      by rw [rd₁, wr₁]; exact hs.mem, hs.fit, by unfold scratchR; rw [sb₁]; exact hs.sep⟩
    obtain ⟨s₂, e₂, v₂, g₂, rd₂, wr₂, f₂⟩ := ldKey_ok (w := n) (by omega) hs₁
    have hK := hs.fit
    have key₁ : s₁.mem.readW (wordAddr K n) 32 = s.mem.readW (wordAddr K n) 32 :=
      f₁.readW (r := ⟨wordAddr K n, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hs.sep.sub_left (word_sub (n := 4) (by omega) (by omega))) (by decide)
    refine ⟨s₂, ?_, fun w hw => ?_, fun j hj hj' => ?_, fun r hr => by rw [g₂ r hr, g₁ r hr],
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], f₁.trans (by unfold scratchR at f₂ ⊢; rw [sb₁] at f₂; exact f₂)⟩
    · rw [keyWordsCode, List.range_succ, List.flatMap_append, runBlock_append]
      rw [keyWordsCode] at e₁
      rw [e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rw [v₂ _ (keySlot_lt (by omega))]
      by_cases hwn : w = n
      · subst hwn; rw [ite_eq_left rfl, key₁]
      · rw [ite_eq_right (by simp [keySlot]; omega), v₁ w (by omega)]
    · rw [v₂ j hj, ite_eq_right (by simp [keySlot] at hj' ⊢; omega),
        o₁ j hj (by simp [keySlot] at hj' ⊢; omega)]

/-! ## The whole function -/

/-- Argument `i` is in the arguments' region. -/
theorem arg_contains3 (s : State) (hfit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32) {i : Nat} (hi : i < 3) :
    (⟨argAddr s 0, 12⟩ : Region).Contains (argAddr s i) 4 := by
  have hs := toNat_addr (s.gpr .esp)
  rw [show argAddr s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) from addr_eq (by omega),
    show argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from addr_eq (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem slotW_of {s : State} {b : BitVec 32} (h : s.gpr sb = b) (j : Nat) :
    slotW s j = s.mem.readW (wordAddr b j) 32 := by
  simp only [slotW, h]

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86.pre s₀) :
    WP isa expandKey s₀ fun s' => abiPreserved s₀ s' ∧ expandKeyX86.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dAS, dAB, dRS, dRB, fitK, fitS, fitB, fitE⟩ := hp
  let K := arg s₀ 0
  let P := arg s₀ 1
  let b := arg s₀ 2
  have fitK' : K.toNat + 16 ≤ 2 ^ 32 := fitK
  have fitS' : P.toNat + 128 ≤ 2 ^ 32 := fitS
  have fitB' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have hwS : ScrIn s₀.wr b := .exact (by rw [hwr]; simp [b]) fitB
  have hwP : (⟨P.setWidth 64, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [P]
  have hrK : (⟨K.setWidth 64, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [K]
  have hrA : (⟨argAddr s₀ 0, 12⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  -- The arguments, through writes of the scratch buffer.
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 3,
      m.readW (argAddr s₀ i) 32 = arg s₀ i := fun hf i hi =>
    hf.readW (arg_contains3 s₀ fitE hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAB) (by decide)
  have argIn : ∀ {s : State}, s.rd = s₀.rd → s.wr = s₀.wr → s.gpr .esp = s₀.gpr .esp → ∀ i < 3,
      InRegions (s.rd ++ s.wr) (s.ea (argOp i)) 4 := fun h1 h2 h3 i hi => by
    rw [h1, h2, ea_arg h3]; exact ⟨_, List.mem_append_left _ hrA, arg_contains3 s₀ fitE hi⟩
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 2) hwS (argIn rfl rfl rfl 2 (by decide))
    (by rw [ea_arg rfl]; rfl)
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  -- The key's words.
  obtain ⟨s₂, e₂, c₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .ecx 0 (argIn rd₁ wr₁ esp₁ 0 (by decide))
  have sb₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide)]; exact b₁
  have h₂ : Room s₂ := ⟨by rw [sb₂, wr₂, wr₁]; exact hwS.mem, by rw [sb₂]; exact fitB'⟩
  have kp₂ : KeyPre s₂ K :=
    ⟨h₂, by rw [c₂, ea_arg esp₁]; exact argR f₁ 0 (by decide),
      List.mem_append_left _ (by rw [rd₂, rd₁]; exact hrK), fitK', by unfold scratchR; rw [sb₂]; exact dKB⟩
  obtain ⟨s₃, e₃, v₃, o₃, g₃, rd₃, wr₃, f₃⟩ := keyWords_ok kp₂ 4 (Nat.le_refl _)
  have sb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), sb₂]
  have f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem :=
    f₁.trans (by rw [← m₂]; unfold scratchR at f₃; rw [sb₂] at f₃; exact f₃)
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [g₃ _ (by decide), o₂ _ (by decide), esp₁]
  -- The key, as on entry.
  let key := Spec.Seed.blockAt s₀.mem (K.setWidth 64)
  have kw₃ : kwS s₃ = keyWords key 0 := by
    have hk : ∀ w < 4, s₂.mem.readW (wordAddr K w) 32 = s₀.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * w)) 32 :=
      fun w hw => by
        rw [m₂, slot_addr (by omega)]
        exact f₁.readW (r := ⟨K.setWidth 64 + BitVec.ofNat 64 (4 * w), 4⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact dKB.sub_left (Offset.sub_base _ (by omega))) (by decide)
    simp only [kwS, keyWords]
    rw [v₃ 0 (by decide), v₃ 1 (by decide), v₃ 2 (by decide), v₃ 3 (by decide), hk 0 (by decide),
      hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide)]
  -- The schedule's pointer.
  obtain ⟨s₄, e₄, c₄, o₄, m₄, rd₄, wr₄⟩ := ldArg_ok s₃ .esi 1
    (argIn (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]) esp₃ 1 (by decide))
  have sb₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), sb₃]
  have h₄ : Room s₄ := h₂.congr (by rw [sb₄, sb₂]) (by rw [wr₄, wr₃])
  have esi₄ : s₄.gpr .esi = P := by rw [c₄, ea_arg esp₃]; exact argR f₀₃ 1 (by decide)
  -- The inputs of `G`.
  obtain ⟨s₅, e₅, h₅, -, v₅, o₅, g₅, rd₅, wr₅, f₅⟩ := keyRounds_ok key h₄
    (by rw [← kw₃]; simp only [kwS, slotW, m₄, sb₄, sb₃]) 16 (Nat.le_refl _)
  have sb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide) (by decide), sb₄]
  -- The inputs, to the schedule.
  have hO : OutPre s₅ P 0 :=
    ⟨h₅, by rw [g₅ _ (by decide) (by decide) (by decide), esi₄]; simp, by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwP,
      fitS', by unfold scratchR; rw [sb₅]; exact dSB⟩
  obtain ⟨s₆, e₆, v₆, -, sl₆, g₆, rd₆, wr₆, f₆⟩ := stores_ok ((List.range 32).map fun i => (uSlot i, i)) s₅ hO
    (by intro p hp; simp only [List.mem_map, List.mem_range] at hp; obtain ⟨i, hi, rfl⟩ := hp
        exact ⟨uSlot_lt hi, by omega⟩)
    (by simp only [List.map_map]; exact nodup_map_range (fun a b hab => by simpa using hab) 32)
  have sb₆ : s₆.gpr sb = b := by rw [g₆ _ (by decide), sb₅]
  have hO₆ : OutPre s₆ P 0 := hO.congr (by rw [sb₆, sb₅]) (g₆ _ (by decide)) wr₆
  have hU₆ : ∀ o < 32, s₆.mem.readW (wordAddr P o) 32 = slotW s₅ (uSlot o) := fun o ho => by
    have h := v₆ (uSlot o, o) (by simp only [List.mem_map, List.mem_range]; exact ⟨o, ho, rfl⟩)
    simp only [Nat.zero_add] at h
    exact h
  -- The schedule's address, argument 1.
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by
    rw [g₆ _ (by decide), g₅ _ (by decide) (by decide) (by decide), o₄ _ (by decide), esp₃]
  have f₀₆ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨P.setWidth 64, 128⟩] s₀.mem s₆.mem := by
    have f₃₅ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₃.mem s₅.mem := by
      rw [← m₄]; unfold scratchR at f₅; rw [sb₄] at f₅; exact f₅
    exact ((f₀₃.trans f₃₅).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f₆.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  have argK : ∀ {m m' : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨P.setWidth 64, 128⟩] m m' →
      m'.readW (argAddr s₀ 1) 32 = m.readW (argAddr s₀ 1) 32 := fun hf =>
    hf.readW (arg_contains3 s₀ fitE (i := 1) (by decide)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dAB
      · exact dAS) (by decide)
  have hA₆ : ArgAt s₆ (argAddr s₀ 1) P :=
    ⟨ea_arg esp₆ 1, by rw [rd₆, wr₆, rd₅, wr₅, rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact
        List.mem_append_left _ hrA |> fun h => ⟨_, h, arg_contains3 s₀ fitE (by decide)⟩,
      by rw [argK f₀₆]; rfl, fun hf => argK (by unfold scratchR at hf; rw [sb₆] at hf; exact hf)⟩
  refine WP.seq (WP.of_runBlock ⟨s₆, ?_, WP.seq (keyChunks_wp hO₆ hA₆ hU₆
    fun s₈ v₈ k₈ sb₈ g₈ rd₈ wr₈ f₈ => ?_)⟩)
  · rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      e₁, Option.bind_some, keyLoad_eq, runBlock_append, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅, Option.bind_some, keyInputs_eq, e₆]
  have edi₈ : s₈.gpr .edi = b := by rw [show Reg.edi = sb from rfl, sb₈, sb₆]
  -- The epilogue.
  have sv₈ : Saved s₀ b s₈.mem := by
    intro i hi
    have hs : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega
    rw [← slotW_of edi₈, k₈ _ (by rw [savedSlot_eq]; omega) hs, sl₆ _ hs,
      o₅ _ hs (.inr (by simp [uSlot, aSlot, savedSlot_eq]; omega)) (.inr (by simp [keySlot, tailSlot, savedSlot_eq]; omega)),
      slotW_of sb₄, m₄, ← slotW_of sb₃, o₃ _ hs (.inr (by simp [keySlot, tailSlot, savedSlot_eq]; omega)),
      slotW_of sb₂, m₂]
    exact sv₁ i hi
  obtain ⟨s₉, e₉, rg₉, o₉, m₉, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [wr₈, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwS) edi₈ sv₈
  have f₀₈ : Frame [⟨b.setWidth 64, 4 * slots⟩, ⟨P.setWidth 64, 128⟩] s₀.mem s₈.mem := by
    unfold scratchR at f₈; rw [sb₆] at f₈
    exact f₀₆.trans f₈
  refine WP.of_runBlock ⟨s₉, e₉, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rg₉ 0 (by decide)
    · exact rg₉ 1 (by decide)
    · exact rg₉ 2 (by decide)
    · exact rg₉ 3 (by decide)
    · rw [o₉ _ (fun i hi => by revert i; decide), g₈ _ (by decide) (by decide), esp₆]
  · rw [m₉]
    exact f₀₈.readW (r := ⟨(s₀.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dRB
      · exact dRS) (by decide)
  · show Spec.Seed.scheduleAt s₉.mem (P.setWidth 64) = Spec.Seed.expandKey key
    rw [Proof.Seed.expandKey_eq]
    apply Vector.ext; intro i hi
    rw [Proof.Seed.scheduleAt_readW _ _ i hi, Vector.getElem_ofFn, m₉, ← slot_addr (by omega), v₈ i (by omega),
      v₅ i (by omega)]

end VG.Proof.Seed.X86
