module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd -- shake: keep (brun's simp set reads its lemmas)
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # The generator stage's arguments in the generation's frame slots -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generator

/-- The frame words the entry sets: the working space `B`, the h tape `hp`
of `n` bytes, the hash workspace, and zero. -/
def entryWords (B hp n : Addr) (k : Nat) : BitVec 64 :=
  if k = 5 then B else if k = 11 then hp else if k = 12 then off B Impl.Dsa.Generation.Layout.hash
  else if k = 13 then n else 0

/-- The memory after the entry's stores. -/
def entryMem (s : State) (F : Addr) : Mem :=
  zeroSlots.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64))
    ((((s.mem.writeW (off F 40) (s.gpr .x0)).writeW (off F 88) (s.gpr .x2)).writeW (off F 104) (s.gpr .x3)).writeW
      (off F 96) (off (s.gpr .x0) Impl.Dsa.Generation.Layout.hash))

theorem word_writeW_frame (m : Mem) (F : Addr) (v : BitVec 64) {d e : Nat}
    (hd : d % 8 = 0 ∧ d + 8 ≤ 448) (he : e % 8 = 0 ∧ e + 8 ≤ 448) :
    word (m.writeW (off F d) v) F e = if d = e then v else word m F e := by
  split
  · subst e; exact word_writeW_self _ _ _ _
  · exact (writeW_outside m F v (by omega)).word (by omega) (by omega)

theorem word_foldl_zero (F : Addr) {e : Nat} (he : e < 34) :
    ∀ (l : List Nat), (∀ k ∈ l, k < 34) → ∀ m : Mem,
      word (l.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64)) m) F (8 * e) =
        if e ∈ l then 0 else word m F (8 * e)
  | [], _, m => by simp
  | k :: l, hl, m => by
    rw [List.foldl_cons, word_foldl_zero F he l (fun j hj => hl j (List.mem_cons_of_mem _ hj)),
      word_writeW_frame _ F _ (by have := hl k List.mem_cons_self; omega) (by omega)]
    by_cases hk : k = e
    · subst hk; simp
    · by_cases hel : e ∈ l
      · simp [hel]
      · have : 8 * k ≠ 8 * e := by omega
        simp [hel, this, Ne.symm hk]

/-- The words the entry sets. -/
theorem entryMem_word (s : State) (F : Addr) {k : Nat}
    (hk : k = 5 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k ∈ zeroSlots) :
    word (entryMem s F) F (8 * k) = entryWords (s.gpr .x0) (s.gpr .x2) (s.gpr .x3) k := by
  have bound : k < 34 := by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  unfold entryMem
  rw [word_foldl_zero F bound zeroSlots (by decide),
    word_writeW_frame _ F _ (d := 96) (by decide) (by omega),
    word_writeW_frame _ F _ (d := 104) (by decide) (by omega),
    word_writeW_frame _ F _ (d := 88) (by decide) (by omega),
    word_writeW_frame _ F _ (d := 40) (by decide) (by omega)]
  simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [entryWords, zeroSlots]

theorem foldl_zero_frame (F : Addr) :
    ∀ (l : List Nat), (∀ k ∈ l, k < 34) → ∀ {m₀ m : Mem}, Frame [⟨F, 272⟩] m₀ m →
      Frame [⟨F, 272⟩] m₀ (l.foldl (fun m k => m.writeW (off F (8 * k)) (0 : BitVec 64)) m)
  | [], _, _, _, h => h
  | k :: l, hl, _, _, h => by
    rw [List.foldl_cons]
    exact foldl_zero_frame F l (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      (h.writeW List.mem_cons_self _ (Offset.contains_base F (n := 8) (by have := hl k List.mem_cons_self; omega)
        (by have := hl k List.mem_cons_self; omega)))

/-- The entry writes only the frame words. -/
theorem entryMem_frame (s : State) (F : Addr) : Frame [⟨F, 272⟩] s.mem (entryMem s F) := by
  unfold entryMem
  have c (d : Nat) (hd : d + 8 ≤ 272) : (⟨F, 272⟩ : Region).Contains (off F d) (64 / 8) :=
    Offset.contains_base F hd (by omega)
  exact foldl_zero_frame F zeroSlots (by decide)
    (((((Frame.refl _ _).writeW List.mem_cons_self _ (c 40 (by decide))).writeW List.mem_cons_self _
      (c 88 (by decide))).writeW List.mem_cons_self _ (c 104 (by decide))).writeW List.mem_cons_self _ (c 96 (by decide)))

theorem entry_ok {s : State} {F : Addr} (hsp : s.sp = F)
    (hw : ∀ d, d + 8 ≤ 272 → InRegions s.wr (off F d) 8) :
    WP isa (.block entry) s fun t => t.mem = entryMem s F ∧ Keep [.x4] s t := by
  have run : WP isa (.block entry) s fun t => t.mem = entryMem s F := by
    simp only [entry, zeroSlots, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    have hh : BitVec.setWidth 64 (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.hash) =
        BitVec.ofNat 64 Impl.Dsa.Generation.Layout.hash := by decide
    have h0 : BitVec.setWidth 64 (0#16) = (0 : BitVec 64) := by decide
    brun [State.write, hh, h0, exec_storeSp (off := 40) (by decide), exec_storeSp (off := 88) (by decide),
      exec_storeSp (off := 104) (by decide), exec_storeSp (off := 96) (by decide),
      exec_storeSp (off := 8) (by decide), exec_storeSp (off := 24) (by decide), exec_storeSp (off := 32) (by decide),
      exec_storeSp (off := 48) (by decide), exec_storeSp (off := 56) (by decide), exec_storeSp (off := 64) (by decide),
      exec_storeSp (off := 72) (by decide), exec_storeSp (off := 80) (by decide), exec_storeSp (off := 112) (by decide),
      exec_storeSp (off := 120) (by decide), exec_storeSp (off := 128) (by decide), exec_storeSp (off := 136) (by decide),
      exec_storeSp (off := 144) (by decide), exec_storeSp (off := 208) (by decide),
      hsp, hw 40 (by decide), hw 88 (by decide), hw 104 (by decide), hw 96 (by decide),
      hw 8 (by decide), hw 24 (by decide), hw 32 (by decide), hw 48 (by decide), hw 56 (by decide), hw 64 (by decide),
      hw 72 (by decide), hw 80 (by decide), hw 112 (by decide), hw 120 (by decide), hw 128 (by decide),
      hw 136 (by decide), hw 144 (by decide), hw 208 (by decide), off]
    simp only [entryMem, zeroSlots, List.foldl_cons, List.foldl_nil, Nat.reduceMul]

  exact WP.mono (WP.keep [.x4] run (by decide)) fun t ⟨hm, k⟩ => ⟨hm, k⟩

end VG.Proof.Dsa.AArch64.Generator
