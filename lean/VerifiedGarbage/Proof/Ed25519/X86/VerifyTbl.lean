module

public import VerifiedGarbage.Impl.Ed25519.X86.VerifyWindow
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.ReadHalves
public import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ed25519.X86.Workspace

/-!
# Ed25519 verification on x86 (32-bit): `-[1]B … -[15]B` in a static

The words of the static `bSym` (`bWords`), as a contract states them (`BHeld`) and as the copy
into the working space reads them, a dword at a time (`BTblAt`, `bDword`), and a memory holding
them for contracts' witnesses (`bSatMem`). Nothing here evaluates the table: each lemma holds for
its words by their definition (`bWord`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86 VG.Impl.X25519.X86

theorem bWords_length : bWords.length = 240 := by simp [bWords]

theorem bWords_getD {i : Nat} (hi : i < 240) : bWords.getD i 0 = bWord i := by
  simp [bWords, List.getD_eq_getElem?_getD, hi]

theorem bConsts_eq : bConsts = [(bSym, bWords)] := rfl

/-- Dword `d` of the static: word `d % 8` of coordinate `d / 8 % 4` of `negBase (d / 32)`. -/
def bDword (d : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((pointCoord (negBase (d / 32)) (d / 8 % 4)).val / (2 ^ 32) ^ (d % 8))

theorem bWord_lo (i : Nat) : (bWord i).setWidth 32 = bDword (2 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [bWord, bDword, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show 2 * i / 32 = i / 16 by omega, show 2 * i / 8 % 4 = i / 4 % 4 by omega,
    show 2 * i % 8 = 2 * (i % 4) by omega, ← Nat.pow_mul, show 32 * (2 * (i % 4)) = 64 * (i % 4) by omega,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem bWord_hi (i : Nat) : (bWord i).extractLsb' 32 32 = bDword (2 * i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [bWord, bDword, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 * i + 1) / 32 = i / 16 by omega, show (2 * i + 1) / 8 % 4 = i / 4 % 4 by omega,
    show (2 * i + 1) % 8 = 2 * (i % 4) + 1 by omega, ← Nat.pow_mul,
    show (2 : Nat) ^ (32 * (2 * (i % 4) + 1)) = 2 ^ (64 * (i % 4)) * 2 ^ 32 by
      rw [← Nat.pow_add]; congr 1; omega,
    ← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self,
    Nat.mod_mod]

/-- The static, in `s`, as a contract states it: its words, not wrapping around, apart from the
regions `wr`. -/
def BHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < 240, s.mem.readW ((s.syms bSym).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0) ∧
  (s.syms bSym).toNat + 1920 ≤ 2 ^ 32 ∧
  ∀ r ∈ wr, Region.Disjoint ⟨(s.syms bSym).setWidth 64, 1920⟩ r

/-- The static at `T`: readable, apart from the working space at `x`, dword `d` its `bDword d`. -/
structure BTblAt (s : State) (x T : BitVec 32) : Prop where
  fit : T.toNat + 1920 ≤ 2 ^ 32
  rd : (⟨T.setWidth 64, 1920⟩ : Region) ∈ s.rd ++ s.wr
  sc : (⟨T.setWidth 64, 1920⟩ : Region).Disjoint (scR 8192 x)
  val : ∀ d < 480, wd s.mem T (4 * d) = bDword d

/-- Dword `d` of the static, readable. -/
theorem BTblAt.inR {s : State} {x T : BitVec 32} (h : BTblAt s x T) {d : Nat} (hd : d < 480) :
    InRegions (s.rd ++ s.wr) (addr T (4 * d)) 4 :=
  ⟨_, h.rd, by
    have := sub_contains (x := T) (a := 0) (k := 1920) (d := 4 * d) (n := 4) (by have := h.fit; omega)
      (Nat.zero_le _) (by omega) (by decide)
    rwa [sub, addr_zero] at this⟩

/-- The static survives what changes only regions apart from it. -/
theorem BTblAt.of_frame {s t : State} {x T : BitVec 32} (h : BTblAt s x T) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, (⟨T.setWidth 64, 1920⟩ : Region).Disjoint r)
    (hrd : t.rd ++ t.wr = s.rd ++ s.wr) : BTblAt t x T :=
  ⟨h.fit, hrd ▸ h.rd, h.sc, fun d hd' => by
    rw [← h.val d hd']
    have hc : (⟨T.setWidth 64, 1920⟩ : Region).Contains (addr T (4 * d)) 4 := by
      have := sub_contains (x := T) (a := 0) (k := 1920) (d := 4 * d) (n := 4) (by have := h.fit; omega)
        (Nat.zero_le _) (by omega) (by decide)
      rwa [sub, addr_zero] at this
    exact Frame.readW hf hc (fun r hr => hd r hr) (by decide)⟩

/-- The static, from a contract's facts: readable, and apart from the working space at `x`. -/
theorem BHeld.tblAt {s : State} {wr : List Region} {x : BitVec 32} (h : BHeld s wr)
    (hrd : (⟨(s.syms bSym).setWidth 64, 1920⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : scR 8192 x ∈ wr) : BTblAt s x (s.syms bSym) := by
  obtain ⟨held, fit', dj⟩ := h
  refine ⟨fit', hrd, dj _ hsc, fun d hd => ?_⟩
  have hw := held (d / 2) (by omega)
  rw [bWords_getD (by omega)] at hw
  obtain ⟨i, rfl | rfl⟩ : ∃ i, d = 2 * i ∨ d = 2 * i + 1 := ⟨d / 2, by omega⟩
  · rw [show 2 * i / 2 = i by omega] at hw
    rw [wd, addr_eq (by omega), show 4 * (2 * i) = 8 * i by omega, Mem.readW_lo32 hw, bWord_lo]
  · rw [show (2 * i + 1) / 2 = i by omega] at hw
    rw [wd, addr_eq (by omega), show 4 * (2 * i + 1) = 8 * i + 4 by omega, ← Offset.add_add,
      Mem.readW_hi32 hw, bWord_hi]

/-- The memory of the contracts' witnesses: the static at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the table). -/
@[irreducible] def bSatMem : Mem := constMem 0x100000 bWords

theorem bSatMem_held : ∀ i < 240,
    bSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  unfold bSatMem
  intro i hi
  exact constMem_held _ _ (by rw [bWords_length]; omega) i (by rw [bWords_length]; exact hi)

end VG.Proof.Ed25519.X86
