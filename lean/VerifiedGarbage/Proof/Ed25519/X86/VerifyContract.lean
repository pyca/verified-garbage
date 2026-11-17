module

public import VerifiedGarbage.Proof.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.X86.CopyWords
public import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity
public import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.X86.VerifyWindow
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.ReadHalves
public import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Ed25519.X86.Workspace

/-! ### `Ed25519.X86.VerifyTbl`, which this module and modules that import it used -/

section

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
  rw [show 2 * i / 32 = i / 16 by omega_using [], show 2 * i / 8 % 4 = i / 4 % 4 by omega_using [],
    show 2 * i % 8 = 2 * (i % 4) by omega_using [], ← Nat.pow_mul, show 32 * (2 * (i % 4)) = 64 * (i % 4) by omega_using [],
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem bWord_hi (i : Nat) : (bWord i).extractLsb' 32 32 = bDword (2 * i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [bWord, bDword, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 * i + 1) / 32 = i / 16 by omega_using [], show (2 * i + 1) / 8 % 4 = i / 4 % 4 by omega_using [],
    show (2 * i + 1) % 8 = 2 * (i % 4) + 1 by omega_using [], ← Nat.pow_mul,
    show (2 : Nat) ^ (32 * (2 * (i % 4) + 1)) = 2 ^ (64 * (i % 4)) * 2 ^ 32 by
      rw [← Nat.pow_add]; congr 1; omega_using [],
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
    have := sub_contains (x := T) (a := 0) (k := 1920) (d := 4 * d) (n := 4) (by have := h.fit; omega_using [this])
      (Nat.zero_le _) (by omega_using [hd]) (by decide)
    rwa [sub, addr_zero] at this⟩

/-- The static survives what changes only regions apart from it. -/
theorem BTblAt.of_frame {s t : State} {x T : BitVec 32} (h : BTblAt s x T) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, (⟨T.setWidth 64, 1920⟩ : Region).Disjoint r)
    (hrd : t.rd ++ t.wr = s.rd ++ s.wr) : BTblAt t x T :=
  ⟨h.fit, hrd ▸ h.rd, h.sc, fun d hd' => by
    rw [← h.val d hd']
    have hc : (⟨T.setWidth 64, 1920⟩ : Region).Contains (addr T (4 * d)) 4 := by
      have := sub_contains (x := T) (a := 0) (k := 1920) (d := 4 * d) (n := 4) (by have := h.fit; omega_using [this])
        (Nat.zero_le _) (by omega_using [hd']) (by decide)
      rwa [sub, addr_zero] at this
    exact Frame.readW hf hc (fun r hr => hd r hr) (by decide)⟩

/-- The static, from a contract's facts: readable, and apart from the working space at `x`. -/
theorem BHeld.tblAt {s : State} {wr : List Region} {x : BitVec 32} (h : BHeld s wr)
    (hrd : (⟨(s.syms bSym).setWidth 64, 1920⟩ : Region) ∈ s.rd ++ s.wr)
    (hsc : scR 8192 x ∈ wr) : BTblAt s x (s.syms bSym) := by
  obtain ⟨held, fit', dj⟩ := h
  refine ⟨fit', hrd, dj _ hsc, fun d hd => ?_⟩
  have hw := held (d / 2) (by omega_using [hd])
  rw [bWords_getD (by omega_using [hd])] at hw
  obtain ⟨i, rfl | rfl⟩ : ∃ i, d = 2 * i ∨ d = 2 * i + 1 := ⟨d / 2, by omega_using []⟩
  · rw [show 2 * i / 2 = i by omega_using []] at hw
    rw [wd, addr_eq (by omega_using [fit', hd]), show 4 * (2 * i) = 8 * i by omega_using [], Mem.readW_lo32 hw, bWord_lo]
  · rw [show (2 * i + 1) / 2 = i by omega_using []] at hw
    rw [wd, addr_eq (by omega_using [fit', hd]), show 4 * (2 * i + 1) = 8 * i + 4 by omega_using [], ← Offset.add_add,
      Mem.readW_hi32 hw, bWord_hi]

/-- The memory of the contracts' witnesses: the static at `0x100000` (irreducible: unfolding it
in a definitional check would evaluate the table). -/
@[irreducible] def bSatMem : Mem := constMem 0x100000 bWords

theorem bSatMem_held : ∀ i < 240,
    bSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  unfold bSatMem
  intro i hi
  exact constMem_held _ _ (by rw [bWords_length]; omega_using []) i (by rw [bWords_length]; exact hi)

end VG.Proof.Ed25519.X86

end

end

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

def verifyLocal : Contract isa where
  pre s :=
    let pk := sub (arg s 0) 0 32
    let sig := sub (arg s 1) 0 64
    let challenge := sub (arg s 2) 0 64
    let scratch := scR 8192 (arg s 3)
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := callStk s
    let tbl : Region := ⟨(s.syms bSym).setWidth 64, 1920⟩
    s.rd = [pk, sig, challenge, args, tbl] ∧ s.wr = [sub (arg s 3) 0 0, scratch] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint scratch ∧
      stk.Disjoint pk ∧ stk.Disjoint sig ∧ stk.Disjoint challenge ∧ BHeld s [scratch, stk]
  post s t := t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) 64 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 2).setWidth 64) 64 ∧
    s.syms bSym = t.syms bSym

theorem input_slice {s : State} {scidx i n skip bytes : Nat} (h : InputPre s scidx i n)
    (hn : skip + bytes ≤ 4 * n) (hb : 0 < bytes) :
    SlicePre s scidx (arg s i + BitVec.ofNat 32 skip) bytes := by
  have hf := h.fit
  have hs : skip < 2 ^ 32 := by omega_using [hn, hb, hf]
  have hsub : (sub (arg s i + BitVec.ofNat 32 skip) 0 bytes).Sub (sub (arg s i) 0 (4 * n)) := by
    rw [sub, addr_plus, Nat.add_zero, sub, addr_eq (by omega_using [hn, hb, hf]), addr_zero]
    exact Offset.sub_base _ hn
  refine ⟨?_, ?_, h.sep.sub_left hsub, h.stk.sub_left hsub⟩
  · intro k len hl hk
    rw [addr_plus]
    exact ⟨_, h.rd, sub_contains (by omega_using [hf]) (Nat.zero_le _)
      (by omega_using [hn, hk]) hl⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt (by omega_using [hn, hb, hf])]
    omega_using [hn, hf]

structure VerifyPre (s : State) : Prop where
  scratch : ScratchPre s 3 4
  pk : SlicePre s 3 (arg s 0 + BitVec.ofNat 32 0) 32
  r : SlicePre s 3 (arg s 1 + BitVec.ofNat 32 0) 32
  scalar : SlicePre s 3 (arg s 1 + BitVec.ofNat 32 32) 32
  challenge : SlicePre s 3 (arg s 2 + BitVec.ofNat 32 0) 64
  signature_fit : (arg s 1).toNat + 64 ≤ 2 ^ 32
  /-- The static of `-[1]B … -[15]B`, which the equation copies. -/
  tbl : BTblAt s (arg s 3) (s.syms bSym)
  tblStk : (⟨(s.syms bSym).setWidth 64, 1920⟩ : Region).Disjoint (callStk s)

theorem verify_pre {s : State} (h : verifyLocal.pre s) : VerifyPre s := by
  obtain ⟨rd, wr, ps, ss, cs, ars, rs, pf, sf, cf, scf, spf, h20, ks, kp, kg, kc, held⟩ := h
  have hp : ScratchPre s 3 4 := ⟨by decide, by rw [wr]; simp, scf,
    by rw [rd]; simp, by omega_using [spf], ars, rs, h20, ks.symm⟩
  have p : InputPre s 3 0 8 := ⟨by rw [rd]; simp, pf, ps, kp.symm⟩
  have sg : InputPre s 3 1 16 := ⟨by rw [rd]; simp, sf, ss, kg.symm⟩
  have ch : InputPre s 3 2 16 := ⟨by rw [rd]; simp, cf, cs, kc.symm⟩
  exact ⟨hp, input_slice p (by decide) (by decide), input_slice sg (by decide) (by decide),
    input_slice sg (by decide) (by decide), input_slice ch (by decide) (by decide), sf,
    held.tblAt (by rw [rd]; simp) (by simp), held.2.2 _ (by simp)⟩

end VG.Proof.Ed25519.X86
