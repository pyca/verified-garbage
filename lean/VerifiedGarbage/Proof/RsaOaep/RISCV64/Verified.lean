module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.CTMain
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-OAEP encryption on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Verified.lean`): the contract's public data as
`PubO`, with the table's (`pubT_of`); constant time (`code_constantTime`,
from `code_ct`); states meeting the precondition for the hash functions the
label is hashed with, with MGF1's table that of any `w` of `vs`, at
`0x300000` (`enc_sat`); and `enc_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.HashTable.RISCV64 (TVar tables fnsOf Coh)

theorem leak_eq {a b c d : List Byte} {w w' : List (BitVec 64)} (ha : a.length = c.length)
    (hb : b.length = d.length)
    (h : (a ++ b).map (·.toNat) ++ w.map (·.toNat) = (c ++ d).map (·.toNat) ++ w'.map (·.toNat)) :
    b = d ∧ w = w' := by
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [ha, hb])
  have hi : a ++ b = c ++ d := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₁
  exact ⟨(List.append_inj hi ha).2, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 h₂⟩

/-- The contract's public data: `PubO`, MGF1's table at the same address,
the tables' functions at the same addresses, and the same tables held. -/
theorem pubT_of {Hs : Spec.Mgf1.Hash} {ts : List FnTable} {s₁ s₂ : State} (h : (encSpec Hs ts).pub s₁ s₂) :
    PubO s₁ s₂ ∧ stackArg s₂ 7 = stackArg s₁ 7 ∧
      (∀ f ∈ (ts.map (fun T : FnTable => T.fns)).flatten, s₁.syms f = s₂.syms f) ∧
      ∀ T ∈ ts, (Abi.tableHeld 64 s₁.mem (stackArg s₁ 7) (FnTable.words isa s₁ T) ↔
        Abi.tableHeld 64 s₂.mem (stackArg s₂ 7) (FnTable.words isa s₂ T)) := by
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec at h
  rw [e] at h
  sig_pub [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi, argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at h
  obtain ⟨hsp, hsy, htab, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  obtain ⟨he, hw⟩ := leak_eq (by simp [bytesAt_length, h3]) (by simp [bytesAt_length, h5]) hl
  refine ⟨⟨hsp.symm, fun r hr => ?_, fun i hi => ?_, he.symm, hw.symm⟩, a7.symm, hsy,
    fun T hT => htab _ _ rfl rfl T hT⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0.symm, a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm]

theorem pubO_refl (s : State) : PubO s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

section
variable {H : Hash} (hH : HashOK H) (cH : HashCT hH) (fH : FitsF H) {Hs : Spec.Mgf1.Hash}
  (hHh : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D)
include cH fH hHh hHl

/-- Constant time: the table of the first run, which the public data makes
the second's, at the same address with its functions at the same addresses. -/
theorem code_constantTime {vs : List TVar} (hc : Coh vs) :
    ConstantTime isa (encSpec Hs (tables vs)).pre (encSpec Hs (tables vs)).pub (encrypt H (fnsOf vs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨⟨T, hT, hh⟩, -⟩ := spec_tab h₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨p, a7, hsy, hiff⟩ := pubT_of hp
  have hn := Proof.HashTable.RISCV64.mem_names hw
  have P₁ : PreO H.D s₁ := hHl ▸ preO_of h₁
  have P₂ : PreO H.D s₂ := hHl ▸ preO_of h₂
  exact code_ct hH cH w.l.ok w.l.ct fH w.l.fits w.l.hash w.l.len w.l.valid hHh hHl _ _ _ _ _ _
    ⟨s₁, ⟨⟨P₁, tabS_entry hc h₁ hw hh⟩, pubO_refl s₁, rfl, rfl, rfl, rfl⟩,
      ⟨P₂, tabS_entry hc h₂ hw ((hiff _ hT).mp hh)⟩, p, a7, (hsy _ hn.1).symm, (hsy _ hn.2.1).symm,
      (hsy _ hn.2.2).symm⟩ e₁ e₂

/-- `vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` against its contract, for the
tables of `vs`, given a state meeting it. -/
theorem enc_verified {vs : List TVar} (hc : Coh vs) (hsat : ∃ s, (encSpec Hs (tables vs)).pre s) :
    Verified RISCV64.target (encrypt H (fnsOf vs)) (encSpec Hs (tables vs)) :=
  ⟨code_correct hH fH hHh hHl hc, code_constantTime hH cH fH hHh hHl hc, hsat⟩

end

/-! ## A state meeting the precondition -/

/-- A state meeting encryption's contract for a seed of `D` bytes, but for
the table: a 512-bit modulus, a one-byte `e`, an empty label and message,
the seed, a working space of 2080 words, 16 words of `pre` at `0x5000`, the
stack arguments at `sp`, and MGF1's table's address `0x300000`. -/
def encSatState (D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x2000 | .a3 => 64 | .a4 => 0x3000 | .a5 => 1 | .a6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10001 then 0x41
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x1001A then 0x02
    else bif Nat.beq a.toNat 0x10020 then 0x20 else bif Nat.beq a.toNat 0x10021 then 0x08
    else bif Nat.beq a.toNat 0x10029 then 0x50 else bif Nat.beq a.toNat 0x10030 then 16
    else bif Nat.beq a.toNat 0x1003A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, D⟩, ⟨0x5000, 128⟩, ⟨0x300000, 40⟩,
    ⟨0x10000, 64⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16640⟩]

section
variable {vs : List TVar} {w : TVar}

theorem stackArgAddr_sat (D j : Nat) (hj : j < 8) :
    (stackArgAddr (encSatState D) j).toNat + 8 ≤ 0x300000 := by
  revert j; show ∀ j < 8, (stackArgAddr (encSatState 0) j).toNat + 8 ≤ 0x300000; decide

theorem stackArg_sat {D j : Nat} {v : Addr} (hj : j < 8) (e : stackArg (encSatState 0) j = v) :
    stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) j = v :=
  (Proof.HashTable.RISCV64.withTable_below _ _ _ (stackArgAddr_sat D j hj)).trans e

theorem sat_a0 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x4100 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a1 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 1 = 0 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a2 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 2 = 0x4200 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a3 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 3 = 0x20000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a4 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 4 = 2080 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a5 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 5 = 0x5000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a6 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 6 = 16 :=
  stackArg_sat (by decide) (by decide)
theorem sat_a7 (D : Nat) : stackArg (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 7 = 0x300000 :=
  stackArg_sat (by decide) (by decide)
theorem sat_e (D : Nat) : stackArgAddr (Proof.HashTable.RISCV64.withTable (encSatState D) vs w) 0 = 0x10000 :=
  show stackArgAddr (encSatState 0) 0 = _ by decide

/-- A state meeting the contract, for the hash functions the label is hashed
with, with MGF1's table that of `w`, at `0x300000`. -/
theorem enc_sat {H : Spec.Mgf1.Hash} (hH : H ∈ labelHashes) (hw : w ∈ vs)
    (hl : (Proof.HashTable.RISCV64.names vs).length < 2 ^ 32) : ∃ s, (encSpec H (tables vs)).pre s := by
  refine ⟨Proof.HashTable.RISCV64.withTable (encSatState H.len) vs w, ?_⟩
  have e : stackBytes = 335 + 1 := rfl
  unfold encSpec
  rw [e]
  simp only [labelHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptTableContract, Spec.RsaOaep.encryptTableSig, Spec.RsaOaep.encryptPrecomputedSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
      argRegs, stackArgs_eight, List.append_eq, List.range, List.range.loop]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', sat_a0, sat_a1, sat_a2, sat_a3, sat_a4, sat_a5, sat_a6,
      sat_a7, sat_e]
    sig_and_intros
    all_goals first
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | exact ⟨Proof.HashTable.RISCV64.tableOf w, List.mem_map_of_mem hw, Proof.HashTable.RISCV64.withTable_held _ _ _⟩
      | exact Proof.HashTable.symsOf_distinct hl
      | (simp only [Spec.Rsa.lenValid]; decide)

end

end VG.Proof.RsaOaep.RISCV64
