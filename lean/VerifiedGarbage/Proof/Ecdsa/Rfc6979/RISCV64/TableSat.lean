module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on RISC-V: the contract with the table is satisfiable

A state meeting `TableInstance.signContract` with the tables of `vs`
(`satT`): the buffers at fixed addresses, the table of a variant `w` of
`vs` at `0x300000`, the functions of `vs` at distinct addresses
(`HashTable.symsOf`), and the curve's table of constants, if any, at
`0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG VG.RISCV64
open VG.Proof.HashTable.RISCV64 (TVar tables names tableOf held_tableOf hashAt_tableOf mem_names)
open VG.Proof.HashTable (symsOf symsOf_distinct put5 put5_held put5_below)

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List TVar) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => BitVec.ofNat 64 w.H.D | .a4 => 0x8000
    | .a5 => 0x300000 | _ => 0
  sp := 0x20000
  mem := put5 m₀ 0x300000 (symT vs w.H.initN) (symT vs w.H.updN) (symT vs w.H.finN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.l.G)) (BitVec.ofNat 64 w.l.G.len)
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.H.D⟩, ⟨0x300000, 40⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 64 (satT vs w m₀ Q Tr).mem 0x300000 (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) :=
  put5_held (ws := [symT vs w.H.initN, symT vs w.H.updN, symT vs w.H.finN,
    BitVec.ofNat 64 (Spec.HashTable.index w.l.G), BitVec.ofNat 64 w.l.G.len]) rfl

theorem symT_distinct {vs : List TVar} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

/-- Regions at literal addresses, one below the other. -/
theorem sep_lit {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 64) (hb : b + k ≤ 2 ^ 64)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) :
    Region.Disjoint ⟨BitVec.ofNat 64 a, n⟩ ⟨BitVec.ofNat 64 b, k⟩ :=
  Region.disjoint_of_sep (by
    simp only [Region.sep, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']
    omega)


theorem satT_sym (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) {n : String}
    (h : n ∉ names vs) : (satT vs w m₀ Q Tr).syms n = 0x100000 := by
  simp only [satT, symT, h, ite_false]

theorem constRegions_symT (vs : List TVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => symT vs name) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := w.l.ok.hD64
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  have hG : Spec.HashTable.hashAt 64 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem 0x300000 =
      some w.l.G := hashAt_tableOf (held_tableOf (satT_held vs w m₀ _ _)).2.1
  simp only [hsw, hDn, satT] at hG ⊢
  sig_and_intros
  all_goals try (intro c hc; simp only [List.mem_singleton] at hc; subst hc)
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w m₀ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact (constRegions_symT vs n W hna).symm
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.l.len.symm, by rw [hw.hmac]; rfl⟩)
    | (intro i hi
       show (put5 m₀ _ _ _ _ _ _).readW (symT vs n + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, put5_below (by bv_omega)]
       exact hheld i hi)
    | (show (1048576 : BitVec 64).toNat % 64 = 0; decide)
    | (refine ⟨show (1048576 : BitVec 64).toNat + 8 * W.length ≤ 2 ^ 64 by bv_omega, ?_, ?_, ?_⟩ <;>
       exact Region.disjoint_of_sep (by
         simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := w.l.ok.hD64
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HashTable.hashAt 64 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem 0x300000 =
      some w.l.G := hashAt_tableOf (held_tableOf (satT_held vs w _ _ _)).2.1
  simp only [hsw, hDn, satT] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.l.len.symm, by rw [hw.hmac]; rfl⟩)

end VG.Proof.Ecdsa.Rfc6979.RISCV64
