module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.RISCV64.TableSpec
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on RISC-V: the contract with the table is satisfiable

A state meeting `TableInstance.signContract` with the tables of `vs`
(`satT`): the buffers at fixed addresses, the table of a hash function `w`
of `vs` at `0x300000`, the functions of `vs` at distinct addresses
(`HashTable.symsOf`), and the curve's table of constants, if any, at
`0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.RISCV64

open VG VG.RISCV64
open VG.Proof.HmacTable.RISCV64 (HVar tables names tableOf held_tableOf hashAt_tableOf mem_names)
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)

/-- Six words at `p`. -/
def put6 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) w₀).writeW (p + BitVec.ofNat 64 (8 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (8 * 2)) w₂).writeW (p + BitVec.ofNat 64 (8 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (8 * 4)) w₄).writeW (p + BitVec.ofNat 64 (8 * 5)) w₅

/-- The table `put6` writes at `0x300000`. -/
theorem put6_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 64 (put6 m 0x300000 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0)
      (ws.getD 5 0)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64,
      BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [Mem.readW_writeW_self64, BitVec.setWidth_eq]

/-- What `put6` keeps below the table. -/
theorem put6_below {m : Mem} {a : Addr} (ha : a.toNat + 8 ≤ 0x300000) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 64) :
    (put6 m 0x300000 w₀ w₁ w₂ w₃ w₄ w₅).readW a 64 = m.readW a 64 := by
  have h0 : (0x300000 + BitVec.ofNat 64 (8 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (8 * 1) : Addr).toNat = 0x300008 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (8 * 2) : Addr).toNat = 0x300010 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (8 * 3) : Addr).toNat = 0x300018 := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (8 * 4) : Addr).toNat = 0x300020 := by decide
  have h5 : (0x300000 + BitVec.ofNat 64 (8 * 5) : Addr).toNat = 0x300028 := by decide
  simp only [put6]
  rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64]
  all_goals first | (simp only [h0, h1, h2, h3, h4, h5]; omega) | omega

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => BitVec.ofNat 64 w.H.D | .a4 => 0x8000
    | .a5 => 0x300000 | _ => 0
  sp := 0x20000
  mem := put6 m₀ 0x300000 (symT vs w.hiN) (symT vs w.H.updN) (symT vs w.hfN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.G)) (BitVec.ofNat 64 w.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G))
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.H.D⟩, ⟨0x300000, 48⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 64 (satT vs w m₀ Q Tr).mem 0x300000 (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) :=
  put6_held (ws := [symT vs w.hiN, symT vs w.H.updN, symT vs w.hfN,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]) rfl

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem constRegions_symT (vs : List HVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => symT vs name) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]

theorem hD_le (w : HVar) : w.H.D ≤ 64 := by
  show w.t.H.D ≤ 64
  have := w.t.l.lens_mem
  simp only [Impl.RsaOaep.RISCV64.lens, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD := hD_le w
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  have hG : Spec.HmacTable.hashAt 64 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem 0x300000 =
      some w.G := hashAt_tableOf (held_tableOf (satT_held vs w m₀ _ _)).2.1
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
       exact ⟨w.t.l.len.symm, by rw [w.hmac]; rfl⟩)
    | (intro i hi
       show (put6 m₀ _ _ _ _ _ _ _).readW (symT vs n + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, put6_below (by bv_omega)]
       exact hheld i hi)
    | (show (1048576 : BitVec 64).toNat % 64 = 0; decide)
    | (refine ⟨show (1048576 : BitVec 64).toNat + 8 * W.length ≤ 2 ^ 64 by bv_omega, ?_, ?_, ?_⟩ <;>
       exact Region.disjoint_of_sep (by
         simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    RISCV64.abi, RISCV64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD := hD_le w
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HmacTable.hashAt 64 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem 0x300000 =
      some w.G := hashAt_tableOf (held_tableOf (satT_held vs w _ _ _)).2.1
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
       exact ⟨w.t.l.len.symm, by rw [w.hmac]; rfl⟩)

end VG.Proof.Ecdsa.Rfc6979.RISCV64
