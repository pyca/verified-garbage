module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the table is satisfiable

A state meeting `TableInstance.signContract` with the tables of `vs`
(`satT`): `esp = 0x20000` and our arguments above it (`out = 0x1000`,
`d = 0x2000`, `digest = 0x3000`, its length, `scratch = 0x8000` and
`hash = 0x300000`), the table of a variant `w` of `vs` at `0x300000`, the
functions of `vs` at distinct addresses (`HashTable.symsOf32`), and the
curve's table of constants `W`, if any, at `0x100000` (`sat_nil`,
`sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86
open VG.Impl.Ecdsa.Rfc6979.X86 (shapeOf)
open VG.Proof.HashTable.X86 (TVar tables names tableOf held_tableOf hashAt_tableOf mem_names)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct put5w put5w_held put5w_below)

/-- Our arguments at `0x20004`: `0x1000, 0x2000, 0x3000, D, 0x8000, 0x300000`. -/
def argMemT (D : Nat) : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20010 then BitVec.ofNat 8 D else if a = 0x20015 then 0x80 else if a = 0x2001a then 0x30 else 0

/-- The state with only the arguments. -/
def argStateT (D : Nat) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := argMemT D
  rd := []
  wr := []

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List TVar) (n : String) : BitVec 32 := if n ∈ names vs then symsOf32 (names vs) n else 0x100000

/-- The words of `w`'s table. -/
def twT (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  [(symT vs w.g.H.initN).setWidth 64, (symT vs w.g.H.updN).setWidth 64, (symT vs w.g.H.finN).setWidth 64,
    BitVec.ofNat 64 (Spec.HashTable.index w.g.G), BitVec.ofNat 64 w.g.G.len]

/-- The memory: the constants `W` at `0x100000`, the arguments, and `w`'s table at `0x300000`. -/
def satMemT (vs : List TVar) (w : TVar) (W : List (BitVec 64)) : Mem :=
  put5w (fun a => if (a - 0x100000).toNat < 8 * W.length then constMem 0x100000 W a else argMemT w.g.H.D a)
    0x300000 (((twT vs w).getD 0 0).setWidth 32) (((twT vs w).getD 1 0).setWidth 32)
    (((twT vs w).getD 2 0).setWidth 32) (((twT vs w).getD 3 0).setWidth 32) (((twT vs w).getD 4 0).setWidth 32)

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the constants `W` (their regions `Tr`). -/
def satT (vs : List TVar) (w : TVar) (W : List (BitVec 64)) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemT vs w W
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.g.H.D⟩, ⟨0x300000, 20⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩]
  syms := symT vs

theorem satT_arg (vs : List TVar) (w : TVar) {W : List (BitVec 64)} (hW : 8 * W.length ≤ 0x100000) (Q : Nat)
    (Tr : List Region) (j : Nat) (hj : j < 6) : arg (satT vs w W Q Tr) j = arg (argStateT w.g.H.D) j := by
  have outside : ∀ j < 6, ∀ b < 4,
      0x100000 ≤ (argAddr (argStateT 0) j + BitVec.ofNat 64 b - 0x100000).toNat := by decide
  have below : ∀ j < 6, (argAddr (argStateT 0) j).toNat + 4 ≤ 0x300000 := by decide
  unfold arg
  rw [show argAddr (satT vs w W Q Tr) j = argAddr (argStateT 0) j from rfl,
    show argAddr (argStateT w.g.H.D) j = argAddr (argStateT 0) j from rfl]
  show (put5w _ _ _ _ _ _ _).readW _ 32 = _
  rw [put5w_below (below j hj)]
  apply Mem.readW_congr
  intro b hb
  show (if _ then _ else _) = argMemT w.g.H.D _
  exact ite_eq_right (by have := outside j hj b (by omega); omega)

theorem argT_vals : ∀ D ∈ [16, 20, 28, 32, 48, 64],
    arg (argStateT D) 0 = 0x1000 ∧ arg (argStateT D) 1 = 0x2000 ∧ arg (argStateT D) 2 = 0x3000 ∧
      arg (argStateT D) 3 = BitVec.ofNat 32 D ∧ arg (argStateT D) 4 = 0x8000 ∧ arg (argStateT D) 5 = 0x300000 := by
  decide

theorem satT_held (vs : List TVar) {w : TVar} (hv : w ∈ vs) (W : List (BitVec 64)) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w W Q Tr).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (satT vs w W Q Tr) (tableOf w)) := by
  have hn := mem_names hv
  rw [show ((0x300000 : BitVec 32).setWidth 64) = 0x300000 by decide,
    show FnTable.words isa (satT vs w W Q Tr) (tableOf w) = twT vs w from rfl]
  exact put5w_held (ws := twT vs w) rfl

theorem symT_distinct {vs : List TVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem sep_lt {a b : Addr} {n k : Nat} (h : a.toNat + n ≤ b.toNat) (hb : b.toNat + k ≤ 2 ^ 64) :
    Mem.Sep a n b k := by
  intro x hx hx'
  bv_omega

theorem satT_word (vs : List TVar) (w : TVar) {W : List (BitVec 64)} (hW : 8 * W.length ≤ 0x100000) (Q : Nat)
    (Tr : List Region) : ∀ i < W.length,
      (satT vs w W Q Tr).mem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  intro i hi
  have hb : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i)).toNat = 0x100000 + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x100000 : Addr).toNat = 0x100000 by decide]; omega
  have ht : ∀ k < 5, ((0x300000 : Addr) + BitVec.ofNat 64 (4 * k)).toNat = 0x300000 + 4 * k := fun k hk => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (0x300000 : Addr).toNat = 0x300000 by decide]; omega
  have sep : ∀ k < 5, Mem.Sep (0x100000 + BitVec.ofNat 64 (8 * i)) (64 / 8)
      (0x300000 + BitVec.ofNat 64 (4 * k)) (32 / 8) := fun k hk =>
    sep_lt (by rw [hb, ht k hk]; omega) (by rw [ht k hk]; omega)
  simp only [satT, satMemT, put5w]
  rw [Mem.readW_writeW_sep (sep 4 (by decide)) (by decide), Mem.readW_writeW_sep (sep 3 (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 2 (by decide)) (by decide), Mem.readW_writeW_sep (sep 1 (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 0 (by decide)) (by decide)]
  rw [Mem.readW_congr (m' := constMem 0x100000 W) fun j hj => ?_]
  · exact constMem_held 0x100000 W (by omega) i hi
  · have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show (if _ then _ else _) = _
    rw [e]; exact ite_eq_left (show 8 * i + j < 8 * W.length by omega)

theorem shape_D : ∀ i < 8, (shapeOf i).1 ∈ [16, 20, 28, 32, 48, 64] := by decide

theorem wD {w : TVar} (hw : WOk w) : w.g.H.D ∈ [16, 20, 28, 32, 48, 64] := by
  rw [show w.g.H.D = (shapeOf (Spec.HashTable.index w.g.G)).1 by rw [hw.2.2]]
  exact shape_D _ hw.2.1

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  have hW : 8 * ([] : List (BitVec 64)).length ≤ 0x100000 := by decide
  have hDl := wD hw
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := argT_vals _ hDl
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 0 (by decide)] at a0
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 1 (by decide)] at a1
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 2 (by decide)] at a2
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 3 (by decide)] at a3
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 4 (by decide)] at a4
  rw [← satT_arg vs w hW T.ecdsa.curve.len [] 5 (by decide)] at a5
  have hD : w.g.H.D ≤ 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hDl; omega
  have hDn : (BitVec.ofNat 32 w.g.H.D).toNat = w.g.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HashTable.hashAt 32 (satT vs w [] T.ecdsa.curve.len []).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.g.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs hv _ _ _)).2.1
  refine ⟨satT vs w [] T.ecdsa.curve.len [], ?_⟩
  have e : argAddr (satT vs w [] T.ecdsa.curve.len []) 0 = 0x20004 := rfl
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil]
  simp only [a0, a1, a2, a3, a4, a5, e, hsw, hDn, tableRegion_eq, List.append_eq, List.append_nil, names_eq]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs hv _ _ _⟩
    | exact symT_distinct hO.2.1
    | exact Region.disjoint_of_sep (by decide)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | omega
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.g.glen.symm, by rw [hw.hmac]; rfl⟩)

theorem constRegions_symT (vs : List TVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]
  rfl

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (hna : n ∉ names vs) (hW8 : 8 * W.length ≤ 0x100000)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  have hW : 8 * W.length ≤ 0x100000 := hW8
  have hDl := wD hw
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := argT_vals _ hDl
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 0 (by decide)] at a0
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 1 (by decide)] at a1
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 2 (by decide)] at a2
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 3 (by decide)] at a3
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 4 (by decide)] at a4
  rw [← satT_arg vs w hW T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] 5 (by decide)] at a5
  have hD : w.g.H.D ≤ 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hDl; omega
  have hDn : (BitVec.ofNat 32 w.g.H.D).toNat = w.g.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HashTable.hashAt 32 (satT vs w W T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.g.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs hv _ _ _)).2.1
  refine ⟨satT vs w W T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have e : argAddr (satT vs w W T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]) 0 = 0x20004 := rfl
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil]
  simp only [a0, a1, a2, a3, a4, a5, e, hsw, hDn, tableRegion_eq, List.append_eq, List.append_nil, names_eq]
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  sig_and_intros
  all_goals try (intro c hc; simp only [List.mem_singleton] at hc; subst hc)
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | exact (constRegions_symT vs n W hna).symm
    | (refine ⟨by dsimp only; bv_omega, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))
    | (intro i hi
       show (satT vs w W T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem.readW
         ((symT vs n).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, show (0x100000 : BitVec 32).setWidth 64 = 0x100000 by decide]
       exact satT_word vs w hW _ _ i hi)
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs hv _ _ _⟩
    | exact symT_distinct hO.2.1
    | exact Region.disjoint_of_sep (by decide)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | omega
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.g.glen.symm, by rw [hw.hmac]; rfl⟩)

end VG.Proof.Ecdsa.Rfc6979.X86
