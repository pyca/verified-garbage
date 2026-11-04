module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSpec
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSpec
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on 32-bit ARM: the contract with the table is satisfiable

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`): a state meeting
`TableInstance.signContract` with the tables of `vs` (`satT`): the buffers
at fixed addresses, the stack arguments (`scratch` and the table) at the
stack pointer, the table of a variant `w` of `vs` at `0x300000`, the
functions of `vs` at distinct addresses (`HashTable.symsOf32`), and the
curve's table of constants, if any, at `0x100000`, where the memory `m₀`
holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables names tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct put5w put5w_held put5w_below)

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List TVar) (n : String) : BitVec 32 := if n ∈ names vs then symsOf32 (names vs) n else 0x100000

/-- The stack arguments at `0x20000`: `scratch` at `0x30000` and the table at `0x300000`. -/
def argsMem (m : Mem) : Mem := (m.writeW 0x20000 (0x30000 : BitVec 32)).writeW 0x20004 (0x300000 : BitVec 32)

/-- The words of `w`'s table, at the addresses `symT` gives `vs`' functions. -/
def twT (vs : List TVar) (w : TVar) : List (BitVec 64) :=
  [(symT vs w.g.H.initN).setWidth 64, (symT vs w.g.H.updN).setWidth 64, (symT vs w.g.H.finN).setWidth 64,
    BitVec.ofNat 64 (Spec.HashTable.index w.g.G), BitVec.ofNat 64 w.g.G.len]

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | .r3 => BitVec.ofNat 32 w.g.H.D | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem := put5w (argsMem m₀) 0x300000 (((twT vs w).getD 0 0).setWidth 32) (((twT vs w).getD 1 0).setWidth 32)
    (((twT vs w).getD 2 0).setWidth 32) (((twT vs w).getD 3 0).setWidth 32) (((twT vs w).getD 4 0).setWidth 32)
  rd := [⟨0x12000, Q⟩, ⟨0x14000, w.g.H.D⟩, ⟨0x300000, 20⟩, ⟨0x20000, 8⟩] ++ Tr
  wr := [⟨0x10000, 2 * Q⟩, ⟨0x30000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w m₀ Q Tr).mem (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) := by
  rw [show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  exact put5w_held (ws := twT vs w) rfl

theorem symT_distinct {vs : List TVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

/-- Regions at literal addresses, one below the other. -/
theorem sep_lit {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2 ^ 64) (hb : b + k ≤ 2 ^ 64)
    (ha' : a < 2 ^ 64) (hb' : b < 2 ^ 64) :
    Region.Disjoint ⟨BitVec.ofNat 64 a, n⟩ ⟨BitVec.ofNat 64 b, k⟩ :=
  Region.disjoint_of_sep (by
    simp only [Region.sep, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']
    omega)

theorem args_frame (m : Mem) : Frame [⟨0x20000, 8⟩] m (argsMem m) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by decide)).writeW (List.mem_singleton_self _) _
    (by decide)

theorem put5w_frame (m : Mem) (w₀ w₁ w₂ w₃ w₄ : BitVec 32) :
    Frame [⟨0x300000, 20⟩] m (put5w m 0x300000 w₀ w₁ w₂ w₃ w₄) := by
  unfold put5w
  refine ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
    (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_) <;>
    decide

theorem satT_arg0 (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 0 = 0x30000 := by
  show (put5w (argsMem m₀) 0x300000 _ _ _ _ _).readW (State.addr ((0x20000 : BitVec 32) + BitVec.ofNat 32 (4 * 0))) 32 = _
  rw [put5w_below (by decide)]
  unfold argsMem
  rw [Frame.readW (rs := [⟨0x20004, 4⟩]) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by decide))
    (r := ⟨0x20000, 4⟩) (by decide) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.disjoint_of_sep (by decide)) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem satT_aa (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArgAddr (satT vs w m₀ Q Tr) 0 = 0x20000 := rfl

theorem stkA : State.addr (131072 : BitVec 32) - BitVec.ofNat 64 512 = 130560 := by decide

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 5 = ⟨p, 20⟩ := rfl

theorem satT_arg1 (vs : List TVar) (w : TVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 1 = 0x300000 := by
  show (put5w (argsMem m₀) 0x300000 _ _ _ _ _).readW (State.addr ((0x20000 : BitVec 32) + BitVec.ofNat 32 (4 * 1))) 32 = _
  rw [put5w_below (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

/-- The digest's length and HMAC, for the hash function the table names. -/
theorem hash_goal {w : TVar} (hw : WOk w) {m : Mem} {a : Addr} (hG : Spec.HashTable.hashAt 32 m a = some w.g.G) :
    ∀ H, Spec.HashTable.hashAt 32 m a = some H → w.g.H.D = H.len ∧ (Spec.Ecdsa.Rfc6979.hmacOf H).isSome = true := by
  intro H hH
  obtain rfl := Option.some.inj (hG.symm.trans hH)
  exact ⟨w.g.glen.symm, by rw [hw.hmac]; rfl⟩

/-- The precondition's facts but for the tables of constants, which hold for `satT`. -/
macro "sat_close" vs:term:max w:term:max hv:term:max hO:term:max hG:term:max hw:term:max : tactic => `(tactic| (
  first
    | rfl
    | decide
    | exact ⟨tableOf $w, List.mem_map_of_mem $hv, satT_held _ _ _ _ _⟩
    | (rw [names_eq]; exact symT_distinct (vs := $vs) ($hO).2.1)
    | (apply Region.disjoint_of_sep
       simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
       bv_omega)
    | bv_omega
    | exact hash_goal $hw $hG))

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  have hD : w.g.H.D ≤ 64 := by have := w.g.ok.hDF; have := w.g.ok.hF; omega
  have hG : Spec.HashTable.hashAt 32 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem
      (State.addr (0x300000 : BitVec 32)) = some w.g.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.g.H.D).toNat = w.g.H.D := by rw [BitVec.toNat_ofNat]; omega
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, satT_arg0, satT_arg1, satT_aa, tableRegion_eq]
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT]
  simp only [satT, hDn, stkA] at hG ⊢
  sig_and_intros
  all_goals sat_close vs w hv hO hG hw

theorem constRegions_symT (vs : List TVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]; rfl

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have hD : w.g.H.D ≤ 64 := by have := w.g.ok.hDF; have := w.g.ok.hF; omega
  have hG : Spec.HashTable.hashAt 32 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      (State.addr (0x300000 : BitVec 32)) = some w.g.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.g.H.D).toNat = w.g.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  have hm : ∀ i < W.length, (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem.readW
      ((symT vs n).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := fun i hi => by
    have hb : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i := by bv_omega
    rw [hsym, show (0x100000 : BitVec 32).setWidth 64 = 0x100000 from rfl]
    show (put5w (argsMem m₀) 0x300000 _ _ _ _ _).readW _ 64 = _
    rw [(put5w_frame _ _ _ _ _ _).readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.disjoint_of_sep (by
          simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)) (by decide),
      (args_frame m₀).readW (r := ⟨0x100000 + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Region.disjoint_of_sep (by
          simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))
        (by decide)]
    exact hheld i hi
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, satT_arg0, satT_arg1, satT_aa, tableRegion_eq]
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val, Abi.withConsts, stackT]
  rw [constRegions_symT vs n W hna]
  simp only [satT, hDn, stkA] at hG hm ⊢
  sig_and_intros
  all_goals try (intro c hc; rw [List.mem_singleton] at hc; subst hc)
  all_goals try (intro t ht; rw [List.mem_singleton] at ht; subst ht)
  all_goals first
    | exact hm
    | sat_close vs w hv hO hG hw
    | (refine ⟨by show 1048576 + 8 * W.length ≤ 2 ^ 32; omega, ?_, ?_, ?_⟩ <;>
       (apply Region.disjoint_of_sep
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        bv_omega))

end VG.Proof.Ecdsa.Rfc6979.Arm
