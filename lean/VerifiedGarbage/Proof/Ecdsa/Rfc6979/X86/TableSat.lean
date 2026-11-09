module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.TableSpec
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the table is satisfiable

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`): a state meeting
`TableInstance.signContract` with the tables of `vs` (`satT`): the buffers
at fixed addresses, our arguments on the stack at `0x20004`, the table of a
variant `w` of `vs` at `0x300000`, the functions of `vs` at distinct
addresses (`HashTable.symsOf32`), and the curve's table of constants, if
any, at `0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86
open VG.Proof.HmacTable.X86 (HVar tables names tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)

/-- Six 32-bit words at `p`. -/
def put6w (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) w₀).writeW (p + BitVec.ofNat 64 (4 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (4 * 2)) w₂).writeW (p + BitVec.ofNat 64 (4 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (4 * 4)) w₄).writeW (p + BitVec.ofNat 64 (4 * 5)) w₅

/-- A word apart from a 32-bit write. -/
theorem readW_sepw {m : Mem} {a b : Addr} {w : Nat} {v : BitVec 32} (hw : w / 8 < 2 ^ 64)
    (h : a.toNat + w / 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) (ha : a.toNat + w / 8 ≤ 2 ^ 64)
    (hb : b.toNat + 4 ≤ 2 ^ 64) : (m.writeW b v).readW a w = m.readW a w :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) hw

theorem toNat_add_lit {p : Addr} {k : Nat} (h : p.toNat + k < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-- The words `put6w` writes. -/
theorem put6w_read {m : Mem} {p : Addr} (hp : p.toNat + 24 ≤ 2 ^ 64) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) :
    ∀ i < 6, (put6w m p w₀ w₁ w₂ w₃ w₄ w₅).readW (p + BitVec.ofNat 64 (4 * i)) 32 = [w₀, w₁, w₂, w₃, w₄, w₅].getD i 0 := by
  intro i hi
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk => toNat_add_lit (by omega)
  have s : ∀ i j, i < 6 → j < 6 → i ≠ j → ∀ v : BitVec 32, ∀ m : Mem,
      (m.writeW (p + BitVec.ofNat 64 (4 * j)) v).readW (p + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := fun i j hi hj hij v m => by
    refine readW_sepw (by decide) ?_ ?_ ?_ <;> simp only [Nat.reduceDiv, t (4 * i) (by omega), t (4 * j) (by omega)] <;>
      omega
  simp only [put6w]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s 0 5 (by decide) (by decide) (by decide), s 0 4 (by decide) (by decide) (by decide),
      s 0 3 (by decide) (by decide) (by decide), s 0 2 (by decide) (by decide) (by decide),
      s 0 1 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [s 1 5 (by decide) (by decide) (by decide), s 1 4 (by decide) (by decide) (by decide),
      s 1 3 (by decide) (by decide) (by decide), s 1 2 (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]; rfl
  · rw [s 2 5 (by decide) (by decide) (by decide), s 2 4 (by decide) (by decide) (by decide),
      s 2 3 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [s 3 5 (by decide) (by decide) (by decide), s 3 4 (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]; rfl
  · rw [s 4 5 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [Mem.readW_writeW_self32]; rfl

/-- What `put6w` keeps apart from its words. -/
theorem put6w_out {m : Mem} {p a : Addr} {w : Nat} (hw : w / 8 < 2 ^ 64) (hp : p.toNat + 24 ≤ 2 ^ 64)
    (ha : a.toNat + w / 8 ≤ p.toNat ∨ p.toNat + 24 ≤ a.toNat) (ha' : a.toNat + w / 8 ≤ 2 ^ 64)
    (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : (put6w m p w₀ w₁ w₂ w₃ w₄ w₅).readW a w = m.readW a w := by
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk => toNat_add_lit (by omega)
  simp only [put6w]
  rw [readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw]
  all_goals first | (simp only [t 0 (by omega), t 4 (by omega), t 8 (by omega), t 12 (by omega), t 16 (by omega),
    t 20 (by omega), show 4 * 0 = 0 from rfl, show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl, show 4 * 4 = 16 from rfl, show 4 * 5 = 20 from rfl]; omega) | omega

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : BitVec 32 :=
  if n ∈ names vs then symsOf32 (names vs) n else 0x100000

/-- The arguments' words. -/
def argsMem (m₀ : Mem) (D : Nat) : Mem := put6w m₀ 0x20004 0x1000 0x2000 0x3000 (BitVec.ofNat 32 D) 0x8000 0x300000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := put6w (argsMem m₀ w.F.H.D) 0x300000 (((symT vs w.F.hiN).setWidth 64).setWidth 32)
    (((symT vs w.F.H.updN).setWidth 64).setWidth 32) (((symT vs w.F.hfN).setWidth 64).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HashTable.index w.G)).setWidth 32) ((BitVec.ofNat 64 w.G.len).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)).setWidth 32)
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w m₀ Q Tr).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) := by
  intro i hi
  have hl : (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)).length = 6 := rfl
  rw [hl] at hi
  exact put6w_read (p := 0x300000) (by decide) _ _ _ _ _ _ i hi |>.trans (by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem satT_arg (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    ∀ i < 6, arg (satT vs w m₀ Q Tr) i = [0x1000, 0x2000, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x8000, 0x300000].getD i 0 := by
  intro i hi
  have ha : argAddr (satT vs w m₀ Q Tr) i = 0x20004 + BitVec.ofNat 64 (4 * i) := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  show (satT vs w m₀ Q Tr).mem.readW (argAddr (satT vs w m₀ Q Tr) i) 32 = _
  have h4 : (0x20004 : Addr).toNat = 0x20004 := rfl
  rw [ha]
  simp only [satT]
  rw [put6w_out (by decide) (by decide) (by
    rw [toNat_add_lit (by omega)]
    show 0x20004 + 4 * i + 32 / 8 ≤ 0x300000 ∨ _; omega) (by rw [toNat_add_lit (by omega)]; omega)]
  exact put6w_read (p := 0x20004) (by decide) _ _ _ _ _ _ i hi

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem constRegions_symT (vs : List HVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]; rfl

/-- What the contract asks of the state, but for its tables of constants. -/
macro "sat_close" : tactic => `(tactic| first
  | decide
  | rfl
  | exact Region.disjoint_of_sep (by
      simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
  | bv_omega)

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  have hD : w.F.H.D ≤ 64 := by
    have := hw.2.1; simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h | h <;> rw [Prod.mk.injEq] at h <;> omega
  have a := satT_arg vs w (fun _ => 0) T.ecdsa.curve.len []
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5
  have e : argAddr (satT vs w (fun _ => 0) T.ecdsa.curve.len []) 0 = 0x20004 := rfl
  have hG : Spec.HmacTable.hashAt 32 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hheld := satT_held vs w (fun _ => 0) T.ecdsa.curve.len []
  have hrd : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).rd =
      [⟨0x2000, T.ecdsa.curve.len⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] := rfl
  have hwr : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).wr =
      [⟨0x1000, 2 * T.ecdsa.curve.len⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩] := rfl
  have hesp : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).gpr .esp = 0x20000 := rfl
  have hsy : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).syms = symT vs := rfl
  generalize satT vs w (fun _ => 0) T.ecdsa.curve.len [] = s at a0 a1 a2 a3 a4 a5 e hG hheld hrd hwr hesp hsy ⊢
  spec_pre_goal
  simp only [a0, a1, a2, a3, a4, a5, e, hrd, hwr, hesp, hsy, hsw] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), w.glen], by rw [hw.hmac]; rfl⟩)
    | (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl)

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hm : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have hD : w.F.H.D ≤ 64 := by
    have := hw.2.1; simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h | h <;> rw [Prod.mk.injEq] at h <;> omega
  have a := satT_arg vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5
  have e : argAddr (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]) 0 = 0x20004 := rfl
  have hG : Spec.HmacTable.hashAt 32 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hheld := satT_held vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have hc : ∀ i < W.length, (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem.readW
      (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := fun i hi => by
    have l1 : (0x100000 : Addr).toNat = 0x100000 := rfl
    have l2 : (0x20004 : Addr).toNat = 0x20004 := rfl
    have l3 : (0x300000 : Addr).toNat = 0x300000 := rfl
    have h1 : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i :=
      toNat_add_lit (by rw [l1]; omega)
    simp only [satT, argsMem]
    rw [put6w_out (by decide) (by decide) (by rw [h1, l3]; simp only [Nat.reduceDiv]; omega) (by rw [h1]; omega),
      put6w_out (by decide) (by decide) (by rw [h1, l2]; simp only [Nat.reduceDiv]; omega) (by rw [h1]; omega)]
    exact hm i hi
  have hrd : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).rd =
      [⟨0x2000, T.ecdsa.curve.len⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] ++ [⟨0x100000, 8 * W.length⟩] := rfl
  have hwr : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).wr =
      [⟨0x1000, 2 * T.ecdsa.curve.len⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩] := rfl
  have hesp : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).gpr .esp = 0x20000 := rfl
  have hsy : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).syms = symT vs := rfl
  have hsym : (symT vs n).setWidth 64 = 0x100000 := by simp only [symT, hna, ite_false]; rfl
  generalize satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] = s
    at a0 a1 a2 a3 a4 a5 e hG hheld hc hrd hwr hesp hsy ⊢
  spec_pre_goal
  simp only [a0, a1, a2, a3, a4, a5, e, hrd, hwr, hesp, hsy, hsw] at hG hheld ⊢
  sig_and_intros
  all_goals try (intro c hc'; simp only [List.mem_singleton] at hc'; subst hc')
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), w.glen], by rw [hw.hmac]; rfl⟩)
    | (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; rfl)
    | exact (constRegions_symT vs n W hna).symm
    | (intro i hi; dsimp only at hi ⊢; rw [hsym]; exact hc i hi)
    | (refine ⟨by bv_omega, ?_, ?_, ?_⟩ <;> first
        | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
           rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by
             simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))
        | exact Region.disjoint_of_sep (by
            simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

end VG.Proof.Ecdsa.Rfc6979.X86
