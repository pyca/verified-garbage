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
at fixed addresses, the stack arguments at `0x9000`, the table of a hash
function `w` of `vs` at `0x300000`, the functions of `vs` at distinct
addresses (`HashTable.symsOf32`), and the curve's table of constants, if
any, at `0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm
open VG.Proof.HmacTable.Arm (HVar vars sha256V tables names tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)

/-- A word read apart from a word written. -/
theorem readW_sepW {m : Mem} {a b : Addr} {w : Nat} {v : BitVec 32} (h : a.toNat + w / 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (ha : a.toNat + w / 8 ≤ 2 ^ 64) (hb : b.toNat + 4 ≤ 2 ^ 64) (hw : w / 8 < 2 ^ 64) :
    (m.writeW b v).readW a w = m.readW a w :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) hw

/-- Six words at `p`. -/
def put6w (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) w₀).writeW (p + BitVec.ofNat 64 (4 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (4 * 2)) w₂).writeW (p + BitVec.ofNat 64 (4 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (4 * 4)) w₄).writeW (p + BitVec.ofNat 64 (4 * 5)) w₅

/-- The table `put6w` writes at `0x300000`, of the low halves of `ws`. -/
theorem put6w_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 6) :
    Abi.tableHeld 32 (put6w m 0x300000 ((ws.getD 0 0).setWidth 32) ((ws.getD 1 0).setWidth 32)
      ((ws.getD 2 0).setWidth 32) ((ws.getD 3 0).setWidth 32) ((ws.getD 4 0).setWidth 32)
      ((ws.getD 5 0).setWidth 32)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put6w, Nat.reduceDiv]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32,
      Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Proof.HashTable.readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Mem.readW_writeW_self32]

/-- Below `0x300000`, `put6w` at `0x300000` changes no word. -/
theorem put6w_below {m : Mem} {a : Addr} {w : Nat} (hw : w / 8 ≤ 8) (ha : a.toNat + w / 8 ≤ 0x300000)
    (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : (put6w m 0x300000 w₀ w₁ w₂ w₃ w₄ w₅).readW a w = m.readW a w := by
  have h0 : (0x300000 + BitVec.ofNat 64 (4 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (4 * 1) : Addr).toNat = 0x300004 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (4 * 2) : Addr).toNat = 0x300008 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (4 * 3) : Addr).toNat = 0x30000C := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (4 * 4) : Addr).toNat = 0x300010 := by decide
  have h5 : (0x300000 + BitVec.ofNat 64 (4 * 5) : Addr).toNat = 0x300014 := by decide
  simp only [put6w]
  rw [readW_sepW, readW_sepW, readW_sepW, readW_sepW, readW_sepW, readW_sepW]
  all_goals first | (simp only [h0, h1, h2, h3, h4, h5]; omega) | omega

/-- The stack arguments, at `0x9000`. -/
def put2w (m : Mem) (w₀ w₁ : BitVec 32) : Mem := (m.writeW 0x9000 w₀).writeW 0x9004 w₁

/-- Above the stack arguments, `put2w` changes no word. -/
theorem put2w_above {m : Mem} {a : Addr} {w : Nat} (hw : w / 8 ≤ 8) (ha : 0x9008 ≤ a.toNat)
    (ha' : a.toNat + w / 8 ≤ 2 ^ 64) (w₀ w₁ : BitVec 32) : (put2w m w₀ w₁).readW a w = m.readW a w := by
  have e₀ : (0x9000 : Addr).toNat = 0x9000 := by decide
  have e₄ : (0x9004 : Addr).toNat = 0x9004 := by decide
  simp only [put2w]
  rw [readW_sepW (.inr (by rw [e₄]; omega)) ha' (by decide) (by omega),
    readW_sepW (.inr (by rw [e₀]; omega)) ha' (by decide) (by omega)]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : BitVec 32 :=
  if n ∈ names vs then symsOf32 (names vs) n else 0x100000

/-- The words of `w`'s table. -/
def tw6 (vs : List HVar) (w : HVar) : List (BitVec 64) :=
  [(symT vs w.F.hiN).setWidth 64, (symT vs w.F.H.updN).setWidth 64, (symT vs w.F.hfN).setWidth 64,
    BitVec.ofNat 64 (Spec.HashTable.index w.G), BitVec.ofNat 64 w.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)]

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => BitVec.ofNat 32 w.F.H.D | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := put6w (put2w m₀ 0x10000 0x300000) 0x300000 (((tw6 vs w).getD 0 0).setWidth 32)
    (((tw6 vs w).getD 1 0).setWidth 32) (((tw6 vs w).getD 2 0).setWidth 32) (((tw6 vs w).getD 3 0).setWidth 32)
    (((tw6 vs w).getD 4 0).setWidth 32) (((tw6 vs w).getD 5 0).setWidth 32)
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩, ⟨0x9000, 8⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x10000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w m₀ Q Tr).mem (State.addr (0x300000 : BitVec 32))
      (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) := by
  rw [show State.addr (0x300000 : BitVec 32) = 0x300000 by decide]
  exact put6w_held (ws := tw6 vs w) rfl

theorem satT_arg0 (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 0 = 0x10000 := by
  show (put6w _ _ _ _ _ _ _ _).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 0))) 32 = _
  rw [put6w_below (by decide) (by decide)]
  simp only [put2w]
  rw [readW_sepW (.inl (by decide)) (by decide) (by decide) (by decide)]
  exact Mem.readW_writeW_self32 _ _ _

theorem satT_arg1 (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    stackArg (satT vs w m₀ Q Tr) 1 = 0x300000 := by
  show (put6w _ _ _ _ _ _ _ _).readW (State.addr (0x9000 + BitVec.ofNat 32 (4 * 1))) 32 = _
  rw [put6w_below (by decide) (by decide)]
  simp only [put2w]
  exact Mem.readW_writeW_self32 _ _ _

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem constRegions_symT (vs : List HVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]; rfl

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} {w : HVar} (hv : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) (hD : w.F.H.D ≤ 64)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  have a0 := satT_arg0 vs w (fun _ => 0) T.ecdsa.curve.len []
  have a1 := satT_arg1 vs w (fun _ => 0) T.ecdsa.curve.len []
  have hG : Spec.HmacTable.hashAt 32 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem
      (State.addr (0x300000 : BitVec 32)) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hsp : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).sp = 0x9000 := rfl
  have hsy : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).syms = symT vs := rfl
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0, a0, a1, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [hDn, a0, a1, hsw, hA]
  sig_and_intros
  all_goals try rw [hsp]
  all_goals try rw [hA]
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hl)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [w.hmac]; rfl⟩)

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} {w : HVar} (hv : w ∈ vs)
    (hl : (names vs).length < 2 ^ 24) (hD : w.F.H.D ≤ 64) {n : String} {W : List (BitVec 64)} (m₀ : Mem)
    (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have a0 := satT_arg0 vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have a1 := satT_arg1 vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have hG : Spec.HmacTable.hashAt 32 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      (State.addr (0x300000 : BitVec 32)) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hsp : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).sp = 0x9000 := rfl
  have hsy : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).syms = symT vs := rfl
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, stackBelow, stackT, String.reduceEq,
    Option.map_some, List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, hsw, tableRegion_eq, names_eq, argAddr0, a0, a1, hsp, hsy]
  have hA : State.addr (0x9000 : BitVec 32) = 0x9000 := by decide
  simp only [hDn, a0, a1, hsw, hA]
  sig_and_intros
  all_goals try rw [hsp]
  all_goals try rw [hA]
  all_goals try (intro c hc; simp only [List.mem_singleton] at hc; subst hc)
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, satT_held vs w _ _ _⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hl)
    | exact (constRegions_symT vs n W hna).symm
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [w.hmac]; rfl⟩)
    | (intro i hi
       show (put6w _ _ _ _ _ _ _ _).readW ((symT vs n).setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, put6w_below (by decide) (by bv_omega), put2w_above (by decide) (by bv_omega) (by bv_omega)]
       exact hheld i hi)
    | (refine ⟨show (1048576 : BitVec 64).toNat + 8 * W.length ≤ 2 ^ 32 by bv_omega, ?_, ?_, ?_⟩ <;>
       exact Region.disjoint_of_sep (by
         simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

theorem names_len : (names vars).length < 2 ^ 24 := by decide

theorem sha256V_mem : sha256V ∈ vars := .tail _ (.tail _ (.tail _ (.head _)))

/-- `vg_ecdsa_<curve>_sign` with the tables of every hash function with HMAC
on ARMv7, for a curve without tables of constants. -/
theorem nilT_verified {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T)
    (hsw : T.scratchWords = 1024) (hQ : T.ecdsa.curve.len ≤ 66) (hcs : R.coreConsts = []) :
    Verified Arm.target (signCodeT R T.tries vars) (specK T R.coreConsts vars) :=
  signT_verified hC hsw vars_ok (by rw [hcs]; exact sat_nil sha256V_mem names_len (by decide) hQ hsw)

/-- The same, for a curve with one table of constants `W`, `m₀` holding it
at `0x100000`. -/
theorem oneT_verified {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T)
    (hsw : T.scratchWords = 1024) (hQ : T.ecdsa.curve.len ≤ 66) {n : String} {W : List (BitVec 64)}
    (hcs : R.coreConsts = [(n, W)]) (m₀ : Mem) (hna : n ∉ names vars) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0) :
    Verified Arm.target (signCodeT R T.tries vars) (specK T R.coreConsts vars) :=
  signT_verified hC hsw vars_ok (by
    rw [hcs]; exact sat_one sha256V_mem names_len (by decide) m₀ hna hW hheld hQ hsw)

end VG.Proof.Ecdsa.Rfc6979.Arm
