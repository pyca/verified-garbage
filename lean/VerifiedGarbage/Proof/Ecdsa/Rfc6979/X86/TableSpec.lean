module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the hash function as a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSpec.lean`):
`TableInstance.signContract`, with the tables of `vs` for `hmac`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hmac` points to is one of `vs`', whose words
give the contract the proof is written against (`preW_of`); its hash
function is the one the table names, so the results agree; and two runs
whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HmacTable.X86 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem ((arg s 5).setWidth 64) (FnTable.words isa s (tableOf w))

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 6 = ⟨p, 24⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The facts of the contract with the table of `w`. -/
theorem preW_of {w : HVar} (hv : w ∈ vs) (hc : Coh vs) (hw : WOk w) {s : State}
    (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (hrd : s.rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, w.F.H.D⟩,
      ⟨(arg s 5).setWidth 64, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hwr : s.wr = [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩,
      ⟨argAddr s 0, 24⟩])
    (od : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 2).setWidth 64, w.F.H.D⟩)
    (oc : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ot : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (dc : Region.Disjoint ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (gc : Region.Disjoint ⟨(arg s 2).setWidth 64, w.F.H.D⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ct : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (oa : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨argAddr s 0, 24⟩)
    (ca : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨argAddr s 0, 24⟩)
    (ta : Region.Disjoint ⟨(arg s 5).setWidth 64, 24⟩ ⟨argAddr s 0, 24⟩)
    (ro : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (rc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (rt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ko : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 2).setWidth 64, w.F.H.D⟩)
    (kc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (kt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (no : (arg s 0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (arg s 1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (arg s 2).toNat + w.F.H.D ≤ 2 ^ 32) (nc : (arg s 4).toNat + 8192 ≤ 2 ^ 32)
    (nt : (arg s 5).toNat + 24 ≤ 2 ^ 32)
    (ht : TblsOk R.E.combConsts s [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩,
      ⟨(s.gpr .esp).setWidth 64, 4⟩, ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩])
    (hheld : HeldW w s)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) :
    PreW R T vs w s := by
  have hh := held_tableOf nt hheld
  rw [hw.blockSize] at hh
  exact ⟨⟨e588, e28, hrd, hwr, od, og, oc, dc, gc, oa.symm, ca.symm, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, ht,
    nt, ot.symm, ct.symm, ta, rt.symm, kt.symm, tabOK_of hc hpw hv, hh.1, hh.2.2.1, hh.2.2.2⟩, hh.2.1⟩

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List HVar) :
    Contract isa :=
  T.signContract ((X86.abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]) stackT

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract the proof is written against. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

/-- Unfolds the contract's precondition at `h`. -/
macro "spec_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, Option.map_some, tableRegion_eq, names_eq] at $h:ident))

/-- The facts the precondition gives, whichever the tables of constants. -/
theorem facts_of (hsw : T.scratchWords = 1024) (hO : OK vs) {s : State} {w : HVar} (hv : w ∈ vs)
    (hheld : HeldW w s) (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 4 + 24 ≤ 2 ^ 32)
    (held : Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hfit : ∀ t ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts,
      t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧
        t.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hrd : s.rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
      ⟨(arg s 5).setWidth 64, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hwr : s.wr = [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩,
      ⟨argAddr s 0, 24⟩])
    (od : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
    (oc : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩
      ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (ot : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (oa : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨argAddr s 0, 24⟩)
    (dc : Region.Disjoint ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (gc : Region.Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (ct : Region.Disjoint ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ca : Region.Disjoint ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩ ⟨argAddr s 0, 24⟩)
    (ta : Region.Disjoint ⟨(arg s 5).setWidth 64, 24⟩ ⟨argAddr s 0, 24⟩)
    (ro : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (rc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (rt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ko : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
    (kc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (kt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (no : (arg s 0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (arg s 1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32) (nc : (arg s 4).toNat + T.scratchWords * 8 ≤ 2 ^ 32)
    (nt : (arg s 5).toNat + 24 ≤ 2 ^ 32)
    (hH : ∀ H, Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H →
      (arg s 3).toNat = H.len ∧ (Spec.HmacTable.hmacOf H).isSome = true) :
    PreW R T vs w s := by
  have hh := held_tableOf nt hheld
  have hlen : (arg s 3).toNat = w.F.H.D := (hH _ (hashAt_tableOf nt hh.2.1)).1.trans w.glen
  rw [hlen] at og gc kg ng hrd
  rw [hsw] at hwr oc dc gc rc kc nc ct ca
  refine preW_of hv hO.1 (hO.2.2.2 w hv) e588 (by omega) hrd hwr od og oc ot dc gc ct oa ca ta ro rc rt
    ko kd kg kc kt no nd ng nc nt ⟨held, fun t htm => ⟨(hfit t htm).1, fun r hr => ?_⟩⟩ hheld hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
  · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
  · exact (hfit t htm).2.2.1
  · exact (hfit t htm).2.2.2

/-- The precondition, with tables of constants. -/
theorem pre_cons (hsw : T.scratchWords = 1024) (hO : OK vs) {c : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))} (hcs : R.E.combConsts = c :: cs) {s : State}
    (h : (specK T (c :: cs) vs).pre s) : PreFacts R T vs s := by
  spec_pre at h
  obtain ⟨e588, e28, hdrop, held, hfit, -, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, oa, dc, -, gc, -,
    ct, ca, ta, ro, -, -, rc, rt, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  rw [List.append_eq, List.append_nil] at hpw
  refine facts_of (R := R) hsw hO hv hheld e588 e28 (by rw [hcs]; exact held) (by rw [hcs]; exact hfit) hpw ?_ hwr
    od og oc ot oa dc gc ct ca ta ro rc rt ko kd kg kc kt no nd ng nc nt hH
  rw [hcs, ← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]

/-- The precondition, without tables of constants. -/
theorem pre_nil (hsw : T.scratchWords = 1024) (hO : OK vs) (hcs : R.E.combConsts = []) {s : State}
    (h : (specK T [] vs).pre s) : PreFacts R T vs s := by
  spec_pre at h
  obtain ⟨e588, e28, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, oa, dc, -, gc, -,
    ct, ca, ta, ro, -, -, rc, rt, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  rw [List.append_eq, List.append_nil] at hpw
  refine facts_of (R := R) hsw hO hv hheld e588 e28 (by rw [hcs]; exact fun _ h => absurd h (by simp))
    (by rw [hcs]; exact fun _ h => absurd h (by simp [Abi.constRegions])) hpw (by rw [hcs, hrd]; rfl) hwr
    od og oc ot oa dc gc ct ca ta ro rc rt ko kd kg kc kt no nd ng nc nt hH

theorem PreW.nt {w : HVar} {s : State} (h : PreW R T vs w s) : (arg s 5).toNat + 24 ≤ 2 ^ 32 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nt, -⟩, -⟩ := h
  exact nt

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.nt hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    T.tried 32 s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64) ((arg s₁ 5).setWidth 64) =
      T.tried 32 s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64) ((arg s₂ 5).setWidth 64) ∧
    (∀ c ∈ R.E.combConsts, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : HVar} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 32 s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 5).setWidth 64) =
      ((instOf T w).result s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.nt hp.2, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hsp, ha, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hsp, ha, ?_, hc, hn⟩
  show ((instOf T w).result s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
    ((instOf T w).result s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- Unfolds the contract's public data at `h`. -/
macro "spec_pub" " at " h:ident : tactic => `(tactic| (
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, Option.map_some, tableRegion_eq, names_eq] at $h:ident))

theorem args_of {s₁ s₂ : State} (e₀ : arg s₁ 0 = arg s₂ 0) (e₁ : arg s₁ 1 = arg s₂ 1) (e₂ : arg s₁ 2 = arg s₂ 2)
    (e₃ : arg s₁ 3 = arg s₂ 3) (e₄ : arg s₁ 4 = arg s₂ 4) (e₅ : arg s₁ 5 = arg s₂ 5) :
    ∀ i < 6, arg s₁ i = arg s₂ i
  | 0, _ => e₀ | 1, _ => e₁ | 2, _ => e₂ | 3, _ => e₃ | 4, _ => e₄ | 5, _ => e₅

/-- The public data, with tables of constants. -/
theorem pub_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.E.combConsts = c :: cs) {s₁ s₂ : State}
    (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  spec_pub at h
  obtain ⟨hsp, hc₀, hcs', hn, hT, htr, e₀, e₁, e₂, e₃, e₄, e₅⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, args_of e₀ e₁ e₂ e₃ e₄ e₅,
    (List.cons.inj htr).1, fun c' hc' => ?_, hn⟩
  rw [hcs] at hc'
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc₀
  · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pub_nil (hcs : R.E.combConsts = []) {s₁ s₂ : State}
    (h : (specK T [] vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  spec_pub at h
  obtain ⟨hsp, hn, hT, htr, e₀, e₁, e₂, e₃, e₄, e₅⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  exact ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, args_of e₀ e₁ e₂ e₃ e₄ e₅,
    (List.cons.inj htr).1, fun c' hc' => absurd hc' (by rw [hcs]; simp), hn⟩

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) : (tabK R T vs).Implies (specK T R.E.combConsts vs) := by
  generalize hcs : R.E.combConsts = cs at hsat ⊢
  have facts : ∀ s, (specK T cs vs).pre s → PreFacts R T vs s := fun s h => by
    cases cs with
    | nil => exact pre_nil hsw hO hcs h
    | cons c cs => exact pre_cons hsw hO hcs h
  have pubs : ∀ s₁ s₂, (specK T cs vs).pub s₁ s₂ → PubFacts R T vs s₁ s₂ := fun s₁ s₂ h => by
    cases cs with
    | nil => exact pub_nil hcs h
    | cons c cs => exact pub_cons hcs h
  refine ⟨fun s h => (facts s h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hO (facts _ h₁) (facts _ h₂) (pubs _ _ hp), hsat⟩
  have hk := (facts s h).pre hO
  cases cs
  all_goals
    sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) :
    Verified X86.target (signCodeT R T.tries vs) (specK T R.E.combConsts vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.X86
