module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the hash function as a table

`TableInstance.signContract`, with the tables of `vs` for `hash`, the
curve's tables of constants and `stackT` bytes of stack (`specK`), from
`tabK`, the contract the proof is written against: on the state with the
arguments' slots readable rather than writable (`nar`, `Verified.narrowTo`).
What the precondition says (`Shared`, `shared_cons`, `shared_nil`): the
table our argument 5 points to is one of `vs`', whose words give `tabK`'s
precondition (`preW_of`); its hash function is the one the table names, so
the results agree (`post_of`); and two runs whose public data agree take the
same table (`pub_of`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HashTable.X86 (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List TVar) :
    Contract isa :=
  T.signContract ((X86.abi.withConsts cs).withTables T.signSig [("hash", tables vs)]) stackT

/-- The regions the proof's contract gives: the arguments' slots readable. -/
def rdK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
    ⟨(arg s 5).setWidth 64, 20⟩, ⟨argAddr s 0, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) cs

def wrK (T : Spec.Ecdsa.Rfc6979.TableInstance) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

/-- The state with the proof's regions. -/
abbrev nar (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (s : State) : State :=
  s.withRegions (rdK T cs s) (wrK T s)

/-- The table our argument 5 points to holds `w`'s. -/
abbrev HeldW (w : TVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem ((arg s 5).setWidth 64) (FnTable.words isa s (tableOf w))

/-- What the precondition says, with the tables of constants `cs`. -/
structure Shared (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (cs : List (String × List (BitVec 64)))
    (s : State) : Prop where
  sp : 544 ≤ (s.gpr .esp).toNat
  top : (s.gpr .esp).toNat + 4 + 24 ≤ 2 ^ 32
  rd : s.rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
    ⟨(arg s 5).setWidth 64, 20⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) cs
  wr : s.wr = [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩, ⟨argAddr s 0, 24⟩]
  held : Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) cs
  fit : ∀ t ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64) cs, t.base.toNat + t.len ≤ 2 ^ 32 ∧
    (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧
      t.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩
  tab : ∃ Tb ∈ tables vs, Abi.tableHeld 32 s.mem ((arg s 5).setWidth 64) (FnTable.words isa s Tb)
  pw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64
  od : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩
  og : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  oc : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩
  ot : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 5).setWidth 64, 20⟩
  oa : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨argAddr s 0, 24⟩
  dc : Region.Disjoint ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩
  gc : Region.Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ ⟨(arg s 4).setWidth 64, 8192⟩
  ct : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨(arg s 5).setWidth 64, 20⟩
  ca : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨argAddr s 0, 24⟩
  ro : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩
  rc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 8192⟩
  ko : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩
  kd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩
  kg : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩ ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  kc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩ ⟨(arg s 4).setWidth 64, 8192⟩
  kt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 544#64, 544⟩ ⟨(arg s 5).setWidth 64, 20⟩
  no : (arg s 0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32
  nd : (arg s 1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32
  ng : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  nc : (arg s 4).toNat + 8192 ≤ 2 ^ 32
  nt : (arg s 5).toNat + 20 ≤ 2 ^ 32
  hH : ∀ H, Spec.HashTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H →
    (arg s 3).toNat = H.len ∧ (Spec.Ecdsa.Rfc6979.hmacOf H).isSome = true

/-- The precondition's simp set. -/
macro "spec_simp" : tactic => `(tactic| simp only [Spec.Ecdsa.Rfc6979.TableInstance.signContract,
    Spec.Ecdsa.Rfc6979.TableInstance.signSig, Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns,
    Abi.withTables, Sig.wordIndex])

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 5 = ⟨p, 20⟩ := rfl

theorem names_eq (vs : List TVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The precondition, with tables of constants. -/
theorem shared_cons {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hsw : T.scratchWords = 1024)
    {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))} {s : State}
    (h : (specK T (c :: cs) vs).pre s) : Shared T vs (c :: cs) s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil] at h
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil] at h
  simp only [hsw, Nat.reduceMul, tableRegion_eq, List.append_eq, List.append_nil, names_eq] at h
  obtain ⟨hsp, htop, hdrop, held, hfit, -, htab, hpw, htake, hwr, od, og, oc, ot, oa, dc, -, gc, -, ct, ca, -, ro,
    -, -, rc, -, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  exact ⟨hsp, htop, by rw [← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop], hwr, held,
    hfit, htab, hpw, od, og, oc, ot, oa, dc, gc, ct, ca, ro, rc, ko, kd, kg, kc, kt, no, nd, ng, nc, nt, hH⟩

/-- The precondition, without tables of constants. -/
theorem shared_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar} (hsw : T.scratchWords = 1024) {s : State}
    (h : (specK T [] vs).pre s) : Shared T vs [] s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil] at h
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw,
    List.append_nil] at h
  simp only [hsw, Nat.reduceMul, tableRegion_eq, List.append_eq, List.append_nil, names_eq] at h
  obtain ⟨hsp, htop, htab, hpw, hrd, hwr, od, og, oc, ot, oa, dc, -, gc, -, ct, ca, -, ro,
    -, -, rc, -, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  exact ⟨hsp, htop, by rw [hrd]; rfl, hwr, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp [Abi.constRegions]),
    htab, hpw, od, og, oc, ot, oa, dc, gc, ct, ca, ro, rc, ko, kd, kg, kc, kt, no, nd, ng, nc, nt, hH⟩

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- The table of `w`, as the proof's contract states it. -/
theorem tab_of {w : TVar} {vs : List TVar} (hv : w ∈ vs) (hc : Coh vs) {s : State}
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hfit : (arg s 5).toNat + 20 ≤ 2 ^ 32) (hh : HeldW w s) : tabFacts w.g.H (fnsOf vs) s := by
  have hm := (held_tableOf hfit hh).1
  have hO := tabOK_of hc hpw hv
  refine ⟨⟨hO.i, hO.u, hO.f⟩, ?_, ?_, ?_⟩
  · rw [← addr_eq (k := 0) (by omega)]; exact hm.1
  · rw [← addr_eq (k := 4) (by omega)]; exact hm.2.1
  · rw [← addr_eq (k := 8) (by omega)]; exact hm.2.2

/-- With the table of `w`: the contract the proof is written against, on the
state with its regions. -/
theorem preW_of {w : TVar} (hv : w ∈ vs) (hc : Coh vs) {s : State} (h : Shared T vs R.E.combConsts s)
    (hh : HeldW w s) : PreW R T vs w (nar T R.E.combConsts s) := by
  have hfit5 := h.nt
  have hm := held_tableOf hfit5 hh
  have hlen : (arg s 3).toNat = w.g.H.D := (h.hH _ (hashAt_tableOf hfit5 hm.2.1)).1.trans w.g.glen
  have hr : (nar T R.E.combConsts s).rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, w.g.H.D⟩,
      ⟨(arg s 5).setWidth 64, 20⟩, ⟨argAddr s 0, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts := by
    show rdK T R.E.combConsts s = _; rw [rdK, hlen]
  have og := h.og; have gc := h.gc; have kg := h.kg; have ng := h.ng
  rw [hlen] at og gc kg ng
  refine ⟨⟨h.sp, by have := h.top; show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega, hr, rfl, h.od, og, h.oc, h.dc, gc, h.oa.symm, h.ca.symm, h.ro, h.rc,
    h.ko, h.kd, kg, h.kc, h.no, h.nd, ng, h.nc, ⟨h.held, fun t ht => ⟨(h.fit t ht).1, fun r hr' => ?_⟩⟩, h.nt,
    h.ot.symm, h.ct.symm, h.kt.symm, tab_of hv hc h.pw hfit5 hh⟩, hm.2.1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl
  · exact (h.fit t ht).2.1 _ (by rw [h.wr]; exact List.mem_cons_self ..)
  · exact (h.fit t ht).2.1 _ (by rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact (h.fit t ht).2.2.1
  · exact (h.fit t ht).2.2.2

theorem Shared.pre (hO : OK vs) {s : State} (h : Shared T vs R.E.combConsts s) :
    (tabK R T vs).pre (nar T R.E.combConsts s) := by
  obtain ⟨Tb, hTb, hh⟩ := h.tab
  obtain ⟨w, hv, rfl⟩ := List.mem_map.mp hTb
  exact ⟨w, hv, hO.2.2.2 w hv, preW_of hv hO.1 h hh⟩

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of (hO : OK vs) {s s' : State} (h : Shared T vs R.E.combConsts s)
    (hp : (tabK R T vs).post (nar T R.E.combConsts s) (s'.withRegions (rdK T R.E.combConsts s) (wrK T s))) :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
        | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨Tb, hTb, hh⟩ := h.tab
  obtain ⟨w, hv, rfl⟩ := List.mem_map.mp hTb
  have hw := hO.2.2.2 w hv
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf h.nt (held_tableOf h.nt hh).2.1))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw (preW_of hv hO.1 h hh)

/-- What the public data say. -/
structure PubF (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s₁ s₂ : State) : Prop where
  held : ∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂
  sp : s₁.gpr .esp = s₂.gpr .esp
  args : ∀ i < 6, arg s₁ i = arg s₂ i
  tried : T.tried 32 s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64) ((arg s₁ 5).setWidth 64) =
    T.tried 32 s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64) ((arg s₂ 5).setWidth 64)
  cs : ∀ c ∈ R.E.combConsts, s₁.syms c.1 = s₂.syms c.1
  ns : ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : TVar} (hw : WOk w) {s : State} (hh : HeldW w s) (hfit : (arg s 5).toNat + 20 ≤ 2 ^ 32) :
    T.tried 32 s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 5).setWidth 64) =
      ((instOf T w).result s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hfit (held_tableOf hfit hh).2.1, hw.hmac,
    tresult_eq]

theorem args6 {s₁ s₂ : State} (a0 : arg s₁ 0 = arg s₂ 0) (a1 : arg s₁ 1 = arg s₂ 1) (a2 : arg s₁ 2 = arg s₂ 2)
    (a3 : arg s₁ 3 = arg s₂ 3) (a4 : arg s₁ 4 = arg s₂ 4) (a5 : arg s₁ 5 = arg s₂ 5) : ∀ i < 6, arg s₁ i = arg s₂ i
  | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : Shared T vs R.E.combConsts s₁)
    (h₂ : Shared T vs R.E.combConsts s₂) (hp : PubF R T vs s₁ s₂) :
    (tabK R T vs).pub (nar T R.E.combConsts s₁) (nar T R.E.combConsts s₂) := by
  obtain ⟨Tb, hTb, hh⟩ := h₁.tab
  obtain ⟨w, hv, rfl⟩ := List.mem_map.mp hTb
  have hw := hO.2.2.2 w hv
  have hh₂ := (hp.held w hv).mp hh
  refine ⟨w, hv, hw, preW_of hv hO.1 h₁ hh, preW_of hv hO.1 h₂ hh₂, hp.sp, hp.args 0 (by decide),
    hp.args 1 (by decide), hp.args 2 (by decide), hp.args 3 (by decide), hp.args 4 (by decide),
    hp.args 5 (by decide), ?_, hp.cs, hp.ns⟩
  show ((instOf T w).result s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
    ((instOf T w).result s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64)).2
  rw [← tried_eq hw hh h₁.nt, ← tried_eq hw hh₂ h₂.nt, hp.tried]

/-- The public data, with tables of constants. -/
theorem pubF_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.E.combConsts = c :: cs) {s₁ s₂ : State} (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubF R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil] at h
  simp only [List.append_eq, List.append_nil, names_eq] at h
  obtain ⟨e₁, hc₀, hcs', hn, hT, htr, a0, a1, a2, a3, a4, a5⟩ := h
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), e₁, args6 a0 a1 a2 a3 a4 a5, (List.cons.inj htr).1,
    fun c' hc' => ?_, hn⟩
  rw [hcs] at hc'
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc₀
  · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pubF_nil (hcs : R.E.combConsts = []) {s₁ s₂ : State} (h : (specK T [] vs).pub s₁ s₂) :
    PubF R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil] at h
  simp only [List.append_eq, List.append_nil, names_eq] at h
  obtain ⟨e₁, hn, hT, htr, a0, a1, a2, a3, a4, a5⟩ := h
  exact ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), e₁, args6 a0 a1 a2 a3 a4 a5, (List.cons.inj htr).1,
    fun c' hc' => absurd hc' (by rw [hcs]; simp), hn⟩

/-- The postcondition's form, for any tables of constants. -/
theorem post_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))} {s s' : State}
    (hp : ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
        | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0) :
    (specK T (c :: cs) vs).post s s' := by
  sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil]
  exact hp

theorem post_nil {s s' : State}
    (hp : ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
        | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0) :
    (specK T [] vs).post s s' := by
  sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil]
  exact hp

/-- The proof's regions are among the shared contract's. -/
theorem coversK_of {cs : List (String × List (BitVec 64))} {s : State} (h : Shared T vs cs s) : Covers (rdK T cs s ++ wrK T s) (s.rd ++ s.wr) := by
  intro a n ⟨r, hr, hc⟩
  refine ⟨r, ?_, hc⟩
  rw [h.rd, h.wr]
  simp only [rdK, wrK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with ((rfl | rfl | rfl | rfl) | hr) | (rfl | rfl) <;> simp_all

theorem coversKW_of {cs : List (String × List (BitVec 64))} {s : State} (h : Shared T vs cs s) : Covers (wrK T s) s.wr := by
  intro a n ⟨r, hr, hc⟩
  refine ⟨r, ?_, hc⟩
  rw [h.wr]
  simp only [wrK, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl <;> simp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) :
    Verified X86.target (signCode R T.tries vs) (specK T R.E.combConsts vs) := by
  have facts : ∀ s, (specK T R.E.combConsts vs).pre s → Shared T vs R.E.combConsts s := fun s h => by
    revert h
    cases R.E.combConsts with
    | nil => exact shared_nil hsw
    | cons c cs => exact shared_cons hsw
  have pubs : ∀ s₁ s₂, (specK T R.E.combConsts vs).pub s₁ s₂ → PubF R T vs s₁ s₂ := fun s₁ s₂ h => by
    cases hcs : R.E.combConsts with
    | nil => rw [hcs] at h; exact pubF_nil hcs h
    | cons c cs => rw [hcs] at h; exact pubF_cons hcs h
  have satK : ∃ s, (tabK R T vs).pre s := hsat.elim fun s h => ⟨_, (facts s h).pre hO⟩
  have hk : Verified X86.target (signCode R T.tries vs) (tabK R T vs) :=
    Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC hO.2.2.2) (.refl satK)
  refine Verified.narrowTo hk (rdK T R.E.combConsts) (wrK T) (fun s h => (facts s h).pre hO)
    (fun s h => coversK_of (facts s h)) (fun s h => coversKW_of (facts s h)) (fun s s' h hp => ?_)
    (fun s₁ s₂ h₁ h₂ hp => pub_of hO (facts _ h₁) (facts _ h₂) (pubs _ _ hp)) hsat
  have hpost := post_of hO (facts s h) hp
  revert hpost
  cases R.E.combConsts with
  | nil => exact post_nil
  | cons c cs => exact post_cons

end VG.Proof.Ecdsa.Rfc6979.X86
