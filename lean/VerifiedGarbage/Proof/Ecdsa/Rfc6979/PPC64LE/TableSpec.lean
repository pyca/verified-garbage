module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Table
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# Deterministic ECDSA on PPC64LE: the contract with the hash function as a table

`TableInstance.signContract`, with the tables of `vs` for `hash` and
`stackT` bytes of stack, implies `tabK` (`tab_implies`): the table `hash`
points to is one of `vs`', whose words give the contract the proof of its
hash function's code is written against, on entry (`pre_facts`); its hash
function is the one the table names, so the results agree; and two runs
whose public data agree take the same table. A state meeting it (`satT`):
the buffers at fixed addresses, the table of a hash function of `vs` at
`0x300000` and the functions of `vs` at distinct addresses (`withTable`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.HashTable.PPC64LE (TVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf
  withTable withTable_held)

variable {C : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List TVar}

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) : Contract isa :=
  T.signContract (PPC64LE.abi.withTables T.signSig [("hash", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 5 = ⟨p, 40⟩ := rfl

theorem names_eq (vs : List TVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hash` points to holds `w`'s. -/
abbrev HeldW (w : TVar) (s : State) : Prop := Abi.tableHeld 64 s.mem (s.gpr .r8) (FnTable.words isa s (tableOf w))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW T vs w s

theorem pre_facts (hsw : T.scratchWords = 1024) (hO : OK vs) {s : State} (h : (specK T vs).pre s) :
    PreFacts T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, dc, gc, ct, ko, kd, kg, kc, kt, no, nd, ng, nc, nt,
    hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .r6).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.l.len
  rw [hlen] at og gc kg ng hrd
  rw [hsw] at hwr oc dc gc kc nc ct
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hrd, hwr, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, hsp, nt, ot.symm, ct.symm, kt,
    tabOK_of hO.1 hpw hv, hh.1⟩, hh.2.1⟩

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK T vs).pre s) (hp : (tabK T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HashTable.hashAt 64 s.mem (s.gpr .r8) = some H → Spec.Ecdsa.Rfc6979.hmacOf H = some F →
        match (T.result H F s.mem (s.gpr .r4) (s.gpr .r5)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .r3) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .r3) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .r3) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List TVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ (∀ r ∈ [Reg.r3, .r4, .r5, .r7, .r8], s₁.gpr r = s₂.gpr r) ∧
    s₁.sp = s₂.sp ∧
    T.tried 64 s₁.mem (s₁.gpr .r4) (s₁.gpr .r5) (s₁.gpr .r8) =
      T.tried 64 s₂.mem (s₂.gpr .r4) (s₂.gpr .r5) (s₂.gpr .r8) ∧
    ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : TVar} (hw : WOk w) {s : State} (hp : PreW T vs w s) :
    T.tried 64 s.mem (s.gpr .r4) (s.gpr .r5) (s.gpr .r8) =
      ((instOf T w).result s.mem (s.gpr .r4) (s.gpr .r5)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.2, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts T vs s₁) (h₂ : PreFacts T vs s₂)
    (hp : PubFacts T vs s₁ s₂) : (tabK T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hg, hsp, ht, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hsp, hg .r3 (by simp), hg .r4 (by simp), hg .r5 (by simp), hg .r7 (by simp), ?_,
    hg .r8 (by simp), hn⟩
  show ((instOf T w).result s₁.mem (s₁.gpr .r4) (s₁.gpr .r5)).2 =
    ((instOf T w).result s₂.mem (s₂.gpr .r4) (s₂.gpr .r5)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

theorem pub_facts {s₁ s₂ : State} (h : (specK T vs).pub s₁ s₂) : PubFacts T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, htr, e₃, e₄, e₅, -, e₇, e₈⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), fun r hr => ?_, hsp, (List.cons.inj htr).1, hn⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts T vs s) : (tabK T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs) (hsat : ∃ s, (specK T vs).pre s) :
    (tabK T vs).Implies (specK T vs) := by
  refine ⟨fun s h => (pre_facts hsw hO h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hO (pre_facts hsw hO h₁) (pre_facts hsw hO h₂) (pub_facts hp), hsat⟩
  have hk := (pre_facts hsw hO h).pre hO
  sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  exact post_of hk hp

/-! ## A state meeting the contract -/

/-- A state meeting the contract, but for the table, for scalars of `Q`
bytes and a digest of `D`. -/
def satT (Q D : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => BitVec.ofNat 64 D | .r7 => 0x8000
    | .r8 => 0x300000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, Q⟩, ⟨0x3000, D⟩, ⟨0x300000, 40⟩]
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]

/-- A state meeting the contract, with the table of one of `vs`. -/
theorem sat (hO : OK vs) (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) :
    ∃ s, (specK T vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨withTable (satT T.ecdsa.curve.len w.H.D) vs w, ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := w.l.ok.hD64
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega
  have hG : Spec.HashTable.hashAt 64 (withTable (satT T.ecdsa.curve.len w.H.D) vs w).mem 0x300000 =
      some w.l.G := hashAt_tableOf (held_tableOf (withTable_held _ vs w)).2.1
  have hheld : ∃ Tb ∈ tables vs, Abi.tableHeld 64 (withTable (satT T.ecdsa.curve.len w.H.D) vs w).mem 0x300000
      (FnTable.words isa (withTable (satT T.ecdsa.curve.len w.H.D) vs w) Tb) :=
    ⟨tableOf w, List.mem_map_of_mem hv, withTable_held _ vs w⟩
  simp only [withTable, satT, hDn, hsw] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | exact trivial
    | exact hheld
    | (rw [List.append_eq, List.append_nil]; exact Proof.HashTable.symsOf_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.l.len.symm, by rw [hw.hmac]; rfl⟩)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract`. -/
theorem signT_verified (hC : CurveT C T) (hsw : T.scratchWords = 1024) (hO : OK vs) (hQ : T.ecdsa.curve.len ≤ 66) :
    Verified PPC64LE.target (signCode C T.tries vs) (specK T vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC hO.2.2.2) (tab_implies hsw hO (sat hO hQ hsw))

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
