module

public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Table
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Table

/-! ### `Ecdsa.Rfc6979.X86_64.TableSpec`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: the contract with the hash function as a table

`TableInstance.signContract`, with the tables of `vs` for `hmac`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hmac` points to is one of `vs`', whose words
give the contract the proof of the body is written against, after the entry
(`preW_of`); its hash function is the one the table names, so the
results agree; and two runs whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- The facts of the contract with the table of `w`, on entry. -/
theorem preW_of {w : MdHash} (hv : w ∈ vs) (hc : Coh vs) (hw : WOk w) {s : State}
    (hsp : 640 ≤ (s.gpr .rsp).toNat)
    (hrd : s.rd = [⟨s.gpr .rsi, T.ecdsa.curve.len⟩, ⟨s.gpr .rdx, w.H.D⟩, ⟨s.gpr .r9, 48⟩] ++
      Abi.constRegions (fun n => s.syms n) R.E.combConsts)
    (hwr : s.wr = [⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩, ⟨s.gpr .r8, 8192⟩])
    (od : Region.Disjoint ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .rsi, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .rdx, w.H.D⟩)
    (oc : Region.Disjoint ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .r8, 8192⟩)
    (dc : Region.Disjoint ⟨s.gpr .rsi, T.ecdsa.curve.len⟩ ⟨s.gpr .r8, 8192⟩)
    (gc : Region.Disjoint ⟨s.gpr .rdx, w.H.D⟩ ⟨s.gpr .r8, 8192⟩)
    (ro : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩)
    (rd : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, T.ecdsa.curve.len⟩)
    (rg : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, w.H.D⟩)
    (rc : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r8, 8192⟩)
    (ko : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩ ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩ ⟨s.gpr .rsi, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩ ⟨s.gpr .rdx, w.H.D⟩)
    (kc : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩ ⟨s.gpr .r8, 8192⟩)
    (no : (s.gpr .rdi).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 64)
    (nd : (s.gpr .rsi).toNat + T.ecdsa.curve.len ≤ 2 ^ 64) (ng : (s.gpr .rdx).toNat + w.H.D ≤ 2 ^ 64)
    (nc : (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64)
    (ht : TblsOk R.E.combConsts s [⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩, ⟨s.gpr .r8, 8192⟩, ⟨s.gpr .rsp, 8⟩,
      ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩])
    (n9 : (s.gpr .r9).toNat + 48 ≤ 2 ^ 64)
    (tout : Region.Disjoint ⟨s.gpr .rdi, 2 * T.ecdsa.curve.len⟩ ⟨s.gpr .r9, 48⟩)
    (tsc : Region.Disjoint ⟨s.gpr .r8, 8192⟩ ⟨s.gpr .r9, 48⟩)
    (tret : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 48⟩)
    (tstk : Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 640, 640⟩ ⟨s.gpr .r9, 48⟩)
    (hheld : Abi.tableHeld 64 s.mem (s.gpr .r9) (FnTable.words isa s (tableOf w)))
    (hpw : (names vs).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g) :
    PreW R T vs w s := by
  have hh := held_tableOf hheld
  rw [hw.blockSize] at hh
  exact ⟨⟨hsp, hrd, hwr, od, og, oc, dc, gc, ro, rd, rg, rc, ko, kd, kg, kc, no, nd, ng, nc, ht, n9, tout.symm,
    tsc.symm, tret.symm, tstk.symm, tabOK_of hc hpw hv, hh.1, rfl, rfl⟩, hh.2.1, hh.2.2.1, hh.2.2.2⟩


/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List MdHash) :
    Contract isa :=
  T.signContract ((X86_64.abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]) stackT

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List MdHash) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : MdHash) (s : State) : Prop := Abi.tableHeld 64 s.mem (s.gpr .r9) (FnTable.words isa s (tableOf w))

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

/-- The precondition, with tables of constants. -/
theorem pre_cons (hsw : T.scratchWords = 1024) (hO : OK vs) {c : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))} (hcs : R.E.combConsts = c :: cs) {s : State}
    (h : (specK T (c :: cs) vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hdrop, held, hfit, -, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, dc, gc, ct, ro, rd, rg, rc,
    rt, ko, kd, kg, kc, kt, no, nd, ng, nc, n9, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .rcx).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.mgf.len
  rw [hlen] at og gc rg kg ng htake
  rw [hsw] at hwr oc dc gc rc kc nc ct
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 (hO.2.2.2 w hv) hsp ?_ hwr od og oc dc gc ro rd rg rc ko kd kg kc no nd ng nc ?_ n9
    ot ct rt kt hheld hpw
  · rw [hcs, ← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]
  · rw [hcs]
    refine ⟨held, fun t htm => ⟨(hfit t htm).1, fun r hr => ?_⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
    · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
    · exact (hfit t htm).2.2.1
    · exact (hfit t htm).2.2.2


/-- The precondition, without tables of constants. -/
theorem pre_nil (hsw : T.scratchWords = 1024) (hO : OK vs) (hcs : R.E.combConsts = []) {s : State}
    (h : (specK T [] vs).pre s) : PreFacts R T vs s := by
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, dc, gc, ct, ro, rd, rg, rc,
    rt, ko, kd, kg, kc, kt, no, nd, ng, nc, n9, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hlen : (s.gpr .rcx).toNat = w.H.D := (hH _ (hashAt_tableOf hh.2.1)).1.trans w.mgf.len
  rw [hlen] at og gc rg kg ng hrd
  rw [hsw] at hwr oc dc gc rc kc nc ct
  rw [List.append_eq, List.append_nil] at hpw
  refine preW_of hv hO.1 (hO.2.2.2 w hv) hsp ?_ hwr od og oc dc gc ro rd rg rc ko kd kg kc no nd ng nc ?_ n9
    ot ct rt kt hheld hpw
  · rw [hcs, hrd]; rfl
  · rw [hcs]; exact ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp [Abi.constRegions])⟩


/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 64 s.mem (s.gpr .r9) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem (s.gpr .rsi) (s.gpr .rdx)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .rax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .rax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .rdi) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.2.1))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ (∀ r ∈ [Reg.rsp, .rdi, .rsi, .rdx, .r8, .r9], s₁.gpr r = s₂.gpr r) ∧
    T.tried 64 s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx) (s₁.gpr .r9) =
      T.tried 64 s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx) (s₂.gpr .r9) ∧
    (∀ c ∈ R.E.combConsts, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : MdHash} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 64 s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .r9) =
      ((instOf T w).result s.mem (s.gpr .rsi) (s.gpr .rdx)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.2.1, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hg, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hg .rsp (by simp), hg .rdi (by simp), hg .rsi (by simp), hg .rdx (by simp),
    hg .r8 (by simp), hg .r9 (by simp), ?_, hc, hn⟩
  show ((instOf T w).result s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 =
    ((instOf T w).result s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- The public data, with tables of constants. -/
theorem pub_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.E.combConsts = c :: cs) {s₁ s₂ : State}
    (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨e₁, hc₀, hcs', hn, hT, htr, e₂, e₃, e₄, -, e₅, e₆⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), fun r hr => ?_, (List.cons.inj htr).1,
    fun c' hc' => ?_, hn⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [hcs] at hc'
    rcases List.mem_cons.mp hc' with rfl | h
    · exact hc₀
    · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pub_nil (hcs : R.E.combConsts = []) {s₁ s₂ : State}
    (h : (specK T [] vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨e₁, hn, hT, htr, e₂, e₃, e₄, -, e₅, e₆⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), fun r hr => ?_, (List.cons.inj htr).1,
    fun c' hc' => absurd hc' (by rw [hcs]; simp), hn⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption


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
      X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) :
    Verified X86_64.target (signCodeT R T.tries vs) (specK T R.E.combConsts vs) :=
  Verified.of_correct (fun _ h => let ⟨t, s', he, hg, hp⟩ := signT_ok hC h
      ⟨t, s', he, abiPreserved_of_exec (signCode_mx R T.tries vs) he hg, hp⟩)
    (signT_ct hC) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: the contract with the table is satisfiable

A state meeting `TableInstance.signContract` with the tables of `vs`
(`satT`): the buffers at fixed addresses, the table of a variant `w` of
`vs` at `0x300000`, the functions of `vs` at distinct addresses
(`HashTable.symsOf`), and the curve's table of constants, if any, at
`0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash)
open VG.Proof.HmacTable.X86_64 (tables names tableOf held_tableOf hashAt_tableOf mem_names)
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
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
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
  all_goals first | (simp only [h0, h1, h2, h3, h4, h5]; omega_arith) | omega_using [ha]

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List MdHash) (n : String) : Addr := if n ∈ names vs then symsOf (names vs) n else 0x100000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List MdHash) (w : MdHash) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => BitVec.ofNat 64 w.H.D | .r8 => 0x8000
    | .r9 => 0x300000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := put6 m₀ 0x300000 (symT vs w.H.hmacInitAnyN) (symT vs w.H.updN) (symT vs w.H.hmacFinN)
    (BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) (BitVec.ofNat 64 w.mgf.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G))
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.H.D⟩, ⟨0x300000, 48⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩]
  syms := symT vs

theorem satT_held (vs : List MdHash) (w : MdHash) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 64 (satT vs w m₀ Q Tr).mem 0x300000 (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) :=
  put6_held (ws := [symT vs w.H.hmacInitAnyN, symT vs w.H.updN, symT vs w.H.hmacFinN,
    BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)]) rfl

theorem symT_distinct {vs : List MdHash} (hl : (names vs).length < 2 ^ 32) :
    (names vs).Pairwise fun f g => f ≠ g → symT vs f ≠ symT vs g :=
  (symsOf_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne


theorem constRegions_symT (vs : List MdHash) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => symT vs name) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hheld : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := by have := w.ok.hDN; have := w.ok.N_le; omega_arith
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hsym : symT vs n = 0x100000 := by simp only [symT, hna, ite_false]
  have hG : Spec.HmacTable.hashAt 64 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem 0x300000 =
      some w.mgf.G := hashAt_tableOf (held_tableOf (satT_held vs w m₀ _ _)).2.1
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
       exact ⟨w.mgf.len.symm, by rw [hw.hmac]; rfl⟩)
    | (intro i hi
       show (put6 m₀ _ _ _ _ _ _ _).readW (symT vs n + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0
       rw [hsym, put6_below (by bv_omega)]
       exact hheld i hi)
    | (show (1048576 : BitVec 64).toNat % 64 = 0; decide)
    | (refine ⟨show (1048576 : BitVec 64).toNat + 8 * W.length ≤ 2 ^ 64 by bv_omega, ?_, ?_, ?_, ?_⟩ <;>
       exact Region.disjoint_of_sep (by
         simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86_64.abi, X86_64.argRegs, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', hsw, tableRegion_eq,
    List.append_nil, names_eq]
  have hD : w.H.D ≤ 64 := by have := w.ok.hDN; have := w.ok.N_le; omega_arith
  have hDn : (BitVec.ofNat 64 w.H.D).toNat = w.H.D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  have hG : Spec.HmacTable.hashAt 64 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem 0x300000 =
      some w.mgf.G := hashAt_tableOf (held_tableOf (satT_held vs w _ _ _)).2.1
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
       exact ⟨w.mgf.len.symm, by rw [hw.hmac]; rfl⟩)

end VG.Proof.Ecdsa.Rfc6979.X86_64
