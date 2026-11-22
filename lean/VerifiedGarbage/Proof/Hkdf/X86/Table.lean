module
-- separate module: its proofs need none of the HMAC implementations' literals that `Scrub` evaluates its side conditions with, so they build in parallel with those

public import VerifiedGarbage.Proof.Hkdf.X86.Key
public import VerifiedGarbage.Proof.Hkdf.X86.Extract
public import VerifiedGarbage.Proof.Hkdf.X86.Expand
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Basic
public import VerifiedGarbage.Spec.Hkdf.Table
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on x86 (32-bit): the contracts with the hash function as a table

As on x86-64 (`Proof/Hkdf/X86_64/Table.lean`): each function is one body,
which loads `D` and `B` from the table `hmac` and calls the table's
functions. For the variants `vs` whose tables it takes (`OK`: their
functions of the same name have the same code, their sizes fit the frames
(`HOk`), and each's streaming states are the specification's for its hash
function, `Streams`), the table of each `w` makes the body meet the
contract with `w` fixed (`keyR`, `key_correct`, `key_ct`). `keyTab` states
that contract for whichever of the tables `hmac` holds, on entry, which the
specification's contract with the tables of `vs` implies (`key_implies`):
the table `hmac` points to is one of `vs`', whose words give the contract
the proof is written against; its hash function is the one the table names;
and two runs whose public data agree take the same table. A state meets it
(`key_sat`): the buffers at fixed addresses, our arguments on the stack at
`0x20004`, the table of a variant of `vs` at `0x300000`, the functions of
`vs` at distinct addresses (`HashTable.symsOf32`). No instruction of the
bodies writes `esp` (`keyBody_noSp`), as none of the table's functions'
does.
-/

@[expose] public section

namespace VG.Proof.Hkdf.X86

open VG VG.X86
open VG.Proof.HmacTable.X86 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)

/-- What the registrations check of the variants whose tables the functions
take: the functions of the same name have the same code, there are fewer
than `2 ^ 24` names, there is one, and each's sizes fit the frames. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ [] ∧ ∀ w ∈ vs, HOk w

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

/-- Each variant's streaming states are those the specification gives its
hash function (`Spec.Hkdf.streamingOf`). -/
def Streams (vs : List HVar) : Prop := ∀ w ∈ vs, Spec.Hkdf.streamingOf w.G = some w.ok.hH.SH

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 6 = ⟨p, 24⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

theorem hvar_mem (w : HVar) : w.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx

/-- The HMAC of `w`'s hash function. -/
theorem HOk.hmac {w : HVar} (hw : HOk w) : Spec.HmacTable.hmacOf w.G = some w.ok.hH.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ (hvar_mem w) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hH.hB.symm, funext fun x => (congrFun hh x).trans (w.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem HOk.blockSize {w : HVar} (hw : HOk w) : Spec.HmacTable.blockSize w.G = w.F.H.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hH.hB

/-- The table `hmac` (our argument `i`) points to holds `w`'s. -/
abbrev HeldW (i : Nat) (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem ((arg s i).setWidth 64) (FnTable.words isa s (tableOf w))

/-- The table's index, as the table of `w` holds it. -/
abbrev IdxW (i : Nat) (w : HVar) (s : State) : Prop :=
  s.mem.readW (addr (arg s i) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

/-- The hash function a table of `w` names, and its streaming states. -/
theorem streams_of {vs : List HVar} (hS : Streams vs) {w : HVar} (hv : w ∈ vs) {m : Mem} {p : BitVec 32}
    (hp : p.toNat + 24 ≤ 2 ^ 32) (h : m.readW (addr p 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G))
    {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash} (hH : Spec.HmacTable.hashAt 32 m (p.setWidth 64) = some H)
    (hSt : Spec.Hkdf.streamingOf H = some S) : S = w.ok.hH.SH := by
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hp h))
  exact Option.some.inj (hSt.symm.trans (hS w hv))

theorem args_of4 {s₁ s₂ : State} (e₀ : arg s₁ 0 = arg s₂ 0) (e₁ : arg s₁ 1 = arg s₂ 1) (e₂ : arg s₁ 2 = arg s₂ 2)
    (e₃ : arg s₁ 3 = arg s₂ 3) : ∀ i < 4, arg s₁ i = arg s₂ i
  | 0, _ => e₀ | 1, _ => e₁ | 2, _ => e₂ | 3, _ => e₃

theorem args_of6 {s₁ s₂ : State} (e₀ : arg s₁ 0 = arg s₂ 0) (e₁ : arg s₁ 1 = arg s₂ 1) (e₂ : arg s₁ 2 = arg s₂ 2)
    (e₃ : arg s₁ 3 = arg s₂ 3) (e₄ : arg s₁ 4 = arg s₂ 4) (e₅ : arg s₁ 5 = arg s₂ 5) : ∀ i < 6, arg s₁ i = arg s₂ i
  | 0, _ => e₀ | 1, _ => e₁ | 2, _ => e₂ | 3, _ => e₃ | 4, _ => e₄ | 5, _ => e₅

theorem args_of7 {s₁ s₂ : State} (e₀ : arg s₁ 0 = arg s₂ 0) (e₁ : arg s₁ 1 = arg s₂ 1) (e₂ : arg s₁ 2 = arg s₂ 2)
    (e₃ : arg s₁ 3 = arg s₂ 3) (e₄ : arg s₁ 4 = arg s₂ 4) (e₅ : arg s₁ 5 = arg s₂ 5) (e₆ : arg s₁ 6 = arg s₂ 6) :
    ∀ i < 7, arg s₁ i = arg s₂ i
  | 0, _ => e₀ | 1, _ => e₁ | 2, _ => e₂ | 3, _ => e₃ | 4, _ => e₄ | 5, _ => e₅ | 6, _ => e₆

/-! ## No instruction writes `esp` but the frames' -/

/-- No instruction of `x` writes `esp`. -/
abbrev OkP (x : Prog isa) : Prop := x.allInstrs (fun i => !Taint.clobbers i .esp) = true

theorem okP_seq {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.seq a b) := by
  show (a.allInstrs _ && b.allInstrs _) = true; rw [ha, hb]; rfl

theorem okP_ite {cnd : Cond} {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.ite cnd a b) := by
  show (a.allInstrs _ && b.allInstrs _) = true; rw [ha, hb]; rfl

theorem okP_loop {cnd : Cond} {a : Prog isa} (ha : OkP a) : OkP (.loop a cnd) := ha

theorem okP_of_noSp {c : Prog isa} (h : NoSp c) : OkP c := by
  rw [OkP, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

/-- No instruction of any of the functions `ts` writes `esp`. -/
def FnsOk (ts : List (String × Prog isa)) : Prop := ∀ q ∈ ts, OkP q.2

theorem icalls_okP : ∀ {ts : List (String × Prog isa)}, FnsOk ts → OkP (Code.icalls (.callr .ebx) ts)
  | [], _ => rfl
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_okP (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    show (Code.icalls (.callr .ebx) (q :: ts)).allInstrs _ = true
    simp only [Code.icalls, Code.allInstrs, show q.2.allInstrs _ = true from hq,
      show (Code.icalls (.callr .ebx) ts).allInstrs _ = true from ih, Bool.and_true]; rfl

theorem tcall_okP {F ti j : Nat} {ts : List (String × Prog isa)} {rs : List Reg} (h : FnsOk ts) :
    OkP (Impl.Hkdf.X86.tcall F ti j ts rs) := by
  show (true && (true && ((!Taint.clobbers (.push rs) .esp) && (Code.icalls (.callr .ebx) ts).allInstrs _ &&
    !Taint.clobbers (.pop .eax rs.length) .esp))) = true
  rw [icalls_okP h]; rfl

theorem fnsOk_of (vs : List HVar) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact okP_of_noSp w.anySp
  · exact okP_of_noSp w.ok.hH.updSp
  · exact okP_of_noSp w.ok.hfSp

theorem keyBody_okP (vs : List HVar) : OkP (Impl.Hkdf.X86.keyBody (fnsOf vs)) :=
  okP_seq rfl (okP_seq rfl (okP_seq (tcall_okP (fnsOk_of vs).1) rfl))

theorem extractBody_okP (vs : List HVar) : OkP (Impl.Hkdf.X86.extractBody (fnsOf vs)) := by
  have h := fnsOk_of vs
  exact okP_seq rfl (okP_seq rfl (okP_seq rfl (okP_seq (tcall_okP h.1) (okP_seq rfl (okP_seq (tcall_okP h.2.1)
    (okP_seq rfl (okP_seq (tcall_okP h.2.2) rfl)))))))

theorem block_okP (vs : List HVar) : OkP (Impl.Hkdf.X86.block (fnsOf vs)) := by
  have h := fnsOk_of vs
  exact okP_seq rfl (okP_seq rfl (okP_seq rfl (okP_seq (tcall_okP h.2.1) (okP_seq rfl (okP_seq (tcall_okP h.2.1)
    (okP_seq rfl (okP_seq (tcall_okP h.2.1) (okP_seq rfl (okP_seq (tcall_okP h.2.2)
    (okP_seq (okP_seq rfl (okP_ite rfl rfl)) (okP_seq rfl (okP_seq rfl rfl))))))))))))

theorem expandBody_okP (vs : List HVar) : OkP (Impl.Hkdf.X86.expandBody (fnsOf vs)) :=
  okP_seq rfl (okP_seq rfl (okP_seq (okP_ite (okP_loop (block_okP vs)) rfl) rfl))

/-- The frame's body of a function whose instructions write no `esp`, and
the function, whose only writes of it are its frame's. -/
theorem frame_sp {n : Nat} {c : Prog isa} (h : OkP c) :
    (Code.frame (.alloc n) c (.free n) : Prog isa).all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  simp only [OkP, Proof.Pbkdf2.Whole.X86.clobbers_esp] at h
  simp only [Code.allInstrs, h]
  rfl

/-! ## `vg_hkdf_key` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specKey (vs : List HVar) : Contract isa :=
  Spec.Hkdf.keyContract (X86.abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]) kStack

/-- The contract with the table of `w`, and its index. -/
def KeyW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (keyR w (fnsOf vs) (names vs) kStack).pre s ∧ IdxW 3 w s

/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def keyTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, KeyW vs w s
  post s s' := ∀ H S, Spec.HmacTable.hashAt 32 s.mem ((arg s 3).setWidth 64) = some H →
    Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s'.mem ((arg s 2).setWidth 64) (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, KeyW vs w s₁ ∧ KeyW vs w s₂ ∧ (keyR w (fnsOf vs) (names vs) kStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem keyT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (keyTab vs).pre s) :
    WP isa (Impl.Hkdf.X86.key (fnsOf vs)) s fun s' => abiPreserved s s' ∧ (keyTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  have nt : (arg s 3).toNat + 24 ≤ 2 ^ 32 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.mono (key_correct (hO.2.2.2 w hv) (NoSp.of_all (keyBody_okP vs)) hp) fun s' ⟨hg, hpost⟩ =>
    ⟨hg, fun H S hH hSt => ?_⟩
  rw [streams_of hS hv nt hix hH hSt]
  exact hpost

theorem keyT_ct (hO : OK vs) : ConstantTime isa (keyTab vs).pre (keyTab vs).pub (Impl.Hkdf.X86.key (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact key_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      exacts [hn.1, hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def KeyFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW 3 w s) ∧ ∀ w ∈ vs, HeldW 3 w s → KeyW vs w s

theorem key_pre (hO : OK vs) {s : State} (h : (specKey vs).pre s) : KeyFacts vs s := by
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, kStack, Impl.Hkdf.X86.kFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, htop, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, pk, -, kt, ka, -, -, rk, -, -, sp, sk, st, -, np, nk, nt,
    -⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf nt hheld
  rw [(hO.2.2.2 w hv).blockSize] at hh
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, htop, hrd, hwr, pk, kt, ka, rk, sp, sk, st, np, nk, nt, tabOK_of hO.1 hpw hv, hh.1, hh.2.2.1,
    hh.2.2.2⟩, hh.2.1⟩

theorem key_pub {s₁ s₂ : State} (h₁ : KeyFacts vs s₁) (h₂ : KeyFacts vs s₂) (h : (specKey vs).pub s₁ s₂) :
    (keyTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.keyContract, Spec.Hkdf.keySig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, kStack, Impl.Hkdf.X86.kFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, args_of4 e0 e1 e2 e3, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem key_implies (hO : OK vs) (hsat : ∃ s, (specKey vs).pre s) : (keyTab vs).Implies (specKey vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp => key_pub (key_pre hO h₁) (key_pre hO h₂) hp,
    hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := key_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86.abi, stackBelow, kStack, Impl.Hkdf.X86.kFr, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
    exact fun H S a b => hp H S a b

end

/-! ## A state meeting each contract -/

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
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The words `put6w` writes. -/
theorem put6w_read {m : Mem} {p : Addr} (hp : p.toNat + 24 ≤ 2 ^ 64) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) :
    ∀ i < 6, (put6w m p w₀ w₁ w₂ w₃ w₄ w₅).readW (p + BitVec.ofNat 64 (4 * i)) 32 =
      [w₀, w₁, w₂, w₃, w₄, w₅].getD i 0 := by
  intro i hi
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk =>
    toNat_add_lit (by omega_using [hp, hk])
  have s : ∀ i j, i < 6 → j < 6 → i ≠ j → ∀ v : BitVec 32, ∀ m : Mem,
      (m.writeW (p + BitVec.ofNat 64 (4 * j)) v).readW (p + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := fun i j hi hj hij v m => by
    refine readW_sepw (by decide) ?_ ?_ ?_ <;>
      simp only [Nat.reduceDiv, t (4 * i) (by omega_using [hi]), t (4 * j) (by omega_using [hj])] <;>
      omega_arith
  simp only [put6w]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
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
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk =>
    toNat_add_lit (by omega_using [hp, hk])
  simp only [put6w]
  rw [readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw]
  all_goals first | (simp only [t 0 (by omega_using []), t 4 (by omega_using []), t 8 (by omega_using []),
    t 12 (by omega_using []), t 16 (by omega_using []), t 20 (by omega_using []), show 4 * 0 = 0 from rfl,
    show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl, show 4 * 3 = 12 from rfl, show 4 * 4 = 16 from rfl,
    show 4 * 5 = 20 from rfl]; omega_arith) | omega_using [ha']

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : BitVec 32 :=
  if n ∈ names vs then symsOf32 (names vs) n else 0x100000

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

/-- Our arguments' words, at `0x20004`. -/
def argMem (a : List (BitVec 32)) : Mem :=
  (put6w (fun _ => 0) 0x20004 (a.getD 0 0) (a.getD 1 0) (a.getD 2 0) (a.getD 3 0) (a.getD 4 0) (a.getD 5 0)).writeW
    0x2001C (a.getD 6 0)

/-- A state meeting a contract: `esp` at `0x20000`, our arguments `a` above
it, the table of `w` at `0x300000`, the regions `rd` and `wr`. -/
def satS (vs : List HVar) (w : HVar) (a : List (BitVec 32)) (rd wr : List Region) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := put6w (argMem a) 0x300000 (((symT vs w.F.hiAnyN).setWidth 64).setWidth 32)
    (((symT vs w.F.H.updN).setWidth 64).setWidth 32) (((symT vs w.F.hfN).setWidth 64).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HashTable.index w.G)).setWidth 32) ((BitVec.ofNat 64 w.G.len).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)).setWidth 32)
  rd := rd
  wr := wr
  syms := symT vs

theorem satS_held (vs : List HVar) (w : HVar) (a : List (BitVec 32)) (rd wr : List Region) :
    Abi.tableHeld 32 (satS vs w a rd wr).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (satS vs w a rd wr) (tableOf w)) := by
  intro i hi
  have hl : (FnTable.words isa (satS vs w a rd wr) (tableOf w)).length = 6 := rfl
  rw [hl] at hi
  exact put6w_read (p := 0x300000) (by decide) _ _ _ _ _ _ i hi |>.trans (by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem satS_arg (vs : List HVar) (w : HVar) (a : List (BitVec 32)) (rd wr : List Region) :
    ∀ i < 7, arg (satS vs w a rd wr) i = a.getD i 0 := by
  intro i hi
  have ha : argAddr (satS vs w a rd wr) i = 0x20004 + BitVec.ofNat 64 (4 * i) := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  show (satS vs w a rd wr).mem.readW (argAddr (satS vs w a rd wr) i) 32 = _
  have h4 : (0x20004 : Addr).toNat = 0x20004 := rfl
  rw [ha]
  simp only [satS]
  rw [put6w_out (by decide) (by decide) (by
    rw [toNat_add_lit (by omega)]
    show 0x20004 + 4 * i + 32 / 8 ≤ 0x300000 ∨ _; omega_using [hi]) (by rw [toNat_add_lit (by omega)]; omega)]
  simp only [argMem]
  by_cases h6 : i = 6
  · subst h6; exact Mem.readW_writeW_self32 _ _ _
  · have hi6 : i < 6 := by omega
    have hs : (0x20004 + BitVec.ofNat 64 (4 * i) : Addr).toNat + 32 / 8 ≤ (0x2001C : Addr).toNat ∨
        (0x2001C : Addr).toNat + 4 ≤ (0x20004 + BitVec.ofNat 64 (4 * i) : Addr).toNat := by
      rw [toNat_add_lit (by omega)]
      exact .inl (by show 0x20004 + 4 * i + 32 / 8 ≤ 0x2001C; omega_using [hi6])
    rw [readW_sepw (by decide) hs (by rw [toNat_add_lit (by omega)]; omega) (by decide)]
    rw [put6w_read (p := 0x20004) (by decide) _ _ _ _ _ _ i hi6]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi6]) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem satS_hash (vs : List HVar) (w : HVar) (a : List (BitVec 32)) (rd wr : List Region) :
    Spec.HmacTable.hashAt 32 (satS vs w a rd wr).mem ((0x300000 : BitVec 32).setWidth 64) = some w.G :=
  hashAt_tableOf (by decide) (held_tableOf (by decide) (satS_held vs w a rd wr)).2.1

/-- What the contracts ask of a state, but for the table. -/
macro "sat_close" : tactic => `(tactic| first
  | decide
  | rfl
  | exact Region.disjoint_of_sep (by
      simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
        BitVec.reduceSub, BitVec.reduceToNat, BitVec.toNat_ofNat]
      omega_arith)
  | bv_omega)

section
variable {vs : List HVar}

theorem key_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specKey vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  refine ⟨satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩], ?_⟩
  have a := satS_arg vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide); have a3 := a 3 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3
  have e : argAddr (satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]) 0 = 0x20004 := rfl
  have hG := satS_hash vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]
  have hheld := satS_held vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]
  have hrd : (satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]).rd = [⟨0x1000, 32⟩, ⟨0x300000, 24⟩] := rfl
  have hwr : (satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]).wr = [⟨0x2000, 384⟩, ⟨0x20004, 16⟩] := rfl
  have hesp : (satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]).gpr .esp = 0x20000 := rfl
  have hsy : (satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩]).syms = symT vs := rfl
  generalize satS vs w [0x1000, 32, 0x2000, 0x300000] [⟨0x1000, 32⟩, ⟨0x300000, 24⟩]
    [⟨0x2000, 384⟩, ⟨0x20004, 16⟩] = s at a0 a1 a2 a3 e hG hheld hrd hwr hesp hsy ⊢
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, kStack, Impl.Hkdf.X86.kFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
  simp only [a0, a1, a2, a3, e, hrd, hwr, hesp, hsy] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       rw [hS w hv]; rfl)

/-- `vg_hkdf_key`, with the tables of `vs`, meets `Spec.Hkdf.keyContract`. -/
theorem key_spec (hO : OK vs) (hS : Streams vs) :
    Verified X86.target (Impl.Hkdf.X86.key (fnsOf vs)) (specKey vs) :=
  Verified.of_correct (fun _ h => keyT_ok hO hS h) (keyT_ct hO) (key_implies hO (key_sat hO hS))

end

/-! ## `vg_hkdf_extract` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExtract (vs : List HVar) : Contract isa :=
  Spec.Hkdf.extractContract (X86.abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) xStack

/-- The contract with the table of `w`, and its index. -/
def ExtractW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (extractR w (fnsOf vs) (names vs) xStack).pre s ∧ IdxW 6 w s

/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def extractTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExtractW vs w s
  post s s' := ∀ H F, Spec.HmacTable.hashAt 32 s.mem ((arg s 6).setWidth 64) = some H →
    Spec.HmacTable.hmacOf H = some F →
    Spec.Sha256.bytesAt s'.mem ((arg s 4).setWidth 64) H.len = Spec.Hkdf.extract F
      (Spec.Sha256.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
      (Spec.Sha256.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExtractW vs w s₁ ∧ ExtractW vs w s₂ ∧ (extractR w (fnsOf vs) (names vs) xStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem extractT_ok (hO : OK vs) {s : State} (h : (extractTab vs).pre s) :
    WP isa (Impl.Hkdf.X86.extract (fnsOf vs)) s fun s' => abiPreserved s s' ∧ (extractTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  have hw := hO.2.2.2 w hv
  have nt : (arg s 6).toNat + 24 ≤ 2 ^ 32 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.mono (extract_correct hw (NoSp.of_all (extractBody_okP vs)) hp) fun s' ⟨hg, hpost⟩ =>
    ⟨hg, fun H F hH hF => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf nt hix))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  rw [w.glen]
  exact hpost

theorem extractT_ct (hO : OK vs) :
    ConstantTime isa (extractTab vs).pre (extractTab vs).pub (Impl.Hkdf.X86.extract (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact extract_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      exacts [hn.1, hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExtractFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW 6 w s) ∧ ∀ w ∈ vs, HeldW 6 w s → ExtractW vs w s

theorem extract_pre (hO : OK vs) {s : State} (h : (specExtract vs).pre s) : ExtractFacts vs s := by
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, xStack, Impl.Hkdf.X86.xFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, htop, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, -, d2, -, d3, d4, -, -, -, r3, -, -, k1, k2, k3, k4, -,
    n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hw := hO.2.2.2 w hv
  have hh := held_tableOf n4 hheld
  have hG : Spec.HmacTable.hashAt 32 s.mem ((arg s 6).setWidth 64) = some w.G := hashAt_tableOf n4 hh.2.1
  have hl : (arg s 5).toNat = w.F.H.D := (hP _ hG).1.trans w.glen
  rw [hw.blockSize] at hh
  rw [List.append_eq, List.append_nil] at hpw
  rw [hl] at hwr d1 d2 d3 d4 r3 k3 n3
  exact ⟨⟨hsp, htop, hrd, hwr, d1, d2, d3, d4, r3, k1, k2, k3, k4, n1, n2, n3, n4, tabOK_of hO.1 hpw hv, hh.1,
    hh.2.2.1, hh.2.2.2⟩, hh.2.1⟩

theorem extract_pub {s₁ s₂ : State} (h₁ : ExtractFacts vs s₁) (h₂ : ExtractFacts vs s₂)
    (h : (specExtract vs).pub s₁ s₂) : (extractTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, xStack, Impl.Hkdf.X86.xFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5, e6⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, args_of7 e0 e1 e2 e3 e4 e5 e6, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem extract_implies (hO : OK vs) (hsat : ∃ s, (specExtract vs).pre s) :
    (extractTab vs).Implies (specExtract vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    extract_pub (extract_pre hO h₁) (extract_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := extract_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86.abi, stackBelow, xStack, Impl.Hkdf.X86.xFr, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
    exact fun H F a b => hp H F a b

theorem extract_sat (hO : OK vs) : ∃ s, (specExtract vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  have hD : w.F.H.D ≤ 64 := hw.2.2.2.2.2
  refine ⟨satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩], ?_⟩
  have a := satS_arg vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide); have a6 := a 6 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5 a6
  have e : argAddr (satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]) 0 = 0x20004 := rfl
  have hG := satS_hash vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]
  have hheld := satS_held vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]
  have hrd : (satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]).rd =
      [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] := rfl
  have hwr : (satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]).wr =
      [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩] := rfl
  have hesp : (satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]).gpr .esp = 0x20000 := rfl
  have hsy : (satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩]).syms = symT vs := rfl
  have hDn : (BitVec.ofNat 32 w.F.H.D).toNat = w.F.H.D := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD])]
  generalize satS vs w [0x1000, 16, 0x2000, 16, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x300000]
    [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, w.F.H.D⟩, ⟨0x20004, 28⟩] = s
    at a0 a1 a2 a3 a4 a5 a6 e hG hheld hrd hwr hesp hsy ⊢
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, xStack, Impl.Hkdf.X86.xFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
  simp only [a0, a1, a2, a3, a4, a5, a6, e, hrd, hwr, hesp, hsy, hDn] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨w.glen.symm, by rw [hw.hmac]; rfl⟩)

/-- `vg_hkdf_extract`, with the tables of `vs`, meets `Spec.Hkdf.extractContract`. -/
theorem extract_spec (hO : OK vs) :
    Verified X86.target (Impl.Hkdf.X86.extract (fnsOf vs)) (specExtract vs) :=
  Verified.of_correct (fun _ h => extractT_ok hO h) (extractT_ct hO) (extract_implies hO (extract_sat hO))

end

/-! ## `vg_hkdf_expand` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExpand (vs : List HVar) : Contract isa :=
  Spec.Hkdf.expandContract (X86.abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) eStack

/-- The contract with the table of `w`, and its index. -/
def ExpandW (vs : List HVar) (w : HVar) (s : State) : Prop :=
  (expandR w (fnsOf vs) (names vs) eStack).pre s ∧ IdxW 5 w s

/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def expandTab (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, ExpandW vs w s
  post s s' := ∀ H S prk, Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H →
    Spec.Hkdf.streamingOf H = some S → Spec.Hkdf.Keyed S s.mem ((arg s 0).setWidth 64) prk →
    Spec.Hkdf.expand S.H H.len prk (Spec.Sha256.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
      (arg s 4).toNat = some (Spec.Sha256.bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExpandW vs w s₁ ∧ ExpandW vs w s₂ ∧ (expandR w (fnsOf vs) (names vs) eStack).pub s₁ s₂

section
variable {vs : List HVar}

theorem expandT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (expandTab vs).pre s) :
    WP isa (Impl.Hkdf.X86.expand (fnsOf vs)) s fun s' => abiPreserved s s' ∧ (expandTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  have nt : (arg s 5).toNat + 24 ≤ 2 ^ 32 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine WP.mono (expand_correct (hO.2.2.2 w hv) (NoSp.of_all (expandBody_okP vs)) hp) fun s' ⟨hg, hpost⟩ =>
    ⟨hg, fun H S prk hH hSt hK => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf nt hix))
  obtain rfl := streams_of hS hv nt hix hH hSt
  rw [w.glen]
  exact hpost prk hK

theorem expandT_ct (hO : OK vs) :
    ConstantTime isa (expandTab vs).pre (expandTab vs).pub (Impl.Hkdf.X86.expand (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact expand_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      exacts [hn.1, hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExpandFacts (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW 5 w s) ∧ ∀ w ∈ vs, HeldW 5 w s → ExpandW vs w s

theorem expand_pre (hO : OK vs) {s : State} (h : (specExpand vs).pre s) : ExpandFacts vs s := by
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, eStack, Impl.Hkdf.X86.eFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, htop, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, -, d2, -, d3, d4, -, -, -, r3, -, -, k1, k2, k3, k4, -,
    n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hw := hO.2.2.2 w hv
  have hh := held_tableOf n4 hheld
  have hG : Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some w.G := hashAt_tableOf n4 hh.2.1
  rw [hw.blockSize] at hh
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, htop, hrd, hwr, d1, d2, d3, d4, r3, k1, k2, k3, k4, n1, n2, n3, n4,
    by rw [← w.glen]; exact (hP _ hG).1, tabOK_of hO.1 hpw hv, hh.1, hh.2.2.1, hh.2.2.2⟩, hh.2.1⟩

theorem expand_pub {s₁ s₂ : State} (h₁ : ExpandFacts vs s₁) (h₂ : ExpandFacts vs s₂)
    (h : (specExpand vs).pub s₁ s₂) : (expandTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, eStack, Impl.Hkdf.X86.eFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, args_of6 e0 e1 e2 e3 e4 e5, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem expand_implies (hO : OK vs) (hsat : ∃ s, (specExpand vs).pre s) :
    (expandTab vs).Implies (specExpand vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    expand_pub (expand_pre hO h₁) (expand_pre hO h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := expand_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86.abi, stackBelow, eStack, Impl.Hkdf.X86.eFr, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
    exact fun H S prk a b c => hp H S prk a b c

theorem expand_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExpand vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD0 : 0 < w.F.H.D := w.ok.hH.hD0
  refine ⟨satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩], ?_⟩
  have a := satS_arg vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5
  have e : argAddr (satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]) 0 = 0x20004 := rfl
  have hG := satS_hash vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]
  have hheld := satS_held vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]
  have hrd : (satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]).rd =
      [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] := rfl
  have hwr : (satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]).wr =
      [⟨0x3000, 16⟩, ⟨0x20004, 24⟩] := rfl
  have hesp : (satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]).gpr .esp = 0x20000 := rfl
  have hsy : (satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩]).syms = symT vs := rfl
  generalize satS vs w [0x1000, 0x2000, 16, 0x3000, 16, 0x300000]
    [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 24⟩] [⟨0x3000, 16⟩, ⟨0x20004, 24⟩] = s
    at a0 a1 a2 a3 a4 a5 e hG hheld hrd hwr hesp hsy ⊢
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, stackBelow, eStack, Impl.Hkdf.X86.eFr, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
  simp only [a0, a1, a2, a3, a4, a5, e, hrd, hwr, hesp, hsy] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       have h16 : (16 : BitVec 32).toNat = 16 := rfl
       refine ⟨by rw [w.glen, h16]; omega_using [hD0], by rw [hS w hv]; rfl⟩)

/-- `vg_hkdf_expand`, with the tables of `vs`, meets `Spec.Hkdf.expandContract`. -/
theorem expand_spec (hO : OK vs) (hS : Streams vs) :
    Verified X86.target (Impl.Hkdf.X86.expand (fnsOf vs)) (specExpand vs) :=
  Verified.of_correct (fun _ h => expandT_ok hO hS h) (expandT_ct hO) (expand_implies hO (expand_sat hO hS))

end

end VG.Proof.Hkdf.X86
