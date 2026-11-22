module

public import VerifiedGarbage.Proof.Hkdf.AArch64.Key
public import VerifiedGarbage.Proof.Hkdf.AArch64.Extract
public import VerifiedGarbage.Proof.Hkdf.AArch64.Expand
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.Sig

/-!
# HKDF on AArch64: the contracts with the hash function as a table

As on x86-64 (`Proof/Hkdf/X86_64/Table.lean`): each function is one body,
which loads `D` and `B` from the table `hmac` and calls the table's
functions. For the variants `vs` whose tables it takes (`OK`: their
functions of the same name have the same code, their sizes fit the frames
(`HOk`), and each's streaming states are the specification's for its hash
function, `Streams`), the table of each `w` makes the body meet the
contract with `w` fixed (`keyR`, `key_correct`, `key_ct`). `keyTab` states
that contract for whichever of the tables `hmac` holds, on entry, which the
specification's contract with the tables of `vs` implies (`key_implies`).
A state meets it (`key_sat`). No instruction of the functions, or of those
they call, writes a callee-saved SIMD register (`key_kv`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.AArch64

open VG VG.AArch64
open VG.Impl.Hkdf.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf
  hashAt_tableOf put6 put6_held symT symT_distinct)

/-- What the registrations check of the variants whose tables the functions
take: the functions of the same name have the same code, there are fewer
than `2 ^ 32` names, there is one, and each's sizes fit the frames. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, HOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

/-- Each variant's streaming states are those the specification gives its
hash function (`Spec.Hkdf.streamingOf`). -/
def Streams (vs : List MdHash) : Prop := ∀ w ∈ vs, Spec.Hkdf.streamingOf w.mgf.G = some w.ok.SH

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 64 p 6 = ⟨p, 48⟩ := rfl

theorem names_eq (vs : List MdHash) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The table `hmac` (in `r`) points to holds `w`'s. -/
abbrev HeldW (r : Reg) (w : MdHash) (s : State) : Prop :=
  Abi.tableHeld 64 s.mem (s.gpr r) (FnTable.words isa s (tableOf w))

/-- The table's index, as the table of `w` holds it. -/
abbrev IdxW (r : Reg) (w : MdHash) (s : State) : Prop :=
  s.mem.readW (s.gpr r + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)

/-- The hash function a table of `w` names, and its streaming states. -/
theorem streams_of {vs : List MdHash} (hS : Streams vs) {w : MdHash} (hv : w ∈ vs) {m : Mem} {p : Addr}
    (h : m.readW (p + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G))
    {H : Spec.Mgf1.Hash} {S : Spec.Hmac.StreamingHash} (hH : Spec.HmacTable.hashAt 64 m p = some H)
    (hSt : Spec.Hkdf.streamingOf H = some S) : S = w.ok.SH := by
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf h))
  exact Option.some.inj (hSt.symm.trans (hS w hv))

/-! ## No instruction writes a callee-saved SIMD register -/

theorem icalls_kv : ∀ {ts : List (String × Prog isa)}, (∀ q ∈ ts, q.2.allInstrs keepsV = true) →
    (Code.icalls (.blr .x16) ts).allInstrs keepsV = true
  | [], _ => rfl
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_kv (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    show (Code.icalls (.blr .x16) (q :: ts)).allInstrs keepsV = true
    simp only [Code.icalls, Code.allInstrs, hq, ih, Bool.and_true]; rfl

theorem init_kv (vs : List MdHash) : ∀ q ∈ (fnsOf vs).init, q.2.allInstrs keepsV = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  exact Proof.Pbkdf2.Md.AArch64.Any.hmacInitAny_keepsV w.ok

theorem upd_kv (vs : List MdHash) : ∀ q ∈ (fnsOf vs).upd, q.2.allInstrs keepsV = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq; exact w.ok.updKeepsV

theorem fin_kv (vs : List MdHash) : ∀ q ∈ (fnsOf vs).fin, q.2.allInstrs keepsV = true := by
  intro q hq; obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq; exact w.ok.hmacFin_keepsV

theorem key_kv (vs : List MdHash) : (key (fnsOf vs)).allInstrs keepsV = true := by
  simp only [key, framed, keyMain, Code.allInstrs, icalls_kv (init_kv vs), Bool.and_true]
  rfl

/-! ## `vg_hkdf_key` -/

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specKey (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.keyContract (AArch64.abi.withTables Spec.Hkdf.keySig [("hmac", tables vs)]) kStack

/-- The contract with the table of `w`, and its index. -/
def KeyW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (keyR w (fnsOf vs) (names vs) kStack).pre s ∧ IdxW .x3 w s

/-- The contract with whichever of the tables of `vs` the table at `x3` is. -/
def keyTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, KeyW vs w s
  post s s' := ∀ H S, Spec.HmacTable.hashAt 64 s.mem (s.gpr .x3) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s'.mem (s.gpr .x2) (Spec.Sha256.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, KeyW vs w s₁ ∧ KeyW vs w s₂ ∧ (keyR w (fnsOf vs) (names vs) kStack).pub s₁ s₂

section
variable {vs : List MdHash}

theorem keyT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (keyTab vs).pre s) :
    ∃ t s', Exec isa (key (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (keyTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, hg, hpost⟩ := WP.withPreservedV (key_correct (hO.2.2.2 w hv) hp) (key_kv vs)
  refine ⟨t, s', he, hg, fun H S hH hSt => ?_⟩
  rw [streams_of hS hv hix hH hSt]
  exact hpost

theorem keyT_ct (hO : OK vs) : ConstantTime isa (keyTab vs).pre (keyTab vs).pub (key (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  exact key_ct (hO.2.2.2 w hv) (mem_names hv).1 s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def KeyFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .x3 w s) ∧ ∀ w ∈ vs, HeldW .x3 w s → KeyW vs w s

theorem key_pre (hO : OK vs) {s : State} (h : (specKey vs).pre s) : KeyFacts vs s := by
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, k1, k2, k3, n1, n2, n3, -⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  rw [List.append_eq, List.append_nil] at hpw
  exact ⟨⟨hsp, hrd, hwr, d1, d2, k1, k2, k3, n1, n2, n3, hh.1, tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem key_pub {s₁ s₂ : State} (h₁ : KeyFacts vs s₁) (h₂ : KeyFacts vs s₂) (h : (specKey vs).pub s₁ s₂) :
    (keyTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.keyContract, Spec.Hkdf.keySig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem key_implies (hO : OK vs) (hsat : ∃ s, (specKey vs).pre s) : (keyTab vs).Implies (specKey vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp => key_pub (key_pre hO h₁) (key_pre hO h₂) hp,
    hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := key_pre hO h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPost,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      AArch64.abi, AArch64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
      List.append_nil, names_eq]
    exact fun H S a b => hp H S a b

/-- The memory with the table of `w` at `0x300000`. -/
def tabMem (vs : List MdHash) (w : MdHash) : Mem :=
  put6 (fun _ => 0) 0x300000 (symT vs w.H.hmacInitAnyN) (symT vs w.H.updN)
    (symT vs w.H.hmacFinN) (BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) (BitVec.ofNat 64 w.mgf.G.len)
    (BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G))

theorem tabMem_held (vs : List MdHash) (w : MdHash) (s : State) (hs : s.syms = symT vs) :
    Abi.tableHeld 64 (tabMem vs w) 0x300000 (FnTable.words isa s (tableOf w)) := by
  rw [Proof.HmacTable.AArch64.words_tableOf, hs]
  exact put6_held (ws := [symT vs w.H.hmacInitAnyN, symT vs w.H.updN, symT vs w.H.hmacFinN,
    BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G), BitVec.ofNat 64 w.mgf.G.len,
    BitVec.ofNat 64 (Spec.HmacTable.blockSize w.mgf.G)]) rfl

/-- A state meeting the contract: `PRK` (32 bytes) at `0x1000`, `key` at
`0x2000`, the table of a variant of `vs` at `0x300000`. -/
def keySat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 0x2000 | .x3 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 32⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x2000, 384⟩]
  syms := symT vs

theorem key_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specKey vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  refine ⟨keySat vs w, ?_⟩
  sig_pre [Spec.Hkdf.keyContract, Spec.Hkdf.keySig, Spec.Hkdf.keyPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, kStack, kFr, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (keySat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (keySat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
  simp only [keySat] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (keySat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       rw [hS w hv]; rfl)

/-- `vg_hkdf_key`, with the tables of `vs`, meets `Spec.Hkdf.keyContract`. -/
theorem key_spec (hO : OK vs) (hS : Streams vs) : Verified AArch64.target (key (fnsOf vs)) (specKey vs) :=
  Verified.of_correct (fun _ h => keyT_ok hO hS h) (keyT_ct hO) (key_implies hO (key_sat hO hS))

end

/-! ## `vg_hkdf_extract` -/

open Extract (extractR xStack)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExtract (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.extractContract (AArch64.abi.withTables Spec.Hkdf.extractSig [("hmac", tables vs)]) xStack

/-- The contract with the table of `w`, and its index. -/
def ExtractW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (extractR w (fnsOf vs) (names vs) xStack).pre s ∧ IdxW .x6 w s

/-- The contract with whichever of the tables of `vs` the table at `x6` is. -/
def extractTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, ExtractW vs w s
  post s s' := ∀ H F, Spec.HmacTable.hashAt 64 s.mem (s.gpr .x6) = some H → Spec.HmacTable.hmacOf H = some F →
    Spec.Sha256.bytesAt s'.mem (s.gpr .x4) H.len = Spec.Hkdf.extract F
      (Spec.Sha256.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (Spec.Sha256.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExtractW vs w s₁ ∧ ExtractW vs w s₂ ∧ (extractR w (fnsOf vs) (names vs) xStack).pub s₁ s₂

/-- The HMAC of a variant's hash function. -/
theorem hmac_of {vs : List MdHash} (hS : Streams vs) {w : MdHash} (hv : w ∈ vs) :
    Spec.HmacTable.hmacOf w.mgf.G = some w.ok.SH.H :=
  Spec.Hkdf.streamingOf_hmacOf _ _ (hS w hv)

theorem extract_kv (vs : List MdHash) : (extract (fnsOf vs)).allInstrs keepsV = true := by
  simp only [extract, framed, extractMain, tcall, Code.allInstrs, icalls_kv (init_kv vs), icalls_kv (upd_kv vs),
    icalls_kv (fin_kv vs), Bool.and_true]
  rfl

section
variable {vs : List MdHash}

theorem extractT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (extractTab vs).pre s) :
    ∃ t s', Exec isa (extract (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (extractTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, hg, hpost⟩ :=
    WP.withPreservedV (Extract.extract_correct (hO.2.2.2 w hv) hp) (extract_kv vs)
  refine ⟨t, s', he, hg, fun H F hH hF => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  obtain rfl := Option.some.inj (hF.symm.trans (hmac_of hS hv))
  rw [w.mgf.len]
  exact hpost

theorem extractT_ct (hO : OK vs) :
    ConstantTime isa (extractTab vs).pre (extractTab vs).pub (extract (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact Extract.extract_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      exacts [hn.1, hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExtractFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .x6 w s) ∧ ∀ w ∈ vs, HeldW .x6 w s → ExtractW vs w s

theorem extract_pre (hO : OK vs) (hS : Streams vs) {s : State} (h : (specExtract vs).pre s) : ExtractFacts vs s := by
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hG : Spec.HmacTable.hashAt 64 s.mem (s.gpr .x6) = some w.mgf.G := hashAt_tableOf hh.2.1
  have hB : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
    simp only [Spec.HmacTable.blockSize, hmac_of hS hv, Option.map_some, Option.getD_some]; exact w.ok.hB
  rw [List.append_eq, List.append_nil] at hpw
  refine ⟨⟨hsp, hrd, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4,
    by rw [(hP _ hG).1, w.mgf.len], hh.1, by rw [hh.2.2.2, hB], tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem extract_pub {s₁ s₂ : State} (h₁ : ExtractFacts vs s₁) (h₂ : ExtractFacts vs s₂)
    (h : (specExtract vs).pub s₁ s₂) : (extractTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5, e6⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, e6, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem extract_implies (hO : OK vs) (hS : Streams vs) (hsat : ∃ s, (specExtract vs).pre s) :
    (extractTab vs).Implies (specExtract vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    extract_pub (extract_pre hO hS h₁) (extract_pre hO hS h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := extract_pre hO hS h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPost,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
    exact fun H F a b => hp H F a b

/-- A state meeting the contract: the salt and the input keying material
(16 bytes each) at `0x1000` and `0x2000`, `PRK` at `0x3000`, the table of a
variant of `vs` at `0x300000`. -/
def extractSat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 16 | .x4 => 0x3000
    | .x5 => BitVec.ofNat 64 w.H.D | .x6 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 16⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x3000, w.H.D⟩]
  syms := symT vs

theorem extract_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExtract vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD : w.H.D ≤ 64 := by have := w.ok.sizes.DN; have := w.ok.N_le; omega_arith
  refine ⟨extractSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.extractContract, Spec.Hkdf.extractSig, Spec.Hkdf.extractPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, xStack, xFr, xWork, work, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (extractSat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (extractSat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
  have h5 : ((extractSat vs w).gpr .x5).toNat = w.H.D := by
    show (BitVec.ofNat 64 w.H.D).toNat = _; rw [BitVec.toNat_ofNat]; omega_using [hD]
  simp only [extractSat] at hG h5 ⊢
  simp only [h5]
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (extractSat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [w.mgf.len], by rw [hmac_of hS hv]; rfl⟩)

/-- `vg_hkdf_extract`, with the tables of `vs`, meets `Spec.Hkdf.extractContract`. -/
theorem extract_spec (hO : OK vs) (hS : Streams vs) :
    Verified AArch64.target (extract (fnsOf vs)) (specExtract vs) :=
  Verified.of_correct (fun _ h => extractT_ok hO hS h) (extractT_ct hO) (extract_implies hO hS (extract_sat hO hS))

end

/-! ## `vg_hkdf_expand` -/

open Expand (expandR eStack)

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specExpand (vs : List MdHash) : Contract isa :=
  Spec.Hkdf.expandContract (AArch64.abi.withTables Spec.Hkdf.expandSig [("hmac", tables vs)]) eStack

/-- The contract with the table of `w`, and its index. -/
def ExpandW (vs : List MdHash) (w : MdHash) (s : State) : Prop :=
  (expandR w (fnsOf vs) (names vs) eStack).pre s ∧ IdxW .x5 w s

/-- The contract with whichever of the tables of `vs` the table at `x5` is. -/
def expandTab (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, ExpandW vs w s
  post s s' := ∀ H S prk, Spec.HmacTable.hashAt 64 s.mem (s.gpr .x5) = some H → Spec.Hkdf.streamingOf H = some S →
    Spec.Hkdf.Keyed S s.mem (s.gpr .x0) prk →
    Spec.Hkdf.expand S.H H.len prk (Spec.Sha256.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (s.gpr .x4).toNat =
      some (Spec.Sha256.bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ := ∃ w ∈ vs, ExpandW vs w s₁ ∧ ExpandW vs w s₂ ∧ (expandR w (fnsOf vs) (names vs) eStack).pub s₁ s₂

theorem expand_kv (vs : List MdHash) : (expand (fnsOf vs)).allInstrs keepsV = true := by
  simp only [expand, framed, expandMain, block, tcall, Code.allInstrs, icalls_kv (upd_kv vs), icalls_kv (fin_kv vs),
    Bool.and_true]
  rfl

section
variable {vs : List MdHash}

theorem expandT_ok (hO : OK vs) (hS : Streams vs) {s : State} (h : (expandTab vs).pre s) :
    ∃ t s', Exec isa (expand (fnsOf vs)) s t s' ∧ abiPreserved s s' ∧ (expandTab vs).post s s' := by
  obtain ⟨w, hv, hp, hix⟩ := h
  obtain ⟨t, s', he, hg, hpost⟩ :=
    WP.withPreservedV (Expand.expand_correct (hO.2.2.2 w hv) hp) (expand_kv vs)
  refine ⟨t, s', he, hg, fun H S prk hH hSt hK => ?_⟩
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hix))
  obtain rfl := streams_of hS hv hix hH hSt
  rw [w.mgf.len]
  exact hpost prk hK

theorem expandT_ct (hO : OK vs) :
    ConstantTime isa (expandTab vs).pre (expandTab vs).pub (expand (fnsOf vs)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, p₁, p₂, hpub⟩ e₁ e₂
  have hn := mem_names hv
  exact Expand.expand_ct (hO.2.2.2 w hv) (fun n h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      exacts [hn.2.1, hn.2.2])
    s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract on entry. -/
def ExpandFacts (vs : List MdHash) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW .x5 w s) ∧ ∀ w ∈ vs, HeldW .x5 w s → ExpandW vs w s

theorem expand_pre (hO : OK vs) (hS : Streams vs) {s : State} (h : (specExpand vs).pre s) : ExpandFacts vs s := by
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4, hP⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  have hh := held_tableOf hheld
  have hG : Spec.HmacTable.hashAt 64 s.mem (s.gpr .x5) = some w.mgf.G := hashAt_tableOf hh.2.1
  have hB : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
    simp only [Spec.HmacTable.blockSize, hmac_of hS hv, Option.map_some, Option.getD_some]; exact w.ok.hB
  rw [List.append_eq, List.append_nil] at hpw
  refine ⟨⟨hsp, hrd, hwr, d1, d2, d3, k1, k2, k3, k4, n1, n2, n3, n4,
    by rw [← w.mgf.len]; exact (hP _ hG).1, hh.1, hh.2.2.1, by rw [hh.2.2.2, hB], tabOK_of hO.1 hpw hv⟩, hh.2.1⟩

theorem expand_pub {s₁ s₂ : State} (h₁ : ExpandFacts vs s₁) (h₂ : ExpandFacts vs s₂)
    (h : (specExpand vs).pub s₁ s₂) : (expandTab vs).pub s₁ s₂ := by
  sig_pub [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq] at h
  obtain ⟨hsp, hn, hT, e0, e1, e2, e3, e4, e5⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  exact ⟨w, hv, f₁ w hv hh, h₂.2 w hv ((hT _ _ rfl rfl _ (List.mem_map_of_mem hv)).mp hh),
    hsp, e0, e1, e2, e3, e4, e5, hn⟩

/-- The contract with the tables of `vs`, given a state that meets it. -/
theorem expand_implies (hO : OK vs) (hS : Streams vs) (hsat : ∃ s, (specExpand vs).pre s) :
    (expandTab vs).Implies (specExpand vs) := by
  refine ⟨fun s h => ?_, fun s s' h hp => ?_, fun s₁ s₂ h₁ h₂ hp =>
    expand_pub (expand_pre hO hS h₁) (expand_pre hO hS h₂) hp, hsat⟩
  · obtain ⟨⟨w, hv, hh⟩, f⟩ := expand_pre hO hS h
    exact ⟨w, hv, f w hv hh⟩
  · sig_post [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPost,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
    exact fun H S prk a b c => hp H S prk a b c

/-- A state meeting the contract: the states at `0x1000`, `info` (16 bytes)
at `0x2000`, 16 bytes of `out` at `0x3000`, the table of a variant of `vs`
at `0x300000`. -/
def expandSat (vs : List MdHash) (w : MdHash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 16 | .x3 => 0x3000 | .x4 => 16 | .x5 => 0x300000 | _ => 0
  sp := 0x20000
  mem := tabMem vs w
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 16⟩, ⟨0x300000, 48⟩]
  wr := [⟨0x3000, 16⟩]
  syms := symT vs

theorem expand_sat (hO : OK vs) (hS : Streams vs) : ∃ s, (specExpand vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hD0 : 0 < w.H.D := w.ok.sizes.D0
  refine ⟨expandSat vs w, ?_⟩
  sig_pre [Spec.Hkdf.expandContract, Spec.Hkdf.expandSig, Spec.Hkdf.expandPre,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    AArch64.abi, AArch64.argRegs, stackBelow, eStack, eFr, eWork, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left', tableRegion_eq,
    List.append_nil, names_eq]
  have hh := held_tableOf (tabMem_held vs w (expandSat vs w) rfl)
  have hG : Spec.HmacTable.hashAt 64 (expandSat vs w).mem 0x300000 = some w.mgf.G := hashAt_tableOf hh.2.1
  simp only [expandSat] at hG ⊢
  sig_and_intros
  all_goals first
    | decide
    | rfl
    | exact ⟨tableOf w, List.mem_map_of_mem hv, tabMem_held vs w (expandSat vs w) rfl⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | exact Region.disjoint_of_sep (by
        simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega)
    | bv_omega
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       have h16 : (16 : BitVec 64).toNat = 16 := rfl
       refine ⟨by rw [w.mgf.len, h16]; omega_using [hD0], by rw [hS w hv]; rfl⟩)

/-- `vg_hkdf_expand`, with the tables of `vs`, meets `Spec.Hkdf.expandContract`. -/
theorem expand_spec (hO : OK vs) (hS : Streams vs) :
    Verified AArch64.target (expand (fnsOf vs)) (specExpand vs) :=
  Verified.of_correct (fun _ h => expandT_ok hO hS h) (expandT_ct hO) (expand_implies hO hS (expand_sat hO hS))

end

end VG.Proof.Hkdf.AArch64
