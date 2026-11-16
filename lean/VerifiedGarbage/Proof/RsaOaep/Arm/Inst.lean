module

public import VerifiedGarbage.Proof.RsaOaep.Arm.DecVerified
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecBase
public import VerifiedGarbage.Proof.HashTable.Arm
public import VerifiedGarbage.Proof.RsaOaep.Arm.DecP
public import VerifiedGarbage.Proof.Rsa.PreKey
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBody
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncChk
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.RsaOaep.Arm.EncBase

/-! ### `RsaOaep.Arm.DecSat`, which only this module used -/

section

/-!
# RSAES-OAEP decryption on ARMv7: the contract is satisfiable

A state that meets `decryptMdTablesContract` (`dec_sat`), with both hash
functions the table of any `w` of `vs`: a modulus of 64 bytes, `e`, `p`,
`q`, `dP`, `dQ` and `qInv` of one byte, an empty label, the working space it
needs, the stack arguments at `0x8000`, and the table, both arguments, at
`0x300000` (`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Dec

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held held_twL withTable_below)
open VG.Proof.HashTable (symsOf32_distinct2)

/-- The state, but for the table. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 0x40 else
    if a = 0x8005 then 0x21 else
    if a = 0x8008 then 1 else
    if a = 0x800d then 0x31 else
    if a = 0x8010 then 1 else
    if a = 0x8015 then 0x32 else
    if a = 0x8018 then 1 else
    if a = 0x801d then 0x33 else
    if a = 0x8020 then 1 else
    if a = 0x8025 then 0x34 else
    if a = 0x8028 then 1 else
    if a = 0x802d then 0x35 else
    if a = 0x8030 then 1 else
    if a = 0x8035 then 0x36 else
    if a = 0x803d then 0x37 else
    if a = 0x8040 then 0x40 else
    if a = 0x8046 then 1 else
    if a = 0x8048 then 0x20 else
    if a = 0x8049 then 8 else
    if a = 0x804e then 0x30 else
    if a = 0x8052 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩, ⟨0x8000, 84⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem dec_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  refine ⟨withTable satState vs w, ?_⟩
  obtain hA : ∀ j < 21, (stackArgAddr satState j).toNat + 4 ≤ 0x300000 := by decide
  obtain a0 : stackArg (withTable satState vs w) 0 = 64 := (withTable_below _ _ _ (hA 0 (by decide))).trans (by decide)
  obtain a1 : stackArg (withTable satState vs w) 1 = 0x2100 := (withTable_below _ _ _ (hA 1 (by decide))).trans (by decide)
  obtain a2 : stackArg (withTable satState vs w) 2 = 1 := (withTable_below _ _ _ (hA 2 (by decide))).trans (by decide)
  obtain a3 : stackArg (withTable satState vs w) 3 = 0x3100 := (withTable_below _ _ _ (hA 3 (by decide))).trans (by decide)
  obtain a4 : stackArg (withTable satState vs w) 4 = 1 := (withTable_below _ _ _ (hA 4 (by decide))).trans (by decide)
  obtain a5 : stackArg (withTable satState vs w) 5 = 0x3200 := (withTable_below _ _ _ (hA 5 (by decide))).trans (by decide)
  obtain a6 : stackArg (withTable satState vs w) 6 = 1 := (withTable_below _ _ _ (hA 6 (by decide))).trans (by decide)
  obtain a7 : stackArg (withTable satState vs w) 7 = 0x3300 := (withTable_below _ _ _ (hA 7 (by decide))).trans (by decide)
  obtain a8 : stackArg (withTable satState vs w) 8 = 1 := (withTable_below _ _ _ (hA 8 (by decide))).trans (by decide)
  obtain a9 : stackArg (withTable satState vs w) 9 = 0x3400 := (withTable_below _ _ _ (hA 9 (by decide))).trans (by decide)
  obtain a10 : stackArg (withTable satState vs w) 10 = 1 := (withTable_below _ _ _ (hA 10 (by decide))).trans (by decide)
  obtain a11 : stackArg (withTable satState vs w) 11 = 0x3500 := (withTable_below _ _ _ (hA 11 (by decide))).trans (by decide)
  obtain a12 : stackArg (withTable satState vs w) 12 = 1 := (withTable_below _ _ _ (hA 12 (by decide))).trans (by decide)
  obtain a13 : stackArg (withTable satState vs w) 13 = 0x3600 := (withTable_below _ _ _ (hA 13 (by decide))).trans (by decide)
  obtain a14 : stackArg (withTable satState vs w) 14 = 0 := (withTable_below _ _ _ (hA 14 (by decide))).trans (by decide)
  obtain a15 : stackArg (withTable satState vs w) 15 = 0x3700 := (withTable_below _ _ _ (hA 15 (by decide))).trans (by decide)
  obtain a16 : stackArg (withTable satState vs w) 16 = 64 := (withTable_below _ _ _ (hA 16 (by decide))).trans (by decide)
  obtain a17 : stackArg (withTable satState vs w) 17 = 0x10000 := (withTable_below _ _ _ (hA 17 (by decide))).trans (by decide)
  obtain a18 : stackArg (withTable satState vs w) 18 = 0x820 := (withTable_below _ _ _ (hA 18 (by decide))).trans (by decide)
  obtain a19 : stackArg (withTable satState vs w) 19 = 0x300000 := (withTable_below _ _ _ (hA 19 (by decide))).trans (by decide)
  obtain a20 : stackArg (withTable satState vs w) 20 = 0x300000 := (withTable_below _ _ _ (hA 20 (by decide))).trans (by decide)
  obtain e : stackArgAddr (withTable satState vs w) 0 = 0x8000 := show stackArgAddr satState 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argRegs, reduceClassify, Loc.val]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, e]
  sig_pre [Spec.RsaOaep.decryptMdTablesContract, Spec.RsaOaep.decryptMdTablesSig, Spec.RsaOaep.decryptSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
    abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-! ## Decryption with the key's precomputed values -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)
open VG.Proof.HashTable (putWs32 add4_toNat)

/-- The stack arguments of `satStateP`: the key (`keyMem`'s), an empty
label, a 64-byte ciphertext, a working space of 2080 words, both tables at
`0x300000`, and `pre` at `0x4800`. -/
def satArgsP : List Nat :=
  [64, 0x2100, 1, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x3600, 0, 0x3700, 64, 0x10000,
    0x820, 0x300000, 0x300000, 0x4800, 24]

/-- The memory of `satStateP`: the stack arguments from `0x8000`, and the
key. -/
def satMemP (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x8000 i && Nat.blt i 0x805C then
    BitVec.ofNat 8 (satArgsP.getD ((i - 0x8000) / 4) 0 / 256 ^ ((i - 0x8000) % 4))
  else bif keyIn i then keyMem a else 0

/-- A state meeting the precomputed decryption's precondition but for the
tables: the key `keyMem` holds (a 512-bit modulus at `0x2000`, 256-bit
primes at `0x4200` and `0x4300` and `pre` at `0x4800`), one-byte `e`. -/
def satStateP : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem := satMemP
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩, ⟨0x4600, 32⟩,
    ⟨0x3600, 0⟩, ⟨0x3700, 64⟩, ⟨0x4800, 192⟩, ⟨0x300000, 44⟩, ⟨0x300000, 44⟩, ⟨0x8000, 92⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x10000, 2080 * 8⟩]

theorem satP_args : ∀ j < 23, stackArg satStateP j = BitVec.ofNat 32 (satArgsP.getD j 0) := by decide

/-- Below the words `putWs32` writes, a byte as before. -/
theorem putWs32_byte {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)}, a.toNat < p.toNat →
    p.toNat + 4 * ws.length < 2 ^ 64 → putWs32 m p ws a = m a
  | _, [], _, _ => rfl
  | p, w :: ws, h, hp => by
    simp only [List.length_cons] at hp
    obtain h4 := add4_toNat (p := p) (by omega_using [hp])
    simp only [putWs32]
    rw [putWs32_byte (by rw [h4]; omega_using [h]) (by rw [h4]; omega_using [hp])]
    obtain hne : ¬ (a - p).toNat < 32 / 8 := by
      rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [hp]
    simp only [Mem.writeW, Mem.write, hne, ↓reduceIte]

theorem satP_key (vs : List TVar) (w : TVar) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x2000 64)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4200 32)
      (Spec.Rsa.bytesAt (withTable satStateP vs w).mem 0x4300 32) =
    some (Spec.Rsa.wordsAt (withTable satStateP vs w).mem 0x4800 24) :=
  key_pre_of fun a ha => by
    obtain hk : a.toNat < 0x48C0 := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha; omega
    obtain h2 : (Nat.ble 0x8000 a.toNat && Nat.blt a.toNat 0x805C) = false := by
      rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, Nat.ble_eq] at h; omega
    show putWs32 satMemP 0x300000 (VG.Proof.HashTable.Arm.twL vs w) a = keyMem a
    rw [putWs32_byte (by show a.toNat < 0x300000; omega_using [hk]) (VG.Proof.HashTable.Arm.twL_room vs w)]
    show (bif _ then _ else _) = _
    rw [h2, Bool.cond_false, ha, Bool.cond_true]

theorem dec_satP {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (specP (tables vs)).pre s := by
  refine ⟨withTable satStateP vs w, ?_⟩
  obtain hA : ∀ j < 23, (stackArgAddr satStateP j).toNat + 4 ≤ 0x300000 := by decide
  obtain hb : ∀ j < 23, stackArg (withTable satStateP vs w) j = BitVec.ofNat 32 (satArgsP.getD j 0) :=
    fun j hj => (withTable_below _ _ _ (hA j hj)).trans (satP_args j hj)
  obtain e : stackArgAddr (withTable satStateP vs w) 0 = 0x8000 := show stackArgAddr satStateP 0 = _ by decide
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  simp only [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide), hb 8 (by decide), hb 9 (by decide), hb 10 (by decide),
    hb 11 (by decide), hb 12 (by decide), hb 13 (by decide), hb 14 (by decide), hb 15 (by decide),
    hb 16 (by decide), hb 17 (by decide), hb 18 (by decide), hb 19 (by decide), hb 20 (by decide),
    hb 21 (by decide), hb 22 (by decide), e, satArgsP]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaOaep.decryptPrecomputedMdTablesContract, Spec.RsaOaep.decryptPrecomputedMdTablesSig,
    Spec.RsaOaep.decryptSig, Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns,
    Abi.withTables, Sig.wordIndex, abi, argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact satP_key vs w)
    | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
    | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.Arm.Dec

end

end

/-! ### `RsaOaep.Arm.EncVerified`, which only this module used -/

section

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: verified

The frames around the body (`wrap_ok`, `wrap_ct`) and the result as the
shared contract states it, for the label's hash function the one whose table
the stack argument 12 is and MGF1's the one whose table the stack argument
13 is (`tabFacts_entered`): `vg_rsa_oaep_encrypt_precomputed`, calling a
precomputed public operation `c`, with both hash functions any of the tables
of `vs`, is verified, given a state that meets the contract (`EncSat.lean`):
`encrypt_verified`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm VG.Impl.RsaOaep.Arm VG.Proof.RsaPkcs1Sig.Arm VG.Proof.RsaPss.Arm VG.Proof.RsaOaep.Arm
open VG.Impl.RsaPss.Arm (frameBytes)
open VG.Proof.HashTable.Arm (TVar tables tableOf fnsOf names Coh held_tableOf hashAt_tableOf tabFacts_entered)

variable (vs : List TVar)

/-- The code, calling `c`, with both hash functions any of the tables of `vs`. -/
abbrev encryptCode (c : PdImpl) : Prog isa := encryptPrecomputed (fnsOf vs) c.name c.code

/-- The contract, with both hash functions each one of the tables of `vs`. -/
abbrev espec : Contract isa := spec (tables vs)

variable {vs}

/-- The public parameters for MGF1's table of `w` and the label's hash
function's of `w₁`, with their functions where `s'` has them. -/
abbrev epw (s s' : State) (w w₁ : TVar) : EP :=
  ep s (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN)
    (TabFacts w.g.H (fnsOf vs) (stackArg s 13) (s'.syms w.g.H.initN) (s'.syms w.g.H.updN) (s'.syms w.g.H.finN))
    (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN) (s'.syms w₁.g.H.finN)
    (TabFacts w₁.g.H (fnsOf vs) (stackArg s 12) (s'.syms w₁.g.H.initN) (s'.syms w₁.g.H.updN)
      (s'.syms w₁.g.H.finN))

theorem spec_sp {s : State} (hs : (espec vs).pre s) : stackBytes ≤ s.sp.toNat := by
  enc_pre at hs
  exact hs.1

theorem fne_of {w : TVar} (hw : w ∈ vs) : (fnsOf vs).init ≠ [] ∧ (fnsOf vs).upd ≠ [] ∧ (fnsOf vs).fin ≠ [] := by
  have := List.ne_nil_of_mem hw
  simp only [fnsOf, ne_eq, List.map_eq_nil_iff]
  exact ⟨this, this, this⟩

/-- The entry state, for the tables of `w` at the stack argument 13 and `w₁`
at 12, with the functions where `s'` has them (`s'` has them where `s`
does). -/
theorem entered_state (hc : Coh vs) {s s' : State} (hs : (espec vs).pre s) {w w₁ : TVar} (hw : w ∈ vs)
    (hw₁ : w₁ ∈ vs) (hh : Abi.tableHeld 32 s.mem (State.addr (stackArg s 13)) (FnTable.words isa s (tableOf w)))
    (hhL : Abi.tableHeld 32 s.mem (State.addr (stackArg s 12)) (FnTable.words isa s (tableOf w₁)))
    (hsy : ∀ n ∈ names vs, s.syms n = s'.syms n) :
    Sy (S w₁.g (epw (vs := vs) s s' w w₁)) (entered frameBytes s) (entered frameBytes s) := by
  obtain ⟨-, -, hpw, hfitL, hfit⟩ := spec_tab hs
  obtain hpw' := hpw.sublist (List.sublist_append_left _ _)
  obtain hsp' : 56 + frameBytes ≤ s.sp.toNat := by have := spec_sp hs; simp only [stackBytes] at this; omega_using [this]
  obtain hHa := hashAt_tableOf hfitL (held_tableOf hfitL hhL).2.1
  obtain ok := (in_of_pre (ai := 0) (au := 0) (af := 0) (T := fun _ => True) (aiL := 0) (auL := 0) (afL := 0)
    (TL := fun _ => True) hs hHa trivial trivial).ok
  rw [ep_lay] at ok
  obtain hn := Proof.HashTable.Arm.mem_names hw
  obtain hnL := Proof.HashTable.Arm.mem_names hw₁
  obtain tf := tabFacts_entered ok hsp' (p := stackArg s 13) (by simp [ep]) hfit hc hpw' hw hh
  obtain tfL := tabFacts_entered ok hsp' (p := stackArg s 12) (by simp [ep]) hfitL hc hpw' hw₁ hhL
  rw [hsy _ hn.1, hsy _ hn.2.1, hsy _ hn.2.2] at tf
  rw [hsy _ hnL.1, hsy _ hnL.2.1, hsy _ hnL.2.2] at tfL
  obtain hi := in_of_pre (ai := s'.syms w.g.H.initN) (au := s'.syms w.g.H.updN) (af := s'.syms w.g.H.finN)
    (aiL := s'.syms w₁.g.H.initN) (auL := s'.syms w₁.g.H.updN) (afL := s'.syms w₁.g.H.finN) hs hHa tf tfL
  rw [w₁.g.glen] at hi
  exact ⟨⟨hi, ⟨hi.ok, hi.ok.sp, rfl, rfl, Frame.refl _ _⟩⟩, rfl⟩

theorem code_ok (hc : Coh vs) (c : PdImpl) {s : State} (hs : (espec vs).pre s) :
    WP isa (encryptCode vs c) s fun t => abiPreserved s t ∧ (espec vs).post s t := by
  obtain ⟨⟨T₁, hT₁, hhL⟩, ⟨T, hT, hh⟩, -, hfitL, hfit⟩ := spec_tab hs
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain hidx := (held_tableOf hfit hh).2.1
  obtain hidxL := (held_tableOf hfitL hhL).2.1
  obtain st := entered_state hc hs hw hw₁ hh hhL (s' := s) fun _ _ => rfl
  have hin := st.1.1
  obtain hsp := spec_sp hs
  obtain hsp' : 56 + frameBytes ≤ s.sp.toNat := by simp only [stackBytes] at hsp; omega_using [hsp]
  refine WP.mono (wrap_ok (by decide) (by omega_using [hsp']) (W := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).W)
    (Q := fun r m => Res w₁.g w.g (epw (vs := vs) s s w w₁) (entered frameBytes s) m r) (fun r hr => ?_)
    (WP.mono ((body_vp w₁.g (epw (vs := vs) s s w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).wp _ _ st)
      fun u hu => ⟨hu.1.1.2.frame, hu.1.2⟩)) fun t ⟨abi, res⟩ => ⟨abi, ?_⟩
  · rw [pushRegion_eq (F := frameBytes) (A := 56) (argv := (epw (vs := vs) s s w w₁).argv)
      (ro := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).ro) (rw := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).rw) hsp']
    exact hin.ok.push_apart r hr
  · sig_post [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    intro H G hH hG
    rw [show BitVec.setWidth 64 (stackArg s 12) = State.addr (stackArg s 12) from rfl, hashAt_tableOf hfitL hidxL,
      Option.some.injEq] at hH
    rw [show BitVec.setWidth 64 (stackArg s 13) = State.addr (stackArg s 13) from rfl, hashAt_tableOf hfit hidx,
      Option.some.injEq] at hG
    subst hH hG
    rw [BitVec.setWidth_append_eq_right]
    obtain ro := fun {R : Region} (hR : R ∈ ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).ro) =>
      entered_ro (F := frameBytes) (A := 56) (argv := (epw (vs := vs) s s w w₁).argv)
        (rw := ((epw (vs := vs) s s w w₁).lay w₁.g.H.D).rw) hin.ok hsp' hR
    obtain hL : labB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).LAB) (by simp)
    obtain hM : msgB (epw (vs := vs) s s w w₁) (entered frameBytes s) =
        Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat :=
      ro (R := (epw (vs := vs) s s w w₁).MSG) (by simp)
    obtain hS : seedB w₁.g (epw (vs := vs) s s w w₁) (entered frameBytes s) = Spec.Rsa.bytesAt s.mem
        (State.addr (stackArg s 6)) w₁.g.H.D := ro (R := (epw (vs := vs) s s w w₁).SEED w₁.g.H.D) (by simp)
    unfold Res at res
    rw [hL, hM, hS] at res
    rw [w₁.g.glen]
    exact res

theorem map_toNat_inj {w : Nat} {a b : List (BitVec w)} (hab : a.map (·.toNat) = b.map (·.toNat)) : a = b :=
  (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hab

theorem code_ct (hc : Coh vs) (c : PdImpl) : ConstantTime isa (espec vs).pre (espec vs).pub (encryptCode vs c) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨T₁, hT₁, hhL₁⟩, ⟨T, hT, hh₁⟩, -, -, -⟩ := spec_tab h₁
  obtain ⟨w₁, hw₁, rfl⟩ := List.mem_map.mp hT₁
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain hsp1 := spec_sp h₁
  sig_pub [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val] at hp
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq] at hp
  obtain ⟨hsp, hsy, htabL, htab, hl, h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
    a13⟩ := hp
  obtain hh₂ := (htab _ _ rfl rfl _ hT).mp hh₁
  obtain hhL₂ := (htabL _ _ rfl rfl _ hT₁).mp hhL₁
  obtain hsy' : ∀ n ∈ names vs, s₂.syms n = s₁.syms n := fun n hn =>
    (hsy n (List.mem_append_left _ hn)).symm
  obtain hep : epw (vs := vs) s₁ s₁ w w₁ = epw (vs := vs) s₂ s₁ w w₁ := by
    obtain ⟨hab, hw⟩ := List.append_inj hl (by simp [bytesAt_length, h3, a1])
    obtain ⟨hn, he⟩ := List.append_inj (map_toNat_inj hab) (by simp [bytesAt_length, h3])
    obtain hw' := map_toNat_inj hw
    simp only [ep]
    rw [hsp, h0, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]
    rw [h2, h3] at hn
    rw [a0, a1] at he
    rw [a10, a11] at hw'
    rw [show State.addr (s₂.gpr .r2) = BitVec.setWidth 64 (s₂.gpr .r2) from rfl, hn,
      show State.addr (stackArg s₂ 0) = BitVec.setWidth 64 (stackArg s₂ 0) from rfl, he,
      show State.addr (stackArg s₂ 10) = BitVec.setWidth 64 (stackArg s₂ 10) from rfl, hw']
  refine (wrap_ct (F := frameBytes) (by decide) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b hh => by rw [hh.1, hh.2]; exact hsp)
    (fun a b hh => by rw [hh.1]; simp only [stackBytes] at hsp1; omega_using [hsp1]) ?_
    s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  refine (body_vp w₁.g (epw (vs := vs) s₁ s₁ w w₁) w.g (fun _ x => x) (fun _ x => x) (fne_of hw) c).ct.mono ?_
    fun _ _ _ => trivial
  rintro a b ⟨x, y, ⟨hx, hy⟩, ha, hb⟩
  rw [ha, hb, hx, hy]
  exact ⟨_, _, entered_state hc h₁ hw hw₁ hh₁ hhL₁ (s' := s₁) (fun _ _ => rfl),
    by rw [hep]; exact entered_state hc h₂ hw hw₁ hh₂ hhL₂ (s' := s₁) hsy'⟩

/-- `vg_rsa_oaep_encrypt_precomputed`, calling `c`, with both hash functions
any of the tables of `vs`, meets the shared contract (satisfiable,
`EncSat.lean`). -/
theorem encrypt_verified (hc : Coh vs) (hsat : ∃ s, (espec vs).pre s) (c : PdImpl) :
    Verified target (encryptCode vs c) (espec vs) :=
  ⟨fun _ hs => let ⟨t, s', he, hq⟩ := code_ok hc c hs; ⟨t, s', he, hq.1, hq.2⟩, code_ct hc c, hsat⟩

end VG.Proof.RsaOaep.Arm.Enc

end

end

/-! ### `RsaOaep.Arm.EncSat`, which only this module used -/

section

/-!
# RSAES-OAEP encryption with a precomputed public key on ARMv7: the contract is satisfiable

A state that meets `encryptMdTablesContract` (`encrypt_sat`), with both hash
functions the table of any `w` of `vs`: a modulus of 64 bytes, `e` of one
byte, an empty label and message, the seed of the hash function's digest
length, the working space it needs, the precomputed values' 16 words, the
stack arguments at `0x8000`, and the table, both arguments, at `0x300000`
(`withTable`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Enc

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables tableOf names withTable withTable_held held_twL withTable_below hashAt_tableOf
  held_tableOf)
open VG.Proof.HashTable (symsOf32_distinct2)

/-- The state, for a seed of `D` bytes, but for the table. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x2000 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x21 else
    if a = 0x8004 then 1 else
    if a = 0x8009 then 0x30 else
    if a = 0x8011 then 0x31 else
    if a = 0x8019 then 0x32 else
    if a = 0x801c then BitVec.ofNat 8 D else
    if a = 0x8022 then 1 else
    if a = 0x8024 then 0x20 else
    if a = 0x8025 then 8 else
    if a = 0x8029 then 0x70 else
    if a = 0x802c then 0x10 else
    if a = 0x8032 then 0x30 else
    if a = 0x8036 then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, D⟩, ⟨0x7000, 128⟩, ⟨0x300000, 44⟩,
    ⟨0x300000, 44⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x10000, 2080 * 8⟩]

theorem encrypt_sat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (spec (tables vs)).pre s := by
  obtain hha : ∀ s : State, Spec.MdHashTable.hashAt 32 (withTable s vs w).mem (State.addr (0x300000 : BitVec 32)) =
      some w.g.G := fun s => hashAt_tableOf (by decide) (held_tableOf (by decide) (withTable_held s vs w)).2.1
  obtain hl' : w.g.G.len ∈ Impl.RsaOaep.Arm.lens := w.g.glen ▸ w.g.lens
  generalize hDd : w.g.G.len = D at hl'
  refine ⟨withTable (satState D) vs w, ?_⟩
  obtain hA : ∀ D ∈ Impl.RsaOaep.Arm.lens, ∀ j < 14, (stackArgAddr (satState D) j).toNat + 4 ≤ 0x300000 := by decide
  obtain hA' := hA D hl'
  obtain a0 : stackArg (withTable (satState D) vs w) 0 = 0x2100 :=
    (withTable_below _ _ _ (hA' 0 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 0 = 0x2100 by decide) D hl')
  obtain a1 : stackArg (withTable (satState D) vs w) 1 = 1 :=
    (withTable_below _ _ _ (hA' 1 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 1 = 1 by decide) D hl')
  obtain a2 : stackArg (withTable (satState D) vs w) 2 = 0x3000 :=
    (withTable_below _ _ _ (hA' 2 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 2 = 0x3000 by decide) D hl')
  obtain a3 : stackArg (withTable (satState D) vs w) 3 = 0 :=
    (withTable_below _ _ _ (hA' 3 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 3 = 0 by decide) D hl')
  obtain a4 : stackArg (withTable (satState D) vs w) 4 = 0x3100 :=
    (withTable_below _ _ _ (hA' 4 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 4 = 0x3100 by decide) D hl')
  obtain a5 : stackArg (withTable (satState D) vs w) 5 = 0 :=
    (withTable_below _ _ _ (hA' 5 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 5 = 0 by decide) D hl')
  obtain a6 : stackArg (withTable (satState D) vs w) 6 = 0x3200 :=
    (withTable_below _ _ _ (hA' 6 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 6 = 0x3200 by decide) D hl')
  obtain a7 : stackArg (withTable (satState D) vs w) 7 = BitVec.ofNat 32 D :=
    (withTable_below _ _ _ (hA' 7 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 7 = BitVec.ofNat 32 D by decide) D hl')
  obtain a8 : stackArg (withTable (satState D) vs w) 8 = 0x10000 :=
    (withTable_below _ _ _ (hA' 8 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 8 = 0x10000 by decide) D hl')
  obtain a9 : stackArg (withTable (satState D) vs w) 9 = 0x820 :=
    (withTable_below _ _ _ (hA' 9 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 9 = 0x820 by decide) D hl')
  obtain a10 : stackArg (withTable (satState D) vs w) 10 = 0x7000 :=
    (withTable_below _ _ _ (hA' 10 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 10 = 0x7000 by decide) D hl')
  obtain a11 : stackArg (withTable (satState D) vs w) 11 = 16 :=
    (withTable_below _ _ _ (hA' 11 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 11 = 16 by decide) D hl')
  obtain a12 : stackArg (withTable (satState D) vs w) 12 = 0x300000 :=
    (withTable_below _ _ _ (hA' 12 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 12 = 0x300000 by decide) D hl')
  obtain a13 : stackArg (withTable (satState D) vs w) 13 = 0x300000 :=
    (withTable_below _ _ _ (hA' 13 (by decide))).trans
      ((show ∀ D ∈ Impl.RsaOaep.Arm.lens, stackArg (satState D) 13 = 0x300000 by decide) D hl')
  have e : stackArgAddr (withTable (satState D) vs w) 0 = 0x8000 := rfl
  obtain hha' := hha (satState D)
  simp only [Impl.RsaOaep.Arm.lens, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
      List.getD_cons_zero, Option.some.injEq, exists_eq_left', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      a12, a13, e]
    sig_pre [Spec.RsaOaep.encryptMdTablesContract, Spec.RsaOaep.encryptMdTablesSig, Spec.RsaOaep.seedLenMdOk,
      Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Abi.withTables, Sig.wordIndex,
      abi, argRegs, reduceClassify, Loc.val]
    sig_and_intros
    all_goals first
      | exact ⟨tableOf w, List.mem_map_of_mem hw, held_twL _ _ _ rfl⟩
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)
      | (intro H' hH'
         obtain rfl := Option.some.inj (hha'.symm.trans hH')
         rw [hDd]; rfl)
      | (rw [List.append_eq, List.append_eq, List.append_nil]; exact symsOf32_distinct2 hl)
      | (simp only [Spec.Rsa.lenValid]; decide)

end VG.Proof.RsaOaep.Arm.Enc

end

end


/-!
# RSAES-OAEP on ARMv7: the instances emitted

What the registrations check of the hash functions whose tables a function
takes (`OK`), and the instances' proofs against the contracts the
registrations state, with both hash functions any of the tables: decryption
(`dec_ok`), decryption with the key's precomputed values (`decP_ok`) and
encryption (`enc_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm

open VG VG.Arm
open VG.Proof.HashTable.Arm (TVar tables names Coh)

/-- What the registrations check of the hash functions whose tables a
function takes: their functions of the same name have the same code, there
are not too many to give distinct addresses in the witnesses, and there is
one. -/
def OK (vs : List TVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ []

instance (vs : List TVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem OK.mem {vs : List TVar} (h : OK vs) : ∃ w, w ∈ vs := List.exists_mem_of_ne_nil _ h.2.2

/-- `vg_rsa_oaep_decrypt`, with the tables of `vs` and the private-key
operation over `c`. -/
theorem dec_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Dec.decCode vs c) (Dec.dspec vs) :=
  Dec.dec_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_sat hw hok.2.1) c

/-- `vg_rsa_oaep_decrypt_precomputed`, with the tables of `vs` and
`vg_rsa_private_checked_precomputed` over `c`. -/
theorem decP_ok (vs : List TVar) (hok : OK vs) (c : Proof.Rsa.Arm.CrtImpl) :
    Verified target (Dec.decCodeP vs c) (Dec.dspecP vs) :=
  Dec.dec_verifiedP hok.1 (let ⟨_, hw⟩ := hok.mem; Dec.dec_satP hw hok.2.1) c

/-- `vg_rsa_oaep_encrypt_precomputed`, with the tables of `vs`, calling `c`. -/
theorem enc_ok (vs : List TVar) (hok : OK vs) (c : RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Enc.encryptCode vs c) (Enc.espec vs) :=
  Enc.encrypt_verified hok.1 (let ⟨_, hw⟩ := hok.mem; Enc.encrypt_sat hw hok.2.1) c

end VG.Proof.RsaOaep.Arm
