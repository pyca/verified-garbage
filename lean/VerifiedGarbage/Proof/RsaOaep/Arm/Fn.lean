module

public import VerifiedGarbage.Impl.RsaOaep.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTab
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSAES-OAEP on ARMv7, as emitted

`Impl.RsaOaep.Arm.Fn` has each function with its cleanup; `Fn` below has
the theorem of each, for any implementation of the private CRT's interface
and the hash functions of any tables (`vs`) of which `OK` holds: it meets
its contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds
(`Arm.Scrub.verifiedScrubbedF`).

Each calls the hash functions of its tables indirectly, which the cleanup
accepts (`scrubSideF`'s `tablesCall`). What it needs of the code
(`CodeOkT`, `Proof/Rsa/Arm/ScrubTab.lean`: its frames within the stack it
zeroes, its indirect calls only of the tables' functions) is proven once,
for code whose hash functions and RSA operation are variables
(`code_okT`), from what each hash function states of its own code
(`PssHash.scrub`, `HashTable.Arm.fnsOf_scrub`) and each CRT implementation
of its own (`CrtImpl.pdOk`, `privCodeP_ok`): no hash function's code is
evaluated. Decryption's frames use 3624 bytes, which is no frame size of the
model, so its contract reserves the next one, 3632
(`Verified.stack_leT`, with the witness of its precondition again). Their
postconditions read the memory on return only within `out` and
decryption's `msg_len`, as on PPC64LE (`Proof/RsaOaep/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privNameP privCodeP pdOfCrt)
open VG.Proof.HashTable.Arm (TVar tables names fnsOf fnsOf_scrub)

/-! ## Postconditions -/

theorem writtenDecrypt_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : m₂.readW l 64 = m₁.readW l 64)
    (h : Spec.RsaOaep.writtenDecrypt m₁ o l n r v) : Spec.RsaOaep.writtenDecrypt m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaOaep.writtenDecrypt, e, el] using h

theorem encryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.encryptMdTablesSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.encryptMdTablesSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of (n := (nLen.setWidth _).toNat) hb.1
        (by rw [← hp.2.1]; exact toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      exact fun H G h1 h2 h3 => written_of e' (h H G h1 h2 h3)

theorem decryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.decryptPrecomputedMdTablesSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
        m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.decryptPrecomputedMdTablesSig, Spec.RsaOaep.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of (n := (nLen.setWidth _).toNat) hb.1
        (by rw [← hp.2.1]; exact toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      have el : m₂.readW ml 64 = m₁.readW ml 64 := Mem.readW_congr fun t ht => by
        have := hb.2.1 (ml + BitVec.ofNat 64 t) (contains_of (by simp only [Nat.reduceDiv] at ht; omega))
        exact this.symm
      exact fun H G h1 h2 => writtenDecrypt_of e' el (h H G h1 h2)

/-! ## Decryption's stack, at a frame size of the model -/

open VG.Proof.RsaOaep.Arm.Dec in
open VG.Proof.HashTable.Arm (withTable held_twL withTable_below tableOf) in
open VG.Proof.HashTable (symsOf32_distinct2) in
theorem decryptSat {vs : List TVar} {w : TVar} (hw : w ∈ vs) (hl : (names vs).length < 2 ^ 24) :
    ∃ s, (Spec.RsaOaep.decryptPrecomputedMdTablesContract
      (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
      3632).pre s := by
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

theorem decryptVerified (vs : List TVar) (hok : OK vs) (v : CrtImpl) :
    Verified target (Proof.RsaOaep.Arm.Dec.decCodeP vs v)
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        3632) :=
  Verified.stack_leT (by decide) (decP_ok vs hok v) (let ⟨_, hw⟩ := hok.mem; decryptSat hw hok.2.1)

/-! ## What the cleanup needs of the code -/

/-- The functions of the tables of `vs` are named among those of
`[("hash", tables vs), ("mgf1", tables vs)]`. -/
theorem names_tableFns (vs : List TVar) :
    ∀ f ∈ names vs, f ∈ tableFns [("hash", tables vs), ("mgf1", tables vs)] := fun f hf => by
  simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  exact .inl (by simpa only [names, List.flatMap, List.mem_flatten, List.mem_map] using hf)

/-- Encryption's code, for any functions of the tables and public operation. -/
theorem encrypt_okT {f : Impl.RsaOaep.Arm.Fns} {T : List String} {N : String} {C : Prog isa}
    (hi : ∀ p ∈ f.init, CodeOk p.2 0 ∧ p.1 ∈ T) (hu : ∀ p ∈ f.upd, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ f.fin, CodeOk p.2 0 ∧ p.1 ∈ T) (hc : CodeOk C 56) :
    CodeOkT (Impl.RsaOaep.Arm.encryptPrecomputed f N C) 240 T := by
  code_okT

/-- Decryption's code, for any functions of the tables and private operation. -/
theorem decrypt_okT {f : Impl.RsaOaep.Arm.Fns} {T : List String} {N : String} {C : Prog isa}
    (hi : ∀ p ∈ f.init, CodeOk p.2 0 ∧ p.1 ∈ T) (hu : ∀ p ∈ f.upd, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ f.fin, CodeOk p.2 0 ∧ p.1 ∈ T) (hc : CodeOk C 3440) :
    CodeOkT (Impl.RsaOaep.Arm.decryptP f N C) 3632 T := by
  code_okT

theorem frameOk_3632 : FrameOk 3632 := by decide

theorem frameOk_240 : FrameOk 240 := by decide

end VG.Proof.RsaOaep.Arm.Scrub

namespace VG.Proof.RsaOaep.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub VG.Proof.RsaOaep.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privNameP privCodeP pdOfCrt)
open VG.Proof.HashTable.Arm (TVar tables fnsOf fnsOf_scrub)

/-- `vg_rsa_oaep_decrypt_precomputed`, with both hash functions any of the
tables of `vs`, calling `vg_rsa_private_checked_precomputed` over `v`. -/
theorem decryptPrecomputed (vs : List TVar) (hok : OK vs) (v : CrtImpl) :
    VerifiedScrubbed target (Impl.RsaOaep.Arm.Fn.decryptPrecomputed (fnsOf vs) (privNameP v) (privCodeP v))
      (Spec.RsaOaep.decryptPrecomputedMdTablesContract
        (abi.withTables Spec.RsaOaep.decryptPrecomputedMdTablesSig [("hash", tables vs), ("mgf1", tables vs)])
        3632) 32 :=
  have hs := fnsOf_scrub (names_tableFns vs)
  verifiedScrubbedF (api := Spec.RsaOaep.decryptPrecomputedMdTablesApi)
    { tables := [("hash", tables vs), ("mgf1", tables vs)]
      code := Proof.RsaOaep.Arm.Dec.decCodeP vs v
      verified := decryptVerified vs hok v }
    (decryptOut _ _) (scrubSideF_ofT (decrypt_okT hs.1 hs.2.1 hs.2.2 (privCodeP_ok v)) frameOk_3632)

/-- `vg_rsa_oaep_encrypt_precomputed`, with both hash functions any of the
tables of `vs`, calling `v`'s public operation. -/
theorem encryptPrecomputed (vs : List TVar) (hok : OK vs) (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaOaep.Arm.Fn.encryptPrecomputed (fnsOf vs) (pdOfCrt v).name (pdOfCrt v).code)
      (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", tables vs), ("mgf1", tables vs)]) 240) 32 :=
  have hs := fnsOf_scrub (names_tableFns vs)
  verifiedScrubbedF (api := Spec.RsaOaep.encryptMdTablesApi)
    { tables := [("hash", tables vs), ("mgf1", tables vs)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode vs (pdOfCrt v)
      verified := enc_ok vs hok (pdOfCrt v) }
    (encryptOut _ _) (scrubSideF_ofT (encrypt_okT hs.1 hs.2.1 hs.2.2 v.pdOk) frameOk_240)

end VG.Proof.RsaOaep.Arm.Fn
