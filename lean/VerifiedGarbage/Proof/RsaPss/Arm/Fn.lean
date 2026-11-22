module

public import VerifiedGarbage.Impl.RsaPss.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubTab
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPss.Arm.Inst
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PSS on ARMv7, as emitted

`Impl.RsaPss.Arm.Fn` has each function with its cleanup; `Fn` below has the
theorem of each, for any implementation of the private CRT's interface and
the hash functions of any tables (`mvs`, the hash function's, and `vs`,
MGF1's) of which `OK` holds: it meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`), which is what its
registration binds (`Arm.Scrub.verifiedScrubbedAll`).

As RSA-OAEP's (`Proof/RsaOaep/Arm/Fn.lean`): what the cleanup needs of the
code (`CodeOkT`) is proven once, for code whose hash functions and RSA
operation are variables (`code_okT`), from what each hash function states of
its own code (`PssHash.scrub`, `MdHashTable.Arm.fnsOf_scrub`,
`HashTable.Arm.fnsOf_scrub`) and each CRT implementation of its own; no hash
function's code is evaluated. Signing's frames use 3672 bytes, which is no
frame size of the model, so its contract reserves the next one, 3680
(`Verified.stack_leT`, with the witnesses of its precondition again). Their
postconditions read the memory on return only within `out`, as on PPC64LE
(`Proof/RsaPss/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privNameP privCodeP pdOfCrt)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-! ## Postconditions -/

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

theorem signOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.signPrecomputedMdTableSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _],
        m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPss.signPrecomputedMdTableSig, Sig.bufs, List.mem_cons, forall_eq_or_imp,
        Elem.size] at hb
      change @Curry.apply (Mem → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of (n := (nLen.setWidth _).toNat) hb.1
        (by rw [← hp.2.1]; exact toNat_sw_le _ (ScrubAbi.plain.tables _ _) outLen)
      exact fun H G h1 h2 => writtenOutcome_of e' (h H G h1 h2)

theorem verifyOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.plain.tables _ _) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

end VG.Proof.RsaPss.Arm.Scrub

/-! ## Signing's stack, at a frame size of the model -/

namespace VG.Proof.RsaPss.Arm.Sg

open VG VG.Arm
open VG.Proof.HashTable (symsOf32 symsOf32_distinct readW_sep32)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- The precomputed signing's precondition, from the facts of a state. -/
theorem sign_pre_of3680 {hs ts : List FnTable} {D : Nat} (hD : D ≤ 64) {s : State}
    (hg : s.gpr = (satStateP D).gpr) (hsp : s.sp = (satStateP D).sp)
    (ha : ∀ j < 22, stackArg s j = BitVec.ofNat 32 ((satArgsP D).getD j 0))
    (hrd : s.rd = (satStateP D).rd) (hwr : s.wr = (satStateP D).wr)
    (hH : ∃ T ∈ hs, Abi.tableHeld 32 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ ts, Abi.tableHeld 32 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((hs.map (fun T : FnTable => T.fns)).flatten ++ ((ts.map (fun T : FnTable => T.fns)).flatten ++ [])).Pairwise
      fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hd : Spec.RsaPss.digestLenOk 32 s.mem 0x300000 (BitVec.ofNat 32 D))
    (hkey : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) :
    (Spec.RsaPss.signPrecomputedMdTableContract
      (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig [("hash", hs), ("mgf1", ts)]) 3680).pre s := by
  have g0 : s.gpr .r0 = 0x1000 := by rw [hg]; rfl
  have g1 : s.gpr .r1 = 64 := by rw [hg]; rfl
  have g2 : s.gpr .r2 = 0x2000 := by rw [hg]; rfl
  have g3 : s.gpr .r3 = 64 := by rw [hg]; rfl
  have sp0 : s.sp = 0x8000 := hsp
  have e0 : stackArgAddr s 0 = 0x8000 := by simp only [stackArgAddr, sp0]; decide
  have hD' : (BitVec.ofNat 32 D).toNat = D := by rw [BitVec.toNat_ofNat]; omega_using [hD]
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide),
    ha 21 (by decide), g0, g1, g2, g3, e0, sp0, hrd, hwr, satArgsP]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signPrecomputedMdTableContract, Spec.RsaPss.signPrecomputedMdTableSig, Spec.MdHashTable.param,
    Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords, Abi.withTables, Sig.wordIndex, abi,
    argRegs, reduceClassify, Loc.val]
  sig_and_intros
  all_goals first
    | (show Spec.Rsa.privatePrecompute _ _ _ = _; exact hkey)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | exact hH
    | exact hG
    | exact hsy
    | exact hd
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hD']; rfl)
    | (rw [hD']; exact dig_disj hD (Region.disjoint_of_sep (by decide)))
    | (rw [hD']; exact (dig_disj hD (Region.disjoint_of_sep (by decide))).symm)
    | (rw [hD']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hD']; simp; omega_using [hD])

theorem sign_sat_of3680 {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) {D : Nat} (hD : D ≤ 64) (hlen : w.h.G.len = D)
    (hb : ∀ j < 22, stackArg (satStateP D) j = BitVec.ofNat 32 ((satArgsP D).getD j 0)) :
    (Spec.RsaPss.signPrecomputedMdTableContract
      (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
        [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) 3680).pre (withTabs (satStateP D) mvs vs w wg) :=
  sign_pre_of3680 hD rfl rfl (fun j hj => (withTabs_arg _ (sat_argsP D j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _⟩ ⟨_, List.mem_map_of_mem hwg, withTabs_heldG _⟩
    (by rw [List.append_nil]; exact symsOf32_distinct hl) (fun H hH => by
      have e3 : State.addr (0x300000 : BitVec 32) = (0x300000 : Addr) := by decide
      have hheld := withTabs_heldH (satStateP D) (mvs := mvs) (vs := vs) (w := w) (wg := wg)
      rw [← e3] at hheld
      have hA := MdHashTable.Arm.hashAt_tableOf (p := 0x300000) (by decide)
        (MdHashTable.Arm.held_tableOf (by decide) hheld).2.2.2
      rw [e3] at hA
      rw [hA, Option.some.injEq] at hH
      subst hH
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), hlen]) (satP_key D)

/-- The precomputed signing's contract, with the tables of `mvs` and `vs`, is
satisfiable. -/
theorem signSat {mvs : List MVar} {vs : List TVar} {w : MVar} {wg : TVar} (hw : w ∈ mvs) (hwg : wg ∈ vs)
    (hl : (allNames mvs vs).length < 2 ^ 24) :
    ∃ s, (Spec.RsaPss.signPrecomputedMdTableContract
      (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
        [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) 3680).pre s := by
  have hG : w.h.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx
  have hlen : w.h.G.len = 16 ∨ w.h.G.len = 20 ∨ w.h.G.len = 28 ∨ w.h.G.len = 32 ∨ w.h.G.len = 48 ∨
      w.h.G.len = 64 := by
    simp only [Spec.Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hG
    rcases hG with e | e | e | e | e | e | e | e | e | e | e | e | e | e <;> rw [e] <;> decide
  rcases hlen with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b16⟩
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b20⟩
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b28⟩
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b32⟩
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b48⟩
  · exact ⟨_, sign_sat_of3680 hw hwg hl (by decide) e satP_b64⟩

end VG.Proof.RsaPss.Arm.Sg

namespace VG.Proof.RsaPss.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privNameP privCodeP pdOfCrt)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

theorem signVerified {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : CrtImpl) :
    Verified target (Proof.RsaPss.Arm.Sg.signCodeP mvs vs v)
      (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
          [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) 3680) :=
  Verified.stack_leT (by decide) (signP_ok hok v)
    (let ⟨_, hw⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.1
     let ⟨_, hwg⟩ := List.exists_mem_of_ne_nil _ hok.2.2.2.2
     Proof.RsaPss.Arm.Sg.signSat hw hwg hok.2.2.1)

/-! ## What the cleanup needs of the code -/

/-- The functions of the tables of `mvs` and `vs` are named among those of
`[("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]`. -/
theorem names_tableFns (mvs : List MVar) (vs : List TVar) :
    (∀ f ∈ MdHashTable.Arm.names mvs,
      f ∈ tableFns [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) ∧
    (∀ f ∈ HashTable.Arm.names vs,
      f ∈ tableFns [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) := by
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩ <;>
    simp only [tableFns, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
  · exact .inl (by simpa only [MdHashTable.Arm.names, List.flatMap, List.mem_flatten, List.mem_map] using hf)
  · exact .inr (by simpa only [HashTable.Arm.names, List.flatMap, List.mem_flatten, List.mem_map] using hf)

/-- Signing's code, for any functions of the tables and private operation. -/
theorem sign_okT {f : Impl.RsaPss.Arm.MdFns} {g : Impl.RsaOaep.Arm.Fns} {T : List String} {N : String}
    {C : Prog isa}
    (h1 : ∀ p ∈ f.init, CodeOk p.2 0 ∧ p.1 ∈ T) (h2 : ∀ p ∈ f.comp, CodeOk p.2 0 ∧ p.1 ∈ T)
    (h3 : ∀ p ∈ f.dig, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hi : ∀ p ∈ g.init, CodeOk p.2 0 ∧ p.1 ∈ T) (hu : ∀ p ∈ g.upd, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ g.fin, CodeOk p.2 0 ∧ p.1 ∈ T) (hc : CodeOk C 3488) :
    CodeOkT (Impl.RsaPss.Arm.signP f g N C) 3680 T := by
  code_okT

/-- Verification's code, for any functions of the tables and public operation. -/
theorem verify_okT {f : Impl.RsaPss.Arm.MdFns} {g : Impl.RsaOaep.Arm.Fns} {T : List String} {N : String}
    {C : Prog isa}
    (h1 : ∀ p ∈ f.init, CodeOk p.2 0 ∧ p.1 ∈ T) (h2 : ∀ p ∈ f.comp, CodeOk p.2 0 ∧ p.1 ∈ T)
    (h3 : ∀ p ∈ f.dig, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hi : ∀ p ∈ g.init, CodeOk p.2 0 ∧ p.1 ∈ T) (hu : ∀ p ∈ g.upd, CodeOk p.2 0 ∧ p.1 ∈ T)
    (hf : ∀ p ∈ g.fin, CodeOk p.2 0 ∧ p.1 ∈ T) (hc : CodeOk C 56) :
    CodeOkT (Impl.RsaPss.Arm.verifyPrecomputed f g N C) 240 T := by
  code_okT

theorem frameOk_3680 : FrameOk 3680 := by decide

theorem frameOk_240 : FrameOk 240 := by decide

end VG.Proof.RsaPss.Arm.Scrub

namespace VG.Proof.RsaPss.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub VG.Proof.RsaPss.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privNameP privCodeP pdOfCrt)
open VG.Proof.HashTable.Arm (TVar)
open VG.Proof.MdHashTable.Arm (MVar)

/-- `vg_rsa_pss_sign_precomputed`, with the hash function any of the tables
of `mvs` and MGF1's any of `vs`, calling `vg_rsa_private_checked_precomputed`
over `v`. -/
theorem signPrecomputed {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPss.Arm.Fn.signPrecomputed (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs) (privNameP v)
        (privCodeP v))
      (Spec.RsaPss.signPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.signPrecomputedMdTableSig
          [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) 3680) 32 :=
  have hm := MdHashTable.Arm.fnsOf_scrub (names_tableFns mvs vs).1
  have hg := HashTable.Arm.fnsOf_scrub (names_tableFns mvs vs).2
  verifiedScrubbedAll (api := Spec.RsaPss.signPrecomputedMdTableApi)
    { tables := [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]
      code := Proof.RsaPss.Arm.Sg.signCodeP mvs vs v
      verified := signVerified hok v }
    (signOut _ _ _)
    (scrubSideF_ofT (sign_okT hm.1 hm.2.1 hm.2.2 hg.1 hg.2.1 hg.2.2 (privCodeP_ok v)) frameOk_3680)

/-- `vg_rsa_pss_verify_precomputed`, with the hash function any of the
tables of `mvs` and MGF1's any of `vs`, calling `v`'s public operation. -/
theorem verifyPrecomputed {mvs : List MVar} {vs : List TVar} (hok : OK mvs vs) (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPss.Arm.Fn.verifyPrecomputed (MdHashTable.Arm.fnsOf mvs) (HashTable.Arm.fnsOf vs)
        (pdOfCrt v).name (pdOfCrt v).code)
      (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig
          [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]) 240) 32 :=
  have hm := MdHashTable.Arm.fnsOf_scrub (names_tableFns mvs vs).1
  have hg := HashTable.Arm.fnsOf_scrub (names_tableFns mvs vs).2
  verifiedScrubbedAll (api := Spec.RsaPss.verifyPrecomputedMdTableApi)
    { tables := [("hash", MdHashTable.Arm.tables mvs), ("mgf1", HashTable.Arm.tables vs)]
      code := Proof.RsaPss.Arm.Vf.verifyCode mvs vs (pdOfCrt v)
      verified := verify_ok hok (pdOfCrt v) }
    (verifyOut _ _ _)
    (scrubSideF_ofT (verify_okT hm.1 hm.2.1 hm.2.2 hg.1 hg.2.1 hg.2.2 v.pdOk) frameOk_240)

end VG.Proof.RsaPss.Arm.Fn
