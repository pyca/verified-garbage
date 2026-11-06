module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTMain
public import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Entry
public import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.MdHashTable.PPC64LE.Tables
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Md
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Md
meta import VerifiedGarbage.Proof.Md5.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha1.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.CTMain
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Correct
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Pre
import VerifiedGarbage.Proof.Framework.Mem

/-!
# RSASSA-PSS on PPC64LE with the tables: `Verified`

Untrusted: everything here is checked by Lean. For variants `vs` of `MdHash`
(`Proof/MdHashTable/PPC64LE/Tables.lean`) and `gs` of `Hash`
(`Proof/HashTable/PPC64LE.lean`) whose functions of the same name have the
same code: the tables a state meeting verification's or signing's
precondition holds give what the proofs need of them (`tabs_of`);
correctness against the contracts (`code_correct`, by `verify_ok` and
`sign_ok`); constant time (`code_constantTime`, by `code_ct`, the second
run holding the same tables, at the anchor's addresses with the anchor's
addresses of their functions). The families of streaming code (`md5F`,
`sha1F`, `sha256F`, `sha512F`), with the constant time of their compression
functions, from their artifacts' proofs, and of the digest of their hash
values, by the taint analysis; one variant of each hash function of
`Spec.Mgf1.hashes` (`mvars`). States meeting the contracts, with the table
of `MdHash` of a variant at `0x300000`, the table of `Hash` of a variant at
`0x300100` and the tables' functions at distinct addresses (`verify_sat`,
`sign_sat`, as on x86-64); and `verify_ok'` and `sign_ok'`, which the
registration binds.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Proof.RsaOaep.PPC64LE (TabS)
open VG.Proof.HashTable.PPC64LE (TVar)
open VG.Proof.MdHashTable.PPC64LE (MVar digName tabsOf)

section
variable {vs : List MVar} {gs : List TVar}

/-- The tables of a state meeting the precondition: one of `vs`' and one of
`gs`', with what the proofs need of them. -/
theorem tabs_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) {s : State}
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ w ∈ vs, ∃ w' ∈ gs,
      Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.PPC64LE.tableOf w')) ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some w.l.G ∧
      s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (MdHashTable.PPC64LE.idx w) ∧
      ∀ {D : Nat}, PreP D s → TabsOn (tabsOf vs gs w w') s := by
  obtain ⟨⟨T, hT, hh⟩, ⟨T', hT', hh'⟩, hpw⟩ := spec_tab h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  have hpH := hpw.sublist (List.sublist_append_left _ _)
  have hpG := hpw.sublist (List.sublist_append_right _ _)
  have hi := (MdHashTable.PPC64LE.held_tableOf hh).2.2.2
  refine ⟨w, hw, w', hw', hh, hh', MdHashTable.PPC64LE.hashAt_tableOf hi, hi, fun P => ⟨?_, ?_⟩⟩
  · refine HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tGR s ∈ s.rd by rw [P.hrd]; simp) P.ktg
      (P.stg.sub_left (sc_sub P)) hc' hpG hw' hh'
  · exact MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P.ka (P.sa.sub_left (sc_sub P)) (show tHR s ∈ s.rd by rw [P.hrd]; simp) P.kth
      (P.sth.sub_left (sc_sub P)) hc hpH hw hh

/-- The correctness of `vg_rsa_pss_verify_precomputed`, against its contract,
for the tables of `vs` and `gs`. -/
theorem code_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) (s : State)
    (h : (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) s t s' ∧
      abiPreserved s s' ∧ (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨w, hw, w', hw', hh, hh', hH, hi, hT⟩ := tabs_of hc hc' h
  have hG := HashTable.PPC64LE.hashAt_tableOf (HashTable.PPC64LE.held_tableOf hh').2.1
  have P := preP_of h hH
  obtain ⟨Tg, T⟩ := hT P
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  obtain ⟨t, s', he, habi, hr⟩ := verify_ok P w.l.ok w.l.hash w.l.len w.l.valid w'.l.ok Tg w'.l.hash w'.l.len
    w'.l.valid T w.F.ok hl w.hN w.hB hi w.sh.1 w.sh.2.1 w.sh.2.2
  refine ⟨t, s', he, habi, ?_⟩
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_post [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.HashTable.param, Abi.withTables, abi, argRegs, stackArgs_eight, List.append_eq]
  intro H' G' hH' hG' hc
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  rw [hr hc]
  unfold vOut
  split <;> rfl

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) :
    ConstantTime isa (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre
      (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pub
      (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨w, hw, w', hw', hh₁, hh₁', hH₁, hi₁, hT₁⟩ := tabs_of hc hc' h₁
  obtain ⟨p, hsy, hiffH, hiffG⟩ := pubT_of hp
  have hh₂ := (hiffH _ (List.mem_map_of_mem hw)).mp hh₁
  have hh₂' := (hiffG _ (List.mem_map_of_mem hw')).mp hh₁'
  have hi₂ := (MdHashTable.PPC64LE.held_tableOf hh₂).2.2.2
  have hH₂ := MdHashTable.PPC64LE.hashAt_tableOf hi₂
  have P₁ := preP_of h₁ hH₁
  have P₂ := preP_of h₂ hH₂
  have hpw₂ := (spec_tab h₂).2.2
  have T₂ : TabsOn (tabsOf vs gs w w') s₂ :=
    ⟨HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tGR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.ktg
      (P₂.stg.sub_left (sc_sub P₂)) hc' (hpw₂.sublist (List.sublist_append_right _ _)) hw' hh₂',
    MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) P₂.ka (P₂.sa.sub_left (sc_sub P₂)) (show tHR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) P₂.kth
      (P₂.sth.sub_left (sc_sub P₂)) hc (hpw₂.sublist (List.sublist_append_left _ _)) hw hh₂⟩
  have hn := MdHashTable.PPC64LE.mem_names hw
  have hn' := HashTable.PPC64LE.mem_names hw'
  have sH : ∀ {f}, f ∈ MdHashTable.PPC64LE.names vs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_left _ hf)).symm
  have sG : ∀ {f}, f ∈ HashTable.PPC64LE.names gs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_right _ hf)).symm
  have hl : w.F.md.Link w.l.ok.SH w.iv w.l.G.len := w.l.len ▸ w.link
  have hk : ∀ {s}, PreP w.l.G.len s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.k1
  exact code_ct (Z := tabsOf vs gs w w') w.l.ok w.l.ct w.l.hash w.l.len w.l.valid w'.l.ok w'.l.ct w'.l.hash
    w'.l.len w'.l.valid w.F.ok w.F.ct w.F.hcc w.F.hdc hl w.hN w.hB w.sh.1 w.sh.2.1 w.sh.2.2 _ _ _ _ _ _
    ⟨s₁, ⟨⟨⟨P₁, hT₁ P₁⟩, ⟨pubP_refl s₁, hk P₁⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi₁⟩,
      ⟨⟨⟨P₂, T₂⟩, ⟨p, hk P₂⟩, p.args 7 (by decide) (by decide), sG hn'.1, sG hn'.2.1, sG hn'.2.2,
        p.args 6 (by decide) (by decide), sH hn.1, sH hn.2.1, sH hn.2.2.1, sH hn.2.2.2.1, sH hn.2.2.2.2⟩, hi₂⟩⟩
    e₁ e₂

/-- `vg_rsa_pss_verify_precomputed` against its contract, for the tables of
`vs` and `gs`, given a state meeting it. -/
theorem verify_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs))
      (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  ⟨code_correct hc hc', code_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE


namespace VG.Proof.MdHashTable.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE

open VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdHashTable.PPC64LE (digest)

theorem md5_hcc : ConstantTime isa (compressK (P := Impl.Md5.PPC64LE.Stream.params) Proof.Md5.md).pre (compressK (P := Impl.Md5.PPC64LE.Stream.params) Proof.Md5.md).pub Impl.Md5.PPC64LE.compress :=
  Proof.Md5.PPC64LE.compress_verified.2.1

theorem sha1_hcc : ConstantTime isa (compressK (P := Impl.Sha1.PPC64LE.Stream.params) Proof.Sha1.md).pre (compressK (P := Impl.Sha1.PPC64LE.Stream.params) Proof.Sha1.md).pub Impl.Sha1.PPC64LE.compress :=
  Proof.Sha1.PPC64LE.compress_verified.2.1

theorem sha256_hcc : ConstantTime isa (compressK (P := Impl.Sha256.PPC64LE.mdParams) Proof.Sha256.md).pre (compressK (P := Impl.Sha256.PPC64LE.mdParams) Proof.Sha256.md).pub Impl.Sha256.PPC64LE.compress :=
  Proof.Sha256.PPC64LE.compress_verified.2.1

theorem sha512_hcc : ConstantTime isa (compressK (P := Impl.Sha512.PPC64LE.mdParams) Proof.Sha512.md).pre (compressK (P := Impl.Sha512.PPC64LE.mdParams) Proof.Sha512.md).pub Impl.Sha512.PPC64LE.compress :=
  Proof.Sha512.PPC64LE.compress_verified.2.1

def md5F : Fam where
  P := Impl.Md5.PPC64LE.Stream.params
  md := Proof.Md5.md
  cn := "vg_md5_compress"
  cc := Impl.Md5.PPC64LE.compress
  ok := ⟨Proof.Md5.PPC64LE.Stream.dims, Proof.Md5.PPC64LE.Stream.shape, by decide, Proof.Md5.PPC64LE.Stream.callee,
    digest_correct Proof.Md5.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := md5_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha1F : Fam where
  P := Impl.Sha1.PPC64LE.Stream.params
  md := Proof.Sha1.md
  cn := "vg_sha1_compress"
  cc := Impl.Sha1.PPC64LE.compress
  ok := ⟨Proof.Sha1.PPC64LE.Stream.dims, Proof.Sha1.PPC64LE.Stream.shape, by decide, Proof.Sha1.PPC64LE.Stream.callee,
    digest_correct Proof.Sha1.PPC64LE.Stream.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha1_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha256F : Fam where
  P := Impl.Sha256.PPC64LE.mdParams
  md := Proof.Sha256.md
  cn := "vg_sha256_compress"
  cc := Impl.Sha256.PPC64LE.compress
  ok := ⟨Proof.Sha256.PPC64LE.Md.dims, Proof.Sha256.PPC64LE.Md.shape, by decide, Proof.Sha256.PPC64LE.Md.callee,
    digest_correct Proof.Sha256.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega),
    fun _ _ => trivial⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha256_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def sha512F : Fam where
  P := Impl.Sha512.PPC64LE.mdParams
  md := Proof.Sha512.md
  cn := "vg_sha512_compress"
  cc := Impl.Sha512.PPC64LE.compress
  ok := ⟨Proof.Sha512.PPC64LE.Md.dims, Proof.Sha512.PPC64LE.Md.shape, by decide, Proof.Sha512.PPC64LE.Md.callee,
    digest_correct Proof.Sha512.PPC64LE.Md.shape (by decide) (by decide), by decide,
    fun m m' p q h => by
      apply Vector.ext
      intro j hj
      simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
      exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega),
    fun n hn => show n < 2 ^ 64 by omega⟩
  ct := by exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  hcc := sha512_hcc
  hdc := by exact digest_ct ⟨_, by taint_decide⟩

def md5M : MVar where
  H := Md5.hash
  l := Proof.RsaOaep.PPC64LE.md5L
  idx := rfl
  F := md5F
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha1M : MVar where
  H := Sha1.hash
  l := Proof.RsaOaep.PPC64LE.sha1L
  idx := rfl
  F := sha1F
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha224M : MVar where
  H := Sha224.hash
  l := Proof.RsaOaep.PPC64LE.sha224L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha256M : MVar where
  H := Sha256.hash
  l := Proof.RsaOaep.PPC64LE.sha256L
  idx := rfl
  F := sha256F
  iv := Spec.Sha256.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha384M : MVar where
  H := Sha384.hash
  l := Proof.RsaOaep.PPC64LE.sha384L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_384
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512M : MVar where
  H := Sha512.hash
  l := Proof.RsaOaep.PPC64LE.sha512L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m =>
    (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_224M : MVar where
  H := Sha512_224.hash
  l := Proof.RsaOaep.PPC64LE.sha512_224L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_224
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

def sha512_256M : MVar where
  H := Sha512_256.hash
  l := Proof.RsaOaep.PPC64LE.sha512_256L
  idx := rfl
  F := sha512F
  iv := Spec.Sha512.H0_512_256
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl, by decide, by decide⟩
  hN := rfl
  hB := rfl
  sh := ⟨by decide, rfl, rfl⟩

/-- Every hash function's variant. -/
def mvars : List MVar := [md5M, sha1M, sha224M, sha256M, sha384M, sha512M, sha512_224M, sha512_256M]

end VG.Proof.MdHashTable.PPC64LE


namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign
open VG.Proof.HashTable.PPC64LE (TVar)
open VG.Proof.MdHashTable.PPC64LE (MVar digName tabsOf)
open VG.Proof.RsaPss.PPC64LE (Tabs)

section
variable {vs : List MVar} {gs : List TVar}

/-- The tables of a state meeting the precondition: one of `vs`' and one of
`gs`', with what the proofs need of them. -/
theorem tabs_of (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) {s : State}
    (h : (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ w ∈ vs, ∃ w' ∈ gs,
      Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (MdHashTable.PPC64LE.tableOf w)) ∧
      Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.PPC64LE.tableOf w')) ∧
      Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some w.l.G ∧
      Spec.HashTable.hashAt 64 s.mem (stackArg s 15) = some w'.l.G ∧
      s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (MdHashTable.PPC64LE.idx w) ∧
      ∀ {D : Nat}, PreS D s → STabsOn (tabsOf vs gs w w') s := by
  obtain ⟨⟨T, hT, hh⟩, ⟨T', hT', hh'⟩, hpw⟩ := spec_tabS h
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hT
  obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hT'
  have hpH := hpw.sublist (List.sublist_append_left _ _)
  have hpG := hpw.sublist (List.sublist_append_right _ _)
  have hi := (MdHashTable.PPC64LE.held_tableOf hh).2.2.2
  refine ⟨w, hw, w', hw', hh, hh', MdHashTable.PPC64LE.hashAt_tableOf hi,
    HashTable.PPC64LE.hashAt_tableOf (HashTable.PPC64LE.held_tableOf hh').2.1, hi, fun P => ⟨?_, ?_⟩⟩
  · exact HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
      (show tGR s ∈ s.rd by rw [P.hrd]; simp) (P.ktg.sub_left kR_sub) (P.stg.sub_left (sc_sub P)) hc' hpG hw' hh'
  · exact MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s) (by rw [P.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) (P.ka.sub_left kR_sub) (P.sa.sub_left (sc_sub P))
      (show tHR s ∈ s.rd by rw [P.hrd]; simp) (P.kth.sub_left kR_sub) (P.sth.sub_left (sc_sub P)) hc hpH hw hh

/-- The correctness of `vg_rsa_pss_sign`, against its contract, for the
tables of `vs` and `gs`. -/
theorem code_correct (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) (s : State)
    (h : (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    ∃ t s', Exec isa (sign (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) s t s' ∧
      abiPreserved s s' ∧ (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).post s s' := by
  obtain ⟨w, hw, w', hw', hh, hh', hH, hG, hi, hT⟩ := tabs_of hc hc' h
  have P := preS_of h hH
  obtain ⟨Tg, T⟩ := hT P
  obtain ⟨t, s', he, habi, hr⟩ := sign_ok P w.l.ok w.l.hash w.l.len w.l.valid w'.l.ok Tg w'.l.hash w'.l.len
    w'.l.valid T hi w.sh.1 w.sh.2.1
  refine ⟨t, s', he, habi, ?_⟩
  have e : stackBytes = 3775 + 1 := rfl
  unfold signSpec
  rw [e]
  sig_post [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig, Spec.MdHashTable.param, Spec.HashTable.param,
    Abi.withTables, abi, argRegs, stackArgs_sixteen, List.append_eq]
  intro H' G' hH' hG'
  rw [hH] at hH'
  rw [hG] at hG'
  cases hH'
  cases hG'
  exact hr

/-- Constant time: the tables of the first run, which the public data makes
the second's, at the same addresses with their functions at the same
addresses. -/
theorem code_constantTime (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs) :
    ConstantTime isa (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre
      (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pub
      (sign (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs)) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ => ?_
  obtain ⟨w, hw, w', hw', hh₁, hh₁', hH₁, -, hi₁, hT₁⟩ := tabs_of hc hc' h₁
  obtain ⟨p, hsy, hiffH, hiffG⟩ := pubS_of hp
  have hh₂ := (hiffH _ (List.mem_map_of_mem hw)).mp hh₁
  have hh₂' := (hiffG _ (List.mem_map_of_mem hw')).mp hh₁'
  have hi₂ := (MdHashTable.PPC64LE.held_tableOf hh₂).2.2.2
  have hH₂ := MdHashTable.PPC64LE.hashAt_tableOf hi₂
  have P₁ := preS_of h₁ hH₁
  have P₂ := preS_of h₂ hH₂
  have hpw₂ := (spec_tabS h₂).2.2
  have T₂ : STabsOn (tabsOf vs gs w w') s₂ :=
    ⟨HashTable.PPC64LE.tabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) (P₂.ka.sub_left kR_sub) (P₂.sa.sub_left (sc_sub P₂))
      (show tGR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) (P₂.ktg.sub_left kR_sub) (P₂.stg.sub_left (sc_sub P₂)) hc'
      (hpw₂.sublist (List.sublist_append_right _ _)) hw' hh₂',
    MdHashTable.PPC64LE.mdTabS_of (by decide) rfl (A := aR s₂) (by rw [P₂.hrd]; simp)
      (in_aR (by decide)) (in_aR_sub (by decide)) (P₂.ka.sub_left kR_sub) (P₂.sa.sub_left (sc_sub P₂))
      (show tHR s₂ ∈ s₂.rd by rw [P₂.hrd]; simp) (P₂.kth.sub_left kR_sub) (P₂.sth.sub_left (sc_sub P₂)) hc
      (hpw₂.sublist (List.sublist_append_left _ _)) hw hh₂⟩
  have hn := MdHashTable.PPC64LE.mem_names hw
  have hn' := HashTable.PPC64LE.mem_names hw'
  have sH : ∀ {f}, f ∈ MdHashTable.PPC64LE.names vs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_left _ hf)).symm
  have sG : ∀ {f}, f ∈ HashTable.PPC64LE.names gs → s₂.syms f = s₁.syms f := fun hf =>
    (hsy _ (List.mem_append_right _ hf)).symm
  have hk : ∀ {s}, PreS w.l.G.len s → 1 ≤ kk s := fun P => Nat.le_trans (by decide) P.k1
  exact code_ct (Z := tabsOf vs gs w w') w.l.ok w.l.ct w.l.len w'.l.ok w'.l.ct w'.l.hash w'.l.len w'.l.valid
    w.l.hash w.l.valid w.sh.1 w.sh.2.1 _ _ _ _ _ _
    ⟨s₁, ⟨⟨⟨P₁, hT₁ P₁⟩, ⟨pubS_refl s₁, hk P₁⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi₁⟩,
      ⟨⟨⟨P₂, T₂⟩, ⟨p, hk P₂⟩, sG hn'.1, sG hn'.2.1, sG hn'.2.2, sH hn.1, sH hn.2.1, sH hn.2.2.1, sH hn.2.2.2.1,
        sH hn.2.2.2.2⟩, hi₂⟩⟩
    e₁ e₂

/-- `vg_rsa_pss_sign` against its contract, for the tables of `vs` and
`gs`, given a state meeting it. -/
theorem sign_verified (hc : MdHashTable.PPC64LE.Coh vs) (hc' : HashTable.PPC64LE.Coh gs)
    (hsat : ∃ s, (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s) :
    Verified PPC64LE.target (sign (MdHashTable.PPC64LE.fnsOf vs) (HashTable.PPC64LE.fnsOf gs))
      (signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  ⟨code_correct hc hc', code_constantTime hc hc', hsat⟩

end

end VG.Proof.RsaPss.PPC64LE.Sg


namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE
open VG.Proof.HashTable (symsOf symsOf_distinct readW_sep64)
open VG.Proof.HashTable.PPC64LE (TVar)
open VG.Proof.MdHashTable.PPC64LE (MVar)

/-- The words `ws` written from `p`. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 8) ws

theorem add8_toNat {p : Addr} (h : p.toNat + 8 < 2 ^ 64) : (p + 8).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 * ws.length ≤ a.toNat) → p.toNat + 8 * ws.length < 2 ^ 64 →
    a.toNat + 8 ≤ 2 ^ 64 → (putWs m p ws).readW a 64 = m.readW a 64
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h8 := add8_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_out (by rw [h8]; omega) (by rw [h8]; omega) ha, readW_sep64 (by omega) ha (by omega)]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 8 * ws.length < 2 ^ 64 →
    Abi.tableHeld 64 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega)
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h8])) (by rw [h8]; omega) (by omega), Mem.readW_writeW_self64]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p w) (p := p + 8) (ws := ws) (by rw [h8]; omega) i
        (by simp at hi; omega)
      rw [show p + BitVec.ofNat 64 (64 / 8 * (i + 1)) = p + 8 + BitVec.ofNat 64 (64 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
      simpa using this

/-- The words of a table, its functions at the addresses `symsOf ns`. -/
def tw (ns : List String) (T : FnTable) : List (BitVec 64) := T.fns.map (symsOf ns) ++ T.data

/-- The names of the tables' functions. -/
def allNames (vs : List MVar) (gs : List TVar) : List String := MdHashTable.PPC64LE.names vs ++ HashTable.PPC64LE.names gs

/-- The memory `m` with the tables of `w` at `0x300000` and `0x300100`, and
`m` itself below `0x300000`. -/
def tabMem (m : Mem) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) : Mem := fun a =>
  bif Nat.blt a.toNat 0x300000 then m a
  else putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
    (tw (allNames vs gs) (HashTable.PPC64LE.tableOf w')) a

/-- A state with `s`'s registers and regions, the tables of `w` at `0x300000`
and `0x300100`, and `vs`' functions at distinct addresses. -/
def withTabs (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) : State :=
  { s with mem := tabMem s.mem vs gs w w', syms := symsOf (allNames vs gs) }

theorem withTabs_arg (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) {j : Nat}
    (hj : (stackArgAddr s j).toNat + 8 ≤ 0x300000) : stackArg (withTabs s vs gs w w') j = stackArg s j := by
  show (tabMem s.mem vs gs w w').readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  refine Mem.readW_congr fun i hi => ?_
  have : (stackArgAddr s j + BitVec.ofNat 64 i).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [tabMem, Nat.blt_eq.mpr this, Bool.cond_true]

/-- Above `0x300000`, the tables' memory. -/
theorem tabMem_above {m : Mem} {vs : List MVar} {gs : List TVar} {w : MVar} {w' : TVar} {p : Addr} {ws : List (BitVec 64)}
    (hp : 0x300000 ≤ p.toNat) (hl : p.toNat + 8 * ws.length < 2 ^ 64)
    (h : Abi.tableHeld 64 (putWs (putWs m 0x300000 (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w))) 0x300100
      (tw (allNames vs gs) (HashTable.PPC64LE.tableOf w'))) p ws) :
    Abi.tableHeld 64 (tabMem m vs gs w w') p ws := by
  intro i hi
  rw [← h i hi]
  refine Mem.readW_congr fun k hk => ?_
  have : ¬ (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat < 0x300000 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hb : Nat.blt (p + BitVec.ofNat 64 (64 / 8 * i) + BitVec.ofNat 64 k).toNat 0x300000 = false := by
    rw [Bool.eq_false_iff]; intro hc; exact this (Nat.blt_eq.mp hc)
  simp only [tabMem, hb, Bool.cond_false]

theorem withTabs_heldH (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300000
      (FnTable.words isa (withTabs s vs gs w w') (MdHashTable.PPC64LE.tableOf w)) := by
  have hl : (tw (allNames vs gs) (MdHashTable.PPC64LE.tableOf w)).length = 11 := by
    simp [tw, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf]
  have c1 : (0x300000 : Addr).toNat = 0x300000 := rfl
  have c2 : (0x300100 : Addr).toNat = 0x300100 := rfl
  refine tabMem_above (by rw [c1]) (by simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf,
    Spec.HashTable.dataOf]) fun i hi => ?_
  have hi' : i < 11 := by
    simp [FnTable.words, MdHashTable.PPC64LE.tableOf, Spec.MdHashTable.dataOf, Spec.HashTable.dataOf] at hi; omega
  rw [putWs_out (.inl (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega))
    (by simp [tw, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf]) (by simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  exact putWs_held (by rw [hl]; decide) i (by rw [hl]; exact hi')

theorem withTabs_heldG (s : State) (vs : List MVar) (gs : List TVar) (w : MVar) (w' : TVar) :
    Abi.tableHeld 64 (withTabs s vs gs w w').mem 0x300100
      (FnTable.words isa (withTabs s vs gs w w') (HashTable.PPC64LE.tableOf w')) :=
  tabMem_above (by decide) (by simp [FnTable.words, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf])
    (putWs_held (by simp [tw, HashTable.PPC64LE.tableOf, Spec.HashTable.dataOf]))


/-! ## Verification with a precomputed key -/

/-- A state meeting verification's precondition but for the tables: a
512-bit modulus, one-byte `e`, a digest of `dl` bytes, 16 words of `pre` at
`0x5000`, the stack arguments at `0x10060`, and the tables' addresses
`0x300000` and `0x300100`. -/
def verifySatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x4600 | .r8 => BitVec.ofNat 64 dl
    | .r9 => 0x4000 | .r10 => 64 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10072 then 0x02 else bif Nat.beq a.toNat 0x10078 then 0x20
    else bif Nat.beq a.toNat 0x10079 then 0x08 else bif Nat.beq a.toNat 0x10081 then 0x50
    else bif Nat.beq a.toNat 0x10088 then 16 else bif Nat.beq a.toNat 0x10092 then 0x30
    else bif Nat.beq a.toNat 0x10099 then 0x01 else bif Nat.beq a.toNat 0x1009A then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4600, dl⟩, ⟨0x4000, 64⟩, ⟨0x5000, 128⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩,
    ⟨0x10060, 64⟩]
  wr := [⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `verifySatBase dl`. -/
def verifyArgs : Nat → BitVec 64
  | 0 => 0 | 1 => 0 | 2 => 0x20000 | 3 => 2080 | 4 => 0x5000 | 5 => 16 | 6 => 0x300000 | _ => 0x300100

theorem verifySat_args (dl : Nat) : ∀ j < 8, (stackArgAddr (verifySatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, verifySatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Verification's precondition, from the facts of a state. -/
theorem verify_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (verifySatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 8, stackArg s j = verifyArgs j)
    (hrd : s.rd = (verifySatBase dl).rd) (hwr : s.wr = (verifySatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (verSpec tsH tsG).pre s := by
  have e : (304 : Nat) = 303 + 1 := rfl
  unfold verSpec
  rw [e]
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), hg, hsp, hrd, hwr, hA, verifyArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.verifyPrecomputedTableContract, Spec.RsaPss.verifyPrecomputedTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, stackArgs_eight, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hdl']; simp; omega)
    | skip

theorem verify_sat_of {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 8, stackArg (verifySatBase dl) j = verifyArgs j) :
    (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre (withTabs (verifySatBase dl) vs gs w w') :=
  verify_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (verifySat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (verifySatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem verifySat_b16 : ∀ j < 8, stackArg (verifySatBase 16) j = verifyArgs j := by decide
theorem verifySat_b20 : ∀ j < 8, stackArg (verifySatBase 20) j = verifyArgs j := by decide
theorem verifySat_b28 : ∀ j < 8, stackArg (verifySatBase 28) j = verifyArgs j := by decide
theorem verifySat_b32 : ∀ j < 8, stackArg (verifySatBase 32) j = verifyArgs j := by decide
theorem verifySat_b48 : ∀ j < 8, stackArg (verifySatBase 48) j = verifyArgs j := by decide
theorem verifySat_b64 : ∀ j < 8, stackArg (verifySatBase 64) j = verifyArgs j := by decide

theorem verify_sat {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b16⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b20⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b28⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b32⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b48⟩
  · exact ⟨_, verify_sat_of hw hw' hl (by decide) e verifySat_b64⟩

/-! ## Signing -/

/-- A state meeting signing's precondition but for the tables: a 512-bit
modulus, one-byte `e`, primes, exponents and `qInv`, a digest of `dl` bytes,
an empty salt, a working space of 2080 words, the stack arguments at
`0x10060`, and the tables' addresses `0x300000` and `0x300100`. -/
def signSatBase (dl : Nat) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 1 | .r9 => 0x4200
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10061 then 0x43
    else bif Nat.beq a.toNat 0x10068 then 1 else bif Nat.beq a.toNat 0x10071 then 0x44
    else bif Nat.beq a.toNat 0x10078 then 1 else bif Nat.beq a.toNat 0x10081 then 0x45
    else bif Nat.beq a.toNat 0x10088 then 1 else bif Nat.beq a.toNat 0x10091 then 0x46
    else bif Nat.beq a.toNat 0x10098 then 1 else bif Nat.beq a.toNat 0x100A1 then 0x41
    else bif Nat.beq a.toNat 0x100A8 then BitVec.ofNat 8 dl else bif Nat.beq a.toNat 0x100B1 then 0x47
    else bif Nat.beq a.toNat 0x100C2 then 0x02 else bif Nat.beq a.toNat 0x100C8 then 0x20
    else bif Nat.beq a.toNat 0x100C9 then 0x08 else bif Nat.beq a.toNat 0x100D2 then 0x30
    else bif Nat.beq a.toNat 0x100D9 then 0x01 else bif Nat.beq a.toNat 0x100DA then 0x30 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4100, dl⟩, ⟨0x4700, 0⟩, ⟨0x300000, 88⟩, ⟨0x300100, 40⟩, ⟨0x10060, 128⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 2080 * 8⟩]

/-- The stack arguments of `signSatBase dl`. -/
def signArgs (dl : Nat) : Nat → BitVec 64
  | 0 => 0x4300 | 1 => 1 | 2 => 0x4400 | 3 => 1 | 4 => 0x4500 | 5 => 1 | 6 => 0x4600 | 7 => 1
  | 8 => 0x4100 | 9 => BitVec.ofNat 64 dl | 10 => 0x4700 | 11 => 0 | 12 => 0x20000 | 13 => 2080
  | 14 => 0x300000 | _ => 0x300100

theorem signSat_args (dl : Nat) : ∀ j < 16, (stackArgAddr (signSatBase dl) j).toNat + 8 ≤ 0x300000 :=
  fun j hj => by
    have c0 : (65536 : Addr).toNat = 65536 := rfl
    simp only [stackArgAddr, signSatBase, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- Signing's precondition, from the facts of a state. -/
theorem sign_pre_of {tsH tsG : List FnTable} {dl : Nat} (hdl : dl ≤ 64) {s : State}
    (hg : s.gpr = (signSatBase dl).gpr) (hsp : s.sp = 0x10000) (ha : ∀ j < 16, stackArg s j = signArgs dl j)
    (hrd : s.rd = (signSatBase dl).rd) (hwr : s.wr = (signSatBase dl).wr)
    (hH : ∃ T ∈ tsH, Abi.tableHeld 64 s.mem 0x300000 (FnTable.words isa s T))
    (hG : ∃ T ∈ tsG, Abi.tableHeld 64 s.mem 0x300100 (FnTable.words isa s T))
    (hsy : ((tsH.map (fun T : FnTable => T.fns)).flatten ++ (tsG.map (fun T : FnTable => T.fns)).flatten).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hd : Spec.RsaPss.digestLenOk 64 s.mem 0x300000 (BitVec.ofNat 64 dl)) :
    (Sg.signSpec tsH tsG).pre s := by
  have e : Sg.stackBytes = 3775 + 1 := rfl
  unfold Sg.signSpec
  rw [e]
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  have hdl' : (BitVec.ofNat 64 dl).toNat = dl := by rw [BitVec.toNat_ofNat]; omega
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), hg, hsp, hrd,
    hwr, hA, signArgs]
  simp only [String.reduceEq, ↓reduceIte, Option.map_some, Nat.reduceAdd, List.getD_cons_succ,
    List.getD_cons_zero, Option.some.injEq, exists_eq_left']
  sig_pre [Spec.RsaPss.signTableContract, Spec.RsaPss.signTableSig,
    Spec.MdHashTable.param, Spec.MdHashTable.wordCount, Spec.MdHashTable.fns, Spec.MdHashTable.dataWords,
    Spec.HashTable.param, Spec.HashTable.wordCount, Spec.HashTable.fns, Abi.withTables, Sig.wordIndex, abi,
    argRegs, Sg.stackArgs_sixteen, List.append_eq, Sig.tableRegion, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | with_reducible assumption
    | (simp only [Spec.Rsa.lenValid]; decide)
    | (rw [hdl']; rfl)
    | (rw [hdl']; apply Region.disjoint_of_sep; simp [Region.sep]; omega)
    | (rw [hdl']; simp; omega)
    | skip

theorem sign_sat_of {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) {dl : Nat} (hdl : dl ≤ 64)
    (hlen : w.l.G.len = dl) (hb : ∀ j < 16, stackArg (signSatBase dl) j = signArgs dl j) :
    (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre
      (withTabs (signSatBase dl) vs gs w w') :=
  sign_pre_of hdl rfl rfl (fun j hj => (withTabs_arg _ vs gs w w' (signSat_args dl j hj)).trans (hb j hj)) rfl rfl
    ⟨_, List.mem_map_of_mem hw, withTabs_heldH _ vs gs w w'⟩ ⟨_, List.mem_map_of_mem hw', withTabs_heldG _ vs gs w w'⟩
    (symsOf_distinct hl) fun H hH => by
      have hA := MdHashTable.PPC64LE.hashAt_tableOf
        (MdHashTable.PPC64LE.held_tableOf (withTabs_heldH (signSatBase dl) vs gs w w')).2.2.2
      cases hH.symm.trans hA
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hlen]

theorem signSat_b16 : ∀ j < 16, stackArg (signSatBase 16) j = signArgs 16 j := by decide
theorem signSat_b20 : ∀ j < 16, stackArg (signSatBase 20) j = signArgs 20 j := by decide
theorem signSat_b28 : ∀ j < 16, stackArg (signSatBase 28) j = signArgs 28 j := by decide
theorem signSat_b32 : ∀ j < 16, stackArg (signSatBase 32) j = signArgs 32 j := by decide
theorem signSat_b48 : ∀ j < 16, stackArg (signSatBase 48) j = signArgs 48 j := by decide
theorem signSat_b64 : ∀ j < 16, stackArg (signSatBase 64) j = signArgs 64 j := by decide

theorem sign_sat {vs : List MVar} {gs : List TVar} {w : MVar} (hw : w ∈ vs) {w' : TVar} (hw' : w' ∈ gs)
    (hl : (allNames vs gs).length < 2 ^ 32) :
    ∃ s, (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)).pre s := by
  have hm := w.l.lens_mem
  rw [← w.l.len] at hm
  simp only [Impl.RsaOaep.PPC64LE.lens, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b16⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b20⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b28⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b32⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b48⟩
  · exact ⟨_, sign_sat_of hw hw' hl (by decide) e signSat_b64⟩

/-! ## The instances -/

/-- What the registration checks of the variants: their functions of the
same name have the same code, there are some, and not too many names. -/
def OK (vs : List MVar) (gs : List TVar) : Prop :=
  MdHashTable.PPC64LE.Coh vs ∧ HashTable.PPC64LE.Coh gs ∧ vs ≠ [] ∧ gs ≠ [] ∧ (allNames vs gs).length < 2 ^ 32

instance (vs : List MVar) (gs : List TVar) : Decidable (OK vs gs) := by unfold OK; infer_instance

theorem ok_mem {vs : List MVar} {gs : List TVar} (h : OK vs gs) : ∃ w, w ∈ vs ∧ ∃ w', w' ∈ gs := by
  obtain ⟨-, -, h1, h2, -⟩ := h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h1
  obtain ⟨w', hw'⟩ := List.exists_mem_of_ne_nil _ h2
  exact ⟨w, hw, w', hw'⟩

/-- `vg_rsa_pss_verify_precomputed`, with the tables of `vs` and `gs`. -/
theorem verify_ok' {vs : List MVar} {gs : List TVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.verifyPrecomputed (MdHashTable.PPC64LE.fnsOf vs)
      (HashTable.PPC64LE.fnsOf gs)) (verSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  verify_verified h.1 h.2.1 (verify_sat hw hw' h.2.2.2.2)

/-- `vg_rsa_pss_sign`, with the tables of `vs` and `gs`. -/
theorem sign_ok' {vs : List MVar} {gs : List TVar} (h : OK vs gs) :
    Verified PPC64LE.target (Impl.RsaPss.PPC64LE.Sign.sign (MdHashTable.PPC64LE.fnsOf vs)
      (HashTable.PPC64LE.fnsOf gs)) (Sg.signSpec (MdHashTable.PPC64LE.tables vs) (HashTable.PPC64LE.tables gs)) :=
  let ⟨_, hw, _, hw'⟩ := ok_mem h
  Sg.sign_verified h.1 h.2.1 (sign_sat hw hw' h.2.2.2.2)

end VG.Proof.RsaPss.PPC64LE
