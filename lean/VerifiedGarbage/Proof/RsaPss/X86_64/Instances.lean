module

public import VerifiedGarbage.Proof.MdHashTable.X86_64.Tables
public import VerifiedGarbage.Proof.HashTable.X86_64
public import VerifiedGarbage.Proof.RsaPss.X86_64.SignCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.PcCCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.EncCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.Shapes
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSASSA-PSS on x86-64 with the tables of `vs`: the instances

For variants `vs` of `MdHash` that pass the checks the registrations make
(`OK`), what signing and verification need of the tables a state holds: a
table of `MdHash` of a variant `w` of `vs` and a table of `Hash` of a
variant `w'` give the functions `tabsOf vs w w'` and the hash functions
`w.mgf.G` and `w'.mgf.G`, which every state whose public data agree also
holds, and with which `encode` and `checkEncoding` for the index of `w`'s hash
function (whose code is that of `w`, `encode_shape`) are correct and
constant time (`esel_of`, `sgood_of`, `ksel_of`, `kgood_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (MdHash HashOK MgfLink)
open VG.Proof.MdHashTable.X86_64 (digName idx Shape held_tableOf hashAt_tableOf htf_of mem_names)
open VG.Proof.Bignum (off)

/-- The tables' functions for the variants `w` (of the table `hash`) and `w'`
(of the table `mgf1`). -/
def tabsOf (vs : List MdHash) (w w' : MdHash) : Tabs :=
  ⟨w.H, digName w, MdHashTable.X86_64.fnsOf vs, w'.H.stream, HashTable.X86_64.fnsOf vs⟩

/-- What the registrations check of the variants whose tables the functions
take: their functions of the same name have the same code, each has the
shape of its index and each index has one, and not too many names. -/
def OK (vs : List MdHash) : Prop :=
  MdHashTable.X86_64.Coh vs ∧ HashTable.X86_64.Coh vs ∧ (∀ w ∈ vs, Shape w) ∧
    (∀ i ∈ idxs, ∃ w ∈ vs, idx w = i) ∧
    (MdHashTable.X86_64.names vs ++ HashTable.X86_64.names vs).length < 2 ^ 32

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

/-! ## The code of an index -/

theorem encode_shape (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) {H : Impl.Pbkdf2.Md.X86_64.Hash} {i : Nat}
    (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) : encode f (ofIdx i) g = encode f H g := by
  show encode f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

theorem check_shape (f : MdFns) (g : Impl.Mgf1.X86_64.Table.Fns) {H : Impl.Pbkdf2.Md.X86_64.Hash} {i : Nat}
    (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) : checkEncoding f (ofIdx i) g = checkEncoding f H g := by
  show checkEncoding f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

/-! ## The functions the tables' calls reach -/

theorem allSafe {c : Prog isa} (h1 : c.allInstrs (fun i => !isa.writesSp i) = true)
    (h2 : c.allInstrs (fun i => !loadsMxcsr i) = true) : c.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, h1, h2]; rfl

theorem mdFns_safe {vs : List MdHash} (hs : ∀ w ∈ vs, Shape w) : MdFnsSafe (MdHashTable.X86_64.fnsOf vs) where
  init q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.iSp w.K.iMx, by dsimp only; rw [w.K.iXD]⟩
  comp q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.cSp w.K.cMx, by dsimp only; rw [w.K.cXD]⟩
  dig q hq := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hi, hP, -⟩ := hs w hw
    dsimp only
    rw [hP]
    exact dig_safe _ hi

theorem hFns_safe (vs : List MdHash) : FnsSafe (HashTable.X86_64.fnsOf vs) where
  init q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    exact ⟨allSafe w.K.iSp w.K.iMx, by dsimp only; rw [w.K.iXD]; omega⟩
  upd q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    refine ⟨allSafe (spAll_of (RsaOaep.X86_64.SpSafe.of_noSp w.ok.updSp)) w.ok.updMx, ?_⟩
    dsimp only
    rw [x86_64Depth_noSp w.ok.updSp]
    have := w.ok.updDepth
    omega
  fin q hq := by
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
    refine ⟨allSafe (spAll_of (RsaOaep.X86_64.SpSafe.of_noSp w.ok.finSp)) w.ok.finMx, ?_⟩
    dsimp only
    rw [x86_64Depth_noSp w.ok.finSp]
    have := w.ok.finDepth
    omega

theorem link_valid {H : Impl.Pbkdf2.Md.X86_64.Hash} (hH : HashOK H) (l : MgfLink H hH) : Proof.Mgf1.Valid l.G :=
  ⟨by rw [l.len]; exact hH.hD0, fun x => by
    rw [l.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, l.len]
    exact Nat.min_eq_left hH.hDN⟩

theorem dig_of_shape {w : MdHash} (h : Shape w) : DigOK w.H := DigOK.of_P h.2.1 (dig_shape _ h.1)

theorem pss_of_shape {w : MdHash} (h : Shape w) : PssChecks w.H.P w.H.D := by
  rw [h.2.1, h.2.2]; exact pss_shape _ h.1

variable {vs : List MdHash} (hok : OK vs)

theorem idx_lt (w : MdHash) : idx w < 2 ^ 64 := by
  have hm := w.mgf.mem
  simp only [idx]
  simp only [Proof.Pbkdf2.Md.X86_64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e <;> rw [e] <;> decide

theorem sp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !isa.writesSp i) = true) : SpSafe c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

include hok in
/-- The code for each index never writes `rsp`, and uses at most `encStack`
or `chkStack` bytes of stack. -/
theorem enc_safe : ∀ i ∈ idxs, SpSafe (encode (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)) ∧
    (encode (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)).x86_64Depth ≤ encStack := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  have hs := hok.2.2.1 w hw
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  refine ⟨sp_of_all ?_, Enc.enc_xd (T := tabsOf vs w w) (mdFns_safe hok.2.2.1) (hFns_safe vs)⟩
  exact Enc.enc_spAll (T := tabsOf vs w w) w.ok (mdFns_safe hok.2.2.1) (hFns_safe vs)

include hok in
theorem chk_safe : ∀ i ∈ idxs, SpSafe (checkEncoding (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)) ∧
    (checkEncoding (MdHashTable.X86_64.fnsOf vs) (ofIdx i) (HashTable.X86_64.fnsOf vs)).x86_64Depth ≤ chkStack := by
  intro i hi
  obtain ⟨w, hw, rfl⟩ := hok.2.2.2.1 i hi
  have hs := hok.2.2.1 w hw
  rw [check_shape _ _ hs.2.1 hs.2.2]
  refine ⟨sp_of_all ?_, Chk.chk_xd (T := tabsOf vs w w) (mdFns_safe hok.2.2.1) (hFns_safe vs)⟩
  exact Chk.chk_spAll (T := tabsOf vs w w) w.ok (mdFns_safe hok.2.2.1) (hFns_safe vs)

/-! ## The tables a state holds -/

/-- The functions of the tables of `vs` at distinct addresses: those of the
tables of `MdHash`, and of `Hash`. -/
theorem distinct_split {sy : String → Addr}
    (h : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → sy f ≠ sy g) :
    (MdHashTable.X86_64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) ∧
      (HashTable.X86_64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) :=
  ⟨(List.pairwise_append.mp h).1, (List.pairwise_append.mp h).2.1⟩

/-- Two states whose names of the tables' functions agree, holding the tables
of `w` and `w'`, have the same words of them. -/
theorem tabWords_eq {s a : State} {pH pG : Addr} {pH' pG' : Addr} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : ∀ f ∈ tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs), a.syms f = s.syms f)
    (hs : Abi.tableHeld 64 s.mem pH (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hs' : Abi.tableHeld 64 s.mem pG (FnTable.words isa s (HashTable.X86_64.tableOf w')))
    (ha : Abi.tableHeld 64 a.mem pH' (FnTable.words isa a (MdHashTable.X86_64.tableOf w)))
    (ha' : Abi.tableHeld 64 a.mem pG' (FnTable.words isa a (HashTable.X86_64.tableOf w'))) :
    tabWords s.mem pH pG = tabWords a.mem pH' pG' := by
  obtain ⟨s0, s3, s4, -⟩ := held_tableOf hs
  obtain ⟨a0, a3, a4, -⟩ := held_tableOf ha
  obtain ⟨⟨t0, t1, t2⟩, -, t4⟩ := HashTable.X86_64.held_tableOf hs'
  obtain ⟨⟨b0, b1, b2⟩, -, b4⟩ := HashTable.X86_64.held_tableOf ha'
  have n := mem_names hw
  have n' := HashTable.X86_64.mem_names hw'
  have e : ∀ f, f ∈ MdHashTable.X86_64.names vs → a.syms f = s.syms f := fun f hf =>
    hsy f (List.mem_append_left _ hf)
  have e' : ∀ f, f ∈ HashTable.X86_64.names vs → a.syms f = s.syms f := fun f hf =>
    hsy f (List.mem_append_right _ hf)
  have t0' : s.mem.readW (off pG 0) 64 = _ := t0
  have t1' : s.mem.readW (off pG 8) 64 = _ := t1
  have t2' : s.mem.readW (off pG 16) 64 = _ := t2
  have b0' : a.mem.readW (off pG' 0) 64 = _ := b0
  have b1' : a.mem.readW (off pG' 8) 64 = _ := b1
  have b2' : a.mem.readW (off pG' 16) 64 = _ := b2
  simp only [tabWords, s0, s3, s4, a0, a3, a4, t0', t1', t2', b0', b1', b2', t4, b4, e _ n.1, e _ n.2.2.2.1,
    e _ n.2.2.2.2, e' w'.H.stream.initN n'.1, e' w'.H.stream.updN n'.2.1, e' w'.H.stream.finN n'.2.2]

include hok in
/-- What encoding needs of the tables of `w` and `w'`, in a state that holds
them at the stack arguments 16 and 17. -/
theorem esel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 16) (stackArg s 11))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 16) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 17) (FnTable.words isa s (HashTable.X86_64.tableOf w'))) :
    ESel (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) s (idx w) (tabsOf vs w w') w.mgf.G w'.mgf.G := by
  obtain ⟨h0, h3, h4, h5, -⟩ := held_tableOf hH
  obtain ⟨⟨g0, g1, g2⟩, g3, g4⟩ := HashTable.X86_64.held_tableOf hG
  have hs := hok.2.2.1 w hw
  obtain ⟨d, d'⟩ := distinct_split hsy
  have hA := hashAt_tableOf h5
  have t := HashTable.X86_64.tabOK_of hok.2.1 d' hw'
  refine ⟨hs.1, h5, ⟨h0, h3, h4, g0, g1, g2, g4, htf_of hok.1 d hw, ⟨t.i, t.u, t.f⟩⟩, hA,
    HashTable.X86_64.hashAt_tableOf g3, ((hdl _ hA).trans w.mgf.len).symm, fun s' h => ?_⟩
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  exact Enc.enc_correct (T := tabsOf vs w w') w.ok w.K w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
    (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) w.mgf s' h

include hok in
/-- What verification needs of the tables of `w` and `w'`, in a state that
holds them at the stack arguments 8 and 9. -/
theorem ksel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (tabFns (MdHashTable.X86_64.tables vs) ++ tabFns (HashTable.X86_64.tables vs)).Pairwise
      fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 8) (s.gpr .r9))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (HashTable.X86_64.tableOf w'))) :
    Pc.KSel (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) s (idx w) (tabsOf vs w w') w.mgf.G
      w'.mgf.G := by
  obtain ⟨h0, h3, h4, h5, -⟩ := held_tableOf hH
  obtain ⟨⟨g0, g1, g2⟩, g3, g4⟩ := HashTable.X86_64.held_tableOf hG
  have hs := hok.2.2.1 w hw
  obtain ⟨d, d'⟩ := distinct_split hsy
  have hA := hashAt_tableOf h5
  have t := HashTable.X86_64.tabOK_of hok.2.1 d' hw'
  refine ⟨hs.1, h5, ⟨h0, h3, h4, g0, g1, g2, g4, htf_of hok.1 d hw, ⟨t.i, t.u, t.f⟩⟩, hA,
    HashTable.X86_64.hashAt_tableOf g3, ((hdl _ hA).trans w.mgf.len).symm, fun s' h => ?_⟩
  rw [check_shape _ _ hs.2.1 hs.2.2]
  exact Chk.chk_correct (T := tabsOf vs w w') w.ok w.K w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
    (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) w.mgf s' h

theorem tidx_read {m : Mem} {p : Addr} {s : State} {w : MdHash}
    (h : Abi.tableHeld 64 m p (FnTable.words isa s (MdHashTable.X86_64.tableOf w))) :
    (m.readW (off p 40) 64).toNat = idx w := by
  rw [(held_tableOf h).2.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (idx_lt w)]

include hok in
/-- Signing's: the tables of the first run's entry state `a`, which every
state whose public data agree with it holds. -/
theorem sgood_of {a : State}
    (ha : (signK (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pre a) :
    ∃ T Hs Gs, SGood (tsH := MdHashTable.X86_64.tables vs) (tsG := HashTable.X86_64.tables vs)
      (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) a T Hs Gs := by
  have hp := SPre.of _ _ ha
  obtain ⟨_, hT, hwa⟩ := hp.tabH
  obtain ⟨w, wm, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hwa'⟩ := hp.tabG
  obtain ⟨w', wm', rfl⟩ := List.mem_map.mp hT'
  have hs := hok.2.2.1 w wm
  have hidx : sidx a = idx w := tidx_read hwa
  refine ⟨tabsOf vs w w', w.mgf.G, w'.mgf.G, ⟨fun s hpub hps => ?_, fun s hpub hps => ?_, ?_⟩⟩
  · have p := SPre.of _ _ hps
    rw [hidx]
    exact esel_of hok wm wm' p.hsy p.hdl ((hpub.2.2.2.2.2.1 _ hT).mp hwa) ((hpub.2.2.2.2.2.2 _ hT').mp hwa')
  · exact tabWords_eq wm wm' hpub.2.2.2.2.1 ((hpub.2.2.2.2.2.1 _ hT).mp hwa) ((hpub.2.2.2.2.2.2 _ hT').mp hwa')
      hwa hwa'
  · rw [hidx, encode_shape _ _ hs.2.1 hs.2.2]
    exact Enc.enc_ct (T := tabsOf vs w w') w.ok w.K w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
      (mdFns_safe hok.2.2.1) (hFns_safe vs) (dig_of_shape hs) (pss_of_shape hs) w.mgf.G

include hok in
/-- Verification's. -/
theorem kgood_of {a : State} (ha : Pc.Pre (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs) a) :
    ∃ T Hs Gs, Pc.KGood (tsH := MdHashTable.X86_64.tables vs) (tsG := HashTable.X86_64.tables vs)
      (MdHashTable.X86_64.fnsOf vs) (HashTable.X86_64.fnsOf vs) a T Hs Gs := by
  obtain ⟨_, hT, hwa⟩ := ha.tabH
  obtain ⟨w, wm, rfl⟩ := List.mem_map.mp hT
  obtain ⟨_, hT', hwa'⟩ := ha.tabG
  obtain ⟨w', wm', rfl⟩ := List.mem_map.mp hT'
  have hs := hok.2.2.1 w wm
  have hidx : Pc.vidx a = idx w := tidx_read hwa
  have hH : ∀ s, (verifyK (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pub a s →
      Abi.tableHeld 64 s.mem (stackArg s 8) (FnTable.words isa s (MdHashTable.X86_64.tableOf w)) := fun s hpub =>
    (hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hT).mp hwa
  have hG : ∀ s, (verifyK (MdHashTable.X86_64.tables vs) (HashTable.X86_64.tables vs)).pub a s →
      Abi.tableHeld 64 s.mem (stackArg s 9) (FnTable.words isa s (HashTable.X86_64.tableOf w')) := fun s hpub =>
    (hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hT').mp hwa'
  refine ⟨tabsOf vs w w', w.mgf.G, w'.mgf.G, ⟨fun s hpub hps => ?_, fun s hpub hps => ?_, ?_⟩⟩
  · rw [hidx]
    exact ksel_of hok wm wm' hps.hsy hps.hdl (hH s hpub) (hG s hpub)
  · exact tabWords_eq wm wm' hpub.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hH s hpub) (hG s hpub) hwa hwa'
  · rw [hidx, check_shape _ _ hs.2.1 hs.2.2]
    exact Chk.chk_ct (T := tabsOf vs w w') w.ok w.K w'.ok.stream w'.mgf.hash w'.mgf.len (link_valid w'.ok w'.mgf)
      (dig_of_shape hs) (pss_of_shape hs) w.mgf.G

end VG.Proof.RsaPss.X86_64
