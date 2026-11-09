module

public import VerifiedGarbage.Proof.MdHashTable.AArch64.Tables
public import VerifiedGarbage.Proof.HashTable.AArch64
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCEnc
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyChk
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.Depth
import VerifiedGarbage.Proof.RsaPss.AArch64.Shapes

/-!
# RSASSA-PSS on AArch64 with the tables of `vs`: the instances

For variants `vs` of `MdHash` that pass the checks the registrations make
(`OK`), what signing and verification need of the tables a state holds: a
table of `MdHash` of a variant `w` of `vs` and a table of `Hash` of a
variant `w'` give the functions `tabsOf vs w w'` and the hash functions
`w.mgf.G` and `w'.mgf.G`, with which `encode` and `checkEncoding` for the
index of `w`'s hash function (whose code is that of `w`, `encode_shape`) are
correct and constant time (`esel_of`, `encCT_of`, `csel_of`, `chkCT_of`), as
on x86-64 (`Proof/RsaPss/X86_64/Instances.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.MdHashTable.AArch64 (digName idx Shape held_tableOf hashAt_tableOf finds_of)
open VG.Proof.RsaOaep.AArch64 (mgf_valid)

/-- The tables' functions for the variants `w` (of the table `hash`) and `w'`
(of the table `mgf1`). -/
def tabsOf (vs : List MdHash) (w w' : MdHash) : Tabs :=
  ⟨w.H, digName w, MdHashTable.AArch64.fnsOf vs, w'.H.stream, HashTable.AArch64.fnsOf vs,
    MdHashTable.AArch64.tables vs, HashTable.AArch64.tables vs⟩

/-- The functions the tables' calls reach push at most one frame. -/
def DepthOK (vs : List MdHash) : Prop :=
  ∀ w ∈ vs, w.H.initC.aarch64Depth ≤ 1 ∧ w.H.compC.aarch64Depth ≤ 1 ∧
    (Impl.MdHashTable.AArch64.digest w.H.P).aarch64Depth ≤ 1 ∧ w.H.updC.aarch64Depth ≤ 1 ∧
    w.H.finC.aarch64Depth ≤ 1

/-- What the registrations check of the variants whose tables the functions
take: their functions of the same name have the same code, each has the
shape of its index and each index has one, not too many names, and the
functions the tables' calls reach push at most one frame. -/
def OK (vs : List MdHash) : Prop :=
  MdHashTable.AArch64.Coh vs ∧ HashTable.AArch64.Coh vs ∧ (∀ w ∈ vs, Shape w) ∧
    (∀ i ∈ idxs, ∃ w ∈ vs, idx w = i) ∧
    (MdHashTable.AArch64.names vs ++ HashTable.AArch64.names vs).length < 2 ^ 32 ∧ DepthOK vs

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK DepthOK; infer_instance

/-! ## The code of an index -/

theorem encode_shape (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) {H : Impl.Pbkdf2.Md.AArch64.Hash}
    {i : Nat} (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) : encode f (ofIdx i) g = encode f H g := by
  show encode f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

theorem check_shape (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) {H : Impl.Pbkdf2.Md.AArch64.Hash}
    {i : Nat} (hP : H.P = (shapeOf i).1) (hD : H.D = (shapeOf i).2) :
    checkEncoding f (ofIdx i) g = checkEncoding f H g := by
  show checkEncoding f (ckH (shapeOf i).1 (shapeOf i).2) g = _
  rw [← hP, ← hD]
  rfl

theorem dig_of_shape {w : MdHash} (h : Shape w) : DigOK w.H.P := by rw [h.2.1]; exact dig_shape _ h.1

theorem pss_of_shape {w : MdHash} (h : Shape w) : PssChecks w.H.P w.H.D := by
  rw [h.2.1, h.2.2]; exact pss_shape _ h.1

variable {vs : List MdHash} (hok : OK vs)

include hok in
theorem fnsD_of : FnsD (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) where
  init q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).1
  comp q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).2.1
  dig q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).2.2.1
  gi q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).1
  gu q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).2.2.2.1
  gf q hq := by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq; exact (hok.2.2.2.2.2 w hw).2.2.2.2

/-! ## `encode` and `checkEncoding` for the index of `w` -/

section
variable {w w' : MdHash} (hw : w ∈ vs)

include hok hw in
theorem enc_of : ∀ s', (Enc.encK (tabsOf vs w w') w.mgf.G w'.mgf.G).pre s' →
    ∃ t s'', Exec isa (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx (idx w)) (HashTable.AArch64.fnsOf vs)) s' t s'' ∧
      abiPreserved s' s'' ∧ (Enc.encK (tabsOf vs w w') w.mgf.G w'.mgf.G).post s' s'' := fun s' h => by
  have hs := hok.2.2.1 w hw
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  exact Enc.enc_correct (T := tabsOf vs w w') w.ok w'.ok.stream w.mgf.hash w.mgf.len (mgf_valid w.mgf)
    w'.mgf.hash w'.mgf.len (mgf_valid w'.mgf) (dig_of_shape hs) s' h

include hok hw in
theorem encCT_of : ConstantTime isa (Enc.encK (tabsOf vs w w') w.mgf.G w'.mgf.G).pre
    (Enc.encK (tabsOf vs w w') w.mgf.G w'.mgf.G).pub
    (encode (MdHashTable.AArch64.fnsOf vs) (ofIdx (idx w)) (HashTable.AArch64.fnsOf vs)) := by
  have hs := hok.2.2.1 w hw
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  exact Enc.enc_constantTime (T := tabsOf vs w w') w.ok w'.ok.stream w.mgf.hash w'.mgf.hash w'.mgf.len
    (mgf_valid w'.mgf) (pss_of_shape hs) (dig_of_shape hs)

include hok hw in
theorem chk_of : ∀ s', (Chk.chkK (tabsOf vs w w') w.mgf.G w'.mgf.G).pre s' →
    ∃ t s'', Exec isa (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx (idx w)) (HashTable.AArch64.fnsOf vs))
      s' t s'' ∧ abiPreserved s' s'' ∧ (Chk.chkK (tabsOf vs w w') w.mgf.G w'.mgf.G).post s' s'' := fun s' h => by
  have hs := hok.2.2.1 w hw
  rw [check_shape _ _ hs.2.1 hs.2.2]
  exact Chk.chk_correct (T := tabsOf vs w w') w.ok w'.ok.stream w.mgf.hash w.mgf.len (mgf_valid w.mgf)
    w'.mgf.hash w'.mgf.len (mgf_valid w'.mgf) (dig_of_shape hs) s' h

include hok hw in
theorem chkCT_of : ConstantTime isa (Chk.chkK (tabsOf vs w w') w.mgf.G w'.mgf.G).pre
    (Chk.chkK (tabsOf vs w w') w.mgf.G w'.mgf.G).pub
    (checkEncoding (MdHashTable.AArch64.fnsOf vs) (ofIdx (idx w)) (HashTable.AArch64.fnsOf vs)) := by
  have hs := hok.2.2.1 w hw
  rw [check_shape _ _ hs.2.1 hs.2.2]
  exact Chk.chk_constantTime (T := tabsOf vs w w') w.ok w'.ok.stream w'.mgf.hash w'.mgf.len
    (mgf_valid w'.mgf) (pss_of_shape hs) (dig_of_shape hs)

end

/-! ## The tables a state holds -/

/-- The functions of the tables of `vs` at distinct addresses: those of the
tables of `MdHash`, and of `Hash`. -/
theorem distinct_split {sy : String → Addr}
    (h : (((MdHashTable.AArch64.tables vs).map (·.fns)).flatten ++
      ((HashTable.AArch64.tables vs).map (·.fns)).flatten).Pairwise fun f g => f ≠ g → sy f ≠ sy g) :
    (MdHashTable.AArch64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) ∧
      (HashTable.AArch64.names vs).Pairwise (fun f g => f ≠ g → sy f ≠ sy g) :=
  ⟨(List.pairwise_append.mp h).1, (List.pairwise_append.mp h).2.1⟩

include hok in
/-- The tables of `w` and `w'` at `pH` and `pG` name the functions `tabsOf vs w w'`. -/
theorem tabsAt_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs) {pH pG : Addr}
    (hsy : (((MdHashTable.AArch64.tables vs).map (·.fns)).flatten ++
      ((HashTable.AArch64.tables vs).map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hH : Abi.tableHeld 64 s.mem pH (FnTable.words isa s (MdHashTable.AArch64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem pG (FnTable.words isa s (HashTable.AArch64.tableOf w'))) :
    TabsAt w.H (digName w) (MdHashTable.AArch64.fnsOf vs) w'.H.stream (HashTable.AArch64.fnsOf vs) pH pG s := by
  obtain ⟨h0, h3, h4, -, -⟩ := held_tableOf hH
  obtain ⟨g0, -, g4⟩ := HashTable.AArch64.held_tableOf hG
  obtain ⟨d, d'⟩ := distinct_split hsy
  obtain ⟨fi, fc, fd⟩ := finds_of hok.1 d hw
  refine ⟨?_, h3, h4, fi, fc, fd, HashTable.AArch64.tabOK_of hok.2.1 d' hw', g0, g4⟩
  rw [show pH = VG.Proof.Bignum.off pH 0 from (BitVec.add_zero pH).symm]
  exact h0

include hok in
/-- What signing needs of the tables of `w` and `w'`, in a state that holds
them at the stack arguments 14 and 15. -/
theorem esel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (((MdHashTable.AArch64.tables vs).map (·.fns)).flatten ++
      ((HashTable.AArch64.tables vs).map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 14) (stackArg s 9))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s (HashTable.AArch64.tableOf w'))) :
    Sgn.ESel (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) (MdHashTable.AArch64.tables vs)
      (HashTable.AArch64.tables vs) s (idx w) (tabsOf vs w w') w.mgf.G w'.mgf.G := by
  have hs := hok.2.2.1 w hw
  have hA := hashAt_tableOf (held_tableOf hH).2.2.2.1
  refine ⟨hs.1, (held_tableOf hH).2.2.2.1, rfl, rfl, ⟨_, List.mem_map_of_mem hw, rfl, hH⟩,
    ⟨_, List.mem_map_of_mem hw', rfl, hG⟩, tabsAt_of hok hw hw' hsy hH hG, hA,
    HashTable.AArch64.hashAt_tableOf (HashTable.AArch64.held_tableOf hG).2.1, ((hdl _ hA).trans w.mgf.len).symm,
    w.mgf.len, enc_of hok hw, ?_⟩
  rw [encode_shape _ _ hs.2.1 hs.2.2]
  exact encode_depth (fnsD_of hok) w.H

include hok in
/-- What verification needs of the tables of `w` and `w'`, in a state that
holds them at the stack arguments 6 and 7. -/
theorem csel_of {s : State} {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs)
    (hsy : (((MdHashTable.AArch64.tables vs).map (·.fns)).flatten ++
      ((HashTable.AArch64.tables vs).map (·.fns)).flatten).Pairwise fun f g => f ≠ g → s.syms f ≠ s.syms g)
    (hdl : Spec.RsaPss.digestLenOk 64 s.mem (stackArg s 6) (s.gpr .x5))
    (hH : Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s (MdHashTable.AArch64.tableOf w)))
    (hG : Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s (HashTable.AArch64.tableOf w'))) :
    Vfy.CSel (MdHashTable.AArch64.fnsOf vs) (HashTable.AArch64.fnsOf vs) (MdHashTable.AArch64.tables vs)
      (HashTable.AArch64.tables vs) s (idx w) (tabsOf vs w w') w.mgf.G w'.mgf.G := by
  have hs := hok.2.2.1 w hw
  have hA := hashAt_tableOf (held_tableOf hH).2.2.2.1
  refine ⟨hs.1, (held_tableOf hH).2.2.2.1, rfl, rfl, ⟨_, List.mem_map_of_mem hw, rfl, hH⟩,
    ⟨_, List.mem_map_of_mem hw', rfl, hG⟩, tabsAt_of hok hw hw' hsy hH hG, hA,
    HashTable.AArch64.hashAt_tableOf (HashTable.AArch64.held_tableOf hG).2.1, ((hdl _ hA).trans w.mgf.len).symm,
    w.mgf.len, chk_of hok hw, ?_⟩
  rw [check_shape _ _ hs.2.1 hs.2.2]
  exact chk_depth (fnsD_of hok) w.H

/-- The names of `tabsOf vs w w'`'s functions the code calls are the tables'. -/
theorem names_sub {w w' : MdHash} (hw : w ∈ vs) (hw' : w' ∈ vs) :
    ∀ n ∈ (tabsOf vs w w').names, n ∈ ((MdHashTable.AArch64.tables vs).map (·.fns)).flatten ++
      ((HashTable.AArch64.tables vs).map (·.fns)).flatten := by
  have hn := MdHashTable.AArch64.mem_names hw
  have hn' := HashTable.AArch64.mem_names hw'
  intro n h
  simp only [Tabs.names, tabsOf, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_append_left _ hn.1
  · exact List.mem_append_left _ hn.2.2.2.1
  · exact List.mem_append_left _ hn.2.2.2.2
  · exact List.mem_append_right _ hn'.1
  · exact List.mem_append_right _ hn'.2.1
  · exact List.mem_append_right _ hn'.2.2

end VG.Proof.RsaPss.AArch64
