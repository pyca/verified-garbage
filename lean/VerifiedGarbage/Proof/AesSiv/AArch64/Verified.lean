import VerifiedGarbage.Proof.AesSiv.AArch64.Init
import VerifiedGarbage.Proof.AesSiv.AArch64.EncCT
import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch

/-!
# AES-SIV on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_cmac_aes_update`, with the implementation of `vg_aes_ctr32` that goes
with it, or for `init` any implementation of `vg_aes_ctr32`), a state
satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`, with no stack: the calls keep their return address
in `x30`, which the functions save in the working space.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.Impl.AesSiv.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_add_lt)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, Proof.CmacAes.AArch64.subkeys_keepsV v]; decide +kernel

theorem encrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (encrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [encrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, ctr,
    ctrBody, ctrMin, ctrLeft, xorBytes, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

theorem decrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (decrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [decrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, ctr,
    ctrBody, ctrMin, ctrLeft, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initAArch64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initAArch64.post s s' :=
  WP.withPreservedV (init_wp v hs) (init_keepsV v)

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract AArch64.abi 0) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initAArch64, AArch64.abi, AArch64.argRegs] [initSat]
      using initSat)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are on the state whose writable regions are the data, the first
2560 bytes of the working space and S2V's state after them (`encWr`), where
`EPre` holds (`encPre_of`); a run from it is a run from the state itself
(`Exec.widen`), so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of the proofs. -/
def encWr (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 2560⟩, ⟨s.gpr .x6 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt`. -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) (s.gpr .x6 + BitVec.ofNat 64 dOff)
    (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧
    EPub s₁ s₂ (s₁.gpr .x2) (s₁.gpr .x3).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre := EPreS
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (Spec.Aes.bytesAt s'.mem (s.gpr .x6) 16, Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre := EPreS
  post s s' :=
    match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .x6) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat = Spec.Siv.zeros (s.gpr .x5).toNat
  pub := encPub

/-- The second run's arguments are the first's. -/
theorem EPreS.of_pub {s₁ s₂ : State} (h₂ : EPreS s₂) (hq : encPub s₁ s₂) :
    EPre s₂ (s₁.gpr .x0) (s₁.gpr .x2) (s₁.gpr .x4) (s₁.gpr .x6) (s₁.gpr .x6 + BitVec.ofNat 64 dOff)
      (s₁.gpr .x1).toNat (s₁.gpr .x3).toNat (s₁.gpr .x5).toNat := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, -⟩ := hq
  rw [q0, q1, q2, q3, q4, q5, q6]; exact h₂

theorem encryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      encryptN.post s s' :=
  WP.withPreservedV (encrypt_wp v hs) (encrypt_keepsV v)

theorem decryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      decryptN.post s s' :=
  WP.withPreservedV (decrypt_wp v hs) (decrypt_keepsV v)

theorem encryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa encryptN.pre encryptN.pub (encrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁ (EPreS.of_pub h₂ hq) hq.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa decryptN.pre decryptN.pub (decrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁ (EPreS.of_pub h₂ hq) hq.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### From the shared contracts -/

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem pairFacts_ro (l : List (Region × Bool)) (h : ∀ a ∈ l, a.2 = false) : Sig.pairFacts l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [Sig.pairFacts, ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.append_nil]
    refine List.filterMap_eq_nil_iff.mpr fun b hb => ?_
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem listed_len {m : Mem} {p : Addr} {n : Nat} {r : Region} (hr : r ∈ Sig.listed 64 m .u8 p n) :
    r.len < 2 ^ 64 := by
  simp only [Sig.listed, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp only [Elem.size, Nat.mul_one]
  exact BitVec.isLt _

/-- The precondition of the shared contracts gives `EPre` on the narrowed state. -/
theorem encPre_of {s : State} (h : (Spec.Siv.encryptContract AArch64.abi 0).pre s) :
    EPreS (s.withRegions s.rd (encWr s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 2576⟩] := by
  sig_pre [Spec.Siv.encryptContract, Spec.Siv.encryptSig, AArch64.abi, AArch64.argRegs, List.append_eq] at h
  sig_split h
  rename_i hrd hwr hcp hc1 hwC hwP hwW hc3
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj] at hrd hwr hc1 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pW, -, -, wDesc, wL, -⟩ := hc1
  obtain ⟨wA, wL'⟩ := hc3
  have sw : Region.Sub ⟨s.gpr .x6, 2560⟩ ⟨s.gpr .x6, 2576⟩ := Region.sub_prefix (by decide)
  have sd : Region.Sub ⟨s.gpr .x6 + BitVec.ofNat 64 dOff, 16⟩ ⟨s.gpr .x6, 2576⟩ :=
    Offset.sub_base _ (by decide)
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWr s := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ encWr s) : r ∈ s.rd ++ encWr s := List.mem_append_right _ hr
  have w₀ : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region) ∈ encWr s := List.mem_cons_self
  have w₁ : (⟨s.gpr .x6, 2560⟩ : Region) ∈ encWr s := List.mem_cons_of_mem _ List.mem_cons_self
  have w₂ : (⟨s.gpr .x6 + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ encWr s :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have dw := Offset.disjoint_base (s.gpr .x6) (d := dOff) (n := 16) (k := 2560) (by decide) (by decide)
  have wD : (s.gpr .x6 + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ hwW (show dOff < 2576 by decide)]; simp only [dOff]; omega
  have e : Env (s.withRegions s.rd (encWr s)) (s.gpr .x0) (s.gpr .x6 + BitVec.ofNat 64 dOff) (s.gpr .x4)
      (s.gpr .x6) (s.gpr .x1).toNat (s.gpr .x5).toNat :=
    ⟨h, rfl, inRd (by rw [hrd]; exact List.mem_cons_self), inWr w₂, inWr w₀, w₁, cW.sub_right sw,
      pW.symm.sub_left sd, dw, pW.sub_right sw, hwC, wD, hwP, by omega, BitVec.isLt _⟩
  refine ⟨⟨e, cW.sub_right sd, hcp, w₀, w₂, rfl, by simp, rfl, by simp, rfl, by simp, rfl,
    inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self), wDesc.symm.sub_right sw,
    wDesc.symm.sub_right sd, wA, fun r hr => ?_⟩, hwr⟩
  exact ⟨h, rfl, e.ctxIn, e.dIn,
    inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), w₁,
    e.c_w, (wL r hr).sub_left sd, dw, (wL r hr).symm.sub_right sw, hwC, wD, wL' r hr, e.wW, listed_len hr⟩

/-- The narrowed state's regions are within the state's. -/
theorem encWr_covers {s : State} (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 2576⟩]) :
    Covers (encWr s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A run from the narrowed state is a run from the state. -/
theorem encWr_exec {c : Prog isa} {s s₁ : State} {t : List Leak}
    (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 2576⟩])
    (he : Exec isa c (s.withRegions s.rd (encWr s)) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd (encWr s)) (rd := s.rd) (wr := s.wr) he
    (Covers.append (Covers.refl s.rd) (encWr_covers hwr)) (encWr_covers hwr)

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data. -/
def encSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩]

theorem encSat_pre : ∃ s, (Spec.Siv.encryptContract AArch64.abi 0).pre s := by
  sig_implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, AArch64.abi, AArch64.argRegs] [encSat]
    using encSat

theorem encPub_of {s₁ s₂ : State} (hp : (Spec.Siv.encryptContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWr s₁)) (s₂.withRegions s₂.rd (encWr s₂)) := by
  sig_pub [Spec.Siv.encryptContract, Spec.Siv.encryptSig, AArch64.abi, AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Spec.Siv.decryptContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWr s₁)) (s₂.withRegions s₂.rd (encWr s₂)) := by
  sig_pub [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, AArch64.abi,
    AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q1, hp⟩

theorem encrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (encrypt v.callee v.ctr.callee v.ctr.suffix) (Spec.Siv.encryptContract AArch64.abi 0) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWr s)) (fun s s₁ => s₁.withRegions s.rd s.wr) (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => encWr_exec (encPre_of hs).2 he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Spec.Siv.encryptContract, Spec.Siv.encryptSig, AArch64.abi, AArch64.argRegs]
      exact hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (decrypt v.callee v.ctr.callee v.ctr.suffix) (Spec.Siv.decryptContract AArch64.abi 0) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWr s)) (fun s s₁ => s₁.withRegions s.rd s.wr) (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => encWr_exec (encPre_of hs).2 he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, AArch64.abi,
        AArch64.argRegs]
      exact hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) encSat_pre

end VG.Proof.AesSiv.AArch64
