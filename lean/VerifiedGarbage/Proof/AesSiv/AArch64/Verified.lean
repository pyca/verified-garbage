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
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    ctr, ctrBody, ctrMin, ctrLeft, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
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

The proofs are against the shared contracts with the working space `W` as a
last argument (`Proof/AesSiv/Scratch.lean`), in `x7`, after `siv` (`T`) in
`x6`. They are on the state whose writable regions are the data, `T` for
`encrypt`, the first 2560 bytes of the working space and S2V's state after
them (`encWrE`, `encWrD`), where `EPre` and `SivArg` hold (`encPre_of`,
`decPre_of`); a run from it is a run from the state itself (`Exec.widen`),
so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2560⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 dOff, 16⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2560⟩, ⟨s.gpr .x7 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt`. -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff)
    (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (s : State) : Prop :=
  SivArg s (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff) (s.gpr .x6) (s.gpr .x5).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    EPub s₁ s₂ (s₁.gpr .x2) (s₁.gpr .x3).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s ∧ (⟨s.gpr .x6, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (Spec.Aes.bytesAt s'.mem (s.gpr .x6) 16, Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s
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
    EPre s₂ (s₁.gpr .x0) (s₁.gpr .x2) (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff)
      (s₁.gpr .x1).toNat (s₁.gpr .x3).toNat (s₁.gpr .x5).toNat := by
  obtain ⟨q0, q1, q2, q3, q4, q5, -, q7, -⟩ := hq
  rw [q0, q1, q2, q3, q4, q5, q7]; exact h₂

theorem SivArgS.of_pub {s₁ s₂ : State} (h₂ : SivArgS s₂) (hq : encPub s₁ s₂) :
    SivArg s₂ (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff) (s₁.gpr .x6) (s₁.gpr .x5).toNat := by
  obtain ⟨-, -, -, -, q4, q5, q6, q7, -⟩ := hq
  rw [q4, q5, q6, q7]; exact h₂

theorem encryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      encryptN.post s s' :=
  WP.withPreservedV (encrypt_wp v hs.1 hs.2.1 hs.2.2) (encrypt_keepsV v)

theorem decryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      decryptN.post s s' :=
  WP.withPreservedV (decrypt_wp v hs.1 hs.2) (decrypt_keepsV v)

theorem encryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa encryptN.pre encryptN.pub (encrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) h₁.2.2
      (by rw [hq.2.2.2.2.2.2.1]; exact h₂.2.2) hq.2.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa decryptN.pre decryptN.pub (decrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

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

/-- `EPre` and `SivArg` from the facts the shared contracts give, on the
narrowed state `σ`: the whole working space at `W` is 2576 bytes. -/
theorem mkPre {σ : State} {C A P W T : Addr} {R N L : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (x0 : σ.gpr .x0 = C) (x1 : σ.gpr .x1 = BitVec.ofNat 64 R) (x2 : σ.gpr .x2 = A)
    (x3 : σ.gpr .x3 = BitVec.ofNat 64 N) (x4 : σ.gpr .x4 = P) (x5 : σ.gpr .x5 = BitVec.ofNat 64 L)
    (x6 : σ.gpr .x6 = T) (x7 : σ.gpr .x7 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr) (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, 2560⟩ : Region) ∈ σ.wr)
    (inD : (⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2576⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, 2576⟩) (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩)
    (wA : (⟨W, 2576⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, 2576⟩ : Region).Disjoint r)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2576⟩)
    (wrC : C.toNat + 512 ≤ 2 ^ 64) (wrP : P.toNat + L ≤ 2 ^ 64) (wrT : T.toNat + 16 ≤ 2 ^ 64)
    (wrW : W.toNat + 2576 ≤ 2 ^ 64) (wrA : A.toNat + N * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r.base.toNat + r.len ≤ 2 ^ 64) (hL : L < 2 ^ 64) :
    EPre σ C A P W (W + BitVec.ofNat 64 dOff) R N L ∧ SivArg σ P W (W + BitVec.ofNat 64 dOff) T L := by
  have sw : Region.Sub ⟨W, 2560⟩ ⟨W, 2576⟩ := Region.sub_prefix (by decide)
  have sd : Region.Sub ⟨W + BitVec.ofNat 64 dOff, 16⟩ ⟨W, 2576⟩ := Offset.sub_base _ (by decide)
  have dw := Offset.disjoint_base W (d := dOff) (n := 16) (k := 2560) (by decide) (by decide)
  have wD : (W + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ wrW (show dOff < 2576 by decide)]; simp only [dOff]; omega
  have inR {r : Region} (h : r ∈ σ.wr) : r ∈ σ.rd ++ σ.wr := List.mem_append_right _ h
  have env (Q : Addr) (n : Nat) (hQ : (⟨Q, n⟩ : Region) ∈ σ.rd ++ σ.wr) (qW : (⟨Q, n⟩ : Region).Disjoint ⟨W, 2576⟩)
      (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) : Env σ C (W + BitVec.ofNat 64 dOff) Q W R n :=
    ⟨hR, rfl, inC, inR inD, hQ, inW, cW.sub_right sw, (qW.sub_right sd).symm, dw, qW.sub_right sw, wrC, wD, wQ,
      by omega, hn⟩
  exact ⟨⟨env P L (inR inP) pW wrP hL, cW.sub_right sd, cP, inP, inD, x0, x1, x2, x3, x4, x5, x7, inA,
    wA.symm.sub_right sw, wA.symm.sub_right sd, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (wrL r hr) (listed_len hr)⟩,
    ⟨x6, inT, pT.symm, tW.sub_right sw, tW.sub_right sd, wrT⟩⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `encryptN`'s on the
narrowed state. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pre s) :
    encryptN.pre (s.withRegions s.rd (encWrE s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2576⟩] := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs, List.append_eq] at h
  sig_split h
  rename_i hrd hwr hcP hcT hc1 hwC hwP hwT hwW hc3
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj] at hrd hwr hc1 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pT, pW, -, -, tW, -, -, wA, wL, -⟩ := hc1
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE s := List.mem_append_left _ hr
  have wT : (⟨s.gpr .x6, 16⟩ : Region) ∈ encWrE s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre (σ := s.withRegions s.rd (encWrE s)) (C := s.gpr .x0) (A := s.gpr .x2) (P := s.gpr .x4)
    (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    (List.mem_append_right _ wT) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _)
  exact ⟨⟨e, t, wT⟩, hwr⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `decryptN`'s on the
narrowed state. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pre s) :
    decryptN.pre (s.withRegions s.rd (encWrD s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2576⟩] := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, AArch64.abi,
    AArch64.argRegs, List.append_eq] at h
  sig_split h
  rename_i hrd hwr hcP hc1 hwC hwP hwT hwW hc3
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj] at hrd hwr hc1 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pT, pW, -, -, tW, wA, wL, -⟩ := hc1
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD s := List.mem_append_left _ hr
  exact ⟨mkPre (σ := s.withRegions s.rd (encWrD s)) (C := s.gpr .x0) (A := s.gpr .x2) (P := s.gpr .x4)
    (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _), hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {s : State}
    (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 2576⟩]) :
    Covers (encWrE s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0,
      by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), dOff, rfl, by simp [dOff]⟩

theorem encWrD_covers {s : State} (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 2576⟩]) :
    Covers (encWrD s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.AArch64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A state satisfying the precondition of `vg_aes_siv_encrypt`, with no
associated data and no data: `siv` at `0x5000`, the working space at
`0x4000`. -/
def encSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x5000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

/-- `encSat`, with `siv` read only. -/
def decSat : State := { encSat with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩] }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    AArch64.abi, AArch64.argRegs] [encSat] using encSat

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    AArch64.abi, AArch64.argRegs] [decSat, encSat] using decSat

theorem encPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.encryptScratchContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE s₁)) (s₂.withRegions s₂.rd (encWrE s₂)) := by
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.decryptScratchContract AArch64.abi 0).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD s₁)) (s₂.withRegions s₂.rd (encWrD s₂)) := by
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem encrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (encrypt v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.encryptScratchContract AArch64.abi 0) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (decrypt v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.decryptScratchContract AArch64.abi 0) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, decSat_pre.elim fun s hs => ⟨_, (decPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) decSat_pre

end VG.Proof.AesSiv.AArch64
