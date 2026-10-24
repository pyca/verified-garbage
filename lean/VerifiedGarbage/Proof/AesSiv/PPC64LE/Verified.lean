module

import VerifiedGarbage.Proof.AesSiv.PPC64LE.Dec
import VerifiedGarbage.Proof.AesSiv.PPC64LE.TopCT
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.MacCT
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchLists
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Init
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Impl.AesSiv.PPC64LE
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Entry
public import VerifiedGarbage.Proof.AesSiv.PPC64LE.S2v
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.PPC64LE

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

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- Component `i`'s region, as the descriptors list it. -/
theorem listed_mem (m : Mem) (A : Addr) {N i : Nat} (hi : i < N) :
    (⟨descW m A i 0, (descW m A i 1).toNat⟩ : Region) ∈ Sig.listed 64 m .u8 A N :=
  List.mem_map.mpr ⟨i, List.mem_range.mpr hi, listed_eq m A i⟩

/-- The public values of `encrypt` and `decrypt`, in their registers. -/
def cxOf (s : State) : Cx :=
  ⟨s.gpr .r3, s.gpr .r10, s.gpr .r5, s.gpr .r7, s.gpr .r9, (s.gpr .r4).toNat, (s.gpr .r6).toNat,
    (s.gpr .r8).toNat⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `encrypt`'s shared contract gives the proofs': the
arguments, the components, and `siv` writable. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract PPC64LE.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s ∧ Covers [⟨(cxOf s).V, 16⟩] s.wr := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, PPC64LE.abi,
    PPC64LE.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons, List.append_nil, List.append_eq] at *
  rename_i cd cv fc fd fv fw hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, -, -, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨s.gpr .r3, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨s.gpr .r7, (s.gpr .r8).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mV : (⟨s.gpr .r9, 16⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨s.gpr .r10, 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have L : Lay (cxOf s) :=
    ⟨fc, fw, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, h, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inWr mV)⟩⟩, fun i hi => ?_, cov_mem mV⟩
  have hm := listed_mem s.mem (s.gpr .r5) hi
  have mP : (⟨descW s.mem (s.gpr .r5) i 0, (descW s.mem (s.gpr .r5) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of `decrypt`'s shared contract gives the proofs': the
arguments and the components. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract PPC64LE.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, PPC64LE.abi,
    PPC64LE.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons, List.append_nil, List.append_eq] at *
  rename_i cd fc fd fv fw hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have mC : (⟨s.gpr .r3, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mV : (⟨s.gpr .r9, 16⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mD : (⟨s.gpr .r7, (s.gpr .r8).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨s.gpr .r10, 2576⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have L : Lay (cxOf s) :=
    ⟨fc, fw, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, h, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inRd mV)⟩⟩, fun i hi => ?_⟩
  have hm := listed_mem s.mem (s.gpr .r5) hi
  have mP : (⟨descW s.mem (s.gpr .r5) i 0, (descW s.mem (s.gpr .r5) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

/-! ## Correctness -/

theorem encrypt_correct (s : State) (hs : (Proof.AesSiv.encryptScratchContract PPC64LE.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.PPC64LE.encrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.encryptScratchContract PPC64LE.abi 0).post s s' := by
  obtain ⟨Ar, hA, hV⟩ := encPre_of hs
  obtain ⟨t, s', he, hab, hq⟩ := encrypt_wp Ar hA hV
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
    PPC64LE.abi, PPC64LE.argRegs, List.getD]
  exact fun _ => hq

theorem decrypt_correct (s : State) (hs : (Proof.AesSiv.decryptScratchContract PPC64LE.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.PPC64LE.decrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.decryptScratchContract PPC64LE.abi 0).post s s' := by
  obtain ⟨Ar, hA⟩ := decPre_of hs
  obtain ⟨t, s', he, hab, hr, hd⟩ := decrypt_wp Ar hA
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
    PPC64LE.abi, PPC64LE.argRegs, List.getD]
  intro _
  simp only [cxOf] at hr hd
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  have hl : ∀ x : List Byte, x.length = (s.gpr .r8).toNat → x.map (fun _ => (0 : Byte)) =
      Spec.Siv.zeros (s.gpr .r8).toNat := fun x hx => by
    rw [List.map_const', hx]; rfl
  split
  · rename_i pt heq
    split at heq
    · rename_i hT
      obtain rfl := Option.some.inj heq
      simp only [eq_true hT.symm, ite_true, List.map_id'] at hr hd
      exact ⟨by rw [hr]; rfl, hd⟩
    · cases heq
  · rename_i heq
    split at heq
    · cases heq
    · rename_i hT
      simp only [eq_false (Ne.symm hT), ite_false] at hr hd
      refine ⟨by rw [hr]; rfl, ?_⟩
      rw [hd]
      exact hl _ (by rw [Proof.Siv.length_ctr (Spec.Siv.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (fun y => Proof.Cmac.aesWith_length _ _ y),
        Proof.Cmac.bytesAt_length])

/-! ## `vg_aes_siv_init` -/

/-- A state satisfying `vg_aes_siv_init`'s precondition: a 32-byte key at
`0x1000`, the context at `0x2000` and the scratch buffer at `0x3000`. -/
def initSat : State where
  gpr r := match r with | .r3 => 0x1000 | .r4 => 32 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified PPC64LE.target Impl.AesSiv.PPC64LE.init
    (Proof.AesSiv.initScratchContract PPC64LE.abi 0) :=
  Verified.of_correct init_correct init_ct (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initPPC64LE, PPC64LE.abi, PPC64LE.argRegs, List.getD] [initSat] using initSat)

/-- `initSat` without the scratch buffer. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    PPC64LE.abi, PPC64LE.argRegs, List.getD] [initFrameSat, initSat] using initFrameSat

/-- `init` with its scratch buffer in a frame of 2592 bytes. -/
theorem init_framed : Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6
    Impl.AesSiv.PPC64LE.init) (Spec.Siv.initContract PPC64LE.abi 2592) :=
  Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre PPC64LE.abi.ptrBits) (post := Spec.Siv.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) init_verified (by decide) (by decide)
    (Proof.AesSiv.initPre_local _) (Proof.AesSiv.initPost_local _) initFrameSat_pre

/-! ## Satisfiable preconditions -/

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data: the context at
`0x1000`, `siv` at `0x5000` and the working space at `0x4000`. -/
def encSat (rd wr : List Region) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r7 => 0x3000 | .r9 => 0x5000 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := rd
  wr := wr

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract PPC64LE.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    PPC64LE.abi, PPC64LE.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract PPC64LE.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, PPC64LE.abi, PPC64LE.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩]

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract PPC64LE.abi 2608).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Spec.Siv.encryptPost,
    PPC64LE.abi, PPC64LE.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩]

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract PPC64LE.abi 2608).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, PPC64LE.abi, PPC64LE.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩]

/-! ## Constant time -/

/-- Descriptors whose bytes are the same in two memories have the same words. -/
theorem descW_eq {m m' : Mem} {A : Addr} {N : Nat}
    (h : ∀ k < N * 16, m (A + BitVec.ofNat 64 k) = m' (A + BitVec.ofNat 64 k))
    {i j : Nat} (hi : i < N) (hj : j < 2) : descW m A i j = descW m' A i j := by
  have e := Mem.read_congr (m := m) (m' := m') (a := A + BitVec.ofNat 64 (16 * i + 8 * j))
    (n := 64 / 8) fun k hk => by rw [Offset.add_add]; exact h _ (by omega)
  simp only [descW, Mem.readW, e]

/-- Two runs from the same public arguments: both from the public values of
the first, with the same descriptors. -/
theorem enc_two {s₁ s₂ : State} (A₂ : Args (cxOf s₂) s₂) (hA₂ : Ads (cxOf s₂) s₂.mem s₂)
    (hp : s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .r10 = s₂.gpr .r10 ∧ ∀ i, i < (s₁.gpr .r6).toNat * 16 →
        s₁.mem (s₁.gpr .r5 + BitVec.ofNat 64 i) = s₂.mem (s₁.gpr .r5 + BitVec.ofNat 64 i)) :
    Args (cxOf s₁) s₂ ∧ Ads (cxOf s₁) s₂.mem s₂ ∧ DescAgree (cxOf s₁) s₁.mem s₂.mem := by
  obtain ⟨-, q3, q4, q5, q6, q7, q8, q9, q10, hd⟩ := hp
  have hcx : cxOf s₂ = cxOf s₁ := by simp only [cxOf, q3, q4, q5, q6, q7, q8, q9, q10]
  rw [hcx] at A₂ hA₂
  exact ⟨A₂, hA₂, fun i hi => ⟨descW_eq hd hi (by decide), descW_eq hd hi (by decide)⟩⟩

theorem encrypt_verified : Verified PPC64LE.target Impl.AesSiv.PPC64LE.encrypt
    (Proof.AesSiv.encryptScratchContract PPC64LE.abi 0) := by
  refine ⟨encrypt_correct, VG.Proof.Gather.PPC64LE.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, encSat_pre⟩
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, PPC64LE.abi, PPC64LE.argRegs,
    List.getD] at hp
  obtain ⟨A₁, hA₁, -⟩ := encPre_of h₁
  obtain ⟨A₂, hA₂, -⟩ := encPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ hp
  exact encrypt_rel A₁ A₂' hA₁ hA₂' hd hp.1

theorem decrypt_verified : Verified PPC64LE.target Impl.AesSiv.PPC64LE.decrypt
    (Proof.AesSiv.decryptScratchContract PPC64LE.abi 0) := by
  refine ⟨decrypt_correct, VG.Proof.Gather.PPC64LE.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, decSat_pre⟩
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak,
    PPC64LE.abi, PPC64LE.argRegs, List.getD] at hp
  obtain ⟨hsp, -, hr⟩ := hp
  obtain ⟨A₁, hA₁⟩ := decPre_of h₁
  obtain ⟨A₂, hA₂⟩ := decPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ ⟨hsp, hr⟩
  exact decrypt_rel A₁ A₂' hA₁ hA₂' hd hsp

/-! ## The working space on the stack -/

/-- `encrypt` with its working space in a frame of 2608 bytes. -/
theorem encrypt_framed : Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10
    Impl.AesSiv.PPC64LE.encrypt) (Spec.Siv.encryptContract PPC64LE.abi 2608) :=
  Verified.stackScratchLists (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre PPC64LE.abi.ptrBits) (post := Spec.Siv.encryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2608) encrypt_verified (by decide) (by decide)
    (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _) encFrameSat_pre

/-- `decrypt` with its working space in a frame of 2608 bytes. -/
theorem decrypt_framed : Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2608 .r10
    Impl.AesSiv.PPC64LE.decrypt) (Spec.Siv.decryptContract PPC64LE.abi 2608) :=
  Verified.stackScratchLists (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre PPC64LE.abi.ptrBits) (post := Spec.Siv.decryptPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2608) (leak := some (Spec.Siv.decryptLeak PPC64LE.abi.ptrBits))
    decrypt_verified (by decide) (by decide)
    (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _) decFrameSat_pre
    (hleak := Proof.AesSiv.decryptLeak_local _)

end VG.Proof.AesSiv.PPC64LE
