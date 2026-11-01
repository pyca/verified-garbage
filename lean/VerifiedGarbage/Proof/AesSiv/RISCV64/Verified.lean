module

import VerifiedGarbage.Proof.AesSiv.RISCV64.Dec
import VerifiedGarbage.Proof.AesSiv.RISCV64.TopCT
public import VerifiedGarbage.Proof.AesSiv.RISCV64.MacCT
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchLists
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Entry
public import VerifiedGarbage.Proof.AesSiv.RISCV64.S2v
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.Artifact

/-!
# AES-SIV on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`Enc.lean`,
`Dec.lean`) and constant time (`TopCT.lean`) of `encrypt` and `decrypt`,
states satisfying their preconditions, and the shared contracts of
`Spec/Siv/Contract.lean` with the working space as a last argument
(`Proof/AesSiv/Scratch.lean`), then in a frame on the stack
(`Verified.stackScratchLists`). `init`'s are in `Init.lean`. As on PPC64LE
(`Proof/AesSiv/PPC64LE/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.RISCV64

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
  ⟨s.gpr .a0, s.gpr .a7, s.gpr .a2, s.gpr .a4, s.gpr .a6, (s.gpr .a1).toNat, (s.gpr .a3).toNat,
    (s.gpr .a5).toNat⟩

/-- The precondition of `encrypt`'s shared contract gives the proofs': the
arguments, the components, and `siv` writable. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s ∧ Covers [⟨(cxOf s).V, 16⟩] s.wr := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, RISCV64.abi,
    RISCV64.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.append_nil, List.append_eq] at *
  rename_i hsp cd cv fc fd fv fw hR cal hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, -, -, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨s.gpr .a0, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mV : (⟨s.gpr .a6, 16⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mW : (⟨s.gpr .a7, 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have L : Lay (cxOf s) :=
    ⟨fc, fw, cal, h, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, hR, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inWr mV)⟩⟩, fun i hi => ?_, cov_mem mV⟩
  have hm := listed_mem s.mem (s.gpr .a2) hi
  have mP : (⟨descW s.mem (s.gpr .a2) i 0, (descW s.mem (s.gpr .a2) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

/-- The precondition of `decrypt`'s shared contract gives the proofs': the
arguments and the components. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s) :
    Args (cxOf s) s ∧ Ads (cxOf s) s.mem s := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, RISCV64.abi,
    RISCV64.argRegs, List.getD] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.append_nil, List.append_eq] at *
  rename_i hsp cd fc fd fv fw hR cal hrd hwr pw fl
  obtain ⟨cW, dV, dW, dA, -, vW, wA, wL, -⟩ := pw
  obtain ⟨fA, fL⟩ := fl
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have mC : (⟨s.gpr .a0, 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mV : (⟨s.gpr .a6, 16⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mA : (⟨s.gpr .a2, 16 * (s.gpr .a3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have mD : (⟨s.gpr .a4, (s.gpr .a5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨s.gpr .a7, 2576⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have L : Lay (cxOf s) :=
    ⟨fc, fw, cal, h, by rw [Nat.mul_comm]; exact fA, fd, fv, cW, cd, by rw [Nat.mul_comm]; exact wA.symm,
      by rw [Nat.mul_comm]; exact dA.symm, dW, vW, dV.symm, hR, BitVec.isLt _⟩
  refine ⟨⟨L, rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, by simp [cxOf], rfl, rfl,
    ⟨cov_mem (inRd mC), cov_mem mW, cov_mem (inRd mA), cov_mem mD, cov_mem (inRd mV)⟩⟩, fun i hi => ?_⟩
  have hm := listed_mem s.mem (s.gpr .a2) hi
  have mP : (⟨descW s.mem (s.gpr .a2) i 0, (descW s.mem (s.gpr .a2) i 1).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  exact ⟨cov_mem (inRd mP), BitVec.isLt _, fL _ hm, (wL _ hm).symm⟩

/-! ## Correctness -/

theorem encrypt_correct (s : State) (hs : (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.RISCV64.encrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).post s s' := by
  obtain ⟨Ar, hA, hV⟩ := encPre_of hs
  obtain ⟨t, s', he, hab, hq⟩ := encrypt_wp Ar hA hV
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
    RISCV64.abi, RISCV64.argRegs, List.getD]
  exact fun _ => hq

theorem decrypt_correct (s : State) (hs : (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s) :
    ∃ t s', Exec isa Impl.AesSiv.RISCV64.decrypt s t s' ∧ abiPreserved s s' ∧
      (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).post s s' := by
  obtain ⟨Ar, hA⟩ := decPre_of hs
  obtain ⟨t, s', he, hab, hr, hd⟩ := decrypt_wp Ar hA
  refine ⟨t, s', he, hab, ?_⟩
  sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
    RISCV64.abi, RISCV64.argRegs, List.getD]
  intro _
  simp only [cxOf] at hr hd
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  have hl : ∀ x : List Byte, x.length = (s.gpr .a5).toNat → x.map (fun _ => (0 : Byte)) =
      Spec.Siv.zeros (s.gpr .a5).toNat := fun x hx => by
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
      exact hl _ (by rw [Proof.Siv.length_ctr (Spec.Siv.ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (fun y => Proof.Cmac.aesWith_length _ _ y),
        Proof.Cmac.bytesAt_length])

/-! ## Satisfiable preconditions -/

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data: the context at
`0x1000`, `siv` at `0x5000` and the working space at `0x4000`. -/
def encSat (rd wr : List Region) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x5000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := rd
  wr := wr

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract RISCV64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract RISCV64.abi 0).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩]

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract RISCV64.abi 2576).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Spec.Siv.encryptPost,
    RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩] [⟨0x3000, 0⟩, ⟨0x5000, 16⟩]

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract RISCV64.abi 2576).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, RISCV64.abi, RISCV64.argRegs, List.getD] [encSat, Mem.readW, Mem.read]
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
    (hp : s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      s₁.gpr .a7 = s₂.gpr .a7 ∧ ∀ i, i < (s₁.gpr .a3).toNat * 16 →
        s₁.mem (s₁.gpr .a2 + BitVec.ofNat 64 i) = s₂.mem (s₁.gpr .a2 + BitVec.ofNat 64 i)) :
    Args (cxOf s₁) s₂ ∧ Ads (cxOf s₁) s₂.mem s₂ ∧ DescAgree (cxOf s₁) s₁.mem s₂.mem := by
  obtain ⟨-, q3, q4, q5, q6, q7, q8, q9, q10, hd⟩ := hp
  have hcx : cxOf s₂ = cxOf s₁ := by simp only [cxOf, q3, q4, q5, q6, q7, q8, q9, q10]
  rw [hcx] at A₂ hA₂
  exact ⟨A₂, hA₂, fun i hi => ⟨descW_eq hd hi (by decide), descW_eq hd hi (by decide)⟩⟩

theorem encrypt_verified : Verified RISCV64.target Impl.AesSiv.RISCV64.encrypt
    (Proof.AesSiv.encryptScratchContract RISCV64.abi 0) := by
  refine ⟨encrypt_correct, VG.Proof.Gather.RISCV64.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, encSat_pre⟩
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, RISCV64.abi, RISCV64.argRegs,
    List.getD] at hp
  obtain ⟨A₁, hA₁, -⟩ := encPre_of h₁
  obtain ⟨A₂, hA₂, -⟩ := encPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ hp
  exact encrypt_rel A₁ A₂' hA₁ hA₂' hd hp.1

theorem decrypt_verified : Verified RISCV64.target Impl.AesSiv.RISCV64.decrypt
    (Proof.AesSiv.decryptScratchContract RISCV64.abi 0) := by
  refine ⟨decrypt_correct, VG.Proof.Gather.RISCV64.ct_of fun s₁ s₂ h₁ h₂ hp => ?_, decSat_pre⟩
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptLeak,
    RISCV64.abi, RISCV64.argRegs, List.getD] at hp
  obtain ⟨hsp, -, hr⟩ := hp
  obtain ⟨A₁, hA₁⟩ := decPre_of h₁
  obtain ⟨A₂, hA₂⟩ := decPre_of h₂
  obtain ⟨A₂', hA₂', hd⟩ := enc_two A₂ hA₂ ⟨hsp, hr⟩
  exact decrypt_rel A₁ A₂' hA₁ hA₂' hd hsp

/-! ## The working space on the stack -/

/-- `encrypt` with its working space in a frame of 2576 bytes. -/
theorem encrypt_framed : Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2576 .a7
    Impl.AesSiv.RISCV64.encrypt) (Spec.Siv.encryptContract RISCV64.abi 2576) :=
  RISCV64.Verified.stackScratchLists (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre RISCV64.abi.ptrBits) (post := Spec.Siv.encryptPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) encrypt_verified (by decide) (by decide) encFrameSat_pre

/-- `decrypt` with its working space in a frame of 2576 bytes. -/
theorem decrypt_framed : Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 2576 .a7
    Impl.AesSiv.RISCV64.decrypt) (Spec.Siv.decryptContract RISCV64.abi 2576) :=
  RISCV64.Verified.stackScratchLists (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre RISCV64.abi.ptrBits) (post := Spec.Siv.decryptPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) (leak := some (Spec.Siv.decryptLeak RISCV64.abi.ptrBits))
    decrypt_verified (by decide) (by decide) decFrameSat_pre

end VG.Proof.AesSiv.RISCV64
