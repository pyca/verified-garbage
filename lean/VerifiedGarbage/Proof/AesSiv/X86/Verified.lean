import VerifiedGarbage.Proof.AesSiv.X86.EncCT
import VerifiedGarbage.Proof.AesSiv.X86.Init
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.X86.Inline

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.Impl.AesSiv.X86
open VG.Proof.AesGcm.X86 (w64 ofNat_toNat32 argsR)

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

theorem below_eq56 {SP : BitVec 32} (h : 56 ≤ SP.toNat) : below SP 56 = ⟨w64 SP - BitVec.ofNat 64 56, 56⟩ := by
  simp only [below, Region.mk.injEq, and_true]
  exact VG.X86.Taint.sub_setWidth h

/-- The entry's public values, from the shared contracts' precondition. -/
abbrev ETopS (s : State) : Prop :=
  ETop (arg s 0) (arg s 6) (s.gpr .esp) (arg s 2) (arg s 4) (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat
    (compA s.mem (arg s 2)) (compL s.mem (arg s 2)) s

theorem encPre_of {s : State} (h : (Spec.Siv.encryptContract X86.abi 56).pre s) : ETopS s := by
  sig_pre [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  sig_split h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, List.map_id', Sig.conj_cons,
    Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.filterMap_cons, List.filterMap_nil,
    List.append_nil, Sig.conj, List.append_eq, filter_true', filter_false', filterMap_some', filterMap_none',
    List.filter_map] at *
  rename_i sp56 fa cd rc rd rw fc fd fw hrd hwr hc1 hc2 hc3
  obtain ⟨cW, ⟨-, cA⟩, dW, dDesc, ⟨dL, dA⟩, wDesc, ⟨wL, wA⟩, ⟨-, descA⟩, -⟩ := hc1
  obtain ⟨retDesc, ⟨retL, retA⟩, sC, sD, sW, sDesc, sL, sA⟩ := hc2
  obtain ⟨descFit, lFit⟩ := hc3
  have bE := below_eq56 sp56
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have mC : (⟨w64 (arg s 0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨w64 (arg s 2), 8 * (arg s 3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mD : (⟨w64 (arg s 4), (arg s 5).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mW : (⟨w64 (arg s 6), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mR : (⟨argAddr s 0, 28⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have L : Lay (arg s 0) (arg s 6) (s.gpr .esp) := ⟨fc, fw, sp56, cW, by rw [bE]; exact sC, by rw [bE]; exact sW⟩
  refine ⟨⟨⟨L, h, ⟨cov_mem (inRd mA), by rw [Nat.mul_comm]; exact descFit,
      by rw [Nat.mul_comm]; exact wDesc.symm, by rw [bE, Nat.mul_comm]; exact sDesc⟩, fun i hi => ?_, BitVec.isLt _⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, by rw [bE]; exact sD⟩, cov_mem mD, cd⟩,
    ⟨cov_mem (inRd mC), cov_mem mW⟩, rfl, rfl, (ofNat_toNat32 _).symm, rfl, (ofNat_toNat32 _).symm, rfl,
    (ofNat_toNat32 _).symm, rfl, by rw [Proof.AesGcm.X86.argsR_eq]; exact cov_mem (inWr mR),
    by rw [Proof.AesGcm.X86.argsR_eq]; exact wA.symm, by omega, rw, rd, BitVec.isLt _⟩, fun j hj => ⟨rfl, rfl⟩⟩
  have hm := comp_mem s.mem (arg s 2) hi
  exact ⟨cov_mem (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))),
    by have := lFit _ hm; rwa [Proof.AesGcm.X86.toNat_w64] at this, (wL _ hm).symm, by rw [bE]; exact sL _ hm⟩

/-- Descriptors whose bytes are the same in two memories list the same
components. -/
theorem comp_eq {m₁ m₂ : Mem} {A : BitVec 32} {N : Nat}
    (h : ∀ i < N * 8, m₁ (w64 A + BitVec.ofNat 64 i) = m₂ (w64 A + BitVec.ofNat 64 i)) {j : Nat} (hj : j < N) :
    compA m₂ A j = compA m₁ A j ∧ compL m₂ A j = compL m₁ A j := by
  have r {d : Nat} (hd : d + 4 ≤ N * 8) : m₂.readW (w64 A + BitVec.ofNat 64 d) 32 =
      m₁.readW (w64 A + BitVec.ofNat 64 d) 32 := by
    have e := Mem.read_congr (m := m₂) (m' := m₁) (a := w64 A + BitVec.ofNat 64 d) (n := 32 / 8)
      fun k hk => by rw [Offset.add_add]; exact (h _ (by omega)).symm
    simp only [Mem.readW, e]
  exact ⟨r (by omega), by simp only [compL]; rw [r (by omega)]⟩

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {s₁ s₂ : State} (h₂ : (Spec.Siv.encryptContract X86.abi 56).pre s₂)
    (q : s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
      arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ arg s₁ 5 = arg s₂ 5 ∧ arg s₁ 6 = arg s₂ 6)
    (hd : ∀ i < (arg s₁ 3).toNat * 8, s₁.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i) =
      s₂.mem (w64 (arg s₁ 2) + BitVec.ofNat 64 i)) :
    ETop (arg s₁ 0) (arg s₁ 6) (s₁.gpr .esp) (arg s₁ 2) (arg s₁ 4) (arg s₁ 1).toNat (arg s₁ 3).toNat
      (arg s₁ 5).toNat (compA s₁.mem (arg s₁ 2)) (compL s₁.mem (arg s₁ 2)) s₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7⟩ := q
  have E := encPre_of h₂
  refine ⟨?_, fun j hj => comp_eq hd hj⟩
  rw [q0, q1, q2, q3, q4, q5, q6, q7]
  exact E.pre

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`: the key context at `0x1000`, 10 rounds, no associated
data (descriptors at `0x2000`), no data (at `0x3000`) and `work` at
`0x4000`, as stack arguments at `0x8004`. -/
def encSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩, ⟨0x8004, 28⟩]

theorem encSat_args : arg encSat 0 = 0x1000 ∧ arg encSat 1 = 10 ∧ arg encSat 2 = 0x2000 ∧ arg encSat 3 = 0 ∧
    arg encSat 4 = 0x3000 ∧ arg encSat 5 = 0 ∧ arg encSat 6 = 0x4000 ∧ argAddr encSat 0 = 0x8004 := by
  decide

theorem encSat_pre : ∃ s, (Spec.Siv.encryptContract X86.abi 56).pre s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, e⟩ := encSat_args
  have esp : encSat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [a0, a1, a2, a3, a4, a5, a6, e, esp] using encSat

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem encrypt_verified :
    Verified X86.target (encrypt v.callee v.suffix) (Spec.Siv.encryptContract X86.abi 56) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, encSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := encrypt_wp v (encPre_of hs).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    exact hq.2
  · sig_pub [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7
    exact (encrypt_top_ct v s₁ (encPre_of h₁) _ _ _ _ _ _
      ⟨encPre_of h₁, encPre_pub h₂ ⟨q0, q1, q2, q3, q4, q5, q6, q7⟩ hp⟩ e₁ e₂).1

/-- The return value: the low word of `edx:eax`. -/
theorem setWidth_ret (a b : BitVec 32) : (a ++ b).setWidth 32 = b := BitVec.setWidth_append_eq_right

theorem decrypt_verified :
    Verified X86.target (decrypt v.callee v.suffix) (Spec.Siv.decryptContract X86.abi 56) := by
  have hpre : ∀ s, (Spec.Siv.decryptContract X86.abi 56).pre s → (Spec.Siv.encryptContract X86.abi 56).pre s :=
    fun _ h => h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, encSat_pre⟩
  · obtain ⟨t, s', he, hq⟩ := decrypt_wp v (encPre_of (hpre _ hs)).pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes]
    rw [setWidth_ret]
    exact hq.2
  · sig_pub [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7
    exact (decrypt_top_ct v s₁ (encPre_of (hpre _ h₁)) _ _ _ _ _ _
      ⟨encPre_of (hpre _ h₁), encPre_pub (hpre _ h₂) ⟨q0, q1, q2, q3, q4, q5, q6, q7⟩ hp⟩ e₁ e₂).1

/-! ## `vg_aes_siv_init` -/

/-- The regions of `initX86`: the key and the stack arguments read-only. -/
def initRd (s : State) : List Region := [⟨w64 (arg s 0), (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
def initWr (s : State) : List Region := [⟨w64 (arg s 2), 512⟩, ⟨w64 (arg s 3), 2560⟩]

theorem initPre_of {s : State} (h : (Proof.AesSiv.initScratchContract X86.abi 48).pre s) :
    initX86.pre (s.withRegions (initRd s) (initWr s)) ∧ s.rd = [⟨w64 (arg s 0), (arg s 1).toNat⟩] ∧
      s.wr = [⟨w64 (arg s 2), 512⟩, ⟨w64 (arg s 3), 2560⟩, ⟨argAddr s 0, 16⟩] := by
  sig_pre [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] at h
  sig_split h
  rename_i sp48 fa hrd hwr kc ks ka cs ca sa rk rc rs ra stk stc sts sta fk fc fs
  exact ⟨⟨rfl, rfl, kc, ks, ka, cs, ca, sa, rk, rc, rs, ra, stk, stc, sts, sta, fk, fc, fs, sp48, (by omega : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32), h⟩,
    hrd, hwr⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition: a key of 32 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 32 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem initSat_pre : ∃ s, (Proof.AesSiv.initScratchContract X86.abi 48).pre s := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 32 := by decide
  have a2 : arg initSat 2 = 0x2000 := by decide
  have a3 : arg initSat 3 = 0x4000 := by decide
  have e : argAddr initSat 0 = 0x8004 := by decide
  have esp : initSat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
    Spec.Siv.initPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using initSat

theorem init_verified :
    Verified X86.target (initCore v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract X86.abi 48) := by
  refine X86.Verified.narrowTo (k := initX86)
    ⟨fun s hs => init_wp v hs, init_ct v, initSat_pre.elim fun s hs => ⟨_, (initPre_of hs).1⟩⟩
    initRd initWr (fun s hs => (initPre_of hs).1) (fun s hs => ?_) (fun s hs => ?_) (fun s s' hs hq => ?_)
    (fun s₁ s₂ h₁ h₂ hp => ?_) initSat_pre
  · obtain ⟨-, hrd, hwr⟩ := initPre_of hs
    rw [hrd, hwr]
    exact Covers.of_mem fun r hr => by
      simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨-, -, hwr⟩ := initPre_of hs
    rw [hwr]
    exact Covers.of_mem fun r hr => by
      simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  · sig_post [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
    exact hq
  · sig_pub [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at hp
    sig_split hp
    rename_i q0 q1 q2 q3
    refine ⟨q0, fun i hi => ?_⟩
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact q1
    · exact q2
    · exact q3
    · exact hp

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

theorem init_noEsp : (initCore v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.allInstrs, noEsp_of v.expandNosp,
    noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (initCore v.expand v.callee v.suffix) ≤ 48 := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with rd := [⟨0x1000, 32⟩], wr := [⟨0x2000, 512⟩, ⟨0x8004, 12⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86.abi 2628).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- `initCore` in a frame of 2580 bytes: the return address, the three
argument slots and the 2560 bytes of working space. -/
theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2580 3 (initCore v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86.abi 2628) :=
  X86.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86.abi.ptrBits) (post := Spec.Siv.initPost X86.abi.ptrBits)
    (wa := true) (stack := 48) (bytes := 2580) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (Proof.AesSiv.initPre_local _) (Proof.AesSiv.initPost_local _) initFrameSat_pre

/-! ## The stack pointer -/

theorem init_spSafe : (initCore v.expand v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [initCore, Impl.CmacAes.Stream.X86.call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v,
    Bool.and_true]
  decide +kernel

theorem encrypt_spSafe : (encrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [encrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

theorem decrypt_spSafe : (decrypt v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [decrypt, encS2v, sivEntry, Impl.AesGcm.X86.entry, start, s2vAds, cmacOf, cmacPre, updCall, finCall,
    Impl.CmacAes.Stream.X86.call6, finish, shortTail, copyN, shortMac, longTail, longMac, ctr, ctrWhole, ctrTail,
    ctrCall, mask, Code.all, Proof.CmacAes.X86.update_spSafe v, Proof.CmacAes.X86.finalize_spSafe v, v.spSafe,
    Bool.and_true]
  decide +kernel

end VG.Proof.AesSiv.X86
