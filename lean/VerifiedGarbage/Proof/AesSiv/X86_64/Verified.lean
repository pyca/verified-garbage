import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.EncCT
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Siv.Contract

/-!
# AES-SIV on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), a state satisfying each precondition, and the shared
contracts of `Spec/Siv/Contract.lean`, with 16 bytes of stack: the return
addresses of the call of a CMAC function (or of `vg_aes_ctr32`) and of its
call of `vg_aes_ctr32`.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_add_lt)
open VG.Proof.CmacAes.X86_64 (update_mx subkeys_mx finalize_mx update_spSafe subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem encrypt_mx (v : Ctr32Impl) : (encrypt v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v, v.mxcsr]
  decide +kernel

theorem decrypt_mx (v : Ctr32Impl) : (decrypt v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v,
    v.mxcsr]
  decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem encrypt_spSafe (v : Ctr32Impl) : (encrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v, v.spSafe]
  decide +kernel

theorem decrypt_spSafe (v : Ctr32Impl) : (decrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v,
    v.spSafe]
  decide +kernel

theorem init_correct (v : Ctr32Impl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 32 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, 2560⟩]

theorem init_verified (v : Ctr32Impl) :
    Verified X86_64.target (init v.expand v.callee v.suffix) (Spec.Siv.initContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Spec.Siv.initContract, Spec.Siv.initSig, initX86_64, X86_64.abi, X86_64.argRegs] [initSat]
      using initSat)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are on the state whose writable regions are the data, the first
2560 bytes of the working space and S2V's state after them (`encWr`), where
`EPre` holds (`encPre_of`); a run from it is a run from the state itself
(`Exec.widen`), so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of the proofs. -/
def encWr (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 2560⟩, ⟨stackArg s 0 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt` (the work space the stack argument). -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (stackArg s 0) (stackArg s 0 + BitVec.ofNat 64 dOff)
    (s.gpr .rsi).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    EPub s₁ s₂ (s₁.gpr .rdx) (s₁.gpr .rcx).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre := EPreS
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (Spec.Aes.bytesAt s'.mem (stackArg s 0) 16, Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre := EPreS
  post s s' :=
    match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Aes.bytesAt s.mem (stackArg s 0) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Siv.zeros (s.gpr .r9).toNat
  pub := encPub

/-- The second run's arguments are the first's. -/
theorem EPreS.of_pub {s₁ s₂ : State} (h₂ : EPreS s₂) (hq : encPub s₁ s₂) :
    EPre s₂ (s₁.gpr .rdi) (s₁.gpr .rdx) (s₁.gpr .r8) (stackArg s₁ 0) (stackArg s₁ 0 + BitVec.ofNat 64 dOff)
      (s₁.gpr .rsi).toNat (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, -⟩ := hq
  rw [q1, q2, q3, q4, q5, q6, q7]; exact h₂

theorem encryptN_correct (v : Ctr32Impl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ encryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decryptN_correct (v : Ctr32Impl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ decryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encryptN_ct (v : Ctr32Impl) :
    ConstantTime isa encryptN.pre encryptN.pub (encrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁ (EPreS.of_pub h₂ hq) hq.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Ctr32Impl) :
    ConstantTime isa decryptN.pre decryptN.pub (decrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁ (EPreS.of_pub h₂ hq) hq.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### From the shared contracts -/

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

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
theorem encPre_of {s : State} (h : (Spec.Siv.encryptContract X86_64.abi 16).pre s) :
    EPreS (s.withRegions s.rd (encWr s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 2576⟩] := by
  sig_pre [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs, stackArgs_one,
    List.append_eq] at h
  sig_pre [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs, stackArgs_one,
    List.append_eq] at h
  sig_split h
  rename_i hsp hsp' hrd hwr hcp hc1 hrc hrp hrw hc2 hwC hwP hwW hc3
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj] at hrd hwr hc1 hc2 hc3
  rw [pairFacts_ro _ (by simp)] at hc1
  obtain ⟨cW, pW, -, ⟨pL, -⟩, wDesc, ⟨wL, -⟩, -⟩ := hc1
  obtain ⟨-, ⟨rL, -⟩, sC, sP, sW, sDesc, sL, -⟩ := hc2
  obtain ⟨wA, wL'⟩ := hc3
  have sw : Region.Sub ⟨stackArg s 0, 2560⟩ ⟨stackArg s 0, 2576⟩ := Region.sub_prefix (by decide)
  have sd : Region.Sub ⟨stackArg s 0 + BitVec.ofNat 64 dOff, 16⟩ ⟨stackArg s 0, 2576⟩ :=
    Offset.sub_base _ (by decide)
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWr s := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ encWr s) : r ∈ s.rd ++ encWr s := List.mem_append_right _ hr
  have w₀ : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region) ∈ encWr s := List.mem_cons_self
  have w₁ : (⟨stackArg s 0, 2560⟩ : Region) ∈ encWr s := List.mem_cons_of_mem _ List.mem_cons_self
  have w₂ : (⟨stackArg s 0 + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ encWr s :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have dw := Offset.disjoint_base (stackArg s 0) (d := dOff) (n := 16) (k := 2560) (by decide) (by decide)
  have wD : (stackArg s 0 + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ hwW (show dOff < 2576 by decide)]; simp only [dOff]; omega
  have e : Env (s.withRegions s.rd (encWr s)) (s.gpr .rdi) (stackArg s 0 + BitVec.ofNat 64 dOff) (s.gpr .r8)
      (stackArg s 0) (s.gpr .rsi).toNat (s.gpr .r9).toNat :=
    ⟨hsp, h, inRd (by rw [hrd]; exact List.mem_cons_self), inWr w₂, inWr w₀, w₁, cW.sub_right sw,
      pW.symm.sub_left sd, dw, pW.sub_right sw, hrc, hrw.sub_right sd, hrp, hrw.sub_right sw, sC,
      sW.sub_right sd, sP, sW.sub_right sw, hwC, wD, hwP, by omega, BitVec.isLt _⟩
  refine ⟨⟨e, rfl, cW.sub_right sd, hcp, w₀, w₂, rfl, by simp, rfl, by simp, rfl, by simp, rfl,
    ⟨_, inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
      List.mem_cons_self))), Region.contains_self _ _⟩,
    inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self), wDesc.symm.sub_right sw,
    wDesc.symm.sub_right sd, sDesc, wA, fun r hr => ?_⟩, hwr⟩
  exact ⟨hsp, h, e.ctxIn, e.dIn, inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hr))), w₁, e.c_w, (wL r hr).sub_left sd, dw,
    (wL r hr).symm.sub_right sw, hrc, e.ret_d, rL r hr, e.ret_w, sC, e.stk_d, sL r hr, e.stk_w, hwC, wD, wL' r hr,
    e.wW, listed_len hr⟩

/-- The narrowed state's regions are within the state's. -/
theorem encWr_covers {s : State} (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 2576⟩]) :
    Covers (encWr s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A run from the narrowed state is a run from the state. -/
theorem encWr_exec {c : Prog isa} {s s₁ : State} {t : List Leak}
    (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 2576⟩])
    (he : Exec isa c (s.withRegions s.rd (encWr s)) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen (s := s.withRegions s.rd (encWr s)) (rd := s.rd) (wr := s.wr) he
    (Covers.append (Covers.refl s.rd) (encWr_covers hwr)) (encWr_covers hwr)
  exact this

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data and no data. -/
def encSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x40 else 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩]

theorem encSat_pre : ∃ s, (Spec.Siv.encryptContract X86_64.abi 16).pre s := by
  sig_implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs, stackArgs_one,
    List.append_eq] [encSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSat

theorem encPub_of {s₁ s₂ : State} (hp : (Spec.Siv.encryptContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWr s₁)) (s₂.withRegions s₂.rd (encWr s₂)) := by
  sig_pub [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs, stackArgs_one,
    List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Spec.Siv.decryptContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWr s₁)) (s₂.withRegions s₂.rd (encWr s₂)) := by
  sig_pub [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs,
    stackArgs_one, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q1, hp⟩

theorem encrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (encrypt v.callee v.suffix) (Spec.Siv.encryptContract X86_64.abi 16) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWr s)) (fun s s₁ => s₁.withRegions s.rd s.wr) (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => encWr_exec (encPre_of hs).2 he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Spec.Siv.encryptContract, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs, stackArgs_one,
        List.append_eq]
      exact hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (decrypt v.callee v.suffix) (Spec.Siv.decryptContract X86_64.abi 16) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWr s)) (fun s s₁ => s₁.withRegions s.rd s.wr) (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => encWr_exec (encPre_of hs).2 he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, X86_64.abi, X86_64.argRegs,
        stackArgs_one, List.append_eq]
      exact hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) encSat_pre

end VG.Proof.AesSiv.X86_64
