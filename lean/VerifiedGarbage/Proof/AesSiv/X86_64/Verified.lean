import VerifiedGarbage.Proof.AesSiv.X86_64.Init
import VerifiedGarbage.Proof.AesSiv.X86_64.EncCT
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.AesSiv.Scratch

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
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v, v.mxcsr]
  decide +kernel

theorem decrypt_mx (v : Ctr32Impl) : (decrypt v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, update_mx v, finalize_mx v,
    v.mxcsr]
  decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem encrypt_spSafe (v : Ctr32Impl) : (encrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.all, update_spSafe v, finalize_spSafe v,
    v.spSafe]
  decide +kernel

theorem decrypt_spSafe (v : Ctr32Impl) : (decrypt v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.all, update_spSafe v,
    finalize_spSafe v, v.spSafe]
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
    Verified X86_64.target (init v.expand v.callee v.suffix) (Proof.AesSiv.initScratchContract X86_64.abi 16) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initX86_64, X86_64.abi, X86_64.argRegs] [initSat]
      using initSat)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are against the shared contracts with the working space `W` as a
last argument (`Proof/AesSiv/Scratch.lean`), passed on the stack after
`siv` (`T`). They are on the state whose writable regions are the data, `T`
for `encrypt`, the first 2560 bytes of the working space and S2V's state after
them (`encWrE`, `encWrD`), where `EPre` and `SivArg` hold (`encPre_of`,
`decPre_of`); a run from it is a run from the state itself (`Exec.widen`),
so `Verified.of_narrow` moves them to the shared contracts. -/

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2560⟩,
    ⟨stackArg s 1 + BitVec.ofNat 64 dOff, 16⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2560⟩, ⟨stackArg s 1 + BitVec.ofNat 64 dOff, 16⟩]

/-- The arguments of `encrypt` and `decrypt`: `siv` and the working space on
the stack. -/
abbrev EPreS (s : State) : Prop :=
  EPre s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 dOff)
    (s.gpr .rsi).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (s : State) : Prop :=
  SivArg s (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 dOff) (stackArg s 0) (s.gpr .r9).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ EPub s₁ s₂ (s₁.gpr .rdx) (s₁.gpr .rcx).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s ∧ (⟨stackArg s 0, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (Spec.Aes.bytesAt s'.mem (stackArg s 0) 16, Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN : Contract isa where
  pre s := EPreS s ∧ SivArgS s
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
    EPre s₂ (s₁.gpr .rdi) (s₁.gpr .rdx) (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 dOff)
      (s₁.gpr .rsi).toNat (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat := by
  obtain ⟨q1, q2, q3, q4, q5, q6, -, q8, -⟩ := hq
  rw [q1, q2, q3, q4, q5, q6, q8]; exact h₂

theorem SivArgS.of_pub {s₁ s₂ : State} (h₂ : SivArgS s₂) (hq : encPub s₁ s₂) :
    SivArg s₂ (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 dOff) (stackArg s₁ 0)
      (s₁.gpr .r9).toNat := by
  obtain ⟨-, -, -, -, q5, q6, q7, q8, -⟩ := hq
  rw [q5, q6, q7, q8]; exact h₂

theorem encryptN_correct (v : Ctr32Impl) (s : State) (hs : encryptN.pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ encryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp v hs.1 hs.2.1 hs.2.2
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decryptN_correct (v : Ctr32Impl) (s : State) (hs : decryptN.pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ decryptN.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp v hs.1 hs.2
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

theorem encryptN_ct (v : Ctr32Impl) :
    ConstantTime isa encryptN.pre encryptN.pub (encrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Ctr32Impl) :
    ConstantTime isa decryptN.pre decryptN.pub (decrypt v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ### From the shared contracts -/

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

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
narrowed state `σ`: `W'` is the whole working space, of 2576 bytes. -/
theorem mkPre {σ : State} {C A P W T : Addr} {R N L : Nat}
    (hsp : 16 ≤ (σ.gpr .rsp).toNat) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (rdi : σ.gpr .rdi = C) (rsi : σ.gpr .rsi = BitVec.ofNat 64 R) (rdx : σ.gpr .rdx = A)
    (rcx : σ.gpr .rcx = BitVec.ofNat 64 N) (r8 : σ.gpr .r8 = P) (r9 : σ.gpr .r9 = BitVec.ofNat 64 L)
    (aT : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (aW : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr)
    (inArgs : (⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, 2560⟩ : Region) ∈ σ.wr)
    (inD : (⟨W + BitVec.ofNat 64 dOff, 16⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, 2576⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, 2576⟩) (pArgs : (⟨P, L⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩) (wA : (⟨W, 2576⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, 2576⟩ : Region).Disjoint r)
    (wArgs : (⟨W, 2576⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2576⟩)
    (rC : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩) (rP : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, L⟩)
    (rT : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩) (rW : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨W, 2576⟩)
    (rL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint r)
    (sC : (below (σ.gpr .rsp) 16).Disjoint ⟨C, 512⟩) (sP : (below (σ.gpr .rsp) 16).Disjoint ⟨P, L⟩)
    (sT : (below (σ.gpr .rsp) 16).Disjoint ⟨T, 16⟩) (sW : (below (σ.gpr .rsp) 16).Disjoint ⟨W, 2576⟩)
    (sA : (below (σ.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩)
    (sL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (below (σ.gpr .rsp) 16).Disjoint r)
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
      (rQ : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨Q, n⟩) (sQ : (below (σ.gpr .rsp) 16).Disjoint ⟨Q, n⟩)
      (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) : Env σ C (W + BitVec.ofNat 64 dOff) Q W R n :=
    ⟨hsp, hR, inC, inR inD, hQ, inW, cW.sub_right sw, (qW.sub_right sd).symm, dw, qW.sub_right sw, rC,
      rW.sub_right sd, rQ, rW.sub_right sw, sC, sW.sub_right sd, sQ, sW.sub_right sw, wrC, wD, wQ,
      by omega, hn⟩
  have inArg {d : Nat} (hd : 8 ≤ d) (hd' : d + 8 ≤ 24) :
      InRegions (σ.rd ++ σ.wr) (σ.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    ⟨_, inArgs, Offset.contains _ (d := d) (n := 8) (e := 8) (k := 16) hd (by omega) (by decide)⟩
  exact ⟨⟨env P L (inR inP) pW rP sP wrP hL, rfl, cW.sub_right sd, cP, inP, inD, rdi, rsi, rdx, rcx, r8, r9,
    aW, inArg (d := 16) (by decide) (by decide), inA, wA.symm.sub_right sw, wA.symm.sub_right sd, sA, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (rL r hr) (sL r hr) (wrL r hr) (listed_len hr)⟩,
    ⟨aT, inArg (d := 8) (by decide) (by decide), pArgs.symm, wArgs.symm.sub_right sw, wArgs.symm.sub_right sd,
      inT, pT.symm, tW.sub_right sw, tW.sub_right sd, sT, rT, wrT⟩⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `encryptN`'s on the
narrowed state. -/
theorem encPre_of {s : State} (h : (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pre s) :
    encryptN.pre (s.withRegions s.rd (encWrE s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2576⟩] := by
  sig_pre [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at h
  sig_split h
  rename_i hsp hsp' hrd hwr hc1 hrc hrp hrT hrw hc2 hwC hwP hwT hwW hc3
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj] at hrd hwr hc1 hc2 hc3
  rw [Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at hc1
  simp only [List.filterMap_cons, List.filterMap_append, List.filterMap_map, List.filterMap_nil, Function.comp_def,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.cond_true, Bool.cond_false, filterMap_some', filterMap_none',
    List.append_nil, List.nil_append, Sig.conj_cons, Sig.conj_append, Sig.conj_map, Sig.conj, List.map_cons,
    List.map_nil, List.map_map] at hc1
  obtain ⟨cP, ⟨-, cW⟩, ⟨pT, pW, -, pL, pArgs⟩, ⟨tW, -, -, -⟩, wA, wL, wArgs⟩ := hc1
  obtain ⟨-, ⟨rL, -⟩, sC, sP, sT, sW, sA, sL, -⟩ := hc2
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE s := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ encWrE s) : r ∈ s.rd ++ encWrE s := List.mem_append_right _ hr
  have wT : (⟨stackArg s 0, 16⟩ : Region) ∈ encWrE s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre (σ := s.withRegions s.rd (encWrE s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
    (W := stackArg s 1) (T := stackArg s 0) (R := (s.gpr .rsi).toNat) (N := (s.gpr .rcx).toNat)
    (L := (s.gpr .r9).toNat) hsp h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ hr))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self))))
    (inWr wT) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega) wrA wrL
    (BitVec.isLt _)
  exact ⟨⟨e, t, wT⟩, hwr⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `decryptN`'s on the
narrowed state. -/
theorem decPre_of {s : State} (h : (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pre s) :
    decryptN.pre (s.withRegions s.rd (encWrD s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2576⟩] := by
  sig_pre [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at h
  sig_split h
  rename_i hsp hsp' hrd hwr hc1 hrc hrp hrT hrw hc2 hwC hwP hwT hwW hc3
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj] at hrd hwr hc1 hc2 hc3
  rw [Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at hc1
  simp only [List.filterMap_cons, List.filterMap_append, List.filterMap_map, List.filterMap_nil, Function.comp_def,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.cond_true, Bool.cond_false, filterMap_some', filterMap_none',
    List.append_nil, List.nil_append, Sig.conj_cons, Sig.conj_append, Sig.conj_map, Sig.conj, List.map_cons,
    List.map_nil, List.map_map] at hc1
  obtain ⟨cP, cW, ⟨pT, pW, -, pL, pArgs⟩, tW, wA, wL, wArgs⟩ := hc1
  obtain ⟨-, ⟨rL, -⟩, sC, sP, sT, sW, sA, sL, -⟩ := hc2
  obtain ⟨wrA, wrL⟩ := hc3
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD s := List.mem_append_left _ hr
  exact ⟨mkPre (σ := s.withRegions s.rd (encWrD s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
    (W := stackArg s 1) (T := stackArg s 0) (R := (s.gpr .rsi).toNat) (N := (s.gpr .rcx).toNat)
    (L := (s.gpr .r9).toNat) hsp h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hr)))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self)))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega) wrA wrL
    (BitVec.isLt _), hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {s : State}
    (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, 2576⟩]) :
    Covers (encWrE s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0,
      by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), dOff, rfl, by simp [dOff]⟩

theorem encWrD_covers {s : State} (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, 2576⟩]) :
    Covers (encWrD s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, dOff, rfl, by simp [dOff]⟩

/-- A state satisfying the precondition of `vg_aes_siv_encrypt`, with no
associated data and no data: `siv` at `0x5000`, the working space at
`0x4000`. -/
def encSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x50 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 2576⟩]

/-- `encSat`, with `siv` read only. -/
def decSat : State := { encSat with
  rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8008, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2576⟩] }

theorem encSat_pre : ∃ s, (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre,
    X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [encSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using encSat

theorem decSat_pre : ∃ s, (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pre s := by
  sig_implies_sat [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [decSat, encSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using decSat

theorem encPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.encryptScratchContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE s₁)) (s₂.withRegions s₂.rd (encWrE s₂)) := by
  sig_pub [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {s₁ s₂ : State} (hp : (Proof.AesSiv.decryptScratchContract X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD s₁)) (s₂.withRegions s₂.rd (encWrD s₂)) := by
  sig_pub [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem encrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (encrypt v.callee v.suffix) (Proof.AesSiv.encryptScratchContract X86_64.abi 16) :=
  Verified.of_narrow (k := encryptN)
    ⟨encryptN_correct v, encryptN_ct v, encSat_pre.elim fun s hs => ⟨_, (encPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.encryptScratchContract, Proof.AesSiv.encryptScratchSig, Spec.Siv.encryptPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) encSat_pre

theorem decrypt_verified (v : Ctr32Impl) :
    Verified X86_64.target (decrypt v.callee v.suffix) (Proof.AesSiv.decryptScratchContract X86_64.abi 16) :=
  Verified.of_narrow (k := decryptN)
    ⟨decryptN_correct v, decryptN_ct v, decSat_pre.elim fun s hs => ⟨_, (decPre_of hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [Proof.AesSiv.decryptScratchContract, Proof.AesSiv.decryptScratchSig, Spec.Siv.decryptPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) decSat_pre

end VG.Proof.AesSiv.X86_64
