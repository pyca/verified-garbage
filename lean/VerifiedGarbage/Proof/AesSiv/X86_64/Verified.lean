module

public import VerifiedGarbage.Proof.AesSiv.Rounds
public import VerifiedGarbage.Proof.AesSiv.X86_64.Init
public import VerifiedGarbage.Proof.AesSiv.X86_64.EncCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.AesSiv.X86_64.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-SIV on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), a state satisfying each precondition, and the shared
contracts of `Spec/Siv/Contract.lean`, with 16 bytes of stack: the return
addresses of the call of a CMAC function (or of `vg_aes_ctr32`) and of its
call of `vg_aes_ctr32`. `encrypt` and `decrypt` are proven in both layouts of
their working space (`Lay`): of 2576 bytes over any implementations
(`encrypt_verified`, `decrypt_verified`), and of 288 over implementations of
`vg_aes_ctr32` and `vg_cmac_aes_update` that never touch their scratch
buffers (`encryptF_verified`, `decryptF_verified`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_add_lt ekF)
open VG.Proof.CmacAes.X86_64 (subkeys_mx finalize_mx subkeys_spSafe finalize_spSafe)

theorem init_mx (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, initAt, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem encrypt_mx {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hg with rfl | rfl | rfl <;>
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.allInstrs, v.mxcsr, finalize_mx v.ctr,
    Proof.CmacAes.X86_64.ctrCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.ctr.mxcsr]
  <;> decide +kernel

theorem decrypt_mx {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  rcases hg with rfl | rfl | rfl <;>
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, v.mxcsr, finalize_mx v.ctr,
    Proof.CmacAes.X86_64.ctrCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.ctr.mxcsr]
  <;> decide +kernel

theorem init_spSafe (v : Ctr32Impl) :
    (init v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, initAt, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem encrypt_spSafe {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases hg with rfl | rfl | rfl <;>
  simp only [encrypt, encryptCore, sivOut, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Code.all, v.spSafe, finalize_spSafe v.ctr,
    Proof.CmacAes.X86_64.ctrCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.ctr.spSafe]
  <;> decide +kernel

theorem decrypt_spSafe {g : Lay} (hg : g.Ok) (v : UpdateImpl) :
    (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  rcases hg with rfl | rfl | rfl <;>
  simp only [decrypt, openTail, sivIn, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, copy, ctr,
    ctrWhole, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Code.all, v.spSafe,
    finalize_spSafe v.ctr,
    Proof.CmacAes.X86_64.ctrCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.ctr.spSafe]
  <;> decide +kernel

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

theorem initF_mx (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  have h : ekF.code.allInstrs (fun i => !loadsMxcsr i) = true := Ctr32Impl.aesni.expandMxcsr
  simp only [initF, initAt, Code.allInstrs, h, subkeys_mx v]; decide +kernel

theorem initF_spSafe (v : Ctr32Impl) :
    (initF ekF v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  have h : ekF.code.all (fun i => !X86_64.isa.writesSp i) = true := Ctr32Impl.aesni.expandSpSafe
  simp only [initF, initAt, Code.all, h, subkeys_spSafe v]; decide +kernel

theorem initF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (initF ekF v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (initF_mx v) he hg, hp⟩

/-- `vg_aes_siv_init` with `scratch: *mut [u64; 9]`, for `initF`. -/
def initScratchSigF : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 9)]

/-- `Spec.Siv.initContract`, whatever `scratch` is (of 9 words). -/
def initScratchContractF {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigF.contract A
    (pre := fun key keyLen ctx _scratch => Spec.Siv.initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => Spec.Siv.initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- A state satisfying `vg_aes_siv_init`'s precondition, with 72 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x2000, 512⟩, ⟨0x4000, 72⟩] }

theorem initF_verified (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target (initF ekF v.callee v.suffix) (initScratchContractF X86_64.abi 16) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [initScratchContractF, initScratchSigF, Spec.Siv.initPre, Spec.Siv.initPost,
      initX86_64F, initX86_64, X86_64.abi, X86_64.argRegs] [initSatF, initSat] using initSatF)

theorem initS_mx (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [initS, initAt, Code.allInstrs, v.expandMxcsr, subkeys_mx v]; decide +kernel

theorem initS_spSafe (v : Ctr32Impl) :
    (initS v.expand v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [initS, initAt, Code.all, v.expandSpSafe, subkeys_spSafe v]; decide +kernel

theorem initS_correct (v : Ctr32Impl) (g : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : initX86_64S.pre s) :
    ∃ t s', Exec isa (initS v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ initX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initS_wp v g hs
  exact ⟨t, s', he, abiPreserved_of_exec (initS_mx v) he hg, hp⟩

/-- `vg_aes_siv_init` with `scratch: *mut [u64; 240]`, for `initS`. -/
def initScratchSigS : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 240)]

/-- `Spec.Siv.initContract`, whatever `scratch` is (of 240 words). -/
def initScratchContractS {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSigS.contract A
    (pre := fun key keyLen ctx _scratch => Spec.Siv.initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => Spec.Siv.initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- A state satisfying `vg_aes_siv_init`'s precondition, with 1920 bytes of
working space. -/
def initSatS : State := { initSat with wr := [⟨0x2000, 512⟩, ⟨0x4000, 1920⟩] }

theorem initS_verified (v : Ctr32Impl) (g : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target (initS v.expand v.callee v.suffix) (initScratchContractS X86_64.abi 16) :=
  Verified.of_correct (initS_correct v g) (initS_ct v g) (by
    sig_implies [initScratchContractS, initScratchSigS, Spec.Siv.initPre, Spec.Siv.initPost,
      initX86_64S, initX86_64, X86_64.abi, X86_64.argRegs] [initSatS, initSat] using initSatS)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are against the shared contracts with the working space `W` as a
last argument (`Proof/AesSiv/Scratch.lean`), passed on the stack after
`siv` (`T`). They are on the state whose writable regions are the data, `T`
for `encrypt`, the first `g.n` bytes of the working space and S2V's state after
them (`encWrE`, `encWrD`), where `EPre` and `SivArg` hold (`encPre_of`,
`decPre_of`); a run from it is a run from the state itself (`Exec.widen`),
so `Verified.of_narrow` moves them to the shared contracts, whose working
space is the `w` words of the layout (`Lay.Fits`). -/

/-- `Proof.AesSiv.encryptScratchSig`, with `work: *mut [u64; w]`. -/
def encryptScratchSigW (w : Nat) : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array true .u8 16), ("work", .array true .u64 w)]

/-- `Proof.AesSiv.encryptScratchContract`, with a working space of `w` words. -/
def encryptScratchContractW {M : ISA} (w : Nat) (A : Abi M) (stack : Nat := 0) : Contract M :=
  (encryptScratchSigW w).contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.encryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      Proof.AesSiv.encryptRoundsPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)

/-- `Proof.AesSiv.decryptScratchSig`, with `work: *mut [u64; w]`. -/
def decryptScratchSigW (w : Nat) : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array false .u8 16), ("work", .array true .u64 w)]
  ret := some .u32

/-- `Proof.AesSiv.decryptScratchContract`, with a working space of `w` words. -/
def decryptScratchContractW {M : ISA} (w : Nat) (A : Abi M) (stack : Nat := 0) : Contract M :=
  (decryptScratchSigW w).contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.decryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      Proof.AesSiv.decryptRoundsPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.decryptLeak A.ptrBits ctx rounds ads adsCount data len siv)

/-- The words of the working space of a layout: its `g.n` bytes and S2V's
state. -/
def Lay.Fits (g : Lay) (w : Nat) : Prop :=
  (g = .soft ∧ w = 322) ∨ (g = .free ∧ w = 36) ∨ (g = .small ∧ w = 242)

theorem Lay.Fits.ok {g : Lay} {w : Nat} (h : g.Fits w) : g.Ok := by
  rcases h with h | h | h
  exacts [.inl h.1, .inr (.inl h.1), .inr (.inr h.1)]

theorem Lay.Fits.bytes {g : Lay} {w : Nat} (h : g.Fits w) : 8 * w = g.n + 16 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (g : Lay) (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, g.n⟩,
    ⟨stackArg s 1 + BitVec.ofNat 64 g.n, 16⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (g : Lay) (s : State) : List Region :=
  [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, g.n⟩, ⟨stackArg s 1 + BitVec.ofNat 64 g.n, 16⟩]

/-- The arguments of `encrypt` and `decrypt`: `siv` and the working space on
the stack. -/
abbrev EPreS (g : Lay) (s : State) : Prop :=
  EPre g s (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 g.n)
    (s.gpr .rsi).toNat (s.gpr .rcx).toNat (s.gpr .r9).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (g : Lay) (s : State) : Prop :=
  SivArg g s (s.gpr .r8) (stackArg s 1) (stackArg s 1 + BitVec.ofNat 64 g.n) (stackArg s 0) (s.gpr .r9).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ EPub s₁ s₂ (s₁.gpr .rdx) (s₁.gpr .rcx).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN (g : Lay) : Contract isa where
  pre s := EPreS g s ∧ SivArgS g s ∧ (⟨stackArg s 0, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (Spec.Aes.bytesAt s'.mem (stackArg s 0) 16, Spec.Aes.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN (g : Lay) : Contract isa where
  pre s := EPreS g s ∧ SivArgS g s
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
theorem EPreS.of_pub {g : Lay} {s₁ s₂ : State} (h₂ : EPreS g s₂) (hq : encPub s₁ s₂) :
    EPre g s₂ (s₁.gpr .rdi) (s₁.gpr .rdx) (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 g.n)
      (s₁.gpr .rsi).toNat (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat := by
  obtain ⟨q1, q2, q3, q4, q5, q6, -, q8, -⟩ := hq
  rw [q1, q2, q3, q4, q5, q6, q8]; exact h₂

theorem SivArgS.of_pub {g : Lay} {s₁ s₂ : State} (h₂ : SivArgS g s₂) (hq : encPub s₁ s₂) :
    SivArg g s₂ (s₁.gpr .r8) (stackArg s₁ 1) (stackArg s₁ 1 + BitVec.ofNat 64 g.n) (stackArg s₁ 0)
      (s₁.gpr .r9).toNat := by
  obtain ⟨-, -, -, -, q5, q6, q7, q8, -⟩ := hq
  rw [q5, q6, q7, q8]; exact h₂

theorem encryptN_correct {g : Lay} (v : UpdateImpl) (K : Calls v g) (s : State) (hs : (encryptN g).pre s) :
    ∃ t s', Exec isa (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      (encryptN g).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp v K hs.1 hs.2.1 hs.2.2
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx hs.1.env.lay v) he hg, hp⟩

theorem decryptN_correct {g : Lay} (v : UpdateImpl) (K : Calls v g) (s : State) (hs : (decryptN g).pre s) :
    ∃ t s', Exec isa (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      (decryptN g).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp v K hs.1 hs.2
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx hs.1.env.lay v) he hg, hp⟩

theorem encryptN_ct {g : Lay} (v : UpdateImpl) (K : Calls v g) :
    ConstantTime isa (encryptN g).pre (encryptN g).pub (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v K h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) hq.2.2.2.2.2.2.2.2
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct {g : Lay} (v : UpdateImpl) (K : Calls v g) :
    ConstantTime isa (decryptN g).pre (decryptN g).pub (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v K h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
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
narrowed state `σ`: the whole working space is the `nT` bytes at `W`, the `g.n`
of the layout and S2V's state. -/
theorem mkPre {g : Lay} (hg : g.Ok) {nT : Nat} (hnT : nT = g.n + 16) {σ : State} {C A P W T : Addr} {R N L : Nat}
    (hsp : 16 ≤ (σ.gpr .rsp).toNat) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (rdi : σ.gpr .rdi = C) (rsi : σ.gpr .rsi = BitVec.ofNat 64 R) (rdx : σ.gpr .rdx = A)
    (rcx : σ.gpr .rcx = BitVec.ofNat 64 N) (r8 : σ.gpr .r8 = P) (r9 : σ.gpr .r9 = BitVec.ofNat 64 L)
    (aT : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 8) 64 = T)
    (aW : σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 16) 64 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr)
    (inArgs : (⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, g.n⟩ : Region) ∈ σ.wr)
    (inD : (⟨W + BitVec.ofNat 64 g.n, 16⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, nT⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, nT⟩) (pArgs : (⟨P, L⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩) (wA : (⟨W, nT⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, nT⟩ : Region).Disjoint r)
    (wArgs : (⟨W, nT⟩ : Region).Disjoint ⟨σ.gpr .rsp + BitVec.ofNat 64 8, 16⟩)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, nT⟩)
    (rC : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨C, 512⟩) (rP : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨P, L⟩)
    (rT : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨T, 16⟩) (rW : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨W, nT⟩)
    (rL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint r)
    (sC : (below (σ.gpr .rsp) 16).Disjoint ⟨C, 512⟩) (sP : (below (σ.gpr .rsp) 16).Disjoint ⟨P, L⟩)
    (sT : (below (σ.gpr .rsp) 16).Disjoint ⟨T, 16⟩) (sW : (below (σ.gpr .rsp) 16).Disjoint ⟨W, nT⟩)
    (sA : (below (σ.gpr .rsp) 16).Disjoint ⟨A, N * 16⟩)
    (sL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (below (σ.gpr .rsp) 16).Disjoint r)
    (wrC : C.toNat + 512 ≤ 2 ^ 64) (wrP : P.toNat + L ≤ 2 ^ 64) (wrT : T.toNat + 16 ≤ 2 ^ 64)
    (wrW : W.toNat + nT ≤ 2 ^ 64) (wrA : A.toNat + N * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r.base.toNat + r.len ≤ 2 ^ 64) (hL : L < 2 ^ 64) :
    EPre g σ C A P W (W + BitVec.ofNat 64 g.n) R N L ∧ SivArg g σ P W (W + BitVec.ofNat 64 g.n) T L := by
  subst hnT
  have hlt := hg.n_lt
  have sw : Region.Sub ⟨W, g.n⟩ ⟨W, g.n + 16⟩ := Region.sub_prefix (Nat.le_add_right _ _)
  have sd : Region.Sub ⟨W + BitVec.ofNat 64 g.n, 16⟩ ⟨W, g.n + 16⟩ := Offset.sub_base _ (Nat.le_refl _)
  have dw := Offset.disjoint_base W (d := g.n) (n := 16) (k := g.n) (Nat.le_refl _) (by omega_using [hlt])
  have wD : (W + BitVec.ofNat 64 g.n).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ wrW (by omega_using [])]; omega_using [wrW]
  have inR {r : Region} (h : r ∈ σ.wr) : r ∈ σ.rd ++ σ.wr := List.mem_append_right _ h
  have env (Q : Addr) (n : Nat) (hQ : (⟨Q, n⟩ : Region) ∈ σ.rd ++ σ.wr) (qW : (⟨Q, n⟩ : Region).Disjoint ⟨W, g.n + 16⟩)
      (rQ : (⟨σ.gpr .rsp, 8⟩ : Region).Disjoint ⟨Q, n⟩) (sQ : (below (σ.gpr .rsp) 16).Disjoint ⟨Q, n⟩)
      (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) : Env g σ C (W + BitVec.ofNat 64 g.n) Q W R n :=
    ⟨hg, hsp, hR, inC, inR inD, hQ, inW, cW.sub_right sw, (qW.sub_right sd).symm, dw, qW.sub_right sw, rC,
      rW.sub_right sd, rQ, rW.sub_right sw, sC, sW.sub_right sd, sQ, sW.sub_right sw, wrC, wD, wQ,
      by omega_using [wrW], hn⟩
  have inArg {d : Nat} (hd : 8 ≤ d) (hd' : d + 8 ≤ 24) :
      InRegions (σ.rd ++ σ.wr) (σ.gpr .rsp + BitVec.ofNat 64 d) 8 :=
    ⟨_, inArgs, Offset.contains _ (d := d) (n := 8) (e := 8) (k := 16) hd (by omega_using [hd']) (by decide)⟩
  exact ⟨⟨env P L (inR inP) pW rP sP wrP hL, rfl, cW.sub_right sd, cP, inP, inD, rdi, rsi, rdx, rcx, r8, r9,
    aW, inArg (d := 16) (by decide) (by decide), inA, wA.symm.sub_right sw, wA.symm.sub_right sd, sA, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (rL r hr) (sL r hr) (wrL r hr) (listed_len hr)⟩,
    ⟨aT, inArg (d := 8) (by decide) (by decide), pArgs.symm, wArgs.symm.sub_right sw, wArgs.symm.sub_right sd,
      inT, pT.symm, tW.sub_right sw, tW.sub_right sd, sT, rT, wrT⟩⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `encryptN`'s on the
narrowed state. -/
theorem encPre_of {g : Lay} {w : Nat} (hf : g.Fits w) {s : State}
    (h : (encryptScratchContractW w X86_64.abi 16).pre s) :
    (encryptN g).pre (s.withRegions s.rd (encWrE g s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, g.n + 16⟩] := by
  have hok := hf.ok
  have hb := hf.bytes
  rcases hf with ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩
  all_goals
  sig_pre [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre, X86_64.abi,
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
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE g s := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ encWrE g s) : r ∈ s.rd ++ encWrE g s := List.mem_append_right _ hr
  have wT : (⟨stackArg s 0, 16⟩ : Region) ∈ encWrE g s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre hok hb (σ := s.withRegions s.rd (encWrE g s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
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
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega_using [hwW]) wrA wrL
    (BitVec.isLt _)
  exact ⟨⟨e, t, wT⟩, by rw [← hb]; exact hwr⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the shared contract gives `decryptN`'s on the
narrowed state. -/
theorem decPre_of {g : Lay} {w : Nat} (hf : g.Fits w) {s : State}
    (h : (decryptScratchContractW w X86_64.abi 16).pre s) :
    (decryptN g).pre (s.withRegions s.rd (encWrD g s)) ∧
      s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, g.n + 16⟩] := by
  have hok := hf.ok
  have hb := hf.bytes
  rcases hf with ⟨hg, rfl⟩ | ⟨hg, rfl⟩ | ⟨hg, rfl⟩
  all_goals
  sig_pre [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre, X86_64.abi,
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
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD g s := List.mem_append_left _ hr
  exact ⟨mkPre hok hb (σ := s.withRegions s.rd (encWrD g s)) (C := s.gpr .rdi) (A := s.gpr .rdx) (P := s.gpr .r8)
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
    cP cW pW pArgs pT wA wL wArgs tW hrc hrp hrT hrw rL sC sP sT sW sA sL hwC hwP hwT (by omega_using [hwW]) wrA wrL
    (BitVec.isLt _), by rw [← hb]; exact hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {g : Lay} {s : State}
    (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, 16⟩, ⟨stackArg s 1, g.n + 16⟩]) :
    Covers (encWrE g s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0,
      by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), g.n, rfl, Nat.le_refl _⟩

theorem encWrD_covers {g : Lay} {s : State}
    (hwr : s.wr = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, g.n + 16⟩]) :
    Covers (encWrD g s) s.wr := by
  rw [hwr]
  refine Covers.of_sub fun r hr => ?_
  simp only [encWrD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by rw [Proof.CmacAes.X86_64.k0], by simp⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, g.n, rfl, Nat.le_refl _⟩

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

/-- `encSat` and `decSat`, with a working space of 288 bytes. -/
def encSatF : State := { encSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 288⟩] }

def decSatF : State := { decSat with wr := [⟨0x3000, 0⟩, ⟨0x4000, 288⟩] }

/-- … and with one of 1936 bytes (`Lay.small`). -/
def encSatS : State := { encSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, 1936⟩] }

def decSatS : State := { decSat with wr := [⟨0x3000, 0⟩, ⟨0x4000, 1936⟩] }

theorem encSat_pre {g : Lay} {w : Nat} (hf : g.Fits w) :
    ∃ s, (encryptScratchContractW w X86_64.abi 16).pre s := by
  rcases hf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · sig_implies_sat [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [encSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSat
  · sig_implies_sat [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      [encSatF, encSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatF
  · sig_implies_sat [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      [encSatS, encSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using encSatS

theorem decSat_pre {g : Lay} {w : Nat} (hf : g.Fits w) :
    ∃ s, (decryptScratchContractW w X86_64.abi 16).pre s := by
  rcases hf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · sig_implies_sat [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [decSat, encSat, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using decSat
  · sig_implies_sat [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [decSatF, decSat, encSat, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using decSatF
  · sig_implies_sat [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
      X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] [decSatS, decSat, encSat, stackArg, stackArgAddr,
      Mem.readW, Mem.read] using decSatS

theorem encPub_of {g : Lay} {w : Nat} {s₁ s₂ : State} (hp : (encryptScratchContractW w X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE g s₁)) (s₂.withRegions s₂.rd (encWrE g s₂)) := by
  sig_pub [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre, X86_64.abi,
    X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {g : Lay} {w : Nat} {s₁ s₂ : State} (hp : (decryptScratchContractW w X86_64.abi 16).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD g s₁)) (s₂.withRegions s₂.rd (encWrD g s₂)) := by
  sig_pub [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

/-- `encrypt` in a layout, against the shared contract with its working space. -/
theorem encrypt_verifiedW {g : Lay} {w : Nat} (hf : g.Fits w) (v : UpdateImpl) (K : Calls v g) :
    Verified X86_64.target (encrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix)
      (encryptScratchContractW w X86_64.abi 16) :=
  Verified.of_narrow (k := encryptN g)
    ⟨encryptN_correct v K, encryptN_ct v K, (encSat_pre hf).elim fun s hs => ⟨_, (encPre_of hf hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE g s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of hf hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of hf hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [encryptScratchContractW, encryptScratchSigW, Proof.AesSiv.encryptRoundsPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) (encSat_pre hf)

/-- `decrypt` in a layout, against the shared contract with its working space. -/
theorem decrypt_verifiedW {g : Lay} {w : Nat} (hf : g.Fits w) (v : UpdateImpl) (K : Calls v g) :
    Verified X86_64.target (decrypt g.x g.n v.callee v.ctr.callee v.ctr.suffix)
      (decryptScratchContractW w X86_64.abi 16) :=
  Verified.of_narrow (k := decryptN g)
    ⟨decryptN_correct v K, decryptN_ct v K, (decSat_pre hf).elim fun s hs => ⟨_, (decPre_of hf hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD g s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of hf hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of hf hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [decryptScratchContractW, decryptScratchSigW, Proof.AesSiv.decryptRoundsPost,
        X86_64.abi, X86_64.argRegs, stackArgs_two, List.append_eq]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) (decSat_pre hf)

/-- Over any implementations, with a working space of 2576 bytes. -/
theorem encrypt_verified (v : UpdateImpl) :
    Verified X86_64.target (encrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.encryptScratchContract X86_64.abi 16) :=
  encrypt_verifiedW (Or.inl ⟨rfl, rfl⟩) v (Calls.soft v)

theorem decrypt_verified (v : UpdateImpl) :
    Verified X86_64.target (decrypt csImm dOff v.callee v.ctr.callee v.ctr.suffix)
      (Proof.AesSiv.decryptScratchContract X86_64.abi 16) :=
  decrypt_verifiedW (Or.inl ⟨rfl, rfl⟩) v (Calls.soft v)

/-- Over implementations of `vg_cmac_aes_update` and `vg_aes_ctr32` that never
touch their scratch buffers, with a working space of 288 bytes. -/
theorem encryptF_verified (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (encrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix)
      (encryptScratchContractW 36 X86_64.abi 16) :=
  encrypt_verifiedW (Or.inr (Or.inl ⟨rfl, rfl⟩)) v (Calls.free v f fc)

theorem decryptF_verified (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateFree v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Free v.ctr.callee) :
    Verified X86_64.target (decrypt csImmF dOffF v.callee v.ctr.callee v.ctr.suffix)
      (decryptScratchContractW 36 X86_64.abi 16) :=
  decrypt_verifiedW (Or.inr (Or.inl ⟨rfl, rfl⟩)) v (Calls.free v f fc)

/-- Over implementations of `vg_cmac_aes_update` and `vg_aes_ctr32` that give
the bitsliced AES its working space 512 bytes into their scratch buffers,
with a working space of 1936 bytes (`Lay.small`). -/
theorem encryptS_verified (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    Verified X86_64.target (encrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix)
      (encryptScratchContractW 242 X86_64.abi 16) :=
  encrypt_verifiedW (Or.inr (Or.inr ⟨rfl, rfl⟩)) v (Calls.small v f fc)

theorem decryptS_verified (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee)
    (fc : Proof.Aes.X86_64.Ctr32Small v.ctr.callee) :
    Verified X86_64.target (decrypt csImmS dOffS v.callee v.ctr.callee v.ctr.suffix)
      (decryptScratchContractW 242 X86_64.abi 16) :=
  decrypt_verifiedW (Or.inr (Or.inr ⟨rfl, rfl⟩)) v (Calls.small v f fc)

end VG.Proof.AesSiv.X86_64
