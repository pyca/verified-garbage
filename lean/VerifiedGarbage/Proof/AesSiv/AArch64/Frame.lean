module

public import VerifiedGarbage.Proof.AesSiv.Scratch
public import VerifiedGarbage.Proof.AesSiv.AArch64.Init
public import VerifiedGarbage.Proof.AesSiv.AArch64.EncCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `AesSiv.AArch64.Verified`, which only this module used -/

section

/-!
# AES-SIV on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_cmac_aes_update`, with the implementation of `vg_aes_ctr32` that goes
with it, or for `init` any implementation of `vg_aes_ctr32`), a state
satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`, with no stack: the calls keep their return address
in `x30`, which the functions save in the working space.
-/

@[expose] public section

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.Impl.AesSiv.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_add_lt)

theorem init_keepsV (v : Ctr32Impl) : (init v.expand v.callee v.suffix).allInstrs keepsV = true := by
  simp only [init, Code.allInstrs, v.expandKeepsV, Proof.CmacAes.AArch64.subkeys_keepsV v]; decide +kernel

theorem encrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (encrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [encrypt, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac, ctr, ctrWhole,
    ctrBody, ctrMin, ctrLeft, xorBytes, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

theorem decrypt_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    (decrypt v.callee v.ctr.callee v.ctr.suffix).allInstrs keepsV = true := by
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    ctr, ctrWhole, ctrBody, ctrMin, ctrLeft, xorBytes, maskData, callUpdate, callFinalize, Code.allInstrs, v.keepsV,
    Proof.CmacAes.AArch64.finalize_keepsV v.ctr, v.ctr.keepsV]
  decide +kernel

/-- The working space of `vg_aes_siv_init` over `v`: the 512 bytes of the key
expansion, or what `vg_cmac_aes_subkeys` needs (`128 + v.scratch`), if more. -/
def sivInitW (v : Ctr32Impl) : Nat := Impl.AesSiv.AArch64.Fn.initWork v.scratch

theorem sivInitW_ok (v : Ctr32Impl) : 128 + v.scratch ≤ sivInitW v ∧ 512 ≤ sivInitW v := by
  rcases v.scratch_ok with h | h <;> simp only [sivInitW, Impl.AesSiv.AArch64.Fn.initWork, h] <;> decide

/-- The working space of the functions `encrypt` and `decrypt` over `v` call,
from `csOff`: none of them needs any for an implementation that needs none,
but `vg_cmac_aes_finalize`'s 128 bytes; else 2176. -/
def sivNw (v : Proof.CmacAes.AArch64.UpdateImpl) : Nat :=
  Impl.AesSiv.AArch64.Fn.cryptWork v.scratch v.ctr.scratch

theorem sivNw_ok (v : Proof.CmacAes.AArch64.UpdateImpl) : NwOk v (sivNw v) := by
  rcases v.scratch_ok with h | h <;> rcases v.ctr.scratch_ok with h' | h' <;>
    exact ⟨by simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h']; decide, by simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h']; decide⟩

theorem sivNw_cases (v : Proof.CmacAes.AArch64.UpdateImpl) : sivNw v = 128 ∨ sivNw v = 2176 := by
  unfold sivNw Impl.AesSiv.AArch64.Fn.cryptWork; split <;> simp

theorem init_correct (v : Ctr32Impl) (s : State) (hs : (initAArch64 (sivInitW v)).pre s) :
    ∃ t s', Exec isa (init v.expand v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧
      (initAArch64 (sivInitW v)).post s s' :=
  WP.withPreservedV (init_wp v (sivInitW_ok v).1 (sivInitW_ok v).2 hs) (init_keepsV v)

/-- A state satisfying `vg_aes_siv_init`'s precondition, with `F` bytes of
working space. -/
def initSatW (F : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 0x2000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 512⟩, ⟨0x4000, F⟩]

/-- `vg_aes_siv_init` with `scratch: *mut [u64; w]`. -/
def initScratchSigW (w : Nat) : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 w)]

/-- `initContract`, whatever `scratch` is (of `w` words). -/
def initScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (initScratchSigW w).contract A
    (pre := fun key keyLen ctx _scratch => Spec.Siv.initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => Spec.Siv.initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

theorem init_verified (v : Ctr32Impl) :
    Verified AArch64.target (init v.expand v.callee v.suffix)
      (initScratchContractW AArch64.abi ((48 + sivInitW v) / 8)) := by
  obtain hc := init_correct v
  obtain ht := init_ct v (sivInitW_ok v).1 (sivInitW_ok v).2
  rcases v.scratch_ok with h | h <;> simp only [sivInitW, Impl.AesSiv.AArch64.Fn.initWork, h, Nat.reduceAdd, Nat.reduceDiv, ite_true,
    show (2048 : Nat) ≠ 0 by decide, ite_false] at hc ht ⊢
  · exact Verified.of_correct hc ht (by
      sig_implies [initScratchContractW, initScratchSigW, Spec.Siv.initPre, Spec.Siv.initPost, initAArch64,
        AArch64.abi, AArch64.argRegs] [initSatW] using initSatW 560)
  · exact Verified.of_correct hc ht (by
      sig_implies [initScratchContractW, initScratchSigW, Spec.Siv.initPre, Spec.Siv.initPost, initAArch64,
        AArch64.abi, AArch64.argRegs] [initSatW] using initSatW 2224)

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`

The proofs are against contracts like the shared ones, with the working space
`W` as a last argument of `272 + Nw` bytes, in `x7`, after `siv` (`T`) in
`x6`. `EPre` and `SivArg` hold on the state (`encPre_of`, `decPre_of`), as it
is: the narrowed state of `Verified.of_narrow` is the state itself. -/

/-- The writable regions of `encrypt`'s proof. -/
def encWrE (Nw : Nat) (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 272 + Nw⟩]

/-- The writable regions of `decrypt`'s proof. -/
def encWrD (Nw : Nat) (s : State) : List Region :=
  [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 272 + Nw⟩]

/-- The arguments of `encrypt` and `decrypt`. -/
abbrev EPreS (Nw : Nat) (s : State) : Prop :=
  EPre Nw s (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff)
    (s.gpr .x1).toNat (s.gpr .x3).toNat (s.gpr .x5).toNat

/-- The synthetic IV of `encrypt` and `decrypt`. -/
abbrev SivArgS (Nw : Nat) (s : State) : Prop :=
  SivArg Nw s (s.gpr .x4) (s.gpr .x7) (s.gpr .x7 + BitVec.ofNat 64 dOff) (s.gpr .x6) (s.gpr .x5).toNat

/-- What two runs agree on. -/
def encPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧
    EPub s₁ s₂ (s₁.gpr .x2) (s₁.gpr .x3).toNat

/-- `vg_aes_siv_encrypt` on the narrowed state. -/
def encryptN (Nw : Nat) : Contract isa where
  pre s := EPreS Nw s ∧ SivArgS Nw s ∧ (⟨s.gpr .x6, 16⟩ : Region) ∈ s.wr
  post s s' :=
    Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Siv.components 64 s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (Spec.Aes.bytesAt s'.mem (s.gpr .x6) 16, Spec.Aes.bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat)
  pub := encPub

/-- `vg_aes_siv_decrypt` on the narrowed state. -/
def decryptN (Nw : Nat) : Contract isa where
  pre s := EPreS Nw s ∧ SivArgS Nw s
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
theorem EPreS.of_pub {Nw : Nat} {s₁ s₂ : State} (h₂ : EPreS Nw s₂) (hq : encPub s₁ s₂) :
    EPre Nw s₂ (s₁.gpr .x0) (s₁.gpr .x2) (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff)
      (s₁.gpr .x1).toNat (s₁.gpr .x3).toNat (s₁.gpr .x5).toNat := by
  obtain ⟨q0, q1, q2, q3, q4, q5, -, q7, -⟩ := hq
  rw [q0, q1, q2, q3, q4, q5, q7]; exact h₂

theorem SivArgS.of_pub {Nw : Nat} {s₁ s₂ : State} (h₂ : SivArgS Nw s₂) (hq : encPub s₁ s₂) :
    SivArg Nw s₂ (s₁.gpr .x4) (s₁.gpr .x7) (s₁.gpr .x7 + BitVec.ofNat 64 dOff) (s₁.gpr .x6) (s₁.gpr .x5).toNat := by
  obtain ⟨-, -, -, -, q4, q5, q6, q7, -⟩ := hq
  rw [q4, q5, q6, q7]; exact h₂

theorem encryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : (encryptN (sivNw v)).pre s) :
    ∃ t s', Exec isa (encrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      (encryptN (sivNw v)).post s s' :=
  WP.withPreservedV (encrypt_wp v (sivNw_ok v) hs.1 hs.2.1 hs.2.2) (encrypt_keepsV v)

theorem decryptN_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : (decryptN (sivNw v)).pre s) :
    ∃ t s', Exec isa (decrypt v.callee v.ctr.callee v.ctr.suffix) s t s' ∧ abiPreserved s s' ∧
      (decryptN (sivNw v)).post s s' :=
  WP.withPreservedV (decrypt_wp v (sivNw_ok v) hs.1 hs.2) (decrypt_keepsV v)

theorem encryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa (encryptN (sivNw v)).pre (encryptN (sivNw v)).pub (encrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel v (sivNw_ok v) h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2.1 (SivArgS.of_pub h₂.2.1 hq) h₁.2.2
      (by rw [hq.2.2.2.2.2.2.1]; exact h₂.2.2) hq.2.2.2.2.2.2.2.2 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decryptN_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa (decryptN (sivNw v)).pre (decryptN (sivNw v)).pub (decrypt v.callee v.ctr.callee v.ctr.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel v (sivNw_ok v) h₁.1 (EPreS.of_pub h₂.1 hq) h₁.2 (SivArgS.of_pub h₂.2 hq) hq.2.2.2.2.2.2.2.2
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

/-- `EPre` and `SivArg` from the facts the contracts give, on the state `σ`:
the whole working space at `W` is `272 + Nw` bytes, with `D` in it. -/
theorem mkPre {Nw : Nat} (hNw : 128 ≤ Nw ∧ Nw ≤ 2176) {σ : State} {C A P W T : Addr} {R N L : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (x0 : σ.gpr .x0 = C) (x1 : σ.gpr .x1 = BitVec.ofNat 64 R) (x2 : σ.gpr .x2 = A)
    (x3 : σ.gpr .x3 = BitVec.ofNat 64 N) (x4 : σ.gpr .x4 = P) (x5 : σ.gpr .x5 = BitVec.ofNat 64 L)
    (x6 : σ.gpr .x6 = T) (x7 : σ.gpr .x7 = W)
    (inC : (⟨C, 512⟩ : Region) ∈ σ.rd ++ σ.wr) (inA : (⟨A, N * 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r ∈ σ.rd ++ σ.wr) (inT : (⟨T, 16⟩ : Region) ∈ σ.rd ++ σ.wr)
    (inP : (⟨P, L⟩ : Region) ∈ σ.wr) (inW : (⟨W, 272 + Nw⟩ : Region) ∈ σ.wr)
    (cP : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (cW : (⟨C, 512⟩ : Region).Disjoint ⟨W, 272 + Nw⟩)
    (pW : (⟨P, L⟩ : Region).Disjoint ⟨W, 272 + Nw⟩) (pT : (⟨P, L⟩ : Region).Disjoint ⟨T, 16⟩)
    (wA : (⟨W, 272 + Nw⟩ : Region).Disjoint ⟨A, N * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, (⟨W, 272 + Nw⟩ : Region).Disjoint r)
    (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 272 + Nw⟩)
    (wrC : C.toNat + 512 ≤ 2 ^ 64) (wrP : P.toNat + L ≤ 2 ^ 64) (wrT : T.toNat + 16 ≤ 2 ^ 64)
    (wrW : W.toNat + (272 + Nw) ≤ 2 ^ 64) (wrA : A.toNat + N * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 σ.mem .u8 A N, r.base.toNat + r.len ≤ 2 ^ 64) (hL : L < 2 ^ 64) :
    EPre Nw σ C A P W (W + BitVec.ofNat 64 dOff) R N L ∧ SivArg Nw σ P W (W + BitVec.ofNat 64 dOff) T L := by
  have sd : Region.Sub ⟨W + BitVec.ofNat 64 dOff, 16⟩ ⟨W, 272 + Nw⟩ :=
    Offset.sub_base _ (by simp only [dOff]; omega)
  have wD : (W + BitVec.ofNat 64 dOff).toNat + 16 ≤ 2 ^ 64 := by
    rw [toNat_add_lt _ wrW (show dOff < 272 + Nw by simp only [dOff]; omega)]; simp only [dOff]; omega
  have inR {r : Region} (h : r ∈ σ.wr) : r ∈ σ.rd ++ σ.wr := List.mem_append_right _ h
  have env (Q : Addr) (n : Nat) (hQ : (⟨Q, n⟩ : Region) ∈ σ.rd ++ σ.wr)
      (qW : (⟨Q, n⟩ : Region).Disjoint ⟨W, 272 + Nw⟩) (wQ : Q.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) :
      Env Nw σ C (W + BitVec.ofNat 64 dOff) Q W R n :=
    ⟨hR, rfl, inC, hQ, inW, cW, (qW.sub_right sd).symm, qW, wrC, wD, wQ, wrW, hn, hNw.1, hNw.2⟩
  exact ⟨⟨env P L (inR inP) pW wrP hL, cW.sub_right sd, cP, inP, x0, x1, x2, x3, x4, x5, x7, inA,
    wA.symm, wA.symm.sub_right sd, wrA,
    fun r hr => env r.base r.len (inL r hr) (wL r hr).symm (wrL r hr) (listed_len hr)⟩,
    ⟨x6, inT, pT.symm, tW, tW.sub_right sd, wrT⟩⟩

/-- `vg_aes_siv_encrypt` with `work: *mut [u64; w]`. -/
def encryptScratchSigW (w : Nat) : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array true .u8 16), ("work", .array true .u64 w)]

/-- `encryptContract`, whatever `work` is (of `w` words). -/
def encryptScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (encryptScratchSigW w).contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.encryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      Proof.AesSiv.encryptRoundsPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_siv_decrypt` with `work: *mut [u64; w]`. -/
def decryptScratchSigW (w : Nat) : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array false .u8 16), ("work", .array true .u64 w)]
  ret := some .u32

/-- `decryptContract`, whatever `work` is (of `w` words). -/
def decryptScratchContractW {M : ISA} (A : Abi M) (w : Nat) (stack : Nat := 0) : Contract M :=
  (decryptScratchSigW w).contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.decryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      Proof.AesSiv.decryptRoundsPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds ads adsCount data len siv _work =>
      Spec.Siv.decryptLeak A.ptrBits ctx rounds ads adsCount data len siv)

/-- `encryptN`'s precondition from the facts of the contract's. -/
theorem mkPreE {Nw : Nat} (hNw : 128 ≤ Nw ∧ Nw ≤ 2176) {s : State}
    (h : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
    (hrd : s.rd = ⟨s.gpr .x0, 512⟩ :: ⟨s.gpr .x2, (s.gpr .x3).toNat * 16⟩ ::
      Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat)
    (hcP : (⟨s.gpr .x0, 512⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩)
    (cW : (⟨s.gpr .x0, 512⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (pT : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 16⟩)
    (pW : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (tW : (⟨s.gpr .x6, 16⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (wA : (⟨s.gpr .x7, 272 + Nw⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat, (⟨s.gpr .x7, 272 + Nw⟩ : Region).Disjoint r)
    (hwC : (s.gpr .x0).toNat + 512 ≤ 2 ^ 64) (hwP : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64)
    (hwT : (s.gpr .x6).toNat + 16 ≤ 2 ^ 64) (hwW : (s.gpr .x7).toNat + (272 + Nw) ≤ 2 ^ 64)
    (wrA : (s.gpr .x2).toNat + (s.gpr .x3).toNat * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat, r.base.toNat + r.len ≤ 2 ^ 64) :
    (encryptN Nw).pre (s.withRegions s.rd (encWrE Nw s)) := by
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrE Nw s := List.mem_append_left _ hr
  have wT : (⟨s.gpr .x6, 16⟩ : Region) ∈ encWrE Nw s := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨e, t⟩ := mkPre hNw (σ := s.withRegions s.rd (encWrE Nw s)) (C := s.gpr .x0) (A := s.gpr .x2)
    (P := s.gpr .x4) (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    (List.mem_append_right _ wT) List.mem_cons_self
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _)
  exact ⟨e, t, wT⟩

set_option linter.unusedSimpArgs false in
/-- The precondition of the contract gives `encryptN`'s on the narrowed state. -/
theorem encPre_of {Nw : Nat} (hNw : Nw = 128 ∨ Nw = 2176) {s : State}
    (h : (encryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pre s) :
    (encryptN Nw).pre (s.withRegions s.rd (encWrE Nw s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 272 + Nw⟩] := by
  rcases hNw with rfl | rfl <;>
  · sig_pre [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre, AArch64.abi,
      AArch64.argRegs, List.append_eq] at h
    sig_split h
    rename_i hrd hwr hcP hcT hc1 hwC hwP hwT hwW hc3
    simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
      Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
      Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj]
      at hrd hwr hc1 hc3
    rw [pairFacts_ro _ (by simp)] at hc1
    obtain ⟨cW, pT, pW, -, -, tW, -, -, wA, wL, -⟩ := hc1
    obtain ⟨wrA, wrL⟩ := hc3
    exact ⟨mkPreE (by decide) h hrd hcP cW pT pW tW wA wL hwC hwP hwT hwW wrA wrL, hwr⟩

/-- `decryptN`'s precondition from the facts of the contract's. -/
theorem mkPreD {Nw : Nat} (hNw : 128 ≤ Nw ∧ Nw ≤ 2176) {s : State}
    (h : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
    (hrd : s.rd = ⟨s.gpr .x0, 512⟩ :: ⟨s.gpr .x6, 16⟩ :: ⟨s.gpr .x2, (s.gpr .x3).toNat * 16⟩ ::
      Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat)
    (hcP : (⟨s.gpr .x0, 512⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩)
    (cW : (⟨s.gpr .x0, 512⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (pT : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 16⟩)
    (pW : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (tW : (⟨s.gpr .x6, 16⟩ : Region).Disjoint ⟨s.gpr .x7, 272 + Nw⟩)
    (wA : (⟨s.gpr .x7, 272 + Nw⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat * 16⟩)
    (wL : ∀ r ∈ Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat, (⟨s.gpr .x7, 272 + Nw⟩ : Region).Disjoint r)
    (hwC : (s.gpr .x0).toNat + 512 ≤ 2 ^ 64) (hwP : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64)
    (hwT : (s.gpr .x6).toNat + 16 ≤ 2 ^ 64) (hwW : (s.gpr .x7).toNat + (272 + Nw) ≤ 2 ^ 64)
    (wrA : (s.gpr .x2).toNat + (s.gpr .x3).toNat * 16 ≤ 2 ^ 64)
    (wrL : ∀ r ∈ Sig.listed 64 s.mem .u8 (s.gpr .x2) (s.gpr .x3).toNat, r.base.toNat + r.len ≤ 2 ^ 64) :
    (decryptN Nw).pre (s.withRegions s.rd (encWrD Nw s)) := by
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ encWrD Nw s := List.mem_append_left _ hr
  exact mkPre hNw (σ := s.withRegions s.rd (encWrD Nw s)) (C := s.gpr .x0) (A := s.gpr .x2)
    (P := s.gpr .x4) (W := s.gpr .x7) (T := s.gpr .x6) (R := (s.gpr .x1).toNat) (N := (s.gpr .x3).toNat)
    (L := (s.gpr .x5).toNat) h rfl (by simp) rfl (by simp) rfl (by simp) rfl rfl
    (inRd (by rw [hrd]; exact List.mem_cons_self))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun r hr => inRd (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr))))
    (inRd (by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
    hcP cW pW pT wA wL tW hwC hwP hwT hwW wrA wrL (BitVec.isLt _)

set_option linter.unusedSimpArgs false in
/-- The precondition of the contract gives `decryptN`'s on the narrowed state. -/
theorem decPre_of {Nw : Nat} (hNw : Nw = 128 ∨ Nw = 2176) {s : State}
    (h : (decryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pre s) :
    (decryptN Nw).pre (s.withRegions s.rd (encWrD Nw s)) ∧
      s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 272 + Nw⟩] := by
  rcases hNw with rfl | rfl <;>
  · sig_pre [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre, AArch64.abi,
      AArch64.argRegs, List.append_eq] at h
    sig_split h
    rename_i hrd hwr hcP hc1 hwC hwP hwT hwW hc3
    simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
      Bool.not_false, filter_true', filter_false', filterMap_some', filterMap_none', List.map_id', Sig.conj_cons,
      Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true, List.nil_append, List.append_nil, Sig.conj]
      at hrd hwr hc1 hc3
    rw [pairFacts_ro _ (by simp)] at hc1
    obtain ⟨cW, pT, pW, -, -, tW, wA, wL, -⟩ := hc1
    obtain ⟨wrA, wrL⟩ := hc3
    exact ⟨mkPreD (by decide) h hrd hcP cW pT pW tW wA wL hwC hwP hwT hwW wrA wrL, hwr⟩

/-- A run from a narrowed state is a run from the state. -/
theorem narrow_exec {c : Prog isa} {s s₁ : State} {t : List Leak} {ws : List Region} (hc : Covers ws s.wr)
    (he : Exec isa c (s.withRegions s.rd ws) t s₁) : Exec isa c s t (s₁.withRegions s.rd s.wr) :=
  Exec.widen (s := s.withRegions s.rd ws) (rd := s.rd) (wr := s.wr) he (Covers.append (Covers.refl s.rd) hc) hc

theorem encWrE_covers {Nw : Nat} {s : State}
    (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, 16⟩, ⟨s.gpr .x7, 272 + Nw⟩]) :
    Covers (encWrE Nw s) s.wr := by
  rw [hwr]; exact Covers.refl _

theorem encWrD_covers {Nw : Nat} {s : State} (hwr : s.wr = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x7, 272 + Nw⟩]) :
    Covers (encWrD Nw s) s.wr := by
  rw [hwr]; exact Covers.refl _

/-- A state satisfying the precondition of `vg_aes_siv_encrypt`, with no
associated data and no data: `siv` at `0x5000`, `F` bytes of working space
at `0x4000`. -/
def encSatW (F : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x4 => 0x3000 | .x6 => 0x5000 | .x7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩, ⟨0x4000, F⟩]

/-- `encSatW`, with `siv` read only. -/
def decSatW (F : Nat) : State :=
  { encSatW F with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩], wr := [⟨0x3000, 0⟩, ⟨0x4000, F⟩] }

theorem encSat_pre {Nw : Nat} (hNw : Nw = 128 ∨ Nw = 2176) :
    ∃ s, (encryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pre s := by
  rcases hNw with rfl | rfl
  · sig_implies_sat [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre,
      AArch64.abi, AArch64.argRegs] [encSatW] using encSatW 400
  · sig_implies_sat [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre,
      AArch64.abi, AArch64.argRegs] [encSatW] using encSatW 2448

theorem decSat_pre {Nw : Nat} (hNw : Nw = 128 ∨ Nw = 2176) :
    ∃ s, (decryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pre s := by
  rcases hNw with rfl | rfl
  · sig_implies_sat [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
      AArch64.abi, AArch64.argRegs] [decSatW, encSatW] using decSatW 400
  · sig_implies_sat [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
      AArch64.abi, AArch64.argRegs] [decSatW, encSatW] using decSatW 2448

theorem encPub_of {Nw : Nat} {s₁ s₂ : State}
    (hp : (encryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrE Nw s₁)) (s₂.withRegions s₂.rd (encWrE Nw s₂)) := by
  sig_pub [encryptScratchContractW, encryptScratchSigW, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem decPub_of {Nw : Nat} {s₁ s₂ : State}
    (hp : (decryptScratchContractW AArch64.abi ((272 + Nw) / 8)).pub s₁ s₂) :
    encPub (s₁.withRegions s₁.rd (encWrD Nw s₁)) (s₂.withRegions s₂.rd (encWrD Nw s₂)) := by
  sig_pub [decryptScratchContractW, decryptScratchSigW, Spec.Siv.decryptPre,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] at hp
  sig_split hp
  rename_i q1 _ q2 q3 q4 q5 q6 q7 q8 q9
  exact ⟨q2, q3, q4, q5, q6, q7, q8, q9, q1, hp⟩

theorem encrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (encrypt v.callee v.ctr.callee v.ctr.suffix)
      (encryptScratchContractW AArch64.abi ((272 + sivNw v) / 8)) :=
  Verified.of_narrow (k := encryptN (sivNw v))
    ⟨encryptN_correct v, encryptN_ct v,
      (encSat_pre (sivNw_cases v)).elim fun s hs => ⟨_, (encPre_of (sivNw_cases v) hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrE (sivNw v) s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (encPre_of (sivNw_cases v) hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrE_covers (encPre_of (sivNw_cases v) hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [encryptScratchContractW, encryptScratchSigW, Proof.AesSiv.encryptRoundsPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => encPub_of hp) (encSat_pre (sivNw_cases v))

theorem decrypt_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target (decrypt v.callee v.ctr.callee v.ctr.suffix)
      (decryptScratchContractW AArch64.abi ((272 + sivNw v) / 8)) :=
  Verified.of_narrow (k := decryptN (sivNw v))
    ⟨decryptN_correct v, decryptN_ct v,
      (decSat_pre (sivNw_cases v)).elim fun s hs => ⟨_, (decPre_of (sivNw_cases v) hs).1⟩⟩
    (fun s => s.withRegions s.rd (encWrD (sivNw v) s)) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun s hs => (decPre_of (sivNw_cases v) hs).1)
    (fun s t s₁ hs he => narrow_exec (encWrD_covers (decPre_of (sivNw_cases v) hs).2) he)
    (fun s t s₁ hs he ha hq => ⟨ha, by
      sig_post [decryptScratchContractW, decryptScratchSigW, Proof.AesSiv.decryptRoundsPost,
        AArch64.abi, AArch64.argRegs]
      exact fun _ => hq⟩)
    (fun s₁ s₂ _ _ hp => decPub_of hp) (decSat_pre (sivNw_cases v))

end VG.Proof.AesSiv.AArch64

end

end


/-!
# AES-SIV on AArch64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of `48 + sivInitW v` bytes that allocates it
(`Verified.stackScratch`). Its calls keep their return address in `x30`, so
they use no stack below it.

`encrypt` and `decrypt` run theirs, proved with the working space as their
last argument (in `x7`), in a frame of `272 + sivNw v` bytes that allocates
it, the same way: the frame leaves the memory as it is, so the list of
slices they take needs nothing more. Each returns with its whole frame
zeroed and the registers it may leave secret cleared
(`Impl.AesSiv.AArch64.Fn`: `init_scrubbed`, `encrypt_scrubbed`, `decrypt_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.Impl.AesSiv.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSatW 0 with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre560 : ∃ s, (Spec.Siv.initContract AArch64.abi 560).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSatW] using initFrameSat

theorem initFrameSat_pre2224 : ∃ s, (Spec.Siv.initContract AArch64.abi 2224).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSatW] using initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (48 + sivInitW v) .x3 (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract AArch64.abi (48 + sivInitW v)) := by
  obtain hv := init_verified v
  rcases v.scratch_ok with h | h <;> simp only [sivInitW, Impl.AesSiv.AArch64.Fn.initWork, h, Nat.reduceAdd, Nat.reduceDiv, ite_true,
    show (2048 : Nat) ≠ 0 by decide, ite_false] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 70)
      (pre := Spec.Siv.initPre AArch64.abi.ptrBits) (post := Spec.Siv.initPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 560) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre560
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 278)
      (pre := Spec.Siv.initPre AArch64.abi.ptrBits) (post := Spec.Siv.initPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 2224) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre2224

/-- A state satisfying `vg_aes_siv_encrypt`'s precondition, without the
working space. -/
def encFrameSat : State := { encSatW 0 with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩] }

theorem encFrameSat_pre400 : ∃ s, (Proof.AesSiv.encryptRoundsContract AArch64.abi 400).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs] [encFrameSat, encSatW] using encFrameSat

theorem encFrameSat_pre2448 : ∃ s, (Proof.AesSiv.encryptRoundsContract AArch64.abi 2448).pre s := by
  implies_sat [Proof.AesSiv.encryptRoundsContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, AArch64.abi,
    AArch64.argRegs] [encFrameSat, encSatW] using encFrameSat

theorem encrypt_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (encrypt v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.encryptRoundsContract AArch64.abi (272 + sivNw v)) := by
  obtain hv := encrypt_verified v
  rcases sivNw_cases v with h | h <;> rw [h] at hv ⊢ <;> simp only [Nat.reduceAdd, Nat.reduceDiv] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 50)
      (pre := Spec.Siv.encryptPre AArch64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 400) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.encryptPostOut_local _ vs m m₁ m₂ r hl) encFrameSat_pre400
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 306)
      (pre := Spec.Siv.encryptPre AArch64.abi.ptrBits) (post := Proof.AesSiv.encryptRoundsPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 2448) hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.encryptPostOut_local _ vs m m₁ m₂ r hl) encFrameSat_pre2448

/-- A state satisfying `vg_aes_siv_decrypt`'s precondition, without the
working space. -/
def decFrameSat : State := { decSatW 0 with wr := [⟨0x3000, 0⟩] }

theorem decFrameSat_pre400 : ∃ s, (Proof.AesSiv.decryptRoundsContract AArch64.abi 400).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] [decFrameSat, decSatW, encSatW] using decFrameSat

theorem decFrameSat_pre2448 : ∃ s, (Proof.AesSiv.decryptRoundsContract AArch64.abi 2448).pre s := by
  implies_sat [Proof.AesSiv.decryptRoundsContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Proof.AesSiv.decryptRoundsPost,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] [decFrameSat, decSatW, encSatW] using decFrameSat

theorem decrypt_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (decrypt v.callee v.ctr.callee v.ctr.suffix))
      (Proof.AesSiv.decryptRoundsContract AArch64.abi (272 + sivNw v)) := by
  obtain hv := decrypt_verified v
  rcases sivNw_cases v with h | h <;> rw [h] at hv ⊢ <;> simp only [Nat.reduceAdd, Nat.reduceDiv] at hv ⊢
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 50)
      (pre := Spec.Siv.decryptPre AArch64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 400) (leak := some (Spec.Siv.decryptLeak AArch64.abi.ptrBits))
      hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.decryptPostOut_local _ vs m m₁ m₂ r hl) decFrameSat_pre400
  · exact AArch64.Verified.stackScratch (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 306)
      (pre := Spec.Siv.decryptPre AArch64.abi.ptrBits) (post := Proof.AesSiv.decryptRoundsPost AArch64.abi.ptrBits)
      (wa := true) (stack := 0) (bytes := 2448) (leak := some (Spec.Siv.decryptLeak AArch64.abi.ptrBits))
      hv (by decide) (by decide)
      (fun vs m m₁ m₂ r hl _ => Proof.AesSiv.decryptPostOut_local _ vs m m₁ m₂ r hl) decFrameSat_pre2448

/-! ## Without secret residue -/

theorem keyRepr_local {m₁ m₂ : Mem} {p : Addr} {key : List Byte}
    (h : ∀ a, Region.Contains ⟨p, 512⟩ a 1 → m₁ a = m₂ a) (hr : Spec.Siv.KeyRepr m₁ p key) :
    Spec.Siv.KeyRepr m₂ p key := by
  have e {d n : Nat} (hn : d + n ≤ 512) :
      Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
    simp only [Spec.Aes.bytesAt]
    refine List.map_congr_left fun i hi => (h _ ?_).symm
    have := List.mem_range.mp hi
    rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hn, this]) (by omega_using [hn, this])
  obtain ⟨hl, h1, h2, h3, h4⟩ := hr
  have hn : 16 * (Spec.Aes.rounds (key.length / 8) + 1) ≤ 240 := by
    simp only [Spec.Aes.rounds]; rcases hl with h | h | h <;> rw [h] <;> decide
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · have := e (d := 0) (n := 16 * (Spec.Aes.rounds (key.length / 8) + 1)) (by omega_using [hn])
    rw [show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p] at this
    rw [this]; exact h1
  · rw [show p + 240 = p + BitVec.ofNat 64 240 from rfl, e (by decide)]; exact h2
  · rw [show p + 256 = p + BitVec.ofNat 64 256 from rfl, e (by decide)]; exact h3
  · rw [show p + 272 = p + BitVec.ofNat 64 272 from rfl, e (by omega_using [hn])]; exact h4

/-- `vg_aes_siv_init`'s postcondition reads the memory on return only within
the context, so it returns with its whole frame zeroed
(`ScrubAll.withScrubAll`). -/
theorem initOk (W : Nat) (hW : 0 < W) :
    ScrubAll.ScrubAllOk (Spec.Siv.initContract abi W) W (Spec.Siv.initSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Siv.initSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [key, kl, ctx], _ =>
      simp only [Spec.Siv.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact keyRepr_local hb.2 h

/-- `vg_aes_siv_encrypt`'s postcondition reads the memory on return only
within the data and `siv`. -/
theorem encryptOk (W : Nat) (hW : 0 < W) :
    ScrubAll.ScrubAllOk (Spec.Siv.encryptContract abi W) W (Spec.Siv.encryptSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Siv.encryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.encryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.encryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2 i (by omega),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)]

/-- `vg_aes_siv_decrypt`'s postcondition reads the memory on return only
within the data. -/
theorem decryptOk (W : Nat) (hW : 0 < W) :
    ScrubAll.ScrubAllOk (Spec.Siv.decryptContract abi W) W (Spec.Siv.decryptSig.retBits abi.ptrBits) :=
  ScrubAll.scrubAllOk_regs (sig := Spec.Siv.decryptSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr] (Spec.Siv.decryptPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.decryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth 64 len).toNat) fun i hi =>
        Proof.AesSiv.agree_of hb.2.1 i (by simpa using hi)
      rw [e]
      exact h key hk

/-! ## The functions, as emitted

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` with their
cleanup (`Impl.AesSiv.AArch64.Fn`): each meets its contract in constant
time and returns without secret residue (`VerifiedScrubbed`), which is what
its registration binds. What the cleanup needs of the code
(`ScrubAll.scrubSide`) is proved of each function's own instructions here,
once, with code that does nothing in the place of the functions it calls,
and of each implementation where it is defined (`UpdateImpl.scrub`,
`Ctr32Impl.scrub`, `Ctr32Impl.expandScrub`). -/

open VG.AArch64.ScrubAll

private theorem init_all {p : Instr → Bool} (B : Nat) (e : Impl.Aes.AArch64.ExpandKey)
    (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x3 (init ⟨"", .block [], ⟨[], [], []⟩⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) = true)
    (he : sideAll p e.code = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x3 (init e c sfx)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, init, Impl.CmacAes.AArch64.subkeys, sideAll,
    Bool.and_eq_true] at h0 ⊢
  simp only [h0, he, hc, and_self]

private theorem init_own (B : Nat) :
    calleeSide (Impl.StackScratch.AArch64.withStackScratch B .x3 (init ⟨"", .block [], ⟨[], [], []⟩⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) Impl.AesSiv.AArch64.Fn.initOwn = true := by
  kernel_rfl

private theorem init_depth (e : Impl.Aes.AArch64.ExpandKey) (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (he : e.code.aarch64Depth = 0) (hc : c.code.aarch64Depth = 0) : (init e c sfx).aarch64Depth = 0 := by
  simp only [init, Impl.CmacAes.AArch64.subkeys, Code.aarch64Depth, he, hc]
  decide

theorem init_side (v : Ctr32Impl) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (48 + sivInitW v) .x3 (init v.expand v.callee v.suffix)) (48 + sivInitW v) 0
      ((Impl.AesSiv.AArch64.Fn.initOwn.union v.expand.clear).union v.callee.clear) [] = true := by
  refine scrubSide_union ?_ ?_ (by decide)
    (init_all _ v.expand v.callee v.suffix (sideAll_union_left (sideAll_union_left (init_own _)))
      (sideAll_union_left (sideAll_union_right v.expandScrub)) (sideAll_union_right v.scrub))
    (linkRegs_union (by decide))
  · rcases v.scratch_ok with h | h <;> simp only [sivInitW, Impl.AesSiv.AArch64.Fn.initWork, h] <;> decide
  · simp only [Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits,
      init_depth _ _ _ (Proof.Aes.AArch64.depth_of_noFrames v.expandNoFrames)
        (Proof.Aes.AArch64.depth_of_noFrames v.noFrames)]
    rcases v.scratch_ok with h | h <;> simp only [sivInitW, Impl.AesSiv.AArch64.Fn.initWork, h] <;> decide

/-- `vg_aes_siv_init` over `v` as emitted, cleanup included: its frame is 560
bytes over an implementation that needs no working space, else 2224. -/
theorem init_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed AArch64.target
      (Impl.AesSiv.AArch64.Fn.init v.expand v.callee v.suffix)
      (Spec.Siv.initContract abi (48 + sivInitW v)) 0 := by
  unfold Impl.AesSiv.AArch64.Fn.init
  rw [v.scratch_eq]
  exact verifiedScrubbed (api := Spec.Siv.initApi)
    { code := Impl.StackScratch.AArch64.withStackScratch (48 + sivInitW v) .x3 (init v.expand v.callee v.suffix)
      verified := init_framed v
      consts := []
      stack := 48 + sivInitW v } _ (initOk _ (by omega_using [])) (init_side v)

private theorem encrypt_all {p : Instr → Bool} (B : Nat) (u : Impl.CmacAes.AArch64.Update)
    (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x7 (encrypt ⟨"", .block [], ⟨[], [], []⟩, 0⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) = true)
    (hu : sideAll p u.code = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x7 (encrypt u c sfx)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, encrypt, encS2v, s2vAds, cmacOf, Impl.AesSiv.AArch64.finish, shortMac, longMac, ctr, ctrWhole, ctrBody, callUpdate, callFinalize, Impl.CmacAes.AArch64.finalize, sideAll,
    Bool.and_eq_true] at h0 ⊢
  simp only [h0, hu, hc, and_self]

private theorem encrypt_own (B : Nat) :
    calleeSide (Impl.StackScratch.AArch64.withStackScratch B .x7 (encrypt ⟨"", .block [], ⟨[], [], []⟩, 0⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) Impl.AesSiv.AArch64.Fn.cryptOwn = true := by
  kernel_rfl

private theorem encrypt_depth (u : Impl.CmacAes.AArch64.Update) (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (hu : u.code.aarch64Depth = 0) (hc : c.code.aarch64Depth = 0) : (encrypt u c sfx).aarch64Depth = 0 := by
  simp only [encrypt, encS2v, s2vAds, cmacOf, Impl.AesSiv.AArch64.finish, shortMac, longMac, ctr, ctrWhole, ctrBody, callUpdate, callFinalize, Impl.CmacAes.AArch64.finalize, Code.aarch64Depth, hu, hc]
  decide

theorem encrypt_side (v : Proof.CmacAes.AArch64.UpdateImpl) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (encrypt v.callee v.ctr.callee v.ctr.suffix)) (272 + sivNw v) 0
      ((Impl.AesSiv.AArch64.Fn.cryptOwn.union v.callee.clear).union v.ctr.callee.clear) [] = true := by
  refine scrubSide_union ?_ ?_ (by decide)
    (encrypt_all _ v.callee v.ctr.callee v.ctr.suffix (sideAll_union_left (sideAll_union_left (encrypt_own _)))
      (sideAll_union_left (sideAll_union_right v.scrub)) (sideAll_union_right v.ctr.scrub))
    (linkRegs_union (by decide))
  · rcases v.scratch_ok with h | h <;> rcases v.ctr.scratch_ok with h' | h' <;>
      simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h'] <;> decide
  · simp only [Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits,
      encrypt_depth _ _ _ (Proof.Aes.AArch64.depth_of_noFrames v.noFrames)
        (Proof.Aes.AArch64.depth_of_noFrames v.ctr.noFrames)]
    rcases v.scratch_ok with h | h <;> rcases v.ctr.scratch_ok with h' | h' <;>
      simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h'] <;> decide

/-- `vg_aes_siv_encrypt` over `v` as emitted, cleanup included: its frame is 400
bytes over implementations that need no working space, else 2448. -/
theorem encrypt_scrubbed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    VerifiedScrubbed AArch64.target
      (Impl.AesSiv.AArch64.Fn.encrypt v.callee v.ctr.callee v.ctr.suffix)
      (Spec.Siv.encryptContract abi (272 + sivNw v)) 0 := by
  unfold Impl.AesSiv.AArch64.Fn.encrypt
  rw [v.scratch_eq, v.ctr.scratch_eq]
  exact verifiedScrubbed (api := Spec.Siv.encryptApi)
    { code := Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (encrypt v.callee v.ctr.callee v.ctr.suffix)
      verified := Proof.AesSiv.encrypt_keyed (encrypt_framed v)
      consts := []
      stack := 272 + sivNw v } _ (encryptOk _ (by omega_using [])) (encrypt_side v)

private theorem decrypt_all {p : Instr → Bool} (B : Nat) (u : Impl.CmacAes.AArch64.Update)
    (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x7 (decrypt ⟨"", .block [], ⟨[], [], []⟩, 0⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) = true)
    (hu : sideAll p u.code = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratch B .x7 (decrypt u c sfx)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, decrypt, openTail, encS2v, s2vAds, cmacOf, Impl.AesSiv.AArch64.finish, shortMac, longMac, ctr, ctrWhole, ctrBody, callUpdate, callFinalize, Impl.CmacAes.AArch64.finalize, sideAll,
    Bool.and_eq_true] at h0 ⊢
  simp only [h0, hu, hc, and_self]

private theorem decrypt_own (B : Nat) :
    calleeSide (Impl.StackScratch.AArch64.withStackScratch B .x7 (decrypt ⟨"", .block [], ⟨[], [], []⟩, 0⟩ ⟨"", .block [], ⟨[], [], []⟩, 0⟩ "")) Impl.AesSiv.AArch64.Fn.cryptOwn = true := by
  kernel_rfl

private theorem decrypt_depth (u : Impl.CmacAes.AArch64.Update) (c : Impl.Aes.AArch64.Ctr32) (sfx : String)
    (hu : u.code.aarch64Depth = 0) (hc : c.code.aarch64Depth = 0) : (decrypt u c sfx).aarch64Depth = 0 := by
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, Impl.AesSiv.AArch64.finish, shortMac, longMac, ctr, ctrWhole, ctrBody, callUpdate, callFinalize, Impl.CmacAes.AArch64.finalize, Code.aarch64Depth, hu, hc]
  decide

theorem decrypt_side (v : Proof.CmacAes.AArch64.UpdateImpl) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (decrypt v.callee v.ctr.callee v.ctr.suffix)) (272 + sivNw v) 32
      ((Impl.AesSiv.AArch64.Fn.cryptOwn.union v.callee.clear).union v.ctr.callee.clear) [] = true := by
  refine scrubSide_union ?_ ?_ (by decide)
    (decrypt_all _ v.callee v.ctr.callee v.ctr.suffix (sideAll_union_left (sideAll_union_left (decrypt_own _)))
      (sideAll_union_left (sideAll_union_right v.scrub)) (sideAll_union_right v.ctr.scrub))
    (linkRegs_union (by decide))
  · rcases v.scratch_ok with h | h <;> rcases v.ctr.scratch_ok with h' | h' <;>
      simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h'] <;> decide
  · simp only [Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits,
      decrypt_depth _ _ _ (Proof.Aes.AArch64.depth_of_noFrames v.noFrames)
        (Proof.Aes.AArch64.depth_of_noFrames v.ctr.noFrames)]
    rcases v.scratch_ok with h | h <;> rcases v.ctr.scratch_ok with h' | h' <;>
      simp only [sivNw, Impl.AesSiv.AArch64.Fn.cryptWork, h, h'] <;> decide

/-- `vg_aes_siv_decrypt` over `v` as emitted, cleanup included: its frame is 400
bytes over implementations that need no working space, else 2448. -/
theorem decrypt_scrubbed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    VerifiedScrubbed AArch64.target
      (Impl.AesSiv.AArch64.Fn.decrypt v.callee v.ctr.callee v.ctr.suffix)
      (Spec.Siv.decryptContract abi (272 + sivNw v)) 32 := by
  unfold Impl.AesSiv.AArch64.Fn.decrypt
  rw [v.scratch_eq, v.ctr.scratch_eq]
  exact verifiedScrubbed (api := Spec.Siv.decryptApi)
    { code := Impl.StackScratch.AArch64.withStackScratch (272 + sivNw v) .x7 (decrypt v.callee v.ctr.callee v.ctr.suffix)
      verified := Proof.AesSiv.decrypt_keyed (decrypt_framed v)
      consts := []
      stack := 272 + sivNw v } _ (decryptOk _ (by omega_using [])) (decrypt_side v)

end VG.Proof.AesSiv.AArch64
