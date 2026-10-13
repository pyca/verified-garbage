module

public import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
public import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Modes.X86_64.CbcDecrypt
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecrypt
public import VerifiedGarbage.Proof.Modes.X86_64.CbcEncrypt
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncrypt
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# CAST5-CBC on x86-64 meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
(`Proof.Modes.X86_64.cbcEncrypt_wp` and `cbcDecrypt_wp`) over CAST5's core
(`Mode.dirCoreSpec`), with the working space at `r9`. The table of S-boxes is
readable where the static `VG_CAST5_S1234` puts it and holds the S-boxes.
`cbcEncrypt_verified`, `cbcDecrypt_verified`: each is correct and constant
time, by the taint analysis: the pointers, `rounds`, `n`, the stack pointer
and the table's address are public, and so is everything the code computes
from them; the subkeys, the chaining value and the data are secret.
`cbcEncrypt_framed` and `cbcDecrypt_framed` run them with their working
space on the stack, zeroed on return: 240 bytes, the 29 words of the scratch
buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5 (Held)
open VG.Proof.Cast5.X86_64.Mode (dirCoreSpec TabAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- The facts of CBC's precondition on this target, with the working space at
`r9`. -/
structure CPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 128⟩, ⟨s.gpr .rdx, 8⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩, ⟨s.gpr .r9, 232⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r9, 232⟩
  dKD : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r9, 232⟩
  dVD : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dVS : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .r9, 232⟩
  dDS : Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩ ⟨s.gpr .r9, 232⟩
  dRD : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dRS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 232⟩
  fK : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .rcx).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .r9).toNat + 232 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 16

/-- The data, in blocks. -/
abbrev dataOf (s : State) (m : Mem) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m (s.gpr .rcx) (s.gpr .r8).toNat
/-- The chaining value. -/
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rdx) 8
/-- The subkeys. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .rdi)

/-- The public arguments and the table's address. -/
def cbcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

/-- CBC encryption on x86-64 with its working space at `r9`. -/
def cbcEncX : Contract isa where
  pre := CPre
  post s s' := dataOf s s'.mem = Spec.Cbc.encrypt (Spec.Cast5.cipher (keyOf s) (s.gpr .rsi).toNat) (ivOf s)
    (dataOf s s.mem)
  pub := cbcPub

/-- CBC decryption on x86-64 with its working space at `r9`. -/
def cbcDecX : Contract isa where
  pre := CPre
  post s s' := dataOf s s'.mem = Spec.Cbc.decrypt (Spec.Cast5.invCipher (keyOf s) (s.gpr .rsi).toNat) (ivOf s)
    (dataOf s s.mem)
  pub := cbcPub

/-- The table, as the core needs it. -/
theorem CPre.tabAt {s : State} (h : CPre s) : TabAt s :=
  ⟨by rw [h.rd]; simp, h.fitT, fun i hi => h.held i (by rw [s1234_length] at hi; exact hi), fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h.dTD
    · exact h.dTS⟩

theorem CPre.rsi {s : State} (_ : CPre s) : s.gpr .rsi = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The key's arguments, apart from the regions `rs`. -/
theorem CPre.keyArgs {s : State} (h : CPre s) {rs : List Region}
    (hK : ∀ r ∈ rs, Region.Disjoint ⟨s.gpr .rdi, 128⟩ r)
    (hT : ∀ r ∈ rs, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r) :
    Mode.ModeKeyArgs s rs (keyOf s, (s.gpr .rsi).toNat) :=
  ⟨⟨s.gpr .rdi, rfl, rfl, by rw [h.rd]; simp, h.fK, hK⟩, h.rsi, h.rounds, h.tabAt, hT⟩

theorem CPre.ret {s s' : State} (h : CPre s)
    (hf : Frame [⟨s.gpr .r9, 8 * (dirCore true).ctrSlots⟩, ⟨s.gpr .rcx, 8 * (dirCore true).bw * (s.gpr .r8).toNat⟩]
      s.mem s'.mem) : s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.dRS
  · rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]; exact h.dRD

theorem cbcDecrypt_wp {s₀ : State} (hp : cbcDecX.pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX.post s₀ s' := by
  have hp' : CPre s₀ := hp
  have hwS : (⟨s₀.gpr .r9, 8 * 29⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have hwD : (⟨s₀.gpr .rcx, 8 * 1 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.wr := by
    rw [hp'.wr, Nat.mul_one, Nat.mul_comm]; simp
  have e : 8 * (dirCore false).bw * (s₀.gpr .r8).toNat = (s₀.gpr .r8).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.X86_64.cbcDecrypt_wp (dirCoreSpec false) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := (keyOf s₀, (s₀.gpr .rsi).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.rd]; simp) hwD hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.fD)
    (hp'.keyArgs (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp'.dKS)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp'.dTS)))
    fun s' ⟨hcs, hdata, hf, _, _⟩ => ⟨⟨hcs, hp'.ret hf⟩, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  exact hdata

theorem cbcEncrypt_wp {s₀ : State} (hp : cbcEncX.pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX.post s₀ s' := by
  have hp' : CPre s₀ := hp
  have hwS : (⟨s₀.gpr .r9, 8 * 29⟩ : Region) ∈ s₀.wr := by rw [hp'.wr]; simp
  have hwD : (⟨s₀.gpr .rcx, 8 * 1 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.wr := by
    rw [hp'.wr, Nat.mul_one, Nat.mul_comm]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .r8).toNat = (s₀.gpr .r8).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.X86_64.cbcEncrypt_wp (dirCoreSpec true) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := (keyOf s₀, (s₀.gpr .rsi).toNat)) rfl rfl rfl rfl ⟨hwS, hp'.fS⟩
    (by rw [hp'.rd]; simp) hwD hp'.dVS (by rw [e]; exact hp'.dDS) (by rw [e]; exact hp'.dVD)
    (by rw [e]; exact hp'.fD)
    (hp'.keyArgs (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dKS
        · rw [e]; exact hp'.dKD)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp'.dTS
        · rw [e]; exact hp'.dTD)))
    fun s' ⟨hcs, hdata, hf, _, _⟩ => ⟨⟨hcs, hp'.ret hf⟩, ?_⟩
  rw [dirCore_bw, Nat.mul_one, blocksOf_eq, blocksOf_eq] at hdata
  exact hdata

/-! ## Constant time -/

def cbcTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [0, 8 * 29], bases := [(.r9, 1, 0)] }

theorem cbcTaint_wf (s : State) (hs : CPre s) : Taint.Wf cbcTaint s := by
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hs.wr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ (s.gpr .r8).toNat * 8; omega)
        (List.Forall₂.cons (by change 8 * 29 ≤ 232; omega) List.Forall₂.nil)
    · exact List.Pairwise.cons (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hs.dDS)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change (s.gpr .r8).toNat * 8 ≤ 2 ^ 64
        have := hs.fD; omega
      · change 232 ≤ 2 ^ 64; omega
  · intro p hp
    simp only [cbcTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hs.wr]
    change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem cbcTaint_agree (s t : State) (hs : CPre s) (ht : CPre t) (hp : cbcPub s t) :
    X86_64.Taint.AgreeS [s1234Sym] cbcTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  refine ⟨⟨?_, ?_, cbcTaint_wf s hs, cbcTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩, fun n hn => ?_⟩
  · constructor
    · intro r hr
      simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6, p7]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.wr, ht.wr, p4, p5, p6]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [cbcTaint, RegSet.not_mem_empty] at hr
  · simp only [List.mem_singleton] at hn
    subst hn
    exact p8

theorem cbcEncrypt_ct : ConstantTime isa cbcEncX.pre cbcEncX.pub cbcEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) cbcTaint cbcTaint_agree (by taint_decide)

theorem cbcDecrypt_ct : ConstantTime isa cbcDecX.pre cbcDecX.pub cbcDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) cbcTaint cbcTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- CBC's contract with the working space as a sixth argument, under the
calling convention with the table. -/
abbrev cbcK (post : Spec.Cast5.cbcSig.Post X86_64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cbcSig 29
    (Spec.Cast5.cbcPre X86_64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def cbcSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 232⟩]
  syms _ := 0x100000

theorem cbc_implies {postX : State → State → Prop} {post : Spec.Cast5.cbcSig.Post X86_64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (cbcK post).post s s') :
    ({ pre := CPre, post := postX, pub := cbcPub } : Contract isa).Implies (cbcK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
      Spec.Cast5.cbcPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKD, dKS, dVD, dVS, dDS, -, -, spD, spS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self), dKD, dKS, dVD, dVS, dDS, spD, spS, fK,
      fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig, X86_64.abi,
      X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨cbcSat, by
    generalize e : cbcSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
      Spec.Cast5.cbcPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x3000, 8⟩ : Region), ⟨0x4000, 232⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cbcEncrypt_verified : Verified X86_64.target cbcEncrypt (cbcK (Proof.Cast5.cbcEncPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncrypt) (by lit_decide) he hg, hpost⟩)
    cbcEncrypt_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
        Proof.Cast5.cbcEncPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cbcDecrypt_verified : Verified X86_64.target cbcDecrypt (cbcK (Proof.Cast5.cbcDecPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecrypt) (by lit_decide) he hg, hpost⟩)
    cbcDecrypt_ct (cbc_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcSig,
        Proof.Cast5.cbcDecPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 240 bytes of stack. -/
def cbcFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem cbcFrame_sat (post : Spec.Cast5.cbcSig.Post X86_64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcSig.contract (X86_64.abi.withConsts ecbConsts) (Spec.Cast5.cbcPre X86_64.abi.ptrBits) post
      true (0 + 240)).pre s := by
  refine ⟨cbcFrameSat, ?_⟩
  generalize e : cbcFrameSat = s
  sig_pre [Spec.Cast5.cbcSig, Spec.Cast5.cbcPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x3000, 8⟩ : Region)] at hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `cbcEncrypt` with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cbcEncrypt)
      (Spec.Cast5.cbcEncryptContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cbcPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cbcEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cbcEncrypt_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cbcEncPostOut_local _) (cbcFrame_sat _)

/-- `cbcDecrypt` with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cbcDecrypt)
      (Spec.Cast5.cbcDecryptContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cbcPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cbcDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cbcDecPostOut_local _) (cbcFrame_sat _)

end VG.Proof.Cast5.X86_64
