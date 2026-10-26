module

public import VerifiedGarbage.Proof.Cast5.AArch64.ModeCore
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
public import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Cast5.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Cast5.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# CAST5-OFB and -CFB64 on AArch64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.AArch64.fb_wp`) over CAST5's core (`Mode.dirCoreSpec true`),
with the IV's address in `x25`, which the core never writes
(`Mode.crypt_keeps`), the specification's results (`Proof.Modes.ofb_of`, …),
and the working space at `x5`. The table of S-boxes is readable where the
static `VG_CAST5_S1234` puts it and holds the S-boxes. `ofb_verified`, …:
each is correct and constant time, by the taint analysis: the pointers,
`rounds`, `n`, the stack pointer and the table's address are public, and so
is everything the code computes from them, which it keeps in registers; the
subkeys, the IV and the data are secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 112 bytes, the 13 words of the
scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.AArch64.Mode (dirCoreSpec TabAt SchedAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

/-- The data, in blocks. -/
abbrev dataOf (s : State) (m : Mem) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m (s.gpr .x3) (s.gpr .x4).toNat
/-- The chaining value. -/
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .x2) 8
/-- The subkeys. -/
abbrev keyOf (s : State) : Spec.Cast5.Schedule := Spec.Cast5.scheduleAt s.mem (s.gpr .x0)

/-- The public arguments and the table's address. -/
def cbcPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

/-- The public registers. -/
def modePub : List Reg := [.x0, .x1, .x2, .x3, .x4, .x5]

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) (hv : c.allInstrs keepsV = true) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, Exec.preservedV he hv⟩

/-- The facts of the feedback modes' precondition on this target, with the
working space at `x5`. -/
structure FPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .x2, 8⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩, ⟨s.gpr .x5, 104⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTV : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x2, 8⟩
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x5, 104⟩
  dKV : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x2, 8⟩
  dKD : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x5, 104⟩
  dVD : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  dVS : Region.Disjoint ⟨s.gpr .x2, 8⟩ ⟨s.gpr .x5, 104⟩
  dDS : Region.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩ ⟨s.gpr .x5, 104⟩
  fK : (s.gpr .x0).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .x3).toNat + (s.gpr .x4).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .x5).toNat + 104 ≤ 2 ^ 64
  rounds : (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16

/-- CAST5 encryption under the key of `s`. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Cast5.cipher (keyOf s) (s.gpr .x1).toNat

def ofbX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x4).toNat
  pub := cbcPub

def cfbEncX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem))
  pub := cbcPub

def cfbDecX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
  pub := cbcPub

/-- The table, as the core needs it. -/
theorem FPre.tabAt {s : State} (h : FPre s) : TabAt s :=
  ⟨by rw [h.rd]; simp, h.fitT, fun i hi => h.held i (by rw [s1234_length] at hi; exact hi), fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.dTV
    · exact h.dTD
    · exact h.dTS⟩

/-- The subkeys, as the core needs them. -/
theorem FPre.schedAt {s : State} (h : FPre s) : SchedAt s (s.gpr .x0) :=
  ⟨by rw [h.rd]; simp, h.fK, fun w hw => by
    rw [h.wr] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact h.dKV
    · exact h.dKD
    · exact h.dKS⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre s₀) :
    WP isa ((dirCore true).fb mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat =
        (List.range (s₀.gpr .x4).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x2) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat := by
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .x4).toNat = (s₀.gpr .x4).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.AArch64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (n := (s₀.gpr .x4).toNat)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [e, hp.wr]; simp) hp.dVS (by rw [e]; exact hp.dDS) (by rw [e]; exact hp.dVD)
    (by rw [e]; exact hp.fD)
    ⟨⟨s₀.gpr .x0, rfl, rfl, hp.schedAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ Mode.crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbX.pre s₀) :
    WP isa ofb s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbX.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
    rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncX.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _))
      rw [hv, h2, blocksOf_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecX.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (s₀.gpr .x4).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [hv, h2, blocksOf_eq]

/-! ## Constant time -/

theorem fbTaint_agree (s₁ s₂ : State) (_ : FPre s₁) (_ : FPre s₂) (hp : cbcPub s₁ s₂) :
    VG.AArch64.Taint.AgreeS [s1234Sym] (Taint.ofRegs modePub) s₁ s₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩ := hp
  refine ⟨⟨hsp, fun r hr => ?_⟩, fun n hn => ?_⟩
  · simp only [VG.AArch64.Taint.mem_ofRegs, modePub, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h1, h2, h3, h4, h5, h6]
  · simp only [List.mem_singleton] at hn
    subst hn
    exact hsy

theorem ofb_ct : ConstantTime isa ofbX.pre ofbX.pub ofb :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX.pre cfbEncX.pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX.pre cfbDecX.pub cfbDecrypt :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- OFB's or CFB's contract with the working space as a sixth argument, under
the calling convention with the table (`cfbSig` is `ofbSig`). -/
abbrev fbK (post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 13
    (Spec.Cast5.ofbPre AArch64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def fbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 104⟩]
  syms _ := 0x100000

theorem fb_implies {postX : State → State → Prop} {post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (fbK post).post s s') :
    ({ pre := FPre, post := postX, pub := cbcPub } : Contract isa).Implies (fbK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨fbSat, by
    generalize e : fbSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩, ⟨0x4000, 104⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem ofb_verified : Verified AArch64.target ofb (fbK (Proof.Cast5.ofbPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofb_wp hs) (by lit_decide) (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    ofb_ct (fb_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.ofbPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbEncrypt_verified :
    Verified AArch64.target cfbEncrypt
      (Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 13
        (Spec.Cast5.cfbPre AArch64.abi.ptrBits) (Proof.Cast5.cfbEncPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cfbEncrypt_ct (fb_implies (post := Proof.Cast5.cfbEncPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbEncPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbDecrypt_verified :
    Verified AArch64.target cfbDecrypt
      (Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 13
        (Spec.Cast5.cfbPre AArch64.abi.ptrBits) (Proof.Cast5.cfbDecPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecrypt_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cfbDecrypt_ct (fb_implies (post := Proof.Cast5.cfbDecPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbDecPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 112 bytes of stack. -/
def fbFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem fbFrame_sat (post : Spec.Cast5.ofbSig.Post AArch64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (AArch64.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre AArch64.abi.ptrBits)
      post true (0 + 112)).pre s := by
  refine ⟨fbFrameSat, ?_⟩
  generalize e : fbFrameSat = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 ofb)
      (Spec.Cast5.ofbContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.ofbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    ofb_verified (by decide) (by decide) (by decide) (Proof.Cast5.ofbPostOut_local _) (fbFrame_sat _)

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cfbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (Proof.Cast5.cfbEncPostOut_local _) (fbFrame_sat _)

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cfbPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (Proof.Cast5.cfbDecPostOut_local _) (fbFrame_sat _)

end VG.Proof.Cast5.AArch64
