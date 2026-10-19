module

public import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
public import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.ModeScratch
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.X86_64.Unchain
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.X86_64.Copy
meta import VerifiedGarbage.Proof.Modes.X86_64.Counter
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Unchain
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# CAST5-OFB and -CFB64 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over CAST5's core (`Mode.dirCoreSpec true`),
with the specification's results (`Proof.Modes.ofb_of`, …), the working
space at `r9`. The core keeps `xmm15`, where the modes keep the IV's address,
its upper half zero (`crypt_keepsIv`): `crypt` puts it back from `rcx`, which
the block code counts down by one (`block_rcx`). The table of
S-boxes is readable where the static `VG_CAST5_S1234` puts it and holds the
S-boxes. `ofb_verified`, …: each is correct and constant time, by the taint
analysis: the pointers, `rounds`, `n`, the stack pointer and the table's
address are public, and so is everything the code computes from them; the
subkeys, the IV and the data are secret. `ofb_framed`, … run them with their
working space on the stack, zeroed on return: 240 bytes, the 29 words of the
scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.X86_64.Mode (dirCoreSpec TabAt dirCore_bw)

/-- The `n` blocks at `p`, as the modes read them. -/
theorem blocksOf_eq (m : Mem) (p : Addr) (n : Nat) :
    VG.Proof.Modes.blocksOf 8 m p n = Spec.Cast5.cbcBlocksAt m p n :=
  (Proof.Cast5.cbcBlocksAt_eq m p n).symm

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

/-- The facts of the feedback modes' precondition on this target, with the
working space at `r9`. -/
structure FPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .rdx, 8⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩, ⟨s.gpr .r9, 232⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTV : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rdx, 8⟩
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .r9, 232⟩
  dKV : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rdx, 8⟩
  dKD : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .rdi, 128⟩ ⟨s.gpr .r9, 232⟩
  dVD : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dVS : Region.Disjoint ⟨s.gpr .rdx, 8⟩ ⟨s.gpr .r9, 232⟩
  dDS : Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩ ⟨s.gpr .r9, 232⟩
  dRV : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 8⟩
  dRD : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩
  dRS : Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 232⟩
  fK : (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .rcx).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .r9).toNat + 232 ≤ 2 ^ 64
  rounds : (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 16

/-- CAST5 encryption under the key of `s`. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Cast5.cipher (keyOf s) (s.gpr .rsi).toNat

def ofbX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .r8).toNat
  pub := cbcPub

def cfbEncX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (dataOf s s.mem))
  pub := cbcPub

def cfbDecX : Contract isa where
  pre := FPre
  post s s' := dataOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (dataOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Cbc.next (ivOf s) (dataOf s s.mem)
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

/-! ## `xmm15` -/

theorem execBlock_app_inv {a b : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa (a ++ b) s = some (s', t)) :
    ∃ u ta tb, execBlock isa a s = some (u, ta) ∧ execBlock isa b u = some (s', tb) := by
  rw [execBlock_append] at h
  obtain ⟨⟨u, ta⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v, tb⟩, h₃, h₄⟩ := Option.map_eq_some_iff.mp h₂
  simp only [Prod.mk.injEq] at h₄
  exact ⟨u, ta, tb, h₁, h₄.1 ▸ h₃⟩

theorem noClobber {c : Prog isa} {r : Reg} (h : c.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi
  simpa using h i hi

/-- `store` counts `rcx` down by one. -/
theorem store_rcx {s s' : State} {t : List Leak} (h : execBlock isa store s = some (s', t)) :
    s'.gpr .rcx = s.gpr .rcx - 1 := by
  obtain ⟨u, _, _, h₁, h₂⟩ := execBlock_app_inv (a := [.bswap32 .rbp, .store32 (at_ .rdx 0) .rbp, .bswap32 .rbx,
    .store32 (at_ .rdx 4) .rbx, .alu .add .rdx (imm 8)]) (b := [.alu .sub .rcx (imm 1)]) h
  rw [← execBlock_gpr (r := .rcx) (by decide) h₁]
  simp only [execBlock, isa, exec, execAlu, readSrc, imm, Option.bind_some, Option.map_some, Option.some.injEq,
    Prod.mk.injEq] at h₂
  rw [← h₂.1, RegUpd.gpr_setReg_self]
  rfl

/-- The block code counts `rcx` down by one. -/
theorem block_rcx (up : Bool) {s s' : State} {t : List Leak}
    (h : Exec isa (if up then encryptBlock else decryptBlock) s t s') : s'.gpr .rcx = s.gpr .rcx - 1 := by
  cases up
  · change Exec isa decryptBlock s t s' at h
    unfold decryptBlock at h
    cases h with
    | seq e₁ e₂ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | seq e₅ e₆ => cases e₆ with
          | block b =>
            rw [store_rcx b, Exec.gpr (noClobber (by decide +kernel)) e₅, Exec.gpr (noClobber (by decide +kernel)) e₃,
              Exec.gpr (noClobber (by decide +kernel)) e₁]
  · change Exec isa encryptBlock s t s' at h
    unfold encryptBlock at h
    cases h with
    | seq e₁ e₂ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | seq e₅ e₆ => cases e₆ with
          | seq e₇ e₈ => cases e₈ with
            | block b =>
              rw [store_rcx b, Exec.gpr (noClobber (by decide +kernel)) e₇,
                Exec.gpr (noClobber (by decide +kernel)) e₅, Exec.gpr (noClobber (by decide +kernel)) e₃,
                Exec.gpr (noClobber (by decide +kernel)) e₁]

/-- `movq xmm, r64` of a register's low half puts back one whose upper half is zero. -/
theorem movq_lo {v : BitVec 128} (h : v.extractLsb' 64 64 = 0) : (0 : BitVec 64) ++ v.extractLsb' 0 64 = v := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h64 : i < 64
  · simp [h64, hi]
  · simp only [h64, decide_false, Bool.false_and, ite_false]
    simp only [Bool.true_and, show i - 64 < 64 by omega, decide_true]
    congr 1; omega

/-- `crypt` keeps `xmm15`, its upper half zero, which it puts back from `rcx`. -/
theorem crypt_keepsIv : Modes.X86_64.KeepsIv (dirCore true).crypt := by
  intro s t s' h hz
  change Exec isa (cryptCode true) s t s' at h
  cases h with
  | seq e₁ e₂ => cases e₁ with
    | block b₁ => cases e₂ with
      | seq e₃ e₄ => cases e₄ with
        | block b₄ =>
          obtain ⟨u, _, _, h₁, h₂⟩ := execBlock_app_inv b₁
          obtain ⟨w, _, _, h₃, h₄⟩ := execBlock_app_inv b₄
          simp only [saveIv, execBlock, isa, exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
          have k₁ := execBlock_gpr (r := .rcx) (by decide) h₂
          have k₃ := execBlock_gpr (r := .rcx) (by decide) h₃
          have k₂ := block_rcx true e₃
          simp only [restoreIv, execBlock, isa, exec, execAlu, readSrc, imm, Option.bind_some, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at h₄
          have hw : w.gpr .rcx + BitVec.signExtend 64 (1#32) = (s.xmm .xmm15).extractLsb' 0 64 := by
            rw [k₃, k₂, k₁, ← h₁.1, RegUpd.gpr_setReg_self, show BitVec.signExtend 64 (1#32) = (1 : BitVec 64) from rfl,
              BitVec.sub_add_cancel]
          rw [← h₄.1]
          simp only [XOp.exec, RegUpd.gpr_setReg_self]
          rw [hw]
          exact movq_lo hz

/-- `crypt` and `prepare` keep `xmm15`. -/
theorem keepsIv_core : Modes.X86_64.KeepsIv (dirCore true).prepare ∧ Modes.X86_64.KeepsIv (dirCore true).crypt :=
  ⟨Modes.X86_64.keepsIv_of_ivSafe (by decide), crypt_keepsIv⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre s₀) :
    WP isa ((dirCore true).fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat =
        (List.range (s₀.gpr .r8).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 8 =
        Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat := by
  have hwS : (⟨s₀.gpr .r9, 8 * 29⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  have e : 8 * (dirCore true).bw * (s₀.gpr .r8).toNat = (s₀.gpr .r8).toNat * 8 := by
    rw [dirCore_bw, Nat.mul_one, Nat.mul_comm]
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := (keyOf s₀, (s₀.gpr .rsi).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [e, hp.wr]; simp) hp.dVS (by rw [e]; exact hp.dDS) (by rw [e]; exact hp.dVD)
    (by rw [e]; exact hp.fD)
    ⟨⟨s₀.gpr .rdi, rfl, rfl, by rw [hp.rd]; simp, hp.fK, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ keepsIv_core)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.dRS
  · rw [e]; exact hp.dRD
  · exact hp.dRV

theorem ofb_wp {s₀ : State} (hp : ofbX.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
    rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _))
      rw [hv, h2, blocksOf_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (s₀.gpr .r8).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Cast5.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [← blocksOf_eq, ← blocksOf_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cast5.cbcBlocksAt _ _ _)
      rw [hv, h2, blocksOf_eq]

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], flags := false,
    lens := [8, 0, 8 * 29], bases := [(.r9, 2, 0)] }

theorem fbTaint_wf (s : State) (hs : FPre s) : Taint.Wf fbTaint s := by
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hs.wr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega) (List.Forall₂.cons
        (by change 0 ≤ (s.gpr .r8).toNat * 8; omega)
        (List.Forall₂.cons (by change 8 * 29 ≤ 232; omega) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.dVD
        · exact hs.dVS
      · obtain rfl := List.mem_singleton.mp hr; exact hs.dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 8 ≤ 2 ^ 64; omega
      · change (s.gpr .r8).toNat * 8 ≤ 2 ^ 64
        have := hs.fD; omega
      · change 232 ≤ 2 ^ 64; omega
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hs.wr]
    change s.gpr .r9 = s.gpr .r9 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree (s t : State) (hs : FPre s) (ht : FPre t) (hp : cbcPub s t) :
    X86_64.Taint.AgreeS [s1234Sym] fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  refine ⟨⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩, fun n hn => ?_⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6, p7]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.wr, ht.wr, p3, p4, p5, p6]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr
  · simp only [List.mem_singleton] at hn
    subst hn
    exact p8

theorem ofb_ct : ConstantTime isa ofbX.pre ofbX.pub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint fbTaint_agree (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa cfbEncX.pre cfbEncX.pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint fbTaint_agree (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa cfbDecX.pre cfbDecX.pub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint fbTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- OFB's or CFB's contract with the working space as a sixth argument, under
the calling convention with the table (`cfbSig` is `ofbSig`). -/
abbrev fbK (post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.ofbSig 29
    (Spec.Cast5.ofbPre X86_64.abi.ptrBits) post

/-- A state satisfying the precondition: one block, 16 rounds. -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0x4000, 232⟩]
  syms _ := 0x100000

theorem fb_implies {postX : State → State → Prop} {post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (fbK post).post s s') :
    ({ pre := FPre, post := postX, pub := cbcPub } : Contract isa).Implies (fbK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, -, spV, spD, spS, fK, -, fD, fS,
      hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, spV, spD, spS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, X86_64.abi,
      X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨fbSat, by
    generalize e : fbSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
      Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 8⟩, ⟨0x4000, 232⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem ofb_verified : Verified X86_64.target ofb (fbK (Proof.Cast5.ofbPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    ofb_ct (fb_implies fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.ofbPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt
      (Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 29
        (Spec.Cast5.cfbPre X86_64.abi.ptrBits) (Proof.Cast5.cfbEncPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    cfbEncrypt_ct (fb_implies (post := Proof.Cast5.cfbEncPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbEncPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt
      (Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cfbSig 29
        (Spec.Cast5.cfbPre X86_64.abi.ptrBits) (Proof.Cast5.cfbDecPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    cfbDecrypt_ct (fb_implies (post := Proof.Cast5.cfbDecPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig,
        Proof.Cast5.cfbDecPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 240 bytes of stack. -/
def fbFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩]
  syms _ := 0x100000

theorem fbFrame_sat (post : Spec.Cast5.ofbSig.Post X86_64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (X86_64.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre X86_64.abi.ptrBits) post
      true (0 + 240)).pre s := by
  refine ⟨fbFrameSat, ?_⟩
  generalize e : fbFrameSat = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts,
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
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 ofb)
      (Spec.Cast5.ofbContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.ofbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    ofb_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.ofbPostOut_local _) (fbFrame_sat _)

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbEncrypt_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbEncPostOut_local _) (fbFrame_sat _)

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbDecPostOut_local _) (fbFrame_sat _)

end VG.Proof.Cast5.X86_64
