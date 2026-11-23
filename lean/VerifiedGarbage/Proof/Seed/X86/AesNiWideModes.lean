module
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.FbScratch
public import VerifiedGarbage.Proof.Seed.CbcScratch
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideCore
public import VerifiedGarbage.Impl.Seed.X86.AesNiWide
public import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Modes.X86.Seq
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.Cbc
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Seed.FbScratch
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideCore
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWide
meta import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Spec.Seed.Cfb
meta import VerifiedGarbage.Spec.Seed.Cbc
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SEED's wide modes by the AES S-box on x86 (32-bit) meet their contracts

`cbcDecryptChained_wp`, `cfbDecrypt_wp`: CBC decryption and CFB128
decryption by groups of four and two blocks, then one at a time
(`Proof.Modes.X86.cbcDecLevels_wp`, `cfbDecLevels_wp`), over SEED's core
for four blocks (`coreSpec`), with the working space, 89 64-bit words, as a
fifth argument (`fbX86`). The four bytes below `esp`, where the core gets
its table's address, are apart from the schedule as from the other buffers.
Each is constant time by the taint analysis of its code (`X86.sseTaint`);
the `_framed` theorems run them with their working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide.Modes

open VG VG.X86 VG.Impl.Seed.X86.AesNiWide VG.Impl.Modes
open VG.Spec.Seed (Direction)
open VG.Proof.Modes.X86 (SeqPre stkRegion cbcDecLevels_wp cfbDecLevels_wp)
open VG.Proof.Seed.X86.AesNi (KeyArgs)
open VG.Proof.Seed.X86.AesNiWide (coreSpec)

theorem scr_eq (d : Direction) (s : State) : Modes.X86.scrR s (core d) = ⟨(arg s 4).setWidth 64, 8 * 89⟩ := by
  simp [Modes.X86.scrR, core, Impl.Seed.X86.AesNiWide.slots]

/-- The four bytes of stack below `esp` are apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : 4 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (Proof.Modes.X86.stkRegion (s.gpr .esp) 4) ⟨argAddr s 0, 20⟩ ∧
      Region.Disjoint (Proof.Modes.X86.stkRegion (s.gpr .esp) 4) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

/-- SEED under the schedule at the first argument. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher := Spec.Seed.cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 1).setWidth 64) 16
/-- The data. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m ((arg s 2).setWidth 64) (arg s 3).toNat

/-- SEED's inverse under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64))

/-- The functions' postconditions. -/
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- A mode on x86 with its working space as the fifth argument, and
the postcondition `post`. -/
def fbX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 89⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 4
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 89 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 4 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Direction) (hstep : M.step = 16) {s : State}
    (h : (fbX86 post).pre s) : SeqPre (core d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, -, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := (coreSpec d).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [core]), fE, ⟨(by rw [hwr]; simp [core, Impl.Seed.X86.AesNiWide.slots]),
      (by simp only [core, Impl.Seed.X86.AesNiWide.slots]; omega_arith)⟩, (by rw [hwr]; simp [core]),
    (fun _ => by rw [hwr]; simp [core]), (by simp only [core]; omega_arith), (by rw [hwr, hstep]; simp [core]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => dRV), (by rw [hstep]; exact dSD), ?_, sA, sR, (by simp only [core]; omega_arith),
    (by rw [hstep]; simp [core]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [core, Impl.Seed.X86.AesNiWide.slots]; omega_arith))

theorem keyArgs_of {post : State → State → Prop} (d : Direction) {s : State} (h : (fbX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (core d)] (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, dSK, -, -, -, fK, -, -, -, fE, fLo⟩ := h
  obtain ⟨sA, -⟩ := stk_apart fE fLo
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_, dSK, sA.sub_right (Region.sub_prefix (by decide))⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))

theorem core_ka (d : Direction) : (core d).ka = 1 := rfl

theorem data_eq (d : Direction) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (core d).bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s := rfl
theorem iv_eq (d : Direction) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * (core d).bw) = ivAt m s := rfl
theorem cipher_enc (s : State) :
    (coreSpec .encrypt).cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := rfl
theorem cipher_dec (s : State) :
    (coreSpec .decrypt).cipher (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) = invCiph s := rfl

theorem levels_fit (d : Direction) : Proof.Modes.X86.LevelsFit (core d) levels := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact ⟨by decide, by show _ ≤ 4; decide⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 cbcDecPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cbcDecPost).post s₀ s' :=
  WP.mono (cbcDecLevels_wp (coreSpec .decrypt) (levels_fit _) (seqPre_of .decrypt rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_dec] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (coreSpec .encrypt) (levels_fit _) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_enc] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions. -/
def fbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16, 8 * 89], argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)], room := 4 }

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (fbX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, -, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 =
        (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dSD
    · exact dSV
    · exact dSS

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 post).pre s₁)
    (h₂ : (fbX86 post).pre s₂) (hpub : (fbX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith), ha 4 (by omega_arith)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem cbcDecryptChained_ct :
    ConstantTime isa (fbX86 cbcDecPost).pre (fbX86 cbcDecPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 cfbDecPost).pre (fbX86 cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { fbX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 89⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 4
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 89 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 4 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 16⟩, ⟨(arg s 4).setWidth 64, 8 * 89⟩]

tactic_template "seed_aesni_wide_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Seed.X86.AesNiWide.Modes.fbX86, VG.Proof.Seed.X86.AesNiWide.Modes.wideContract,
                     VG.Proof.Seed.X86.AesNiWide.Modes.narrowRd, VG.Proof.Seed.X86.AesNiWide.Modes.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (fbX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  seed_aesni_wide_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 712⟩, ⟨0x8004, 20⟩]
theorem wide_implies_cbcDec :
    (wideContract cbcDecPost).Implies (Proof.Seed.cbcDecChainedScratchContract X86.abi 89 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cbcDecPost] at h
    sig_split h
    sig_reduce [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cbcDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cbcDecPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cbcDecPost]
  · sig_implies_sat [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig, Proof.Seed.cbcDecChainedPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cbcDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract cfbDecPost).Implies (Proof.Seed.fbScratchContract X86.abi 89 Proof.Seed.cfbDecPost 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost]
  · sig_implies_sat [Proof.Seed.fbScratchContract, Proof.Seed.fbScratchSig, Spec.Seed.ofbSig, Proof.Seed.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no blocks at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_fb (post : Spec.Seed.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Seed.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 740)).pre s := by
  implies_sat [Spec.Seed.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_cbc (post : Spec.Seed.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Seed.cbcChainedSig.contract X86.abi (post := post) (writeArgs := true) (stack := 740)).pre s := by
  implies_sat [Spec.Seed.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 post).post s s')
    (hct : ConstantTime isa (fbX86 post).pre (fbX86 post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd narrowWr (wide_pre post) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    exact hR _ _ _ _ _ _ h
  · intro s₁ s₂ _ _ h
    seed_aesni_wide_narrow
    exact h

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract X86.abi 89 4) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h) wide_implies_cbcDec

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.Seed.fbScratchContract X86.abi 89 Proof.Seed.cfbDecPost 4) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 736 4 178 cbcDecryptChained)
      (Spec.Seed.cbcDecryptChainedContract X86.abi 740) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 89) (post := Proof.Seed.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 4)
    (bytes := 736) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cbcDecChainedPost_local _) (Proof.Seed.cbcDecChainedPostOut_local _) (frameSat_cbc _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 736 4 178 cfbDecrypt)
      (Spec.Seed.cfbDecryptContract X86.abi 740) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 89) (post := Proof.Seed.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 4)
    (bytes := 736) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cfbDecPost_local _) (Proof.Seed.cfbDecPostOut_local _) (frameSat_fb _)

end VG.Proof.Seed.X86.AesNiWide.Modes
