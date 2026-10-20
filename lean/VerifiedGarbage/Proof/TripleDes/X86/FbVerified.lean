module

public import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Proof.TripleDes.X86.ModeCore
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Modes.X86.Seq
import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
public import VerifiedGarbage.Impl.TripleDes.X86.Fb
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Proof.TripleDes.X86.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.TripleDes.X86.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86.FbLit
meta import VerifiedGarbage.Impl.TripleDes.X86.Fb

/-!
# Triple DES-OFB, -CFB64 and -CFB8 on x86 (32-bit) meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, … : the modes' OFB, CFB and CFB8
(`Proof.Modes.X86.ofb_wp`, …) over Triple DES's core in the encryption
direction (`Mode.dirCoreSpec .encrypt`), with the working space as a fifth
argument (`fbX86`, whose data is `st` bytes a step: 8, or 1 for CFB8). The
chaining value is written back, so it is writable, and the taint analysis
knows the argument words holding the addresses of the data, the chaining
value and the scratch buffer as the base addresses of the writable regions,
with room for the block function's call below `esp`. The `_framed` theorems
run them with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Cbc

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (stkRegion)
open VG.Proof.TripleDes (bytesAt_eq)

theorem scr_eq (s : State) (d : Spec.TripleDes.Direction) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 4).setWidth 64, 8 * 118⟩ := by
  simp [Modes.X86.scrR, dirCore, schedSlot]

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-- The stack below `esp` is apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : 16 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨argAddr s 0, 20⟩ ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 16) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

end VG.Proof.TripleDes.X86.Cbc

namespace VG.Proof.TripleDes.X86.Fb

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion ofb_wp cfbEnc_wp cfbDec_wp cfb8Enc_wp cfb8Dec_wp)
open VG.Proof.TripleDes.X86.Mode (dirCoreSpec KeyArgs)
open VG.Proof.TripleDes.X86.Cbc (scr_eq stk_apart cbcBlocksAt_eq)

/-- Triple DES under the schedule at the first argument. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64))
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m ((arg s 1).setWidth 64) 8
/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.TripleDes.cbcBlocksAt m ((arg s 2).setWidth 64) (arg s 3).toNat
/-- The data, in bytes. -/
abbrev bytesOf (m : Mem) (s : State) : List Byte := Spec.TripleDes.bytesAt m ((arg s 2).setWidth 64) (arg s 3).toNat

/-- The functions' postconditions. -/
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 3).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def cfb8EncPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (Spec.Cfb8.encrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s))
def cfb8DecPost (s s' : State) : Prop :=
  bytesOf s'.mem s = Spec.Cfb8.decrypt (ciph s) (ivAt s.mem s) (bytesOf s.mem s) ∧
    ivAt s'.mem s = Spec.Cfb8.next (ivAt s.mem s) (bytesOf s.mem s)

/-- OFB, CFB64 or CFB8 on x86 with its working space as the fifth argument,
`st` bytes of data a step, and the postcondition `post`. -/
def fbX86 (st : Nat) (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 118⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [data, iv, scratch] ∧
    key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + st * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 118 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {st : Nat} {post : State → State → Prop} {M : Mode} (d : Spec.TripleDes.Direction)
    (hstep : M.step = st) (hst : 0 < st) (hst8 : st ≤ 8) {s : State} (h : (fbX86 st post).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := (dirCoreSpec d).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, schedSlot]),
      (by simp only [dirCore, schedSlot]; omega)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => dRV), (by rw [hstep]; exact dSD), ?_, sA, sR, (by simp [dirCore]; omega),
    (by rw [hstep]; simp only [dirCore]; omega), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega))

theorem keyArgs_of {st : Nat} {post : State → State → Prop} (d : Spec.TripleDes.Direction) {s : State}
    (h : (fbX86 st post).pre s) : KeyArgs s [Modes.X86.scrR s (dirCore d)]
      (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, -, -, dSS, fK, -, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dSS

theorem dirCore_ka (d : Spec.TripleDes.Direction) : (dirCore d).ka = 1 := rfl

theorem data_eq (d : Spec.TripleDes.Direction) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (dirCore d).bw) m ((arg s 2).setWidth 64) (arg s 3).toNat = dataAt m s :=
  (cbcBlocksAt_eq _ _ _).symm
theorem iv_eq (d : Spec.TripleDes.Direction) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 1).setWidth 64) (4 * (dirCore d).bw) = ivAt m s := rfl
theorem bytes_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) (arg s 3).toNat = bytesOf m s := rfl
theorem cipher_eq (s : State) :
    (dirCoreSpec .encrypt).cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) = ciph s := rfl

tactic_template "tdes_post_eq" h:ident h':ident : tactic =>
  `(tactic| simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.bytes0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp,
                     Proof.Modes.X86.P, Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, bytes_eq, cipher_eq]
                     at $h:ident $h':ident)

theorem ofb_wp_x86 {s₀ : State} (hp : (fbX86 8 ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 8 ofbPost).post s₀ s' :=
  WP.mono (ofb_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 8 cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 8 cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 8 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 8 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDec_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfb8Encrypt_wp {s₀ : State} (hp : (fbX86 1 cfb8EncPost).pre s₀) :
    WP isa cfb8Encrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 1 cfb8EncPost).post s₀ s' :=
  WP.mono (cfb8Enc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

theorem cfb8Decrypt_wp {s₀ : State} (hp : (fbX86 1 cfb8DecPost).pre s₀) :
    WP isa cfb8Decrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 1 cfb8DecPost).post s₀ s' :=
  WP.mono (cfb8Dec_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl (by decide) (by decide) hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by tdes_post_eq h2 h3; exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions, and room
for the block function's call below `esp`. -/
def fbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8, 8 * 118], argLen := 24,
    argBases := [(12, 0), (8, 1), (20, 2)], room := 16 }

theorem fbTaint_wf {st : Nat} {post : State → State → Prop} {s : State} (hp : (fbX86 st post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dSD
    · exact dSV
    · exact dSS

theorem fbTaint_agree {st : Nat} {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 st post).pre s₁)
    (h₂ : (fbX86 st post).pre s₂) (hpub : (fbX86 st post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ofb_ct : ConstantTime isa (fbX86 8 ofbPost).pre (fbX86 8 ofbPost).pub ofb := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint ofb h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 8 cfbEncPost).pre (fbX86 8 cfbEncPost).pub cfbEncrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfbEncrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 8 cfbDecPost).pre (fbX86 8 cfbDecPost).pub cfbDecrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfbDecrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfb8Encrypt_ct : ConstantTime isa (fbX86 1 cfb8EncPost).pre (fbX86 1 cfb8EncPost).pub cfb8Encrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfb8Encrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfb8Decrypt_ct : ConstantTime isa (fbX86 1 cfb8DecPost).pre (fbX86 1 cfb8DecPost).pub cfb8Decrypt := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.taint.check fbTaint cfb8Decrypt h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (st : Nat) (post : State → State → Prop) : Contract isa :=
  { fbX86 st post with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
      let data : Region := ⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 118⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 16
      s.rd = [key] ∧ s.wr = [iv, data, scratch, args] ∧
      key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + st * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 118 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 384⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (st : Nat) (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, st * (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 8 * 118⟩]

tactic_template "tdes_fb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Fb.fbX86, VG.Proof.TripleDes.X86.Fb.wideContract,
                     VG.Proof.TripleDes.X86.Fb.narrowRd, VG.Proof.TripleDes.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (st : Nat) (post : State → State → Prop) (s : State) (h : (wideContract st post).pre s) :
    (fbX86 st post).pre (s.withRegions (narrowRd s) (narrowWr st s)) := by
  obtain ⟨_, _, h⟩ := h
  tdes_fb_narrow
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
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 944⟩, ⟨0x8004, 20⟩]

theorem wide_implies_ofb :
    (wideContract 8 ofbPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.ofbPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, ofbPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.ofbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbEnc :
    (wideContract 8 cfbEncPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbEncPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbEncPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract 8 cfbDecPost).Implies (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbDecPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; try simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfbDecPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Proof.TripleDes.cfbDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfb8Enc :
    (wideContract 1 cfb8EncPost).Implies (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8EncPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfb8EncPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8EncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfb8Dec :
    (wideContract 1 cfb8DecPost).Implies (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8DecPost 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.one_mul] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; simp only [Nat.one_mul] at *; with_reducible assumption)
  · sig_implies_post [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below, cfb8DecPost, ciph, ivAt, dataAt, bytesOf]
  · sig_implies_pub [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
  · sig_implies_sat [Proof.TripleDes.cfb8ScratchContract, Proof.TripleDes.cfb8ScratchSig, Spec.TripleDes.cfb8Sig, Proof.TripleDes.cfb8DecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
the chaining value at `0x2000`, and no data at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_pre (post : Spec.TripleDes.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbSig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.ofbSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_pre8 (post : Spec.TripleDes.cfb8Sig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfb8Sig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.cfb8Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {st : Nat} {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 st post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 st post).post s s')
    (hct : ConstantTime isa (fbX86 st post).pre (fbX86 st post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract st post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 st post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre st post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd (narrowWr st) (wide_pre st post) ?_ ?_ ?_ ?_ hsat
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
    tdes_fb_narrow
    exact h

theorem ofb_verified :
    Verified X86.target ofb (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.ofbPost 16) :=
  fb_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb
theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbEncPost 16) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc
theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.TripleDes.fbScratchContract X86.abi 118 Proof.TripleDes.cfbDecPost 16) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec
theorem cfb8Encrypt_verified :
    Verified X86.target cfb8Encrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8EncPost 16) :=
  fb_verified (fun _ hs => cfb8Encrypt_wp hs) cfb8Encrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Enc
theorem cfb8Decrypt_verified :
    Verified X86.target cfb8Decrypt (Proof.TripleDes.cfb8ScratchContract X86.abi 118 Proof.TripleDes.cfb8DecPost 16) :=
  fb_verified (fun _ hs => cfb8Decrypt_wp hs) cfb8Decrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfb8Dec

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 ofb)
      (Spec.TripleDes.ofbContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.ofbPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ofbPost_local _) (Proof.TripleDes.ofbPostOut_local _) (frameSat_pre _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfbEncrypt)
      (Spec.TripleDes.cfbEncryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbEncPost_local _) (Proof.TripleDes.cfbEncPostOut_local _) (frameSat_pre _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfbDecrypt)
      (Spec.TripleDes.cfbDecryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbDecPost_local _) (Proof.TripleDes.cfbDecPostOut_local _) (frameSat_pre _)

/-- `cfb8Encrypt` with its working space on the stack. -/
theorem cfb8Encrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfb8Encrypt)
      (Spec.TripleDes.cfb8EncryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8EncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfb8Encrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8EncPost_local _) (Proof.TripleDes.cfb8EncPostOut_local _) (frameSat_pre8 _)

/-- `cfb8Decrypt` with its working space on the stack. -/
theorem cfb8Decrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cfb8Decrypt)
      (Spec.TripleDes.cfb8DecryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cfb8DecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cfb8Decrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8DecPost_local _) (Proof.TripleDes.cfb8DecPostOut_local _) (frameSat_pre8 _)

end VG.Proof.TripleDes.X86.Fb
