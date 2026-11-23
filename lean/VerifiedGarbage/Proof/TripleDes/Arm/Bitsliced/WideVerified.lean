module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Wide
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Spec.TripleDes.Cbc
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.TripleDes.Arm.Wide
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Modes.CfbDec
import VerifiedGarbage.Proof.Modes.Fb
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Wide
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.FbScratch
meta import VerifiedGarbage.Spec.TripleDes.Cbc
meta import VerifiedGarbage.Spec.TripleDes.Cfb
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Impl.TripleDes.Arm.Wide
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
meta import VerifiedGarbage.Proof.TripleDes.CbcBlocks
meta import VerifiedGarbage.Proof.Modes.Cbc
meta import VerifiedGarbage.Proof.Modes.Ctr
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Tdea
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Proof.Modes.CfbDec
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# Triple DES-CBC and -CFB64 decryption on ARMv7, a batch at a time, meet their contracts

`cbcDecrypt_framed`, `cfbDecrypt_framed`: the batched functions
(`Impl/TripleDes/Arm/Wide.lean`), proven with their working space of 1024
bytes as a stack argument (`wideC`), with it on the stack, zeroed on return.

Constant time is the taint analysis's: the pointers and the count of blocks
are public, and the working space, whose address is the stack argument, is
a writable region whose public slots keep the pointers and the counters
public through memory.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Impl.TripleDes.Arm.Wide VG.Spec.TripleDes
open VG.Proof.TripleDes.Bitslice (wAt)
open VG.Proof.Modes (blocksOf)

/-! ## The blocks, as the modes' specifications have them -/

theorem cbcPrev_toList (m : Mem) (D I : Addr) (q : Nat) :
    Modes.cbcPrev 8 m D (Spec.Aes.bytesAt m I 8) q = (prevBlock m D I q).toList := by
  unfold Modes.cbcPrev prevBlock
  by_cases h0 : q = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; exact Proof.TripleDes.bytesAt_eq m I
  · rw [ite_eq_right h0, ite_eq_right h0]; exact Proof.TripleDes.bytesAt_eq m _

theorem invCipher_bytes (K : Schedule) (m : Mem) (p : Addr) :
    invCipher K (Spec.Aes.bytesAt m p 8) = (decryptBlock K (blockAt m p)).toList := by
  rw [invCipher, Proof.TripleDes.ofFn_bytesAt]

theorem ofFn_toList (v : Block) : (Vector.ofFn fun i : Fin 8 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi; simp [List.getD_eq_getElem?_getD]

theorem cipher_toList (K : Schedule) (v : Block) : cipher K v.toList = (encryptBlock K v).toList := by
  rw [cipher, ofFn_toList]

/-- The chaining value after the blocks. -/
theorem next_prev (m m' : Mem) (D I : Addr) (N : Nat) (ivo : blockAt m' I = prevBlock m D I N) :
    Spec.Aes.bytesAt m' I 8 = Spec.Cbc.next (Spec.Aes.bytesAt m I 8) (blocksOf 8 m D N) := by
  rw [Proof.TripleDes.bytesAt_eq, ivo, ← cbcPrev_toList]
  unfold Modes.cbcPrev
  by_cases h0 : N = 0
  · subst h0; rfl
  · rw [ite_eq_right h0, Modes.next_blocksOf 8 m D _ h0]

/-- The data and the chaining value after CBC decryption's batches. -/
theorem cbc_spec (K : Schedule) (m m' : Mem) (D I : Addr) (N : Nat)
    (out : ∀ q < N, ∀ r < 8, m' (wAt D q + BitVec.ofNat 64 r) =
      cbcF K (blockAt m (wAt D q)) (prevBlock m D I q) r)
    (ivo : blockAt m' I = prevBlock m D I N) :
    blocksOf 8 m' D N = Spec.Cbc.decrypt (invCipher K) (Spec.Aes.bytesAt m I 8) (blocksOf 8 m D N) ∧
      Spec.Aes.bytesAt m' I 8 = Spec.Cbc.next (Spec.Aes.bytesAt m I 8) (blocksOf 8 m D N) := by
  have hc : ∀ b, (invCipher K b).length = 8 := fun b => by simp [invCipher]
  have hiv : (Spec.Aes.bytesAt m I 8).length = 8 := by simp [Spec.Aes.bytesAt]
  refine ⟨Modes.cbc_of_dinv hc hiv (Modes.dinv_of_blocks (by decide) fun q hq r hr => ?_), next_prev m m' D I N ivo⟩
  rw [ite_eq_left hq, Modes.cbcOut_getD hc m D hiv q hr, ← Offset.add_add, out q hq r hr, cbcPrev_toList,
    invCipher_bytes]
  rfl

/-- The data and the chaining value after CFB decryption's batches. -/
theorem cfb_spec (K : Schedule) (m m' : Mem) (D I : Addr) (N : Nat)
    (out : ∀ q < N, ∀ r < 8, m' (wAt D q + BitVec.ofNat 64 r) =
      cfbF K (blockAt m (wAt D q)) (prevBlock m D I q) r)
    (ivo : blockAt m' I = prevBlock m D I N) :
    blocksOf 8 m' D N = Spec.Cfb.decrypt (cipher K) (Spec.Aes.bytesAt m I 8) (blocksOf 8 m D N) ∧
      Spec.Aes.bytesAt m' I 8 = Spec.Cbc.next (Spec.Aes.bytesAt m I 8) (blocksOf 8 m D N) := by
  have hc : ∀ b, (cipher K b).length = 8 := fun b => by simp [cipher]
  refine ⟨Modes.CfbDec.of_dinv hc (Modes.dinv_of_blocks (by decide) fun q hq r hr => ?_), next_prev m m' D I N ivo⟩
  rw [ite_eq_left hq, Modes.fbOut_getD .cfbDec hc m D _ q hr, Modes.CfbDec.input_eq, ← Offset.add_add,
    out q hq r hr, cbcPrev_toList, cipher_toList]
  unfold cfbF
  rw [bbyte_blockAt m _ hr]
  rfl

/-! ## The contracts as the code sees them -/

/-- The contract of a function on the schedule, the chaining value and the
data, with its working space as a stack argument, as `sig_pre` evaluates it. -/
def wideC (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let iv : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 1024⟩
    let arg : Region := ⟨stackArgAddr s 0, 4⟩
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ s.rd = [key, arg] ∧ s.wr = [iv, data, scr] ∧ key.Disjoint iv ∧
      key.Disjoint data ∧ key.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint arg ∧
      data.Disjoint scr ∧ data.Disjoint arg ∧ scr.Disjoint arg ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 1024 ≤ 2 ^ 32
  post := post
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem wideC_fn {post : State → State → Prop} {s : State} (h : (wideC post).pre s) : WideFn s := by
  obtain ⟨sp, rd, wr, ki, kd, ks, id, is, -, ds, -, -, fk, fi, fd, fs⟩ := h
  exact ⟨sp, rd, wr, ki, kd, ks, id, is, ds, fk, fi, fd, fs⟩

/-- CBC decryption's postcondition. -/
def cbcPost (s s' : State) : Prop :=
  blocksOf 8 s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cbc.decrypt (invCipher (scheduleAt s.mem (State.addr (s.gpr .r0))))
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (blocksOf 8 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ∧
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
      Spec.Cbc.next (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (blocksOf 8 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- CFB decryption's postcondition. -/
def cfbPost (s s' : State) : Prop :=
  blocksOf 8 s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cfb.decrypt (cipher (scheduleAt s.mem (State.addr (s.gpr .r0))))
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (blocksOf 8 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) ∧
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
      Spec.Cbc.next (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (blocksOf 8 s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

theorem cfb_ok (s : State) (hs : (wideC cfbPost).pre s) :
    ∃ t s', Exec isa cfbDecrypt s t s' ∧ abiPreserved s s' ∧ (wideC cfbPost).post s s' := by
  obtain ⟨t, s', he, hp, out, ivo⟩ := wide_wp (fun h => cfbBatch_ok h) (wideC_fn hs)
  exact ⟨t, s', he, ⟨hp, Exec.sp he⟩, cfb_spec _ _ _ _ _ _ out ivo⟩

theorem cbc_ok (s : State) (hs : (wideC cbcPost).pre s) :
    ∃ t s', Exec isa cbcDecrypt s t s' ∧ abiPreserved s s' ∧ (wideC cbcPost).post s s' := by
  obtain ⟨t, s', he, hp, out, ivo⟩ := wide_wp (fun h => cbcBatch_ok h) (wideC_fn hs)
  exact ⟨t, s', he, ⟨hp, Exec.sp he⟩, cbc_spec _ _ _ _ _ _ out ivo⟩

/-! ## Constant time -/

/-- The initial taint: the arguments, and the working space, the third
writable region, whose address is the stack argument. -/
def τW : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [8, 0, 1024], argLen := 4,
    argBases := [(0, 2)] }

theorem τW_wf {post : State → State → Prop} {s : State} (h : (wideC post).pre s) : VG.Arm.Taint.Wf τW s := by
  obtain ⟨hspF, -, hwr, -, -, -, id, is, ia, ds, da, sa, -, fi, fd, fs⟩ := h
  have harg : (⟨stackArgAddr s 0, 4⟩ : Region) = ⟨State.addr s.sp, 4⟩ := by simp [stackArgAddr]
  refine ⟨fun _ => ⟨by simp [hwr, τW], ?_, ?_⟩, fun p hp => by simp [τW] at hp,
    fun _ => ⟨hspF, fun r hr => ?_⟩, fun p hp => ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil]
    exact ⟨⟨id, is⟩, ds, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [State.addr, BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    show (⟨State.addr s.sp, 4⟩ : Region).Disjoint r
    rw [← harg]
    rcases hr with rfl | rfl | rfl
    · exact ia.symm
    · exact da.symm
    · exact sa.symm
  · simp only [τW, List.mem_singleton] at hp; subst hp
    refine ⟨by decide, ?_⟩
    simp [VG.Arm.Taint.region, hwr, stackArg, stackArgAddr]

theorem τW_agree {post : State → State → Prop} (s₁ s₂ : State) (h₁ : (wideC post).pre s₁)
    (h₂ : (wideC post).pre s₂) (hp : (wideC post).pub s₁ s₂) : VG.Arm.Taint.Agree τW s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, pa⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τW_wf h₁, τW_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, ?_⟩
  · simp only [τW, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.2.1, h₂.2.2.1, p1, p2, p3, pa]
  · exact fun k hk => argMem_of (j := 1) psp (by simpa using h₁.1)
      (fun i hi => by obtain rfl : i = 0 := by omega_using [hi]
                      exact pa) k hk

theorem cbc_ct : ConstantTime isa (wideC cbcPost).pre (wideC cbcPost).pub cbcDecrypt :=
  VG.Taint.constantTime (A := VG.Arm.taint) τW τW_agree (by taint_decide)

theorem cfb_ct : ConstantTime isa (wideC cfbPost).pre (wideC cfbPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.Arm.taint) τW τW_agree (by taint_decide)

/-! ## The contracts -/

/-- A state satisfying the precondition with the working space as an
argument: the schedule at `0x1000`, the chaining value at `0x2000`, one
block at `0x3000`, the working space at 0 (the stack argument, which reads 0). -/
def wideSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩, ⟨0, 1024⟩]

/-- A state satisfying the functions' precondition. -/
def wideFrameSat : State := { wideSat with rd := [⟨0x1000, 384⟩], wr := [⟨0x2000, 8⟩, ⟨0x3000, 8⟩] }

theorem cbc_implies : (wideC cbcPost).Implies (Proof.TripleDes.cbcDecChainedScratchContract Arm.abi 128 0) where
  pre s h := by
    sig_pre [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Proof.TripleDes.cbcDecChainedPost, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [Proof.TripleDes.cbcBlocksAt_eq, Proof.TripleDes.cbcBlocksAt_eq]
    change cbcPost s s' at h
    unfold cbcPost at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [wideSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using wideSat

theorem cbcDecrypt_verified :
    Verified Arm.target cbcDecrypt (Proof.TripleDes.cbcDecChainedScratchContract Arm.abi 128 0) :=
  Verified.of_correct cbc_ok cbc_ct cbc_implies

theorem cbcDecryptFrameSat : ∃ s, (Spec.TripleDes.cbcDecryptChainedContract Arm.abi 1040).pre s := by
  implies_sat [Spec.TripleDes.cbcDecryptChainedContract, Spec.TripleDes.cbcChainedSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [wideFrameSat, wideSat] using wideFrameSat

/-- `cbcDecrypt`, with its working space on the stack (zeroed on return). -/
theorem cbcDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1040 0 cbcDecrypt)
      (Spec.TripleDes.cbcDecryptChainedContract Arm.abi 1040) :=
  Arm.Verified.stackScratch (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64) (n := 128)
    (post := Proof.TripleDes.cbcDecChainedPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1040)
    cbcDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cbcDecChainedPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.TripleDes.cbcDecChainedPostOut_local _ vs mm m₁ m₂ r hl) cbcDecryptFrameSat

theorem cfb_implies :
    (wideC cfbPost).Implies (Proof.TripleDes.fbScratchContract Arm.abi 128 Proof.TripleDes.cfbDecPost 0) where
  pre s h := by
    sig_pre [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    rcases h with ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
    rw [Nat.mul_comm] at wr kd id ds da fd
    exact ⟨sp, rd, wr, ki, kd, ks, id, ivs, ia, ds, da, sa, fk, fi, fd, fb⟩
  post s s' _ h := by
    sig_post [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Proof.TripleDes.cfbDecPost,
      Spec.TripleDes.ofbSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [Proof.TripleDes.cbcBlocksAt_eq, Proof.TripleDes.cbcBlocksAt_eq]
    change cfbPost s s' at h
    unfold cfbPost at h
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact h
  sat := by
    sig_implies_sat [Proof.TripleDes.fbScratchContract, Proof.TripleDes.fbScratchSig, Spec.TripleDes.ofbSig,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr]
      [wideSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using wideSat

theorem cfbDecrypt_verified :
    Verified Arm.target cfbDecrypt (Proof.TripleDes.fbScratchContract Arm.abi 128 Proof.TripleDes.cfbDecPost 0) :=
  Verified.of_correct cfb_ok cfb_ct cfb_implies

theorem cfbDecryptFrameSat : ∃ s, (Spec.TripleDes.cfbDecryptContract Arm.abi 1040).pre s := by
  implies_sat [Spec.TripleDes.cfbDecryptContract, Spec.TripleDes.cfbSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [wideFrameSat, wideSat] using wideFrameSat

/-- `cfbDecrypt`, with its working space on the stack (zeroed on return). -/
theorem cfbDecrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 1040 0 cfbDecrypt)
      (Spec.TripleDes.cfbDecryptContract Arm.abi 1040) :=
  Arm.Verified.stackScratch (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64) (n := 128)
    (post := Proof.TripleDes.cfbDecPost Arm.abi.ptrBits) (wa := true) (stack := 0) (m := 0) (bytes := 1040)
    cfbDecrypt_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.TripleDes.cfbDecPost_local _)
    (fun vs mm m₁ m₂ r hl _ => Proof.TripleDes.cfbDecPostOut_local _ vs mm m₁ m₂ r hl) cfbDecryptFrameSat

end VG.Proof.TripleDes.Arm.Bitsliced
