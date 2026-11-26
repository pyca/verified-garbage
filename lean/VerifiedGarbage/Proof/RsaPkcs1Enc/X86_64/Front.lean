module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Front
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecHash
import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.RsaOaep.X86_64.DecSpec
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecPrecomputed
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Front
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.Framework.ForallLength

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on x86-64

`Front.code` (`Impl/RsaPkcs1Enc/X86_64/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedContract` with 3784 bytes of stack
(`front_verified`), for any callee verified against
`Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract` with 3480: its proof is used
only through that contract.

**The call.** As `forward` does (`Proof/Framework/X86_64/ForwardCall.lean`),
`setup` copies the stack arguments to the bottom of the frame and leaves the
argument registers as they came; it also stores `out`, `k` and `msg_len` in
slots above the copies (`Z`), so the callee starts from `narrowF`'s state
with other bytes there (`withMem`). Its contract does not read them: the
precondition and the public data read memory only within the buffers and the
copies (`pre_like`, `pub_of`, from `preP_local` and `leakP_local`), and the
postcondition reads the memory on entry only within the buffers
(`postP_local`), so it is the callee's contract of our arguments (`call_ok`,
`Called`, `CPost`).

**After the call.** In RSAES-OAEP's frame and layout of `scratch` (`Lay`,
`Rep`, `Proof/RsaOaep/X86_64/`), each piece run with its permissions narrowed
to the frame and our 8192 bytes of `scratch` (`nar`), so that `out` and
`msg_len` stay as the call left them until `copyOut`: the buffer's first
`2 k` bytes (`clrN`) cleared, `out` copied to it, its first `k` bytes shifted
by `k - L` in a pass for each bit of `k` (`shift_ok`: pass `p` runs while
`2^p ≤ k`, and reads the zeros after the `k` bytes, `bufK`), which leaves
the message and zeros (`shift_val`), and copied back (`St0` … `St4`,
`tail_ok`).

**Constant time.** Two runs related by the contract's public data (`Rel`):
the blocks by the taint analysis, from `rsp` (`rel_rsp`) or from the frame
and the slots of `out`, `k`, `msg_len` and `scratch` (`rel_frT`), the call by
the callee's constant time (`front_ct`).
-/

-- separate module: the function's proofs, which build alongside `Scrub.lean`'s evaluation of decryption's code that `FrontScrub.lean` needs

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Front

open VG VG.X86_64

/-! ## The contract's parts -/

abbrev sig : Sig := Proof.RsaPkcs1Enc.decryptPrecomputedBodySig

/-- `Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract`'s precondition. -/
def preP : Curry (sig.words abi.ptrBits) (Mem → Prop) :=
  fun _out outLen _msgLen n nLen _e eLen _d dLen _input inputLen p pLen q qLen _dp
      dpLen _dq dqLen _qinv qinvLen _scratch scratchLen pre preLen m =>
    Spec.Rsa.lenValid nLen.toNat ∧ outLen.toNat = nLen.toNat ∧ inputLen.toNat = nLen.toNat ∧
      1 ≤ eLen.toNat ∧ eLen.toNat ≤ nLen.toNat ∧ 1 ≤ dLen.toNat ∧ dLen.toNat ≤ nLen.toNat ∧
      1 ≤ pLen.toNat ∧ pLen.toNat < nLen.toNat ∧ 1 ≤ qLen.toNat ∧ qLen.toNat < nLen.toNat ∧
      dpLen.toNat = pLen.toNat ∧ qinvLen.toNat = pLen.toNat ∧ dqLen.toNat = qLen.toNat ∧
      Spec.Rsa.scratchWords nLen.toNat ≤ scratchLen.toNat ∧
      preLen.toNat = Spec.Rsa.privatePrecomputedWords nLen.toNat pLen.toNat qLen.toNat ∧
      Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m n nLen.toNat) (Spec.Rsa.bytesAt m p pLen.toNat)
        (Spec.Rsa.bytesAt m q qLen.toNat) = some (Spec.Rsa.wordsAt m pre preLen.toNat)

/-- Its postcondition. -/
def postP : sig.Post abi.ptrBits :=
  fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
      dq _dqLen qinv _qinvLen _scratch _scratchLen _pre _preLen m m' r =>
    Proof.RsaPkcs1Enc.writtenMsgEnd m' out msgLen nLen.toNat r
      (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt m n nLen.toNat) (Spec.Rsa.bytesAt m e eLen.toNat)
        (Spec.Rsa.bytesAt m d dLen.toNat) (Spec.Rsa.bytesAt m p pLen.toNat) (Spec.Rsa.bytesAt m q qLen.toNat)
        (Spec.Rsa.bytesAt m dp pLen.toNat) (Spec.Rsa.bytesAt m dq qLen.toNat)
        (Spec.Rsa.bytesAt m qinv pLen.toNat) (Spec.Rsa.bytesAt m input nLen.toNat))

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedContract`'s postcondition. -/
def postFP : sig.Post abi.ptrBits :=
  fun out _outLen msgLen n nLen e eLen d dLen input _inputLen p pLen q qLen dp _dpLen
      dq _dqLen qinv _qinvLen _scratch _scratchLen _pre _preLen m m' r =>
    Spec.RsaPkcs1Enc.writtenMsg m' out msgLen nLen.toNat r
      (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt m n nLen.toNat) (Spec.Rsa.bytesAt m e eLen.toNat)
        (Spec.Rsa.bytesAt m d dLen.toNat) (Spec.Rsa.bytesAt m p pLen.toNat) (Spec.Rsa.bytesAt m q qLen.toNat)
        (Spec.Rsa.bytesAt m dp pLen.toNat) (Spec.Rsa.bytesAt m dq qLen.toNat)
        (Spec.Rsa.bytesAt m qinv pLen.toNat) (Spec.Rsa.bytesAt m input nLen.toNat))

/-- What both may leak. -/
def leakP : Curry (sig.words abi.ptrBits) (Mem → List Nat) :=
  fun _out _outLen _msgLen n nLen e eLen _d _dLen _input _inputLen _p _pLen _q
      _qLen _dp _dpLen _dq _dqLen _qinv _qinvLen _scratch _scratchLen pre _preLen m =>
    (Spec.Rsa.bytesAt m n nLen.toNat ++ Spec.Rsa.bytesAt m e eLen.toNat).map (·.toNat) ++
      Spec.Rsa.privatePrecomputedLeak m pre nLen.toNat

theorem cK_eq (n : Nat) : Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract abi n =
    sig.contract abi preP postP true n (some leakP) := rfl

theorem fK_eq (n : Nat) : Spec.RsaPkcs1Enc.decryptPrecomputedContract abi n =
    sig.contract abi preP postFP true n (some leakP) := rfl

theorem hk : 6 ≤ (sig.words abi.ptrBits).length := by decide
theorem hnl : Sig.noLists sig.params = true := by decide
theorem nStack_eq : nStack sig = 19 := by decide

/-! ## Locality -/

theorem bytes_ag {m₁ m₂ : Mem} {p : Addr} {L k : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hk : k ≤ L) : Spec.Rsa.bytesAt m₂ p k = Spec.Rsa.bytesAt m₁ p k := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left fun i hi => (h _ ?_).symm
  have := List.mem_range.mp hi
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le i (2 ^ 64)
  omega_arith

theorem words_ag {m₁ m₂ : Mem} {p : Addr} {L k : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    (hk : 8 * k ≤ L) : Spec.Rsa.wordsAt m₂ p k = Spec.Rsa.wordsAt m₁ p k := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => Mem.readW_congr fun j hj => (h _ ?_).symm
  have := List.mem_range.mp hi
  simp only [Region.Contains]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  have := Nat.mod_le (8 * i + j) (2 ^ 64)
  omega_arith

theorem toNat_ptr (x : BitVec 64) : @BitVec.toNat abi.ptrBits x = x.toNat := rfl

theorem len25 : (sig.words abi.ptrBits).length = 25 := by decide

/-- The 25 argument words. -/
theorem vs25 {vs : List (BitVec 64)} (h : vs.length = (sig.words abi.ptrBits).length) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 : BitVec 64,
      vs = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
        a22, a23, a24] := by
  rw [len25] at h
  revert vs; refine @(forall_length (n := 25) ?_)
  intro a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23,
    a24, rfl⟩

/-- `preP` reads memory only in `n`, `p`, `q` and `pre`. -/
theorem preP_local : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
    (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists abi.ptrBits m₁ sig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sig.words abi.ptrBits) preP vs m₁ → Curry.apply (sig.words abi.ptrBits) preP vs m₂ := by
  intro vs m₁ m₂ hl hb _ h
  obtain ⟨o, oL, ml, n, nL, e, eL, d, dL, i, iL, p, pL, q, qL, dp, dpL, dq, dqL, qi, qiL, sc, scL, pre, preL, rfl⟩ :=
    vs25 hl
  simp only [sig, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig, Proof.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
    Nat.mul_one] at hb
  obtain ⟨-, -, bn, -, -, -, bp, bq, -, -, -, -, bpre⟩ := hb
  replace h : preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₁ := h
  show preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₂
  simp only [preP, toNat_ptr] at h ⊢
  rw [bytes_ag (k := nL.toNat) bn (by omega_arith), bytes_ag (k := pL.toNat) bp (by omega_arith),
    bytes_ag (k := qL.toNat) bq (by omega_arith), words_ag (k := preL.toNat) bpre (by omega_arith)]
  exact h

/-- Under `preP`, `postP` reads the memory on entry only in the buffers. -/
theorem postP_local {vs : List (BitVec 64)} {m₁ m₂ m' : Mem} {r : BitVec 32}
    (hl : vs.length = (sig.words abi.ptrBits).length)
    (hp : Curry.apply (sig.words abi.ptrBits) preP vs m₁)
    (hb : ∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a)
    (h : Curry.apply (sig.words abi.ptrBits) postP vs m₁ m' r) :
    Curry.apply (sig.words abi.ptrBits) postP vs m₂ m' r := by
  obtain ⟨o, oL, ml, n, nL, e, eL, d, dL, i, iL, p, pL, q, qL, dp, dpL, dq, dqL, qi, qiL, sc, scL, pre, preL, rfl⟩ :=
    vs25 hl
  simp only [sig, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig, Proof.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
    Nat.mul_one] at hb
  obtain ⟨-, -, bn, be, bd, bi, bp, bq, bdp, bdq, bqi, -, -⟩ := hb
  replace hp : preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₁ := hp
  simp only [preP, toNat_ptr] at hp
  obtain ⟨-, -, hiL, -, -, -, -, -, -, -, -, hdpL, hqiL, hdqL, -⟩ := hp
  replace h : postP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₁ m' r := h
  show postP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₂ m' r
  simp only [postP, toNat_ptr] at h ⊢
  rw [bytes_ag (k := nL.toNat) bn (by omega_arith), bytes_ag (k := eL.toNat) be (by omega_arith),
    bytes_ag (k := dL.toNat) bd (by omega_arith), bytes_ag (k := pL.toNat) bp (by omega_arith),
    bytes_ag (k := qL.toNat) bq (by omega_arith), bytes_ag (k := pL.toNat) bdp (by omega_arith),
    bytes_ag (k := qL.toNat) bdq (by omega_arith), bytes_ag (k := pL.toNat) bqi (by omega_arith),
    bytes_ag (k := nL.toNat) bi (by omega_arith)]
  exact h

/-- Under `preP`, `leakP` reads memory only in the buffers. -/
theorem leakP_local {vs : List (BitVec 64)} {m₁ m₂ : Mem} (hl : vs.length = (sig.words abi.ptrBits).length)
    (hp : Curry.apply (sig.words abi.ptrBits) preP vs m₁)
    (hb : ∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) :
    Curry.apply (sig.words abi.ptrBits) leakP vs m₁ = Curry.apply (sig.words abi.ptrBits) leakP vs m₂ := by
  obtain ⟨o, oL, ml, n, nL, e, eL, d, dL, i, iL, p, pL, q, qL, dp, dpL, dq, dqL, qi, qiL, sc, scL, pre, preL, rfl⟩ :=
    vs25 hl
  simp only [sig, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig, Proof.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
    Nat.mul_one] at hb
  obtain ⟨-, -, bn, be, -, -, -, -, -, -, -, -, bpre⟩ := hb
  replace hp : preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₁ := hp
  simp only [preP, toNat_ptr] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpl, -⟩ := hp
  show leakP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₁ =
    leakP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m₂
  simp only [leakP, Spec.Rsa.privatePrecomputedLeak, toNat_ptr]
  rw [bytes_ag (k := nL.toNat) bn (by omega_arith), bytes_ag (k := eL.toNat) be (by omega_arith),
    words_ag (k := Spec.Rsa.precomputedWords nL.toNat) bpre
      (by rw [hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega_arith)]

/-! ## Other bytes outside the buffers and the stack arguments -/

/-- The contracts, with any postcondition `Q`. -/
abbrev C (Q : sig.Post abi.ptrBits) (n : Nat) : Contract isa := sig.contract abi preP Q true n (some leakP)

/-- `y` with the memory `m`. -/
def withMem (y : State) (m : Mem) : State := { y with mem := m }

@[simp] theorem withMem_gpr (y : State) (m : Mem) : (withMem y m).gpr = y.gpr := rfl
@[simp] theorem withMem_mem (y : State) (m : Mem) : (withMem y m).mem = m := rfl
@[simp] theorem withMem_rd (y : State) (m : Mem) : (withMem y m).rd = y.rd := rfl
@[simp] theorem withMem_wr (y : State) (m : Mem) : (withMem y m).wr = y.wr := rfl
@[simp] theorem withMem_mxcsr (y : State) (m : Mem) : (withMem y m).mxcsr = y.mxcsr := rfl
@[simp] theorem withMem_unknowns (y : State) (m : Mem) : (withMem y m).unknowns = y.unknowns := rfl

theorem argArea_mem (y : State) : (⟨stackArgAddr y 0, 8 * nStack sig⟩, false) ∈ allRegions sig y := by
  simp only [allRegions, argArea, len25]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem bufs_sub {y : State} {b : Region × Bool} (hb : b ∈ Sig.bufs sig.params (allArgs sig y)) :
    b ∈ allRegions sig y := List.mem_append_left _ (List.mem_append_left _ hb)

/-- The arguments of a state with other bytes outside its stack arguments. -/
theorem allArgs_like {y : State} {m : Mem} {Z : Region} (hm : Frame [Z] y.mem m)
    (hA : Region.Disjoint ⟨stackArgAddr y 0, 8 * nStack sig⟩ Z) :
    allArgs sig (withMem y m) = allArgs sig y := by
  simp only [allArgs, withMem_gpr]
  refine congrArg (List.map y.gpr argRegs ++ ·) (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.mp hj
  show m.readW (stackArgAddr y j) 64 = y.mem.readW (stackArgAddr y j) 64
  refine hm.readW (r := ⟨stackArgAddr y j, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  exact hA.sub_left (Offset.sub (y.gpr .rsp) (d := 8 * (j + 1)) (e := 8 * (0 + 1)) (by omega_arith)
    (by simp only [nStack, len25] at hj ⊢; omega_arith))

theorem allRegions_like {y : State} {m : Mem} {Z : Region} (hm : Frame [Z] y.mem m)
    (hZ : ∀ a ∈ allRegions sig y, a.1.Disjoint Z) :
    allArgs sig (withMem y m) = allArgs sig y ∧
      bufRegions sig (withMem y m) = bufRegions sig y ∧
      allRegions sig (withMem y m) = allRegions sig y := by
  have hd : Region.Disjoint ⟨stackArgAddr y 0, 8 * nStack sig⟩ Z :=
    hZ (⟨stackArgAddr y 0, 8 * nStack sig⟩, false) (argArea_mem y)
  have hA := allArgs_like hm hd
  have hB : bufRegions sig (withMem y m) = bufRegions sig y := by
    rw [bufRegions, bufRegions, hA, Sig.lists_of_noLists _ _ _ _ hnl, Sig.lists_of_noLists _ _ _ _ hnl]
  refine ⟨hA, hB, ?_⟩
  rw [allRegions, allRegions, hB]
  rfl

/-- The precondition of a state with other bytes in a region apart from
its buffers and stack arguments. -/
theorem pre_like {Q : sig.Post abi.ptrBits} {n : Nat} {y : State} {m : Mem} {Z : Region}
    (hy : (C Q n).pre y) (hm : Frame [Z] y.mem m) (hZ : ∀ a ∈ allRegions sig y, a.1.Disjoint Z) :
    (C Q n).pre (withMem y m) := by
  obtain ⟨hA, hB, hR⟩ := allRegions_like hm hZ
  unfold C at hy ⊢
  rw [pre_args hk] at hy ⊢
  obtain ⟨hst, hrd, hwr, hpw, hres, hb, hp⟩ := hy
  rw [hR, hB, hA]
  refine ⟨hst, hrd, hwr, hpw, hres, hb, preP_local _ _ _ (allArgs_length sig y hk) (fun b hb' a ha => ?_)
    (fun r hr => by rw [Sig.lists_of_noLists _ _ _ _ hnl] at hr; simp at hr) hp⟩
  exact (hm a fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact hZ b (bufs_sub hb') a ha hc).symm

/-- The public data of two states whose arguments are those of two states
of a contract, in memory that agrees on their buffers. -/
theorem pub_of {Q Q' : sig.Post abi.ptrBits} {n n' : Nat} {x₁ x₂ s₁ s₂ : State}
    (h₁ : (C Q' n').pre s₁) (h₂ : (C Q' n').pre s₂) (hp : (C Q' n').pub s₁ s₂)
    (ha₁ : allArgs sig x₁ = allArgs sig s₁) (ha₂ : allArgs sig x₂ = allArgs sig s₂)
    (hb₁ : ∀ b ∈ Sig.bufs sig.params (allArgs sig s₁), ∀ a, b.1.Contains a 1 → s₁.mem a = x₁.mem a)
    (hb₂ : ∀ b ∈ Sig.bufs sig.params (allArgs sig s₂), ∀ a, b.1.Contains a 1 → s₂.mem a = x₂.mem a)
    (hsp : x₁.gpr .rsp = x₂.gpr .rsp) (hmx : x₁.mxcsr = x₂.mxcsr) : (C Q n).pub x₁ x₂ := by
  unfold C at h₁ h₂ hp ⊢
  have p₁ := ((pre_args hk).mp h₁).2.2.2.2.2.2
  have p₂ := ((pre_args hk).mp h₂).2.2.2.2.2.2
  rw [pubL_args hk] at hp ⊢
  obtain ⟨⟨-, hlk⟩, hpa, -⟩ := hp
  refine ⟨⟨⟨hsp, hmx⟩, ?_⟩, by rw [ha₁, ha₂]; exact hpa, fun r hr => ?_⟩
  · show Curry.apply _ leakP (allArgs sig x₁) x₁.mem = Curry.apply _ leakP (allArgs sig x₂) x₂.mem
    rw [ha₁, ha₂, ← leakP_local (allArgs_length sig s₁ hk) p₁ hb₁, ← leakP_local (allArgs_length sig s₂ hk) p₂ hb₂]
    exact hlk
  · rw [Sig.descs_of_noLists _ _ _ hnl] at hr; simp at hr

/-! ## Before the call -/

open VG.Proof.Bignum (off word word_writeW_self)
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Proof.RsaOaep.X86_64 (ea_sp)

/-- The frame's base. -/
abbrev F (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 296

/-- The slots above the copies of the stack arguments. -/
def Z (s : State) : Region := ⟨off (F s) 152, 144⟩

/-- The memory `setup` leaves, from that of the copies, `w`'s. -/
def stashMem (w : State) : Mem :=
  ((w.mem.writeW (off (w.gpr .rsp) 168) (w.gpr .rdi)).writeW (off (w.gpr .rsp) 184) (w.gpr .rsi)).writeW
    (off (w.gpr .rsp) 232) (w.gpr .rdx)

theorem pre_post {Q Q' : sig.Post abi.ptrBits} {n : Nat} {s : State} (h : (C Q n).pre s) : (C Q' n).pre s := h

theorem setup_eq : Impl.RsaPkcs1Enc.X86_64.Front.setup = Impl.ForwardCall.X86_64.copies 296 (nStack sig) ++
    ([.store (sp 168) .rdi, .store (sp 184) .rsi, .store (sp 232) .rdx] : List Instr) := rfl

theorem stash_run {w : State} (hfr : (⟨w.gpr .rsp, 296⟩ : Region) ∈ w.wr) :
    WP isa (.block ([.store (sp 168) .rdi, .store (sp 184) .rsi, .store (sp 232) .rdx] : List Instr)) w
      (fun t => t = withMem w (stashMem w)) := by
  have c : ∀ d, d + 8 ≤ 296 → InRegions w.wr (off (w.gpr .rsp) d) 8 := fun d hd =>
    ⟨_, hfr, Offset.contains_base _ hd (by omega_arith)⟩
  xrun [VG.Proof.RsaOaep.X86_64.ea_sp, c 168 (by decide), c 184 (by decide), c 232 (by decide)]
  rfl

/-- `setup`, from the frame's push: the copies, then the slots. -/
theorem setup_ok {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3784).pre s) :
    WP isa (.block Impl.RsaPkcs1Enc.X86_64.Front.setup) (allocState 296 s)
      (fun t => t = withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))) := by
  obtain ⟨hrun, -, hwr', -, -, hg, -, -⟩ := fwdState_run (stack := 3480) (bytes := 296) hs hk (by decide) (by decide)
  rw [setup_eq]
  refine WP.block_append (WP.block ⟨_, hrun, stash_run ?_⟩)
  rw [hwr', hg .rsp (by decide)]
  exact List.mem_cons_self ..

/-! ## The callee's postcondition -/

theorem args19 (s : State) :
    List.map (stackArg s) (List.range 19) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
      stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17, stackArg s 18] := rfl

theorem allArgs_eq (s : State) : allArgs sig s = [s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8,
    s.gpr .r9, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
      stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16, stackArg s 17, stackArg s 18] := by
  simp only [allArgs, len25, argRegs, List.map_cons, List.map_nil, Nat.reduceSub, args19, List.cons_append,
    List.nil_append]

/-- `vg_rsa_pkcs1_decrypt_precomputed_body`'s postcondition, by name: what the
decryption of the arguments of `s` writes to memory `m` with the result `r`. -/
def CPost (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Proof.RsaPkcs1Enc.writtenMsgEnd m (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat r (decOf s)
where
  decOf (s : State) : Spec.Rsa.Outcome :=
    Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 8).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 13) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (s.gpr .r8).toNat)

theorem cpost_of {s : State} {m : Mem} {r : BitVec 32}
    (h : Curry.apply (sig.words abi.ptrBits) postP (allArgs sig s) s.mem m r) : CPost s m r := by
  rw [allArgs_eq] at h
  exact h

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s postcondition, by name. -/
def FPost (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg m (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat r (CPost.decOf s)

theorem fpost_to {s : State} {m : Mem} {r : BitVec 32} (h : FPost s m r) :
    Curry.apply (sig.words abi.ptrBits) postFP (allArgs sig s) s.mem m r := by
  rw [allArgs_eq]
  exact h

/-! ## The call -/

open VG.Proof.RsaPkcs1Enc.X86_64.Dec (DPre)

/-- The stack the function uses. -/
abbrev stkF (s : State) : Region := below (s.gpr .rsp) 3784

theorem F_eq (s : State) : F s = s.gpr .rsp - BitVec.ofNat 64 3784 + BitVec.ofNat 64 3488 :=
  Offset.sub_ofNat_eq _ (by decide)

/-- Bytes of the frame are in the stack the function uses. -/
theorem fslot_sub (s : State) {d n : Nat} (h : d + n ≤ 296) : Region.Sub ⟨off (F s) d, n⟩ (stkF s) := by
  rw [F_eq, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.sub_base _ (by omega_arith)

theorem frame_stk (s : State) : Region.Sub ⟨F s, 296⟩ (stkF s) := by
  have := fslot_sub s (d := 0) (n := 296) (by decide)
  rwa [off, BitVec.add_zero] at this

/-- The bytes below the frame are in the stack the function uses. -/
theorem below_stk (s : State) {n : Nat} (h : n ≤ 3488) : Region.Sub (below (F s) n) (stkF s) :=
  fun x hx => below_sub (sp := s.gpr .rsp) (a := n + 296) (b := 3784) (by omega_arith) (by decide) x
    (below_below _ 296 n x hx)

/-- A frame word past changes below the frame, and in the buffers. -/
theorem frame_ww {Z' : Region} {m₁ m₂ : Mem} (h : Frame [Z'] m₁ m₂) (a : Addr) (v : BitVec 64) :
    Frame [Z'] (m₁.writeW a v) (m₂.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact h x hx

theorem Z_eq (s : State) : Z s = ⟨s.gpr .rsp - BitVec.ofNat 64 144, 144⟩ := by
  rw [Z, Offset.sub_ofNat_eq (s.gpr .rsp) (show 144 ≤ 296 by decide)]

/-- The writable regions of the callee: the buffers' writable ones. -/
theorem wr_eq (s : State) : ((fwdRegions sig 296 s).filter (·.2)).map (·.1) = [Dec.outR s, Dec.mlR s, Dec.scrR s] := by
  rw [fwdRegions, bufRegions, allArgs_eq, Sig.lists_of_noLists _ _ _ _ hnl]
  simp only [sig, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig, Proof.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.map_nil, List.append_nil, List.filter_cons, List.filter_nil, Elem.size, Nat.mul_one,
    List.map_cons, Dec.outR, Dec.mlR, Dec.scrR, Bool.false_eq_true, ↓reduceIte, Nat.one_mul]

/-- What the call leaves. -/
structure Called (s t : State) : Prop where
  rsp : t.gpr .rsp = F s
  rd : t.rd = s.rd
  wr : t.wr = ⟨F s, 296⟩ :: s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r
  mx : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  wOut : word t.mem (F s) 168 = s.gpr .rdi
  wK : word t.mem (F s) 184 = s.gpr .rsi
  wMl : word t.mem (F s) 232 = s.gpr .rdx
  fr : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] s.mem t.mem
  post : CPost s t.mem ((t.gpr .rax).setWidth 32)

theorem disj_wr {s : State} (hp : DPre s) {R : Region} (hR : Region.Sub R (Dec.stkR s)) :
    ∀ r ∈ [Dec.outR s, Dec.mlR s, Dec.scrR s], R.Disjoint r := by
  intro r hr
  have hsi := hp.hsi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.dKo.sub_left hR
  · exact hp.dKm.sub_left hR
  · exact hp.dKs.sub_left hR

theorem slot3480 (s : State) {d n : Nat} (h : d + n ≤ 296) :
    Region.Sub ⟨off (F s) d, n⟩ (Dec.stkR s) := by
  rw [Dec.stkR, show decStack = 3480 from rfl, show F s = s.gpr .rsp - BitVec.ofNat 64 3480 + BitVec.ofNat 64 3184 from Offset.sub_ofNat_eq _ (by decide),
    off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.sub_base _ (by omega_arith)

/-- The call of `vg_rsa_pkcs1_decrypt_precomputed_body`, from `setup`'s state. -/
theorem call_ok {Q : sig.Post abi.ptrBits} {name : String} {callee : Prog isa}
    (hv : ∀ s, (C postP 3480).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (C postP 3480).post s s')
    (hsafe : SpSafe callee) (hd : callee.x86_64Depth ≤ 3480) {s : State} (hs : (C Q 3784).pre s) (hp : DPre s) :
    WP isa (.call name callee) (withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))) (Called s) := by
  have hs' : (C postP (3480 + 296 + 8)).pre s := pre_post hs
  obtain ⟨-, hrd', hwr', hmxw, -, hg, hfw, -⟩ := fwdState_run (stack := 3480) (bytes := 296) hs' hk (by decide) (by decide)
  have hargsN := (narrowF_facts (stack := 3480) (bytes := 296) hk (by decide) (by decide) hs').2.2.2.1
  have hall := allRegions_narrowF (stack := 3480) (bytes := 296) hk (by decide) (by decide) (by decide) hs'
  have hout := fwd_out (stack := 3480) (bytes := 296) hk hs'
  have hagN := narrowF_agree (stack := 3480) (bytes := 296) hk (by decide) (by decide) hs'
  have hpreN := narrowF_pre (stack := 3480) (bytes := 296) hk (by decide) (by decide) (by decide) preP_local hs'
  have hsp1 := hp.sp1
  have hsp2 := hp.sp2
  generalize hw : fwdState sig 296 s = w at hrd' hwr' hmxw hg hfw hagN hpreN hargsN
  have hwrsp : w.gpr .rsp = F s := (hg .rsp (by decide)).trans (allocState_rsp' _ _)
  have hN : narrowF sig 296 s = w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
      (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) := by rw [← hw]; rfl
  rw [hN] at hall hagN hpreN hargsN
  -- The stores of `setup`, in `Z s`.
  have hZs : Frame [Z s] w.mem (stashMem w) := by
    have c : ∀ d, 152 ≤ d → d + 8 ≤ 296 → (Z s).Contains (off (w.gpr .rsp) d) 8 := fun d h1 h2 => by
      rw [hwrsp]; exact Offset.contains (F s) (e := 152) (k := 144) h1 (by omega_arith) (by omega_arith)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (c 232 (by decide) (by decide))
  -- The callee's entry: `narrowF`'s, with the slots.
  have hentry : (withMem w (stashMem w)).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
      (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) =
      withMem (w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
        (((fwdRegions sig 296 s).filter (·.2)).map (·.1))) ((stashMem w).writeW (w.gpr .rsp - 8) (w.unknowns 0)) :=
    rfl
  have hZe : Frame [Z s] (w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
      (((fwdRegions sig 296 s).filter (·.2)).map (·.1))).mem ((stashMem w).writeW (w.gpr .rsp - 8) (w.unknowns 0)) :=
    frame_ww hZs _ _
  have hZd : ∀ a ∈ fwdRegions sig 296 s, a.1.Disjoint (Z s) := by
    intro a ha
    simp only [fwdRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · rw [Z_eq]; exact hout a ha (by decide) (by decide)
    · rw [nStack_eq, Z]
      exact Offset.base_disjoint (F s) (k := 152) (e := 152) (n := 144) (Nat.le_refl _) (by decide)
  have hpre := pre_like hpreN hZe (by rw [hall]; exact hZd)
  rw [← hentry] at hpre
  -- The callee's regions are within the caller's and the frame.
  have hs'' := hs'
  rw [pre_args hk] at hs''
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs''
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hlistR : ∀ a ∈ (Sig.lists 64 s.mem sig.params (allArgs sig s)).map (fun r => (r, false)),
      a.1 ∈ s.rd := fun a ha => by
    rw [Sig.lists_of_noLists _ _ _ _ hnl] at ha; simp at ha
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) (withMem w (stashMem w)).wr := by
    rw [withMem_wr, hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
      ((withMem w (stashMem w)).rd ++ (withMem w (stashMem w)).wr) := by
    rw [withMem_rd, withMem_wr, hrd', hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hlistR a ha)
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ (a := 296)
        (b := 296) (Nat.le_refl _) (by rw [nStack_eq]; decide) (by decide)⟩)
  refine WP.callF (k := C postP 3480) hv hsafe (by omega_arith) hpre (Covers.append_left hcovR (Covers.right hcovW))
    hcovW fun s' hrd₁ hwr₁ hcs hfr ⟨s₂, hm₂, hg₂, hpost⟩ hmx => ?_
  rw [withMem_gpr, hwrsp, wr_eq] at hfr
  rw [withMem_mem] at hfr
  -- Memory, from the entry on.
  have fbig : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] s.mem s'.mem := by
    refine Frame.trans (Frame.sub hfw fun r hr => ?_) (Frame.trans (Frame.sub hZs fun r hr => ?_) (Frame.sub hfr fun r hr => ?_))
    · rw [List.mem_singleton.mp hr, allocState_rsp', nStack_eq]
      exact ⟨stkF s, by simp, fun x hx => frame_stk s x (Offset.sub_base (F s) (d := 0) (n := 152) (k := 296)
        (by decide) x (by rwa [BitVec.add_zero]))⟩
    · rw [List.mem_singleton.mp hr, Z]
      exact ⟨stkF s, by simp, fslot_sub s (by decide)⟩
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨Dec.outR s, by simp, fun _ h => h⟩
      · exact ⟨Dec.mlR s, by simp, fun _ h => h⟩
      · exact ⟨Dec.scrR s, by simp, fun _ h => h⟩
      · exact ⟨stkF s, by simp, below_stk s (by omega_arith)⟩
  -- The slots, from the stores on.
  have hslot : ∀ {d : Nat}, 152 ≤ d → d + 8 ≤ 296 → word s'.mem (F s) d = word (stashMem w) (F s) d := fun h1 h2 =>
    hfr.readW (r := ⟨off (F s) _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact disj_wr hp (slot3480 s (by omega_arith)) r hr
      · rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_below (F s) (by omega_arith)) (by decide)
  have hst : stashMem w = ((w.mem.writeW (off (F s) 168) (w.gpr .rdi)).writeW (off (F s) 184) (w.gpr .rsi)).writeW
      (off (F s) 232) (w.gpr .rdx) := by rw [stashMem, hwrsp]
  have g : ∀ q : Reg, q ≠ .rax → q ≠ .rsp → w.gpr q = s.gpr q := fun q h1 h2 =>
    (hg q h1).trans (allocState_gpr' _ _ h2)
  -- The callee's postcondition, of the caller's arguments.
  have hargsE := (allRegions_like hZe (by rw [hall]; exact hZd)).1
  rw [hargsN] at hargsE
  rw [← hentry] at hargsE
  have hpreE := ((pre_args hk).mp hpre).2.2.2.2.2.2
  rw [post_args hk] at hpost
  rw [hargsE] at hpost hpreE
  have hb : ∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ a, b.1.Contains a 1 →
      ((withMem w (stashMem w)).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1))
        (((fwdRegions sig 296 s).filter (·.2)).map (·.1))).mem a = s.mem a := fun b hb' a ha => by
    rw [hentry, withMem_mem, hZe a fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact hZd b (List.mem_append_left _ (List.mem_append_left _ hb')) a ha hc]
    exact hagN b hb' a ha
  have hpost' := postP_local (allArgs_length sig s hk) hpreE hb hpost
  rw [hm₂, hg₂ .rax (by decide)] at hpost'
  refine ⟨?_, hrd₁.trans (by rw [withMem_rd, hrd']; rfl), hwr₁.trans (by rw [withMem_wr, hwr']; rfl),
    fun r hr hr' => ?_, ?_, ?_, ?_, ?_, fbig, cpost_of hpost'⟩
  · rw [hcs .rsp (by simp [calleeSaved]), withMem_gpr, hwrsp]
  · have hra : r ≠ .rax := by rintro rfl; simp [calleeSaved] at hr
    rw [hcs r hr, withMem_gpr, g r hra hr']
  · rw [hmx, withMem_mxcsr, hmxw]
  · rw [hslot (by decide) (by decide), hst, word_ww _ _ _ (by decide) (by decide) (by decide),
      word_ww _ _ _ (by decide) (by decide) (by decide), word_writeW_self, g _ (by decide) (by decide)]
  · rw [hslot (by decide) (by decide), hst, word_ww _ _ _ (by decide) (by decide) (by decide), word_writeW_self,
      g _ (by decide) (by decide)]
  · rw [hslot (by decide) (by decide), hst, word_writeW_self, g _ (by decide) (by decide)]

/-! ## After the call: the pieces in the frame -/

section
open VG.Proof.RsaOaep.X86_64 (Lay Rep upd nW clrV cpV selV ShI copy_ok byteLoop_ok stepR_ok Apart ea_at0 ea_ix
  ea_ix0 off_plus shr1_ofNat dbl_ofNat Rep.apart neg_and1 selB)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.RsaOaep.X86_64 (frameBytes oRsa oBuf sOut sK sMl sR sA sScr)
open VG.Impl.RsaPkcs1Enc.X86_64.Front (clearBuf copyIn shiftPass nextPass shift copyOut toBuf ret)
open VG.Proof.Bignum (off_off)
open VG.Proof.Bignum.X86_64 (Scr ofNat_sub_beq wp_upto)

/-- `8 ⌈k / 4⌉`: the bytes `clearBuf` clears, at least `2 k`. -/
def clrN (k : Nat) : Nat := 8 * ((k + 3) / 4)

theorem clrN_ofNat {k : Nat} (hk : k ≤ 1024) :
    (BitVec.ofNat 64 k + 3) >>> 2 <<< 3 = BitVec.ofNat 64 (clrN k) := by
  rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, clrN]
  omega_arith

/-- `n` bytes from `o` cleared a word at a time, `n` in `r10`. -/
theorem clearR_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {o n : Nat} (hn : 0 < n) (h8 : n % 8 = 0) (ho : o + n ≤ oRsa) (hn31 : n < 2 ^ 31)
    (hcx : u.gpr .rcx = off S o) (hax : u.gpr .rax = 0) (hr8 : u.gpr .r8 = BitVec.ofNat 64 0)
    (h10 : u.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block [.store (Impl.Mgf1.X86_64.ix .rcx .r8) .rax, .alu .add .r8 (.imm 8),
        .alu .cmp .r8 (.reg .r10)]) .ne) u fun u' =>
      Lay u' F S ∧ Keep [.r8] u u' ∧ Rep u'.mem F S (clrV V o n) W := by
  refine wp_upto (a := 0) (N := n / 8) (by omega_using [hn, h8]) (fun j v => Lay v F S ∧ Keep [.r8] u v ∧
      v.gpr .r8 = BitVec.ofNat 64 (8 * j) ∧ Rep v.mem F S (clrV V o (8 * j)) W) ?_ (fun v ⟨Lv, k, _, Rv⟩ => ?_)
    ⟨L, Keep.refl _ _, hr8, (congrArg (fun V' => Rep u.mem F S V' W) (funext fun x => by
      simp only [clrV]; rw [ifn (by omega_using [])])).mpr R⟩
  · intro j _ hj v ⟨Lv, k, hv8, Rv⟩
    have hea : v.ea (Impl.Mgf1.X86_64.ix .rcx .r8) = off S (o + 8 * j) := by
      rw [ea_ix0, k.gpr (by decide), hcx, hv8]; exact off_off S o (8 * j)
    refine WP.mono (WP.keep [.r8] (Q := fun v' => v'.zf = some (decide (j + 1 = n / 8)) ∧
        v'.gpr .r8 = BitVec.ofNat 64 (8 * (j + 1)) ∧ v'.mem = v.mem.writeW (off S (o + 8 * j)) (0#64)) ?_ rfl)
      fun v' ⟨⟨hz, h8', hm⟩, k'⟩ => ⟨hz, ?_⟩
    · xrun [hea, Lv.sst (d := o + 8 * j) (by omega_using [ho, hj]), k.gpr (show Reg.rax ∉ [Reg.r8] by decide), hax,
        hv8, k.gpr (show Reg.r10 ∉ [Reg.r8] by decide), h10, VG.Proof.RsaOaep.X86_64.ofNat_add_lit,
        ofNat_sub_beq (show 8 * j + 8 < 2 ^ 64 by omega_using [hn31, hj]) (show n < 2 ^ 64 by omega_using [hn31])]
      exact ⟨by simp only [decide_eq_decide]; omega_using [h8], by congr 1, rfl⟩
    · have R' := Rv.ws Lv.geo (o := o + 8 * j) (w := 64) (by omega_using [ho, hj]) (0#64)
      rw [← hm] at R'
      have R'' : Rep v'.mem F S (clrV V o (8 * (j + 1))) W := by
        refine (congrArg (fun V' => Rep v'.mem F S V' W) (funext fun x => ?_)).mp R'
        simp only [VG.Proof.RsaOaep.X86_64.stBytes, clrV]
        by_cases h1 : o + 8 * j ≤ x ∧ x < o + 8 * j + 64 / 8
        · rw [ifp h1, ifp (by omega_using [h1])]
          exact BitVec.eq_of_toNat_eq (by simp)
        · rw [ifn h1]
          by_cases h2 : o ≤ x ∧ x < o + 8 * j
          · rw [ifp h2, ifp (by omega_using [h2])]
          · rw [ifn h2, ifn (by omega_using [h1, h2])]
      exact ⟨Lv.of_rep Rv R'' (k'.gpr (by decide)) k'.2.2, (k.trans k').mono (by decide), h8', R''⟩
  · rw [show 8 * (n / 8) = n by omega_using [h8]] at Rv
    exact ⟨Lv, k, Rv⟩

theorem clearBuf_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {k : Nat} (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k) (hk1 : k ≤ 1024) :
    WP isa clearBuf u fun u' => Lay u' F S ∧ Keep [.rcx, .rax, .r8, .r10] u u' ∧ u'.gpr .rcx = off S oBuf ∧
      Rep u'.mem F S (clrV V oBuf (clrN k)) W := by
  have hs := L.slot
  simp only [Bignum.word] at hs
  refine WP.seq (WP.mono (WP.keep [.rcx, .rax, .r8, .r10] (Q := fun v => v.gpr .rcx = off S oBuf ∧ v.gpr .rax = 0 ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.gpr .r10 = BitVec.ofNat 64 (clrN k) ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk'⟩ => ?_)
  · xrun [clearBuf, Impl.RsaOaep.X86_64.scr, Impl.Mgf1.X86_64.scr, Impl.RsaOaep.X86_64.lay, List.cons_append,
      List.nil_append, VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
      L.ld (d := sK) (by decide), R.slot (d := sK) (k := 23) rfl (by decide) hk,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oBuf < 2 ^ 31 by decide), clrN_ofNat hk1]
  obtain Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  exact WP.mono (clearR_ok Lv (hm ▸ R) (o := oBuf) (n := clrN k) (by unfold clrN; omega_arith)
    (by unfold clrN; omega_arith) (by unfold clrN oBuf oRsa; omega_arith) (by unfold clrN; omega_arith) h₁ h₂ h₃ h₄)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk'.trans kw).mono (by decide), (kw.gpr (by decide)).trans h₁, Rw⟩

theorem copyIn_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hcx : u.gpr .rcx = off S oBuf) {o : Addr} {k : Nat} (ho : W 21 = o)
    (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k) (hk1 : k ≤ 1024)
    (hsrc : ∀ i < k, InRegions (u.rd ++ u.wr) (o + BitVec.ofNat 64 i) 1)
    (hdis : ∀ i < k, ∀ j < k, o + BitVec.ofNat 64 i ≠ off S (oBuf + 0 + j)) :
    WP isa copyIn u fun u' => Lay u' F S ∧ Keep [.rsi, .r10, .rax, .r8] u u' ∧ u'.gpr .rcx = off S oBuf ∧
      Rep u'.mem F S (cpV V (fun i => u.mem (o + BitVec.ofNat 64 i)) (oBuf + 0) k) W := by
  refine WP.seq (WP.mono (WP.keep [.rsi, .r10, .r8] (Q := fun v => v.gpr .rsi = o ∧ v.gpr .r10 = BitVec.ofNat 64 k ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, h₃, hm⟩, hk'⟩ => ?_)
  · xrun [copyIn, VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.slot (d := sOut) (k := 21) rfl (by decide) ho, R.slot (d := sK) (k := 23) rfl (by decide) hk]
  obtain Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  have hcv : v.gpr .rcx = off S oBuf := (hk'.gpr (by decide)).trans hcx
  refine WP.mono (copy_ok Lv (hm ▸ R) (d := .rcx) (by decide) (p := o) (o := oBuf) (disp := 0) (n := k)
    (stepR_ok (by omega_arith) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₂) hk0
    (by unfold oBuf oRsa; omega_arith) h₁ hcv h₃ (fun i hi => by rw [hk'.2.1, hk'.2.2]; exact hsrc i hi) hdis)
    fun w ⟨Lw, kw, Rw⟩ => ⟨Lw, (hk'.trans kw).mono (by decide), (kw.gpr (by decide)).trans hcv, ?_⟩
  rw [hm] at Rw
  exact Rw


/-- One pass, with the buffer at `rcx`: its first `k` (`r10`) bytes replaced
by those `d` (`rdx`) after them if bit 0 of `a` (`sA`) is set. -/
theorem shiftPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {d k : Nat} (hcx : u.gpr .rcx = off S oBuf) (hdx : u.gpr .rdx = BitVec.ofNat 64 d)
    (h10 : u.gpr .r10 = BitVec.ofNat 64 k) (hd1 : 1 ≤ d) (hd2 : d ≤ 1024) (hk0 : 0 < k) (hk1 : k ≤ 1024) :
    WP isa shiftPass u fun u' => Lay u' F S ∧ Keep [.rsi, .r11, .r9, .r8, .rax, .rdi] u u' ∧
      Rep u'.mem F S (selV V d (decide ((W 34).toNat % 2 = 1)) k) W := by
  have c3 : oBuf = 1024 := rfl
  unfold shiftPass
  refine WP.seq (WP.mono (WP.keep [.rsi, .r11, .r9, .r8] (Q := fun v => v.gpr .rsi = off S (oBuf + d) ∧
      v.gpr .r9 = (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) ∧
      v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · xrun [VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sA) (by decide), hcx, hdx,
      R.slot (d := sA) (k := 34) rfl (by decide) rfl, show BitVec.setWidth 64 (0 : BitVec 32) = 0#64 from rfl, neg_and1]
    rw [BitVec.add_comm, off_plus]
  obtain h₁ : v.gpr .rcx = off S oBuf := (hk.gpr (by decide)).trans hcx
  obtain h10v : v.gpr .r10 = BitVec.ofNat 64 k := (hk.gpr (by decide)).trans h10
  obtain Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine WP.mono (byteLoop_ok (n := k) hk0
    (stepR_ok (by omega_arith) v (show Reg.r10 ∉ [Reg.rax, .rdi, .r8] by decide) (by decide) h10v)
    (ShI v F S V W d (decide ((W 34).toNat % 2 = 1))) ?_ ⟨Lv, Keep.refl _ _, h₄,
      (congrArg (fun V' => Rep v.mem F S V' W) (funext fun x => by
        simp only [selV]; rw [ifn (by omega_arith)])).mpr (hm ▸ R)⟩) fun w I => ⟨I.L, (hk.trans I.keep).mono (by decide), I.R⟩
  intro j hj w I
  obtain hcw : w.gpr .rcx = off S oBuf := (I.keep.gpr (by decide)).trans h₁
  obtain hsw : w.gpr .rsi = off S (oBuf + d) := (I.keep.gpr (by decide)).trans h₂
  obtain h9w : w.gpr .r9 = (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) := (I.keep.gpr (by decide)).trans h₃
  obtain va : w.mem (off S (oBuf + j)) = V (oBuf + j) := by
    rw [I.R.scr _ (by unfold oRsa; omega_arith), selV, ifn (by omega_arith)]
  obtain vb : w.mem (off S (oBuf + d + j)) = V (oBuf + j + d) := by
    rw [I.R.scr _ (by unfold oRsa; omega_arith), selV, ifn (by omega_arith), show oBuf + d + j = oBuf + j + d by omega_arith]
  obtain e : (if (W 34).toNat % 2 = 1 then BitVec.allOnes 64 else 0#64) =
      (if decide ((W 34).toNat % 2 = 1) then BitVec.allOnes 64 else 0#64) := by simp
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
      w'.mem = w.mem.writeW (off S (oBuf + j))
        (if decide ((W 34).toNat % 2 = 1) then V (oBuf + j + d) else V (oBuf + j))) ?_ rfl)
    fun w' ⟨⟨h8', hm'⟩, k⟩ => ⟨(I.keep.trans k).mono (by decide), h8', fun w'' k' hm'' h8'' => ?_⟩
  · xrun [ea_ix0, hcw, hsw, h9w, I.r8, off_plus, I.L.sld8 (d := oBuf + j) (by unfold oRsa; omega_arith),
      I.L.sld8 (d := oBuf + d + j) (by unfold oRsa; omega_arith), I.L.sst8 (d := oBuf + j) (by unfold oRsa; omega_arith),
      va, vb, e, selB]
  · have R' := I.R.wb I.L.geo (o := oBuf + j) (by unfold oRsa; omega_arith)
      (if decide ((W 34).toNat % 2 = 1) then V (oBuf + j + d) else V (oBuf + j))
    rw [← hm', ← hm''] at R'
    obtain R'' : Rep w''.mem F S (selV V d (decide ((W 34).toNat % 2 = 1)) (j + 1)) W := by
      refine (congrArg (fun V' => Rep w''.mem F S V' W) (funext fun x => ?_)).mp R'
      unfold upd selV
      by_cases hx : x = oBuf + j
      · subst hx
        rw [ifp (show oBuf + j = oBuf + j from rfl), ifp (show oBuf ≤ oBuf + j ∧ oBuf + j < oBuf + (j + 1) by omega_arith)]
      · rw [ifn hx]
        by_cases h' : oBuf ≤ x ∧ x < oBuf + j
        · rw [ifp h', ifp (show oBuf ≤ x ∧ x < oBuf + (j + 1) by omega_arith)]
        · rw [ifn h', ifn (show ¬ (oBuf ≤ x ∧ x < oBuf + (j + 1)) by omega_arith)]
    exact ⟨I.L.of_rep I.R R'' (by rw [k'.gpr (by decide), k.gpr (by decide)]) (k'.2.2.trans k.2.2),
      (I.keep.trans (k.trans k')).mono (by decide), h8'', R''⟩

theorem nextPass_eq : nextPass =
    ([.mov .rax (.mem (Impl.Mgf1.X86_64.sp sA)), .shift .shr .rax 1, .store (Impl.Mgf1.X86_64.sp sA) .rax] :
      List Instr) ++ ([.alu .add .rdx (.reg .rdx), .alu .cmp .r10 (.reg .rdx)] : List Instr) := rfl

theorem cf_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide ((BitVec.ofNat 64 a).toNat < (BitVec.ofNat 64 b).toNat) = decide (a < b) := by
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- The next pass: `a / 2`, `2 d`, and CF set once `k < 2 d`. -/
theorem nextPass_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {a d k : Nat} (ha : W 34 = BitVec.ofNat 64 a) (hdx : u.gpr .rdx = BitVec.ofNat 64 d)
    (h10 : u.gpr .r10 = BitVec.ofNat 64 k) (ha' : a < 2 ^ 64) (hd : 2 * d < 2 ^ 64) (hk : k < 2 ^ 64) :
    WP isa (.block nextPass) u fun u' => Lay u' F S ∧ Keep [.rax, .rdx] u u' ∧
      u'.gpr .rdx = BitVec.ofNat 64 (2 * d) ∧ u'.cf = some (decide (k < 2 * d)) ∧
      Rep u'.mem F S V (upd W 34 (BitVec.ofNat 64 (a / 2))) := by
  have G' := L.geo
  rw [nextPass_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun u' => u'.mem = u.mem.writeW (off F (8 * 34)) (BitVec.ofNat 64 (a / 2)))
    ?_ rfl) fun u1 ⟨hm1, k1⟩ => ?_
  · xrun [VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sA) (by decide), L.st (d := sA) (by decide),
      R.slot (d := sA) (k := 34) rfl (by decide) ha, shr1_ofNat ha']
    rfl
  obtain R1 : Rep u1.mem F S V _ := hm1 ▸ R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 (a / 2))
  obtain L1 := L.of_rep' R R1 (by simp [upd]) (k1.gpr (by decide)) k1.2.2
  obtain hdx1 : u1.gpr .rdx = BitVec.ofNat 64 d := (k1.gpr (by decide)).trans hdx
  obtain h101 : u1.gpr .r10 = BitVec.ofNat 64 k := (k1.gpr (by decide)).trans h10
  refine WP.mono (WP.keep [.rdx, .r10] (Q := fun u' => u'.gpr .rdx = BitVec.ofNat 64 (2 * d) ∧
    u'.gpr .r10 = u1.gpr .r10 ∧ u'.cf = some (decide (k < 2 * d)) ∧ u'.mem = u1.mem) ?_ rfl)
    fun u2 ⟨⟨hd2, h102, hc2, hm2⟩, k2⟩ => ?_
  · xrun [hdx1, h101, dbl_ofNat, cf_ofNat hk hd]
  refine ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), ⟨fun r hr => ?_, k2.2.1.trans k1.2.1,
    k2.2.2.trans k1.2.2⟩, hd2, hc2, hm2 ▸ R1⟩
  by_cases h : r = .r10
  · subst h; rw [h102]; exact k1.gpr (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact (k2.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2, h⟩)).trans
      (k1.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr.1))

/-- The byte `x` of the buffer `V` of `k` bytes, followed by zeros. -/
def bufK (V : Nat → Byte) (k x : Nat) : Byte := if x < k then V (oBuf + x) else 0

/-- Before pass `p` of the shift by `A` of the buffer's first `k` bytes. -/
structure ShiftI (u₀ : State) (F S : Addr) (V₀ : Nat → Byte) (W₀ : Nat → BitVec 64) (k A p : Nat) (w : State) :
    Prop where
  L : Lay w F S
  keep : Keep [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] u₀ w
  rcx : w.gpr .rcx = off S oBuf
  rdx : w.gpr .rdx = BitVec.ofNat 64 (2 ^ p)
  r10 : w.gpr .r10 = BitVec.ofNat 64 k
  le : 2 ^ p ≤ k
  rep : ∃ V W, Rep w.mem F S V W ∧ W 34 = BitVec.ofNat 64 (A / 2 ^ p) ∧ (∀ j < nW, j ≠ 34 → W j = W₀ j) ∧
    (∀ i < k, V (oBuf + i) = bufK V₀ k (i + A % 2 ^ p)) ∧
    (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + k) → V o = V₀ o)

/-- The buffer's first `k` bytes shifted left by `k - L` bytes, `L` the
word at `msg_len`, in a pass for each bit of `k`. -/
theorem shift_ok {u : State} {F S : Addr} (L : Lay u F S) {V₀ : Nat → Byte} {W₀ : Nat → BitVec 64}
    (R : Rep u.mem F S V₀ W₀) (hcx : u.gpr .rcx = off S oBuf) {k Ln : Nat} {ml : Addr}
    (hk : W₀ 23 = BitVec.ofNat 64 k) (hm : W₀ 29 = ml) (hin : InRegions (u.rd ++ u.wr) ml 8)
    (hv : u.mem.readW ml 64 = BitVec.ofNat 64 Ln) (hL : Ln ≤ k) (hk0 : 0 < k) (hk1 : k ≤ 1024)
    (hz : ∀ x, k ≤ x → x < 2 * k → V₀ (oBuf + x) = 0) :
    WP isa shift u fun u' => Lay u' F S ∧ Keep [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] u u' ∧
      u'.gpr .rcx = off S oBuf ∧ ∃ V W', Rep u'.mem F S V W' ∧ (∀ j < nW, j ≠ 34 → W' j = W₀ j) ∧
        (∀ i < k, V (oBuf + i) = bufK V₀ k (i + (k - Ln))) ∧
        (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + k) → V o = V₀ o) := by
  have G' := L.geo
  unfold shift
  obtain R1 := R.wf G' (k := 34) (by decide) (BitVec.ofNat 64 (k - Ln))
  refine WP.seq (WP.mono (WP.keep [.rax, .rdi, .rdx, .r10] (Q := fun v =>
      v.gpr .rdx = BitVec.ofNat 64 1 ∧ v.gpr .r10 = BitVec.ofNat 64 k ∧
      v.mem = u.mem.writeW (off F (8 * 34)) (BitVec.ofNat 64 (k - Ln))) ?_ rfl) fun v ⟨⟨hdv, h10v, hm'⟩, hk'⟩ => ?_)
  · xrun [VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sK) (by decide), L.ld (d := sMl) (by decide),
      L.st (d := sA) (by decide), R.slot (d := sK) (k := 23) rfl (by decide) hk,
      R.slot (d := sMl) (k := 29) rfl (by decide) hm, ea_at0, hin, hv, VG.Offset.ofNat_sub_ofNat hL]
    all_goals rfl
  obtain hcv : v.gpr .rcx = off S oBuf := (hk'.gpr (by decide)).trans hcx
  obtain Rv : Rep v.mem F S V₀ _ := hm' ▸ R1
  obtain Lv := L.of_rep' R Rv (by simp [upd]) (hk'.gpr (by decide)) hk'.2.2
  obtain I0 : ShiftI u F S V₀ W₀ k (k - Ln) 0 v := ⟨Lv, hk'.mono (by decide), hcv, hdv, h10v, by rw [Nat.pow_zero]; exact hk0, V₀, _,
    Rv, by simp [upd], fun j _ h1 => by simp only [upd, ifn h1],
    fun i hi => by simp only [Nat.pow_zero, Nat.mod_one, Nat.add_zero, bufK]; rw [ifp hi], fun _ _ => rfl⟩
  refine WP.loop (M := isa) (fun n w => ∃ p, n = 11 - p ∧ p < 11 ∧ ShiftI u F S V₀ W₀ k (k - Ln) p w)
    ?_ (11 - 0) v ⟨0, rfl, by decide, I0⟩
  rintro n w ⟨p, rfl, hp, I⟩
  obtain ⟨V, W', Rw, h34, hW, hB, hO⟩ := I.rep
  have hpk := I.le
  have hp0 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  obtain hAp : k - Ln < 2 ^ 64 := by omega_arith
  refine WP.seq (WP.mono (shiftPass_ok I.L Rw I.rcx I.rdx I.r10 hp0 (by omega_arith) hk0 hk1)
    fun w1 ⟨L1, k1, R1⟩ => ?_)
  refine WP.mono (nextPass_ok L1 R1 (a := (k - Ln) / 2 ^ p) (d := 2 ^ p) (k := k) h34
    ((k1.gpr (by decide)).trans I.rdx) ((k1.gpr (by decide)).trans I.r10)
    (by have := Nat.div_le_self (k - Ln) (2 ^ p); omega_arith) (by omega_arith) (by omega_arith))
    fun w2 ⟨L2, k2, hd2, hc2, R2⟩ => ?_
  obtain hbit : (W' 34).toNat % 2 = (k - Ln) / 2 ^ p % 2 := by
    have := Nat.div_le_self (k - Ln) (2 ^ p)
    rw [h34, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (k - Ln) / 2 ^ p) (by omega_arith)]
  obtain hrep : ∃ V W, Rep w2.mem F S V W ∧ W 34 = BitVec.ofNat 64 ((k - Ln) / 2 ^ (p + 1)) ∧
      (∀ j < nW, j ≠ 34 → W j = W₀ j) ∧
      (∀ i < k, V (oBuf + i) = bufK V₀ k (i + (k - Ln) % 2 ^ (p + 1))) ∧
      (∀ o, ¬ (oBuf ≤ o ∧ o < oBuf + k) → V o = V₀ o) := by
    refine ⟨_, _, R2, ?_, fun j hj h1 => ?_, fun i hi => ?_, fun o ho => ?_⟩
    · simp only [upd]; rw [Nat.pow_succ, Nat.div_div_eq_div_mul]; rfl
    · simp only [upd, ifn h1]; exact hW j hj h1
    · simp only [selV]
      rw [Nat.mod_pow_succ, ifp (show oBuf ≤ oBuf + i ∧ oBuf + i < oBuf + k by omega_arith)]
      rcases Nat.mod_two_eq_zero_or_one ((k - Ln) / 2 ^ p) with h0 | h1
      · rw [hbit, h0, show decide (0 = 1) = false from rfl]
        simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero]
        exact hB i hi
      · rw [hbit, h1, show decide (1 = 1) = true from rfl]
        simp only [ite_true, Nat.mul_one]
        rw [show oBuf + i + 2 ^ p = oBuf + (i + 2 ^ p) by omega_arith]
        by_cases hik : i + 2 ^ p < k
        · rw [hB (i + 2 ^ p) hik]; congr 1; omega_arith
        · rw [hO _ (by omega_arith), hz _ (by omega_arith) (by omega_arith), bufK, ifn (by omega_arith)]
    · have ho' : ¬ (oBuf ≤ o ∧ o < oBuf + k) := ho
      unfold selV; rw [ifn ho']; exact hO o ho
  obtain ⟨V', W'', R', h34', hW'', hB', hO'⟩ := hrep
  have hkeep : Keep [.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] u w2 := ((I.keep.trans k1).trans k2).mono (by decide)
  have hcx2 : w2.gpr .rcx = off S oBuf := ((k2.gpr (by decide)).trans (k1.gpr (by decide))).trans I.rcx
  by_cases hl : 2 ^ (p + 1) ≤ k
  · have hp1 : p + 1 < 11 := by
      refine Nat.lt_of_not_le fun h => ?_
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
      have : 2 ^ 11 = 2048 := rfl
      omega_arith
    refine .inr ⟨by simp only [eval, hc2]; simp [Nat.pow_succ] at hl ⊢; omega_arith, 11 - (p + 1), by omega_arith, p + 1, rfl,
      hp1, L2, hkeep, hcx2, by rw [hd2, Nat.pow_succ, Nat.mul_comm], (k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans I.r10),
      hl, V', W'', R', h34', fun j hj h1 => hW'' j hj h1, hB', hO'⟩
  · refine .inl ⟨by simp only [eval, hc2]; simp [Nat.pow_succ] at hl ⊢; omega_arith, L2, hkeep, hcx2, V', W'', R', hW'',
      fun i hi => ?_, hO'⟩
    rw [hB' i hi, Nat.mod_eq_of_lt (show k - Ln < 2 ^ (p + 1) by omega_arith)]


structure OutI (u₀ : State) (o : Addr) (S : Addr) (V : Nat → Byte) (k j : Nat) (v : State) : Prop where
  keep : Keep [.rax, .r8] u₀ v
  r8 : v.gpr .r8 = BitVec.ofNat 64 j
  fr : Frame [⟨o, k⟩] u₀.mem v.mem
  out : ∀ i < j, v.mem (o + BitVec.ofNat 64 i) = V (oBuf + i)

/-- The buffer's first `k` bytes (at `rcx`) to `out`. -/
theorem copyOut_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (hcx : u.gpr .rcx = off S oBuf) {o : Addr} {k : Nat} (ho : W 21 = o)
    (hk : W 23 = BitVec.ofNat 64 k) (hk0 : 0 < k) (hk1 : k ≤ 1024) (hw : (⟨o, k⟩ : Region) ∈ u.wr)
    (hnw : o.toNat + k ≤ 2 ^ 64) (ha : Apart F S ⟨o, k⟩) :
    WP isa copyOut u fun u' => Lay u' F S ∧ Keep [.rdi, .r10, .rax, .r8] u u' ∧ Rep u'.mem F S V W ∧
      (∀ i < k, u'.mem (o + BitVec.ofNat 64 i) = V (oBuf + i)) ∧ Frame [⟨o, k⟩] u.mem u'.mem := by
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .r8] (Q := fun v => v.gpr .rdi = o ∧
      v.gpr .r10 = BitVec.ofNat 64 k ∧ v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl)
    fun v ⟨⟨h₁, h₂, h₄, hm⟩, hk'⟩ => ?_)
  · xrun [copyOut, VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sOut) (by decide), L.ld (d := sK) (by decide),
      R.slot (d := sOut) (k := 21) rfl (by decide) ho, R.slot (d := sK) (k := 23) rfl (by decide) hk]
  have hsc : Scr v o k := Scr.of_mem (by rw [hk'.2.2]; exact hw) hnw
  have Lv : Lay v F S := L.congr (hk'.gpr (by decide)) hk'.2.2 (by rw [hm])
  have hcv : v.gpr .rcx = off S oBuf := (hk'.gpr (by decide)).trans hcx
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (byteLoop_ok hk0 (stepR_ok (by omega_arith) v (show Reg.r10 ∉ [Reg.rax, .r8] by decide) (by decide) h₂)
    (OutI v o S V k) ?_ ⟨Keep.refl _ _, h₄, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun w I => ?_
  · intro j hj w I
    have hdw : w.gpr .rdi = o := (I.keep.gpr (by decide)).trans h₁
    have hcw : w.gpr .rcx = off S oBuf := (I.keep.gpr (by decide)).trans hcv
    have Rw : Rep w.mem F S V W := Rep.apart Rv ha I.fr
    have Lw : Lay w F S := Lv.congr (I.keep.gpr (by decide)) I.keep.2.2 (by
      rw [VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl, VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl,
        Rw.fr 14 (by decide), Rv.fr 14 (by decide)])
    have hst : InRegions w.wr (o + BitVec.ofNat 64 j) 1 := by
      have := hsc.st8 (d := j) (by omega_arith); rw [I.keep.2.2]; exact this
    have hb : w.mem (off S (oBuf + j)) = V (oBuf + j) := Rw.scr _ (by unfold oBuf oRsa; omega_arith)
    refine WP.mono (WP.keep [.rax] (Q := fun w' => w'.gpr .r8 = BitVec.ofNat 64 j ∧
        w'.mem = w.mem.writeW (o + BitVec.ofNat 64 j) (V (oBuf + j))) ?_ rfl)
      fun w' ⟨⟨h8', hm'⟩, k'⟩ => ⟨(I.keep.trans k').mono (by decide), h8', fun w'' k'' hm'' h8'' => ?_⟩
    · xrun [ea_ix, hdw, hcw, I.r8, off_plus, Lw.sld8 (d := oBuf + j) (by unfold oBuf oRsa; omega_arith), hb,
        show o + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = o + BitVec.ofNat 64 j from BitVec.add_zero _, hst,
        VG.Proof.RsaOaep.X86_64.trunc_zext]
    · refine ⟨(I.keep.trans (k'.trans k'')).mono (by decide), h8'', ?_, fun i hi => ?_⟩
      · rw [hm'', hm']
        exact I.fr.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
      · rw [hm'', hm', VG.WriteBytes.writeW8_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [ifn (Offset.add_ofNat_ne o (by omega_arith) (by omega_arith) h), I.out i (by omega_arith)]
  · have fr : Frame [⟨o, k⟩] u.mem w.mem := by rw [← hm]; exact I.fr
    have Rw : Rep w.mem F S V W := Rep.apart R ha fr
    refine ⟨L.congr ((I.keep.gpr (by decide)).trans (hk'.gpr (by decide))) (I.keep.2.2.trans hk'.2.2) ?_,
      (hk'.trans I.keep).mono (by decide), Rw, I.out, fr⟩
    rw [VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl, VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl,
      Rw.fr 14 (by decide), R.fr 14 (by decide)]


/-! ## After the call: the whole -/

/-- `Lay` with the permissions narrowed to the frame and our working space. -/
theorem lay_narrow {u : State} {F S : Addr} (L : Lay u F S) (rd : List Region) :
    Lay (u.withRegions rd [⟨F, frameBytes⟩, ⟨S, oRsa⟩]) F S :=
  ⟨L.rsp, List.mem_cons_self .., L.F8, L.Fw, Scr.of_mem (by simp) L.Sw, L.slot, L.dFS, L.dRS⟩

theorem lay_widen {v : State} {F S : Addr} {rd wr : List Region} (L : Lay (v.withRegions rd wr) F S)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ v.wr) (hsc : Scr v S oRsa) : Lay v F S :=
  ⟨L.rsp, hfr, L.F8, L.Fw, hsc, L.slot, L.dFS, L.dRS⟩

theorem scr_cov {u : State} {S : Addr} (h : Scr u S oRsa) : Covers [⟨S, oRsa⟩] u.wr := by
  obtain ⟨⟨B₀, o₀, L₀, hm, hb, hL, _⟩, _⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hm, o₀, hb, by simp only; omega_arith⟩

/-- A piece run with its permissions narrowed to the frame and our working
space, which it then changes memory only in. -/
theorem nar {c : Prog isa} (hn : c.noCalls = true) {u : State} {F S : Addr}
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ u.wr) (hsc : Scr u S oRsa) {P : State → Prop}
    (h : WP isa c (u.withRegions (u.rd ++ u.wr) [⟨F, frameBytes⟩, ⟨S, oRsa⟩]) P) :
    WP isa c u fun v => v.rd = u.rd ∧ v.wr = u.wr ∧ Frame [⟨F, frameBytes⟩, ⟨S, oRsa⟩] u.mem v.mem ∧
      P (v.withRegions (u.rd ++ u.wr) [⟨F, frameBytes⟩, ⟨S, oRsa⟩]) := by
  have hcw : Covers [⟨F, frameBytes⟩, ⟨S, oRsa⟩] u.wr := fun a n ⟨r, hr, hc⟩ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, hc⟩
    · exact scr_cov hsc a n ⟨_, List.mem_singleton_self _, hc⟩
  exact regionModel.wp_narrow h (Covers.append_left (fun _ _ h => h) (Covers.right hcw)) hcw
    (Code.noFrames_of_noCalls hn) (.inl hn) fun _ _ _ h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩

/-- The layout of the frame after `after`, from the precondition. -/
theorem lay_of {s u : State} (hp : DPre s) (hsp : u.gpr .rsp = F s) (hwr : u.wr = ⟨F s, frameBytes⟩ :: s.wr)
    (hsl : word u.mem (F s) 112 = stackArg s 15) : Lay u (F s) (stackArg s 15) := by
  have h1 := hp.sp1; have h2 := hp.sp2; have h3 := hp.hsl; have h4 := hp.k1; have h5 := hp.wS
  have hds : decStack = 3480 := rfl
  have hF : (F s).toNat = (s.gpr .rsp).toNat - 296 := by
    simp only [F, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega_arith
  have hS : (⟨stackArg s 15, oRsa⟩ : Region).Sub (Dec.scrR s) :=
    Region.sub_prefix (by unfold oRsa; omega_arith)
  have hfr : Region.Sub ⟨F s, 296⟩ (Dec.stkR s) := by
    have := slot3480 s (d := 0) (n := 296) (by decide); rwa [off, BitVec.add_zero] at this
  have hbr : Region.Sub (below (F s) 16) (Dec.stkR s) := fun x hx => by
    have := below_sub (sp := s.gpr .rsp) (a := 16 + 296) (b := 3480) (by decide) (by decide) x
      (below_below _ 296 16 x hx)
    rw [Dec.stkR, hds]; exact this
  rw [hds] at h1
  refine ⟨hsp, by rw [hwr]; exact List.mem_cons_self .., by omega_arith,
    by unfold frameBytes; omega_arith, ⟨⟨stackArg s 15, 0, (stackArg s 16).toNat * 8, ?_, by simp [off], ?_, ?_⟩,
      by unfold oRsa; omega_arith⟩, hsl, (hp.dKs.sub_left hfr).sub_right hS, (hp.dKs.sub_left hbr).sub_right hS⟩
  · rw [hwr, hp.hwr]; simp
  · unfold oRsa; omega_arith
  · omega_arith

/-- What the whole function leaves in its frame. -/
structure Fin (s v : State) : Prop where
  rsp : v.gpr .rsp = F s
  rd : v.rd = s.rd
  wr : v.wr = ⟨F s, 296⟩ :: s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → v.gpr r = s.gpr r
  mx : v.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] s.mem v.mem
  post : FPost s v.mem ((v.gpr .rax).setWidth 32)


/-! ## The message, first -/

theorem wordsAt_one (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 1 = [m.readW p 64] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]

theorem bytesAt_len (m : Mem) (p : Addr) (k : Nat) : (Spec.Rsa.bytesAt m p k).length = k := by
  simp [Spec.Rsa.bytesAt]

/-- What the callee leaves at `out` and `msg_len`: a message `M` after
zeros, and its length; and what the function must leave instead. -/
theorem shape {m : Mem} {out ml : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Proof.RsaPkcs1Enc.writtenMsgEnd m out ml k r o) :
    ∃ M : List Byte, M.length ≤ k ∧ Spec.Rsa.bytesAt m out k = List.replicate (k - M.length) 0 ++ M ∧
      m.readW ml 64 = BitVec.ofNat 64 M.length ∧
      ∀ m' : Mem, Spec.Rsa.bytesAt m' out k = M ++ List.replicate (k - M.length) 0 →
        m'.readW ml 64 = m.readW ml 64 → Spec.RsaPkcs1Enc.writtenMsg m' out ml k r o := by
  cases o with
  | ok M =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    have hl := congrArg List.length hb
    rw [bytesAt_len, List.length_append, List.length_replicate] at hl
    refine ⟨M, by omega_arith, hb, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, hb', ?_⟩⟩
    rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | invalid =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | fault =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]

theorem arg15_eq (s : State) : off (F s) 424 = stackArgAddr s 15 := by
  rw [off, F, show (424 : Nat) = 296 + 128 from rfl, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]
  rfl

/-- After the call, the function's own stack argument 15, `scratch`. -/
theorem arg15_ok {s t : State} (hp : DPre s) (hfr : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] s.mem t.mem)
    (hrd : t.rd = s.rd) :
    InRegions (t.rd ++ t.wr) (off (F s) 424) 8 ∧ t.mem.readW (off (F s) 424) 64 = stackArg s 15 := by
  obtain ⟨A, hA1, hA2, hA⟩ := hp.hra
  have hsp2 := hp.sp2
  have hsub : ∀ {B : Nat}, 136 ≤ B → Region.Sub ⟨stackArgAddr s 15, 8⟩ ⟨stackArgAddr s 0, B⟩ := fun hB =>
    Offset.sub (s.gpr .rsp) (d := 8 * (15 + 1)) (e := 8 * (0 + 1)) (by decide) (by omega_arith)
  rw [arg15_eq]
  refine ⟨⟨_, List.mem_append_left _ (by rw [hrd]; exact hA), Offset.contains (s.gpr .rsp) (d := 8 * (15 + 1))
    (n := 8) (e := 8 * (0 + 1)) (k := A) (by decide) (by omega_arith) (by omega_arith)⟩, ?_⟩
  refine hfr.readW (r := ⟨stackArgAddr s 15, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.dOa.sub_right (hsub (Nat.le_refl _))).symm
  · exact (hp.dMa.sub_right (hsub (Nat.le_refl _))).symm
  · exact (hp.dsa.sub_right (hsub (Nat.le_refl _))).symm
  · exact Offset.disjoint_below (s.gpr .rsp) (n := 3784) (d := 8 * (15 + 1)) (k := 8) (by omega_arith)

/-- `out`, apart from the frame, our working space and the stack below the
frame. -/
theorem apart_out {s : State} (hp : DPre s) :
    Apart (F s) (stackArg s 15) ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ := by
  have h3 := hp.hsl; have h4 := hp.k1
  have hS : (⟨stackArg s 15, oRsa⟩ : Region).Sub (Dec.scrR s) :=
    Region.sub_prefix (by unfold oRsa; omega_arith)
  have hfr : Region.Sub ⟨F s, 296⟩ (Dec.stkR s) := by
    have := slot3480 s (d := 0) (n := 296) (by decide); rwa [off, BitVec.add_zero] at this
  have hbr : Region.Sub (below (F s) 16) (Dec.stkR s) := fun x hx => by
    have := below_sub (sp := s.gpr .rsp) (a := 16 + 296) (b := 3480) (by decide) (by decide) x
      (below_below _ 296 16 x hx)
    rw [Dec.stkR, show decStack = 3480 from rfl]; exact this
  exact ⟨hp.dKo.sub_left hfr, (hp.dOs.sub_right hS).symm, hp.dKo.sub_left hbr⟩


theorem frame3480 (s : State) : Region.Sub ⟨F s, 296⟩ (Dec.stkR s) := by
  have := slot3480 s (d := 0) (n := 296) (by decide); rwa [off, BitVec.add_zero] at this

/-! ## After the call: the pieces, one by one -/

section
variable {s : State} (hp : DPre s)
include hp

theorem hS15 : (⟨stackArg s 15, oRsa⟩ : Region).Sub (Dec.scrR s) := by
  have h3 := hp.hsl; have hk1 := hp.k1
  exact Region.sub_prefix (by unfold oRsa; omega_arith)

theorem mlK {m₁ m₂ : Mem} (hf : Frame [⟨F s, frameBytes⟩, ⟨stackArg s 15, oRsa⟩] m₁ m₂) :
    m₂.readW (s.gpr .rdx) 64 = m₁.readW (s.gpr .rdx) 64 := by
  refine hf.readW (r := ⟨s.gpr .rdx, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.dKm.sub_left (frame3480 s)).symm
  · exact hp.dMs.sub_right (hS15 hp)

theorem outK {m₁ m₂ : Mem} (hf : Frame [⟨F s, frameBytes⟩, ⟨stackArg s 15, oRsa⟩] m₁ m₂) :
    ∀ i < (s.gpr .r8).toNat, m₂ (s.gpr .rdi + BitVec.ofNat 64 i) = m₁ (s.gpr .rdi + BitVec.ofNat 64 i) := by
  have hsi := hp.hsi
  refine fun i hi => hf.bytes (R := ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩) (fun r hr => ?_)
    (by show (s.gpr .r8).toNat ≤ 2 ^ 64; omega_arith) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := hp.dKo; rw [hsi] at this; exact (this.sub_left (frame3480 s)).symm
  · have := hp.dOs; rw [hsi] at this; exact this.sub_right (hS15 hp)

theorem frS {m₁ m₂ : Mem} (hf : Frame [⟨F s, frameBytes⟩, ⟨stackArg s 15, oRsa⟩] m₁ m₂) :
    Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] m₁ m₂ := hf.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stkF s, by simp, frame_stk s⟩
  · exact ⟨Dec.scrR s, by simp, hS15 hp⟩

end

/-- In the frame after the call: where the arguments' slots and `scratch`
are, and what changed. -/
structure En (s v : State) : Prop where
  rsp : v.gpr .rsp = F s
  rd : v.rd = s.rd
  wr : v.wr = ⟨F s, 296⟩ :: s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → v.gpr r = s.gpr r
  mx : v.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
  fr : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] s.mem v.mem
  w14 : word v.mem (F s) 112 = stackArg s 15
  w21 : word v.mem (F s) 168 = s.gpr .rdi
  w23 : word v.mem (F s) 184 = s.gpr .rsi
  w29 : word v.mem (F s) 232 = s.gpr .rdx

/-- What the call left in `m0`, with the result `R`: a message `M` at the end
of `out`, its length at `msg_len`, and what the function must leave instead. -/
structure Data (s : State) (m0 : Mem) (R : BitVec 64) (M : List Byte) : Prop where
  len : M.length ≤ (s.gpr .r8).toNat
  out : Spec.Rsa.bytesAt m0 (s.gpr .rdi) (s.gpr .r8).toNat = List.replicate ((s.gpr .r8).toNat - M.length) 0 ++ M
  ml : m0.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 M.length
  fin : ∀ m' : Mem, Spec.Rsa.bytesAt m' (s.gpr .rdi) (s.gpr .r8).toNat =
      M ++ List.replicate ((s.gpr .r8).toNat - M.length) 0 → m'.readW (s.gpr .rdx) 64 = m0.readW (s.gpr .rdx) 64 →
      Spec.RsaPkcs1Enc.writtenMsg m' (s.gpr .rdi) (s.gpr .rdx) (s.gpr .r8).toNat (R.setWidth 32) (CPost.decOf s)

/-- Between the pieces. -/
structure Mid (s v : State) (m0 : Mem) (R : BitVec 64) (M : List Byte) : Prop where
  en : En s v
  data : Data s m0 R M
  w30 : word v.mem (F s) 240 = R
  ml : v.mem.readW (s.gpr .rdx) 64 = m0.readW (s.gpr .rdx) 64

/-- The message, then zeros: what the function leaves at `out`. -/
abbrev tgt (s : State) (M : List Byte) : List Byte := M ++ List.replicate ((s.gpr .r8).toNat - M.length) 0

/-- After `after`, and after each piece. -/
def St0 (s v : State) : Prop := ∃ m0 R M, Mid s v m0 R M ∧
  ∀ i < (s.gpr .r8).toNat, v.mem (s.gpr .rdi + BitVec.ofNat 64 i) = m0 (s.gpr .rdi + BitVec.ofNat 64 i)
def St1 (s v : State) : Prop := ∃ m0 R M, Mid s v m0 R M ∧ v.gpr .rcx = off (stackArg s 15) oBuf ∧
  (∀ i < (s.gpr .r8).toNat, v.mem (s.gpr .rdi + BitVec.ofNat 64 i) = m0 (s.gpr .rdi + BitVec.ofNat 64 i)) ∧
  ∀ x < 2 * (s.gpr .r8).toNat, v.mem (off (stackArg s 15) (oBuf + x)) = 0
def St2 (s v : State) : Prop := ∃ m0 R M, Mid s v m0 R M ∧ v.gpr .rcx = off (stackArg s 15) oBuf ∧
  ∀ x < 2 * (s.gpr .r8).toNat, v.mem (off (stackArg s 15) (oBuf + x)) =
    if x < (s.gpr .r8).toNat then m0 (s.gpr .rdi + BitVec.ofNat 64 x) else 0
def St3 (s v : State) : Prop := ∃ m0 R M, Mid s v m0 R M ∧ v.gpr .rcx = off (stackArg s 15) oBuf ∧
  ∀ i < (s.gpr .r8).toNat, v.mem (off (stackArg s 15) (oBuf + i)) = (tgt s M).getD i 0
def St4 (s v : State) : Prop := ∃ m0 R M, Mid s v m0 R M ∧
  Spec.Rsa.bytesAt v.mem (s.gpr .rdi) (s.gpr .r8).toNat = tgt s M

theorem en_lay {s v : State} (hp : DPre s) (h : En s v) : Lay v (F s) (stackArg s 15) := lay_of hp h.rsp h.wr h.w14

theorem rep0 (v : State) (F S : Addr) :
    Rep v.mem F S (fun o => v.mem (off S o)) (fun j => word v.mem F (8 * j)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem getD_of {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `En` past a piece that changed memory only in the frame and our working
space, keeping the slots of the arguments and `scratch`. -/
theorem En.step {s v v' : State} (h : En s v) (hrsp : v'.gpr .rsp = v.gpr .rsp) (hrd : v'.rd = v.rd)
    (hwr : v'.wr = v.wr) (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → v'.gpr r = v.gpr r) (hmx : v'.mxcsr = v.mxcsr)
    (hf : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] v.mem v'.mem)
    (hw : ∀ d ∈ [112, 168, 184, 232], word v'.mem (F s) d = word v.mem (F s) d) : En s v' :=
  ⟨hrsp.trans h.rsp, hrd.trans h.rd, hwr.trans h.wr, fun r hr hr' => (hcs r hr hr').trans (h.cs r hr hr'),
    by rw [hmx]; exact h.mx, h.fr.trans hf, (hw 112 (by simp)).trans h.w14, (hw 168 (by simp)).trans h.w21,
    (hw 184 (by simp)).trans h.w23, (hw 232 (by simp)).trans h.w29⟩

theorem cs_keep {rs : List Reg} {v v' : State} (h : Keep rs v v')
    (hrs : ∀ r ∈ rs, r ∉ calleeSaved) : ∀ r ∈ calleeSaved, r ≠ .rsp → v'.gpr r = v.gpr r :=
  fun r hr _ => h.gpr fun h' => hrs r h' hr

/-- `after`: the call's result to `sR`, `scratch` to `sScr`. -/
theorem after_ok {s t : State} (hp : DPre s) (hc : Called s t) :
    WP isa (.block Impl.RsaPkcs1Enc.X86_64.Front.after) t (St0 s) := by
  have hsi := hp.hsi
  obtain ⟨M, hML, hbM, hmlM, hfin⟩ := shape hc.post
  obtain ⟨hain, haval⟩ := arg15_ok hp hc.fr hc.rd
  have c : ∀ d, d + 8 ≤ 296 → InRegions t.wr (off (F s) d) 8 := fun d hd =>
    ⟨_, by rw [hc.wr]; exact List.mem_cons_self .., Offset.contains_base _ hd (by omega_arith)⟩
  have h424 : (t.mem.writeW (off (F s) 240) (t.gpr .rax)).readW (off (F s) (296 + 8 + 8 * 15)) 64 = stackArg s 15 :=
    (word_ww _ _ _ (d := 424) (by decide) (by decide) (by decide)).trans haval
  refine WP.mono_mx (by decide) (WP.mono (WP.keep [.r11] (Q := fun u => u.mem = (t.mem.writeW (off (F s) 240)
      (t.gpr .rax)).writeW (off (F s) 112) (stackArg s 15)) ?_ rfl) fun u h => h) fun u ⟨hmu, ku⟩ hmx => ?_
  · xrun [h424, Impl.RsaPkcs1Enc.X86_64.Front.after, Impl.RsaOaep.X86_64.arg, Impl.RsaOaep.X86_64.frameBytes,
      Impl.RsaOaep.X86_64.sR, Impl.RsaOaep.X86_64.sScr, VG.Proof.RsaOaep.X86_64.ea_sp, hc.rsp, c 240 (by decide),
      c 112 (by decide), hain, haval]
  have hFu : Frame [⟨F s, frameBytes⟩, ⟨stackArg s 15, oRsa⟩] t.mem u.mem := by
    rw [hmu]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨t.mem, t.gpr .rax, M, ⟨⟨(ku.gpr (by decide)).trans hc.rsp, ku.2.1.trans hc.rd, ku.2.2.trans hc.wr,
    fun r hr hr' => (cs_keep ku (by decide) r hr hr').trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx, hc.fr.trans (frS hp hFu),
    by rw [hmu, word_writeW_self], ?_, ?_, ?_⟩, ⟨hML, hbM, hmlM, hfin⟩, ?_, mlK hp hFu⟩,
    fun i hi => outK hp hFu i hi⟩
  · rw [hmu, word_ww _ _ _ (by decide) (by decide) (by decide), word_ww _ _ _ (by decide) (by decide) (by decide)]
    exact hc.wOut
  · rw [hmu, word_ww _ _ _ (by decide) (by decide) (by decide), word_ww _ _ _ (by decide) (by decide) (by decide)]
    exact hc.wK
  · rw [hmu, word_ww _ _ _ (by decide) (by decide) (by decide), word_ww _ _ _ (by decide) (by decide) (by decide)]
    exact hc.wMl
  · rw [hmu, word_ww _ _ _ (by decide) (by decide) (by decide), word_writeW_self]

theorem words_of {v : State} {m' : Mem} {F S : Addr} {V' : Nat → Byte} {W : Nat → BitVec 64}
    (R' : Rep m' F S V' W) (hW : ∀ j < VG.Proof.RsaOaep.X86_64.nW, j ≠ 34 → W j = word v.mem F (8 * j)) :
    ∀ d ∈ [112, 168, 184, 232, 240], word m' F d = word v.mem F d := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact (R'.fr 14 (by decide)).trans (hW 14 (by decide) (by decide))
  · exact (R'.fr 21 (by decide)).trans (hW 21 (by decide) (by decide))
  · exact (R'.fr 23 (by decide)).trans (hW 23 (by decide) (by decide))
  · exact (R'.fr 29 (by decide)).trans (hW 29 (by decide) (by decide))
  · exact (R'.fr 30 (by decide)).trans (hW 30 (by decide) (by decide))

/-- `Mid` past a piece run narrowed to the frame and our working space. -/
theorem Mid.nar {s v v' : State} {m0 : Mem} {R : BitVec 64} {M : List Byte} (hp : DPre s) (h : Mid s v m0 R M)
    (hrsp : v'.gpr .rsp = v.gpr .rsp) (hrd : v'.rd = v.rd) (hwr : v'.wr = v.wr)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → v'.gpr r = v.gpr r) (hmx : v'.mxcsr = v.mxcsr)
    (hf : Frame [⟨F s, frameBytes⟩, ⟨stackArg s 15, oRsa⟩] v.mem v'.mem)
    (hw : ∀ d ∈ [112, 168, 184, 232, 240], word v'.mem (F s) d = word v.mem (F s) d) : Mid s v' m0 R M :=
  ⟨h.en.step hrsp hrd hwr hcs hmx (frS hp hf) fun d hd => hw d (by simp at hd ⊢; omega_arith), h.data,
    (hw 240 (by simp)).trans h.w30, (mlK hp hf).trans h.ml⟩

/-- The buffer cleared. -/
theorem clear_ok {s v : State} (hp : DPre s) (h : St0 s v) : WP isa clearBuf v (St1 s) := by
  obtain ⟨m0, R, M, hm, hout⟩ := h
  have hsi := hp.hsi; have hk1 := hp.k1; have hk2 := hp.k2
  have L := en_lay hp hm.en
  refine WP.mono_mx (by decide) (nar (by decide) L.fr L.sc (clearBuf_ok (lay_narrow L (v.rd ++ v.wr))
    (rep0 v (F s) (stackArg s 15)) (k := (s.gpr .r8).toNat)
    (by show word v.mem (F s) 184 = _; rw [hm.en.w23, ← hsi, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega_arith) hk2)) fun v1 ⟨hrd1, hwr1, hf1, L1', k1, hcx1, R1⟩ hmx => ?_
  have e : ∀ r, r ∉ [Reg.rcx, .rax, .r8, .r10] → v1.gpr r = v.gpr r := fun r hr => k1.gpr hr
  refine ⟨m0, R, M, hm.nar hp (e _ (by decide)) hrd1 hwr1 (fun r hr _ => e r (by
      intro h'; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp [calleeSaved] at hr)) hmx hf1
    (words_of R1 fun _ _ _ => rfl), hcx1, fun i hi => (outK hp hf1 i hi).trans (hout i hi),
    fun x hx => ?_⟩
  rw [show v1.mem (off (stackArg s 15) (oBuf + x)) = _ from R1.scr _ (by unfold oBuf oRsa; omega_arith)]
  simp only [clrV]
  rw [ifp (by unfold clrN; omega_arith)]

/-- `out` copied to the buffer. -/
theorem cin_ok {s v : State} (hp : DPre s) (h : St1 s v) : WP isa copyIn v (St2 s) := by
  obtain ⟨m0, R, M, hm, hcx, hout, hz⟩ := h
  have hsi := hp.hsi; have hk1 := hp.k1; have hk2 := hp.k2; have wO := hp.wO; have h3 := hp.hsl
  have L := en_lay hp hm.en
  refine WP.mono_mx (by decide) (nar (by decide) L.fr L.sc (copyIn_ok (lay_narrow L (v.rd ++ v.wr))
    (rep0 v (F s) (stackArg s 15)) hcx (o := s.gpr .rdi) (k := (s.gpr .r8).toNat) hm.en.w21
    (by show word v.mem (F s) 184 = _; rw [hm.en.w23, ← hsi, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega_arith) hk2 (fun i hi => ?_) (fun i hi j hj he => ?_)))
    fun v2 ⟨hrd2, hwr2, hf2, L2', k2, hcx2, R2⟩ hmx => ?_
  · refine ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, List.mem_append_left _ (List.mem_append_right _ ?_),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    rw [hm.en.wr, hp.hwr]; simp
  · refine hp.dOs (s.gpr .rdi + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_arith) (by omega_arith)) ?_
    rw [he]
    have wS := hp.wS
    exact (Offset.contains_base (stackArg s 15) (d := oBuf + 0 + j) (n := 1) (k := (stackArg s 16).toNat * 8)
      (by unfold oBuf; omega_arith) (by unfold oBuf; omega_arith))
  have e : ∀ r, r ∉ [Reg.rsi, .r10, .rax, .r8] → v2.gpr r = v.gpr r := fun r hr => k2.gpr hr
  refine ⟨m0, R, M, hm.nar hp (e _ (by decide)) hrd2 hwr2 (fun r hr _ => e r (by
      intro h'; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp [calleeSaved] at hr)) hmx hf2
    (words_of R2 fun _ _ _ => rfl), hcx2, fun x hx => ?_⟩
  rw [show v2.mem (off (stackArg s 15) (oBuf + x)) = _ from R2.scr _ (by unfold oBuf oRsa; omega_arith)]
  simp only [cpV]
  by_cases hxk : x < (s.gpr .r8).toNat
  · rw [ifp (by omega_arith), ifp hxk, show oBuf + x - (oBuf + 0) = x by omega_arith]
    exact hout x hxk
  · rw [ifn (by omega_arith), ifn hxk]
    exact hz x hx

/-- The buffer, shifted: the message, then zeros. -/
theorem shift_val {s : State} {M : List Byte} {m0 : Mem} (hML : M.length ≤ (s.gpr .r8).toNat)
    (hb : Spec.Rsa.bytesAt m0 (s.gpr .rdi) (s.gpr .r8).toNat = List.replicate ((s.gpr .r8).toNat - M.length) 0 ++ M)
    {V₀ : Nat → Byte} (hV : ∀ x < 2 * (s.gpr .r8).toNat, V₀ (oBuf + x) =
      if x < (s.gpr .r8).toNat then m0 (s.gpr .rdi + BitVec.ofNat 64 x) else 0)
    {i : Nat} (hi : i < (s.gpr .r8).toNat) :
    bufK V₀ (s.gpr .r8).toNat (i + ((s.gpr .r8).toNat - M.length)) = (tgt s M).getD i 0 := by
  have key : ∀ j (hj : j < (s.gpr .r8).toNat), m0 (s.gpr .rdi + BitVec.ofNat 64 j) =
      (List.replicate ((s.gpr .r8).toNat - M.length) 0 ++ M)[j]'(by simp; omega_arith) := fun j hj => by
    have := congrArg (fun l : List Byte => l[j]?) hb
    simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
    rw [List.getElem?_eq_getElem (by simp; omega_arith)] at this
    exact Option.some.inj this
  rw [getD_of (by simp; omega_arith), bufK]
  by_cases hiL : i < M.length
  · rw [ifp (by omega_arith : i + ((s.gpr .r8).toNat - M.length) < (s.gpr .r8).toNat), hV _ (by omega_arith),
      ifp (by omega_arith : i + ((s.gpr .r8).toNat - M.length) < (s.gpr .r8).toNat), key _ (by omega_arith),
      List.getElem_append_left hiL, List.getElem_append_right (by simp only [List.length_replicate]; omega_arith)]
    simp only [List.length_replicate, Nat.add_sub_cancel]
  · rw [List.getElem_append_right (by omega_arith), List.getElem_replicate, ifn (by omega_arith)]

theorem sh_ok {s v : State} (hp : DPre s) (h : St2 s v) : WP isa shift v (St3 s) := by
  obtain ⟨m0, R, M, hm, hcx, hV⟩ := h
  have hsi := hp.hsi; have hk1 := hp.k1; have hk2 := hp.k2
  have L := en_lay hp hm.en
  refine WP.mono_mx (by decide) (nar (by decide) L.fr L.sc (shift_ok (lay_narrow L (v.rd ++ v.wr))
    (rep0 v (F s) (stackArg s 15)) hcx (k := (s.gpr .r8).toNat) (Ln := M.length) (ml := s.gpr .rdx)
    (by show word v.mem (F s) 184 = _; rw [hm.en.w23, ← hsi, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hm.en.w29 ?_ (hm.ml.trans hm.data.ml) hm.data.len (by omega_arith) hk2 (fun x h1 h2 => ?_)))
    fun v3 ⟨hrd3, hwr3, hf3, L3', k3, hcx3, V, W', R3, hW', hB, hO⟩ hmx => ?_
  · refine ⟨⟨s.gpr .rdx, 8⟩, List.mem_append_left _ (List.mem_append_right _ ?_), Region.contains_self _ _⟩
    rw [hm.en.wr, hp.hwr]; simp
  · show v.mem (off (stackArg s 15) (oBuf + x)) = 0
    rw [hV x h2, ifn (by omega_arith)]
  have e : ∀ r, r ∉ [Reg.rax, .rcx, .rsi, .r11, .r9, .r8, .rdi, .rdx, .r10] → v3.gpr r = v.gpr r :=
    fun r hr => k3.gpr hr
  refine ⟨m0, R, M, hm.nar hp (e _ (by decide)) hrd3 hwr3 (fun r hr _ => e r (by
      intro h'; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved] at hr)) hmx hf3
    (words_of R3 hW'), hcx3, fun i hi => ?_⟩
  rw [show v3.mem (off (stackArg s 15) (oBuf + i)) = _ from R3.scr _ (by unfold oBuf oRsa; omega_arith),
    hB i (by omega_arith)]
  exact shift_val hm.data.len hm.data.out (fun x hx => hV x hx) hi

theorem bytes_getD {m : Mem} {p : Addr} {k : Nat} {T : List Byte} (hT : T.length = k)
    (h : ∀ i < k, m (p + BitVec.ofNat 64 i) = T.getD i 0) : Spec.Rsa.bytesAt m p k = T := by
  refine List.ext_getElem (by simp [Spec.Rsa.bytesAt, hT]) fun i h1 h2 => ?_
  have hi : i < k := by simpa [Spec.Rsa.bytesAt] using h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i hi, getD_of h2]

theorem cout_ok {s v : State} (hp : DPre s) (h : St3 s v) : WP isa copyOut v (St4 s) := by
  obtain ⟨m0, R, M, hm, hcx, hT⟩ := h
  have hsi := hp.hsi; have hk1 := hp.k1; have hk2 := hp.k2; have wO := hp.wO; have hML := hm.data.len
  have L := en_lay hp hm.en
  have hw : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) ∈ v.wr := by rw [hm.en.wr, hp.hwr, ← hsi]; simp
  refine WP.mono_mx (by decide) (copyOut_ok L (rep0 v (F s) (stackArg s 15)) hcx (o := s.gpr .rdi)
    (k := (s.gpr .r8).toNat) hm.en.w21
    (by show word v.mem (F s) 184 = _; rw [hm.en.w23, ← hsi, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (by omega_arith) hk2 hw (by omega_arith) (by have := apart_out hp; rwa [hsi] at this))
    fun v4 ⟨L4, k4, R4, hout4, hf4⟩ hmx => ?_
  have e : ∀ r, r ∉ [Reg.rdi, .r10, .rax, .r8] → v4.gpr r = v.gpr r := fun r hr => k4.gpr hr
  have hfr : Frame [Dec.outR s, Dec.mlR s, Dec.scrR s, stkF s] v.mem v4.mem := hf4.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨Dec.outR s, by simp, by rw [Dec.outR, hsi]; exact fun _ h => h⟩
  have hw' : ∀ d ∈ [112, 168, 184, 232, 240], word v4.mem (F s) d = word v.mem (F s) d :=
    words_of R4 fun _ _ _ => rfl
  refine ⟨m0, R, M, ⟨hm.en.step (e _ (by decide)) k4.2.1 k4.2.2 (fun r hr _ => e r (by
      intro h'; simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> simp [calleeSaved] at hr)) hmx hfr
      fun d hd => hw' d (by simp at hd ⊢; omega_arith), hm.data, (hw' 240 (by simp)).trans hm.w30, ?_⟩,
    bytes_getD (by simp; omega_arith) fun i hi => (hout4 i hi).trans (hT i hi)⟩
  rw [hf4.readW (r := ⟨s.gpr .rdx, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; have := hp.dOm; rw [hsi] at this; exact this.symm) (by decide)]
  exact hm.ml

theorem ret_ok {s v : State} (hp : DPre s) (h : St4 s v) : WP isa (.block Impl.RsaPkcs1Enc.X86_64.Front.ret) v (Fin s) := by
  obtain ⟨m0, R, M, hm, hb⟩ := h
  have L := en_lay hp hm.en
  refine WP.mono_mx (by decide) (WP.mono (WP.keep [.rax] (Q := fun v5 => v5.gpr .rax = R ∧ v5.mem = v.mem) ?_ rfl)
    fun v5 h => h) fun v5 ⟨⟨hax, hm5⟩, k5⟩ hmx => ?_
  · xrun [Impl.RsaPkcs1Enc.X86_64.Front.ret, VG.Proof.RsaOaep.X86_64.ea_sp, L.rsp, L.ld (d := sR) (by decide),
      (rep0 v (F s) (stackArg s 15)).slot (d := sR) (k := 30) rfl (by decide) hm.w30]
  refine ⟨(k5.gpr (by decide)).trans hm.en.rsp, k5.2.1.trans hm.en.rd, k5.2.2.trans hm.en.wr,
    fun r hr hr' => (cs_keep k5 (by decide) r hr hr').trans (hm.en.cs r hr hr'), by rw [hmx]; exact hm.en.mx,
    by rw [hm5]; exact hm.en.fr, ?_⟩
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ _
  rw [hax, hm5]
  exact hm.data.fin v.mem hb hm.ml

/-- After the call, the rest. -/
theorem tail_ok {s t : State} (hp : DPre s) (hc : Called s t) :
    WP isa (.seq (.block Impl.RsaPkcs1Enc.X86_64.Front.after) Impl.RsaPkcs1Enc.X86_64.Front.tail) t (Fin s) := by
  rw [show Impl.RsaPkcs1Enc.X86_64.Front.tail = .seq (.seq clearBuf (.seq copyIn shift))
    (.seq copyOut (.block Impl.RsaPkcs1Enc.X86_64.Front.ret)) from rfl]
  exact WP.seq (WP.mono (after_ok hp hc) fun u h0 => WP.seq (WP.seq (WP.mono (clear_ok hp h0) fun v1 h1 =>
    WP.seq (WP.mono (cin_ok hp h1) fun v2 h2 => WP.mono (sh_ok hp h2) fun v3 h3 =>
      WP.seq (WP.mono (cout_ok hp h3) fun v4 h4 => ret_ok hp h4)))))

/-! ## The function -/

/-- The precondition, with less of the stack. -/
theorem pre_stack {Q : sig.Post abi.ptrBits} {n n' : Nat} (hn : n ≤ n') {s : State} (h : (C Q n').pre s) :
    (C Q n).pre s := by
  unfold C at h ⊢
  rw [pre_args hk] at h ⊢
  obtain ⟨⟨hs, hwf⟩, hr, hw, hpw, hd, hb, ht⟩ := h
  refine ⟨⟨?_, hwf⟩, hr, hw, hpw, ?_, hb, ht⟩
  · right; rcases hs with hs | hs <;> omega_arith
  · intro r hr a ha
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact hd _ (List.mem_cons_self ..) a ha
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [stackBelow] at hr
      · rw [stackBelow_pos _ h0, List.mem_singleton] at hr
        subst hr
        have hn0 : 0 < n' := by omega_arith
        refine (hd (below (s.gpr .rsp) n') (List.mem_cons_of_mem _ (by rw [stackBelow_pos _ hn0]; simp)) a ha).sub_left
          (below_sub hn (by rcases hs with hs | hs <;> omega_arith))

theorem dpre_of {Q : sig.Post abi.ptrBits} {s : State} (h : (C Q 3784).pre s) : DPre s :=
  (Dec.dPreP_of (pre_post (pre_stack (show 3480 ≤ 3784 by decide) h))).1

/-- `writtenMsg` of buffers apart from regions, whatever the regions hold. -/
theorem writtenMsg_frame {regions : List Region} {m m' : Mem} {out ml : Addr} {n : Nat} {r : BitVec 32}
    {o : Spec.Rsa.Outcome} (f : Frame regions m m') (fit : n < 2 ^ 64)
    (sepO : ∀ q ∈ regions, (⟨out, n⟩ : Region).Disjoint q)
    (sepM : ∀ q ∈ regions, (⟨ml, 8 * 1⟩ : Region).Disjoint q)
    (h : Spec.RsaPkcs1Enc.writtenMsg m out ml n r o) : Spec.RsaPkcs1Enc.writtenMsg m' out ml n r o := by
  have hb := Proof.Rsa.rsa_bytes_frame f fit sepO
  have hw := Proof.Rsa.wordsAt_frame f (n := 1) (by decide) sepM
  cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsg] at h ⊢ <;> rw [hb, hw] <;> exact h

/-- The function, from a state its contract allows, meets its
postcondition. -/
theorem front_ok {name : String} {callee : Prog isa}
    (hv : ∀ s, (C postP 3480).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (C postP 3480).post s s')
    (hsafe : SpSafe callee) (hd : callee.x86_64Depth ≤ 3480) {s : State} (hs : (C postFP 3784).pre s) :
    WP isa (Impl.RsaPkcs1Enc.X86_64.Front.code name callee) s fun s' => abiPreserved s s' ∧ (C postFP 3784).post s s' := by
  have hp := dpre_of hs
  have hsp1 := hp.sp1; have hsp2 := hp.sp2; have hsi := hp.hsi
  have hds : decStack = 3480 := rfl
  rw [hds] at hsp1
  refine alloc_frame_ok (by decide) (by unfold Impl.RsaOaep.X86_64.frameBytes; omega_arith) ?_
  refine WP.seq (WP.mono (setup_ok hs) fun t1 ht1 => ?_)
  subst ht1
  refine WP.seq (WP.mono (call_ok (name := name) hv hsafe hd hs hp) fun t2 hc2 => ?_)
  refine WP.mono (tail_ok hp hc2) fun v hv => ⟨by rw [hv.rsp, allocState_rsp']; rfl, by rw [hv.wr]; rfl, fun m u hm => ?_⟩
  have sep : ∀ {R : Region}, (Dec.stkR s).Disjoint R →
      ∀ q ∈ [(⟨s.gpr .rsp - BitVec.ofNat 64 296, 296⟩ : Region)], R.Disjoint q := fun hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    exact (hd.sub_left (frame3480 s)).symm
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show v.gpr .rsp + BitVec.ofNat 64 296 = s.gpr .rsp
      rw [hv.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else v.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      exact hv.cs r hr hr'
  · show m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
    rw [hm.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact Offset.base_disjoint_below _ (by decide)) (by decide)]
    refine hv.fr.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun q hq => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hp.dRo
    · exact hp.dRm
    · exact hp.dRs
    · exact Offset.base_disjoint_below _ (by decide)
  · exact hv.mx
  · unfold C
    rw [post_args hk]
    refine fpost_to ?_
    have hpost := hv.post
    have dKo := hp.dKo
    rw [hsi] at dKo
    exact writtenMsg_frame hm (s.gpr .r8).isLt (sep dKo) (sep hp.dKm) hpost


/-! ## Constant time: the blocks -/

theorem setup_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block Impl.RsaPkcs1Enc.X86_64.Front.setup) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem after_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block Impl.RsaPkcs1Enc.X86_64.Front.after) hc).isSome = true :=
  ⟨_, by taint_decide⟩



/-! ## Constant time -/

/-- The regions of the callee's contract, and the state before the call. -/
abbrev RD (s : State) : List Region := ((fwdRegions sig 296 s).filter (!·.2)).map (·.1)
abbrev WR (s : State) : List Region := ((fwdRegions sig 296 s).filter (·.2)).map (·.1)
abbrev tS (s : State) : State := withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))

/-- The callee's entry, from `setup`'s state: its precondition, its
permissions within ours, its arguments ours, in memory ours in our buffers. -/
theorem entry_ok {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3784).pre s) :
    (C postP 3480).pre ((withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))) ∧
    Covers ((((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) ++ (((fwdRegions sig 296 s).filter (·.2)).map (·.1))) ((withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).rd ++ (withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).wr) ∧ Covers (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) (withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).wr ∧
    allArgs sig ((withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))) = allArgs sig s ∧
    (∀ b ∈ Sig.bufs sig.params (allArgs sig s), ∀ a, b.1.Contains a 1 →
      s.mem a = ((withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))).mem a) ∧
    (withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).gpr .rsp = F s ∧ ((withMem (fwdState sig 296 s) (stashMem (fwdState sig 296 s))).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))).mxcsr = s.mxcsr := by
  have hs' : (C postP (3480 + 296 + 8)).pre s := pre_post hs
  obtain ⟨-, hrd', hwr', hmxw, -, hg, -, -⟩ := fwdState_run (stack := 3480) (bytes := 296) hs' hk (by decide) (by decide)
  have hargsN := (narrowF_facts (stack := 3480) (bytes := 296) hk (by decide) (by decide) hs').2.2.2.1
  have hall := allRegions_narrowF (stack := 3480) (bytes := 296) hk (by decide) (by decide) (by decide) hs'
  have hout := fwd_out (stack := 3480) (bytes := 296) hk hs'
  have hagN := narrowF_agree (stack := 3480) (bytes := 296) hk (by decide) (by decide) hs'
  have hpreN := narrowF_pre (stack := 3480) (bytes := 296) hk (by decide) (by decide) (by decide) preP_local hs'
  generalize hw : fwdState sig 296 s = w at hrd' hwr' hmxw hg hagN hpreN hargsN
  have hwrsp : w.gpr .rsp = F s := (hg .rsp (by decide)).trans (allocState_rsp' _ _)
  have hN : narrowF sig 296 s = w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) := by rw [← hw]; rfl
  rw [hN] at hall hagN hpreN hargsN
  have hZs : Frame [Z s] w.mem (stashMem w) := by
    have c : ∀ d, 152 ≤ d → d + 8 ≤ 296 → (Z s).Contains (off (w.gpr .rsp) d) 8 := fun d h1 h2 => by
      rw [hwrsp]; exact Offset.contains (F s) (e := 152) (k := 144) h1 (by omega_arith) (by omega_arith)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 168 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 184 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (c 232 (by decide) (by decide))
  have hentry : (withMem w (stashMem w)).callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) =
      withMem (w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))) ((stashMem w).writeW (w.gpr .rsp - 8) (w.unknowns 0)) := rfl
  have hZe : Frame [Z s] (w.callEntry.withRegions (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) (((fwdRegions sig 296 s).filter (·.2)).map (·.1))).mem
      ((stashMem w).writeW (w.gpr .rsp - 8) (w.unknowns 0)) := frame_ww hZs _ _
  have hZd : ∀ a ∈ fwdRegions sig 296 s, a.1.Disjoint (Z s) := by
    intro a ha
    simp only [fwdRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · rw [Z_eq]; exact hout a ha (by decide) (by decide)
    · rw [nStack_eq, Z]
      exact Offset.base_disjoint (F s) (k := 152) (e := 152) (n := 144) (Nat.le_refl _) (by decide)
  have hpre := pre_like hpreN hZe (by rw [hall]; exact hZd)
  have hargsE := (allRegions_like hZe (by rw [hall]; exact hZd)).1
  rw [hargsN] at hargsE
  rw [← hentry] at hpre hargsE
  have hs'' := hs'
  rw [pre_args hk] at hs''
  obtain ⟨-, hrd, hwr, -, -, -, -⟩ := hs''
  have hbufR : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = false → a.1 ∈ s.rd := fun a ha h => by
    rw [hrd]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha),
      by simp [h]⟩, rfl⟩
  have hbufW : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), a.2 = true → a.1 ∈ s.wr := fun a ha h => by
    rw [hwr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ ha), h⟩,
      rfl⟩
  have hcovW : Covers (((fwdRegions sig 296 s).filter (·.2)).map (·.1)) (withMem w (stashMem w)).wr := by
    rw [withMem_wr, hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact List.mem_cons_of_mem _ (hbufW a ha hf')
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha; simp at hf'
    · simp at hf'
  have hcovR : Covers (((fwdRegions sig 296 s).filter (!·.2)).map (·.1)) ((withMem w (stashMem w)).rd ++ (withMem w (stashMem w)).wr) := by
    rw [withMem_rd, withMem_wr, hrd', hwr']
    refine Covers.of_forall fun r hr => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, hf'⟩ := List.mem_filter.mp ha
    simp only [fwdRegions, bufRegions, List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact Covers.left (Covers.of_mem fun x hx => by
        simp only [List.mem_singleton] at hx; subst hx; exact hbufR a ha (by simpa using hf'))
    · rw [Sig.lists_of_noLists _ _ _ _ hnl] at ha; simp at ha
    · exact Covers.right (Covers.one ⟨_, List.mem_cons_self .., Offset.contains_below _ (a := 296)
        (b := 296) (Nat.le_refl _) (by rw [nStack_eq]; decide) (by decide)⟩)
  refine ⟨hpre, Covers.append_left hcovR (Covers.right hcovW), hcovW, hargsE, fun b hb' a ha => ?_, hwrsp, ?_⟩
  · rw [hentry, withMem_mem, hZe a fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact hZd b (List.mem_append_left _ (List.mem_append_left _ hb')) a ha hc]
    exact (hagN b hb' a ha).symm
  · rw [State.withRegions_mxcsr, State.callEntry_mxcsr, withMem_mxcsr]
    exact hmxw

/-- What two states a contract relates agree on. -/
theorem pub_regs {s₁ s₂ : State} (h : (C postFP 3784).pub s₁ s₂) :
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ stackArg s₁ 15 = stackArg s₂ 15 ∧ stackArg s₁ 16 = stackArg s₂ 16 ∧
      s₁.mxcsr = s₂.mxcsr := by
  have hmx := ((pubL_args hk).mp h).1.1.2
  have h' : (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3784).pub s₁ s₂ := h
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    abi, argRegs, args19, List.append_eq, List.range, List.range.loop] at h'
  obtain ⟨hsp, -, hdi, hsi, hdx, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a15, a16, -⟩ := h'
  exact ⟨hsp, hdi, hsi, hdx, a15, a16, hmx⟩

/-- Two runs, each from a state of the contract, related by its public data,
and each in a state `G` says of its own. -/
def Rel (G : State → State → Prop) (a b : State) : Prop :=
  ∃ s₁ s₂, (C postFP 3784).pre s₁ ∧ (C postFP 3784).pre s₂ ∧ (C postFP 3784).pub s₁ s₂ ∧ G s₁ a ∧ G s₂ b

theorem rel_step {G G' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Rel G) c fun _ _ => True)
    (hw : ∀ s t, (C postFP 3784).pre s → G s t → WP isa c t (G' s)) : RelCT isa (Rel G) c (Rel G') := by
  intro t₁ t₂ τ₁ τ₂ t₁' t₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, p₁, p₂, hpub, g₁, g₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ t₁ p₁ g₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ t₂ p₂ g₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, s₁, s₂, p₁, p₂, hpub, y₁, y₂⟩

open VG.Proof.RsaOaep.X86_64 (FrV frT frT_agree) in
theorem frv_of {s v : State} (hp : DPre s) (h : En s v) : FrV 3 (F s) s.wr v := by
  have hsi := hp.hsi
  refine ⟨h.rsp, h.wr, by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h => absurd h List.not_mem_nil) .nil)))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.dKo.sub_left (frame3480 s)
      · exact hp.dKm.sub_left (frame3480 s)
      · exact hp.dKs.sub_left (frame3480 s)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dOm
      · exact hp.dOs
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact hp.dMs
  · intro r hr
    rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Nat.le_of_lt (BitVec.isLt _)
    · show 8 ≤ 2 ^ 64; decide
    · have := hp.wS; simp only; omega_arith

open VG.Proof.RsaOaep.X86_64 (FrV frT frT_agree) in
/-- A piece the taint analysis checks from the frame, its slots of the
arguments and `scratch` and the registers `rs` public, in two runs. -/
theorem rel_frT {G : State → State → Prop} (hG : ∀ s v, G s v → En s v) (rs : List Reg)
    (hr : ∀ s₁ s₂ t₁ t₂, (C postFP 3784).pub s₁ s₂ → G s₁ t₁ → G s₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    {c : Prog isa} (h : ∃ hc, (taint.check (frT rs [14, 21, 23, 29] 3) c hc).isSome = true) :
    RelCT isa (Rel G) c fun _ _ => True := by
  obtain ⟨_, h⟩ := h
  refine RelCT.taint (A := taint) (frT rs [14, 21, 23, 29] 3) (fun t₁ t₂ ⟨s₁, s₂, p₁, p₂, hpub, g₁, g₂⟩ => ?_) h
  have e₁ := hG _ _ g₁
  have e₂ := hG _ _ g₂
  have hp₁ := dpre_of p₁
  have hp₂ := dpre_of p₂
  obtain ⟨hsp, hdi, hsi, hdx, a15, a16, -⟩ := pub_regs hpub
  have hF : F s₁ = F s₂ := by simp only [F, hsp]
  have hw : s₁.wr = s₂.wr := by rw [hp₁.hwr, hp₂.hwr, hdi, hsi, hdx, a15, a16]
  refine frT_agree (frv_of hp₁ e₁) (hw ▸ hF ▸ frv_of hp₂ e₂) (hr _ _ _ _ hpub g₁ g₂) (by decide) fun k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [e₁.w14, hF, e₂.w14, a15]
  · rw [e₁.w21, hF, e₂.w21, hdi]
  · rw [e₁.w23, hF, e₂.w23, hsi]
  · rw [e₁.w29, hF, e₂.w29, hdx]

theorem rel_rsp {G : State → State → Prop} (hG : ∀ s v, G s v → v.gpr .rsp = F s) {c : Prog isa}
    (h : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) c hc).isSome = true) : RelCT isa (Rel G) c fun _ _ => True := by
  obtain ⟨_, h⟩ := h
  refine RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun t₁ t₂ ⟨s₁, s₂, p₁, p₂, hpub, g₁, g₂⟩ =>
    Taint.agree_ofRegs fun r hr => ?_) h
  rw [List.mem_singleton.mp hr, hG _ _ g₁, hG _ _ g₂, F, F, (pub_regs hpub).1]

open VG.Proof.RsaOaep.X86_64 (frT) in
theorem clear_taint : ∃ hc, (taint.check (frT [] [14, 21, 23, 29] 3) clearBuf hc).isSome = true :=
  ⟨_, by taint_decide⟩

open VG.Proof.RsaOaep.X86_64 (frT) in
theorem cin_taint : ∃ hc, (taint.check (frT [.rcx] [14, 21, 23, 29] 3) copyIn hc).isSome = true :=
  ⟨_, by taint_decide⟩

open VG.Proof.RsaOaep.X86_64 (frT) in
theorem sh_taint : ∃ hc, (taint.check (frT [.rcx] [14, 21, 23, 29] 3) shift hc).isSome = true :=
  ⟨_, by taint_decide⟩

open VG.Proof.RsaOaep.X86_64 (frT) in
theorem out_taint : ∃ hc, (taint.check (frT [.rcx] [14, 21, 23, 29] 3)
    (.seq copyOut (.block Impl.RsaPkcs1Enc.X86_64.Front.ret)) hc).isSome = true :=
  ⟨_, by taint_decide⟩


/-- The function is constant time but for its public data. -/
theorem front_ct {name : String} {callee : Prog isa}
    (hv : ∀ s, (C postP 3480).pre s → ∃ t s', Exec isa callee s t s' ∧ abiPreserved s s' ∧ (C postP 3480).post s s')
    (hct : ConstantTime isa (C postP 3480).pre (C postP 3480).pub callee)
    (hsafe : SpSafe callee) (hd : callee.x86_64Depth ≤ 3480) :
    ConstantTime isa (C postFP 3784).pre (C postFP 3784).pub (Impl.RsaPkcs1Enc.X86_64.Front.code name callee) := by
  refine RelCT.constantTime (RelCT.alloc ((?_ : RelCT isa (Rel fun s t => t = allocState 296 s) _ fun _ _ => True).mono
    (fun a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, e₁, e₂⟩ => ⟨s₁, s₂, h₁, h₂, hp, e₁, e₂⟩) fun _ _ _ => trivial))
  rw [show Impl.RsaPkcs1Enc.X86_64.Front.body name callee = .seq (.block Impl.RsaPkcs1Enc.X86_64.Front.setup)
    (.seq (.call name callee) (.seq (.block Impl.RsaPkcs1Enc.X86_64.Front.after)
      (.seq (.seq clearBuf (.seq copyIn shift)) (.seq copyOut (.block Impl.RsaPkcs1Enc.X86_64.Front.ret)))))
    from rfl]
  have rcx : ∀ {G : State → State → Prop}, (∀ s v, G s v → v.gpr .rcx = off (stackArg s 15) oBuf) →
      ∀ s₁ s₂ t₁ t₂, (C postFP 3784).pub s₁ s₂ → G s₁ t₁ → G s₂ t₂ → ∀ r ∈ [Reg.rcx], t₁.gpr r = t₂.gpr r :=
    fun hG s₁ s₂ t₁ t₂ hpub g₁ g₂ r hr => by
      rw [List.mem_singleton.mp hr, hG _ _ g₁, hG _ _ g₂, (pub_regs hpub).2.2.2.2.1]
  refine RelCT.seq (rel_step (G' := fun s t => t = tS s) (rel_rsp (fun s t h => by rw [h, allocState_rsp']) setup_taint)
    fun s t hs h => by subst h; exact setup_ok hs) ?_
  refine RelCT.seq (rel_step (G' := Called) (RelCT.callEx (k := C postP 3480) hv hct
      fun t₁ t₂ ⟨s₁, s₂, p₁, p₂, hpub, e₁, e₂⟩ => ?_)
    fun s t hs h => by subst h; exact call_ok hv hsafe hd hs (dpre_of hs)) ?_
  · subst e₁ e₂
    obtain ⟨pr₁, c₁, w₁, a₁, b₁, r₁, m₁⟩ := entry_ok p₁
    obtain ⟨pr₂, c₂, w₂, a₂, b₂, r₂, m₂⟩ := entry_ok p₂
    obtain ⟨hsp, -, -, -, -, -, hmx⟩ := pub_regs hpub
    refine ⟨_, _, _, _, pr₁, pr₂, pub_of p₁ p₂ hpub a₁ a₂ b₁ b₂ ?_ (by rw [m₁, m₂, hmx]), c₁, w₁, c₂, w₂, ?_⟩
    · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, r₁, r₂, F, F, hsp]
    · rw [r₁, r₂, F, F, hsp]
  refine RelCT.seq (rel_step (G' := St0) (rel_rsp (fun s t h => h.rsp) after_taint)
    fun s t hs h => after_ok (dpre_of hs) h) ?_
  refine RelCT.seq (RelCT.seq (rel_step (G' := St1) (rel_frT (fun s v ⟨_, _, _, hm, _⟩ => hm.en) []
      (fun _ _ _ _ _ _ _ r hr => absurd hr List.not_mem_nil) clear_taint)
      fun s t hs h => clear_ok (dpre_of hs) h)
    (RelCT.seq (rel_step (G' := St2) (rel_frT (fun s v ⟨_, _, _, hm, _⟩ => hm.en) [.rcx]
        (rcx fun s v ⟨_, _, _, _, h, _⟩ => h) cin_taint) fun s t hs h => cin_ok (dpre_of hs) h)
      (rel_step (G' := St3) (rel_frT (fun s v ⟨_, _, _, hm, _⟩ => hm.en) [.rcx]
        (rcx fun s v ⟨_, _, _, _, h, _⟩ => h) sh_taint) fun s t hs h => sh_ok (dpre_of hs) h))) ?_
  exact rel_frT (fun s v ⟨_, _, _, hm, _⟩ => hm.en) [.rcx] (rcx fun s v ⟨_, _, _, _, h, _⟩ => h) out_taint

/-- A state that meets the contract: `vg_rsa_pkcs1_decrypt_precomputed_body`'s. -/
theorem satF : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3784).pre s := by
  refine ⟨Dec.preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    abi, argRegs, args19, List.append_eq]
  obtain ⟨-, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := Dec.pre_args
  have ha : stackArgAddr Dec.preState 0 = 0x10008 := by decide
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, ha]
  sig_and_intros
  rotate_right
  · rw [show BitVec.toNat (64 : BitVec 64) = 64 from rfl, show BitVec.toNat (32 : BitVec 64) = 32 from rfl,
      show BitVec.toNat (24 : BitVec 64) = 24 from rfl]
    exact Dec.preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-- `vg_rsa_pkcs1_decrypt_precomputed` on x86-64, calling code
verified as `vg_rsa_pkcs1_decrypt_precomputed_body` with 3480 bytes of stack,
meets its contract with 3784. -/
theorem front_verified {name : String} {callee : Prog isa}
    (h : Verified target callee (Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract abi 3480))
    (hsp : callee.all (fun i => !isa.writesSp i) = true) (hd : callee.x86_64Depth ≤ 3480) :
    Verified target (Impl.RsaPkcs1Enc.X86_64.Front.code name callee)
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3784) := by
  rw [cK_eq] at h
  obtain ⟨hv, hct, -⟩ := h
  have hsafe := SpSafe.of_all hsp
  exact ⟨fun s hs => front_ok hv hsafe hd hs, front_ct hv hct hsafe hd, satF⟩

end

end VG.Proof.RsaPkcs1Enc.X86_64.Front
