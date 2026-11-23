module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Front
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Shift
import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Front
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract

/-!
# `vg_rsa_pkcs1_decrypt_precomputed` on RISC-V

`Front.code` (`Impl/RsaPkcs1Enc/RISCV64/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedContract` with 3632 bytes of stack
(`front_verified`), for any callee verified against
`Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract` with 3456 whose frames use at
most that (`sdepth`): its proof is used only through that contract. The
function as emitted, with its cleanup, is `decryptPrecomputed`.

**The call.** `setup` copies the 17 stack arguments to the bottom of the
frame (`copyArg`, `copies_run`), and stores the return address, `out`, `k`
and `msg_len` in the slots above them (`Stashed`). The callee runs with the
permissions of its own contract: the buffers, and the copies, read only
(`cAll`). Its precondition, public data and postcondition read memory only
within the buffers (`preP_local`, `leakP_local`, `postP_local`), which lie
apart from the frame, so they are those of our arguments (`entry_pre`,
`entry_pub`); it writes only its writable buffers and the stack below the
frame (`WP.callAny`), so the slots and our stack arguments are as they were
(`call_ok`, `Called`).

**After the call.** In registers loaded once (`load_ok`, `Base`): the buffer
at `scratch` cleared, `out` copied to it, shifted by `k - L` in eleven passes
(`pass_ok`, `shift_ok`: RSASSA-PSS verification's `passV` and `shV`, and
`shV_in11`), which leaves the message and zeros (`shifted`), and copied back
(`tail_ok`). `msg_len` and the result stay as the call left them
(`front_wp`).

**Constant time.** Two runs whose arguments agree where the contract says
they are public (`Dec.same_ofP`): the blocks by the taint analysis, from the
stack pointer or from `scratch`, `out`, `k` and `msg_len`, the call by the
callee's constant time (`front_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Front

open VG VG.RISCV64

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

theorem hk : (sig.words abi.ptrBits).length = 8 + 17 := by decide
theorem hnl : Sig.noLists sig.params = true := by decide

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
  match vs, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
      a23, a24], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21,
      a22, a23, a24, rfl⟩

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


/-! ## The contracts -/

/-- The contracts, with any postcondition `Q`. -/
abbrev C (Q : sig.Post abi.ptrBits) (n : Nat) : Contract isa := sig.contract abi preP Q true n (some leakP)

theorem pre_post {Q Q' : sig.Post abi.ptrBits} {n : Nat} {s : State} (h : (C Q n).pre s) : (C Q' n).pre s := h

theorem args_length (s : State) : (stkArgs 17 s).length = (sig.words abi.ptrBits).length := by
  rw [stkArgs_length, hk]

/-! ## The frame -/

/-- The frame's base. -/
abbrev E (s : State) : Addr := s.sp - BitVec.ofNat 64 176

/-- The stack the function uses. -/
abbrev stk (s : State) : Region := below s.sp 3632

theorem E_off (s : State) (d : Nat) : E s + BitVec.ofNat 64 (176 + d) = s.sp + BitVec.ofNat 64 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- What the caller's precondition gives of the stack. -/
structure Stk (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  le : 3632 ≤ s.sp.toNat
  fit : s.sp.toNat + 8 * 17 ≤ 2 ^ 64

theorem stk_of {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3632).pre s) : Stk s := by
  rw [pre_stk hk hnl] at hs
  obtain ⟨⟨hal, hst, hfit⟩, -⟩ := hs
  exact ⟨hal, by rcases hst with h | h <;> omega_using [h], by rcases hfit with h | h <;> omega_using [h]⟩

theorem E_toNat {s : State} (h : Stk s) : (E s).toNat = s.sp.toNat - 176 := toNat_sub_ofNat' (by omega_using [h.le])

/-- Bytes of the frame are in the stack the function uses. -/
theorem fr_stk (s : State) {d n : Nat} (h : d + n ≤ 176) : Region.Sub ⟨E s + BitVec.ofNat 64 d, n⟩ (stk s) := by
  rw [show E s = s.sp - BitVec.ofNat 64 3632 + BitVec.ofNat 64 3456 from Offset.sub_ofNat_eq _ (by decide),
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.sub_base _ (by omega_using [h])

theorem frame_stk (s : State) : Region.Sub ⟨E s, 176⟩ (stk s) := by
  have := fr_stk s (d := 0) (n := 176) (by decide)
  rwa [BitVec.add_zero] at this

/-- The stack below the frame is in it. -/
theorem below_stk (s : State) : Region.Sub (below (E s) 3456) (stk s) := below_below s.sp 176 3456

/-- A slot of the frame. -/
theorem slot_in (s : State) {d : Nat} (h : d + 8 ≤ 176) : (⟨E s, 176⟩ : Region).Contains (E s + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ h (by omega_using [h])

theorem slot_al {s : State} (h : Stk s) {d : Nat} (hd : d % 8 = 0) :
    (E s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have e := E_toNat h
  have a := h.al
  have l := h.le
  exact Spill.al8 (by rw [e]; omega_using [a, l]) hd

theorem argArea_eq (s : State) : argAreaStk 17 s = [(⟨stackArgAddr s 0, 8 * 17⟩, false)] := rfl

/-- The arguments' regions, the buffers' and the stack arguments'. -/
theorem all_eq (s : State) : allStk sig 17 s = Sig.bufs sig.params (stkArgs 17 s) ++ [(⟨stackArgAddr s 0, 8 * 17⟩, false)] := rfl

/-- What the caller's precondition gives of its regions. -/
structure Regs (s : State) : Prop where
  rd : s.rd = ((allStk sig 17 s).filter (!·.2)).map (·.1)
  wr : s.wr = ((allStk sig 17 s).filter (·.2)).map (·.1)
  pw : (allStk sig 17 s).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1)
  res : ∀ a ∈ allStk sig 17 s, (stk s).Disjoint a.1
  nw : ∀ a ∈ Sig.bufs sig.params (stkArgs 17 s), a.1.base.toNat + a.1.len ≤ 2 ^ 64
  pre : Curry.apply (sig.words abi.ptrBits) preP (stkArgs 17 s) s.mem
  alb : ∀ p ∈ Sig.alignedBufs sig.params (stkArgs 17 s), p.1.toNat % p.2 = 0

theorem regs_of {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3632).pre s) : Regs s := by
  rw [pre_stk hk hnl] at hs
  obtain ⟨-, hrd, hwr, hpw, hres, hnw, hpr, halb⟩ := hs
  exact ⟨hrd, hwr, hpw, fun a ha => hres _ (by rw [stackBelow_pos _ (by decide)]; exact List.mem_singleton_self _) a ha,
    hnw, hpr, halb⟩

/-- The buffers lie apart from the stack the function uses. -/
theorem bufs_stk {s : State} (R : Regs s) {b : Region × Bool} (hb : b ∈ Sig.bufs sig.params (stkArgs 17 s)) :
    b.1.Disjoint (stk s) :=
  (R.res b (List.mem_append_left _ hb)).symm

/-- The stack arguments lie apart from it. -/
theorem argA_stk {s : State} (R : Regs s) : (⟨stackArgAddr s 0, 8 * 17⟩ : Region).Disjoint (stk s) :=
  (R.res _ (List.mem_append_right _ (List.mem_singleton_self _))).symm

theorem argA_rd {s : State} (R : Regs s) : (⟨stackArgAddr s 0, 8 * 17⟩ : Region) ∈ s.rd := by
  rw [R.rd]
  exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, rfl⟩

/-- The writable regions are buffers. -/
theorem wr_buf {s : State} (R : Regs s) {x : Region} (hx : x ∈ s.wr) :
    ∃ b ∈ Sig.bufs sig.params (stkArgs 17 s), b.1 = x ∧ b.2 = true := by
  rw [R.wr] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hb, h2⟩ := List.mem_filter.mp hb
  rcases List.mem_append.mp hb with hb | hb
  · exact ⟨b, hb, rfl, h2⟩
  · rw [argArea_eq, List.mem_singleton] at hb; subst hb; simp at h2

theorem wr_stk {s : State} (R : Regs s) {x : Region} (hx : x ∈ s.wr) : x.Disjoint (stk s) := by
  obtain ⟨b, hb, rfl, -⟩ := wr_buf R hx
  exact bufs_stk R hb

/-- The stack arguments lie apart from the writable regions. -/
theorem argA_wr {s : State} (R : Regs s) {x : Region} (hx : x ∈ s.wr) :
    (⟨stackArgAddr s 0, 8 * 17⟩ : Region).Disjoint x := by
  obtain ⟨b, hb, rfl, h2⟩ := wr_buf R hx
  have := List.pairwise_append.mp R.pw
  exact (this.2.2 b hb _ (List.mem_singleton_self _) (by simp [h2])).symm

/-- The stack argument `j` is in the stack arguments' region. -/
theorem arg_in (s : State) {j : Nat} (hj : j < 17) (hfit : s.sp.toNat + 8 * 17 ≤ 2 ^ 64) :
    (⟨stackArgAddr s 0, 8 * 17⟩ : Region).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr, stackArgAddr]
  exact Offset.contains _ (d := 8 * j) (n := 8) (e := 8 * 0) (k := 8 * 17) (by omega_using []) (by omega_using [hj])
    (by have := s.sp.isLt; omega_using [hfit, this])

/-! ## Before the call -/

/-- After `setup`: the copies of the stack arguments at the frame's bottom,
the return address, `out`, `k` and `msg_len` in their slots. -/
structure Stashed (s t : State) : Prop where
  sp : t.sp = E s
  rd : t.rd = s.rd
  wr : t.wr = ⟨E s, 176⟩ :: s.wr
  gpr : ∀ r, r ≠ .t0 → r ≠ .t1 → t.gpr r = s.gpr r
  fr : Frame [⟨E s, 176⟩] s.mem t.mem
  args : ∀ j < 17, t.mem.readW (E s + BitVec.ofNat 64 (8 * j)) 64 = stackArg s j
  ra : t.mem.readW (E s + BitVec.ofNat 64 136) 64 = s.gpr .ra
  out : t.mem.readW (E s + BitVec.ofNat 64 144) 64 = s.gpr .a0
  k : t.mem.readW (E s + BitVec.ofNat 64 152) 64 = s.gpr .a1
  ml : t.mem.readW (E s + BitVec.ofNat 64 160) 64 = s.gpr .a2

/-- A word written at one offset of `p`, read at another. -/
theorem rw_ne (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64)
    (he : e + 8 ≤ 2 ^ 64) : (m.writeW (p + BitVec.ofNat 64 d) v).readW (p + BitVec.ofNat 64 e) 64 =
      m.readW (p + BitVec.ofNat 64 e) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (h.symm) he hd) (by decide)

theorem stash_args {s : State} (S : Stk s) (R : Regs s) :
    ∀ j < 17, InRegions ((allocd 176 s).rd ++ (allocd 176 s).wr)
      ((allocd 176 s).sp + BitVec.ofNat 64 (176 + 8 * j)) 8 := fun j hj => by
  refine ⟨⟨stackArgAddr s 0, 8 * 17⟩, List.mem_append_left _ (argA_rd R), ?_⟩
  rw [show (allocd 176 s).sp = E s from rfl, E_off]
  exact arg_in s hj S.fit

theorem setup_ok {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3632).pre s) :
    WP isa (.block Impl.RsaPkcs1Enc.RISCV64.Front.setup) (allocd 176 s) (Stashed s) := by
  have S := stk_of hs
  have R := regs_of hs
  have hal : (E s).toNat % 8 = 0 := by
    have a := S.al; have l := S.le; rw [E_toNat S]; omega_using [a, l]
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.setup
  simp only [Impl.RsaPkcs1Enc.RISCV64.Front.sRa, Impl.RsaPkcs1Enc.RISCV64.Front.sOut,
    Impl.RsaPkcs1Enc.RISCV64.Front.sK, Impl.RsaPkcs1Enc.RISCV64.Front.sMl]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (d := .t0) (imm := 0) (by decide), WP.block_nil ?_⟩
  generalize hu : (allocd 176 s).write .t0 ((allocd 176 s).sp + BitVec.ofNat 64 0) = u
  have usp : u.sp = E s := by rw [← hu]; rfl
  have ut0 : u.gpr .t0 = u.sp := by rw [← hu, RegUpd.gpr_write_self, BitVec.add_zero]; rfl
  have ug : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r := fun r h => by rw [← hu, RegUpd.gpr_write_of_ne _ _ h]; rfl
  have umem : u.mem = s.mem := by rw [← hu]; rfl
  have urd : u.rd = s.rd := by rw [← hu]; rfl
  have uwr : u.wr = ⟨E s, 176⟩ :: s.wr := by rw [← hu]; rfl
  have hrun := copies_run (bytes := 176) (u := u) ut0 (by rw [usp]; exact hal) (by decide) 17 (by decide)
    (fun j hj => by rw [← hu]; exact stash_args S R j hj)
    (fun j hj => ⟨_, by rw [uwr]; exact List.mem_cons_self .., by rw [usp]; exact slot_in s (by omega_using [hj])⟩)
  obtain ⟨hf, hv⟩ := copiedState_mem (bytes := 176) (u := u) 17 (by decide) (by decide)
  refine ⟨_, _, Exec.block_iff.mpr hrun, ?_⟩
  generalize hw : copiedState 176 u 17 = w at hf hv
  have wsp : w.sp = E s := by rw [← hw, copiedState_sp, usp]
  have wrd : w.rd = s.rd := by rw [← hw, copiedState_rd, urd]
  have wwr : w.wr = ⟨E s, 176⟩ :: s.wr := by rw [← hw, copiedState_wr, uwr]
  have wg : ∀ r, r ≠ .t0 → r ≠ .t1 → w.gpr r = s.gpr r := fun r h0 h1 => by
    rw [← hw, copiedState_gpr _ _ h1, ug r h0]
  have wt0 : w.gpr .t0 = E s := by rw [← hw, copiedState_gpr _ _ (by decide), ut0, usp]
  have c : ∀ d, d % 8 = 0 → d + 8 ≤ 176 → InRegions w.wr (E s + BitVec.ofNat 64 d) 8 := fun d _ hd =>
    ⟨_, by rw [wwr]; exact List.mem_cons_self .., slot_in s hd⟩
  rw [usp, umem] at hf hv
  refine Steps.wp_sd (by decide) (by rw [wt0]) (slot_al S (by decide)) (c 136 (by decide) (by decide))
    fun w₁ v₁ => ?_
  refine Steps.wp_sd (by decide) (by rw [v₁.gpr, wt0]) (slot_al S (by decide)) (by rw [v₁.wr]; exact c 144 (by decide) (by decide))
    fun w₂ v₂ => ?_
  refine Steps.wp_sd (by decide) (by rw [v₂.gpr, v₁.gpr, wt0]) (slot_al S (by decide))
    (by rw [v₂.wr, v₁.wr]; exact c 152 (by decide) (by decide)) fun w₃ v₃ => ?_
  refine Steps.wp_sd (by decide) (by rw [v₃.gpr, v₂.gpr, v₁.gpr, wt0]) (slot_al S (by decide))
    (by rw [v₃.wr, v₂.wr, v₁.wr]; exact c 160 (by decide) (by decide)) fun w₄ v₄ => WP.block_nil ?_
  have hm : w₄.mem = (((w.mem.writeW (E s + BitVec.ofNat 64 136) (s.gpr .ra)).writeW (E s + BitVec.ofNat 64 144)
      (s.gpr .a0)).writeW (E s + BitVec.ofNat 64 152) (s.gpr .a1)).writeW (E s + BitVec.ofNat 64 160) (s.gpr .a2) := by
    rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr, v₂.gpr, v₁.gpr, wg _ (by decide) (by decide),
      wg _ (by decide) (by decide), wg _ (by decide) (by decide), wg _ (by decide) (by decide)]
  have g : ∀ r, w₄.gpr r = w.gpr r := fun r => by rw [v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr]
  refine ⟨by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, wsp], by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, wrd],
    by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, wwr], fun r h0 h1 => by rw [g, wg r h0 h1], ?_, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    refine ((((Frame.sub hf fun r hr => ?_).writeW (List.mem_singleton_self _) _ (slot_in s (by decide))).writeW
      (List.mem_singleton_self _) _ (slot_in s (by decide))).writeW (List.mem_singleton_self _) _
      (slot_in s (by decide))).writeW (List.mem_singleton_self _) _ (slot_in s (by decide))
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · rw [hm, rw_ne _ _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      rw_ne _ _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      rw_ne _ _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      rw_ne _ _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]), hv j hj, E_off]
    rfl
  · rw [hm, rw_ne _ _ _ (by decide) (by decide) (by decide), rw_ne _ _ _ (by decide) (by decide) (by decide),
      rw_ne _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [hm, rw_ne _ _ _ (by decide) (by decide) (by decide), rw_ne _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, rw_ne _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [hm, Mem.readW_writeW_self64]

/-! ## The call -/

/-- The callee's regions: the buffers, and the copies of the stack
arguments, read only. -/
def cAll (s : State) : List (Region × Bool) :=
  Sig.bufs sig.params (stkArgs 17 s) ++ [(⟨E s + BitVec.ofNat 64 (8 * 0), 8 * 17⟩, false)]

abbrev cRd (s : State) : List Region := ((cAll s).filter (!·.2)).map (·.1)
abbrev cWr (s : State) : List Region := ((cAll s).filter (·.2)).map (·.1)

section
variable {s t : State} (T : Stashed s t)
include T

theorem entry_args : stkArgs 17 (t.callEntry.withRegions (cRd s) (cWr s)) = stkArgs 17 s := by
  have h1 : argRegs.map (t.callEntry.withRegions (cRd s) (cWr s)).gpr = argRegs.map s.gpr :=
    List.map_congr_left fun q hq => by
      rw [State.withRegions_gpr, State.callEntry_gpr _ (fun h => by revert q; decide),
        T.gpr q (fun h => by subst h; revert hq; decide) (fun h => by subst h; revert hq; decide)]
  have h2 : (List.range 17).map (stackArg (t.callEntry.withRegions (cRd s) (cWr s))) =
      (List.range 17).map (stackArg s) := List.map_congr_left fun j hj => by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * j)) 64 = _
    rw [T.sp]
    exact T.args j (List.mem_range.mp hj)
  show argRegs.map _ ++ _ = argRegs.map _ ++ _
  rw [h1, h2]

theorem entry_all : allStk sig 17 (t.callEntry.withRegions (cRd s) (cWr s)) = cAll s := by
  rw [allStk, entry_args T, argArea_eq, stackArgAddr, State.withRegions_sp, State.callEntry_sp, T.sp]
  rfl

end

/-- A buffer of the callee is one of ours, or in the frame. -/
theorem cAll_cases {s : State} {a : Region × Bool} (ha : a ∈ cAll s) :
    a ∈ Sig.bufs sig.params (stkArgs 17 s) ∨ a = (⟨E s + BitVec.ofNat 64 (8 * 0), 8 * 17⟩, false) := by
  rcases List.mem_append.mp ha with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem copies_sub (s : State) : Region.Sub ⟨E s + BitVec.ofNat 64 (8 * 0), 8 * 17⟩ (stk s) :=
  fr_stk s (by decide)

/-- The callee's writable regions are ours. -/
theorem cWr_wr {s : State} (R : Regs s) {x : Region} (hx : x ∈ cWr s) : x ∈ s.wr := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ha, h2⟩ := List.mem_filter.mp ha
  rcases cAll_cases ha with ha | rfl
  · rw [R.wr]
    exact List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h2⟩, rfl⟩
  · simp at h2

theorem cRd_rd {s : State} (R : Regs s) {x : Region} (hx : x ∈ cRd s) :
    x ∈ s.rd ∨ x = ⟨E s + BitVec.ofNat 64 (8 * 0), 8 * 17⟩ := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨ha, h2⟩ := List.mem_filter.mp ha
  rcases cAll_cases ha with ha | rfl
  · rw [R.rd]
    exact .inl (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨List.mem_append_left _ ha, h2⟩, rfl⟩)
  · exact .inr rfl

/-- The callee's precondition, at its entry. -/
theorem entry_pre {Q : sig.Post abi.ptrBits} {s t : State} (hs : (C Q 3632).pre s) (T : Stashed s t) :
    (C postP 3456).pre (t.callEntry.withRegions (cRd s) (cWr s)) := by
  have S := stk_of hs
  have R := regs_of hs
  have ha := entry_args T
  refine (pre_stk hk hnl).mpr ?_
  rw [entry_all T, ha]
  have hsp : (t.callEntry.withRegions (cRd s) (cWr s)).sp = E s := T.sp
  have he := E_toNat S
  have hl := S.le
  have hfit := S.fit
  have hal := S.al
  refine ⟨⟨by rw [hsp, he]; omega_using [hal, hl], .inr (by rw [hsp, he]; omega_using [hl]),
      .inr (by rw [hsp, he]; omega_using [hl, hfit])⟩, rfl, rfl, ?_, ?_, R.nw, ?_, R.alb⟩
  · -- Pairwise disjoint.
    simp only [cAll, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
    refine ⟨List.Pairwise.sublist (List.sublist_append_left _ _) R.pw, trivial, fun a ha b hb _ => ?_⟩
    subst hb
    exact (bufs_stk R ha).sub_right (copies_sub s)
  · -- The reserved stack, below the frame.
    intro r hr a ha
    rw [hsp, stackBelow_pos _ (by decide), List.mem_singleton] at hr
    subst hr
    rcases cAll_cases ha with ha | rfl
    · exact ((bufs_stk R ha).sub_right (below_stk s)).symm
    · show Region.Disjoint (below (E s) 3456) ⟨E s + BitVec.ofNat 64 (8 * 0), 8 * 17⟩
      exact (Offset.disjoint_below (E s) (n := 3456) (d := 8 * 0) (k := 8 * 17) (by decide)).symm
  · -- The precondition, which reads only the buffers.
    refine preP_local _ _ _ (args_length s) (fun b hb x hx => ?_) (fun r hr => by
      rw [Sig.lists_of_noLists _ _ _ _ hnl] at hr; simp at hr) R.pre
    exact (T.fr x fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact bufs_stk R hb x hx (frame_stk s x hc)).symm

/-- What the call leaves. -/
structure Called (s c : State) : Prop where
  sp : c.sp = E s
  rd : c.rd = s.rd
  wr : c.wr = ⟨E s, 176⟩ :: s.wr
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  ra : c.mem.readW (E s + BitVec.ofNat 64 136) 64 = s.gpr .ra
  out : c.mem.readW (E s + BitVec.ofNat 64 144) 64 = s.gpr .a0
  k : c.mem.readW (E s + BitVec.ofNat 64 152) 64 = s.gpr .a1
  ml : c.mem.readW (E s + BitVec.ofNat 64 160) 64 = s.gpr .a2
  scr : c.mem.readW (stackArgAddr s 13) 64 = stackArg s 13
  fr : Frame (s.wr ++ [stk s]) s.mem c.mem
  post : Curry.apply (sig.words abi.ptrBits) postP (stkArgs 17 s) s.mem c.mem ((c.gpr .a0).setWidth _)

/-- The call of `vg_rsa_pkcs1_decrypt_precomputed_body`, from `setup`'s state. -/
theorem call_ok {Q : sig.Post abi.ptrBits} {name : String} {callee : Prog isa}
    (hv : Verified target callee (C postP 3456)) (hd : sdepth callee ≤ 3456) {s t : State}
    (hs : (C Q 3632).pre s) (T : Stashed s t) : WP isa (.call name callee) t (Called s) := by
  have S := stk_of hs
  have R := regs_of hs
  have hl := S.le
  have hpre := entry_pre hs T
  have hcov : Covers (cRd s ++ cWr s) (t.rd ++ t.wr) := Covers.of_sub fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · rcases cRd_rd R hx with hx | rfl
      · exact ⟨x, List.mem_append_left _ (by rw [T.rd]; exact hx), 0, (BitVec.add_zero _).symm, by omega_using []⟩
      · exact ⟨⟨E s, 176⟩, List.mem_append_right _ (by rw [T.wr]; exact List.mem_cons_self ..), 8 * 0, rfl,
          by show 8 * 0 + 8 * 17 ≤ 176; decide⟩
    · exact ⟨x, List.mem_append_right _ (by rw [T.wr]; exact List.mem_cons_of_mem _ (cWr_wr R hx)), 0,
        (BitVec.add_zero _).symm, by omega_using []⟩
  have hcw : Covers (cWr s) t.wr := Covers.of_mem fun x hx => by rw [T.wr]; exact List.mem_cons_of_mem _ (cWr_wr R hx)
  refine WP.callAny hv.1 hpre hcov hcw ?_ (by omega_using [hd])
  intro c hrd hwr hsp hfr hcs hq
  rw [T.sp] at hfr
  -- What the callee may write lies apart from the stack arguments and the slots.
  have hfrS : ∀ x ∈ cWr s ++ [below (E s) (sdepth callee)], Region.Sub x (stk s) ∨ x ∈ s.wr := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact .inr (cWr_wr R hx)
    · rw [List.mem_singleton.mp hx]
      exact .inl fun y hy => below_stk s y (below_sub (sp := E s) (a := sdepth callee) (b := 3456) hd (by decide) y hy)
  have slot : ∀ d, d + 8 ≤ 176 → c.mem.readW (E s + BitVec.ofNat 64 d) 64 = t.mem.readW (E s + BitVec.ofNat 64 d) 64 :=
    fun d h => hfr.readW (r := ⟨E s + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun x hx => by
      rcases List.mem_append.mp hx with hx' | hx'
      · exact ((wr_stk R (cWr_wr R hx')).sub_right (fr_stk s h)).symm
      · rw [List.mem_singleton.mp hx']
        exact Offset.disjoint_below (E s) (by omega_using [hd, h])) (by decide)
  have fbig : Frame (s.wr ++ [stk s]) s.mem c.mem := by
    refine Frame.trans (Frame.sub T.fr fun r hr => ?_) (Frame.sub hfr fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact ⟨stk s, by simp, frame_stk s⟩
    · rcases hfrS r hr with h | h
      · exact ⟨stk s, by simp, h⟩
      · exact ⟨r, List.mem_append_left _ h, fun _ h => h⟩
  have hbuf : ∀ b ∈ Sig.bufs sig.params (stkArgs 17 s), ∀ x, b.1.Contains x 1 → t.mem x = s.mem x := fun b hb x hx =>
    T.fr x fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact bufs_stk R hb x hx (frame_stk s x hc)
  rw [post_stk hk, entry_args T] at hq
  have hpreT : Curry.apply (sig.words abi.ptrBits) preP (stkArgs 17 s) t.mem :=
    preP_local _ _ _ (args_length s) (fun b hb x hx => (hbuf b hb x hx).symm)
      (fun r hr => by rw [Sig.lists_of_noLists _ _ _ _ hnl] at hr; simp at hr) R.pre
  refine ⟨hsp.trans T.sp, hrd.trans T.rd, hwr.trans T.wr, fun r hr => (hcs r hr).trans (T.gpr r
      (fun h => by subst h; revert hr; decide) (fun h => by subst h; revert hr; decide)),
    (slot 136 (by decide)).trans T.ra, (slot 144 (by decide)).trans T.out, (slot 152 (by decide)).trans T.k,
    (slot 160 (by decide)).trans T.ml, ?_, fbig, postP_local (args_length s) hpreT hbuf hq⟩
  -- The stack argument `scratch`, which nothing writes.
  refine fbig.readW (r := ⟨stackArgAddr s 0, 8 * 17⟩) (arg_in s (by decide) S.fit) (fun x hx => ?_) (by decide)
  rcases List.mem_append.mp hx with hx | hx
  · exact argA_wr R hx
  · rw [List.mem_singleton.mp hx]; exact argA_stk R

/-! ## The callee's precondition gives decryption's facts -/

theorem pre_mono {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3632).pre s) : (C postP 3456).pre s := by
  rw [pre_stk hk hnl] at hs ⊢
  obtain ⟨⟨hal, hst, hfit⟩, hrd, hwr, hpw, hres, hnw, hpr, halb⟩ := hs
  refine ⟨⟨hal, .inr ?_, hfit⟩, hrd, hwr, hpw, fun r hr a ha => ?_, hnw, hpr, halb⟩
  · rcases hst with h | h <;> omega_using [h]
  · rw [stackBelow_pos _ (by decide), List.mem_singleton] at hr
    subst hr
    exact (hres _ (by rw [stackBelow_pos _ (by decide)]; exact List.mem_singleton_self _) a ha).sub_left
      (Offset.sub_below _ (by decide) (by decide))

open VG.Proof.RsaPkcs1Enc.RISCV64.Dec (DPre oR mlR sR)

theorem dpre_of {Q : sig.Post abi.ptrBits} {s : State} (hs : (C Q 3632).pre s) : DPre true s :=
  (Dec.dPreP_of (by rw [show Dec.stackBytes = 3456 from rfl, cK_eq]; exact pre_mono hs)).1

/-! ## After the call -/

open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_li wp_addi wp_subi wp_add wp_sub wp_mov wp_xor wp_and wp_srl
  wp_sll wp_lbu wp_sb wp_ld wp_addSp wp_nil fill_ok copy_ok)
open VG.Proof.Mgf1 (ifp ifn)
open VG.Impl.RsaPkcs1Enc.RISCV64.Front (load diff clearBuf copyIn shiftPass nextPass shift copyOut tail)
open VG.WriteBytes

/-- The byte `o` from `p`. -/
abbrev at_ (m : Mem) (p : Addr) (o : Nat) : Byte := m (p + BitVec.ofNat 64 o)

theorem at_wb (m : Mem) (p : Addr) (xs : List Byte) {o : Nat} (ho : o < 2 ^ 64) :
    at_ (writeBytes m p xs) p o = if o < xs.length then xs.getD o 0 else at_ m p o := by
  simp only [at_, writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]

theorem at_w8 (m : Mem) (p : Addr) (b : Byte) {d o : Nat} (hd : d < 2 ^ 64) (ho : o < 2 ^ 64) :
    at_ (m.writeW (p + BitVec.ofNat 64 d) b) p o = if o = d then b else at_ m p o := by
  simp only [at_]
  rw [writeW8_apply]
  by_cases h : o = d
  · subst h; simp
  · rw [ifn (Offset.add_ofNat_ne p ho hd h), ifn h]

/-- What every piece after the call keeps: the frame, the result of the call
in `a0`, and `scratch`, `out` and `k` in `a6`, `a7` and `t6`. -/
structure Base (s : State) (r0 : BitVec 64) (v : State) : Prop where
  sp : v.sp = E s
  rd : v.rd = s.rd
  wr : v.wr = ⟨E s, 176⟩ :: s.wr
  pres : ∀ r ∈ preserved, v.gpr r = s.gpr r
  a0 : v.gpr .a0 = r0
  a6 : v.gpr .a6 = stackArg s 13
  a7 : v.gpr .a7 = s.gpr .a0
  t6 : v.gpr .t6 = s.gpr .a1

theorem Base.kept {s v v' : State} {r0 : BitVec 64} (h : Base s r0 v) {rs : List Reg} (k : Kept rs v v')
    (hrs : ∀ r ∈ rs, r ∉ (([.a0, .a6, .a7, .t6] : List Reg) ++ preserved) := by decide) : Base s r0 v' :=
  ⟨k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    fun r hr => (k.gpr r fun h' => hrs r h' (List.mem_append_right _ hr)).trans (h.pres r hr),
    (k.gpr .a0 fun h' => hrs _ h' (by simp)).trans h.a0, (k.gpr .a6 fun h' => hrs _ h' (by simp)).trans h.a6,
    (k.gpr .a7 fun h' => hrs _ h' (by simp)).trans h.a7, (k.gpr .t6 fun h' => hrs _ h' (by simp)).trans h.t6⟩

section
variable {s : State} (P : DPre true s)
include P

/-- `k` and the length of `scratch`. -/
theorem kk_le : (s.gpr .a1).toNat ≤ 1024 ∧ 64 ≤ (s.gpr .a1).toNat := by
  have a := P.h1; have b := P.k1; have c := P.k2; omega_using [a, b, c]

theorem scr_len : 2048 ≤ (stackArg s 14).toNat * 8 := by
  have hs := P.hs; have b := P.k1
  simp only [Spec.Rsa.scratchWords] at hs
  omega_using [hs, b]

theorem scr_w {v : State} (hw : v.wr = ⟨E s, 176⟩ :: s.wr) {o : Nat} (ho : o < 2048) :
    InRegions v.wr (stackArg s 13 + BitVec.ofNat 64 o) 1 := by
  have hl := scr_len P
  refine ⟨sR s, by rw [hw, P.hwr]; simp, Offset.contains_base _ (by omega_using [hl, ho]) (by omega_using [ho])⟩

theorem scr_r {v : State} (hw : v.wr = ⟨E s, 176⟩ :: s.wr) {o : Nat} (ho : o < 2048) :
    InRegions (v.rd ++ v.wr) (stackArg s 13 + BitVec.ofNat 64 o) 1 :=
  let ⟨r, hr, hc⟩ := scr_w P hw ho
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem out_w {v : State} (hw : v.wr = ⟨E s, 176⟩ :: s.wr) {i : Nat} (hi : i < (s.gpr .a1).toNat) :
    InRegions v.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
  ⟨oR s, by rw [hw, P.hwr]; simp, Offset.contains_base _ (by omega_using [hi]) (by have hk := kk_le P; omega_using [hi, hk])⟩

theorem out_r {v : State} (hw : v.wr = ⟨E s, 176⟩ :: s.wr) {i : Nat} (hi : i < (s.gpr .a1).toNat) :
    InRegions (v.rd ++ v.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 :=
  let ⟨r, hr, hc⟩ := out_w P hw hi
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- The buffer at `scratch`. -/
abbrev bufR (s : State) : Region := ⟨stackArg s 13, 2048⟩

theorem buf_sub : Region.Sub (bufR s) (sR s) := Region.sub_prefix (scr_len P)

theorem out_buf : (oR s).Disjoint (bufR s) := P.os.sub_right (buf_sub P)

/-- `out`'s bytes and the buffer's are apart. -/
theorem out_ne {i o : Nat} (hi : i < (s.gpr .a1).toNat) (ho : o < 2048) :
    s.gpr .a0 + BitVec.ofNat 64 i ≠ stackArg s 13 + BitVec.ofNat 64 o := fun e => by
  have hk := kk_le P
  exact out_buf P (s.gpr .a0 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hk]))
    (by rw [e]; exact Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho]))

end

/-- After the loads: `msg_len` in `t3`, memory as the call left it. -/
theorem load_ok {s c : State} (P : DPre true s) (S : Stk s) (hc : Called s c) :
    WP isa (.block load) c fun v => Base s (c.gpr .a0) v ∧ v.gpr .t3 = s.gpr .a2 ∧ v.mem = c.mem := by
  have c' : ∀ d, d % 8 = 0 → d + 8 ≤ 176 → InRegions (c.rd ++ c.wr) (E s + BitVec.ofNat 64 d) 8 := fun d _ hd =>
    ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), slot_in s hd⟩
  have hA : InRegions (c.rd ++ c.wr) (stackArgAddr s 13) 8 := by
    refine ⟨⟨stackArgAddr s 0, 8 * 17⟩, List.mem_append_left _ (by rw [hc.rd, P.hrd]; simp), arg_in s (by decide) S.fit⟩
  have hAal : (stackArgAddr s 13).toNat % 8 = 0 := Spill.al8 (by have := P.sp16; omega_using [this]) (by decide)
  unfold load
  simp only [Impl.RsaPkcs1Enc.RISCV64.Front.sOut, Impl.RsaPkcs1Enc.RISCV64.Front.sK,
    Impl.RsaPkcs1Enc.RISCV64.Front.sMl, Impl.RsaPkcs1Enc.RISCV64.Front.aScr, Impl.RsaPkcs1Enc.RISCV64.Front.frameBytes]
  refine wp_addSp (imm := 0) fun t₀ o₀ e₀ => ?_
  have t0 : t₀.gpr .t0 = E s := by rw [e₀, hc.sp, BitVec.add_zero]
  refine wp_ld (a := E s + BitVec.ofNat 64 144) (by rw [t0]) (slot_al S (by decide))
    (by rw [o₀.rd, o₀.wr]; exact c' 144 (by decide) (by decide)) fun t₁ o₁ e₁ => ?_
  refine wp_ld (a := E s + BitVec.ofNat 64 152) (by rw [o₁.get .t0, t0]) (slot_al S (by decide))
    (by rw [o₁.rd, o₁.wr, o₀.rd, o₀.wr]; exact c' 152 (by decide) (by decide)) fun t₂ o₂ e₂ => ?_
  refine wp_ld (a := stackArgAddr s 13) (by rw [o₂.get .t0, o₁.get .t0, t0, E_off]; rfl) hAal
    (by rw [o₂.rd, o₂.wr, o₁.rd, o₁.wr, o₀.rd, o₀.wr]; exact hA) fun t₃ o₃ e₃ => ?_
  refine wp_ld (a := E s + BitVec.ofNat 64 160) (by rw [o₃.get .t0, o₂.get .t0, o₁.get .t0, t0])
    (slot_al S (by decide)) (by rw [o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr, o₀.rd, o₀.wr]; exact c' 160 (by decide) (by decide))
    fun t₄ o₄ e₄ => wp_nil ?_
  have k : Only [.t0, .a7, .t6, .a6, .t3] c t₄ := (o₀.trans (o₁.trans (o₂.trans (o₃.trans o₄)))).mono
  have hm : t₄.mem = c.mem := k.mem
  refine ⟨⟨k.sp.trans hc.sp, k.rd.trans hc.rd, k.wr.trans hc.wr, fun r hr => (k.gpr r (by revert r; decide)).trans
      (hc.pres r hr), k.gpr .a0 (by decide), ?_, ?_, ?_⟩, ?_, hm⟩
  · rw [o₄.get .a6, e₃, o₂.mem, o₁.mem, o₀.mem, hc.scr]
  · rw [o₄.get .a7, o₃.get .a7, o₂.get .a7, e₁, o₀.mem, hc.out]
  · rw [o₄.get .t6, o₃.get .t6, e₂, o₁.mem, o₀.mem, hc.k]
  · rw [e₄, o₃.mem, o₂.mem, o₁.mem, o₀.mem, hc.ml]

/-- `s = k - *msg_len` into `t3`. -/
theorem diff_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) (h3 : v.gpr .t3 = s.gpr .a2) :
    WP isa (.block diff) v fun v' => Base s r0 v' ∧ v'.gpr .t3 = s.gpr .a1 - v.mem.readW (s.gpr .a2) 64 ∧
      v'.mem = v.mem := by
  unfold diff
  refine wp_ld (a := s.gpr .a2) (by rw [h3, BitVec.add_zero]) P.mal
    ⟨mlR s, List.mem_append_right _ (by rw [h.wr, P.hwr]; simp), Region.contains_self _ _⟩ fun t₁ o₁ e₁ => ?_
  refine wp_sub fun t₂ o₂ e₂ => wp_nil ?_
  have k : Only [.t3, .t3] v t₂ := o₁.trans o₂
  exact ⟨h.kept k.keep, by rw [e₂, o₁.get .t6, h.t6, e₁], k.mem⟩

/-- The buffer cleared. -/
theorem clear_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) :
    WP isa clearBuf v fun v' => Base s r0 v' ∧ v'.gpr .t3 = v.gpr .t3 ∧
      v'.mem = writeBytes v.mem (stackArg s 13) (List.replicate 2048 0) := by
  unfold clearBuf
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_li (imm := 1) (by decide) fun t₂ o₂ e₂ =>
    wp_sll (sh := 11) (fun t₃ o₃ e₃ => wp_li (imm := 0) (by decide) fun t₄ o₄ e₄ => wp_nil ?_))
  have k₄ : Only [.a1, .t5, .t5, .t0] v t₄ := o₁.trans (o₂.trans (o₃.trans o₄))
  refine WP.mono (fill_ok (p := stackArg s 13) (n := 2048) (b := 0) (by decide) (by decide)
    (by rw [o₄.get .a1, o₃.get .a1, o₂.get .a1, e₁, h.a6]) (by rw [o₄.get .t5, e₃, e₂]; decide)
    (by rw [e₄]; decide) (fun i hi => scr_w P (k₄.wr.trans h.wr) hi)) fun t' ⟨hk, hm⟩ => ?_
  have K : Kept [.a1, .t5, .t5, .t0, .a1, .t5] v t' := k₄.keep.trans hk
  exact ⟨h.kept K, K.gpr .t3 (by decide), by rw [hm, k₄.mem]⟩

/-- `out`'s `k` bytes to the buffer. -/
theorem copyIn_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) :
    WP isa copyIn v fun v' => Base s r0 v' ∧ v'.gpr .t3 = v.gpr .t3 ∧
      v'.mem = writeBytes v.mem (stackArg s 13) (Spec.Rsa.bytesAt v.mem (s.gpr .a0) (s.gpr .a1).toNat) := by
  have hk := kk_le P
  unfold copyIn
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] v t₃ := o₁.trans (o₂.trans o₃)
  refine WP.mono (copy_ok (p := stackArg s 13) (q := s.gpr .a0) (n := (s.gpr .a1).toNat) (by omega_using [hk])
    (by omega_using [hk]) (by rw [o₃.get .a1, e₂, o₁.get .a6, h.a6]) (by rw [o₃.get .a4, o₂.get .a4, e₁, h.a7])
    (by rw [e₃, o₂.get .t6, o₁.get .t6, h.t6, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [k₃.rd, k₃.wr]; exact out_r P h.wr hj)
    (fun i hi => by rw [k₃.wr]; exact scr_w P h.wr (by omega_using [hi, hk]))
    (fun j hj i hi => out_ne P hj (by omega_using [hi, hk]))) fun t' ⟨hk', hm⟩ => ?_
  have K : Kept [.a4, .a1, .a5, .t0, .a4, .a1, .a5] v t' := k₃.keep.trans hk'
  exact ⟨h.kept K, K.gpr .t3 (by decide), by rw [hm, k₃.mem]⟩

/-! ## The shift -/

open VG.Proof.RsaPss.RISCV64 (passV shV shV_out mask_odd sel_byte)
open VG.Proof.Bignum.RISCV64 (wp_countdown)

/-- A pass, by bit 0 of `x` (`t3`) and `d` bytes (`t4`), on the buffer's
first `k` bytes. -/
theorem pass_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) {x d : Nat}
    (h3 : v.gpr .t3 = BitVec.ofNat 64 x) (h4 : v.gpr .t4 = BitVec.ofNat 64 d) (hd : d ≤ 1024) :
    WP isa shiftPass v fun v' => Base s r0 v' ∧ Kept [.a1, .a2, .a3, .a4, .a5, .t1, .t2] v v' ∧
      Frame [bufR s] v.mem v'.mem ∧ ∀ o < 2048, at_ v'.mem (stackArg s 13) o =
        passV (at_ v.mem (stackArg s 13)) 0 (s.gpr .a1).toNat (x % 2 = 1) d o := by
  have hk := kk_le P
  let S := stackArg s 13
  let K := (s.gpr .a1).toNat
  let V := at_ v.mem S
  let bit : Bool := x % 2 = 1
  unfold shiftPass
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ => wp_li (imm := 1) (by decide) fun t₃ o₃ e₃ =>
    wp_and fun t₄ o₄ e₄ => wp_li (imm := 0) (by decide) fun t₅ o₅ e₅ => wp_sub fun t₆ o₆ e₆ =>
    wp_mov fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.a1, .a2, .a3, .a4, .a5] v t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have g1 : t₁.gpr .a1 = S := by rw [e₁, h.a6]
  have g6 : t₇.gpr .a3 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .a3, e₆, e₅, o₅.get .a3, e₄, e₃, o₃.get .t3, o₂.get .t3, o₁.get .t3, h3, mask_odd]
    simp only [bit, decide_eq_true_eq]
  have g7 : t₇.gpr .a5 = BitVec.ofNat 64 K := by
    rw [e₇, o₆.get .t6, o₅.get .t6, o₄.get .t6, o₃.get .t6, o₂.get .t6, o₁.get .t6, h.t6, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have bt : Base s r0 t₇ := h.kept k₇.keep
  refine WP.mono (wp_countdown (cnt := .a5) (N := K) (by omega_using [hk]) (by omega_using [hk])
    (fun i u => Base s r0 u ∧ Kept [.a1, .a2, .a5, .t1, .t2] t₇ u ∧ u.gpr .a1 = S + BitVec.ofNat 64 i ∧
      u.gpr .a2 = S + BitVec.ofNat 64 (i + d) ∧ Frame [bufR s] v.mem u.mem ∧ ∀ o < 2048, at_ u.mem S o =
        if o < i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨bt, Kept.refl _ _, by rw [o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1, o₂.get .a1, g1,
        BitVec.add_zero],
      by rw [o₇.get .a2, o₆.get .a2, o₅.get .a2, o₄.get .a2, o₃.get .a2, e₂, g1, o₁.get .t4, h4, Nat.zero_add],
      by rw [k₇.mem]; exact Frame.refl _ _, fun o _ => by rw [ifn (by omega_using []), k₇.mem]⟩ g7)
    fun u ⟨bu, ou, _, _, fu, vu⟩ => ⟨bu, (k₇.keep.trans ou).mono, fu, fun o ho => by
      rw [vu o ho, passV]; simp only [Nat.zero_le, true_and, Nat.zero_add]; rfl⟩
  intro i hi u ⟨bu, ou, u1, u2, fu, vu⟩ _
  simp only [Impl.RsaOaep.RISCV64.Dec.passBody, List.cons_append, List.nil_append]
  refine wp_lbu (a := S + BitVec.ofNat 64 i) (by rw [u1, BitVec.add_zero])
    (scr_r P bu.wr (by omega_using [hi, hk])) fun u₁ p₁ f₁ => ?_
  refine wp_lbu (a := S + BitVec.ofNat 64 (i + d)) (by rw [p₁.get .a2, u2, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr]; exact scr_r P bu.wr (by omega_using [hi, hk, hd])) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.t1, .t2] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_sb (a := S + BitVec.ofNat 64 i) (by rw [k₅.get .a1, u1, BitVec.add_zero])
    (by rw [k₅.wr]; exact scr_w P bu.wr (by omega_using [hi, hk])) fun u₆ m₆ => ?_
  refine wp_addi (imm := 1) fun u₇ p₇ f₇ => wp_addi (imm := 1) fun u₈ p₈ f₈ =>
    wp_subi (imm := 1) fun u₉ p₉ f₉ => wp_nil ?_
  have hb : (u₅.gpr .t1).setWidth 8 = if bit then V (i + d) else V i := by
    have va : u.mem (S + BitVec.ofNat 64 i) = V i := by
      have := vu i (by omega_using [hi, hk]); rw [ifn (by omega_using [])] at this; exact this
    have vb : u₁.mem (S + BitVec.ofNat 64 (i + d)) = V (i + d) := by
      have := vu (i + d) (by omega_using [hi, hk, hd]); rw [ifn (by omega_using [])] at this; rw [p₁.mem]; exact this
    rw [f₅, p₄.get .t1, p₃.get .t1, p₂.get .t1, f₁, f₄, f₃, f₂, p₂.get .t1, f₁, va, vb, p₃.get .a3,
      p₂.get .a3, p₁.get .a3, ou.get .a3, g6]
    exact sel_byte _ _ bit
  have q : Kept [.t1, .t2, .a1, .a2, .a5] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (S + BitVec.ofNat 64 i) (if bit then V (i + d) else V i) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, k₅.mem]
  refine ⟨⟨bu.kept q, (ou.trans q).mono, ?_, ?_, ?_, fun o ho => ?_⟩, ?_⟩
  · rw [p₉.get .a1, p₈.get .a1, f₇, m₆.gpr, k₅.get .a1, u1, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [p₉.get .a2, f₈, p₇.get .a2, m₆.gpr, k₅.get .a2, u2, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show i + d + 1 = i + 1 + d by omega_using []]
  · rw [hm]
    exact fu.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hi, hk])
      (by omega_using [hi, hk]))
  · rw [hm, at_w8 _ _ _ (by omega_using [hi, hk]) (by omega_using [ho]), vu o ho]
    by_cases e : o = i
    · subst e
      rw [ifp rfl, ifp (show o < o + 1 by omega_using [])]
    · rw [ifn e]
      by_cases e' : o < i
      · rw [ifp e', ifp (show o < i + 1 by omega_using [e'])]
      · rw [ifn e', ifn (show ¬ o < i + 1 by omega_using [e, e'])]
  · rw [f₉, p₈.get .a5, p₇.get .a5, m₆.gpr, k₅.get .a5]

/-- The eleven passes, by the bits of `a` (`t3`). -/
theorem shift_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) {a : Nat}
    (ha : a < 2048) (h3 : v.gpr .t3 = BitVec.ofNat 64 a) :
    WP isa shift v fun v' => Base s r0 v' ∧ Frame [bufR s] v.mem v'.mem ∧
      ∀ o < 2048, at_ v'.mem (stackArg s 13) o = shV (at_ v.mem (stackArg s 13)) 0 (s.gpr .a1).toNat a 11 o := by
  let S := stackArg s 13
  let V := at_ v.mem S
  unfold shift
  refine WP.seq (wp_li (imm := 1) (by decide) fun t₁ o₁ e₁ => wp_li (imm := 11) (by decide) fun t₂ o₂ e₂ => wp_nil ?_)
  have k₂ : Only [.t4, .t5] v t₂ := o₁.trans o₂
  refine WP.mono (wp_countdown (cnt := .t5) (N := 11) (by decide) (by decide)
    (fun j u => Base s r0 u ∧ u.gpr .t3 = BitVec.ofNat 64 (a / 2 ^ j) ∧ u.gpr .t4 = BitVec.ofNat 64 (2 ^ j) ∧
      Frame [bufR s] v.mem u.mem ∧ ∀ o < 2048, at_ u.mem S o = shV V 0 (s.gpr .a1).toNat a j o) ?_
    ⟨h.kept k₂.keep, by rw [k₂.get .t3, h3, Nat.pow_zero, Nat.div_one], by rw [o₂.get .t4, e₁],
      by rw [k₂.mem]; exact Frame.refl _ _, fun o _ => by rw [k₂.mem]; rfl⟩ (by rw [e₂]))
    fun u ⟨bu, _, _, fu, vu⟩ => ⟨bu, fu, vu⟩
  intro j hj u ⟨bu, u3, u4, fu, vu⟩ _
  have hp : 2 ^ j ≤ 1024 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show j ≤ 10 by omega_using [hj])
    exact this
  refine WP.seq (WP.mono (pass_ok P bu u3 u4 hp) fun u₁ ⟨b₁, k₁, f₁, v₁⟩ => ?_)
  unfold nextPass
  refine wp_srl fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi (imm := 1) fun u₄ p₄ f₄ => wp_nil ?_
  have k₄ : Only [.t3, .t4, .t5] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨b₁.kept k₄.keep, ?_, ?_, fu.trans (by rw [k₄.mem]; exact f₁), fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .t3, p₃.get .t3, f₂, k₁.get .t3, u3, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have : a / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self a (2 ^ j); omega_using [ha, this]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self (a / 2 ^ j) 2; omega_arith)]
  · rw [p₄.get .t4, f₃, p₂.get .t4, k₁.get .t4, u4, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄.mem, v₁ o ho]
    show passV (at_ u.mem S) _ _ _ _ o = passV (shV V 0 (s.gpr .a1).toNat a j) _ _ _ _ o
    unfold passV
    have hk := kk_le P
    by_cases c : 0 ≤ o ∧ o < 0 + (s.gpr .a1).toNat
    · rw [ifp c, ifp c, vu o ho, vu (o + 2 ^ j) (by omega_using [hk, hp, c])]
    · rw [ifn c, ifn c, vu o ho]
  · rw [f₄, p₃.get .t5, p₂.get .t5, k₁.get .t5]

/-- Eleven passes shift the `n` bytes from `b` left by `a < 2^11`, zeros
coming in from the `2^10` bytes after them: RSASSA-PSS verification's
`shV_in` (ten passes), with one more. -/
theorem shV_in11 (V : Nat → Byte) (b n a : Nat) (hz : ∀ x, n ≤ x → x < n + 2 ^ 10 → V (b + x) = 0) :
    ∀ j ≤ 11, ∀ i < n, shV V b n a j (b + i) = if i + a % 2 ^ j < n then V (b + (i + a % 2 ^ j)) else 0
  | 0, _, i, hi => by simp only [shV, Nat.pow_zero, Nat.mod_one, Nat.add_zero]; rw [ifp hi]
  | j + 1, hj, i, hi => by
    obtain ih := shV_in11 V b n a hz j (by omega_using [hj])
    have hm : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * (a / 2 ^ j % 2) := Nat.mod_pow_succ
    obtain h2 := Nat.mod_lt (a / 2 ^ j) (show 0 < 2 by decide)
    obtain hp : 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_using [hj])
    obtain hmj := Nat.mod_lt a (Nat.two_pow_pos j)
    rw [shV, passV, ifp ⟨by omega_using [], by omega_using [hi]⟩]
    by_cases hb : a / 2 ^ j % 2 = 1
    · rw [ifp (decide_eq_true hb), show b + i + 2 ^ j = b + (i + 2 ^ j) by omega_using []]
      rw [hb, Nat.mul_one] at hm
      rw [hm]
      by_cases hl : i + 2 ^ j < n
      · rw [ih (i + 2 ^ j) hl, show i + 2 ^ j + a % 2 ^ j = i + (a % 2 ^ j + 2 ^ j) by omega_using []]
      · rw [shV_out V b n a j _ (by omega_using [hl]), hz _ (by omega_using [hl]) (by omega_using [hi, hp]),
          ifn (by omega_using [hl])]
    · have hb0 : a / 2 ^ j % 2 = 0 := by omega_using [hb]
      rw [ifn (by simpa using hb), hm, hb0, Nat.mul_zero, Nat.add_zero, ih i hi]

/-- The buffer's first `k` bytes to `out`. -/
theorem copyOut_ok {s v : State} {r0 : BitVec 64} (P : DPre true s) (h : Base s r0 v) :
    WP isa copyOut v fun v' => Base s r0 v' ∧
      v'.mem = writeBytes v.mem (s.gpr .a0) (Spec.Rsa.bytesAt v.mem (stackArg s 13) (s.gpr .a1).toNat) := by
  have hk := kk_le P
  unfold copyOut
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_mov fun t₃ o₃ e₃ => wp_nil ?_)
  have k₃ : Only [.a4, .a1, .a5] v t₃ := o₁.trans (o₂.trans o₃)
  refine WP.mono (copy_ok (p := s.gpr .a0) (q := stackArg s 13) (n := (s.gpr .a1).toNat) (by omega_using [hk])
    (by omega_using [hk]) (by rw [o₃.get .a1, e₂, o₁.get .a7, h.a7]) (by rw [o₃.get .a4, o₂.get .a4, e₁, h.a6])
    (by rw [e₃, o₂.get .t6, o₁.get .t6, h.t6, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [k₃.rd, k₃.wr]; exact scr_r P h.wr (by omega_using [hj, hk]))
    (fun i hi => by rw [k₃.wr]; exact out_w P h.wr hi)
    (fun j hj i hi => fun e => out_ne P hi (by omega_using [hj, hk]) e.symm)) fun t' ⟨hk', hm⟩ => ?_
  have K : Kept [.a4, .a1, .a5, .t0, .a4, .a1, .a5] v t' := k₃.keep.trans hk'
  exact ⟨h.kept K, by rw [hm, k₃.mem]⟩

/-- The return address back from its slot. -/
theorem ret_ok {s v : State} {r0 : BitVec 64} (S : Stk s) (h : Base s r0 v)
    (hra : v.mem.readW (E s + BitVec.ofNat 64 136) 64 = s.gpr .ra) :
    WP isa (.block Impl.RsaPkcs1Enc.RISCV64.Front.ret) v fun v' => Base s r0 v' ∧ v'.gpr .ra = s.gpr .ra ∧
      v'.mem = v.mem := by
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.ret
  simp only [Impl.RsaPkcs1Enc.RISCV64.Front.sRa]
  refine wp_addSp (imm := 0) fun t₀ o₀ e₀ => ?_
  refine wp_ld (a := E s + BitVec.ofNat 64 136) (by rw [e₀, h.sp, BitVec.add_zero]) (slot_al S (by decide))
    ⟨_, List.mem_append_right _ (by rw [o₀.wr, h.wr]; exact List.mem_cons_self ..), slot_in s (by decide)⟩
    fun t₁ o₁ e₁ => wp_nil ?_
  have k : Only [.t0, .ra] v t₁ := o₀.trans o₁
  exact ⟨h.kept k.keep, by rw [e₁, o₀.mem, hra], k.mem⟩

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

/-- The bytes written from `p`, read back. -/
theorem bytesAt_wb (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m p xs) p xs.length = xs := by
  refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [show writeBytes m p xs (p + BitVec.ofNat 64 i) = at_ (writeBytes m p xs) p i from rfl,
    at_wb _ _ _ (by omega_using [h, h2]), ifp h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

/-- The buffer, shifted left by the zeros before the message: the message,
then zeros. -/
theorem shifted {m1 m4 : Mem} {out S : Addr} {K : Nat} {M : List Byte} (hML : M.length ≤ K) (hK : K ≤ 1024)
    (hb : Spec.Rsa.bytesAt m1 out K = List.replicate (K - M.length) 0 ++ M) {V : Nat → Byte}
    (hV : ∀ x < 2048, V x = if x < K then m1 (out + BitVec.ofNat 64 x) else 0)
    (h4 : ∀ i < K, at_ m4 S i = shV V 0 K (K - M.length) 11 i) :
    Spec.Rsa.bytesAt m4 S K = M ++ List.replicate (K - M.length) 0 := by
  have key : ∀ j (hj : j < K), m1 (out + BitVec.ofNat 64 j) =
      (List.replicate (K - M.length) 0 ++ M)[j]'(by simp; omega_arith) := fun j hj => by
    have := congrArg (fun l : List Byte => l[j]?) hb
    simp only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
    rw [List.getElem?_eq_getElem (by simp; omega_arith)] at this
    exact Option.some.inj this
  have hz : ∀ x, K ≤ x → x < K + 2 ^ 10 → V (0 + x) = 0 := fun x h1 h2 => by
    rw [Nat.zero_add, hV x (by omega_using [hK, h2]), ifn (by omega_using [h1])]
  refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith) fun i h1 h2 => ?_
  have hi : i < K := by simpa [Spec.Rsa.bytesAt] using h1
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  have e := shV_in11 V 0 K (K - M.length) hz 11 (Nat.le_refl _) i hi
  simp only [Nat.zero_add] at e
  rw [show m4 (S + BitVec.ofNat 64 i) = at_ m4 S i from rfl, h4 i hi, e,
    Nat.mod_eq_of_lt (show K - M.length < 2 ^ 11 by omega_using [hK])]
  by_cases hiL : i < M.length
  · rw [ifp (by omega_arith : i + (K - M.length) < K), hV _ (by omega_arith), ifp (by omega_arith),
      key _ (by omega_arith), List.getElem_append_left hiL,
      List.getElem_append_right (by simp only [List.length_replicate]; omega_arith)]
    simp only [List.length_replicate, Nat.add_sub_cancel]
  · rw [List.getElem_append_right (by omega_arith), List.getElem_replicate, ifn (by omega_arith)]

/-! ## The postconditions, by name -/

theorem stk17 (s : State) :
    List.map (stackArg s) (List.range 17) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
      stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
      stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := rfl

theorem args_eq (s : State) : stkArgs 17 s = [s.gpr .a0, s.gpr .a1, s.gpr .a2, s.gpr .a3, s.gpr .a4, s.gpr .a5,
    s.gpr .a6, s.gpr .a7, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4,
    stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    stackArg s 12, stackArg s 13, stackArg s 14, stackArg s 15, stackArg s 16] := by
  simp only [stkArgs, argRegs, List.map_cons, List.map_nil, stk17, List.cons_append, List.nil_append]

/-- What decryption of the arguments of `s` gives. -/
def decOf (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .a4).toNat)

theorem cpost_of {s : State} {m : Mem} {r : BitVec 32}
    (h : Curry.apply (sig.words abi.ptrBits) postP (stkArgs 17 s) s.mem m r) :
    Proof.RsaPkcs1Enc.writtenMsgEnd m (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat r (decOf s) := by
  rw [args_eq] at h
  exact h

theorem fpost_to {s : State} {m : Mem} {r : BitVec 32}
    (h : Spec.RsaPkcs1Enc.writtenMsg m (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat r (decOf s)) :
    Curry.apply (sig.words abi.ptrBits) postFP (stkArgs 17 s) s.mem m r := by
  rw [args_eq]
  exact h

/-! ## After the call: the whole -/

theorem sub_ofNat_toNat {K L : Nat} (h : L ≤ K) (hK : K < 2 ^ 64) :
    BitVec.ofNat 64 K - BitVec.ofNat 64 L = BitVec.ofNat 64 (K - L) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- After the loads: the buffer shifted and copied back, the return address
back. -/
theorem tail_ok {s c v : State} (P : DPre true s) (S : Stk s) (R : Regs s) (hc : Called s c) (hv : Base s (c.gpr .a0) v)
    (h3 : v.gpr .t3 = s.gpr .a2) (hm : v.mem = c.mem) :
    WP isa tail v fun w => Base s (c.gpr .a0) w ∧ w.gpr .ra = s.gpr .ra ∧ Frame [bufR s, oR s] c.mem w.mem ∧
      ∃ M : List Byte, M.length ≤ (s.gpr .a1).toNat ∧
        Spec.Rsa.bytesAt w.mem (s.gpr .a0) (s.gpr .a1).toNat = M ++ List.replicate ((s.gpr .a1).toNat - M.length) 0 ∧
        ∀ m' : Mem, Spec.Rsa.bytesAt m' (s.gpr .a0) (s.gpr .a1).toNat =
            M ++ List.replicate ((s.gpr .a1).toNat - M.length) 0 →
          m'.readW (s.gpr .a2) 64 = c.mem.readW (s.gpr .a2) 64 →
          Spec.RsaPkcs1Enc.writtenMsg m' (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((c.gpr .a0).setWidth 32)
            (decOf s) := by
  have hk := kk_le P
  have h1 := P.h1
  obtain ⟨M, hML, hb, hml, hfin₀⟩ := shape (cpost_of hc.post)
  have hfin : ∀ m' : Mem, Spec.Rsa.bytesAt m' (s.gpr .a0) (s.gpr .a1).toNat =
      M ++ List.replicate ((s.gpr .a1).toNat - M.length) 0 → m'.readW (s.gpr .a2) 64 = c.mem.readW (s.gpr .a2) 64 →
      Spec.RsaPkcs1Enc.writtenMsg m' (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((c.gpr .a0).setWidth 32)
        (decOf s) := fun m' e₁ e₂ => hfin₀ m' (by rw [← h1]; exact e₁) e₂
  rw [← h1] at hML hb
  let K := (s.gpr .a1).toNat
  let Sc := stackArg s 13
  have hbo : ∀ x, Region.Contains (oR s) x 1 → (bufR s).Contains x 1 → False := fun x h₁ h₂ => out_buf P x h₁ h₂
  unfold tail
  refine WP.seq (WP.mono (diff_ok P hv h3) fun v₁ ⟨b₁, t3₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (clear_ok P b₁) fun v₂ ⟨b₂, t3₂, m₂⟩ => ?_)
  refine WP.seq (WP.mono (copyIn_ok P b₂) fun v₃ ⟨b₃, t3₃, m₃⟩ => ?_)
  have ha : v₃.gpr .t3 = BitVec.ofNat 64 (K - M.length) := by
    rw [t3₃, t3₂, t3₁, hm, hml, ← sub_ofNat_toNat hML (by omega_using [hk]), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (shift_ok P b₃ (a := K - M.length) (by omega_using [hk]) ha) fun v₄ ⟨b₄, f₄, s₄⟩ => ?_)
  refine WP.seq (WP.mono (copyOut_ok P b₄) fun v₅ ⟨b₅, m₅⟩ => ?_)
  -- The memory, from the call's on.
  have F2 : Frame [bufR s] c.mem v₂.mem := by
    rw [m₂, m₁, hm]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  have F3 : Frame [bufR s] v₂.mem v₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by
      rw [bytesAt_len]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hk])
  have F5 : Frame [oR s] v₄.mem v₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [bytesAt_len]; exact Region.contains_self _ _)
  have F : Frame [bufR s, oR s] c.mem v₅.mem :=
    (((F2.trans F3).trans f₄).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (F5.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  have hfr : ∀ x ∈ [bufR s, oR s], Region.Disjoint ⟨E s + BitVec.ofNat 64 136, 8⟩ x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact (((wr_stk R (by rw [P.hwr]; simp)).sub_left (buf_sub P)).sub_right (fr_stk s (by decide))).symm
    · exact ((wr_stk R (by rw [P.hwr]; simp)).sub_right (fr_stk s (by decide))).symm
  refine WP.mono (ret_ok S b₅ (by rw [F.readW (Region.contains_self _ _) hfr (by decide), hc.ra])) fun w ⟨bw, raw, mw⟩ =>
    ⟨bw, raw, by rw [mw]; exact F, M, hML, ?_, hfin⟩
  -- The buffer before the shift: `out`'s bytes, then zeros.
  have hV : ∀ x < 2048, at_ v₃.mem Sc x = if x < K then c.mem (s.gpr .a0 + BitVec.ofNat 64 x) else 0 := fun x hx => by
    rw [m₃, at_wb _ _ _ (by omega_using [hx]), bytesAt_len]
    by_cases h : x < K
    · rw [ifp h, ifp h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [bytesAt_len]; exact h)]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, Option.getD_some]
      exact F2 _ fun r hr hc' => by
        rw [List.mem_singleton.mp hr] at hc'
        exact hbo _ (Offset.contains_base _ (by omega_using [h]) (by omega_using [h, hk])) hc'
    · rw [ifn h, ifn h, m₂, at_wb _ _ _ (by omega_using [hx]), List.length_replicate, ifp hx,
        List.getD_eq_getElem?_getD, List.getElem?_replicate, ifp hx]
      rfl
  have hsh := shifted hML hk.1 hb hV fun i hi => s₄ i (by omega_using [hi, hk])
  have e := bytesAt_wb v₄.mem (s.gpr .a0) (Spec.Rsa.bytesAt v₄.mem (stackArg s 13) (s.gpr .a1).toNat)
    (by rw [bytesAt_len]; omega_using [hk])
  rw [bytesAt_len] at e
  rw [mw, m₅, e]
  exact hsh

/-! ## The whole function -/

/-- The postcondition of the contract with the message first, from the final
state's memory and result. -/
theorem post_fp {s f : State}
    (hf : Spec.RsaPkcs1Enc.writtenMsg f.mem (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((f.gpr .a0).setWidth 32)
      (decOf s)) : (C postFP 3632).post s f := by
  rw [post_stk hk]
  exact fpost_to hf

theorem front_wp {name : String} {callee : Prog isa} (hv : Verified target callee (C postP 3456))
    (hd : sdepth callee ≤ 3456) {s : State} (hs : (C postFP 3632).pre s) :
    WP isa (Impl.RsaPkcs1Enc.RISCV64.Front.code name callee) s fun f => abiPreserved s f ∧ (C postFP 3632).post s f := by
  have S := stk_of hs
  have R := regs_of hs
  have P := dpre_of hs
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.code
  simp only [Impl.RsaPkcs1Enc.RISCV64.Front.frameBytes]
  refine WP.alloc (by decide) (by have := S.le; omega_using [this]) ?_
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.body
  refine WP.seq (WP.mono (setup_ok hs) fun t T => ?_)
  refine WP.seq (WP.mono (call_ok hv hd hs T) fun c hc => ?_)
  refine WP.seq (WP.mono (load_ok P S hc) fun v ⟨bv, h3, hm⟩ => ?_)
  refine WP.mono (tail_ok P S R hc bv h3 hm) fun w ⟨bw, raw, fw, M, hML, hout, hfin⟩ m u fm => ?_
  -- The frame's bytes, which the `free` loses, lie apart from `out` and `msg_len`.
  have hfo : (oR s).Disjoint ⟨s.sp - BitVec.ofNat 64 176, 176⟩ :=
    (wr_stk R (by rw [P.hwr]; simp)).sub_right (frame_stk s)
  have hfm : (mlR s).Disjoint ⟨s.sp - BitVec.ofNat 64 176, 176⟩ :=
    (wr_stk R (by rw [P.hwr]; simp)).sub_right (frame_stk s)
  refine ⟨⟨fun r hr => bw.pres r hr, ?_, raw⟩, post_fp ?_⟩
  · show w.sp + BitVec.ofNat 64 176 = s.sp
    rw [bw.sp, BitVec.sub_add_cancel]
  · show Spec.RsaPkcs1Enc.writtenMsg m (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((w.gpr .a0).setWidth 32) (decOf s)
    rw [bw.a0]
    refine hfin m ?_ ?_
    · rw [bytes_ag (m₁ := w.mem) (L := (s.gpr .a1).toNat) (fun x hx => (fm x fun r hr hc' => by
        rw [List.mem_singleton.mp hr] at hc'; exact hfo x hx hc').symm) (Nat.le_refl _)]
      exact hout
    · rw [fm.readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hfm)
        (by decide), fw.readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact P.ms.sub_right (buf_sub P)
          · exact P.om.symm) (by decide)]

theorem front_correct {name : String} {callee : Prog isa} (hv : Verified target callee (C postP 3456))
    (hd : sdepth callee ≤ 3456) :
    ∀ s, (C postFP 3632).pre s → ∃ t s', Exec isa (Impl.RsaPkcs1Enc.RISCV64.Front.code name callee) s t s' ∧
      abiPreserved s s' ∧ (C postFP 3632).post s s' := fun s hs => by
  obtain ⟨t, s', he, ha, hp⟩ := front_wp hv hd hs
  exact ⟨t, s', he, ha, hp⟩

/-! ## Constant time -/

open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint ct_of)

/-- The memory of the callee's entry is the caller's in the buffers. -/
theorem entry_bufs {Q : sig.Post abi.ptrBits} {s t : State} (hs : (C Q 3632).pre s) (T : Stashed s t) :
    ∀ b ∈ Sig.bufs sig.params (stkArgs 17 s), ∀ x, b.1.Contains x 1 → s.mem x = t.mem x := fun b hb x hx =>
  (T.fr x fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact bufs_stk (regs_of hs) hb x hx (frame_stk s x hc)).symm

/-- The callee's public data, from the caller's. -/
theorem entry_pub {s₁ s₂ t₁ t₂ : State} (h₁ : (C postFP 3632).pre s₁) (h₂ : (C postFP 3632).pre s₂)
    (hp : (C postFP 3632).pub s₁ s₂) (T₁ : Stashed s₁ t₁) (T₂ : Stashed s₂ t₂) :
    (C postP 3456).pub (t₁.callEntry.withRegions (cRd s₁) (cWr s₁)) (t₂.callEntry.withRegions (cRd s₂) (cWr s₂)) := by
  rw [pubL_stk hk hnl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [entry_args T₁, entry_args T₂]
  refine ⟨⟨by show t₁.sp = t₂.sp; rw [T₁.sp, T₂.sp, E, E, hsp], ?_⟩, hpa⟩
  show Curry.apply _ leakP (stkArgs 17 s₁) t₁.mem = Curry.apply _ leakP (stkArgs 17 s₂) t₂.mem
  rw [← leakP_local (args_length s₁) (regs_of h₁).pre (entry_bufs h₁ T₁),
    ← leakP_local (args_length s₂) (regs_of h₂).pre (entry_bufs h₂ T₂)]
  exact hlk

theorem front_ct {name : String} {callee : Prog isa} (hv : Verified target callee (C postP 3456))
    (hd : sdepth callee ≤ 3456) :
    ConstantTime isa (C postFP 3632).pre (C postFP 3632).pub (Impl.RsaPkcs1Enc.RISCV64.Front.code name callee) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have Q := Dec.same_ofP (s₁ := σ₁) (s₂ := σ₂) hq
  have S₁ := stk_of p₁
  have S₂ := stk_of p₂
  have P₁ := dpre_of p₁
  have P₂ := dpre_of p₂
  have R₁ := regs_of p₁
  have R₂ := regs_of p₂
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.code
  simp only [Impl.RsaPkcs1Enc.RISCV64.Front.frameBytes]
  refine RelCT.alloc ((?_ : RelCT isa (Eq2 (allocd 176 σ₁) (allocd 176 σ₂)) _ TT).mono
    (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)
  unfold Impl.RsaPkcs1Enc.RISCV64.Front.body
  -- The copies and the slots, at the stack pointer.
  refine rel_seq (rel_taint [] (show σ₁.sp - _ = σ₂.sp - _ by rw [Q.sp]) (by simp) (by taint_decide))
    (setup_ok p₁) (setup_ok p₂) fun t₁ t₂ T₁ T₂ => ?_
  -- The call, by the callee's contract.
  refine rel_seq (RelCT.callEx hv.1 hv.2.1 fun a b ⟨ha, hb⟩ => ?_) (call_ok hv hd p₁ T₁) (call_ok hv hd p₂ T₂)
    fun c₁ c₂ hc₁ hc₂ => ?_
  · subst ha hb
    have cov : ∀ {s t : State} (R : Regs s) (T : Stashed s t), Covers (cRd s ++ cWr s) (t.rd ++ t.wr) ∧
        Covers (cWr s) t.wr := fun {s t} R T =>
      ⟨Covers.of_sub fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · rcases cRd_rd R hx with hx | rfl
          · exact ⟨x, List.mem_append_left _ (by rw [T.rd]; exact hx), 0, (BitVec.add_zero _).symm, by omega_using []⟩
          · exact ⟨⟨E s, 176⟩, List.mem_append_right _ (by rw [T.wr]; exact List.mem_cons_self ..), 8 * 0, rfl,
              by show 8 * 0 + 8 * 17 ≤ 176; decide⟩
        · exact ⟨x, List.mem_append_right _ (by rw [T.wr]; exact List.mem_cons_of_mem _ (cWr_wr R hx)), 0,
            (BitVec.add_zero _).symm, by omega_using []⟩,
      Covers.of_mem fun x hx => by rw [T.wr]; exact List.mem_cons_of_mem _ (cWr_wr R hx)⟩
    exact ⟨cRd σ₁, cWr σ₁, cRd σ₂, cWr σ₂, entry_pre p₁ T₁, entry_pre p₂ T₂, entry_pub p₁ p₂ hq T₁ T₂,
      (cov R₁ T₁).1, (cov R₁ T₁).2, (cov R₂ T₂).1, (cov R₂ T₂).2⟩
  -- The loads, at the stack pointer.
  refine rel_seq (rel_taint [] (by rw [hc₁.sp, hc₂.sp, E, E, Q.sp]) (by simp) (by taint_decide))
    (load_ok P₁ S₁ hc₁) (load_ok P₂ S₂ hc₂) fun v₁ v₂ ⟨b₁, h3₁, _⟩ ⟨b₂, h3₂, _⟩ => ?_
  -- The rest, from `scratch`, `out`, `k` and `msg_len`.
  refine rel_taint [.a6, .a7, .t6, .t3] (by rw [b₁.sp, b₂.sp, E, E, Q.sp]) (fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [b₁.a6, b₂.a6, Q.arg 13 (by decide)]
  · rw [b₁.a7, b₂.a7, Q.gpr .a0 (by decide)]
  · rw [b₁.t6, b₂.t6, Q.gpr .a1 (by decide)]
  · rw [h3₁, h3₂, Q.gpr .a2 (by decide)]

/-! ## `Verified` -/

theorem front_sat : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3632).pre s := by
  refine ⟨Dec.preState, ?_⟩
  have e : (3632 : Nat) = 3631 + 1 := rfl
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    abi, argRegs, Dec.stackArgs_seventeen, List.append_eq, List.range,
    List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := Dec.pre_args
  have ha : stackArgAddr Dec.preState 0 = 0x10000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, ha]
  sig_and_intros
  rotate_right 4
  · exact Dec.preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (unfold Spec.Rsa.lenValid; decide)

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling any code verified
against `vg_rsa_pkcs1_decrypt_precomputed_body`'s contract with 3456 bytes of
stack. -/
theorem front_verified {name : String} {callee : Prog isa}
    (hv : Verified target callee (Proof.RsaPkcs1Enc.decryptPrecomputedBodyContract abi 3456))
    (hd : sdepth callee ≤ 3456) :
    Verified target (Impl.RsaPkcs1Enc.RISCV64.Front.code name callee)
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3632) := by
  rw [cK_eq] at hv
  rw [fK_eq]
  exact ⟨front_correct hv hd, front_ct hv hd, by rw [← fK_eq]; exact front_sat⟩

/-! ## Without secret residue -/

open VG.RISCV64.Scrub

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem front_postOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
      (Proof.RsaPkcs1Enc.decryptPrecomputedBodySig.retBits 64) := by
  rw [fK_eq]
  refine postOut_of_local_pre (leak := some _) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => ?_
  obtain ⟨o, oL, ml, n, nL, e, eL, d, dL, i, iL, p, pL, q, qL, dp, dpL, dq, dqL, qi, qiL, sc, scL, pre, preL, rfl⟩ :=
    vs25 hlen
  simp only [sig, Proof.RsaPkcs1Enc.decryptPrecomputedBodySig, Proof.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
    Nat.mul_one] at hb
  obtain ⟨bo, bm, -⟩ := hb
  replace hpre : preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m := hpre
  simp only [preP, toNat_ptr] at hpre
  have hol := hpre.2.1
  replace h : postFP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m m₁ r := h
  show postFP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m m₂ r
  simp only [postFP, toNat_ptr] at h ⊢
  have hby : Spec.Rsa.bytesAt m₂ o nL.toNat = Spec.Rsa.bytesAt m₁ o nL.toNat :=
    bytes_ag (k := nL.toNat) bo (by omega_arith)
  have hw : Spec.Rsa.wordsAt m₂ ml 1 = Spec.Rsa.wordsAt m₁ ml 1 := words_ag (k := 1) bm (by omega_arith)
  revert h
  generalize Spec.RsaPkcs1Enc.decrypt _ _ _ _ _ _ _ _ _ = oc
  cases oc <;> simp only [Spec.RsaPkcs1Enc.writtenMsg, hby, hw] <;> exact id

theorem codeP_depth : sdepth Impl.RsaPkcs1Enc.RISCV64.Decrypt.codeP ≤ 3456 := by lit_decide

/-- `vg_rsa_pkcs1_decrypt_precomputed` as emitted: `Front.code`
calling `vg_rsa_pkcs1_decrypt_precomputed_body`'s code before its cleanup, as an
internal function of its own, then the cleanup of the 3632 bytes of stack it
and its callee use. -/
theorem decryptPrecomputed :
    VerifiedScrubbed target Impl.RsaPkcs1Enc.RISCV64.Fn.decryptPrecomputed
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3632) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.decryptPrecomputedApi) (W := 3632)
    { code := Impl.RsaPkcs1Enc.RISCV64.Front.code Impl.RsaPkcs1Enc.RISCV64.Fn.bodyName
        Impl.RsaPkcs1Enc.RISCV64.Decrypt.codeP
      verified := front_verified Dec.codeP_verified codeP_depth }
    (front_postOut _) (by lit_decide)

end VG.Proof.RsaPkcs1Enc.RISCV64.Front
