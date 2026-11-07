module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Entry
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.PcVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Callees
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndTaint
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rc2.PairMem

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on ARMv7: the layout, the scan and the call's arguments

`EP`: what two runs share (the frame's base `B`, the pointers, the lengths,
`e`, the words of `pre`, and the trace of drawing `PS`, `mask`), and its
layout (`EP.lay`), with the stack of the call below the frame (`C`). `In P σ`:
the state `σ` the body starts from; `S P σ s`: a state of the body. The
shared contract gives `In (ep s) (entered frameBytes s)` (`in_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm

/-- What two runs share. -/
structure EP where
  B : BitVec 32
  out : BitVec 32
  tape : BitVec 32
  n : BitVec 32
  e : BitVec 32
  msg : BitVec 32
  rand : BitVec 32
  scr : BitVec 32
  pre : BitVec 32
  K : Nat
  el : Nat
  ml : Nat
  rl : Nat
  sl : Nat
  ql : Nat
  nB : List Byte
  eB : List Byte
  pw : List (BitVec 64)
  mask : List Nat

/-- The stack of the call: `vg_rsa_pkcs1_encrypt_precomputed`'s. -/
abbrev callStack : Nat := 1168

namespace EP

variable (P : EP)

abbrev OUT : Region := ⟨State.addr P.out, P.K⟩
abbrev TAPE : Region := ⟨State.addr P.tape, 16⟩
abbrev N : Region := ⟨State.addr P.n, P.K⟩
abbrev E : Region := ⟨State.addr P.e, P.el⟩
abbrev MSG : Region := ⟨State.addr P.msg, P.ml⟩
abbrev RAND : Region := ⟨State.addr P.rand, P.rl⟩
abbrev SCR : Region := ⟨State.addr P.scr, P.sl * 8⟩
abbrev PRE : Region := ⟨State.addr P.pre, P.ql * 8⟩

/-- The length of `PS`. -/
abbrev pl : Nat := P.K - P.ml - 3

/-- The arguments, in order. -/
abbrev argv : List (BitVec 32) :=
  [P.out, BitVec.ofNat 32 P.K, P.tape, P.n, BitVec.ofNat 32 P.K, P.e, BitVec.ofNat 32 P.el, P.msg,
    BitVec.ofNat 32 P.ml, P.rand, BitVec.ofNat 32 P.rl, P.scr, BitVec.ofNat 32 P.sl, P.pre,
    BitVec.ofNat 32 P.ql]

abbrev lay : Lay where
  B := P.B
  F := frameBytes
  A := 44
  argv := P.argv
  ro := [P.N, P.E, P.MSG, P.RAND, P.PRE]
  rw := [P.OUT, P.TAPE, P.SCR]
  C := callStack

end EP

/-- The tape, as the state `σ` holds it. -/
abbrev randB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.rand) P.rl

/-- The state the body starts from. -/
structure In (P : EP) (σ : State) : Prop where
  ok : P.lay.Ok σ
  kv : Spec.Rsa.lenValid P.K
  el1 : 1 ≤ P.el
  elK : P.el ≤ P.K
  mlK : P.ml + 11 ≤ P.K
  rlK : P.rl ≤ Spec.RsaPkcs1Enc.padEntropy P.pl
  slK : Spec.Rsa.publicScratchWords P.K ≤ P.sl
  qlK : P.ql = Spec.Rsa.precomputedWords P.K
  nB : Spec.Rsa.bytesAt σ.mem (State.addr P.n) P.K = P.nB
  eB : Spec.Rsa.bytesAt σ.mem (State.addr P.e) P.el = P.eB
  pw : Spec.Rsa.wordsAt σ.mem (State.addr P.pre) P.ql = P.pw
  mask : (Spec.RsaPkcs1Enc.padSearch P.pl (randB P σ)).trace = P.mask

/-- A state of the body. -/
abbrev S (P : EP) (σ s : State) : Prop := In P σ ∧ P.lay.St σ s

namespace In

variable {P : EP} {σ : State} (h : In P σ)
include h

theorem k64 : 64 ≤ P.K := h.kv.1
theorem k1024 : P.K ≤ 1024 := h.kv.2
theorem pl8 : 8 ≤ P.pl := by have := h.mlK; show 8 ≤ P.K - P.ml - 3; omega
theorem pl_le : P.pl ≤ 1021 := by have := h.k1024; show P.K - P.ml - 3 ≤ 1021; omega
theorem rl_le : P.rl ≤ P.pl + 128 := h.rlK

end In

/-! ## The entry -/

/-- The stack the function uses: the push, the inner frame and the call's. -/
abbrev stackBytes : Nat := 56 + frameBytes + callStack

/-- The shared contract, with that stack. -/
abbrev spec : Contract isa := Spec.RsaPkcs1Enc.encryptRandomContract abi stackBytes

/-- The public parameters of an entry state. -/
def ep (s : State) : EP where
  B := s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 frameBytes
  out := s.gpr .r0
  tape := s.gpr .r2
  n := s.gpr .r3
  e := stackArg s 1
  msg := stackArg s 3
  rand := stackArg s 5
  scr := stackArg s 7
  pre := stackArg s 9
  K := (stackArg s 0).toNat
  el := (stackArg s 2).toNat
  ml := (stackArg s 4).toNat
  rl := (stackArg s 6).toNat
  sl := (stackArg s 8).toNat
  ql := (stackArg s 10).toNat
  nB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat
  pw := Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 9)) (stackArg s 10).toNat
  mask := (Spec.RsaPkcs1Enc.padSearch ((stackArg s 0).toNat - (stackArg s 4).toNat - 3)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 5)) (stackArg s 6).toNat)).trace

theorem ep_lay (s : State) :
    (ep s).lay = layOf frameBytes 44 (ep s).argv [(ep s).N, (ep s).E, (ep s).MSG, (ep s).RAND, (ep s).PRE]
      [(ep s).OUT, (ep s).TAPE, (ep s).SCR] s callStack := rfl

theorem in_of_pre {s : State} (h : spec.pre s) : In (ep s) (entered frameBytes s) := by
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val] at h
  sig_split h
  rename_i hsp hsa hrd hwr oT oN oE oM oR oS oQ oA tN tE tM tR tS tQ tA nS eS mS rS sQ sA
    kO kT kN kE kM kR kS kQ kA fO fT fN fE fM fR fS fQ kv olk el1 elK mlK rlK slK
  have qlK := h
  have h2312 : 2312 ≤ s.sp.toNat := hsp
  have r1 : s.gpr .r1 = stackArg s 0 := BitVec.eq_of_toNat_eq olk
  rw [olk] at hwr oT oN oE oM oR oS oQ oA kO fO
  have hpush : Frame [FrameStack.belowA s.sp 56] s.mem (entered frameBytes s).mem :=
    FrameStack.pushed_frameA (rs := Impl.RsaPkcs1Sig.Arm.pushRegs) (by show 56 ≤ s.sp.toNat; omega_arith)
  have below : Region.Sub (FrameStack.belowA s.sp 56)
      ⟨State.addr s.sp - BitVec.ofNat 64 2312, 2312⟩ := by
    show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ _
    rw [FrameStack.addr_sub' (by omega_arith)]
    exact Offset.sub_below _ (by omega_arith) (by omega_arith)
  have hok : (ep s).lay.Ok (entered frameBytes s) := by
    rw [ep_lay]
    refine ok_entered (by decide) (by decide) rfl hsp hsa hrd hwr ?_ ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [kN, kE, kM, kR, kQ, kO, kT, kS, kA]
    · intro w hw r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hw with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [oN, oE, oM, oR, oQ, oA, tN, tE, tM, tR, tQ, tA, nS.symm, eS.symm, mS.symm, rS.symm, sQ, sA]
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_pair.mpr tS⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      exacts [oT, oS]
    · intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [fN, fE, fM, fR, fQ, fO, fT, fS]
    · intro j hj
      rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
      · rfl
      · simp [regArg, ep, r1]
      · rfl
      · rfl
    · intro i hi
      rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
        i = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ep]
  have ro := fun {R : Region} (hR : R ∈ [(ep s).N, (ep s).E, (ep s).MSG, (ep s).RAND, (ep s).PRE]) =>
    entered_ro (F := frameBytes) (A := 44) (C := callStack) (argv := (ep s).argv)
      (rw := [(ep s).OUT, (ep s).TAPE, (ep s).SCR]) hok (show 56 + 1088 ≤ s.sp.toNat by omega_arith) hR
  refine
    { ok := hok
      kv := kv, el1 := el1, elK := elK, mlK := mlK, rlK := rlK, slK := slK, qlK := qlK
      nB := ro (R := (ep s).N) (by simp)
      eB := ro (R := (ep s).E) (by simp)
      pw := wordsAt_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (kQ.sub_left below).symm)
        (by show (stackArg s 10).toNat * 8 ≤ 2 ^ 64; omega_arith)
      mask := by
        show (Spec.RsaPkcs1Enc.padSearch _ (Spec.Rsa.bytesAt _ (ep s).RAND.base (ep s).RAND.len)).trace = _
        rw [ro (R := (ep s).RAND) (by simp)]
        rfl }

end VG.Proof.RsaPkcs1Enc.Arm.Rnd

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

/-! ## The scan

After `i` octets of the tape, the scan has kept their nonzero octets,
`kept P σ i`, at the start of `PS` (`At`). The trace in `EP` fixes how many
octets the scan reads (`N`), which of them are zero and how many it has kept
after each: the branches and the loop's iterations are the same in two runs
(`scan_vp`). The scan ends at `N` (`Done`), with `PS` full, the padding
string of `nonzeroPrefix` (`accept_of`), or the tape read with fewer nonzero
octets (`reject_of`).
-/

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Enc (nz scanLen)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_ldrb wp_strb wp_cmp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## The tape -/

/-- The kept octets after `i` octets of the tape, and how many. -/
abbrev kept (P : EP) (σ : State) (i : Nat) : List Byte := nz ((randB P σ).take i)
abbrev cnt (P : EP) (σ : State) (i : Nat) : Nat := (kept P σ i).length

/-- The octets the scan reads, from the trace. -/
abbrev N (P : EP) : Nat := P.mask.length

theorem nonzeroPrefix_fst : ∀ {n : Nat} {R : List Byte} {r : List Byte × Nat},
    Spec.RsaPkcs1Enc.nonzeroPrefix n R = some r → r.1 = nz (R.take r.2) ∧ r.1.length = n
  | 0, R, r, h => by
    simp only [Spec.RsaPkcs1Enc.nonzeroPrefix, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | n + 1, [], r, h => by simp [Spec.RsaPkcs1Enc.nonzeroPrefix] at h
  | n + 1, b :: R, r, h => by
    simp only [Spec.RsaPkcs1Enc.nonzeroPrefix] at h
    split at h
    · rename_i hb
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨e, l⟩ := nonzeroPrefix_fst h'
      refine ⟨?_, l⟩
      rw [List.take_succ_cons, hb, VG.Proof.RsaPkcs1Enc.nz_cons_zero]; exact e
    · rename_i hb
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨e, l⟩ := nonzeroPrefix_fst h'
      refine ⟨?_, by simp [l]⟩
      rw [List.take_succ_cons, VG.Proof.RsaPkcs1Enc.nz_cons_ne hb, e]

theorem scanLen_pos : ∀ {n : Nat} {R : List Byte}, 0 < n → R ≠ [] → 0 < scanLen n R
  | 0, _, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ + 1, [], _, h => absurd rfl h
  | _ + 1, b :: _, _, _ => by simp only [scanLen]; split <;> omega

section

variable {P : EP} {σ σ₁ σ₂ : State}

theorem randB_length (P : EP) (σ : State) : (randB P σ).length = P.rl := bytesAt_length _ _ _

theorem In.scan (h : In P σ) : scanLen P.pl (randB P σ) = N P := by
  rw [N, ← h.mask, VG.Proof.RsaPkcs1Enc.trace_eq, VG.Proof.RsaPkcs1Enc.zeroMask_length, List.length_take,
    Nat.min_eq_left (VG.Proof.RsaPkcs1Enc.scanLen_le _ _)]

theorem In.N_le (h : In P σ) : N P ≤ P.rl := by
  rw [← h.scan, ← randB_length P σ]; exact VG.Proof.RsaPkcs1Enc.scanLen_le _ _

theorem cnt_eq (h₁ : In P σ₁) (h₂ : In P σ₂) {i : Nat} (hi : i ≤ N P) : cnt P σ₁ i = cnt P σ₂ i :=
  VG.Proof.RsaPkcs1Enc.nz_take_length_eq (h₁.mask.trans h₂.mask.symm) i (by rw [h₁.scan]; exact hi)

theorem zero_eq (h₁ : In P σ₁) (h₂ : In P σ₂) {i : Nat} (hi : i < N P) :
    ((randB P σ₁).getD i 0 = 0 ↔ (randB P σ₂).getD i 0 = 0) :=
  VG.Proof.RsaPkcs1Enc.zero_iff (h₁.mask.trans h₂.mask.symm) (by rw [h₁.scan]; exact hi)

theorem nz_length_split (R : List Byte) (i : Nat) :
    (nz R).length = (nz (R.take i)).length + (nz (R.drop i)).length := by
  rw [← List.length_append, ← VG.Proof.RsaPkcs1Enc.nz_append, List.take_append_drop]

/-- `PS` full at the end of the scan: the padding string of `nonzeroPrefix`. -/
theorem accept_of (h : In P σ) (hc : cnt P σ (N P) = P.pl) :
    Spec.RsaPkcs1Enc.nonzeroPrefix P.pl (randB P σ) = some (kept P σ (N P), N P) := by
  have hle : P.pl ≤ (nz (randB P σ)).length := by
    have : (nz ((randB P σ).take (N P))).length = P.pl := hc
    rw [nz_length_split _ (N P)]; omega
  obtain ⟨r, hr⟩ := VG.Proof.RsaPkcs1Enc.nonzeroPrefix_isSome hle
  have h2 := VG.Proof.RsaPkcs1Enc.used_eq hr
  rw [h.scan] at h2
  rw [hr, show r = (r.1, r.2) from rfl, (nonzeroPrefix_fst hr).1, h2]

/-- `PS` not full at the end of the scan: the tape read, with fewer nonzero octets. -/
theorem reject_of (h : In P σ) (hc : cnt P σ (N P) ≠ P.pl) :
    (nz (randB P σ)).length < P.pl ∧ N P = P.rl ∧ cnt P σ (N P) < P.pl := by
  have hlt : (nz (randB P σ)).length < P.pl := by
    rcases Nat.lt_or_ge (nz (randB P σ)).length P.pl with h' | h'
    · exact h'
    · exfalso
      obtain ⟨r, hr⟩ := VG.Proof.RsaPkcs1Enc.nonzeroPrefix_isSome h'
      have h2 := VG.Proof.RsaPkcs1Enc.used_eq hr
      rw [h.scan] at h2
      obtain ⟨e, l⟩ := nonzeroPrefix_fst hr
      rw [e, h2] at l
      exact hc l
  have hN : N P = P.rl := by
    rw [← h.scan, VG.Proof.RsaPkcs1Enc.scanLen_all hlt, randB_length]
  refine ⟨hlt, hN, ?_⟩
  rw [cnt, kept, hN, List.take_of_length_le (by rw [randB_length])]
  exact hlt

end

/-! ## Arithmetic -/

theorem sub3 {K ml : Nat} (h : ml + 11 ≤ K) (hK : K ≤ 1024) :
    BitVec.ofNat 32 K - BitVec.ofNat 32 ml - 3 = BitVec.ofNat 32 (K - ml - 3) := by
  apply BitVec.eq_of_toNat_eq
  have e3 : (3 : BitVec 32).toNat = 3 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, e3]
  omega_arith

theorem ofNat_succ (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e1]
  omega_arith

theorem setWidth_byte (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega_arith

theorem z_byte (b : Byte) : (b.setWidth 32 - 0 == 0) = decide (b = 0) := by
  rw [show b.setWidth 32 - 0 = b.setWidth 32 from BitVec.sub_zero _]
  by_cases h : b = 0
  · subst h; rfl
  · have : b.setWidth 32 ≠ 0 := fun e => h (by rw [← setWidth_byte b, e]; rfl)
    exact (beq_eq_false_iff_ne.mpr this).trans (decide_eq_false h).symm

theorem ofNat_sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases e : a = b
  · subst e; simp
  · have : BitVec.ofNat 32 a - BitVec.ofNat 32 b ≠ 0 := by
      intro h
      apply e
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      have e0 : (0 : BitVec 32).toNat = 0 := rfl
      rw [e0] at this
      omega_arith
    simp only [e, decide_false, beq_eq_false_iff_ne]
    exact this

/-! ## The stages -/

/-- `PS`'s first bytes. -/
def BufL (P : EP) (s : State) (l : List Byte) : Prop :=
  ∀ j < l.length, s.mem (P.lay.fr (oBuf + j)) = l.getD j 0

/-- After `start`. -/
def G1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ s.gpr .r1 = P.rand ∧ s.gpr .r8 = BitVec.ofNat 32 P.rl ∧ s.gpr .r3 = BitVec.ofNat 32 P.pl ∧
    s.gpr .r0 = P.B + BitVec.ofNat 32 oBuf ∧ s.gpr .r4 = 0 ∧ s.gpr .r5 = 0

/-- After `i` octets of the tape. -/
structure At (P : EP) (σ : State) (i : Nat) (s : State) : Prop where
  st : S P σ s
  hi : i ≤ P.rl
  hc : cnt P σ i ≤ P.pl
  r0 : s.gpr .r0 = P.B + BitVec.ofNat 32 (oBuf + cnt P σ i)
  r1 : s.gpr .r1 = P.rand + BitVec.ofNat 32 i
  r3 : s.gpr .r3 = BitVec.ofNat 32 P.pl
  r4 : s.gpr .r4 = BitVec.ofNat 32 i
  r5 : s.gpr .r5 = BitVec.ofNat 32 (cnt P σ i)
  r8 : s.gpr .r8 = BitVec.ofNat 32 P.rl
  buf : BufL P s (kept P σ i)

/-- After the load of octet `i`. -/
structure Ld (P : EP) (σ : State) (i : Nat) (s : State) : Prop where
  st : S P σ s
  hN : i < N P
  hc : cnt P σ i < P.pl
  r0 : s.gpr .r0 = P.B + BitVec.ofNat 32 (oBuf + cnt P σ i)
  r1 : s.gpr .r1 = P.rand + BitVec.ofNat 32 (i + 1)
  r3 : s.gpr .r3 = BitVec.ofNat 32 P.pl
  r4 : s.gpr .r4 = BitVec.ofNat 32 (i + 1)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (cnt P σ i)
  r6 : s.gpr .r6 = ((randB P σ).getD i 0).setWidth 32
  r8 : s.gpr .r8 = BitVec.ofNat 32 P.rl
  z : s.z = decide ((randB P σ).getD i 0 = 0)
  buf : BufL P s (kept P σ i)

/-- Before octet `i`, with octets left and `PS` not full. -/
def A (P : EP) (i : Nat) (σ s : State) : Prop := At P σ i s ∧ i < N P ∧ cnt P σ i < P.pl

/-- After octet `i`. -/
def B1 (P : EP) (i : Nat) (σ s : State) : Prop := At P σ (i + 1) s ∧ i < N P ∧ cnt P σ i < P.pl

/-- The end of the scan. -/
def Done (P : EP) (σ s : State) : Prop := At P σ (N P) s

section

variable {P : EP} {σ s : State}

theorem kept_succ {i : Nat} (hi : i < P.rl) :
    kept P σ (i + 1) =
      if (randB P σ).getD i 0 = 0 then kept P σ i else kept P σ i ++ [(randB P σ).getD i 0] := by
  have hl : i < (randB P σ).length := by rw [randB_length]; exact hi
  have e : (randB P σ).take (i + 1) = (randB P σ).take i ++ [(randB P σ).getD i 0] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp only [kept, e]
  split
  · rename_i h; rw [h, VG.Proof.RsaPkcs1Enc.nz_zero]
  · rename_i h; exact VG.Proof.RsaPkcs1Enc.nz_ne h _

theorem start_wp (hs : S P σ s) : WP isa (.block start) s (G1 P σ) := by
  have hK := hs.1.k1024
  have hml := hs.1.mlK
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t1 u1 => ?_
  have s1 : P.lay.St σ t1 := hs.2.of_rest (u1.rest (ws := [.r12]) (by simp)) u1.mem
  refine s1.wp_arg (j := 9) (by simp) (by dsimp only; decide) fun t2 s2 u2 => ?_
  refine s2.wp_arg (j := 10) (by simp) (by dsimp only; decide) fun t3 s3 u3 => ?_
  refine s3.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t4 s4 u4 => ?_
  refine s4.wp_arg (j := 8) (by simp) (by dsimp only; decide) fun t5 s5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun t6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun t7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun t8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun t9 u9 => ?_
  refine wp_mov (op2_imm (by decide)) fun t10 u10 => WP.block_nil ⟨⟨hs.1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((s5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem).of_rest (u7.rest (ws := [.r3]) (by simp))
      u7.mem).of_rest (u8.rest (ws := [.r0]) (by simp)) u8.mem).of_rest (u9.rest (ws := [.r4]) (by simp))
      u9.mem).of_rest (u10.rest (ws := [.r5]) (by simp)) u10.mem
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
    rfl
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    rfl
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), u7.gpr, dpVal, u6.gpr, dpVal,
      u5.gpr, u5.other _ (by decide), u4.gpr]
    exact sub3 hml hK
  · rw [u10.other _ (by decide), u9.other _ (by decide), u8.gpr, dpVal, u7.other _ (by decide),
      u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.gpr, hs.2.sp, BitVec.add_zero]
  · rw [u10.other _ (by decide), u9.gpr]
  · rw [u10.gpr]

theorem at0 (h : G1 P σ s) : At P σ 0 s := by
  obtain ⟨hs, r1, r8, r3, r0, r4, r5⟩ := h
  have := hs.1.pl8
  exact ⟨hs, Nat.zero_le _, Nat.zero_le _, by rw [r0]; rfl, by rw [r1]; simp, r3, by rw [r4]; rfl,
    by rw [r5]; rfl, r8, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem load_wp {i : Nat} (h : A P i σ s) : WP isa (.block load) s (Ld P σ i) := by
  obtain ⟨h, hN, hc⟩ := h
  have hs := h.st
  have hNl := hs.1.N_le
  have hfr := hs.1.ok.fits P.RAND (by simp)
  simp only [Proof.X25519.Arm.addr_toNat] at hfr
  have hi : i < P.rl := by omega_arith
  have hrlK := hs.1.rl_le
  have hpl := hs.1.pl_le
  have hA : State.addr (P.rand + BitVec.ofNat 32 i) = State.addr P.rand + BitVec.ofNat 64 i :=
    addr_add (by omega_arith)
  have hval : s.mem (State.addr P.rand + BitVec.ofNat 64 i) = (randB P σ).getD i 0 := by
    have := congrArg (fun l => l.getD i 0) (hs.2.ro (R := P.RAND) (by simp))
    simp only at this
    rw [bytesAt_getD hi] at this
    exact this
  refine wp_ldrb (by decide) (a := State.addr P.rand + BitVec.ofNat 64 i) (by rw [h.r1, BitVec.add_zero, hA])
    ⟨P.RAND, List.mem_append_left _ (by rw [hs.2.rd, hs.2.ok.rd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun t1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t4 u4 z4 => WP.block_nil ⟨⟨hs.1, ?_⟩, hN, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact ((hs.2.of_rest (u1.rest (ws := [.r6]) (by simp)) u1.mem).of_rest (u2.rest (ws := [.r1]) (by simp))
      u2.mem).of_rest (u3.rest (ws := [.r4]) (by simp)) u3.mem |>.of_rest (u4.rest []) u4.mem
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r0]
  · rw [u4.gpr, u3.other _ (by decide), u2.gpr, dpVal, u1.other _ (by decide), h.r1]
    exact Offset.add_ofNat_add_one _ _
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r3]
  · rw [u4.gpr, u3.gpr, dpVal, u2.other _ (by decide), u1.other _ (by decide), h.r4, ofNat_succ]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r5]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hval]
  · rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.r8]
  · rw [z4, u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hval, z_byte]
  · intro j hj
    rw [u4.mem, u3.mem, u2.mem, u1.mem]
    exact h.buf j hj

theorem skip_at {i : Nat} (h : Ld P σ i s) (hz : (randB P σ).getD i 0 = 0) : B1 P i σ s := by
  have hNl := h.st.1.N_le
  have hN := h.hN
  have hk : kept P σ (i + 1) = kept P σ i := by rw [kept_succ (by omega_arith), ite_eq_left hz]
  exact ⟨⟨h.st, by omega_arith, by rw [cnt, hk]; exact Nat.le_of_lt h.hc, by rw [cnt, hk]; exact h.r0, h.r1, h.r3,
    h.r4, by rw [cnt, hk]; exact h.r5, h.r8, by rw [hk]; exact h.buf⟩, h.hN, h.hc⟩

theorem keep_wp {i : Nat} (h : Ld P σ i s) (hz : (randB P σ).getD i 0 ≠ 0) :
    WP isa (.block keep) s (B1 P i σ) := by
  have hs := h.st
  have hNl := hs.1.N_le
  have hpl := hs.1.pl_le
  have hc := h.hc
  have hc' : (kept P σ i).length < P.pl := h.hc
  have hN := h.hN
  have hk : kept P σ (i + 1) = kept P σ i ++ [(randB P σ).getD i 0] := by
    rw [kept_succ (by omega_arith), ite_eq_right hz]
  have hl : cnt P σ (i + 1) = cnt P σ i + 1 := by rw [cnt, hk]; simp
  have hF : oBuf + cnt P σ i + 1 ≤ P.lay.F := by show oBuf + cnt P σ i + 1 ≤ frameBytes; simp only [oBuf, frameBytes]; omega_arith
  refine wp_strb (by decide) (a := P.lay.fr (oBuf + cnt P σ i)) ?_ (hs.2.inFr hF) fun t1 u1 => ?_
  · rw [h.r0, BitVec.add_zero]
    exact hs.2.ok.addrB (by show _ < frameBytes + 56 + 44; simp only [oBuf, frameBytes]; omega_arith)
  have s1 : P.lay.St σ t1 := hs.2.frameW hF (by
    rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
    u1.rd u1.wr u1.sp
  refine wp_dp (op2_imm (by decide)) fun t2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun t3 u3 => WP.block_nil ⟨⟨⟨hs.1, ?_⟩, by omega_arith, by omega_arith, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, h.hN, h.hc⟩
  · exact (s1.of_rest (u2.rest (ws := [.r0]) (by simp)) u2.mem).of_rest (u3.rest (ws := [.r5]) (by simp)) u3.mem
  · rw [u3.other _ (by decide), u2.gpr, dpVal, u1.gpr, h.r0, Offset.add_ofNat_add_one, hl]; rfl
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r1]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r3]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r4]
  · rw [u3.gpr, dpVal, u2.other _ (by decide), u1.gpr, h.r5, ofNat_succ, hl]
  · rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r8]
  · intro j hj
    rw [u3.mem, u2.mem, u1.mem, WriteBytes.writeW8_apply, h.r6, setWidth_byte, hk]
    rw [hk] at hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by simp only [oBuf]; omega_arith) (by simp only [oBuf]; omega_arith)
        (show oBuf + j ≠ oBuf + (kept P σ i).length by omega_arith)), getD_append_left _ _ _ hj]
      exact h.buf j hj
    · rw [ite_eq_left rfl, getD_append_right _ _ _ (Nat.le_refl _), Nat.sub_self]; rfl

theorem cmp53_wp {i : Nat} (h : B1 P i σ s) :
    WP isa (.block [.cmp .r5 (.reg .r3)]) s fun t =>
      B1 P i σ t ∧ t.z = decide (cnt P σ (i + 1) = P.pl) := by
  obtain ⟨a, hN, hc⟩ := h
  have hpl := a.st.1.pl_le
  have hc' := a.hc
  refine wp_cmp (op2_reg _ _) fun t u z => WP.block_nil ⟨⟨?_, hN, hc⟩, ?_⟩
  · exact ⟨⟨a.st.1, a.st.2.of_rest (u.rest []) u.mem⟩, a.hi, a.hc, by rw [u.gpr]; exact a.r0,
      by rw [u.gpr]; exact a.r1, by rw [u.gpr]; exact a.r3, by rw [u.gpr]; exact a.r4, by rw [u.gpr]; exact a.r5,
      by rw [u.gpr]; exact a.r8, fun j hj => by rw [u.mem]; exact a.buf j hj⟩
  · rw [z, a.r5, a.r3, ofNat_sub_beq (by omega_arith) (by omega_arith)]

/-- `B1` with whether to stop in Z. -/
def B3 (P : EP) (i : Nat) (σ s : State) : Prop :=
  B1 P i σ s ∧ s.z = decide (cnt P σ (i + 1) = P.pl ∨ i + 1 = P.rl)

theorem B1.flags {i : Nat} {t : State} (h : B1 P i σ s) (u : Fupd s t) : B1 P i σ t := by
  obtain ⟨a, hN, hc⟩ := h
  exact ⟨⟨⟨a.st.1, a.st.2.of_rest (u.rest []) u.mem⟩, a.hi, a.hc, by rw [u.gpr]; exact a.r0,
      by rw [u.gpr]; exact a.r1, by rw [u.gpr]; exact a.r3, by rw [u.gpr]; exact a.r4, by rw [u.gpr]; exact a.r5,
      by rw [u.gpr]; exact a.r8, fun j hj => by rw [u.mem]; exact a.buf j hj⟩, hN, hc⟩

theorem full_wp {i : Nat} (h : B1 P i σ s) (hf : cnt P σ (i + 1) = P.pl) :
    WP isa (.block [.cmp .r5 (.reg .r5)]) s (B3 P i σ) :=
  wp_cmp (op2_reg _ _) fun t u z => WP.block_nil ⟨h.flags u, by rw [z, BitVec.sub_self]; simp [hf]⟩

theorem ended_wp {i : Nat} (h : B1 P i σ s) (hf : cnt P σ (i + 1) ≠ P.pl) :
    WP isa (.block [.cmp .r4 (.reg .r8)]) s (B3 P i σ) := by
  have hrl := h.1.st.1.rl_le
  have hpl := h.1.st.1.pl_le
  have hi := h.1.hi
  refine wp_cmp (op2_reg _ _) fun t u z => WP.block_nil ⟨h.flags u, ?_⟩
  rw [z, h.1.r4, h.1.r8, ofNat_sub_beq (by omega_arith) (by omega_arith)]
  simp [hf]

end

/-! ## Constant time -/

section

variable {P : EP}

theorem start_vp : VP (S P) (.block start) (G1 P) :=
  VP.stk (code := [_, _, _, _, _, _, _, _, _]) (by decide) (by decide)
    (fun _ _ _ _ h₁ h₂ => by rw [h₁.2.sp, h₂.2.sp]) fun _ _ h => start_wp h

theorem load_vp (i : Nat) : VP (A P i) (.block load) (fun σ s => Ld P σ i s) :=
  VP.taint [.r1, .r4] load_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.r1, h₂.1.r1]
    · rw [h₁.1.r4, h₂.1.r4]) fun _ _ h => load_wp h

end

end VG.Proof.RsaPkcs1Enc.Arm.Rnd

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

/-! ## The scan's loop, in constant time

Each octet's branch, the stores of the kept ones and the end of the loop
are the same in two runs with the same trace (`scan_vp`); then whether `PS`
is full (`full_vp`).
-/

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.RsaPkcs1Enc (nz scanLen)
open VG.Proof.X25519.Arm (Fupd wp_cmp op2_imm op2_reg eval_ne eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)

variable {P : EP}

theorem At.flags {σ s t : State} {i : Nat} (a : At P σ i s) (u : Fupd s t) : At P σ i t :=
  ⟨⟨a.st.1, a.st.2.of_rest (u.rest []) u.mem⟩, a.hi, a.hc, by rw [u.gpr]; exact a.r0,
    by rw [u.gpr]; exact a.r1, by rw [u.gpr]; exact a.r3, by rw [u.gpr]; exact a.r4, by rw [u.gpr]; exact a.r5,
    by rw [u.gpr]; exact a.r8, fun j hj => by rw [u.mem]; exact a.buf j hj⟩

theorem keep_vp (i : Nat) :
    VP (fun σ s => Ld P σ i s ∧ isa.eval .ne s = some true) (.block keep) (B1 P i) :=
  VP.taint [.r0, .r5] keep_taint (fun _ _ _ _ h₁ h₂ r hr => by
    have e := cnt_eq h₁.1.st.1 h₂.1.st.1 (Nat.le_of_lt h₁.1.hN)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.r0, h₂.1.r0, e]
    · rw [h₁.1.r5, h₂.1.r5, e]) fun _ _ h => keep_wp h.1 (by
      have := h.2; rw [eval_ne, h.1.z] at this; simpa using this)

theorem branch_vp (i : Nat) : VP (fun σ s => Ld P σ i s) (.ite .ne (.block keep) (.block [])) (B1 P i) :=
  VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [eval_ne, eval_ne, h₁.z, h₂.z, decide_eq_decide.mpr (zero_eq h₁.st.1 h₂.st.1 h₁.hN)])
    (keep_vp i) (VP.block_nil fun _ _ h => skip_at h.1 (by
      have := h.2; rw [eval_ne, h.1.z] at this; simpa using this))

theorem more_vp (i : Nat) : VP (B1 P i) more (B3 P i) := by
  refine VP.seq (G := fun σ s => B1 P i σ s ∧ s.z = decide (cnt P σ (i + 1) = P.pl))
    (VP.taint [.r5, .r3] cmp53_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.r5, h₂.1.r5, cnt_eq h₁.1.st.1 h₂.1.st.1 h₁.2.1]
      · rw [h₁.1.r3, h₂.1.r3]) fun _ _ h => cmp53_wp h) ?_
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by
      rw [eval_eq, eval_eq, h₁.2, h₂.2, cnt_eq h₁.1.1.st.1 h₂.1.1.st.1 h₁.1.2.1]) ?_ ?_
  · exact VP.taint [.r5] cmp55_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.1.1.1.r5, h₂.1.1.1.r5, cnt_eq h₁.1.1.1.st.1 h₂.1.1.1.st.1 h₁.1.1.2.1]) fun _ _ h => full_wp h.1.1 (by
        have := h.2; rw [eval_eq, h.1.2] at this; simpa using this)
  · exact VP.taint [.r4, .r8] cmp48_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.1.1.r4, h₂.1.1.1.r4]
      · rw [h₁.1.1.1.r8, h₂.1.1.1.r8]) fun _ _ h => ended_wp h.1.1 (by
        have := h.2; rw [eval_eq, h.1.2] at this; simpa using this)

theorem step_vp (i : Nat) : VP (A P i) step (B3 P i) :=
  (load_vp i).seq ((branch_vp i).seq (more_vp i))

/-- The loop's invariant, with `k` iterations left. -/
def I (P : EP) (k : Nat) (σ s : State) : Prop :=
  k ≤ N P ∧ At P σ (N P - k) s ∧ (0 < k → cnt P σ (N P - k) < P.pl)

theorem body_vp (n : Nat) : VP (I P (n + 1)) step fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → Done P σ s) ∧ (0 < n → I P n σ s) := by
  refine VP.of_imp (p := n + 1 ≤ N P) (fun _ _ h => h.1) fun hn1 => ?_
  refine (step_vp (P := P) (N P - (n + 1))).mono
    (fun σ s h => ⟨h.2.1, by omega, h.2.2 (by omega)⟩) fun σ s h => ?_
  obtain ⟨⟨a, hN, hc⟩, hz⟩ := h
  have hin := a.st.1
  have hstop := VG.Proof.RsaPkcs1Enc.stop_iff (n := P.pl) (r := randB P σ) (j := N P - (n + 1))
    (by rw [hin.scan]; exact hN) hc
  rw [randB_length, hin.scan] at hstop
  have hst : (cnt P σ (N P - (n + 1) + 1) = P.pl ∨ N P - (n + 1) + 1 = P.rl) ↔ n = 0 :=
    hstop.trans (⟨fun h => by omega, fun h => by omega⟩ : N P = N P - (n + 1) + 1 ↔ n = 0)
  have hle := a.hc
  refine ⟨?_, fun h0 => ?_, fun hp => ?_⟩
  · rw [eval_ne, hz]
    congr 1
    by_cases h0 : n = 0
    · rw [decide_eq_true (hst.mpr h0)]
      simp [h0]
    · simp only [mt hst.mp h0, decide_false, Bool.not_false]
      exact (decide_eq_true (Nat.pos_of_ne_zero h0)).symm
  · have e : N P - (n + 1) + 1 = N P := by omega_arith
    rw [e] at a
    exact a
  · have hn := mt hst.mp (by omega_arith)
    have e : N P - (n + 1) + 1 = N P - n := by omega_arith
    refine ⟨by omega, by rw [← e]; exact a, fun _ => ?_⟩
    rw [← e]
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Or.inl h) hn

theorem cmp8_wp {σ s : State} (h : G1 P σ s) :
    WP isa (.block [.cmp .r8 (.imm 0)]) s fun t => At P σ 0 t ∧ t.z = decide (P.rl = 0) := by
  have a := at0 h
  have hrl := h.1.1.rl_le
  have hpl := h.1.1.pl_le
  refine wp_cmp (op2_imm (by decide)) fun t u z => WP.block_nil ⟨a.flags u, ?_⟩
  rw [z, a.r8, show BitVec.ofNat 32 P.rl - 0 = BitVec.ofNat 32 P.rl from BitVec.sub_zero _,
    Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]

theorem scan_vp : VP (G1 P) scan (Done P) := by
  refine VP.seq (G := fun σ s => At P σ 0 s ∧ s.z = decide (P.rl = 0))
    (VP.taint [.r8] cmp8_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]) fun _ _ h => cmp8_wp h) ?_
  refine VP.ite (fun _ _ _ _ h₁ h₂ => by rw [eval_ne, eval_ne, h₁.2, h₂.2]) ?_ ?_
  · refine (VP.loop (I := I P) (fun n => body_vp n) (N P - 1)).mono (fun σ s h => ?_) fun _ _ h => h
    obtain ⟨⟨a, hz⟩, he⟩ := h
    have hin := a.st.1
    have hrl : P.rl ≠ 0 := by rw [eval_ne, hz] at he; simpa using he
    have hN : 1 ≤ N P := by
      rw [← hin.scan]
      exact VG.Proof.RsaPkcs1Enc.Arm.Rnd.scanLen_pos (by have := hin.pl8; omega_arith) (fun e => hrl (by
        rw [← randB_length P σ, e]; rfl))
    rw [Nat.sub_add_cancel hN]
    refine ⟨Nat.le_refl _, by rw [Nat.sub_self]; exact a, fun _ => ?_⟩
    rw [Nat.sub_self]
    have := hin.pl8
    show 0 < P.pl
    omega_arith
  · refine VP.block_nil fun σ s h => ?_
    obtain ⟨⟨a, hz⟩, he⟩ := h
    have hrl : P.rl = 0 := by rw [eval_ne, hz] at he; simpa using he
    have hN : N P = 0 := by have := a.st.1.N_le; omega_arith
    show At P σ (N P) s
    rw [hN]; exact a

theorem full_wp' {σ s : State} (h : Done P σ s) :
    WP isa (.block [.cmp .r5 (.reg .r3)]) s fun t => Done P σ t ∧ t.z = decide (cnt P σ (N P) = P.pl) := by
  have hpl := h.st.1.pl_le
  have hc := h.hc
  refine wp_cmp (op2_reg _ _) fun t u z => WP.block_nil ⟨At.flags h u, ?_⟩
  rw [z, h.r5, h.r3, ofNat_sub_beq (by omega_arith) (by omega_arith)]

theorem full_vp : VP (Done P) (.block [.cmp .r5 (.reg .r3)])
    (fun σ s => Done P σ s ∧ s.z = decide (cnt P σ (N P) = P.pl)) :=
  VP.taint [.r5, .r3] cmp53_taint (fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [At.r5 h₁, At.r5 h₂, cnt_eq (At.st h₁).1 (At.st h₂).1 (Nat.le_refl _)]
    · rw [At.r3 h₁, At.r3 h₂]) fun _ _ h => full_wp' h

end VG.Proof.RsaPkcs1Enc.Arm.Rnd

namespace VG.Proof.RsaPkcs1Enc.Arm.Rnd

/-! ## The tape and the call's arguments

With `PS` full: `tape` is `[N, 0]` (`tapeStore_wp`, each word in two
halves), then the call's arguments (`callArgs_wp`), `PS` the frame's, and the
call of `vg_rsa_pkcs1_encrypt_precomputed` by its contract (`call_vp`).
-/

open VG VG.Arm VG.Impl.RsaPkcs1Enc.Arm.Random VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_str wp_cmp op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## The tape's words -/

theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

theorem zero_append_ofNat {u : Nat} (hu : u < 2 ^ 32) :
    (0 : BitVec 32) ++ BitVec.ofNat 32 u = BitVec.ofNat 64 u := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu,
    Nat.mod_eq_of_lt (by omega)]
  simp

/-- The four words of `tape`, as halves of its two. -/
def Tape4 (m : Mem) (a : Addr) (w0 w2 : BitVec 32) : Prop :=
  m.readW (a + BitVec.ofNat 64 0) 32 = w0 ∧ m.readW (a + BitVec.ofNat 64 4) 32 = 0 ∧
    m.readW (a + BitVec.ofNat 64 8) 32 = w2 ∧ m.readW (a + BitVec.ofNat 64 12) 32 = 0

theorem wordsAt_tape {m : Mem} {a : Addr} {u r : Nat} (hu : u < 2 ^ 32) (hr : r < 2 ^ 32)
    (h : Tape4 m a (BitVec.ofNat 32 u) (BitVec.ofNat 32 r)) :
    Spec.Rsa.wordsAt m a 2 = [BitVec.ofNat 64 u, BitVec.ofNat 64 r] := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  show [m.readW (a + BitVec.ofNat 64 (8 * 0)) 64, m.readW (a + BitVec.ofNat 64 (8 * 1)) 64] = _
  rw [readW64_split, readW64_split, Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat]
  simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add, show 8 + 4 = 12 from rfl]
  rw [h0, h1, h2, h3, zero_append_ofNat hu, zero_append_ofNat hr]

theorem tape4 (m : Mem) (a : Addr) (w0 w1 w2 w3 : BitVec 32) :
    let m' := (((m.writeW (a + BitVec.ofNat 64 0) w0).writeW (a + BitVec.ofNat 64 4) w1).writeW
      (a + BitVec.ofNat 64 8) w2).writeW (a + BitVec.ofNat 64 12) w3
    m'.readW (a + BitVec.ofNat 64 0) 32 = w0 ∧ m'.readW (a + BitVec.ofNat 64 4) 32 = w1 ∧
      m'.readW (a + BitVec.ofNat 64 8) 32 = w2 ∧ m'.readW (a + BitVec.ofNat 64 12) 32 = w3 := by
  have w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 16 → e + 4 ≤ 16 →
      (m.writeW (a + BitVec.ofNat 64 e) v).readW (a + BitVec.ofNat 64 d) 32 = m.readW (a + BitVec.ofNat 64 d) 32 :=
    fun m d e v h hd he => Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [w _ 0 12 _ (by decide) (by decide) (by decide), w _ 0 8 _ (by decide) (by decide) (by decide),
      w _ 0 4 _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [w _ 4 12 _ (by decide) (by decide) (by decide), w _ 4 8 _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [w _ 8 12 _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · exact Mem.readW_writeW_self32 _ _ _

variable {P : EP}

/-- `tape`'s words. -/
abbrev TapeW (P : EP) (m : Mem) (w0 w2 : BitVec 32) : Prop := Tape4 m (State.addr P.tape) w0 w2

theorem TapeW.frame {m m' : Mem} {w0 w2 : BitVec 32} {rs : List Region} (h : TapeW P m w0 w2)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, P.TAPE.Disjoint r) : TapeW P m' w0 w2 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨(hf.readW (r := P.TAPE) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)).trans h0,
    (hf.readW (r := P.TAPE) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)).trans h1,
    (hf.readW (r := P.TAPE) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)).trans h2,
    (hf.readW (r := P.TAPE) (Offset.contains_base _ (by decide) (by decide)) hd (by decide)).trans h3⟩

theorem BufL.frame {s t : State} {l : List Byte} {rs : List Region} (h : BufL P s l) (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.lay.fr oBuf, l.length⟩ r) : BufL P t l := fun j hj => by
  rw [hf.byte1 (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega)))]
  exact h j hj

/-! ## Where the buffers are -/

section

variable {σ : State}

theorem In.tapeFr (h : In P σ) {d n : Nat} (hd : d + n ≤ frameBytes + 56) :
    P.TAPE.Disjoint ⟨P.lay.fr d, n⟩ :=
  (h.ok.stk_fr (R := P.TAPE) (.inr (by simp)) hd).symm

theorem In.tapeLow (h : In P σ) : P.TAPE.Disjoint P.lay.LOW := (h.ok.low_buf (R := P.TAPE) (.inr (by simp))).symm

theorem In.dOT (h : In P σ) : P.OUT.Disjoint P.TAPE := by
  have w := h.ok.wrw
  rw [List.pairwise_cons] at w
  exact w.1 _ (by simp)

theorem In.dOS (h : In P σ) : P.OUT.Disjoint P.SCR := by
  have w := h.ok.wrw
  rw [List.pairwise_cons] at w
  exact w.1 _ (by simp)

theorem In.dTS (h : In P σ) : P.TAPE.Disjoint P.SCR := by
  have w := h.ok.wrw
  rw [List.pairwise_cons, List.pairwise_cons] at w
  exact w.2.1 _ (by simp)

theorem In.fitT (h : In P σ) : P.tape.toNat + 16 ≤ 2 ^ 32 := by
  have := h.ok.fits P.TAPE (by simp)
  simpa [Proof.X25519.Arm.addr_toNat] using this

end

/-! ## The stages -/

/-- With `PS` full at the end of the scan. -/
def Acc (P : EP) (σ s : State) : Prop := Done P σ s ∧ cnt P σ (N P) = P.pl

/-- After `tapeLoad`. -/
def C0 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ cnt P σ (N P) = P.pl ∧ s.gpr .r3 = BitVec.ofNat 32 P.pl ∧ s.gpr .r4 = BitVec.ofNat 32 (N P) ∧
    s.gpr .r7 = P.tape ∧ BufL P s (kept P σ (N P))

/-- What the rest of the accepting path keeps. -/
def K1 (P : EP) (σ s : State) : Prop :=
  S P σ s ∧ cnt P σ (N P) = P.pl ∧ BufL P s (kept P σ (N P)) ∧ TapeW P s.mem (BitVec.ofNat 32 (N P)) 0

/-- After `tapeStore`. -/
def C1 (P : EP) (σ s : State) : Prop := K1 P σ s ∧ s.gpr .r3 = BitVec.ofNat 32 P.pl

/-- The call's stack arguments. -/
abbrev outv (P : EP) : List (BitVec 32) :=
  [P.e, BitVec.ofNat 32 P.el, P.msg, BitVec.ofNat 32 P.ml, P.B + BitVec.ofNat 32 oBuf, BitVec.ofNat 32 P.pl,
    P.scr, BitVec.ofNat 32 P.sl, P.pre, BitVec.ofNat 32 P.ql]

def OutA (P : EP) (s : State) : Prop := ∀ i < 10, s.mem.readW (P.lay.fr (4 * i)) 32 = (outv P).getD i 0

/-- Before the call. -/
def C2 (P : EP) (σ s : State) : Prop :=
  K1 P σ s ∧ OutA P s ∧ s.gpr .r0 = P.out ∧ s.gpr .r1 = BitVec.ofNat 32 P.K ∧ s.gpr .r2 = P.n ∧
    s.gpr .r3 = BitVec.ofNat 32 P.K

/-- The message, as the state `σ` holds it. -/
abbrev msgB (P : EP) (σ : State) : List Byte := Spec.Rsa.bytesAt σ.mem (State.addr P.msg) P.ml

/-- What the call writes and returns. -/
def CR (P : EP) (σ : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Rsa.publicPrecompute P.nB = some P.pw →
    Spec.Rsa.written m (State.addr P.out) P.K r (Spec.RsaPkcs1Enc.encrypt P.nB P.eB (msgB P σ) (kept P σ (N P)))

/-- After the call. -/
def C3 (P : EP) (σ s : State) : Prop := K1 P σ s ∧ CR P σ s.mem (s.gpr .r0)

section

variable {σ s : State}

theorem tapeLoad_wp (h : Acc P σ s) : WP isa (.block tapeLoad) s (C0 P σ) := by
  obtain ⟨a, hf⟩ := h
  exact a.st.2.wp_arg (j := 2) (by simp) (by dsimp only; decide) fun t st u => WP.block_nil
    ⟨⟨a.st.1, st⟩, hf, by rw [u.other _ (by decide)]; exact a.r3, by rw [u.other _ (by decide)]; exact a.r4, u.gpr,
      fun j hj => by rw [u.mem]; exact a.buf j hj⟩

theorem wp_strT (hs : S P σ s) (h7 : s.gpr .r7 = P.tape) {d : Nat} (hd : d + 4 ≤ 16) {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → Mupd s t (s.mem.writeW (State.addr P.tape + BitVec.ofNat 64 d) (s.gpr r)) →
      WP isa (.block is) t Q) :
    WP isa (.block (.str r .r7 d :: is)) s Q := by
  have hf := hs.1.fitT
  refine wp_str (by omega) (a := State.addr P.tape + BitVec.ofNat 64 d) (by rw [h7]; exact addr_add (by omega))
    ⟨P.TAPE, by rw [hs.2.wr, hs.2.ok.wr]; simp, Offset.contains_base _ hd (by omega)⟩ fun t u => k t ⟨hs.1, ?_⟩ u
  refine hs.2.write (rs := [⟨State.addr P.tape + BitVec.ofNat 64 d, 4⟩]) ?_ (fun r hr => ?_) u.rd u.wr u.sp
  · rw [u.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨P.TAPE, by simp, Offset.sub_base _ hd⟩

theorem tapeStore_wp (h : C0 P σ s) : WP isa (.block tapeStore) s (C1 P σ) := by
  obtain ⟨hs, hf, r3, r4, r7, buf⟩ := h
  have hN := hs.1.N_le
  have hrl := hs.1.rl_le
  have hpl := hs.1.pl_le
  refine wp_mov (op2_imm (by decide)) fun t1 u1 => ?_
  have s1 : S P σ t1 := ⟨hs.1, hs.2.of_rest (u1.rest (ws := [.r6]) (by simp)) u1.mem⟩
  have g1 : ∀ r, r ≠ .r6 → t1.gpr r = s.gpr r := u1.other
  refine wp_strT s1 (by rw [g1 _ (by decide), r7]) (d := 0) (by decide) fun t2 s2 m2 => ?_
  refine wp_strT s2 (by rw [m2.gpr, g1 _ (by decide), r7]) (d := 4) (by decide) fun t3 s3 m3 => ?_
  refine wp_strT s3 (by rw [m3.gpr, m2.gpr, g1 _ (by decide), r7]) (d := 8) (by decide) fun t4 s4 m4 => ?_
  refine wp_strT s4 (by rw [m4.gpr, m3.gpr, m2.gpr, g1 _ (by decide), r7]) (d := 12) (by decide)
    fun t5 s5 m5 => WP.block_nil ⟨⟨s5, hf, ?_, ?_⟩, ?_⟩
  · have fr : Frame [P.TAPE] s.mem t5.mem := by
      rw [m5.mem, m4.mem, m3.mem, m2.mem, u1.mem]
      exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))
    exact buf.frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hs.1.tapeFr (by show oBuf + cnt P σ (N P) ≤ frameBytes + 56; simp only [oBuf, frameBytes]; omega)).symm
  · have e := tape4 s.mem (State.addr P.tape) (s.gpr .r4) 0 0 0
    have v6 : t1.gpr .r6 = 0 := u1.gpr
    rw [m5.mem, m4.mem, m3.mem, m2.mem, u1.mem, m4.gpr, m3.gpr, m2.gpr, v6, g1 _ (by decide)]
    obtain ⟨e0, e1, e2, e3⟩ := e
    exact ⟨e0.trans r4, e1, e2.trans rfl, e3⟩
  · rw [m5.gpr, m4.gpr, m3.gpr, m2.gpr, g1 _ (by decide), r3]

/-- A word of the frame below `PS` written. -/
theorem K1.frameFr (h : K1 P σ s) {t : State} (ht : P.lay.St σ t) {d : Nat} (hd : d + 4 ≤ oBuf) (v : BitVec 32)
    (hm : t.mem = s.mem.writeW (P.lay.fr d) v) : K1 P σ t := by
  obtain ⟨hs, hf, buf, tw⟩ := h
  have hpl := hs.1.pl_le
  refine ⟨⟨hs.1, ht⟩, hf, fun j hj => ?_, tw.frame (rs := [⟨P.lay.fr d, 4⟩]) (by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hs.1.tapeFr (by simp only [oBuf, frameBytes] at hd ⊢; omega)⟩
  have hj' : j < P.pl := by rw [← hf]; exact hj
  rw [hm, Lay.byte_fr_other _ _ _ (by simp only [oBuf] at hd ⊢; omega) (by simp only [oBuf]; omega)
    (by simp only [oBuf] at hd; omega)]
  exact buf j hj

theorem callArgs_wp (h : C1 P σ s) : WP isa (.block callArgs) s (C2 P σ) := by
  obtain ⟨k1, r3⟩ := h
  have hs := k1.1
  show WP isa (.block (.addSp .r12 0 :: _)) s _
  refine Bignum.Arm.wp_stackAddr (by decide) fun t0 u0 => ?_
  have h0 : K1 P σ t0 := ⟨⟨hs.1, hs.2.of_rest (u0.rest (ws := [.r12]) (by simp)) u0.mem⟩, k1.2.1,
    fun j hj => by rw [u0.mem]; exact k1.2.2.1 j hj, by rw [u0.mem]; exact k1.2.2.2⟩
  have r12 : t0.gpr .r12 = P.B := by rw [u0.gpr, hs.2.sp, BitVec.add_zero]
  refine h0.1.2.wp_copyArg (j := 5) (d := 0) r12 (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t1 s1 v1 g1 m1 => ?_
  have h1 := h0.frameFr s1 (by decide) _ m1
  refine s1.wp_copyArg (j := 6) (d := 4) (by rw [g1 _ (by decide), r12]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t2 s2 v2 g2 m2 => ?_
  have h2 := h1.frameFr s2 (by decide) _ m2
  refine s2.wp_copyArg (j := 7) (d := 8) (by rw [g2 _ (by decide), g1 _ (by decide), r12]) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t3 s3 v3 g3 m3 => ?_
  have h3 := h2.frameFr s3 (by decide) _ m3
  refine s3.wp_copyArg (j := 8) (d := 12) (by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t4 s4 v4 g4 m4 => ?_
  have h4 := h3.frameFr s4 (by decide) _ m4
  have r12' : t4.gpr .r12 = P.B := by
    rw [g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide), r12]
  refine wp_dp (op2_imm (by decide)) fun t5 u5 => ?_
  have s5 : P.lay.St σ t5 := s4.of_rest (u5.rest (ws := [.r0]) (by simp)) u5.mem
  have h5 : K1 P σ t5 := ⟨⟨hs.1, s5⟩, h4.2.1, fun j hj => by rw [u5.mem]; exact h4.2.2.1 j hj,
    by rw [u5.mem]; exact h4.2.2.2⟩
  have r12'' : t5.gpr .r12 = P.B := by rw [u5.other _ (by decide), r12']
  refine s5.wp_strFr (d := 16) (by dsimp only; decide) (by decide) r12'' fun t6 s6 m6 => ?_
  have h6 := h5.frameFr s6 (by decide) _ m6.mem
  refine s6.wp_strFr (d := 20) (by dsimp only; decide) (by decide) (by rw [m6.gpr, r12'']) fun t7 s7 m7 => ?_
  have h7 := h6.frameFr s7 (by decide) _ m7.mem
  have r12₇ : t7.gpr .r12 = P.B := by rw [m7.gpr, m6.gpr, r12'']
  refine s7.wp_copyArg (j := 11) (d := 24) r12₇ (by simp) (by dsimp only; decide) (by dsimp only; decide)
    (by decide) (by decide) fun t8 s8 v8 g8 m8 => ?_
  have h8 := h7.frameFr s8 (by decide) _ m8
  refine s8.wp_copyArg (j := 12) (d := 28) (by rw [g8 _ (by decide), r12₇]) (by simp) (by dsimp only; decide)
    (by dsimp only; decide) (by decide) (by decide) fun t9 s9 v9 g9 m9 => ?_
  have h9 := h8.frameFr s9 (by decide) _ m9
  refine s9.wp_copyArg (j := 13) (d := 32) (by rw [g9 _ (by decide), g8 _ (by decide), r12₇]) (by simp)
    (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t10 s10 v10 g10 m10 => ?_
  have h10 := h9.frameFr s10 (by decide) _ m10
  refine s10.wp_copyArg (j := 14) (d := 36) (by rw [g10 _ (by decide), g9 _ (by decide), g8 _ (by decide), r12₇])
    (by simp) (by dsimp only; decide) (by dsimp only; decide) (by decide) (by decide) fun t11 s11 v11 g11 m11 => ?_
  have h11 := h10.frameFr s11 (by decide) _ m11
  refine s11.wp_arg (j := 0) (by simp) (by dsimp only; decide) fun t12 s12 u12 => ?_
  refine s12.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t13 s13 u13 => ?_
  refine s13.wp_arg (j := 3) (by simp) (by dsimp only; decide) fun t14 s14 u14 => ?_
  refine s14.wp_arg (j := 4) (by simp) (by dsimp only; decide) fun t15 s15 u15 => WP.block_nil ?_
  have mm : t15.mem = t11.mem := by rw [u15.mem, u14.mem, u13.mem, u12.mem]
  refine ⟨⟨⟨hs.1, s15⟩, h11.2.1, fun j hj => by rw [mm]; exact h11.2.2.1 j hj, by rw [mm]; exact h11.2.2.2⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mm, m11]
    have w : ∀ (m : Mem) (d e : Nat) (v : BitVec 32), d + 4 ≤ e ∨ e + 4 ≤ d → d + 4 ≤ 40 → e + 4 ≤ 40 →
        (m.writeW (P.lay.fr e) v).readW (P.lay.fr d) 32 = m.readW (P.lay.fr d) 32 :=
      fun m d e v h hd he => Lay.readW_fr_other _ _ _ h (by omega) (by omega)
    have wr : ∀ (m : Mem) (d : Nat) (v : BitVec 32), (m.writeW (P.lay.fr d) v).readW (P.lay.fr d) 32 = v :=
      fun m d v => Mem.readW_writeW_self32 _ _ _
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        w _ _ _ _ (by decide) (by decide) (by decide), m6.mem, w _ _ _ _ (by decide) (by decide) (by decide), u5.mem,
        m4, w _ _ _ _ (by decide) (by decide) (by decide), m3, w _ _ _ _ (by decide) (by decide) (by decide), m2,
        w _ _ _ _ (by decide) (by decide) (by decide), m1, wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        w _ _ _ _ (by decide) (by decide) (by decide), m6.mem, w _ _ _ _ (by decide) (by decide) (by decide), u5.mem,
        m4, w _ _ _ _ (by decide) (by decide) (by decide), m3, w _ _ _ _ (by decide) (by decide) (by decide), m2,
        wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        w _ _ _ _ (by decide) (by decide) (by decide), m6.mem, w _ _ _ _ (by decide) (by decide) (by decide), u5.mem,
        m4, w _ _ _ _ (by decide) (by decide) (by decide), m3, wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        w _ _ _ _ (by decide) (by decide) (by decide), m6.mem, w _ _ _ _ (by decide) (by decide) (by decide), u5.mem,
        m4, wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        w _ _ _ _ (by decide) (by decide) (by decide), m6.mem, wr, u5.gpr, dpVal, r12']; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, w _ _ _ _ (by decide) (by decide) (by decide), m7.mem,
        wr, m6.gpr, u5.other _ (by decide), g4 _ (by decide), g3 _ (by decide), g2 _ (by decide), g1 _ (by decide),
        u0.other _ (by decide), r3]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        w _ _ _ _ (by decide) (by decide) (by decide), m8, wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, w _ _ _ _ (by decide) (by decide) (by decide), m9,
        wr]; rfl
    · rw [w _ _ _ _ (by decide) (by decide) (by decide), m10, wr]; rfl
    · rw [wr]; rfl
  · rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.gpr]; rfl
  · rw [u15.other _ (by decide), u14.other _ (by decide), u13.gpr]; rfl
  · rw [u15.other _ (by decide), u14.gpr]; rfl
  · rw [u15.gpr]; rfl

end

end VG.Proof.RsaPkcs1Enc.Arm.Rnd
