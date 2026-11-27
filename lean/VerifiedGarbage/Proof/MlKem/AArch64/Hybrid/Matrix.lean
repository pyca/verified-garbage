module

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Begin
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result

/-! ### `MlKem.AArch64.Hybrid.Pair`, which this module and modules that import it used -/

section

/-!
# A hashing pair, complete

`pairMCode_ok`: `beginM_ok`, then `Paired.finishCode` from
`Paired.finish_ok`, run from the state `beginM` left with the registers
of the pair's start (which is all `finish_ok` asks of its `initial` state
but its memory). `PairMPostW.outcome`: its outcome in terms of the
specification (as `Paired.PairPostW.outcome`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid
variable {sha3 : Bool}

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Proof.MlKem.AArch64.Paired (Context stepWrites accepted seedState seedBytes pairRegs
  pairWorkingRegs finishCode finish_ok PairPostW)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

theorem pairM_iff (sb ss off : Nat) (L : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (a j m : Nat) (w16 : Bool)
    (s : State) (Q : State → Prop) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pairM sha3 sb ss off L S a j m w16) s Q ↔
    WP isa (.seq (beginMCode sha3 L S sb ss a (a+1) j m (off+1024*a) (off+1024*(a+1)) w16) (finishCode sha3 w16)) s Q := by
  simp only [Impl.MlKem.AArch64.Hybrid.pairM, beginMCode, Paired.initialCode, finishCode, seqs]
  simp only [WP.seq_iff (M := isa)]

structure PairMPostW (w16 : Bool) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (A B : Spec.Sha3.State) (p a b e st : Addr) (E : List Byte) (j m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWrites3 p a b st s.sp) s.mem t.mem
  left : CoeffsUpToW w16 t.mem a (accepted A 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted A 5)) (fun _=>0)
  reducedLeft : ReducedW (cw w16) t.mem a
  right : CoeffsUpToW w16 t.mem b (accepted B 5).length (VG.Proof.MlKem.AArch64.Sample.cvW w16 (accepted B 5)) (fun _=>0)
  reducedRight : ReducedW (cw w16) t.mem b
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (accepted A 5).length=256 ∧ (accepted B 5).length=256 then 1 else 0)
  hash : stateAt t.mem st = hstate E (j + min 3 m) (dB S)
  ek : bytesAt t.mem e S.len = E

theorem pairMCode_ok {w16 : Bool} (L : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State}
    {p seed outA outB table e st : Addr} {E : List Byte} {sb ss a j m oa ob : Nat} (hS : SrcOk S)
    (hss : ss < 65536) (hsb : sb + 32 ≤ 32768) (h8b : sb % 8 = 0) (hoa : oa < 65536) (hob : ob < 65536)
    (h : Paired.BeginInput sb ss oa ob p seed outA outB table s)
    (hh : HashInput S p outA outB table e st s)
    (hb : ∀ k < m, k < 3 → 136 * (j + k) < S.len)
    (hash : stateAt s.mem st = hstate E j (dB S)) (hE : bytesAt s.mem e S.len = E)
    (h24 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) :
    WP isa (.seq (beginMCode sha3 L S sb ss a (a+1) j m oa ob w16) (finishCode sha3 w16)) s
      (PairMPostW w16 S (seedState s.mem seed a L.k) (seedState s.mem seed (a+1) L.k) p outA outB e st E j m s) := by
  refine WP.seq (WP.mono_syms (beginM_ok (sha3 := sha3) L S hS hss hsb h8b hoa hob h hh hb hash hE)
    fun u hu sy => ?_)
  let initial : State := { s with mem := u.mem }
  have hk : Keep pairWorkingRegs initial u :=
    let k := hu.keep.mono (rs' := pairWorkingRegs) (by decide)
    ⟨k.gpr, k.rd, k.wr, k.sp, k.vcs⟩
  refine WP.mono (finish_ok (sha3 := sha3) (initial := initial) hk (Frame.refl _ _) hu.saved hu.progress
    (by rw [sy]; exact h.symbol) hu.flag (hu.keep.get .x24) h24) fun t ht => ?_
  have fut : Frame (stepWrites p outA outB) u.mem t.mem := ht.frame
  have hSt : ∀ r ∈ stepWrites p outA outB, (stR st).Disjoint r := by
    intro r hr; simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hh.lay.dSP
    · exact hh.aS.symm
    · exact hh.bS.symm
  have hE' : ∀ r ∈ stepWrites p outA outB, (Region.mk e S.len).Disjoint r := by
    intro r hr; simp only [stepWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hh.lay.dEP
    · exact hh.aE.symm
    · exact hh.bE.symm
  refine ⟨⟨ht.keep.gpr, ht.keep.rd, ht.keep.wr, ht.keep.sp, ht.keep.vcs⟩, hu.frame.trans (fut.mono fun r hr => List.mem_append_left _ hr), ht.left,
    ht.reducedLeft, ht.right, ht.reducedRight, ht.status, ?_, ?_⟩
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame fut hSt, hu.hash]
  · rw [VG.Proof.MlKem.bytesAt_frame fut hE' (by have := hS.lim; omega_using [this]), hu.ek]

structure PairMOutcomeW (w16 : Bool) (S : Impl.MlKem.AArch64.Hybrid.HSrc) (A B : List Byte) (p a b e st : Addr) (E : List Byte) (j m : Nat)
    (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (pairWrites3 p a b st s.sp) s.mem t.mem
  reducedLeft : ReducedW (cw w16) t.mem a
  reducedRight : ReducedW (cw w16) t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAtW (cw w16) t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)
  hash : stateAt t.mem st = hstate E (j + min 3 m) (dB S)
  ek : bytesAt t.mem e S.len = E

theorem PairMPostW.outcome {w16 : Bool} {S : Impl.MlKem.AArch64.Hybrid.HSrc} {s t : State} {p seed a b e st : Addr} {E : List Byte} {i i' k n m : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairMPostW w16 S (seedState s.mem seed i k) (seedState s.mem seed i' k) p a b e st E n m s t) :
    PairMOutcomeW w16 S (seedBytes s.mem seed i k) (seedBytes s.mem seed i' k) p a b e st E n m s t := by
  have ra := Paired.accepted_result hk hk256 h.left
  have rb := Paired.accepted_result hk hk256 h.right
  refine ⟨h.keep,h.frame,h.reducedLeft,h.reducedRight,?_,?_,?_,h.hash,h.ek⟩
  · rcases ra with ⟨_,ha⟩|⟨_,ha⟩
    · exact Or.inr ha
    · exact Or.inl ha
  · rcases rb with ⟨_,hb⟩|⟨_,hb⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rw [h.status]
    rcases ra with ⟨la,ha⟩|⟨la,ha⟩ <;> rcases rb with ⟨lb,hb⟩|⟨lb,hb⟩ <;>
      simp [ha,hb,la,lb]

end VG.Proof.MlKem.AArch64.Hybrid

end

end

/-!
# The paired matrix, hashing a message

`paired_step3`: a pair of the matrix of a function with the layout `L` that
absorbs the next three blocks of a message into the third state
(`Hybrid.pair3`) keeps the paired matrix's invariant (`Kem.BInvW`, here from
the memory each step starts in, with the writes since the matrix began framed
by `bW3`), and the state the hash of the message `M` is squeezed from in
`scratch`'s first 200 bytes (`HInv.hash`): `ek` for encapsulation's `H(ek)`,
`z ‖ c` (copied to `scratch`) for decapsulation's `J(z ‖ c)`, as the first
pairs of `Kem16P.matrixP` do.
`MsgOk` is where the message lies. Its x3 calls use the 128 bytes below the
stack pointer (`Stk128`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid
variable {sha3 : Bool}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay} {L : Layout}

/-- The 128 bytes below the stack pointer, apart from the arguments. -/
structure Stk128 (P : KemLay) (L : Layout) (s₀ : State) : Prop where
  sp : 128 ≤ s₀.sp.toNat
  args : ∀ b < L.nb, (frame s₀.sp).Disjoint ⟨kA s₀ b, L.len b⟩

theorem Stk128.R {s₀ : State} (hk : Stk128 P L s₀) {b o l : Nat} (hb : b < L.nb) (f : o + l ≤ L.len b) :
    (frame s₀.sp).Disjoint (R (kA s₀) b o l) :=
  (hk.args b hb).sub_right (R.sub f)

/-- The message: `S.len` bytes of argument `b` from offset `o`, absorbed by the code `S`. -/
structure Msg where
  S : Impl.MlKem.AArch64.Hybrid.HSrc
  b : Nat
  o : Nat

/-- Where the message is. -/
abbrev Msg.reg (M : Msg) (s₀ : State) : Region := R (kA s₀) M.b M.o M.S.len

/-- What hashing the message during the matrix needs of it: the code finds it
from its register, it can be read, and the matrix, the third state and the
frame do not write it. -/
structure MsgOk (P : KemLay) (L : Layout) (M : Msg) (s₀ : State) : Prop where
  src : SrcOk M.S
  reg : ∀ s, KB P L s₀ s → s.gpr M.S.r + BitVec.ofNat 64 M.S.base = (M.reg s₀).base
  rd : ∀ s, KB P L s₀ s → Covers [M.reg s₀] (s.rd ++ s.wr)
  dST : (R (kA s₀) L.sc 0 200).Disjoint (M.reg s₀)
  dW : ∀ r ∈ bW P L s₀, (M.reg s₀).Disjoint r
  dSS : (M.reg s₀).Disjoint (R (kA s₀) L.sc SS 2048)
  dA : ∀ e < P.k * P.k, (M.reg s₀).Disjoint (R (kA s₀) L.sc (AH + 1024 * e) 1024)
  frm : (frame s₀.sp).Disjoint (M.reg s₀)

/-- What the hashing matrix writes. -/
abbrev bW3 (P : KemLay) (L : Layout) (s₀ : State) : List Region :=
  bW P L s₀ ++ [R (kA s₀) L.sc 0 200, frame s₀.sp]

/-- After `n` entries of `Â` and `j` hashing pairs, from memory `mA`. -/
structure HInvW (w16 : Bool) (P : KemLay) (L : Layout) (M : Msg) (s₀ : State) (mA : Mem) (ρ E : List Byte)
    (n j : Nat) (s : State) : Prop where
  b : BInvW w16 P L s₀ s.mem ρ n s
  fr : Frame (bW3 P L s₀) mA s.mem
  hash : stateAt s.mem (kA s₀ L.sc) = hstate E (3 * j) (dB M.S)
  ek : bytesAt s.mem (M.reg s₀).base M.S.len = E

/-- The rejection table, apart from the frame too. -/
structure MT3 (P : KemLay) (L : Layout) (s₀ s : State) : Prop where
  t : MatrixTable P L s₀ s
  stk : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (frame s₀.sp)

theorem stR_sc (s₀ : State) : stR (kA s₀ L.sc) = R (kA s₀) L.sc 0 200 := by
  simp only [stR, R, ptr_zero]

theorem binv_rebase {w16 : Bool} {s₀ s : State} {mA : Mem} {ρ : List Byte} {n : Nat} (h : BInvW w16 P L s₀ mA ρ n s) :
    BInvW w16 P L s₀ s.mem ρ n s :=
  ⟨h.kb, Frame.refl _ _, h.rho, h.acc, h.red, h.res⟩

theorem far3 {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o)) (h200 : 200 ≤ o) :
    ∀r∈pairWrites3 (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) (kA s₀ L.sc) s₀.sp,
      (R (kA s₀) L.sc o l).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pair_far hp he hf hs r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [stR_sc]; exact sdisj hp hf (by lom) (Or.inr h200)
    · exact (hk.R (b := L.sc) hp.scb (hp.fs hf)).symm

theorem safe_frame {s₀ : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) :
    Safe P L s₀ (frame s₀.sp) :=
  ⟨(hk.R (b := L.sc) hp.scb hp.sv).symm, fun c hc => (hk.args c (by
    have := hp.scw; have := hp.scb; omega_arith)).symm⟩

theorem BInvW.paired3 {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA : Mem}
    {ρ E : List Byte} {S : Impl.MlKem.AArch64.Hybrid.HSrc} {ea : Addr} {e : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    {j m : Nat}
    (ht : PairMOutcomeW w16 S (matSeed ρ (e/P.k) (e%P.k)) (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))
      (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) ea (kA s₀ L.sc) E j m s t) :
    BInvW w16 P L s₀ t.mem ρ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWrites3 (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1))
      (kA s₀ L.sc) s₀.sp) s.mem t.mem := by
    have f := ht.frame; rw [h.kb.sp] at f; exact f
  have old {j : Nat} (hj : j<e) := far3 hp hk he (o:=AH+1024*j) (l:=1024)
    (by lom) (by constructor <;> lom) (by lom)
  refine ⟨h.kb.frame ht.keep fr (by decide) ?_, Frame.refl _ _, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · simp only [Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> exact safe_scr hp (by lom)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [stR_sc]; exact safe_scr hp (by lom)
      · exact safe_frame hp hk
  · rw [bytesAt_frame fr (far3 hp hk he (o := SB) (l := 32) (by lom) (by constructor <;> lom) (by lom))
      (by decide)]
    exact h.rho
  · have hall : okR P ρ (e+2) ↔ (okR P ρ e ∧ (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega_using [],okR_succ,okR_succ]
    rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro j hj
    rcases (by omega_using [hj] : j<e ∨ j=e ∨ j=e+1) with hj|rfl|rfl
    · exact reducedW_frame fr (old hj) (h.red j hj)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro j hj
    rcases (by omega_using [hj] : j<e ∨ j=e ∨ j=e+1) with hj|rfl|rfl
    · rw [polyAtW_frame fr (old hj)]; exact h.res j hj
    · exact ht.left
    · exact ht.right

/-- What a hashing pair needs of the message, the third state and the frame. -/
theorem hash_input {M : Msg} {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) (hM : MsgOk P L M s₀)
    {e : Nat} (he : e+1<P.k*P.k) (h : KB P L s₀ s) (tb : MT3 P L s₀ s) :
    HashInput M.S (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) (s.syms "VG_MLKEM_REJ_SHUFFLE")
      (M.reg s₀).base (kA s₀ L.sc) s := by
  have hw := hp.wf
  refine ⟨⟨cov_s hp h (o := SS) (l := 2048) (by lom), ?_, hM.rd s h, by rw [h.sp]; exact hk.sp,
    ?_, ?_, hM.dSS, ?_, ?_, ?_⟩, hM.reg s h, h.x28, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stR_sc]; exact cov_s hp h (by lom)
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · rw [stR_sc]; exact hM.dST
  · rw [h.sp]; exact hk.R hp.scb (hp.fs (o := SS) (l := 2048) (by lom))
  · rw [h.sp, stR_sc]; exact hk.R hp.scb (hp.fs (by lom))
  · rw [h.sp]; exact hM.frm
  · exact tb.t.apart.sub_right (Region.sub_prefix (by have := hp.sv; rw [hp.scl] at this; lom))
  · rw [h.sp]; exact tb.stk
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · exact (hM.dA e (by omega_using [he])).symm
  · exact (hM.dA (e+1) he).symm

theorem MT3.frame {s₀ s t : State} (h : MT3 P L s₀ s) {rs : List Region}
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.syms=s.syms) (hf : Frame rs s.mem t.mem)
    (sub : ∀r∈rs,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩ ∨ r = frame s₀.sp) : MT3 P L s₀ t := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · rw [hs]
    exact h.t.artifact.frame hf (fun r hh => by
      rcases sub r hh with hh | rfl
      · exact h.t.apart.sub_right hh
      · exact h.stk)
  · rw [hs,hr,hw]; exact h.t.readable
  · rw [hs]; exact h.t.apart
  · rw [hs]; exact h.stk

theorem x24_bit {w16 : Bool} {s₀ s : State} {mA : Mem} {ρ : List Byte} {n : Nat} (h : BInvW w16 P L s₀ mA ρ n s) :
    s.gpr .x24 = 0 ∨ s.gpr .x24 = 1 := by
  rw [h.acc]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **A hashing pair** of the matrix. -/
theorem paired_step3 {w16 : Bool} {M : Msg} {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀)
    (hM : MsgOk P L M s₀) {mA : Mem} {ρ E : List Byte}
    {i : Nat} (he : 2*i+1<P.k*P.k) (hb : 136 * (3 * i + 2) < M.S.len)
    (h : HInvW w16 P L M s₀ mA ρ E (2*i) i s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pair3 sha3 P M.S (2*i) i w16) s fun t =>
      HInvW w16 P L M s₀ mA ρ E (2*i+2) (i+1) t ∧ MT3 P L s₀ t := by
  have hw := hp.wf
  rw [Impl.MlKem.AArch64.Hybrid.pair3, pairM_iff]
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*i)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH+1024*(2*i+1)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hk1 : 0 < P.k := hf.1
  have hk2 : P.k ≤ 256 := by omega_using [hf.2.1]
  have pin := pair_input (L := L) hp he h.b.kb tb.t
  have hin := hash_input hp hk hM he h.b.kb tb
  refine WP.mono_syms (pairMCode_ok (sha3 := sha3) P M.S (a := 2*i) (j := 3*i) (m := 3) hM.src (by decide) (by decide)
    (by decide) hoa hob pin hin (fun k hk _ => by omega_using [hb, hk]) h.hash h.ek
    (x24_bit h.b)) fun t ht sy => ?_
  have post := ht.outcome (p := sA L s₀ SS) hk1 hk2
  have seed {j : Nat} : Paired.seedBytes s.mem (sA L s₀ SB) j P.k=matSeed ρ (j/P.k) (j%P.k) := by
    simp only [Paired.seedBytes,h.b.rho,matSeed]
  rw [seed,seed] at post
  have fr : Frame (pairWrites3 (sA L s₀ SS) (aP L s₀ (2*i)) (aP L s₀ (2*i+1))
      (kA s₀ L.sc) s₀.sp) s.mem t.mem := by
    have f := post.frame; rw [h.b.kb.sp] at f; exact f
  have sub3 : ∀ r ∈ pairWrites3 (sA L s₀ SS) (aP L s₀ (2*i)) (aP L s₀ (2*i+1))
      (kA s₀ L.sc) s₀.sp, ∃ r' ∈ bW3 P L s₀, Region.Sub r r' := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', hs⟩ := pair_sub (L := L) (s₀ := s₀) he r hr
      exact ⟨r', List.mem_append_left _ hr', hs⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨R (kA s₀) L.sc 0 200, by simp, by rw [stR_sc]; exact fun _ h => h⟩
      · exact ⟨frame s₀.sp, by simp, fun _ h => h⟩
  refine ⟨⟨BInvW.paired3 hp hk he h.b post, h.fr.trans (fr.sub sub3), ?_, ht.ek⟩, ?_⟩
  · rw [ht.hash, show 3 * (i + 1) = 3 * i + min 3 3 by omega_using []]
  · refine tb.frame post.keep.rd post.keep.wr sy fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (pair_scratch hp he r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by rw [stR_sc]; exact scratch_sub hp (by lom))
      · exact .inr rfl

theorem bW_sub {s₀ : State} : ∀ r ∈ bW P L s₀, r ∈ bW3 P L s₀ :=
  fun _ hr => List.mem_append_left _ hr

/-- The arithmetic of the hashing pairs. -/
structure HashOk (P : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Prop where
  part : S.len % 136 ≠ 0
  three : (S.len / 136 + 1) % 3 = 0
  pairs : Impl.MlKem.AArch64.Hybrid.hashPairs S ≤ P.k * P.k / 2

theorem hashOk768 : HashOk lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768) :=
  ⟨by decide, by decide, by decide⟩
theorem hashOk1024 : HashOk Impl.MlKem1024.AArch64.lay1024 (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024) :=
  ⟨by decide, by decide, by decide⟩

end VG.Proof.MlKem.AArch64.Hybrid
