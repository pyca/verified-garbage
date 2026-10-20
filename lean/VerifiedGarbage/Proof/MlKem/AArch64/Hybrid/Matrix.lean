module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# The paired matrix, hashing a message

`matrixH_ok`: the matrix (`Hybrid.matrixH`) of a function with the layout
`L` satisfies the paired matrix's invariant (`Kem.BInv`, here from the
memory each step starts in, with the writes since the matrix began framed by
`bW3`), and leaves in `scratch`'s first 200 bytes the state the hash of the
message `M` is squeezed from (`HInv.hash`): `ek` for encapsulation's
`H(ek)`, `z ‖ c` (copied to `scratch`) for decapsulation's `J(z ‖ c)`.
`MsgOk` is where the message lies. Its x3 calls use the 128 bytes below the
stack pointer (`Stk128`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

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

abbrev HInv := HInvW false

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
    have := hp.scw; have := hp.scb; omega)).symm⟩

theorem BInvW.paired3 {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀) {mA : Mem}
    {ρ E : List Byte} {S : Impl.MlKem.AArch64.Hybrid.HSrc} {ea : Addr} {e i : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : Pair3OutcomeW w16 S (matSeed ρ (e/P.k) (e%P.k)) (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))
      (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) ea (kA s₀ L.sc) E i s t) :
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
      rw [show e+2=(e+1)+1 by omega,okR_succ,okR_succ]
    rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro j hj
    rcases (by omega : j<e ∨ j=e ∨ j=e+1) with hj|rfl|rfl
    · exact reducedW_frame fr (old hj) (h.red j hj)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro j hj
    rcases (by omega : j<e ∨ j=e ∨ j=e+1) with hj|rfl|rfl
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
  · exact (hM.dA e (by omega)).symm
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
    WP isa (Impl.MlKem.AArch64.Hybrid.pair3 P M.S (2*i) i w16) s fun t =>
      HInvW w16 P L M s₀ mA ρ E (2*i+2) (i+1) t ∧ MT3 P L s₀ t := by
  have hw := hp.wf
  rw [pair3_iff]
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*i)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH+1024*(2*i+1)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hk1 : 0 < P.k := hf.1
  have hk2 : P.k ≤ 256 := by omega_using [hf.2.1]
  have pin := pair_input (L := L) hp he h.b.kb tb.t
  have hin := hash_input hp hk hM he h.b.kb tb
  refine WP.mono_syms (pair3Code_ok P M.S (a := 2*i) (i := i) hM.src hoa hob pin hin hb h.hash h.ek
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
  · rw [ht.hash, show 3 * (i + 1) = 3 * i + 3 by omega]
  · refine tb.frame post.keep.rd post.keep.wr sy fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (pair_scratch hp he r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by rw [stR_sc]; exact scratch_sub hp (by lom))
      · exact .inr rfl

theorem bW_st {s₀ : State} (hp : Pre P L s₀) :
    ∀ r ∈ bW P L s₀, (stR (kA s₀ L.sc)).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rw [stR_sc]
  rcases mem4 hr with rfl | rfl | rfl | rfl
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact below_R hp hp.scb (hp.fs (by lom))

theorem bW_sub {s₀ : State} : ∀ r ∈ bW P L s₀, r ∈ bW3 P L s₀ :=
  fun _ hr => List.mem_append_left _ hr

/-- **A pair that does not hash.** -/
theorem paired_stepH {w16 : Bool} {M : Msg} {s₀ s : State} (hp : Pre P L s₀) (hM : MsgOk P L M s₀) {mA : Mem}
    {ρ E : List Byte} {e j : Nat}
    (he : e+1<P.k*P.k) (h : HInvW w16 P L M s₀ mA ρ E e j s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair P false e w16) s fun t =>
      HInvW w16 P L M s₀ mA ρ E (e+2) j t ∧ MT3 P L s₀ t := by
  refine WP.mono_syms (paired_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  refine ⟨⟨binv_rebase hb, h.fr.trans (hb.fr.mono bW_sub), ?_, ?_⟩, mt, by rw [sy]; exact tb.stk⟩
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hb.fr (bW_st hp), h.hash]
  · rw [VG.Proof.MlKem.bytesAt_frame hb.fr hM.dW (by have := hM.src.lim; omega), h.ek]

/-- **The singleton.** -/
theorem singleton_stepH {w16 : Bool} {M : Msg} {s₀ s : State} (hp : Pre P L s₀) (hM : MsgOk P L M s₀)
    {mA : Mem} {ρ E : List Byte} {e j : Nat}
    (he : e<P.k*P.k) (h : HInvW w16 P L M s₀ mA ρ E e j s) (tb : MT3 P L s₀ s) :
    WP isa (Paired.lastCode SB SS e P.k (AH+1024*e) w16) s fun t =>
      HInvW w16 P L M s₀ mA ρ E (e+1) j t ∧ MT3 P L s₀ t := by
  refine WP.mono_syms (singleton_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  refine ⟨⟨binv_rebase hb, h.fr.trans (hb.fr.mono bW_sub), ?_, ?_⟩, mt, by rw [sy]; exact tb.stk⟩
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hb.fr (bW_st hp), h.hash]
  · rw [VG.Proof.MlKem.bytesAt_frame hb.fr hM.dW (by have := hM.src.lim; omega), h.ek]

/-- The arithmetic of the hashing pairs. -/
structure HashOk (P : KemLay) (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Prop where
  part : S.len % 136 ≠ 0
  three : (S.len / 136 + 1) % 3 = 0
  pairs : Impl.MlKem.AArch64.Hybrid.hashPairs S ≤ P.k * P.k / 2

theorem hashOk768 : HashOk lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768) :=
  ⟨by decide, by decide, by decide⟩
theorem hashOk1024 : HashOk Impl.MlKem1024.AArch64.lay1024 (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024) :=
  ⟨by decide, by decide, by decide⟩

/-- **The matrix.** -/
theorem matrixH_ok {w16 : Bool} {M : Msg} {s₀ s : State} (hp : Pre P L s₀) (hk : Stk128 P L s₀)
    (hM : MsgOk P L M s₀) (ho : HashOk P M.S) {mA : Mem} {ρ E : List Byte}
    (h : HInvW w16 P L M s₀ mA ρ E 0 0 s) (tb : MT3 P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.matrixH P M.S w16) s fun t =>
      HInvW w16 P L M s₀ mA ρ E (P.k*P.k) (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) t ∧ MT3 P L s₀ t := by
  have hk' : 0<P.k := hp.wf.facts.1
  have hn : 0<P.k*P.k := Nat.mul_pos hk' hk'
  have hP := ho.pairs
  apply WPs.seqs
  · intro hh
    have parts := List.append_eq_nil_iff.mp hh
    by_cases hodd : P.k*P.k%2=1
    · simpa only [ite_eq_left hodd,List.cons_ne_nil] using parts.2
    · have np : 0<P.k*P.k/2 := by omega
      exact map_range_ne_nil np _ parts.1
  · apply WPs.append
    refine WPs.mono (WPs.range (I := fun i t => HInvW w16 P L M s₀ mA ρ E (2*i)
      (min i (Impl.MlKem.AArch64.Hybrid.hashPairs M.S)) t ∧ MT3 P L s₀ t)
      (fun i hi t ht => ?_) ⟨by simpa using h, tb⟩) fun t ht => ?_
    · by_cases hh : i < Impl.MlKem.AArch64.Hybrid.hashPairs M.S
      · rw [ite_eq_left hh]
        have hb : 136 * (3 * i + 2) < M.S.len := by
          have := ho.part; have := ho.three
          simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hh
          omega
        rw [show min i (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) = i by omega] at ht
        refine WP.mono (paired_step3 hp hk hM (by omega) hb ht.1 ht.2) fun u hu => ?_
        rw [show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) = i+1 by omega,
          show 2*(i+1) = 2*i+2 by omega]
        exact hu
      · rw [ite_eq_right hh]
        rw [show min i (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) = Impl.MlKem.AArch64.Hybrid.hashPairs M.S by omega] at ht
        refine WP.mono (paired_stepH hp hM (by omega : 2*i+1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        rw [show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) = Impl.MlKem.AArch64.Hybrid.hashPairs M.S by omega,
          show 2*(i+1) = 2*i+2 by omega]
        exact hu
    · rw [show min (P.k*P.k/2) (Impl.MlKem.AArch64.Hybrid.hashPairs M.S) = Impl.MlKem.AArch64.Hybrid.hashPairs M.S by omega] at ht
      by_cases hodd : P.k*P.k%2=1
      · rw [ite_eq_left hodd]
        apply WPs.single
        rw [Paired.lastSample_eq]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx] at ht
        refine WP.mono (singleton_stepH hp hM (by omega : P.k*P.k-1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        simpa only [Nat.sub_add_cancel hn] using hu
      · rw [ite_eq_right hodd]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        simpa only [WPs,idx] using ht

end VG.Proof.MlKem.AArch64.Hybrid
