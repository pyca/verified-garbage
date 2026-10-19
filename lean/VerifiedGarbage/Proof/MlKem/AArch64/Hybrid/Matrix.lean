module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Pair
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-!
# The encapsulation matrix, hashing `ek`

`matrixH_ok`: the matrix (`Hybrid.matrixH`) satisfies the paired matrix's
invariant (`Kem.BInv`, here from the memory each step starts in, with the
writes since the matrix began framed by `bW3`), and leaves in `scratch`'s
first 200 bytes the state SHA3-256 squeezes `H(ek)` from (`HInv.hash`).
Its x3 calls use the 128 bytes below the stack pointer (`Stk128`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Spec.MlKem
open VG.Proof.MlKem

variable {P : KemLay}

/-- The 128 bytes below the stack pointer, apart from the arguments. -/
structure Stk128 (P : KemLay) (s₀ : State) : Prop where
  sp : 128 ≤ s₀.sp.toNat
  args : ∀ b < 5, (frame s₀.sp).Disjoint ⟨kA s₀ b, (enL P).len b⟩

theorem Stk128.R {s₀ : State} (hk : Stk128 P s₀) {b o l : Nat} (hb : b < 5) (f : o + l ≤ (enL P).len b) :
    (frame s₀.sp).Disjoint (R (kA s₀) b o l) :=
  (hk.args b hb).sub_right (R.sub f)

/-- What the hashing matrix writes. -/
abbrev bW3 (P : KemLay) (s₀ : State) : List Region :=
  bW P (enL P) s₀ ++ [R (kA s₀) (enL P).sc 0 200, frame s₀.sp]

/-- After `n` entries of `Â` and `j` hashing pairs, from memory `mA`. -/
structure HInvW (w16 : Bool) (P : KemLay) (s₀ : State) (mA : Mem) (ρ E : List Byte) (n j : Nat) (s : State) : Prop where
  b : BInvW w16 P (enL P) s₀ s.mem ρ n s
  fr : Frame (bW3 P s₀) mA s.mem
  hash : stateAt s.mem (kA s₀ (enL P).sc) = hstate E (3 * j)

abbrev HInv := HInvW false

/-- The rejection table, apart from the frame too. -/
structure MT3 (P : KemLay) (s₀ s : State) : Prop where
  t : MatrixTable P (enL P) s₀ s
  stk : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint (frame s₀.sp)

theorem stR_sc (s₀ : State) : stR (kA s₀ (enL P).sc) = R (kA s₀) (enL P).sc 0 200 := by
  simp only [stR, R, ptr_zero]

theorem binv_rebase {w16 : Bool} {s₀ s : State} {mA : Mem} {ρ : List Byte} {n : Nat} (h : BInvW w16 P (enL P) s₀ mA ρ n s) :
    BInvW w16 P (enL P) s₀ s.mem ρ n s :=
  ⟨h.kb, Frame.refl _ _, h.rho, h.acc, h.red, h.res⟩

theorem far3 {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) {e : Nat} (he : e+1<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o)) (h200 : 200 ≤ o) :
    ∀r∈pairWrites3 (sA (enL P) s₀ SS) (aP (enL P) s₀ e) (aP (enL P) s₀ (e+1)) (kA s₀ (enL P).sc) s₀.sp,
      (R (kA s₀) (enL P).sc o l).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pair_far hp he hf hs r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [stR_sc]; exact sdisj hp hf (by lom) (Or.inr h200)
    · exact (hk.R (b := (enL P).sc) hp.scb (hp.fs hf)).symm

theorem safe_frame {s₀ : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) :
    Safe P (enL P) s₀ (frame s₀.sp) :=
  ⟨(hk.R (b := (enL P).sc) hp.scb hp.sv).symm, fun c hc => (hk.args c (by
    have : c < 2 := hc; omega)).symm⟩

theorem BInvW.paired3 {w16 : Bool} {s₀ s t : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) {mA : Mem}
    {ρ E : List Byte} {e i : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P (enL P) s₀ mA ρ e s)
    (ht : Pair3OutcomeW w16 P (matSeed ρ (e/P.k) (e%P.k)) (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))
      (sA (enL P) s₀ SS) (aP (enL P) s₀ e) (aP (enL P) s₀ (e+1)) (kA s₀ 0) (kA s₀ (enL P).sc) E i s t) :
    BInvW w16 P (enL P) s₀ t.mem ρ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWrites3 (sA (enL P) s₀ SS) (aP (enL P) s₀ e) (aP (enL P) s₀ (e+1))
      (kA s₀ (enL P).sc) s₀.sp) s.mem t.mem := by
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

/-- What a hashing pair needs of `ek`, the third state and the frame. -/
theorem hash_input {s₀ s : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P (enL P) s₀ s) (tb : MT3 P s₀ s) :
    HashInput P (sA (enL P) s₀ SS) (aP (enL P) s₀ e) (aP (enL P) s₀ (e+1)) (s.syms "VG_MLKEM_REJ_SHUFFLE")
      (kA s₀ 0) (kA s₀ (enL P).sc) s := by
  have hw := hp.wf
  have ek0 : ∀ (o l o' l' : Nat), o + l ≤ P.ekLen → o' + l' ≤ SV P + 48 →
      (R (kA s₀) 0 o l).Disjoint (R (kA s₀) (enL P).sc o' l') := fun o l o' l' f f' =>
    hp.args.rdisj (show 0 < 5 by decide) hp.scb (by simpa [enL] using f) (hp.fs f') (.inr (.inr hp.scw))
      (.inl (by simp [enL, Layout.sc]))
  have ekR : (Region.mk (kA s₀ 0) P.ekLen) = R (kA s₀) 0 0 P.ekLen := by simp only [R, ptr_zero]
  have hle : 0 + P.ekLen ≤ P.ekLen := by omega
  refine ⟨⟨cov_s hp h (o := SS) (l := 2048) (by lom), ?_, ?_, by rw [h.sp]; exact hk.sp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.x28, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stR_sc]; exact cov_s hp h (by lom)
  · rw [ekR]; exact cov_r hp h (show 0 < 5 by decide) (by simp [enL])
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · rw [stR_sc, ekR]; exact (ek0 0 P.ekLen 0 200 hle (by lom)).symm
  · rw [ekR]; exact ek0 0 P.ekLen SS 2048 hle (by lom)
  · rw [h.sp]; exact hk.R hp.scb (hp.fs (o := SS) (l := 2048) (by lom))
  · rw [h.sp, stR_sc]; exact hk.R hp.scb (hp.fs (by lom))
  · rw [h.sp, ekR]; exact hk.R (show 0 < 5 by decide) (by simp [enL])
  · exact h.x25
  · exact tb.t.apart.sub_right (Region.sub_prefix (by have := hp.sv; rw [hp.scl] at this; lom))
  · rw [h.sp]; exact tb.stk
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · rw [stR_sc]; exact sdisj hp (by lom) (by lom) (by lom)
  · rw [ekR]; exact (ek0 0 P.ekLen (AH+1024*e) 1024 hle (by lom)).symm
  · rw [ekR]; exact (ek0 0 P.ekLen (AH+1024*(e+1)) 1024 hle (by lom)).symm

theorem MT3.frame {s₀ s t : State} (h : MT3 P s₀ s) {rs : List Region}
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.syms=s.syms) (hf : Frame rs s.mem t.mem)
    (sub : ∀r∈rs,Region.Sub r ⟨kA s₀ (enL P).sc,P.scl⟩ ∨ r = frame s₀.sp) : MT3 P s₀ t := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · rw [hs]
    exact h.t.artifact.frame hf (fun r hh => by
      rcases sub r hh with hh | rfl
      · exact h.t.apart.sub_right hh
      · exact h.stk)
  · rw [hs,hr,hw]; exact h.t.readable
  · rw [hs]; exact h.t.apart
  · rw [hs]; exact h.stk

theorem ek_kb {s₀ s : State} (h : KB P (enL P) s₀ s) :
    bytesAt s.mem (kA s₀ 0) P.ekLen = Encaps.ekE P s₀ := h.ro 0 (show 0 < 2 by decide)

theorem x24_bit {w16 : Bool} {s₀ s : State} {mA : Mem} {ρ : List Byte} {n : Nat} (h : BInvW w16 P (enL P) s₀ mA ρ n s) :
    s.gpr .x24 = 0 ∨ s.gpr .x24 = 1 := by
  rw [h.acc]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **A hashing pair** of the matrix. -/
theorem paired_step3 {w16 : Bool} {s₀ s : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) {mA : Mem} {ρ : List Byte}
    {i : Nat} (he : 2*i+1<P.k*P.k) (hb : 136 * (3 * i + 2) < P.ekLen) (h8 : P.ekLen % 8 = 0)
    (hlim : P.ekLen ≤ 4096)
    (h : HInvW w16 P s₀ mA ρ (Encaps.ekE P s₀) (2*i) i s) (tb : MT3 P s₀ s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.pair3 P (2*i) i w16) s fun t =>
      HInvW w16 P s₀ mA ρ (Encaps.ekE P s₀) (2*i+2) (i+1) t ∧ MT3 P s₀ t := by
  have hw := hp.wf
  rw [pair3_iff]
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*i)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH+1024*(2*i+1)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hk1 : 0 < P.k := hf.1
  have hk2 : P.k ≤ 256 := by omega_using [hf.2.1]
  have pin := pair_input (L := enL P) hp he h.b.kb tb.t
  have hin := hash_input hp hk he h.b.kb tb
  refine WP.mono_syms (pair3Code_ok P (a := 2*i) (i := i) hoa hob pin hin hb h8 hlim h.hash (ek_kb h.b.kb) (x24_bit h.b)) fun t ht sy => ?_
  have post := ht.outcome (p := sA (enL P) s₀ SS) hk1 hk2
  have seed {j : Nat} : Paired.seedBytes s.mem (sA (enL P) s₀ SB) j P.k=matSeed ρ (j/P.k) (j%P.k) := by
    simp only [Paired.seedBytes,h.b.rho,matSeed]
  rw [seed,seed] at post
  have fr : Frame (pairWrites3 (sA (enL P) s₀ SS) (aP (enL P) s₀ (2*i)) (aP (enL P) s₀ (2*i+1))
      (kA s₀ (enL P).sc) s₀.sp) s.mem t.mem := by
    have f := post.frame; rw [h.b.kb.sp] at f; exact f
  have sub3 : ∀ r ∈ pairWrites3 (sA (enL P) s₀ SS) (aP (enL P) s₀ (2*i)) (aP (enL P) s₀ (2*i+1))
      (kA s₀ (enL P).sc) s₀.sp, ∃ r' ∈ bW3 P s₀, Region.Sub r r' := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', hr', hs⟩ := pair_sub (L := enL P) (s₀ := s₀) he r hr
      exact ⟨r', List.mem_append_left _ hr', hs⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨R (kA s₀) (enL P).sc 0 200, by simp, by rw [stR_sc]; exact fun _ h => h⟩
      · exact ⟨frame s₀.sp, by simp, fun _ h => h⟩
  refine ⟨⟨BInvW.paired3 hp hk he h.b post, h.fr.trans (fr.sub sub3), ?_⟩, ?_⟩
  · rw [ht.hash, show 3 * (i + 1) = 3 * i + 3 by omega]
  · refine tb.frame post.keep.rd post.keep.wr sy fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (pair_scratch hp he r hr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by rw [stR_sc]; exact scratch_sub hp (by lom))
      · exact .inr rfl

theorem bW_st {s₀ : State} (hp : Pre P (enL P) s₀) :
    ∀ r ∈ bW P (enL P) s₀, (stR (kA s₀ (enL P).sc)).Disjoint r := by
  have hw := hp.wf
  intro r hr
  rw [stR_sc]
  rcases mem4 hr with rfl | rfl | rfl | rfl
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact sdisj hp (by lom) (by lom) (by lom)
  · exact below_R hp hp.scb (hp.fs (by lom))

theorem bW_sub {s₀ : State} : ∀ r ∈ bW P (enL P) s₀, r ∈ bW3 P s₀ :=
  fun _ hr => List.mem_append_left _ hr

/-- **A pair that does not hash.** -/
theorem paired_stepH {w16 : Bool} {s₀ s : State} (hp : Pre P (enL P) s₀) {mA : Mem} {ρ E : List Byte} {e j : Nat}
    (he : e+1<P.k*P.k) (h : HInvW w16 P s₀ mA ρ E e j s) (tb : MT3 P s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair P false e w16) s fun t =>
      HInvW w16 P s₀ mA ρ E (e+2) j t ∧ MT3 P s₀ t := by
  refine WP.mono_syms (paired_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  refine ⟨⟨binv_rebase hb, h.fr.trans (hb.fr.mono bW_sub), ?_⟩, mt, by rw [sy]; exact tb.stk⟩
  rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hb.fr (bW_st hp), h.hash]

/-- **The singleton.** -/
theorem singleton_stepH {w16 : Bool} {s₀ s : State} (hp : Pre P (enL P) s₀) {mA : Mem} {ρ E : List Byte} {e j : Nat}
    (he : e<P.k*P.k) (h : HInvW w16 P s₀ mA ρ E e j s) (tb : MT3 P s₀ s) :
    WP isa (Paired.lastCode SB SS e P.k (AH+1024*e) w16) s fun t =>
      HInvW w16 P s₀ mA ρ E (e+1) j t ∧ MT3 P s₀ t := by
  refine WP.mono_syms (singleton_step hp he h.b tb.t) fun t ⟨hb, mt⟩ sy => ?_
  refine ⟨⟨binv_rebase hb, h.fr.trans (hb.fr.mono bW_sub), ?_⟩, mt, by rw [sy]; exact tb.stk⟩
  rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame hb.fr (bW_st hp), h.hash]

/-- The arithmetic of the hashing pairs. -/
structure HashOk (P : KemLay) : Prop where
  h8 : P.ekLen % 8 = 0
  lim : P.ekLen ≤ 4096
  part : P.ekLen % 136 ≠ 0
  three : (P.ekLen / 136 + 1) % 3 = 0
  pairs : Impl.MlKem.AArch64.Hybrid.hashPairs P ≤ P.k * P.k / 2

theorem hashOk768 : HashOk lay768 := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem hashOk1024 : HashOk Impl.MlKem1024.AArch64.lay1024 := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The matrix.** -/
theorem matrixH_ok {w16 : Bool} {s₀ s : State} (hp : Pre P (enL P) s₀) (hk : Stk128 P s₀) (ho : HashOk P)
    {mA : Mem} {ρ : List Byte}
    (h : HInvW w16 P s₀ mA ρ (Encaps.ekE P s₀) 0 0 s) (tb : MT3 P s₀ s) :
    WP isa (Impl.MlKem.AArch64.Hybrid.matrixH P w16) s fun t =>
      HInvW w16 P s₀ mA ρ (Encaps.ekE P s₀) (P.k*P.k) (Impl.MlKem.AArch64.Hybrid.hashPairs P) t ∧ MT3 P s₀ t := by
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
    refine WPs.mono (WPs.range (I := fun i t => HInvW w16 P s₀ mA ρ (Encaps.ekE P s₀) (2*i)
      (min i (Impl.MlKem.AArch64.Hybrid.hashPairs P)) t ∧ MT3 P s₀ t)
      (fun i hi t ht => ?_) ⟨by simpa using h, tb⟩) fun t ht => ?_
    · by_cases hh : i < Impl.MlKem.AArch64.Hybrid.hashPairs P
      · rw [ite_eq_left hh]
        have hb : 136 * (3 * i + 2) < P.ekLen := by
          have := ho.part; have := ho.three
          simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hh
          omega
        rw [show min i (Impl.MlKem.AArch64.Hybrid.hashPairs P) = i by omega] at ht
        refine WP.mono (paired_step3 hp hk (by omega) hb ho.h8 ho.lim ht.1 ht.2) fun u hu => ?_
        rw [show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = i+1 by omega,
          show 2*(i+1) = 2*i+2 by omega]
        exact hu
      · rw [ite_eq_right hh]
        rw [show min i (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega] at ht
        refine WP.mono (paired_stepH hp (by omega : 2*i+1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        rw [show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega,
          show 2*(i+1) = 2*i+2 by omega]
        exact hu
    · rw [show min (P.k*P.k/2) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega] at ht
      by_cases hodd : P.k*P.k%2=1
      · rw [ite_eq_left hodd]
        apply WPs.single
        rw [Paired.lastSample_eq]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx] at ht
        refine WP.mono (singleton_stepH hp (by omega : P.k*P.k-1<P.k*P.k) ht.1 ht.2) fun u hu => ?_
        simpa only [Nat.sub_add_cancel hn] using hu
      · rw [ite_eq_right hodd]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        simpa only [WPs,idx] using ht

end VG.Proof.MlKem.AArch64.Hybrid
