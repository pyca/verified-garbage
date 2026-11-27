module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FastFinish
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Begin
import VerifiedGarbage.Proof.Framework.Block

/-! ### `MlKem.AArch64.Paired.Pair`, which this module and modules that import it used -/

section

/-! # The complete paired matrix sampler -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem pair_iff {w16 : Bool} (L : KemLay) (kg : Bool) (a : Nat) (s : State) (Q : State→Prop) :
    WP isa (Impl.MlKem.AArch64.Paired.pair sha3 L kg a w16) s Q ↔
    WP isa (.seq (beginCode sha3 (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
      a (a+1) L.k ((if kg then KG.AH else KEM.AH)+1024*a)
      ((if kg then KG.AH else KEM.AH)+1024*(a+1)) w16) (finishCode sha3 w16)) s Q := by
  simp only [Impl.MlKem.AArch64.Paired.pair,beginCode,initialCode,finishCode,seqs]
  simp only [WP.seq_iff (M := isa)]

theorem pairCode_ok {w16 : Bool} {s : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hoa : oa<65536) (hob : ob<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p) (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (houtA : s.gpr .x28+BitVec.ofNat 64 oa=outA) (houtB : s.gpr .x28+BitVec.ofNat 64 ob=outB)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ctx : Context p outA outB table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE"=table)
    (hb : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (.seq (beginCode sha3 sb ss a b k oa ob w16) (finishCode sha3 w16)) s
      (PairPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB s) := by
  refine WP.seq (WP.mono_syms (begin_ok (sha3 := sha3) hss hsb h8 hoa hob hp hseed houtA houtB hin hsep ctx ht)
    fun t h sy=>?_)
  exact finish_ok (sha3 := sha3) (h.keep.mono (by decide)) h.frame h.saved h.progress (by rw [sy]; exact ht)
    h.flag (h.keep.get .x24 (by decide)) hb

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Paired.SpecPost`, which this module and modules that import it used -/

section

/-! # Paired sampler outcomes stated using the existing public specification -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure PairOutcomeW (w16 : Bool) (A B : List Byte) (p a b : Addr) (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (stepWrites p a b) s.mem t.mem
  reducedLeft : ReducedW (cw w16) t.mem a
  reducedRight : ReducedW (cw w16) t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAtW (cw w16) t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)

theorem PairPostW.outcome {w16 : Bool} {s t : State} {p seed a b : Addr} {i j k : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairPostW w16 (seedState s.mem seed i k) (seedState s.mem seed j k) p a b s t) :
    PairOutcomeW w16 (seedBytes s.mem seed i k) (seedBytes s.mem seed j k) p a b s t := by
  have ra := accepted_result hk hk256 h.left
  have rb := accepted_result hk hk256 h.right
  refine ⟨h.keep,h.frame,h.reducedLeft,h.reducedRight,?_,?_,?_⟩
  · rcases ra with ⟨_,ha⟩|⟨_,ha⟩
    · exact Or.inr ha
    · exact Or.inl ha
  · rcases rb with ⟨_,hb⟩|⟨_,hb⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rw [h.status]
    rcases ra with ⟨la,ha⟩|⟨la,ha⟩ <;> rcases rb with ⟨lb,hb⟩|⟨lb,hb⟩ <;>
      simp [ha,hb,la,lb]

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Paired.LastSpecPost`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem

structure LastOutcomeW (w16 : Bool) (B : List Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep pairRegs s t
 frame : Frame (fullWrites p out) s.mem t.mem
 reduced : ReducedW (cw w16) t.mem out
 result : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem out)
 status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleNTT 280 B).isSome then 1 else 0)

theorem LastPostW.outcome {w16 : Bool} {B : List Byte} {p out : Addr} {s t : State} (h : LastPostW w16 B p out s t) :
    LastOutcomeW w16 B p out s t := by
  refine ⟨h.keep,h.frame,h.reduced,?_,?_⟩
  · rcases h.result with ⟨_,hr⟩ | ⟨_,hr⟩; exact Or.inr hr; exact Or.inl hr
  · rw [h.status]
    rcases h.result with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr]

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Optimized.KemMatrixFrame`, which only this module used -/

section

/-! # Paired matrix writes preserve the encryption caller and prior entries -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

def pairWrites (L : Layout) (s₀ : State) (e : Nat) : List Region :=
  Paired.stepWrites (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1))

def lastWrites (L : Layout) (s₀ : State) (e : Nat) : List Region :=
  Paired.fullWrites (sA L s₀ SS) (aP L s₀ e)

theorem pair_far {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o)) :
    ∀r∈pairWrites L s₀ e,(R (kA s₀) L.sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact sdisj hp hf (by lom) hs.1
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega_using [hs])
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega_using [hs])

theorem pair_kb {s₀ s t : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (pairWrites L s₀ e) s.mem t.mem) :
    KB P L s₀ t := by
  have hw := hp.wf
  refine h.frame hk hf (by decide) ?_
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> exact safe_scr hp (by lom)

theorem pair_sub {s₀ : State} {e : Nat} (he : e+1<P.k*P.k) :
    ∀r∈pairWrites L s₀ e,∃r'∈bW P L s₀,Region.Sub r r' := by
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,by simp,fun _ h => h⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega_using []) (by omega_using [he])⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega_using []) (by omega_using [he])⟩

theorem last_far {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+1)≤o)) :
    ∀r∈lastWrites L s₀ e,(R (kA s₀) L.sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact sdisj hp hf (by lom) hs.1
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega_using [hs])

theorem last_kb {s₀ s t : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (lastWrites L s₀ e) s.mem t.mem) :
    KB P L s₀ t := by
  have hw := hp.wf
  refine h.frame hk hf (by decide) ?_
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> exact safe_scr hp (by lom)

theorem last_sub {s₀ : State} {e : Nat} (he : e<P.k*P.k) :
    ∀r∈lastWrites L s₀ e,∃r'∈bW P L s₀,Region.Sub r r' := by
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,by simp,fun _ h => h⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega_using []) (by omega_using [he])⟩

end VG.Proof.MlKem.AArch64.Kem

end

end

/-! ### `MlKem.AArch64.Optimized.KemMatrixPost`, which only this module used -/

section

/-! # Advance the encryption matrix invariant by pairs and the odd final entry -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
variable {P : KemLay} {L : Layout}

theorem BInvW.paired {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : Paired.PairOutcomeW w16 (matSeed ρ (e/P.k) (e%P.k)) (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))
      (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) s t) :
    BInvW w16 P L s₀ mA ρ (e+2) t := by
  have hw := hp.wf
  have fr : Frame (pairWrites L s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := pair_far hp he (o:=AH+1024*i) (l:=1024)
    (by lom) (by constructor <;> lom)
  refine ⟨pair_kb hp he h.kb ht.keep fr,h.fr.trans (fr.sub (pair_sub he)),?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (pair_far hp he (o := SB) (l := 32) (by lom) (by constructor <;> lom)) (by decide)]
    exact h.rho
  · have hall : okR P ρ (e+2) ↔ (okR P ρ e ∧ (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome) ∧
        (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome := by
      rw [show e+2=(e+1)+1 by omega_using [],okR_succ,okR_succ]
    rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      by_cases hc : (sampleNTT 280 (matSeed ρ ((e+1)/P.k) ((e+1)%P.k))).isSome <;>
      simp [hall,ha,hb,hc]
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reducedLeft
    · exact ht.reducedRight
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e ∨ i=e+1) with hi|rfl|rfl
    · rw [polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.left
    · exact ht.right

theorem BInvW.singleton {w16 : Bool} {s₀ s t : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s)
    (ht : Paired.LastOutcomeW w16 (matSeed ρ (e/P.k) (e%P.k)) (sA L s₀ SS) (aP L s₀ e) s t) :
    BInvW w16 P L s₀ mA ρ (e+1) t := by
  have hw := hp.wf
  have fr : Frame (lastWrites L s₀ e) s.mem t.mem := ht.frame
  have old {i : Nat} (hi : i<e) := last_far hp he (o:=AH+1024*i) (l:=1024)
    (by lom) (by constructor <;> lom)
  refine ⟨last_kb hp he h.kb ht.keep fr,h.fr.trans (fr.sub (last_sub he)),?_,?_,?_,?_⟩
  · rw [bytesAt_frame fr (last_far hp he (o := SB) (l := 32) (by lom) (by constructor <;> lom)) (by decide)]
    exact h.rho
  · rw [ht.status,h.acc]
    by_cases ha : okR P ρ e <;>
      by_cases hb : (sampleNTT 280 (matSeed ρ (e/P.k) (e%P.k))).isSome <;>
      simp [okR_succ,ha,hb]
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e) with hi|rfl
    · exact reducedW_frame fr (old hi) (h.red i hi)
    · exact ht.reduced
  · intro i hi
    rcases (by omega_using [hi] : i<e ∨ i=e) with hi|rfl
    · rw [polyAtW_frame fr (old hi)]; exact h.res i hi
    · exact ht.result

end VG.Proof.MlKem.AArch64.Kem

end

end


/-! # Instantiate paired matrix calls at encryption scratch addresses -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}

structure MatrixTable (P : KemLay) (L : Layout) (s₀ s : State) : Prop where
 artifact : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 readable : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 apart : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨kA s₀ L.sc,P.scl⟩

theorem MatrixTable.frame {s₀ s t : State} {rs : List Region} (h : MatrixTable P L s₀ s)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.syms=s.syms) (hf : Frame rs s.mem t.mem)
    (sub : ∀r∈rs,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩) : MatrixTable P L s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]; exact h.artifact.frame hf (fun r hh => h.apart.sub_right (sub r hh))
  · rw [hs,hr,hw]; exact h.readable
  · rw [hs]; exact h.apart

theorem scratch_sub {s₀ : State} (hp : Pre P L s₀) {o l : Nat} (hf : o+l≤SV P+48) :
    Region.Sub (R (kA s₀) L.sc o l) ⟨kA s₀ L.sc,P.scl⟩ := by
  have hh := hp.fs hf
  rw [hp.scl] at hh
  exact R.sub hh

theorem pair_scratch {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k) :
    ∀r∈pairWrites L s₀ e,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scratch_sub hp (by lom)

theorem last_scratch {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k) :
    ∀r∈lastWrites L s₀ e,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact scratch_sub hp (by lom)

theorem pair_context {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.Context (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨cov_s hp h (by lom),cov_s hp h (by lom),cov_s hp h (by lom),
    sdisj hp (by lom) (by lom) (by lom),sdisj hp (by lom) (by lom) (by lom),
    sdisj hp (by lom) (by lom) (by lom),tb.artifact,tb.readable,?_,?_,?_⟩ <;>
    exact tb.apart.sub_right (scratch_sub hp (by lom))

theorem singleton_context {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.SingleContext (sA L s₀ SS) (aP L s₀ e) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨cov_s hp h (by lom),cov_s hp h (by lom),sdisj hp (by lom) (by lom) (by lom),
    tb.artifact,tb.readable,?_,?_⟩ <;> exact tb.apart.sub_right (scratch_sub hp (by lom))

theorem paired_step {w16 : Bool} {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s) (tb : MatrixTable P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair sha3 P false e w16) s fun t =>
      BInvW w16 P L s₀ mA ρ (e+2) t ∧ MatrixTable P L s₀ t := by
  have hw := hp.wf
  rw [Paired.pair_iff]
  refine WP.mono_syms (Paired.pairCode_ok (sha3 := sha3) (by decide) (by decide) (by decide)
    (by change AH+1024*e<65536; lom) (by change AH+1024*(e+1)<65536; lom) (e28 h.kb SS) (e28 h.kb SB) (e28 h.kb (AH+1024*e)) (e28 h.kb (AH+1024*(e+1)))
    (fun j hj => ?_) (sdisj hp (by lom) (by lom) (by decide)) (pair_context hp he h.kb tb) rfl
    (by
      rw [h.acc]
      by_cases hh : okR P ρ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy => ?_
  · rw [ptr_add]
    exact in_R (cov_sr hp h.kb (o := SB) (l := 32) (by lom)) (k := 8*j) (by omega_using [hj]) (by omega_using [])
  · have post := ht.outcome (by lom) (by lom)
    have seed {i : Nat} : Paired.seedBytes s.mem (sA L s₀ SB) i P.k=matSeed ρ (i/P.k) (i%P.k) := by
      simp only [Paired.seedBytes,h.rho,matSeed]
    rw [seed,seed] at post
    exact ⟨h.paired hp he post,tb.frame post.keep.rd post.keep.wr sy post.frame (pair_scratch hp he)⟩

theorem singleton_step {w16 : Bool} {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s) (tb : MatrixTable P L s₀ s) :
    WP isa (Paired.lastCode sha3 SB SS e P.k (AH+1024*e) w16) s fun t =>
      BInvW w16 P L s₀ mA ρ (e+1) t ∧ MatrixTable P L s₀ t := by
  have hw := hp.wf
  refine WP.mono_syms (Paired.lastCode_ok (sha3 := sha3) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    (e28 h.kb SS) (e28 h.kb SB) (e28 h.kb (AH+1024*e)) (fun j hj => ?_)
    (sdisj hp (by lom) (by lom) (by decide)) (sdisj hp (by lom) (by lom) (by lom))
    (singleton_context hp he h.kb tb) rfl (by
      rw [h.acc]
      by_cases hh : okR P ρ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy => ?_
  · rw [ptr_add]
    exact in_R (cov_sr hp h.kb (o := SB) (l := 32) (by lom)) (k := 8*j) (by omega_using [hj]) (by omega_using [])
  · have post := ht.outcome
    have seed : Paired.seedBytes s.mem (sA L s₀ SB) e P.k=matSeed ρ (e/P.k) (e%P.k) := by
      simp only [Paired.seedBytes,h.rho,matSeed]
    rw [seed] at post
    exact ⟨h.singleton hp he post,tb.frame post.keep.rd post.keep.wr sy post.frame (last_scratch hp he)⟩

end VG.Proof.MlKem.AArch64.Kem
