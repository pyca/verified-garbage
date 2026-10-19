module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed66
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInitial
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSqueezeRate
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round

/-! ## The core loop -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_addImm wp_subImm wp_movz)
open VG.Proof.MlKem.AArch64 (eval_zero eval_nonzero)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (SqueezeKeep)
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (rounds)

/-- Writing a core register other than the input pointer keeps the core's
environment. -/
theorem CoreEnv.upd {σ s t : State} {wlen : Nat} {w1 work : Addr} {B : Spec.Sha3.State}
    {i emitted : Nat} {d : Reg} {v : BitVec 64} (h : CoreEnv σ wlen w1 work B i emitted s)
    (hu : Upd s t d v) (hd : d ∈ coreRegs) (h5 : d ≠ .x5) :
    CoreEnv σ wlen w1 work B i emitted t := by
  refine ⟨(h.keep.trans (RegKeep.upd hu)).mono fun r hr => ?_,?_,?_,?_⟩
  · rcases List.mem_append.mp hr with hr|hr
    · exact hr
    · rw [List.mem_singleton.mp hr]; exact hd
  · rw [hu.mem]; exact h.frame
  · rw [hu.other .x5 (Ne.symm h5)]; exact h.ptr
  · rw [hu.mem]; exact h.output

theorem pairs_upd {s t : State} {A B : Spec.Sha3.State} {d : Reg} {v : BitVec 64}
    (h : Pairs s A B) (hu : Upd s t d v) : Pairs t A B := by
  intro i hi; rw [hu.vec]; exact h i hi

/-- The loop's registers before the permutation `i`, with `k` permutations
already counted down in `x11`. -/
structure LoopRegs (wlen : Nat) (work : Addr) (k i : Nat) (s : State) : Prop where
  left : s.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-k)
  masks : s.gpr .x12=BitVec.ofNat 64 (5-min i 5)
  out : s.gpr .x10=work+BitVec.ofNat 64 (256+136*min i 5)

theorem LoopRegs.keep {wlen k i : Nat} {work : Addr} {s t : State} {rs : List Reg}
    (h : LoopRegs wlen work k i s) (hk : RegKeep rs s t)
    (hrs : .x10 ∉ rs ∧ .x11 ∉ rs ∧ .x12 ∉ rs) : LoopRegs wlen work k i t :=
  ⟨(hk.gpr .x11 hrs.2.1).trans h.left,(hk.gpr .x12 hrs.2.2).trans h.masks,
    (hk.gpr .x10 hrs.1).trans h.out⟩

/-- Each permutation advances both unrelated sponge states. -/
theorem coreRound_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (h : CoreState σ wlen w1 work A B i s) :
    WP isa (.block rounds) s fun t =>
      RoundState σ wlen w1 work A B i i t ∧ RegKeep [.x16] s t := by
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.Hw.rounds2_ok h.pairs)
    fun t ⟨hk,hp⟩ => ?_
  have hl : RegKeep [.x16] s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by simp [he])),hk.rd,hk.wr,hk.sp⟩
  refine ⟨⟨⟨(h.keep.trans hl).mono (by simp [coreRegs]),?_,?_,?_⟩,hp⟩,hl⟩
  · rw [hk.mem]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]; exact h.ptr
  · rw [hk.mem]; exact h.output

/-- Only the first five permutations serialize the independent mask stream. -/
theorem coreEmit_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (h : RoundState σ wlen w1 work A B i i s) (hl : LoopRegs wlen work i i s) :
    WP isa (.ite (.zero .x .x12) (.block []) (.block squeezeNext)) s fun t =>
      RoundState σ wlen w1 work A B i (i+1) t ∧ LoopRegs wlen work i (i+1) t := by
  by_cases hi : i<5
  · have h12 : s.gpr .x12=BitVec.ofNat 64 (5-i) := by
      rw [hl.masks,Nat.min_eq_left (by omega)]
    have h10 : s.gpr .x10=work+BitVec.ofNat 64 (256+136*i) := by
      rw [hl.out,Nat.min_eq_left (by omega)]
    refine WP.ite false (by
      rw [eval_zero,h12]
      exact congrArg some (beq_eq_false_iff_ne.mpr fun he => by
        have := congrArg BitVec.toNat he
        change _=(BitVec.ofNat 64 0).toNat at this
        simp only [BitVec.toNat_ofNat] at this
        omega)) (fun hb => Bool.noConfusion hb) fun _ => ?_
    unfold squeezeNext
    rw [show ∀ (L : List Instr) (a b c d : Instr), L++[a,b,c,d]=(L++[a,b])++[c,d] from
      fun _ _ _ _ _ => by simp,WP.block_append_iff]
    refine WP.mono (highRate_ok h.pairs h10 (fun j hj => ?_) ?_) fun a ⟨hk,hp,ho,hf⟩ => ?_
    · rw [h.keep.wr,Offset.add_add]
      exact hc.writable _ _ (by omega)
    · rw [h.keep.wr]
      change InRegions σ.wr ((work+BitVec.ofNat 64 (256+136*i))+BitVec.ofNat 64 128) 8
      rw [Offset.add_add]
      exact hc.writable _ _ (by omega)
    have hka : RegKeep [.x6,.x7] s a :=
      ⟨fun r hr => hk.gpr r (fun he => hr (by simp [he])) (fun he => hr (by simp [he])),
        hk.rd,hk.wr,hk.sp⟩
    refine wp_addImm (by decide) fun b hb => wp_subImm (by decide) fun t ht =>
      WP.block_nil ?_
    have h10a : a.gpr .x10=s.gpr .x10 := hka.gpr .x10 (by decide)
    have h12a : a.gpr .x12=s.gpr .x12 := hka.gpr .x12 (by decide)
    have h11a : a.gpr .x11=s.gpr .x11 := hka.gpr .x11 (by decide)
    rw [buffer_addr] at ho hf
    have hpb := pairs_upd hp hb
    have hpt := pairs_upd hpb ht
    refine ⟨⟨⟨((h.keep.trans hka).trans ((RegKeep.upd hb).trans (RegKeep.upd ht))).mono
      (by simp [coreRegs]),?_,?_,?_⟩,hpt⟩,⟨?_,?_,?_⟩⟩
    · rw [ht.mem,hb.mem]
      apply h.frame.trans
      exact hf.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨bufferRegion work,by simp,Offset.sub_base (bufferBase work)
          (d:=136*i) (n:=136) (k:=680) (by omega)⟩)
    · rw [ht.other .x5 (by decide),hb.other .x5 (by decide),hka.gpr .x5 (by decide)]
      exact h.ptr
    · rw [ht.mem,hb.mem,Nat.min_eq_left (by omega)]
      have hold := h.output
      rw [Nat.min_eq_left (by omega)] at hold
      exact streamOutput_append hi hold ho hf
    · rw [ht.other .x11 (by decide),hb.other .x11 (by decide),h11a]; exact hl.left
    · rw [ht.gpr,hb.other .x12 (by decide),h12a,h12,Nat.min_eq_left (by omega),
        Offset.ofNat_sub_ofNat (by omega)]
      congr 1
    · rw [ht.other .x10 (by decide),hb.gpr,h10a,h10,Nat.min_eq_left (by omega),
        Offset.add_add]
      congr 1
  · have h12 : s.gpr .x12=0 := by rw [hl.masks,Nat.min_eq_right (by omega)]; rfl
    refine WP.ite true (by rw [eval_zero,h12]; rfl) (fun _ => WP.block_nil ?_)
      (fun hb => Bool.noConfusion hb)
    refine ⟨⟨⟨h.keep,h.frame,h.ptr,?_⟩,h.pairs⟩,⟨hl.left,?_,?_⟩⟩
    · have ho := h.output
      rw [Nat.min_eq_right (by omega)] at ho
      rw [Nat.min_eq_right (by omega)]
      exact ho
    · rw [hl.masks,Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
    · rw [hl.out,Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]

private theorem full_bound {σ : State} {wlen i j : Nat} {w1 work : Addr}
    (hc : CoreConfig σ wlen w1 work) (hi : i<(64+wlen)/136-1) (hj : j<17) :
    72+136*i+8*j+8≤wlen := by
  rcases hc.length with he|he
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega
  · rw [he] at hi ⊢
    simp only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub] at hi
    omega

/-- The next full commitment block is read from the immutable packed input. -/
theorem coreFull_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work)
    (hi : i<(64+wlen)/136-1) (h : RoundState σ wlen w1 work A B i (i+1) s) :
    WP isa (.block full) s fun t =>
      CoreState σ wlen w1 work A B (i+1) t ∧ RegKeep [.x5,.x7] s t := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 (72+136*i) := by
    rw [h.ptr,inputPtr,fullCount,Nat.min_eq_left (by omega)]
  refine WP.mono (full_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp5,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (full_bound hc hi hj)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) s.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 =
      xorWords (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i)) σ.mem
        (w1+BitVec.ofNat 64 (72+136*i)) 17 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (full_bound hc hi hj)
    rw [hptr,he] at hp
    refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk⟩
    · rw [hm]; exact h.frame
    · rw [hp5,hptr]
      change (w1+BitVec.ofNat 64 (72+136*i))+BitVec.ofNat 64 136=inputPtr wlen w1 (i+1)
      rw [Offset.add_add,inputPtr,fullCount,Nat.min_eq_left (by omega)]
      congr 1
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter wlen σ.mem w1 i (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_left hi]
      exact hp

theorem coreTail65_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ 768 w1 work) (h : RoundState σ 768 w1 work A B 5 6 s) :
    WP isa (.block tail) s fun t =>
      CoreState σ 768 w1 work A B 6 t ∧ RegKeep [.x5,.x7] s t := by
  have hptr : s.gpr .x5=w1+BitVec.ofNat 64 752 := h.ptr
  refine WP.mono (tail_ok h.pairs (fun j hj=>?_)) fun t ⟨hk,hm,hp⟩ => ?_
  · rw [hptr,Offset.add_add]
    exact h.toCoreEnv.readable hc (by omega)
  · have he : xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) s.mem
        (w1+BitVec.ofNat 64 752) 2 =
      xorWords (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5)) σ.mem
        (w1+BitVec.ofNat 64 752) 2 := by
      apply xorWords_congr
      intro j hj
      rw [Offset.add_add]
      exact h.toCoreEnv.word hc (by omega)
    rw [hptr,he] at hp
    refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk.mono (by simp)⟩
    · rw [hm]; exact h.frame
    · rw [hk.gpr .x5 (by decide)]
      exact h.ptr
    · rw [hm]; exact h.output
    · change Pairs t (absorbAfter 768 σ.mem w1 5 (Spec.Sha3.keccakF (lowRun 768 σ.mem w1 A 5))) _
      simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
        Nat.reduceMul,ite_false,ite_true] using hp

theorem coreTail87_ok {σ s : State} {w1 work : Addr} {A B : Spec.Sha3.State}
    (h : RoundState σ 1024 w1 work A B 7 8 s) :
    WP isa (.block (paddingWord 0 31 0 ++ paddingWord 16 0x8000 3)) s fun t =>
      CoreState σ 1024 w1 work A B 8 t ∧ RegKeep [.x5,.x7] s t := by
  refine WP.mono (padding_ok (by decide) h.pairs) fun t ⟨hk,hm,hp⟩ => ?_
  refine ⟨⟨⟨(h.keep.trans hk).mono (by simp [coreRegs]),?_,?_,?_⟩,?_⟩,hk.mono (by simp)⟩
  · rw [hm]; exact h.frame
  · rw [hk.gpr .x5 (by decide)]
    exact h.ptr
  · rw [hm]; exact h.output
  · change Pairs t (absorbAfter 1024 σ.mem w1 7 (Spec.Sha3.keccakF (lowRun 1024 σ.mem w1 A 7))) _
    simpa only [absorbAfter,Nat.reduceAdd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceLT,
      ite_false,ite_true,ite_eq_right (by decide : ¬ (1024:Nat)=768)] using hp

/-- The block absorbed after the permutation `i`, the last of the
`(64+wlen)/136+1-i` left. -/
theorem coreAbsorb_ok {σ s : State} {wlen i : Nat} {w1 work : Addr}
    {A B : Spec.Sha3.State} (hc : CoreConfig σ wlen w1 work) (hiN : i≤(64+wlen)/136)
    (h : RoundState σ wlen w1 work A B i (i+1) s)
    (h11 : s.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-i)) :
    WP isa (absorbNext wlen) s fun t =>
      CoreState σ wlen w1 work A B (i+1) t ∧ RegKeep [.x5,.x7,.x13] s t := by
  have hN : (64+wlen)/136≤8 := by rcases hc.length with rfl|rfl <;> decide
  have hN1 : 1≤(64+wlen)/136 := by rcases hc.length with rfl|rfl <;> decide
  refine WP.seq (wp_subImm (by decide) fun a ha => WP.block_nil ?_)
  have hra : RoundState σ wlen w1 work A B i (i+1) a :=
    ⟨h.toCoreEnv.upd ha (by simp [coreRegs]) (by decide),pairs_upd h.pairs ha⟩
  have h13 : a.gpr .x13=BitVec.ofNat 64 ((64+wlen)/136+1-i)-BitVec.ofNat 64 1 := by
    rw [ha.gpr,h11]
  have h11a : a.gpr .x11=s.gpr .x11 := ha.other .x11 (by decide)
  have hka : RegKeep [.x13] s a := RegKeep.upd ha
  by_cases hl : i=(64+wlen)/136
  · refine WP.ite true (by
      rw [eval_zero,h13,Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
      simp [hl]) (fun _ => WP.block_nil ?_) (fun hb => Bool.noConfusion hb)
    refine ⟨⟨⟨hra.keep,hra.frame,?_,hra.output⟩,?_⟩,hka.mono (by simp)⟩
    · rw [hra.ptr,inputPtr,inputPtr,fullCount,fullCount,
        Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
    · change Pairs a (absorbAfter wlen σ.mem w1 i
        (Spec.Sha3.keccakF (lowRun wlen σ.mem w1 A i))) _
      rw [absorbAfter,ite_eq_right (by omega),ite_eq_right (by omega)]
      exact hra.pairs
  refine WP.ite false (by
    rw [eval_zero,h13,Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq,decide_eq_false_iff_not]
    omega) (fun hb => Bool.noConfusion hb) fun _ => ?_
  refine WP.seq (wp_subImm (by decide) fun b hb => WP.block_nil ?_)
  have hrb : RoundState σ wlen w1 work A B i (i+1) b :=
    ⟨hra.toCoreEnv.upd hb (by simp [coreRegs]) (by decide),pairs_upd hra.pairs hb⟩
  have h13b : b.gpr .x13=BitVec.ofNat 64 ((64+wlen)/136+1-i)-BitVec.ofNat 64 2 := by
    rw [hb.gpr,h11a,h11]
  have hkb : RegKeep [.x13] s b := (hka.trans (RegKeep.upd hb)).mono (by simp)
  by_cases hp : i=(64+wlen)/136-1
  · refine WP.ite true (by
      rw [eval_zero,h13b,Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
      simp only [Option.some.injEq,decide_eq_true_eq]
      omega) (fun _ => ?_) (fun hb => Bool.noConfusion hb)
    rcases hc.length with hw|hw
    · subst wlen
      have hi5 : i=5 := hp
      subst i
      exact WP.mono (coreTail65_ok hc hrb) fun t ⟨ht,hk⟩ =>
        ⟨ht,(hkb.trans hk).mono (by simp)⟩
    · subst wlen
      have hi7 : i=7 := hp
      subst i
      exact WP.mono (coreTail87_ok hrb) fun t ⟨ht,hk⟩ =>
        ⟨ht,(hkb.trans hk).mono (by simp)⟩
  · refine WP.ite false (by
      rw [eval_zero,h13b,Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
      simp only [Option.some.injEq,decide_eq_false_iff_not]
      omega) (fun hb => Bool.noConfusion hb) fun _ => ?_
    exact WP.mono (coreFull_ok hc (by omega) hrb) fun t ⟨ht,hk⟩ =>
      ⟨ht,(hkb.trans hk).mono (by simp)⟩

/-- The loop's invariant, `k` iterations before its exit. -/
def CoreInv (σ : State) (wlen : Nat) (w1 work : Addr) (A B : Spec.Sha3.State)
    (k : Nat) (s : State) : Prop :=
  ∃ i, i+k=(64+wlen)/136+1 ∧ 0<k ∧ CoreState σ wlen w1 work A B i s ∧ LoopRegs wlen work i i s

/-- All the permutations: seven for ML-DSA-65, nine for ML-DSA-87, with
only five cached-mask squeeze blocks. -/
theorem core_ok {σ s : State} {wlen : Nat} {w1 work : Addr} {A B : Spec.Sha3.State}
    (hc : CoreConfig σ wlen w1 work) (h : CoreState σ wlen w1 work A B 0 s) :
    WP isa (coreFor wlen) s (CoreState σ wlen w1 work A B ((64+wlen)/136+1)) := by
  have hN : (64+wlen)/136≤8 := by rcases hc.length with rfl|rfl <;> decide
  have h19 : s.gpr .x19=work := (h.keep.gpr .x19 (by decide)).trans hc.workPtr
  refine WP.seq (wp_movz fun a ha => wp_movz fun b hb => wp_addImm (by decide) fun c hc' =>
    WP.block_nil ?_)
  have hsc : CoreState σ wlen w1 work A B 0 c :=
    ⟨((h.toCoreEnv.upd ha (by simp [coreRegs]) (by decide)).upd hb (by simp [coreRegs])
      (by decide)).upd hc' (by simp [coreRegs]) (by decide),
      pairs_upd (pairs_upd (pairs_upd h.pairs ha) hb) hc'⟩
  have hlc : LoopRegs wlen work 0 0 c := by
    refine ⟨?_,?_,?_⟩
    · rw [hc'.other .x11 (by decide),hb.other .x11 (by decide),ha.gpr]
      rcases hc.length with rfl|rfl <;> rfl
    · rw [hc'.other .x12 (by decide),hb.gpr]; rfl
    · rw [hc'.gpr,hb.other .x19 (by decide),ha.other .x19 (by decide),h19]; rfl
  refine WP.loop (M:=isa) (CoreInv σ wlen w1 work A B) ?_ ((64+wlen)/136+1) c
    ⟨0,by omega,by omega,hsc,hlc⟩
  rintro k t ⟨i,hik,hk,hs,hl⟩
  refine WP.seq (WP.mono (coreRound_ok hs) fun a ⟨ha,hka⟩ => ?_)
  have hla := hl.keep hka (by simp)
  refine WP.seq (WP.mono (coreEmit_ok hc ha hla) fun b ⟨hb,hlb⟩ => ?_)
  refine WP.seq (WP.mono (coreAbsorb_ok hc (by omega) hb hlb.left) fun d ⟨hd,hkd⟩ => ?_)
  have hld := hlb.keep hkd (by simp)
  refine wp_subImm (by decide) fun e he => WP.block_nil ?_
  have hse : CoreState σ wlen w1 work A B (i+1) e :=
    ⟨hd.toCoreEnv.upd he (by simp [coreRegs]) (by decide),pairs_upd hd.pairs he⟩
  have h11 : e.gpr .x11=BitVec.ofNat 64 ((64+wlen)/136+1-(i+1)) := by
    rw [he.gpr,hld.left,Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  by_cases hlast : i=(64+wlen)/136
  · refine Or.inl ⟨?_,?_⟩
    · rw [eval_nonzero,h11,hlast,Nat.sub_self]; rfl
    · rw [← hlast]; exact hse
  · refine Or.inr ⟨?_,k-1,by omega,i+1,by omega,by omega,hse,⟨h11,?_,?_⟩⟩
    · rw [eval_nonzero,h11]
      exact congrArg some (bne_iff_ne.mpr fun he' => by
        have := congrArg BitVec.toNat he'
        change _=(BitVec.ofNat 64 0).toNat at this
        simp only [BitVec.toNat_ofNat] at this
        omega)
    · rw [he.other .x12 (by decide)]; exact hld.masks
    · rw [he.other .x10 (by decide)]; exact hld.out

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailNonceValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

theorem nonceWord_value (k : BitVec 64) :
    (nonceWord k).toNat=k.toNat%65536+2031616 := by
  have hx : ((k <<< 48) >>> 48).toNat=k.toNat%65536 := by
    rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
    change (k.toNat*281474976710656 % (65536*281474976710656))/281474976710656=_
    rw [Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by decide)]
  rw [nonceWord,BitVec.toNat_add,hx]
  change (k.toNat%65536+2031616)%18446744073709551616=_
  exact Nat.mod_eq_of_lt (by omega)

theorem nonceValue_byte (a k : BitVec 64) (hk : a.toNat=k.toNat%65536+2031616) {i : Nat} (hi : i<8) :
    a.extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ 3≤i by omega) with h|h|h|h
  · subst i
    simp only [ite_true,Nat.mul_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk, Nat.div_one, Nat.add_mod]
    simp only [show 2031616 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    simpa only [Nat.div_one] using Nat.mod_mul_right_mod k.toNat 256 256
  · subst i
    simp only [ite_eq_right (by decide : ¬ (1:Nat)=0),ite_true,Nat.mul_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow]
    rw [hk]
    change ((k.toNat % (256*256) + 7936*256)/256)%256 = _
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.add_mod]
    simp only [show 7936 % 256 = 0 from rfl, Nat.add_zero, Nat.mod_mod]
    rw [Nat.mod_mul_right_div_self, Nat.mod_mod]
  · subst i
    simp only [ite_eq_right (by decide : ¬ (2:Nat)=0),ite_eq_right (by decide : ¬ (2:Nat)=1),ite_true]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.reducePow,Nat.reduceMul]
    rw [hk]
    change ((k.toNat % 65536 + 31*65536)/65536)%256 = 31
    rw [Nat.add_mul_div_right _ _ (by decide), Nat.mod_div_self]
  · simp only [ite_eq_right (by omega : ¬ i=0),ite_eq_right (by omega : ¬ i=1),
      ite_eq_right (by omega : ¬ i=2)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat]
    have hb : 8*i≥24 := by omega
    have he : a.toNat<2^24 := by omega
    have hdiv : a.toNat/2^(8*i)=0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) hb))
    rw [Nat.shiftRight_eq_div_pow,hdiv]
    rfl

theorem nonceWord_byte (k : BitVec 64) {i : Nat} (hi : i<8) :
    (nonceWord k).extractLsb' (8*i) 8 =
      if i=0 then k.extractLsb' 0 8 else if i=1 then k.extractLsb' 8 8
      else if i=2 then 0x1f else 0 :=
  nonceValue_byte (nonceWord k) k (nonceWord_value k) hi

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end

/-! ## From `CommitTailSeed.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

def seedBytes (m : Mem) (p : Addr) (k : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m p 64 ++ [k.extractLsb' 0 8,k.extractLsb' 8 8]

theorem seedBytes_length (m : Mem) (p : Addr) (k : BitVec 64) :
    (seedBytes m p k).length=66 := by
  simp only [seedBytes,List.length_append,Proof.Sha3.bytesAt_length,List.length_cons,List.length_nil]

theorem seedBytes_get (m : Mem) (p : Addr) (k : BitVec 64) {j : Nat} (hj : j<66) :
    (seedBytes m p k).getD j 0 = if j<64 then m (p+BitVec.ofNat 64 j)
      else if j=64 then k.extractLsb' 0 8 else k.extractLsb' 8 8 := by
  unfold seedBytes
  by_cases h : j<64
  · rw [ite_eq_left h]
    rw [List.getD,List.getElem?_append_left (by rw [Proof.Sha3.bytesAt_length]; exact h)]
    exact Proof.MlKem.bytesAt_getD m p h
  · rw [ite_eq_right h,List.getD,List.getElem?_append_right (by rw [Proof.Sha3.bytesAt_length]; omega),Proof.Sha3.bytesAt_length]
    rcases (show j=64 ∨ j=65 by omega) with rfl|rfl <;> rfl

theorem seedNonceState_get (m : Mem) (p : Addr) (k : BitVec 64) {i : Nat} (hi : i<25) :
    (seedNonceState m p k)[i]! = if i<8 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i=8 then nonceWord k else if i=16 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedNonceState
  rw [Vector.getElem_ofFn]

theorem seedNonceState_A0 (m : Mem) (p : Addr) (k : BitVec 64) :
    seedNonceState m p k = Optimized.ResidentSeed66.A0 (seedBytes m p k) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Optimized.ResidentSeed66.byteOf_A0 (seedBytes_length m p k) hj]
  unfold Proof.Sha3.byteOf
  rw [seedNonceState_get m p k (by omega)]
  by_cases h32 : j<64
  · rw [ite_eq_left (by omega : j/8<8),ite_eq_left (by omega : j<66),
      seedBytes_get m p k (by omega),ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8<8)]
    by_cases h40 : j<72
    · rw [ite_eq_left (by omega : j/8=8),nonceWord_byte k (by omega)]
      rcases (show j=64 ∨ j=65 ∨ j=66 ∨ 67≤j by omega) with h|h|h|h
      · subst j
        rw [ite_eq_left (by decide : 64<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j
        rw [ite_eq_left (by decide : 65<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j; simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8=8)]
      by_cases h20 : j/8=16
      · rw [ite_eq_left h20,Optimized.ResidentMask.pad_byte (j%8) (by omega)]
        by_cases he : j=135 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail

end
