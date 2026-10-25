module

public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
public import VerifiedGarbage.Proof.Bignum.PdRanges
public import VerifiedGarbage.Proof.Bignum.X86_64.PubMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.PcMain
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import Mathlib.Logic.Relator
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Set

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def phases (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2, Folded.exp M.mm, M.mm aY aX aY]

theorem rest_eq (M : Mont) :
    Folded.rest M.mm = seqs ((wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code) ++ (phases M ++ wordOutStepsArr aY)) := rfl

/-- What an exponentiation leaves, from the setup's state `a`: the result `y`
at `aY`, `input^e mod N` for an input `X` below `N` when `R` is `R² mod N`;
the workspace changed only within `expAll`; the header. -/
def ExpOut (B : Addr) (Z w : Nat) (minv : BitVec 64) (N R X e : Nat) (a d : State) : Prop :=
  ∃ y, (X < N → R % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N → y = X ^ e % N) ∧ Good d B Z w minv ∧
    wv d.mem B (slot w aY) w = y ∧ Frm B (expAll w) a.mem d.mem ∧ Keep mmRegs a d ∧
    d.mxcsr.extractLsb' 6 10 = a.mxcsr.extractLsb' 6 10

/-- `seqs` of two nonempty lists, for `Code.allInstrs`. -/
theorem allInstrs_seqs_append (p : Instr → Bool) {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) :
    (seqs (a ++ b)).allInstrs p = ((seqs a).allInstrs p && (seqs b).allInstrs p) := by
  induction a with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, e, rfl⟩ : ∃ d e, b = d :: e := by cases b with | nil => exact absurd rfl hb | cons d e => exact ⟨d, e, rfl⟩
      rfl
    | cons d e =>
      show (Code.seq c (seqs ((d :: e) ++ b))).allInstrs p =
        ((Code.seq c (seqs (d :: e))).allInstrs p && (seqs b).allInstrs p)
      simp only [Code.allInstrs, ih (by simp), Bool.and_assoc]

theorem mask_not_expAll (w : Nat) : ∀ r ∈ expAll w, 8 * sMask + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMask := by
  have := hdr_lt_slot w aOne (show sMask < 32 by decide)
  have := hdr_lt_slot w aXm (show sMask < 32 by decide)
  have := hdr_lt_slot w aAcc (show sMask < 32 by decide)
  have := hdr_lt_slot w aTmp (show sMask < 32 by decide)
  have := hdr_lt_slot w aY (show sMask < 32 by decide)
  simp only [expAll, pExpRanges, pBitRanges, bitRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sMask, sI, sV, sBit, VG.Impl.Bignum.Public.sStarted, sFn] at * <;> omega_arith

/-- `rest` with the exponentiation `Es`: safe for every accepted cache, and
`input^e mod N` for a valid one. -/
theorem restWith_ok (Es : List (Prog isa)) (hEs : Es ≠ []) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R)
    (hE : ∀ (a : State) (minv : BitVec 64), SetupOut a B Z ((k+7)/8) minv N (Spec.Rsa.os2ip xb) →
      Frm B (pdAll ((k+7)/8)) s.mem a.mem → Keep mmRegs s a →
      wv a.mem B (slot ((k+7)/8) aR2) ((k+7)/8) = R →
      WP isa (seqs Es) a (ExpOut B Z ((k+7)/8) minv N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a)) :
    WP isa (seqs ((wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code) ++ (Es ++ wordOutStepsArr aY))) s
      fun t => ∃ y : Nat,
        (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
          y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
        MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
          (decide (Spec.Rsa.os2ip xb < N)) ∧ t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hle : ∀ r ∈ pdAll ((k+7)/8), r.1+r.2 ≤ Z :=
    fun r hr => (pdAll_le _ r hr).trans hZ
  refine wp_seqs_append (by simp [wordIn]) (by simp [hEs])
    (WP.mono_mx (by decide +kernel) (wordSetup_ok h) fun a ⟨mi,so,fa,ka,rra⟩ mxa => ?_)
  refine wp_seqs_append hEs (by simp [wordOutStepsArr])
    (WP.mono (hE a mi so fa ka rra) fun d ⟨y,hy,gd,yd,fd,kd,mxd⟩ => ?_)
  have fac : Frm B (pdAll ((k+7)/8)) s.mem d.mem := fa.trans (fd.mono (expAll_sub _))
  have fixed := Fixed.of_frm fac (pdAll_fixed _)
  have keep := ka.trans kd
  have maskD : word d.mem B (8*sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [fd.word_eq (mask_not_expAll _) (by unfold sMask sFn; omega_arith)]
    exact so.mask
  refine WP.mono_mx (by decide +kernel) (wordOutPhase_ok gd hZ (by omega_arith) (by omega_arith) yd
    (by rw [fixed sOut (by decide)]; exact h.hO)
    (by rw [fixed sK (by decide)]; exact h.hK) maskD
    (by rw [keep.2.2]; exact h.outSpan) h.outSep)
    fun t ⟨bytes,rax,saved,frame,kt⟩ mxt =>
      ⟨if Spec.Rsa.os2ip xb < N then y else Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N, ?_, ⟨?_,rax,
      fun i hi => by rw [saved i hi]; exact fixed i (by omega_arith),
      fun y hy hy' => by rw [frame y hy',InScr.of_frm fac hle y hy],
      (keep.trans kt).mono (by decide)⟩, by rw [mxt, mxd, mxa]⟩
  · intro hRR
    by_cases hX : Spec.Rsa.os2ip xb < N
    · rw [ite_eq_left hX]; exact hy hX hRR
    · rw [ite_eq_right hX]
  · by_cases hX : Spec.Rsa.os2ip xb < N
    · simpa only [hX, decide_true, ↓reduceIte] using bytes
    · simpa only [hX, decide_false, ↓reduceIte, Bool.false_eq_true] using bytes

/-- The ADX code's exponentiation: `X = input R`, `x^(e-1) R`, then `x^e`. -/
theorem phasesCore_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) (a : State) (mi : BitVec 64)
    (hg : Good a B Z ((k+7)/8) mi) (hN : wv a.mem B (slot ((k+7)/8) aN) ((k+7)/8) = N)
    (hinv : ((word a.mem B (slot ((k+7)/8) aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (hX : wv a.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb)
    (fa : Frm B (pdAll ((k+7)/8)) s.mem a.mem)
    (ka : Keep mmRegs s a) (rra : wv a.mem B (slot ((k+7)/8) aR2) ((k+7)/8) = R)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (phases M)) a (ExpOut B Z ((k+7)/8) mi N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a) := by
  refine WP.mono_mx hmx (Q := fun d => ∃ y, _ ∧ _ ∧ _ ∧ _ ∧ _) ?_ fun d ⟨y, h1, h2, h3, h4, h5⟩ mxd =>
    ⟨y, h1, h2, h3, h4, h5, by rw [mxd]⟩
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hb : B.toNat + slot ((k+7)/8) 8 ≤ 2^64 := by omega_arith
  have hw : 2 ≤ (k+7)/8 := by omega_arith
  have hR := VG.Proof.Bignum.coprime_pow2 h.odd (64*((k+7)/8))
  have hle : ∀ r ∈ pdAll ((k+7)/8), r.1+r.2 ≤ Z :=
    fun r hr => (pdAll_le _ r hr).trans hZ
  unfold phases
  -- `X = input R`.
  refine WP.seq (WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) hg hZ hw
    (by omega_arith) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hN hinv (by rw [rra]; exact h.rlt))
    fun b ⟨gb,nb,ib,lb,mb,ab,kb⟩ => ?_)
  rw [hX,rra] at mb
  have fb : Frm B (pdAll ((k+7)/8)) a.mem b.mem :=
    Frm.of_arrays ab (by simp [pdAll,pExpRanges,pBitRanges,bitRanges])
  have fb' : Frm B (expAll ((k+7)/8)) a.mem b.mem :=
    Frm.of_arrays ab (by simp [expAll,pExpRanges,pBitRanges,bitRanges])
  have fab := fa.trans fb
  have xab := Fixed.of_frm fab (pdAll_fixed _)
  have heb := h.e.congrK (InScr.of_frm fab hle) (ka.trans kb)
  obtain ⟨x,hx⟩ := exists_mont hR h.n1 (wv b.mem B (slot ((k+7)/8) aXm) ((k+7)/8))
  have inputB : wv b.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb := by
    rw [ab.wv_of_not_mem (by decide) (by decide) hb]; exact hX
  -- The exponentiation, by `e - 1`.
  refine WP.seq (WP.mono (exp_ok M (x := x) ⟨gb,nb,ib,rfl⟩ hZ hw (by omega_arith) hR lb hx
    (by rw [xab sE (by decide)]; exact h.hE) (by rw [xab sElen (by decide)]; exact h.hL) heb h.el h.L1 (by omega_arith)
    h.eodd h.e3)
    fun c ⟨cc,hYN,hYc,fc,kc⟩ => ?_)
  have inputC : wv c.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb :=
    (input_preserved fc hb).trans inputB
  -- The last multiplication, by the input.
  rw [seqs_one]
  refine WP.mono (final_factor_ok M (x := x) (e := Spec.Rsa.os2ip (evenLast eb)) cc.good hZ hw (by omega_arith)
    cc.n cc.inv hR inputC hYN hYc)
    fun d ⟨gd,yd,ad,kd⟩ => ?_
  have fd : Frm B (expAll ((k+7)/8)) c.mem d.mem :=
    Frm.of_arrays ad (by simp [expAll,pExpRanges,pBitRanges,bitRanges])
  refine ⟨_, fun _ hRR => ?_, gd, yd,
    (fb'.trans (fc.mono fun r hr => by simp only [expAll, List.mem_append]; exact .inr hr)).trans fd,
    ((kb.trans kc).trans kd).mono (by decide)⟩
  have same := VG.Proof.Bignum.encoded_base hR hx mb hRR
  rw [VG.Proof.Bignum.factor_congr same, os2ip_evenLast h.eodd]

theorem phases_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) (a : State) (mi : BitVec 64)
    (so : SetupOut a B Z ((k+7)/8) mi N (Spec.Rsa.os2ip xb)) (fa : Frm B (pdAll ((k+7)/8)) s.mem a.mem)
    (ka : Keep mmRegs s a) (rra : wv a.mem B (slot ((k+7)/8) aR2) ((k+7)/8) = R)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (seqs (phases M)) a (ExpOut B Z ((k+7)/8) mi N R (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip eb) a) :=
  phasesCore_ok M h a mi so.good so.n so.inv so.x fa ka rra hmx

/-- Execution is safe for every accepted cache. A valid cache additionally
establishes the numerical result. -/
theorem rest_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R)
    (hmx : (seqs (phases M)).allInstrs (fun i => !loadsMxcsr i) = true) :
    WP isa (Folded.rest M.mm) s fun t => ∃ y : Nat,
      (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
        y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  rw [rest_eq]
  exact WP.mono (restWith_ok (phases M) (by simp [phases]) h fun a mi so fa ka rra => phases_ok M h a mi so fa ka rra hmx)
    fun t ⟨y, hy, hp, _⟩ => ⟨y, hy, hp⟩

end VG.Proof.Bignum.X86_64.FoldedPublic
