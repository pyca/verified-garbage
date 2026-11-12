module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Checks
public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Guard
import VerifiedGarbage.Proof.Rsa.X86.WordRt.Mul
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.X86.CvInverseCall
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Rsa.X86.InvGate
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange

/-! # CRT parameter calculation at a run-time width: the divisions

`n / p` before the checks (`firstDiv_ok`), and `d mod (p - 1)` and
`d mod (q - 1)` after them (`divP_ok`, `divQ_ok`), on `RtWs`; `core_ok`
composes them with the checks.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs andS)
open VG.Impl.Rsa.X86.KeyRt (Lay sCy sQb)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append bank invArrs invSlots rtSlots)
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.WordRt (MLen wq mw Bal Top)

structure Start (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  n : num s.mem g.base (kw len) aDQ = g.N
  p : num s.mem g.base (kw len) aP = g.P
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  zeros : ∀ j ∈ zeroC, num s.mem g.base (kw len) j = 0

theorem firstDiv_ok {g : Geometry} {len : Nat} {s : State} (h : Start g len s) {ap aq : Nat}
    (cp : VG.Proof.Bignum.X86.CallArgument s g.base g.size 9 (BitVec.ofNat 32 ap))
    (cq : VG.Proof.Bignum.X86.CallArgument s g.base g.size 11 (BitVec.ofNat 32 aq))
    (hap : ap ≤ 1024) (haq : aq ≤ 1024) (hpB : g.P < 2 ^ (8 * ap)) (hqB : g.Q < 2 ^ (8 * aq)) :
    WP isa firstDiv s fun t => StC g len t ∧
      Keep g.base (kw len) [aDR2, aDR3] [sPodd, sG, VG.Impl.Rsa.X86.WordModRt.oJ] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      ∃ an, an ≤ 1024 ∧ VG.Proof.Bignum.X86.CallArgument s g.base g.size 7 (BitVec.ofNat 32 an) ∧ kw an = kw len ∧
        (slot t.mem g.base sG = 0 ↔ Bal an ap aq (mw s.mem g.base (kw len) aDQ (kw len - 1))) := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  obtain ⟨an, han, hkw, cn⟩ := h.ws.lenArg
  unfold firstDiv
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (bitOf_ok h.ws (j := aP) (sl := sPodd) (by decide) (by decide))
    fun v ⟨hv, kv, vv, rv⟩ => ?_)
  have Ov := keep_outside h.ws.ws kv (by simp) (by decide)
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.balanced_ok hv (cn.keep rv (by decide) Ov) (cp.keep rv (by decide) Ov)
    (cq.keep rv (by decide) Ov) han hap haq (n := aDQ) (sl := sG) (by decide) (by decide)) fun u ⟨hu, ku, eu, ru⟩ => ?_
  have pu : num u.mem g.base (kw len) aP = g.P := by
    rw [ku.num (by simp) (by decide) (fit _ (by decide)), kv.num (by simp) (by decide) (fit _ (by decide)), h.p]
  have qu : num u.mem g.base (kw len) aQ = g.Q := by
    rw [ku.num (by simp) (by decide) (fit _ (by decide)), kv.num (by simp) (by decide) (fit _ (by decide)), h.q]
  have pu' : val32 u.mem g.base (arr (kw len) aP) (kw len) = g.P := pu
  have qu' : val32 u.mem g.base (arr (kw len) aQ) (kw len) = g.Q := qu
  -- The product: over the primes' `w / 2` words where the guard holds.
  suffices H : WP isa (VG.Impl.Rsa.X86.WordModRt.ifBalanced sG (VG.Impl.Rsa.X86.WordModRt.mulHalf lay aDR2 aP aQ)
      (VG.Impl.Rsa.X86.WordModRt.mulWide lay aDR2 aP aQ)) u fun t => RtWs lay t g.base g.size len nArr ∧
        Keep g.base (kw len) [aDR2, aDR2 + 1] [VG.Impl.Rsa.X86.WordModRt.oJ] u.mem t.mem ∧
        val32 t.mem g.base (arr (kw len) aDR2) (2 * kw len) = g.P * g.Q ∧
        Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] u t by
    refine WP.mono H fun t ⟨ht, kt, et, rt⟩ => ?_
    have K : Keep g.base (kw len) [aDR2, aDR3] [sPodd, sG, VG.Impl.Rsa.X86.WordModRt.oJ] s.mem t.mem :=
      (kv.mono (by simp) (by decide)).trans ((ku.mono (by simp) (by decide)).trans (kt.mono (by decide) (by decide)))
    have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
      (rv.mono (by decide)).trans ((ru.mono (by decide)).trans (rt.mono (by decide)))
    have same (j : Nat) (hj : j < nArr) (notWritten : j ∉ [aDR2, aDR3]) :
        num t.mem g.base (kw len) j = num s.mem g.base (kw len) j :=
      K.num (fun k hk e => notWritten (by subst e; exact hk)) (by decide) (fit j hj)
    refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, K, R, an, han, cn, hkw, ?_⟩
    · rw [kt.slot (by decide) (by decide), ku.slot (by decide) (by decide), vv, h.p]
    · rw [same _ (by decide) (by decide), h.p]
    · rw [same _ (by decide) (by decide), h.q]
    · rw [same _ (by decide) (by decide), h.d]
    · rw [K.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
    · rw [same _ (by decide) (by decide), h.n]
    · exact et
    · intro j hj
      have fits : j < nArr := by
        simp only [zeroCk, List.mem_cons, List.not_mem_nil, or_false] at hj
        unfold nArr; omega
      have notWritten : j ∉ [aDR2, aDR3] := by
        simp only [zeroCk, List.mem_cons, List.not_mem_nil, or_false] at hj
        simp only [aDR2, aDR3, List.mem_cons, List.not_mem_nil, or_false]
        omega
      rw [same j fits notWritten]
      exact h.zeros j (by simp only [zeroCk, zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
    · rw [kt.slot (by decide) (by decide), eu]
      have w : mw v.mem g.base (kw len) aDQ (kw len - 1) = mw s.mem g.base (kw len) aDQ (kw len - 1) :=
        kv.word (by unfold S; omega) (by simp) (by decide) (fit _ (by decide))
      rw [w]
  refine VG.Proof.Rsa.X86.WordRt.ifBalanced_ok hu (sl := sG) (by decide) eu ?_ ?_
  · intro hB u' hu' K' m'
    obtain ⟨h8, h2p, h2q, -, -⟩ := hB
    have kan : kw len = 2 * ((an + 7) / 8) := hkw ▸ rfl
    have e8p : 8 * ap = 32 * (kw len / 2) := by omega
    have e8q : 8 * aq = 32 * (kw len / 2) := by omega
    have lowP : val32 u'.mem g.base (arr (kw len) aP) (kw len / 2) = g.P := by
      rw [m', VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := kw len) (by omega) (by rw [pu', ← e8p]; exact hpB), pu']
    have lowQ : val32 u'.mem g.base (arr (kw len) aQ) (kw len / 2) = g.Q := by
      rw [m', VG.Proof.Rsa.X86.WordRt.val32_low_of_lt (n := kw len) (by omega) (by rw [qu', ← e8q]; exact hqB), qu']
    refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulHalf_ok hu' (o := aDR2) (a := aP) (b := aQ) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, kt, et, rt⟩ =>
        ⟨ht, by rw [← m']; exact kt, by rw [et, lowP, lowQ], (K'.mono (by decide)).trans rt⟩
  · intro _ u' hu' K' m'
    refine WP.mono (VG.Proof.Rsa.X86.WordRt.mulWide_ok hu' (o := aDR2) (a := aP) (b := aQ) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨ht, kt, et, rt⟩ =>
        ⟨ht, by rw [← m']; exact kt, by rw [et, m', pu, qu], (K'.mono (by decide)).trans rt⟩

theorem InverseResult.frame {g : Geometry} {len : Nat} {m m' : Mem} {js ds : List Nat}
    (h : InverseResult g len m) (keep : Keep g.base (kw len) js ds m m')
    (hj : ∀ j ∈ js, j ≠ 3) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (mask : ∀ d ∈ ds, sMask + 4 ≤ d ∨ d + 4 ≤ sMask) (fit : arr (kw len) 3 + S (kw len) ≤ 2 ^ 64) :
    InverseResult g len m' := by
  obtain ⟨v, hv, hi⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [keep.slot (by decide) mask]; exact hv
  · rw [keep.num hj hd fit]; exact hi

structure StE (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  q : num s.mem g.base (kw len) aQ = g.Q
  d : num s.mem g.base (kw len) aD = g.D
  ddTop : w32 s.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0
  remP : 0 < 2 * (g.P / 2) → num s.mem g.base (kw len) aDR2 = g.D % (2 * (g.P / 2))
  mask : InverseResult g len s.mem

theorem divP_ok {g : Geometry} {len : Nat} {s : State} (h : StD g len s) :
    WP isa (div aDR2) s fun t => StE g len t ∧
      Keep g.base (kw len) [aDQ, aDR2, aDT] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  refine WP.mono (div_ok h.ws (q := aDQ) (r := aDR2) (d := aDD) (t := aDT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.ddTop) ?_
  rintro t ⟨ht, kt, rt, vt⟩
  refine ⟨⟨ht, ?_, ?_, ?_, ?_, ?_⟩, kt, rt.mono (by decide)⟩
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), h.q]
  · rw [kt.num (by decide) (by decide) (fit _ (by decide)), h.d]
  · rw [kt.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  · intro pos
    have positive : 0 < num s.mem g.base (kw len) aDD := by rw [h.dd]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base (kw len) aDR2 = num s.mem g.base (kw len) aDQ % num s.mem g.base (kw len) aDD at rem
    rw [h.dq, h.dd] at rem
    exact rem
  · exact h.mask.frame kt (by decide) (by decide) (by decide) (fit _ (by decide))

/-- After the remainders: known where `p q = n`. -/
structure Computed (g : Geometry) (len : Nat) (s : State) : Prop where
  ws : RtWs lay s g.base g.size len nArr
  remP : g.P * g.Q = g.N → 0 < 2 * (g.P / 2) → num s.mem g.base (kw len) aDR2 = g.D % (2 * (g.P / 2))
  remQ : g.P * g.Q = g.N → 0 < 2 * (g.Q / 2) → num s.mem g.base (kw len) aDR3 = g.D % (2 * (g.Q / 2))
  mask : InverseResult g len s.mem

theorem divQ_ok {g : Geometry} {len : Nat} {s : State} (h : StE g len s) :
    WP isa (seqs [VG.Impl.Rsa.X86.KeyRt.copy lay aDQ aD, VG.Impl.Rsa.X86.KeyRt.copy lay aDD aQ,
      .block (VG.Impl.Rsa.X86.KeyRt.clrLow lay aDD), div aDR3]) s fun t => Computed g len t ∧
      Keep g.base (kw len) [aDQ, aDD, aDR3, aDT] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h.ws (o := aDQ) (a := aD) (by decide) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok hu (o := aDD) (a := aQ) (by decide) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv, topv⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLow_ok hv (j := aDD) (by decide)) fun z ⟨hz, kz, vz, rz, topz⟩ => ?_
  have top : w32 z.mem g.base (arr (kw len) aDD + 4 * (kw len)) = 0 := by
    rw [topz, topv, ku.word (by unfold S; omega) (by decide) (by decide) (fit _ (by decide)), h.ddTop]
  refine WP.mono (div_ok hz (q := aDQ) (r := aDR3) (d := aDD) (t := aDT) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) top) fun t ⟨ht, kt, rt, vt⟩ => ?_
  have K : Keep g.base (kw len) [aDQ, aDD, aDR3, aDT] [sCy, sQb] s.mem t.mem :=
    ku.mono.trans (kv.mono.trans (kz.mono.trans (kt.mono (by decide) (by decide))))
  have R : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans ((rz.mono (by decide)).trans (rt.mono (by decide))))
  refine ⟨⟨ht, ?_, ?_, h.mask.frame K (by decide) (by decide) (by decide) (fit _ (by decide))⟩, K, R⟩
  · intro _; rw [K.num (by decide) (by decide) (fit _ (by decide))]; exact h.remP
  · have divisor : num z.mem g.base (kw len) aDD = 2 * (g.Q / 2) := by
      rw [vz, vv, ku.num (by decide) (by decide) (fit _ (by decide)), h.q]
    have numerator : num z.mem g.base (kw len) aDQ = g.D := by
      rw [kz.num (by decide) (by decide) (fit _ (by decide)), kv.num (by decide) (by decide) (fit _ (by decide)), vu, h.d]
    intro _ pos
    have positive : 0 < num z.mem g.base (kw len) aDD := by rw [divisor]; exact pos
    have rem := (vt positive).2
    change num t.mem g.base (kw len) aDR3 = num z.mem g.base (kw len) aDQ % num z.mem g.base (kw len) aDD at rem
    rw [divisor, numerator] at rem
    exact rem

/-- The remainders bit by bit. -/
theorem divRems_ok {g : Geometry} {len : Nat} {s : State} (h : StD g len s) :
    WP isa divRems s fun t => Computed g len t ∧
      Keep g.base (kw len) [aDQ, aDR2, aDD, aDR3, aDT] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold divRems rems
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  exact WP.mono (divP_ok h) fun d ⟨hd, kd, rd⟩ => WP.mono (divQ_ok hd) fun t ⟨ht, kt, rt⟩ =>
    ⟨ht, kd.mono.trans kt.mono, rd.trans rt⟩

/-- The header words the word steps write. -/
abbrev wordSlots : List Nat := [VG.Impl.Rsa.X86.WordModRt.oD, VG.Impl.Rsa.X86.WordModRt.oD1,
  VG.Impl.Rsa.X86.WordModRt.oV, VG.Impl.Bignum.X86.R2Words.oMask VG.Impl.Rsa.X86.WordModRt.h0,
  VG.Impl.Rsa.X86.WordModRt.oSteps, VG.Impl.Rsa.X86.WordModRt.oQ, VG.Impl.Rsa.X86.WordModRt.oU0,
  VG.Impl.Rsa.X86.WordModRt.oU2, VG.Impl.Rsa.X86.WordModRt.oDig]

/-- The remainders by word steps: `p`'s length `a` (and, under the guard, `q`'s), and where `p q = n`,
`p - 1` and `q - 1` with their top bits set. -/
theorem wordRems_ok {g : Geometry} {len : Nat} {s : State} (h : StD g len s) {a : Nat}
    (hm : MLen s g.base g.size 9 a) (h4 : 4 ≤ wq a) (hw : wq a ≤ kw len)
    (top : g.P * g.Q = g.N → Top (wq a) (2 * (g.P / 2)) ∧ Top (wq a) (2 * (g.Q / 2))) :
    WP isa wordRems s fun t => Computed g len t ∧
      Keep g.base (kw len) [aDQ, aDR2, aDD, aDR3, aDT] wordSlots s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  unfold wordRems rems
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_cond_ok h.ws hm (x := aDQ) (r := aDR2) (m := aDD) (t := aDT)
    (top := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h4 hw (by simp)) fun t1 ⟨h1, k1, c1, r1⟩ => ?_
  have O1 := keep_outside h.ws.ws k1 (by simp; decide) (by decide)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h1 (o := aDQ) (a := aD) (by decide) (by decide) (by decide)) fun u ⟨hu, ku, vu, ru, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok hu (o := aDD) (a := aQ) (by decide) (by decide) (by decide)) fun v ⟨hv, kv, vv, rv, _⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clrLow_ok hv (j := aDD) (by decide)) fun z ⟨hz, kz, vz, rz, _⟩ => ?_
  have Kz : Keep g.base (kw len) [aDQ, aDD] [] t1.mem z.mem := ku.mono.trans (kv.mono.trans kz.mono)
  have Rz : Keeps [.eax, .ebx, .ecx, .edx, .ebp] t1 z :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans (rz.mono (by decide)))
  have Oz := keep_outside h1.ws Kz (by simp; decide) (by decide)
  have hmz : MLen z g.base g.size 9 a :=
    (hm.keep r1 (by decide) O1).keep Rz (by decide) Oz
  refine WP.mono (VG.Proof.Rsa.X86.WordRt.wordMod_cond_ok hz hmz (x := aDQ) (r := aDR3) (m := aDD) (t := aDT)
    (top := none) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h4 hw (by simp)) fun t ⟨ht, kt, ct, rt⟩ => ?_
  have K : Keep g.base (kw len) [aDQ, aDR2, aDD, aDR3, aDT] wordSlots s.mem t.mem :=
    k1.mono.trans (Kz.mono.trans kt.mono)
  have R : Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := r1.trans ((Rz.mono (by decide)).trans rt)
  have dz : num z.mem g.base (kw len) aDQ = g.D := by
    rw [kz.num (by decide) (by decide) (fit _ (by decide)), kv.num (by decide) (by decide) (fit _ (by decide)), vu,
      k1.num (by decide) (by decide) (fit _ (by decide)), h.d]
  have mz : num z.mem g.base (kw len) aDD = 2 * (g.Q / 2) := by
    rw [vz, vv, ku.num (by decide) (by decide) (fit _ (by decide)), k1.num (by decide) (by decide) (fit _ (by decide)),
      h.q]
  refine ⟨⟨ht, fun hpq _ => ?_, fun hpq _ => ?_, h.mask.frame K (by decide) (by decide) (by decide) (fit _ (by decide))⟩,
    K, R⟩
  · have e := (c1 (by rw [h.dd]; exact (top hpq).1)).2
    simp only [VG.Proof.Rsa.X86.WordRt.xw] at e
    change num t1.mem g.base (kw len) aDR2 = num s.mem g.base (kw len) aDQ % num s.mem g.base (kw len) aDD at e
    rw [kt.num (by decide) (by decide) (fit _ (by decide)), Kz.num (by decide) (by decide) (fit _ (by decide)), e,
      h.dq, h.dd]
  · have e := (ct (by rw [mz]; exact (top hpq).2)).2
    simp only [VG.Proof.Rsa.X86.WordRt.xw] at e
    change num t.mem g.base (kw len) aDR3 = num z.mem g.base (kw len) aDQ % num z.mem g.base (kw len) aDD at e
    rw [e, dz, mz]

def coreArrays : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 18, 19, 20, 21, 22, 23]
def coreSlots : List Nat := [sOdd, sB, sC, sT, sPodd, sE1, sE2, sE3, sMask, sCy, sQb, sG] ++ rtSlots

theorem StD.mem {g : Geometry} {len : Nat} {s u : State} (h : StD g len s) (hu : RtWs lay u g.base g.size len nArr)
    (M : u.mem = s.mem) : StD g len u :=
  ⟨hu, by rw [M]; exact h.q, by rw [M]; exact h.d, by rw [M]; exact h.ddTop, by rw [M]; exact h.dq,
    by rw [M]; exact h.dd, by rw [M]; exact h.mask⟩

theorem core_ok [VG.Proof.Rsa.X86.BatchLaw] {g : Geometry} {len : Nat} {s : State} (h : Start g len s) {args : Nat → BitVec 32}
    (gate : InvGate args g.base g.size g.P g.Q s) (lens : (args 9).toNat ≤ 1024 ∧ (args 11).toNat ≤ 1024)
    (arg9 : ∀ t, Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t →
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) s.mem t.mem →
      VG.Proof.Bignum.X86.CallArgument t g.base g.size 9 (args 9)) :
    WP isa core s fun t =>
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem g.base (kw len) aZero = 0 ∧ Computed g len t := by
  have fit := fun j (hj : j < nArr) => h.ws.ws.fit64 (j := j) hj
  have cp : VG.Proof.Bignum.X86.CallArgument s g.base g.size 9 (BitVec.ofNat 32 (args 9).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gate.pArg
  have cq : VG.Proof.Bignum.X86.CallArgument s g.base g.size 11 (BitVec.ofNat 32 (args 11).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gate.qArg
  have pB : g.P < 2 ^ (8 * (args 9).toNat) := by rw [← VG.Proof.Bignum.pow256_eq]; exact gate.pBound
  have qB : g.Q < 2 ^ (8 * (args 11).toNat) := by rw [← VG.Proof.Bignum.pow256_eq]; exact gate.qBound
  unfold VG.Impl.Rsa.X86.CrtValuesRt.core
  refine WP.seq (WP.mono (firstDiv_ok h cp cq lens.1 lens.2 pB qB) fun a ⟨ha, ka, ra, an, _, _, hkw, hg⟩ => ?_)
  refine WP.seq ?_
  change WP isa (seqs (checksA ++ checksB)) a _
  rw [wp_seqs_append (by unfold checksA; exact List.cons_ne_nil _ _) (by unfold checksB; exact List.cons_ne_nil _ _)]
  refine WP.mono (checksA_ok ha) fun b ⟨hb, kb, rb⟩ => ?_
  have ga := gate.keep ra (by decide) (keep_outside h.ws.ws ka (by decide) (by decide))
  have gb := ga.keep rb (by decide) (keep_outside ha.ws.ws kb (by decide) (by decide))
  refine WP.mono (checksB_ok hb gb) fun c ⟨hc, kc, rc⟩ => ?_
  have spb : b.gpr .esp = s.gpr .esp := (rb.1 .esp (by decide)).trans (ra.1 .esp (by decide))
  rw [spb] at kc
  have Kc : VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
      (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) s.mem c.mem :=
    (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs
      ((ka.mono (by decide) (by decide)).trans (kb.mono (by decide) (by decide)))).trans
      (kc.mono (ranges_sub (by decide) (by decide)))
  have Rc : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s c := ra.trans ((rb.mono (by decide)).trans rc)
  have nowrap : g.size ≤ 2 ^ 64 := by have := h.ws.ws.workspace.nowrap; omega
  -- The guard, through the checks.
  have sc : slot c.mem g.base sG = slot a.mem g.base sG := by
    rw [outsS_slot kc gate.room (by decide) hc.ws.ws.hdr_le (by decide), kb.slot (by decide) (by decide)]
  have topN : 2 ^ 31 ≤ mw s.mem g.base (kw len) aDQ (kw len - 1) ↔ 2 ^ (32 * kw len - 1) ≤ g.N := by
    rw [← h.n]; exact VG.Proof.Rsa.X86.WordRt.top_iff h.ws.kw_pos
  have post : ∀ t, Computed g len t →
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) c.mem t.mem →
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] c t →
      VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      num t.mem g.base (kw len) aZero = 0 ∧ Computed g len t := fun t ht K R => by
    have K' := Kc.trans K
    refine ⟨K', Rc.trans R, ?_, ht⟩
    rw [outsS_num K' gate.room (by decide) (by decide)
      (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end (by decide)) h.ws.ws.fits) nowrap]
    exact h.zeros aZero (by decide)
  have hg' : slot c.mem g.base sG = 0 ↔
      Bal an (args 9).toNat (args 11).toNat (mw s.mem g.base (kw len) aDQ (kw len - 1)) := by
    rw [sc]; exact hg
  refine VG.Proof.Rsa.X86.WordRt.ifBalanced_ok hc.ws (sl := sG) (by decide) hg'
    (fun bal u hu Ku Mu => ?_) (fun _ u hu Ku Mu => ?_)
  · obtain ⟨h4, hroom, tops⟩ := VG.Proof.Rsa.X86.WordRt.bal_top bal hkw topN pB qB
    have Ou : VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS g.base (s.gpr .esp)
        (VG.Proof.Rsa.X86.Keys.ranges (kw len) coreArrays coreSlots) s.mem u.mem := by
      rw [Mu]; exact Kc
    have hm : MLen u g.base g.size 9 (args 9).toNat :=
      ⟨by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact arg9 u (Rc.trans (Ku.mono (by decide))) Ou, lens.1⟩
    refine WP.mono (wordRems_ok (hc.mem hu Mu) hm h4 (by omega) fun hpq => ⟨(tops hpq).2.1, (tops hpq).2.2⟩)
      fun t ⟨ht, kt, rt⟩ => post t ht ?_ ((Ku.mono (by decide)).trans (rt.mono (by decide)))
    rw [← Mu]
    exact VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs (kt.mono (by decide) (by decide))
  · refine WP.mono (divRems_ok (hc.mem hu Mu)) fun t ⟨ht, kt, rt⟩ =>
      post t ht ?_ ((Ku.mono (by decide)).trans rt)
    rw [← Mu]
    exact VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.of_outs (kt.mono (by decide) (by decide))

end VG.Proof.Rsa.X86.CrtValuesRt
