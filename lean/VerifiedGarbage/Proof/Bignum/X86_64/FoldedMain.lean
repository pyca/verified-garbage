module

public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedIO
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Sse

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def phases (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2, Folded.exp M.mm, M.mm aY aX aY]

theorem rest_eq (M : Mont) :
    Folded.rest M.mm = seqs ((wordIn ++ restStepsWith VG.Impl.Rsa.X86_64.Compare8.code) ++ (phases M ++ wordOutStepsArr aY)) := rfl

/-- Execution is safe for every accepted cache. A valid cache additionally
establishes the numerical result. -/
theorem rest_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Folded.rest M.mm) s fun t => ∃ y : Nat,
      (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
        y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hb : B.toNat + slot ((k+7)/8) 8 ≤ 2^64 := by omega
  have hw : 2 ≤ (k+7)/8 := by omega
  have hR := VG.Proof.Bignum.coprime_pow2 h.odd (64*((k+7)/8))
  have hle : ∀ r ∈ pdAll ((k+7)/8), r.1+r.2 ≤ Z :=
    fun r hr => (pdAll_le _ r hr).trans hZ
  rw [rest_eq]
  refine wp_seqs_append (by simp [wordIn]) (by simp [phases])
    (WP.mono (wordSetup_ok h) fun a ⟨mi,so,fa,ka,rra⟩ => ?_)
  refine wp_seqs_append (by simp [phases]) (by simp [wordOutStepsArr]) ?_
  unfold phases
  -- `X = input R`.
  refine WP.seq (WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good hZ hw
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) so.n so.inv (by rw [rra]; exact h.rlt))
    fun b ⟨gb,nb,ib,lb,mb,ab,kb⟩ => ?_)
  rw [so.x,rra] at mb
  have fb : Frm B (pdAll ((k+7)/8)) a.mem b.mem :=
    Frm.of_arrays ab (by simp [pdAll,pExpRanges,pBitRanges,bitRanges])
  have fab := fa.trans fb
  have xab := Fixed.of_frm fab (pdAll_fixed _)
  have heb := h.e.congrK (InScr.of_frm fab hle) (ka.trans kb)
  obtain ⟨x,hx⟩ := exists_mont hR h.n1 (wv b.mem B (slot ((k+7)/8) aXm) ((k+7)/8))
  have inputB : wv b.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb := by
    rw [ab.wv_of_not_mem (by decide) (by decide) hb]; exact so.x
  -- The exponentiation, by `e - 1`.
  refine WP.seq (WP.mono (exp_ok M (x := x) ⟨gb,nb,ib,rfl⟩ hZ hw (by omega) hR lb hx
    (by rw [xab sE (by decide)]; exact h.hE) (by rw [xab sElen (by decide)]; exact h.hL) heb h.el h.L1 (by omega)
    h.eodd h.e3)
    fun c ⟨cc,hYN,hYc,fc,kc⟩ => ?_)
  have inputC : wv c.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb :=
    (input_preserved fc hb).trans inputB
  -- The last multiplication, by the input.
  rw [seqs_one]
  refine WP.mono (final_factor_ok M (x := x) (e := Spec.Rsa.os2ip (evenLast eb)) cc.good hZ hw (by omega)
    cc.n cc.inv hR inputC hYN hYc)
    fun d ⟨gd,yd,ad,kd⟩ => ?_
  have fd : Frm B (pdAll ((k+7)/8)) c.mem d.mem :=
    Frm.of_arrays ad (by simp [pdAll,pExpRanges,pBitRanges,bitRanges])
  have fac := (fab.trans (fc.mono (pExpRanges_pdAll _))).trans fd
  have fixed := Fixed.of_frm fac (pdAll_fixed _)
  have keep := ((ka.trans kb).trans kc).trans kd
  have maskD : word d.mem B (8*sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [ad.hslot (by decide),
      fc.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (by unfold sMask sFn; omega),ab.hslot (by decide)]
    exact so.mask
  refine WP.mono (wordOutPhase_ok gd hZ (by omega) (by omega) yd
    (by rw [fixed sOut (by decide)]; exact h.hO)
    (by rw [fixed sK (by decide)]; exact h.hK) maskD
    (by rw [keep.2.2]; exact h.outSpan) h.outSep)
    fun t ⟨bytes,rax,saved,frame,kt⟩ =>
      ⟨x^Spec.Rsa.os2ip (evenLast eb) * Spec.Rsa.os2ip xb % N,?_,⟨?_,rax,
      fun i hi => by rw [saved i hi]; exact fixed i (by omega),
      fun y hy hy' => by rw [frame y hy',InScr.of_frm fac hle y hy],
      (keep.trans kt).mono (by decide)⟩⟩
  · intro hRR
    have same := VG.Proof.Bignum.encoded_base hR hx mb hRR
    rw [VG.Proof.Bignum.factor_congr same, os2ip_evenLast h.eodd]
  · simpa only [decide_eq_true_eq] using bytes

end VG.Proof.Bignum.X86_64.FoldedPublic
