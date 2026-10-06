import VerifiedGarbage.Proof.Bignum.X86_64.FoldedExp
import VerifiedGarbage.Proof.Bignum.X86_64.PdMain

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

def phases (M : Mont) : List (Prog isa) := [M.mm aXm aX aR2,Folded.exp65537 M.mm]

theorem rest_eq (M : Mont) :
    Folded.rest M.mm = seqs ((pdIn ++ restSteps) ++ (phases M ++ outSteps)) := rfl

/-- Execution is safe for every accepted cache. A valid cache additionally
establishes the numerical result for exponent 65537. -/
theorem rest_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Folded.rest M.mm) s fun t => ∃ y : Nat,
      (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
        y = Spec.Rsa.os2ip xb ^ 65537 % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.z
  have hn := h.scr.nowrap
  have hb : B.toNat + slot ((k+7)/8) 8 ≤ 2^64 := by omega
  have hw : 2 ≤ (k+7)/8 := by omega
  have hR := VG.Proof.Bignum.coprime_pow2 h.odd (64*((k+7)/8))
  have hle : ∀ r ∈ pdAll ((k+7)/8), r.1+r.2 ≤ Z :=
    fun r hr => (pdAll_le _ r hr).trans hZ
  rw [rest_eq]
  refine wp_seqs_append (by simp [pdIn]) (by simp [phases])
    (WP.mono (pdSetup_ok h) fun a ⟨mi,so,fa,ka,rra⟩ => ?_)
  refine wp_seqs_append (by simp [phases]) (by simp [outSteps,outStepsArr]) ?_
  unfold phases
  refine WP.seq (WP.mono (mmN_ok M (o := aXm) (a := aX) (b := aR2) so.good hZ hw
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) so.n so.inv (by rw [rra]; exact h.rlt))
    fun b ⟨gb,nb,ib,lb,mb,ab,kb⟩ => ?_)
  rw [so.x,rra] at mb
  have fb : Frm B (pdAll ((k+7)/8)) a.mem b.mem :=
    Frm.of_arrays ab (by simp [pdAll,pExpRanges,pBitRanges,bitRanges])
  obtain ⟨x,hx⟩ := exists_mont hR h.n1 (wv b.mem B (slot ((k+7)/8) aXm) ((k+7)/8))
  have inputB : wv b.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb := by
    rw [ab.wv_of_not_mem (by decide) (by decide) hb]; exact so.x
  rw [seqs_one]
  refine WP.mono (exp65537_factor_ok M ⟨gb,nb,ib,rfl⟩ hZ hw (by omega) hR lb hx inputB)
    fun c ⟨gc,yc,fc,kc⟩ => ?_
  have fac := (fa.trans fb).trans (fc.mono fun _ hr => List.mem_append_right _ hr)
  have fixed := Fixed.of_frm fac (pdAll_fixed _)
  have keep := (ka.trans kb).trans kc
  have maskC : word c.mem B (8*sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [fc.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega),ab.hslot (by decide)]
    exact so.mask
  refine WP.mono (outPhase_ok gc hZ (by omega) (by omega) yc
    (by rw [fixed sOut (by decide)]; exact h.hO)
    (by rw [fixed sK (by decide)]; exact h.hK) maskC
    (fun j hj => by rw [keep.2.2]; exact h.out j hj) h.outSep)
    fun t ⟨bytes,rax,saved,frame,kt⟩ => ⟨x^65536 * Spec.Rsa.os2ip xb % N,?_,⟨?_,rax,
      fun i hi => by rw [saved i hi]; exact fixed i (by omega),
      fun y hy hy' => by rw [frame y hy',InScr.of_frm fac hle y hy],
      (keep.trans kt).mono (by decide)⟩⟩
  · intro hRR
    have same := VG.Proof.Bignum.encoded_base hR hx mb hRR
    have eq := VG.Proof.Bignum.factor_congr (e := 65536) same
    rwa [show (65536 : Nat)+1 = 65537 by decide] at eq
  · simpa only [decide_eq_true_eq] using bytes

end VG.Proof.Bignum.X86_64.FoldedPublic
