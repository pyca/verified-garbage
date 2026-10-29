module
public import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
public import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `vg_rsa_crt_values` on ARMv7: the division of `n` by `p` -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys VG.Proof.Bignum.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

/-- `divHdr q r d t`: the division's header. -/
theorem divHdr_ok {s : State} {B : BitVec 32} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < 256) (hr : r < 256) (hd : d < 256) (ht : t < 256)
    (cnt : s.mem.readW (off (State.addr B) 16) 32 = BitVec.ofNat 32 w) {rest : List Instr} {Q : State → Prop}
    (k : ∀ u, Ws u B Z w N → Keep B w [] [0, 4, 8, 12] s.mem u.mem → DivHdr u.mem B w q r d t →
      Rest opRegs s u → WP isa (.block rest) u Q) :
    WP isa (.block (divHdr q r d t ++ rest)) s Q := by
  have hz := h.hdr_le
  have nw := h.nowrap
  unfold divHdr
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h (by decide) hq fun s1 p1 r1 m1 h1 => ?_
  refine wp_strSlot h1 (d := 0) (by decide) fun s2 u2 => ?_
  have h2 := h1.of_mupd u2
  refine ptr_ok h2 (by decide) hr fun s3 p3 r3 m3 h3 => ?_
  refine wp_strSlot h3 (d := 4) (by decide) fun s4 u4 => ?_
  have h4 := h3.of_mupd u4
  refine ptr_ok h4 (by decide) hd fun s5 p5 r5 m5 h5 => ?_
  refine wp_strSlot h5 (d := 8) (by decide) fun s6 u6 => ?_
  have h6 := h5.of_mupd u6
  refine ptr_ok h6 (by decide) ht fun s7 p7 r7 m7 h7 => ?_
  refine wp_strSlot h7 (d := 12) (by decide) fun u u8 => ?_
  have k2 : Keep B w [] [0, 4, 8, 12] s1.mem s2.mem := by rw [u2.mem]; exact keep_write _ _ (by simp) (by decide)
  have k4 : Keep B w [] [0, 4, 8, 12] s3.mem s4.mem := by rw [u4.mem]; exact keep_write _ _ (by simp) (by decide)
  have k6 : Keep B w [] [0, 4, 8, 12] s5.mem s6.mem := by rw [u6.mem]; exact keep_write _ _ (by simp) (by decide)
  have k8 : Keep B w [] [0, 4, 8, 12] s7.mem u.mem := by rw [u8.mem]; exact keep_write _ _ (by simp) (by decide)
  have K : Keep B w [] [0, 4, 8, 12] s.mem u.mem := by
    rw [← m1]; refine k2.trans ?_; rw [← m3]; refine k4.trans ?_; rw [← m5]; refine k6.trans ?_
    rw [← m7]; exact k8
  have rd : ∀ (m : Mem) (o : Nat) (v : BitVec 32) (e : Nat), (e + 4 ≤ o ∨ o + 4 ≤ e) ∧ e < 100 ∧ o < 100 →
      (m.writeW (off (State.addr B) o) v).readW (off (State.addr B) e) 32 = m.readW (off (State.addr B) e) 32 :=
    fun m o v e he => Mem.readW_writeW_sep (Offset.sep _ he.1 (by omega) (by omega)) (by decide)
  refine k u (h7.of_mupd u8) K ⟨?_, ?_, ?_, ?_, ?_⟩ ((r1.mono (by simp)).trans ((u2.rest _).trans
    ((r3.mono (by simp)).trans ((u4.rest _).trans ((r5.mono (by simp)).trans ((u6.rest _).trans
      ((r7.mono (by simp)).trans (u8.rest _))))))))
  · rw [u8.mem, rd _ _ _ _ (by decide), m7, u6.mem, rd _ _ _ _ (by decide), m5, u4.mem,
      rd _ _ _ _ (by decide), m3, u2.mem, Mem.readW_writeW_self32, p1]
  · rw [u8.mem, rd _ _ _ _ (by decide), m7, u6.mem, rd _ _ _ _ (by decide), m5, u4.mem,
      Mem.readW_writeW_self32, p3]
  · rw [u8.mem, rd _ _ _ _ (by decide), m7, u6.mem, Mem.readW_writeW_self32, p5]
  · rw [u8.mem, Mem.readW_writeW_self32, p7]
  · rw [u8.mem, rd _ _ _ _ (by decide), m7, u6.mem, rd _ _ _ _ (by decide), m5, u4.mem,
      rd _ _ _ _ (by decide), m3, u2.mem, rd _ _ _ _ (by decide), m1, cnt]

/-- The arrays still zero after the first division. -/
def zeroC : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 23]

/-- After the division of `n` by `p`. -/
structure StC (s0 s : State) : Prop where
  base : Base s0 s
  count : s.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0)
  podd : slot s.mem (cvB s0) sPodd = Spec.Rsa.os2ip (pBytes s0) % 2
  p : num s.mem (cvB s0) (cvW s0) aP = Spec.Rsa.os2ip (pBytes s0)
  q : num s.mem (cvB s0) (cvW s0) aQ = Spec.Rsa.os2ip (qBytes s0)
  d : num s.mem (cvB s0) (cvW s0) aD = Spec.Rsa.os2ip (dBytes s0)
  ddTop : w32 s.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0
  div : 0 < Spec.Rsa.os2ip (pBytes s0) →
    num s.mem (cvB s0) (cvW s0) aDQ = Spec.Rsa.os2ip (nBytes s0) / Spec.Rsa.os2ip (pBytes s0) ∧
    num s.mem (cvB s0) (cvW s0) aDR = Spec.Rsa.os2ip (nBytes s0) % Spec.Rsa.os2ip (pBytes s0)
  zeros : ∀ j ∈ zeroC, val32 s.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) = 0

/-- The word `w` of an array that is zero. -/
theorem top_of_full {m : Mem} {B : BitVec 32} {w j : Nat}
    (h : val32 m (State.addr B) (arr w j) (w + 2) = 0) : w32 m (State.addr B) (arr w j + 4 * w) = 0 := by
  have := val32_zero_part h (a := w) (c := 1) (by omega)
  simpa [val32] using this

theorem num_of_zero {m : Mem} {B : BitVec 32} {w j : Nat}
    (h : val32 m (State.addr B) (arr w j) (w + 2) = 0) : num m B w j = 0 := by
  have := val32_zero_part h (a := 0) (c := w) (by omega)
  simpa using this

/-- The geometry of the division of `n` by `p`. -/
abbrev gN (s0 : State) : VG.Proof.Rsa.Arm.Div.Geometry := divGeom (cvB s0) (cvZ s0) (cvW s0) aDQ aDR aDD aDT

/-- `divN`, then the division, which starts from its context. -/
theorem divN_pre_ok {s0 s : State} (h : StA s0 s) :
    WP isa (seqs divN) s fun u => VG.Proof.Rsa.Arm.Div.Context (gN s0) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (StC s0) := by
  have pre := h.base.pre
  have hw := h.ws
  have fit := fun j (hj : j < nArr) => hw.fit64 (j := j) hj
  unfold divN
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok hw (o := aDD) (a := aP) (by decide) (by decide) (by decide) (by decide))
    fun t1 ⟨h1, k1, e1, r1, top1⟩ => ?_
  have b1 := h.base.keep k1 (by decide) (by simp) (by simp) r1.sp r1.rd r1.wr
  show WP isa (.block (bitOf sPodd aP ++ divHdr aDQ aDR aDD aDT)) t1 _
  refine bitOf_ok h1 (by decide) (by decide) (by decide) fun t2 h2 k2 o2 r2 => ?_
  have b2 := b1.keep k2 (by simp) (by decide) (by decide) r2.sp r2.rd r2.wr
  rw [← List.append_nil (divHdr _ _ _ _)]
  have c2 : t2.mem.readW (off (State.addr (cvB s0)) 16) 32 = BitVec.ofNat 32 (cvW s0) := by
    rw [← h.count]
    refine BitVec.eq_of_toNat_eq ?_
    change slot t2.mem (cvB s0) 16 = slot s.mem (cvB s0) 16
    rw [k2.slot (by decide) (by decide), k1.slot (by decide) (by simp)]
  refine divHdr_ok h2 (by decide) (by decide) (by decide) (by decide) c2 fun t3 h3 k3 d3 r3 => WP.block_nil ?_
  have b3 := b2.keep k3 (by simp) (by decide) (by decide) r3.sp r3.rd r3.wr
  have fDD := fit aDD (by decide)
  have hS : S (cvW s0) = 4 * (cvW s0 + 2) := rfl
  have top3 : w32 t3.mem (State.addr (cvB s0)) (arr (cvW s0) aDD + 4 * cvW s0) = 0 := by
    rw [k3.word (by omega_arith) (by simp) (by decide) fDD, k2.word (by omega_arith) (by simp) (by decide) fDD, top1,
      top_of_full (h.zeros aDD (by decide))]
  refine ⟨divGeom_ctx h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) d3, ?_⟩
  refine WP.mono (div_ok h3 (q := aDQ) (r := aDR) (d := aDD) (t := aDT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3 top3)
    fun t ⟨k, r, v⟩ => ?_
  have bt := b3.keep k (by decide) (by simp) (by simp) r.sp r.rd r.wr
  -- Transport through the four steps.
  have tr : ∀ j, j ≠ aDD → j ≠ aDQ → j ≠ aDR → j ≠ aDT → j < nArr →
      val32 t.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) =
        val32 s.mem (State.addr (cvB s0)) (arr (cvW s0) j) (cvW s0 + 2) := by
    intro j h1 h2 h3 h4 hj
    rw [k.full (by simp; omega_arith) (by simp) (fit j hj), k3.full (by simp) (by decide) (fit j hj),
      k2.full (by simp) (by decide) (fit j hj), k1.full (by simpa using fun e => h1 e.symm) (by simp) (fit j hj)]
  have trn : ∀ j, j ≠ aDD → j ≠ aDQ → j ≠ aDR → j ≠ aDT → j < nArr →
      num t.mem (cvB s0) (cvW s0) j = num s.mem (cvB s0) (cvW s0) j := by
    intro j h1 h2 h3 h4 hj
    rw [k.num (by simp; omega_arith) (by simp) (fit j hj), k3.num (by simp) (by decide) (fit j hj),
      k2.num (by simp) (by decide) (fit j hj), k1.num (by simpa using fun e => h1 e.symm) (by simp) (fit j hj)]
  have p1 : num t1.mem (cvB s0) (cvW s0) aP = Spec.Rsa.os2ip (pBytes s0) := by
    rw [k1.num (by decide) (by simp) (fit _ (by decide)), h.p]
  refine ⟨bt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [← c2]
    refine BitVec.eq_of_toNat_eq ?_
    change slot t.mem (cvB s0) 16 = slot t2.mem (cvB s0) 16
    rw [k.slot (by decide) (by simp), k3.slot (by decide) (by decide)]
  · rw [k.slot (by decide) (by simp), k3.slot (by decide) (by decide), o2, p1]
  · rw [trn _ (by decide) (by decide) (by decide) (by decide) (by decide), h.p]
  · rw [trn _ (by decide) (by decide) (by decide) (by decide) (by decide), h.q]
  · rw [trn _ (by decide) (by decide) (by decide) (by decide) (by decide), h.d]
  · rw [k.word (by omega_arith) (by decide) (by simp) fDD, top3]
  · intro pos
    have dd : num t3.mem (cvB s0) (cvW s0) aDD = Spec.Rsa.os2ip (pBytes s0) := by
      rw [k3.num (by simp) (by decide) fDD, k2.num (by simp) (by decide) fDD, e1, h.p]
    have dq : num t3.mem (cvB s0) (cvW s0) aDQ = Spec.Rsa.os2ip (nBytes s0) := by
      rw [k3.num (by simp) (by decide) (fit _ (by decide)), k2.num (by simp) (by decide) (fit _ (by decide)),
        k1.num (by decide) (by simp) (fit _ (by decide)), h.n]
    obtain ⟨vr, vq⟩ := v (by rw [dd]; exact pos)
    rw [dd, dq] at vr vq
    exact ⟨vq, vr⟩
  · simp only [zeroC, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [tr j (by simp only [aDD]; omega_arith) (by simp only [aDQ]; omega_arith) (by simp only [aDR]; omega_arith)
      (by simp only [aDT]; omega_arith) (by simp only [nArr]; omega_arith)]
    exact h.zeros j (by simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false]; omega_arith)

theorem divN_ok {s0 s : State} (h : StA s0 s) :
    WP isa (.seq (seqs divN) VG.Impl.Rsa.Arm.Div.code) s (StC s0) :=
  WP.seq_iff.mpr (WP.mono (divN_pre_ok h) fun _ h => h.2)

end VG.Proof.Rsa.Arm.CrtValues
