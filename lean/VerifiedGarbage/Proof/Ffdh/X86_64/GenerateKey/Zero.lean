module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
import VerifiedGarbage.Proof.Rsa.X86_64.CvFail
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH key generation on x86-64: initialize the public output -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- The initial public output is zero, and readable by the shared private-key core. -/
theorem zero_ok {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) (hd : s.gpr .rdi = p.B) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK) s fun t =>
      Base p rb t ∧ Src t p.B p.Z p.yp (List.replicate p.k 0) ∧
      (∀ a, (∀ i < p.k, a ≠ off p.yp i) → t.mem a = s.mem a) ∧
      (∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d) ∧
      Keep [.rsi, .rcx, .rax] s t := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  refine WP.mono (zeroOut_ok h.scr hd (by omega) (by decide) (by decide)
    (h.hdr (sY, p.yp) (by simp [GkP.headers]))
    (h.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])) (by omega) (by omega) h.y)
    fun t ⟨hz, hf, k⟩ => ?_
  have hout : Outside p.B p.Z (2 ^ 64 - p.Z) s.mem t.mem := by
    intro a ha
    have ha64 : ofs p.B a < 2 ^ 64 := (a - p.B).isLt
    apply hf
    intro i hi he
    have := h.y.sep i hi
    rw [← he] at this
    omega
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d :=
    fun d hd => hout.word (Or.inl hd) (by have := h.scr.nowrap; omega)
  have hdom : Src t p.B p.Z p.dp p.dom := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.dom.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yd j hj i (by rw [← h.doml]; exact hi)))]; exact h.dom.val i hi,
    h.dom.out⟩
  have hrand : Src t p.B p.Z p.rp rb := ⟨fun i hi => by rw [k.2.1, k.2.2]; exact h.rand.rd i hi,
    fun i hi => by rw [hf _ (fun j hj => Ne.symm (h.yr j hj i (by rw [← h.rl]; exact hi)))]; exact h.rand.val i hi,
    h.rand.out⟩
  refine ⟨⟨h.k1, h.k2, h.dl, h.doml, h.rl, h.hZ, h.scr.congr k.2.2, hdom, hrand,
    ⟨fun i hi => by rw [k.2.2]; exact h.x.wr i hi, h.x.sep⟩,
    ⟨fun i hi => by rw [k.2.2]; exact h.y.wr i hi, h.y.sep⟩,
    h.xy, h.xd, h.xr, h.yd, h.yr, ?_, h.valid⟩, ?_, hf, hh, k⟩
  · intro e he
    rw [hh _ (by
      simp only [GkP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [sDom, sDomLen, sK, sY, sX, sRand, sFn] <;> omega)]
    exact h.hdr e he
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.k := by simpa only [List.length_replicate] using hi
      obtain ⟨r, hr, hc⟩ := h.y.wr i hi'
      exact ⟨r, List.mem_append_right _ (by rw [k.2.2]; exact hr), hc⟩
    · intro i hi
      rw [hz i (by simpa only [List.length_replicate] using hi)]
      exact (List.getElem_replicate hi).symm
    · intro i hi
      exact h.y.sep i (by simpa only [List.length_replicate] using hi)

end VG.Proof.Ffdh.X86_64.GenerateKey
