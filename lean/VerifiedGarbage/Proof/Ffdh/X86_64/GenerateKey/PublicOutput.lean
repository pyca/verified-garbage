module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ArithmeticBridge
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH on x86-64: range-check and encode a generated public key -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

abbrev GkP.z (p : GkP) (rb : List Byte) : Nat := p.kp.z (p.xb rb)
abbrev GkP.fl (p : GkP) (rb : List Byte) : Prop := p.kp.fl (p.xb rb)

def PublicPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (if p.fl rb then p.z rb else 0) p.k ∧
    t.gpr .rax = bit (p.fl rb) ∧ t.gpr .rdi = p.B ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ Scr t p.B p.Z ∧
    word t.mem p.B (8 * sX) = off p.xp p.ld ∧ word t.mem p.B (8 * sXl) = BitVec.ofNat 64 p.n ∧
    word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem publicOutput_ok {p : GkP} {rb : List Byte} {s : State}
    (h : CheckPrivate.Value p.kp (p.xb rb) s) (hx : Src s p.B p.Z p.xp (p.cut rb))
    (ho : OutOk s p.B p.Z p.yp p.k) (ha : Apart p.xp p.k p.yp p.k)
    (hxl : (p.cut rb).length = p.k) :
    WP isa (seqs publicOutput) s (PublicPost p rb s) := by
  unfold publicOutput
  refine wp_seqs_cons (by simp [range])
    (WP.mono (value_bridge h ho) fun u ⟨hu, hi₁, hs₁, k₁⟩ => ?_)
  have hxu := hx.congrK hi₁ k₁
  refine wp_seqs_append (a := range aY) (by simp [range]) (by simp)
    (WP.mono (Exchange.value_checked hu) fun v ⟨hv, hi₂, hs₂, k₂⟩ => ?_)
  have hxv := hxu.congrK hi₂ k₂
  have hv' := hv
  obtain ⟨⟨mi, hb, hc⟩, _, _, _⟩ := hv
  refine WP.mono (Exchange.output_ok hv') fun t ⟨hy, hflag, hd, hf, hs₃, k₃⟩ => ?_
  have hhf : Outside p.B p.Z (2 ^ 64 - p.Z) v.mem t.mem := by
    intro a hh
    have ha64 : ofs p.B a < 2 ^ 64 := (a - p.B).isLt
    apply hf
    intro i hi he
    change a = p.yp + BitVec.ofNat 64 i at he
    have hsep : p.Z ≤ ofs p.B (p.yp + BitVec.ofNat 64 i) := hb.sep i hi
    rw [← he] at hsep
    omega
  have hh : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word v.mem p.B d :=
    fun d hd => hhf.word (Or.inl hd) (by have hn : p.B.toNat + p.Z ≤ 2 ^ 64 := hb.scr.nowrap; omega)
  have hxt : Src t p.B p.Z p.xp (p.cut rb) := by
    refine ⟨fun i hi => by rw [k₃.2.1, k₃.2.2]; exact hxv.rd i hi, ?_, hxv.out⟩
    intro i hi
    rw [hf _ (fun j hj => ha i (by rwa [hxl] at hi) j hj)]
    exact hxv.val i hi
  have hZ : 128 * p.k + 256 ≤ p.Z := hb.hZ
  have hs₁' : ∀ i < 6, word u.mem p.B (8 * i) = word s.mem p.B (8 * i) := hs₁
  have hs₂' : ∀ i < 6, word v.mem p.B (8 * i) = word u.mem p.B (8 * i) := hs₂
  have hs₃' : ∀ i < 6, word t.mem p.B (8 * i) = word v.mem p.B (8 * i) := hs₃
  refine ⟨hy, hflag, hd, hxt, hb.scr.congr k₃.2.2, ?_, ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [hh _ (by change 168 ≤ p.Z; omega)]
    exact hb.hdr (sX, off p.xp p.ld) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · rw [hh _ (by change 176 ≤ p.Z; omega)]
    exact hb.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · rw [hh _ (by change 152 ≤ p.Z; omega)]
    exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [Exchange.ExP.headers, outputP, GkP.kp])
  · intro i hi
    rw [hs₃' i hi, hs₂' i hi, hs₁' i hi]
  · exact (RunFrame.of_scr hi₁).trans ((RunFrame.of_scr hi₂).trans (RunFrame.of_y hf))

end VG.Proof.Ffdh.X86_64.GenerateKey
