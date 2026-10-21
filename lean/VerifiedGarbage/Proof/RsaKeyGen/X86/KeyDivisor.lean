module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyCrt
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.Rsa.X86.KeyEq
import VerifiedGarbage.Proof.Rsa.X86.KeySelect

/-! # A safe CRT divisor, including zero factor predecessors -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem divisorOf_ok {s : State} {B : Addr} {Z n input : Nat} (h : Ws s B Z n 32)
    (hi : input < 32) (ip : 16 ≤ input) (one : num s.mem B n aOne = 1) :
    WP isa (divisorOf n input) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, aDen] [sT, kFlag] s.mem t.mem ∧
      num t.mem B n aDen = (if num s.mem B n input = 0 then 1 else num s.mem B n input) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fi := h.fit64 hi
  have fo := h.fit64 (j := aOne) (by decide)
  unfold divisorOf seqs
  refine WP.seq (WP.mono (constArray_ok h (by decide) (Nat.two_pow_pos _))
    fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  have Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; unfold aT1; omega) (by simp) fi
  have oneU : num u.mem B n aOne = 1 :=
    (Ou.num (by decide) (by simp) fo).trans one
  refine WP.seq (WP.mono (eqS_ok hu (by decide) hi (by decide)
    (by unfold aT2; omega) (by decide) (by decide)) fun v ⟨hv, Ov, flag, Kv⟩ => ?_)
  rw [Iu, zero] at flag
  have Iv : num v.mem B n input = num s.mem B n input :=
    (Ov.num (by simp only [List.mem_singleton]; unfold aT2; omega) (by decide) fi).trans Iu
  have oneV : num v.mem B n aOne = 1 :=
    (Ov.num (by decide) (by decide) fo).trans oneU
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (sel_ok hv (by decide) hi (by decide) (by decide) bit)
    fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (Ou.join Ov (js := [aT1, aT2, aDen]) (ds := [sT, kFlag])).join Ot
    (js := [aT1, aT2, aDen]) (ds := [sT, kFlag]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  rw [selected, flag, Iv, oneV]
  by_cases I : num s.mem B n input = 0 <;> simp [I]

end VG.Proof.RsaKeyGen.X86.Key
