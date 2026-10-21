module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Common parity at a public runtime width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (aU aV kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem bothEven_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block bothEven) s fun t => Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag =
        (if num s.mem B n aU % 2 = 0 ∧ num s.mem B n aV % 2 = 0 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have fu := h.arr_fit (j := aU) (by decide)
  have fv := h.arr_fit (j := aV) (by decide)
  have nowrap := h.old.workspace.nowrap
  unfold bothEven
  refine h.ptr_ok (arr aU) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega)
    fun u Ku mu Pu => ?_
  have hu := h.keep Ku (by rw [mu]; exact Outside.refl _ _ _ _)
  refine wp_movS (VG.Proof.Mont.X86.Rt.readSrc_ptr hu.full.rt Pu (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fu; omega))
    fun v V _ => ?_
  have Kv : Keeps [.eax, .ecx, .edx] s v := (Ku.mono (by decide)).trans (V.keeps.mono (by decide))
  have mv : v.mem = s.mem := V.mem.trans mu
  have hv := h.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.ptr_ok (arr aV) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega)
    fun w Kw mw Pw => ?_
  have hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine wp_orS (VG.Proof.Mont.X86.Rt.readSrc_ptr hw.full.rt Pw (d := 0)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fv; omega))
    fun x X => ?_
  refine wp_logicS (.inl rfl) rfl fun y Y => wp_logicS (.inr rfl) rfl fun z Zf => ?_
  have K : Keeps [.eax, .ecx, .edx] s z := (Kv.trans (Kw.mono (by decide))).trans
    ((X.keeps.mono (by decide)).trans ((Y.keeps.mono (by decide)).trans (Zf.keeps.mono (by decide))))
  have memory : z.mem = s.mem := Zf.mem.trans (Y.mem.trans (X.mem.trans (mw.trans mv)))
  have hz := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have value : z.gpr .ecx =
      ((s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aU)) 32 |||
        s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n aV)) 32) &&& (1 : BitVec 32)) ^^^ 1 := by
    rw [Zf.gpr, Y.gpr, X.gpr, Kw.1 _ (by decide), V.gpr, mw, V.mem, mu,
      Nat.add_zero, arr, offset_array, Width.words, arr, offset_array, Width.words]
    rfl
  refine WP.mono (store_slot hz (d := kFlag) (by decide) .ecx) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, value, VG.Proof.RsaKeyGen.X86.Key.even_bit,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aU,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity _ _ h.wpos aV]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
