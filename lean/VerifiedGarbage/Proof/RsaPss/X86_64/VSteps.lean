module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VShape
import VerifiedGarbage.Proof.RsaOaep.X86_64.DecLoops
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: the pieces of `verifyMain`, for two runs

What each piece of `verifyMain` leaves of `VS`, the frame's shape: the
arguments of the public operation (`vpubArgs_step`), the call
(`vcall_step`), the accumulator and MGF1's slots (`vacc_step`), MGF1
(`vmgf_step`), the scan (`vscan_step`), the hash calls and their arguments
(`vinit_step`, `vupd_step`, `vfin_step`, …) and the copies and blocks of the
salt's hash.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sHD sCtr oEm oSt oDig oLh oBuf oW oRsa scr lay)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor initF updF finF)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub Lay Rep upd nW inR inR_cons inR_nil regs
  retR Good wp_good block_good keep_cs3 cs_disj lenOf tw Here Fns initF_ok updF_ok finF_ok sizes scr_ok
  mW mW_args mW_other StepW)
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashFns (StreamingOK)

variable {s : State}

/-- A piece that keeps the frame's words, from `VS P`. -/
theorem VS.keepW {P : State → (Nat → BitVec 64) → Prop} {t t' : State} (h : VS P s t)
    (he' : VEnv s t') (L' : Lay t' (fb s) (stackArg s 4))
    (hR : ∀ V W, Rep t.mem (fb s) (stackArg s 4) V W → ∃ V', Rep t'.mem (fb s) (stackArg s 4) V' W) :
    VS P s t' := by
  obtain ⟨-, -, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  obtain ⟨V', R'⟩ := hR V W R
  exact ⟨he', L', ⟨V', W, R', hA, h33, h44, hP⟩, hf⟩

/-- A piece that only touches registers. -/
theorem VS.regs {P : State → (Nat → BitVec 64) → Prop} {t t' : State} (h : VS P s t) {rs : List Reg}
    (hk : Keep rs t t') (hm : t'.mem = t.mem) (hrs : rs.all (fun r => !calleeSaved.contains r) = true)
    (hsp : Reg.rsp ∉ rs) (hmx : t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10)
    (hf : StepW (t.wr ++ [below (t.gpr .rsp) 16]) t t') : VS P s t' :=
  h.keepW (h.1.step hk.2.1 hk.2.2 (hk.gpr hsp) (keep_cs3 hk hrs) hmx hf)
    (h.2.1.congr (hk.gpr hsp) hk.2.2 (by rw [hm])) fun V W R => ⟨V, hm ▸ R⟩

/-! ## The hash calls -/

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh)

include hT in
theorem vinit_step {P : State → (Nat → BitVec 64) → Prop} {j : Nat}
    {i : Nat} (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) (fF : VFns s T i)
    {t : State} (h : VS P s t) (hdi : t.gpr .rdi = off (stackArg s 4) oSt) :
    WP isa (initF (8 * j)) t (VS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  have hfn : W j = tw s.mem (stackArg s i) 0 := by
    rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hA.sel.2.2.1.1
    · exact hA.sel.2.2.2.1
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.initF_good _) (initF_ok hT fF he.here L R (j := j) rfl
    (by rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hfn hdi))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

include hT in
theorem vupd_step {P : State → (Nat → BitVec 64) → Prop} {j : Nat}
    {i : Nat} (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) (fF : VFns s T i)
    {t : State} (h : VS P s t) {a len : Nat} (ha : a + len ≤ oRsa) (hda : a + len ≤ oSt ∨ oSt + T.S.stateBytes ≤ a)
    (hwa : a + len ≤ oW ∨ oW + 8 * T.scratch ≤ a)
    (hdi : t.gpr .rdi = off (stackArg s 4) oSt) (hdx : t.gpr .rdx = off (stackArg s 4) a)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 len) (h8 : t.gpr .r8 = off (stackArg s 4) oW) :
    WP isa (updF (8 * j)) t (VS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  have hfn : W (j + 1) = tw s.mem (stackArg s i) 1 := by
    rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hA.sel.2.2.1.2.1
    · exact hA.sel.2.2.2.2.1
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.updF_good _) (updF_ok hT fF he.here L R (j := j) rfl
    (by rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hfn ha hda hwa hdi hdx hcx h8))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

include hT in
theorem vfin_step {P : State → (Nat → BitVec 64) → Prop} {j : Nat}
    {i : Nat} (hji : (j = 45 ∧ i = 10) ∨ (j = 48 ∧ i = 11)) (fF : VFns s T i)
    {t : State} (h : VS P s t) {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (hdi : t.gpr .rdi = off (stackArg s 4) oSt) (hdx : t.gpr .rdx = off (stackArg s 4) o)
    (hcx : t.gpr .rcx = off (stackArg s 4) oW) :
    WP isa (finF (8 * j)) t (VS P s) := by
  obtain ⟨he, L, ⟨V, W, R, hA, h33, h44, hP⟩, hf⟩ := h
  have hfn : W (j + 2) = tw s.mem (stackArg s i) 2 := by
    rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hA.sel.2.2.1.2.2
    · exact hA.sel.2.2.2.2.2
  refine WP.mono (wp_good (VG.Proof.RsaOaep.X86_64.finF_good _) (finF_ok hT fF he.here L R (j := j) rfl
    (by rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hfn ho hdi hdx hcx))
    fun t' ⟨⟨L', rd', wr', cs', R', _, _⟩, sp', mx', f'⟩ =>
      ⟨he.step rd' wr' sp' (fun r hr _ => cs' r hr) mx' f', L', ⟨_, W, R', hA, h33, h44, hP⟩, hf⟩

end VG.Proof.RsaPss.X86_64
