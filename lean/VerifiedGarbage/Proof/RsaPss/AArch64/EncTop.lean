module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCorrect
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.RsaPss.AArch64.Restore
import VerifiedGarbage.Proof.RsaPss.EncodeEq
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-!
# EMSA-PSS's encoding on AArch64: the whole function

`code_ok`: from the precondition, `encode` keeps the calling convention and
returns 1 with `em` holding `Spec.RsaPss.encode`'s encoding, or 0 if the
salt does not fit (`Post`): the prologue (`prologue_ok`), the checks of the
lengths (`body_ok`), and the restores (`restore_frame_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (fitH_ok saltFits_ok restore_frame_ok)
open VG.Proof.RsaPss.AArch64.Sgn (fb stk)

/-- The result, and the calling convention. -/
def Post (D : Nat) (Hs Gs : Spec.Mgf1.Hash) (s s' : State) : Prop :=
  abiPreserved s s' ∧ OutOk D Hs Gs s s'.mem (s'.gpr .x0)

section
variable {H : Hash} (hH : HashOK H) {Gm : Impl.Pbkdf2.Md.AArch64.Stream}
  (hGm : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK Gm) {Hs Gs : Spec.Mgf1.Hash}
  (hHs : ∀ x, Hs.hash x = hH.SH.H.hash x) (hHl : Hs.len = H.D) (hHv : Proof.Mgf1.Valid Hs)
  (hGh : ∀ x, Gs.hash x = hGm.SH.H.hash x) (hGl : Gs.len = Gm.D)
  (hGv : Proof.Mgf1.Valid Gs) {f : MdFns} {dn : String} (hdo : DigOK H.P) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns}

include hH hHs hHl hHv hGh hGl hGv hdo in
/-- After the prologue and `fitH`: the checks of the lengths, then the
encoding or 0. -/
theorem body_ok {tsH tsG : List FnTable} {s u : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) (hu : AtT s u)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 (s.gpr .x1).toNat)
    (h10 : (u.gpr .x10 != 0) = decide ((s.gpr .x1).toNat < H.D + 2)) :
    WP isa (.ite (.nonzero .x .x10) ret0 (seqs [.block ([ld .x12 sSaltLen] ++ saltFits H),
      .ite (.nonzero .x .x10) ret0 (encMain f H g)])) u fun t => MidE s t ∧ OutOk H.D Hs Gs s t.mem (t.gpr .x0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hsl : (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).length = (s.gpr .x4).toNat :=
    VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _
  have hel := hp.hel
  refine WP.ite _ (eval_nonzero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [h10, decide_eq_true_eq] at hb
    exact ret0_ok hu.e (RsaPss.encode_none₂ Hs Gs (by rw [hsl, ← hel, hHl]; omega))
  rw [h10, decide_eq_false_iff_not] at hb
  unfold seqs seqs
  refine WP.seq (WP.mono_syms (saltFits_ok H hD (F := fb s) hu.e.sp
    (by rw [hu.e.rd, hu.e.wr]; exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ (by decide) (by decide))))
    (a := (s.gpr .x1).toNat) (sl := (s.gpr .x4).toNat) (by omega) (by omega) h9
    (by rw [hu.e.fr.rs (.x4, sSaltLen) (by simp [encSlots]), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (s.gpr .x4).isLt) fun u₃ ⟨O₃, x9₃, x10₃⟩ sy₃ => ?_)
  have hu₃ := hu.only O₃ sy₃
  refine WP.ite _ (eval_nonzero _ _) (fun hb₃ => ?_) (fun hb₃ => ?_)
  · rw [x10₃, decide_eq_true_eq] at hb₃
    exact ret0_ok hu₃.e (RsaPss.encode_none₂ Hs Gs (by rw [hsl, ← hel, hHl]; omega))
  rw [x10₃, decide_eq_false_iff_not] at hb₃
  exact encMain_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht hu₃ x9₃ (by omega)

include hH hHs hHl hHv hGh hGl hGv hdo in
theorem code_ok {tsH tsG : List FnTable} {s : State} (hp : PreE H.D tsH tsG s)
    (ht : TabsAt H dn f Gm g (stackArg s 0) (stackArg s 1) s) : WP isa (encode f H g) s (Post H.D Hs Gs s) := by
  have hD : H.D + 2 < 4096 := by have := hH.sizes.DN; have := hH.N_le; omega
  have hk2 := hp.k2
  unfold encode
  refine WP.alloc (by decide) (by have := fb_toNat hp; omega) ?_
  unfold encBody seqs seqs seqs
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono_syms (prologue_ok hp (by simp [allocated]) (by simp [allocated]) (by simp [allocated])
    (by simp [allocated]) (fun r => by simp [allocated]) (fun r _ => by simp [allocated])) fun u hu sy => ?_
  refine WP.mono (tabSlots_ok hp hu (by rw [sy]; simp [allocated])) fun u₀ hu₀ => ?_
  refine WP.mono_syms (fitH_ok H hD (k := (s.gpr .x1).toNat)
    (by rw [hu₀.e.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by omega)) fun u₁ ⟨O₁, x9₁, x10₁⟩ sy₁ => ?_
  refine WP.seq (WP.mono (body_ok hH hGm hHs hHl hHv hGh hGl hGv hdo hp ht (hu₀.only O₁ sy₁) x9₁ x10₁)
    fun t ⟨m, r⟩ => ?_)
  exact WP.mono (restore_frame_ok m.sp m.wr m.v m.fr.sv) fun w ⟨habi, hx0, hmem⟩ =>
    ⟨habi, by rw [hx0, hmem]; exact r⟩

end

end VG.Proof.RsaPss.AArch64.Enc
