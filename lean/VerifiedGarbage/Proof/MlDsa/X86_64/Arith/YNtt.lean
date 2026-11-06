module
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr

import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.TabFill
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on x86-64: the frame of the NTT and its inverse on AVX2 registers

What the NTT and its inverse on AVX2 registers (`LazyNtt.lean`) share: ML-KEM's
`withMxcsr` runs the code from any MXCSR and keeps what it does
(`ymx_correct`); the prologue leaves the table of zetas in `scratch` and the
constants in both lanes (`ypro_ok`), with which the layers start (`LIY`,
`ynttBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok ifp ifn sel GOnly WP.keep writesOnly
  gprPreserved_of withMxcsr_ok mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq zetas ntt nttInv)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)

/-! ## The prologue and the layers -/

/-- The table of zetas and the constants. -/
theorem ypro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block ypro) s fun s' => Tab zmTab s'.mem sP 256 ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [ypro, WP.block_append_iff]
  refine WP.mono (ytabFill_ok zetaTbl zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1⟩ => WP.mono (yconsts_ok s1) fun s2 ⟨hc, k2, m2, x2, _⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants in both lanes. -/
structure LIY (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-! ## The functions -/

/-- The code in `withMxcsr`, from its state `s1`: the prologue, then the
layers `l`, which leave `G`. -/
theorem ynttBody_ok {t : Poly → Poly} {s s1 : State} (hs : (inPlaceK t).pre s) {l : Prog isa} {G : Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, LIY (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => PolyIs s3.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi)] s2.mem s3.mem) :
    WP isa (.seq (.block ypro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (ypro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 ⟨hP, hf3⟩ => ⟨hP, ?_⟩
  refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans (frame_fs hf3 ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- `withMxcsr` around the body, and the ABI. -/
theorem ymx_correct {t : Poly → Poly} {l : Prog isa} (s : State) (hs : (inPlaceK t).pre s)
    (hk : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9]) (.seq (.block ypro) l) = true)
    (hctl : ctlOk (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) = true)
    (hk' : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r11])
      (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block ypro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (VG.Impl.MlKem.X86_64.withMxcsr .rsi 768 (.seq (.block ypro) l)) s tr s' ∧
      abiPreserved s s' ∧ (inPlaceK t).post s s' := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := withMxcsr_ok (c := .seq (.block ypro) l) (by decide) [.rax, .rcx, .rdx, .r8, .r9] (by decide) rfl hw
    (writesOnly_of hk) (hl)
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (writesOnly_of hk')
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _)) hP

end VG.Proof.MlDsa.X86_64.Arith
