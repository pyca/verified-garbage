module
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Rsa.X86.CvFrames
import VerifiedGarbage.Proof.Bignum.X86.ExportTruncated
import VerifiedGarbage.Proof.Rsa.X86.CvLoad
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Masked CRT output preserves the workspace header and other arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem output_word {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 3)
    (f : Frame [g.buffer (2 * i.val)] m m') {d : Nat} (bound : d + 4 ≤ g.size) :
    w32 m' g.base d = w32 m g.base d := by
  unfold w32
  rw [f.readW (r := ⟨g.base, g.size⟩) (a := off g.base d) (w := 32)
    (Scr.contains h.ws.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (h.outputScratch i).symm) (by decide)]

theorem output_num {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 3)
    (f : Frame [g.buffer (2 * i.val)] m m') {j : Nat} (hj : j < nArr) :
    num m' g.base (2 * g.n) j = num m g.base (2 * g.n) j := by
  apply val32_congr
  intro k hk
  have fits := h.ws.arr_fit hj
  unfold S at fits
  exact output_word h i f (by omega)

theorem store_ok {g : CallGeometry} {s : State} (h : Inputs g s) (i : Fin 3) {j : Nat}
    (hj : j < nArr) (zero : num s.mem g.base (2 * g.n) aZero = 0) (accept : Bool)
    (mask : slot s.mem g.base sMask = if accept then 1 else 0) :
    WP isa (store g.n (2 * i.val) j) s fun t =>
      Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        Spec.Rsa.i2osp ((if accept then num s.mem g.base (2 * g.n) j else 0) %
          2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len ∧
      Frame [⟨off g.base (arr (2 * g.n) j), S (2 * g.n)⟩, g.buffer (2 * i.val)] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem g.base d = slot s.mem g.base d) ∧
      (∀ k, k < nArr → k ≠ j → num t.mem g.base (2 * g.n) k = num s.mem g.base (2 * g.n) k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have fits := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  have fit64 := h.ws.fit64 hj
  unfold store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h.ws hj (by decide) hj (by decide) (by rw [mask]; cases accept <;> decide))
    fun u ⟨hu, ku, vu, ru⟩ => ?_
  have outside := h.keepOutside ku (by simp_all) (by simp)
  have frameU := h.scratchFrame outside
  have inputsU := h.after ru (by decide) (by decide) frameU
  have raw : Outside g.base (arr (2 * g.n) j) (S (2 * g.n)) s.mem u.mem := by
    intro a ha
    apply ku a
    intro r hr
    simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hr
    subst r
    exact ha
  have ownFrame := outside_frame raw fit64
  have chosen : num u.mem g.base (2 * g.n) j = if accept then num s.mem g.base (2 * g.n) j else 0 := by
    rw [vu, mask, zero]; cases accept <;> rfl
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (argumentPair_ok (d := .ebx) (by decide) (by decide)
    ((inputsU.arguments _ (by omega)).readSrc) ((inputsU.arguments _ (by omega)).readSrc)) ?_
  rintro v ⟨P, C, M, K⟩
  have positive := h.outputPositive i
  have bound := h.outputBound i
  simp only [S] at fits
  change WP isa (VG.Impl.Bignum.X86.storeBE (arr (2 * g.n) j)) v _
  refine WP.mono (storeBE_truncated_ok (hu.workspace.of_keeps K (by decide)) positive
    (w := 2 * g.n) (by omega) (by omega) (by rw [C]; simp [CallGeometry.buffer])
    (by rw [P]; exact h.outputFit i)
    (by rw [P, K.2.2, ru.2.2]; exact h.outputWrite i)
    (by rw [P]; exact (h.outputScratch i).symm.sub_left (Offset.sub_base g.base (by omega)))) ?_
  rintro t ⟨value, frame, rest⟩
  rw [P, M] at value frame
  have F : Frame [g.buffer (2 * i.val)] u.mem t.mem := frame
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    (ru.mono (by decide)).trans ((K.mono (by decide)).trans (rest.mono (by decide)))
  have fullFrame : Frame g.writes s.mem t.mem :=
    frameU.trans (F.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
      rcases cases with e | e | e <;> simp [CallGeometry.writes, e]))
  refine ⟨h.after all (by decide) (by decide) fullFrame, ?_, ?_, ?_, ?_, all⟩
  · change Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
      Spec.Rsa.i2osp (num u.mem g.base (2 * g.n) j % 2 ^ (8 * (g.buffer (2 * i.val)).len))
        (g.buffer (2 * i.val)).len at value
    change num u.mem g.base (2 * g.n) j = _ at chosen
    rw [chosen] at value
    exact value
  · exact (ownFrame.mono (by simp)).trans (F.mono (by simp))
  · intro d hd
    change w32 t.mem g.base d = w32 s.mem g.base d
    rw [output_word h i F (by have := h.ws.hdr_le; omega)]
    exact ku.slot hd (by simp)
  · intro k hk ne
    rw [output_num h i F hk]
    exact ku.num (by simpa using Ne.symm ne) (by simp) (h.ws.fit64 hk)
end VG.Proof.Rsa.X86.CrtValues
