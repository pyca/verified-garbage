module

public import VerifiedGarbage.Proof.Rsa.X86.RvInputs
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Bignum.X86.ExportTruncated
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # Masked recovery output preserves the workspace header and other arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (kw sel_ok arrPtr_ok lenSrc)

theorem output_word {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') {d : Nat} (bound : d + 4 ≤ g.Z) :
    w32 m' g.B d = w32 m g.B d := by
  unfold w32
  rw [f.readW (r := ⟨g.B, g.Z⟩) (a := off g.B d) (w := 32)
    (Scr.contains h.ws.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (h.outputScratch i).symm) (by decide)]

theorem output_num {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') {j : Nat} (hj : j < nArr) :
    num m' g.B g.toGeo.w j = num m g.B g.toGeo.w j := by
  apply val32_congr
  intro k hk
  have fits := h.ws.arr_fit hj
  unfold S at fits
  exact output_word h i f (by omega)

theorem store_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Fin 2) {j : Nat}
    (hj : j < nArr) (hjz : j ≠ aZero) (zero : num s.mem g.B g.toGeo.w aZero = 0) (accept : Bool)
    (mask : slot s.mem g.B sMask = if accept then 1 else 0) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.store (2 * i.val) j) s fun t =>
      Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        Spec.Rsa.i2osp ((if accept then num s.mem g.B g.toGeo.w j else 0) %
          2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len ∧
      Frame [⟨off g.B (arr g.toGeo.w j), S g.toGeo.w⟩, g.buffer (2 * i.val)] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem g.B d = slot s.mem g.B d) ∧
      (∀ k, k < nArr → k ≠ j → num t.mem g.B g.toGeo.w k = num s.mem g.B g.toGeo.w k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := h.rt len
  have kn : kw (8 * g.n + 8) = g.toGeo.w := kw_nar g.n
  have fits := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  have fit64 := h.ws.fit64 hj
  have up := h.upper
  have hi := i.isLt
  unfold VG.Impl.Rsa.X86.RecoverRt.store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok r hj (by decide) hj (by decide) (by rw [mask]; cases accept <;> decide) (.inl hjz))
    fun u ⟨ru, ku, vu, rku⟩ => ?_
  rw [kn] at ku vu
  have outside := h.keepBody ku (by simpa using hj) (by simp)
  have frameU := h.scratchFrame outside
  have inputsU := h.after rku (by decide) (by decide) frameU
  have raw : Outside g.B (arr g.toGeo.w j) (S g.toGeo.w) s.mem u.mem := by
    intro a ha
    apply ku a
    intro r hr
    simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hr
    subst r
    exact ha
  have ownFrame := outside_frame raw fit64
  have chosen : num u.mem g.B g.toGeo.w j = if accept then num s.mem g.B g.toGeo.w j else 0 := by
    rw [vu, mask, zero]; cases accept <;> rfl
  have positive := h.outputPositive i
  have bound := h.outputBound i
  have outFit := h.outputFit i
  have outWrite := h.outputWrite i
  have outScratch := h.outputScratch i
  simp only [CallGeometry.buffer] at positive bound outFit outWrite outScratch ⊢
  generalize hL : (g.args (2 * i.val + 1)).toNat = L at positive bound outFit outWrite outScratch ⊢
  have Lw : L ≤ 4 * g.toGeo.w := by simp only [Geo.w, VG.Impl.Rsa.X86.Recover.width]; omega
  simp only [S] at fits
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (inputsU.arguments (2 * i.val) (by omega)).readSrc fun u₁ U₁ _ => ?_
  have h₁ := inputsU.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (2 * i.val + 1) (by omega)).readSrc fun u₂ U₂ _ => ?_
  have K₂ : Keeps [.ebx, .ecx] u u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have m₂ : u₂.mem = u.mem := by rw [U₂.mem, U₁.mem]
  have r₂ := ru.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by rw [kn]; omega)
    fun v Kv mv pv _ => ?_
  rw [kn] at pv
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  have srcAddr : byteAddr (v.gpr .esi) = off g.B (arr g.toGeo.w j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega)
  have K₄ : Keeps [.ebx, .ecx, .edx, .esi] u v₄ :=
    ((K₂.mono (by decide)).trans (Kv.mono (by decide))).trans ((u₃.keeps.mono (by decide)).trans
      (u₄.keeps.mono (by decide)))
  have m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  have ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have ebx₄ : v₄.gpr .ebx = g.args (2 * i.val) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
  have esi₄ : v₄.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (L - 1) := by
    have ecx : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
  have keepU : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ := (rku.mono (by decide)).trans (K₄.mono (by decide))
  have hsub : Region.Sub ⟨off g.B (arr g.toGeo.w j), L⟩ ⟨g.B, g.Z⟩ := by
    have := Offset.sub g.B (d := arr g.toGeo.w j) (n := L) (e := 0) (k := g.Z) (Nat.zero_le _)
      (by omega)
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.mono (reverseBuffer_ok v₄ (src := v.gpr .esi) (dst := g.args (2 * i.val)) (n := L) (by omega)
    (by omega) outFit (by omega)
    (by rw [keepU.2.1, keepU.2.2, srcAddr]; exact h.ws.workspace.read (by omega))
    (by rw [keepU.2.2]; exact outWrite) (by rw [srcAddr]; exact outScratch.symm.sub_left hsub) ebx₄ esi₄ ecx₄)
    fun t ⟨V, F, _, T⟩ => ?_
  have F' : Frame [⟨byteAddr (g.args (2 * i.val)), L⟩] u.mem t.mem := by rw [← m₄]; exact F
  have all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keepU.trans (T.mono (by decide))
  have Fb : Frame [g.buffer (2 * i.val)] u.mem t.mem := by simpa [CallGeometry.buffer, hL] using F'
  have fullFrame : Frame g.writes s.mem t.mem :=
    frameU.trans (Fb.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      have cases : i.val = 0 ∨ i.val = 1 := by omega
      rcases cases with e | e <;> simp [CallGeometry.writes, e]))
  refine ⟨h.after all (by decide) (by decide) fullFrame, ?_, ?_, ?_, ?_, all⟩
  · rw [V, srcAddr, m₄, ← chosen]
    have eq : (u.mem.read (off g.B (arr g.toGeo.w j)) (4 * g.toGeo.w)).toNat =
        num u.mem g.B g.toGeo.w j := read_eq_val32 _ _ _ _
    rw [read_prefix u.mem _ (Lw), BitVec.toNat_setWidth, eq]
  · exact (ownFrame.mono (by simp)).trans (F'.mono (by simp))
  · intro d hd
    change w32 t.mem g.B d = w32 s.mem g.B d
    rw [output_word h i Fb (by have := h.ws.hdr_le; omega)]
    exact ku.slot hd (by simp)
  · intro k hk ne
    rw [output_num h i Fb hk]
    exact ku.num (by simpa using Ne.symm ne) (by simp) (h.ws.fit64 hk)
end VG.Proof.Rsa.X86.Recover
