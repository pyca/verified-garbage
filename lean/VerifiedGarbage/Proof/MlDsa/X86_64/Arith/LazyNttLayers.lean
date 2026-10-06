import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith hiding bfly blockN layF
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep sel)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (zetas)

theorem lane_lazyBfly : laneSseBlock (toY lazyBfly) = some lazyBfly := by decide +kernel
theorem lane_core2f : laneSseBlock (toY (gath2 ++ lazyBfly ++ scat2)) = some (gath2 ++ lazyBfly ++ scat2) := by
  decide +kernel
theorem lane_core1f : laneSseBlock (toY (gath1 ++ lazyBfly ++ scat1)) = some (gath1 ++ lazyBfly ++ scat1) := by
  decide +kernel

structure LIY (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LIY.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, YConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInvY fP s s')
    (hc : ∀ s, LIY fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LIY fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem yfwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 128 / len = k) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay lazyBfly len k 4) s fun s' => PolyIs s'.mem fP (layer F len) ∧ BInvY fP s s' := by
  rw [layer]
  exact ylay_ok bfly_ok lane_lazyBfly (block_ok op) hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl <;> omega)
    (fun c _ => step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 lazyBfly 32 0x00 0x55 8) s fun s' => PolyIs s'.mem fP (layer F 4) ∧ BInvY fP s s' := by
  have h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  have h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [layer, show 128 / 4 = 32 from rfl]
  exact ylay4_ok bfly_ok lane_lazyBfly (block_ok op) 32 0x00 0x55 8 (fun c => 32 + c) (fun m => 32 + 2 * m) rfl
    (fun m _ => by omega) (fun m _ e he => ⟨by rw [h0 e he]; omega, by rw [h5 e he]; omega⟩)
    (fun m _ => (step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 lazyBfly 64 0xA0 0xF5 16) s fun s' => PolyIs s'.mem fP (layer F 2) ∧ BInvY fP s s' := by
  have hA : ∀ e < 4, sel 0xA0 e = 2 * (e / 2) := by decide
  have hF : ∀ e < 4, sel 0xF5 e = 1 + 2 * (e / 2) := by decide
  rw [layer, show 128 / 2 = 64 from rfl]
  exact ylay2_ok (block_ok op) bfly_ok lane_core2f 64 0xA0 0xF5 16 (fun c => 64 + c) (fun i => 64 + 4 * i) rfl
    (fun i _ => by omega) (fun i _ e he => ⟨by rw [hA e he]; omega, by rw [hF e he]; omega⟩)
    (fun i _ => (step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 lazyBfly 128 yzeta8 32) s fun s' => PolyIs s'.mem fP (layer F 1) ∧ BInvY fP s s' := by
  rw [layer, show 128 / 1 = 128 from rfl]
  exact ylay1_ok (block_ok op) bfly_ok lane_core1f 128 yzeta8 32 (fun c => 128 + c) (fun i => 128 + 8 * i) rfl
    (fun i _ => by omega)
    (fun i hi s h8 hin hT => WP.mono (yzeta8_ok (by omega) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega), (z l hl).2⟩, o⟩)
    (fun i _ => (step_fwd _ _ 8 (by decide)).trans (congrArg _ (by omega))) hc hdi hsi hS hT hwf hw hd


end VG.Proof.MlDsa.X86_64.Arith.Lazy
