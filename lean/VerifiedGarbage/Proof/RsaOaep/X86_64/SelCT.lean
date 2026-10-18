module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Sel
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Sel
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: the selectors in constant time

`selPrologue jH jG` is constant time in two runs with the same frame, the
same selectors and the same tables (`SelPt`, `selPro_ct`): its blocks are
checked by the taint analysis from `rsp` (and, after the load of a table's
address, from it too), its dispatches go the same way in both runs
(`two_chain`), and their cases differ only in the lengths they store as
immediates, which the taint analysis checks for every length up to 64.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp seqs)
open VG.Proof.MlKem.X86_64 (Keep ifn)
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post two_taint Scr)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)

theorem consts_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block (consts d))
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block (consts 0)))).isSome = true := by
  decide +kernel

theorem gd_taint : ∀ d < 65, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .rax (im d), .store (sp sGD) .rax])
    (taint.hintOf (Taint.ofRegs [.rsp]) (.block [.mov32 .rax (im 0), .store (sp sGD) .rax]))).isSome = true := by
  decide +kernel

variable {α : Type}

/-- The dispatch on `rax`, `kk a` in both runs, to `f` of each length of
`ls`: constant time if each case is, from the states but for `rax` and the
flags. -/
theorem two_chainW {ls : List (Nat × Nat)} (hls : LensOK ls) {kk : α → Nat} (hkk : ∀ a, kk a ∈ ls.map (·.1)) {f : Nat → Prog isa}
    {Φ : α → State → Prop} (hax : ∀ a t, Φ a t → t.gpr .rax = BitVec.ofNat 64 (kk a)) {Q : State → State → Prop}
    (hc : ∀ p ∈ ls, RelCT isa (Two fun a t => kk a = p.1 ∧ Mod Φ a t) (f p.2) Q) :
    RelCT isa (Two Φ) (Impl.Dispatch.X86_64.chain (ls.map fun p => (p.1, f p.2))) Q := by
  have hkeys : Proof.Dispatch.keys (ls.map fun p => (p.1, f p.2)) = ls.map (·.1) := by
    simp only [Proof.Dispatch.keys, List.map_map]; rfl
  have hsel : ∀ {a t}, Φ a t → Proof.Dispatch.X86_64.sel t = kk a := fun {a t} h => by
    have := hls.lt _ (hkk a)
    simp only [Proof.Dispatch.X86_64.sel, hax a t h, BitVec.toNat_ofNat]; omega
  refine Proof.Dispatch.chain_relCT Proof.Dispatch.X86_64.tests (by rw [hkeys]; exact hls.lt)
    (by rw [hkeys]; exact hls.nodup) (fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨by rw [hsel h₁, hsel h₂], by
      rw [hkeys, hsel h₁]; exact hkk a⟩) fun k c hc' => ?_
  obtain ⟨p, hm, he⟩ := List.mem_map.mp hc'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact (hc p hm).mono (fun s₁ s₂ ⟨a₁, a₂, ⟨a, h₁, h₂⟩, hs₁, r₁, r₂, _, _⟩ =>
    ⟨a, ⟨(hsel h₁).symm.trans hs₁, a₁, h₁, r₁.mem, r₁.rd, r₁.wr, fun r _ => r₁.gpr r⟩,
      ⟨(hsel h₁).symm.trans hs₁, a₂, h₂, r₂.mem, r₂.rd, r₂.wr, fun r _ => r₂.gpr r⟩⟩) fun _ _ h => h

theorem two_chain {kk : α → Nat} (hkk : ∀ a, kk a ∈ lens.map (·.1)) {f : Nat → Prog isa}
    {Φ : α → State → Prop} (hax : ∀ a t, Φ a t → t.gpr .rax = BitVec.ofNat 64 (kk a)) {Q : State → State → Prop}
    (hc : ∀ p ∈ lens, RelCT isa (Two fun a t => kk a = p.1 ∧ Mod Φ a t) (f p.2) Q) :
    RelCT isa (Two Φ) (Impl.Dispatch.X86_64.chain (lens.map fun p => (p.1, f p.2))) Q :=
  two_chainW lensOK hkk hax hc

/-- A point of `selPrologue`: in the frame `F a`, with the selectors `kH a`
and `kG a` the stack arguments `jH` and `jG`, readable, outside the frame,
and the tables `pH a` and `pG a` the stack arguments `jG + 1` and `jG + 2`. -/
structure SelPt (F S : α → Addr) (jH jG : Nat) (kH kG : α → Nat) (pH pG : α → Addr) (a : α) (t : State) :
    Prop where
  L : Lay t (F a) (S a)
  rep : ∃ V W, Rep t.mem (F a) (S a) V W
  inH : InRegions (t.rd ++ t.wr) (off (F a) (frameBytes + 8 + 8 * jH)) 8
  inG : InRegions (t.rd ++ t.wr) (off (F a) (frameBytes + 8 + 8 * jG)) 8
  args : ∀ m', Frame [⟨F a, frameBytes⟩] t.mem m' →
    m'.readW (off (F a) (frameBytes + 8 + 8 * jH)) 64 = BitVec.ofNat 64 (kH a) ∧
      m'.readW (off (F a) (frameBytes + 8 + 8 * jG)) 64 = BitVec.ofNat 64 (kG a)
  tH : ∃ w₀ w₁ w₂, TabAt t (F a) (jG + 1) (pH a) w₀ w₁ w₂
  tG : ∃ w₀ w₁ w₂, TabAt t (F a) (jG + 2) (pG a) w₀ w₁ w₂

variable {F S : α → Addr} {jH jG : Nat} {kH kG : α → Nat} {pH pG : α → Addr}

/-- After stores to the frame's slots but `scratch`'s. -/
theorem SelPt.of_frame {a : α} {t t' : State} (h : SelPt F S jH jG kH kG pH pG a t) {V V' : Nat → Byte}
    {W W' : Nat → BitVec 64} (R : Rep t.mem (F a) (S a) V W) (R' : Rep t'.mem (F a) (S a) V' W')
    (h14 : W' 14 = W 14) (hsp : t'.gpr .rsp = t.gpr .rsp) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hf : Frame [⟨F a, frameBytes⟩] t.mem t'.mem) : SelPt F S jH jG kH kG pH pG a t' :=
  ⟨h.L.of_rep' R R' h14 hsp hwr, ⟨V', W', R'⟩, by rw [hrd, hwr]; exact h.inH, by rw [hrd, hwr]; exact h.inG,
    fun m' hf' => h.args m' (hf.trans hf'),
    let ⟨w₀, w₁, w₂, T⟩ := h.tH; ⟨w₀, w₁, w₂, T.mono hrd hwr hf⟩,
    let ⟨w₀, w₁, w₂, T⟩ := h.tG; ⟨w₀, w₁, w₂, T.mono hrd hwr hf⟩⟩

theorem SelPt.of_mod {a : α} {t t₀ : State} (h : SelPt F S jH jG kH kG pH pG a t₀) (hm : t.mem = t₀.mem)
    (hrd : t.rd = t₀.rd) (hwr : t.wr = t₀.wr) (g : ∀ r, r ≠ .rax → t.gpr r = t₀.gpr r) :
    SelPt F S jH jG kH kG pH pG a t :=
  have hf : Frame [⟨F a, frameBytes⟩] t₀.mem t.mem := by rw [hm]; exact Frame.refl _ _
  ⟨h.L.congr (g .rsp (by decide)) hwr (by rw [hm]), hm ▸ h.rep, by rw [hrd, hwr]; exact h.inH,
    by rw [hrd, hwr]; exact h.inG, fun m' hf' => h.args m' (hm ▸ hf'),
    let ⟨w₀, w₁, w₂, T⟩ := h.tH; ⟨w₀, w₁, w₂, T.mono hrd hwr hf⟩,
    let ⟨w₀, w₁, w₂, T⟩ := h.tG; ⟨w₀, w₁, w₂, T.mono hrd hwr hf⟩⟩

theorem selPins {Φ : α → State → Prop} (h : ∀ a t, Φ a t → t.gpr .rsp = F a) : Pins Φ [.rsp] :=
  fun a _ _ h₁ h₂ r hr => by rw [List.mem_singleton.mp hr, h a _ h₁, h a _ h₂]

/-- A selector to its slot `8 k`. -/
theorem selArg_ok {a : α} {t : State} (h : SelPt F S jH jG kH kG pH pG a t) {j k : Nat} {v : BitVec 64}
    (hin : InRegions (t.rd ++ t.wr) (off (F a) (frameBytes + 8 + 8 * j)) 8)
    (hv : t.mem.readW (off (F a) (frameBytes + 8 + 8 * j)) 64 = v) (hk : k < nW) (hk14 : k ≠ 14) :
    WP isa (.block (argSlot j (8 * k))) t fun t' => SelPt F S jH jG kH kG pH pG a t' ∧ t'.gpr .rax = v := by
  obtain ⟨V, W, R⟩ := h.rep
  have hF := h.L.Fw
  exact WP.mono (argSlot_ok h.L.rsp h.L.frScr hin hv (d := 8 * k) (by unfold nW at hk; unfold frameBytes at hk ⊢; omega))
    fun t' ⟨kp, ax, hm⟩ => ⟨h.of_frame R (hm ▸ R.wf h.L.geo hk v) (by simp [upd, Ne.symm hk14]) (kp.gpr (by decide))
      kp.2.1 kp.2.2 (by rw [hm]; exact frame_wF hF (Frame.refl _ _) (by unfold nW at hk; unfold frameBytes at hk ⊢; omega) v), ax⟩

/-- A table's address into `rax`, then its words to the slots `8 k` to
`8 (k + 2)`. -/
theorem fns_ct {j k : Nat} {p : α → Addr}
    (hT : ∀ a t, SelPt F S jH jG kH kG pH pG a t → ∃ w₀ w₁ w₂, TabAt t (F a) j (p a) w₀ w₁ w₂)
    (hk : k + 2 < nW) (hk14 : 14 < k)
    (htd : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (arg j))]) hc).isSome = true)
    (htt : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rax]) (.block (fnTail (8 * k))) hc).isSome = true) :
    RelCT isa (Two (SelPt F S jH jG kH kG pH pG)) (.block (fnSlots j (8 * k))) (Two (SelPt F S jH jG kH kG pH pG)) := by
  obtain ⟨_, htd⟩ := htd
  obtain ⟨_, htt⟩ := htt
  have hk' : k + 2 < 51 := hk
  rw [fnSlots_eq]
  refine RelCT.block_append (RelCT.seq (two_post (Ψ := fun a t => SelPt F S jH jG kH kG pH pG a t ∧ t.gpr .rax = p a)
    (two_taint [.rsp] (selPins fun a t h => h.L.rsp) htd) fun a t h => ?_)
    (two_post (two_taint [.rsp, .rax] (fun a _ _ h₁ h₂ r hr => ?_) htt) fun a t h => ?_))
  · obtain ⟨w₀, w₁, w₂, T⟩ := hT a t h
    obtain ⟨V, W, R⟩ := h.rep
    exact WP.mono (fnHead_ok h.L.rsp T) fun t' ⟨kp, hm, ax⟩ =>
      ⟨h.of_frame R (hm ▸ R) rfl (kp.gpr (by decide)) kp.2.1 kp.2.2 (by rw [hm]; exact Frame.refl _ _), ax⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.L.rsp, h₂.1.L.rsp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨w₀, w₁, w₂, T⟩ := hT a t h.1
    obtain ⟨V, W, R⟩ := h.1.rep
    have hF := h.1.L.Fw
    have G' := h.1.L.geo
    refine WP.mono (fnTail_ok h.1.L.rsp h.1.L.frScr hF T h.2 (d := 8 * k) (by unfold frameBytes; omega))
      fun t' ⟨kp, hm⟩ => ?_
    have R' : Rep t'.mem (F a) (S a) V (upd (upd (upd W k w₀) (k + 1) w₁) (k + 2) w₂) := by
      rw [hm, show 8 * k + 8 = 8 * (k + 1) by omega, show 8 * k + 16 = 8 * (k + 2) by omega]
      exact ((R.wf G' (k := k) (by unfold nW frameBytes; omega) w₀).wf G' (k := k + 1) (by unfold nW frameBytes; omega)
        w₁).wf G' (k := k + 2) (by unfold nW frameBytes; omega) w₂
    refine h.1.of_frame R R' (by simp only [upd]; rw [ifn (by omega), ifn (by omega), ifn (by omega)]) (kp.gpr (by decide)) kp.2.1 kp.2.2 ?_
    rw [hm]
    exact frame_wF hF (frame_wF hF (frame_wF hF (Frame.refl _ _) (by unfold frameBytes; omega) _)
      (by unfold frameBytes; omega) _) (by unfold frameBytes; omega) _

/-- `selPrologueWith ls` in two runs with the same frame, selectors and
tables. -/
theorem selProW_ct {ls : List (Nat × Nat)} (hls : LensOK ls) (hkH : ∀ a, kH a ∈ ls.map (·.1))
    (hkG : ∀ a, kG a ∈ ls.map (·.1))
    (htH : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (argSlot jH sSelH)) hc).isSome = true)
    (htG : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (argSlot jG sSelG)) hc).isSome = true)
    (htFH : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (arg (jG + 1)))]) hc).isSome = true)
    (htFG : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (arg (jG + 2)))]) hc).isSome = true) :
    RelCT isa (Two (SelPt F S jH jG kH kG pH pG)) (selPrologueWith ls jH jG) fun _ _ => True := by
  obtain ⟨_, htH⟩ := htH
  obtain ⟨_, htG⟩ := htG
  have pinP : ∀ {Ψ : α → State → Prop}, (∀ a t, Ψ a t → SelPt F S jH jG kH kG pH pG a t) → Pins Ψ [.rsp] :=
    fun h => selPins fun a t p => (h a t p).L.rsp
  have pinM : ∀ {Ψ : α → State → Prop} {kk : α → Nat} (k : Nat),
      (∀ a t, Ψ a t → SelPt F S jH jG kH kG pH pG a t) → Pins (fun a t => kk a = k ∧ Mod Ψ a t) [.rsp] :=
    fun k h => selPins fun a t ⟨_, t₀, p, _, _, _, g⟩ => (g .rsp (by decide)).trans (h a t₀ p).L.rsp
  unfold selPrologueWith seqs seqs seqs seqs
  -- `hash` to its slot.
  refine RelCT.seq (two_post (Ψ := fun a t => SelPt F S jH jG kH kG pH pG a t ∧ t.gpr .rax = BitVec.ofNat 64 (kH a))
    (two_taint [.rsp] (pinP fun _ _ h => h) htH) fun a t h =>
      selArg_ok h h.inH (h.args _ (Frame.refl _ _)).1 (k := 37) (by decide) (by decide)) ?_
  -- Its lengths.
  refine RelCT.seq (two_post (Ψ := SelPt F S jH jG kH kG pH pG)
    (two_chainW hls hkH (f := fun D => .block (consts D)) (fun a t h => h.2) fun p hp =>
      two_taint [.rsp] (pinM _ fun _ _ h => h.1) (consts_taint p.2 (by have := hls.le p hp; omega)))
    fun a t h => ?_) ?_
  · obtain ⟨⟨i, D⟩, hm, he⟩ := List.mem_map.mp (hkH a)
    simp only at he
    subst he
    refine chainLW_wp hls (f := fun D => .block (consts D)) hm h.2 fun s' hs' => ?_
    have p' := h.1.of_mod hs'.mem hs'.rd hs'.wr fun r _ => hs'.gpr r
    obtain ⟨V, W, R⟩ := p'.rep
    have hF := p'.L.Fw
    have G' := p'.L.geo
    refine WP.mono (consts_ok p'.L.rsp p'.L.frScr (hls.le _ hm)) fun u ⟨k, m⟩ => ?_
    have R' : Rep u.mem (F a) (S a) V (upd (upd (upd (upd W 39 (BitVec.ofNat 64 D)) 40 (BitVec.ofNat 64 (D + 1)))
        41 (BitVec.ofNat 64 (2 * D + 1))) 42 (BitVec.ofNat 64 (2 * D + 2))) := by
      rw [m]
      exact (((R.wf G' (k := 39) (by decide) _).wf G' (k := 40) (by decide) _).wf G' (k := 41) (by decide) _).wf G'
        (k := 42) (by decide) _
    refine p'.of_frame R R' (by simp [upd]) (k.gpr (by decide)) k.2.1 k.2.2 ?_
    rw [m]
    exact frame_wF hF (frame_wF hF (frame_wF hF (frame_wF hF (Frame.refl _ _) (by decide) _) (by decide) _)
      (by decide) _) (by decide) _
  -- `mgf1_hash` to its slot.
  refine RelCT.seq (two_post (Ψ := fun a t => SelPt F S jH jG kH kG pH pG a t ∧ t.gpr .rax = BitVec.ofNat 64 (kG a))
    (two_taint [.rsp] (pinP fun _ _ h => h) htG) fun a t h =>
      selArg_ok h h.inG (h.args _ (Frame.refl _ _)).2 (k := 38) (by decide) (by decide)) ?_
  -- Its length.
  refine RelCT.seq (two_post (Ψ := SelPt F S jH jG kH kG pH pG)
    (two_chainW hls hkG (f := fun D => .block [.mov32 .rax (im D), .store (sp sGD) .rax]) (fun a t h => h.2)
      fun p hp => two_taint [.rsp] (pinM _ fun _ _ h => h.1) (gd_taint p.2 (by have := hls.le p hp; omega)))
    fun a t h => ?_) ?_
  · obtain ⟨⟨i, D⟩, hm, he⟩ := List.mem_map.mp (hkG a)
    simp only at he
    subst he
    refine chainLW_wp hls (f := fun D => .block [.mov32 .rax (im D), .store (sp sGD) .rax]) hm h.2 fun s' hs' => ?_
    have p' := h.1.of_mod hs'.mem hs'.rd hs'.wr fun r _ => hs'.gpr r
    obtain ⟨V, W, R⟩ := p'.rep
    have hF := p'.L.Fw
    refine WP.mono (gd_ok p'.L.rsp p'.L.frScr (hls.le _ hm)) fun u ⟨k, m⟩ => ?_
    refine p'.of_frame R (m ▸ R.wf p'.L.geo (k := 43) (by decide) _) (by simp [upd]) (k.gpr (by decide)) k.2.1 k.2.2 ?_
    rw [m]
    exact frame_wF hF (Frame.refl _ _) (by decide) _
  -- The tables' words.
  refine RelCT.block_append (RelCT.seq (fns_ct (k := 45) (fun a t h => h.tH) (by decide) (by decide) htFH
    ⟨_, by taint_decide⟩) ?_)
  exact (fns_ct (k := 48) (fun a t h => h.tG) (by decide) (by decide) htFG ⟨_, by taint_decide⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

/-- `selPrologue` in two runs with the same frame, selectors and tables. -/
theorem selPro_ct (hkH : ∀ a, kH a ∈ lens.map (·.1)) (hkG : ∀ a, kG a ∈ lens.map (·.1))
    (htH : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (argSlot jH sSelH)) hc).isSome = true)
    (htG : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (argSlot jG sSelG)) hc).isSome = true)
    (htFH : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (arg (jG + 1)))]) hc).isSome = true)
    (htFG : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (arg (jG + 2)))]) hc).isSome = true) :
    RelCT isa (Two (SelPt F S jH jG kH kG pH pG)) (selPrologue jH jG) fun _ _ => True :=
  selProW_ct lensOK hkH hkG htH htG htFH htFG

end VG.Proof.RsaOaep.X86_64
