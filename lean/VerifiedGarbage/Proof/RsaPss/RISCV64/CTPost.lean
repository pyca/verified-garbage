module

-- separate module: it builds in parallel with `Correct`, which `Verified` also needs.

public import VerifiedGarbage.Proof.RsaPss.RISCV64.CTHash
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Post
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.RsaPss.RISCV64.CTBlocks
import VerifiedGarbage.Proof.RsaPss.RISCV64.Shift
public import VerifiedGarbage.Proof.RsaPss.RISCV64.Prefix

/-!
# RSASSA-PSS verification on RISC-V: constant time after the public operation

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPss/PPC64LE/CTPost.lean`): two runs from states with `BL` for the
same anchor, `c`, `salt_len` and the salt-length mode in `s5`–`s7` (`Xa`),
and a salt length that fits if one is given (`Fit`), leak alike (`post_ct`):
the blocks and call-free loops by the taint analysis (`CTBlocks`), MGF1 by
`mgfXor_ct`, the hashing of `M'` by `hashFixed_ct` and `hashAny_ct`, and the
branches on the salt-length mode by `two_ite`, which `s7` holds for both;
between them each run keeps `BL` by correctness. While MGF1 runs, the three
values wait at `oV` (`Sv`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPss.RISCV64
open VG.Impl.RsaOaep.RISCV64 (oSt oDig oCtr oRsa mgfXor)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.RsaOaep.RISCV64 (Base Fits off off_off view fx Agree Ok B two_seq HashCT hfits offs MFit MgfA
  mgfXor_ct mgfXor_ok)
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept Two Pins two_post two_ite eval_zero)
open VG.Proof.RsaOaep (mixV)
open VG.Proof.Mgf1 (ifp ifn)

/-- The salt length given fits in `DB`. -/
abbrev Fit (D : Nat) (a : State) : Prop := anyL a = 0 → (a.gpr .a7).toNat + 1 ≤ (dbLen D a).toNat

/-- MGF1's arguments for unmasking `DB`, from the anchor. -/
abbrev qM (D : Nat) (a : State) : Nat × Nat × Nat × Nat :=
  ((lo a).toNat + (dbLen D a).toNat, D, (lo a).toNat, (dbLen D a).toNat)

/-- `c`, `salt_len` and the mode at `oV`. -/
abbrev Sv (a t : State) : Prop :=
  t.mem.readW (off (Sp a) oV) 64 = cm a ∧ t.mem.readW (off (Sp a) (oV + 8)) 64 = a.gpr .a7 ∧
    t.mem.readW (off (Sp a) (oV + 16)) 64 = anyL a

theorem readV {m m' : Mem} {S : Addr} (h : ∀ i < 24, view m' S (oV + i) = view m S (oV + i)) {d : Nat}
    (hd : d + 8 ≤ 24) : m'.readW (off S (oV + d)) 64 = m.readW (off S (oV + d)) 64 :=
  Mem.readW_congr fun i hi => by
    have e := h (d + i) (by omega)
    simp only [view] at e
    show m' (off (off S (oV + d)) i) = m (off (off S (oV + d)) i)
    rw [off_off, Nat.add_assoc]; exact e

theorem Sv.keep {a t t' : State} (h : Sv a t)
    (hv : ∀ i < 24, view t'.mem (Sp a) (oV + i) = view t.mem (Sp a) (oV + i)) : Sv a t' := by
  have e0 := readV hv (d := 0) (by decide)
  rw [Nat.add_zero] at e0
  exact ⟨e0.trans h.1, (readV hv (d := 8) (by decide)).trans h.2.1, (readV hv (d := 16) (by decide)).trans h.2.2⟩

/-- Pins of states with `BL` and `Xa`. -/
theorem xa_pins {D : Nat} {α : Type} {Φ : α → State → Prop} {an : α → State}
    (h : ∀ x t, Φ x t → BL D (an x) t ∧ Xa (an x) t) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7] := by decide) : Pins Φ rs :=
  fun x t₁ t₂ h₁ h₂ => by
  obtain ⟨b₁, x₁⟩ := h x t₁ h₁
  obtain ⟨b₂, x₂⟩ := h x t₂ h₂
  obtain ⟨f₁, g₁, v₁⟩ := b₁.agree (lOk D)
  obtain ⟨f₂, g₂, v₂⟩ := b₂.agree (lOk D)
  refine ⟨f₁.trans f₂.symm, fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact g₁.trans g₂.symm
  · exact (v₁ _ (by decide)).trans (v₂ _ (by decide)).symm
  · exact (v₁ _ (by decide)).trans (v₂ _ (by decide)).symm
  · exact (v₁ _ (by decide)).trans (v₂ _ (by decide)).symm
  · exact (v₁ _ (by decide)).trans (v₂ _ (by decide)).symm
  · exact x₁.s5.trans x₂.s5.symm
  · exact x₁.s6.trans x₂.s6.symm
  · exact x₁.s7.trans x₂.s7.symm

section
variable {D : Nat} {H : Hash} (hH : HashOK H) (cH : HashCT hH) (hF : H.F ≤ 208) (hD : H.D = D)
  {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hH.SH.H.hash x) (hGl : Gs.len = H.D)
  (hGv : Proof.Mgf1.Valid Gs)

theorem acc0_wp {a t : State} (h : BL D a t) (x : Xa a t) :
    WP isa (.block acc0) t fun t' => BL D a t' ∧ Xa a t' := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (acc0_ok (agree_lay P g) b (x.xs g)) fun t' ⟨b', k', _⟩ =>
    ⟨⟨s, P, g, b'⟩, x.of fun r hr => k'.gpr r (by revert r; decide)⟩

theorem spill_wp {a t : State} (h : BL D a t) (x : Xa a t) :
    WP isa (.block spill) t fun t' => BL D a t' ∧ Xa a t' ∧ Sv a t' := by
  obtain ⟨s, P, g, b⟩ := h
  have hS : Sp s = Sp a := g.ag.S
  exact WP.mono (spill_ok (agree_lay P g) b (x.xs g)) fun t' ⟨b', g', _, w5, w6, w7⟩ =>
    ⟨⟨s, P, g, b'⟩, x.of fun r _ => g' r, by rw [← hS, w5, g.cm], by rw [← hS, w6, g.sl],
      by rw [← hS, w7, g.any]⟩

theorem qM_fit {a t : State} (h : BL D a t) : MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 := by
  have := h.dn
  show MFit ((lo a).toNat + (dbLen D a).toNat) D (lo a).toNat (dbLen D a).toNat
  exact ⟨by omega, by omega, .inr (by omega), by omega⟩

include hD in
theorem dbArgs_wp {a t : State} (h : BL D a t) (v : Sv a t) :
    WP isa (.block (dbArgs H)) t fun t' =>
      MgfA Sp (vP D) (PreL D) (AgreeP D) (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 a t' ∧
        Sv a t' := by
  obtain ⟨s, P, g, b⟩ := h
  have hS : Sp s = Sp a := g.ag.S
  exact WP.mono (dbArgs_ok (agree_lay P g) hD b) fun t' ⟨b', k', x6, x7, x8, x9⟩ =>
    ⟨⟨s, P, g, b', by rw [x6, hS], x7, by rw [x8, hS], x9⟩, by simp only [Sv, k'.mem]; exact v⟩

include hH cH hF hD hGh hGl hGv in
theorem mgf_two : RelCT isa (Two fun a t =>
      MgfA Sp (vP D) (PreL D) (AgreeP D) (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 a t ∧
        MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2) (mgfXor H) fun _ _ => True := by
  subst hD
  exact (RelCT.exists_ (P := fun (x : {x : Nat × Nat × Nat × Nat // MFit x.1 x.2.1 x.2.2.1 x.2.2.2}) =>
      Two (MgfA Sp (vP H.D) (PreL H.D) (AgreeP H.D) x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    fun x => mgfXor_ct (lOk H.D) hH cH hF x.2 hGh hGl hGv).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨⟨qM H.D a, h₁.2⟩, a, h₁.1, h₂.1⟩) fun _ _ h => h

include hH hF hD hGh hGl hGv in
theorem mgf_wp {a t : State}
    (h : MgfA Sp (vP D) (PreL D) (AgreeP D) (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2 a t)
    (v : Sv a t) : WP isa (mgfXor H) t fun t' => BL D a t' ∧ Sv a t' := by
  obtain ⟨s, P, g, b, h6, h7, h8, h9⟩ := h
  have hS : Sp s = Sp a := g.ag.S
  have hf := qM_fit (D := D) ⟨s, P, g, b⟩
  have hfd := hf.fd
  subst hD
  refine WP.mono (mgfXor_ok P.F hH hF hGh hGl hGv hf b (by rw [h6, hS]) h7 (by rw [h8, hS]) h9)
    fun t' ⟨b', v'⟩ => ⟨⟨s, P, g, b'⟩, v.keep fun i hi => ?_⟩
  have e := v' (oV + i) ⟨by unfold oV oRsa; omega, .inr (by unfold oV oCtr; omega)⟩
  rw [mixV, ifn (by show ¬((qM H.D a).2.2.1 ≤ oV + i ∧ _); unfold oV; omega)] at e
  rw [← hS]; exact e

theorem reload_wp {a t : State} (h : BL D a t) (v : Sv a t) :
    WP isa (.block reload) t fun t' => BL D a t' ∧ Xa a t' := by
  obtain ⟨s, P, g, b⟩ := h
  have hS : Sp s = Sp a := g.ag.S
  exact WP.mono (reload_ok (agree_lay P g) b (by rw [hS, v.1, g.cm]) (by rw [hS, v.2.1, g.sl])
    (by rw [hS, v.2.2, g.any])) fun t' ⟨b', x', _⟩ => ⟨⟨s, P, g, b'⟩, x'.xa g⟩

theorem clearTop_wp {a t : State} (h : BL D a t) (x : Xa a t) :
    WP isa (.block clearTop) t fun t' => BL D a t' ∧ Xa a t' := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (clearTop_ok (agree_lay P g) b (x.xs g)) fun t' ⟨b', k', _⟩ =>
    ⟨⟨s, P, g, b'⟩, x.of fun r hr => k'.gpr r (by revert r; decide)⟩

/-- Some position in `DB` in `a5`. -/
abbrev Pos5 (D : Nat) (a t : State) : Prop := ∃ pos < (dbLen D a).toNat, t.gpr .a5 = BitVec.ofNat 64 pos

theorem scan_wp {a t : State} (h : BL D a t) (x : Xa a t) :
    WP isa scan t fun t' => BL D a t' ∧ Xa a t' ∧ Pos5 D a t' := by
  obtain ⟨s, P, g, b⟩ := h
  have L := agree_lay P g
  have hd1 := L.d1
  exact WP.mono (scan_ok L b (w := fun j => view t.mem (Sp s) ((lo a).toNat + j)) fun _ _ => rfl)
    fun t' ⟨b', _, o', x5, _⟩ => ⟨⟨s, P, g, b'⟩, x.of fun r hr => o'.gpr r (by revert r; decide), _,
      by split <;> omega, x5⟩

/-- Some position in `DB` in `s8`, and the length of the salt after it in `s11`. -/
abbrev Pos11 (D : Nat) (a t : State) : Prop :=
  ∃ pos < (dbLen D a).toNat, t.gpr .s8 = BitVec.ofNat 64 pos ∧
    t.gpr .s11 = BitVec.ofNat 64 ((dbLen D a).toNat - pos - 1)

theorem posCheck_wp {a t : State} (h : BL D a t) (x : Xa a t) (hp : Pos5 D a t) :
    WP isa (.block posCheck) t fun t' => BL D a t' ∧ Xa a t' ∧ Pos11 D a t' := by
  obtain ⟨s, P, g, b⟩ := h
  obtain ⟨pos, hp, x5⟩ := hp
  exact WP.mono (posCheck_ok (agree_lay P g) b rfl x5 hp rfl) fun t' ⟨b', o', _, x11, x8⟩ =>
    ⟨⟨s, P, g, b'⟩, x.of fun r hr => o'.gpr r (by revert r; decide), pos, hp, x8, x11⟩

theorem lenCheck_wp {a t : State} (h : BL D a t) (x : Xa a t) (hp : Pos11 D a t) :
    WP isa lenCheck t fun t' => BL D a t' ∧ Xa a t' ∧ Pos11 D a t' := by
  obtain ⟨s, P, g, b⟩ := h
  obtain ⟨pos, hp, x8, x11⟩ := hp
  exact WP.mono (lenCheck_ok (agree_lay P g) b (x.xs g) rfl x11) fun t' ⟨b', o', _⟩ =>
    ⟨⟨s, P, g, b'⟩, x.of fun r hr => o'.gpr r (by revert r; decide), pos, hp, by rw [o'.get .s8, x8],
      by rw [o'.get .s11, x11]⟩

include hD in
theorem prefix_wp {nset : List Instr} {n : Nat} (hn : 8 ≤ n) (hn' : n ≤ 2048)
    (hns : ∀ {u : State} {is : List Instr} {Q : State → Prop},
      (∀ u', Only [.t5] u u' → u'.gpr .t5 = BitVec.ofNat 64 n → WP isa (.block is) u' Q) →
      WP isa (.block (nset ++ is)) u Q)
    {a t : State} (h : BL D a t) : WP isa (mPrefix H nset) t fun t' => BL D a t' ∧ Kept mpR t t' := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (prefix_ok (agree_lay P g) hD hn hn' hns b) fun t' ⟨b', g', _⟩ => ⟨⟨s, P, g, b'⟩, g'⟩

include hD in
theorem salt_wp {a t : State} (h : BL D a t) (x : Xa a t) (hsl : (a.gpr .a7).toNat + 1 ≤ (dbLen D a).toNat) :
    WP isa (copySalt H) t fun t' => BL D a t' ∧ Kept mpR t t' := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (salt_ok (agree_lay P g) hD b (x.xs g) (by rw [g.sl]; exact hsl)) fun t' ⟨b', k', _⟩ =>
    ⟨⟨s, P, g, b'⟩, k'⟩

include hH hF hD in
theorem hashFixed_wp {a t : State} (h : BL D a t) (h6 : t.gpr .s6 = a.gpr .a7)
    (hsl : (a.gpr .a7).toNat + 8 + D ≤ 2048) : WP isa (hashFixed H) t (BL D a) := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (hashFixedG_ok P.F hH hF hD (sl := (a.gpr .a7).toNat) (by rw [h6, ofNat_toNat]) b hsl)
    fun t' ⟨b', _⟩ => ⟨s, P, g, b'⟩

include hD in
theorem copyDb_wp {a t : State} (h : BL D a t) : WP isa (copyDb H) t fun t' => BL D a t' ∧ Kept mpR t t' := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (copyDb_ok (agree_lay P g) hD b) fun t' ⟨b', g', _⟩ => ⟨⟨s, P, g, b'⟩, g'⟩

include hD in
theorem shift_wp {a t : State} (h : BL D a t) {pos : Nat} (hp : pos < (dbLen D a).toNat)
    (h8 : t.gpr .s8 = BitVec.ofNat 64 pos) :
    WP isa (shift H) t fun t' => BL D a t' ∧ t'.gpr .s11 = t.gpr .s11 := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (shift_ok (agree_lay P g) hD b h8 hp) fun t' ⟨b', k', _⟩ =>
    ⟨⟨s, P, g, b'⟩, k'.gpr .s11 (by decide)⟩

include hH hF hD in
theorem hashAny_wp {a t : State} (h : BL D a t) {sl : Nat} (hsl : sl < (dbLen D a).toNat)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 sl) : WP isa (hashAny H) t (BL D a) := by
  obtain ⟨s, P, g, b⟩ := h
  exact WP.mono (hashAny_ok (agree_lay P g) hH hF hD b hsl h11) fun t' ⟨b', _⟩ => ⟨s, P, g, b'⟩

theorem Pos11.keep {a t t' : State} (h : Pos11 D a t) (g : Kept mpR t t') : Pos11 D a t' := by
  obtain ⟨pos, hp, x8, x11⟩ := h
  exact ⟨pos, hp, by rw [g.get .s8, x8], by rw [g.get .s11, x11]⟩

include hH cH hF hD hGh hGl hGv in
/-- The code after the public operation, in both runs. -/
theorem post_ct : RelCT isa (Two fun a t => BL D a t ∧ Xa a t ∧ Fit D a)
    (.seq (.block acc0) (.seq (.block spill) (.seq (.block (dbArgs H)) (.seq (mgfXor H)
      (.seq (.block reload) (.seq (.block clearTop) (.seq scan (.seq (.block posCheck) (.seq lenCheck
      (finish H)))))))))) fun _ _ => True := by
  let P0 := fun (a t : State) => BL D a t ∧ Xa a t ∧ Fit D a
  refine two_seq (Ψ := P0) (acc0_taint (bl_pins (an := id) (fun _ _ h => h.1) [.s0, .s1, .s3]))
    (fun a t h => WP.mono (acc0_wp h.1 h.2.1) fun t' ⟨b, x⟩ => ⟨b, x, h.2.2⟩) ?_
  let P1 := fun (a t : State) => (BL D a t ∧ Sv a t) ∧ Fit D a
  refine two_seq (Ψ := P1) (spill_taint (bl_pins (an := id) (fun _ _ h => h.1) [.s0]))
    (fun a t h => WP.mono (spill_wp h.1 h.2.1) fun t' ⟨b, _, v⟩ => ⟨⟨b, v⟩, h.2.2⟩) ?_
  refine two_seq (Ψ := fun a t => ((MgfA Sp (vP D) (PreL D) (AgreeP D) (qM D a).1 (qM D a).2.1 (qM D a).2.2.1
      (qM D a).2.2.2 a t ∧ MFit (qM D a).1 (qM D a).2.1 (qM D a).2.2.1 (qM D a).2.2.2) ∧ Sv a t) ∧ Fit D a)
    (dbArgs_taint H (bl_pins (an := id) (fun _ _ h => h.1.1) []))
    (fun a t h => WP.mono (dbArgs_wp hD h.1.1 h.1.2) fun t' ⟨m, v⟩ => ⟨⟨⟨m, qM_fit h.1.1⟩, v⟩, h.2⟩) ?_
  refine two_seq (Ψ := P1) ((mgf_two hH cH hF hD hGh hGl hGv).mono (fun _ _ ⟨a, h₁, h₂⟩ =>
      ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h)
    (fun a t h => WP.mono (mgf_wp hH hF hD hGh hGl hGv h.1.1.1 h.1.2) fun t' bv => ⟨bv, h.2⟩) ?_
  refine two_seq (Ψ := P0) (reload_taint (bl_pins (an := id) (fun _ _ h => h.1.1) [.s0]))
    (fun a t h => WP.mono (reload_wp h.1.1 h.1.2) fun t' ⟨b, x⟩ => ⟨b, x, h.2⟩) ?_
  refine two_seq (Ψ := P0) (clearTop_taint (bl_pins (an := id) (fun _ _ h => h.1) [.s0, .s3]))
    (fun a t h => WP.mono (clearTop_wp h.1 h.2.1) fun t' ⟨b, x⟩ => ⟨b, x, h.2.2⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos5 D a t)
    (scan_taint (bl_pins (an := id) (fun _ _ h => h.1) [.s0, .s3, .s4]))
    (fun a t h => WP.mono (scan_wp h.1 h.2.1) fun t' ⟨b, x, p⟩ => ⟨⟨b, x, h.2.2⟩, p⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos11 D a t)
    (posCheck_taint (bl_pins (an := id) (fun _ _ h => h.1.1) [.s0, .s1]))
    (fun a t h => WP.mono (posCheck_wp h.1.1 h.1.2.1 h.2) fun t' ⟨b, x, p⟩ => ⟨⟨b, x, h.1.2.2⟩, p⟩) ?_
  refine two_seq (Ψ := fun a t => P0 a t ∧ Pos11 D a t)
    (lenCheck_taint (xa_pins (an := id) (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) [.s7]))
    (fun a t h => WP.mono (lenCheck_wp h.1.1 h.1.2.1 h.2) fun t' ⟨b, x, p⟩ => ⟨⟨b, x, h.1.2.2⟩, p⟩) ?_
  -- The salt's hash, by the salt-length mode.
  refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1.s7, h₂.1.2.1.s7]) ?_ ?_
  · have ha : ∀ {a t : State}, (P0 a t ∧ Pos11 D a t) ∧ isa.eval (.zero .s7) t = some true → anyL a = 0 :=
      fun ⟨h, e⟩ => by rw [eval_zero, h.1.2.1.s7] at e; exact beq_iff_eq.mp (Option.some.inj e)
    let F0 := fun (a t : State) => (BL D a t ∧ Xa a t) ∧ (a.gpr .a7).toNat + 1 ≤ (dbLen D a).toNat
    refine two_seq (Ψ := F0) (mPrefix8_taint H (bl_pins (an := id) (fun _ _ h => h.1.1.1) [.s0, .s2]))
      (fun a t h => WP.mono (prefix_wp hD (by decide) (by decide) nset8 h.1.1.1) fun t' ⟨b, k⟩ =>
        ⟨⟨b, h.1.1.2.1.of fun r hr => k.gpr r (by revert r; decide)⟩, h.1.1.2.2 (ha h)⟩) ?_
    refine two_seq (Ψ := F0) (copySalt_taint H (xa_pins (an := id) (fun _ _ h => h.1) [.s0, .s3, .s4, .s6]))
      (fun a t h => WP.mono (salt_wp hD h.1.1 h.1.2 h.2) fun t' ⟨b, k⟩ =>
        ⟨⟨b, h.1.2.of fun r hr => k.gpr r (by revert r; decide)⟩, h.2⟩) ?_
    have hb : ∀ {a t : State}, F0 a t → (a.gpr .a7).toNat + 8 + D ≤ 2048 := fun h => by
      have := h.1.1.dn; have := h.2; omega
    refine two_seq (Ψ := BL D) ((hashFixed_ct hH cH hF hD).mono (fun _ _ ⟨a, h₁, h₂⟩ =>
        ⟨a, ⟨h₁.1.1, h₁.1.2.s6, hb h₁⟩, ⟨h₂.1.1, h₂.1.2.s6, hb h₂⟩⟩) fun _ _ h => h)
      (fun a t h => hashFixed_wp hH hF hD h.1.1 h.1.2.s6 (hb h)) ?_
    exact cmpH_taint H oDig (bl_pins (an := id) (fun _ _ h => h) [.s0, .s3, .s4])
  · let A0 := fun (a t : State) => BL D a t ∧ Pos11 D a t
    refine two_seq (Ψ := A0) (mPrefix2048_taint H (bl_pins (an := id) (fun _ _ h => h.1.1.1) [.s0, .s2]))
      (fun a t h => WP.mono (prefix_wp hD (by decide) (by decide) nset2048 h.1.1.1) fun t' ⟨b, k⟩ =>
        ⟨b, h.1.2.keep k⟩) ?_
    refine two_seq (Ψ := A0) (copyDb_taint H (bl_pins (an := id) (fun _ _ h => h.1) [.s0, .s3, .s4]))
      (fun a t h => WP.mono (copyDb_wp hD h.1) fun t' ⟨b, k⟩ => ⟨b, h.2.keep k⟩) ?_
    let A1 := fun (a t : State) => BL D a t ∧ ∃ sl < (dbLen D a).toNat, t.gpr .s11 = BitVec.ofNat 64 sl
    refine two_seq (Ψ := A1) (shift_taint H (bl_pins (an := id) (fun _ _ h => h.1) [.s0, .s4]))
      (fun a t h => ?_) ?_
    · obtain ⟨pos, hp, x8, x11⟩ := h.2
      exact WP.mono (shift_wp hD h.1 hp x8) fun t' ⟨b, g⟩ =>
        ⟨b, (dbLen D a).toNat - pos - 1, by omega, by rw [g, x11]⟩
    have hs : ∀ {a t : State}, A1 a t → S11 t := fun h => by
      obtain ⟨sl, hsl, x11⟩ := h.2
      have := h.1.dn
      exact ⟨sl, x11, by omega⟩
    refine two_seq (Ψ := BL D) ((hashAny_ct hH cH hF hD).mono (fun _ _ ⟨a, h₁, h₂⟩ =>
        ⟨a, ⟨h₁.1, hs h₁⟩, ⟨h₂.1, hs h₂⟩⟩) fun _ _ h => h)
      (fun a t h => let ⟨_, hsl, x11⟩ := h.2; hashAny_wp hH hF hD h.1 hsl x11) ?_
    exact cmpH_taint H oSel (bl_pins (an := id) (fun _ _ h => h) [.s0, .s3, .s4])

end

end VG.Proof.RsaPss.RISCV64
