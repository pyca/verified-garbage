module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Open
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTOne
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Open
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Compare
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.InitCT
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamVerify
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.TextAbsorb
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesGcm.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Contract
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISC-V: `vg_aes_gcm_open` is constant time

Untrusted: everything here is checked by Lean. The entry as for `seal`
(`CTSeal.lean`), then `tag_len` (`s8`), public, and the two branches of
`tagLenOk`. Once the tag length is allowed, the data is decrypted only if
the tags are equal, which may differ between two runs only as the result
does (the contract's `pub`: whether it succeeds). The invariants of the
pieces up to that comparison carry what the rest of each run reaches
(`CT.seqG`, from `open_head`): the result in `s8`, which is then the same in
both runs.
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- Two runs of `c₁` carry what a further `R` reaches from them. -/
theorem CT.seqG {I J Z : State → Prop} {c₁ R c₂ : Prog isa} (h₁ : CT I c₁) (w : ∀ s, I s → WP isa c₁ s J)
    (h₂ : CT (fun s => J s ∧ WP isa R s Z) c₂) : CT (fun s => I s ∧ WP isa (.seq c₁ R) s Z) (.seq c₁ c₂) :=
  CT.seq (h₁.mono fun _ h => h.1) (fun s h => WP.mono (WP.forall_det (w s h.1) (P := fun _ : Unit => True)
    (Q := fun _ s' => WP isa R s' Z) fun _ _ => WP.seq_iff.mp h.2) fun _ h => ⟨h.1, h.2 () trivial⟩) h₂

theorem openRes_isSome {t : State} (hok : Spec.Gcm.tagLenOk (stackArg t 1).toNat = true) :
    (openRes t).isSome = decide (openTagOk t) := by
  have e : openRes t = if openTagOk t then
      some (Spec.Gcm.gctr (Spec.Gcm.ctxCiph t.mem (t.gpr .a0) (t.gpr .a1).toNat)
        (Spec.Gcm.inc32 (Spec.Gcm.j0 (Spec.Gcm.ctxH t.mem (t.gpr .a0)) (bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat)))
        (bytesAt t.mem (t.gpr .a6) (t.gpr .a7).toNat)) else none := by
    simp only [openRes, Spec.Gcm.openResult, hok, ite_true, Spec.Gcm.decryptWith]
  rw [e]
  by_cases h : openTagOk t
  · simp only [eq_true h, ite_true, decide_true, Option.isSome_some]
  · simp only [eq_false h, ite_false, decide_false, Option.isSome_none]

theorem openHead_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [])
    (.block [.addSp .t1 0, .load .d .t1 .t1 16]) h).isSome = true := ⟨_, by taint_decide⟩

theorem openRest_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint
    (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1])
    (.block (oneRest ++ ([.load .d .s8 .t1 8] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tagLenOk_taint' : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8]) tagLenOk h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp112_taint : ∃ h, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs [.s8, .s0]) (cmp 112) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem nil_taint (b : List Instr) (h : b = [.li .a0 0] ∨ b = [mov .s5 .s7] ∨ b = [mov .s8 .a0] ∨
    b = [mov .a0 .s8]) : ∃ hh, (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs []) (.block b) hh).isSome = true := by
  rcases h with rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `OneI`, with the tag's address `T` and length `TL` in `s9` and `s8`. -/
def OneO (c W sp : Addr) (R : Nat) (Np : Addr) (n : Nat) (Ad A D Ln T TL : BitVec 64) (s : State) : Prop :=
  OneI c W sp R Np n Ad A D Ln s ∧ s.gpr .s9 = T ∧ s.gpr .s8 = TL ∧ Covers [⟨T, TL.toNat⟩] (s.rd ++ s.wr)

section
variable {c W sp : Addr} {R : Nat} {Np : Addr} {n : Nat} {Ad A D Ln T TL : BitVec 64}

theorem OneO.frame {s s' : State} (h : OneO c W sp R Np n Ad A D Ln T TL s) {V : Reg → BitVec 64}
    (hV : ∀ r ∈ frozen, V r = s.gpr r) (he : Env V sp s') (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ {d : Nat}, 232 ≤ d ∧ d + 8 ≤ 248 → ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r) :
    OneO c W sp R Np n Ad A D Ln T TL s' :=
  ⟨h.1.frame hV he hrd hwr hsp hf hs, (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.1),
    (he.fr _ (by decide)).trans ((hV _ (by decide)).trans h.2.2.1), by rw [hrd, hwr]; exact h.2.2.2⟩

/-- `OneI` after a step that changes only `s8` among the registers it pins. -/
theorem OneI.self {s s' : State} (h : OneI c W sp R Np n Ad A D Ln s) (hg : ∀ r, r ≠ .s8 → s'.gpr r = s.gpr r)
    (hk : Keeps s s') : OneI c W sp R Np n Ad A D Ln s' := by
  obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h
  have q : ∀ r ∈ frozen, r ≠ .s8 → s'.gpr r = V r := fun r hr h19 => (hg r h19).trans (he.fr r hr)
  refine ⟨s'.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Env.self he hg hk, hN.of_eq hk.rd hk.wr hk.sp,
    hA.of_eq hk.rd hk.wr hk.sp, hD.of_eq hk.rd hk.wr hk.sp, by rw [hk.mem]; exact sa, by rw [hk.mem]; exact sd⟩
  · rw [q _ (by decide) (by decide), a]
  · rw [q _ (by decide) (by decide), b]
  · rw [q _ (by decide) (by decide), d]
  · rw [q _ (by decide) (by decide), e]
  · rw [q _ (by decide) (by decide), f]
  · rw [q _ (by decide) (by decide), i]
  · rw [q _ (by decide) (by decide), k]

/-- The result of the comparison in `s8`, for `b`. -/
abbrev Res (b : Bool) (s : State) : Prop := s.gpr .s8 = BitVec.ofNat 64 (if b then 1 else 0)

/-- The slots of the addresses are apart from what `oneTag 112` writes. -/
theorem slot_ot112 (L : Lay c (W + BitVec.ofNat 64 16) W) (hk : StkOk c (W + BitVec.ofNat 64 16) W sp) {d : Nat}
    (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ otFrame (W + BitVec.ofNat 64 16) W 112 sp, (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (a := 0) (n := 48) (by decide) (.inr ⟨by omega, by omega⟩)).symm.sub_right
      (by simpa using Region.sub_prefix (base := W + BitVec.ofNat 64 16) (show 48 ≤ 48 by decide))
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact hk.w.sub_left (Lay.wSub (by omega))

/-- The slots are apart from a block of `W` at `e ≥ 248`. -/
theorem slot_at {e : Nat} (he : 248 ≤ e) (he' : e + 16 ≤ 2560) {d : Nat} (hd : 232 ≤ d ∧ d + 8 ≤ 248) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 e, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact Lay.w_w (.inl (by omega)) (by omega) he'

variable (L : Lay c (W + BitVec.ofNat 64 16) W) (hR : R = 10 ∨ R = 12 ∨ R = 14)
  (hTd : (⟨T, TL.toNat⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 256, 16⟩) (t1 : 1 ≤ TL.toNat) (t16 : TL.toNat ≤ 16)
  (b : Bool)
include L hR hTd t1 t16

/-- `open` from `oneAad` on, once the tag length is allowed, with what the
comparison of the tags gives (`Res b`). -/
theorem openGood_ct : CT (fun s => (OneO c W sp R Np n Ad A D Ln T TL s ∧ s.gpr .s4 = Np ∧
    s.gpr .s5 = BitVec.ofNat 64 n) ∧ WP isa (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112)
      (.seq (.block [mov .s8 .a0]) (.block [])))))) s (Res b))
    (.seq oneAad (.seq (oneTag 112) (.seq recv (.seq (cmp 112) (.seq (.block [mov .s8 .a0])
      (.seq (.ite (.zero .s8) (.block []) oneCrypt) (.block [mov .a0 .s8]))))))) := by
  -- `oneAad`
  refine CT.seqG (J := fun s => OneO c W sp R Np n Ad A D Ln T TL s ∧ OneAbs c W A s)
    ((oneAad_ct L).mono fun s ⟨⟨hO, _⟩, h24, h25⟩ => ⟨hO, h24, h25⟩)
    (fun s ⟨hT, h24, h25⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    refine WP.mono (WP.with_rdwr (oneAad_ok (L.v a b d) (A := Ad) he rfl h24 h25 f (by rw [b, d]; exact hN)
      (by rw [b, d, i]; exact hA) (by rw [d]; exact sa))) fun s' ⟨oa, rd, wr, sp'⟩ =>
        ⟨hT.frame (fun r hr => (he.fr r hr).symm) oa.env rd wr sp' oa.frame
          (fun hd' => by rw [← d]; exact slot_j0 (L.v a b d) he.stk' hd'),
        blockAt s.mem (V .s2 + BitVec.ofNat 64 240), bytesAt s.mem Ad (V .s10).toNat,
        by rw [← a]; exact oa.hH, by rw [i, length_bytesAt], by rw [← b]; exact oa.abs⟩
  -- `oneTag 112`
  refine CT.seqG (J := OneO c W sp R Np n Ad A D Ln T TL) ((oneTag_ct L (.inr rfl) hR).mono fun s ⟨hT, _⟩ => hT.1)
    (fun s ⟨hT, H, x, hH, hl, hab⟩ => ?_) ?_
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have hk := he.stk'
    rw [a, b, d] at hk
    exact WP.mono (WP.with_rdwr (oneTag_ok (L.v a b d) (o := 112) (.inr rfl) (H := H) (a := x) (D := D) he e hR
      (by rw [a]; exact hH) (by rw [i]; exact hl) (by rw [b]; exact hab) (by rw [b, d, k]; exact hD.ok)
      (by rw [d]; exact sd)))
      fun s' ⟨ot, rd, wr, sp'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) ot.env rd wr sp'
        (by have := ot.frame; rw [b, d] at this; exact this) (fun hd' => slot_ot112 L hk hd')
  -- `recv`
  refine CT.seqG (J := OneO c W sp R Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := recv_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, a₁, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, a₂, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    have h20 : V .s9 = T := by rw [← he.fr _ (by decide), hT.2.1]
    exact WP.mono (recv_ok he (by rw [d]; exact L.wal) h19 t1 t16 (by rw [h20]; exact hT.2.2.2)
      (by rw [h20, d]; exact hTd))
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- `cmp 112`
  refine CT.seqG (J := OneO c W sp R Np n Ad A D Ln T TL) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := cmp112_taint
    refine CT.taint _ (fun s₁ s₂ ⟨⟨_, _, _, d₁, _, _, _, _, h₁, _⟩, _, b₁, _⟩
      ⟨⟨_, _, _, d₂, _, _, _, _, h₂, _⟩, _, b₂, _⟩ => ⟨h₁.sp.trans h₂.sp.symm, fun r hr => ?_⟩) hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [b₁, b₂]
    · rw [h₁.s0, h₂.s0, d₁, d₂]
  · obtain ⟨V, a, b, d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := hT.1
    have h19 : V .s8 = BitVec.ofNat 64 TL.toNat := by rw [← he.fr _ (by decide), hT.2.2.1]; simp
    exact WP.mono (cmp_ok he (by rw [d]; exact L.wal) (o := 112) (.inr rfl) h19 t1 t16)
      fun s' ⟨_, hf', g', k'⟩ => hT.frame (fun r hr => (he.fr r hr).symm) (he.keep (fun r hr => g' r
        (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide)) k'.sp k'.rd k'.wr) k'.rd k'.wr k'.sp hf'
        (fun hd' => by rw [d]; exact slot_at (by decide) (by decide) hd')
  -- the result into `s8`
  refine CT.seqG (J := OneI c W sp R Np n Ad A D Ln) ?_ (fun s hT => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [mov .s8 .a0] (.inr (.inr (.inl rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨⟨_, _, _, _, _, _, _, _, h₁, _⟩, _⟩ => ⟨h₁.sp, by simp⟩) hc
  · exact Steps.wp_mv fun s' u => WP.block_nil (hT.1.self u.other ⟨u.mem, u.rd, u.wr, u.sp⟩)
  -- the data decrypted only if the tags are equal, which both runs agree on
  have ev : ∀ s, OneI c W sp R Np n Ad A D Ln s ∧ WP isa (.block []) s (Res b) →
      isa.eval (.zero .s8) s = some (decide ((if b then 1 else 0) = 0)) := fun s h =>
    eval_zero (WP.block_nil_iff.mp h.2) (by split <;> decide)
  refine CT.seq (J := fun s => s.gpr .s0 = W ∧ s.sp = sp)
    (CT.ite _ ev (fun _ => CT.skip) (fun _ => (oneCrypt_ct L hR).mono fun s h => h.1)) (fun s h => ?_) ?_
  · obtain ⟨V, a, b', d, e, f, i, k, he, hN, hA, hD, sa, sd⟩ := h.1
    refine WP.ite _ (ev s h) (fun _ => WP.block_nil_iff.mpr ⟨by rw [he.s0, d], he.sp⟩) (fun _ => ?_)
    exact WP.mono (oneCrypt_ok (L.v a b' d) he e hR (by rw [a, b', d, k]; exact hD) (by rw [d]; exact sd) rfl)
      fun s' oc => ⟨by rw [oc.env.s0, d], oc.env.sp⟩
  · obtain ⟨_, hc⟩ := nil_taint [mov .a0 .s8] (.inr (.inr (.inr rfl)))
    exact CT.taintEq _ (fun _ => 0) sp (fun s ⟨_, hsp⟩ => ⟨hsp, by simp⟩) hc

end

/-- `mv s5, s7` after `tagLenOk`: the entry's registers again. -/
theorem mov25_so1 {W T : Addr} {t₀ s₂ s₃ s₄ : State} (h2 : SO1 W T t₀ s₂)
    (g : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s₂.gpr r) (k : Keeps s₂ s₃) (u : Steps.Upd s₃ s₄ .s5 (s₃.gpr .s7)) :
    SO1 W T t₀ s₄ ∧ s₄.gpr .s8 = s₂.gpr .s8 := by
  refine ⟨h2.keep (fun r h0 _ => ?_) ⟨by rw [u.mem, k.mem], by rw [u.rd, k.rd], by rw [u.wr, k.wr],
    by rw [u.sp, k.sp]⟩, by rw [u.other _ (by decide), g _ (by decide) (by decide)]⟩
  by_cases e : r = .s5
  · subst e
    rw [u.gpr, g _ (by decide) (by decide), h2.s7, h2.s5]
  · rw [u.other r e, g r h0 e]

/-- After the entry (and `s5` restored), what the pieces need. -/
theorem open_one {t₀ s : State} (h : openPre t₀) (h1 : SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s)
    (h19 : s.gpr .s8 = stackArg t₀ 1) :
    OneO (t₀.gpr .a0) (stackArg t₀ 2) t₀.sp (t₀.gpr .a1).toNat (t₀.gpr .a2) (t₀.gpr .a3).toNat (t₀.gpr .a4)
        (t₀.gpr .a5) (t₀.gpr .a6) (t₀.gpr .a7) (stackArg t₀ 0) (stackArg t₀ 1) s ∧
      s.gpr .s4 = t₀.gpr .a2 ∧ s.gpr .s5 = BitVec.ofNat 64 (t₀.gpr .a3).toNat := by
  have hk₀ := openStk h
  obtain ⟨hrd, hwr, dcd, dcW, dnd, dnW, dad, daW, ddt, ddW, ddA, dtW, dWA, fc, fn, fa, fd, ft, fW, fsp, hR, hstk,
    -⟩ := id h
  have hC : Covers [⟨t₀.gpr .a0, 256⟩] (t₀.rd ++ t₀.wr) := covers_mem (List.mem_append_left _ (by rw [hrd]; simp))
  have hW : Covers [⟨stackArg t₀ 2, 2560⟩] t₀.wr := by rw [hwr]; exact covers_mem (by simp)
  have hk₁ := h1.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨t₀.gpr .a6, (t₀.gpr .a7).toNat⟩] s.wr := by
    rw [hk₁.wr, hwr]; exact covers_mem (by simp)
  refine ⟨⟨⟨s.gpr, h1.s2, h1.s1, h1.s0, by rw [h1.s3]; exact toN, by rw [h1.s7]; exact toN, h1.s10, h1.s11,
    one_env h1 hC hW hk₀, ?_, ?_, ⟨⟨covers_left hDw, (t₀.gpr .a7).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩, hDw, dcd⟩,
    h1.aad, h1.dat⟩, h1.s9, h19, ?_⟩, h1.s4, by rw [h1.s5]; exact toN⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a3).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp)),
      (t₀.gpr .a5).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW, by rw [hk₁.sp]; exact hstk.buf (by simp)⟩
  · rw [hk₁.rd, hk₁.wr]; exact covers_mem (List.mem_append_left _ (by rw [hrd]; simp))

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩, qres⟩ := hq
  have h₁' : openPre σ₁ := h₁
  obtain ⟨_, _, _, dcW, _, _, _, _, _, _, _, dtW, _, fc, _, _, _, _, fW, _, hR, _, ca, wa⟩ := h₁'
  let I₀ : State → Prop := fun s => openPre s ∧ s.gpr .a0 = σ₁.gpr .a0 ∧ s.gpr .a1 = σ₁.gpr .a1 ∧
    s.gpr .a2 = σ₁.gpr .a2 ∧ s.gpr .a3 = σ₁.gpr .a3 ∧ s.gpr .a4 = σ₁.gpr .a4 ∧ s.gpr .a5 = σ₁.gpr .a5 ∧
    s.gpr .a6 = σ₁.gpr .a6 ∧ s.gpr .a7 = σ₁.gpr .a7 ∧ s.sp = σ₁.sp ∧ stackArg s 0 = stackArg σ₁ 0 ∧
    stackArg s 1 = stackArg σ₁ 1 ∧ stackArg s 2 = stackArg σ₁ 2 ∧ (openRes s).isSome = (openRes σ₁).isSome
  refine ⟨I₀, ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨h₂, q3.symm, q4.symm,
    q5.symm, q6.symm, q7.symm, q8.symm, q9.symm, q10.symm, qsp.symm, (qa 0 (by decide)).symm,
    (qa 1 (by decide)).symm, (qa 2 (by decide)).symm, (qres hR).symm⟩, ?_⟩
  -- the entry: its head loads `W` from a public address, the rest saves through it
  let J₁ : State → Prop := fun s => ∃ t₀, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s ∧
    s.gpr .s8 = stackArg t₀ 1
  refine CT.seq (J := J₁) ?_ (fun s hs => WP.mono (openEntry_wp hs.1) fun s' ⟨a, b⟩ => ⟨s, hs, a, b⟩) ?_
  · let v : Reg → BitVec 64 := fun r => if r = .t1 then stackArg σ₁ 2 else σ₁.gpr r
    have hl : openEntry = [.addSp .t1 0, .load .d .t1 .t1 16] ++ (oneRest ++ ([.load .d .s8 .t1 8] : List Instr)) := by
      rw [openEntry, oneEntry_eq, List.append_assoc]
    rw [hl]
    refine RelCT.block_append (CT.seq (J := fun s => s.sp = σ₁.sp ∧
      ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1], s.gpr r = v r) ?_ ?_ ?_)
    · obtain ⟨_, hc⟩ := openHead_taint
      exact CT.taintEq _ σ₁.gpr σ₁.sp (fun s ⟨_, _, _, _, _, _, _, _, _, esp, _⟩ => ⟨esp, by simp⟩) hc
    · intro s ⟨hs, e3, e4, e5, e6, e7, e8, e9, e10, esp, _, _, ea2, _⟩
      have hA : Covers [args s 3] (s.rd ++ s.wr) := covers_mem (List.mem_append_left _ (by rw [hs.1]; simp))
      have hsa : s.sp.toNat % 16 = 0 := (openStk hs).al
      refine WP.mono (oneA_ok (W := stackArg s 2) (.inr rfl) hsa (args_in hA (by decide) (i := 2) (by decide)) rfl)
        fun sA ⟨a12, gA, kA⟩ => ⟨kA.sp.trans esp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [v, a12, ea2, e3, e4, e5, e6, e7, e8, e9, e10, gA]
    · obtain ⟨_, hc⟩ := openRest_taint
      exact CT.taintEq _ v σ₁.sp (fun s h => h) hc
  -- the tag length
  let ok := Spec.Gcm.tagLenOk (stackArg σ₁ 1).toNat
  let J₂ : State → Prop := fun s => ∃ t₀ s₂, I₀ t₀ ∧ SO1 (stackArg t₀ 2) (stackArg t₀ 0) t₀ s₂ ∧
    s₂.gpr .s8 = stackArg t₀ 1 ∧ (∀ r, r ≠ .t0 → r ≠ .s5 → s.gpr r = s₂.gpr r) ∧ Keeps s₂ s ∧
    s.gpr .s5 = BitVec.ofNat 64 (if ok then 1 else 0)
  refine CT.seq (J := J₂) ?_ (fun s ⟨t₀, ht, h1, h19⟩ => ?_) ?_
  · obtain ⟨_, hc⟩ := tagLenOk_taint'
    exact CT.taintEq _ (fun _ => stackArg σ₁ 1) σ₁.sp (fun s ⟨t₀, ht, h1, h19⟩ =>
      ⟨h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1, by simp [h19, ht.2.2.2.2.2.2.2.2.2.2.2.1]⟩) hc
  · have h19' : s.gpr .s8 = BitVec.ofNat 64 (stackArg t₀ 1).toNat := by rw [h19]; simp
    refine WP.mono (tagLenOk_ok h19' (stackArg t₀ 1).isLt) fun s' ⟨h25, g, k⟩ =>
      ⟨t₀, s, ht, h1, h19, g, k, ?_⟩
    rw [h25, ht.2.2.2.2.2.2.2.2.2.2.2.1]
  -- the two branches, then `restore`
  have ev : ∀ s, J₂ s → isa.eval (.zero .s5) s = some (decide ((if ok then 1 else 0) = 0)) :=
    fun s ⟨_, _, _, _, _, _, _, h25⟩ => eval_zero h25 (by split <;> decide)
  have L₀ := oneLay fc fW dcW ca wa
  refine CT.seq (J := fun s => s.gpr .s0 = stackArg σ₁ 2 ∧ s.sp = σ₁.sp) (CT.ite _ ev (fun _ => ?_) (fun hb => ?_))
    (fun s hs => ?_) ?_
  · obtain ⟨_, hc⟩ := nil_taint [.li .a0 0] (.inl rfl)
    exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
      ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
  · have hok : ok = true := by
      cases e : ok
      · simp [e] at hb
      · rfl
    obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
    refine CT.seq ?_ (fun s ⟨t₀, s₂, ht, h1, h19, g, k, _⟩ => ?_)
      (openGood_ct (sp := σ₁.sp) (Np := σ₁.gpr .a2) (n := (σ₁.gpr .a3).toNat) (Ad := σ₁.gpr .a4) (A := σ₁.gpr .a5)
        (D := σ₁.gpr .a6) (Ln := σ₁.gpr .a7) L₀ hR (dtW.sub_right (Lay.wSub (by decide))) t1 t16
        (openRes σ₁).isSome)
    · obtain ⟨_, hc⟩ := nil_taint [mov .s5 .s7] (.inr (.inl rfl))
      exact CT.taintEq _ (fun _ => 0) σ₁.sp (fun s ⟨t₀, s₂, ht, h1, _, _, k, _⟩ =>
        ⟨k.sp.trans (h1.keeps.sp.trans ht.2.2.2.2.2.2.2.2.2.1), by simp⟩) hc
    · obtain ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩ := ht
      refine Steps.wp_mv fun s₄ u => WP.block_nil ?_
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      have o := open_one hpre h4 (h19₄.trans h19)
      rw [e3, e4, e5, e6, e7, e8, e9, e10, ea0, ea1, ea2, esp] at o
      refine ⟨o, open_head hpre h4 (h19₄.trans h19) hok₀ (T := .block []) fun s₉ om => WP.block_nil_iff.mpr ?_⟩
      show s₉.gpr .s8 = _
      rw [om.s8, ← eres, openRes_isSome hok₀]
      by_cases hx : openTagOk t₀
      · simp only [eq_true hx, ite_true, decide_true]
      · simp only [eq_false hx, ite_false, decide_false, Bool.false_eq_true]
  · obtain ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩ := hs
    refine WP.ite _ (ev s ⟨t₀, s₂, ⟨hpre, e3, e4, e5, e6, e7, e8, e9, e10, esp, ea0, ea1, ea2, eres⟩, h1, h19, g, k, h25⟩)
      (fun ht => ?_) (fun hf => ?_)
    · exact Steps.wp_li (imm := 0) (by decide) fun s' u => WP.block_nil
        ⟨by rw [u.other _ (by decide), g _ (by decide) (by decide), h1.s0, ea2],
          by rw [u.sp, k.sp, h1.keeps.sp, esp]⟩
    · have hok : ok = true := by
        cases e : ok
        · simp [e] at hf
        · rfl
      have hok₀ : Spec.Gcm.tagLenOk (stackArg t₀ 1).toNat = true := by rw [ea1]; exact hok
      refine WP.seq (Steps.wp_mv fun s₄ u => WP.block_nil ?_)
      obtain ⟨h4, h19₄⟩ := mov25_so1 h1 g k u
      exact WP.mono (open_good hpre h4 (h19₄.trans h19) hok₀) fun s' oo =>
        ⟨by rw [oo.s0, ea2], by rw [oo.sp, esp]⟩
  · obtain ⟨_, hc⟩ := restore_taint
    exact CT.taintEq _ (fun _ => stackArg σ₁ 2) σ₁.sp (fun s ⟨e31, esp⟩ => ⟨esp, by simp [e31]⟩) hc

end VG.Proof.AesGcm.RISCV64
