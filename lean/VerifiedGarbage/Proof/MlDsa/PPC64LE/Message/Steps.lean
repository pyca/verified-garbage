module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Pieces
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.Message.Common

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message`: the steps

As Ed448's whole functions on this target (`Proof/Ed448/PPC64LE/Whole/`),
whose invariant `Inv` (`Proof/Ed25519/PPC64LE/Whole/Frame.lean`) they share:
the registers `rs` and the link register saved at `oSV(E)`, then the
arguments moved into `rs` (`setup_ok`, by `movs_ok`); the two bytes
`0 ‖ ctx_len` stored at `oHdr(E)` (`hdr_ok`); a hash, or any step that keeps
the callee-saved registers and writes within the body's regions, apart from
the slots, keeps `Inv` (`inv_kept`); the branch on `ctx_len >> 8`
(`wp_ite`, `shr8_zero`); and the moves of a call's arguments (`args4_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Impl.Ed25519.PPC64LE.Whole (saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea save_ok saveG)
open VG.Impl.Sha3.PPC64LE.Pieces (Piece Len)
open VG.Proof.Sha3.PPC64LE.Pieces (Kept PieceOk)

/-- `mov`s from registers that none of them writes, to distinct registers. -/
theorem movs_ok : ∀ (ms : List (Reg × Reg)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ ms.map Prod.fst) → (ms.map Prod.fst).Nodup →
    (∀ u, u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      (∀ p ∈ ms, u.gpr p.1 = s.gpr p.2) → (∀ r, r ∉ ms.map Prod.fst → u.gpr r = s.gpr r) →
      WP isa (.block rest) u Q) →
    WP isa (.block (ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  intro ms
  induction ms with
  | nil => exact fun _ _ k => k _ rfl rfl rfl rfl (fun _ h => absurd h List.not_mem_nil) fun _ _ => rfl
  | cons p ms ih =>
    intro s rest Q hs hn k
    obtain ⟨d, n⟩ := p
    have hn' := List.nodup_cons.mp hn
    have h0 := hs (d, n) List.mem_cons_self
    simp only [List.map_cons, List.cons_append]
    refine wp_addi h0.1 (by decide) fun u hu => ih (fun q hq => ⟨(hs q (List.mem_cons_of_mem _ hq)).1,
      fun h => (hs q (List.mem_cons_of_mem _ hq)).2 (List.mem_cons_of_mem _ h)⟩) hn'.2
      fun u' m' rd' wr' sp' hm ho => k u' (m'.trans hu.mem) (rd'.trans hu.rd) (wr'.trans hu.wr) (sp'.trans hu.sp)
        (fun q hq => ?_) fun r hr => ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hn'.1, hu.gpr, BitVec.add_zero]
      · have hq2 : q.2 ≠ d := fun e => (hs q (List.mem_cons_of_mem _ hq)).2 (e ▸ List.mem_cons_self)
        rw [hm q hq, hu.other _ hq2]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hu.other r hr.1]

/-- The saves at `o(F)` (`F` in `f`), then the moves `ms` into the registers `rs`, which hold `v`: the
invariant holds after them. -/
theorem setup_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {ms : List (Reg × Reg)} {v : Reg → BitVec 64}
    {W : List Region} {rest : List Instr} {Q : State → Prop} (hf0 : f ≠ .r0)
    (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (hW : ∃ R ∈ W, Region.Sub (slotArea (s.gpr f) o rs) R) (hms : ms.map Prod.fst = rs)
    (hsrc : ∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ rs) (hnd : rs.Nodup) (hv : ∀ p ∈ ms, v p.1 = s.gpr p.2)
    (k : ∀ u, Inv s (s.gpr f) o rs v W u → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine save_ok hf0 hfits hlo hin fun u hu _ hsv hfr => ?_
  refine movs_ok ms (fun p hp => ⟨(hsrc p hp).1, hms ▸ (hsrc p hp).2⟩) (hms ▸ hnd)
    fun u' m' rd' wr' sp' hm ho => k u' ⟨rd'.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, fun r hr => ?_,
      fun r hr hn => ?_, m' ▸ hsv, m' ▸ hfr.sub fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hW⟩
  · rw [← hms] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [hm p hp, hv p hp, hu.gpr _ (by simpa using (hsrc p hp).1)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simpa using fun e => (by revert hr; rw [e]; decide : False))]

/-- A step that keeps the callee-saved registers, writing within `W` and apart from the slots. -/
theorem inv_kept {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hk : Kept Wc t t')
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' :=
  h.step hrs hk.rd hk.wr hk.sp hk.cs hk.frame hsub hd

/-- `Inv` from a state that agrees with `s` on what it records. -/
theorem inv_rebase {s u t : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W : List Region}
    (h : Inv u F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsp : u.sp = s.sp) (hlr : u.lr = s.lr) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    Inv s F o rs v W t where
  rd := h.rd.trans hrd
  wr := h.wr.trans hwr
  sp := h.sp.trans hsp
  regs := h.regs
  pres r hr hn := (h.pres r hr hn).trans (hg r hr)
  saved p hp := by
    rw [h.saved p hp]
    obtain ⟨⟨r, i⟩, hm', rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, hlt, he⟩ := List.mem_zipIdx hm'
    have hm'' : r ∈ rs ++ [.r0] := by rw [he]; exact List.getElem_mem _
    simp only [saveG]
    by_cases h0 : r = .r0
    · simp only [h0, ↓reduceIte, hlr]
    · have hr : r ∈ rs := by
        rcases List.mem_append.mp hm'' with h' | h'
        · exact h'
        · exact absurd (List.mem_singleton.mp h') h0
      simp only [h0, ↓reduceIte, hg r (hrs r hr)]
  frame := hm ▸ h.frame

/-! ## Pieces and regions -/

theorem pieceOk_of {N : Nat} {t : State} {sc : Addr} {p : Piece} {R : Region} (hR : p.R t.gpr = R)
    (hb : p.base ∈ preserved) (ho : p.off < 2 ^ 15) (hl : p.len.Ok) (hc : PPC64LE.Covers [R] (t.rd ++ t.wr))
    (hd : R.Disjoint ⟨sc, N⟩) (hb' : (below t.sp 48).Disjoint R) : PieceOk N sc t p :=
  ⟨hb, ho, hl, hR ▸ hc, hR ▸ hd, hR ▸ hb'⟩

theorem cov_in {ws : List Region} {P : Addr} {k d n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : d + n ≤ k) :
    PPC64LE.Covers [⟨P + BitVec.ofNat 64 d, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, d, rfl, h⟩

theorem cov_in0 {ws : List Region} {P : Addr} {k n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : n ≤ k) :
    PPC64LE.Covers [⟨P, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem cov_rd {rd wr ws : List Region} (h : PPC64LE.Covers ws rd) : PPC64LE.Covers ws (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## The header -/

/-- The memory after the two bytes `0 ‖ c` at `a`. -/
abbrev hdrMem (m : Mem) (a : Addr) (c : BitVec 64) : Mem :=
  (m.writeW a ((0 : BitVec 64).setWidth 8)).writeW (a + BitVec.ofNat 64 1) (c.setWidth 8)

theorem hdrMem_bytes (m : Mem) (a : Addr) (c : Nat) :
    Spec.Sha3.bytesAt (hdrMem m a (BitVec.ofNat 64 c)) a 2 = [0, BitVec.ofNat 8 c] := by
  have hne : a ≠ a + BitVec.ofNat 64 1 := fun e => by
    have := congrArg (fun x => (x - a).toNat) e
    simp only [BitVec.sub_self, Offset.add_sub_cancel_left] at this
    exact absurd this (by decide)
  simp only [Spec.Sha3.bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil,
    show a + BitVec.ofNat 64 0 = a from BitVec.add_zero a, hdrMem]
  rw [Proof.MlDsa.Message.byte_writeW_self, Proof.MlDsa.Message.byte_writeW_other _ hne,
    Proof.MlDsa.Message.byte_writeW_self]
  simp only [List.cons.injEq, and_true]
  refine ⟨rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem hdrMem_frame (m : Mem) (a : Addr) (c : BitVec 64) : Frame [⟨a, 2⟩] m (hdrMem m a c) := by
  refine Frame.write (Frame.write (Frame.refl _ _) List.mem_cons_self _ ?_) List.mem_cons_self _ ?_
  · simpa using Offset.contains_base a (d := 0) (n := 1) (k := 2) (by decide) (by decide)
  · exact Offset.contains_base a (d := 1) (n := 1) (k := 2) (by decide) (by decide)

/-- `0 ‖ c` at `o(f)` (`c` in `cr`). -/
theorem hdr_ok {s : State} {f cr : Reg} (hf0 : f ≠ .r0) (hc0 : cr ≠ .r0) {o : Nat} (ho : o + 1 < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr f + BitVec.ofNat 64 o) 1) (hw1 : InRegions s.wr (s.gpr f + BitVec.ofNat 64 (o + 1)) 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, t.mem = hdrMem s.mem (s.gpr f + BitVec.ofNat 64 o) (s.gpr cr) → t.rd = s.rd → t.wr = s.wr →
      t.sp = s.sp → (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block ([.li .r0 0, .stb .r0 f o, .stb cr f (o + 1)] ++ is)) s Q := by
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun u₁ h₁ => ?_
  have g : u₁.gpr f = s.gpr f := h₁.other _ hf0
  refine wp_stb hf0 (by omega) rfl (by rw [h₁.wr, g]; exact hw) fun u₂ h₂ => ?_
  refine wp_stb hf0 ho rfl (by rw [h₂.wr, h₁.wr, h₂.gpr, g]; exact hw1) fun u₃ h₃ => ?_
  refine k u₃ ?_ (by rw [h₃.rd, h₂.rd, h₁.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr]) (by rw [h₃.sp, h₂.sp, h₁.sp])
    fun r hr => by rw [h₃.gpr, h₂.gpr, h₁.other _ hr]
  rw [h₃.mem, h₂.gpr, h₂.mem, h₁.mem, g, h₁.gpr, h₁.other _ hc0, hdrMem, Proof.MlDsa.Message.add_add]
  rfl

/-! ## The branch on the length of the context -/

theorem wp_ite {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (ht : b = true → WP isa th s Q) (he : b = false → WP isa el s Q) :
    WP isa (.ite c th el) s Q := by
  cases b
  · obtain ⟨t, s', e, q⟩ := he rfl; exact ⟨_, s', Exec.iteF hc e, q⟩
  · obtain ⟨t, s', e, q⟩ := ht rfl; exact ⟨_, s', Exec.iteT hc e, q⟩

theorem shr8_zero (x : BitVec 64) : (x >>> 8 == 0#64) = decide (x.toNat < 256) := by
  have h : (x >>> 8).toNat = x.toNat / 256 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hx : x.toNat < 256
  · simp only [hx, decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq (by rw [h, Nat.div_eq_of_lt hx]; rfl)
  · simp only [hx, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [h] at this
    exact hx (by simp at this; omega)

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp [eval, State.read, Size.bits]

end VG.Proof.MlDsa.PPC64LE.Message
