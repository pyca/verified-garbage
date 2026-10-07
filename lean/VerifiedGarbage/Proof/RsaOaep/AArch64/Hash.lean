import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSAES-OAEP on AArch64: calling the streaming hash functions

As on x86-64 (`Proof/RsaOaep/X86_64/Hash.lean`): the streaming `init`,
`update` and `finalize` of a hash function (a `StreamOK`,
`Proof/Pbkdf2/Md/AArch64/Calls.lean`), called from the frame on the state at
`scratch + oSt`, with the working space at `scratch + oW` and the digest to
`scratch + o`: what each leaves of the frame and the working space (`Lay`,
`Rep`, with the ranges it writes read again, and `Step`), and what it
computes.

`Step F S ws t t'`: from `t` to `t'`, the regions, the stack pointer, the
callee-saved registers but `x30` and the preserved vector registers stay,
and memory changes only in the frame, our working space, the 16 bytes
below the frame and the regions `ws`.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Proof.Pbkdf2.Md.AArch64.Calls (StreamOK After VecKept init_call upd_call fin_call UpdArgs FinArgs)

/-- What every piece keeps. -/
structure Step (F S : Addr) (ws : List Region) (t t' : State) : Prop where
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r
  vec : VecKept t t'
  frame : Frame (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: ws) t.mem t'.mem

theorem Step.refl (F S : Addr) (ws : List Region) (t : State) : Step F S ws t t :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Step.trans {F S : Addr} {ws : List Region} {t u w : State} (h : Step F S ws t u) (h' : Step F S ws u w) :
    Step F S ws t w :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, fun r hr h30 => (h'.cs r hr h30).trans (h.cs r hr h30),
    h.vec.trans h'.vec, h.frame.trans h'.frame⟩

theorem preserved_cases {P : Reg → Prop} (h19 : P .x19) (h20 : P .x20) (h21 : P .x21) (h22 : P .x22)
    (h23 : P .x23) (h24 : P .x24) (h25 : P .x25) (h26 : P .x26) (h27 : P .x27) (h28 : P .x28) (h30 : P .x30) :
    ∀ r ∈ preserved, P r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A block that keeps memory, the regions, `sp`, the vector registers and
the callee-saved registers. -/
theorem Step.blk {F S : Addr} (ws : List Region) {t t' : State} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hv : t'.v = t.v) (hcs : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hm : t'.mem = t.mem) : Step F S ws t t' :=
  ⟨hrd, hwr, hsp, hcs, fun r _ => by rw [hv], by rw [hm]; exact Frame.refl _ _⟩

/-- The callee-saved registers, unchanged by a block that writes none. -/
macro "cs_rfl" : term => `(preserved_cases (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

/-- `Step` of a block that keeps memory and writes no callee-saved register. -/
macro "blk_step" : term => `(Step.blk _ rfl rfl rfl rfl cs_rfl rfl)

/-- Closes what remains of a block's run: facts reduced to `True`, `Step`,
closed equalities, and the callee-saved registers. -/
macro "oaep_fin" : tactic =>
  `(tactic| (and_intros <;> first | trivial | exact blk_step | exact cs_rfl | decide))

/-- A byte store in our working space keeps `Step`'s frame. -/
theorem frame_wb {F S : Addr} {ws : List Region} {m m' : Mem}
    (h : Frame (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: ws) m m') {o : Nat} (ho : o < oRsa) (v : BitVec (8 * 1)) :
    Frame (⟨F, frameBytes⟩ :: ⟨S, oRsa⟩ :: retR F :: ws) m (m'.write (off S o) 1 v) :=
  h.write (List.mem_cons_of_mem _ (List.mem_cons_self ..)) v (cS S (by omega))

/-- A step in fewer regions. -/
theorem Step.mono {F S : Addr} {ws ws' : List Region} {t u : State} (h : Step F S ws t u)
    (hs : ∀ r ∈ ws, r ∈ ws') : Step F S ws' t u :=
  ⟨h.rd, h.wr, h.sp, h.cs, h.vec, h.frame.mono fun r hr => by
    simp only [List.mem_cons] at hr ⊢
    rcases hr with h | h | h | h
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl h)), .inr (.inr (.inr (hs r h)))]⟩

/-- A call's `After`, writing ranges of our working space. -/
theorem Step.of_after {t t' : State} {F S : Addr} (L : Lay t F S) {rgs : List (Nat × Nat)}
    (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa) (A : After t (regs S rgs) t') (ws : List Region) : Step F S ws t t' :=
  ⟨A.rd, A.wr, A.sp, A.cs, A.vec, A.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub_base S (hrg p hp)⟩
    · rw [List.mem_singleton.mp hr, L.sp]
      exact ⟨retR F, by simp, fun _ h => h⟩⟩

/-- What a call leaves of the frame: `Lay`, and the view of memory with the
ranges `rgs` it may write read again. -/
theorem Lay.after_call {t t' : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (A : After t (regs S rgs) t') :
    Lay t' F S ∧ Rep t'.mem F S (fun o => if inR rgs o then t'.mem (off S o) else V o) W := by
  have hF : Frame (regs S rgs ++ [retR F]) t.mem t'.mem := by have := A.frame; rw [L.sp] at this; exact this
  have R' := R.frame L.geo hrg hF
  refine ⟨L.congr A.sp A.wr ?_, R'⟩
  rw [show sScr = 8 * 12 from rfl, R'.fr 12 (by decide), R.fr 12 (by decide)]

variable {G : Stream} (hG : StreamOK G)

include hG in
theorem sizes : G.S ≤ 256 ∧ G.F ≤ 64 ∧ hG.Wb ≤ 1072 ∧ G.D ≤ G.F ∧ 0 < G.D :=
  ⟨hG.hSB, hG.hF, by have := hG.hWb; have := hG.hW; omega, hG.hDF, hG.hD0⟩

/-! ## `init` -/

include hG in
theorem init_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) (h0 : t.gpr .x0 = off S oSt) (ws : List Region) :
    WP isa (.call G.initN G.initC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S)] o then t'.mem (off S o) else V o) W ∧
      hG.SH.Repr t'.mem (off S oSt) [] := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have hr : ∀ p ∈ [(oSt, G.S)], p.1 + p.2 ≤ oRsa := by simp only [List.mem_singleton]; rintro p rfl; exact h1
  refine init_call hG h0 (L.cov h1) fun t' A hrep => ?_
  obtain ⟨L', R'⟩ := L.after_call R hr A
  exact ⟨L', Step.of_after L hr A ws, R', hrep⟩

/-! ## `update` -/

include hG in
/-- `update`'s arguments for the `len` bytes at `scratch + a`. -/
theorem updArgs_of {t : State} {F S : Addr} (L : Lay t F S) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S a) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) : UpdArgs hG t (off S oSt) (off S a) (off S oW) len := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  exact { x0 := h0, x2 := h2
          x3 := by rw [h3, BitVec.toNat_ofNat]; unfold oRsa at ha; omega
          x4 := h4
          cd := Covers.right (L.cov ha)
          cw := Covers.pair (L.cov h1) (L.cov h2')
          st_sc := sdis S (Or.inl hsw) h1 h2'
          d_st := sdis S hda ha h1
          d_sc := sdis S hwa ha h2'
          sp16 := L.sp16
          stk_st := L.stk h1, stk_d := L.stk ha, stk_sc := L.stk h2' }

include hG in
/-- `update` of the state with the `len` bytes at `scratch + a`, from the
arguments in `x0`, `x2`, `x3`, `x4`. -/
theorem upd_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {a len : Nat} (ha : a + len ≤ oRsa)
    (hda : a + len ≤ oSt ∨ oSt + G.S ≤ a) (hwa : a + len ≤ oW ∨ oW + hG.Wb ≤ a)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S a) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) (ws : List Region) :
    WP isa (.call G.updN G.updC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ (List.range len).map fun i => V (a + i))) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hr : ∀ p ∈ [(oSt, G.S), (oW, hG.Wb)], p.1 + p.2 ≤ oRsa := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption
  refine upd_call hG (updArgs_of hG L ha hda hwa h0 h2 h3 h4) fun t' A hrep => ?_
  obtain ⟨L', R'⟩ := L.after_call R hr A
  refine ⟨L', Step.of_after L hr A ws, R', fun m hm hc => ?_⟩
  have e : Spec.Sha256.bytesAt t.mem (off S a) len = (List.range len).map fun i => V (a + i) := by
    simp only [Spec.Sha256.bytesAt]
    exact List.map_congr_left fun i hi => by
      show t.mem (off (off S a) i) = _
      rw [off_off]; exact R.scr _ (by have := List.mem_range.mp hi; omega)
  rw [← e]; exact hrep m hm hc

/-! ## `finalize` -/

include hG in
/-- `finalize`'s arguments for the digest to `scratch + o`. -/
theorem finArgs_of {t : State} {F S : Addr} (L : Lay t F S) {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S o) (h3 : t.gpr .x3 = off S oW) :
    FinArgs hG t (off S oSt) (off S o) (off S oW) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have h3' : o + G.F ≤ oRsa := by unfold oSt oW oRsa at *; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  exact { x0 := h0, x2 := h2, x3 := h3
          cw := Covers.cons (L.cov h1) (Covers.pair (L.cov h3') (L.cov h2'))
          st_o := sdis S (by unfold oSt oW at *; omega) h1 h3'
          st_sc := sdis S (Or.inl hsw) h1 h2'
          o_sc := sdis S (by unfold oSt oW at *; omega) h3' h2'
          sp16 := L.sp16
          stk_st := L.stk h1, stk_o := L.stk h3', stk_sc := L.stk h2' }

include hG in
/-- `finalize` of the state to `scratch + o`, from the arguments in `x0`,
`x2`, `x3`. -/
theorem fin_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {o : Nat} (ho : o + 64 ≤ oSt ∨ (oSt + 256 ≤ o ∧ o + 64 ≤ oW))
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = off S o) (h3 : t.gpr .x3 = off S oW) (ws : List Region) :
    WP isa (.call G.finN G.finC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun x => if inR [(oSt, G.S), (o, G.F), (oW, hG.Wb)] x then t'.mem (off S x) else V x) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        ∀ i < G.D, t'.mem (off S (o + i)) = (hG.SH.H.hash m).getD i 0) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have h3' : o + G.F ≤ oRsa := by unfold oSt oW oRsa at *; omega
  have hr : ∀ p ∈ [(oSt, G.S), (o, G.F), (oW, hG.Wb)], p.1 + p.2 ≤ oRsa := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl) <;> with_reducible assumption
  refine fin_call hG (finArgs_of hG L ho h0 h2 h3) fun t' A hrep => ?_
  obtain ⟨L', R'⟩ := L.after_call R hr A
  refine ⟨L', Step.of_after L hr A ws, R', fun m hm hl hc i hi => ?_⟩
  have e := hrep m hm hl hc
  rw [← e, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show i < G.F by omega),
    Option.map_some, Option.getD_some, off_off]

include hG in
/-- `update`'s arguments for the `len` bytes at `d`, outside our working
space, the frame and the stack the call uses. -/
theorem updExtArgs_of {t : State} {F S : Addr} (L : Lay t F S) {d : Addr} {len : Nat} (hlen : len < 2 ^ 64)
    (hcd : Covers [⟨d, len⟩] (t.rd ++ t.wr)) (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩)
    (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = d) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) : UpdArgs hG t (off S oSt) d (off S oW) len := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hsw : oSt + G.S ≤ oW := by unfold oSt oW; omega
  exact { x0 := h0, x2 := h2
          x3 := by rw [h3, BitVec.toNat_ofNat]; omega
          x4 := h4
          cd := hcd
          cw := Covers.pair (L.cov h1) (L.cov h2')
          st_sc := sdis S (Or.inl hsw) h1 h2'
          d_st := hds.sub_right (Offset.sub_base S h1)
          d_sc := hds.sub_right (Offset.sub_base S h2')
          sp16 := L.sp16
          stk_st := L.stk h1, stk_d := by rw [L.sp]; exact hdk, stk_sc := L.stk h2' }

include hG in
/-- `update` of the state with the `len` bytes at `d`, outside our working
space, the frame and the stack the call uses. -/
theorem updExt_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {d : Addr} {len : Nat} (hlen : len < 2 ^ 64)
    (hcd : Covers [⟨d, len⟩] (t.rd ++ t.wr)) (hds : Region.Disjoint ⟨d, len⟩ ⟨S, oRsa⟩)
    (hdk : (below F 16).Disjoint ⟨d, len⟩)
    (h0 : t.gpr .x0 = off S oSt) (h2 : t.gpr .x2 = d) (h3 : t.gpr .x3 = BitVec.ofNat 64 len)
    (h4 : t.gpr .x4 = off S oW) (ws : List Region) :
    WP isa (.call G.updN G.updC) t fun t' => Lay t' F S ∧ Step F S ws t t' ∧
      Rep t'.mem F S (fun o => if inR [(oSt, G.S), (oW, hG.Wb)] o then t'.mem (off S o) else V o) W ∧
      (∀ m, hG.SH.Repr t.mem (off S oSt) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hG.SH.Repr t'.mem (off S oSt) (m ++ Spec.Rsa.bytesAt t.mem d len)) := by
  have hz := sizes hG
  have h1 : oSt + G.S ≤ oRsa := by unfold oSt oRsa; omega
  have h2' : oW + hG.Wb ≤ oRsa := by unfold oW oRsa; omega
  have hr : ∀ p ∈ [(oSt, G.S), (oW, hG.Wb)], p.1 + p.2 ≤ oRsa := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> with_reducible assumption
  refine upd_call hG (updExtArgs_of hG L hlen hcd hds hdk h0 h2 h3 h4) fun t' A hrep => ?_
  obtain ⟨L', R'⟩ := L.after_call R hr A
  exact ⟨L', Step.of_after L hr A ws, R', fun m hm hc => hrep m hm hc⟩

end VG.Proof.RsaOaep.AArch64
