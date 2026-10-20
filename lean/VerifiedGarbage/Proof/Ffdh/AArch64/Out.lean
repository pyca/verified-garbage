module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# FFDH on AArch64: the stages across stores outside the working space

A key-generation attempt writes its results outside the working space while
it runs. The stages hold across such stores (`In.out`, `Pa.out`, `R2f.out`),
for the run's data with other inputs (`FD.withSrcs`): their octets are the
stores' results.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- The run's data with the other inputs `ss`. -/
abbrev FD.withSrcs (D : FD) (ss : List (Addr × List Byte)) : FD := ⟨D.B, D.Z, D.k, D.dl, D.dp, D.dom, D.hs, ss⟩

/-- Memory below `Z` kept by stores outside it. -/
theorem outside_of_frame {B : Addr} {Z : Nat} {m m' : Mem} {op : Addr} {len : Nat}
    (hsep : ∀ j < len, Z ≤ ofs B (op + BitVec.ofNat 64 j))
    (hx : ∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → m' x = m x) : Outside B Z (2 ^ 64) m m' :=
  fun x hx' => hx x fun j hj he => by
    have := hsep j hj
    rw [← he] at this
    have : ofs B x < 2 ^ 64 := (x - B).isLt
    rcases hx' with h | h <;> omega

theorem Base.out {D : FD} {t u : State} (h : Base D t) (hrd : u.rd = t.rd) (hwr : u.wr = t.wr)
    (hdom : ∀ i < D.dom.length, u.mem (D.dp + BitVec.ofNat 64 i) = t.mem (D.dp + BitVec.ofNat 64 i))
    {ss : List (Addr × List Byte)} (hss : ∀ e ∈ ss, Src u D.B D.Z e.1 e.2) (hhs : ∀ q ∈ D.hs, q.1 ∈ argSlots) :
    Base (D.withSrcs ss) u :=
  ⟨h.scr.congr hwr, h.k1, h.k2, h.dl, h.hZ,
    ⟨fun i hi => by rw [hrd, hwr]; exact h.dom.rd i hi, fun i hi => by rw [hdom i hi]; exact h.dom.val i hi,
      h.dom.out⟩, h.doml, hss, hhs⟩

/-- `SubMem` across stores outside the working space. -/
theorem SubMem.out {t u : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} (hc : SubMem t B Z o w wx mi)
    (hout : Outside B Z (2 ^ 64) t.mem u.mem) (hwr : u.wr = t.wr) : SubMem u B Z o w wx mi := by
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hi := hc.hi
  have h256 : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega
  have hW : ∀ d, d + 8 ≤ Z → word u.mem B d = word t.mem B d := fun d hd =>
    hout.word (Or.inl hd) (by omega)
  have hh : ∀ i < 32, word u.mem (off B o) (8 * i) = word t.mem (off B o) (8 * i) := fun i hi' => by
    rw [word_off, word_off]; exact hW _ (by have := hdr_lt_slot wx 8 hi'; omega)
  exact ⟨hc.scr.congr hwr,
    ⟨(hh _ (by decide)).trans hc.hdr.hw, (hh _ (by decide)).trans hc.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (hc.hdr.harr j hj)⟩,
    (hh _ (by decide)).trans hc.link, (hW _ (by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega)).trans hc.nw,
    fun j hj => (hW _ (by unfold sArr at *; omega)).trans (hc.narr j hj), hc.lo, hc.hi⟩

/-- `XVals` across stores outside the working space. -/
theorem _root_.VG.Proof.Bignum.AArch64.XVals.out {t u : State} {B : Addr} {Z o w wx : Nat} {mi : BitVec 64} {X : Nat}
    (hc : SubMem t B Z o w wx mi) (hv : XVals t B o wx mi X) (hout : Outside B Z (2 ^ 64) t.mem u.mem) :
    XVals u B o wx mi X := by
  have hn := hc.scr.nowrap
  have hi := hc.hi
  have sN := slot_le (w := wx) (show aN < 8 by decide)
  have sO := slot_le (w := wx) (show aOne < 8 by decide)
  have hN0 := hdr_lt_slot wx aN (show 31 < 32 by decide)
  have h8 := hdr_lt_slot wx 8 (show 31 < 32 by decide)
  have hV : ∀ d k, d + 8 * k ≤ slot wx 8 → wv u.mem (off B o) d k = wv t.mem (off B o) d k :=
    fun d k hd => by rw [wv_off, wv_off]; exact hout.wv (Or.inl (by unfold tabBytes at hi; omega)) (by omega)
  refine ⟨(hV _ wx (by omega)).trans hv.n, ?_, (hV _ wx (by omega)).trans hv.one⟩
  rw [word_off, hout.word (Or.inl (by unfold tabBytes at hi; omega)) (by omega), ← word_off]
  exact hv.inv

/-- Slots across stores outside the working space. -/
theorem Slots.out {m m' : Mem} {B : Addr} {Z : Nat} {L : List (Nat × BitVec 64)} (h : Slots m B L)
    (hout : Outside B Z (2 ^ 64) m m') (hZ : 256 ≤ Z) (hL : ∀ q ∈ L, q.1 < 32) :
    Slots m' B L := fun q hq => by
  have := hL q hq
  rw [hout.word (Or.inl (by omega)) (by omega)]; exact h q hq

theorem Pa.out {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t) (hout : Outside D.B D.Z (2 ^ 64) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (h0 : u.gpr .x0 = D.B)
    (hdom : ∀ i < D.dom.length, u.mem (D.dp + BitVec.ofNat 64 i) = t.mem (D.dp + BitVec.ofNat 64 i))
    {ss : List (Addr × List Byte)} (hss : ∀ e ∈ ss, Src u D.B D.Z e.1 e.2) : Pa (D.withSrcs ss) mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, -⟩ := h
  have hn := hb.scr.nowrap
  have hZ := hb.hZ
  have hk := hb.k1
  have hws : 8 * sWs + 8 ≤ 256 := by decide
  exact ⟨hb.out hrd hwr hdom hss hb.hs, hc.out hout hwr, hv.out hc hout,
    by rw [hout.word (Or.inl (by omega)) (by omega)]; exact hWs,
    hs.out hout (by omega) fun q hq => kept_lt _ (hdr_kept D hb.hs q hq), hmv, h0⟩

theorem In.out {D : FD} {mi : BitVec 64} {t u : State} (h : In D mi t) (hout : Outside D.B D.Z (2 ^ 64) t.mem u.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (h0 : u.gpr .x0 = t.gpr .x0)
    (hdom : ∀ i < D.dom.length, u.mem (D.dp + BitVec.ofNat 64 i) = t.mem (D.dp + BitVec.ofNat 64 i))
    {ss : List (Addr × List Byte)} (hss : ∀ e ∈ ss, Src u D.B D.Z e.1 e.2) : In (D.withSrcs ss) mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv⟩ := h
  have hn := hb.scr.nowrap
  have hZ := hb.hZ
  have hk := hb.k1
  have hws : 8 * sWs + 8 ≤ 256 := by decide
  exact ⟨hb.out hrd hwr hdom hss hb.hs, (hc.toMem.out hout hwr).ctx (h0.trans hc.x0), hv.out hc.toMem hout,
    by rw [hout.word (Or.inl (by omega)) (by omega)]; exact hWs,
    hs.out hout (by omega) fun q hq => kept_lt _ (hdr_kept D hb.hs q hq), hmv⟩

theorem R2f.out {D : FD} {t u : State} (h : R2f D t) (hb : Base D t) (hout : Outside D.B D.Z (2 ^ 64) t.mem u.mem) :
    R2f D u := by
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have sR := slot_le (w := D.w) (show aR2 < 8 by decide)
  have e : wv u.mem (off D.B (inner D.w)) (slot D.w aR2) D.w = wv t.mem (off D.B (inner D.w)) (slot D.w aR2) D.w := by
    rw [wv_off, wv_off]
    exact hout.wv (Or.inl (by unfold tabBytes32 at hroom; omega)) (by unfold tabBytes32 at hroom; omega)
  unfold R2f; rw [e]; exact h

/-- `Pa` after a change of the outer header's slots that the run keeps none of. -/
theorem Pa.hdrW {D : FD} {mi : BitVec 64} {t u : State} (h : Pa D mi t) {rs : List (Nat × Nat)}
    (hf : Frm D.B rs t.mem u.mem) (hr : ∀ r ∈ rs, 8 * 16 ≤ r.1 ∧ r.1 + r.2 ≤ 256)
    (hk : ∀ r ∈ rs, ∀ i ∈ keptSlots, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i)
    (hw : ∀ r ∈ rs, 8 * sWs + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sWs) {rs' : List Reg} (k : Keep rs' t u)
    (h0 : u.gpr .x0 = D.B) : Pa D mi u := by
  obtain ⟨hb, hc, hv, hWs, hs, hmv, -⟩ := h
  have hroom := hb.room
  have hi256 : 256 ≤ inner D.w := by simp only [inner, slot, hdrBytes]; omega
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega
  have i : InScr D.B D.Z t.mem u.mem := InScr.of_frm hf fun r hr' => by have := (hr r hr').2; omega
  exact ⟨hb.keep i k, hc.of_parent hf hr k.wr, hv.of_parent hc hf (fun r hr' => (hr r hr').2),
    by rw [hf.word_eq hw (by decide)]; exact hWs, slots_frm hb.hs hs hf hk, hmv, h0⟩

end VG.Proof.Ffdh.AArch64
