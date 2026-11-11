module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_private_precompute` on x86-64: the masked copies are constant time

`outArr j` leaks the same in runs with the same workspace and destination
(`outArr_ct`); `out` does, in runs with the same working space and `pre`
(`out_ct`): its addresses are the workspaces' and `pre`'s, and its counts
their lengths, while the mask, the values and `-m⁻¹` are only data.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (copyMasked outArr outAt out)
open VG.Impl.Rsa.X86_64 (eightW)

/-- The public data of `outArr`: the workspace and the destination. -/
structure OAPub where
  X : Addr
  Zx : Nat
  wx : Nat
  D : Addr
  e : Nat

/-- Before `outArr j`. -/
def OAPre (p : OAPub) (s : State) : Prop :=
  ∃ mx, Good s p.X p.Zx p.wx mx ∧ slot p.wx 8 ≤ p.Zx ∧ s.gpr .rbx = off p.D p.e

/-- `outArr j` leaks the same in runs with the same workspace and
destination, given that the taint analysis checks its header loads. -/
theorem outArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr j)))])
      hc).isSome = true) :
    RelCT isa (Two OAPre) (seqs (outArr j)) fun _ _ => True := by
  unfold outArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .r12 = BitVec.ofNat 64 p.wx ∧
      t.gpr .rsi = off p.X (slot p.wx j) ∧ t.gpr .rbx = off p.D p.e) [.rdi]
    (pins_of (fun p _ => p.X) fun p s ⟨_, hg, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.rdi) hT ?_)
    (two_taint [.r12, .rsi, .rbx] (pins_of (fun p r => if r = .r12 then BitVec.ofNat 64 p.wx else
        if r = .rsi then off p.X (slot p.wx j) else off p.D p.e)
      fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  rintro p s ⟨mx, hg, hZ, hbx⟩
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.X (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.wx 8 hi; omega)
  exact WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.wx ∧
      t.gpr .rsi = off p.X (slot p.wx j))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr j) (by unfold sArr; omega),
      hg.hdr.hw, hg.hdr.harr j hj]) rfl) fun t ⟨⟨h12, hsi⟩, k⟩ => ⟨h12, hsi, (k.gpr (by decide)).trans hbx⟩

/-- The public data of `out`: the working space, the workspaces' offsets
and words, and `pre`. -/
structure OPub where
  B : Addr
  Z : Nat
  w : Nat
  op : Nat
  wp : Nat
  oq : Nat
  wq : Nat
  D : Addr
  L8 : Nat

/-- What `out`'s parts keep: `n`'s workspace and header, the primes'
workspaces, and `pre`. -/
structure OB (p : OPub) (minv mp mq : BitVec 64) (s : State) : Prop where
  good : Good s p.B p.Z p.w minv
  out : word s.mem p.B (8 * sOut) = p.D
  wsP : word s.mem p.B (8 * sWsP) = off p.B p.op
  wsQ : word s.mem p.B (8 * sWsQ) = off p.B p.oq
  pws : WsAt s.mem p.B p.op p.wp mp
  qws : WsAt s.mem p.B p.oq p.wq mq
  zw : slot p.w 8 ≤ p.Z
  loP : slot p.w 8 ≤ p.op
  hiP : p.op + slot p.wp 8 ≤ p.Z
  loQ : slot p.w 8 ≤ p.oq
  hiQ : p.oq + slot p.wq 8 ≤ p.Z
  w1 : 1 ≤ p.w
  w2 : p.w < 2 ^ 20
  wp1 : 1 ≤ p.wp
  wp2 : p.wp < 2 ^ 20
  wq1 : 1 ≤ p.wq
  wq2 : p.wq < 2 ^ 20
  len : 16 * p.w + 8 * p.wp + 8 * p.wq ≤ p.L8
  hL : p.D.toNat + p.L8 ≤ 2 ^ 64
  wr : (⟨p.D, p.L8⟩ : Region) ∈ s.wr
  sep : ∀ x, ofs p.B x < p.Z → p.L8 ≤ ofs p.D x

/-- `OB` for some `-m⁻¹`s, and `rbx` at `pre + e p`. -/
def OAt (e : OPub → Nat) (p : OPub) (s : State) : Prop :=
  (∃ minv mp mq, OB p minv mp mq s) ∧ s.gpr .rbx = off p.D (e p)

theorem OB.of_scr {p : OPub} {minv mp mq : BitVec 64} {s t : State} (h : OB p minv mp mq s)
    (hm : ∀ x, ofs p.B x < p.Z → t.mem x = s.mem x) (hwr : t.wr = s.wr) (hdi : t.gpr .rdi = p.B) :
    OB p minv mp mq t := by
  have hn := h.good.scr.nowrap
  have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
  have hw : ∀ d, d + 8 ≤ p.Z → word t.mem p.B d = word s.mem p.B d := fun d hd => word_of_scr hm hd hn
  have hP8 : 8 * 32 ≤ slot p.wp 8 := by unfold slot hdrBytes; omega
  have hQ8 : 8 * 32 ≤ slot p.wq 8 := by unfold slot hdrBytes; omega
  have hlo := h.loP
  have hhi := h.hiP
  have hlo' := h.loQ
  have hhi' := h.hiQ
  exact { h with
    good := Good.of_scr h.good h.zw hm hwr hdi
    out := (hw _ (by unfold sOut sFn; omega)).trans h.out
    wsP := (hw _ (by unfold sWsP sFn; omega)).trans h.wsP
    wsQ := (hw _ (by unfold sWsQ sFn; omega)).trans h.wsQ
    pws := h.pws.of_words fun i hi => by rw [word_off, word_off]; exact hw _ (by omega)
    qws := h.qws.of_words fun i hi => by rw [word_off, word_off]; exact hw _ (by omega)
    wr := by rw [hwr]; exact h.wr }

theorem pins_oat {e : OPub → Nat} : Pins (OAt e) [.rdi, .rbx] :=
  pins_of (fun p r => if r = .rdi then p.B else off p.D (e p)) fun p s ⟨⟨_, _, _, h⟩, hbx⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.good.rdi
    · exact hbx

/-- `outArr j` of `n`'s workspace. -/
theorem arrN_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr j)))])
      hc).isSome = true) {e : OPub → Nat} (he : ∀ p, e p + 8 * p.w ≤ 16 * p.w) :
    RelCT isa (Two (OAt e)) (seqs (outArr j)) (Two (OAt fun p => e p + 8 * p.w)) := by
  refine two_post (two_map (fun p => (⟨p.B, p.Z, p.w, p.D, e p⟩ : OAPub))
    (fun p s ⟨⟨minv, _, _, h⟩, hbx⟩ => ⟨minv, h.good, h.zw, hbx⟩) (outArr_ct hj hT)) ?_
  rintro p s ⟨⟨minv, mp, mq, h⟩, hbx⟩
  have hn := h.good.scr.nowrap
  have hL := h.hL
  have hlen := h.len
  have hhe := he p
  have hw1 := h.w1
  have hw2 := h.w2
  have hzw := h.zw
  exact WP.mono (outArr_ok h.good h.zw hj hw1 (by omega) hbx rfl (by omega)
    (fun i hi => ⟨_, h.wr, Offset.contains_base p.D (by omega) (by omega)⟩)
    (fun i hi => by
      have := slot_le (w := p.w) hj
      have := sep_of (o := 0) (d := slot p.w j + 8 * i) h.sep (eD := e p) (n := 8 * p.w) (by omega) (by omega) hn
      simpa [off_off] using this)) fun t ⟨_, ho, hbx', k⟩ =>
    ⟨⟨minv, mp, mq, h.of_scr (scr_of_outside ho h.sep (by omega)) k.2.2 ((k.gpr (by decide)).trans h.good.rdi)⟩,
      hbx'⟩

/-- `outAt sl` of the workspace at `o p` (`wx p` words), its base in slot
`sl`. -/
theorem at_ct {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true)
    (hsl : sl < 32) {e o wx : OPub → Nat}
    (hsel : ∀ p minv mp mq s, OB p minv mp mq s → ∃ mx, word s.mem p.B (8 * sl) = off p.B (o p) ∧
      WsAt s.mem p.B (o p) (wx p) mx ∧ slot p.w 8 ≤ o p ∧ o p + slot (wx p) 8 ≤ p.Z ∧ 1 ≤ wx p ∧ wx p < 2 ^ 20 ∧
      e p + 8 * wx p ≤ p.L8) :
    RelCT isa (Two (OAt e)) (seqs (outAt sl)) (Two (OAt fun p => e p + 8 * wx p)) := by
  refine two_post ?_ ?_
  · unfold outAt
    simp only [List.append_assoc]
    refine RelCT.seqs_append (by simp) (by simp [outArr]) (RelCT.seq (two_piece (Ψ := fun p t =>
        OAPre ⟨off p.B (o p), slot (wx p) 8, wx p, p.D, e p⟩ t ∧ 1 ≤ wx p ∧ wx p < 2 ^ 20 ∧
          e p + 8 * wx p ≤ p.L8 ∧ p.D.toNat + p.L8 ≤ 2 ^ 64 ∧ (⟨p.D, p.L8⟩ : Region) ∈ t.wr ∧
          ∀ x, ofs (off p.B (o p)) x < slot (wx p) 8 → p.L8 ≤ ofs p.D x) _
      (pins_of (fun p _ => p.B) fun p s ⟨⟨_, _, _, h⟩, _⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.good.rdi) hT ?_) ?_)
    · rintro p s ⟨⟨minv, mp, mq, h⟩, hbx⟩
      obtain ⟨mx, hslv, hws, hlo, hhi, hw1, hw2, hhe⟩ := hsel p minv mp mq s h
      have hs := h.good.scr
      have hn := hs.nowrap
      have hX8 : 256 ≤ slot (wx p) 8 := by unfold slot hdrBytes; omega
      refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B (o p) ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, h.good.rdi, hdrOff, hs.ld (d := 8 * sl) (by have := hdr_lt_slot p.w 8 hsl; omega),
          hslv]) rfl)
        fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨⟨mx, ⟨(hs.congr k.2.2).sub (o := o p) (n := slot (wx p) 8) hhi (by omega), hdi,
          by rw [hm]; exact hws.hdr⟩, Nat.le_refl _, (k.gpr (by decide)).trans hbx⟩, hw1, hw2, hhe, h.hL,
          by rw [k.2.2]; exact h.wr, fun x hx => h.sep x (ofs_lt_of_sub hhi hn hx)⟩
    refine RelCT.seqs_append (by simp [outArr]) (by simp) (RelCT.seq (two_post (Ψ := fun p t =>
      t.gpr .rdi = off p.B (o p)) (two_map _ (fun _ _ h => h.1) (outArr_ct (show aY < 8 by decide) (by taint_decide)))
      fun p s ⟨⟨mx, hg, hZ, hbx⟩, hw1, hw2, hhe, hL, hwr, hS⟩ => ?_) ?_)
    · dsimp only at hg hZ hbx
      have hn := hg.scr.nowrap
      exact WP.mono (outArr_ok hg hZ (show aY < 8 by decide) hw1 (by omega) hbx rfl (by omega)
        (fun i hi => ⟨_, hwr, Offset.contains_base p.D (by omega) (by omega)⟩)
        (fun i hi => by
          have := slot_le (w := wx p) (show aY < 8 by decide)
          have := sep_of (o := 0) (d := slot (wx p) aY + 8 * i) hS (eD := e p) (n := 8 * wx p) (by omega)
            (by omega) hn
          simpa [off_off] using this)) fun t ⟨_, _, _, k⟩ => (k.gpr (by decide)).trans hg.rdi
    exact two_taint [.rdi] (pins_of (fun p _ => off p.B (o p)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)
  · rintro p s ⟨⟨minv, mp, mq, h⟩, hbx⟩
    obtain ⟨mx, hslv, hws, hlo, hhi, hw1, hw2, hhe⟩ := hsel p minv mp mq s h
    exact WP.mono (outAt_ok h.good hlo hhi hw1 (by omega) hsl hslv hws hbx rfl (by omega) h.hL h.wr h.sep)
      fun t ⟨_, ho, hbx', hdi, _, k⟩ =>
        ⟨⟨minv, mp, mq, h.of_scr (scr_of_outside ho h.sep (by omega)) k.2.2 hdi⟩, hbx'⟩

/-- `out` leaks the same in runs with the same working space, workspaces
and `pre`. -/
theorem out_ct : RelCT isa (Two fun p s => ∃ minv mp mq, OB p minv mp mq s) (seqs out) fun _ _ => True := by
  unfold out
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [outArr]) (RelCT.seq (R := Two (OAt fun _ => 0)) (two_piece [.rdi]
    (pins_of (fun p _ => p.B) fun p s ⟨_, _, _, h⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.good.rdi) (by taint_decide) ?_) ?_)
  · rintro p s ⟨minv, mp, mq, h⟩
    have hs := h.good.scr
    have hn := hs.nowrap
    have h8 := hdr_lt_slot p.w 8 (show 31 < 32 by decide)
    have hzw := h.zw
    refine WP.mono (WP.keep [.rbx, .r15] (Q := fun t => t.gpr .rbx = off p.D 0 ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, h.good.rdi, hdrOff, hs.ld (d := 8 * sOut) (by unfold sOut sFn; omega),
        hs.ld (d := 8 * sMask) (by unfold sMask sFn; omega), h.out]) rfl)
      fun t ⟨⟨hbx, hm⟩, k⟩ => ⟨⟨minv, mp, mq, h.of_scr (fun x _ => by rw [hm]) k.2.2
        ((k.gpr (by decide)).trans h.good.rdi)⟩, hbx⟩
  refine RelCT.seqs_append (by simp [outArr]) (by simp [outArr]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w)) (arrN_ct (show aN < 8 by decide) (by taint_decide) fun _ => by omega) ?_)
  refine RelCT.seqs_append (by simp [outArr]) (by simp [outAt]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w))
    (arrN_ct (show aR2 < 8 by decide) (by taint_decide) fun _ => by omega) ?_)
  refine RelCT.seqs_append (by simp [outAt]) (by simp [outAt]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w + 8 * p.wp))
    (at_ct (o := OPub.op) (wx := OPub.wp) (sl := sWsP) (by taint_decide) (by decide)
      fun p minv mp mq s h => ⟨mp, h.wsP, h.pws, h.loP, h.hiP, h.wp1, h.wp2, by have := h.len; omega⟩) ?_)
  refine RelCT.seqs_append (by simp [outAt]) (by simp) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w + 8 * p.wp + 8 * p.wq))
    (at_ct (o := OPub.oq) (wx := OPub.wq) (sl := sWsQ) (by taint_decide) (by decide)
      fun p minv mp mq s h => ⟨mq, h.wsQ, h.qws, h.loQ, h.hiQ, h.wq1, h.wq2, by have := h.len; omega⟩) ?_)
  exact two_taint [.rdi] (pins_of (fun p _ => p.B) fun p s ⟨⟨_, _, _, h⟩, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.good.rdi) (by taint_decide)

end VG.Proof.Bignum.X86_64.PrivPre
