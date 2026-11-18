module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Correct
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Correct
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtBack
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
import VerifiedGarbage.Proof.Bignum.CrtResult
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFront
meta import VerifiedGarbage.Proof.Bignum.CrtResult
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.R2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
meta import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Out
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Bignum.X86_64.PrivPre.CTCode`, which only this module used -/

section

/-! ### `Bignum.X86_64.PrivPre.CTMain`, which only this module used -/

section

/-! ### `Bignum.X86_64.PrivPre.CTOut`, which only this module used -/

section

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
    hg.scr.ld (by have := hdr_lt_slot p.wx 8 hi; omega_using [hZ, this])
  exact WP.mono (WP.keep [.r12, .rsi] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.wx ∧
      t.gpr .rsi = off p.X (slot p.wx j))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr j) (by unfold sArr; omega_using [hj]),
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
  have hP8 : 8 * 32 ≤ slot p.wp 8 := by unfold slot hdrBytes; omega_using []
  have hQ8 : 8 * 32 ≤ slot p.wq 8 := by unfold slot hdrBytes; omega_using []
  have hlo := h.loP
  have hhi := h.hiP
  have hlo' := h.loQ
  have hhi' := h.hiQ
  exact { h with
    good := Good.of_scr h.good h.zw hm hwr hdi
    out := (hw _ (by unfold sOut sFn; omega_using [hP8, hhi])).trans h.out
    wsP := (hw _ (by unfold sWsP sFn; omega_using [hP8, hhi])).trans h.wsP
    wsQ := (hw _ (by unfold sWsQ sFn; omega_using [hP8, hhi])).trans h.wsQ
    pws := h.pws.of_words fun i hi => by rw [word_off, word_off]; exact hw _ (by omega_using [hP8, hhi, hi])
    qws := h.qws.of_words fun i hi => by rw [word_off, word_off]; exact hw _ (by omega_using [hQ8, hhi', hi])
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
  exact WP.mono (outArr_ok h.good h.zw hj hw1 (by omega_using [hw2]) hbx rfl (by omega_using [hhe, hw2])
    (fun i hi => ⟨_, h.wr, Offset.contains_base p.D (by omega_using [hlen, hhe, hi]) (by omega_using [hhe, hw2, hi])⟩)
    (fun i hi => by
      have := slot_le (w := p.w) hj
      have := sep_of (o := 0) (d := slot p.w j + 8 * i) h.sep (eD := e p) (n := 8 * p.w) (by omega_using [hlen, hhe]) (by omega_using [hzw, hi, this]) hn
      simpa [off_off] using this)) fun t ⟨_, ho, hbx', k⟩ =>
    ⟨⟨minv, mp, mq, h.of_scr (scr_of_outside ho h.sep (by omega_using [hlen, hhe])) k.2.2 ((k.gpr (by decide)).trans h.good.rdi)⟩,
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
      have hX8 : 256 ≤ slot (wx p) 8 := by unfold slot hdrBytes; omega_using []
      refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B (o p) ∧ t.mem = s.mem)
        (by xrun [State.ea, hdr, h.good.rdi, hdrOff, hs.ld (d := 8 * sl) (by have := hdr_lt_slot p.w 8 hsl; omega_using [hsl, hhi, hX8]),
          hslv]) rfl)
        fun t ⟨⟨hdi, hm⟩, k⟩ => ⟨⟨mx, ⟨(hs.congr k.2.2).sub (o := o p) (n := slot (wx p) 8) hhi (by omega_using [hX8]), hdi,
          by rw [hm]; exact hws.hdr⟩, Nat.le_refl _, (k.gpr (by decide)).trans hbx⟩, hw1, hw2, hhe, h.hL,
          by rw [k.2.2]; exact h.wr, fun x hx => h.sep x (ofs_lt_of_sub hhi hn hx)⟩
    refine RelCT.seqs_append (by simp [outArr]) (by simp) (RelCT.seq (two_post (Ψ := fun p t =>
      t.gpr .rdi = off p.B (o p)) (two_map _ (fun _ _ h => h.1) (outArr_ct (show aY < 8 by decide) (by taint_decide)))
      fun p s ⟨⟨mx, hg, hZ, hbx⟩, hw1, hw2, hhe, hL, hwr, hS⟩ => ?_) ?_)
    · dsimp only at hg hZ hbx
      have hn := hg.scr.nowrap
      exact WP.mono (outArr_ok hg hZ (show aY < 8 by decide) hw1 (by omega_using [hw2]) hbx rfl (by omega_using [hhe, hL])
        (fun i hi => ⟨_, hwr, Offset.contains_base p.D (by omega_using [hhe, hi]) (by omega_using [hhe, hL, hi])⟩)
        (fun i hi => by
          have := slot_le (w := wx p) (show aY < 8 by decide)
          have := sep_of (o := 0) (d := slot (wx p) aY + 8 * i) hS (eD := e p) (n := 8 * wx p) (by omega_using [hhe])
            (by omega_using [hi, this]) hn
          simpa [off_off] using this)) fun t ⟨_, _, _, k⟩ => (k.gpr (by decide)).trans hg.rdi
    exact two_taint [.rdi] (pins_of (fun p _ => off p.B (o p)) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)
  · rintro p s ⟨⟨minv, mp, mq, h⟩, hbx⟩
    obtain ⟨mx, hslv, hws, hlo, hhi, hw1, hw2, hhe⟩ := hsel p minv mp mq s h
    exact WP.mono (outAt_ok h.good hlo hhi hw1 (by omega_using [hw2]) hsl hslv hws hbx rfl (by omega_using [hhe]) h.hL h.wr h.sep)
      fun t ⟨_, ho, hbx', hdi, _, k⟩ =>
        ⟨⟨minv, mp, mq, h.of_scr (scr_of_outside ho h.sep (by omega_using [hhe])) k.2.2 hdi⟩, hbx'⟩

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
      (by xrun [State.ea, hdr, h.good.rdi, hdrOff, hs.ld (d := 8 * sOut) (by unfold sOut sFn; omega_using [h8, hzw]),
        hs.ld (d := 8 * sMask) (by unfold sMask sFn; omega_using [h8, hzw]), h.out]) rfl)
      fun t ⟨⟨hbx, hm⟩, k⟩ => ⟨⟨minv, mp, mq, h.of_scr (fun x _ => by rw [hm]) k.2.2
        ((k.gpr (by decide)).trans h.good.rdi)⟩, hbx⟩
  refine RelCT.seqs_append (by simp [outArr]) (by simp [outArr]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w)) (arrN_ct (show aN < 8 by decide) (by taint_decide) fun _ => by omega_using []) ?_)
  refine RelCT.seqs_append (by simp [outArr]) (by simp [outAt]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w))
    (arrN_ct (show aR2 < 8 by decide) (by taint_decide) fun _ => by omega_using []) ?_)
  refine RelCT.seqs_append (by simp [outAt]) (by simp [outAt]) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w + 8 * p.wp))
    (at_ct (o := OPub.op) (wx := OPub.wp) (sl := sWsP) (by taint_decide) (by decide)
      fun p minv mp mq s h => ⟨mp, h.wsP, h.pws, h.loP, h.hiP, h.wp1, h.wp2, by have := h.len; omega_using [this]⟩) ?_)
  refine RelCT.seqs_append (by simp [outAt]) (by simp) (RelCT.seq
    (R := Two (OAt fun p => 0 + 8 * p.w + 8 * p.w + 8 * p.wp + 8 * p.wq))
    (at_ct (o := OPub.oq) (wx := OPub.wq) (sl := sWsQ) (by taint_decide) (by decide)
      fun p minv mp mq s h => ⟨mq, h.wsQ, h.qws, h.loQ, h.hiQ, h.wq1, h.wq2, by have := h.len; omega_using [this]⟩) ?_)
  exact two_taint [.rdi] (pins_of (fun p _ => p.B) fun p s ⟨⟨_, _, _, h⟩, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.good.rdi) (by taint_decide)

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-! ### `Bignum.X86_64.PrivPre.CTR2`, which only this module used -/

section

/-!
# `vg_rsa_private_precompute` on x86-64: `R_X² mod X` is constant time

`double` and `doubles` leak the same in runs with the same workspace and
count, whatever their moduli and `-m⁻¹` (`double_ctW`, `doubles_ctW`), and
so do `r2X` (`r2X_ct`), whose loop and branches count the lengths, and
`r2At` (`r2At_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2X r2At link bW chunkWords fixStart fixStep fixStepB fixSub)

/-- `DblHeadL`, which does not read `-m⁻¹`, for a workspace. -/
def DblHeadW (mo acc tmp o : Nat) (L : Ws) (t : State) : Prop := DblHeadL mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩ t

/-- `double` leaks the same in runs with the same workspace. -/
theorem double_ctW {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodW) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece (Ψ := DblHeadW mo acc tmp o) _ pins_goodW h fun L _ ⟨minv, hg⟩ =>
      dblHead_ok (L := ⟨L.B, L.Z, L.w, minv⟩) hg hmo hacc htmp ho)
    (two_taint _ (fun L => pins_dblHead mo acc tmp o ⟨L.B, L.Z, L.w, 0⟩) (by taint_decide))

/-- The public data of `doubles` in a workspace whose `-m⁻¹` is secret. -/
structure DblPubW where
  L : Ws
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAtW (mo acc tmp o sl : Nat) (p : DblPubW) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat) (minv : BitVec 64), DblsInv σ p.L.B p.L.Z p.L.w minv mo acc tmp o sl p.c O N j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAtW_good {mo acc tmp o sl : Nat} {p : DblPubW} {j : Nat} {t : State}
    (h : DblsAtW mo acc tmp o sl p j t) : GoodW p.L t :=
  let ⟨_, _, _, minv, hI, hZ, _⟩ := h; ⟨minv, ⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `doubles` leaks the same in runs with the same workspace and count. -/
theorem doubles_ctW {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblPubW) s => ∃ minv, GoodL ⟨p.L.B, p.L.Z, p.L.w, minv⟩ s ∧ 2 ≤ p.L.w ∧
      p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) fun _ _ => True := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsAtW mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ ⟨m₁, h₁, _⟩ ⟨m₂, h₂, _⟩ => pins_goodW ⟨p.L.B, p.L.Z, p.L.w⟩ s₁ s₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩) h' ?_) ?_
  · rintro p s ⟨minv, hg, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.rdi hg.1.hdr hg.2 hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega_using [hc1], s, _, _, minv, hI, hg.2, hw, hw', hc', Nat.lt_of_le_of_lt (Nat.zero_le _) hO⟩
  refine RelCT.mono (two_loop (Φ := DblsAtW mo acc tmp o sl) (Ψ := fun _ _ => True) (fun p => p.c) ?_ ?_)
    (fun _ _ h => h) fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : DblPubW × Nat) s => GoodW q.1.L s)
      (two_map (·.1.L) (fun _ _ h => dblsAtW_good h.2) (double_ctW hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_goodW q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨minv, ⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, minv, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, O, N, minv, hI', hZ, hw, hw', hc', hN0⟩, fun _ => trivial⟩

theorem pins1 {α : Type} {Φ : α → State → Prop} {r₁ : Reg} (f₁ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a) : Pins Φ [r₁] := fun a _ _ h₁ h₂ r hr => by
  rw [List.mem_singleton.mp hr, h a _ h₁, h a _ h₂]

theorem pins2 {α : Type} {Φ : α → State → Prop} {r₁ r₂ : Reg} (f₁ f₂ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a ∧ s.gpr r₂ = f₂ a) : Pins Φ [r₁, r₂] := fun a _ _ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h a _ h₁).1, (h a _ h₂).1]
  · rw [(h a _ h₁).2, (h a _ h₂).2]

theorem pins3 {α : Type} {Φ : α → State → Prop} {r₁ r₂ r₃ : Reg} (f₁ f₂ f₃ : α → BitVec 64)
    (h : ∀ a s, Φ a s → s.gpr r₁ = f₁ a ∧ s.gpr r₂ = f₂ a ∧ s.gpr r₃ = f₃ a) : Pins Φ [r₁, r₂, r₃] :=
  fun a _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [(h a _ h₁).1, (h a _ h₂).1]
    · rw [(h a _ h₁).2.1, (h a _ h₂).2.1]
    · rw [(h a _ h₁).2.2, (h a _ h₂).2.2]

/-- The public data of `r2X` and `r2At`: the working space, `n`'s words,
and the prime's workspace's offset and words. -/
structure RXPub where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  wx : Nat

/-- The prime's workspace. -/
abbrev RXPub.ws (p : RXPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩
/-- `R² mod n`'s chunks. -/
abbrev RXPub.K (p : RXPub) : Nat := (p.w + p.wx - 1) / p.wx
/-- `A` after `k` reductions. -/
abbrev RXPub.A (p : RXPub) (k : Nat) : Nat := 64 * (k * p.wx) + 128 * p.wx

/-- The sizes' bounds. -/
def RXB (p : RXPub) : Prop := 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 20

/-- At `r2X`'s start. -/
def RXPre (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p ∧
    wv s.mem (off p.B p.o) (slot p.wx aY) p.wx < X

/-- From `fixStart` on, after `k` reductions. -/
def RXK (p : RXPub) (k : Nat) (t : State) : Prop :=
  ∃ σ mx X, FInv False σ t p.B p.Z p.o p.w p.wx mx X k ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p

/-- After the reduction of a step. -/
def RXM (p : RXPub) (k : Nat) (t : State) : Prop :=
  ∃ σ mx X, FMid False σ t p.B p.Z p.o p.w p.wx mx X k ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p

section
variable {p : RXPub} {s t : State} {rs : List Reg} {k : Nat}

theorem RXPre.step (h : RXPre p s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hdi : .rdi ∉ rs) : RXPre p t := by
  obtain ⟨mx, X, hc, hv, h1, h2, hb, hy⟩ := h
  exact ⟨mx, X, hc.of_frm (rs := []) (by rw [hm]; exact fun _ _ => rfl) (by simp) k'.2.2 (k'.gpr hdi),
    ⟨by rw [hm]; exact hv.n, by rw [hm]; exact hv.inv, by rw [hm]; exact hv.one⟩, h1, h2, hb, by rw [hm]; exact hy⟩

theorem RXK.step (h : RXK p k s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : .rdi ∉ rs) : RXK p k t :=
  let ⟨σ, mx, X, hI, h1, h2, hb⟩ := h; ⟨σ, mx, X, hI.step hm k' hrs hdi, h1, h2, hb⟩

theorem RXM.step (h : RXM p k s) (hm : t.mem = s.mem) (k' : Keep rs s t) (hrs : ∀ r ∈ rs, r ∈ mmRegs)
    (hdi : .rdi ∉ rs) : RXM p k t :=
  let ⟨σ, mx, X, hI, h1, h2, hb⟩ := h; ⟨σ, mx, X, hI.step hm k' hrs hdi, h1, h2, hb⟩

theorem RXPre.rdi (h : RXPre p s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, hc, _⟩ := h; hc.rdi
theorem RXK.rdi (h : RXK p k s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, _, hI, _⟩ := h; hI.c.rdi
theorem RXM.rdi (h : RXM p k s) : s.gpr .rdi = off p.B p.o := let ⟨_, _, _, hI, _⟩ := h; hI.c.rdi

theorem RXK.good (h : RXK p k s) : GoodW p.ws s := let ⟨_, mx, _, hI, _⟩ := h; ⟨mx, hI.c.good, Nat.le_refl _⟩

theorem RXK.bnd (h : RXK p k s) : RXB p := let ⟨_, _, _, _, _, _, hb⟩ := h; hb

end

/-! ## The chunks -/

/-- After `chunkWords`' blocks. -/
def XC1 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧ t.gpr .r12 = p.B
def XC2 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧
  t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rcx = BitVec.ofNat 64 0
def XC3 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rax = BitVec.ofNat 64 p.wx ∧
  t.gpr .rcx = BitVec.ofNat 64 (p.K * p.wx)

theorem chunk_ct : RelCT isa (Two RXPre) (seqs chunkWords) (Two XC3) := by
  simp only [chunkWords, seqs]
  refine RelCT.seq (two_piece (Ψ := XC1) [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h.rdi) (by taint_decide)
    ?_) (RelCT.seq (two_piece (Ψ := XC2) [.rdi, .r12] (pins2 (fun p => off p.B p.o) (fun p => p.B)
      fun _ _ h => ⟨h.1.rdi, h.2.2⟩) (by taint_decide) ?_)
    (two_post (two_taint [.rax, .r12, .rcx] (pins3 (fun p => BitVec.ofNat 64 p.wx) (fun p => BitVec.ofNat 64 p.w)
      (fun _ => BitVec.ofNat 64 0) fun _ _ h => h.2) (by taint_decide)) ?_))
  · intro p s h
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (chunkA_ok hc) fun t ⟨h1, h2, hm, k⟩ => ⟨h.step hm k (by decide), h1, h2⟩
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (chunkB_ok hc h2) fun t ⟨h3, h4, hm, k⟩ =>
      ⟨h.step hm k (by decide), (k.gpr (by decide)).trans h1, h3, h4⟩
  · rintro p s ⟨h, h1, h2, h3⟩
    obtain ⟨_, _, _, _, _, _, ⟨hb1, hb2, hb3⟩, _⟩ := id h
    exact WP.mono (kLoop_ok (by omega_using [hb1]) (by omega_using [hb1, hb2]) (by omega_using [hb2, hb3]) h1 h2 h3) fun t ⟨hcx, hm, k⟩ =>
      ⟨h.step hm k (by decide), (k.gpr (by decide)).trans h1, hcx⟩

/-! ## `fixStart` -/

def S1 (p : RXPub) (t : State) : Prop := RXPre p t ∧ t.gpr .rcx = BitVec.ofNat 64 (p.A p.K) ∧ t.gpr .r12 = p.B
def F0 (p : RXPub) (t : State) : Prop := RXK p p.K t ∧ t.cf = some (decide (p.A p.K < 128 * p.w))

theorem fs_ct : RelCT isa (Two XC3) (seqs fixStart) (Two F0) := by
  simp only [fixStart, seqs]
  refine RelCT.seq (two_piece (Ψ := S1) [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h.1.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun p => off p.B p.o) (fun p => p.B)
      fun _ _ h => ⟨h.1.rdi, h.2.2⟩) (by taint_decide) ?_)
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨_, _, hc, -⟩ := id h
    exact WP.mono (fsA_ok hc h2 h1) fun t ⟨h3, h4, hm, k⟩ => ⟨h.step hm k (by decide), h3, h4⟩
  · rintro p s ⟨h, h1, h2⟩
    obtain ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hy⟩ := h
    obtain ⟨hK1, hK2⟩ := kBounds (w := p.w) (show 1 ≤ p.wx by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb1])
    exact WP.mono (fsB_ok hc h2 h1 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb2, hb3, hK2]) hb3) fun t ⟨hm, hcf, k⟩ =>
      ⟨⟨s, mx, X, finv_store (Pr := False) hc hv (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb1]) hy (fun h => h.elim) hm k (by decide) (by decide),
        hX1, hXo, hb1, hb2, hb3⟩, hcf⟩

/-! ## The extra reductions -/

/-- After the extra reductions: `128 w ≤ A`. -/
def G (q : RXPub × Nat) (t : State) : Prop := RXK q.1 q.2 t ∧ 128 * q.1.w ≤ q.1.A q.2 ∧ q.1.A q.2 < 2 ^ 30

def Bpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXK q.1 q.2 s
def Mpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXM q.1 q.2 s
def Lpre (n : Nat) (q : RXPub × Nat) (s : State) : Prop := Mpre n q s ∧ s.gpr .r12 = q.1.B
def Bpost (n : Nat) (q : RXPub × Nat) (s : State) : Prop :=
  n = 128 * q.1.w - q.1.A q.2 ∧ q.1.A q.2 < 128 * q.1.w ∧ RXK q.1 (q.2 + 1) s ∧
    s.cf = some (decide (q.1.A (q.2 + 1) < 128 * q.1.w))

theorem body_ct (M : Mont) (n : Nat) :
    RelCT isa (Two (Bpre n)) (.seq (M.mm aY aY aOne) fixStep) (Two (Bpost n)) := by
  refine RelCT.seq (two_post (Ψ := Mpre n) (two_map (fun q => q.1.ws) (fun _ _ h => h.2.2.good)
    (M.ct (by unfold MmUse; decide))) ?_) ?_
  · rintro q s ⟨hn, hA, σ, mx, X, hI, hX1, hXo, ⟨hb1, hb2, hb3⟩⟩
    exact WP.mono (mulY_ok M hI hX1 hb1 hb3 hb2) fun t h => ⟨hn, hA, σ, mx, X, h, hX1, hXo, hb1, hb2, hb3⟩
  unfold fixStep
  refine RelCT.seq (two_piece (Ψ := Lpre n) [.rdi] (pins1 (fun q => off q.1.B q.1.o) fun _ _ h => h.2.2.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun q => off q.1.B q.1.o) (fun q => q.1.B)
      fun _ _ h => ⟨h.1.2.2.rdi, h.2⟩) (by taint_decide) ?_)
  · rintro q s ⟨hn, hA, h⟩
    obtain ⟨_, _, _, hI, -⟩ := id h
    exact WP.mono (link_ok hI.c) fun t ⟨h12, hm, k⟩ => ⟨⟨hn, hA, h.step hm k (by decide) (by decide)⟩, h12⟩
  · rintro q s ⟨⟨hn, hA, σ, mx, X, hI, hX1, hXo, ⟨hb1, hb2, hb3⟩⟩, h12⟩
    exact WP.mono (stepFin_ok hI h12 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb1]) hb3 hA) fun t ⟨hI', hcf⟩ =>
      ⟨hn, hA, ⟨σ, mx, X, hI', hX1, hXo, hb1, hb2, hb3⟩, hcf⟩

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := by simp [eval, h]
theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := by simp [eval, h]

theorem extra_ct (M : Mont) :
    RelCT isa (Two F0) (.ite .b (.loop (.seq (M.mm aY aY aOne) fixStep) .b) (.block [])) (Two G) := by
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_b h₁.2, eval_b h₂.2]) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨p, ⟨h₁, e₁⟩, ⟨h₂, _⟩⟩ x₁ x₂
    have hlt : p.A p.K < 128 * p.w := by
      have := (eval_b h₁.2).symm.trans e₁; simpa using this
    refine RelCT.loop (fun n s₁ s₂ => ∃ q : RXPub × Nat, Bpre n q s₁ ∧ Bpre n q s₂) (fun n => ?_)
      (128 * p.w - p.A p.K) s₁ s₂ t₁ t₂ s₁' s₂' ⟨(p, p.K), ⟨rfl, hlt, h₁.1⟩, ⟨rfl, hlt, h₂.1⟩⟩ x₁ x₂
    refine (body_ct M n).mono (fun _ _ ⟨q, b₁, b₂⟩ => ⟨q, b₁, b₂⟩) ?_
    rintro u₁ u₂ ⟨q, ⟨hn, hA, k₁, c₁⟩, ⟨-, -, k₂, c₂⟩⟩
    have hb := k₁.bnd
    obtain ⟨hb1, -, hb3⟩ := hb
    have e1 := Nat.add_one_mul q.2 q.1.wx
    refine ⟨by rw [eval_b c₁, eval_b c₂], fun hf => ?_, fun ht => ?_⟩
    · have : ¬ q.1.A (q.2 + 1) < 128 * q.1.w := by
        have := (eval_b c₁).symm.trans hf; simpa using this
      exact ⟨(q.1, q.2 + 1), ⟨k₁, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [this], by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hA, hb3, e1]⟩, ⟨k₂, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [this], by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hA, hb3, e1]⟩⟩
    · have hlt' : q.1.A (q.2 + 1) < 128 * q.1.w := by
        have := (eval_b c₁).symm.trans ht; simpa using this
      exact ⟨128 * q.1.w - q.1.A (q.2 + 1), by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hn, hA, hb1, e1], (q.1, q.2 + 1), ⟨rfl, hlt', k₁⟩, ⟨rfl, hlt', k₂⟩⟩
  · refine (two_post (Ψ := fun p s => G (p, p.K) s) (two_taint [] (fun _ _ _ _ _ _ h => by simp at h)
      (by taint_decide)) fun p s ⟨⟨h, hcf⟩, he⟩ => WP.block_nil ⟨h, ?_⟩).mono (fun _ _ h => h)
      fun _ _ ⟨p, h₁, h₂⟩ => ⟨(p, p.K), h₁, h₂⟩
    have : ¬ p.A p.K < 128 * p.w := by
      have := (eval_b hcf).symm.trans he; simpa using this
    obtain ⟨hb1, hb2, hb3⟩ := h.bnd
    obtain ⟨hK1, hK2⟩ := kBounds (w := p.w) (show 1 ≤ p.wx by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb1])
    exact ⟨by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [this], by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [hb2, hb3, hK2]⟩

/-! ## The doublings -/

def G1 (q : RXPub × Nat) (t : State) : Prop := G q t ∧ t.gpr .rcx = BitVec.ofNat 64 (q.1.A q.2) ∧ t.gpr .r12 = q.1.B
def G2 (q : RXPub × Nat) (t : State) : Prop :=
  G q t ∧ t.gpr .rcx = BitVec.ofNat 64 (q.1.A q.2 - 128 * q.1.w) ∧ t.zf = some (decide (q.1.A q.2 = 128 * q.1.w))

theorem sub_ct : RelCT isa (Two G) (seqs fixSub) (Two G2) := by
  simp only [fixSub, seqs]
  refine RelCT.seq (two_piece (Ψ := G1) [.rdi] (pins1 (fun q => off q.1.B q.1.o) fun _ _ h => h.1.rdi)
    (by taint_decide) ?_) (two_piece [.rdi, .r12] (pins2 (fun q => off q.1.B q.1.o) (fun q => q.1.B)
      fun _ _ h => ⟨h.1.1.rdi, h.2.2⟩) (by taint_decide) ?_)
  · rintro q s ⟨h, h1, h2⟩
    obtain ⟨_, _, _, hI, -⟩ := id h
    exact WP.mono (subA_ok hI.c hI.d) fun t ⟨h3, h4, hm, k⟩ =>
      ⟨⟨h.step hm k (by decide) (by decide), h1, h2⟩, h3, h4⟩
  · rintro q s ⟨⟨h, h1, h2⟩, h3, h4⟩
    obtain ⟨_, _, _, hI, _, _, -, -, hb3⟩ := id h
    exact WP.mono (subB_ok hI.c h4 h3 (by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [h2]) h1 hb3) fun t ⟨h5, h6, hm, k⟩ =>
      ⟨⟨h.step hm k (by decide) (by decide), h1, h2⟩, h5, h6⟩

theorem dbl_ct : RelCT isa (Two G2) (.ite .e (.block []) (doubles aN aAcc aTmp aY sRem)) fun _ _ => True := by
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_e h₁.2.2, eval_e h₂.2.2]) (two_taint [] (fun _ _ _ _ _ _ h => by
    simp at h) (by taint_decide)) ?_
  refine two_map (fun q => (⟨q.1.ws, q.1.A q.2 - 128 * q.1.w⟩ : DblPubW)) (fun q s ⟨⟨⟨h, h1, h2⟩, h3, h4⟩, he⟩ => ?_)
    (doubles_ctW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (sl := sRem) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))
  have hne : q.1.A q.2 ≠ 128 * q.1.w := by
    have := (eval_e h4).symm.trans he; simpa using this
  obtain ⟨_, mx, _, hI, _, _, hb1, -, -⟩ := h
  exact ⟨mx, ⟨hI.c.good, Nat.le_refl _⟩, hb1, by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [h2], by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [h1, hne], by (try simp only [RXPub.A] at *); (try simp only [RXPub.K] at *); omega_using [h2], h3, by rw [hI.v.n]; exact hI.lt⟩

/-- `r2X` leaks the same in runs with the same workspaces. -/
theorem r2X_ct (M : Mont) : RelCT isa (Two RXPre) (seqs (r2X M.mm)) fun _ _ => True := by
  unfold r2X
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [chunkWords]) (by simp [fixStart]) (RelCT.seq chunk_ct ?_)
  refine RelCT.seqs_append (by simp [fixStart]) (by simp) (RelCT.seq fs_ct ?_)
  refine RelCT.seqs_append (by simp) (by simp [fixSub]) (RelCT.seq (extra_ct M) ?_)
  exact RelCT.seqs_append (by simp [fixSub]) (by simp) (RelCT.seq sub_ct dbl_ct)

/-! ## `r2At` -/

/-- `r2At_ok`'s hypotheses. -/
def APre (sl : Nat) (p : RXPub) (s : State) : Prop :=
  ∃ (minv mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 20 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ word s.mem p.B (8 * sl) = off p.B p.o ∧
    WsAt s.mem p.B p.o p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1

/-- In the prime's workspace. -/
def E1 (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p
/-- After the reduction of `R² mod n`. -/
def E2 (p : RXPub) (s : State) : Prop :=
  ∃ mx X, SubCtx s p.B p.Z p.o p.w p.wx mx ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ RXB p ∧
    wv s.mem (off p.B p.o) (slot p.wx aXc) p.wx < X

/-- The workspace as `redc` sees it. -/
abbrev RXPub.xp (p : RXPub) : XPub := ⟨p.B, p.Z, p.o, p.w, p.wx⟩

/-- `r2At sl` leaks the same in runs with the same workspaces, given that the
taint analysis checks its load of the prime's workspace. -/
theorem r2At_ct (M : Mont) {sl : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rdi (.mem (hdr sl))]) hc).isSome = true) :
    RelCT isa (Two (APre sl)) (seqs (r2At M.mm sl)) fun _ _ => True := by
  unfold r2At
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp) (by simp [redc]) (RelCT.seq (two_piece (Ψ := E1) [.rdi]
    (pins1 (fun p => p.B) fun _ _ ⟨_, _, _, hg, _⟩ => hg.rdi) hT ?_) ?_)
  · rintro p s ⟨minv, mx, X, hg, hw8, hw20, hlo, hhi, hwx2, hwxw, hsl, hslv, hws, hX, hX1, hXo⟩
    have hs := hg.scr
    have := hdr_lt_slot p.w 8 (show sl < 32 from hsl)
    refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off p.B p.o ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hs.ld (d := 8 * sl) (by omega_using [hlo, hhi, this]), hslv]) rfl) fun t ⟨⟨hdi, hm⟩, k⟩ =>
      ⟨mx, X, SubCtx.mk' (hs.congr k.2.2) (by rw [hm]; exact hg.hdr) (by rw [hm]; exact hws) hdi hlo
        (hi_of_wsTab hhi), ⟨by rw [hm]; exact hX.n, by rw [hm]; exact hX.inv, by rw [hm]; exact hX.one⟩, hX1, hXo,
        hwx2, hwxw, hw20⟩
  refine RelCT.seqs_append (by simp [redc]) (by simp [copyArr]) (RelCT.seq (two_post (Ψ := E2)
    (two_map RXPub.xp (fun p _ ⟨mx, X, hc, hv, hX1, _, hb1, hb2, hb3⟩ => ⟨mx, X, hc, hv, hb1, hb2, show p.w < 2 ^ 30 by omega_using [hb3], hX1,
      by decide⟩) (redc_ct_of M (j := aR2) (by taint_decide))) ?_) ?_)
  · rintro p s ⟨mx, X, hc, hv, hX1, hXo, hb1, hb2, hb3⟩
    exact WP.mono (redc_ok M hc hv hb1 hb2 (by omega_using [hb3]) hX1 (j := aR2) (by decide)) fun t ⟨hc', hv', hlt, _⟩ =>
      ⟨mx, X, hc', hv', hX1, hXo, ⟨hb1, hb2, hb3⟩, hlt⟩
  refine RelCT.seqs_append (by simp [copyArr]) (by simp [r2X]) (RelCT.seq (two_post (Ψ := RXPre)
    (two_map RXPub.ws (fun _ _ ⟨mx, _, hc, _⟩ => ⟨mx, hc.good, Nat.le_refl _⟩)
      (copyArr_ct (o := aY) (a := aXc) (by decide) (by decide) (by taint_decide))) ?_) ?_)
  · rintro p s ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hlt⟩
    have hn := hc.good.scr.nowrap
    exact WP.mono (copyArr_ok hc.good (Nat.le_refl _) (by omega_using [hb1]) (by omega_using [hb2, hb3]) (o := aY) (a := aXc)
      (by decide) (by decide) (by decide)) fun t ⟨hv₃, ho₃, k₃⟩ => by
        have f₃ : Frm (off p.B p.o) (r2Ranges p.wx) s.mem t.mem :=
          Frm.of_outside (ho₃.mono (o' := slot p.wx aY) (n' := 8 * (p.wx + 2)) (Nat.le_refl _) (by omega_using []))
            (by simp [r2Ranges])
        exact ⟨mx, X, hc.of_frm f₃ (r2Ranges_ok p.wx) k₃.2.2 (k₃.gpr (by decide)), xvals_r2 hv hn (by omega_using [hb1]) f₃,
          hX1, hXo, ⟨hb1, hb2, hb3⟩, by rw [hv₃]; exact hlt⟩
  refine RelCT.seqs_append (by simp [r2X]) (by simp) (RelCT.seq (two_post (Ψ := fun p t =>
    t.gpr .rdi = off p.B p.o) (r2X_ct M) ?_) (two_taint [.rdi] (pins1 (fun p => off p.B p.o) fun _ _ h => h)
      (by taint_decide)))
  rintro p s ⟨mx, X, hc, hv, hX1, hXo, ⟨hb1, hb2, hb3⟩, hy⟩
  exact WP.mono (r2X_ok M (Pr := False) hc hv hX1 hXo hb1 hb2 hb3 hy (fun h => h.elim)) fun _ h => h.1.rdi

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: `main` is constant time but for `n`

The stages of `vg_rsa_private_crt`'s proof (`CrtCTMain.lean`), with what
`out` needs of `pre` (`ExtS`): its setup and checks (`nSetup_ct`,
`setupS_ct`, `checksS_ct`), then `r2At sWsP` and `r2At sWsQ` (`r2At_ct`) and
`out` (`out_ct`), each from the state its correctness lemma describes
(`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.PrivPre (r2At r2Phase out outArr outAt)

/-- The public data of `main`: `vg_rsa_private_crt`'s, and `pre`'s length
in bytes. -/
structure PPPub where
  c : CrtPub
  L8 : Nat

/-- What `out` needs of `pre`, at the start of `main`. -/
def ExtS (L8 : Nat) (p : CrtPub) (σ : State) : Prop :=
  (⟨p.op, L8⟩ : Region) ∈ σ.wr ∧ p.op.toNat + L8 ≤ 2 ^ 64 ∧ (∀ x, ofs p.B x < p.Z → L8 ≤ ofs p.op x) ∧
    L8 = 8 * (2 * p.w + wsWords p.pl + wsWords p.ql)

/-- A stage, with `ExtS`. -/
def RX (L8 : Nat) (R : StageRel) : StageRel := fun p σ xb pb qb dpb dqb qib t =>
  R p σ xb pb qb dpb dqb qib t ∧ ExtS L8 p σ

/-- A state at a stage of `main`. -/
def SX (R : StageRel) (q : PPPub) (t : State) : Prop := Stage (RX q.L8 R) q.c t

theorem stageX_step {R R' : StageRel} {c : Prog isa} (hct : RelCT isa (Two (Stage R)) c fun _ _ => True)
    (hw : ∀ p σ xb pb qb dpb dqb qib t,
      CrtPre σ p.B p.Z p.k p.op p.np p.ip p.pp p.qp p.dpp p.dqp p.qip p.pl p.ql p.nb xb pb qb dpb dqb qib →
      Spec.Rsa.modulusValid p.N p.k = true → R p σ xb pb qb dpb dqb qib t →
      WP isa c t (R' p σ xb pb qb dpb dqb qib)) :
    RelCT isa (Two (SX R)) c (Two (SX R')) :=
  two_post (two_map PPPub.c (fun _ _ ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, _⟩ =>
      ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr⟩) hct)
    fun _ _ ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, hr, hx⟩ =>
      WP.mono (hw _ _ _ _ _ _ _ _ _ h hv hr) fun _ h' => ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, h', hx⟩

/-- `main`'s setup and checks. -/
theorem front_ctX (M : Mont) :
    RelCT isa (Two (SX R0)) (seqs (nSetup M.mm ++ primesSetup ++ checks)) (Two (SX R3)) := by
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [checks]) (RelCT.seq (R := Two (SX R2)) ?_ ?_)
  · refine RelCT.seqs_append (by simp [nSetup]) (by simp [primesSetup]) (RelCT.seq (R := Two (SX R1)) ?_ ?_)
    · exact stageX_step (nSetup_ct M) fun p σ xb _ _ _ _ _ _ h hv ht => by
        subst ht; exact WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ => ⟨minv, hr⟩
    · exact stageX_step ((setupS_ct setup_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
        fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, hr⟩ => WP.mono (setupPart_ok h hr) fun _ h' => ⟨minv, h'⟩
  · exact stageX_step ((checksS_ct checks_ct).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
        WP.mono (checksPart_ok h hv hr) fun _ ⟨mp', mq', h'⟩ => ⟨minv, mp', mq', h'⟩

/-- After `R_p² mod p`. -/
def RM : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, R2Mid σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

/-- After `R_q² mod q`. -/
def RD : StageRel := fun p σ xb pb qb _ _ qib t => ∃ minv mp mq, R2Done σ t p.B p.Z p.w p.pl p.ql minv mp mq p.N
  (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (p.mask xb pb qb qib)

/-- `R_p² mod p`. -/
theorem r2P_ctX (M : Mont) : RelCT isa (Two (SX R3)) (seqs (r2At M.mm sWsP)) (Two (SX RM)) := by
  refine stageX_step ((r2At_ct M (by taint_decide)).mono
    (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offP p.w, wsWords p.pl⟩ : RXPub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      WP.mono (r2P_ok M h hv hr rfl) fun _ h' => ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, hP', -⟩ := mask_facts (rfl : p.mask xb pb qb qib = _) hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hZq := h.z
  exact ⟨minv, hr.nv, minv, mp, _, hr.good, by dsimp only [CrtPub.w]; omega_using [hk1], by dsimp only [CrtPub.w]; omega_using [hk2],
    Nat.le_refl _, by dsimp only [CrtPub.w] at *; unfold offQ at hZq; unfold offP; omega_using [hZq],
    by dsimp only; unfold wsWords; omega_using [], wsWords_le (by dsimp only [CrtPub.w]; omega_using [hpl2]) (by dsimp only [CrtPub.w]; omega_using [hk1]),
    by decide, hr.wsP, hr.pws, hr.pxv, hP'.1, hP'.2⟩

/-- `R_q² mod q`. -/
theorem r2Q_ctX (M : Mont) : RelCT isa (Two (SX RM)) (seqs (r2At M.mm sWsQ)) (Two (SX RD)) := by
  refine stageX_step ((r2At_ct M (by taint_decide)).mono
    (fun _ _ h => two_stage (fun p _ => (⟨p.B, p.Z, p.w, offQ p.w p.pl, wsWords p.ql⟩ : RXPub))
      (fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ => ?_) h) fun _ _ h => h)
    fun p σ xb pb qb dpb dqb qib t h hv ⟨minv, mp, mq, hr⟩ =>
      WP.mono (r2Q_ok M h hv hr rfl) fun _ h' => ⟨minv, mp, mq, h'⟩
  obtain ⟨hodd, hN1, hPN, hQN⟩ := crt_bounds h hv
  obtain ⟨-, -, hQ'⟩ := mask_facts (rfl : p.mask xb pb qb qib = _) hodd hPN hQN
  have hk1 := h.k1
  have hk2 := h.k2
  have hql2 := h.ql2
  have hZq := h.z
  exact ⟨minv, hr.nv, minv, mq, _, hr.good, by dsimp only [CrtPub.w]; omega_using [hk1], by dsimp only [CrtPub.w]; omega_using [hk2],
    by dsimp only; unfold offQ; omega_using [], hZq,
    by dsimp only; unfold wsWords; omega_using [], wsWords_le (by dsimp only [CrtPub.w]; omega_using [hql2]) (by dsimp only [CrtPub.w]; omega_using [hk1]),
    by decide, hr.wsQ, hr.qws, hr.qxv, hQ'.1, hQ'.2⟩

/-- `out`. -/
theorem out_ctX : RelCT isa (Two (SX RD)) (seqs out) fun _ _ => True := by
  refine two_map (fun q : PPPub => (⟨q.c.B, q.c.Z, q.c.w, offP q.c.w, wsWords q.c.pl, offQ q.c.w q.c.pl,
    wsWords q.c.ql, q.c.op, q.L8⟩ : OPub))
    (fun q t ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, ⟨minv, mp, mq, hr⟩, hx⟩ => ?_) out_ct
  obtain ⟨hwr, hL, hS, hL8⟩ := hx
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.z
  have hP8 : 256 ≤ slot (wsWords q.c.pl) 8 := by unfold slot hdrBytes; omega_using []
  have hout : word t.mem q.c.B (8 * sOut) = q.c.op := (hr.hfix sOut (by decide) (by decide)).trans h.hO
  have hwr' : (⟨q.c.op, q.L8⟩ : Region) ∈ t.wr := by rw [hr.keep.2.2]; exact hwr
  refine ⟨minv, mp, mq, hr.good, hout, hr.wsP, hr.wsQ, hr.pws, hr.qws, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hL, hwr', hS⟩
  all_goals try dsimp only [CrtPub.w] at *
  all_goals try unfold offQ at *
  all_goals try unfold offP at *
  all_goals try unfold wsWords at *
  all_goals omega_arith

/-- `main` leaks the same in runs that agree on the public data. -/
theorem main_ct (M : Mont) : RelCT isa (Two (SX R0)) (PrivPre.main M.mm) fun _ _ => True := by
  unfold PrivPre.main
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [out]) (RelCT.seq (R := Two (SX RD)) ?_ out_ctX)
  refine RelCT.seqs_append (by simp [nSetup]) (by simp [r2Phase, r2At]) (RelCT.seq (front_ctX M) ?_)
  exact RelCT.seqs_append (by simp [r2At]) (by simp [r2At]) (RelCT.seq (r2P_ctX M) (r2Q_ctX M))

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: constant time but for `n`

`entry`, `zeroPre` and the modulus' check leak the same in runs that agree
on the public data (the arguments but `p`'s and `q`'s bytes, and `n`), and
so do `fail` and `main` (`main_ct`): `code_ct`, and the contract's
`ConstantTime` (`code_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of `vg_rsa_private_precompute`: `main`'s, the stack
pointer and `pre`'s length. -/
structure PCPub where
  q : PPPub
  rsp : Addr
  rsi : BitVec 64

/-- A state the contract allows, with the public data `P`. -/
def PRel (P : PCPub) (s : State) : Prop :=
  ppContract.pre s ∧ s.gpr .rsp = P.rsp ∧ s.gpr .rsi = P.rsi ∧ (s.gpr .rsi).toNat * 8 = P.q.L8 ∧
    stackArg s 2 = P.q.c.B ∧ (stackArg s 3).toNat * 8 = P.q.c.Z ∧ (s.gpr .rcx).toNat = P.q.c.k ∧
    s.gpr .rdi = P.q.c.op ∧ s.gpr .rdx = P.q.c.np ∧ s.gpr .rdi = P.q.c.ip ∧ s.gpr .r8 = P.q.c.pp ∧
    stackArg s 0 = P.q.c.qp ∧ s.gpr .r8 = P.q.c.dpp ∧ stackArg s 0 = P.q.c.dqp ∧ s.gpr .rdi = P.q.c.qip ∧
    (s.gpr .r9).toNat = P.q.c.pl ∧ (stackArg s 1).toNat = P.q.c.ql ∧
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = P.q.c.nb

theorem entry_split : PrivPre.entry =
    ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++ PrivPre.entry.drop 1 := rfl

/-- What the rest of the code needs after `entry`. -/
def Cont (s t : State) : Prop :=
  t.gpr .rdi = stackArg s 2 ∧ t.gpr .rsi = s.gpr .rsi ∧ Scr t (stackArg s 2) ((stackArg s 3).toNat * 8) ∧
    word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧
    WP isa PrivPre.zeroPre t fun t₂ => t₂.gpr .rdi = stackArg s 2 ∧
      WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s)

/-- After `entry`'s first instruction. -/
def C1 (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .r11 = P.q.c.B ∧ t.gpr .rsp = P.rsp ∧ WP isa (.block (PrivPre.entry.drop 1)) t (Cont s)

/-- After `entry`. -/
def C2 (P : PCPub) (t : State) : Prop := ∃ s, PRel P s ∧ Cont s t

theorem entry_ct : RelCT isa (Two PRel) (.block PrivPre.entry) (Two C2) := by
  rw [entry_split]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
    (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
  intro P s hs
  have c := ppCtx_of hs.1
  have hZ := c.hZ
  have hk1 := c.hk1
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  have hpl2 := c.hpl2
  have hql2 := c.hql2
  have hk2 := c.hk2
  have hh : WP isa (.block PrivPre.entry) s (Cont s) :=
    WP.mono (WP.and (head_ok c) (entry_ok c)) fun t ⟨hw, hdi, _, hO, _, _, _, _, _, _, _, _, _, _, _, k⟩ =>
      ⟨hdi, k.gpr (by decide), c.hs.congr k.2.2, hO, WP.mono (WP.and hw (zeroPre_ok (c.hs.congr k.2.2) hdi
        (by omega_using [hZ]) (L := (s.gpr .rsi).toNat) (by omega_using [hL]) (by omega_using [hL, hpl2, hql2, hk2])
        (by rw [k.gpr (by decide), ofNat_toNat_self]) hO (fun j hj => by rw [k.2.2]; exact c.hout j hj)))
        fun t₂ ⟨hr, _, _, k₂⟩ => ⟨(k₂.gpr (by decide)).trans hdi, hr⟩⟩
  rw [entry_split, WP.block_append_iff] at hh
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
  refine WP.mono (WP.and hh (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 2)
    (by xrun [State.ea, e2, c.ha 2 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
      ⟨s, hs, h11.trans hs.2.2.2.2.1, (k.gpr (by decide)).trans hs.2.1, hw⟩

/-- Before `zeroPre`'s loop. -/
def C2b (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .rsi = P.q.c.op ∧ t.gpr .rcx = BitVec.ofNat 64 P.q.L8 ∧ t.gpr .rdi = P.q.c.B ∧
    WP isa (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) t
      fun t₂ => t₂.gpr .rdi = stackArg s 2 ∧
        WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t₂ (PPHead s)

/-- After `zeroPre`. -/
def C3 (P : PCPub) (t : State) : Prop :=
  ∃ s, PRel P s ∧ t.gpr .rdi = P.q.c.B ∧ WP isa (.block [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))]) t
    (PPHead s)

theorem zero_ct : RelCT isa (Two C2) PrivPre.zeroPre (Two C3) := by
  unfold PrivPre.zeroPre
  refine RelCT.seq (two_piece (Ψ := C2b) [.rdi, .rsi] (fun P s₁ s₂ ⟨σ₁, h₁, c₁⟩ ⟨σ₂, h₂, c₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [c₁.1, c₂.1, h₁.2.2.2.2.1, h₂.2.2.2.2.1]
      · rw [c₁.2.1, c₂.2.1, h₁.2.2.1, h₂.2.2.1]) (by taint_decide) ?_)
    (two_post (two_taint [.rsi, .rcx, .rdi] (fun P s₁ s₂ ⟨_, _, a₁, b₁, d₁, _⟩ ⟨_, _, a₂, b₂, d₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂]
      · rw [b₁, b₂]
      · rw [d₁, d₂]) (by taint_decide))
      fun P t ⟨s, hs, _, _, _, hw⟩ => WP.mono hw fun t₂ ⟨hdi, hr⟩ => ⟨s, hs, hdi.trans hs.2.2.2.2.1, hr⟩)
  rintro P t ⟨s, hs, hdi, hsi, hsc, hO, hw⟩
  have hn := hsc.nowrap
  have c := ppCtx_of hs.1
  have hZ := c.hZ
  have hk1 := c.hk1
  have hL := c.hL
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at hL
  unfold PrivPre.zeroPre at hw
  rw [WP.seq_iff] at hw
  have hl : InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * sOut)) 8 := hsc.ld (by unfold sOut sFn; omega_using [hZ])
  refine WP.mono (WP.and hw (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
      t'.gpr .rcx = BitVec.ofNat 64 ((s.gpr .rsi).toNat * 8))
    (by xrun [State.ea, hdr, hdi, hdrOff, hl, hO, hsi, eight_w _ (ofNat_toNat_self (s.gpr .rsi)).symm]) rfl))
    fun t' ⟨hw', ⟨hsi', hcx'⟩, k⟩ => ⟨s, hs, by rw [hsi', hs.2.2.2.2.2.2.2.1], by rw [hcx', hs.2.2.2.1],
      by rw [k.gpr (by decide), hdi, hs.2.2.2.2.1], hw'⟩

/-- After the reloads. -/
def C4 (P : PCPub) (t : State) : Prop := ∃ s, PRel P s ∧ PPHead s t

/-- After the modulus' check. -/
def C5 (P : PCPub) (t : State) : Prop :=
  ∃ s t₁, PRel P s ∧ PPHead s t₁ ∧ t.mem = t₁.mem ∧ Keep [.rax, .rbp, .rsi] t₁ t ∧
    t.zf = some (Spec.Rsa.modulusValid P.q.c.N P.q.c.k)

theorem check_ct : RelCT isa (Two C3)
    (.block (([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid)) (Two C5) := by
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := C4) [.rdi] (fun P s₁ s₂ ⟨_, _, a₁, _⟩ ⟨_, _, a₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [a₁, a₂]) (by taint_decide)
      fun P t ⟨s, hs, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩)
    (two_piece [.rdx, .rcx] (fun P s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.rdx, h₂.rdx, c₁.2.2.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.2.2.1]
      · rw [h₁.rcx, h₂.rcx, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]) (by taint_decide) ?_))
  rintro P t ⟨s, hs, h⟩
  have c := ppCtx_of hs.1
  have hnb := Src.of_head (t := t) c.hnb (by rw [bytesAt_length]; exact c.hon) h.frame h.keep.2.1 h.keep.2.2
  obtain ⟨-, -, -, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hn⟩ := id hs
  refine WP.mono (invalid_ok h.rdx h.rcx c.hk1 c.hk2 (bytesAt_length _ _ _) (fun i hi => hnb.rd i (by
    rw [bytesAt_length]; exact hi)) (fun i hi => hnb.val i _)) fun t' ⟨hz, hm, k⟩ => ⟨s, t, hs, h, hm, k, ?_⟩
  rw [hz, CrtPub.N, ← hn, hk]

theorem fail_ct : RelCT isa (Two fun P t => C5 P t ∧ isa.eval .ne t = some true) fail fun _ _ => True := by
  unfold fail
  have pin : ∀ P t, (C5 P t ∧ isa.eval .ne t = some true) → t.gpr .rdi = P.q.c.B := fun P t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩ =>
    (k.gpr (by decide)).trans (h.rdi.trans hs.2.2.2.2.1)
  refine RelCT.seq (two_piece (Ψ := fun (P : PCPub) t => t.gpr .rsi = P.q.c.op ∧
      t.gpr .rcx = BitVec.ofNat 64 P.q.c.k ∧ t.gpr .rdi = P.q.c.B) [.rdi]
    (fun P s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pin P s₁ h₁, pin P s₂ h₂]) (by taint_decide) ?_)
    (two_taint [.rsi, .rcx, .rdi] (fun P s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
  rintro P t ⟨⟨s, t₁, hs, h, hm, k, _⟩, _⟩
  have c := ppCtx_of hs.1
  have hpre := ppPre_of c h hm k
  have hn := hpre.scr.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off (stackArg s 2) (8 * i)) 8 := fun i hi =>
    hpre.scr.ld (by omega_using [hZ, hi])
  refine WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t' => t'.gpr .rsi = s.gpr .rdi ∧
      t'.gpr .rcx = BitVec.ofNat 64 (s.gpr .rcx).toNat) (by
    xrun [State.ea, hdr, hpre.rdi, hdrOff, hl sOut (by decide), hl sK (by decide), hpre.hO, hpre.hK]) rfl)
    fun t' ⟨⟨hsi, hcx⟩, k'⟩ => ⟨by rw [hsi, hs.2.2.2.2.2.2.2.1], by rw [hcx, hs.2.2.2.2.2.2.1],
      (k'.gpr (by decide)).trans (hpre.rdi.trans hs.2.2.2.2.1)⟩

/-- `main`'s stages from the modulus' check, for a valid modulus. -/
theorem toSX {P : PCPub} {t : State} (h : C5 P t ∧ isa.eval .ne t = some false) : SX R0 P.q t := by
  obtain ⟨⟨s, t₁, hs, hh, hm, k, hz⟩, he⟩ := h
  have c := ppCtx_of hs.1
  have hpre := ppPre_of c hh hm k
  have hv : Spec.Rsa.modulusValid P.q.c.N P.q.c.k = true := by simp only [eval, hz] at he; simpa using he
  obtain ⟨-, -, hsi, hL8, hB, hZ, hk, hop, hnp, hip, hpp, hqp, hdpp, hdqp, hqip, hpl, hql, hnb⟩ := hs
  have kk := hh.keep.trans k
  refine ⟨t, List.replicate (s.gpr .rcx).toNat 0, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat,
    Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat, List.replicate (s.gpr .r9).toNat 0, ?_, hv, rfl,
    ?_, ?_, ?_, ?_⟩
  · rw [← hnb, ← hB, ← hZ, ← hk, ← hop, ← hnp, ← hip, ← hpp, ← hqp, ← hdpp, ← hdqp, ← hqip, ← hpl, ← hql]
    exact hpre
  · rw [kk.2.2, ← hop, ← hL8]; exact c.hpreR
  · rw [← hop, ← hL8]; exact c.hwrap
  · rw [← hop, ← hL8, ← hB, ← hZ]; exact c.hS
  · rw [← hL8, preWords c, CrtPub.w, ← hk, ← hpl, ← hql]; omega_using []

/-- `vg_rsa_private_precompute` leaks the same in runs that agree on the
public data. -/
theorem code_ct (M : Mont) : RelCT isa (Two PRel) (PrivPre.code M.mm) fun _ _ => True := by
  unfold PrivPre.code
  refine RelCT.seq entry_ct (RelCT.seq zero_ct (RelCT.seq check_ct (two_ite (fun P s₁ s₂ h₁ h₂ => ?_)
    fail_ct ((main_ct M).mono (fun _ _ h => two_bind (fun P t₁ t₂ h₁ h₂ => ⟨P.q, toSX h₁, toSX h₂⟩) h)
      fun _ _ h => h))))
  obtain ⟨_, _, _, _, _, _, z₁⟩ := h₁
  obtain ⟨_, _, _, _, _, _, z₂⟩ := h₂
  simp only [eval, z₁, z₂]

/-- The public data of a state. -/
def pcPubOf (s : State) : PCPub :=
  ⟨⟨⟨stackArg s 2, (stackArg s 3).toNat * 8, (s.gpr .rcx).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .rdi, s.gpr .r8,
    stackArg s 0, s.gpr .r8, stackArg s 0, s.gpr .rdi, (s.gpr .r9).toNat, (stackArg s 1).toNat,
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩, (s.gpr .rsi).toNat * 8⟩, s.gpr .rsp, s.gpr .rsi⟩

/-- `vg_rsa_private_precompute` is constant time but for `n`. -/
theorem code_constantTime (M : Mont) : ConstantTime isa ppContract.pre ppContract.pub (PrivPre.code M.mm) := by
  refine RelCT.constantTime ((code_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pcPubOf s₁, ?_, ?_⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, hn⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), r .rsi (by decide), by rw [r .rsi (by decide)]; rfl, a2.symm,
      by rw [← a3]; rfl, by rw [r .rcx (by decide)]; rfl, r .rdi (by decide), r .rdx (by decide),
      r .rdi (by decide), r .r8 (by decide), a0.symm, r .r8 (by decide), a0.symm, r .rdi (by decide),
      by rw [r .r9 (by decide)]; rfl, by rw [← a1]; rfl, hn.symm⟩

end VG.Proof.Bignum.X86_64.PrivPre

end

end

/-!
# `vg_rsa_private_precompute` on x86-64: verified

With Montgomery multiplication by calls (`CallMont`), whose code inlined is
`PrivPre.code M.mm` for the `Mont` the calls run as: its correctness
(`code_correct`), constant time (`code_constantTime`), the contract on the
registers implying the shared one with 8 bytes of stack (`pp_implies`), and
a postcondition that reads memory only in `pre` (`pp_patch`, `pp_postOut`,
for `X86_64.Scrub.withScrubAll`); and the `Verified` the registration uses
(`pp_verified`, `ppAdx_verified`), from the checks the kernel evaluates on
the code (that it inlines, and that it never loads MXCSR).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64
/-- The postcondition reads memory only in `pre`, apart from the 8 bytes
below `rsp`. -/
theorem pp_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : ppContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : ppContract.post s b) :
    ppContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have c := ppCtx_of hs
  have hm := Clear.miss_wr hc c.hpreR c.hwrap (k := (s.gpr .rsi).toNat * 8) (Nat.le_refl _)
  simp only [ppContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, wordsAt_overlay fun i hi => hm i (by omega_using [hi])]
  exact hp

theorem pp_call_verified (M : Mont) {c : Prog isa} (hc : c.InlineOk = true) (hin : c.inline = PrivPre.code M.mm)
    (hmx : (PrivPre.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.privatePrecomputeContract abi 8) :=
  Proof.Rsa.X86_64.Verified.of_inline_sig hc (hin ▸ code_correct M hmx) (hin ▸ code_constantTime M) pp_implies
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) pp_patch

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega_using [hk, ht, this]) (by omega_using [hk, hN, ht, this]))).symm

open VG.X86_64.Scrub in
/-- The postcondition reads memory on return only in `pre`. -/
theorem pp_postOut (stack : Nat) :
    PostOut (Spec.Rsa.privatePrecomputeContract abi stack) (Spec.Rsa.privatePrecomputeSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h hpre ⊢
    obtain ⟨hk, hpl1, hpl2, hql1, hql2, hL, -⟩ := hpre
    have hk2 := hk.2
    simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
      Spec.Rsa.modulusWords] at hL
    rw [wordsAt_congr (q := ArgWord.addr.ofRaw pre) (k := BitVec.toNat ((ArgWord.int abi.ptrBits).ofRaw preLen))
      (N := BitVec.toNat ((ArgWord.int abi.ptrBits).ofRaw preLen) * 8) (by omega_using []) (by omega_using [hpl2, hql2, hL, hk2]) hb.1]
    exact h
theorem pp_verified :
    Verified target (Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.privatePrecomputeContract abi 8) :=
  pp_call_verified Mont.fnBase (by decide +kernel) rfl (by decide +kernel)

theorem ppAdx_verified :
    Verified target (Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.privatePrecomputeContract abi 8) :=
  pp_call_verified Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)

end VG.Proof.Bignum.X86_64.PrivPre
