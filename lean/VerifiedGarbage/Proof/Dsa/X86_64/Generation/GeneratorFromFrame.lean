module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorArguments
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! ### `Dsa.X86_64.Generation.GeneratorCheck`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorRange`, which only this module used -/

section

/-! # Exact range filtering of each public generator input -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Impl.Bignum.X86_64

theorem generatorRange_ok {s : State} {B pp hp : Addr} {Z w : Nat} {pb hb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = hp) (xlen : word s.mem B 152 = BitVec.ofNat 64 hb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z hp hb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ hb.length) (hxw : hb.length ≤ 8 * w) (hodd : Spec.Rsa.os2ip pb % 2 = 1) :
    WP isa Impl.Dsa.X86_64.Generation.generatorRange s fun t =>
      t.gpr .rax = mask (decide (1 < Spec.Rsa.os2ip hb ∧ Spec.Rsa.os2ip hb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorRange
  refine WP.seq (WP.mono (generatorLoadPair_ok h hptr hlen xptr xlen sp sx hp1 hpw hx1 hxw)
    fun v ⟨hv, vp, vx, fv, kv⟩ => ?_)
  refine WP.seq (WP.mono (decrementOdd_ok hv (by decide : 0 < 16) (by rw [vp]; exact hodd))
    fun z ⟨hz, zp, fz, kz⟩ => ?_)
  have zx : wv z.mem B (slot w 1) w = Spec.Rsa.os2ip hb := by
    rw [fz.wv (Or.inr (by simp only [slot, hdrBytes]; omega_using []))
      (by have := h.sl (by decide : 1 < 16); have := h.scr.nowrap; omega_arith), vx]
  refine WP.mono (VG.Proof.Dsa.X86_64.rangeMask_ok hz.good.1 hz.good.2 h.w1 (by have := h.w2; omega_using [this]) true)
    fun t ⟨htmask, hm, kt⟩ => ?_
  have ht : Ws t B Z w := hz.congr (by rw [hm]; exact Frm.refl B [] _)
    (by simp) kt (by decide)
  refine ⟨?_, ht, ?_, ((kv.trans kz).trans kt).mono (by decide)⟩
  · simpa only [VG.Impl.Bignum.X86_64.Public.aX, VG.Impl.Bignum.X86_64.Public.aN, ite_true, zx, zp, vp] using htmask
  · have fz' : Frm B [ar w 0, ar w 1] v.mem z.mem :=
      Frm.of_outside (fz.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp [ar])
    rw [hm]
    exact fv.trans fz'

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorResult`, which only this module used -/

section

/-! # Accept the computed generator exactly when it is greater than one -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Impl.Bignum.X86_64

theorem generatorResult_ok {s : State} {B pp gp : Addr} {Z w : Nat} {pb gb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = gp) (xlen : word s.mem B 152 = BitVec.ofNat 64 gb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z gp gb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ gb.length) (hxw : gb.length ≤ 8 * w) (hlt : Spec.Rsa.os2ip gb < Spec.Rsa.os2ip pb) :
    WP isa Impl.Dsa.X86_64.Generation.generatorResult s fun t =>
      t.gpr .rax = mask (decide (1 < Spec.Rsa.os2ip gb)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorResult
  refine WP.seq (WP.mono (generatorLoadPair_ok h hptr hlen xptr xlen sp sx hp1 hpw hx1 hxw)
    fun u ⟨hu, up, ug, fu, ku⟩ => ?_)
  refine WP.mono (VG.Proof.Dsa.X86_64.rangeMask_ok hu.good.1 hu.good.2 h.w1 (by have := h.w2; omega_using [this]) true)
    fun t ⟨htmask, hm, kt⟩ => ?_
  refine ⟨?_, hu.congr (by rw [hm]; exact Frm.refl B [] _) (by simp) kt (by decide),
    hm ▸ fu, (ku.trans kt).mono (by decide)⟩
  simpa only [VG.Impl.Bignum.X86_64.Public.aX, VG.Impl.Bignum.X86_64.Public.aN, ite_true, ug, up, hlt, and_true] using htmask

end VG.Proof.Dsa.X86_64.Generation

end

end


/-! # Common frame binding for generator-input and generator-result checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem generatorCheck_ok {s : State} {B F : Addr} {Z w len : Nat} {W : Nat → BitVec 64}
    {pb xb : List Byte} (result : Bool) (h : Ws s B Z w) (hl : len < 2 ^ 31)
    (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (sp : Src s B Z (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sx : Src s B Z (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) xb)
    (hp : pb.length = len) (hx : xb.length = len) (hpos : 1 ≤ len) (hfit : len ≤ 8 * w)
    (hodd : result = false → Spec.Rsa.os2ip pb % 2 = 1)
    (hresult : result = true → Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb) :
    WP isa (.seq (.block (headerArguments (generatorRangeArguments len result)))
      (if result then generatorResult else generatorRange)) s fun t =>
      t.gpr .rax = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [(128, 128), ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (generatorArguments_ok h hl result hsp hr hwords hsep)
    fun u ⟨hu, up, upl, ux, uxl, fu, ku⟩ => ?_)
  have ff : Frm B [(128, 128)] s.mem u.mem := Frm.of_outside fu (by simp)
  have hb : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ Z := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.h256
  have spu := sp.congrK (InScr.of_frm ff hb) ku
  have sxu := sx.congrK (InScr.of_frm ff hb) ku
  have check : WP isa (if result then generatorResult else generatorRange) u fun t =>
      t.gpr .rax = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Ws t B Z w ∧ Frm B [ar w 0, ar w 1] u.mem t.mem ∧ Keep mmRegs u t := by
    cases result with
    | false =>
      exact generatorRange_ok hu up (by rw [hp]; exact upl) ux (by rw [hx]; exact uxl)
        spu sxu (by omega_using [hp, hpos]) (by omega_using [hp, hfit]) (by omega_using [hx, hpos]) (by omega_using [hx, hfit]) (hodd rfl)
    | true =>
      exact generatorResult_ok hu up (by rw [hp]; exact upl) ux (by rw [hx]; exact uxl)
        spu sxu (by omega_using [hp, hpos]) (by omega_using [hp, hfit]) (by omega_using [hx, hpos]) (by omega_using [hx, hfit]) (hresult rfl)
  exact WP.mono check fun t ⟨hm, ht, ft, kt⟩ =>
    ⟨hm, ht, (ff.mono (by simp)).trans (ft.mono (fun r hr => List.mem_cons_of_mem _ hr)),
      (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Complete generator range checks from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorFromFrame_ok {s : State} {B F S : Addr} {Z len : Nat}
    {V : Nat → Byte} {W : Nat → BitVec 64} {pb xb : List Byte} (result : Bool)
    (L : Lay s F S) (R : Rep s.mem F S V W) (hs : Scr s B Z)
    (hB : W 5 + BitVec.ofNat 64 arithmetic = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (hZ : slot (len / 8) 16 ≤ Z)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (hframe : ∀ k < 37, ∀ i < 8, Z ≤ ofs B (off (off F (8 * k)) i))
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨B, Z⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨B, Z⟩)
    (sp : Src s B Z (off (W 5) Impl.Dsa.Generation.Layout.p) pb)
    (sx : Src s B Z (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) xb)
    (hp : pb.length = len) (hx : xb.length = len)
    (hodd : result = false → Spec.Rsa.os2ip pb % 2 = 1)
    (hresult : result = true → Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len result) s fun t =>
      t.gpr .rax = mask (decide (if result then 1 < Spec.Rsa.os2ip xb
        else 1 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip pb - 1)) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧ Ws t B Z (len / 8) ∧
      Frame [⟨B, Z⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hb : 2 ≤ len / 8 ∧ len / 8 < 2 ^ 24 ∧ 1 ≤ len ∧ len < 2 ^ 31 ∧ len ≤ 8 * (len / 8) := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  unfold Impl.Dsa.X86_64.Generation.generatorRangeFromFrame
  simp only [seqs]
  refine WP.seq (WP.mono (workspaceBase_ok L R hB) fun u ⟨hdi, hm, ku⟩ => ?_)
  have spu := sp.congrK (fun a _ => by rw [hm]) ku
  have sxu := sx.congrK (fun a _ => by rw [hm]) ku
  refine WP.seq (WP.mono (workspace_ok (hs.congr ku.2.2) hdi hZ hb.1 hb.2.1)
    fun v ⟨hv, _, fv, kv⟩ => ?_)
  have bounds : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega_using [hz]
  refine WP.mono (generatorCheck_ok result hv hb.2.2.2.1
    ((kv.gpr (by decide)).trans ((ku.gpr (by decide)).trans L.rsp))
    (fun k hk => by rw [kv.2.1, kv.2.2, ku.2.1, ku.2.2]; exact L.ld (by unfold frameBytes; omega_using [hk]))
    (fun k hk => by rw [frame_word_of_workspace fv bounds (hframe k hk), hm]; exact R.fr k hk)
    hsep (spu.congrK (InScr.of_frm fv bounds) kv) (sxu.congrK (InScr.of_frm fv bounds) kv)
    hp hx hb.2.2.1 hb.2.2.2.2 hodd hresult) fun t ⟨hr, ht, ft, kt⟩ => ?_
  have allk := (ku.trans kv).trans kt
  have ff : Frame [⟨B, Z⟩] s.mem t.mem := by
    intro a ha
    have hn := ha ⟨B, Z⟩ (by simp)
    change ¬ ofs B a < Z at hn
    rw [ft a (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> right
      · exact Nat.le_trans hz (by omega_using [hn])
      · exact Nat.le_trans (hZ.trans' (slot_lt (by decide : 0 < 16))) (by omega_using [hn])
      · exact Nat.le_trans (hZ.trans' (slot_lt (by decide : 1 < 16))) (by omega_using [hn])),
      fv a (fun r hr => Or.inr (Nat.le_trans (bounds r hr) (by omega_using [hn]))), hm]
  have Rt := rep_of_disjoint_frame R ff
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hF)
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact hS)
  exact ⟨hr, lay_of_rep L R Rt rfl (allk.gpr (by decide)) allk.2.2, Rt, ht, ff, allk.mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
