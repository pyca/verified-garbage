module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
public import VerifiedGarbage.Spec.Dsa.Generate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Chunks
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Call
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.X86_64.PublicCalls
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Spec.Dsa
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.WorkspaceBase
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import Mathlib.Tactic.Attr.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! ### `Dsa.X86_64.Generation.GeneratorStages`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorInput`, which this module and modules that import it used -/

section

/-! # Bind the current generator candidate to the reusable exponentiation parent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout

theorem generatorInput_ok {s : State} {F S B hp : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hB : W 5 = B) (hh : W 21 = hp)
    (hout : InRegions s.wr (off B 272) 8) :
    WP isa (.block Impl.Dsa.X86_64.Generation.generatorInput) s fun t =>
      t.gpr .rdi = B ∧ word t.mem B 272 = hp ∧
      Outside B 272 8 s.mem t.mem ∧ Keep [.rdi, .rax] s t := by
  refine WP.mono (WP.keep [.rdi, .rax] (Q := fun t =>
      t.gpr .rdi = B ∧ t.mem = s.mem.writeW (off B 272) hp) (by
    xrun [Impl.Dsa.X86_64.Generation.generatorInput, ea_sp, L.rsp, Core.field, Field.offset,
      State.ea, BitVec.ofInt_natCast, Impl.Mgf1.X86_64.sp,
      L.ld (d := 40) (by decide), L.ld (d := 168) (by decide),
      R.slot (d := 40) (k := 5) rfl (by decide) hB,
      R.slot (d := 168) (k := 21) rfl (by decide) hh, hout]) rfl)
    fun t ⟨⟨hdi, hm⟩, hk⟩ => ?_
  refine ⟨hdi, ?_, ?_, hk⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorModulus`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorFields`, which this module and modules that import it used -/

section

/-! # Initialize the generator exponentiation's saved parent operands -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64 VG.Impl.Dsa.Layout

theorem generatorFields_ok {s : State} {B : Addr} {Z w len : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : 336 ≤ Z) (hlen : len < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.generatorFields len)) s fun t =>
      Good t B Z w mi ∧
      word t.mem B 256 = off B VG.Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 288 = off B VG.Impl.Dsa.Generation.Layout.exponent ∧
      word t.mem B 328 = BitVec.ofNat 64 len ∧
      word t.mem B 272 = word s.mem B 272 ∧
      Outside B 256 80 s.mem t.mem ∧ Keep [.rax] s t := by
  have hv : (BitVec.ofNat 32 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  let m1 := s.mem.writeW (off B 256) (off B VG.Impl.Dsa.Generation.Layout.p)
  let m2 := m1.writeW (off B 288) (off B VG.Impl.Dsa.Generation.Layout.exponent)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m2.writeW (off B 328) (BitVec.ofNat 64 len)) (by
    xrun [Impl.Dsa.X86_64.Generation.generatorFields, Core.field, Field.offset, State.ea, BitVec.ofInt_natCast, h.rdi,
      h.scr.st (d := 256) (by omega_using [hZ]), h.scr.st (d := 288) (by omega_using [hZ]), h.scr.st (d := 328) (by omega_using [hZ]),
      sx_ofNat (by decide : VG.Impl.Dsa.Generation.Layout.p < 2 ^ 31),
      sx_ofNat (by decide : VG.Impl.Dsa.Generation.Layout.exponent < 2 ^ 31), hv]
    rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have f1 : Outside B 256 8 s.mem m1 := writeW_outside _ _ _ (by decide)
  have f2 : Outside B 288 8 m1 m2 := writeW_outside _ _ _ (by decide)
  have f3 : Outside B 328 8 m2 t.mem := by rw [hm]; exact writeW_outside _ _ _ (by decide)
  have ff : Outside B 256 80 s.mem t.mem :=
    ((f1.mono (by decide) (by decide)).trans (f2.mono (by decide) (by decide))).trans
      (f3.mono (by decide) (by decide))
  refine ⟨⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi, ?_⟩, ?_, ?_, ?_, ?_, ff, hk⟩
  · refine ⟨?_, ?_, fun j hj => ?_⟩
    · change word t.mem B 48 = _
      rw [ff.word (d := 48) (Or.inl (by decide)) (by decide)]
      exact h.hdr.hw
    · change word t.mem B 56 = _
      rw [ff.word (d := 56) (Or.inl (by decide)) (by decide)]
      exact h.hdr.hminv
    · rw [ff.word (Or.inl (by unfold VG.Impl.Bignum.X86_64.sArr; omega_using [hj]))
        (by unfold VG.Impl.Bignum.X86_64.sArr; omega_using [hj])]
      exact h.hdr.harr j hj
  · rw [f3.word (d := 256) (Or.inl (by decide)) (by decide),
      f2.word (d := 256) (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [f3.word (d := 288) (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [f3.word (d := 272) (Or.inl (by decide)) (by decide),
      f2.word (d := 272) (Or.inl (by decide)) (by decide),
      f1.word (d := 272) (Or.inr (by decide)) (by decide)]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Initialize the reusable p exponentiation workspace from generated bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

theorem generatorModulus_ok {s : State} {B : Addr} {len : Nat} {pb : List Byte}
    (hs : Scr s B activeBytes) (hdi : s.gpr .rdi = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (hbl : pb.length = len)
    (src : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (hodd : Spec.Dsa.decodeBE pb % 2 = 1) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorModulus len) s fun t =>
      ∃ mi, Good t B activeBytes outerWords 0 ∧
        ChildReady t.mem B pWorkspace (len / 8) (Spec.Dsa.decodeBE pb) mi ∧
        word t.mem B 256 = off B VG.Impl.Dsa.Generation.Layout.p ∧
        word t.mem B 288 = off B VG.Impl.Dsa.Generation.Layout.exponent ∧
        word t.mem B 328 = BitVec.ofNat 64 len ∧
        word t.mem B 272 = word s.mem B 272 ∧
        Frm B ([(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8)) s.mem t.mem ∧
        Keep coreRegs s t := by
  have hlen : 1 ≤ len ∧ len < 2 ^ 31 ∧ 2 ≤ len / 8 ∧ len / 8 ≤ outerWords ∧
      len / 8 = (len + 7) / 8 ∧ pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  unfold Impl.Dsa.X86_64.Generation.generatorModulus
  simp only [seqs]
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86_64.parent_ok hs hdi (by decide))
    fun u ⟨gu, fu, ku⟩ => ?_)
  have ffu : Frm B [(48, 80)] s.mem u.mem := Frm.of_outside fu (by simp)
  have sru := src.congrK (InScr.of_frm ffu (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) ku
  refine WP.seq (WP.mono (generatorFields_ok gu (by decide) (by omega_using [hl]))
    fun v ⟨gv, vp, ve, vl, vg, fv, kv⟩ => ?_)
  have ffv : Frm B [(256, 80)] u.mem v.mem := Frm.of_outside fv (by simp)
  have srv := sru.congrK (InScr.of_frm ffv (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) kv
  refine WP.mono (VG.Proof.Dsa.X86_64.child_ok gv (by decide) (by decide) (by decide)
    hlen.2.2.2.2.2 hlen.2.2.1 hlen.2.2.2.1 (by decide)
    ⟨.input .p, .pLen⟩ (by trivial) (by exact vp) (by simpa only [hbl, Field.offset] using vl)
    srv (by omega_using [hl, hbl]) (by omega_using [hl, hbl]) (by rw [hbl]; exact hlen.2.2.2.2.1) hodd)
    fun t ⟨mi, gt, ready, ft, kt⟩ => ?_
  refine ⟨mi, gt, ready, ?_, ?_, ?_, ?_, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  · rw [init_word ft (d := 256) (by decide) (Or.inr (by decide)) (by decide), vp]
  · rw [init_word ft (d := 288) (by decide) (Or.inr (by decide)) (by decide), ve]
  · rw [init_word ft (d := 328) (by decide) (Or.inr (by decide)) (by decide), vl]
  · rw [init_word ft (d := 272) (by decide) (Or.inr (by decide)) (by decide), vg,
      fu.word (d := 272) (Or.inr (by decide)) (by decide)]
  · have ff : Frm B [(48, 80), (256, 80)] s.mem v.mem :=
      (Frm.of_outside fu (by simp)).trans (Frm.of_outside fv (by simp))
    exact (ff.mono (fun r hr => List.mem_append_left _ hr)).trans
      (ft.mono (fun r hr => List.mem_append_right _ hr))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorFromFrame`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.DecrementOdd`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorLoads`, which the modules that import this one used -/

section

/-! # Load a modulus and a candidate into the range-check workspace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.Rsa VG.Impl.Bignum.X86_64

theorem generatorLoadPair_ok {s : State} {B pp hp : Addr} {Z w : Nat} {pb hb : List Byte}
    (h : Ws s B Z w)
    (hptr : word s.mem B 128 = pp) (hlen : word s.mem B 136 = BitVec.ofNat 64 pb.length)
    (xptr : word s.mem B 144 = hp) (xlen : word s.mem B 152 = BitVec.ofNat 64 hb.length)
    (sp : Src s B Z pp pb) (sx : Src s B Z hp hb)
    (hp1 : 1 ≤ pb.length) (hpw : pb.length ≤ 8 * w)
    (hx1 : 1 ≤ hb.length) (hxw : hb.length ≤ 8 * w) :
    WP isa Impl.Dsa.X86_64.Generation.generatorLoadPair s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 0) w = Spec.Rsa.os2ip pb ∧
      wv t.mem B (slot w 1) w = Spec.Rsa.os2ip hb ∧
      Frm B [ar w 0, ar w 1] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorLoadPair
  refine WP.seq (WP.mono (loadCandidateArray_ok h (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) hptr hlen sp hp1 hpw) fun u ⟨hu, up, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; simp [slot, hdrBytes]; omega_using [hd])
      (by have := h.scr.nowrap; have := h.h256; omega_using [hd])
  have sxu := sx.congrK (InScr.of_frm fu (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.sl (by decide))) ku
  refine WP.mono (loadCandidateArray_ok hu (by decide : 1 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) (by rw [uh 144 (by decide)]; exact xptr)
    (by rw [uh 152 (by decide)]; exact xlen) sxu hx1 hxw) fun v ⟨hv, vx, fv, kv⟩ => ?_
  have vp : wv v.mem B (slot w 0) w = Spec.Rsa.os2ip pb := by
    rw [fv.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl; left; simp only [slot, hdrBytes]; omega_using [])
      (by have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega_arith), up]
  exact ⟨hv, vp, vx, (fu.mono (by simp)).trans (fv.mono (by simp)), (ku.trans kv).mono (by decide)⟩


end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The generator's upper endpoint p−1 requires only a low-limb decrement -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem decrementOdd_ok {s : State} {B : Addr} {Z w j : Nat}
    (h : Ws s B Z w) (hj : j < 16) (ho : wv s.mem B (slot w j) w % 2 = 1) :
    WP isa (.block (decA j)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w j) w = wv s.mem B (slot w j) w - 1 ∧
      Outside B (slot w j) 8 s.mem t.mem ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have room := h.sl hj
  have nowrap := h.scr.nowrap
  have hw := h.w1
  refine WP.mono (decA_ok h hj) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B (slot w j) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_using [room, nowrap])
  have ff : Frm B [(slot w j, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  refine ⟨h.congr ff (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _)
    hk (by decide), ?_, hf, hk⟩
  have upper : wv t.mem B (slot w j + 8) (w - 1) = wv s.mem B (slot w j + 8) (w - 1) :=
    hf.wv (Or.inr (by omega_using [])) (by omega_using [room, nowrap])
  have low : word t.mem B (slot w j) = word s.mem B (slot w j) - 1 := by
    rw [hm, word_writeW_self]
  have odd : (word s.mem B (slot w j)).toNat % 2 = 1 := by
    rw [wv_low (by omega_using [hw] : 0 < w)] at ho
    omega_using [ho]
  have sub : (word s.mem B (slot w j) - 1).toNat = (word s.mem B (slot w j)).toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega_using [odd])]
    rfl
  rw [wv_low (by omega_using [hw] : 0 < w), upper, low, sub, wv_low (m := s.mem) (by omega_using [hw] : 0 < w)]
  omega_using [odd]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorArguments`, which this module and modules that import it used -/

section

/-! # Bind either h or computed g to the native range checker -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private theorem generator_arguments_fit {len : Nat} (hl : len < 2 ^ 31) (result : Bool) :
    ∀ a ∈ generatorRangeArguments len result, argumentFits a := by
  intro a ha
  cases result <;> simp only [generatorRangeArguments, Bool.false_eq_true, ite_false, ite_true,
    List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  all_goals first | decide | exact ⟨by decide, by decide, hl⟩

theorem generatorArguments_ok {s : State} {B F : Addr} {Z w len : Nat} {W : Nat → BitVec 64}
    (h : Ws s B Z w) (hl : len < 2 ^ 31) (result : Bool) (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8) :
    WP isa (.block (headerArguments (generatorRangeArguments len result))) s fun t =>
      Ws t B Z w ∧
      word t.mem B 128 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 136 = BitVec.ofNat 64 len ∧
      word t.mem B 144 = (if result then off (W 5) Impl.Dsa.Generation.Layout.g else W 21) ∧
      word t.mem B 152 = BitVec.ofNat 64 len ∧
      Outside B 128 128 s.mem t.mem ∧ Keep [.rax] s t := by
  have hB : Scr s B 256 := by
    simpa only [off, BitVec.add_zero] using h.scr.sub (o := 0) (n := 256) h.h256 (by decide)
  have fits := generator_arguments_fit hl result
  refine WP.mono (headerArguments_ok _ fits hB h.rdi hsp hr hwords hsep) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ fits
  have wh (k : Nat) (hk32 : k < 32) : word t.mem B (8 * k) =
      argumentWords W (fun j => word s.mem B (8 * j)) (generatorRangeArguments len result) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ fits hk32
  have hh (d : Nat) (hd : d + 8 ≤ 128) : word t.mem B d = word s.mem B d :=
    hf.word (Or.inl hd) (by omega_using [hd])
  have stride : word t.mem B 224 = word s.mem B 224 := by
    cases result <;> exact wh 28 (by decide)
  have ht : Ws t B Z w := ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi,
    (hh 48 (by decide)).trans h.hw, stride.trans h.hS, fun j hj => (hh (8 * sArr j) (by unfold sArr; omega_using [hj])).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, hf, hk⟩
  · cases result <;> exact wh 16 (by decide)
  · cases result <;> exact wh 17 (by decide)
  · cases result <;> simpa [argumentWords, generatorRangeArguments, argumentValue] using wh 18 (by decide)
  · cases result <;> exact wh 19 (by decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

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

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorPlan`, which this module and modules that import it used -/

section

/-! # Shared memory plan for native generator filtering and exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GeneratorPlan where
  B : Addr
  A : Addr
  F : Addr
  S : Addr
  hp : Addr
  Z : Nat
  len : Nat
  pb : List Byte
  hb : List Byte
  eb : List Byte
  width : len = 128 ∨ len = 256 ∨ len = 384
  arithmeticBase : B + BitVec.ofNat 64 arithmetic = A
  workspaceRoom : slot (len / 8) 16 ≤ Z
  pLength : pb.length = len
  hLength : hb.length = len
  eLength : eb.length = len
  pPositive : 1 < Spec.Dsa.decodeBE pb
  pOdd : Spec.Dsa.decodeBE pb % 2 = 1
  frameHeaders : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off A (8 * j)) 8
  frameOutside : ∀ k < 37, ∀ i < 8, Z ≤ ofs A (off (off F (8 * k)) i)
  frameSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨off B g, len⟩],
    (⟨F, frameBytes⟩ : Region).Disjoint r
  hashSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨off B g, len⟩],
    (⟨S, oRsa⟩ : Region).Disjoint r
  pSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨off B p, len⟩ : Region).Disjoint r
  hSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨hp, len⟩ : Region).Disjoint r
  eSeparate : ∀ r ∈ [⟨A, Z⟩, ⟨B, Impl.Dsa.Layout.activeBytes⟩, ⟨off B g, len⟩, ⟨F, frameBytes⟩],
    (⟨off B exponent, len⟩ : Region).Disjoint r
  gArithmeticSeparate : (⟨off B g, len⟩ : Region).Disjoint ⟨A, Z⟩
  gParentOutside : ∀ i < len, Impl.Dsa.Layout.activeBytes ≤ ofs B (off (off B g) i)
  gArithmeticOutside : ∀ i < len, Z ≤ ofs A (off (off B g) i)

def GeneratorPlan.changed (p : GeneratorPlan) : List Region :=
  [⟨p.A, p.Z⟩, ⟨p.B, Impl.Dsa.Layout.activeBytes⟩, ⟨off p.B g, p.len⟩, ⟨p.F, frameBytes⟩]

def GeneratorPlan.value (p : GeneratorPlan) : Nat :=
  Spec.Dsa.powMod (Spec.Dsa.decodeBE p.hb) (Spec.Dsa.decodeBE p.eb) (Spec.Dsa.decodeBE p.pb)

structure GeneratorMemory (p : GeneratorPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.F p.S
  rep : ∃ V, Rep s.mem p.F p.S V W
  base : W 5 = p.B
  input : W 21 = p.hp
  arithmetic : Scr s p.A p.Z
  parent : Scr s p.B Impl.Dsa.Layout.activeBytes
  pArithmetic : Src s p.A p.Z (off p.B Impl.Dsa.Generation.Layout.p) p.pb
  hArithmetic : Src s p.A p.Z p.hp p.hb
  eArithmetic : Src s p.A p.Z (off p.B exponent) p.eb
  pParent : Src s p.B Impl.Dsa.Layout.activeBytes (off p.B Impl.Dsa.Generation.Layout.p) p.pb
  hParent : Src s p.B Impl.Dsa.Layout.activeBytes p.hp p.hb
  eParent : Src s p.B Impl.Dsa.Layout.activeBytes (off p.B exponent) p.eb
  gWrite : ∀ i < p.len, InRegions s.wr (off (off p.B g) i) 1

theorem GeneratorMemory.frame {p : GeneratorPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : GeneratorMemory p W s) (L : Lay t p.F p.S) (R : ∃ V, Rep t.mem p.F p.S V W')
    (hb : W' 5 = p.B) (hh : W' 21 = p.hp)
    (hf : Frame p.changed s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    GeneratorMemory p W' t := by
  have hn : p.len < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> omega_using [hh]
  have fp : ∀ r ∈ p.changed, (⟨off p.B Impl.Dsa.Generation.Layout.p, p.pb.length⟩ : Region).Disjoint r := by
    rw [p.pLength]; exact p.pSeparate
  have fh : ∀ r ∈ p.changed, (⟨p.hp, p.hb.length⟩ : Region).Disjoint r := by
    rw [p.hLength]; exact p.hSeparate
  have fe : ∀ r ∈ p.changed, (⟨off p.B exponent, p.eb.length⟩ : Region).Disjoint r := by
    rw [p.eLength]; exact p.eSeparate
  exact ⟨L, R, hb, hh, h.arithmetic.congr hwr, h.parent.congr hwr,
    source_of_frame h.pArithmetic hf fp (p.pLength ▸ hn) hrd hwr,
    source_of_frame h.hArithmetic hf fh (p.hLength ▸ hn) hrd hwr,
    source_of_frame h.eArithmetic hf fe (p.eLength ▸ hn) hrd hwr,
    source_of_frame h.pParent hf fp (p.pLength ▸ hn) hrd hwr,
    source_of_frame h.hParent hf fh (p.hLength ▸ hn) hrd hwr,
    source_of_frame h.eParent hf fe (p.eLength ▸ hn) hrd hwr,
    fun i hi => by rw [hwr]; exact h.gWrite i hi⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorOutput`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorStatus`, which the modules that import this one used -/

section

/-! # Generator decision flags and persistent success/retry status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorTest_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    {valid : Bool} (h : GeneratorMemory p W s) (hr : s.gpr .rax = mask valid) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      t.zf = some (!valid) ∧ GeneratorMemory p W t ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (!valid) ∧ t.mem = s.mem) (by
    xrun [hr]
    cases valid <;> decide) rfl) fun t ⟨⟨hz, hm⟩, kt⟩ => ?_
  obtain ⟨V, R⟩ := h.rep
  have Rt : Rep t.mem p.F p.S V W := hm ▸ R
  have Lt := lay_of_rep h.layout R Rt rfl (kt.gpr (by decide)) kt.2.2
  exact ⟨hz, h.frame Lt ⟨V, Rt⟩ h.base h.input (by rw [hm]; exact Frame.refl _ _)
    kt.2.1 kt.2.2, hm, kt⟩

theorem generatorSetStatus_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) (status : Nat) (hs : status < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) s fun t =>
      GeneratorMemory p (upd W 19 (BitVec.ofNat 64 status)) t ∧
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Rsa.bytesAt s.mem (off p.B g) p.len ∧
      Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (stackStatus_ok h.layout R status hs) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.F, frameBytes⟩] s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.F, frameBytes⟩ (by simp)
    change ¬ ofs p.F a < frameBytes at hn
    unfold frameBytes at hn
    omega_using [hn]
  have frame : Frame p.changed s.mem t.mem := ff.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  refine ⟨h.frame Lt ⟨V, Rt⟩ (by simpa [upd] using h.base) (by simpa [upd] using h.input)
    frame kt.2.1 kt.2.2, ?_, frame, kt⟩
  apply VG.Proof.Dsa.Generation.frame_bytesAt ff
  · intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact (p.frameSeparate _ (by simp)).symm
  · rcases p.width with hh | hh | hh <;> omega_using [hh]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Accept precisely nontrivial generator powers, preserving their bytes -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorOutputRange_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s)
    (hg : Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame p.len true) s fun t =>
      t.gpr .rax = mask (decide (1 < p.value)) ∧ GeneratorMemory p W t ∧
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value ∧
      Frame p.changed s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have hn : p.len < 2 ^ 64 := by rcases p.width with hh | hh | hh <;> omega_using [hh]
  have hlt : p.value < Spec.Dsa.decodeBE p.pb := VG.Proof.Dsa.powMod_lt _ _ (by have := p.pPositive; omega_using [this])
  have hfit : p.value < 256 ^ p.len := Nat.lt_trans hlt (p.pLength ▸ VG.Proof.Dsa.decodeBE_lt p.pb)
  have hdecode := VG.Proof.Dsa.decodeBE_encodeBE hfit
  have src : Src s p.A p.Z (off p.B g) (Spec.Dsa.encodeBE p.len p.value) := by
    have hlen := VG.Proof.Dsa.encodeBE_length p.len p.value
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => p.gArithmeticOutside i (hlen ▸ hi)⟩
    · obtain ⟨r, hr, hc⟩ := h.gWrite i (hlen ▸ hi)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · have eq := congrArg (fun bs : List Byte => bs[i]?) hg
      simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
        show i < p.len from hlen ▸ hi, ↓reduceIte, Option.map_some, List.getElem?_eq_getElem hi,
        Option.some.injEq] using eq
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorFromFrame_ok (xb := Spec.Dsa.encodeBE p.len p.value) true h.layout R h.arithmetic
    (by rw [h.base]; exact p.arithmeticBase) p.width p.workspaceRoom p.frameHeaders p.frameOutside
    (p.frameSeparate _ (by simp)) (p.hashSeparate _ (by simp))
    (by simpa only [h.base] using h.pArithmetic) (by simpa only [↓reduceIte, h.base] using src)
    p.pLength (VG.Proof.Dsa.encodeBE_length p.len p.value) (fun he => Bool.noConfusion he)
    (fun _ => by change Spec.Dsa.decodeBE _ < _; rw [hdecode]; exact hlt))
    fun t ⟨hr, Lt, Rt, _, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  refine ⟨?_, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, ?_, frame, kt⟩
  · change t.gpr .rax = mask (decide (1 < Spec.Dsa.decodeBE _)) at hr
    rwa [hdecode] at hr
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact p.gArithmeticSeparate) (Nat.le_of_lt hn), hg]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Generator range and power stages preserve their common memory invariant -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorFootprint.lean`, which only this module imported.
section

/-! # Global memory footprint of the reused generator exponentiation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.X86_64 VG.Impl.Dsa.Layout
open VG.Impl.Bignum.X86_64

theorem generator_power_frame {B : Addr} {len : Nat} {m m' : Mem}
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hf : CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len m m') :
    Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] m m' := by
  have hsize : pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have sub : Region.Sub ⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ ⟨B, activeBytes⟩ :=
    Offset.sub_base B (by omega)
  intro a ha
  have hn := ha ⟨B, activeBytes⟩ (by simp)
  have hn' : ¬ (⟨off B pWorkspace, slot (len / 8) 8 + tabBytes (len / 8)⟩ : Region).Contains a 1 :=
    fun hc => hn (sub a hc)
  apply hf a
  · right
    change ¬ ofs B a < activeBytes at hn
    unfold activeBytes at hn
    omega
  · intro r hr
    right
    have hb := (workRanges_ok (len / 8) r hr).2
    change ¬ ofs (off B pWorkspace) a < slot (len / 8) 8 + tabBytes (len / 8) at hn'
    omega
  · intro i hi he
    apply ha ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by rcases hl with hh | hh | hh <;> omega)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorPower.lean`, which only this module imported.
section

/-! # Generator construction uses the existing verified public exponentiation -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

theorem generatorPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr}
    {len modulus : Nat} {mi : BitVec 64} {hb eb : List Byte}
    (h : Good s B activeBytes outerWords 0)
    (child : ChildReady s.mem B pWorkspace (len / 8) modulus mi)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hm : 1 < modulus) (hodd : modulus % 2 = 1)
    (has : OperandBytes s B activeBytes ⟨.input .g, .pLen⟩ hb)
    (hes : OperandBytes s B activeBytes ⟨.input .x, .pLen⟩ eb)
    (hhl : hb.length = len) (hel : eb.length = len)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorPower Sq.mm M.mm) s fun t =>
      Good t B activeBytes outerWords 0 ∧ ChildReady t.mem B pWorkspace (len / 8) modulus mi ∧
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) modulus) ∧
      CallFrame B pWorkspace (len / 8) (off B VG.Impl.Dsa.Generation.Layout.g) len s.mem t.mem ∧
      Keep coreRegs s t := by
  have hlen : 1 ≤ len ∧ len ≤ 1024 ∧ 2 ≤ len / 8 ∧ len / 8 ≤ 48 ∧
      len / 8 = (len + 7) / 8 ∧ pWorkspace + slot (len / 8) 8 + tabBytes (len / 8) ≤ activeBytes := by
    rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  exact corePublicPow_ok M Sq h child (by decide) (by decide) hlen.2.2.2.2.2 (by decide)
    hlen.2.2.1 hlen.2.2.2.1 hlen.2.2.2.1 (by decide) hm hodd
    ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩ ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩
    (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 31; decide)
    has hes (by omega) (by rw [hhl, ← hlen.2.2.2.2.1]) (by omega) (by omega)
    (by simpa only [hhl] using has.length) hlen.1 (by omega) hlen.2.2.2.2.1 hout houtside

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorPowerFresh.lean`, which only this module imported.
section

/-! # Initialize and evaluate one generator power from arbitrary scratch -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

theorem generatorPowerFresh_ok (M : Mont) (Sq : MontS) {s : State} {B hp : Addr}
    {len : Nat} {pb hb eb : List Byte}
    (hs : Scr s B activeBytes) (hdi : s.gpr .rdi = B)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hpl : pb.length = len) (hhl : hb.length = len) (hel : eb.length = len)
    (hm : 1 < Spec.Dsa.decodeBE pb) (hodd : Spec.Dsa.decodeBE pb % 2 = 1)
    (hptr : word s.mem B 272 = hp)
    (sp : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (sh : Src s B activeBytes hp hb)
    (se : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.exponent) eb)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i)) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorPowerFresh Sq.mm M.mm len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) (Spec.Dsa.decodeBE pb)) ∧
      Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem t.mem ∧
      Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorPowerFresh
  refine WP.seq (WP.mono (generatorModulus_ok hs hdi hl hpl sp hodd)
    fun u ⟨mi, gu, child, _, ep, plen, gh, fu, ku⟩ => ?_)
  have bounds : ∀ r ∈ [(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8), r.1 + r.2 ≤ activeBytes := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, initRanges] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · decide
    · decide
    · decide
    · rcases hl with hh | hh | hh <;> rw [hh] <;> decide
  have shu := sh.congrK (InScr.of_frm fu bounds) ku
  have seu := se.congrK (InScr.of_frm fu bounds) ku
  have has : OperandBytes u B activeBytes ⟨.input .g, .pLen⟩ hb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hhl]; exact plen
    · change Src u B activeBytes (word u.mem B 272) hb
      rw [gh, hptr]; exact shu
  have hes : OperandBytes u B activeBytes ⟨.input .x, .pLen⟩ eb := by
    refine ⟨?_, ?_⟩
    · change word u.mem B 328 = _
      rw [hel]; exact plen
    · change Src u B activeBytes (word u.mem B 288) eb
      rw [ep]; exact seu
  refine WP.mono (generatorPower_ok M Sq gu child hl hm hodd has hes hhl hel
    (fun i hi => by rw [ku.2.2]; exact hout i hi) houtside)
    fun t ⟨_, _, result, ft, kt⟩ => ?_
  have ff : Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    intro r hr
    right
    have hn := ha ⟨B, activeBytes⟩ (by simp)
    change ¬ ofs B a < activeBytes at hn
    exact Nat.le_trans (bounds r hr) (by omega)
  exact ⟨result, ff.trans (generator_power_frame hl ft), (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorEvaluate.lean`, which only this module imported.
section

/-! # Evaluate h^((p−1)/q) while retaining the persistent generation frame -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Layout

theorem generatorEvaluate_ok (M : Mont) (Sq : MontS) {s : State} {B F S hp : Addr}
    {len : Nat} {pb hb eb : List Byte} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hB : W 5 = B) (hhp : W 21 = hp)
    (hs : Scr s B activeBytes) (hl : len = 128 ∨ len = 256 ∨ len = 384)
    (hpl : pb.length = len) (hhl : hb.length = len) (hel : eb.length = len)
    (hm : 1 < Spec.Dsa.decodeBE pb) (hodd : Spec.Dsa.decodeBE pb % 2 = 1)
    (sp : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.p) pb)
    (sh : Src s B activeBytes hp hb)
    (se : Src s B activeBytes (off B VG.Impl.Dsa.Generation.Layout.exponent) eb)
    (hout : ∀ i < len, InRegions s.wr (off (off B VG.Impl.Dsa.Generation.Layout.g) i) 1)
    (houtside : ∀ i < len, activeBytes ≤ ofs B (off (off B VG.Impl.Dsa.Generation.Layout.g) i))
    (hF : ∀ r ∈ [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩], (⟨F, frameBytes⟩ : Region).Disjoint r)
    (hS : ∀ r ∈ [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩], (⟨S, oRsa⟩ : Region).Disjoint r) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorEvaluate Sq.mm M.mm len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off B VG.Impl.Dsa.Generation.Layout.g) len =
        Spec.Dsa.encodeBE len (Spec.Dsa.powMod (Spec.Dsa.decodeBE hb) (Spec.Dsa.decodeBE eb) (Spec.Dsa.decodeBE pb)) ∧
      Lay t F S ∧ Rep t.mem F S V W ∧
      Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem t.mem ∧
      Keep (.rdi :: coreRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorEvaluate
  refine WP.seq (WP.mono (generatorInput_ok L R hB hhp (hs.st (by decide)))
    fun u ⟨hdi, hptr, fu, ku⟩ => ?_)
  have ff : Frm B [(272, 8)] s.mem u.mem := Frm.of_outside fu (by simp)
  have bounds : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  refine WP.mono (generatorPowerFresh_ok M Sq (hs.congr ku.2.2) hdi hl hpl hhl hel hm hodd hptr
    (sp.congrK (InScr.of_frm ff bounds) ku) (sh.congrK (InScr.of_frm ff bounds) ku)
    (se.congrK (InScr.of_frm ff bounds) ku)
    (fun i hi => by rw [ku.2.2]; exact hout i hi) houtside) fun t ⟨result, ft, kt⟩ => ?_
  have fg : Frame [⟨B, activeBytes⟩, ⟨off B VG.Impl.Dsa.Generation.Layout.g, len⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    right
    have hn := ha ⟨B, activeBytes⟩ (by simp)
    change ¬ ofs B a < activeBytes at hn
    unfold activeBytes at hn
    omega
  have frame := fg.trans ft
  have Rt := rep_of_disjoint_frame R frame hF hS
  have keep := ku.trans kt
  exact ⟨result, lay_of_rep L R Rt rfl (keep.gpr (by decide)) keep.2.2, Rt, frame, keep.mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem generatorInputRange_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame p.len false) s fun t =>
      t.gpr .rax = mask (decide (1 < Spec.Dsa.decodeBE p.hb ∧
        Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1)) ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorFromFrame_ok false h.layout R h.arithmetic
    (by rw [h.base]; exact p.arithmeticBase) p.width p.workspaceRoom p.frameHeaders p.frameOutside
    (p.frameSeparate _ (by simp)) (p.hashSeparate _ (by simp))
    (by simpa only [h.base] using h.pArithmetic) (by simpa only [Bool.false_eq_true, ↓reduceIte, h.input] using h.hArithmetic)
    p.pLength p.hLength (fun _ => p.pOdd) (fun he => Bool.noConfusion he))
    fun t ⟨hr, Lt, Rt, _, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  exact ⟨hr, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, frame, kt⟩

theorem generatorEvaluateStage_ok (M : Mont) (Sq : MontS)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorEvaluate Sq.mm M.mm p.len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.rdi :: coreRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorEvaluate_ok M Sq h.layout R h.base h.input h.parent
    p.width p.pLength p.hLength p.eLength p.pPositive p.pOdd
    h.pParent h.hParent h.eParent h.gWrite p.gParentOutside
    (by intro r hr; exact p.frameSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr))
    (by intro r hr; exact p.hashSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr)))
    fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by
    intro r hr; simp only [GeneratorPlan.changed, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h])
  exact ⟨result, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.2.1 kt.2.2, frame, kt⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Preserve the whole h tape while testing successive complete chunks -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorStep.lean`, which only this module imported.
section

/-! # Complete native generator attempt: input filter, power, output filter -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GeneratorPlan.accepts (p : GeneratorPlan) : Prop :=
  1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1 ∧ 1 < p.value

instance (p : GeneratorPlan) : Decidable p.accepts := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem generatorStep_ok (M : Mont) (Sq : MontS)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.len) s fun t =>
      GeneratorMemory p (upd W 19 (if p.accepts then 1 else 3)) t ∧
      (p.accepts → Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) ∧
      Frame p.changed s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorStep
  refine WP.seq (WP.mono (generatorInputRange_ok h) fun u ⟨hr, hu, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (generatorTest_ok hu hr) fun v ⟨hz, hv, hm, kv⟩ => ?_)
  have fv : Frame p.changed s.mem v.mem := hm ▸ fu
  by_cases input : 1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1
  · refine WP.ite false (by simp [eval, hz, input]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    change WP isa (.seq _ (.seq _ (.seq _ _))) v _
    refine WP.seq (WP.mono (generatorEvaluateStage_ok M Sq hv) fun w ⟨gw, hw, fw, kw⟩ => ?_)
    refine WP.seq (WP.mono (generatorOutputRange_ok hw gw) fun x ⟨rx, hx, gx, fx, kx⟩ => ?_)
    refine WP.seq (WP.mono (generatorTest_ok hx rx) fun y ⟨zy, hy, my, ky⟩ => ?_)
    have fy : Frame p.changed s.mem y.mem := my ▸ ((fv.trans fw).trans fx)
    have gy : Spec.Rsa.bytesAt y.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value := my ▸ gx
    have keep := (((ku.trans kv).trans kw).trans kx).trans ky
    by_cases output : 1 < p.value
    · have accepted : p.accepts := ⟨input.1, input.2, output⟩
      refine WP.ite false (by simp [eval, zy, output]) (fun he => Bool.noConfusion he) (fun _ => ?_)
      refine WP.mono (generatorSetStatus_ok hy 1 (by decide)) fun t ⟨ht, gt, ft, kt⟩ => ?_
      exact ⟨by simpa [accepted] using ht, fun _ => gt.trans gy,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
    · have rejected : ¬ p.accepts := fun ha => output ha.2.2
      refine WP.ite true (by simp [eval, zy, output]) (fun _ => ?_) (fun he => Bool.noConfusion he)
      refine WP.mono (generatorSetStatus_ok hy 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
      exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
  · have rejected : ¬ p.accepts := fun ha => input ⟨ha.1, ha.2.1⟩
    refine WP.ite true (by simp [eval, hz, input]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (generatorSetStatus_ok hv 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
    exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
      fv.trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorSearchPlan.lean`, which only this module imported.
section

/-! # Original h tape and per-chunk plans for the native generator loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure GeneratorSearchPlan where
  core : GeneratorPlan
  saved : Nat → BitVec 64
  tape : List Byte
  tapePtr : Addr
  tapeFits : tape.length < 2 ^ 64
  tapeSeparate : ∀ r ∈ core.changed, (⟨tapePtr, tape.length⟩ : Region).Disjoint r
  q : Nat
  exponentValue : Spec.Dsa.decodeBE core.eb = (Spec.Dsa.decodeBE core.pb - 1) / q

def GeneratorSearchPlan.chunk (p : GeneratorSearchPlan) (used : Nat)
    (room : used + p.core.len ≤ p.tape.length) : GeneratorPlan :=
  { p.core with
    hp := off p.tapePtr used
    hb := (p.tape.drop used).take p.core.len
    hLength := by simp only [List.length_take, List.length_drop]; omega_using [room]
    hSeparate := by
      intro r hr
      exact fun a ha hb => p.tapeSeparate r hr a (Offset.sub_base p.tapePtr room a ha) hb }

def GeneratorSearchPlan.remaining (p : GeneratorSearchPlan) (used : Nat) : Option Nat :=
  Spec.Dsa.generator (Spec.Dsa.decodeBE p.core.pb) p.q
    ((Spec.Dsa.generationChunks p.core.len (p.tape.drop used)).map Spec.Dsa.decodeBE)

theorem GeneratorSearchPlan.remaining_done (p : GeneratorSearchPlan) {used : Nat}
    (h : p.tape.length - used < p.core.len) : p.remaining used = none := by
  unfold remaining
  rw [VG.Proof.Dsa.Generation.generationChunks_done (by simpa only [List.length_drop] using h)]
  rfl

theorem GeneratorSearchPlan.remaining_step (p : GeneratorSearchPlan) {used : Nat}
    (room : used + p.core.len ≤ p.tape.length) :
    p.remaining used = if (p.chunk used room).accepts then some (p.chunk used room).value
      else p.remaining (used + p.core.len) := by
  have hw : 0 < p.core.len := by rcases p.core.width with hh | hh | hh <;> omega_using [hh]
  rw [remaining, VG.Proof.Dsa.Generation.generator_chunks_step hw (by
    simp only [List.length_drop]; omega_using [room])]
  simp only [GeneratorPlan.accepts, GeneratorPlan.value, chunk, p.exponentValue,
    remaining, List.drop_drop]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def generatorSlots : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 28]

structure GeneratorSearchMemory (p : GeneratorSearchPlan) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.core.F p.core.S
  rep : ∃ V, Rep s.mem p.core.F p.core.S V W
  base : W 5 = p.core.B
  tapeBase : W 11 = p.tapePtr
  tapeLength : W 12 = BitVec.ofNat 64 p.tape.length
  slots : ∀ k ∈ generatorSlots, W k = p.saved k
  arithmetic : Scr s p.core.A p.core.Z
  parent : Scr s p.core.B Impl.Dsa.Layout.activeBytes
  pArithmetic : Src s p.core.A p.core.Z (off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeArithmetic : Src s p.core.A p.core.Z p.tapePtr p.tape
  eArithmetic : Src s p.core.A p.core.Z (off p.core.B exponent) p.core.eb
  pParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (off p.core.B Impl.Dsa.Generation.Layout.p) p.core.pb
  tapeParent : Src s p.core.B Impl.Dsa.Layout.activeBytes p.tapePtr p.tape
  eParent : Src s p.core.B Impl.Dsa.Layout.activeBytes (off p.core.B exponent) p.core.eb
  gWrite : ∀ i < p.core.len, InRegions s.wr (off (off p.core.B g) i) 1

theorem GeneratorSearchMemory.frame {p : GeneratorSearchPlan} {W W' : Nat → BitVec 64} {s t : State}
    (h : GeneratorSearchMemory p W s) (L : Lay t p.core.F p.core.S)
    (R : ∃ V, Rep t.mem p.core.F p.core.S V W')
    (hw : ∀ k ∈ generatorSlots, W' k = W k)
    (hf : Frame p.core.changed s.mem t.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    GeneratorSearchMemory p W' t := by
  have hn : p.core.len < 2 ^ 64 := by rcases p.core.width with hh | hh | hh <;> omega_using [hh]
  have fp : ∀ r ∈ p.core.changed, (⟨off p.core.B Impl.Dsa.Generation.Layout.p, p.core.pb.length⟩ : Region).Disjoint r := by
    rw [p.core.pLength]; exact p.core.pSeparate
  have fe : ∀ r ∈ p.core.changed, (⟨off p.core.B exponent, p.core.eb.length⟩ : Region).Disjoint r := by
    rw [p.core.eLength]; exact p.core.eSeparate
  exact ⟨L, R, (hw 5 (by simp [generatorSlots])).trans h.base, (hw 11 (by simp [generatorSlots])).trans h.tapeBase,
    (hw 12 (by simp [generatorSlots])).trans h.tapeLength,
    fun k hk => (hw k hk).trans (h.slots k hk), h.arithmetic.congr hwr, h.parent.congr hwr,
    source_of_frame h.pArithmetic hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeArithmetic hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eArithmetic hf fe (p.core.eLength ▸ hn) hrd hwr,
    source_of_frame h.pParent hf fp (p.core.pLength ▸ hn) hrd hwr,
    source_of_frame h.tapeParent hf p.tapeSeparate p.tapeFits hrd hwr,
    source_of_frame h.eParent hf fe (p.core.eLength ▸ hn) hrd hwr,
    fun i hi => by rw [hwr]; exact h.gWrite i hi⟩

theorem GeneratorSearchMemory.chunk {p : GeneratorSearchPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorSearchMemory p W s) {used : Nat} (room : used + p.core.len ≤ p.tape.length)
    (ptr : W 21 = off p.tapePtr used) : GeneratorMemory (p.chunk used room) W s :=
  ⟨h.layout, h.rep, h.base, ptr, h.arithmetic, h.parent,
    h.pArithmetic, source_slice h.tapeArithmetic room, h.eArithmetic,
    h.pParent, source_slice h.tapeParent room, h.eParent, h.gWrite⟩

end VG.Proof.Dsa.X86_64.Generation
