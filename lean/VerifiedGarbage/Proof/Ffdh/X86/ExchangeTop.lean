module

public import VerifiedGarbage.Proof.Ffdh.X86.Exchange
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-! # `vg_ffdh_exchange` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Exchange

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Ffdh.X86.CheckPublic (YGeo yv)
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : ExchangeABI s) : WrapABI Impl.Ffdh.X86.Exchange.args 11 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h; decide), by decide⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

/-- The domain's, x's and y's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat
abbrev entryX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat
abbrev entryY (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat

/-- The output. -/
abbrev outR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.Exchange.args)) Impl.Ffdh.X86.Exchange.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain, x and y; and write: the output. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 7) (arg s 8).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat ∧ InRegions wr (argumentPointer s 0) (arg s 1).toNat

/-- The inputs and the output, as the synthetic arguments give them, apart from the 40 bytes below
the frame. -/
theorem frame_geo {s : State} (A : ExchangeABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) (arg s 3).toNat rd wr ∧
    YGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) rd wr ∧
    XGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) (arg s 6).toNat rd wr ∧
    OutGeo (synth Impl.Ffdh.X86.Exchange.args (arg s)) (wsBase Impl.Ffdh.X86.Exchange.args s)
      (wsSize Impl.Ffdh.X86.Exchange.args s) (pLenOf Impl.Ffdh.X86.Exchange.args s) wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.Exchange.args (arg s) 8),
      pLenOf Impl.Ffdh.X86.Exchange.args s⟩ (below sp 40) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.Exchange.args (arg s) 10), (arg s 6).toNat⟩
      (below sp 40) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have yR : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.yLen
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.outLen
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have sub40 : Region.Sub (below sp 40) ⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 40#64 = BitVec.ofNat 64 116 from rfl]
    exact Region.sub_prefix (by decide)
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, ⟨(ofn _).symm, ?_, ?_, ?_⟩,
    ⟨(ofn _).symm, A.xPos, A.xLen, A.xBound, hrd.2.2.1, A.xScratch⟩, ⟨?_, ?_, ?_⟩, ?_,
    (A.belowX.sub_left sub40).symm⟩
  · show (arg s 7).toNat + _ ≤ _
    rw [← yR]; exact A.yBound
  · show InRegions _ (argumentPointer s 7) _
    rw [← yR]; exact hrd.2.1
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← yR]; exact A.yScratch
  · show (arg s 0).toNat + _ ≤ _
    rw [← oR]; exact A.outBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← oR]; exact hrd.2.2.2
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.outScratch.symm
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← yR]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : ExchangeABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- What the contract asks of the result. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Ffdh.domainValid (arg s 4).toNat (entryDom s) = true →
    Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s), Spec.Rsa.os2ip (entryY s)⟩ = true →
      Spec.Rsa.written m (argumentPointer s 0) (arg s 1).toNat r
        (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)) (Spec.Rsa.os2ip (entryX s))
          (Spec.Rsa.os2ip (entryY s)))

/-- The result for valid inputs: `exchangeOp`. -/
theorem result_eq {len : Nat} {D : List Byte} {x y : Nat} {c : Bool} {m : Mem} {out : Addr} {r : BitVec 32}
    (hl : 0 < len) (hD : D.length = 2 * len ∨ D.length = 3 * len)
    (hc : c = (decide (y ^ x % safeM (Spec.Ffdh.domainOf len D).p < pm1 len (Spec.Ffdh.domainOf len D).p) &&
      decide (1 < y ^ x % safeM (Spec.Ffdh.domainOf len D).p)))
    (hr : r = BitVec.ofNat 32 c.toNat)
    (hb : Spec.Rsa.bytesAt m out len =
      Spec.Rsa.i2osp (if c then y ^ x % safeM (Spec.Ffdh.domainOf len D).p else 0) len)
    (v : Spec.Ffdh.domainValid len D = true) (pv : Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf len D, y⟩ = true) :
    Spec.Rsa.written m out len r (Spec.Ffdh.exchangeOp (Spec.Ffdh.domainOf len D) x y) := by
  have mv := VG.Proof.Ffdh.domainValid_mod v
  unfold Spec.Rsa.modulusValid at mv
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at mv
  have gt : 1 < (Spec.Ffdh.domainOf len D).p := by have := Nat.two_pow_pos 511; have := mv.1.1.2; omega
  have lo : 256 ^ (len - 1) ≤ (Spec.Ffdh.domainOf len D).p := by
    have := v; unfold Spec.Ffdh.domainValid at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  have hi : (Spec.Ffdh.domainOf len D).p < 256 ^ len := by
    have := VG.Proof.Bignum.os2ip_lt (D.take len)
    rw [List.length_take, Nat.min_eq_left (by omega)] at this
    exact this
  rw [VG.Proof.Ffdh.exchangeOp_eq pv (by omega) (VG.Proof.Ffdh.octets_bitLength hl lo hi)]
  rw [safeM_of gt mv.1.1.1, pm1_of (by omega)] at hc
  rw [safeM_of gt mv.1.1.1] at hb
  generalize y ^ x % (Spec.Ffdh.domainOf len D).p = z at hc hb ⊢
  by_cases e : 1 < z ∧ z < (Spec.Ffdh.domainOf len D).p - 1
  · have : c = true := by rw [hc]; simp [e.1, e.2]
    subst this
    simp only [e, and_self, ↓reduceIte] at hb ⊢
    exact ⟨hr, hb⟩
  · have : c = false := by
      rw [hc]
      by_cases a : z < (Spec.Ffdh.domainOf len D).p - 1
      · have b : ¬ 1 < z := fun b => e ⟨b, a⟩
        simp only [a, b, decide_true, decide_false, Bool.and_false]
      · simp only [a, decide_false, Bool.false_and]
    subst this
    simp only [e, ↓reduceIte, Bool.false_eq_true] at hb ⊢
    exact ⟨hr, by rw [hb, VG.Proof.Bignum.i2osp_zero']⟩

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : ExchangeABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.Exchange.args s) (wsSize Impl.Ffdh.X86.Exchange.args s)
      (pLenOf Impl.Ffdh.X86.Exchange.args s) (synth Impl.Ffdh.X86.Exchange.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.Exchange.args s, wsSize Impl.Ffdh.X86.Exchange.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.Exchange.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([outR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.Exchange.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.Exchange.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, Y, X, O, hy40, hx40⟩ := frame_geo A espf I.extra
  have yR : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.yLen
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.Exchange.args s := A.outLen
  have D : domBytes f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (arg s 3).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega)
  have Yv : yv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s) =
      Spec.Rsa.os2ip (entryY s) := by
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _) = _
    rw [← yR]
    exact congrArg _ (frame_keep A Ft A.yScratch A.belowY (by have := A.yBound; omega))
  have Xv : xv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (arg s 6).toNat = Spec.Rsa.os2ip (entryX s) :=
    congrArg _ (frame_keep A Ft A.xScratch A.belowX (by have := A.xBound; omega))
  have Pv : comp f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s) 0 =
      (Spec.Ffdh.domainOf (pLenOf Impl.Ffdh.X86.Exchange.args s) (entryDom s)).p := by
    rw [comp_p f.mem _ (dlen := (arg s 3).toNat) (by have := G.dl; omega)]
    exact congrArg (fun d => (Spec.Ffdh.domainOf _ d).p) D
  refine WP.mono (body_ok I G Y X O hy40 hx40) fun t ⟨E, B, F, K⟩ =>
    ⟨fun v pv => ?_, by rw [List.singleton_append, outR, oR]; exact F, K⟩
  have Z : zv f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s)
      (arg s 6).toNat = Spec.Rsa.os2ip (entryY s) ^ Spec.Rsa.os2ip (entryX s) %
        safeM (Spec.Ffdh.domainOf (pLenOf Impl.Ffdh.X86.Exchange.args s) (entryDom s)).p := by
    rw [zv, Yv, Xv, Pv]
  show Spec.Rsa.written _ _ (arg s 1).toNat _ _
  rw [oR]
  refine result_eq (len := (arg s 4).toNat) (D := entryDom s) (x := Spec.Rsa.os2ip (entryX s))
    (y := Spec.Rsa.os2ip (entryY s))
    (c := acc f.mem (synth Impl.Ffdh.X86.Exchange.args (arg s)) (pLenOf Impl.Ffdh.X86.Exchange.args s)
      (arg s 6).toNat) (by have := A.pLen.1; omega)
    (by have := A.dLen; simpa [Spec.Rsa.bytesAt, Spec.Ffdh.domainLenValid] using this) ?_ E ?_ v pv
  · rw [acc, Z, Pv]
    rfl
  · refine B.trans ?_
    rw [Z]
    rfl

theorem operation_ok {s : State} (A : ExchangeABI s) :
    WP isa Impl.Ffdh.X86.Exchange.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [outR s])
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retOut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.outScratch.symm)
    (P := fun m e => spec s m e) fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.Exchange
