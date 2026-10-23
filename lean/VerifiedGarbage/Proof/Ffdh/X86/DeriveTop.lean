module

import VerifiedGarbage.Proof.Ffdh.X86.Derive
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.KeyGenTop
public import VerifiedGarbage.Proof.Ffdh.X86.Ops
public import VerifiedGarbage.Impl.Ffdh.X86.Derive
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen

/-! # `vg_ffdh_derive_public` on i686 against its contract: the public value -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Derive

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckPrivate (XGeo xv)
open VG.Proof.Ffdh.X86.KeyGen (OutAt)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

/-- What the contract gives `vg_ffdh_derive_public(y, y_len, domain, domain_len, p_len, x, x_len, scratch,
scratch_len)`. -/
structure DerivePublicABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩,
    ⟨argAddr s 0, 36⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  domScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  xScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outX : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  scratchArgs : (⟨argumentPointer s 7, (arg s 8).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  belowOut : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  domBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  xBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratchBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 4).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 4).toNat (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 4).toNat
  xPos : 1 ≤ (arg s 6).toNat
  xLen : (arg s 6).toNat ≤ (arg s 4).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 4).toNat ≤ (arg s 8).toNat

theorem derivePublicABI_of {s : State} (h : (Spec.Ffdh.derivePublicContract abi stack).pre s) :
    DerivePublicABI s := by
  sig_pre [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem wrapABI {s : State} (A : DerivePublicABI s) : WrapABI Impl.Ffdh.X86.DerivePublic.args 9 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h),
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

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.DerivePublic.args)) Impl.Ffdh.X86.DerivePublic.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The domain's and x's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat
abbrev entryX (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat

/-- The output. -/
abbrev outR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩

/-- What the body may read: the domain and x; and write: y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 5) (arg s 6).toNat ∧ InRegions wr (argumentPointer s 0) (arg s 1).toNat

/-- The inputs and the output, as the synthetic arguments give them. -/
structure Geo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen xl : Nat) (sp : BitVec 32)
    (rd wr : List Region) : Prop where
  dom : DomGeo args base bytes len dlen rd wr
  dom40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  x : XGeo args base bytes len xl rd wr
  x40 : Region.Disjoint ⟨byteAddr (args 10), xl⟩ (below sp 96)
  out : OutAt args base bytes len 0 sp wr
  e1 : args 1 = BitVec.ofNat 32 len

theorem frame_geo {s : State} (A : DerivePublicABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    Geo (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (wsBase Impl.Ffdh.X86.DerivePublic.args s)
      (wsSize Impl.Ffdh.X86.DerivePublic.args s) (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (arg s 3).toNat
      (arg s 6).toNat sp rd wr := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  have sub40 : Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  have subF : Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.DerivePublic.args s := A.outLen
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, (A.belowDom.sub_left sub40).symm,
    ⟨(ofn _).symm, A.xPos, A.xLen, A.xBound, hrd.2.1, A.xScratch⟩, (A.belowX.sub_left sub40).symm,
    ⟨?_, ?_, ?_, ?_, ?_⟩, (ofn _).symm⟩
  · show (arg s 0).toNat + _ ≤ _
    rw [← oR]; exact A.outBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← oR]; exact hrd.2.2
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.outScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← oR]; exact A.belowOut.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← oR]; exact (A.belowOut.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : DerivePublicABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩)
    (hb : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hws
    · exact (hb.sub_left (by rw [FA]; exact Offset.sub_below _ (by decide) (by decide))).symm) hn

/-- What the contract asks of the status and the output. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Ffdh.domainValid (arg s 4).toNat (entryDom s) = true →
    let a := Spec.Ffdh.domainOf (arg s 4).toNat (entryDom s)
    let x := Spec.Rsa.os2ip (entryX s)
    r.toNat = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 4).toNat =
          Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg s 4).toNat
      else Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 4).toNat = List.replicate (arg s 4).toNat 0

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : DerivePublicABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.DerivePublic.args s) (wsSize Impl.Ffdh.X86.DerivePublic.args s)
      (pLenOf Impl.Ffdh.X86.DerivePublic.args s) (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.DerivePublic.args s, wsSize Impl.Ffdh.X86.DerivePublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.DerivePublic.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([outR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.DerivePublic.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.DerivePublic.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  have Gm := frame_geo A espf I.extra
  have oR : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.DerivePublic.args s := A.outLen
  have D : CheckDomain.domBytes f.mem (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (arg s 3).toNat =
      entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega)
  have Xv : xv f.mem (synth Impl.Ffdh.X86.DerivePublic.args (arg s)) (arg s 6).toNat = Spec.Rsa.os2ip (entryX s) :=
    congrArg _ (frame_keep A Ft A.xScratch A.belowX (by have := A.xBound; omega))
  refine WP.mono (body_ok I Gm.dom Gm.x Gm.dom40 Gm.x40 Gm.out Gm.e1) fun t ⟨r, E, F, K, P⟩ => ⟨fun v => ?_, ?_, K⟩
  · have P' := P (by rw [D]; exact v)
    simp only [CheckPrivate.params] at P'
    rw [D, Xv] at P'
    obtain ⟨hr, hb⟩ := P'
    refine ⟨?_, hb⟩
    rw [E, BitVec.toNat_ofNat, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (KeyGen.keyStatus_le _ _) (by decide))
  · rw [List.singleton_append, outR, oR]; exact F

theorem operation_ok {s : State} (A : DerivePublicABI s) :
    WP isa Impl.Ffdh.X86.DerivePublic.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [outR s])
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.retOut)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact A.outScratch.symm)
    (P := fun m e => spec s m e) fun f I espf Ft => frame_ok A f I espf Ft

theorem correct (s : State) (h : (Spec.Ffdh.derivePublicContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.DerivePublic.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.derivePublicContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (derivePublicABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro v
  exact V v

end VG.Proof.Ffdh.X86.Derive
