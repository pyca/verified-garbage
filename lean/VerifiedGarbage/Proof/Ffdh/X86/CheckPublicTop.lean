module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # `vg_ffdh_check_public` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckPublic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Ffdh.X86.CheckDomain (domBytes)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : CheckPublicABI s) : WrapABI Impl.Ffdh.X86.CheckPublic.args 7 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h), by decide⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  wsIn := by rw [A.wr]; exact List.mem_cons_self ..
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

/-- The domain's and y's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat
abbrev entryY (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 3) (arg s 4).toNat

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckPublic.args)) Impl.Ffdh.X86.CheckPublic.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain and y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 0) (arg s 1).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 3) (arg s 4).toNat

/-- The domain and y, as the synthetic arguments give them, for permissions that read them, apart from
the 40 bytes below the frame. -/
theorem frame_geo {s : State} (A : CheckPublicABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPublic.args s)
      (wsSize Impl.Ffdh.X86.CheckPublic.args s) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) (arg s 1).toNat rd wr ∧
    YGeo (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (wsBase Impl.Ffdh.X86.CheckPublic.args s)
      (wsSize Impl.Ffdh.X86.CheckPublic.args s) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) rd wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPublic.args (arg s) 2), (arg s 1).toNat⟩ (below sp 40) ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckPublic.args (arg s) 8),
      pLenOf Impl.Ffdh.X86.CheckPublic.args s⟩ (below sp 40) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 116 := rfl
  have yl := A.yLen
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
  have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPublic.args s := yl
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, ⟨(ofn _).symm, ?_, ?_, ?_⟩, (A.belowDom.sub_left sub40).symm, ?_⟩
  · show (arg s 3).toNat + _ ≤ _
    rw [← yR]; exact A.yBound
  · show InRegions _ (argumentPointer s 3) _
    rw [← yR]; exact hrd.2
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact A.yScratch
  · show Region.Disjoint ⟨argumentPointer s 3, _⟩ _
    rw [← yR]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : CheckPublicABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩)
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

/-- The status the contract asks for, for a valid domain. -/
abbrev spec (s : State) : Nat :=
  if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (arg s 2).toNat (entryDom s), Spec.Rsa.os2ip (entryY s)⟩
  then 1 else 0

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CheckPublicABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.CheckPublic.args s) (wsSize Impl.Ffdh.X86.CheckPublic.args s)
      (pLenOf Impl.Ffdh.X86.CheckPublic.args s) (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckPublic.args s, wsSize Impl.Ffdh.X86.CheckPublic.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.CheckPublic.body f fun t =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (t.gpr .eax).toNat = spec s) ∧
      Frame ([] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.CheckPublic.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.CheckPublic.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, Y, hb40, hy40⟩ := frame_geo A espf I.extra
  have D : domBytes f.mem (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (arg s 1).toNat = entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega)
  have Yv : yv f.mem (synth Impl.Ffdh.X86.CheckPublic.args (arg s)) (pLenOf Impl.Ffdh.X86.CheckPublic.args s) =
      Spec.Rsa.os2ip (entryY s) := by
    have yR : (arg s 4).toNat = pLenOf Impl.Ffdh.X86.CheckPublic.args s := A.yLen
    show Spec.Rsa.os2ip (Spec.Rsa.bytesAt f.mem (argumentPointer s 3) _) = _
    rw [← yR]
    exact congrArg _ (frame_keep A Ft A.yScratch A.belowY (by have := A.yBound; omega))
  refine WP.mono (body_ok I G Y hb40 hy40)
    fun t ⟨r, ⟨E, F, K⟩, V⟩ => ⟨fun v => ?_, by rw [List.nil_append]; exact F, K⟩
  rw [show pLenOf Impl.Ffdh.X86.CheckPublic.args s = (arg s 2).toNat from rfl] at V Yv
  rw [D] at V
  rw [E, V v, expected, D, Yv]
  split <;> rfl

theorem operation_ok {s : State} (A : CheckPublicABI s) :
    WP isa Impl.Ffdh.X86.CheckPublic.code s fun u =>
      (Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → (u.gpr .eax).toNat = spec s) ∧
        abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _
    rw [A.rd]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := []) (fun _ h => by cases h)
    (fun _ h => by cases h)
    (P := fun _ e => Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) = true → e.toNat = spec s)
    fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.CheckPublic
