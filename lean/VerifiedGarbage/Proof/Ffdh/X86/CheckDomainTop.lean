module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.X86.Stages

/-! # `vg_ffdh_check_domain` on i686 against its contract: the result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.CheckDomain

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In)
open VG.Proof.Ffdh.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

theorem wrapABI {s : State} (A : CheckDomainABI s) : WrapABI Impl.Ffdh.X86.CheckDomain.args 5 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h),
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

/-- The domain's bytes at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.CheckDomain.args)) Impl.Ffdh.X86.CheckDomain.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- What the body may read: the domain. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 0) (arg s 1).toNat

/-- The domain and its components, as the synthetic arguments give them, for permissions that read it,
apart from the 96 bytes below the frame. -/
theorem frame_geo {s : State} (A : CheckDomainABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    DomGeo (synth Impl.Ffdh.X86.CheckDomain.args (arg s)) (wsBase Impl.Ffdh.X86.CheckDomain.args s)
      (wsSize Impl.Ffdh.X86.CheckDomain.args s) (pLenOf Impl.Ffdh.X86.CheckDomain.args s) (arg s 1).toNat rd wr ∧
    Region.Disjoint ⟨byteAddr (synth Impl.Ffdh.X86.CheckDomain.args (arg s) 2), (arg s 1).toNat⟩ (below sp 96) := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd, A.domScratch,
    A.pLen.1, A.pLen.2⟩, ?_⟩
  refine (A.belowDom.sub_left ?_).symm
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
    show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
    ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
  exact Region.sub_prefix (by decide)

/-- The domain's bytes, kept by the entry and the frame's filling. -/
theorem frame_dom {s : State} (A : CheckDomainABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckDomain.args s, wsSize Impl.Ffdh.X86.CheckDomain.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) :
    domBytes m (synth Impl.Ffdh.X86.CheckDomain.args (arg s)) (arg s 1).toNat = entryDom s := by
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have frameDom : Region.Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩ ⟨frameAt s, argsFrame⟩ := by
    refine (A.belowDom.sub_left ?_).symm
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  exact frame_bytes Ft (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.domScratch
    · exact frameDom) (by have := A.domBound; omega)

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : CheckDomainABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.CheckDomain.args s) (wsSize Impl.Ffdh.X86.CheckDomain.args s)
      (pLenOf Impl.Ffdh.X86.CheckDomain.args s) (synth Impl.Ffdh.X86.CheckDomain.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.CheckDomain.args s, wsSize Impl.Ffdh.X86.CheckDomain.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.CheckDomain.body f fun t =>
      (t.gpr .eax).toNat = (if Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) then 1 else 0) ∧
      Frame ([] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.CheckDomain.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.CheckDomain.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, hb40⟩ := frame_geo A espf I.extra
  refine WP.mono (body_ok I G hb40) fun t ⟨E, F, K⟩ => ⟨?_, by rw [List.nil_append]; exact F, K⟩
  rw [E, frame_dom A Ft, show pLenOf Impl.Ffdh.X86.CheckDomain.args s = (arg s 2).toNat from rfl]
  cases Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) <;> rfl

theorem operation_ok {s : State} (A : CheckDomainABI s) :
    WP isa Impl.Ffdh.X86.CheckDomain.code s fun u =>
      (u.gpr .eax).toNat = (if Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) then 1 else 0) ∧
        abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _
    rw [A.rd]; exact ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := []) (fun _ h => by cases h)
    (fun _ h => by cases h) (P := fun _ e => e.toNat = if Spec.Ffdh.domainValid (arg s 2).toNat (entryDom s) then 1 else 0)
    fun f I espf Ft => frame_ok A f I espf Ft

end VG.Proof.Ffdh.X86.CheckDomain
