module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Ffdh.X86.Ops

/-! # `vg_ffdh_generate_key` on i686 against its contract: the key pair -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of)
open VG.Proof.Ffdh.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

/-- What the contract gives `vg_ffdh_generate_key(x, x_len, y, y_len, domain, domain_len, p_len, rand,
rand_len, scratch, scratch_len)`. -/
structure GenerateKeyABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 44 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 44⟩]
  xy : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  xDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  xRand : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  xScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  xArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  yDom : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  yRand : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  yScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  yArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  domScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  domArgs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  randScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  randArgs : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  retX : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retY : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  retRand : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  belowRand : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  xBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  domBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  randBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 6).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 6).toNat (arg s 5).toNat
  xLen : (arg s 1).toNat = (arg s 6).toNat
  yLen : (arg s 3).toNat = (arg s 6).toNat
  randLen : (arg s 8).toNat = (arg s 6).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 6).toNat ≤ (arg s 10).toNat

theorem generateKeyABI_of {s : State} (h : (Spec.Ffdh.generateKeyContract abi stack).pre s) : GenerateKeyABI s := by
  sig_pre [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem wrapABI {s : State} (A : GenerateKeyABI s) : WrapABI Impl.Ffdh.X86.GenerateKey.args 11 s where
  below := ⟨(fun _ h => by cases h; decide), by decide, by decide, by decide, (fun _ h => by cases h; decide),
    (fun _ h => by cases h; decide), by decide⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem frameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill Impl.Ffdh.X86.GenerateKey.args)) Impl.Ffdh.X86.GenerateKey.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The bytes of the domain and of `rand` at entry. -/
abbrev entryDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat
abbrev entryRand (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat

/-- The outputs. -/
abbrev xR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev yR (s : State) : Region := ⟨argumentPointer s 2, (arg s 3).toNat⟩

/-- What the body may read: the domain and `rand`; and write: x and y. -/
abbrev Rd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 4) (arg s 5).toNat ∧
    InRegions (rd ++ wr) (argumentPointer s 7) (arg s 8).toNat ∧
    InRegions wr (argumentPointer s 0) (arg s 1).toNat ∧ InRegions wr (argumentPointer s 2) (arg s 3).toNat

/-- The 40 bytes below the frame, and the frame, below the caller's stack pointer. -/
theorem frame_subs {s : State} (A : GenerateKeyABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ∧
      Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

/-- The inputs and the outputs, as the synthetic arguments give them. -/
structure Geo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen : Nat) (sp : BitVec 32) (rd wr : List Region) :
    Prop where
  dom : DomGeo args base bytes len dlen rd wr
  dom40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  cut : KeyCut.CutGeo base bytes len (args 10) (args 0) sp rd wr
  rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩
  r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below sp 96)
  domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩
  ox : OutAt args base bytes len 0 sp wr
  oy : OutAt args base bytes len 8 sp wr
  e9 : args 9 = BitVec.ofNat 32 len
  xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩

theorem frame_geo {s : State} (A : GenerateKeyABI s) {sp : BitVec 32}
    (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) {rd wr : List Region} (hrd : Rd s rd wr) :
    Geo (synth Impl.Ffdh.X86.GenerateKey.args (arg s)) (wsBase Impl.Ffdh.X86.GenerateKey.args s)
      (wsSize Impl.Ffdh.X86.GenerateKey.args s) (pLenOf Impl.Ffdh.X86.GenerateKey.args s) (arg s 5).toNat sp rd wr := by
  obtain ⟨sub40, subF⟩ := frame_subs A espf
  have xL : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.xLen
  have yL : (arg s 3).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.yLen
  have rL : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.randLen
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have dx : Region.Disjoint ⟨argumentPointer s 0, pLenOf Impl.Ffdh.X86.GenerateKey.args s⟩
      ⟨argumentPointer s 2, pLenOf Impl.Ffdh.X86.GenerateKey.args s⟩ := by
    have := A.xy; rw [xL, yL] at this; exact this
  refine ⟨⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, hrd.1,
    A.domScratch, A.pLen.1, A.pLen.2⟩, (A.belowDom.sub_left sub40).symm, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, (ofn _).symm, dx⟩
  · show (arg s 7).toNat + _ ≤ _
    rw [← rL]; exact A.randBound
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 7) _
    rw [← rL]; exact hrd.2.1
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ ⟨argumentPointer s 0, _⟩
    have := A.xRand.symm; rw [rL, xL] at this; exact this
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact A.xScratch
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact A.randScratch
  · show Region.Disjoint ⟨argumentPointer s 7, _⟩ _
    rw [← rL]; exact (A.belowRand.sub_left sub40).symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xDom.symm
  · show (arg s 0).toNat + _ ≤ _
    rw [← xL]; exact A.xBound
  · show InRegions _ (argumentPointer s 0) _
    rw [← xL]; exact hrd.2.2.1
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.xScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 0, _⟩
    rw [← xL]; exact A.belowX.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 0, _⟩ _
    rw [← xL]; exact (A.belowX.sub_left sub40).symm
  · show (arg s 2).toNat + _ ≤ _
    rw [← yL]; exact A.yBound
  · show InRegions _ (argumentPointer s 2) _
    rw [← yL]; exact hrd.2.2.2
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.yScratch.symm
  · show Region.Disjoint _ ⟨argumentPointer s 2, _⟩
    rw [← yL]; exact A.belowY.sub_left subF
  · show Region.Disjoint ⟨argumentPointer s 2, _⟩ _
    rw [← yL]; exact (A.belowY.sub_left sub40).symm

/-- The bytes apart from the frame and the working space, kept by the entry and the frame's filling. -/
theorem frame_keep {s : State} (A : GenerateKeyABI s) {m : Mem}
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.GenerateKey.args s, wsSize Impl.Ffdh.X86.GenerateKey.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem m) {p : Addr} {n : Nat}
    (hws : Region.Disjoint ⟨p, n⟩ ⟨wsBase Impl.Ffdh.X86.GenerateKey.args s, wsSize Impl.Ffdh.X86.GenerateKey.args s⟩)
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

/-- What the contract asks of the status and the outputs. -/
abbrev spec (s : State) (m : Mem) (r : BitVec 32) : Prop :=
  Spec.Ffdh.domainValid (arg s 6).toNat (entryDom s) = true →
    let a := Spec.Ffdh.domainOf (arg s 6).toNat (entryDom s)
    let x := Spec.Ffdh.scalarOfOctets a (entryRand s)
    r.toNat = Spec.Ffdh.keyStatus a x ∧
      if Spec.Ffdh.keyStatus a x = 1 then
        Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = Spec.Rsa.i2osp x (arg s 6).toNat ∧
          Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat =
            Spec.Rsa.i2osp (Spec.Rsa.powMod a.g x a.p) (arg s 6).toNat
      else Spec.Rsa.bytesAt m (argumentPointer s 0) (arg s 6).toNat = List.replicate (arg s 6).toNat 0 ∧
        Spec.Rsa.bytesAt m (argumentPointer s 2) (arg s 6).toNat = List.replicate (arg s 6).toNat 0

theorem keyStatus_le (a : Spec.Ffdh.Parameters) (x : Nat) : Spec.Ffdh.keyStatus a x ≤ 3 := by
  unfold Spec.Ffdh.keyStatus; split
  · decide
  · split <;> decide

/-- The body, from the frame's state. -/
theorem frame_ok {s : State} (A : GenerateKeyABI s) (f : State)
    (I : In (Rd s) (wsBase Impl.Ffdh.X86.GenerateKey.args s) (wsSize Impl.Ffdh.X86.GenerateKey.args s)
      (pLenOf Impl.Ffdh.X86.GenerateKey.args s) (synth Impl.Ffdh.X86.GenerateKey.args (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase Impl.Ffdh.X86.GenerateKey.args s, wsSize Impl.Ffdh.X86.GenerateKey.args s⟩,
      ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    WP isa Impl.Ffdh.X86.GenerateKey.body f fun t => spec s t.mem (t.gpr .eax) ∧
      Frame ([xR s, yR s] ++ CrtRt.frameR (wsBase Impl.Ffdh.X86.GenerateKey.args s) (f.gpr .esp)
        (fR (pLenOf Impl.Ffdh.X86.GenerateKey.args s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  have Gm := frame_geo A espf I.extra
  have xL : (arg s 1).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.xLen
  have yL : (arg s 3).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.yLen
  have rL : (arg s 8).toNat = pLenOf Impl.Ffdh.X86.GenerateKey.args s := A.randLen
  have D : Spec.Rsa.bytesAt f.mem (byteAddr (synth Impl.Ffdh.X86.GenerateKey.args (arg s) 2)) (arg s 5).toNat =
      entryDom s :=
    frame_keep A Ft A.domScratch A.belowDom (by have := A.domBound; omega)
  have R : Spec.Rsa.bytesAt f.mem (byteAddr (synth Impl.Ffdh.X86.GenerateKey.args (arg s) 10))
      (pLenOf Impl.Ffdh.X86.GenerateKey.args s) = entryRand s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 7) _ = _
    rw [← rL]
    exact frame_keep A Ft A.randScratch A.belowRand (by have := A.randBound; omega)
  refine WP.mono (body_ok I Gm.dom Gm.dom40 Gm.cut Gm.rWs Gm.r40 Gm.domX Gm.ox Gm.oy Gm.e9 Gm.xy)
    fun t ⟨r, E, F, K, P⟩ => ⟨fun v => ?_, ?_, K⟩
  · have P' := P (by show Spec.Ffdh.domainValid _ (Spec.Rsa.bytesAt _ _ _) = true; rw [D]; exact v)
    simp only [CheckPrivate.params, CheckDomain.domBytes] at P'
    rw [D, R] at P'
    obtain ⟨hr, hb⟩ := P'
    refine ⟨?_, hb⟩
    rw [E, BitVec.toNat_ofNat, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (keyStatus_le _ _) (by decide))
  · rw [List.cons_append, List.singleton_append, xR, yR, xL, yL]; exact F

theorem operation_ok {s : State} (A : GenerateKeyABI s) :
    WP isa Impl.Ffdh.X86.GenerateKey.code s fun u => spec s u.mem (u.gpr .eax) ∧ abiPreserved s u := by
  have hx : Rd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    show InRegions (s.rd ++ _) _ _ ∧ InRegions (s.rd ++ _) _ _ ∧ InRegions _ _ _ ∧ InRegions _ _ _
    rw [A.rd, A.wr]
    exact ⟨⟨_, List.mem_cons_self .., Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.contains_self _ _⟩,
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Region.contains_self _ _⟩⟩
  exact wrap_ok (wrapABI A) (NoSp.of_all frameBody_all) hx (Out := [xR s, yR s])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.retX
      · exact A.retY)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.xScratch.symm
      · exact A.yScratch.symm)
    (P := fun m e => spec s m e) fun f I espf Ft => frame_ok A f I espf Ft

theorem correct (s : State) (h : (Spec.Ffdh.generateKeyContract abi stack).pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.GenerateKey.code s trace t ∧ abiPreserved s t ∧
      (Spec.Ffdh.generateKeyContract abi stack).post s t := by
  obtain ⟨trace, t, E, V, P⟩ := operation_ok (generateKeyABI_of h)
  refine ⟨trace, t, E, P, ?_⟩
  sig_post [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro v
  exact V v

end VG.Proof.Ffdh.X86.KeyGen
