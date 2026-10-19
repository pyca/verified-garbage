module

public import VerifiedGarbage.Proof.Dsa.X86_64.ChildBases
public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCount
public import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildBases
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCount
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.X86_64.NewChild
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.X86_64.NewChild
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Spec.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Child
meta import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.Setup
meta import VerifiedGarbage.Proof.Dsa.X86_64.Store
meta import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Constant time of creating and initializing a modulus workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ChildPublic extends BPub where
  extent : pWorkspace ≤ x.Z
  offset : x.o < 2 ^ 31
  lo : slot x.w 8 ≤ x.o
  hi : x.o + slot x.wx 8 + tabBytes x.wx ≤ x.Z
  widthPositive : 2 ≤ x.wx
  widthParent : x.wx ≤ x.w
  widthBound : x.w < 2 ^ 30
  positive : 1 ≤ len
  lengthBound : len < 2 ^ 31
  width : x.wx = (len + 7) / 8

def ChildPre (a : Operand) (p : ChildPublic) (s : State) : Prop :=
  (∃ mi, Good s p.x.B p.x.Z p.x.w mi) ∧
  ∃ bs, pointerValue s.mem p.x.B a.pointer = p.ptr ∧
    word s.mem p.x.B a.length.offset = BitVec.ofNat 64 bs.length ∧
    Src s p.x.B p.x.Z p.ptr bs ∧ bs.length = p.len

theorem childHead_ok (a : Operand) (ha : pointerFits a.pointer) {p : ChildPublic} {s : State}
    (h : ChildPre a p s) :
    WP isa (.block (Core.operand arg argLen a ++ childCount p.x.o ++ childBases)) s
      (LPre aN arg argLen p.toBPub) := by
  obtain ⟨⟨mi, hg⟩, bs, hp, hl, hsrc, hlen⟩ := h
  have hkw : p.x.wx = (bs.length + 7) / 8 := by rw [hlen]; exact p.width
  have hslot : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega
  have hbound : p.x.o + slot p.x.wx 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; have := p.hi; omega
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (operand_context hg p.extent a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hup, hul, _, hfu, hku⟩ => ?_
  have hfui : Frm p.x.B (initRanges p.x.o p.x.wx) s.mem u.mem := init_call_frame hfu
  have hul' : word u.mem p.x.B (8 * argLen) = BitVec.ofNat 64 bs.length := hul.trans hl
  refine WP.mono (newChild_ok hgu p.extent p.offset (by rw [hlen]; have := p.lengthBound; omega)
    hul' p.lo (by rw [← hkw]; exact p.hi)) fun v ⟨oldMi, hcv, hfv, hkv⟩ => ?_
  rw [← hkw] at hcv
  have hfvi : Frm p.x.B (initRanges p.x.o p.x.wx) u.mem v.mem := init_child_frame hfv (by omega) hbound
  have hvsrc := init_source (hfui.trans hfvi) (hku.trans hkv)
    (Nat.le_trans (by decide) p.extent) (by have := p.hi; omega) hsrc
  have hvword : ∀ i < 32, word v.mem p.x.B (8 * i) = word u.mem p.x.B (8 * i) := by
    intro i hi
    have hff : Frm (off p.x.B p.x.o) [(48, 88)] u.mem v.mem := Frm.of_outside hfv (by simp)
    exact hff.word_below (L := 136) (by intro r hr; rw [List.mem_singleton.mp hr]; decide)
      (by omega) (by have := p.lo; unfold slot hdrBytes at this; omega)
      (by have := p.lo; unfold slot hdrBytes at this; omega)
  exact ⟨oldMi, bs, hcv, p.widthPositive, p.widthParent, p.widthBound,
    by decide, by decide, by decide, (hvword _ (by decide)).trans (hup.trans hp),
    (hvword _ (by decide)).trans hul', hlen, hvsrc, hlen ▸ p.positive,
    hlen ▸ p.lengthBound, hkw ▸ Nat.le_refl _⟩

theorem loadModulus_ct : RelCT isa (Two (LPre aN arg argLen)) (Arithmetic.load aN arg argLen)
    (Two (fun (p : BPub) s => LinkedPre p.x s)) := by
  refine two_post (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) ?_
  intro p s ⟨minv, bs, hc, hw2, hwx, hw30, ha, hp', hl', hp, hl, _, hs, h1, h31, hfit⟩
  exact WP.mono (load_ok hc hw2 hwx hw30 ha hp' hl' hp hl hs h1 h31 hfit)
    fun t ⟨ht, _⟩ => ⟨minv, ht⟩

theorem sealChild_ct : RelCT isa (Two LinkedPre) (.block (initInverse ++ [Crt.leave]))
    (fun _ _ => True) := by
  change RelCT isa (Two LinkedPre) (.block (([.mov .rbx (.mem (hdr (sArr aN)))] : List Instr) ++
    ([.mov .rbx (.mem (at0 .rbx))] ++ minv ++ [.store (hdr sMinv) .r15, Crt.leave]))) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun (p : XPub) t => t.gpr .rdi = off p.B p.o ∧
    t.gpr .rbx = off (off p.B p.o) (slot p.wx aN)) [.rdi]
    (pins_of (fun p _ => off p.B p.o) (by
      intro p s ⟨_, hc⟩ r hr; obtain rfl := List.mem_singleton.mp hr; exact hc.rdi)) (by taint_decide) ?_) ?_
  · intro p s ⟨_, hc⟩
    xrun [State.ea, hdr, hdrOff, hc.rdi, hc.hdr.harr aN (by decide),
      hc.good.scr.ld (hdr_lt_slot p.wx 8 (show sArr aN < 32 by decide))]
  · exact two_taint [.rdi, .rbx] (pins_of (fun p r => if r = .rdi then off p.B p.o else
      off (off p.B p.o) (slot p.wx aN)) (by
        intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2)) (by taint_decide)

theorem child_ct (a : Operand) (ha : pointerFits a.pointer) (o : Nat)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi])
      (.block (Core.operand arg argLen a ++ childCount o ++ childBases)) hint).isSome = true) :
    RelCT isa (Two (fun p s => ChildPre a p s ∧ p.x.o = o)) (SignVerify.child o a) (fun _ _ => True) := by
  have hhead : RelCT isa (Two (fun p s => ChildPre a p s ∧ p.x.o = o))
      (.block (Core.operand arg argLen a ++ childCount o ++ childBases))
      (Two (fun (p : ChildPublic) s => LPre aN arg argLen p.toBPub s)) := by
    refine two_piece [.rdi] (pins_of (fun p _ => p.x.B) (by
      intro p s h r hr; obtain rfl := List.mem_singleton.mp hr
      obtain ⟨_, hg⟩ := h.1.1; exact hg.rdi)) hT ?_
    intro p s ⟨h, ho⟩
    rw [← ho]
    exact childHead_ok a ha h
  have hload := two_map ChildPublic.toBPub (fun _ _ h => h) loadModulus_ct
  have hseal := two_map (fun p : BPub => p.x) (fun _ _ h => h) sealChild_ct
  have h := RelCT.seq hhead (RelCT.seq hload hseal)
  simpa only [SignVerify.child, seqs, childCount, childBases, initInverse,
    List.append_assoc, List.cons_append, List.nil_append] using h

end VG.Proof.Dsa.X86_64
