module

public import VerifiedGarbage.Proof.Dsa.X86_64.ChildBases
public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCount
public import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.X86_64.NewChild
import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildBases
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.X86_64.NewChild
meta import VerifiedGarbage.Proof.Dsa.X86_64.InitFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify

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
