module

public import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
public import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
public import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonFinish

/-! ### `Ed25519.X86.ScalarVerified`, which this module and modules that import it used -/

section

/-! ### `Ed25519.X86.ScalarContract`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def scalarReduceLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let input : Region := ⟨(arg s 1).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := callStk s
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      input.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 8 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint scratch ∧
      stk.Disjoint input
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

theorem scalarReduce_pre {s : State} (h : scalarReduceLocal.pre s) :
    ScratchPre s 2 3 ∧ InputPre s 2 1 16 ∧ OutputPre s 2 := by
  obtain ⟨rd, wr, os, ins, _, ars, ro, rs, ofit, ifit, sfit, spfit, h20, ks, ki⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rs, h20, ks.symm⟩,
    ⟨?_, ifit, ?_, by rw [sub, addr_zero]; exact ki.symm⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ins
  · rw [wr]; simp
end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.ScalarMain`. -/

@[expose] public section

section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_correct {s : State} (h : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  obtain ⟨hp, hi, ho⟩ := scalarReduce_pre h
  simp only [scalarReduce, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.mono (loadInput_ok hp hi hu (by decide) (dst := 128) (by decide) (by decide) (by decide))
    fun v ⟨hv, words, _⟩ => ?_
  refine WP.seq (WP.mono (scalarEngine_ok (hv.ctx hp.fit hp.wr hp.stk)) fun w ⟨kw, fw, vw⟩ => ?_)
  have hw := hv.scalarEngine hp.fit kw fw
  refine WP.mono (finishWords_ok hp ho hw (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, vw, Spec.Ed25519.scalarReduce, scalarInput_num v.mem hp.fit]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  apply congrArg (· % Spec.Ed25519.L)
  have ew : num (fun k => wv v.mem (arg s 2) (128 + 4 * k)) 16 =
      num (fun k => wv s.mem (arg s 1) (0 + 4 * k)) 16 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (words k hk)
  rw [ew, ← decode_words s.mem 16 (by have := hi.fit; omega_using [this]), addr_zero]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarReduce_wf {s : State} (h : scalarReduceLocal.pre s) : VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  obtain ⟨hp, _, ho⟩ := scalarReduce_pre h
  exact scalarTaint_wf hp ho h.2.1 h.2.2.2.2.1

theorem scalarReduce_ct : ConstantTime isa scalarReduceLocal.pre scalarReduceLocal.pub scalarReduce := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 2 3) ?_ (by native_taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2⟩ := hp
  have ps := (scalarReduce_pre hs).1
  have pt := (scalarReduce_pre ht).1
  refine scalarTaint_agree (scalarReduce_wf hs) (scalarReduce_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

theorem scalarReduce_ok (s : State) (h : scalarReduceLocal.pre s) :
    ∃ tr t, Exec isa scalarReduce s tr t ∧ abiPreserved s t ∧ scalarReduceLocal.post s t :=
  scalarReduce_correct h

end VG.Proof.Ed25519.X86

end

end

@[expose] public section

namespace VG.Proof.Ed25519.X86.Whole
open VG VG.X86 VG.Impl.Ed25519.X86

theorem frame_addr {E : BitVec 32} {d : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) :
    (E + BitVec.ofNat 32 d).setWidth 64 = E.setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega_using [hf, hd])

theorem frame_fit {E : BitVec 32} {d n : Nat} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hd : d < 256) (hn : d + n ≤ 256) : (E + BitVec.ofNat 32 d).toNat + n ≤ 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hf, hd]), Nat.mod_eq_of_lt (by omega_using [hd])]
  omega_using [hf, hn]

theorem frame_below {E : BitVec 32} {d n : Nat} (he : 24 ≤ E.toNat)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hd : d < 256) (hn : d + n ≤ 256) :
    (below E 4).Disjoint ⟨(E + BitVec.ofNat 32 d).setWidth 64, n⟩ := by
  change Region.Disjoint ⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
  rw [Taint.sub_setWidth (by omega_using [he] : 4 ≤ E.toNat), frame_addr hf hd]
  exact Offset.disjoint_below_above _ (by omega_using [hn])

theorem reduce_nosp : NoSp scalarReduce := NoSp.of_all (by lit_decide)
theorem reduce_stack : stackUse scalarReduce = 0 := by lit_decide

def reduceRd (E : BitVec 32) : List Region :=
  [⟨(E + 192).setWidth 64, 64⟩, ⟨E.setWidth 64, 12⟩]
def reduceWr (E scr : BitVec 32) (d : Nat) : List Region :=
  [⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩, ⟨scr.setWidth 64, 8192⟩]

variable {E scr : BitVec 32} {g : Reg → BitVec 32} {m₀ : Mem} {rd wr : List Region}
    {s : State} {d : Nat}

theorem reduce_pre (hc : Ctx E g m₀ rd wr s) (H : HashSpace E scr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : slots E s 1 = E + 192) (a2 : slots E s 2 = scr) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd E) (reduceWr E scr d)) := by
  have ca {j : Nat} (hj : j < 64) := call_arg hc.esp H.below H.frameFit hj
  have e0 := (ca (j := 0) (by decide)).trans a0
  have e1 := (ca (j := 1) (by decide)).trans a1
  have e2 := (ca (j := 2) (by decide)).trans a2
  have outSub : Region.Sub ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (STK E) := by
    rw [frame_addr H.frameFit (by omega_using [hd'])]
    exact fun p hp => frame_sub E p (Offset.sub_base _ hd' p hp)
  have digSub : Region.Sub ⟨(E + 192).setWidth 64, 64⟩ (STK E) := by
    have e : (E + 192).setWidth 64 = E.setWidth 64 + 192 := frame_addr H.frameFit (by decide : 192 < 256)
    rw [e]
    exact fun p hp => frame_sub E p (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp)
  have argSub : Region.Sub ⟨E.setWidth 64, 12⟩ (STK E) :=
    fun p hp => frame_sub E p (Region.sub_prefix (by decide) p hp)
  have ab := arg_base hc.esp (reduceRd E) (reduceWr E scr d)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, e0, e1, e2, ab]
  refine ⟨rfl, rfl, H.sep.sub_left outSub, H.sep.sub_left digSub, ?_, H.sep.sub_left argSub,
    frame_below H.below H.frameFit (by omega_using [hd']) hd', H.sep.sub_left (below_sub_stack H.below (by decide)),
    frame_fit H.frameFit (by omega_using [hd']) hd', frame_fit H.frameFit (by decide) (by decide), H.scratchFit, ?_⟩
  · rw [frame_addr H.frameFit (by omega_using [hd'])]
    exact Offset.base_disjoint _ (by omega_using [hd]) (by omega_using [hd'])
  · have e : (E - 4).toNat = E.toNat - 4 := sub_toNat (k := 4) (by have := H.below; omega_using [this])
    have := H.frameFit; have := H.below
    refine ⟨by rw [e]; omega_arith, by rw [e]; omega_using [this], ?_⟩
    simp only [callStk, State.withRegions_gpr, State.callEntry_esp, hc.esp]
    exact ⟨H.call_stk, inner_frame H.below H.frameFit (d := 192) (n := 64) (by decide) (by decide)⟩

theorem reduce_call (hc : Ctx E g m₀ rd wr s) (H : HashSpace E scr)
    (hscr : (⟨scr.setWidth 64, 8192⟩ : Region) ∈ wr)
    (hd : 24 ≤ d) (hd' : d + 32 ≤ 256)
    (a0 : slots E s 0 = E + BitVec.ofNat 32 d)
    (a1 : slots E s 1 = E + 192) (a2 : slots E s 2 = scr) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx E g m₀ rd wr t ∧
      Frame (reduceWr E scr d ++ [below E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((E + BitVec.ofNat 32 d).setWidth 64) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem ((E + 192).setWidth 64) 64) := by
  have wd : Within ⟨(E + 192).setWidth 64, 64⟩ (FR E) :=
    ⟨192, frame_addr H.frameFit (by decide), by change 192 + 64 ≤ 256; decide⟩
  have wo : Within ⟨(E + BitVec.ofNat 32 d).setWidth 64, 32⟩ (FR E) :=
    ⟨d, frame_addr H.frameFit (by omega_using [hd']), hd'⟩
  have cov : Covers (reduceRd E ++ reduceWr E scr d) (rd ++ FR E :: wr) := by
    refine Covers.of_sub ?_
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨FR E, by simp, wd⟩
    · exact ⟨FR E, by simp, 0, by simp, by change 0 + 12 ≤ 256; decide⟩
    · exact ⟨FR E, by simp, wo⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ hscr), 0, by simp, by simp⟩
  have ws : ∀ r ∈ reduceWr E scr d, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl wo
    · exact .inr ⟨_, hscr, 0, by simp, by simp⟩
  with_reducible
    refine call_ok hc H.below scalarReduce_ok reduce_nosp (by rw [reduce_stack]; decide)
      (reduce_pre hc H hd hd' a0 a1 a2) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨t₂, hm, _, hp⟩ := post
  have ca {j : Nat} (hj : j < 64) := call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt t₂.mem ((arg s.callEntry 0).setWidth 64) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 64) at hp
  rw [hm, (ca (j := 0) (by decide)).trans a0, (ca (j := 1) (by decide)).trans a1] at hp
  rw [hp]
  refine congrArg Spec.Ed25519.scalarReduce ?_
  apply callEntry_bytes (r := ⟨(E + 192).setWidth 64, 64⟩) ?_ (by change 64 ≤ 2 ^ 64; decide)
  rw [hc.esp]
  exact (frame_below H.below H.frameFit (by decide : 192 < 256) (by decide : 192 + 64 ≤ 256)).symm

end VG.Proof.Ed25519.X86.Whole
