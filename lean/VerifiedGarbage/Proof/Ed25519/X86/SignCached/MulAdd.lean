module

public import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Calls
public import VerifiedGarbage.Impl.Ed25519.X86.SignCached
public import VerifiedGarbage.Proof.Ed25519.X86.Whole.Hash
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hash
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86.Lit
public import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
public import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
public import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ed25519.X86.MulAdd
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonInput
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
meta import VerifiedGarbage.Proof.Ed25519.X86.ScalarEngine
meta import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Ed25519.X86.CommonMemory
meta import VerifiedGarbage.Proof.X25519.X86.Arith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! ### `Ed25519.X86.MulAddVerified`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.X86.MulAddMain`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.X86.MulAddContract`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := callStk s
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      8 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint scratch ∧ stk.Disjoint r ∧ stk.Disjoint k ∧ stk.Disjoint a
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

theorem scalarMulAdd_pre {s : State} (h : scalarMulAddLocal.pre s) :
    ScratchPre s 4 5 ∧ InputPre s 4 2 8 ∧ InputPre s 4 3 8 ∧ InputPre s 4 1 8 ∧ OutputPre s 4 := by
  obtain ⟨rd, wr, os, rs, ks, ss, _, ars, ro, rsc, ofit, rfit, kfit, afit, sfit, spfit, h20, stk, tr, tk,
    ta⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rsc, h20, stk.symm⟩,
    ⟨?_, kfit, ?_, by rw [sub, addr_zero]; exact tk.symm⟩, ⟨?_, afit, ?_, by rw [sub, addr_zero]; exact ta.symm⟩,
    ⟨?_, rfit, ?_, by rw [sub, addr_zero]; exact tr.symm⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ks
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ss
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact rs
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.MulAddSetup`. -/
section
/-! Merged from `Proof.Ed25519.X86.MulAddWide`. -/
section
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulTerms_value (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) = colv m x (prodTerms 256 288 k) +
      (if k < 8 then wv m x (320 + 4 * k) else 0) := by
  simp only [scalarMulTerms, colv, List.map_append, List.sum_append]
  split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, tval]

theorem num_extend8 (f : Nat → Nat) : num (fun k => if k < 8 then f k else 0) 16 = num f 8 := by
  rw [num_16]
  have h0 : num (fun k => if 8 + k < 8 then f (8 + k) else 0) 8 = 0 := by
    have he : (fun k => if 8 + k < 8 then f (8 + k) else 0) = (fun _ => 0) := by
      funext k; rw [ite_eq_right (by omega_using [])]
    rw [he]; rfl
  rw [h0, Nat.mul_zero, Nat.add_zero]
  exact num_congr fun k hk => ite_eq_left hk

theorem scalarMulTerms_num (m : Mem) (x : BitVec 32) :
    num (fun k => colv m x (scalarMulTerms k)) 16 = fe m x 256 * fe m x 288 + fe m x 320 := by
  simp only [scalarMulTerms_value]
  rw [num_add, num_extend8]
  have hp : num (fun k => colv m x (prodTerms 256 288 k)) 16 = fe m x 256 * fe m x 288 := by
    simp only [colv, prodTerms, List.map_map]
    exact prod_identity (fun i => wv m x (256 + 4 * i)) (fun i => wv m x (288 + 4 * i))
  rw [hp]; rfl

theorem scalarMulTerms_bound (m : Mem) (x : BitVec 32) (k : Nat) :
    colv m x (scalarMulTerms k) < 2 ^ 68 := by
  rw [scalarMulTerms_value]
  have hl : (prodTerms 256 288 k).length ≤ 8 := by
    simp only [prodTerms, List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hp := colv_le_len (m := m) (x := x) (B := 2 ^ 64) (ts := prodTerms 256 288 k) fun t ht => by
    simp only [prodTerms, List.mem_map] at ht
    obtain ⟨i, _, rfl⟩ := ht
    exact wv_mul_le _ _ _ _
  have hm := Nat.mul_le_mul_right (2 ^ 64) hl
  have hw := wv_lt m x (320 + 4 * k)
  split <;> omega_using [hp, hm, hw]

theorem scalarMulTerms_reads {k : Nat} (hk : k < 16) {t : Term} (ht : t ∈ scalarMulTerms k)
    {d : Nat} (hd : d ∈ treads t) : d + 4 ≤ 4096 ∧ 128 + 4 * k ≤ d := by
  simp only [scalarMulTerms, List.mem_append] at ht
  rcases ht with ht | ht
  · simp only [prodTerms, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at ht
    obtain ⟨i, ⟨hi, _, hki⟩, rfl⟩ := ht
    simp only [treads, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> constructor <;> omega_using [hk, hi, hki]
  · split at ht
    · simp only [List.mem_singleton] at ht; subst ht
      simp only [treads, List.mem_singleton] at hd; subst hd
      constructor <;> omega_using [hk]
    · simp only [List.not_mem_nil] at ht

theorem scalarWideMul_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block scalarWideMul) s fun t => Keep s t ∧ Frame [sub x 128 64] s.mem t.mem ∧
      num (fun k => wv t.mem x (128 + 4 * k)) 16 = fe s.mem x 256 * fe s.mem x 288 + fe s.mem x 320 := by
  refine WP.block_append (WP.mono zeroAcc_ok fun u ⟨ku, mu, au⟩ => ?_)
  refine WP.mono (cols_ok (ku.ctx hc) scalarMulTerms 16 (by decide)
    (fun k hk t ht d hd => let h := scalarMulTerms_reads hk ht hd; ⟨h.1, Or.inr h.2⟩)
    (fun k _ => scalarMulTerms_bound _ _ k) (by rw [au]; decide)) fun t ⟨kt, ft, et, _⟩ => ?_
  rw [au, Nat.zero_add, scalarMulTerms_num, mu] at et
  have hA := fe_lt s.mem x 256
  have hB := fe_lt s.mem x 288
  have hC := fe_lt s.mem x 320
  have hab := Nat.mul_le_mul (Nat.le_pred_of_lt hA) (Nat.le_pred_of_lt hB)
  change fe s.mem x 256 * fe s.mem x 288 ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) at hab
  have hz : acc t = 0 := by
    change _ + (2 ^ 256 * 2 ^ 256) * acc t = _ at et
    omega_using [et, hab, hC]
  rw [hz, Nat.mul_zero, Nat.add_zero] at et
  rw [mu] at ft
  exact ⟨ku.trans kt, ft, et⟩
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem copied_fe {s₀ t : State} {p x : BitVec 32} {dst : Nat}
    (hp : p.toNat + 32 ≤ 2 ^ 32)
    (hw : ∀ k < 8, wd t.mem x (dst + 4 * k) = wd s₀.mem p (4 * k)) :
    fe t.mem x dst = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem (p.setWidth 64) 32) := by
  have ew : fe t.mem x dst = num (fun k => wv s₀.mem p (0 + 4 * k)) 8 :=
    num_congr fun k hk => by simpa only [Nat.zero_add] using congrArg BitVec.toNat (hw k hk)
  rw [ew, ← decode_words s₀.mem 8 (by omega_using [hp]), addr_zero]

theorem scalarMulInputs_ok {s₀ s : State} (hp : ScratchPre s₀ 4 5)
    (hA : InputPre s₀ 4 2 8) (hB : InputPre s₀ 4 3 8) (hC : InputPre s₀ 4 1 8)
    (hs : Saved s₀ (arg s₀ 4) s) :
    WP isa (.block scalarMulInputs) s fun t => Saved s₀ (arg s₀ 4) t ∧
      fe t.mem (arg s₀ 4) 256 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 288 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 3).setWidth 64) 32) ∧
      fe t.mem (arg s₀ 4) 320 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32) := by
  have he : scalarMulInputs =
      (([.mov .esi (.mem (at_ .esp 12))] : List Instr) ++ copyWords 256 8) ++
      ((([.mov .esi (.mem (at_ .esp 16))] : List Instr) ++ copyWords 288 8) ++
      (([.mov .esi (.mem (at_ .esp 8))] : List Instr) ++ copyWords 320 8)) := by
    simp only [scalarMulInputs, List.append_assoc]
  rw [he]
  refine WP.block_append (WP.mono (loadInput_ok hp hA hs (by decide) (dst := 256)
    (by decide) (by decide) (by decide)) fun u ⟨hu, wu, _⟩ => ?_)
  refine WP.block_append (WP.mono (loadInput_ok hp hB hu (by decide) (dst := 288)
    (by decide) (by decide) (by decide)) fun v ⟨hv, wv, fv⟩ => ?_)
  refine WP.mono (loadInput_ok hp hC hv (by decide) (dst := 320)
    (by decide) (by decide) (by decide)) fun t ⟨ht, wt, ft⟩ => ?_
  refine ⟨ht, ?_, ?_, copied_fe hC.fit wt⟩
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide)),
      fe_frame1 fv hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hA.fit wu
  · rw [fe_frame1 ft hp.fit (by decide) (by decide) (Or.inl (by decide))]
    exact copied_fe hB.fit wv
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_correct {s : State} (h : scalarMulAddLocal.pre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  obtain ⟨hp, hA, hB, hC, ho⟩ := scalarMulAdd_pre h
  simp only [scalarMulAdd, List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (abiSave_ok hp) fun u hu => ?_))
  refine WP.block_append (WP.mono (scalarMulInputs_ok hp hA hB hC hu) fun v ⟨hv, evA, evB, evC⟩ => ?_)
  refine WP.mono (scalarWideMul_ok (hv.ctx hp.fit hp.wr hp.stk)) fun w ⟨kw, fw, ew⟩ => ?_
  have hw := hv.of_offset hp.fit (Keep.scalar kw) fw (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (scalarEngine_ok (hw.ctx hp.fit hp.wr hp.stk)) fun z ⟨kz, fz, ez⟩ => ?_)
  have hz := hw.scalarEngine hp.fit kz fz
  refine WP.mono (finishWords_ok hp ho hz (src := scalarR) (by decide)) fun t ⟨abi_t, et⟩ => ⟨abi_t, ?_⟩
  change Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 = _
  rw [et, ez, scalarInput_num w.mem hp.fit, ew, evA, evB, evC, Spec.Ed25519.scalarMulAdd]
  rw [Nat.add_comm]
end VG.Proof.Ed25519.X86
end

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem scalarMulAdd_wf {s : State} (h : scalarMulAddLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 4 5) s := by
  obtain ⟨hp, _, _, _, ho⟩ := scalarMulAdd_pre h
  obtain ⟨_, wr, _, _, _, _, ao, _⟩ := h
  exact scalarTaint_wf hp ho wr ao

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (scalarTaint 4 5) ?_ (by native_taint_decide)
  intro s t hs ht hp
  obtain ⟨sp, a0, a1, a2, a3, a4⟩ := hp
  have ps := (scalarMulAdd_pre hs).1
  have pt := (scalarMulAdd_pre ht).1
  refine scalarTaint_agree (scalarMulAdd_wf hs) (scalarMulAdd_wf ht) sp ?_ (by decide)
    hs.2.1 ht.2.1 ps.sp_fit pt.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [a0, a1, a2, a3, a4]

theorem scalarMulAdd_ok (s : State) (h : scalarMulAddLocal.pre s) :
    ∃ tr t, Exec isa scalarMulAdd s tr t ∧ abiPreserved s t ∧ scalarMulAddLocal.post s t :=
  scalarMulAdd_correct h

end VG.Proof.Ed25519.X86

end

end

@[expose] public section

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
open VG.Impl.Ed25519.X86 (scalarMulAdd)
open VG.Impl.Ed25519.X86.PublicKey (callWith)

def half (L : Lay) : Region := ⟨(L.out + 32).setWidth 64, 32⟩
def mulRd (L : Lay) : List Region := [field L 96, field L 128, field L 32, ⟨L.E.setWidth 64, 20⟩]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (t : State) : Prop :=
  Whole.slots L.E t 0 = L.out + 32 ∧ Whole.slots L.E t 1 = fp L 96 ∧
    Whole.slots L.E t 2 = fp L 128 ∧ Whole.slots L.E t 3 = fp L 32 ∧ Whole.slots L.E t 4 = L.scr

theorem mul_nosp : NoSp scalarMulAdd := NoSp.of_all (by lit_decide)
theorem mul_stack : stackUse scalarMulAdd = 0 := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem half_addr (hL : L.Ok) : (L.out + 32).setWidth 64 = L.out.setWidth 64 + 32 :=
  addr_eq (x := L.out) (k := 32) (by have := hL.no; omega_using [this])

theorem halfWithin (hL : L.Ok) : Whole.Within (half L) L.OUT :=
  ⟨32, half_addr hL, by change 32 + 32 ≤ 64; decide⟩

theorem mul_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  have a0 := (ca (j := 0) (by decide)).trans ha.1
  have a1 := (ca (j := 1) (by decide)).trans ha.2.1
  have a2 := (ca (j := 2) (by decide)).trans ha.2.2.1
  have a3 := (ca (j := 3) (by decide)).trans ha.2.2.2.1
  have a4 := (ca (j := 4) (by decide)).trans ha.2.2.2.2
  have ae := Whole.arg_base hc.esp (mulRd L) (mulWr L)
  have ret : Region.Sub ⟨(L.E - 4).setWidth 64, 4⟩ L.STK := Whole.below_sub_stack H.below (by decide)
  have args : Region.Sub ⟨L.E.setWidth 64, 20⟩ L.STK :=
    fun p hp => Whole.frame_sub L.E p (Region.sub_prefix (by decide) p hp)
  have out := (halfWithin hL).sub
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hc.esp, a0, a1, a2, a3, a4, ae]
  refine ⟨rfl, rfl, hL.oc.sub_left out, hL.kc.sub_left (field_sub hL (d := 96) (by decide)),
    hL.kc.sub_left (field_sub hL (d := 128) (by decide)), hL.kc.sub_left (field_sub hL (d := 32) (by decide)),
    (hL.ko.sub_left args).sub_right out, hL.kc.sub_left args,
    (hL.ko.sub_left ret).sub_right out, hL.kc.sub_left ret, ?_,
    field_fit hL (by decide), field_fit hL (by decide), field_fit hL (by decide), hL.nc, ?_⟩
  · have h := hL.no
    rw [BitVec.toNat_add, show (32 : BitVec 32).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega_using [h])]
    omega_using [h]
  · have e : (L.E - 4).toNat = L.E.toNat - 4 := sub_toNat (k := 4) (by have := hL.below; omega_using [this])
    have := hL.top; have := hL.below
    refine ⟨by rw [e]; omega_arith, by rw [e]; omega_using [this], ?_⟩
    simp only [callStk, State.withRegions_gpr, State.callEntry_esp, hc.esp]
    have hf : L.E.toNat + 256 ≤ 2 ^ 32 := by omega_arith
    exact ⟨hL.kc.sub_left (Whole.inner_sub_stack hL.below),
      Whole.inner_frame hL.below hf (d := 96) (n := 32) (by decide) (by decide),
      Whole.inner_frame hL.below hf (d := 128) (n := 32) (by decide) (by decide),
      Whole.inner_frame hL.below hf (d := 32) (n := 32) (by decide) (by decide)⟩

theorem mul_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (mulWr L ++ [below L.E 24]) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem ((L.out + 32).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 32).setWidth 64) 32) := by
  have cov := hash_covers (L := L) (rs := mulRd L ++ mulWr L) (by
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (fieldWithin hL (by decide))
    · exact .inl (argsWithin L (by decide))
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact scratch_covered ⟨0, by simp, by simp⟩)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr ⟨L.OUT, by simp [Lay.outputs], halfWithin hL⟩
    · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by simp⟩
  with_reducible
    refine Whole.call_ok hc hL.below scalarMulAdd_ok mul_nosp (by rw [mul_stack]; decide)
      (mul_pre hc hL ha) cov ws fun t ht hf _ post => ⟨ht, hf, ?_⟩
  obtain ⟨s₂, hm, _, hp⟩ := post
  have H := hashSpace hL
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hc.esp H.below H.frameFit hj
  change Spec.Ed25519.bytesAt s₂.mem ((arg s.callEntry 0).setWidth 64) 32 = Spec.Ed25519.scalarMulAdd
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 1).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 2).setWidth 64) 32)
    (Spec.Ed25519.bytesAt s.callEntry.mem ((arg s.callEntry 3).setWidth 64) 32) at hp
  rw [hm, (ca (by decide)).trans ha.1, (ca (by decide)).trans ha.2.1,
    (ca (by decide)).trans ha.2.2.1, (ca (by decide)).trans ha.2.2.2.1] at hp
  rw [field_ce hc hL (d := 96) (by decide), field_ce hc hL (d := 128) (by decide),
    field_ce hc hL (d := 32) (by decide)] at hp
  exact hp

theorem mul_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (primitiveWrites L (half L)) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out.setWidth 64 + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem ((fp L 96).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 128).setWidth 64) 32)
        (Spec.Ed25519.bytesAt s.mem ((fp L 32).setWidth 64) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha (vs := [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0])
    (by decide) (Whole.valid_all (by decide))) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs.slot hL (j := 0) (by decide) (by decide)
  have a1 := hs.slot hL (j := 1) (by decide) (by decide)
  have a2 := hs.slot hL (j := 2) (by decide) (by decide)
  have a3 := hs.slot hL (j := 3) (by decide) (by decide)
  have a4 := hs.slot hL (j := 4) (by decide) (by decide)
  change Whole.slots L.E u 4 = L.scr + 0#32 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hft, hp⟩ =>
    ⟨ht, primitive_frame hf hft, ?_⟩
  rw [half_addr hL, field_setup hL hf (d := 96) (by decide) (by decide),
    field_setup hL hf (d := 128) (by decide) (by decide),
    field_setup hL hf (d := 32) (by decide) (by decide)] at hp
  exact hp

end VG.Proof.Ed25519.X86.SignCached
