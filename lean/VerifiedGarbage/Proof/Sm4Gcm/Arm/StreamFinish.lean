module

public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Flush
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sm4Gcm.Arm.TextAbsorb`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: absorbing the text (`textAbsorb`)

Untrusted: everything here is checked by Lean. `textAbsorb` absorbs the `len`
bytes at `data` into GHASH as text: before the first text (`text_len` 0) it
pads the additional data first (`firstFlush`), and it does nothing for no
bytes (`textAbsorb_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput zeros padLen)
open VG.Proof.Gcm (Absorbed)

/-- The regions `textAbsorb` writes. -/
abbrev taFrame (st w sp : BitVec 32) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 16, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem lowTo_mod16 {hi lo : BitVec 32} {P : Nat} (h : (hi ++ lo).toNat = P) : lo.toNat % 16 = P % 16 := by
  rw [Proof.Gcm.toNat_append] at h; omega_arith

theorem z_sub0 (x : BitVec 32) : (x - 0#32 == 0) = decide (x.toNat = 0) := by
  by_cases h : x.toNat = 0 <;> simp [BitVec.toNat_eq, h]

theorem or_zero_iff (lo hi : BitVec 32) : (lo ||| hi).toNat = 0 ↔ (hi ++ lo).toNat = 0 := by
  constructor
  · intro h
    have : lo ||| hi = 0#32 := BitVec.eq_of_toNat_eq (by simpa using h)
    rw [BitVec.or_eq_zero_iff] at this
    obtain ⟨rfl, rfl⟩ := this; rfl
  · intro h
    rw [Proof.Gcm.toNat_append] at h
    have h1 : lo = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega_arith)
    have h2 : hi = 0#32 := BitVec.eq_of_toNat_eq (by simp; omega_arith)
    subst h1 h2; rfl

/-- After `textAbsorb`, from `m₀`: GHASH has absorbed `x`. -/
structure TaOut (c st w sp k7 k8 : BitVec 32) (s₀ : State) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  args : ArgsKeep 5 s₀ s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (taFrame st w sp) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

omit L in
theorem abs_taFrame {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') : Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

omit L in
theorem t_taFrame {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') : Frame (taFrame st w sp) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem textAbsorb_ok [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s : State} {H : Block} {a ct : List Byte} (he : Env c st w sp k7 k8 s)
    (hk : ArgsKeep 5 s₀ s) (hf : s₀.sp.toNat + 4 * 5 ≤ 2 ^ 32) (hin : args s₀ 5 ∈ s₀.rd)
    (hA : ∀ r ∈ taFrame st w sp, (args s₀ 5).Disjoint r)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (hd : DataOk st w sp s (arg s₀ 2) (arg s₀ 3).toNat)
    (ha : a.length % 16 = k8.toNat % 16) (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa textAbsorb s (TaOut c st w sp k7 k8 s₀ H (ghashInput a ct)
      (ghashInput a (ct ++ bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)) s.mem) := by
  have hn := (arg s₀ 3).isLt
  obtain ⟨i5, v5⟩ := hk.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, h5₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r5 12, .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r5 = arg s₀ 3 ∧ s₁.z = decide ((arg s₀ 3).toNat = 0) ∧ (∀ r, r ≠ .r5 → s₁.gpr r = s.gpr r) ∧
      Keeps s s₁ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · simp only [z_subFlags, gpr_setReg, ite_true, v5]
      exact z_sub0 _
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hK₁.sp hK₁.rd hK₁.wr
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf' => ?_)
  · have h0 : (arg s₀ 3).toNat = 0 := by simpa using ht
    rw [h0]
    refine WP.block_nil ⟨he₁, hk₁, by rw [hK₁.mem]; exact hH, fun hab => ?_, by rw [hK₁.mem]; exact Frame.refl _ _⟩
    simp only [bytesAt, List.range_zero, List.map_nil, List.append_nil, hK₁.mem]; exact hab
  have h0 : (arg s₀ 3).toNat ≠ 0 := by simpa using hf'
  -- `Z` iff no text so far
  obtain ⟨i2, v2⟩ := hk₁.at hf hin 0 (by decide) (show 4 * 0 = 0 from rfl)
  obtain ⟨i3, v3⟩ := hk₁.at hf hin 1 (by decide) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₂, run₂, hz₂, hg₂, hK₂⟩ : ∃ s₂, runBlock isa tlenZero s₁ = some s₂ ∧
      s₂.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [z_sub0, ← hP]
      exact decide_eq_decide.mpr (or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  have hk₂ := hk₁.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  have hm₂ : s₂.mem = s.mem := hK₂.mem.trans hK₁.mem
  -- the additional data padded, before the first text
  let x' := if ct = [] then a ++ zeros (padLen a.length) else ghashInput a ct
  have hx' : x'.length % 16 = ct.length % 16 := by
    by_cases hc : ct = []
    · subst hc; simp only [x', ite_true, List.length_append, Proof.Gcm.length_zeros, List.length_nil]
      exact Proof.Gcm.length_pad_mod _
    · simp only [x', hc, ite_false, Proof.Gcm.ghashInput_of_ne hc, List.length_append, Proof.Gcm.length_zeros]
      have := Proof.Gcm.length_pad_mod a.length; omega_arith
  have hlt := Nat.mod_lt a.length (show 16 > 0 by decide)
  have mid : WP isa (.ite .eq firstFlush (.block [])) s₂ fun s₄ => Env c st w sp k7 k8 s₄ ∧ ArgsKeep 5 s₀ s₄ ∧
      blockAt s₄.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      (Absorbed s.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
        Absorbed s₄.mem (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H x') ∧
      Frame (tFrame st w sp 16) s.mem s₄.mem := by
    refine WP.ite _ (eval_eq' hz₂) (fun ht => ?_) (fun hf₂ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      have v0 := he₂.r8
      obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r8 (imm 15)] s₂ = some s₃ ∧
          s₃.gpr .r6 = BitVec.ofNat 32 (a.length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
        refine ⟨_, by arun [], ?_, ?_, ?_⟩
        · simp only [gpr_setReg, ite_true, v0, and15, ha]
        · intro r a; simp [gpr_setReg, a]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
      have he₃ := he₂.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide)) hK₃.sp hK₃.rd hK₃.wr
      have hm₃ : s₃.mem = s.mem := hK₃.mem.trans hm₂
      refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := a) (H := H) ⟨he₃, by rw [hm₃]; exact hH⟩ h6₃))
        fun s₄ hh => ?_
      obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
      have hf₄ := hfl.frame
      rw [hm₃] at hf₄
      refine ⟨hfl.env, (hk₂.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr).frame hf hfl.frame
          (fun r hr => hA r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
            rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₄ rd₄ wr₄, hfl.hH, fun hab => ?_, hf₄⟩
      simp only [x', hc, ite_true]
      refine hfl.abs ?_
      rw [hm₃]; subst hc; exact hab
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₂
      refine WP.block_nil ⟨he₂, hk₂, by rw [hm₂]; exact hH, fun hab => ?_, by rw [hm₂]; exact Frame.refl _ _⟩
      simp only [x', hc, ite_false, hm₂]; exact hab
  refine WP.seq (WP.mono mid fun s₄ ⟨he₄, hk₄, hH₄, hab₄, hf₄⟩ => ?_)
  -- the arguments of `absorb`
  obtain ⟨i4, v4⟩ := hk₄.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i5', v5'⟩ := hk₄.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨i2', v2'⟩ := hk₄.at hf hin 0 (by decide) (show 4 * 0 = 0 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa textArgs s₄ = some s₅ ∧
      s₅.gpr .r4 = arg s₀ 2 ∧ s₅.gpr .r5 = arg s₀ 3 ∧ s₅.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 0).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5', v5', i2', v2'], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v4]
    · simp [gpr_setReg, v5']
    · simp only [gpr_setReg, ite_true, v2', and15]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide)) hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  have hrd₅ : s₅.rd = s.rd := hk₅.rd.trans hk.rd.symm
  have hwr₅ : s₅.wr = s.wr := hk₅.wr.trans hk.wr.symm
  have hai : AbsIn c st w sp k7 k8 16 H x' (arg s₀ 2) (arg s₀ 3).toNat s₅ :=
    ⟨he₅, h4₅, by rw [h5₅]; simp, by rw [h6₅, hx', lowTo_mod16 hP], hd.of_eq hrd₅ hwr₅, by rw [hK₅.mem]; exact hH₄⟩
  refine WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) hai)) fun s₆ hh => ?_
  obtain ⟨ho, rd₆, wr₆, sp₆⟩ := hh
  have hdat : bytesAt s₅.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    rw [hK₅.mem]
    exact bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hd.st.sub_right (Lay.stSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.w.sub_right (Lay.wSub (by decide))
      · exact hd.stk.symm) (by have := hd.lt; omega_arith)
  have hne : bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat ≠ [] := by
    intro e; have := congrArg List.length e; rw [length_bytesAt] at this; exact h0 (by simpa using this)
  refine ⟨ho.env, hk₅.frame hf ho.frame (fun r hr => hA r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) sp₆ rd₆ wr₆, ?_, ?_, ?_⟩
  · rw [blockAt_frame ho.frame (ctx_absFrame L (.inr rfl)), hK₅.mem, hH₄]
  · intro hab
    have := ho.abs (by rw [hK₅.mem]; exact hab₄ hab)
    rw [hdat] at this
    rw [Proof.Gcm.ghashInput_append _ _ _ hne]
    exact this
  · rw [hK₅.mem] at ho
    exact (t_taFrame hf₄).trans (abs_taFrame ho.frame)

end

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.FinTag`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: the tag of a streaming state (`finTag o`)

Untrusted: everything here is checked by Lean. `finTag o` pads the buffered
bytes (of the additional data if there is no text, of the text otherwise)
and absorbs them, then the lengths block, and writes the tag to `W + o`
(`finTag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput ghash ghashFrom blocks zeros padLen toBytes ofBytes)
open VG.Proof.Gcm (Absorbed lensBlock padded)

theorem disj_sub {X : Region} {rs rs' : List Region} (h : ∀ r ∈ rs', X.Disjoint r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : ∀ r ∈ rs, X.Disjoint r := fun r hr => by
  obtain ⟨r', hr', hsub⟩ := hs r hr; exact (h r' hr').sub_right hsub

/-- `tFrame` is within `tagFrame`. -/
theorem tFrame_sub {st w sp : BitVec 32} {o : Nat} :
    ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ tagFrame st w sp o, Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by simpa using Offset.sub_base (State.addr st) (show 16 + 16 ≤ 32 by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 256⟩, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_tagFrame {st w sp : BitVec 32} {o : Nat} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (tagFrame st w sp o) m m' := h.sub tFrame_sub

/-- After `finTag o`, from `m₀`, for additional data of `ah:k8` bytes. -/
structure FinOut (c st w sp ah k8 : BitVec 32) (na : Nat) (s₀ : State) (o : Nat) (H : Block) (a ct : List Byte)
    (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env c st w sp k7 k8 s
  args : ArgsKeep na s₀ s
  out : Absorbed m₀ (State.addr st + BitVec.ofNat 64 16) (State.addr st + BitVec.ofNat 64 32) H (ghashInput a ct) →
    bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) 16 =
      toBytes (ghashFrom H (ghash H (blocks (padded a ct))) [ofBytes (lensBlock (ah ++ k8).toNat ct.length)]
        ^^^ ciphOf m₀ (State.addr c) (blockAt m₀ (State.addr st)))
  frame : Frame (tagFrame st w sp o) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem finTag_ok [VG.Proof.Gcm.Arm.GhashLaw] {na : Nat} (hna : 2 ≤ na) {s₀ s : State} {o : Nat} (ho : o = 0 ∨ o = 112) {H : Block}
    {a ct : List Byte} (he : Env c st w sp k7 k8 s) (hk : ArgsKeep na s₀ s) (hf : s₀.sp.toNat + 4 * na ≤ 2 ^ 32)
    (hin : args s₀ na ∈ s₀.rd) (hA : ∀ r ∈ tagFrame st w sp o, (args s₀ na).Disjoint r)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H)
    (ha : a.length % 16 = k8.toNat % 16) (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa (finTag o) s (FinOut c st w sp k7 k8 na s₀ o H a ct s.mem) := by
  have hlt := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  obtain ⟨i2, v2⟩ := hk.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨i3, v3⟩ := hk.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₁, run₁, hz₁, hg₁, hK₁⟩ : ∃ s₁, runBlock isa tlenZero s = some s₁ ∧
      s₁.z = decide (ct.length = 0) ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [tlenZero]; arun [i2, v2, i3, v3], ?_, ?_, ?_⟩
    · simp only [z_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, v2, v3]
      rw [z_sub0, ← hP]
      exact decide_eq_decide.mpr (or_zero_iff _ _)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hk₁ := hk.of_eq hK₁.mem hK₁.sp hK₁.rd hK₁.wr
  -- `r6`: the length of the buffered bytes, modulo 16
  have mid : WP isa (.ite .eq (.block [.mov .r6 (.reg .r8)]) (.block [.ldrSp .r6 0])) s₁ fun s₂ =>
      (s₂.gpr .r6).toNat % 16 = (ghashInput a ct).length % 16 ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧
        Keeps s₁ s₂ := by
    refine WP.ite _ (eval_eq' hz₁) (fun ht => ?_) (fun hf₁ => ?_)
    · have hc : ct = [] := List.eq_nil_of_length_eq_zero (by simpa using ht)
      subst hc
      have v0 : s₁.gpr .r8 = k8 := by rw [hg₁ _ (by decide) (by decide), he.r8]
      refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
      · simp [gpr_setReg, v0, Proof.Gcm.ghashInput_nil, ha]
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    · have hc : ct ≠ [] := fun e => by subst e; simp at hf₁
      obtain ⟨i2', v2'⟩ := hk₁.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
      refine WP.of_runBlock ⟨_, by arun [i2', v2'], ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, v2', Proof.Gcm.ghashInput_of_ne hc, List.length_append,
          Proof.Gcm.length_zeros, lowTo_mod16 hP]
        have := Proof.Gcm.length_pad_mod a.length; omega_arith
      · intro r hr; simp [gpr_setReg, hr]
      · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.mono mid fun s₂ ⟨h6₂, hg₂, hK₂⟩ => ?_)
  obtain ⟨s₃, run₃, h6₃, hg₃, hK₃⟩ : ∃ s₃, runBlock isa [.dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((ghashInput a ct).length % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, and15, h6₂]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hK₀₃ : Keeps s s₃ := (hK₁.trans hK₂).trans hK₃
  have he₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [hg₃ _ (by decide), hg₂ _ (by decide), hg₁ _ (by decide) (by decide)]) hK₀₃.sp hK₀₃.rd hK₀₃.wr
  have hk₃ := hk.of_eq hK₀₃.mem hK₀₃.sp hK₀₃.rd hK₀₃.wr
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl) (x := ghashInput a ct) (H := H)
    ⟨he₃, by rw [hK₀₃.mem]; exact hH⟩ h6₃)) fun s₄ hh => ?_)
  obtain ⟨hfl, rd₄, wr₄, sp₄⟩ := hh
  have hk₄ := hk₃.frame hf hfl.frame (disj_sub hA tFrame_sub) sp₄ rd₄ wr₄
  have hf₄ := hfl.frame
  rw [hK₀₃.mem] at hf₄
  -- the lengths
  have w0 := hfl.env.r8
  have w1 := hfl.env.r7
  obtain ⟨j2, w2⟩ := hk₄.at hf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨j3, w3⟩ := hk₄.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, hg₅, hK₅⟩ : ∃ s₅, runBlock isa [.mov .r4 (.reg .r8), .mov .r5 (.reg .r7),
      .ldrSp .r6 0, .ldrSp .r7 4] s₄ = some s₅ ∧ s₅.gpr .r4 = k8 ∧ s₅.gpr .r5 = k7 ∧ s₅.gpr .r6 = arg s₀ 0 ∧
      s₅.gpr .r7 = arg s₀ 1 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j2, w2, j3, w3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, w0]
    · simp [gpr_setReg, w1]
    · simp [gpr_setReg, w2]
    · simp [gpr_setReg, w3]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := hfl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₅ _ (by decide) (by decide) (by decide) (by decide))
    hK₅.sp hK₅.rd hK₅.wr
  have hk₅ := hk₄.of_eq hK₅.mem hK₅.sp hK₅.rd hK₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅ (H := H) (by rw [hK₅.mem]; exact hfl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, hP, hK₅.mem] at tg
  refine ⟨⟨_, tg.env⟩, hk₄.frame hf tg.frame hA (sp₆.trans hK₅.sp) (rd₆.trans hK₅.rd) (wr₆.trans hK₅.wr), fun hab => ?_, ?_⟩
  · rw [tg.out]
    have hw := (hfl.abs (by rw [hK₀₃.mem]; exact hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [show ghashInput a ct ++ zeros (padLen (ghashInput a ct).length) = padded a ct from rfl] at hw
    rw [hw, ciph_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.cs.sub_right (Lay.stSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.kc.symm),
      blockAt_frame hf₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simpa using Lay.st_st (st := st) (a := 0) (n := 16) (d := 16) (k := 16) (.inl (by decide)) (by decide)
            (by decide)
        · simpa using L.st_w (a := 0) (n := 16) (d := 96) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 16) (d := 512) (k := 256) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using (L.stk_st (a := 0) (n := 16) (by decide)).symm)]
  · exact (t_tagFrame hf₄).trans tg.frame

end

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.StreamCrypt`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.Arm.CryptOk`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- The rest of the keystream block. -/
theorem cryptHead_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ CrMid c st w sp k7 k8 icb P D n s.mem j s') := by
  obtain hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt32
  have he := h.env
  refine WP.seq (WP.mono (minLen_ok s h.r6 h.r5 (by omega_arith) hn') fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  obtain hk1 : 1 ≤ k := by omega_arith
  obtain hk16 : P % 16 + k ≤ 16 := by omega_arith
  obtain hkn : k ≤ n := by omega_arith
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r10 64,
      .dp .add .r1 .r1 (.reg .r6), .mov .r2 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]
      s₁ = some s₂ ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 (64 + P % 16) ∧ s₂.gpr .r2 = D ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    obtain e10 := hg .r10 (by decide) (by decide)
    obtain e4 := hg .r4 (by decide) (by decide)
    obtain e5 := hg .r5 (by decide) (by decide)
    obtain e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, ofNat_sub32 hkn hn']
    · simp [gpr_setReg, h3]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain hk₂' := hk.trans hk₂
  obtain eK : State.addr (st + BitVec.ofNat 32 (64 + P % 16)) = State.addr st + BitVec.ofNat 64 (64 + P % 16) :=
    L.stA (by omega_arith)
  obtain lp : LoopPre s₂ (st + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h1, h2, h3', hk1, by omega_arith, by rw [L.stN (by omega_arith)]; have := L.sw; omega_arith,
      by have := h.data.ok.fit; omega_arith, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr, eK]; exact covers_left (he.perm.stC (by omega_arith))
    · rw [hk₂'.wr]; exact (h.data.take hkn).wr
    · rw [eK]; exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eK, hk₂'.mem] at hm₃
  obtain hxl := length_xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k
  obtain fw : Frame [⟨State.addr D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact writeBytes_frame' _ hxl
  obtain hdisjst : ∀ r ∈ [(⟨State.addr D, k⟩ : Region)],
      (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨State.addr st + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  obtain he₃ : Env c st w sp k7 k8 s₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lo.sp.trans hk₂'.sp) (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr)
  obtain hc₃ : ciphOf s₃.mem (State.addr c) = ciphOf s.mem (State.addr c) :=
    ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx)
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h5],
    h.data.of_eq (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    refine (hc₀.head hP hk16).congr (blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    obtain e := bytesAt_writeBytes_self s.mem (State.addr D)
      (xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k) (by rw [hxl]; omega_arith)
    rw [hxl] at e
    rw [hm₃, e, xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem (State.addr D) k) (by rw [length_bytesAt]; exact hk16)
    rw [length_bytesAt, add_ofNat_assoc] at this
    exact this
  · exact bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (split_disj hkn h.data.ok.lt).symm) (by omega_arith)
  · by_cases hkk : k = n
    · left; omega_arith
    · right; omega_arith
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
/-- The split of the rest into whole blocks for `vg_sm4_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitCtr s = some s' ∧
      s'.gpr .r3 = D + BitVec.ofNat 32 j ∧ s'.gpr .r12 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain hand := and15 (BitVec.ofNat 32 (n - j))
  rw [toNat32 (by omega_arith)] at hand
  obtain hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) (by omega_arith)]; congr 1; omega_arith
  refine ⟨_, by simp only [splitCtr]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, shr4 (show n - j < 2 ^ 32 by omega_arith)]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, add32_ofNat_assoc]
  · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega_arith
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5,
      shr4 (show n - j < 2 ^ 32 by omega_arith)]
    rw [z_cmp (by omega_arith) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- The arguments of `vg_sm4_ctr32` for the whole blocks. -/
theorem wholeArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa [.mov .r0 (.reg .r9), addI .r2 .r10 48] s = some s' ∧
      s'.gpr .r0 = c ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain h9 := he.r9; have h10 := he.r10
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h10]
  · intro r a b; simp [gpr_setReg, a, b]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arguments of `vg_sm4_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {D : BitVec 32} {j nb : Nat} {s : State} (he : Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = D + BitVec.ofNat 32 j) (h12 : s.gpr .r12 = BitVec.ofNat 32 nb)
    (hdj : DataW c st w sp k7 k8 s (D + BitVec.ofNat 32 j) (16 * nb)) :
    CtrCall s c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb := by
  obtain eC := L.stA (d := 48) (by decide)
  have hk := he.sp
  refine ⟨h0, h2, h3, h12, by rw [hk]; exact L.sp8, by have := L.cw; omega_arith,
    by rw [L.stN (by decide)]; have := L.sw; omega_arith, by have := hdj.ok.fit; omega_arith,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact hdj.ok.stk
  · exact covers_prefix he.perm.ctx (by decide)
  · exact covers_cons (he.perm.stC (by decide)) hdj.wr

/-- The arguments of `vg_sm4_ctr32` on the keystream block. -/
theorem ctrTail_mk {s : State} (he : Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = st + BitVec.ofNat 32 64) (h12 : s.gpr .r12 = BitVec.ofNat 32 1) :
    CtrCall s c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) 1 := by
  obtain eC := L.stA (d := 48) (by decide)
  obtain eK := L.stA (d := 64) (by decide)
  have hk := he.sp
  refine ⟨h0, h2, h3, h12, by rw [hk]; exact L.sp8, by have := L.cw; omega_arith,
    by rw [L.stN (by decide)]; have := L.sw; omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, eK, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact L.stk_st (by decide)
  · exact covers_prefix he.perm.ctx (by decide)
  · exact covers_cons (he.perm.stC (by decide)) (he.perm.stC (by decide))

/-- Whole blocks. -/
theorem cryptWhole_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 icb P D n m₀ j s) (hc : ciphOf s.mem (State.addr c) = ciphOf m₀ (State.addr c)) :
    WP isa cryptWhole s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ CrMid c st w sp k7 k8 icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h3, h12, h4, h5, hz, hg₁, hk₁⟩ := splitCtr_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h12 h4 h5 hz
  obtain h16 : 16 * nb ≤ n - j := by omega_arith
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  obtain hd₁ : DataW c st w sp k7 k8 s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  refine WP.ite (decide (nb = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega_arith, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega_arith⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    obtain hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega_arith)
    obtain hdj := h.data.sub (j := j) (k := 16 * nb) (by omega_arith) (by omega_arith)
    obtain eD := h.data.ok.addr (j := j) (by omega_arith)
    obtain ⟨s₂, run₂, h0', h2', hg₂, hk₂⟩ := wholeArgs_ok he₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    obtain he₂ : Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide))
      hk₂.sp hk₂.rd hk₂.wr
    obtain eC := L.stA (d := 48) (by decide)
    have hk := he₂.sp
    obtain hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) nb :=
      ctrWhole_mk L he₂ h0' h2' (by rw [hg₂ _ (by decide) (by decide), h3])
        (by rw [hg₂ _ (by decide) (by decide), h12])
        (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr))
    refine WP.mono (ctr_call hcall) fun s₃ g => ?_
    obtain gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem, eC, eD, hk] at gout gctr gframe
    obtain hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := State.addr D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega_arith, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega_arith, ?_, ?_,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, ?_, .inr (by omega_arith), ?_⟩, by omega_arith⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide), h5]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      obtain hj16 : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (ciphOf m₀ (State.addr c)) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        obtain e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega_arith, bytesAt_add, bytesAt_add,
          List.take_left' (length_bytesAt _ _ _), List.take_left' (length_bytesAt _ _ _)] at e
      obtain hjd : bytesAt s₃.mem (State.addr D) j = bytesAt s.mem (State.addr D) j := bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact split_disj (D := State.addr D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega_arith))
        · exact (h.data.take h.le).ok.stk.symm) (by omega_arith)
      exact done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      obtain hdis : ∀ r ∈ [⟨State.addr st + BitVec.ofNat 64 48, 16⟩, ⟨State.addr D + BitVec.ofNat 64 j, 16 * nb⟩,
          below sp],
          (⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        obtain hst := h.data.ok.st; have hW := h.data.ok.w; have hK := h.data.ok.stk
        obtain hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨State.addr D, n⟩ :=
          Offset.sub_base _ (by omega_arith)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← add_ofNat_assoc]
          have := split_disj (D := State.addr D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega_arith)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega_arith] at this
          exact this.symm
        · exact (hK.sub_right hs).symm
      rw [bytesAt_frame gframe hdis (by omega_arith)]
      obtain e := congrArg (List.drop (16 * nb)) h.rest
      obtain e₂ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega_arith, bytesAt_add,
          List.drop_left' (length_bytesAt _ _ _), add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega_arith))⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The keystream block zeroed and the arguments of `vg_sm4_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa tailArgs s = some s' ∧
      s'.mem = Cmac.store4 s.mem (State.addr st + BitVec.ofNat 64 64) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .r3 = st + BitVec.ofNat 32 64 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  obtain w₀ := he.perm.stW (show 64 + 4 ≤ 80 by decide)
  obtain w₁ := he.perm.stW (show 68 + 4 ≤ 80 by decide)
  obtain w₂ := he.perm.stW (show 72 + 4 ≤ 80 by decide)
  obtain w₃ := he.perm.stW (show 76 + 4 ≤ 80 by decide)
  refine ⟨_, by simp only [tailArgs]; arun [h10, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg]
  · intro r a b d e; simp [gpr_setReg, a, b, d, e]
  all_goals rfl

/-- The last bytes' keystream block, from `vg_sm4_ctr32`. -/
structure TailKs (c st w sp k7 k8 : BitVec 32) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (j : Nat) (s₀ s : State) : Prop where
  mid : CrMid c st w sp k7 k8 icb P D n m₀ j s₀
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  ks : blockAt s.mem (State.addr st + BitVec.ofNat 64 64) =
    ciphOf m₀ (State.addr c) (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  frame : Frame [⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]
    s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 icb P D n m₀ j s) (hc : ciphOf s.mem (State.addr c) = ciphOf m₀ (State.addr c)) :
    WP isa (.seq (.block tailArgs) ctrCall) s (TailKs c st w sp k7 k8 icb P D n m₀ j s) := by
  have he := h.env
  obtain ⟨s₂, run₂, hm₂, h0, h2, h3, h12, hg₂, hrd₂, hwr₂, hsp₂⟩ := tailArgs_ok L he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  obtain he₂ : Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  obtain eC := L.stA (d := 48) (by decide)
  obtain eK := L.stA (d := 64) (by decide)
  obtain fz : Frame [⟨State.addr st + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  obtain hKS0 : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 64) = 0 := by
    rw [blockAt, hm₂, store4_zero_bytes]; decide
  obtain hCB : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 48) = blockAt s.mem (State.addr st + BitVec.ofNat 64 48) :=
    blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  obtain hc₂ : ciphOf s₂.mem (State.addr c) = ciphOf m₀ (State.addr c) := by
    rw [ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))), hc]
  obtain hcall : CtrCall s₂ c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) 1 :=
    ctrTail_mk L he₂ h0 h2 h3 h12
  refine WP.mono (ctr_call hcall) fun s₃ g => ?_
  obtain gout := g.out; have gctr := g.ctr; have gframe := g.frame
  simp only [eC, eK, hk] at gout gctr gframe
  rw [blocksAt_one, blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hrd₂], by rw [g.wr, hwr₂]⟩
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s₀ s : State}
    (h : TailKs c st w sp k7 k8 icb P D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop) s
      (CrOut c st w sp k7 k8 icb P D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt32
  obtain hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  obtain hdj := hm.data.sub (j := j) (k := n - j) (by omega_arith) (by omega_arith)
  obtain eD := hm.data.ok.addr (j := j) (by omega_arith)
  have he₃ := h.env
  obtain ⟨s₄, run₄, h1, h2, h3, hg₄, hk₄⟩ : ∃ s₄, runBlock isa
      [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] s = some s₄ ∧
      s₄.gpr .r1 = st + BitVec.ofNat 32 64 ∧ s₄.gpr .r2 = D + BitVec.ofNat 32 j ∧
      s₄.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s.gpr r) ∧ Keeps s s₄ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r10]
    · simp [gpr_setReg, h.r4]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  obtain eK := L.stA (d := 64) (by decide)
  obtain lp : LoopPre s₄ (st + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨h1, h2, h3, by omega_arith, by omega_arith, by rw [L.stN (by decide)]; have := L.sw; omega_arith, hdj.ok.fit, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr, eK]; exact covers_left (he₃.perm.stC (by omega_arith))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · rw [eK]; exact (hdj.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  refine WP.mono (xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [hk₄.mem, eK, eD] at hm₅
  obtain hxl := length_xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j)
  obtain fw : Frame [⟨State.addr D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact writeBytes_frame' _ hxl
  obtain dst := hdj.ok.st; have dw := hdj.ok.w; have dk := hdj.ok.stk
  rw [eD] at dst dw dk
  obtain hd₃ : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
      bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dst.sub_right (Lay.stSub (by decide))
    · exact dw.sub_right (Lay.wSub (by decide))
    · exact dk.symm
  obtain ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) (by rw [length_bytesAt]; omega_arith)
    (by rw [length_bytesAt]; omega_arith)
  rw [length_bytesAt] at ht
  obtain dS : ∀ r ∈ [(⟨State.addr D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨State.addr st + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [lo.other r a b c d e, hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (lo.sp.trans hk₄.sp) (lo.rd.trans hk₄.rd) (lo.wr.trans hk₄.wr), ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega_arith]
    exact (ht hc₀).2.congr (blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    obtain hdone : bytesAt s₅.mem (State.addr D) j = bytesAt s₀.mem (State.addr D) j := by
      obtain hdt := (hm.data.take hm.le).ok
      rw [bytesAt_frame fw (fun r hr => ?_) (by omega_arith), bytesAt_frame h.frame (fun r hr => ?_) (by omega_arith)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
        · exact hdt.stk.symm
      · simp only [List.mem_singleton] at hr; subst hr; exact split_disj hm.le hm.data.ok.lt
    obtain hpiece : bytesAt s₅.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
        xorKs (ciphOf m₀ (State.addr c)) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) := by
      obtain e := bytesAt_writeBytes_self s.mem (State.addr D + BitVec.ofNat 64 j)
        (xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j))
        (by rw [hxl]; omega_arith)
      rw [hxl] at e
      rw [hm₅, e, xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega_arith]
    exact done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega_arith)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 icb P D n m₀ j s) (hj : n - j < 16)
    (hc : ciphOf s.mem (State.addr c) = ciphOf m₀ (State.addr c)) :
    WP isa cryptTail s (CrOut c st w sp k7 k8 icb P D n m₀) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 (by omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ : Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  obtain h₁ : CrMid c st w sp k7 k8 icb P D n m₀ j s₁ :=
    ⟨he₁, h.le, (by rw [hg₁]; exact h.r4), (by rw [hg₁]; exact h.r5),
      h.data.of_eq hrd₁ hwr₁, (fun hc₀ => by rw [hm₁]; exact h.ctr hc₀), (fun hc₀ => by rw [hm₁]; exact h.done hc₀),
      (by rw [hm₁]; exact h.rest), h.whole, (by rw [hm₁]; exact h.frame)⟩
  refine WP.ite (decide (n - j = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega_arith
    subst h0
    exact WP.block_nil ⟨he₁, fun hc₀ => h₁.ctr hc₀, fun hc₀ => h₁.done hc₀, h₁.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (tailKs_ok L h₁ (by rw [hm₁]; exact hc)) fun _ ht => tailXor_ok L ht hj h0)

theorem CrMid.ciph {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : CrMid c st w sp k7 k8 icb P D n m₀ j s) : ciphOf s.mem (State.addr c) = ciphOf m₀ (State.addr c) :=
  ciph_frame h.frame (ctx_crFrame L h.data)

omit L in
theorem CrIn.keep {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : CrIn c st w sp k7 k8 icb P D n s) (hg : s'.gpr = s.gpr) (hk : Keeps s s') : CrIn c st w sp k7 k8 icb P D n s' :=
  ⟨h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr, by rw [hg]; exact h.r4, by rw [hg]; exact h.r5,
    by rw [hg]; exact h.r6, h.data.of_eq hk.rd hk.wr⟩

/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      CrMid c st w sp k7 k8 icb P D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt P (show 16 > 0 by decide); omega_arith)
  obtain h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (P % 16 = 0)) (eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega_arith, by rw [h₂.r4, add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero],
      h₂.data, fun hc₀ => by rw [hm₂]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [hm₂, add_ofNat_zero], .inr (by omega_arith), by rw [hm₂]; exact Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    have := cryptHead_ok L h₂ h0 hP
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : CrIn c st w sp k7 k8 icb P D n s) :
    WP isa crypt s (CrOut c st w sp k7 k8 icb P D n s.mem) := by
  have hn' := h.data.ok.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := cmp0_ok s .r5 h.r5 hn'
  obtain h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h₁.env, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (cryptFill_ok L h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt`

Untrusted: everything here is checked by Lean. Both save our caller's
registers in `scratch` (`W`); `encrypt` XORs the keystream into the data
(`crypt`) and then absorbs the ciphertext into GHASH (`textAbsorb`), and
`decrypt` the other way round (`streamEncrypt_wp`, `streamDecrypt_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ghashInput gctr inc32 j0)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs)

theorem scLay {s₀ : State} (h : streamCryptPre s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp := by
  obtain ⟨-, -, dcs, -, dcW, -, dsW, -, -, -, -, bc, bs, -, bW, fc, fs, -, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SC1 (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp (s₀.gpr .r7) (s₀.gpr .r2) s₁
  args : ArgsKeep 5 s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ 4) s₀
  frame : Frame [savedR (arg s₀ 4)] s₀.mem s₁.mem

theorem sc_argsW {s₀ : State} (h : streamCryptPre s₀) : ∀ r ∈ [savedR (arg s₀ 4)], (args s₀ 5).Disjoint r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm

theorem sc1_wp {s₀ : State} (h : streamCryptPre s₀) {Q : State → Prop} (k : ∀ s₁, SC1 s₀ s₁ → Q s₁) :
    WP isa (.block cryptEntry) s₀ Q := by
  obtain hA := sc_argsW h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fW, -, spf⟩ := h
  obtain hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) := by
    rw [hrd]; exact covers_of_mem (by simp)
  obtain hS : Covers [⟨State.addr (s₀.gpr .r1), 80⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain hW : Covers [⟨State.addr (arg s₀ 4), 768⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  obtain ha : ∀ i < 5, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * i))) 4 :=
    fun i hi => arg_in (n := 5) hi spf (by rw [hrd]; simp)
  refine entry_ok (off := 16) (by decide) (ha 4 (by decide)) fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  obtain hk : ArgsKeep 5 s₀ s₁ := (ArgsKeep.refl 5 s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem textArgs_run {s₀ s : State} (hk : ArgsKeep 5 s₀ s) (hf : s₀.sp.toNat + 4 * 5 ≤ 2 ^ 32)
    (hin : args s₀ 5 ∈ s₀.rd) :
    ∃ s', runBlock isa textArgs s = some s' ∧
      s'.gpr .r4 = arg s₀ 2 ∧ s'.gpr .r5 = arg s₀ 3 ∧ s'.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 0).toNat % 16) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i4, v4⟩ := hk.at hf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i5, v5⟩ := hk.at hf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨i2, v2⟩ := hk.at hf hin 0 (by decide) (show 4 * 0 = 0 from rfl)
  refine ⟨_, by simp only [textArgs]; arun [i4, v4, i5, v5, i2, v2], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v4]
  · simp [gpr_setReg, v5]
  · simp only [gpr_setReg, ite_true, v2, and15]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  · exact ⟨rfl, rfl, rfl, rfl⟩

section
variable {s₀ : State} (h : streamCryptPre s₀)
include h

/-- The data, as `crypt` needs it. -/
theorem sc_dataW {k7 : BitVec 32} {s : State} (hk : ArgsKeep 5 s₀ s) :
    DataW (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r2) s (arg s₀ 2) (arg s₀ 3).toNat := by
  obtain ⟨hrd, hwr, -, dcD, -, dsD, -, -, dDW, -, -, -, -, bD, -, -, -, fD, -, -, -⟩ := h
  obtain hD : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] s.wr := by
    rw [hk.wr, hwr]; exact covers_of_mem (by simp)
  exact ⟨⟨covers_left hD, (arg s₀ 3).isLt, fD, dsD.symm, dDW, bD⟩, hD, dcD⟩

/-- The input of `crypt`, for `P` bytes of text so far. -/
theorem sc_crIn {k7 : BitVec 32} {s : State} (he : Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r2) s)
    (hk : ArgsKeep 5 s₀ s) (h4 : s.gpr .r4 = arg s₀ 2) (h5 : s.gpr .r5 = arg s₀ 3)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 0).toNat % 16)) (icb : Block) {P : Nat}
    (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = P) :
    CrIn (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp k7 (s₀.gpr .r2) icb P (arg s₀ 2) (arg s₀ 3).toNat s :=
  ⟨he, h4, by rw [h5]; simp, by rw [h6, lowTo_mod16 hP], sc_dataW h hk⟩

/-- The stack arguments are apart from what the pieces write. -/
theorem sc_argsCr : ∀ r ∈ crFrame (s₀.gpr .r1) (arg s₀ 4) s₀.sp (arg s₀ 2) (arg s₀ 3).toNat, (args s₀ 5).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, dsA, -, dDA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dDA.symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem sc_argsTa : ∀ r ∈ taFrame (s₀.gpr .r1) (arg s₀ 4) s₀.sp, (args s₀ 5).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, dsA, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dsA.sub_left (Lay.stSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

end

section
variable {c st w sp : BitVec 32} (L : Lay c st w sp)
include L

theorem stp_crFrame {k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n)
    {d k : Nat} (h1 : d + k ≤ 48) :
    ∀ r ∈ crFrame st w sp D n, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.st.sub_right (Lay.stSub (by omega_arith))).symm
  · exact Lay.st_st (.inl h1) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega_arith)).symm

theorem stp_taFrame {d k : Nat} (hd : d + k ≤ 16 ∨ 48 ≤ d ∧ d + k ≤ 80) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
  · exact (L.stk_st (by omega_arith)).symm

theorem stp_saved {d k : Nat} (h1 : d + k ≤ 80) :
    ∀ r ∈ [savedR w], (⟨State.addr st + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.st_w h1 (.inr ⟨by decide, by decide⟩)

theorem ctx_saved : ∀ r ∈ [savedR w], (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact L.cw'.sub_right (Lay.wSub (by decide))

theorem ctx_taFrame : ∀ r ∈ taFrame st w sp, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem data_taFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ taFrame st w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

omit L in
theorem data_saved {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk st w sp s D n) :
    ∀ r ∈ [savedR w], (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact hd.w.sub_right (Lay.wSub (by decide))

theorem saved_taFrame : ∀ r ∈ taFrame st w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
/-- `ciphOf` is `ctxCiph`, and a frame apart from the context keeps it. -/
theorem ciph_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) :
    ciphOf m' (State.addr c) = ctxCiph m (State.addr c) := ciph_frame hf hd

omit L in
theorem ctxH_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) :
    blockAt m' (State.addr c + BitVec.ofNat 64 240) = ctxH m (State.addr c) := by
  rw [ctxH_eq, blockAt_frame hf (fun r hr => (hd r hr).sub_left (Lay.ctxSub (by decide)))]

end

/-- What `encrypt` (or `decrypt`) does, for the counter block `icb`, the
additional data `a` and the text `ct` so far (only their lengths matter to
the code). -/
structure EncOut (s₀ : State) (icb : Block) (a ct : List Byte) (dec : Bool) (s : State) : Prop where
  ctr : Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length →
    Ctr s.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb (ct.length + (arg s₀ 3).toNat)
  out : Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length →
    bytesAt s.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length
        (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)
  abs : Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64)
      (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length →
    Absorbed s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) →
    Absorbed s.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 16) (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghashInput a (ct ++ if dec then bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat else
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)))
  j : blockAt s.mem (State.addr (s₀.gpr .r1)) = blockAt s₀.mem (State.addr (s₀.gpr .r1))

theorem enc_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .r2).toNat % 16) (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct false s' := by
  obtain L := scLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain hin : args s₀ 5 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (WP.block_append (sc1_wp h fun s₁ h1 => ?_))
  obtain ⟨s₂, run₂, h4, h5, h6, hg₂, hK₂⟩ := textArgs_run h1.args spf hin
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hK₂.sp hK₂.rd hK₂.wr
  obtain hk₂ := h1.args.of_eq hK₂.mem hK₂.sp hK₂.rd hK₂.wr
  obtain ci := sc_crIn h he₂ hk₂ h4 h5 h6 icb hP
  have hd₂ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₃ hh => ?_)
  obtain ⟨co, rd₃, wr₃, sp₃⟩ := hh
  obtain hk₃ := hk₂.frame spf co.frame (sc_argsCr h) sp₃ rd₃ wr₃
  obtain hd₃ := (sc_dataW (k7 := s₀.gpr .r7) h hk₃).ok
  obtain f₂ : Frame [savedR (arg s₀ 4)] s₀.mem s₂.mem := by rw [hK₂.mem]; exact h1.frame
  obtain hH₃ : blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame co.frame (fun r hr => (ctx_crFrame L hd₂ r hr).sub_left (Lay.ctxSub (by decide))),
      ctxH_keep f₂ (ctx_saved L)]
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L co.env hk₃ spf hin (sc_argsTa h) hH₃ hd₃ ha hP))
    fun s₄ hh => ?_)
  obtain ⟨ta, rd₄, wr₄, sp₄⟩ := hh
  obtain sv₄ : SavedAt s₄.mem (arg s₀ 4) s₀ :=
    (((hK₂.mem ▸ h1.saved : SavedAt s₂.mem (arg s₀ 4) s₀)).frame co.frame (saved_crFrame L hd₂)).frame ta.frame
      (saved_taFrame L)
  refine WP.mono (restore_ok ta.env.r11 fW (covers_left ta.env.perm.w) sv₄ ta.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  obtain hc : ciphOf s₂.mem (State.addr (s₀.gpr .r0)) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) :=
    ciph_keep f₂ (ctx_saved L)
  obtain ctr₂ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb P →
      Ctr s₂.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64) (ciphOf s₂.mem (State.addr (s₀.gpr .r0))) icb P :=
    fun hc₀ => by
      rw [hc]
      exact hc₀.congr (blockAt_frame f₂ (stp_saved L (by decide))) (blockAt_frame f₂ (stp_saved L (by decide)))
  obtain dat₂ : bytesAt s₂.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat :=
    bytesAt_frame f₂ (data_saved hd₂.ok) (by have := hd₂.ok.lt; omega_arith)
  obtain out₃ : Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length →
      bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
        xorKs (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb ct.length
          (bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat) := fun hc₀ => by
    rw [co.out (ctr₂ hc₀), hc, dat₂]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₂ hc₀)
    rw [hc] at this
    exact this.congr (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
      (blockAt_frame ta.frame (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  · rw [hm, bytesAt_frame ta.frame (data_taFrame hd₃) (by have := hd₃.lt; omega_arith)]
    exact out₃ hc₀
  · rw [hm]
    obtain hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    obtain hab₃ : Absorbed s₃.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 16)
        (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 32) (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (ghashInput a ct) :=
      (hab.congr (blockAt_frame f₂ (stp_saved L (by decide)))
        (bytesAt_frame f₂ (stp_saved L (by omega_arith)) (by omega_arith))).congr
        (blockAt_frame co.frame (stp_crFrame L hd₂ (by decide)))
        (bytesAt_frame co.frame (stp_crFrame L hd₂ (by omega_arith)) (by omega_arith))
    have := ta.abs hab₃
    rw [out₃ hc₀] at this
    exact this
  · rw [hm, blockAt_frame ta.frame (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame co.frame (by simpa using stp_crFrame L hd₂ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₂ (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem dec_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamCryptPre s₀) (icb : Block) {a ct : List Byte}
    (ha : a.length % 16 = (s₀.gpr .r2).toNat % 16) (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ EncOut s₀ icb a ct true s' := by
  obtain L := scLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have fW := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain hin : args s₀ 5 ∈ s₀.rd := by rw [h.1]; simp
  refine WP.seq (sc1_wp h fun s₁ h1 => ?_)
  obtain hd₁ := (sc_dataW (k7 := s₀.gpr .r7) h h1.args).ok
  obtain hH₁ : blockAt s₁.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) :=
    ctxH_keep h1.frame (ctx_saved L)
  refine WP.seq (WP.mono (WP.with_rdwr (textAbsorb_ok L h1.env h1.args spf hin (sc_argsTa h) hH₁ hd₁ ha hP))
    fun s₂ hh => ?_)
  obtain ⟨ta, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨s₃, run₃, h4, h5, h6, hg₃, hK₃⟩ := textArgs_run ta.args spf hin
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := ta.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide) (by decide)) hK₃.sp hK₃.rd hK₃.wr
  obtain hk₃ := ta.args.of_eq hK₃.mem hK₃.sp hK₃.rd hK₃.wr
  obtain ci := sc_crIn h he₃ hk₃ h4 h5 h6 icb hP
  have hd₃ := ci.data
  refine WP.seq (WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₄ hh => ?_)
  obtain ⟨co, rd₄, wr₄, sp₄⟩ := hh
  obtain f₃ : Frame (taFrame (s₀.gpr .r1) (arg s₀ 4) s₀.sp) s₁.mem s₃.mem := by rw [hK₃.mem]; exact ta.frame
  obtain sv₄ : SavedAt s₄.mem (arg s₀ 4) s₀ :=
    ((h1.saved.frame f₃ (saved_taFrame L))).frame co.frame (saved_crFrame L hd₃)
  refine WP.mono (restore_ok co.env.r11 fW (covers_left co.env.perm.w) sv₄ co.env.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm : s'.mem = s₄.mem := hh.2.1
  obtain hc : ciphOf s₃.mem (State.addr (s₀.gpr .r0)) = ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [ciph_keep f₃ (ctx_taFrame L)]; exact ciph_keep h1.frame (ctx_saved L)
  obtain ctr₃ : ∀ {P : Nat}, Ctr s₀.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) icb P →
      Ctr s₃.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 48)
      (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 64) (ciphOf s₃.mem (State.addr (s₀.gpr .r0))) icb P :=
    fun hc₀ => by
      rw [hc]
      exact (hc₀.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (blockAt_frame h1.frame (stp_saved L (by decide)))).congr
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
        (blockAt_frame f₃ (stp_taFrame L (.inr ⟨by decide, by decide⟩)))
  obtain dat₁ : bytesAt s₁.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat :=
    bytesAt_frame h1.frame (data_saved hd₁) (by have := hd₁.lt; omega_arith)
  obtain dat₃ : bytesAt s₃.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
    rw [bytesAt_frame f₃ (data_taFrame hd₁) (by have := hd₁.lt; omega_arith), dat₁]
  refine ⟨fun hc₀ => ?_, fun hc₀ => ?_, fun hc₀ hab => ?_, ?_⟩
  · rw [hm]
    have := co.ctr (ctr₃ hc₀)
    rwa [hc] at this
  · rw [hm, co.out (ctr₃ hc₀), hc, dat₃]
  · rw [hm]
    obtain hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
    obtain hab₂ := ta.abs ((hab.congr (blockAt_frame h1.frame (stp_saved L (by decide)))
        (bytesAt_frame h1.frame (stp_saved L (by omega_arith)) (by omega_arith))))
    rw [dat₁] at hab₂
    rw [← hK₃.mem] at hab₂
    obtain hb' := Nat.mod_lt (ghashInput a (ct ++ bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat)).length
      (show 16 > 0 by decide)
    exact hab₂.congr (blockAt_frame co.frame (stp_crFrame L hd₃ (by decide)))
      (bytesAt_frame co.frame (stp_crFrame L hd₃ (by omega_arith)) (by omega_arith))
  · rw [hm, blockAt_frame co.frame (by simpa using stp_crFrame L hd₃ (d := 0) (k := 16) (by decide)),
      blockAt_frame f₃ (by simpa using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame h1.frame (by simpa using stp_saved L (d := 0) (k := 16) (by decide))]

theorem streamEncrypt_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamEncryptArm.pre s₀) :
    WP isa streamEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamEncryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  obtain h₀ := enc_run h' 0 (a := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 1 ++ arg s₀ 0).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0))
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph hh i.1 i.2.1 (gctr ciph (inc32 (j0 hh i.1)) i.2.2) ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 0).toNat = i.2.2.length)
    fun i hi => enc_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1)
      (ct := gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) i.2.2)
      (low_mod16 hi.2.1).symm (by rw [Proof.Gcm.length_gctr]; exact hi.2.2))
    fun s' hh => ⟨hh.1, fun iv a p hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, p⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  obtain hl' : (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
      (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv)) p).length = p.length := Proof.Gcm.length_gctr _ _ _
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [Bool.false_eq_true, ite_false] at eo₃
  rw [hl'] at eo₁ eo₂ eo₃
  rw [← Proof.Gcm.gctr_append] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [Proof.Gcm.length_gctr, List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' hl']

theorem streamDecrypt_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamDecryptArm.pre s₀) :
    WP isa streamDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ streamDecryptArm.post s₀ s' := by
  have h' : streamCryptPre s₀ := h
  obtain h₀ := dec_run h' 0 (a := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 1 ++ arg s₀ 0).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0))
      let hh := ctxH s₀.mem (State.addr (s₀.gpr .r0))
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) ciph hh i.1 i.2.1 i.2.2 ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 0).toNat = i.2.2.length)
    fun i hi => dec_run h' (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1)) (a := i.2.1) (ct := i.2.2)
      (low_mod16 hi.2.1).symm hi.2.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => ?_⟩
  obtain ⟨-, eo⟩ := hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, hct⟩ := hs
  simp only [ofNat_lit] at hab hct
  obtain eo₁ := eo.ctr hct
  obtain eo₂ := eo.out hct
  obtain eo₃ := eo.abs hct hab
  simp only [ite_true] at eo₃
  refine ⟨?_, ?_⟩
  · rw [Proof.Gcm.streamRepr_iff]
    simp only [ofNat_lit]
    refine ⟨eo.j.trans hj, eo₃, ?_⟩
    rw [List.length_append, length_bytesAt]; exact eo₁
  · rw [eo₂, Proof.Gcm.gctr_append, List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_finish`

Untrusted: everything here is checked by Lean. `stream_finish` saves our
caller's registers in `work` (`W`), writes the tag to its first 16 bytes
with `finTag` and copies it to `tag` (`tagOut_ok`, `streamFinish_wp`). The
entry is shared with `stream_verify` (`fin1_wp`, for `n` words of stack
arguments, `work` the `wi`-th).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ghashInput fullTag)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (store4)

theorem lensBlock_mod (L c : Nat) : lensBlock (L % 2 ^ 64) c = lensBlock L c := by
  simp only [lensBlock]
  rw [← Proof.Gcm.be64_mod (8 * (L % 2 ^ 64)), ← Proof.Gcm.be64_mod (8 * L)]
  congr 2; omega_using []

theorem toNat_of_eq {x : BitVec 64} {L : Nat} (h : x = BitVec.ofNat 64 L) : x.toNat = L % 2 ^ 64 := by
  rw [h, BitVec.toNat_ofNat]

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- `tagOut ta`: the tag at `W` copied to `T`, the stack argument at `[sp + ta]`. -/
theorem tagOut_ok {s : State} (he : Env c st w sp k7 k8 s) {ta : Nat} (hta : ta = 8 ∨ ta = 12) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 ta)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 ta)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa (tagOut ta) s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 768 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega_using [hTf, hd])
  have r₀ := he.perm.wR (show 0 + 4 ≤ 768 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 768 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 768 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 768 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa (tagOut ta) s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [tagOut]; rcases hta with rfl | rfl <;> arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Cmac.frame_store4 _ _ _ _ _, hg, hk.1,
    hk.2.1, hk.2.2⟩

end

section
variable {n wi : Nat}

theorem finLay {s₀ : State} (h : finPre n wi s₀) : Lay (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, dcs, dcW, dsW, -, -, bc, bs, bW, fc, fs, fW, sp8, -⟩ := h
  exact Lay.of fc fs fW sp8 dcs dcW dsW bc bs bW

/-- After the entry, from `s₀`. -/
structure SF1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ wi) s₀.sp (s₀.gpr .r3) (s₀.gpr .r2) s₁
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ wi) s₀
  frame : Frame [savedR (arg s₀ wi)] s₀.mem s₁.mem

theorem fin1_wp {s₀ : State} (h : finPre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, SF1 n wi s₀ s₁ → Q s₁) : WP isa (.block (finEntry (4 * wi))) s₀ Q := by
  obtain ⟨⟨hc, hin⟩, ⟨hs, hw, -⟩, -, -, -, -, dWA, -, -, -, -, -, fW, -, spf⟩ := h
  have hA : ∀ r ∈ [savedR (arg s₀ wi)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  have hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  have hS : Covers [⟨State.addr (s₀.gpr .r1), 80⟩] s₀.wr := covers_of_mem hs
  have hW : Covers [⟨State.addr (arg s₀ wi), 768⟩] s₀.wr := covers_of_mem hw
  have ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 :=
    arg_in (n := n) hn spf hin
  refine entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  have hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

theorem fin_argsTag {s₀ : State} (h : finPre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ tagFrame (s₀.gpr .r1) (arg s₀ wi) s₀.sp o, (args s₀ n).Disjoint r := by
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, dsA, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (dsA.sub_left (Region.sub_prefix (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega_using [ho]))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- The tag, from the entry. -/
theorem fin_tag [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₁ : State} (h : finPre n wi s₀) (hn : 2 ≤ n) (h1 : SF1 n wi s₀ s₁) {o : Nat}
    (ho : o = 0 ∨ o = 112) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .r2).toNat % 16)
    (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa (finTag o) s₁ (FinOut (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ wi) s₀.sp (s₀.gpr .r3) (s₀.gpr .r2) n s₀ o
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct s₁.mem) := by
  have L := finLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact finTag_ok L hn ho h1.env h1.args spf h.1.2 (fin_argsTag h ho)
    (ctxH_keep h1.frame (ctx_saved L)) ha hP

/-- The tag, for a state that represents `a` and `ct`, from a memory `m₀` that
differs from the entry's only apart from the context and the state. -/
theorem fin_out {s₀ s : State} {m₀ : Mem} {rs : List Region} (hf₀ : Frame rs s₀.mem m₀)
    (hdc : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r)
    (hds : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r1), 80⟩ : Region).Disjoint r) {o : Nat} {iv a ct : List Byte}
    (hf : FinOut (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ wi) s₀.sp (s₀.gpr .r3) (s₀.gpr .r2) n s₀ o
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) a ct m₀ s)
    (hs : StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct) (hl : (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 a.length) :
    bytesAt s.mem (State.addr (arg s₀ wi) + BitVec.ofNat 64 o) 16 =
      fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
        iv a ct := by
  rw [Proof.Gcm.streamRepr_iff] at hs
  obtain ⟨hj, hab, -⟩ := hs
  simp only [ofNat_lit] at hab hj
  have hb := Nat.mod_lt (ghashInput a ct).length (show 16 > 0 by decide)
  have dS : ∀ {d k : Nat}, d + k ≤ 80 → ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd r hr => (hds r hr).sub_left (Lay.stSub hd)
  rw [hf.out (hab.congr (blockAt_frame hf₀ (dS (by decide)))
      (bytesAt_frame hf₀ (dS (by omega_using [])) (by omega_using []))),
    ciph_keep hf₀ hdc,
    blockAt_frame hf₀ (by simpa using dS (d := 0) (k := 16) (by decide)), hj,
    toNat_of_eq hl, lensBlock_mod, Proof.Gcm.fullTag_eq]

end

theorem streamFinish_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamFinishArm.pre s₀) :
    WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ streamFinishArm.post s₀ s' := by
  have h' : finPre 4 3 s₀ := streamFinishPreArm.fin h
  have L := finLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hrd, hwr, -, -, -, -, -, -, tW, tA, -, -, -, -, -, -, -, fT, -⟩ := h
  have hin : args s₀ 4 ∈ s₀.rd := h'.1.2
  have hTw : Covers [⟨State.addr (arg s₀ 2), 16⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have dW : ∀ {d k : Nat}, d + k ≤ 768 → (⟨State.addr (arg s₀ 2), 16⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 3) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  have run : ∀ {a ct : List Byte}, a.length % 16 = (s₀.gpr .r2).toNat % 16 → (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length →
      WP isa streamFinish s₀ fun s' => abiPreserved s₀ s' ∧ ∀ iv,
        StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 a.length →
        bytesAt s'.mem (State.addr (arg s₀ 2)) 16 =
          fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
            (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := fun ha hP =>
    WP.seq (fin1_wp (wi := 3) h' (by decide) (by decide) fun s₁ h1 =>
      WP.seq (WP.mono (fin_tag h' (by decide) h1 (.inl rfl) ha hP) fun s₂ hf => by
        obtain ⟨k7, he⟩ := hf.env
        obtain ⟨i4, v4⟩ := hf.args.at spf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
        obtain ⟨s₃, run₃, hb₃, hf₃, g₃, rd₃, wr₃, sp₃⟩ := tagOut_ok L he (.inl rfl) i4 v4
          (by rw [hf.args.wr]; exact hTw) fT (by simpa using dW (d := 0) (k := 16) (by decide))
        refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
        have he₃ := he.keep (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
        have sv₂ := h1.saved.frame hf.frame (saved_tagFrame L (.inl rfl))
        exact WP.mono (restore_ok he₃.r11 fW (covers_left he₃.perm.w)
          (sv₂.frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact (dW (by decide)).symm)) he₃.sp)
          fun s' hh => ⟨hh.1, fun iv hs hl => by
            have := fin_out (n := 4) (wi := 3) h1.frame (ctx_saved L) (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)) hf hs hl
            rw [add_ofNat_zero] at this
            rw [hh.2.1, hb₃, this]⟩))
  have h₀ := run (a := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 1 ++ arg s₀ 0).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte × List Byte =>
      StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
          (ctxH s₀.mem (State.addr (s₀.gpr .r0))) i.1 i.2.1 i.2.2 ∧
        (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.2.1.length ∧ (arg64 s₀ 0).toNat = i.2.2.length)
    fun i hi => WP.mono (run (a := i.2.1) (ct := i.2.2) (low_mod16 hi.2.1).symm hi.2.2)
      fun s' hh => hh.2 i.1 hi.1 hi.2.1)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨iv, a, c⟩ ⟨hs, hl, hp⟩⟩

end VG.Proof.Sm4Gcm.Arm
