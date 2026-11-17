module

public import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Ed448.Arm.SignCached
public import VerifiedGarbage.Proof.Ed448.Arm.BaseLit
public import VerifiedGarbage.Proof.Ed448.Arm.ScalarLit
public import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Layout
public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Wrap
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.BlocksCT
import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Calls
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.EntryCT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
public import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Hash
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ed448.Arm.SignCached.CT`, which only this module used -/

section

/-!
# Ed448 signing with a cached public key on ARMv7: constant time

As `vg_ed448_verify`'s on this target: two runs from the same pointers,
lengths and `sp` set up the same arguments for every call, each callee is
constant time under its own contract, and the blocks between the calls
address memory only through `sp`, `r12` and `scratch`
(`Proof/Ed448/Arm/Shake/CT.lean`); the positions the absorptions return
depend only on the lengths.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.FR Whole.rel_wp Whole.CallReady Whole.block_cons_ct Whole.block_nil_ct Whole.Within
  Whole.call_ok Whole.zeroWords_ct)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs Two Slots valid_const valid_frame frame_within DataOk
  hdr_len)
open VG.Proof.Ed448.Arm (scalarReduceLocal scalarReduce_ok scalarReduce_ct scalarBaseLocal scalarBase_ok
  scalarBase_ct scalarMulAddLocal scalarMulAdd_ok scalarMulAdd_ct)
open VG.Proof.Ed448 (BaseCombOk)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hashes -/

theorem seed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) seedHash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  obtain ⟨cs, ds⟩ := hL.input_data (R := L.SEED) (D := ⟨State.addr L.seed, 57⟩) (by simp [Lay.inputs])
    ⟨0, (BitVec.add_zero _).symm, by simp⟩
  obtain e1 : argVal L.E L.value (.caller 1 0) = L.seed := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  obtain a := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) (src := .caller 1 0) (len := .const 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by rw [e1, e57]; exact cs) (by rw [e1, e57]; exact ds.kwr)
    (by rw [e1, e57]; exact hL.ne)
  exact (hk.zeroState_ct ha hb (scr_at L)).seq (a.seq ((hk.padStep_ct ha hb (scr_at L) _
    (Nat.mod_lt _ (by decide))).seq (hk.sqzStep_ct ha hb (scr_at L) (by decide) (by decide))))

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) prune (fun a b => a.sp = b.sp) := by
  unfold prune
  refine RelCT.seq (M := isa) (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) ?_
    ((Shake.r12_ct Impl.Ed448.Arm.PublicKey.pruneOps (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
  · refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ?_) Whole.block_nil_ct
    simp only [exec, S, show 122 < 256 from by decide, ite_true, Option.some.injEq] at ea eb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 122) hp⟩
  · intro i hi a b h
    simp only [Impl.Ed448.Arm.PublicKey.pruneOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]

theorem prune_ct (hL : L.Ok) : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) prune (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- An absorption of input data. -/
theorem input_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : Shake.valid 12 src) (vl : Shake.valid 12 len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argVal L.E L.value src), (argVal L.E L.value len).toNat⟩ R)
    (hfit : (argVal L.E L.value src).toNat + (argVal L.E L.value len).toNat ≤ 2 ^ 32) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC src len))
      (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value len).toNat) % 136)) :=
  let h := hL.input_data hR hw
  hL.kit.next_ct ha hb (scr_at L) P hP vs vl h.1 h.2.kwr hfit

/-- An absorption of the frame's bytes at `d`. -/
theorem local_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (P : Nat) (hP : P < 136)
    {d k : Nat} (h8 : 8 ≤ d) (hd : d + k ≤ 248) (hk : k < 65536) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC (.frame d) (.const k)))
      (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value (.const k)).toNat) % 136)) := by
  obtain hkn : (argVal L.E L.value (.const k)).toNat = k := by
    simp only [argVal, BitVec.toNat_ofNat]; omega_using [hd]
  have hd' : argVal L.E L.value (.frame d) = L.E + BitVec.ofNat 32 d := rfl
  exact hL.kit.next_ct ha hb (scr_at L) P hP (valid_frame (by omega_using [hd])) (valid_const hk)
    (by rw [hd', hkn, hL.kit.frame_addr (by omega_using [hd])]; exact .inl (frame_within _ hd))
    (by rw [hd', hkn, hL.kit.frame_addr (by omega_using [hd])]; exact (hL.away_fr h8 hd).kwr)
    (by rw [hd', hkn]; exact hL.kit.frame_fit hd)

theorem hdrAbs_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs SC (.frame HDR) (.const 10)))
      (T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((0 + (argVal L.E L.value (.const 10)).toNat) % 136)) := by
  have hd' : argVal L.E L.value (.frame HDR) = L.E + BitVec.ofNat 32 HDR := rfl
  have hkn : (argVal L.E L.value (.const 10)).toNat = 10 := rfl
  exact hL.kit.first_ct ha hb (scr_at L) (valid_frame (by decide)) (valid_const (by decide))
    (by rw [hd', hkn, hL.kit.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hd', hkn, hL.kit.frame_addr (by decide)]; exact hL.away_hdr.kwr)
    (by rw [hd', hkn]; exact hL.kit.frame_fit (by decide))

theorem nonce_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) nonceHash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  obtain x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  obtain x3 := local_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (d := K) (k := 57)
    (by decide) (by decide) (by decide)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  obtain x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := LEN) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact hL.nm)
  let P4 : Nat := (P3 + (argVal L.E L.value LEN).toNat) % 136
  exact (hk.zeroState_ct ha hb (scr_at L)).seq ((hdrAbs_ct hL ha hb).seq (x2.seq (x3.seq (x4.seq
    ((hk.padStep_ct ha hb (scr_at L) P4 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (scr_at L) (by decide) (by decide)))))))

theorem chal_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) chalHash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  obtain x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  obtain e0 : argVal L.E L.value (.caller 0 0) = L.out := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  obtain x3 := hk.next_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) P2 (Nat.mod_lt _ (by decide))
    (src := .caller 0 0) (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide))
    (by rw [e0, e57]; exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), r0_within L⟩)
    (by rw [e0, e57]; exact hL.away_r0.kwr) (by rw [e0, e57]; have := hL.no; omega_using [this])
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  obtain x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 2 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega_using [this])
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  obtain x5 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := LEN) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argVal L.E L.value LEN).toNat) % 136
  exact (hk.zeroState_ct ha hb (scr_at L)).seq ((hdrAbs_ct hL ha hb).seq (x2.seq (x3.seq (x4.seq (x5.seq
    ((hk.padStep_ct ha hb (scr_at L) P5 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (scr_at L) (by decide) (by decide))))))))

/-! ## The scalar calls -/

/-- A call's arguments, from the slots the set-up gives them. -/
theorem slot_reg {args : List (Reg × Value)} {stk : List Value} {s : State} (h : Slots L.E L.value args stk s)
    {r : Reg} {v : Value} (hm : (r, v) ∈ args) : s.gpr r = argVal L.E L.value v := h.1 _ hm

theorem reduceR_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 57), (.r1, .frame HASH), (.r2, .caller SC 0)]
  obtain get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L (L.out + BitVec.ofNat 32 57) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    obtain h0 := slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    obtain h1 := slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    obtain h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  obtain hO : Whole.Within (L.ob 57 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.ob 57 57) R :=
    .inr ⟨L.OUT, out_in L, Lay.Ok.ob_within (by decide)⟩
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[L.fr HASH 114], [L.ob 57 57, L.SCR],
      reduce_pre hL (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide))
        (hL.ob_stk (by decide) (by decide)) (hL.ob_scr (by decide)) (get t h),
      reduce_covers hO, reduce_writes hO⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .caller 0 57) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact WP.mono (reduce_call hc hL (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide))
      (hL.ob_stk (by decide) (by decide)) (hL.ob_scr (by decide)) hO (get t hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem reduceK_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, .caller SC 0)]
  obtain get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L (L.E + BitVec.ofNat 32 K) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    obtain h0 := slot_reg hs (r := .r0) (v := .frame K) (by simp [args])
    obtain h1 := slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    obtain h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  obtain hO : Whole.Within (L.fr K 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.fr K 57) R :=
    .inl (frame_within _ (by decide))
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨valid_frame (by decide), valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[L.fr HASH 114], [L.fr K 57, L.SCR],
      reduce_pre hL (by rw [hk.frame_addr (by decide)]) (hk.frame_fit (by decide))
        (fr_fr (by decide) (by decide) (by decide)) (hk.stack_scr (by decide)) (get t h),
      reduce_covers hO, reduce_writes hO⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .frame K) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact WP.mono (reduce_call hc hL (by rw [hk.frame_addr (by decide)]) (hk.frame_fit (by decide))
      (fr_fr (by decide) (by decide) (by decide)) (hk.stack_scr (by decide)) hO (get t hs))
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem base_ct (hl : BaseCombOk) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)]
  obtain get : ∀ t, Slots L.E L.value args [] t → BaseArgs L t := by
    intro t hs
    obtain h0 := slot_reg hs (r := .r0) (v := .caller 0 0) (by simp [args])
    obtain h1 := slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    obtain h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct (scalarBase_ok hl) scalarBase_ct
    (fun t _ h => ⟨[L.ob 57 57], [L.R0, L.SCR], base_pre hL (get t h), base_covers L, base_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hg (.r0, .caller 0 0) (by simp [args]), hg (.r1, .caller 0 57) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args]), hsp⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc (scalarBase_ok hl) base_noFrames (base_pre hL (get t hs)) (base_covers L)
      (base_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem mulAdd_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.Arm.scalarMulAdd)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 57), (.r1, .caller 0 57), (.r2, .frame K), (.r3, .frame S)]
  obtain get : ∀ t, Slots L.E L.value args [.caller SC 0] t → MulArgs L t := by
    intro t hs
    obtain h0 := slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    obtain h1 := slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    obtain h2 := slot_reg hs (r := .r2) (v := .frame K) (by simp [args])
    obtain h3 := slot_reg hs (r := .r3) (v := .frame S) (by simp [args])
    obtain a0 := hs.2 0 (by simp)
    simp only [argVal, Lay.value, SC, BitVec.add_zero, List.getElem_cons_zero] at h0 h1 h2 h3 a0
    exact ⟨h0, h1, h2, h3, a0⟩
  refine (hk.setup_ct ha hb args [.caller SC 0] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, valid_frame (by decide), valid_frame (by decide),
          fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, fun _ h => nomatch h⟩)).seq ?_
  apply Shake.Kit.call_ct scalarMulAdd_ok scalarMulAdd_ct
    (fun t he h => ⟨mulRd L, [L.ob 57 57, L.SCR], mul_pre hL he (get t h), mul_covers L, mul_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 0 57) (by simp [args]), hg (.r1, .caller 0 57) (by simp [args]),
      hg (.r2, .frame K) (by simp [args]), hg (.r3, .frame S) (by simp [args]), ht 0 (by simp)⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarMulAdd_ok mulAdd_noFrames (mul_pre hL hc.sp (get t hs)) (mul_covers L)
      (mul_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 2 60).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-! ## The body -/

theorem body_ct (hl : BaseCombOk) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) body (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  obtain h : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt 4 HDR)) (T2 L g₁ g₂ m₁ m₂ fun _ => True) :=
    (hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 4) (off := HDR) (by decide) hL.cl (by decide)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
  exact h.seq ((seed_ct hL ha hb).seq ((prune_ct hL).seq ((nonce_ct hL ha hb).seq ((reduceR_ct hL ha hb).seq
    ((base_ct hl hL ha hb).seq ((chal_ct hL ha hb).seq ((reduceK_ct hL ha hb).seq
      ((mulAdd_ct hL ha hb).seq (wipe_ct hL)))))))))

end VG.Proof.Ed448.Arm.SignCached

end

end

/-! ### `Ed448.Arm.SignCached.Body`, which only this module used -/

section

/-!
# Ed448 signing with a cached public key on ARMv7: the body

`body_ok`: the steps (`Hash.lean`, `Calls.lean`) in order, each keeping
what the later ones read (the header of `dom4`, `s`, the prefix, `r` and
`R`), leave `Spec.Ed448.sign` in `out` (`Proof.Ed448.sign_pipeline`), given
the public key of the private key.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs hdrBytes frame_bytes)
open VG.Proof.Ed448 (BaseCombOk)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The two halves of a 114-byte region. -/
theorem bytes_halves (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 114 = Spec.Ed448.bytesAt m p 57 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  simp only [Proof.Ed448.bytesAt_eq]
  exact Proof.X25519.bytesAt_add m p 57 57

theorem drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [bytes_halves]
  exact List.drop_left' (by simp [Spec.Ed448.bytesAt])

theorem disj1 {D r₀ : Region} (h : D.Disjoint r₀) : ∀ r ∈ [r₀], D.Disjoint r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact h

theorem disj2 {D r₀ r₁ : Region} (h₀ : D.Disjoint r₀) (h₁ : D.Disjoint r₁) : ∀ r ∈ [r₀, r₁], D.Disjoint r :=
  fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h₀
    · rw [List.mem_singleton.mp hr]; exact h₁

/-- Regions of the frame and of `out` that a step keeps. -/
theorem keep {D : Region} (h : Away L D) {ex : List Region} (hx : ∀ r ∈ ex, D.Disjoint r)
    {m m' : Mem} (hf : Frame (W L ex) m m') (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := h.bytes hx hf hn

theorem body_ok (hl : BaseCombOk) (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hpk : Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)) :
    WP isa body t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 114 =
        Spec.Ed448.sign (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)
          (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  obtain n10 : (10 : Nat) ≤ 2 ^ 64 := by decide
  obtain n57 : (57 : Nat) ≤ 2 ^ 64 := by decide
  -- Regions kept, and the disjointness of each from what the steps write.
  obtain dHS : (L.fr HDR 10).Disjoint (L.fr S 114) := fr_fr (by decide) (by decide) (by decide)
  obtain dHS' : (L.fr HDR 10).Disjoint (L.fr S 57) := fr_fr (by decide) (by decide) (by decide)
  obtain dHH : (L.fr HDR 10).Disjoint (L.fr HASH 114) := fr_fr (by decide) (by decide) (by decide)
  obtain dHr : (L.fr HDR 10).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  obtain dHc : (L.fr HDR 10).Disjoint L.SCR := hk.stack_scr (by decide)
  obtain dHR : (L.fr HDR 10).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 236 + 10 ≤ 280))).sub_right (r0_sub L)
  obtain dKS : (L.fr K 57).Disjoint (L.fr S 57) := fr_fr (by decide) (by decide) (by decide)
  obtain dSH : (L.fr S 57).Disjoint (L.fr HASH 114) := fr_fr (by decide) (by decide) (by decide)
  obtain dSr : (L.fr S 57).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  obtain dSc : (L.fr S 57).Disjoint L.SCR := hk.stack_scr (by decide)
  obtain dSR : (L.fr S 57).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 122 + 57 ≤ 280))).sub_right (r0_sub L)
  have dSK : (L.fr S 57).Disjoint (L.fr K 57) := dKS.symm
  obtain drR : (L.ob 57 57).Disjoint L.R0 := Offset.disjoint_base _ (by decide) (by decide)
  obtain drc : (L.ob 57 57).Disjoint L.SCR := hL.ob_scr (by decide)
  obtain drH : (L.ob 57 57).Disjoint (L.fr HASH 114) := hL.ob_stk (by decide) (by decide)
  obtain drK : (L.ob 57 57).Disjoint (L.fr K 57) := hL.ob_stk (by decide) (by decide)
  obtain dRH : L.R0.Disjoint (L.fr HASH 114) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 8 + 114 ≤ 280))).sub_right (r0_sub L)).symm
  obtain dRK : L.R0.Disjoint (L.fr K 57) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 179 + 57 ≤ 280))).sub_right (r0_sub L)).symm
  obtain dRc : L.R0.Disjoint L.SCR := hL.oc.sub_left (r0_sub L)
  have dRr : L.R0.Disjoint (L.ob 57 57) := drR.symm
  have aH := hL.away_hdr
  have aS := hL.away_s
  obtain ar := hL.away_ob (o := 57) (l := 57) (by decide)
  have aR := hL.away_r0
  -- The header.
  refine WP.seq (WP.mono (hdr_step hc hL ha) fun t1 ⟨hc1, hh1⟩ => ?_)
  -- `SHAKE256(seed)`, pruned.
  refine WP.seq (WP.mono (seed_step hc1 hL ha) fun t2 ⟨hc2, hf2, hb2⟩ => ?_)
  obtain hh2 := keep aH (disj1 dHS) hf2 n10
  simp only at hh2
  refine WP.seq (WP.mono (prune_step hc2 hL) fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  obtain hh3 := frame_bytes hf3 (D := L.fr HDR 10) (disj1 dHS') n10
  obtain hp3 := frame_bytes hf3 (D := L.fr K 57) (disj1 dKS) n57
  simp only at hh3 hp3
  obtain hpfx : Spec.Ed448.bytesAt t3.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      (Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114).drop 57 := by
    rw [hp3, ← hb2, drop57, Offset.add_add]; rfl
  rw [hb2] at hs3
  -- The nonce's hash, and `r`.
  refine WP.seq (WP.mono (nonce_step hc3 hL ha (by rw [hh3, hh2, hh1])) fun t4 ⟨hc4, hf4, hb4⟩ => ?_)
  obtain hh4 := keep aH (disj1 dHH) hf4 n10
  obtain hs4 := keep aS (disj1 dSH) hf4 n57
  simp only at hh4 hs4
  rw [hpfx] at hb4
  refine WP.seq (WP.mono (reduceR_step hc4 hL ha) fun t5 ⟨hc5, hf5, hr5⟩ => ?_)
  obtain hh5 := keep aH (disj2 dHr dHc) hf5 n10
  obtain hs5 := keep aS (disj2 dSr dSc) hf5 n57
  simp only at hh5 hs5
  rw [hb4] at hr5
  -- `R`.
  refine WP.seq (WP.mono (base_step hl hc5 hL ha) fun t6 ⟨hc6, hf6, hR6⟩ => ?_)
  obtain hh6 := keep aH (disj2 dHR dHc) hf6 n10
  obtain hs6 := keep aS (disj2 dSR dSc) hf6 n57
  obtain hr6 := keep ar (disj2 drR drc) hf6 n57
  simp only at hh6 hs6 hr6
  rw [hr5] at hR6 hr6
  -- The challenge's hash, and `k`.
  refine WP.seq (WP.mono (chal_step hc6 hL ha (by rw [hh6, hh5, hh4, hh3, hh2, hh1]))
    fun t7 ⟨hc7, hf7, hb7⟩ => ?_)
  obtain hs7 := keep aS (disj1 dSH) hf7 n57
  obtain hr7 := keep ar (disj1 drH) hf7 n57
  obtain hR7 := keep aR (disj1 dRH) hf7 n57
  simp only at hs7 hr7 hR7
  rw [hR6] at hb7
  refine WP.seq (WP.mono (reduceK_step hc7 hL ha) fun t8 ⟨hc8, hf8, hk8⟩ => ?_)
  obtain hs8 := keep aS (disj2 dSK dSc) hf8 n57
  obtain hr8 := keep ar (disj2 drK drc) hf8 n57
  obtain hR8 := keep aR (disj2 dRK dRc) hf8 n57
  simp only at hs8 hr8 hR8
  rw [hb7] at hk8
  -- `S`.
  refine WP.seq (WP.mono (mulAdd_step hc8 hL ha) fun t9 ⟨hc9, hf9, hS9⟩ => ?_)
  obtain hR9 := keep aR (disj2 dRr dRc) hf9 n57
  simp only at hR9
  -- The locals, cleared.
  refine WP.mono (wipe_step hc9 hL) fun u ⟨hu, hw⟩ => ⟨hu, ?_⟩
  rw [hw, bytes_halves, hR9, hR8, hR7, hR6, hS9, hr8, hr7, hr6, hk8, hs8, hs7, hs6, hs5, hs4]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs3

end VG.Proof.Ed448.Arm.SignCached

end

end


/-!
# Ed448 signing with a cached public key on ARMv7: the whole function

`signLocal`, the contract the proof is written against; `signCached_ok`, the
frame (`Whole.wrap_ok`) around the body; `signCached_ct`, constant time
(`Whole.wrap_ct`, from `body_ct`); and `signCached_verified`, against
`Spec.Ed448.signCachedContract Arm.abi 280`, given the reference ladder's
agreement with the specification (`BaseCombOk`), which only the
registration file supplies.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok Whole.wrap_ct
  Whole.originalWord Whole.Ctx)
open VG.Proof.Ed448 (BaseCombOk)

/-- `vg_ed448_sign_cached(out = r0, seed = r1, pk = r2, context = r3,
ctxlen = [sp], message = [sp, #4], len = [sp, #8], scratch = [sp, #12])`, with
280 bytes of stack. -/
def signLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 114⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let msg : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 3), 8192⟩
    let args : Region := ⟨State.addr s.sp, 16⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed, pk, ctx, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint scr ∧ seed.Disjoint out ∧ seed.Disjoint scr ∧ pk.Disjoint out ∧ pk.Disjoint scr ∧
      ctx.Disjoint out ∧ ctx.Disjoint scr ∧ msg.Disjoint out ∧ msg.Disjoint scr ∧
      args.Disjoint out ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧
      stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 114 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧
      (stackArg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat ≤ 255 ∧
      Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2 ∧ stackArg s 3 = stackArg t 3

def lay (s : State) : Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
    Whole.base s⟩

section
variable {s : State} (h : signLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_top : s.sp.toNat + 16 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := h
  exact ht

theorem original_args : (lay s).ORIG = ⟨State.addr s.sp, 16⟩ := by
  unfold Lay.ORIG lay
  rw [Whole.base_addr (entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  obtain hs := stack_eq h
  obtain ⟨_, hw, _, _, _, _, _, _, _, _, _, _, _, ko, _, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hs]
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok : (lay s).Ok := by
  obtain hb := entry_below h
  obtain ht := entry_top h
  obtain ho := original_args h
  obtain hs : (lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, oc, eo, ec, po, pc, xo, xc, mo, mc, ao, ac, ko, ke, kp, kx, km, kc, no, ne, np, nx, nm, nc,
    _, _, cl, _⟩ := h
  refine ⟨?_, by change (stackArg s 0).toNat < 256; omega_arith, oc, eo, ec, po, pc, xo, xc, mo, mc,
    by rw [ho]; exact ao, by rw [ho]; exact ac, by rw [hs]; exact ko, by rw [hs]; exact ke,
    by rw [hs]; exact kp, by rw [hs]; exact kx, by rw [hs]; exact km, by rw [hs]; exact kc,
    no, ne, np, nx, nm, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 296 ≤ 2 ^ 32
  omega_arith

theorem entry_regions : (lay s).inputs = Whole.bodyRd s ∧ (lay s).outputs = s.wr := by
  simp only [Lay.inputs, original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.SEED, Lay.PK, Lay.CTX, Lay.MSG, Lay.OUT, Lay.SCR,
    Lay.ARGS, lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Ctx (lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  obtain hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs _
  rw [(entry_regions h).1, (entry_regions h).2]
  exact hc

/-- The caller's stack argument `j - 6`, at `E + 248 + 4 j`, where the caller put it. -/
theorem caller_word {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) {j : Nat} (hj : 10 ≤ j) (hj' : j < 12) :
    p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = stackArg s (j - 8) := by
  obtain hb := entry_below h
  obtain ht := entry_top h
  obtain hf := Whole.saved_frame hb hp
  obtain hbt := Whole.base_top hb
  obtain ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j) =
      State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 8))) := by
    rw [addr_add (by omega_arith), Whole.base_addr hb, show 248 + 4 * j = 280 + 4 * (j - 8) by omega_arith,
      ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
      BitVec.sub_add_cancel]
  rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j), 4⟩) (Region.contains_self _ _)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide), ea]
  rfl

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : Arguments (lay s) p.mem := by
  obtain hb := entry_below h
  obtain ht := entry_top h
  intro j hj
  obtain ⟨hj12, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega_arith) hp hj
    obtain he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega_arith
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, lay, stackArg, stackArgAddr] using hw
  · have he : j = 10 ∨ j = 11 := by omega_arith
    rcases he with rfl | rfl
    · exact caller_word h hp (by decide) (by decide)
    · exact caller_word h hp (by decide) (by decide)

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  obtain ht := entry_top h
  intro j hj h4
  refine ⟨⟨State.addr s.sp, 16⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega_arith)]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega_arith) (by omega_arith)

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, ke, kp, kx, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ke.symm
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 16) (by decide)

theorem entry_key {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed448.bytesAt p.mem (State.addr (lay s).pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (lay s).seed) 57) := by
  obtain hk : Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  obtain hf := Whole.saved_frame (entry_below h) hp
  obtain hp' := entry_input h hf (r := ⟨State.addr (s.gpr .r2), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  obtain hs' := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  change Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r2)) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r1)) 57)
  simp only at hp' hs'
  rw [hp', hs']
  exact hk

end

theorem body_noFrames : body.noFrames = true := by
  simp only [body, seedHash, prune, nonceHash, chalHash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, reduce_noFrames,
    base_noFrames, mulAdd_noFrames]
  rfl

theorem signCached_ok (hl : BaseCombOk) {s : State} (h : signLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ signLocal.post s u := by
  obtain hw := Whole.wrap_ok body_noFrames (by decide : 6 ≤ 6) (entry_below h)
    (by have := entry_top h; omega_arith) (entry_read h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) (stackArg s 2).toNat))
    (fun p hp => WP.mono (body_ok hl (entry_ctx h hp) (lay_ok h) (entry_args h hp) (entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  obtain e1 := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  obtain e3 := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega_arith)
  obtain e5 := entry_input h hf (r := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 2).toNat ≤ 2 ^ 64; have := (stackArg s 2).isLt; omega_arith)
  change Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r0)) 114 = _
  simp only at e1 e3 e5
  rw [hp, e1, e3, e5]

theorem lay_eq {s t : State} (hp : signLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2, a3⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2, a3]

theorem signCached_ct (hl : BaseCombOk) : ConstantTime isa signLocal.pre signLocal.pub code := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => entry_below hs)
    (fun _ hs => by have := entry_top hs; omega_arith) (fun _ hs => entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok hl (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_key hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    obtain he := lay_eq hp
    obtain hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    obtain hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    exact ⟨(body_ct hl (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The contract -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, `scratch`'s address `0x10000` as the fourth
argument on the stack, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a = 0x900E then 1 else if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  obtain hi' := List.mem_range.mp hi
  obtain ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega_arith
  obtain hne : (0x2000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega_arith
  simp only [satMem, hne, ↓reduceIte, ha, show 0x2000 + i < 0x3000 from by omega_arith, true_or]

theorem sat_key : Spec.Ed448.bytesAt satMem 0x3000 57 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    obtain hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    obtain ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega_arith
    obtain hne : (0x3000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
      have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega_arith
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, satMem, hne, ↓reduceIte, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega_arith, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk : Spec.Ed448.bytesAt satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt satMem 0x2000 57) := by
  rw [sat_seed, sat_key]
  rfl

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract Arm.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, satState]
    sig_and_intros
    all_goals try exact sat_pk
    all_goals decide +kernel

theorem sign_implies : signLocal.Implies (Spec.Ed448.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [signLocal, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := sat

/-- `vg_ed448_sign_cached` on ARMv7, given the reference comb's agreement
with the specification. -/
theorem signCached_verified (hl : BaseCombOk) :
    Verified Arm.target code (Spec.Ed448.signCachedContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok hl h) (signCached_ct hl) (.refl sign_implies.sat_left))
    sign_implies

end VG.Proof.Ed448.Arm.SignCached
