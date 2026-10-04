import VerifiedGarbage.Proof.Ed448.Arm.SignCached.Body
import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified

/-!
# Ed448 signing with a cached public key on ARMv7: constant time

As `vg_ed448_verify`'s on this target: two runs from the same pointers,
lengths and `sp` set up the same arguments for every call, each callee is
constant time under its own contract, and the blocks between the calls
address memory only through `sp`, `r12` and `scratch`
(`Proof/Ed448/Arm/Shake/CT.lean`); the positions the absorptions return
depend only on the lengths.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.FR Whole.rel_wp Whole.CallReady Whole.block_cons_ct Whole.block_nil_ct Whole.Within
  Whole.call_ok Whole.zeroWords_ct)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs Two Slots valid_const valid_frame frame_within DataOk
  hdr_len)
open VG.Proof.Ed448.Arm (scalarReduceLocal scalarReduce_ok scalarReduce_ct scalarBaseLocal scalarBase_ok
  scalarBase_ct scalarMulAddLocal scalarMulAdd_ok scalarMulAdd_ct)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hashes -/

theorem seed_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) seedHash (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  obtain ⟨cs, ds⟩ := hL.input_data (R := L.SEED) (D := ⟨State.addr L.seed, 57⟩) (by simp [Lay.inputs])
    ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have e1 : argVal L.E L.value (.caller 1 0) = L.seed := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  have a := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) (src := .caller 1 0) (len := .const 57)
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
  have hkn : (argVal L.E L.value (.const k)).toNat = k := by
    simp only [argVal, BitVec.toNat_ofNat]; omega
  have hd' : argVal L.E L.value (.frame d) = L.E + BitVec.ofNat 32 d := rfl
  exact hL.kit.next_ct ha hb (scr_at L) P hP (valid_frame (by omega)) (valid_const hk)
    (by rw [hd', hkn, hL.kit.frame_addr (by omega)]; exact .inl (frame_within _ hd))
    (by rw [hd', hkn, hL.kit.frame_addr (by omega)]; exact (hL.away_fr h8 hd).kwr)
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
  have x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  have x3 := local_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (d := K) (k := 57)
    (by decide) (by decide) (by decide)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
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
  have x2 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  have e0 : argVal L.E L.value (.caller 0 0) = L.out := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  have x3 := hk.next_ct (g₁ := g₁) (g₂ := g₂) ha hb (scr_at L) P2 (Nat.mod_lt _ (by decide))
    (src := .caller 0 0) (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide))
    (by rw [e0, e57]; exact .inr ⟨L.OUT, List.mem_append_right _ (out_in L), r0_within L⟩)
    (by rw [e0, e57]; exact hL.away_r0.kwr) (by rw [e0, e57]; have := hL.no; omega)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 2 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega)
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x5 := input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
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
  have get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L (L.out + BitVec.ofNat 32 57) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    have h0 := slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    have h1 := slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    have h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hO : Whole.Within (L.ob 57 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.ob 57 57) R :=
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
  have get : ∀ t, Slots L.E L.value args [] t → ReduceArgs L (L.E + BitVec.ofNat 32 K) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    have h0 := slot_reg hs (r := .r0) (v := .frame K) (by simp [args])
    have h1 := slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    have h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hO : Whole.Within (L.fr K 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.fr K 57) R :=
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

theorem base_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase)
      (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)]
  have get : ∀ t, Slots L.E L.value args [] t → BaseArgs L t := by
    intro t hs
    have h0 := slot_reg hs (r := .r0) (v := .caller 0 0) (by simp [args])
    have h1 := slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    have h2 := slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
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
  have get : ∀ t, Slots L.E L.value args [.caller SC 0] t → MulArgs L t := by
    intro t hs
    have h0 := slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    have h1 := slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    have h2 := slot_reg hs (r := .r2) (v := .frame K) (by simp [args])
    have h3 := slot_reg hs (r := .r3) (v := .frame S) (by simp [args])
    have a0 := hs.2 0 (by simp)
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

theorem body_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) body (T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have h : RelCT isa (T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt 4 HDR)) (T2 L g₁ g₂ m₁ m₂ fun _ => True) :=
    (hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 4) (off := HDR) (by decide) hL.cl (by decide)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
  exact h.seq ((seed_ct hL ha hb).seq ((prune_ct hL).seq ((nonce_ct hL ha hb).seq ((reduceR_ct hL ha hb).seq
    ((base_ct hl hL ha hb).seq ((chal_ct hL ha hb).seq ((reduceK_ct hL ha hb).seq
      ((mulAdd_ct hL ha hb).seq (wipe_ct hL)))))))))

end VG.Proof.Ed448.Arm.SignCached
