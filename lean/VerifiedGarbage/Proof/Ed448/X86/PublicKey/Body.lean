import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Layout
import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
import VerifiedGarbage.Impl.Ed448.X86.PublicKey

/-!
# Ed448 public-key derivation on x86 (32-bit): correctness

For any `base` meeting `scalarBaseLocal` (`CalleeOk`): `SHAKE256(seed, 114)`
in the frame at `HASH` (`hash_ok`), its first 57 bytes pruned in place
(`Kit.prune_ok`), `[s]B` encoded into `out` by `base` (`base_step`), and the
frame from `HASH` on cleared; `publicKey_ok`: the whole function.
-/

namespace VG.Proof.Ed448.X86.PublicKey

open VG VG.X86 VG.Impl.Ed448.X86.PublicKey
open VG.Impl.Ed25519.X86.Whole (Value setup)
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots Whole.Within Whole.FR Whole.valid Whole.call_ok Whole.Ctx.zeroWords)

variable {s t u : State} {g : Reg → BitVec 32} {m : Mem}

/-- The frame's invariant, from any registers and memory on entry. -/
abbrev GCtx (s : State) (g : Reg → BitVec 32) (m : Mem) (t : State) : Prop :=
  VG.Proof.Ed25519.X86.Whole.Ctx (base s) g m (pkRd s) (pkWr s) t

theorem scr_at (s : State) : ScrAt 3 (arg s) 2 (arg s 2) := ⟨by decide, rfl⟩

/-- `SHAKE256(seed, 114)` in the frame at `HASH`. -/
theorem hash_ok (h : Facts s) (hc : GCtx s g m t) (ha : Args (base s) 3 (arg s) m) :
    WP isa Impl.Ed448.X86.PublicKey.hash t fun u => GCtx s g m u ∧
      Spec.Sha3.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
        Spec.Sha3.shake256 (Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57) 114 := by
  have hk := kit h
  unfold Impl.Ed448.X86.PublicKey.hash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at s)) fun t1 ⟨hc1, hz, _⟩ => ?_)
  refine WP.seq (WP.mono (hk.first_abs hc1 ha (scr_at s) (src := .caller 1 0) (len := .const 57)
    (P := arg s 1) (N := 57) (show 1 < 3 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
    (.inr ⟨SEED s, List.mem_append_left _ (seed_in s), whole _⟩) (hk.away_input (seed_in s) (whole _))
    h.seed (repr_nil hz)) fun t2 ⟨hc2, _, hr2, hp2⟩ => ?_)
  have e1 : Spec.Sha3.bytesAt t1.mem ((arg s 1).setWidth 64) 57 = Spec.Sha3.bytesAt m ((arg s 1).setWidth 64) 57 :=
    hk.input_bytes (D := SEED s) hc1 (seed_in s) (whole (SEED s)) (by show 57 ≤ 2 ^ 64; decide)
  rw [e1] at hr2
  refine WP.seq (WP.mono (hk.pad_step hc2 ha (scr_at s) hr2 (by rw [hp2, length_sbytes]))
    fun t3 ⟨hc3, _, hs3⟩ => ?_)
  refine WP.mono (hk.sqz_step hc3 ha (scr_at s) (d := HASH) (by decide) (by decide)) fun u ⟨hu, _, hb⟩ =>
    ⟨hu, ?_⟩
  rw [hb, hs3, ← shake256_eq]

/-- The outgoing arguments of `scalar_base(out, esp + HASH, scratch)`. -/
structure BaseSlots (s u : State) : Prop where
  a0 : Whole.slots (base s) u 0 = arg s 0
  a1 : Whole.slots (base s) u 1 = base s + BitVec.ofNat 32 HASH
  a2 : Whole.slots (base s) u 2 = arg s 2

theorem base_setup (h : Facts s) (hc : GCtx s g m t) (ha : Args (base s) 3 (arg s) m) :
    WP isa (.block baseArgs) t fun u => GCtx s g m u ∧ Frame [⟨(base s).setWidth 64, 24⟩] t.mem u.mem ∧
      BaseSlots s u := by
  have hk := kit h
  unfold baseArgs
  refine WP.mono (hk.setup_ok hc ha (vs := [.caller 0 0, .frame HASH, .caller 2 0]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨show 0 < 3 by decide, trivial, show 2 < 3 by decide,
      fun _ h => nomatch h⟩)) fun u ⟨hu, hm, hs, _⟩ => ⟨hu, hm, ?_⟩
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argVal_frame, argVal_caller, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero]
    at a0 a1 a2
  exact ⟨a0, a1, a2⟩

theorem base_pre (h : Facts s) (hu : GCtx s g m u) (hs : BaseSlots s u) :
    scalarBaseLocal.pre (u.callEntry.withRegions
      [fr (base s) HASH 57, ⟨(base s).setWidth 64, 12⟩] [OUT s, SCR (arg s 2)]) := by
  have hk := kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have hb := hk.below
  have hf := hk.frame
  have e4 := hk.esp4
  have lout : (Lo (base s)).Disjoint (OUT s) := (hk.ko _ (out_in s)).sub_left (lo_sub _)
  have lscr := hk.lo_scr
  have ab : ∀ rd wr, argAddr (u.callEntry.withRegions rd wr) 0 = (base s).setWidth 64 :=
    VG.Proof.Ed25519.X86.Whole.arg_base hu.esp
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr, arg_withRegions,
    State.withRegions_gpr, State.callEntry_esp, hu.esp, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, hk.slot_arg hu (j := 2) (by decide) hs.a2, ab, fa]
  exact ⟨trivial, trivial, h.oc, hk.fr_scr (by decide), Kit.args_disj (by decide) lout,
    Kit.args_disj (by decide) lscr, hk.ret_disj lout, hk.ret_disj lscr, h.out, hk.fr_fit (by decide),
    h.scratch, by omega⟩

theorem base_covers (s : State) : Covers ([fr (base s) HASH 57, ⟨(base s).setWidth 64, 12⟩] ++ [OUT s, SCR (arg s 2)])
    (pkRd s ++ Whole.FR (base s) :: pkWr s) := by
  refine covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · exact .inl (args_within _ (by decide))
  · exact .inr ⟨_, List.mem_append_right _ (out_in s), whole _⟩
  · exact .inr ⟨_, List.mem_append_right _ (scr_in s), whole _⟩

theorem base_writes (s : State) : ∀ r ∈ [OUT s, SCR (arg s 2)], Whole.Within r (Whole.FR (base s)) ∨
    ∃ R ∈ pkWr s, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, out_in s, whole _⟩
  · exact .inr ⟨_, scr_in s, whole _⟩

def base_ready (h : Facts s) (hu : GCtx s g m u) (hs : BaseSlots s u) :
    VG.Proof.Ed25519.X86.Whole.CallReady scalarBaseLocal (base s) (pkRd s) (pkWr s) u :=
  ⟨_, _, base_pre h hu hs, base_covers s, base_writes s⟩

theorem base_call {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s) (hu : GCtx s g m u)
    (hs : BaseSlots s u) :
    WP isa (.call "vg_ed448_scalar_base" base') u fun v => GCtx s g m v ∧
      Spec.Ed448.bytesAt v.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 57) := by
  have hk := kit h
  have fa := hk.fr_addr (d := HASH) (by decide)
  have lo := lo_fr (base s) (d := HASH) (l := 57) (by decide) (by decide)
  refine Whole.call_ok hu hk.below hB.ok hB.nosp hB.stack (base_pre h hu hs) (base_covers s) (base_writes s)
    fun v hv _ _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hv, ?_⟩
  simp only [scalarBaseLocal, State.withRegions_mem, arg_withRegions, hm₂, hk.slot_arg hu (j := 0) (by decide) hs.a0,
    hk.slot_arg hu (j := 1) (by decide) hs.a1, fa] at hpost
  rw [hpost, hk.entry_bytes hu (D := fr (base s) HASH 57) lo (by show 57 ≤ 2 ^ 64; decide)]

/-- `scalar_base(out, esp + HASH, scratch)`. -/
theorem base_step {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s) (hc : GCtx s g m t)
    (ha : Args (base s) 3 (arg s) m) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" base') t fun u => GCtx s g m u ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 57) := by
  refine WP.seq (WP.mono (base_setup h hc ha) fun u ⟨hu, hm, hs⟩ => ?_)
  refine WP.mono (base_call hB h hu hs) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  rw [ho, frame_bytes hm (D := fr (base s) HASH 57) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by show 57 ≤ 2 ^ 64; decide)]

/-- The frame from `HASH` on, cleared; `out` as it was. -/
theorem wipe_step (h : Facts s) (hc : GCtx s g m t) :
    WP isa (.block wipe) t fun u => GCtx s g m u ∧
      Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57 = Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57 := by
  have hk := kit h
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 6) (count := 58) hk.frame (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  refine frame_bytes hf (D := OUT s) (fun r hr => ?_) (by show 57 ≤ 2 ^ 64; decide)
  rw [List.mem_singleton.mp hr]
  exact ((hk.ko _ (out_in s)).sub_left (frame_sub_stk _ (d := 4 * 6) (l := 4 * 58) (by decide))).symm

theorem body_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s) (hc : GCtx s g m t)
    (ha : Args (base s) 3 (arg s) m) :
    WP isa (body base') t fun u => GCtx s g m u ∧ Spec.Ed448.bytesAt u.mem ((arg s 0).setWidth 64) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) := by
  have hk := kit h
  refine WP.seq (WP.mono (hash_ok h hc ha) fun t₁ ⟨hc₁, hh⟩ => ?_)
  refine WP.seq (WP.mono (hk.prune_ok hc₁ (q := HASH) (by decide)) fun t₂ ⟨hc₂, _, hn, _⟩ => ?_)
  refine WP.seq (WP.mono (base_step hB h hc₂ ha) fun t₃ ⟨hc₃, ho⟩ => ?_)
  refine WP.mono (wipe_step h hc₃) fun u ⟨hu, hw⟩ => ⟨hu, ?_⟩
  have hh' : Spec.Ed448.bytesAt t₁.mem ((base s).setWidth 64 + BitVec.ofNat 64 HASH) 114 =
      Spec.Sha3.shake256 (Spec.Ed448.bytesAt m ((arg s 1).setWidth 64) 57) 114 := hh
  rw [hw, ho, Spec.Ed448.scalarBase, hn, hh']
  rfl

theorem body_nosp {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') : NoSp (body base') :=
  nosp_seq (nosp_seq (NoSp.of_all (by decide +kernel))
      (nosp_seq (absorb_nosp' (NoSp.of_all (by decide +kernel)))
        (nosp_seq (pad_nosp' (NoSp.of_all (by decide +kernel))) (squeeze_nosp' (NoSp.of_all (by decide +kernel))))))
    (nosp_seq (NoSp.of_all (by decide +kernel))
      (nosp_seq (nosp_seq (NoSp.of_all (by decide +kernel)) hB.nosp) (NoSp.of_all (by decide +kernel))))

theorem publicKey_ok {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') {s : State} (hp : pkLocal.pre s) :
    WP isa (code base') s fun t => abiPreserved s t ∧ pkLocal.post s t := by
  have h := facts hp
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := h.below; omega) (body_nosp hB)
    (WP.mono (body_ok hB h (push_ctx hp.1 hp.2.1 h.below) (args_val s 3)) fun u ⟨hu, ho⟩ =>
      ⟨pop_abi (by decide) h.below hu (ret_out h), ?_⟩)
  change Spec.Ed448.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem ((arg s 0).setWidth 64) 57 = _
  rw [popped_mem]
  exact ho

end VG.Proof.Ed448.X86.PublicKey
