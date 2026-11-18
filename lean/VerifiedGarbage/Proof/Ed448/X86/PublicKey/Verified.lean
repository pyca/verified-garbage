module

public import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Ed448.X86.Shake.CT
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
public import VerifiedGarbage.Proof.Ed448.X86.Shake.Entry
public import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
public import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
public import VerifiedGarbage.Proof.Ed448.X86.Callee
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
public import VerifiedGarbage.Impl.Ed448.X86.PublicKey
import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Ed448.X86.Shake.Entry
meta import VerifiedGarbage.Proof.Ed448.X86.Shake.Sponge
meta import VerifiedGarbage.Proof.Ed448.X86.Shake.Prune
meta import VerifiedGarbage.Proof.Ed448.X86.BaseLocal
meta import VerifiedGarbage.Proof.Ed448.X86.Callee
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe
meta import VerifiedGarbage.Impl.Ed448.X86.PublicKey
meta import VerifiedGarbage.Proof.Ed25519.X86.Whole.HashPre
meta import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! ### `Ed448.X86.PublicKey.Body`, which only this module used -/

section

/-! ### `Ed448.X86.PublicKey.Layout`, which only this module used -/

section

/-!
# Ed448 public-key derivation on x86 (32-bit): the contract the proof is written against

`pkLocal`, as Ed25519's on this target (`Proof/Ed25519/X86/PublicKey/Layout.lean`)
with 57-byte buffers: what `vg_ed448_public_key(out, seed, scratch)` reads
and writes, their separation, and the 280 bytes of stack below its return
address. `Facts` are its separation and bounds, and `kit` the layout facts
the calls need (`Shake.Kit`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86.PublicKey

open VG VG.X86
open VG.Proof.Ed448.X86.Shake (base ARGS RET Kit SCR)

def pkRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩]
def pkWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 57⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

def pkLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 280
    s.rd = pkRd s ∧ s.wr = pkWr s ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s t := Spec.Ed448.bytesAt t.mem ((arg s 0).setWidth 64) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem ((arg s 1).setWidth 64) 57)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2

abbrev OUT (s : State) : Region := ⟨(arg s 0).setWidth 64, 57⟩
abbrev SEED (s : State) : Region := ⟨(arg s 1).setWidth 64, 57⟩

structure Facts (s : State) : Prop where
  os : (OUT s).Disjoint (SEED s)
  oc : (OUT s).Disjoint (SCR (arg s 2))
  sc : (SEED s).Disjoint (SCR (arg s 2))
  ao : (ARGS s 3).Disjoint (OUT s)
  ac : (ARGS s 3).Disjoint (SCR (arg s 2))
  ro : (RET s).Disjoint (OUT s)
  rc : (RET s).Disjoint (SCR (arg s 2))
  ko : (below (s.gpr .esp) 280).Disjoint (OUT s)
  ks : (below (s.gpr .esp) 280).Disjoint (SEED s)
  kc : (below (s.gpr .esp) 280).Disjoint (SCR (arg s 2))
  out : (arg s 0).toNat + 57 ≤ 2 ^ 32
  seed : (arg s 1).toNat + 57 ≤ 2 ^ 32
  scratch : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  below : 280 ≤ (s.gpr .esp).toNat
  above : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32

theorem facts {s : State} (h : pkLocal.pre s) : Facts s := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, a, b, c, d, e⟩ := h
  exact ⟨os, oc, sc, ao, ac, ro, rc, ko, ks, kc, a, b, c, d, e⟩

theorem seed_in (s : State) : SEED s ∈ pkRd s := List.mem_cons_self
theorem args_in (s : State) : ARGS s 3 ∈ pkRd s := List.mem_cons_of_mem _ List.mem_cons_self
theorem out_in (s : State) : OUT s ∈ pkWr s := List.mem_cons_self
theorem scr_in (s : State) : SCR (arg s 2) ∈ pkWr s := List.mem_cons_of_mem _ List.mem_cons_self

theorem kit {s : State} (h : Facts s) : Kit (base s) (arg s 2) 3 (pkRd s) (pkWr s) := by
  refine Shake.kit h.below (by have := h.above; omega_using [this]) h.scratch (scr_in s) ?_ ?_ ?_ (args_in s)
  · intro R hR
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [h.ko, h.kc]
  · intro r hr R hR
    simp only [pkRd, pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr hR
    rcases hr with rfl | rfl <;> rcases hR with rfl | rfl
    exacts [h.os.symm, h.sc, h.ao, h.ac]
  · intro r hr
    simp only [pkRd, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.ks.symm, Shake.args_stack (n := 3) h.below (by have := h.above; omega_using [this]) (by decide)]

theorem ret_out {s : State} (h : Facts s) : ∀ R ∈ pkWr s, (RET s).Disjoint R := by
  intro R hR
  simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [h.ro, h.rc]

end VG.Proof.Ed448.X86.PublicKey

end

end


/-!
# Ed448 public-key derivation on x86 (32-bit): correctness

For any `base` meeting `scalarBaseLocal` (`CalleeOk`): `SHAKE256(seed, 114)`
in the frame at `HASH` (`hash_ok`), its first 57 bytes pruned in place
(`Kit.prune_ok`), `[s]B` encoded into `out` by `base` (`base_step`), and the
frame from `HASH` on cleared; `publicKey_ok`: the whole function.
-/

@[expose] public section

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
    h.scratch, by omega_using [hf, e4], hk.callee_room, hk.callee_stk _ (out_in s), hk.callee_stk _ (scr_in s)⟩

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
    (by simp only [List.length_replicate]; have := h.below; omega_using [this]) (body_nosp hB)
    (WP.mono (body_ok hB h (push_ctx hp.1 hp.2.1 h.below) (args_val s 3)) fun u ⟨hu, ho⟩ m v fl =>
      ⟨pop_abi (by decide) h.below hu (ret_out h) fl v, ?_⟩)
  change Spec.Ed448.bytesAt m ((arg s 0).setWidth 64) 57 = _
  refine Eq.trans (List.map_congr_left fun _ hi => fl.bytes (R := OUT s) (fun r hr => by
    rw [List.mem_singleton.mp hr, List.length_replicate]
    exact (h.ko.sub_left (below_sub (by decide) h.below)).symm)
    (by show 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)) ?_
  exact ho

end VG.Proof.Ed448.X86.PublicKey

end

end

/-!
# Ed448 public-key derivation on x86 (32-bit): constant time, and `Verified`

As Ed25519's on this target: two runs from the same pointers and `esp` set
up the same arguments for every call, each callee is constant time under its
own contract (the sponge functions' and `scalarBaseLocal`, `CalleeOk.ct`),
and the blocks between the calls address memory only through `esp`
(`taint_decide`). `publicKey_verified`: for any `base` meeting
`scalarBaseLocal` (`CalleeOk`), `code base` meets
`Spec.Ed448.publicKeyContract X86.abi 280`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86.PublicKey

open VG VG.X86 VG.Impl.Ed448.X86.PublicKey
open VG.Impl.Ed448.X86.Shake (callWith)
open VG.Proof.Ed448.X86.Shake
open VG.Proof.Ed25519.X86 (Whole.slots)

variable {s₁ s₂ : State}

theorem base_eq (hp : pkLocal.pub s₁ s₂) : base s₂ = base s₁ := by
  simp only [base, hp.1]

theorem rd_eq (hp : pkLocal.pub s₁ s₂) : pkRd s₂ = pkRd s₁ := by
  simp only [pkRd, argAddr, hp.1, hp.2.2.1]

theorem wr_eq (hp : pkLocal.pub s₁ s₂) : pkWr s₂ = pkWr s₁ := by
  simp only [pkWr, hp.2.1, hp.2.2.2]

/-- The second run's argument words, as the first's. -/
theorem args₂ (hp : pkLocal.pub s₁ s₂) : Args (base s₁) 3 (arg s₁) s₂.mem := by
  intro i hi
  rw [← base_eq hp, args_val s₂ 3 i hi]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [hp.2.1.symm, hp.2.2.1.symm, hp.2.2.2.symm]

abbrev Two₁ (s₁ s₂ : State) := Two (base s₁) (pkRd s₁) (pkWr s₁) s₁.gpr s₂.gpr s₁.mem s₂.mem

theorem base_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s₁) :
    RelCT isa (Two₁ s₁ s₂ (BaseSlots s₁)) (.call "vg_ed448_scalar_base" base') (Two₁ s₁ s₂ fun _ => True) :=
  call_ct hB.ok hB.ct (fun _ _ _ hc hs => base_ready h hc hs)
    (fun a b ea eb ha hb ar aw br bw => by
      have e := (kit h).args_eq ea eb (k := 3) (by decide) (fun i hi => by
        rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        exacts [ha.a0.trans hb.a0.symm, ha.a1.trans hb.a1.symm, ha.a2.trans hb.a2.symm]) ar aw br bw
      exact ⟨entry_esp ea eb ar aw br bw, e 0 (by decide), e 1 (by decide), e 2 (by decide)⟩)
    (fun _ hc hs => WP.mono (base_call hB h hc hs) fun _ hv => ⟨hv.1, trivial⟩)
    (fun _ hc hs => WP.mono (base_call hB h hc hs) fun _ hv => ⟨hv.1, trivial⟩)

theorem body_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') (h : Facts s₁)
    (hp : pkLocal.pub s₁ s₂) :
    RelCT isa (Two₁ s₁ s₂ fun _ => True) (body base') (Two₁ s₁ s₂ fun _ => True) := by
  have hk := kit h
  have ha := args_val s₁ 3
  have hb := args₂ hp
  have hsc := scr_at s₁
  unfold body Impl.Ed448.X86.PublicKey.hash callWith
  refine RelCT.seq (RelCT.seq (hk.zero_ct ha hb hsc (by taint_decide))
    (RelCT.seq (hk.first_ct ha hb hsc (src := .caller 1 0) (len := .const 57) (P := arg s₁ 1) (N := 57)
      (show 1 < 3 by decide) trivial (by rw [argVal_caller, BitVec.add_zero]) rfl
      (.inr ⟨SEED s₁, List.mem_append_left _ (seed_in s₁), whole _⟩) (hk.away_input (seed_in s₁) (whole _))
      h.seed (by taint_decide))
      (RelCT.seq (hk.padStep_ct ha hb hsc (pos := 57 % 136) (by decide) (by taint_decide))
        (hk.sqzStep_ct ha hb hsc (d := HASH) (by decide) (by decide) (by taint_decide))))) ?_
  refine RelCT.seq (hk.prune_ct (q := HASH) (by decide) (by taint_decide)) (RelCT.seq (RelCT.seq ?_
    (base_ct (s₂ := s₂) hB h)) ?_)
  · exact block_ct (by taint_decide) (fun _ hc _ => WP.mono (base_setup h hc ha) fun _ hu => ⟨hu.1, hu.2.2⟩)
      (fun _ hc _ => WP.mono (base_setup h hc hb) fun _ hu => ⟨hu.1, hu.2.2⟩)
  · exact block_ct (by taint_decide) (fun _ hc _ => WP.mono (wipe_step h hc) fun _ hu => ⟨hu.1, trivial⟩)
      (fun _ hc _ => WP.mono (wipe_step h hc) fun _ hu => ⟨hu.1, trivial⟩)

theorem publicKey_ct {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    ConstantTime isa pkLocal.pre pkLocal.pub (code base') := by
  apply RelCT.constantTime
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb a' b' ⟨s₁, s₂, ⟨p₁, p₂, hp⟩, rfl, rfl⟩ ea eb
  have c₂ := push_ctx p₂.1 p₂.2.1 (facts p₂).below
  rw [base_eq hp, rd_eq hp, wr_eq hp] at c₂
  exact ⟨(body_ct hB (facts p₁) hp _ _ _ _ _ _
    ⟨⟨push_ctx p₁.1 p₁.2.1 (facts p₁).below, trivial⟩, ⟨c₂, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The shared contract -/

def pkWide : Contract isa := { pkLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 57⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint seed ∧ out.Disjoint scratch ∧
      seed.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ stack.Disjoint out ∧
      stack.Disjoint seed ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 57 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ (s.gpr .esp).toNat ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
}

def pkSatMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

def pkSatState : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := pkSatMem
  rd := [⟨0x2000, 57⟩]
  wr := [⟨0x1000, 57⟩, ⟨0x4000, 8192⟩, ⟨0x8004, 12⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) :
    pkLocal.pre (s.withRegions (pkRd s) (pkWr s)) := by
  obtain ⟨_, _, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩ := h
  simp only [pkLocal, pkRd, pkWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, below, Taint.sub_setWidth nb]
  exact ⟨True.intro, True.intro, os, oc, sc, ao, ac, ro, rc, ko, ks, kc, no, ns, nc, nb, na⟩

theorem pkWide_implies : pkWide.Implies (Spec.Ed448.publicKeyContract X86.abi 280) := by
  have a0 : arg pkSatState 0 = 0x1000 := by decide
  have a1 : arg pkSatState 1 = 0x2000 := by decide
  have a2 : arg pkSatState 2 = 0x4000 := by decide
  have e : argAddr pkSatState 0 = 0x8004 := by decide
  have sp : pkSatState.gpr .esp = 0x8000 := rfl
  sig_implies [Spec.Ed448.publicKeyContract, Spec.Ed448.publicKeySig,
    Spec.Ed448.scratchWords, pkWide, pkLocal, below, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, e, sp] using pkSatState

theorem publicKey_verified {base' : Prog isa} (hB : CalleeOk scalarBaseLocal base') :
    Verified X86.target (code base') (Spec.Ed448.publicKeyContract X86.abi 280) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkLocal.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target (code base') pkLocal :=
    Verified.of_correct (fun _ h => publicKey_ok hB h) (publicKey_ct hB) (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with (rfl | rfl) | rfl | rfl <;> simp only [true_or, or_true]
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [pkWide, pkLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed448.X86.PublicKey
