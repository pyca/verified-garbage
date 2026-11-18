module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Packed
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Point
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `Ed25519.PPC64LE.PointTable`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.PointOps`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.FieldVerified`, which this module and modules that import it used -/

section

/-!
# `vg_gf25519_r32_pow250` and `vg_ed25519_r32_point_add` on PPC64LE, by register

Each function meets a contract of its facts by register (`powPPC`, `addPPC`),
with no stack (`pow_ok'`, `add_ok'`). The elements as the contracts read them
are the proofs' (`SpecConv`). No function writes a nonvolatile register or the
link register, or calls another.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Proof.X25519.Field32 (valAt Fits Keeps Keeps₂)

/-- The working space of `pow250` and the point addition, `bytes` long, in `r3`. -/
def wsPre (bytes : Nat) (s : State) : Prop := s.rd = [] ∧ s.wr = [⟨s.gpr .r3, bytes⟩]

def wsPub (s₁ s₂ : State) : Prop := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

/-- `pow250`'s facts by register: `a^(2^250 - 1)` and `a^11` from `a`, the rest of the
working space kept. -/
def powPPC : Contract isa where
  pre := wsPre 4096
  post s s' :=
    valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.oAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ (2 ^ 250 - 1) % P ∧
      valAt s'.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.eAt) % P =
        valAt s.mem (s.gpr .r3) (BitVec.ofNat 32 Proof.X25519.Field32.aAt) ^ 11 % P ∧
      Keeps₂ (s.gpr .r3) s.mem s'.mem
  pub := wsPub

/-- The point addition's facts by register: `p + q` into `p`, the rest of the working space
kept. -/
def addPPC : Contract isa where
  pre s := wsPre 8192 s ∧ Proof.Ed25519.Point32.elemAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.dAt = Spec.Ed25519.d
  post s s' :=
    Proof.Ed25519.Point32.pointAt s'.mem (s.gpr .r3) Proof.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.pAt)
          (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .r3) Proof.Ed25519.Point32.qAt) ∧
      Proof.Ed25519.Point32.Keeps (s.gpr .r3) s.mem s'.mem
  pub := wsPub

/-- Code that writes only the registers `R`, none of them nonvolatile, and never the link
register, keeps the ABI's registers. -/
theorem abi_of_rest {c : Prog isa} {R : List Reg} (hR : ∀ r ∈ preserved, r ∉ R) {s s' : State}
    {t : List Leak} (he : VG.Exec isa c s t s') (hr : Rest R s s') (hn : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true) : abiPreserved s s' :=
  ⟨fun r hr' => hr.gpr r (hR r hr'), hr.sp, Exec.lr he hn hl⟩

/-! ## `pow250` -/

theorem pow_ok' (s : State) (hs : powPPC.pre s) :
    ∃ t s', VG.Exec isa pow250Fn s t s' ∧ abiPreserved s s' ∧ powPPC.post s s' := by
  obtain ⟨_, hwr⟩ := hs
  obtain ⟨t, s', he, hR, hF, hE⟩ := pow250Fn_ok (s := s) rfl
    ⟨4096, Nat.le_refl _, by rw [hwr]; exact List.mem_singleton_self _⟩
  have h15 : env s'.mem (s.gpr .r3) 15 = Proof.X25519.pw (env s.mem (s.gpr .r3) 2) (2 ^ 250 - 1) := by
    rw [congrFun hE 15, (power250Env_eval _).1, Proof.X25519.chainF_eq]
  have h14 : env s'.mem (s.gpr .r3) 14 = Proof.X25519.pw (env s.mem (s.gpr .r3) 2) 11 := by
    rw [congrFun hE 14, (power250Env_eval _).2, Proof.X25519.chainF_eq]
  refine ⟨t, s', he, abi_of_rest (by decide) he hR (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), ?_, ?_, keeps_pow hF⟩
  · rw [show Proof.X25519.Field32.oAt = offset 15 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    have h := val_of_env h15
    exact h
  · rw [show Proof.X25519.Field32.eAt = offset 14 from rfl, show Proof.X25519.Field32.aAt = offset 2 from rfl,
      valAt_ofNat, valAt_ofNat]
    exact val_of_env (e := 11) h14

/-! ## The point addition -/

theorem addW_ok (b : Addr) :
    ∀ op ∈ pointAddOps, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ addW b, r.Sub r' := by
  have h : ∀ op ∈ pointAddOps, (opOut op).val < 4 ∨ (8 ≤ (opOut op).val ∧ (opOut op).val < 16) := by
    decide
  intro op hop r hr
  have ho := h op hop
  have hA := ACC_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases ho with ho | ho
    · exact ⟨_, List.mem_cons_self, Offset.sub _ (by simp only [offset]; omega_using []) (by simp only [offset]; omega_using [ho])⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        Offset.sub _ (by simp only [offset]; omega_using [ho]) (by simp only [offset]; omega_using [ho])⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Offset.sub _ (Nat.le_refl _)
      (Nat.le_refl _)⟩

theorem add_ok' (s : State) (hs : addPPC.pre s) :
    ∃ t s', VG.Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addPPC.post s s' := by
  obtain ⟨⟨_, hwr⟩, hd⟩ := hs
  have hc : Ctx (s.gpr .r3) (s.write .r6 (s.gpr .r3 + BitVec.ofNat 64 0)) :=
    ⟨by simp [State.write], 8192, by decide, by simp [State.write, hwr]⟩
  have hw : WP isa addFn s fun t => Rest (.r6 :: clob) s t ∧ Frame (addW (s.gpr .r3)) s.mem t.mem ∧
      env t.mem (s.gpr .r3) = evalOps pointAddOps (env s.mem (s.gpr .r3)) := by
    refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
    have hc1 : Ctx (s.gpr .r3) s1 := ⟨by rw [u1.gpr]; simp, by rw [u1.wr, hwr]; exact ⟨8192, by decide, by simp⟩⟩
    refine WP.mono (fieldCodeW_ok pointAddOps (by decide) _ (addW_ok _) hc1) fun t ⟨hr, hf, he⟩ =>
      ⟨(u1.rest (by decide)).trans (hr.mono (by decide)), by rw [u1.mem] at hf; exact hf, by rw [he, u1.mem]⟩
  obtain ⟨t, s', he, hR, hF, hE⟩ := hw
  refine ⟨t, s', he, abi_of_rest (by decide) he hR (by decide +kernel)
    (by rw [← Code.allInstrs_eq]; decide +kernel), ?_, keeps_add hF⟩
  rw [pointAt_eq, pointAt_eq, pointAt_q, hE]
  exact pointAdd_eval _ (by rw [← elemAt_eq]; exact hd)

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: calls of the point addition, and doubling

A call of `vg_ed25519_r32_point_add` (`addCall_ok`), from a working space of
8192 bytes with `d` in slot 16, leaves in slots 0–3 the sum of the points in
slots 0–3 and 4–7, keeps every slot but 0–3 and the temporaries 8–15
(`Keeps`, `env_keeps`), and keeps `Keep`: no register but `fclob`, no memory
but the field area. A doubling (`doubleCall_ok`) copies the point to slots
4–7 and adds.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

/-- The point addition's working space: `ws` in `r6`, its 8192 bytes writable. -/
structure Ctx8 (b : Addr) (s : State) : Prop where
  r6 : s.gpr .r6 = b
  wr : (⟨b, 8192⟩ : Region) ∈ s.wr

theorem Ctx8.ctx {b : Addr} {s : State} (h : Ctx8 b s) : Ctx b s := ⟨h.r6, 8192, by decide, h.wr⟩

theorem Ctx8.of_keep {b : Addr} {s t : State} (h : Ctx8 b s) (k : Keep b s t) : Ctx8 b t :=
  ⟨by rw [k.rest.gpr _ (by decide), h.r6], by rw [k.rest.wr]; exact h.wr⟩

/-- The slots the point addition keeps: all but the sum's and the temporaries'. -/
def Kept (i : Slot) : Prop := 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val

instance (i : Slot) : Decidable (Kept i) := by unfold Kept; infer_instance

theorem env_keeps {b : Addr} {m m' : Mem} (h : Proof.Ed25519.Point32.Keeps b m m') {i : Slot} (hi : Kept i) :
    env m' b i = env m b i := by
  have hs := slot_range i
  have hA := ACC_eq
  unfold env FS
  rw [← read_V, ← read_V]
  refine congrArg (fun v : BitVec (8 * 32) => Proof.X25519.toFe v.toNat) (Mem.read_congr fun j hj => ?_)
  have hi' := hi
  unfold Kept at hi'
  have ho : offset i = 64 + 32 * i.val := rfl
  rw [Offset.add_add]
  refine (h (offset i + j) (by simp only [Proof.Ed25519.Point32.wsBytes]; omega_using [hs, hj])
    (by simp only [Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes]; omega_using [hi', ho]) (by omega_using [hj, hi', ho]) (by omega_using [hs, hj]))

/-- The registers `vg_ed25519_r32_point_add` never writes. -/
def keptRegs : List Reg := [.r2, .r3, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23,
  .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- **A call of the point addition**. -/
theorem addCall_ok {b : Addr} {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) :
    WP isa addCall s fun t => Keep b s t ∧
      point (env t.mem b) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7) ∧
      ∀ i : Slot, Kept i → env t.mem b i = env s.mem b i := by
  unfold addCall
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have e3 : s1.gpr .r3 = b := by rw [u1.gpr, hc.r6, BitVec.add_zero]
  have g : ∀ q, q ∉ linkRegs → (s1.callEntry.withRegions [] [⟨b, 8192⟩]).gpr q = s1.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hsub : ∀ r ∈ ([⟨b, 8192⟩] : List Region), ∃ r' ∈ s1.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton.mp hr, u1.wr]
    exact ⟨_, hc.wr, 0, by simp, by simp⟩
  have hd' : Proof.Ed25519.Point32.elemAt s1.mem b Proof.Ed25519.Point32.dAt = Spec.Ed25519.d := by
    rw [u1.mem, show Proof.Ed25519.Point32.dAt = offset 16 from rfl, elemAt_eq]; exact hd
  refine WP.seq (WP.call (k := addPPC) add_ok' (rd := []) (wr := [⟨b, 8192⟩])
    ⟨⟨rfl, by rw [State.withRegions_wr, g _ (by decide), e3]⟩, by
      rw [State.withRegions_mem, State.callEntry_mem, g _ (by decide), e3]; exact hd'⟩
    (Covers.of_sub fun r hr => by
      obtain ⟨r', hr', h'⟩ := hsub r (by simpa using hr)
      exact ⟨r', List.mem_append_right _ hr', h'⟩)
    (Covers.of_sub hsub) ?_ (by decide +kernel))
  intro t hrd hwr hsp hfr _ hkeep ⟨hpt, hks⟩
  have c3 : (s1.callEntry.withRegions [] [⟨b, 8192⟩]).gpr .r3 = b := by rw [g _ (by decide), e3]
  simp only [State.withRegions_mem, State.callEntry_mem, c3] at hpt hks
  rw [u1.mem] at hpt hks
  -- The registers the callee never writes.
  have nw : ((instrs addFn).all fun i => (keptRegs).all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  have hk : ∀ q ∈ keptRegs, t.gpr q = s1.gpr q := fun q hq => by
    refine hkeep q (by revert hq; cases q <;> decide) fun i hi => ?_
    have := List.all_eq_true.mp (List.all_eq_true.mp nw i hi) q hq
    simpa using this
  refine wp_addi (by decide) (by decide) fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · by_cases h6 : q = .r6
    · subst h6
      rw [v1.gpr, hk _ (by decide), e3, BitVec.add_zero, hc.r6]
    · rw [v1.other _ h6, hk _ (by revert hq h6; cases q <;> decide), u1.other _ (by revert hq; cases q <;> decide)]
  · rw [v1.rd, hrd, u1.rd]
  · rw [v1.wr, hwr, u1.wr]
  · rw [v1.sp, hsp, u1.sp]
  · rw [v1.mem]
    intro x hx
    have hnf := hx _ (List.mem_singleton_self _)
    by_cases hw : (⟨b, 8192⟩ : Region).Contains x 1
    · have hi : (x - b).toNat + 1 ≤ 8192 := hw
      have hx' : x = b + BitVec.ofNat 64 (x - b).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hlo : (x - b).toNat < 64 ∨ 1024 ≤ (x - b).toNat := by
        by_contra hc
        refine hnf ?_
        rw [hx']
        exact Offset.contains _ (by omega_using [hc]) (by omega_using [hc]) (by omega_using [])
      rw [hx']
      exact hks _ (by simp only [Proof.Ed25519.Point32.wsBytes]; omega_using [hi])
        (by simp only [Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes]; omega_using [hlo]) (by omega_using [hlo]) (by omega_using [hlo])
    · rw [← u1.mem]
      exact hfr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hw
  · rw [v1.mem, ← pointAt_eq, hpt, pointAt_eq, pointAt_q]
  · intro i hi
    rw [v1.mem]
    exact env_keeps hks hi

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: points in tables

A table entry is a point's four coordinates, 128 bytes at an offset `o` of
the working space above the field area (`tableAt`). `pointToTable` with
`r14` at the entry writes the point of slots 0–3 there
(`pointToTable_ok`), and `pointFromTable` reads it into slots 0–3
(`pointFromTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

theorem Ctx8.inW {b : Addr} {s : State} (h : Ctx8 b s) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n :=
  in_base h.wr hd (by omega_using [hd])

theorem Ctx8.inR {b : Addr} {s : State} (h : Ctx8 b s) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) hd (by omega_using [hd])

theorem Ctx8.of_rest {b : Addr} {s t : State} {R : List Reg} (h : Ctx8 b s) (hr : Rest R s t)
    (h6 : Reg.r6 ∉ R) : Ctx8 b t :=
  ⟨by rw [hr.gpr _ h6, h.r6], by rw [hr.wr]; exact h.wr⟩

/-- The point at offset `o`, as four elements. -/
def tableAt (m : Mem) (b : Addr) (o : Nat) : Spec.Ed25519.Point :=
  ⟨FS m b o, FS m b (o + 32), FS m b (o + 64), FS m b (o + 96)⟩

section
variable {b : Addr}

/-- After `j` coordinates of `pointToTable` from `s0`. -/
structure ToTableInv (b : Addr) (o : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 32 * j⟩] s0.mem s.mem
  outs : ∀ i < j, V s.mem b (o + 32 * i) = V s0.mem b (64 + 32 * i)

theorem pointToTable_ok {s : State} (hc : Ctx8 b s) {o : Nat} (h14 : s.gpr .r14 = b + BitVec.ofNat 64 o)
    (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 128⟩] s.mem t.mem ∧
      tableAt t.mem b o = point (env s.mem b) 0 1 2 3 := by
  refine WP.mono (wp_range_flatMap (M := isa) (ToTableInv b o s) (fun j t hj h => ?_) 4 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest, h.frame, ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    refine WP.mono (packField_ok hct.ctx (q := b + BitVec.ofNat 64 o) (a := 64 + 32 * j) (dst := 32 * j)
      (by rw [h.rest.gpr _ (by decide), h14]) (by omega_using [hj]) (by omega_using [hj])
      (fun k hk => by rw [Offset.add_add]; exact hct.inW (by omega_using [ho', hj, hk]))
      (by rw [Offset.add_add]; exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho', hj]) (by omega_using [hj]))) fun u hu => ?_
    have hf : Frame [⟨b + BitVec.ofNat 64 (o + 32 * j), 32⟩] t.mem u.mem := by
      have := hu.frame; rwa [Offset.add_add] at this
    have hsrc : V t.mem b (64 + 32 * j) = V s.mem b (64 + 32 * j) := by
      unfold V
      exact val32_congr (limb_frame h.frame fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [ho, hj, hk])) (by omega_using [hj, hk]) (by omega_using [ho', hj]))
    refine ⟨h.rest.trans hu.rest, ?_, fun i hi => ?_⟩
    · refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← h.outs i hi]
        unfold V
        exact val32_congr (limb_frame hf fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hi, hk])) (by omega_arith) (by omega_using [ho', hj]))
      · rw [← hsrc, V, V]
        refine val32_congr fun k hk => ?_
        have := hu.outs k hk
        rw [wd_shift] at this
        rw [limb, show o + 32 * i + 4 * k = o + (32 * i + 4 * k) by omega_using [], this]
  · simp only [tableAt, point, env, FS]
    have e0 := h.outs 0 (by decide)
    have e1 := h.outs 1 (by decide)
    have e2 := h.outs 2 (by decide)
    have e3 := h.outs 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3
    rw [e0, e1, e2, e3]
    rfl

/-- After `j` coordinates of `pointFromTable` from `s0`. -/
structure FromTableInv (b : Addr) (o : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r7] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 64, 32 * j⟩] s0.mem s.mem
  outs : ∀ i < j, V s.mem b (64 + 32 * i) = V s0.mem b (o + 32 * i)

theorem pointFromTable_ok {s : State} (hc : Ctx8 b s) {o : Nat} (h14 : s.gpr .r14 = b + BitVec.ofNat 64 o)
    (ho : 1024 ≤ o) (ho' : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      Rest [.r7] s t ∧ Frame [⟨b + BitVec.ofNat 64 64, 128⟩] s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 = tableAt s.mem b o ∧ ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  refine WP.mono (wp_range_flatMap (M := isa) (FromTableInv b o s) (fun j t hj h => ?_) 4 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest, h.frame, ?_, fun i hi => ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    refine WP.mono (unpackField_ok hct.ctx (q := b + BitVec.ofNat 64 o) (o := 64 + 32 * j) (src := 32 * j)
      (by rw [h.rest.gpr _ (by decide), h14]) (by omega_using [hj]) (by omega_using [hj])
      (fun k hk => by rw [Offset.add_add]; exact hct.inR (by omega_using [ho', hj, hk]))
      (by rw [Offset.add_add]; exact Offset.disjoint _ (by omega_using [ho]) (by omega_using [ho', hj]) (by omega_using [hj])))
      fun u ⟨ru, fu, lu⟩ => ?_
    have hsrc : V t.mem b (o + 32 * j) = V s.mem b (o + 32 * j) := by
      unfold V
      exact val32_congr (limb_frame h.frame fun r hr k hk => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_using [ho])) (by omega_using [ho', hj, hk]) (by omega_using [hj]))
    refine ⟨h.rest.trans ru, ?_, fun i hi => ?_⟩
    · refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← h.outs i hi]
        unfold V
        exact val32_congr (limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hi, hk])) (by omega_arith) (by omega_using [hj]))
      · rw [← hsrc, V, V]
        refine val32_congr fun k hk => ?_
        rw [lu k hk, wd_shift, limb, show o + 32 * i + 4 * k = o + (32 * i + 4 * k) by omega_using []]
  · have e0 := h.outs 0 (by decide)
    have e1 := h.outs 1 (by decide)
    have e2 := h.outs 2 (by decide)
    have e3 := h.outs 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3
    simp only [tableAt, point, env, FS]
    rw [show offset 0 = 64 from rfl, show offset 1 = 96 from rfl, show offset 2 = 128 from rfl,
      show offset 3 = 160 from rfl, e0, e1, e2, e3]
  · have hs := slot_range i
    unfold env FS V
    refine congrArg _ (val32_congr (limb_frame h.frame fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by simp only [offset]; omega_using [hi])) (by omega_using [hs, hk]) (by omega_using [])

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: doublings and tables of powers

`doubleCall_ok`: the point of slots 0–3 doubled (`p + p`). `double16_ok`:
doubled 16 times in a loop counted by `r15`, `powerPoint p 16`.
`pointPowers_ok`: the table at `start` filled with `powerPoint p (stride j)`
for `j < count`, the point doubled `stride` times between entries.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (powerPoint)

/-- Code that keeps the registers outside `R` and the memory outside the field area, maps the
point of slots 0–3 by `f` and keeps slot 16 and above. -/
def PtSpec (b : Addr) (R : List Reg) (c : Prog isa) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) : Prop :=
  ∀ s, Ctx8 b s → env s.mem b 16 = Spec.Ed25519.d → WP isa c s fun t =>
    Rest R s t ∧ Frame [FA b] s.mem t.mem ∧ point (env t.mem b) 0 1 2 3 = f (point (env s.mem b) 0 1 2 3) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i

theorem env_copyPointToQ (e : Env) : point (evalOps copyPointToQOps e) 4 5 6 7 = point e 0 1 2 3 ∧
    point (evalOps copyPointToQOps e) 0 1 2 3 = point e 0 1 2 3 ∧
    ∀ i : Slot, 8 ≤ i.val → evalOps copyPointToQOps e i = e i := by
  refine ⟨rfl, rfl, fun i hi => ?_⟩
  simp only [evalOps, copyPointToQOps, List.foldl, evalOp, Function.update_apply]
  obtain h4 : i ≠ 4 := fun h => by subst h; exact absurd hi (by decide)
  obtain h5 : i ≠ 5 := fun h => by subst h; exact absurd hi (by decide)
  obtain h6 : i ≠ 6 := fun h => by subst h; exact absurd hi (by decide)
  obtain h7 : i ≠ 7 := fun h => by subst h; exact absurd hi (by decide)
  simp only [h4, h5, h6, h7, ite_false]

theorem doubleCall_ok (b : Addr) : PtSpec b fclob doubleCall fun p => Spec.Ed25519.pointAdd p p := by
  intro s hc hd
  unfold doubleCall copyPointToQ
  refine WP.seq (WP.mono (fieldCode_ok copyPointToQOps hc.ctx) fun t ⟨kt, et⟩ => ?_)
  obtain ⟨q4, q0, qk⟩ := env_copyPointToQ (env s.mem b)
  rw [← et] at q4 q0 qk
  refine WP.mono (addCall_ok (hc.of_keep kt) (by rw [qk 16 (by decide), hd])) fun u ⟨ku, pu, keu⟩ =>
    ⟨kt.rest.trans ku.rest, kt.frame.trans ku.frame, by rw [pu, q4, q0], fun i hi => ?_⟩
  rw [keu i (.inr hi), qk i (by omega_arith)]

theorem PtSpec.mono {b : Addr} {R R' : List Reg} {c : Prog isa} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (h : PtSpec b R c f) (hR : ∀ r ∈ R, r ∈ R') : PtSpec b R' c f :=
  fun s hc hd => WP.mono (h s hc hd) fun _ ⟨r, fr, p, k⟩ => ⟨r.mono hR, fr, p, k⟩

/-- Sixteen doublings, counted by `r15`. -/
theorem double16_ok (b : Addr) : PtSpec b (.r15 :: fclob) double16 fun p => powerPoint p 16 := by
  intro s hc hd
  unfold double16
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  obtain hc1 : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.r15]) (by decide)) (by decide)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 16 ∧ Rest (.r15 :: fclob) s t ∧ Frame [FA b] s.mem t.mem ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧ point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (16 - n) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i) ?_ 16 s1
    ⟨by decide, by decide, u1.rest (by decide), by rw [u1.mem]; exact Frame.refl _ _, u1.gpr,
      by rw [u1.mem]; rfl, fun i _ => by rw [u1.mem]⟩
  rintro n t ⟨h1, h2, hr, hf, h15, hp, hk⟩
  obtain hct : Ctx8 b t := hc.of_rest hr (by decide)
  unfold doubleBody
  refine WP.seq (WP.mono (doubleCall_ok b t hct (by rw [hk 16 (by decide), hd])) fun u ⟨ru, fu, pu, ku⟩ => ?_)
  refine wp_subi (by decide) (by decide) fun u1 v1 => WP.block_nil ?_
  obtain e15 : u1.gpr .r15 = BitVec.ofNat 64 (n - 1) := by
    rw [v1.gpr, ru.gpr _ (by decide), h15, ofNat_sub_one h1 (by omega_arith)]
  obtain hz : (u1.gpr .r15 != 0) = decide (n - 1 ≠ 0) := by rw [e15, ofNat_ne_zero (by omega_arith)]
  obtain hp' : point (env u1.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (16 - (n - 1)) := by
    rw [v1.mem, pu, hp, show 16 - (n - 1) = 16 - n + 1 by omega_arith]; rfl
  obtain hr' : Rest (.r15 :: fclob) s u1 := hr.trans ((ru.mono (by decide)).trans (v1.rest (by decide)))
  obtain hf' : Frame [FA b] s.mem u1.mem := by rw [v1.mem]; exact hf.trans fu
  obtain hk' : ∀ i : Slot, 16 ≤ i.val → env u1.mem b i = env s.mem b i := fun i hi => by
    rw [v1.mem, ku i hi, hk i hi]
  rw [eval_nonzero, hz]
  by_cases h0 : n - 1 = 0
  · refine .inl ⟨by simp [h0], hr', hf', ?_, hk'⟩
    rw [hp', h0]
  · exact .inr ⟨by simp [h0], n - 1, by omega_arith, by omega_arith, by omega_arith, hr', hf', e15, hp', hk'⟩

/-- A table entry outside a frame's regions keeps its point. -/
theorem tableAt_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 o, 128⟩ : Region).Disjoint r) : tableAt m' b o = tableAt m b o := by
  obtain h : ∀ c < 4, V m' b (o + 32 * c) = V m b (o + 32 * c) := fun c hc => by
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk =>
      (hd r hr).sub_left (Offset.sub b (d := o + 32 * c + 4 * k) (n := 4) (e := o) (k := 128) (by omega_arith) (by omega_arith)))
  simp only [tableAt, FS]
  rw [← Nat.add_zero o, ← Nat.mul_zero 32, h 0 (by decide), Nat.mul_zero, Nat.add_zero,
    show o + 32 = o + 32 * 1 from rfl, h 1 (by decide), show o + 64 = o + 32 * 2 from rfl, h 2 (by decide),
    show o + 96 = o + 32 * 3 from rfl, h 3 (by decide)]

/-- A slot outside a frame's regions keeps its element. -/
theorem env_keep {b : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (i : Slot)
    (hd : ∀ r ∈ rs, (⟨b + BitVec.ofNat 64 (offset i), 32⟩ : Region).Disjoint r) : env m' b i = env m b i := by
  have := slot_range i
  unfold env FS V
  exact congrArg _ (val32_congr (limb_frame hf fun r hr k hk =>
    (hd r hr).sub_left (Offset.sub b (d := offset i + 4 * k) (n := 4) (e := offset i) (k := 32) (by omega_arith) (by omega_arith))))

/-- `r14` at entry `n` of the table at `start`. -/
theorem tableAddr_ok {b : Addr} {s : State} (hc : Ctx8 b s) {start n : Nat} (hs : start < 2 ^ 15) (hn : n < 64)
    (h16 : s.gpr .r16 = BitVec.ofNat 64 n) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Rest [.r7, .r14] s t → t.mem = s.mem → t.gpr .r14 = b + BitVec.ofNat 64 (start + 128 * n) →
      WP isa (.block is) t Q) :
    WP isa (.block (tableAddr start ++ is)) s Q := by
  unfold tableAddr
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) hs fun s1 u1 => wp_lsl (by decide) fun s2 u2 => wp_add fun s3 u3 => ?_
  refine k s3 ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide))))
    (by rw [u3.mem, u2.mem, u1.mem]) ?_
  rw [u3.gpr, u2.gpr, u2.other _ (by decide), u1.gpr, u1.other _ (by decide), hc.r6, h16, BitVec.add_assoc,
    show BitVec.ofNat 64 n <<< 7 = BitVec.ofNat 64 (128 * n) by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith, BitVec.ofNat_add]

theorem ofNat_sub_ne_zero {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0) = decide (a ≠ c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := fun e => h (by
      obtain e' : BitVec.ofNat 64 a = BitVec.ofNat 64 c := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 c), e]; simp
      have := congrArg BitVec.toNat e'
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at this)
    rw [bne_iff_ne.mpr this]
    simp [h]

/-- The point doubled `stride` times: `double16` or one `doubleCall`. -/
theorem powerBatch_ok (b : Addr) (batch : Bool) :
    PtSpec b (.r15 :: fclob) (powerBatch batch) fun p => powerPoint p (powerStride batch) := by
  cases batch
  · exact (doubleCall_ok b).mono (by decide)
  · exact double16_ok b

/-- While filling the table at `start` from `s0`, for the point `p`: `n` entries written. -/
structure PowInv (b : Addr) (start count stride : Nat) (s0 : State) (p : Spec.Ed25519.Point) (n : Nat)
    (s : State) : Prop where
  lt : n < count
  ctx : Ctx8 b s
  rest : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s0 s
  frame : Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s0.mem s.mem
  r16 : s.gpr .r16 = BitVec.ofNat 64 n
  point : point (env s.mem b) 0 1 2 3 = powerPoint p (stride * n)
  table : ∀ j < n, tableAt s.mem b (start + 128 * j) = powerPoint p (stride * j)
  keep : ∀ i : Slot, 16 ≤ i.val → env s.mem b i = env s0.mem b i

/-- **A table of powers**. -/
theorem pointPowers_ok {b : Addr} {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d)
    {start count : Nat} (batch : Bool) (hs : 1024 ≤ start) (hs' : start + 128 * count ≤ 8192)
    (hc1 : 1 ≤ count) :
    WP isa (pointPowers start count batch) s fun t =>
      Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s t ∧
      Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s.mem t.mem ∧
      (∀ j < count, tableAt t.mem b (start + 128 * j) =
        powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j)) ∧
      point (env t.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * count) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem b i = env s.mem b i := by
  obtain hS : start < 2 ^ 15 := by omega_arith
  obtain hC : count < 64 := by omega_arith
  unfold pointPowers
  refine WP.seq (wp_li (by decide) fun s1 u1 => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun m t => ∃ n, m = count - n ∧
      PowInv b start count (powerStride batch) s (point (env s.mem b) 0 1 2 3) n t) ?_ count s1
    ⟨0, by omega_arith, by omega_arith, hc.of_rest (u1.rest (ws := [.r16]) (by decide)) (by decide), u1.rest (by decide),
      by rw [u1.mem]; exact Frame.refl _ _, u1.gpr, by rw [u1.mem]; rfl, fun j hj => by omega_arith,
      fun i _ => by rw [u1.mem]⟩
  rintro m t ⟨n, rfl, h⟩
  have hn := h.lt
  unfold powersBody
  refine WP.seq (tableAddr_ok h.ctx hS (by omega_arith) h.r16 fun t1 r1 m1 e14 => ?_)
  obtain hc1' : Ctx8 b t1 := h.ctx.of_rest r1 (by decide)
  refine WP.mono (pointToTable_ok hc1' e14 (by omega_arith) (by omega_arith)) fun t2 ⟨r2, f2, tb2⟩ => ?_
  rw [m1] at tb2 f2
  obtain hc2 : Ctx8 b t2 := hc1'.of_rest r2 (by decide)
  obtain hd2 : env t2.mem b 16 = Spec.Ed25519.d := by
    have := slot_range (16 : Slot)
    unfold env FS V
    rw [← hd, ← h.keep 16 (by decide)]
    refine congrArg _ (val32_congr (limb_frame f2 fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by simp only [offset] at *; omega_arith)) (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (powerBatch_ok b batch t2 hc2 hd2) fun t3 ⟨r3, f3, p3, k3⟩ => ?_)
  obtain hc3 : Ctx8 b t3 := hc2.of_rest r3 (by decide)
  unfold powersNext
  refine wp_addi (by decide) (by decide) fun t4 u4 => wp_subi (by decide) (by omega_arith) fun t5 u5 => WP.block_nil ?_
  obtain e16 : t5.gpr .r16 = BitVec.ofNat 64 (n + 1) := by
    rw [u5.other _ (by decide), u4.gpr, r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h.r16,
      BitVec.ofNat_add]
  obtain e7 : (t5.gpr .r7 != 0) = decide (n + 1 ≠ count) := by
    rw [u5.gpr, u4.gpr, r3.gpr _ (by decide), r2.gpr _ (by decide), r1.gpr _ (by decide), h.r16,
      show BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) from (BitVec.ofNat_add _ _).symm,
      ofNat_sub_ne_zero (by omega_arith) (by omega_arith)]
  obtain hm5 : t5.mem = t3.mem := by rw [u5.mem, u4.mem]
  obtain hFA : ∀ o, start ≤ o → o + 128 ≤ start + 128 * count →
      (⟨b + BitVec.ofNat 64 o, 128⟩ : Region).Disjoint (FA b) := fun o h1 h2 =>
    Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain hpt : point (env t2.mem b) 0 1 2 3 = point (env t.mem b) 0 1 2 3 := by
    obtain e : ∀ i : Slot, env t2.mem b i = env t.mem b i := fun i => by
      refine env_keep f2 i fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      have := slot_range i
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    simp only [point, e]
  obtain hR : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s t5 :=
    h.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide))))))
  obtain hF : Frame [FA b, ⟨b + BitVec.ofNat 64 start, 128 * count⟩] s.mem t5.mem := by
    rw [hm5]
    refine h.frame.trans ((f2.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (f3.mono fun r hr => by simp [List.mem_singleton.mp hr]))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  obtain hP : point (env t5.mem b) 0 1 2 3 = powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * (n + 1)) := by
    rw [hm5, p3, hpt, h.point]
    dsimp only
    rw [← Proof.Ed25519.powerPoint_add, Nat.mul_succ]
  obtain hT : ∀ j < n + 1, tableAt t5.mem b (start + 128 * j) =
      powerPoint (point (env s.mem b) 0 1 2 3) (powerStride batch * j) := by
    intro j hj
    rw [hm5, tableAt_keep f3 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hFA _ (by omega_arith) (by omega_arith)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [tableAt_keep f2 fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact h.table j hj
    · rw [tb2, h.point]
  obtain hK : ∀ i : Slot, 16 ≤ i.val → env t5.mem b i = env s.mem b i := fun i hi => by
    rw [hm5, k3 i hi, ← h.keep i hi]
    refine env_keep f2 i fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    have := slot_range i
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  rw [eval_nonzero, e7]
  by_cases hl : n + 1 = count
  · refine .inl ⟨by simp [hl], hR, hF, fun j hj => hT j (by omega_arith), by rw [hP, hl], hK⟩
  · exact .inr ⟨by simp [hl], count - (n + 1), by omega_arith, n + 1, rfl,
      ⟨by omega_arith, hc3.of_rest ((u4.rest (ws := [.r7, .r16]) (by decide)).trans (u5.rest (by decide))) (by decide), hR, hF, e16, hP, hT,
        hK⟩⟩

end VG.Proof.Ed25519.PPC64LE
