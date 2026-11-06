module

public import VerifiedGarbage.Impl.Xdh.Arm
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Xdh.Rel
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Xdh.Arm
meta import VerifiedGarbage.Proof.Xdh.Common
meta import VerifiedGarbage.Proof.Xdh.Rel
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 and X448 exchange, with RFC 7748's check, on ARMv7

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Xdh/RISCV64.lean`): for any callee `c` without frames whose
contract `k` its proof gives (`Callee`), `Impl.Xdh.Arm.exchange` pushes
`lr` at `B + 4` and `out` at `B`, for `B = sp - 8` (`Pushed`), calls `c`
with its arguments as they came (`called_wp`), which writes neither, pops
`out` into `r1` (`Popped`), ORs the `n` bytes there into `r3`
(`orBytes_wp`) and computes the result from it (`checked_wp`); the last pop
restores `lr` (`exchange_wp`). Two runs whose pointers agree (`Pub`) leak
the same trace (`exchange_ct`).
-/

@[expose] public section

namespace VG.Proof.Xdh.Arm

open VG VG.Arm VG.Impl.Xdh.Arm
open VG.Spec.X25519 (bytesAt)
open VG.Proof.Xdh (Eq2 TT rel_seq ct_of)
open VG.Proof.X25519.Arm (Upd wp_ldrb wp_dp wp_mov wp_movw op2_reg op2_imm op2_lsr dpVal)

section
variable (n w : Nat) (s : State)

/-- The regions of the arguments, and the 8 bytes of our frames. -/
abbrev outR : Region := ⟨State.addr (s.gpr .r0), n⟩
abbrev scR : Region := ⟨State.addr (s.gpr .r1), n⟩
abbrev ptR : Region := ⟨State.addr (s.gpr .r2), n⟩
abbrev wsR : Region := ⟨State.addr (s.gpr .r3), w⟩
abbrev frR : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩

end

/-- What the callee needs at its entry. -/
def CallPre (n w : Nat) (s : State) : Prop :=
  s.rd = [scR n s, ptR n s] ∧ s.wr = [outR n s, wsR w s] ∧
    (outR n s).Disjoint (scR n s) ∧ (outR n s).Disjoint (ptR n s) ∧ (outR n s).Disjoint (wsR w s) ∧
    (scR n s).Disjoint (wsR w s) ∧ (ptR n s).Disjoint (wsR w s) ∧
    (s.gpr .r0).toNat + n ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + n ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + n ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + w ≤ 2 ^ 32

/-- What the exchange function needs: the callee's needs, and room for the
frames, apart from the arguments. -/
def ExPre (n w : Nat) (s : State) : Prop :=
  CallPre n w s ∧ (frR s).Disjoint (outR n s) ∧ (frR s).Disjoint (scR n s) ∧
    (frR s).Disjoint (ptR n s) ∧ (frR s).Disjoint (wsR w s) ∧ 8 ≤ s.sp.toNat

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in `r0`
if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem (State.addr (s.gpr .r0)) n =
      f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n) ∧
    (s'.gpr .r0).setWidth 32 =
      if f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n) =
        List.replicate n 0 then 0 else 1

/-- What two runs agree on: the pointers. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

/-- The exchange function's contract on ARMv7. -/
def exContract (n w : Nat) (f : List Byte → List Byte → List Byte) : Contract isa where
  pre := ExPre n w
  post := ExPost n f
  pub := Pub

/-- The callee, by its contract `k`. -/
structure Callee (n w : Nat) (f : List Byte → List Byte → List Byte) (c : Prog isa) (k : Contract isa) :
    Prop where
  hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  hct : ConstantTime isa k.pre k.pub c
  pre : ∀ s, CallPre n w s → k.pre s
  post : ∀ s s', k.post s s' →
    bytesAt s'.mem (State.addr (s.gpr .r0)) n =
      f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n)
  pub : ∀ s₁ s₂, Pub s₁ s₂ → k.pub s₁ s₂
  nf : c.noFrames = true

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-! ## The frames -/

section
variable {n w : Nat} {s : State}

/-- The base of the frames. -/
abbrev B (s : State) : Addr := State.addr s.sp - BitVec.ofNat 64 8

theorem addr4 (h : ExPre n w s) : State.addr (s.sp - BitVec.ofNat 32 4) = B s + BitVec.ofNat 64 4 := by
  have hsp := h.2.2.2.2.2
  rw [B, FrameStack.addr_sub' (by omega)]
  bv_omega

theorem addr44 (h : ExPre n w s) :
    State.addr (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4) = B s := by
  have hsp := h.2.2.2.2.2
  rw [B, show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 by bv_omega,
    FrameStack.addr_sub' (by omega)]

theorem B_toNat (h : ExPre n w s) : (B s).toNat + 8 ≤ 2 ^ 32 := by
  have hsp := h.2.2.2.2.2
  have e := VG.Proof.X25519.Arm.addr_toNat s.sp
  have := s.sp.isLt
  rw [B, BitVec.toNat_sub, BitVec.toNat_ofNat, e]
  omega

/-- The frames' words are apart from a region apart from both. -/
theorem fr_part {r : Region} (hr : (frR s).Disjoint r) {d : Nat} (hd : d ≤ 4) :
    (⟨B s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r :=
  hr.sub_left (Offset.sub_base _ (by omega))

theorem slot_sep (h : ExPre n w s) : (⟨B s, 4⟩ : Region).Disjoint ⟨B s + BitVec.ofNat 64 4, 4⟩ := by
  have := B_toNat h
  exact Offset.base_disjoint _ (k := 4) (e := 4) (by omega) (by omega)

theorem fr_contains {d : Nat} (hd : d ≤ 4) :
    (frR s).Contains (B s + BitVec.ofNat 64 d) 4 :=
  Offset.contains_base _ (by omega) (by omega)

end

/-! ## The phases -/

/-- The memory once both pushes are done. -/
abbrev eMem (s : State) : Mem :=
  (s.mem.writeW (B s + BitVec.ofNat 64 4) (s.gpr .lr)).writeW (B s) (s.gpr .r0)

/-- The state the call starts in: both frames pushed. -/
structure Pushed (n w : Nat) (s e : State) : Prop where
  mem : e.mem = eMem s
  gpr : e.gpr = s.gpr
  sp : e.sp = s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4
  rd : e.rd = s.rd
  wr : e.wr = ⟨B s, 4⟩ :: ⟨B s + BitVec.ofNat 64 4, 4⟩ :: s.wr

theorem pushed_pushed {n w : Nat} {s : State} (h : ExPre n w s) :
    Pushed n w s (pushed [.r0] (pushed [.lr] s)) := by
  refine ⟨?_, rfl, rfl, rfl, ?_⟩
  · simp only [pushed, storeWords, List.map_cons, List.map_nil, List.length_singleton, Nat.mul_one]
    rw [addr4 h, addr44 h]
  · simp only [pushed_wr, List.length_singleton, Nat.mul_one, pushed_sp]
    rw [addr4 h, addr44 h]

/-- The memory the pushes leave outside the frames. -/
theorem pushed_keep {s : State} {r : Region} (hr : (frR s).Disjoint r)
    {x : Addr} (hx : r.Contains x 1) : eMem s x = s.mem x := by
  have hf : Frame [frR s] s.mem (eMem s) := by
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fr_contains (s := s) (by decide))).writeW
      (List.mem_singleton_self _) _ ?_
    simpa using fr_contains (s := s) (d := 0) (by decide)
  exact hf x fun r' hr' hc => by
    rw [List.mem_singleton.mp hr'] at hc
    exact hr x hc hx

theorem bytes_keep {s : State} {p : Addr} {k : Nat}
    (hd : (frR s).Disjoint ⟨p, k⟩) (hn : p.toNat + k ≤ 2 ^ 64) :
    bytesAt (eMem s) p k = bytesAt s.mem p k := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact pushed_keep hd (Offset.contains_base _ (by omega) (by omega))

theorem addr_bound (a : BitVec 32) {k : Nat} (h : a.toNat + k ≤ 2 ^ 32) : (State.addr a).toNat + k ≤ 2 ^ 64 := by
  rw [VG.Proof.X25519.Arm.addr_toNat]; omega

/-- After the call: `f` of the arguments at `out`, and the frames as they were. -/
structure Called (n w : Nat) (f : List Byte → List Byte → List Byte) (s z : State) : Prop where
  out : bytesAt z.mem (State.addr (s.gpr .r0)) n =
    f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n)
  slot : z.mem.readW (B s) 32 = s.gpr .r0
  ra : z.mem.readW (B s + BitVec.ofNat 64 4) 32 = s.gpr .lr
  pres : ∀ r ∈ preserved, r ≠ .lr → z.gpr r = s.gpr r
  sp : z.sp = s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4
  rd : z.rd = s.rd
  wr : z.wr = ⟨B s, 4⟩ :: ⟨B s + BitVec.ofNat 64 4, 4⟩ :: s.wr

/-- The callee's entry. -/
theorem Pushed.callPre {n w : Nat} {s e : State} (h : ExPre n w s) (he : Pushed n w s e) :
    CallPre n w (e.callEntry.withRegions s.rd s.wr) := by
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, -, -, -, -, -⟩ := h
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) :
      (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr]
  simp only [CallPre, outR, scR, ptR, wsR, State.withRegions_rd, State.withRegions_wr,
    g .r0 (by simp), g .r1 (by simp), g .r2 (by simp), g .r3 (by simp)]
  exact ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩

/-- The regions the call is given are ours. -/
theorem Pushed.covers {n w : Nat} {s e : State} (he : Pushed n w s e) :
    Covers (s.rd ++ s.wr) (e.rd ++ e.wr) ∧ Covers s.wr e.wr :=
  ⟨covers_mem fun r hr => by
    rw [he.rd, he.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)),
   covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)⟩

theorem called_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} {s e : State} (h : ExPre n w s) (he : Pushed n w s e) :
    WP isa (.call name c) e (Called n w f s) := by
  have hcp := he.callPre h
  have hs := slot_sep h
  have hB := B_toNat h
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, f0, f1, f2, f3, hsp⟩ := h
  obtain ⟨hcov, hw⟩ := he.covers
  refine WP.callCalls hk.hv (hk.pre _ hcp) hcov hw (fun z rd' wr' sp' fr' pres' _ post' => ?_) hk.nf
  have hpost := hk.post _ _ post'
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2]) : (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr]
  simp only [State.withRegions_mem, State.callEntry_mem, g .r0 (by simp), g .r1 (by simp), g .r2 (by simp),
    he.mem] at hpost
  rw [bytes_keep f1 (addr_bound _ b1), bytes_keep f2 (addr_bound _ b2)] at hpost
  -- The frames, which the callee does not write.
  have hfr : ∀ {d : Nat}, d ≤ 4 → ∀ r ∈ s.wr, (⟨B s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro d hd r hr
    rw [wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fr_part f0 hd
    · exact fr_part f3 hd
  have em : e.mem.readW (B s + BitVec.ofNat 64 4) 32 = s.gpr .lr := by
    rw [he.mem, eMem, Mem.readW_writeW_sep (Region.Disjoint.sep hs.symm (Region.contains_self _ _)
      (Region.contains_self _ _)), Mem.readW_writeW_self32]
    decide
  have es : e.mem.readW (B s) 32 = s.gpr .r0 := by
    rw [he.mem, eMem, Mem.readW_writeW_self32]
  refine ⟨hpost, ?_, ?_, fun r hr hlr => ?_, sp'.trans he.sp, rd'.trans he.rd, wr'.trans he.wr⟩
  · have h0 : ∀ r ∈ s.wr, (⟨B s, 4⟩ : Region).Disjoint r := fun r hr => by
      simpa using hfr (d := 0) (by decide) r hr
    rw [Frame.readW fr' (r := ⟨B s, 4⟩) (Region.contains_self _ _) h0 (by decide)]
    exact es
  · rw [Frame.readW fr' (r := ⟨B s + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _) (hfr (by decide))
      (by decide)]
    exact em
  · rw [pres' r hr hlr, he.gpr]

/-- After the pop of `out` into `r1`. -/
structure Popped (n w : Nat) (f : List Byte → List Byte → List Byte) (s u : State) : Prop where
  out : bytesAt u.mem (State.addr (s.gpr .r0)) n =
    f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n)
  ra : u.mem.readW (B s + BitVec.ofNat 64 4) 32 = s.gpr .lr
  pres : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = s.sp - BitVec.ofNat 32 4
  rd : u.rd = s.rd
  wr : u.wr = ⟨B s + BitVec.ofNat 64 4, 4⟩ :: s.wr
  r1 : u.gpr .r1 = s.gpr .r0

theorem popped_of {n w : Nat} {f : List Byte → List Byte → List Byte} {s z : State} (h : ExPre n w s)
    (hz : Called n w f s z) : Popped n w f s (popped .r1 4 z) := by
  have hread : z.mem.readW (State.addr z.sp) 32 = s.gpr .r0 := by
    rw [hz.sp, addr44 h]
    exact hz.slot
  refine ⟨hz.out, hz.ra, fun r hr hlr => ?_, ?_, hz.rd, ?_, ?_⟩
  · rw [popped_gpr (show r ≠ .r1 by revert r; decide), hz.pres r hr hlr]
  · rw [popped_sp, hz.sp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_wr, hz.wr]; rfl
  · simp only [popped, State.setReg, ↓reduceIte, hread]

/-! ## The check -/

theorem orBytes_wp (o : BitVec 32) (m : Mem) : ∀ (i : Nat), i < 4096 → o.toNat + i ≤ 2 ^ 32 →
    ∀ (u : State) (is : List Instr) (Q : State → Prop), u.gpr .r1 = o → u.mem = m →
    (∀ j < i, InRegions (u.rd ++ u.wr) (State.addr o + BitVec.ofNat 64 j) 1) →
    (∀ u', u'.gpr .r3 = u.gpr .r3 ||| (orAll m (State.addr o) i).setWidth 32 → u'.gpr .r1 = o →
      u'.mem = m → u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp →
      (∀ r, r ≠ .r3 → r ≠ .r2 → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) →
    WP isa (.block (orBytes i ++ is)) u Q := by
  intro i
  induction i with
  | zero =>
    intro _ _ u is Q ht hm _ k
    exact k u (by simp [orAll]) ht hm rfl rfl rfl fun _ _ _ => rfl
  | succ i ih =>
    intro hi ho u is Q ht hm hin k
    rw [orBytes, List.append_assoc]
    refine ih (by omega) (by omega) u _ Q ht hm (fun j hj => hin j (by omega))
      fun u' g1 g0 gm grd gwr gsp go => ?_
    refine wp_ldrb (a := State.addr o + BitVec.ofNat 64 i) (by omega)
      (by rw [g0]; exact Arm.addr_add (by omega)) (by rw [grd, gwr]; exact hin i (by omega)) fun u₁ v₁ => ?_
    refine wp_dp (op2_reg _ _) fun u₂ v₂ => ?_
    refine k u₂ ?_ ?_ ?_ ?_ ?_ ?_ fun r h1 h2 => ?_
    · rw [v₂.gpr, dpVal, v₁.other _ (by decide), v₁.gpr, g1, gm, orAll, BitVec.setWidth_or, BitVec.or_assoc]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), g0]
    · rw [v₂.mem, v₁.mem, gm]
    · rw [v₂.rd, v₁.rd, grd]
    · rw [v₂.wr, v₁.wr, gwr]
    · rw [v₂.sp, v₁.sp, gsp]
    · rw [v₂.other r h1, v₁.other r h2, go r h1 h2]

/-- After the check. -/
structure Checked (n w : Nat) (f : List Byte → List Byte → List Byte) (s v : State) : Prop where
  popped : Popped n w f s v
  r0 : v.gpr .r0 = if orAll v.mem (State.addr (s.gpr .r0)) n = 0 then 0 else 1

theorem checked_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s u : State} (h : ExPre n w s)
    (hn : n < 4096) (hu : Popped n w f s u) : WP isa (.block (check n)) u (Checked n w f s) := by
  obtain ⟨⟨rd, wr, -, -, -, -, -, b0, -, -, -⟩, -, -, -, -, -⟩ := h
  unfold check
  refine wp_movw fun u₁ v₁ => ?_
  refine orBytes_wp (s.gpr .r0) u.mem n hn b0 u₁ _ _ (by rw [v₁.other _ (by decide), hu.r1]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hu.rd, hu.wr, wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩) fun u' g1 _ gm grd gwr gsp go => ?_
  refine wp_dp (op2_imm (by decide)) fun u₂ v₂ => wp_mov (op2_lsr (by decide)) fun u₃ v₃ =>
    wp_dp (op2_imm (by decide)) fun u₄ v₄ => WP.block_nil ?_
  have hm : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem, v₂.mem, gm]
  refine ⟨⟨?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hu.out
  · rw [hm]; exact hu.ra
  · rw [v₄.other r (by revert r; decide), v₃.other r (by revert r; decide), v₂.other r (by revert r; decide),
      go r (by revert r; decide) (by revert r; decide), v₁.other r (by revert r; decide), hu.pres r hr hlr]
  · rw [v₄.sp, v₃.sp, v₂.sp, gsp, v₁.sp, hu.sp]
  · rw [v₄.rd, v₃.rd, v₂.rd, grd, v₁.rd, hu.rd]
  · rw [v₄.wr, v₃.wr, v₂.wr, gwr, v₁.wr, hu.wr]
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), go _ (by decide) (by decide),
      v₁.other _ (by decide), hu.r1]
  · rw [v₄.gpr, dpVal, v₃.gpr, v₂.gpr, dpVal, g1, v₁.gpr, hm]
    rw [show ((0 : BitVec 16).setWidth 32) = 0 from rfl, show ∀ x : BitVec 32, 0 ||| x = x from fun x => BitVec.zero_or]
    exact result_shr32 _

/-! ## The whole function -/

theorem lr_ok {n w : Nat} {f : List Byte → List Byte → List Byte} {s v : State} (h : ExPre n w s)
    (hv : Checked n w f s v) : abiPreserved s (popped .lr 4 v) ∧ ExPost n f s (popped .lr 4 v) := by
  have hra : v.mem.readW (State.addr v.sp) 32 = s.gpr .lr := by
    rw [hv.popped.sp, addr4 h]; exact hv.popped.ra
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · by_cases hlr : r = .lr
    · subst hlr
      simp only [popped, State.setReg, ↓reduceIte, hra]
    · rw [popped_gpr hlr, hv.popped.pres r hr hlr]
  · rw [popped_sp, hv.popped.sp]; exact BitVec.sub_add_cancel _ _
  · exact hv.popped.out
  · rw [popped_gpr (r := .lr) (q := .r0) (by decide), BitVec.setWidth_eq, hv.r0]
    exact result_spec _ _ _ _ hv.popped.out

theorem exchange_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 4096) {s : State} (h : ExPre n w s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  have hsp := h.2.2.2.2.2
  refine WP.frame (rs := [.lr]) (by decide) (by simp only [List.length_singleton]; omega) (by decide) ?_
  refine WP.seq (WP.frame (rs := [.r0]) (by decide) ?_ (by decide) ?_)
  · simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := s.sp.isLt
    omega
  refine WP.mono (called_wp hk h (pushed_pushed h)) fun z hz => ?_
  exact WP.mono (checked_wp h hn (popped_of h hz)) fun v hv => lr_ok h hv

/-! ## Constant time -/

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact Taint.agree_ofRegs hr) h

theorem exchange_ct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String}
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (ExPre n w) Pub (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1.1, p₂.1.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.1.2.1, p₂.1.2.1]; simp only [outR, wsR, q0, q3]
  refine (RelCT.frame (P := Eq2 σ₁ σ₂) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The outer frame's body: the inner frame, then the check.
  refine RelCT.seq (R := fun a b => Popped n w f σ₁ a ∧ Popped n w f σ₂ b) ?_ ?_
  · intro a₁ a₂ t₁ t₂ a₁' a₂' ⟨s₁, s₂, ⟨hs₁, hs₂⟩, e₁, e₂⟩ x₁ x₂
    rw [hs₁] at e₁
    rw [hs₂] at e₂
    rw [push_pushed (by decide) (by simp only [List.length_singleton]; have := p₁.2.2.2.2.2; omega),
      Option.some.injEq] at e₁
    rw [push_pushed (by decide) (by simp only [List.length_singleton]; have := p₂.2.2.2.2.2; omega),
      Option.some.injEq] at e₂
    · subst e₁ e₂
      -- The inner frame, around the call.
      have k₁ := pushed_pushed p₁
      have k₂ := pushed_pushed p₂
      have hfr := RelCT.frame (rs := [.r0]) (r := .r1) (n := 4) (body := .call name c)
        (P := Eq2 (M := isa) (pushed [.lr] σ₁) (pushed [.lr] σ₂)) (fun a b ⟨ha, hb⟩ => by subst ha hb; simp [qsp]) ?_
      · obtain ⟨ht, -⟩ := hfr _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂
        refine ⟨ht, ?_⟩
        -- What the inner frame leaves, by the correctness proof and determinism.
        have w₁ : WP isa (.frame (.push [.r0]) (.call name c) (.pop .r1 4)) (pushed [.lr] σ₁)
            (Popped n w f σ₁) := by
          refine WP.frame (rs := [.r0]) (by decide) ?_ (by decide)
            (WP.mono (called_wp hk p₁ k₁) fun z hz => popped_of p₁ hz)
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₁.sp.isLt; have := p₁.2.2.2.2.2; omega
        have w₂ : WP isa (.frame (.push [.r0]) (.call name c) (.pop .r1 4)) (pushed [.lr] σ₂)
            (Popped n w f σ₂) := by
          refine WP.frame (rs := [.r0]) (by decide) ?_ (by decide)
            (WP.mono (called_wp hk p₂ k₂) fun z hz => popped_of p₂ hz)
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₂.sp.isLt; have := p₂.2.2.2.2.2; omega
        obtain ⟨_, y₁, ey₁, hy₁⟩ := w₁
        obtain ⟨_, y₂, ey₂, hy₂⟩ := w₂
        obtain ⟨-, rfl⟩ := Exec.det x₁ ey₁
        obtain ⟨-, rfl⟩ := Exec.det x₂ ey₂
        exact ⟨hy₁, hy₂⟩
      · intro b₁ b₂ t₁ t₂ b₁' b₂' ⟨s₁, s₂, ⟨hs₁, hs₂⟩, e₁, e₂⟩ y₁ y₂
        rw [hs₁] at e₁
        rw [hs₂] at e₂
        rw [push_pushed (by decide) (by
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₁.sp.isLt; have := p₁.2.2.2.2.2; omega), Option.some.injEq] at e₁
        rw [push_pushed (by decide) (by
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₂.sp.isLt; have := p₂.2.2.2.2.2; omega), Option.some.injEq] at e₂
        subst e₁ e₂
        refine RelCT.call hk.hv hk.hct σ₁.rd σ₁.wr (P := Eq2 (M := isa) (pushed [.r0] (pushed [.lr] σ₁))
          (pushed [.r0] (pushed [.lr] σ₂))) (fun a b ⟨ha, hb⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ y₁ y₂
        subst ha hb
        have c₂ := k₂.callPre p₂
        rw [hrd, hwr] at c₂
        have v₂ := k₂.covers
        rw [hrd, hwr] at v₂
        have g {s : State} (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) :
            ((pushed [.r0] (pushed [.lr] s)).callEntry.withRegions σ₁.rd σ₁.wr).gpr r = s.gpr r := by
          rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]; rfl
        refine ⟨hk.pre _ (k₁.callPre p₁), hk.pre _ c₂, hk.pub _ _ ?_, k₁.covers.1, k₁.covers.2, v₂.1, v₂.2⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [g _ (by simp), g _ (by simp), q0]
        · rw [g _ (by simp), g _ (by simp), q1]
        · rw [g _ (by simp), g _ (by simp), q2]
        · rw [g _ (by simp), g _ (by simp), q3]
        · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, qsp]
  -- The check.
  · intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨hu₁, hu₂⟩ x₁ x₂
    exact rel_taint [.r1] (σ₁ := u₁) (σ₂ := u₂) (by simp [hu₁.r1, hu₂.r1, q0]) ht _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂

/-! ## `Verified` -/

/-- The low word of the pair of registers the ABI returns a value in. -/
theorem ret32 (x y : BitVec 32) : (x ++ y).setWidth 32 = y := BitVec.setWidth_append_eq_right

theorem exchange_correct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 4096) :
    ∀ s, (exContract n w f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) hn h
    exact ⟨t, s', he, ha, hp⟩

end VG.Proof.Xdh.Arm
