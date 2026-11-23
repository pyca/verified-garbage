module

public import VerifiedGarbage.Impl.Xdh.Arm
public import VerifiedGarbage.Proof.Framework.Arm.ViaReg
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Xdh.Rel
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Impl.Xdh.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.ViaReg
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

open VG VG.Arm VG.Impl.Xdh.Arm VG.Arm.FrameStack
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
/-- Our frames and the `d` bytes of stack the callee uses below them. -/
abbrev frD (d : Nat) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 (8 + d), 8 + d⟩

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
def ExPre (n w d : Nat) (s : State) : Prop :=
  CallPre n w s ∧ (frD s d).Disjoint (outR n s) ∧ (frD s d).Disjoint (scR n s) ∧
    (frD s d).Disjoint (ptR n s) ∧ (frD s d).Disjoint (wsR w s) ∧ 8 + d ≤ s.sp.toNat

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in `r0`
if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem (State.addr (s.gpr .r0)) n =
      f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n) ∧
    (s'.gpr .r0).setWidth 32 =
      if f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n) =
        List.replicate n 0 then 0 else 1

/-- What two runs agree on: the pointers, and the addresses of the functions
`fns`. -/
def Pub (fns : List String) (s₁ s₂ : State) : Prop :=
  s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧ ∀ f ∈ fns, isa.fnAddr s₁ f = isa.fnAddr s₂ f

/-- The exchange function's contract on ARMv7. -/
def exContract (n w d : Nat) (fns : List String) (f : List Byte → List Byte → List Byte) : Contract isa where
  pre := ExPre n w d
  post := ExPost n f
  pub := Pub fns

/-- The callee, by its contract `k`, with `d` bytes of stack, from states
that agree on the addresses of `fns`. -/
structure Callee (n w d : Nat) (fns : List String) (f : List Byte → List Byte → List Byte) (c : Prog isa)
    (k : Contract isa) :
    Prop where
  hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  hct : ConstantTime isa k.pre k.pub c
  pre : ∀ s, CallPre n w s → d ≤ s.sp.toNat → (∀ r ∈ s.rd ++ s.wr, (belowA s.sp d).Disjoint r) → k.pre s
  post : ∀ s s', k.post s s' →
    bytesAt s'.mem (State.addr (s.gpr .r0)) n =
      f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n)
  pub : ∀ s₁ s₂, Pub fns s₁ s₂ → k.pub s₁ s₂
  st : armStack c ≤ d

/-- No byte is below `sp` within 0 bytes. -/
theorem belowA_zero_disjoint (sp : BitVec 32) (r : Region) : (belowA sp 0).Disjoint r :=
  fun _ h => absurd h (by simp only [Region.Contains]; omega)

/-- Code without frames uses no stack. -/
theorem armStack_of_noFrames : ∀ {c : Prog isa}, c.noFrames = true → armStack c = 0
  | .block _, _ => rfl
  | .seq a b, h | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [armStack, armStack_of_noFrames h.1, armStack_of_noFrames h.2, Nat.max_self]
  | .loop b _, h | .call _ b, h => by simp only [Code.noFrames] at h; simp only [armStack, armStack_of_noFrames h]
  | .icall _ _ b nx, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [armStack, armStack_of_noFrames h.1, armStack_of_noFrames h.2, Nat.max_self]
  | .frame .., h => by simp only [Code.noFrames, Bool.false_eq_true] at h

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-! ## The frames -/

section
variable {n w d : Nat} {s : State}

/-- The base of the frames. -/
abbrev B (s : State) : Addr := State.addr s.sp - BitVec.ofNat 64 8

theorem addr4 (h : ExPre n w d s) : State.addr (s.sp - BitVec.ofNat 32 4) = B s + BitVec.ofNat 64 4 := by
  have hsp := h.2.2.2.2.2
  rw [B, FrameStack.addr_sub' (by omega_using [hsp])]
  bv_omega

theorem addr44 (h : ExPre n w d s) :
    State.addr (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4) = B s := by
  have hsp := h.2.2.2.2.2
  rw [B, show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 by bv_omega,
    FrameStack.addr_sub' (by omega_using [hsp])]

theorem B_toNat (h : ExPre n w d s) : (B s).toNat + 8 ≤ 2 ^ 32 := by
  have hsp := h.2.2.2.2.2
  have e := VG.Proof.X25519.Arm.addr_toNat s.sp
  have := s.sp.isLt
  rw [B, BitVec.toNat_sub, BitVec.toNat_ofNat, e]
  omega_using [hsp]

/-- Our frames are within `frD`. -/
theorem frR_sub (d : Nat) (s : State) : Region.Sub (frR s) (frD s d) := by
  have e : State.addr s.sp - BitVec.ofNat 64 8 =
      State.addr s.sp - BitVec.ofNat 64 (8 + d) + BitVec.ofNat 64 d := by
    rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  show Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ _
  rw [e]
  exact Offset.sub_base _ (by omega_using [])

/-- What `ExPre` asks of `frD`, of our frames. -/
theorem ExPre.frs (h : ExPre n w d s) :
    (frR s).Disjoint (outR n s) ∧ (frR s).Disjoint (scR n s) ∧ (frR s).Disjoint (ptR n s) ∧
      (frR s).Disjoint (wsR w s) :=
  ⟨h.2.1.sub_left (frR_sub d s), h.2.2.1.sub_left (frR_sub d s), h.2.2.2.1.sub_left (frR_sub d s),
    h.2.2.2.2.1.sub_left (frR_sub d s)⟩

/-- The callee's `d` bytes of stack, below our frames, are within `frD`. -/
theorem room_sub (h : ExPre n w d s) : Region.Sub (belowA (s.sp - BitVec.ofNat 32 8) d) (frD s d) := by
  have hsp := h.2.2.2.2.2
  have e : State.addr (s.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 d) = State.addr s.sp - BitVec.ofNat 64 (8 + d) := by
    rw [addr_sub' (by rw [sub_toNat' (by omega_using [hsp])]; omega_using [hsp]), addr_sub' (by omega_using [hsp]),
      BitVec.sub_sub, ← BitVec.ofNat_add]
  show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 d), d⟩ _
  rw [e]
  exact Region.sub_prefix (by omega_using [])

/-- The frames' words are apart from a region apart from both. -/
theorem fr_part {r : Region} (hr : (frR s).Disjoint r) {d : Nat} (hd : d ≤ 4) :
    (⟨B s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r :=
  hr.sub_left (Offset.sub_base _ (by omega_using [hd]))

theorem slot_sep (h : ExPre n w d s) : (⟨B s, 4⟩ : Region).Disjoint ⟨B s + BitVec.ofNat 64 4, 4⟩ := by
  have := B_toNat h
  exact Offset.base_disjoint _ (k := 4) (e := 4) (by omega_using []) (by omega_using [])

theorem fr_contains {d : Nat} (hd : d ≤ 4) :
    (frR s).Contains (B s + BitVec.ofNat 64 d) 4 :=
  Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

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

theorem pushed_pushed {n w d : Nat} {s : State} (h : ExPre n w d s) :
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
  exact pushed_keep hd (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))

theorem addr_bound (a : BitVec 32) {k : Nat} (h : a.toNat + k ≤ 2 ^ 32) : (State.addr a).toNat + k ≤ 2 ^ 64 := by
  rw [VG.Proof.X25519.Arm.addr_toNat]; omega_using [h]

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
theorem Pushed.callPre {n w d : Nat} {s e : State} (h : ExPre n w d s) (he : Pushed n w s e) :
    CallPre n w (e.callEntry.withRegions s.rd s.wr) := by
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, -, -, -, -, -⟩ := h
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) :
      (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr]
  simp only [CallPre, outR, scR, ptR, wsR, State.withRegions_rd, State.withRegions_wr,
    g .r0 (by simp), g .r1 (by simp), g .r2 (by simp), g .r3 (by simp)]
  exact ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩

/-- The callee's stack is apart from the arguments. -/
theorem Pushed.room {n w d : Nat} {s e : State} (h : ExPre n w d s) (he : Pushed n w s e) :
    ∀ r ∈ (e.callEntry.withRegions s.rd s.wr).rd ++ (e.callEntry.withRegions s.rd s.wr).wr,
      (belowA (e.callEntry.withRegions s.rd s.wr).sp d).Disjoint r := by
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, he.sp,
    show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 by bv_omega]
  intro r hr
  rw [h.1.1, h.1.2.1] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.2.2.1.sub_left (room_sub h)
  · exact h.2.2.2.1.sub_left (room_sub h)
  · exact h.2.1.sub_left (room_sub h)
  · exact h.2.2.2.2.1.sub_left (room_sub h)

/-- The callee's stack is there. -/
theorem Pushed.roomSp {n w d : Nat} {s e : State} (h : ExPre n w d s) (he : Pushed n w s e) :
    d ≤ (e.callEntry.withRegions s.rd s.wr).sp.toNat := by
  have hsp := h.2.2.2.2.2
  simp only [State.withRegions_sp, State.callEntry_sp, he.sp,
    show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 by bv_omega,
    sub_toNat' (show 8 ≤ s.sp.toNat by omega_using [hsp])]
  omega_using [hsp]

/-- The regions the call is given are ours. -/
theorem Pushed.covers {n w : Nat} {s e : State} (he : Pushed n w s e) :
    Covers (s.rd ++ s.wr) (e.rd ++ e.wr) ∧ Covers s.wr e.wr :=
  ⟨covers_mem fun r hr => by
    rw [he.rd, he.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)),
   covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)⟩

theorem called_wp {n w d : Nat} {f : List Byte → List Byte → List Byte} {fns : List String} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w d fns f c k) {name : String} {s e : State} (h : ExPre n w d s) (he : Pushed n w s e) :
    WP isa (.call name c) e (Called n w f s) := by
  have hcp := he.callPre h
  have hroom := he.room h
  have hroomSp := he.roomSp h
  have hs := slot_sep h
  have hB := B_toNat h
  have hes : State.addr e.sp = B s := by rw [he.sp]; exact addr44 h
  have hesp : 8 + d ≤ s.sp.toNat := h.2.2.2.2.2
  have hen : e.sp.toNat = s.sp.toNat - 8 := by
    rw [he.sp, show s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 by bv_omega,
      sub_toNat' (by omega_using [hesp])]
  obtain ⟨f0, f1, f2, f3⟩ := h.frs
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, -, -, -, -, hsp⟩ := h
  obtain ⟨hcov, hw⟩ := he.covers
  have hd : armStack c ≤ e.sp.toNat := by have := hk.st; rw [hen]; omega_using [hesp, this]
  refine WP.callF hk.hv (hk.pre _ hcp hroomSp hroom) hcov hw (by simpa using hd) (fun z rd' wr' sp' fr' pres' post' => ?_)
  have hpost := hk.post _ _ post'
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2]) : (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr]
  simp only [State.withRegions_mem, State.callEntry_mem, g .r0 (by simp), g .r1 (by simp), g .r2 (by simp),
    he.mem] at hpost
  rw [bytes_keep f1 (addr_bound _ b1), bytes_keep f2 (addr_bound _ b2)] at hpost
  -- The frames, which the callee does not write.
  have hfr : ∀ {d' : Nat}, d' ≤ 4 → ∀ r ∈ s.wr ++ [belowA e.sp (armStack c)],
      (⟨B s + BitVec.ofNat 64 d', 4⟩ : Region).Disjoint r := by
    intro d' hd' r hr
    rcases List.mem_append.mp hr with hr | hr
    · rw [wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fr_part f0 hd'
      · exact fr_part f3 hd'
    · simp only [List.mem_singleton] at hr; subst r
      simp only [belowA]
      rw [addr_sub' hd, hes]
      exact Offset.disjoint_below _ (by have := hk.st; omega_using [hd', hesp, this])
  have em : e.mem.readW (B s + BitVec.ofNat 64 4) 32 = s.gpr .lr := by
    rw [he.mem, eMem, Mem.readW_writeW_sep (Region.Disjoint.sep hs.symm (Region.contains_self _ _)
      (Region.contains_self _ _)), Mem.readW_writeW_self32]
    decide
  have es : e.mem.readW (B s) 32 = s.gpr .r0 := by
    rw [he.mem, eMem, Mem.readW_writeW_self32]
  refine ⟨hpost, ?_, ?_, fun r hr hlr => ?_, sp'.trans he.sp, rd'.trans he.rd, wr'.trans he.wr⟩
  · have h0 : ∀ r ∈ s.wr ++ [belowA e.sp (armStack c)], (⟨B s, 4⟩ : Region).Disjoint r := fun r hr => by
      simpa using hfr (d' := 0) (by decide) r hr
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

/-- The bytes of a region apart from a released frame are what they were. -/
theorem bytes_lost {F : Region} {m m' : Mem} (hf : Frame [F] m m') {p : Addr} {k : Nat}
    (hd : (⟨p, k⟩ : Region).Disjoint F) : bytesAt m' p k = bytesAt m p k := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => lost_byte hf hd (List.mem_range.mp hi)

/-- The output is apart from the frames' two words. -/
theorem out_apart {n w d : Nat} {s : State} (h : ExPre n w d s) :
    (outR n s).Disjoint ⟨B s, 4⟩ ∧ (outR n s).Disjoint ⟨B s + BitVec.ofNat 64 4, 4⟩ :=
  ⟨(h.frs.1.sub_left (Region.sub_prefix (by decide))).symm,
    (h.frs.1.sub_left (Offset.sub_base _ (by decide))).symm⟩

theorem popped_of {n w d : Nat} {f : List Byte → List Byte → List Byte} {s z : State} (h : ExPre n w d s)
    (hz : Called n w f s z) {m : Mem} {u : Nat → BitVec 32} (hm : Frame [⟨B s, 4⟩] z.mem m) :
    Popped n w f s { popped .r1 4 z with mem := m, unknowns := u } := by
  have hread : z.mem.readW (State.addr z.sp) 32 = s.gpr .r0 := by
    rw [hz.sp, addr44 h]
    exact hz.slot
  refine ⟨?_, ?_, fun r hr hlr => ?_, ?_, hz.rd, ?_, ?_⟩ <;> dsimp only
  · rw [bytes_lost hm (out_apart h).1]; exact hz.out
  · rw [hm.readW (r := ⟨B s + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
    exact hz.ra
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
    refine ih (by omega_using [hi]) (by omega_using [ho]) u _ Q ht hm (fun j hj => hin j (by omega_using [hj]))
      fun u' g1 g0 gm grd gwr gsp go => ?_
    refine wp_ldrb (a := State.addr o + BitVec.ofNat 64 i) (by omega_using [hi])
      (by rw [g0]; exact Arm.addr_add (by omega_using [ho])) (by rw [grd, gwr]; exact hin i (by omega_using [])) fun u₁ v₁ => ?_
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

theorem checked_wp {n w d : Nat} {f : List Byte → List Byte → List Byte} {s u : State} (h : ExPre n w d s)
    (hn : n < 4096) (hu : Popped n w f s u) : WP isa (.block (check n)) u (Checked n w f s) := by
  obtain ⟨⟨rd, wr, -, -, -, -, -, b0, -, -, -⟩, -, -, -, -, -⟩ := h
  unfold check
  refine wp_movw fun u₁ v₁ => ?_
  refine orBytes_wp (s.gpr .r0) u.mem n hn b0 u₁ _ _ (by rw [v₁.other _ (by decide), hu.r1]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hu.rd, hu.wr, wr]; simp,
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hn, hj])⟩) fun u' g1 _ gm grd gwr gsp go => ?_
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

theorem lr_ok {n w d : Nat} {f : List Byte → List Byte → List Byte} {s v : State} (h : ExPre n w d s)
    (hv : Checked n w f s v) {m : Mem} {u : Nat → BitVec 32} (hm : Frame [⟨B s + BitVec.ofNat 64 4, 4⟩] v.mem m) :
    abiPreserved s { popped .lr 4 v with mem := m, unknowns := u } ∧
      ExPost n f s { popped .lr 4 v with mem := m, unknowns := u } := by
  have hra : v.mem.readW (State.addr v.sp) 32 = s.gpr .lr := by
    rw [hv.popped.sp, addr4 h]; exact hv.popped.ra
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only
  · by_cases hlr : r = .lr
    · subst hlr
      simp only [popped, State.setReg, ↓reduceIte, hra]
    · rw [popped_gpr hlr, hv.popped.pres r hr hlr]
  · rw [popped_sp, hv.popped.sp]; exact BitVec.sub_add_cancel _ _
  · rw [bytes_lost hm (out_apart h).2]; exact hv.popped.out
  · rw [popped_gpr (r := .lr) (q := .r0) (by decide), BitVec.setWidth_eq, hv.r0]
    exact result_spec _ _ _ _ hv.popped.out

theorem exchange_wp {n w d : Nat} {f : List Byte → List Byte → List Byte} {fns : List String} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w d fns f c k) {name : String} (hn : n < 4096) {s : State} (h : ExPre n w d s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  have hsp := h.2.2.2.2.2
  refine WP.frame (rs := [.lr]) (by decide) (by simp only [List.length_singleton]; omega_using [hsp]) (by decide) ?_
  refine WP.seq (WP.frame (rs := [.r0]) (by decide) ?_ (by decide) ?_)
  · simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := s.sp.isLt
    omega_using [hsp]
  refine WP.mono (called_wp hk h (pushed_pushed h)) fun z hz m u hm => ?_
  change Frame [⟨State.addr (s.sp - BitVec.ofNat 32 4 - BitVec.ofNat 32 4), 4⟩] z.mem m at hm
  rw [addr44 h] at hm
  refine WP.mono (checked_wp h hn (popped_of h hz hm)) fun v hv m' u' hm' => ?_
  change Frame [⟨State.addr (s.sp - BitVec.ofNat 32 4), 4⟩] v.mem m' at hm'
  rw [addr4 h] at hm'
  exact lr_ok h hv hm'

/-! ## Constant time -/

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact Taint.agree_ofRegs hr) h

theorem exchange_ct {n w d : Nat} {f : List Byte → List Byte → List Byte} {fns : List String} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w d fns f c k) {name : String}
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (ExPre n w d) (Pub fns) (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp, qf⟩ := hq
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1.1, p₂.1.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.1.2.1, p₂.1.2.1]; simp only [outR, wsR, q0, q3]
  refine (RelCT.frame (P := Eq2 σ₁ σ₂) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The outer frame's body: the inner frame, then the check.
  refine RelCT.seq (R := fun a b => Popped n w f σ₁ a ∧ Popped n w f σ₂ b) ?_ ?_
  · intro a₁ a₂ t₁ t₂ a₁' a₂' ⟨s₁, s₂, ⟨hs₁, hs₂⟩, e₁, e₂⟩ x₁ x₂
    rw [hs₁] at e₁
    rw [hs₂] at e₂
    rw [push_pushed (by decide) (by simp only [List.length_singleton]; have := p₁.2.2.2.2.2; omega_using [this]),
      Option.some.injEq] at e₁
    rw [push_pushed (by decide) (by simp only [List.length_singleton]; have := p₂.2.2.2.2.2; omega_using [this]),
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
            (WP.mono (called_wp hk p₁ k₁) fun z hz m u hm => popped_of p₁ hz (by
              change Frame [⟨State.addr (_ - BitVec.ofNat 32 4 - BitVec.ofNat 32 4), 4⟩] z.mem m at hm
              rw [addr44 p₁] at hm; exact hm))
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₁.sp.isLt; have := p₁.2.2.2.2.2; omega_using [this]
        have w₂ : WP isa (.frame (.push [.r0]) (.call name c) (.pop .r1 4)) (pushed [.lr] σ₂)
            (Popped n w f σ₂) := by
          refine WP.frame (rs := [.r0]) (by decide) ?_ (by decide)
            (WP.mono (called_wp hk p₂ k₂) fun z hz m u hm => popped_of p₂ hz (by
              change Frame [⟨State.addr (_ - BitVec.ofNat 32 4 - BitVec.ofNat 32 4), 4⟩] z.mem m at hm
              rw [addr44 p₂] at hm; exact hm))
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₂.sp.isLt; have := p₂.2.2.2.2.2; omega_using [this]
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
          have := σ₁.sp.isLt; have := p₁.2.2.2.2.2; omega_using [this]), Option.some.injEq] at e₁
        rw [push_pushed (by decide) (by
          simp only [pushed_sp, List.length_singleton, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have := σ₂.sp.isLt; have := p₂.2.2.2.2.2; omega_using [this]), Option.some.injEq] at e₂
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
        have r₂ := k₂.room p₂
        rw [hrd, hwr] at r₂
        have q₂ := k₂.roomSp p₂
        rw [hrd, hwr] at q₂
        refine ⟨hk.pre _ (k₁.callPre p₁) (k₁.roomSp p₁) (k₁.room p₁), hk.pre _ c₂ q₂ r₂, hk.pub _ _ ?_, k₁.covers.1, k₁.covers.2, v₂.1, v₂.2⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [g _ (by simp), g _ (by simp), q0]
        · rw [g _ (by simp), g _ (by simp), q1]
        · rw [g _ (by simp), g _ (by simp), q2]
        · rw [g _ (by simp), g _ (by simp), q3]
        · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, qsp]
        · exact qf
  -- The check.
  · intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨hu₁, hu₂⟩ x₁ x₂
    exact rel_taint [.r1] (σ₁ := u₁) (σ₂ := u₂) (by simp [hu₁.r1, hu₂.r1, q0]) ht _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂

/-! ## `Verified` -/

/-- The low word of the pair of registers the ABI returns a value in. -/
theorem ret32 (x y : BitVec 32) : (x ++ y).setWidth 32 = y := BitVec.setWidth_append_eq_right

theorem exchange_correct {n w d : Nat} {f : List Byte → List Byte → List Byte} {fns : List String} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w d fns f c k) {name : String} (hn : n < 4096) :
    ∀ s, (exContract n w d fns f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w d fns f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) hn h
    exact ⟨t, s', he, ha, hp⟩

/-! ## A callee that calls a function by its address in `r10`

`entryReg fn .r10 name c'` saves `r10` and `lr` in a frame of 8 bytes,
puts `fn`'s address in `r10` and calls `c'`, `c` made to call `fn` by it
(`Code.viaRegAt`), with the arguments as they came: from a callee `c` of the
exchange, it is one, with 8 bytes of stack, for runs that agree on `fn`'s
address (`Callee.entryReg`). -/

section Entry

open VG.Proof.Arm VG.Impl.Arm

/-- What the entry needs: the callee's needs, and 8 bytes of stack apart
from the arguments. -/
def EntryPre (n w : Nat) (s : State) : Prop :=
  CallPre n w s ∧ 8 ≤ s.sp.toNat ∧ ∀ r ∈ s.rd ++ s.wr, (belowA s.sp 8).Disjoint r

/-- The entry's contract: `f` of the scalar and the point at `out`. -/
def entryContract (n w : Nat) (fns : List String) (f : List Byte → List Byte → List Byte) : Contract isa where
  pre := EntryPre n w
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) n =
    f (bytesAt s.mem (State.addr (s.gpr .r1)) n) (bytesAt s.mem (State.addr (s.gpr .r2)) n)
  pub := Pub fns

/-- `CallPre` reads only the argument registers and the regions. -/
theorem CallPre.of_eq {n w : Nat} {s t : State} (h : CallPre n w s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hg : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], t.gpr r = s.gpr r) : CallPre n w t := by
  obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
  simp only [CallPre, outR, scR, ptR, wsR, hrd, hwr, hg .r0 (by simp), hg .r1 (by simp), hg .r2 (by simp),
    hg .r3 (by simp)]
  exact ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩

/-- The state the call starts in: the frame pushed and `fn`'s address in `r10`. -/
abbrev eTwo (fn : String) (s : State) : State := (pushed [.r10, .lr] s).setReg .r10 (s.syms fn)

/-- The frame's region. -/
abbrev eFr (s : State) : Region := belowA s.sp 8

theorem eTwo_gpr (fn : String) (s : State) {r : Reg} (h : r ≠ .r10) : (eTwo fn s).gpr r = s.gpr r := by
  simp only [eTwo, State.setReg, h, ↓reduceIte, pushed_gpr]

theorem eTwo_mem (fn : String) (s : State) :
    (eTwo fn s).mem = (s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 8)) (s.gpr .r10)).writeW
      (State.addr (s.sp - BitVec.ofNat 32 8 + 4)) (s.gpr .lr) := rfl

theorem eTwo_sp (fn : String) (s : State) : (eTwo fn s).sp = s.sp - BitVec.ofNat 32 8 := rfl

theorem eTwo_wr (fn : String) (s : State) : (eTwo fn s).wr = eFr s :: s.wr := rfl

theorem eTwo_rd (fn : String) (s : State) : (eTwo fn s).rd = s.rd := rfl

/-- The entry state of the call. -/
abbrev eCall (fn : String) (s : State) : State := (eTwo fn s).callEntry.withRegions s.rd s.wr

theorem eCall_gpr (fn : String) (s : State) {r : Reg} (h : r ∉ linkRegs) (h10 : r ≠ .r10) :
    (eCall fn s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h, eTwo_gpr fn s h10]

theorem eCall_regAt (fn : String) (s : State) : RegAt fn .r10 (eCall fn s) := by
  unfold RegAt
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  simp only [eTwo, State.setReg, ↓reduceIte]
  rfl

theorem eCall_callPre {n w : Nat} (fn : String) {s : State} (h : CallPre n w s) : CallPre n w (eCall fn s) :=
  h.of_eq rfl rfl fun r hr => eCall_gpr fn s (by revert r; decide) (by revert r; decide)

/-- The frame's two words, and the frame apart from a region apart from it. -/
theorem eFr_words {s : State} (hsp : 8 ≤ s.sp.toNat) :
    State.addr (s.sp - BitVec.ofNat 32 8 + 4) = State.addr (s.sp - BitVec.ofNat 32 8) + BitVec.ofNat 64 4 ∧
      (⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩ : Region).Disjoint
        ⟨State.addr (s.sp - BitVec.ofNat 32 8) + BitVec.ofNat 64 4, 4⟩ := by
  have hs := sub_toNat' (sp := s.sp) hsp
  have := s.sp.isLt
  exact ⟨Arm.addr_add (by rw [hs]; omega_using [hsp]), Offset.base_disjoint _ (k := 4) (e := 4) (by omega_using [])
    (by omega_using [])⟩

theorem eFr_sub (s : State) {d : Nat} (hd : d ≤ 4) :
    Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 8) + BitVec.ofNat 64 d, 4⟩ (eFr s) :=
  Offset.sub_base _ (by omega_using [hd])

theorem Callee.entry_wp {n w : Nat} {fn name : String} {f : List Byte → List Byte → List Byte} {c : Prog isa}
    {k : Contract isa} (hk : Callee n w 0 [] f c k) (hn : c.noFrames = true) (hr : KeepsReg .r10 c) {s : State}
    (h : EntryPre n w s) :
    WP isa (entryReg fn .r10 name (Code.viaRegAt fn .r10 c)) s fun z =>
      abiPreserved s z ∧ (entryContract n w [fn] f).post s z := by
  obtain ⟨hcp, hsp, hroom⟩ := h
  obtain ⟨wd, wsep⟩ := eFr_words hsp
  have hfr : ∀ {d : Nat}, d ≤ 4 → ∀ r ∈ s.wr,
      (⟨State.addr (s.sp - BitVec.ofNat 32 8) + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r :=
    fun hd r hr' => fun a ha hb => hroom r (List.mem_append_right _ hr') a (eFr_sub s hd a ha) hb
  have hv' := Exec.viaRegAt_ok (n := fn) hk.hv hr
  refine WP.frame (rs := [.r10, .lr]) (r := .r10) (by decide) (by simpa using hsp) (by decide) ?_
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons (s' := eTwo fn s) rfl (WP.block_nil ?_))
  refine WP.seq (WP.callCalls hv' ⟨hk.pre _ (eCall_callPre fn hcp) (Nat.zero_le _)
      (fun r _ => belowA_zero_disjoint _ r), eCall_regAt fn s⟩
    (covers_mem fun r hr' => by
      rw [eTwo_rd, eTwo_wr]
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact List.mem_append_left _ hr'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr'))
    (covers_mem fun r hr' => by rw [eTwo_wr]; exact List.mem_cons_of_mem _ hr')
    (fun z rd' wr' sp' fr' pres' _ post' => ?_) (by rw [noFrames_viaRegAt]; exact hn))
  -- The frame's words, which the call does not write.
  have zlr : z.mem.readW (State.addr (z.sp + BitVec.ofNat 32 4)) 32 = s.gpr .lr := by
    rw [sp', eTwo_sp, show s.sp - BitVec.ofNat 32 8 + BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 + 4 from rfl, wd,
      Frame.readW fr' (r := ⟨State.addr (s.sp - BitVec.ofNat 32 8) + BitVec.ofNat 64 4, 4⟩)
        (Region.contains_self _ _) (hfr (by decide)) (by decide), eTwo_mem, wd, Mem.readW_writeW_self32]
  have zr10 : z.mem.readW (State.addr (s.sp - BitVec.ofNat 32 8)) 32 = s.gpr .r10 := by
    have h0 := hfr (d := 0) (by decide)
    simp only [BitVec.add_zero] at h0
    rw [Frame.readW fr' (r := ⟨State.addr (s.sp - BitVec.ofNat 32 8), 4⟩) (Region.contains_self _ _) h0 (by decide),
      eTwo_mem, wd, Mem.readW_writeW_sep (Region.Disjoint.sep wsep (Region.contains_self _ _)
        (Region.contains_self _ _)), Mem.readW_writeW_self32]
    all_goals decide
  have hin : InRegions (z.rd ++ z.wr) (State.addr (z.sp + BitVec.ofNat 32 4)) 4 := by
    refine ⟨eFr s, by rw [wr', eTwo_wr]; simp, ?_⟩
    rw [sp', eTwo_sp, show s.sp - BitVec.ofNat 32 8 + BitVec.ofNat 32 4 = s.sp - BitVec.ofNat 32 8 + 4 from rfl, wd]
    exact Offset.contains_base _ (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.cons (s' := z.setReg .lr (z.mem.readW (State.addr (z.sp + BitVec.ofNat 32 4)) 32))
    (by simp only [exec, show (4 : Nat) < 4096 by decide, ite_true, State.load32, hin, Option.map_some]) (WP.block_nil ?_)
  intro m u hm
  -- The bytes at `out`, apart from the frame.
  have hout : (outR n s).Disjoint (eFr s) := fun a ha hb => hroom _ (by
    obtain ⟨-, wr, -⟩ := hcp; simp [wr]) a hb ha
  have hpost := hk.post _ _ post'
  simp only [State.withRegions_mem, State.callEntry_mem, eCall_gpr fn s (r := .r0) (by decide) (by decide),
    eCall_gpr fn s (r := .r1) (by decide) (by decide), eCall_gpr fn s (r := .r2) (by decide) (by decide)] at hpost
  have hpf : Frame [eFr s] s.mem (eTwo fn s).mem := by
    have := storeWords_frame [s.gpr .r10, s.gpr .lr] s.mem (s.sp - BitVec.ofNat 32 8)
      (by rw [sub_toNat' hsp]; have := s.sp.isLt; simp; omega_using [hsp])
    exact this
  have hsc : (scR n s).Disjoint (eFr s) := fun a ha hb => hroom _ (by
    obtain ⟨rd, -⟩ := hcp; simp [rd]) a hb ha
  have hpt : (ptR n s).Disjoint (eFr s) := fun a ha hb => hroom _ (by
    obtain ⟨rd, -⟩ := hcp; simp [rd]) a hb ha
  rw [bytes_lost hpf hsc, bytes_lost hpf hpt] at hpost
  refine ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩ <;> dsimp only
  · by_cases h10 : r = .r10
    · subst h10
      simp only [popped, State.setReg, ↓reduceIte, sp']
      exact zr10
    · rw [popped_gpr h10]
      by_cases hl : r = .lr
      · subst hl; simp only [State.setReg, ↓reduceIte]; exact zlr
      · simp only [State.setReg, hl, ↓reduceIte]
        rw [pres' r hr' hl, eTwo_gpr fn s h10]
  · simp only [popped_sp, State.setReg, sp', pushed_sp, List.length_cons, List.length_nil]
    exact BitVec.sub_add_cancel _ _
  · change bytesAt m _ n = _
    rw [bytes_lost (F := eFr s) (by simpa [State.setReg] using hm) hout]
    exact hpost

theorem syms_of_fnAddr {s₁ s₂ : State} {f : String} (h : isa.fnAddr s₁ f = isa.fnAddr s₂ f) :
    s₁.syms f = s₂.syms f := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at e
  have := (s₁.syms f).isLt
  have := (s₂.syms f).isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e

/-- `ldr t, [sp, #off]` leaks the same from states whose stack pointers agree. -/
theorem ldrSp_rel {P : State → State → Prop} {t : Reg} {off : Nat} (h : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) TT := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
  cases e₂ with
  | block h₂ =>
  simp only [execBlock] at h₁ h₂
  split at h₁ <;> [cases h₁; skip]
  split at h₂ <;> [cases h₂; skip]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
  rw [← h₁.2, ← h₂.2]
  exact ⟨by simp only [addrs, h _ _ hp], trivial⟩

theorem Callee.entry_ct {n w : Nat} {fn name : String} {f : List Byte → List Byte → List Byte} {c : Prog isa}
    {k : Contract isa} (hk : Callee n w 0 [] f c k) (hc : Code.icallFree c = true) (hr : KeepsReg .r10 c) :
    ConstantTime isa (EntryPre n w) (Pub [fn]) (entryReg fn .r10 name (Code.viaRegAt fn .r10 c)) := by
  have hv' := Exec.viaRegAt_ok (n := fn) hk.hv hr
  have hct' := ConstantTime.viaRegAt (n := fn) hk.hct hc hr
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp, qf⟩ := hq
  have hy : σ₁.syms fn = σ₂.syms fn := syms_of_fnAddr (qf fn (List.mem_singleton_self _))
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1.1, p₂.1.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.1.2.1, p₂.1.2.1]; simp only [outR, wsR, q0, q3]
  refine (RelCT.frame (P := Eq2 σ₁ σ₂) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  refine RelCT.seq (R := fun a b => a = eTwo fn σ₁ ∧ b = eTwo fn σ₂) ?_ ?_
  · intro a₁ a₂ t₁ t₂ a₁' a₂' ⟨s₁, s₂, ⟨hs₁, hs₂⟩, e₁, e₂⟩ x₁ x₂
    rw [hs₁] at e₁
    rw [hs₂] at e₂
    rw [push_pushed (by decide) (by simpa using p₁.2.1), Option.some.injEq] at e₁
    rw [push_pushed (by decide) (by simpa using p₂.2.1), Option.some.injEq] at e₂
    subst e₁ e₂
    cases x₁ with
    | block h₁ =>
    cases x₂ with
    | block h₂ =>
    rw [show execBlock isa [.adrSym .r10 fn] (pushed [.r10, .lr] σ₁) = some (eTwo fn σ₁, []) from rfl,
      Option.some.injEq, Prod.mk.injEq] at h₁
    rw [show execBlock isa [.adrSym .r10 fn] (pushed [.r10, .lr] σ₂) = some (eTwo fn σ₂, []) from rfl,
      Option.some.injEq, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₁
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨rfl, rfl, rfl⟩
  refine RelCT.seq (R := fun (a b : State) => a.sp = b.sp) ?_ (ldrSp_rel fun _ _ h => h)
  intro a₁ a₂ t₁ t₂ a₁' a₂' ⟨ha₁, ha₂⟩ x₁ x₂
  subst ha₁ ha₂
  have c₂ := eCall_callPre fn p₂.1
  have hcall := RelCT.call (n := name) hv' hct' σ₁.rd σ₁.wr (P := Eq2 (M := isa) (eTwo fn σ₁) (eTwo fn σ₂))
    (fun a b ⟨ha, hb⟩ => by
      subst ha hb
      have e₂ : (eTwo fn σ₂).callEntry.withRegions σ₁.rd σ₁.wr = eCall fn σ₂ := by
        simp only [eCall, hrd, hwr]
      rw [e₂]
      refine ⟨⟨hk.pre _ (eCall_callPre fn p₁.1) (Nat.zero_le _) (fun r _ => belowA_zero_disjoint _ r),
          eCall_regAt fn σ₁⟩,
        ⟨hk.pre _ c₂ (Nat.zero_le _) (fun r _ => belowA_zero_disjoint _ r), eCall_regAt fn σ₂⟩,
        ⟨hk.pub _ _ ⟨?_, ?_, ?_, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩, hy⟩, ?_, ?_, ?_, ?_⟩
      · rw [eCall_gpr fn σ₁ (by decide) (by decide), eCall_gpr fn σ₂ (by decide) (by decide), q0]
      · rw [eCall_gpr fn σ₁ (by decide) (by decide), eCall_gpr fn σ₂ (by decide) (by decide), q1]
      · rw [eCall_gpr fn σ₁ (by decide) (by decide), eCall_gpr fn σ₂ (by decide) (by decide), q2]
      · rw [eCall_gpr fn σ₁ (by decide) (by decide), eCall_gpr fn σ₂ (by decide) (by decide), q3]
      · simp only [eCall, State.withRegions_sp, State.callEntry_sp, eTwo_sp, qsp]
      all_goals refine covers_mem fun r hr' => ?_
      all_goals first
        | (rw [eTwo_rd, eTwo_wr]
           rcases List.mem_append.mp hr' with hr' | hr'
           · exact List.mem_append_left _ hr'
           · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr'))
        | (rw [eTwo_wr]; exact List.mem_cons_of_mem _ hr')
        | (rw [eTwo_rd, eTwo_wr, hrd, hwr]
           rcases List.mem_append.mp hr' with hr' | hr'
           · exact List.mem_append_left _ hr'
           · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr'))
        | (rw [eTwo_wr, hwr]; exact List.mem_cons_of_mem _ hr'))
  obtain ⟨ht, -⟩ := hcall _ _ _ _ _ _ ⟨rfl, rfl⟩ x₁ x₂
  refine ⟨ht, ?_⟩
  show a₁'.sp = a₂'.sp
  rw [Exec.sp x₁, Exec.sp x₂, eTwo_sp, eTwo_sp, qsp]

/-- **`entryReg` of a callee of the exchange, made to call `fn` by `r10`, is
one**, with 8 bytes of stack, for runs that agree on `fn`'s address. -/
theorem Callee.entryReg {n w : Nat} {fn name : String} {f : List Byte → List Byte → List Byte} {c : Prog isa}
    {k : Contract isa} (hk : Callee n w 0 [] f c k) (hn : c.noFrames = true) (hc : Code.icallFree c = true)
    (hr : KeepsReg .r10 c) :
    Callee n w 8 [fn] f (entryReg fn .r10 name (Code.viaRegAt fn .r10 c)) (entryContract n w [fn] f) where
  hv s h := by
    obtain ⟨t, s', e, ha, hp⟩ := hk.entry_wp (fn := fn) (name := name) hn hr h
    exact ⟨t, s', e, ha, hp⟩
  hct := hk.entry_ct hc hr
  pre s h hsp hroom := ⟨h, hsp, hroom⟩
  post _ _ h := h
  pub _ _ h := h
  st := by
    unfold Impl.Arm.entryReg
    simp only [armStack, armStack_of_noFrames (show (Code.viaRegAt fn .r10 c).noFrames = true by
      rw [noFrames_viaRegAt]; exact hn), List.length_cons, List.length_nil]
    decide

end Entry

end VG.Proof.Xdh.Arm
