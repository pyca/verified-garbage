module

public import VerifiedGarbage.Impl.Xdh.RISCV64
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Impl.Xdh.RISCV64
meta import VerifiedGarbage.Proof.Xdh.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT

/-!
# X25519 and X448 exchange, with RFC 7748's check, on RISC-V

Untrusted: everything here is checked by Lean. For any callee `c` whose
contract `k` its proof gives (`Callee`): what a call of it needs at its entry
(`CallPre`, the registers and regions of `vg_x25519(out = a0, scalar = a1,
point = a2, scratch = a3)` with `n`-byte arguments and `w` bytes of working
space) gives `k.pre`, and `k.post` the `n` bytes it writes to `out`.
`Impl.Xdh.RISCV64.exchange` then pushes a frame of 16 bytes at `B = sp - 16`,
which keeps the return address at `B + 8`, stores `out` at `B` (`saved_wp`),
calls `c` with its arguments as they came (`called_wp`), which writes
neither, loads `out` back (`restored_wp`) and ORs the `n` bytes there into
`t1` (`orBytes_wp`), whose comparison with zero is the result
(`exchange_wp`). Two runs whose pointers agree (`Pub`) leak the same trace
(`exchange_ct`): the push and pop are at the stack pointer, the call is
constant time by `k`, and the check's addresses are `out`'s, given the taint
analysis of the check (`check n` from `t0`).
-/

@[expose] public section

namespace VG.Proof.Xdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Xdh.RISCV64
open VG.Spec.X25519 (bytesAt)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint ct_of)

section
variable (n w : Nat) (s : State)

/-- The regions of the arguments, and our frame. -/
abbrev outR : Region := ⟨s.gpr .a0, n⟩
abbrev scR : Region := ⟨s.gpr .a1, n⟩
abbrev ptR : Region := ⟨s.gpr .a2, n⟩
abbrev wsR : Region := ⟨s.gpr .a3, w⟩
abbrev frR : Region := ⟨s.sp - 16, 16⟩

end

/-- What the callee needs at its entry. -/
def CallPre (n w : Nat) (s : State) : Prop :=
  s.rd = [scR n s, ptR n s] ∧ s.wr = [outR n s, wsR w s] ∧
    (outR n s).Disjoint (scR n s) ∧ (outR n s).Disjoint (ptR n s) ∧ (outR n s).Disjoint (wsR w s) ∧
    (scR n s).Disjoint (wsR w s) ∧ (ptR n s).Disjoint (wsR w s) ∧
    (s.gpr .a0).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + n ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + w ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0

/-- What the exchange function needs: the callee's needs, and room for the
frame, apart from the arguments. -/
def ExPre (n w : Nat) (s : State) : Prop :=
  CallPre n w s ∧ (frR s).Disjoint (outR n s) ∧ (frR s).Disjoint (scR n s) ∧
    (frR s).Disjoint (ptR n s) ∧ (frR s).Disjoint (wsR w s) ∧ 16 ≤ s.sp.toNat

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in the
low word of `a0` if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem (s.gpr .a0) n = f (bytesAt s.mem (s.gpr .a1) n) (bytesAt s.mem (s.gpr .a2) n) ∧
    (s'.gpr .a0).setWidth 32 =
      if f (bytesAt s.mem (s.gpr .a1) n) (bytesAt s.mem (s.gpr .a2) n) = List.replicate n 0 then 0 else 1

/-- What two runs agree on: the pointers. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- The exchange function's contract on RISC-V. -/
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
    bytesAt s'.mem (s.gpr .a0) n = f (bytesAt s.mem (s.gpr .a1) n) (bytesAt s.mem (s.gpr .a2) n)
  pub : ∀ s₁ s₂, Pub s₁ s₂ → k.pub s₁ s₂
  nf : c.noFrames = true

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-! ## The frame -/

section
variable {n w : Nat} {s : State}

/-- The frame's base, and the stack pointer above it. -/
theorem sp_eq (h : ExPre n w s) : (s.sp - 16).toNat + 16 = s.sp.toNat := by
  have := h.2.2.2.2.2
  rw [BitVec.toNat_sub, show (16 : Addr).toNat = 16 from rfl]
  omega

theorem fr_al (h : ExPre n w s) : (s.sp - 16).toNat % 16 = 0 := by
  have e := sp_eq h
  have := h.1.2.2.2.2.2.2.2.2.2.2.2.2
  omega

/-- The 8 bytes at `B + d`, for `d` 0 or 8, are the frame's. -/
theorem fr_contains {d : Nat} (hd : d ≤ 8) :
    (frR s).Contains (s.sp - 16 + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ (by omega) (by omega)

theorem slot_sep (h : ExPre n w s) :
    (⟨s.sp - 16, 8⟩ : Region).Disjoint ⟨s.sp - 16 + 8, 8⟩ := by
  have e := sp_eq h
  exact Offset.base_disjoint _ (k := 8) (e := 8) (by omega) (by omega)

/-- A part of the frame is apart from a region apart from the frame. -/
theorem fr_part {r : Region} (hr : (frR s).Disjoint r) {d : Nat} (hd : d ≤ 8) :
    (⟨s.sp - 16 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r :=
  hr.sub_left (Offset.sub_base _ (by omega))

end

/-! ## The phases -/

/-- After `out` is saved: the frame holds `out` at `B` and the return
address at `B + 8`. -/
structure Saved (n w : Nat) (s e : State) : Prop where
  mem : e.mem = (s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra)).writeW (s.sp - 16) (s.gpr .a0)
  gpr : ∀ r, r ≠ .t0 → e.gpr r = s.gpr r
  sp : e.sp = s.sp - 16
  rd : e.rd = s.rd
  wr : e.wr = frR s :: s.wr

theorem saved_wp {n w : Nat} {s : State} (h : ExPre n w s) :
    WP isa (.block save) (pushed .ra s) (Saved n w s) := by
  unfold save
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine wp_sd (a := s.sp - 16) (by decide) (by rw [v₁.gpr]; simp [pushed]) (by have := fr_al h; omega)
    ⟨frR s, by rw [v₁.wr]; exact List.mem_cons_self .., by
      simpa using fr_contains (s := s) (d := 0) (by decide)⟩ fun u₂ v₂ => WP.block_nil ?_
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [v₂.mem, v₁.mem, v₁.other _ (by decide)]; rfl
  · rw [v₂.gpr, v₁.other r hr]; rfl
  · rw [v₂.sp, v₁.sp]; rfl
  · rw [v₂.rd, v₁.rd]; rfl
  · rw [v₂.wr, v₁.wr]; rfl

/-- The memory the push and the save leave outside the frame. -/
theorem saved_keep {s : State} {r : Region} (hr : (frR s).Disjoint r) {x : Addr}
    (hx : r.Contains x 1) :
    ((s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra)).writeW (s.sp - 16) (s.gpr .a0)) x = s.mem x := by
  have hf : Frame [frR s] s.mem ((s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra)).writeW (s.sp - 16) (s.gpr .a0)) := by
    refine ((Frame.refl _ _).write (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
    · simp only [Region.Contains]
      rw [show s.sp - 16 + 8 - (s.sp - 16) = 8 from by bv_omega]
      decide
    · simp only [Region.Contains, BitVec.sub_self]
      decide
  exact hf x fun r' hr' hc => by
    rw [List.mem_singleton.mp hr'] at hc
    exact hr x hc hx

/-- After the call: `f` of the arguments at `out`, and the frame as it was. -/
structure Called (n w : Nat) (f : List Byte → List Byte → List Byte) (s z : State) : Prop where
  out : bytesAt z.mem (s.gpr .a0) n = f (bytesAt s.mem (s.gpr .a1) n) (bytesAt s.mem (s.gpr .a2) n)
  slot : z.mem.readW (s.sp - 16) 64 = s.gpr .a0
  ra : z.mem.read (s.sp - 16 + 8) 8 = s.gpr .ra
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = s.sp - 16
  rd : z.rd = s.rd
  wr : z.wr = frR s :: s.wr

/-- The callee's entry. -/
theorem Saved.callPre {n w : Nat} {s e : State} (h : ExPre n w s) (he : Saved n w s e) :
    CallPre n w (e.callEntry.withRegions s.rd s.wr) := by
  have hal := fr_al h
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, -⟩, -, -, -, -, -⟩ := h
  have g (r : Reg) (hr : r ∈ [Reg.a0, .a1, .a2, .a3]) :
      (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide),
      he.gpr r (by revert r; decide)]
  simp only [CallPre, outR, scR, ptR, wsR, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, he.sp, g .a0 (by simp), g .a1 (by simp), g .a2 (by simp), g .a3 (by simp)]
  exact ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, hal⟩

/-- The regions the call is given are ours. -/
theorem Saved.covers {n w : Nat} {s e : State} (he : Saved n w s e) :
    Covers (s.rd ++ s.wr) (e.rd ++ e.wr) ∧ Covers s.wr e.wr :=
  ⟨covers_mem fun r hr => by
    rw [he.rd, he.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr),
   covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr⟩

theorem called_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} {s e : State} (h : ExPre n w s) (he : Saved n w s e) :
    WP isa (.call name c) e (Called n w f s) := by
  have hcp := he.callPre h
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, al⟩, f0, f1, f2, f3, hsp⟩ := h
  obtain ⟨hcov, hw⟩ := he.covers
  refine WP.call hk.hv (hk.pre _ hcp) hcov hw (fun z rd' wr' sp' fr' pres' _ post' => ?_) hk.nf
  have hpost := hk.post _ _ post'
  have g (r : Reg) (hr : r ∈ [Reg.a0, .a1, .a2]) : (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr r (by revert r; decide)]
  simp only [State.withRegions_mem, State.callEntry_mem, g .a0 (by simp), g .a1 (by simp), g .a2 (by simp),
    he.mem] at hpost
  -- The arguments, which the push and the save left.
  have hk1 : ∀ x, (scR n s).Contains x 1 → _ := fun x hx => saved_keep (s := s) f1 hx
  have hk2 : ∀ x, (ptR n s).Contains x 1 → _ := fun x hx => saved_keep (s := s) f2 hx
  have ksc : bytesAt ((s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra)).writeW (s.sp - 16) (s.gpr .a0))
      (s.gpr .a1) n = bytesAt s.mem (s.gpr .a1) n := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact hk1 _ (Offset.contains_base _ (by omega) (by omega))
  have kpt : bytesAt ((s.mem.write (s.sp - 16 + 8) 8 (s.gpr .ra)).writeW (s.sp - 16) (s.gpr .a0))
      (s.gpr .a2) n = bytesAt s.mem (s.gpr .a2) n := by
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact hk2 _ (Offset.contains_base _ (by omega) (by omega))
  rw [ksc, kpt] at hpost
  -- The frame, which the callee does not write.
  have hfr : ∀ {d : Nat}, d ≤ 8 → ∀ r ∈ s.wr, (⟨s.sp - 16 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d hd r hr
    rw [wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fr_part f0 hd
    · exact fr_part f3 hd
  have em : e.mem.read (s.sp - 16 + 8) 8 = s.gpr .ra := by
    rw [he.mem]
    have hs := slot_sep (n := n) (w := w) ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, al⟩, f0, f1, f2, f3, hsp⟩
    simp only [Mem.writeW]
    rw [Mem.read_write_sep (Region.Disjoint.sep hs.symm (Region.contains_self _ _) (Region.contains_self _ _)),
      read_write_self]
    all_goals decide
  have es : e.mem.readW (s.sp - 16) 64 = s.gpr .a0 := by
    rw [he.mem, Mem.readW_writeW_self64]
  refine ⟨hpost, ?_, ?_, fun r hr => by rw [pres' r hr, he.gpr r (by revert r; decide)], sp'.trans he.sp,
    rd'.trans he.rd, wr'.trans he.wr⟩
  · have h0 : ∀ r ∈ s.wr, (⟨s.sp - 16, 8⟩ : Region).Disjoint r := fun r hr => by
      simpa using hfr (d := 0) (by decide) r hr
    rw [Frame.readW fr' (r := ⟨s.sp - 16, 8⟩) (Region.contains_self _ _) h0 (by decide)]
    exact es
  · rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl,
      Frame.read fr' (r := ⟨s.sp - 16 + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _) (hfr (by decide))
      (by decide)]
    exact em

/-- After `out` is loaded back into `t0`. -/
structure Restored (n w : Nat) (f : List Byte → List Byte → List Byte) (s u : State) : Prop where
  called : Called n w f s u
  t0 : u.gpr .t0 = s.gpr .a0

theorem restored_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s z : State} (h : ExPre n w s)
    (hz : Called n w f s z) : WP isa (.block restore) z (Restored n w f s) := by
  unfold restore
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := s.sp - 16) (by decide) (by rw [v₁.gpr, hz.sp]; simp) (by have := fr_al h; omega)
    ⟨frR s, by rw [v₁.rd, v₁.wr, hz.wr]; simp, by simpa using fr_contains (s := s) (d := 0) (by decide)⟩
    fun u₂ v₂ => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [v₂.mem, v₁.mem]; exact hz.out
  · rw [v₂.mem, v₁.mem]; exact hz.slot
  · rw [v₂.mem, v₁.mem]; exact hz.ra
  · rw [v₂.other r (by revert r; decide), v₁.other r (by revert r; decide), hz.pres r hr]
  · rw [v₂.sp, v₁.sp, hz.sp]
  · rw [v₂.rd, v₁.rd, hz.rd]
  · rw [v₂.wr, v₁.wr, hz.wr]
  · rw [v₂.gpr, v₁.mem, hz.slot]

/-! ## The check -/

theorem orBytes_wp (a : Addr) (m : Mem) : ∀ (i : Nat), i < 2048 → ∀ (u : State) (is : List Instr)
    (Q : State → Prop), u.gpr .t0 = a → u.mem = m →
    (∀ j < i, InRegions (u.rd ++ u.wr) (a + BitVec.ofNat 64 j) 1) →
    (∀ u', u'.gpr .t1 = u.gpr .t1 ||| (orAll m a i).setWidth 64 → u'.gpr .t0 = a → u'.mem = m →
      u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → (∀ r, r ≠ .t1 → r ≠ .t2 → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) →
    WP isa (.block (orBytes i ++ is)) u Q := by
  intro i
  induction i with
  | zero =>
    intro _ u is Q ht hm _ k
    exact k u (by simp [orAll]) ht hm rfl rfl rfl fun _ _ _ => rfl
  | succ i ih =>
    intro hi u is Q ht hm hin k
    rw [orBytes, List.append_assoc]
    refine ih (by omega) u _ Q ht hm (fun j hj => hin j (by omega)) fun u' g1 g0 gm grd gwr gsp go => ?_
    refine wp_lbu (a := a + BitVec.ofNat 64 i) (by omega) (by rw [g0])
      (by rw [grd, gwr]; exact hin i (by omega)) fun u₁ v₁ => ?_
    refine wp_or fun u₂ v₂ => ?_
    refine k u₂ ?_ ?_ ?_ ?_ ?_ ?_ fun r h1 h2 => ?_
    · rw [v₂.gpr, v₁.other _ (by decide), v₁.gpr, g1, gm, orAll, BitVec.setWidth_or, BitVec.or_assoc]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), g0]
    · rw [v₂.mem, v₁.mem, gm]
    · rw [v₂.rd, v₁.rd, grd]
    · rw [v₂.wr, v₁.wr, gwr]
    · rw [v₂.sp, v₁.sp, gsp]
    · rw [v₂.other r h1, v₁.other r h2, go r h1 h2]

/-- After the check. -/
structure Checked (n w : Nat) (f : List Byte → List Byte → List Byte) (s v : State) : Prop where
  called : Called n w f s v
  a0 : (v.gpr .a0).setWidth 32 = if orAll v.mem (s.gpr .a0) n = 0 then 0 else 1

theorem checked_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s u : State} (h : ExPre n w s)
    (hn : n < 2048) (hu : Restored n w f s u) : WP isa (.block (check n)) u (Checked n w f s) := by
  obtain ⟨⟨rd, wr, -, -, -, -, -, b0, -, -, -, -, -⟩, -, -, -, -, -⟩ := h
  unfold check
  refine wp_li (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine orBytes_wp (s.gpr .a0) u.mem n hn u₁ _ _ (by rw [v₁.other _ (by decide), hu.t0]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hu.called.rd, hu.called.wr, wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩) fun u' g1 _ gm grd gwr gsp go => ?_
  refine wp_li (imm := 0) (by decide) fun u₂ v₂ => wp_sltu fun u₃ v₃ => WP.block_nil ?_
  have hm : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, gm]
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hu.called.out
  · rw [hm]; exact hu.called.slot
  · rw [hm]; exact hu.called.ra
  · rw [v₃.other r (by revert r; decide), v₂.other r (by revert r; decide), go r (by revert r; decide)
      (by revert r; decide), v₁.other r (by revert r; decide), hu.called.pres r hr]
  · rw [v₃.sp, v₂.sp, gsp, v₁.sp, hu.called.sp]
  · rw [v₃.rd, v₂.rd, grd, v₁.rd, hu.called.rd]
  · rw [v₃.wr, v₂.wr, gwr, v₁.wr, hu.called.wr]
  · rw [v₃.gpr, v₂.gpr, v₂.other _ (by decide), g1, v₁.gpr, hm]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_or]
    exact result_lt _

/-! ## The whole function -/

theorem popped_ok {n w : Nat} {f : List Byte → List Byte → List Byte} {s v : State}
    (hv : Checked n w f s v) : abiPreserved s (popped .ra v) ∧ ExPost n f s (popped .ra v) := by
  have hra : v.mem.read (v.sp + 8) 8 = s.gpr .ra := by rw [hv.called.sp]; exact hv.called.ra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show (v.write .ra _).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ (show r ≠ .ra by revert r; decide), hv.called.pres r hr]
  · show v.sp + 16 = s.sp
    rw [hv.called.sp]; exact BitVec.sub_add_cancel _ _
  · show (v.write .ra (v.mem.read (v.sp + 8) 8)).gpr .ra = s.gpr .ra
    rw [RegUpd.gpr_write_self, hra]
  · exact hv.called.out
  · show ((v.write .ra (v.mem.read (v.sp + 8) 8)).gpr .a0).setWidth 32 = _
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), hv.a0]
    exact result_spec _ _ _ _ hv.called.out

theorem exchange_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2048) {s : State} (h : ExPre n w s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  refine WP.frame h.2.2.2.2.2 ?_
  refine WP.seq (WP.mono (saved_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (called_wp hk h he) fun z hz => ?_)
  refine WP.seq (WP.mono (restored_wp h hz) fun u hu => ?_)
  exact WP.mono (checked_wp h hn hu) fun v hv => popped_ok hv

/-! ## Constant time -/

theorem exchange_ct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String}
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.t0]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (ExPre n w) Pub (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1.1, p₂.1.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.1.2.1, p₂.1.2.1]; simp only [outR, wsR, q0, q3]
  refine (RelCT.frame (P := Eq2 σ₁ σ₂) (R := TT) (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
    ((?_ : RelCT isa (Eq2 (pushed .ra σ₁) (pushed .ra σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- `out` into the frame.
  refine rel_seq (rel_taint [] (show σ₁.sp - 16 = σ₂.sp - 16 by rw [qsp]) (by simp) (by taint_decide))
    (saved_wp p₁) (saved_wp p₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The call, by its callee's contract.
  have g {s e : State} (he : Saved n w s e) (r : Reg) (hr : r ∈ [Reg.a0, .a1, .a2, .a3]) :
      (e.callEntry.withRegions σ₁.rd σ₁.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide), he.gpr r (by revert r; decide)]
  refine rel_seq (RelCT.call hk.hv hk.hct σ₁.rd σ₁.wr fun a b ⟨ha, hb⟩ => ?_)
    (called_wp hk p₁ he₁) (called_wp hk p₂ he₂) fun z₁ z₂ hz₁ hz₂ => ?_
  · subst ha hb
    have c₂ := he₂.callPre p₂
    rw [hrd, hwr] at c₂
    have v₂ := he₂.covers
    rw [hrd, hwr] at v₂
    refine ⟨hk.pre _ (he₁.callPre p₁), hk.pre _ c₂, hk.pub _ _ ?_, he₁.covers.1, he₁.covers.2, v₂.1, v₂.2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [g he₁ _ (by simp), g he₂ _ (by simp), q0]
    · rw [g he₁ _ (by simp), g he₂ _ (by simp), q1]
    · rw [g he₁ _ (by simp), g he₂ _ (by simp), q2]
    · rw [g he₁ _ (by simp), g he₂ _ (by simp), q3]
    · simp only [State.withRegions_sp, State.callEntry_sp, he₁.sp, he₂.sp, qsp]
  -- `out` back, and the check.
  refine rel_seq (rel_taint [] (by rw [hz₁.sp, hz₂.sp, qsp]) (by simp) (by taint_decide))
    (restored_wp p₁ hz₁) (restored_wp p₂ hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  exact rel_taint [.t0] (by rw [hu₁.called.sp, hu₂.called.sp, qsp]) (by simp [hu₁.t0, hu₂.t0, q0]) ht

/-! ## `Verified` -/

theorem exchange_correct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2048) :
    ∀ s, (exContract n w f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) hn h
    exact ⟨t, s', he, ha, hp⟩

end VG.Proof.Xdh.RISCV64
