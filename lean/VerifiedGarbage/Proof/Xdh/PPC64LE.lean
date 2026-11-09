module

public import VerifiedGarbage.Impl.Xdh.PPC64LE
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
meta import VerifiedGarbage.Impl.Xdh.PPC64LE
meta import VerifiedGarbage.Proof.Xdh.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT

/-!
# X25519 and X448 exchange, with RFC 7748's check, on PPC64LE

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Xdh/RISCV64.lean`): for any callee `c` whose contract `k` its proof
gives (`Callee`), `Impl.Xdh.PPC64LE.exchange` moves the link register to
`r0`, pushes a frame of 48 bytes at `B = sp - 48`, which keeps it at
`B + 32` (and the back chain at `B`), stores `out` at `B + 40`
(`saved_wp`), calls `c` with its arguments as they came (`called_wp`),
which writes neither, loads `out` back (`restored_wp`), ORs the `n` bytes
there into `r11` (`orBytes_wp`) and computes the result from it
(`checked_wp`); the pop and `mtlr` restore the link register
(`exchange_wp`). Two runs whose pointers agree (`Pub`) leak the same trace
(`exchange_ct`).
-/

@[expose] public section

namespace VG.Proof.Xdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Xdh.PPC64LE
open VG.Spec.X25519 (bytesAt)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_seq rel_taint ct_of)

/-! ## Steps -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure U (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem U.write (s : State) (d : Reg) (v : BitVec 64) : U s (s.write d v) d v :=
  ⟨RegUpd.gpr_write_self _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', U s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (by simp [exec, show imm < 32768 from h]) (k _ (U.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', U s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (U.write _ _ _))

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', U s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (U.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', U s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (U.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', U s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (U.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', U s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (U.write _ _ _))

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', U s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (U.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', U s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (U.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr t) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ rfl rfl rfl rfl rfl rfl)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

end

section
variable (n w : Nat) (s : State)

/-- The regions of the arguments, and the 48 bytes of our frame. -/
abbrev outR : Region := ⟨s.gpr .r3, n⟩
abbrev scR : Region := ⟨s.gpr .r4, n⟩
abbrev ptR : Region := ⟨s.gpr .r5, n⟩
abbrev wsR : Region := ⟨s.gpr .r6, w⟩
abbrev frR : Region := ⟨s.sp - 48, 48⟩

end

/-- What the callee needs at its entry. -/
def CallPre (n w : Nat) (s : State) : Prop :=
  s.rd = [scR n s, ptR n s] ∧ s.wr = [outR n s, wsR w s] ∧
    (outR n s).Disjoint (scR n s) ∧ (outR n s).Disjoint (ptR n s) ∧ (outR n s).Disjoint (wsR w s) ∧
    (scR n s).Disjoint (wsR w s) ∧ (ptR n s).Disjoint (wsR w s) ∧
    (s.gpr .r3).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + n ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + n ≤ 2 ^ 64 ∧
    (s.gpr .r6).toNat + w ≤ 2 ^ 64

/-- What the exchange function needs: the callee's needs, and room for the
frame, apart from the arguments. -/
def ExPre (n w : Nat) (s : State) : Prop :=
  CallPre n w s ∧ (frR s).Disjoint (outR n s) ∧ (frR s).Disjoint (scR n s) ∧
    (frR s).Disjoint (ptR n s) ∧ (frR s).Disjoint (wsR w s) ∧ 48 ≤ s.sp.toNat

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in the
low word of `r3` if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem (s.gpr .r3) n = f (bytesAt s.mem (s.gpr .r4) n) (bytesAt s.mem (s.gpr .r5) n) ∧
    (s'.gpr .r3).setWidth 32 =
      if f (bytesAt s.mem (s.gpr .r4) n) (bytesAt s.mem (s.gpr .r5) n) = List.replicate n 0 then 0 else 1

/-- What two runs agree on: the pointers. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- The exchange function's contract on PPC64LE. -/
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
    bytesAt s'.mem (s.gpr .r3) n = f (bytesAt s.mem (s.gpr .r4) n) (bytesAt s.mem (s.gpr .r5) n)
  pub : ∀ s₁ s₂, Pub s₁ s₂ → k.pub s₁ s₂
  nf : c.noFrames = true

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-! ## The frame -/

section
variable {n w : Nat} {s : State}

theorem sp_eq (h : ExPre n w s) : (s.sp - 48).toNat + 48 = s.sp.toNat := by
  have := h.2.2.2.2.2
  rw [BitVec.toNat_sub, show (48 : Addr).toNat = 48 from rfl]
  omega

/-- The 8 bytes at `B + d`, for `d ≤ 40`, are the frame's. -/
theorem fr_contains {d : Nat} (hd : d ≤ 40) :
    (frR s).Contains (s.sp - 48 + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ (by omega) (by omega)

/-- A part of the frame is apart from a region apart from the frame. -/
theorem fr_part {r : Region} (hr : (frR s).Disjoint r) {d k : Nat} (hd : d + k ≤ 48) :
    (⟨s.sp - 48 + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
  hr.sub_left (Offset.sub_base _ hd)

/-- The frame's writable region, and the slots in it. -/
theorem slot_in : (⟨s.sp - 48 + 32, 16⟩ : Region).Contains (s.sp - 48 + 40) 8 := by
  simp only [Region.Contains]
  rw [show s.sp - 48 + 40 - (s.sp - 48 + 32) = 8 from by bv_omega]
  decide

theorem slot_sep (h : ExPre n w s) :
    (⟨s.sp - 48 + 40, 8⟩ : Region).Disjoint ⟨s.sp - 48 + 32, 8⟩ := by
  have e := sp_eq h
  have := Offset.disjoint (s.sp - 48) (d := 40) (n := 8) (e := 32) (k := 8) (.inr (by omega)) (by omega)
    (by omega)
  simpa using this

end

/-! ## The phases -/

/-- The memory once the push and the save are done. -/
abbrev eMem (s : State) : Mem :=
  (((s.mem.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 s.lr)).writeW (s.sp - 48 + 40) (s.gpr .r3)

/-- After `out` is saved: the frame holds the link register at `B + 32` and
`out` at `B + 40`. -/
structure Saved (n w : Nat) (s e : State) : Prop where
  mem : e.mem = eMem s
  gpr : ∀ r, r ≠ .r0 → r ≠ .r12 → e.gpr r = s.gpr r
  sp : e.sp = s.sp - 48
  rd : e.rd = s.rd
  wr : e.wr = ⟨s.sp - 48 + 32, 16⟩ :: s.wr

theorem saved_wp {n w : Nat} {s : State} :
    WP isa (.block save) (pushed .r0 (s.write .r0 s.lr)) (Saved n w s) := by
  unfold save
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine wp_std (a := s.sp - 48 + 40) (by decide) (by decide)
    (by rw [v₁.gpr, BitVec.add_zero]; rfl)
    ⟨_, by rw [v₁.wr]; exact List.mem_cons_self .., by simpa [pushed, RegUpd.sp_write] using slot_in⟩
    fun u₂ g₂ m₂ r₂ w₂ p₂ _ => WP.block_nil ?_
  refine ⟨?_, fun r h0 h12 => ?_, ?_, ?_, ?_⟩
  · rw [m₂, v₁.mem, v₁.other _ (by decide)]; rfl
  · rw [g₂, v₁.other r h12]
    simp only [pushed]
    exact RegUpd.gpr_write_of_ne _ _ h0
  · rw [p₂, v₁.sp]; rfl
  · rw [r₂, v₁.rd]; rfl
  · rw [w₂, v₁.wr]; rfl

/-- The memory the push and the save leave outside the frame. -/
theorem saved_keep {s : State} {r : Region} (hr : (frR s).Disjoint r) {x : Addr}
    (hx : r.Contains x 1) : eMem s x = s.mem x := by
  have hf : Frame [frR s] s.mem (eMem s) := by
    refine (((Frame.refl _ _).write (List.mem_singleton_self _) _ ?_).write (List.mem_singleton_self _) _
      ?_).writeW (List.mem_singleton_self _) _ ?_
    · simpa using fr_contains (s := s) (d := 0) (by decide)
    · exact fr_contains (s := s) (d := 32) (by decide)
    · exact fr_contains (s := s) (d := 40) (by decide)
  exact hf x fun r' hr' hc => by
    rw [List.mem_singleton.mp hr'] at hc
    exact hr x hc hx

/-- After the call: `f` of the arguments at `out`, and the frame as it was. -/
structure Called (n w : Nat) (f : List Byte → List Byte → List Byte) (s z : State) : Prop where
  out : bytesAt z.mem (s.gpr .r3) n = f (bytesAt s.mem (s.gpr .r4) n) (bytesAt s.mem (s.gpr .r5) n)
  slot : z.mem.readW (s.sp - 48 + 40) 64 = s.gpr .r3
  ra : z.mem.read (s.sp - 48 + 32) 8 = s.lr
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = s.sp - 48
  rd : z.rd = s.rd
  wr : z.wr = ⟨s.sp - 48 + 32, 16⟩ :: s.wr

/-- The callee's entry. -/
theorem Saved.callPre {n w : Nat} {s e : State} (h : ExPre n w s) (he : Saved n w s e) :
    CallPre n w (e.callEntry.withRegions s.rd s.wr) := by
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, -, -, -, -, -⟩ := h
  have g (r : Reg) (hr : r ∈ [Reg.r3, .r4, .r5, .r6]) :
      (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide),
      he.gpr r (by revert r; decide) (by revert r; decide)]
  simp only [CallPre, outR, scR, ptR, wsR, State.withRegions_rd, State.withRegions_wr,
    g .r3 (by simp), g .r4 (by simp), g .r5 (by simp), g .r6 (by simp)]
  exact ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩

/-- The regions the call is given are ours. -/
theorem Saved.covers {n w : Nat} {s e : State} (he : Saved n w s e) :
    Covers (s.rd ++ s.wr) (e.rd ++ e.wr) ∧ Covers s.wr e.wr :=
  ⟨covers_mem fun r hr => by
    rw [he.rd, he.wr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr),
   covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr⟩

theorem bytes_keep {s : State} {p : Addr} {n : Nat} (hd : (frR s).Disjoint ⟨p, n⟩)
    (hn : p.toNat + n ≤ 2 ^ 64) : bytesAt (eMem s) p n = bytesAt s.mem p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact saved_keep hd (Offset.contains_base _ (by omega) (by omega))

theorem called_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} {s e : State} (h : ExPre n w s) (he : Saved n w s e) :
    WP isa (.call name c) e (Called n w f s) := by
  have hcp := he.callPre h
  have hs := slot_sep h
  obtain ⟨⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩, f0, f1, f2, f3, hsp⟩ := h
  obtain ⟨hcov, hw⟩ := he.covers
  refine WP.call hk.hv (hk.pre _ hcp) hcov hw (fun z rd' wr' sp' fr' pres' _ post' => ?_) hk.nf
  have hpost := hk.post _ _ post'
  have g (r : Reg) (hr : r ∈ [Reg.r3, .r4, .r5]) : (e.callEntry.withRegions s.rd s.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide),
      he.gpr r (by revert r; decide) (by revert r; decide)]
  simp only [State.withRegions_mem, State.callEntry_mem, g .r3 (by simp), g .r4 (by simp), g .r5 (by simp),
    he.mem] at hpost
  rw [bytes_keep f1 b1, bytes_keep f2 b2] at hpost
  -- The frame, which the callee does not write.
  have hfr : ∀ {d : Nat}, d ≤ 40 → ∀ r ∈ s.wr, (⟨s.sp - 48 + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    intro d hd r hr
    rw [wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fr_part f0 (by omega)
    · exact fr_part f3 (by omega)
  have em : e.mem.read (s.sp - 48 + 32) 8 = s.lr := by
    rw [he.mem]
    simp only [eMem, Mem.writeW, Nat.reduceDiv]
    rw [Mem.read_write_sep (Region.Disjoint.sep hs.symm (Region.contains_self _ _) (Region.contains_self _ _)),
      read_write_self]
    all_goals decide
  have es : e.mem.readW (s.sp - 48 + 40) 64 = s.gpr .r3 := by
    rw [he.mem, eMem, Mem.readW_writeW_self64]
  refine ⟨hpost, ?_, ?_, fun r hr => ?_, sp'.trans he.sp, rd'.trans he.rd, wr'.trans he.wr⟩
  · rw [show (40 : Addr) = BitVec.ofNat 64 40 from rfl,
      Frame.readW fr' (r := ⟨s.sp - 48 + BitVec.ofNat 64 40, 8⟩) (Region.contains_self _ _) (hfr (by decide))
      (by decide)]
    exact es
  · rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Frame.read fr' (r := ⟨s.sp - 48 + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (hfr (by decide))
      (by decide)]
    exact em
  · rw [pres' r hr, he.gpr r (by revert r; decide) (by revert r; decide)]

/-- After `out` is loaded back into `r12`. -/
structure Restored (n w : Nat) (f : List Byte → List Byte → List Byte) (s u : State) : Prop where
  called : Called n w f s u
  r12 : u.gpr .r12 = s.gpr .r3

theorem restored_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s z : State}
    (hz : Called n w f s z) : WP isa (.block restore) z (Restored n w f s) := by
  unfold restore
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine wp_ld (a := s.sp - 48 + 40) (by decide) (by decide) (by rw [v₁.gpr, hz.sp]; simp)
    ⟨_, by rw [v₁.rd, v₁.wr, hz.wr]; simp, slot_in⟩ fun u₂ v₂ => WP.block_nil ?_
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

theorem orBytes_wp (a : Addr) (m : Mem) : ∀ (i : Nat), i < 2 ^ 15 → ∀ (u : State) (is : List Instr)
    (Q : State → Prop), u.gpr .r12 = a → u.mem = m →
    (∀ j < i, InRegions (u.rd ++ u.wr) (a + BitVec.ofNat 64 j) 1) →
    (∀ u', u'.gpr .r11 = u.gpr .r11 ||| (orAll m a i).setWidth 64 → u'.gpr .r12 = a → u'.mem = m →
      u'.rd = u.rd → u'.wr = u.wr → u'.sp = u.sp → (∀ r, r ≠ .r11 → r ≠ .r10 → u'.gpr r = u.gpr r) →
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
    refine wp_lbz (a := a + BitVec.ofNat 64 i) (by decide) (by omega) (by rw [g0])
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
  r3 : (v.gpr .r3).setWidth 32 = if orAll v.mem (s.gpr .r3) n = 0 then 0 else 1

theorem checked_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {s u : State} (h : ExPre n w s)
    (hn : n < 2 ^ 15) (hu : Restored n w f s u) : WP isa (.block (check n)) u (Checked n w f s) := by
  obtain ⟨⟨rd, wr, -, -, -, -, -, b0, -, -, -⟩, -, -, -, -, -⟩ := h
  unfold check
  refine wp_li (imm := 0) (by decide) fun u₁ v₁ => ?_
  refine orBytes_wp (s.gpr .r3) u.mem n hn u₁ _ _ (by rw [v₁.other _ (by decide), hu.r12]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hu.called.rd, hu.called.wr, wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩) fun u' g1 _ gm grd gwr gsp go => ?_
  refine wp_subi (by decide) (by decide) fun u₂ v₂ => wp_lsr (by decide) fun u₃ v₃ =>
    wp_li (imm := 1) (by decide) fun u₄ v₄ => wp_xor fun u₅ v₅ => WP.block_nil ?_
  have hm : u₅.mem = u.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, gm]
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hu.called.out
  · rw [hm]; exact hu.called.slot
  · rw [hm]; exact hu.called.ra
  · rw [v₅.other r (by revert r; decide), v₄.other r (by revert r; decide), v₃.other r (by revert r; decide),
      v₂.other r (by revert r; decide), go r (by revert r; decide) (by revert r; decide),
      v₁.other r (by revert r; decide), hu.called.pres r hr]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, gsp, v₁.sp, hu.called.sp]
  · rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, grd, v₁.rd, hu.called.rd]
  · rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, gwr, v₁.wr, hu.called.wr]
  · rw [v₅.gpr, v₄.gpr, v₄.other _ (by decide), v₃.gpr, v₂.gpr, g1, v₁.gpr, hm]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_or]
    exact result_shr _

/-! ## The whole function -/

/-- The frame popped and the link register back: what the function leaves. -/
theorem popped_ok {n w : Nat} {f : List Byte → List Byte → List Byte} {s v : State}
    (hv : Checked n w f s v) :
    WP isa (.block [.mtlr .r0]) (popped .r0 v) fun z => abiPreserved s z ∧ ExPost n f s z := by
  refine WP.cons exec_mtlr (WP.block_nil ?_)
  have hra : v.mem.read (v.sp + 32) 8 = s.lr := by rw [hv.called.sp]; exact hv.called.ra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show (v.write .r0 _).gpr r = _
    rw [RegUpd.gpr_write_of_ne _ _ (show r ≠ .r0 by revert r; decide), hv.called.pres r hr]
  · show v.sp + 48 = s.sp
    rw [hv.called.sp]; exact BitVec.sub_add_cancel _ _
  · show (v.write .r0 (v.mem.read (v.sp + 32) 8)).gpr .r0 = s.lr
    rw [RegUpd.gpr_write_self, hra]
  · exact hv.called.out
  · show ((v.write .r0 (v.mem.read (v.sp + 32) 8)).gpr .r3).setWidth 32 = _
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), hv.r3]
    exact result_spec _ _ _ _ hv.called.out

theorem exchange_wp {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2 ^ 15) {s : State} (h : ExPre n w s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  refine WP.seq (WP.cons exec_mflr (WP.block_nil ?_))
  refine WP.seq (WP.frame (by rw [RegUpd.sp_write]; exact h.2.2.2.2.2) ?_)
  refine WP.seq (WP.mono (saved_wp (n := n) (w := w)) fun e he => ?_)
  refine WP.seq (WP.mono (called_wp hk h he) fun z hz => ?_)
  refine WP.seq (WP.mono (restored_wp hz) fun u hu => ?_)
  exact WP.mono (checked_wp h hn hu) fun v hv => popped_ok hv

/-! ## Constant time -/

theorem exchange_ct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String}
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r12]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (ExPre n w) Pub (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have hrd : σ₂.rd = σ₁.rd := by rw [p₁.1.1, p₂.1.1]; simp only [scR, ptR, q1, q2]
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.1.2.1, p₂.1.2.1]; simp only [outR, wsR, q0, q3]
  -- The link register into `r0`.
  refine rel_seq (rel_taint [] qsp (by simp) (by taint_decide))
    (WP.cons exec_mflr (WP.block_nil rfl)) (WP.cons exec_mflr (WP.block_nil rfl)) fun a₁ a₂ ha₁ ha₂ => ?_
  subst ha₁ ha₂
  refine RelCT.seq (R := fun a b : State => a.sp = b.sp) ?_
    (RelCT.taint (A := taint) (P := fun a b : State => a.sp = b.sp) (Taint.ofRegs [])
      (fun _ _ hab => ⟨hab, fun r h' => by simp at h'⟩) (by taint_decide))
  refine (RelCT.frame (P := Eq2 (σ₁.write .r0 σ₁.lr) (σ₂.write .r0 σ₂.lr)) (R := TT)
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact qsp)
    ((?_ : RelCT isa (Eq2 (pushed .r0 (σ₁.write .r0 σ₁.lr)) (pushed .r0 (σ₂.write .r0 σ₂.lr))) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h))
  -- `out` into the frame.
  refine rel_seq (rel_taint [] (show σ₁.sp - 48 = σ₂.sp - 48 by rw [qsp]) (by simp) (by taint_decide))
    (saved_wp (n := n) (w := w)) (saved_wp (n := n) (w := w)) fun e₁ e₂ he₁ he₂ => ?_
  -- The call, by its callee's contract.
  have g {s e : State} (he : Saved n w s e) (r : Reg) (hr : r ∈ [Reg.r3, .r4, .r5, .r6]) :
      (e.callEntry.withRegions σ₁.rd σ₁.wr).gpr r = s.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide),
      he.gpr r (by revert r; decide) (by revert r; decide)]
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
    (restored_wp hz₁) (restored_wp hz₂) fun u₁ u₂ hu₁ hu₂ => ?_
  exact rel_taint [.r12] (by rw [hu₁.called.sp, hu₂.called.sp, qsp]) (by simp [hu₁.r12, hu₂.r12, q0]) ht

/-! ## `Verified` -/

theorem exchange_correct {n w : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w f c k) {name : String} (hn : n < 2 ^ 15) :
    ∀ s, (exContract n w f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) hn h
    exact ⟨t, s', he, ha, hp⟩

end VG.Proof.Xdh.PPC64LE
