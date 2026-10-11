import VerifiedGarbage.Proof.Cast5.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Spill

/-!
# CAST5 on ARMv7: ECB

`ecb up` takes the working space from the stack, saves the callee-saved
registers in it, keeps its arguments in their slots, runs the block function
on each block in turn (`ecbLoop_ok`) and restores the registers
(`ecb_correct`).
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega)]

/-! ## The saved registers -/

def savedSlots : List (Reg × Nat) := saved.zipIdx.map fun (r, i) => (r, savedOff + 4 * i)

theorem save_eq : save = savedSlots.map fun p => Instr.str p.1 .r12 p.2 := rfl
theorem restore_eq : restore = savedSlots.map fun p => Instr.ldr p.1 .r12 p.2 := rfl
theorem savedSlots_ok : Spill.Slots 64 100 savedSlots := by decide
theorem savedSlots_restorable : Spill.Restorable .r12 savedSlots := by decide
theorem savedSlots_preserved : ∀ r ∈ preserved, r ∈ savedSlots.map Prod.fst := by decide
theorem savedSlots_ne : ∀ p ∈ savedSlots, p.1 ≠ .r12 := by decide

/-! ## The loop over the blocks -/

/-- The state of ECB with `j` of the `N` blocks at `d` done, from the memory
`m0` after the setup: the slots, the blocks, and nothing else written but the
data and the first 24 bytes of the working space at `c`. -/
structure LInv (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d kb : BitVec 32) (n N j : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 24⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    if i < j then cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
    else Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i))
  dslot : u.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = d + BitVec.ofNat 32 (8 * j)
  nslot : u.mem.readW (State.addr c + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (N - j)
  sslot : u.mem.readW (State.addr c + BitVec.ofNat 64 8) 32 = kb
  rslot : u.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 n
  sk : Spec.Cast5.scheduleAt u.mem (State.addr kb) = k
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp

/-- What the loop needs of the layout: the schedule at `kb`, the `N` blocks at
`d` and the working space at `c`, separate and within the address space. -/
structure Lay (s : State) (c d kb : BitVec 32) (n N : Nat) : Prop where
  cfit : c.toNat + 256 ≤ 2 ^ 32
  dfit : d.toNat + 8 * N ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr c, 256⟩ : Region) ∈ s.wr
  dat : (⟨State.addr d, 8 * N⟩ : Region) ∈ s.wr
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  dDS : Region.Disjoint ⟨State.addr d, 8 * N⟩ ⟨State.addr c, 256⟩
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr c, 256⟩
  dKD : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr d, 8 * N⟩
  nv : n = 12 ∨ n = 16

theorem addr_blk {d : BitVec 32} {N j : Nat} (hd : d.toNat + 8 * N ≤ 2 ^ 32) (hj : j < N) :
    State.addr (d + BitVec.ofNat 32 (8 * j)) = State.addr d + BitVec.ofNat 64 (8 * j) := addr_add (by omega)

theorem sub_blk (D : Addr) {N j : Nat} (hj : j < N) :
    Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * N⟩ := Offset.sub_base _ (by omega)

theorem sub_c24 (C : Addr) : Region.Sub ⟨C, 24⟩ ⟨C, 256⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢; omega

theorem sub_ct256 (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 8⟩ ⟨C, 256⟩ := Offset.sub_base _ (by decide)

theorem sub_ct (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 8⟩ ⟨C, 24⟩ := Offset.sub_base _ (by decide)

/-- The block function's precondition, at block `j`. -/
theorem LInv.bpre {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    BPre u c (d + BitVec.ofNat 32 (8 * j)) kb n where
  r12 := h.r12
  cfit := hl.cfit
  pfit := by
    have := hl.dfit
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  kfit := hl.kfit
  scr := by rw [h.wr]; exact hl.scr
  blk := fun {off w} hw => by
    have := hl.dfit
    rw [addr_blk hl.dfit hj, Proof.Cast5.add_ofNat_add, h.wr]
    exact ⟨_, hl.dat, Offset.contains_base _ (by omega) (by omega)⟩
  sch := by rw [h.rd, h.wr]; exact hl.sch
  dPS := by rw [addr_blk hl.dfit hj]; exact hl.dDS.sub_left (sub_blk _ hj)
  dKS := hl.dKS
  dKP := by rw [addr_blk hl.dfit hj]; exact hl.dKD.sub_right (sub_blk _ hj)
  data := h.dslot
  sched := h.sslot
  rounds := h.rslot
  nv := hl.nv

theorem ofNat_sub_one {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 32) :
    BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- `advance`: on to the next block. -/
theorem advance_ok (v : State) {c : BitVec 32} (hc : v.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w) {x y : BitVec 32}
    (hx : v.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = x)
    (hy : (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).readW (State.addr c + BitVec.ofNat 64 4) 32 = y) :
    WP isa (.block advance) v fun w =>
      w.mem = (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).writeW (State.addr c + BitVec.ofNat 64 4) (y - 1) ∧
      w.z = (y - 1 == 0) ∧ w.gpr .r12 = c ∧ w.rd = v.rd ∧ w.wr = v.wr ∧ w.sp = v.sp := by
  have aS := addr_off hcf
  have hin' : ∀ {off w : Nat}, off + w ≤ 256 → InRegions (v.rd ++ v.wr) (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hcg⟩ := hin hw; exact ⟨g, List.mem_append_right _ hg, hcg⟩
  unfold advance
  crun [dataOff, nOff, hc, aS, hin, hin', hx, hy]

theorem slot_disj (C : Addr) {off : Nat} (ho : off + 4 ≤ 16) :
    Region.Disjoint ⟨C + BitVec.ofNat 64 off, 4⟩ ((⟨C + BitVec.ofNat 64 16, 8⟩ : Region)) := Offset.disjoint _ (by omega) (by omega) (by decide)

/-- A block and another, or the working space. -/
theorem blk_disj_blk (D : Addr) {N i j : Nat} (hi : i < N) (hj : j < N) (hN : 8 * N ≤ 2 ^ 32) (hij : i ≠ j) :
    Region.Disjoint ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

/-- One block, then on to the next. -/
theorem step_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    WP isa (.seq (crypt up) (.block advance)) u fun w => LInv s m0 up k c d kb n N (j + 1) w ∧
      w.z = decide (j + 1 = N) := by
  have hcf := hl.cfit
  have hdf := hl.dfit
  have eP := addr_blk hdf hj
  refine WP.seq (WP.mono (crypt_ok (h.bpre hl hj) up) fun v ⟨vb, vf, v12, vrd, vwr, vsp⟩ => ?_)
  rw [eP] at vb vf
  -- The regions the block function wrote, against the slots and the other blocks.
  have dCt (off : Nat) (ho : off + 4 ≤ 16) : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr c + BitVec.ofNat 64 off, 4⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hl.dDS.sub_left (sub_blk _ hj)).symm.sub_left (Offset.sub_base _ (by omega))
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  have vslot (off : Nat) (ho : off + 4 ≤ 16) :
      v.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 = u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 :=
    vf.readW (Region.contains_self _ _) (dCt off ho) (by decide)
  have hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [vwr, h.wr]; exact ⟨_, hl.scr, Offset.contains_base _ hw (by omega)⟩
  refine WP.mono (advance_ok v v12 hcf hin (x := d + BitVec.ofNat 32 (8 * j)) (y := BitVec.ofNat 32 (N - j))
    (by rw [vslot 0 (by decide)]; exact h.dslot)
    (by rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      vslot 4 (by decide)]; exact h.nslot)) fun w ⟨wm, wz, w12, wrd, wwr, wsp⟩ => ?_
  -- The writes of `advance`.
  have fw : Frame [⟨State.addr c, 24⟩] v.mem w.mem := by
    rw [wm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  have dC24 (R : Region) (hR : Region.Disjoint R ⟨State.addr c, 256⟩) : ∀ r ∈ [(⟨State.addr c, 24⟩ : Region)],
      Region.Disjoint R r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (sub_c24 _)
  have frK : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr kb, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.dKD.sub_right (sub_blk _ hj)
    · exact hl.dKS.sub_right (sub_ct256 _)
  refine ⟨⟨w12, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, wrd.trans (vrd.trans h.rd), wwr.trans (vwr.trans h.wr),
    wsp.trans (vsp.trans h.sp)⟩, ?_⟩
  · refine h.fr.trans ((vf.sub fun r hr => ?_).trans (fw.mono (by simp)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_blk _ hj⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_ct _⟩
  · have hdi : Region.Disjoint ⟨State.addr d + BitVec.ofNat 64 (8 * i), 8⟩ ⟨State.addr c, 256⟩ :=
      hl.dDS.sub_left (sub_blk _ hi)
    rw [blockAt_frame fw (dC24 _ hdi)]
    by_cases hij : i = j
    · subst hij
      rw [vb, ite_eq_left (by omega), h.blocks i hi, ite_eq_right (by omega), h.sk]
    · rw [blockAt_frame vf ?_, h.blocks i hi]
      · by_cases hlt : i < j
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact blk_disj_blk _ hi hj (by omega) hij
        · exact hdi.sub_right (sub_ct256 _)
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (8 * j)]
    rfl
  · rw [wm, Mem.readW_writeW_self32, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 8 (by decide)]
    exact h.sslot
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 12 (by decide)]
    exact h.rslot
  · rw [scheduleAt_frame fw (dC24 _ hl.dKS), scheduleAt_frame vf frK]
    exact h.sk
  · rw [wz, ofNat_sub_one (by omega) (by omega)]
    by_cases he : j + 1 = N
    · rw [decide_eq_true he, show N - j - 1 = 0 by omega]; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (N - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega
      simpa using this

/-- The loop over the blocks, from `j = 0`: afterwards every block is done. -/
theorem ecbLoop_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (hl : Lay s c d kb n N) (hN : 0 < N) (h : LInv s m0 up k c d kb n N 0 u) :
    WP isa (.loop (.seq (crypt up) (.block advance)) .ne) u (LInv s m0 up k c d kb n N N) := by
  refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = N - j ∧ j < N ∧ LInv s m0 up k c d kb n N j v)
    ?_ N u ⟨0, rfl, hN, h⟩
  rintro m v ⟨j, rfl, hj, hv⟩
  refine WP.mono (step_ok hl hv hj) fun w ⟨hw, wz⟩ => ?_
  by_cases he : j + 1 = N
  · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
  · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, N - (j + 1), by omega, j + 1, rfl,
      by omega, hw⟩

/-! ## The whole function -/

/-- The ECB functions' contract on ARMv7, as their proof states it. -/
def ecbArm (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let dat : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 256⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sch, args] ∧ s.wr = [dat, scr] ∧ sch.Disjoint dat ∧ sch.Disjoint scr ∧ dat.Disjoint scr ∧
      args.Disjoint dat ∧ args.Disjoint scr ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1).toNat
        (if up then .encrypt else .decrypt) (Spec.Cast5.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem cipher_map (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (bs : List Spec.Cast5.Block) :
    bs.map (cipher up k n) = Spec.Cast5.ecb k n (if up then .encrypt else .decrypt) bs := by
  cases up <;> rfl

/-- What the end needs: every block done, and nothing else written since the
setup but the first 24 bytes of the working space. -/
structure Done (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d : BitVec 32) (n N : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 24⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem LInv.done {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (h : LInv s m0 up k c d kb n N N u) : Done s m0 up k c d n N u :=
  ⟨h.r12, h.fr, fun i hi => by rw [h.blocks i hi, ite_eq_left hi], h.rd, h.wr⟩

/-- The end: the registers restored, and the blocks as the contract says. -/
theorem restore_ok {s u : State} {m0 : Mem} {up : Bool} {c : BitVec 32} (hc : c = stackArg s 0)
    (hs : (ecbArm up).pre s)
    (hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots)
    (hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0)
    (h : Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u) :
    WP isa (.block restore) u fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, _, hdf, hcf, _, _⟩ := hs
  rw [← hc] at hcf dKS dDS hwr
  have hsv' : Spill.Saved u.mem (State.addr (u.gpr .r12)) (s.setReg .r12 c).gpr savedSlots := by
    rw [h.r12]
    refine hsv.frame savedSlots_ok h.fr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dDS.sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint_base _ (by decide) (by decide)
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok savedSlots_ok savedSlots_restorable (by rw [h.r12]; omega)
    (fun d _ hd => by
      rw [h.rd, h.wr, hwr, h.r12]
      exact ⟨⟨State.addr c, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    hsv') fun s' ⟨hg, _, hm, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rw [Spill.restored_reg hg (savedSlots_preserved r hr)]
    exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact absurd hr (by decide))
  · show Spec.Cast5.blocksAt s'.mem _ _ = _
    rw [hm, ← cipher_map]
    unfold Spec.Cast5.blocksAt
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp only [Function.comp]
    rw [h.blocks i hi, blockAt_frame hm0 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDS.sub_left (sub_blk _ hi)]

/-- The arguments to their slots, then whether there are blocks. -/
theorem slots_ok (u : State) {c : BitVec 32} (hc : u.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions u.wr (State.addr c + BitVec.ofNat 64 off) w) :
    WP isa (.block [.str .r2 .r12 dataOff, .str .r3 .r12 nOff, .str .r0 .r12 schedOff, .str .r1 .r12 roundsOff,
      .cmp .r3 (.imm 0)]) u fun w =>
      w.mem = (((u.mem.writeW (State.addr c + BitVec.ofNat 64 0) (u.gpr .r2)).writeW (State.addr c + BitVec.ofNat 64 4)
        (u.gpr .r3)).writeW (State.addr c + BitVec.ofNat 64 8) (u.gpr .r0)).writeW (State.addr c + BitVec.ofNat 64 12)
          (u.gpr .r1) ∧
      w.z = (u.gpr .r3 - 0 == 0) ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp := by
  have aS := addr_off hcf
  unfold dataOff nOff schedOff roundsOff
  crun [hc, aS, hin]
  rfl

theorem slot_frame (m : Mem) (C : Addr) (a b x y : BitVec 32) :
    Frame [⟨C, 16⟩] m ((((m.writeW (C + BitVec.ofNat 64 0) a).writeW (C + BitVec.ofNat 64 4) b).writeW
      (C + BitVec.ofNat 64 8) x).writeW (C + BitVec.ofNat 64 12) y) :=
  ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem ecb_correct (up : Bool) (s : State) (hs : (ecbArm up).pre s) :
    WP isa (ecb up) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  have hs₀ := hs
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, hkf, hdf, hcf, _, hn⟩ := hs
  obtain ⟨c, hc⟩ : ∃ c, c = stackArg s 0 := ⟨_, rfl⟩
  rw [← hc] at hcf dKS dDS hwr
  have hargs : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨⟨stackArgAddr s 0, 4⟩, by rw [hrd]; simp, Region.contains_self _ _⟩
  have inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨State.addr c, 256⟩, by rw [hwr]; simp, Offset.contains_base _ hw (by omega)⟩
  unfold ecb
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- The working space, and the saved registers.
  have h1 : WP isa (.block [.ldrSp .r12 0]) s fun s₁ => s₁ = s.setReg .r12 c := by
    crun [hargs]
    rw [hc]; rfl
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff, save_eq]
  refine WP.mono (WP.keep [] (Spill.save_block_ok savedSlots_ok (s := s.setReg .r12 c)
    (by simp only [gpr_setReg_self]; omega) fun d _ hd => by simp only [gpr_setReg_self, wr_setReg]; exact inC (by omega))
    (by decide)) fun s₂ ⟨⟨g₂, rd₂, wr₂, m₂⟩, k₂⟩ => ?_
  simp only [gpr_setReg_self] at m₂
  have c₂ : s₂.gpr .r12 = c := by rw [g₂, gpr_setReg_self]
  refine WP.mono (slots_ok s₂ c₂ hcf fun hw => by rw [wr₂]; exact inC hw) fun s₃ ⟨m₃, z₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
  -- The memory after the setup.
  obtain ⟨m0, hm0e⟩ : ∃ m0, s₃.mem = m0 := ⟨_, rfl⟩
  have hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots := by
    rw [← hm0e, m₃, m₂]
    refine (Spill.saveMem_saved _ _ _ _ savedSlots_ok).frame savedSlots_ok (slot_frame _ _ _ _ _ _) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  have hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0 := by
    rw [← hm0e, m₃, m₂]
    exact (Spill.saveMem_frame _ _ _ (by decide) _ (by decide)).trans
      ((slot_frame _ _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun x hx => by simp only [Region.Contains] at hx ⊢; omega⟩)
  have g₃' (r : Reg) (hr : r ≠ .r12) : s₃.gpr r = s.gpr r := by
    rw [g₃, g₂]; exact gpr_setReg_of_ne _ _ hr
  have rd₃' : s₃.rd = s.rd := rd₃.trans rd₂
  have wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  have sp₃' : s₃.sp = s.sp := sp₃.trans k₂.sp
  have lay : Lay s c (s.gpr .r2) (s.gpr .r0) (s.gpr .r1).toNat (s.gpr .r3).toNat :=
    { cfit := hcf, dfit := hdf, kfit := hkf, scr := by rw [hwr]; simp, dat := by rw [hwr]; simp,
      sch := by rw [hrd]; simp, dDS := dDS, dKS := dKS, dKD := dKD, nv := hn }
  have done : ∀ u : State, Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u → WP isa (.block restore) u fun s' =>
        (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' :=
    fun u hu => restore_ok hc hs₀ hsv hm0 hu
  refine WP.seq (WP.mono (Q := Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
    (s.gpr .r1).toNat (s.gpr .r3).toNat) ?_ done)
  refine wp_ite_eq (fun hz => WP.block_nil ⟨by rw [g₃, g₂, gpr_setReg_self], by rw [hm0e]; exact Frame.refl _ _,
      fun i hi => ?_, rd₃', wr₃'⟩) (fun hz => ?_)
  · rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
    have h0 : s.gpr .r3 - 0 = 0 := beq_iff_eq.mp hz
    have : (s.gpr .r3).toNat = 0 := by bv_omega
    omega
  · have hN : 0 < (s.gpr .r3).toNat := by
      rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
      have h0 : s.gpr .r3 - 0 ≠ 0 := fun e => by rw [e] at hz; exact absurd hz (by decide)
      bv_omega
    have l0 : LInv s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2) (s.gpr .r0)
        (s.gpr .r1).toNat (s.gpr .r3).toNat 0 s₃ :=
      { r12 := by rw [g₃, g₂, gpr_setReg_self]
        fr := by rw [hm0e]; exact Frame.refl _ _
        blocks := fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _), hm0e]
        dslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
          exact (BitVec.add_zero _).symm
        nslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), Nat.sub_zero, BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
        rslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sk := by
          rw [hm0e]
          exact scheduleAt_frame hm0 fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS
        rd := rd₃'
        wr := wr₃'
        sp := sp₃' }
    exact WP.mono (ecbLoop_ok lay hN l0) fun u hu => hu.done

end VG.Proof.Cast5.Arm
