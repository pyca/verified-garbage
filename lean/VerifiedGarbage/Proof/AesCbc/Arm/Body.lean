import VerifiedGarbage.Proof.AesCbc.Arm.Loop
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.AesOcb.Arm.Callee

/-!
# AES-CBC on ARMv7: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`). The block functions are
called as AES-OCB calls them (`Proof.AesOcb.Arm.blk_call`), in a frame that
pushes the working space.
-/

namespace VG.Proof.AesCbc.Arm

open VG VG.Arm VG.Impl.AesCbc.Arm
open VG.Impl.CmacAes.Arm (advance xor4)
open VG.Proof.CmacAes.Arm (W R Dp N S schR dataR scrR argsR belowR savedMem xorBlk zeroBlk xorBlk_ok zeroBlk_ok
  add0)
open VG.Proof.AesOcb.Arm (BlkFn BlkCall BlkPost blkFrame blk_call encF decF)
open VG.Proof.AesGcm.Arm (below)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_mov wp_add wp_subs ofNat_beq_zero sub_ofNat)
open VG.Spec.Aes (bytesAt)

theorem encFrame_eq : encFrame = blkFrame encF := rfl
theorem decFrame_eq : decFrame = blkFrame decF := rfl

/-- The block `r7` points at, as a 32-bit address. -/
abbrev D32 (s₀ : State) (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 (16 * k)

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := State.addr (S s₀) + BitVec.ofNat 64 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨State.addr (S s₀), 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega)

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.blkCall {k : Nat} (hk : k < N s₀) {s : State}
    (r0 : s.gpr .r0 = W s₀) (r1 : s.gpr .r1 = s₀.gpr .r1) (r2 : s.gpr .r2 = D32 s₀ k) (r3 : s.gpr .r3 = 1)
    (r12 : s.gpr .r12 = S s₀) (sp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkCall s (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 := by
  have hb : below s.sp = belowR s₀ := by rw [sp]; rfl
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  refine ⟨r0, by rw [r1]; simp [R], r2, by rw [r3]; rfl, r12, hp.rounds, by rw [sp]; exact hp.sp8, hp.sch_fit,
    by rw [qN]; omega, by omega, ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_,
    by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩
  · rw [hd]; exact hp.sch_data.sub_right (UPre.data_sub hk)
  · rw [hd]; exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  · rw [hb, hd]; exact hp.b_data.sub_right (UPre.data_sub hk)
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

end

section
variable {s₀ : State}

theorem covBlk {k : Nat} (hk : k < N s₀) {rs : List Region} (h : dataR s₀ ∈ rs) :
    Covers [⟨blk s₀ k, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dataR s₀, h, 16 * k, rfl, by simp; omega⟩

theorem covIv {rs : List Region} (h : ivR s₀ ∈ rs) : Covers [⟨State.addr (Iv s₀), 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ivR s₀, h, 0, by simp, by simp⟩

theorem covSv {rs : List Region} (h : scrR s₀ ∈ rs) : Covers [⟨Sv s₀, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, h, 2048, rfl, by simp⟩

/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩

/-- A region within those a step may change. -/
theorem stepIn {k : Nat} {r : Region}
    (h : r = ⟨blk s₀ k, 16⟩ ∨ r = ivR s₀ ∨ Region.Sub r ⟨State.addr (S s₀), 2064⟩ ∨ r = belowR s₀) :
    ∃ r' ∈ [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀], Region.Sub r r' := by
  rcases h with rfl | rfl | h | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

theorem bigOf (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hs : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem) {m : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem m) :
    Frame (Big s₀) s₀.mem m :=
  have _ := hp
  UPre.big_of (hs.trans (stepFrame hk hf))

end

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-! ## The arguments of the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s : State) (m : Mem) (s₁ : State) : Prop where
  pre : BlkCall s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- The registers the invariant pins that the code before the call reads. -/
structure Regs (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = Iv s₀
  r7 : s.gpr .r7 = D32 s₀ k
  r10 : s.gpr .r10 = S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem LInv.regs {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) : Regs s₀ k s :=
  ⟨h.r4, h.r5, h.r6, h.r7, h.r10, h.sp, h.rd, h.wr⟩

/-- `Regs` after a step that keeps those registers. -/
theorem Regs.of {s₀ : State} {k : Nat} {s s' : State} (h : Regs s₀ k s)
    (g : ∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) (sp : s'.sp = s.sp) (rd : s'.rd = s.rd)
    (wr : s'.wr = s.wr) : Regs s₀ k s' :=
  ⟨by rw [g _ (by decide) (by decide), h.r4], by rw [g _ (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide), h.r6], by rw [g _ (by decide) (by decide), h.r7],
    by rw [g _ (by decide) (by decide), h.r10], by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr]⟩

theorem callArgs_eq : callArgs = [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r7),
    .mov .r3 (.imm 1), .mov .r12 (.reg .r10)] := rfl

theorem callArgs_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : Regs s₀ k s) :
    WP isa (.block callArgs) s (PreA s₀ k s s.mem) := by
  rw [callArgs_eq]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 _ => by
      rw [u₅.other _ h12, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨hp.blkCall hk ?_ ?_ ?_ ?_ ?_ (by rw [sp₅, h.sp]) (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]), keep, sp₅,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      h.r4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      h.r5]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r7]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r10]

/-- What a call leaves, about the registers. -/
theorem post_regs {s₀ : State} {k : Nat} {s s₁ s₂ : State} {m : Mem} (F : BlkFn) (h : Regs s₀ k s)
    (a : PreA s₀ k s m s₁) (c : BlkPost F s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 s₂) : Regs s₀ k s₂ := by
  have g : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := fun r hr hlr => by
    rw [c.saved r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hlr
      | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨by rw [g .r4 (by simp [preserved]) (by decide), h.r4], by rw [g .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [g .r6 (by simp [preserved]) (by decide), h.r6], by rw [g .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [g .r10 (by simp [preserved]) (by decide), h.r10], by rw [c.sp, a.sp, h.sp], by rw [c.rd, a.rd, h.rd],
    by rw [c.wr, a.wr, h.wr]⟩

/-- What `advance` leaves after block `k`. -/
theorem advance_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (h : Regs s₀ k s) (h8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k))
    (h11 : s.gpr .r11 = s₀.gpr .r11)
    (hf : Frame [ivR s₀, dataR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) s.mem)
    (hd : Spec.Cbc.blocksAt s.mem (State.addr (Dp s₀)) (N s₀) = outK enc s₀ (k + 1) ++ (blks s₀).drop (k + 1))
    (hi : bytesAt s.mem (State.addr (Iv s₀)) 16 =
      Spec.Cbc.next (iv0 s₀) (cts enc ((blks s₀).take (k + 1)) (outK enc s₀ (k + 1)))) :
    WP isa (.block advance) s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hdf := hp.data_fit
  have hN := (stackArg s₀ 0).isLt
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by rw [u₃.other _ (by decide), h8]
  have dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have g : ∀ r, r ≠ .r7 → r ≠ .r8 → s₄.gpr r = s.gpr r := fun r h7 h8' => by
    rw [u₄.other _ h8', u₃.other _ h7]
  refine ⟨⟨by rw [g _ (by decide) (by decide), h.r4], by rw [g _ (by decide) (by decide), h.r5],
    by rw [g _ (by decide) (by decide), h.r6], ?_, by rw [u₄.gpr, r8₃, dec],
    by rw [g _ (by decide) (by decide), h.r10], by rw [g _ (by decide) (by decide), h11],
    by rw [u₄.sp, u₃.sp, h.sp], by rw [u₄.rd, u₃.rd, h.rd], by rw [u₄.wr, u₃.wr, h.wr],
    by rw [u₄.mem, u₃.mem]; exact hf, by rw [u₄.mem, u₃.mem]; exact hd, by rw [u₄.mem, u₃.mem]; exact hi⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, h.r7, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega)

/-! ## Moving blocks -/

theorem xor4_eq (pb qb cb : Reg) (pd qd cd : Nat) (is : List Instr) :
    xor4 pb qb cb pd qd cd ++ is = xorBlk .r12 .lr pb qb cb pd qd cd ++ is := rfl

theorem zero4_eq (b : Reg) (d : Nat) (is : List Instr) :
    zero4 b d ++ is = .mov .r12 (.imm 0) :: (zeroBlk .r12 b d ++ is) := rfl

/-- What moving a block leaves. -/
structure Moved (s : State) (m : Mem) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- The block at `qb + qd` XORed into the block at `cb + cd`. -/
theorem xorIn_wp {cb qb : Reg} {cd qd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hq : qb ≠ .r12 ∧ qb ≠ .lr) (hc : cb ≠ .r12 ∧ cb ≠ .lr) (hcd : cd + 12 < 4096) (hqd : qd + 12 < 4096)
    (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32) (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Moved s (Proof.Cmac.xor4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr cb) + BitVec.ofNat 64 cd) (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s' →
      WP isa (.block is) s' Q) :
    WP isa (.block (xor4 cb qb cb cd qd cd ++ is)) s Q := by
  rw [xor4_eq]
  exact xorBlk_ok (by decide) hc.1 hc.2 hq.1 hq.2 hc.1 hc.2 hcd hqd hcd fc fq fc
    (Covers.right wC)
    rQ wC fun s' g => k s' ⟨g.gpr, g.mem, g.rd, g.wr, g.sp⟩

/-- The block at `qb + qd` copied to `cb + cd`, as a zeroed block XORed with it. -/
theorem copy_wp {cb qb : Reg} {cd qd : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hq : qb ≠ .r12 ∧ qb ≠ .lr) (hc : cb ≠ .r12 ∧ cb ≠ .lr) (hcd : cd + 12 < 4096) (hqd : qd + 12 < 4096)
    (fq : (s.gpr qb).toNat + qd + 16 ≤ 2 ^ 32) (fc : (s.gpr cb).toNat + cd + 16 ≤ 2 ^ 32)
    (rQ : Covers [⟨State.addr (s.gpr qb) + BitVec.ofNat 64 qd, 16⟩] (s.rd ++ s.wr))
    (wC : Covers [⟨State.addr (s.gpr cb) + BitVec.ofNat 64 cd, 16⟩] s.wr)
    (k : ∀ s', Moved s (copy4Mem s.mem (State.addr (s.gpr cb) + BitVec.ofNat 64 cd)
        (State.addr (s.gpr qb) + BitVec.ofNat 64 qd)) s' → WP isa (.block is) s' Q) :
    WP isa (.block (zero4 cb cd ++ (xor4 cb qb cb cd qd cd ++ is))) s Q := by
  rw [zero4_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have e₁ : ∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r := u₁.other
  refine zeroBlk_ok u₁.gpr hcd (by rw [e₁ _ hc.1]; exact fc)
    (by rw [e₁ _ hc.1, u₁.wr]; exact wC) fun s₂ G₂ m₂ rd₂ wr₂ sp₂ => ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h => by rw [G₂, e₁ r h]
  refine xorIn_wp hq hc hcd hqd (by rw [e₂ _ hq.1]; exact fq) (by rw [e₂ _ hc.1]; exact fc)
    (by rw [e₂ _ hq.1, rd₂, wr₂, u₁.rd, u₁.wr]; exact rQ) (by rw [e₂ _ hc.1, wr₂, u₁.wr]; exact wC)
    fun s₃ g₃ => k s₃ ⟨fun r h₁ h₂ => by rw [g₃.gpr r h₁ h₂, e₂ r h₁], ?_, by rw [g₃.rd, rd₂, u₁.rd],
      by rw [g₃.wr, wr₂, u₁.wr], by rw [g₃.sp, sp₂, u₁.sp]⟩
  rw [g₃.mem, m₂, e₂ _ hc.1, e₂ _ hq.1, e₁ _ hc.1, u₁.mem]; rfl

/-! ## Encryption -/

theorem encPost_eq : encPost = zero4 .r6 0 ++ (xor4 .r6 .r7 .r6 0 0 0 ++ advance) := rfl

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv true s₀ k s) :
    WP isa (.block encPre) s
      (PreA s₀ k s (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)))) := by
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have qN := hp.dataN hk
  have hd := hp.dataA hk
  have rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r6]; omega)
    (by rw [h.r7, qN]; omega) (by rw [h.r6, add0, rw₀]; exact covIv (by simp))
    (by rw [h.r7, add0, hd, w₀]; exact covBlk hk (by simp)) fun s₁ g₁ => ?_
  have m₁ : s₁.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₁.mem, h.r7, h.r6, add0, add0, hd]
  refine WP.mono (callArgs_wp hp hk (h.regs.of g₁.gpr g₁.sp g₁.rd g₁.wr)) fun s₂ a => ?_
  exact ⟨a.pre, fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12 hlr, g₁.gpr r h12 hlr],
    by rw [a.sp, g₁.sp], by rw [a.mem, m₁], by rw [a.rd, g₁.rd], by rw [a.wr, g₁.wr]⟩

/-- A register the code before and after the call keeps. -/
theorem kept {s₀ : State} {k : Nat} {s s₁ s₂ : State} {m : Mem} {F : BlkFn} (a : PreA s₀ k s m s₁)
    (c : BlkPost F s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀) 1 s₂) {r : Reg} (hr : r = .r8 ∨ r = .r11) :
    s₂.gpr r = s.gpr r := by
  rcases hr with rfl | rfl
  · rw [c.saved _ (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [c.saved _ (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]

theorem encBody_ok : BodyOk true encBody := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  rw [encFrame_eq]
  refine WP.seq (WP.mono (blk_call encF a.pre) fun s₂ c => ?_)
  have rg₂ := post_regs encF h.regs a c
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  -- Memory so far.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [encPost_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r7, qN]; omega)
    (by rw [rg₂.r6]; omega) (by rw [rg₂.r7, add0, hd, rw₂]; exact covBlk hk (by simp))
    (by rw [rg₂.r6, add0, w₂]; exact covIv (by simp)) fun s₃ g₃ => ?_
  have m₃ : s₃.mem = copy4Mem s₂.mem (State.addr (Iv s₀)) (blk s₀ k) := by
    rw [g₃.mem, rg₂.r6, rg₂.r7, add0, add0, hd]
  have f₃ : Frame [ivR s₀] s₂.mem s₃.mem := by rw [m₃]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₃.mem :=
    fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  -- The new block, and the chaining value.
  have hblk := h.block hk
  have newBlk : bytesAt s₃.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK true s₀ k))) := by
    rw [Proof.Cmac.bytesAt_frame f₃ (one (hp.blk_iv hk)) (by decide), ← hd, bytesAt_of_statesAt c.out, hd,
      show encF.f = Spec.Aes.cipher from rfl, ← UPre.sched_bytes hp big₁, ← aesWith_state, a.mem,
      xorIn4_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  have newIv : bytesAt s₃.mem (State.addr (Iv s₀)) 16 = bytesAt s₃.mem (blk s₀ k) 16 := by
    rw [m₃, copy4Mem_bytes _ (hp.blk_iv hk).symm,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame s₂.mem (State.addr (Iv s₀)) (blk s₀ k)) (one (hp.blk_iv hk))
        (by decide)]
  have hl : (outK true s₀ k).length = k := by
    simp [cbc, length_encrypt, Spec.Cbc.blocksAt]; omega
  have outSucc : outK true s₀ (k + 1) = outK true s₀ k ++ [bytesAt s₃.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbc, ciph, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  refine advance_wp hp hk (rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr)
    (by rw [g₃.gpr _ (by decide) (by decide), kept a c (.inl rfl), h.r8])
    (by rw [g₃.gpr _ (by decide) (by decide), kept a c (.inr rfl), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [cts, ite_true, outSucc, next_snoc]

/-! ## Decryption -/

theorem decPre_eq : decPre = zero4 .r10 2048 ++ (xor4 .r10 .r7 .r10 2048 0 2048 ++ callArgs) := rfl

theorem decPost_eq : decPost =
    xor4 .r7 .r6 .r7 0 0 0 ++ (zero4 .r6 0 ++ (xor4 .r6 .r10 .r6 0 2048 0 ++ advance)) := rfl

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv false s₀ k s) :
    WP isa (.block decPre) s (PreA s₀ k s (copy4Mem s.mem (Sv s₀) (blk s₀ k))) := by
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  have qN := hp.dataN hk
  have hd := hp.dataA hk
  have rw₀ : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₀ : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  rw [decPre_eq]
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [h.r7, qN]; omega)
    (by rw [h.r10]; omega) (by rw [h.r7, add0, hd, rw₀]; exact covBlk hk (by simp))
    (by rw [h.r10, w₀]; exact covSv (by simp)) fun s₁ g₁ => ?_
  have m₁ : s₁.mem = copy4Mem s.mem (Sv s₀) (blk s₀ k) := by rw [g₁.mem, h.r10, h.r7, add0, hd]
  refine WP.mono (callArgs_wp hp hk (h.regs.of g₁.gpr g₁.sp g₁.rd g₁.wr)) fun s₂ a => ?_
  exact ⟨a.pre, fun r h0 h1 h2 h3 h12 hlr => by rw [a.keep r h0 h1 h2 h3 h12 hlr, g₁.gpr r h12 hlr],
    by rw [a.sp, g₁.sp], by rw [a.mem, m₁], by rw [a.rd, g₁.rd], by rw [a.wr, g₁.wr]⟩

theorem decBody_ok : BodyOk false decBody := by
  intro s₀ hp k hk s h
  have hd := hp.dataA hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  rw [decFrame_eq]
  refine WP.seq (WP.mono (blk_call decF a.pre) fun s₂ c => ?_)
  have rg₂ := post_regs decF h.regs a c
  have hb : below s₁.sp = belowR s₀ := by rw [a.sp, h.sp]; rfl
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨State.addr (S s₀), 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf hp hk h.frame (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₂.wr, hp.wr]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₂.rd, rg₂.wr, hp.rd, hp.wr]; rfl
  rw [decPost_eq]
  refine xorIn_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₂.r6]; omega)
    (by rw [rg₂.r7, qN]; omega) (by rw [rg₂.r6, add0, rw₂]; exact covIv (by simp))
    (by rw [rg₂.r7, add0, hd, w₂]; exact covBlk hk (by simp)) fun s₃ g₃ => ?_
  have m₃ : s₃.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) (State.addr (Iv s₀)) := by
    rw [g₃.mem, rg₂.r7, rg₂.r6, add0, add0, hd]
  have f₃ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₃.mem := by rw [m₃]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have rg₃ := rg₂.of g₃.gpr g₃.sp g₃.rd g₃.wr
  have w₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [rg₃.wr, hp.wr]
  have rw₃ : s₃.rd ++ s₃.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rg₃.rd, rg₃.wr, hp.rd, hp.wr]; rfl
  refine copy_wp (by decide) (by decide) (by decide) (by decide) (by rw [rg₃.r10]; omega)
    (by rw [rg₃.r6]; omega) (by rw [rg₃.r10, rw₃]; exact covSv (by simp))
    (by rw [rg₃.r6, add0, w₃]; exact covIv (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = copy4Mem s₃.mem (State.addr (Iv s₀)) (Sv s₀) := by
    rw [g₄.mem, rg₃.r6, rg₃.r10, add0]
  have f₄ : Frame [ivR s₀] s₃.mem s₄.mem := by rw [m₄]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] s.mem s₄.mem :=
    (fs₂.trans (f₃.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨State.addr (S s₀), 2048⟩, belowR s₀],
      (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
    · exact (hp.b_scr.sub_right (UPre.scr_sub (by decide))).symm
  have hblk := h.block hk
  have ivIn : bytesAt s₂.mem (State.addr (Iv s₀)) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), hblk]
  have newBlk : bytesAt s₄.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [Proof.Cmac.bytesAt_frame f₄ (one (hp.blk_iv hk)) (by decide), m₃, xorIn4_bytes _ (hp.blk_iv hk),
      ivIn, ← hd, bytesAt_of_statesAt c.out, hd, show decF.f = Spec.Aes.invCipher from rfl,
      ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₄.mem (State.addr (Iv s₀)) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [m₄, copy4Mem_bytes _ hp.iv_sv, m₃,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_sv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callSv (by decide), a.mem, copy4Mem_bytes _ (hp.blk_sv hk).symm, hblk]
  have hl : (outK false s₀ k).length = k := by
    simp [cbc, length_decrypt, Spec.Cbc.blocksAt]; omega
  have outSucc : outK false s₀ (k + 1) = outK false s₀ k ++ [bytesAt s₄.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbc, ciph, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  refine advance_wp hp hk (rg₃.of g₄.gpr g₄.sp g₄.rd g₄.wr)
    (by rw [g₄.gpr _ (by decide) (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inl rfl), h.r8])
    (by rw [g₄.gpr _ (by decide) (by decide), g₃.gpr _ (by decide) (by decide), kept a c (.inr rfl), h.r11])
    (h.frame.trans (stepFrame hk fStep)) ?_ ?_
  · rw [hp.blocksAt_step hk fStep, h.data, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.Arm
