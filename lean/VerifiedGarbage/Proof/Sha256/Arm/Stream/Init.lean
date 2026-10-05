import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Impl.Sha256.Arm.Stream
import VerifiedGarbage.Proof.Sha256.StateMem

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.Arm.Stream.Common`. -/
section

/-!
# Streaming SHA-256 on ARMv7: calling the compression function, and saving registers

What HMAC and PBKDF2, which call SHA-256's compression function themselves and
save our caller's registers where its streaming code does, use: the call
(`compressAt`), and saving and restoring the registers (`save`, `restore`). The
streaming `update` and `finalize` are proven generically
(`Proof/Sha256/Arm/Stream/Md.lean`), and the per-instruction rules are
`VG.Proof.MdStream.Arm`'s.
-/

namespace VG.Proof.Sha256.Arm.Stream

open VG VG.Arm VG.Impl.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm (compress_verified contains_offset)
open VG.Proof.MdStream.Arm (Upd WP.cons op2_imm wp_mov wp_ldr wp_str)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## The compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem r0_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r0 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r0) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem r3_ok : ∀ i ∈ instrs Impl.Sha256.Arm.compress, dstOf i ≠ some .r3 := by
  have : ((instrs Impl.Sha256.Arm.compress).all fun i => dstOf i != some .r3) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- Compressing the block at `r1` into the hash value at `r0`, with scratch
space at `r3`. -/
theorem compressAt_ok {s : State} {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + 32 ≤ 2 ^ 32) (f₁ : src.toNat + 64 ≤ 2 ^ 32) (f₃ : scr.toNat + 112 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, 32⟩ ⟨State.addr scr, 112⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr st, 32⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, 64⟩ ⟨State.addr scr, 112⟩)
    (hc : Covers [⟨State.addr src, 64⟩, ⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr src)) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt compressCall
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have e0 : s₁.gpr .r0 = st := by rw [u₁.other _ (by decide), h0]
  have e1 : s₁.gpr .r1 = src := by rw [u₁.other _ (by decide), h1]
  have e2 : s₁.gpr .r2 = 1 := u₁.gpr
  have e3 : s₁.gpr .r3 = scr := by rw [u₁.other _ (by decide), h3]
  have c : ∀ r, r ∉ linkRegs → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr s₁ h
  refine WP.call (k := Proof.Sha256.compressArm) compress_verified.1
    (rd := [⟨State.addr src, 64 * 1⟩]) (wr := [⟨State.addr st, 32⟩, ⟨State.addr scr, 112⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), c _ (show Reg.r3 ∉ linkRegs by decide), e0, e1, e2, e3]
    exact ⟨rfl, trivial, d₁, d₂, d₃, f₀, by simpa using f₁, f₃⟩
  · rw [u₁.rd, u₁.wr]; simpa using hc
  · rw [u₁.wr]; exact hw
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha256.compressArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, e2, u₁.mem] at hpost
    rw [show (BitVec.toNat (1 : BitVec 32)) = 1 from rfl, VG.Proof.Sha256.Arm.Stream.compressBlocks_one] at hpost
    refine hQ s' (hrd.trans u₁.rd) (hwr.trans u₁.wr) (fun r hr hlr => ?_) (by rw [hg _ VG.Proof.Sha256.Arm.Stream.r0_ok (by decide), e0])
      (by rw [hg _ VG.Proof.Sha256.Arm.Stream.r3_ok (by decide), e3]) (hsp.trans u₁.sp) (u₁.mem ▸ hf) hpost
    have : r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr hlr, u₁.other r this]

/-! ## Saving and restoring our caller's registers -/

theorem saved_slots : Spill.Slots 112 148 saved := by decide

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 148 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = Proof.MdStream.Arm.saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_slots_ok VG.Proof.Sha256.Arm.Stream.saved_slots (by omega) hin (k _ rfl rfl rfl rfl rfl)

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (Proof.MdStream.Arm.saveMem m B g saved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 :=
  Spill.saveMem_saved B g m saved VG.Proof.Sha256.Arm.Stream.saved_slots

theorem saveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ 160) → Frame [⟨B, 160⟩] m (Proof.MdStream.Arm.saveMem m B g l) :=
  Spill.saveMem_frame m B g (by decide)

theorem saved_bound : ∀ p ∈ saved, p.2 + 4 ≤ 160 ∧ 112 ≤ p.2 := by decide

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr) (hfit : scr.toNat + 160 ≤ 2 ^ 32)
    (hin : ∀ d, 112 ≤ d → d + 4 ≤ 148 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → (∀ r, r ∉ saved.map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  rw [restore, ← List.append_nil (saved.map _)]
  subst h3
  exact Spill.restore_slots_ok VG.Proof.Sha256.Arm.Stream.saved_slots (by decide) (by omega) hin hsv
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' ho hr hm hrd hwr hsp)

end VG.Proof.Sha256.Arm.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.Arm.Stream.Init`. -/
section

/-!
# Streaming SHA-256 on ARMv7: `init`
-/

namespace VG.Proof.Sha256.Arm.Stream

open VG VG.Arm VG.Impl.Sha256.Arm.Stream
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.MdStream.Arm (WP.cons wp_str)
open VG.Spec.Sha256 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `[r0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movw .r12 (x.extractLsb' 0 16), .movt .r12 (x.extractLsb' 16 16), .str .r12 .r0 off]

variable (iv : Spec.Sha256.HashValue)

theorem initWith_eq : initWith iv = .block (VG.Proof.Sha256.Arm.Stream.word iv[0] 0 ++ VG.Proof.Sha256.Arm.Stream.word iv[1] 4 ++ VG.Proof.Sha256.Arm.Stream.word iv[2] 8 ++ VG.Proof.Sha256.Arm.Stream.word iv[3] 12 ++
    VG.Proof.Sha256.Arm.Stream.word iv[4] 16 ++ VG.Proof.Sha256.Arm.Stream.word iv[5] 20 ++ VG.Proof.Sha256.Arm.Stream.word iv[6] 24 ++ VG.Proof.Sha256.Arm.Stream.word iv[7] 28) := rfl

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off < 4096) {rest : List Instr}
    {s : State} {Q : State → Prop} (hfit : (s.gpr .r0).toNat + off < 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Proof.Sha256.Arm.Stream.word x off ++ rest)) s Q := by
  simp only [VG.Proof.Sha256.Arm.Stream.word, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl ?_)
  refine wp_str ho (by simp only [State.setReg]; exact addr_add hfit) hout fun s' u => ?_
  refine k s' (fun r hr => by rw [u.gpr]; simp [State.setReg, hr]) u.rd u.wr u.sp ?_
  rw [u.mem]
  simp only [State.setReg, ite_true, movw_movt]

theorem init_correct {s₀ : State} (hp : (Proof.Sha256.initArm iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha256.initArm iv).post s₀ s' := by
  obtain ⟨-, hwr, hfit⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨State.addr (s₀.gpr .r0), 96⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [VG.Proof.Sha256.Arm.Stream.initWith_eq, ← List.append_nil (_ ++ VG.Proof.Sha256.Arm.Stream.word iv[7] 28)]
  simp only [List.append_assoc]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by omega) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .r0 = s₀.gpr .r0 := g1 _ (by decide)
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k1]; omega) (by rw [wr1, k1]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .r0 = s₀.gpr .r0 := by rw [g2 _ (by decide), k1]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k2]; omega) (by rw [wr2, wr1, k2]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .r0 = s₀.gpr .r0 := by rw [g3 _ (by decide), k2]
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k3]; omega) (by rw [w3, k3]; exact o 3 (by omega))
    fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : s4.gpr .r0 = s₀.gpr .r0 := by rw [g4 _ (by decide), k3]
  have w4 : s4.wr = s₀.wr := by rw [wr4, w3]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k4]; omega) (by rw [w4, k4]; exact o 4 (by omega))
    fun s5 g5 _ wr5 sp5 m5 => ?_
  have k5 : s5.gpr .r0 = s₀.gpr .r0 := by rw [g5 _ (by decide), k4]
  have w5 : s5.wr = s₀.wr := by rw [wr5, w4]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k5]; omega) (by rw [w5, k5]; exact o 5 (by omega))
    fun s6 g6 _ wr6 sp6 m6 => ?_
  have k6 : s6.gpr .r0 = s₀.gpr .r0 := by rw [g6 _ (by decide), k5]
  have w6 : s6.wr = s₀.wr := by rw [wr6, w5]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k6]; omega) (by rw [w6, k6]; exact o 6 (by omega))
    fun s7 g7 _ wr7 sp7 m7 => ?_
  have k7 : s7.gpr .r0 = s₀.gpr .r0 := by rw [g7 _ (by decide), k6]
  have w7 : s7.wr = s₀.wr := by rw [wr7, w6]
  refine VG.Proof.Sha256.Arm.Stream.word_ok (by decide) (by rw [k7]; omega) (by rw [w7, k7]; exact o 7 (by omega))
    fun s8 g8 _ _ sp8 m8 => WP.block_nil ?_
  have k8 : ∀ r, r ≠ .r12 → s8.gpr r = s₀.gpr r := fun r h => by
    rw [g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s8.mem = Proof.Sha256.StateMem.writeState s₀.mem (State.addr (s₀.gpr .r0)) iv := by
    rw [m8, m7, m6, m5, m4, m3, m2, m1, k7, k6, k5, k4, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k8 r ?_, by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Sha256.ReprFrom iv s8.mem (State.addr (s₀.gpr .r0)) []
    rw [hm]
    exact Proof.Sha256.Stream.reprFrom_nil (Proof.Sha256.StateMem.stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

/-- `initWith iv` is verified, given that the taint analysis, which the
kernel can only run on a literal `iv`, accepts it. -/
theorem initWith_verified {hc} (hct : (taint.check (Taint.ofRegs [.r0]) (initWith iv) hc).isSome = true) :
    Verified Arm.target (initWith iv) (Proof.Sha256.initArm iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨VG.Proof.Sha256.Arm.Stream.initSat, rfl, rfl, by decide⟩⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.Sha256.Arm.Stream.init_correct iv hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) (fun _ _ _ _ hp => ?_) hct
    exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp

theorem init_verified : Verified Arm.target init (Proof.Sha256.initArm H0) :=
  VG.Proof.Sha256.Arm.Stream.initWith_verified _ (hct := by taint_decide)

theorem init224_verified : Verified Arm.target init224 (Proof.Sha256.initArm Spec.Sha256.H0_224) :=
  VG.Proof.Sha256.Arm.Stream.initWith_verified _ (hct := by taint_decide)

end VG.Proof.Sha256.Arm.Stream

end
