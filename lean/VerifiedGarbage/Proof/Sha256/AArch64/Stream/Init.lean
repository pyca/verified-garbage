import VerifiedGarbage.Proof.MdStream.AArch64.Words
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common`. -/
section

/-!
# SHA-256 on AArch64: calling the compression function

The call of the compression function (`compressAt`), as HMAC-SHA-256 and
PBKDF2-HMAC-SHA-256 use it. The weakest-precondition rules it is proved
with are the generic ones (`VG.Proof.MdStream.AArch64`).
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (compress_verified)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz one_toNat)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress)

/-! ## The compression function -/

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem compress_noFrames : Impl.Sha256.AArch64.compress.noFrames = true := by lit_decide

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {s : State} {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, 32⟩ ⟨scr, 112⟩) (d₂ : Region.Disjoint ⟨src, 64⟩ ⟨st, 32⟩)
    (d₃ : Region.Disjoint ⟨src, 64⟩ ⟨scr, 112⟩)
    (hc : Covers [⟨src, 64⟩, ⟨st, 32⟩, ⟨scr, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 32⟩, ⟨scr, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, 32⟩, ⟨scr, 112⟩] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem src) → Q s') :
    WP isa compressAt s Q := by
  unfold compressAt
  refine WP.seq (wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .x0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19]
  have e1 : s₃.gpr .x1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1]
  have e2 : s₃.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .x3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h20]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .x2 = BitVec.setWidth 64 (1 : BitVec 16) :=
    (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := Proof.Sha256.compressAArch64) compress_verified.1
    (rd := [⟨src, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨scr, 112⟩]) ?_ ?_ ?_ ?_ VG.Proof.Sha256.AArch64.Stream.compress_noFrames
  · simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, one_toNat]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Sha256.compressAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, one_toNat, VG.Proof.Sha256.AArch64.Stream.compressBlocks_one, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr h30 => (hcs r hr h30).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf) hpost

end VG.Proof.Sha256.AArch64.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init`. -/
section

/-!
# Streaming SHA-256 on AArch64: `init`
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Proof.MdStream.AArch64 (WP.cons)
open VG.Spec.Sha256 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `[x0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movz .w .x9 (x.extractLsb' 0 16) 0, .movk .w .x9 (x.extractLsb' 16 16) 1, .str .w .x9 .x0 off]

variable (iv : Spec.Sha256.HashValue)

theorem initWith_eq : initWith iv = .block (VG.Proof.Sha256.AArch64.Stream.word iv[0] 0 ++ VG.Proof.Sha256.AArch64.Stream.word iv[1] 4 ++ VG.Proof.Sha256.AArch64.Stream.word iv[2] 8 ++ VG.Proof.Sha256.AArch64.Stream.word iv[3] 12 ++
    VG.Proof.Sha256.AArch64.Stream.word iv[4] 16 ++ VG.Proof.Sha256.AArch64.Stream.word iv[5] 20 ++ VG.Proof.Sha256.AArch64.Stream.word iv[6] 24 ++ VG.Proof.Sha256.AArch64.Stream.word iv[7] 28) := rfl

/-- `movz` of the low half then `movk` of the high half, then a 32-bit store. -/
theorem movzk (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (x.extractLsb' 0 16))) &&& (65535 : BitVec 32) |||
        BitVec.setWidth 32 (x.extractLsb' 16 16) <<< 16)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.ofNat_eq_ofNat, BitVec.getLsbD_ofNat,
    VG.AArch64.testBit_65535, hi, decide_true, Bool.true_and, Nat.zero_add]
  rcases (by omega : i < 16 ∨ 16 ≤ i) with h | h <;>
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and,
    Bool.and_false, Bool.or_false, Bool.false_or, Bool.and_true, Bool.not_true, Bool.not_false]
  all_goals exact congrArg _ (by omega)

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Proof.Sha256.AArch64.Stream.word x off ++ rest)) s Q := by
  simp only [VG.Proof.Sha256.AArch64.Stream.word, List.cons_append, List.nil_append]
  refine WP.cons exec_movz_w (WP.cons exec_movk_w (WP.cons (exec_str_w ho ?_) (k _ ?_ rfl rfl rfl ?_)))
  · simpa [State.write] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, ite_true]
    congr 1
    exact VG.Proof.Sha256.AArch64.Stream.movzk x

theorem init_correct {s₀ : State} (hp : (Proof.Sha256.initAArch64 iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha256.initAArch64 iv).post s₀ s' := by
  apply WP.withPreservedV (hc := by rw [VG.Proof.Sha256.AArch64.Stream.initWith_eq]; rfl)
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .x0, 96⟩, by simp [hwr], VG.Proof.Sha256.StateMem.contains_offset (by omega) (by omega)⟩
  rw [VG.Proof.Sha256.AArch64.Stream.initWith_eq, ← List.append_nil (_ ++ VG.Proof.Sha256.AArch64.Stream.word iv[7] 28)]
  simp only [List.append_assoc]
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [wr1, g1 _ (by decide)]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [wr2, wr1, g2 _ (by decide), g1 _ (by decide)]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  have k3 : s3.gpr .x0 = s₀.gpr .x0 := by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [w3, k3]; exact o 3 (by omega)) fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : ∀ r, r ≠ .x9 → s4.gpr r = s₀.gpr r := fun r h => by rw [g4 r h, g3 r h, g2 r h, g1 r h]
  have w4 : s4.wr = s₀.wr := by rw [wr4, wr3, wr2, wr1]
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [w4, k4 _ (by decide)]; exact o 4 (by omega))
    fun s5 g5 _ wr5 sp5 m5 => ?_
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [wr5, w4, g5 _ (by decide), k4 _ (by decide)]; exact o 5 (by omega))
    fun s6 g6 _ wr6 sp6 m6 => ?_
  have w6 : s6.wr = s₀.wr := by rw [wr6, wr5, w4]
  have k6 : s6.gpr .x0 = s₀.gpr .x0 := by rw [g6 _ (by decide), g5 _ (by decide), k4 _ (by decide)]
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [w6, k6]; exact o 6 (by omega)) fun s7 g7 _ wr7 sp7 m7 => ?_
  have w7 : s7.wr = s₀.wr := by rw [wr7, w6]
  have k7 : s7.gpr .x0 = s₀.gpr .x0 := by rw [g7 _ (by decide), k6]
  refine VG.Proof.Sha256.AArch64.Stream.word_ok (by decide) (by rw [w7, k7]; exact o 7 (by omega)) fun s8 g8 _ _ sp8 m8 =>
    WP.block_nil ?_
  have k8 : ∀ r, r ≠ .x9 → s8.gpr r = s₀.gpr r := fun r h => by
    rw [g8 r h, g7 r h, g6 r h, g5 r h, k4 r h]
  have hm : s8.mem = VG.Proof.Sha256.StateMem.writeState s₀.mem (s₀.gpr .x0) iv := by
    rw [m8, m7, m6, m5, m4, m3, m2, m1]
    simp only [g7 _ (show Reg.x0 ≠ .x9 by decide), g6 _ (show Reg.x0 ≠ .x9 by decide),
      g5 _ (show Reg.x0 ≠ .x9 by decide), k4 _ (show Reg.x0 ≠ .x9 by decide),
      g3 _ (show Reg.x0 ≠ .x9 by decide), g2 _ (show Reg.x0 ≠ .x9 by decide),
      g1 _ (show Reg.x0 ≠ .x9 by decide)]
    rfl
  refine ⟨⟨fun r hr => k8 r ?_, by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Sha256.ReprFrom iv s8.mem (s₀.gpr .x0) []
    rw [hm]
    exact Proof.Sha256.Stream.reprFrom_nil (VG.Proof.Sha256.StateMem.stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

/-- `initWith iv` is verified, given that the taint analysis, which the
kernel can only run on a literal `iv`, accepts it. -/
theorem initWith_verified {hc} (hct : (taint.check (Taint.ofRegs [.x0]) (initWith iv) hc).isSome = true) :
    Verified AArch64.target (initWith iv) (Proof.Sha256.initAArch64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨VG.Proof.Sha256.AArch64.Stream.initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.Sha256.AArch64.Stream.init_correct iv hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) ?_ hct
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

theorem init_verified : Verified AArch64.target init (Proof.Sha256.initAArch64 H0) :=
  VG.Proof.Sha256.AArch64.Stream.initWith_verified _ (hct := by taint_decide)

theorem init224_verified : Verified AArch64.target init224 (Proof.Sha256.initAArch64 Spec.Sha256.H0_224) :=
  VG.Proof.Sha256.AArch64.Stream.initWith_verified _ (hct := by taint_decide)

end VG.Proof.Sha256.AArch64.Stream

end
