module

public import VerifiedGarbage.Proof.Pbkdf2.PPC64LE.Iterate
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public meta import VerifiedGarbage.Impl.Pbkdf2.PPC64LE
import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on PPC64LE: correctness

The entry block (`entry_ok`), the prologue (`setup_ok`, `fill_ok`), the
loop (`Iterate.lean`) and the epilogue (`epilogue_ok`) compose to `correct`.
`ct` is the taint analysis of `main` after the entry block, which
zero-extends `n`: `n` is public only in its low 32 bits, so the two runs
agree on the whole of `r5` only once correctness says what the block leaves
there (`RelCT.wpDep`). `verified` moves the proof to the shared contract
of an instance of the hash function, with no stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE

open VG VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params mov save restore saved compressAt)
open VG.Impl.Pbkdf2.PPC64LE (raO hvO blkO padLen prologue epilogue main entry iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (Dims Upd ShapeD CalleeOk wp_mov wp_addi wp_std wp_ld wp_lsl wp_lsr Saved
  saveMem saveMem_saved saveMem_frame save_ok restore_ok preserved_of untouched add_ofNat)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The entry block -/

/-- `(x << 32) >> 32` is the low 32 bits of `x`. -/
theorem zext32 (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- After the entry block: the return address in `r0`, `n` zero-extended in `r5`. -/
structure Entry (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = s₀.lr
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nn s₀)
  other : ∀ r, r ≠ .r0 → r ≠ .r5 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem entry_ok (s₀ : State) : WP isa (.block entry) s₀ (Entry s₀) := by
  refine Proof.MdStream.PPC64LE.WP.cons exec_mflr (wp_lsl (by decide) fun s₁ x₁ =>
    wp_lsr (by decide) fun s₂ x₂ => WP.block_nil ⟨?_, ?_, fun r h0 h5 => ?_, ?_, ?_, ?_, ?_⟩)
  · rw [x₂.other _ (by decide), x₁.other _ (by decide)]; rfl
  · rw [x₂.gpr, x₁.gpr, show (s₀.write .r0 s₀.lr).gpr .r5 = s₀.gpr .r5 from rfl, zext32]
  · rw [x₂.other r h5, x₁.other r h5]; simp only [State.write, h0, ite_false]
  · rw [x₂.mem, x₁.mem]; rfl
  · rw [x₂.rd, x₁.rd]; rfl
  · rw [x₂.wr, x₁.wr]; rfl
  · rw [x₂.sp, x₁.sp]; rfl

/-! ## The prologue -/

/-- The memory after saving our caller's registers and our return address. -/
def saveAll (P : Params) (s₀ : State) : Mem :=
  (saveMem P s₀.mem (scr s₀) s₀.gpr).writeW (scr s₀ + BitVec.ofNat 64 (raO P)) s₀.lr

/-- After saving our caller's registers and our return address and setting
up our registers. -/
structure Setup (P : Params) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = hv P s₀
  r27 : s.gpr .r27 = scr s₀
  r28 : s.gpr .r28 = blk P s₀
  r30 : s.gpr .r30 = tp s₀
  r31 : s.gpr .r31 = BitVec.ofNat 64 (nn s₀)
  r3 : s.gpr .r3 = key s₀
  r4 : s.gpr .r4 = up s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  mem : s.mem = saveAll P s₀

theorem saveMem_congr (P : Params) (m : Mem) (b : Addr) {g g' : Reg → BitVec 64}
    (h : ∀ r, r ≠ .r0 → r ≠ .r5 → g r = g' r) : saveMem P m b g = saveMem P m b g' := by
  simp only [saveMem, h .r26 (by decide) (by decide), h .r27 (by decide) (by decide),
    h .r28 (by decide) (by decide), h .r29 (by decide) (by decide), h .r30 (by decide) (by decide),
    h .r31 (by decide) (by decide)]

section
variable {P : Params} {D Wi : Nat} (hz : Sizes P D Wi) {s₀ : State} (hp : Pre P D Wi s₀)
include hz hp

theorem setup_ok {e : State} (he : Entry s₀ e) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Setup P s₀ s → WP isa (.block rest) s Q) :
    WP isa (.block (save P .r7 ++
      ([.store .d .r0 .r7 (raO P), .addi .r26 .r7 (hvO P), mov .r27 .r7, .addi .r28 .r7 (blkO P),
        mov .r30 .r6, mov .r31 .r5] : List Instr) ++ rest)) e Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_W := hz.W
  have := so8 hz
  have g7 : e.gpr .r7 = scr s₀ := he.other _ (by decide) (by decide)
  simp only [List.append_assoc]
  refine save_ok hz.dims (b := .r7) (by decide) (fun d h₁ h₂ => by
    rw [g7, he.wr]; exact in_scr hz hp rfl (by omega_using [h₂, hz_fits]))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_std (a := scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega_arith,
      by simp only [raO]; omega_arith⟩
    (by rw [g₁, g7]) (by rw [wr₁, he.wr]; exact in_scr hz hp rfl (by simp only [raO]; omega_using [hz_fits]))
    fun s₂ g₂ => ?_
  refine wp_addi (by simp only [hvO]; omega_arith) fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addi (by simp only [blkO]; omega_arith) fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => ?_
  have G : ∀ r, r ≠ .r26 → r ≠ .r27 → r ≠ .r28 → r ≠ .r30 → r ≠ .r31 → s₇.gpr r = s₁.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h2, u₃.other r h1, g₂.gpr]
  refine k s₇ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, rd₁, he.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, wr₁, he.wr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂.gpr, g₁, g7, hvO]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      g₂.gpr, g₁, g7]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g₁, g7, blkO]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g₁, he.other _ (by decide) (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂.gpr, g₁, he.r5]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁, he.other _ (by decide) (by decide)]
  · rw [G _ (by decide) (by decide) (by decide) (by decide) (by decide), g₁, he.other _ (by decide) (by decide)]
  · have : r ≠ .r26 ∧ r ≠ .r27 ∧ r ≠ .r28 ∧ r ≠ .r30 ∧ r ≠ .r31 ∧ r ≠ .r0 ∧ r ≠ .r5 := by
      revert r; decide
    rw [G r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1, g₁,
      he.other r this.2.2.2.2.2.1 this.2.2.2.2.2.2]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, g₂.sp, sp₁, he.sp]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, g₂.mem, m₁, g₁, g7, he.r0, he.mem, saveAll,
      saveMem_congr P _ _ he.other]

omit hp in
theorem saveAll_frame : Frame [⟨scr s₀, P.so + 56⟩] s₀.mem (saveAll P s₀) := by
  have := so8 hz
  refine ((saveMem_frame hz.dims s₀.mem (scr s₀) s₀.gpr).sub fun r hr => ?_).writeW
    (List.mem_singleton_self _) _
    (Offset.contains_base _ (by simp only [raO]; omega_arith) (by simp only [raO]; omega_arith))
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩

omit hp in
theorem saveAll_saved : SavedAll P s₀ (saveAll P s₀) := by
  have := so8 hz
  refine ⟨fun q hq => ?_, Mem.readW_writeW_self64 _ _ _⟩
  have hd := saved_off hz hq
  rw [saveAll, Mem.readW_writeW_sep (Offset.sep _ (.inl (by simp only [raO]; omega_using [hd]))
    (by omega_arith) (by simp only [raO]; omega_arith)) (by decide)]
  exact saveMem_saved hz.dims _ _ _ q hq

/-- Writing `U`, the padding and the length field into the block. -/
theorem fill_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) (hok : H.lenOk (P.B + D)) {s : State}
    (h : Setup P s₀ s) :
    WP isa (.block ((List.range (D / 4)).flatMap (Impl.Pbkdf2.PPC64LE.cp32 .r4 .r28 0 0) ++
      padLen P D ++ ([mov .r29 .r3] : List Instr))) s (Inv P D Wi H s₀ (nn s₀)) := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN
  have hz_pad := hz.pad; have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4; have hz_W := hz.W
  have := B_ge hz
  have : P.B % 4 = 0 := by rcases hz.dims.B with h | h <;> omega_arith
  have hD4 : 4 * (D / 4) = D := by omega_arith
  simp only [List.append_assoc]
  refine Proof.Hmac.Stream.PPC64LE.copy32_ok (by decide) (by decide) (by decide) (by decide) 0 0 (D / 4)
    ⟨by omega_arith, by omega_arith⟩ _ s _
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [h.r4, h.rd, hp.rd, add0]
    exact ⟨uR D s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [h.r28, blk0]; exact in_blk hz hp h.wr (by omega_using [hj, hz_pad])
  · rw [h.r4, h.r28, blk0, add0, hD4]
    exact hp.u_s.sep (Region.contains_self _ _) (Offset.contains_base _ (hz.hvND_W)
      (Nat.lt_of_le_of_lt hz.hvN_W (Nat.lt_of_le_of_lt hz.W (by decide))))
  rw [h.r28, h.r4, blk0, add0, hD4] at m₁
  refine padLen_ok hs hok hz.D4 hz.L4 this (hz.pad) (B_le hz) (s := s₁) (p := blk P s₀)
    (by rw [g₁ _ (by decide), h.r28])
    (by rw [g₁ _ (by decide), h.r26, add_ofNat, add_ofNat,
      show P.so + 56 + (P.N + P.B - P.L) = P.so + 56 + P.N + (P.B - P.L) by omega_using [hz_pad]])
    (fun a n h' => in_blk hz hp (wr₁.trans h.wr) h') fun s₄ g₄ rd₄ wr₄ sp₄ f₄ p₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => WP.block_nil ?_
  have hG : ∀ r ∈ kept, r ≠ .r29 → s₅.gpr r = s.gpr r := fun r hr h2 => by
    rw [u₅.other r h2, g₄ r (ne8 r hr) (ne11 r hr) h2, g₁ r (ne8 r hr)]
  have f₁ : Frame [⟨blk P s₀, P.B⟩] s.mem s₁.mem := by
    rw [m₁]; refine writeBytes_frame _ _ _ ?_
    rw [bytesAt_length]
    have := Offset.contains_base (blk P s₀) (d := 0) (n := D) (k := P.B) (hz.zD_B) (by omega_arith)
    rwa [blk0] at this
  have fM : Frame [⟨blk P s₀, P.B⟩] s.mem s₅.mem := by
    rw [u₅.mem]; exact f₁.trans f₄
  have fB : Frame (bodyR P D s₀) s.mem s₅.mem := fM.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_body (Nat.le_add_right _ _) (Nat.le_refl _)
  have fS : Frame [tR D s₀, scR Wi s₀] s₀.mem s.mem := by
    rw [h.mem]; exact saveAll_frame hz |>.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR Wi s₀, by simp, Region.sub_prefix (hz.hv_W)⟩
  refine ⟨⟨by rw [u₅.rd, rd₄, rd₁, h.rd], by rw [u₅.wr, wr₄, wr₁, h.wr],
    by rw [hG _ (by decide) (by decide), h.r26], by rw [hG _ (by decide) (by decide), h.r27],
    by rw [hG _ (by decide) (by decide), h.r28],
    by rw [u₅.gpr, g₄ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r3],
    by rw [hG _ (by decide) (by decide), h.r30],
    fun r hr => by rw [hG _ (untouched_kept r hr) (untouched_ne29 r hr), h.cs r hr],
    by rw [u₅.sp, sp₄, sp₁, h.sp],
    fS.trans (frame_scr (a := P.so + 56 + P.N) (hz.fits) fM)⟩,
    by rw [u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide), g₁ _ (by decide), h.r31],
    saved_frame hz hp (h.mem ▸ saveAll_saved hz) fB, by rw [u₅.mem]; exact p₄, Nat.le_refl _, ?_⟩
  · -- `U` and `T`.
    have hU : bytesAt s₅.mem (blk P s₀) D = bytesAt s₀.mem (up s₀) D := by
      rw [u₅.mem, u₄, m₁, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hz.D_lt64), h.mem]
      refine Memory.frame_bytesAt (saveAll_frame hz) (fun r hr => ?_) (hz.D_le64)
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.u_s.sub_right (Region.sub_prefix (hz.hv_W))
    have hT : bytesAt s₅.mem (tp s₀) D = bytesAt s₀.mem (tp s₀) D := by
      refine Memory.frame_bytesAt ((saveAll_frame hz).mono
        (rs' := [⟨scr s₀, P.so + 56⟩, ⟨blk P s₀, P.B⟩]) (by simp) |>.trans
        ((h.mem ▸ fM).mono (by simp))) (fun r hr => ?_) (hz.D_le64)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (hz.hv_W))
      · exact hp.t_s.sub_right (scr_sub s₀ (hz.fits))
    rw [hU, hT]

theorem prologue_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) (hok : H.lenOk (P.B + D)) {e : State}
    (he : Entry s₀ e) : WP isa (.block (prologue P D)) e (Inv P D Wi H s₀ (nn s₀)) := by
  have := setup_ok hz hp he (rest := (List.range (D / 4)).flatMap (Impl.Pbkdf2.PPC64LE.cp32 .r4 .r28 0 0) ++
    padLen P D ++ [mov .r29 .r3]) fun s h => fill_ok hz hp hs hok h
  unfold prologue
  simpa only [List.append_assoc] using this

omit hz hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {m : Mem}
    (hT : bytesAt m (tp s₀) D =
      Spec.Pbkdf2.iterate (stepM P D H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) D) (bytesAt s₀.mem (tp s₀) D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) S.digestBytes)
        (bytesAt s₀.mem (tp s₀) S.digestBytes) := by
  have hB : 0 < P.B := by have hl_DL := hl.DL; omega_arith
  rw [hl.hB] at hk
  rw [hl.hS] at ho
  have li : (xorPad k0 ipad).length = P.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = P.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length H hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {H : Md P.B P.N P.L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv D) {s : State}
    (h : Inv P D Wi H s₀ 0 s) :
    WP isa (.block (epilogue P)) s fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_W := hz.W
  have := so8 hz
  unfold epilogue
  rw [List.append_assoc]
  refine wp_ld (a := scr s₀ + BitVec.ofNat 64 (raO P)) ⟨by simp only [raO]; omega_arith,
      by simp only [raO]; omega_arith⟩
    (by rw [h.r27]) (in_scr' hz hp h.wr (by simp only [raO]; omega_arith)) fun s₁ u₁ => ?_
  show WP isa (.block (restore P ++ [.mtlr .r0])) s₁ _
  rw [WP.block_append_iff]
  refine restore_ok hz.dims (scr := scr s₀) (by rw [u₁.other _ (by decide), h.r27])
    (fun d _ hd₂ => by rw [u₁.rd, u₁.wr]; exact in_scr' hz hp h.wr (by omega_arith))
    s₀.gpr (by rw [u₁.mem]; exact h.saved.1)
    fun s' hsv hother hmem _ _ hsp => Proof.MdStream.PPC64LE.WP.cons exec_mtlr (WP.block_nil
      ⟨⟨fun r hr => ?_, by show s'.sp = _; rw [hsp, u₁.sp, h.sp], ?_⟩, fun k0 hk hi ho => ?_⟩)
  · refine preserved_of (P := P) hsv (fun r hr => ?_) r hr
    rw [hother r (untouched_not_saved _ r hr), u₁.other r (untouched_ne0 r hr), h.cs r hr]
  · show s'.gpr .r0 = s₀.lr
    rw [hother _ (by simp [saved]), u₁.gpr, h.saved.2]
  · show bytesAt s'.mem (s₀.gpr .r6) S.digestBytes = _
    rw [hmem, u₁.mem]; exact post_eq hl h.val.symm hk hi ho

end

/-! ## Correctness -/

/-- What the proof needs of a hash function, with its code's `Params`, a
`D`-byte digest and `Wi` bytes of scratch space: the sizes, the length field
and digest of its code, that its hash value depends only on the bytes it is
stored in, that the length field of a `B + D`-byte message is its byte
count's, and that it is the hash function `S` of the specification. -/
structure HashOk (P : Params) (D Wi : Nat) (S : StreamingHash) (H : Md P.B P.N P.L) (iv : H.HV) : Prop where
  sizes : Sizes P D Wi
  shape : ShapeD H D
  reloc : H.Reloc
  lenOk : H.lenOk (P.B + D)
  link : H.Link S iv D

theorem correct {P : Params} {D Wi : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D Wi S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P D Wi s₀) :
    WP isa (iterate P D name code) s₀ fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  unfold iterate main
  refine WP.seq (WP.mono (entry_ok s₀) fun e he => ?_)
  refine WP.seq (WP.mono (prologue_ok ho.sizes hp ho.shape ho.lenOk he) fun s₁ h => ?_)
  exact WP.seq (WP.mono (loop_ok ho.sizes hp ho.shape ho.reloc hf h) fun s₂ h₂ =>
    epilogue_ok ho.sizes hp ho.link h₂)

/-! ## Constant time -/

/-- `iterate` is constant time, given the taint analysis of `main`, for any
precondition (`iterK`'s, or `iterG`'s with any stack). -/
theorem ctOf (P : Params) (D : Nat) (name : String) (code : Prog isa) {pre : State → Prop}
    {pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
      (s₁.gpr .r5).setWidth 32 = (s₂.gpr .r5).setWidth 32 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧
      s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp)
    {hc : VG.Taint.Hint vectorTaint.T}
    (hb : (vectorTaint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (main P D name code) hc).isSome = true) :
    ConstantTime isa pre pub (iterate P D name code) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq ?_ (RelCT.taint (A := vectorTaint)
    (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (fun _ _ h => h) hb))
  have ag4 : ∀ s₁ s₂ : State, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.r3, .r4, .r6, .r7]) s₁ s₂ := by
    rintro s₁ s₂ ⟨_, _, hq⟩
    obtain ⟨h3, h4, _, h6, h7, hsp⟩ := hpub s₁ s₂ hq
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  refine RelCT.mono (RelCT.wpDep (F := Entry) (RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r6, .r7])
    ag4 (by taint_decide)) fun s₁ s₂ _ => ⟨entry_ok s₁, entry_ok s₂⟩) (fun _ _ h => h) ?_
  rintro s₁' s₂' ⟨-, σ₁, σ₂, ⟨_, _, hq⟩, a, b⟩
  obtain ⟨h3, h4, h5, h6, h7, hsp⟩ := hpub σ₁ σ₂ hq
  refine ⟨by rw [a.sp, b.sp, hsp], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a.other _ (by decide) (by decide), b.other _ (by decide) (by decide), h3]
  · rw [a.other _ (by decide) (by decide), b.other _ (by decide) (by decide), h4]
  · rw [a.r5, b.r5, nn, nn, h5]
  · rw [a.other _ (by decide) (by decide), b.other _ (by decide) (by decide), h6]
  · rw [a.other _ (by decide) (by decide), b.other _ (by decide) (by decide), h7]

/-- `iterate` is constant time, given the taint analysis of `main`. -/
theorem ct (P : Params) (D : Nat) (name : String) (code : Prog isa) (S : StreamingHash) (Wi : Nat)
    {hc : VG.Taint.Hint vectorTaint.T}
    (hb : (vectorTaint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (main P D name code) hc).isSome = true) :
    ConstantTime isa (iterK S Wi).pre (iterK S Wi).pub (iterate P D name code) :=
  ctOf P D name code (fun _ _ h => h) hb

/-! ## As PBKDF2's whole derivation calls it -/

/-- The streaming iteration's contract (`iterG`), with any stack: what
PBKDF2's whole derivation (`Proof/Pbkdf2/Whole/PPC64LE/`) calls `iterate`
with. -/
theorem pre_ofG {P : Params} {D Wi F : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (iterG S Wi F).pre s₀) : Pre P D Wi s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem correctG {P : Params} {D Wi : Nat} {S : StreamingHash} {H : Md P.B P.N P.L} {iv : H.HV}
    (ho : HashOk P D Wi S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code) (F : Nat) :
    ∀ s, (iterG S Wi F).pre s →
      ∃ t s', Exec isa (iterate P D name code) s t s' ∧ abiPreserved s s' ∧ (iterG S Wi F).post s s' :=
  fun _ hs => by
    obtain ⟨t, s', he, h₁, h₂⟩ := correct ho hf (pre_ofG ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩

/-- `iterG`'s precondition, with any stack, is `iterK`'s and more. -/
theorem iterK_of_iterG {S : StreamingHash} {Wi F : Nat} {s : State} (h : (iterG S Wi F).pre s) :
    (iterK S Wi).pre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem ctG {P : Params} {D : Nat} {name : String} {code : Prog isa} {S : StreamingHash} {Wi : Nat}
    (ct : ConstantTime isa (iterK S Wi).pre (iterK S Wi).pub (iterate P D name code)) (F : Nat) :
    ConstantTime isa (iterG S Wi F).pre (iterG S Wi F).pub (iterate P D name code) :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ct s₁ s₂ t₁ t₂ s₁' s₂' (iterK_of_iterG h₁) (iterK_of_iterG h₂) hp e₁ e₂

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

theorem iterate_noFrames (P : Params) (D : Nat) (name : String) {code : Prog isa} (hc : code.noFrames = true) :
    (iterate P D name code).noFrames = true := by
  simp [iterate, main, Impl.Pbkdf2.PPC64LE.body, Impl.Pbkdf2.PPC64LE.compressBlock, compressAt,
    Impl.MdStream.PPC64LE.compressWith, Code.noFrames, hc]

/-! ## The shared contract -/

theorem iterImp {I : Spec.Hmac.Instance} (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I PPC64LE.abi 0).pre s) :
    (iterK I.S (8 * I.scratch)).Implies (Proof.Pbkdf2.Instance.iterateContract I PPC64LE.abi 0) := by
  generic_implies [Proof.Pbkdf2.Instance.iterateContract, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig,
    iterK, PPC64LE.abi, PPC64LE.argRegs] using hs

/-- `iterate` against the shared contract of an instance `I` of the hash
function, with the `Wi` bytes of scratch space it uses, given its constant
time. -/
theorem verified {P : Params} {D Wi : Nat} {H : Md P.B P.N P.L} {iv : H.HV} {I : Spec.Hmac.Instance}
    (ho : HashOk P D Wi I.S H iv) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hfit : Wi ≤ 8 * I.scratch)
    (ct : ConstantTime isa (iterK I.S Wi).pre (iterK I.S Wi).pub (iterate P D name code))
    (hs : ∃ s, (Proof.Pbkdf2.Instance.iterateContract I PPC64LE.abi 0).pre s) :
    Verified PPC64LE.target (iterate P D name code) (Proof.Pbkdf2.Instance.iterateContract I PPC64LE.abi 0) := by
  have imp := iterImp hs
  have hS : I.S.stateBytes = P.N + P.B := ho.link.hS
  have hD : I.S.digestBytes = D := ho.link.hD
  have wide : ∀ s, (iterK I.S (8 * I.scratch)).pre s →
      (iterK I.S Wi).pre (s.withRegions s.rd [⟨s.gpr .r6, I.S.digestBytes⟩, ⟨s.gpr .r7, Wi⟩]) := by
    intro s ⟨h1, _, h3, h4, h5, h6, h7⟩
    exact ⟨h1, rfl, h3, h4.sub_right (Region.sub_prefix hfit), h5, h6.sub_right (Region.sub_prefix hfit),
      h7.sub_right (Region.sub_prefix hfit)⟩
  have v : Verified PPC64LE.target (iterate P D name code) (iterK I.S Wi) :=
    ⟨fun s hs => by
      obtain ⟨t, s', he, h₁, h₂⟩ := correct ho hf (pre_of hS hD hs); exact ⟨t, s', he, h₁, h₂⟩, ct,
      imp.sat_left.elim fun s h => ⟨_, wide s h⟩⟩
  refine (Verified.widen v (fun s => [⟨s.gpr .r6, I.S.digestBytes⟩, ⟨s.gpr .r7, Wi⟩]) wide
      (fun _ h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) imp.sat_left).of_implies imp
  obtain ⟨_, h2, _⟩ := h
  rw [h2]
  exact .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hfit⟩ .nil)

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `sc` bytes of scratch space. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r3 => 0x10000 | .r4 => 0x20000 | .r5 => 1 | .r6 => 0x30000 | .r7 => 0x40000
    | _ => 0
  lr := 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, sc⟩]

end VG.Proof.Pbkdf2.PPC64LE
