module

public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Contract
public import VerifiedGarbage.Impl.Pbkdf2.PPC64LE
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on PPC64LE

The same proof as on AArch64 (`Proof/Pbkdf2/AArch64/Iterate.lean`): the
iteration (`Impl/Pbkdf2/PPC64LE.lean`) is correct for any hash function the
generic streaming proofs describe (`Md`), whose code stores the length field
and writes the digest as `ShapeD` says, with any correct compression function
(`CalleeOk`), used as a black box through its proof; `Md.hmac_step` says that
its two compressions per step compute HMAC.

The first block moves the return address to `r0` and zero-extends `n`; the
rest (`main`) runs from that state, and the lemmas describe it in terms of
the entry state `s₀`. The contract (`iterK`) has the streaming iteration's
postcondition (`iterG`), and no stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.PPC64LE

open VG VG.PPC64LE
open VG.Impl.MdStream.PPC64LE (Params mov save restore saved compressAt)
open VG.Impl.Pbkdf2.PPC64LE (raO hvO blkO loadKey padFrom padLen xorW compressBlock body prologue epilogue
  main entry iterate)
open VG.Proof.MdStream (Md)
open VG.Proof.MdStream.PPC64LE (Dims Upd Mupd ShapeD CalleeOk wp_mov wp_li wp_addi wp_subi wp_std wp_stw wp_ld
  wp_lwz wp_lsl wp_lsr Saved saveMem saveMem_saved saveMem_frame saved_offset save_ok restore_ok
  preserved_of untouched add_ofNat ofNat_pred ofNat_beq_zero eval_zero eval_nonzero compressAt_ok setWidth32)
open VG.Proof.Pbkdf2.Stream.PPC64LE (iterG)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame writeBytes_append)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## The contract -/

/-- The contract the proof is written against: `Proof.Pbkdf2.iterateContract`
of the streaming hash function `S` with `Wi` bytes of scratch space, on
PPC64LE, with no stack. -/
def iterK (S : StreamingHash) (Wi : Nat) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 2 * S.stateBytes⟩
    let u : Region := ⟨s.gpr .r4, S.digestBytes⟩
    let t : Region := ⟨s.gpr .r6, S.digestBytes⟩
    let scratch : Region := ⟨s.gpr .r7, Wi⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch
  post := (iterG S Wi 0).post
  pub := (iterG S Wi 0).pub

/-! ## What the proof needs of a hash function -/

/-- The sizes the proof supports, checked for each hash function by `decide`:
words of 4 bytes, a digest of at most the hash value, room for the padding
in the block after the digest, and room in the scratch space (`Wi` bytes) for
the compression function's, our caller's registers, our return address, the
hash value and the block. -/
structure Sizes (P : Params) (D Wi : Nat) : Prop where
  dims : Dims P
  N4 : P.N % 4 = 0
  D4 : D % 4 = 0
  L4 : P.L % 4 = 0
  D0 : 0 < D
  DN : D ≤ P.N
  NL : P.N + P.L ≤ P.B
  pad : D + 4 ≤ P.B - P.L
  fits : P.so + 56 + P.N + P.B ≤ Wi
  W : Wi ≤ 8192

/-! ## The precondition -/

section
variable (P : Params) (D Wi : Nat) (s₀ : State)

abbrev key : Addr := s₀.gpr .r3
abbrev up : Addr := s₀.gpr .r4
abbrev tp : Addr := s₀.gpr .r6
abbrev scr : Addr := s₀.gpr .r7
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .r5).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * (P.N + P.B)⟩
abbrev uR : Region := ⟨up s₀, D⟩
abbrev tR : Region := ⟨tp s₀, D⟩
abbrev scR : Region := ⟨scr s₀, Wi⟩
/-- The hash value being compressed, and the block. -/
abbrev hv : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 56)
abbrev blk : Addr := scr s₀ + BitVec.ofNat 64 (P.so + 56 + P.N)

end

structure Pre (P : Params) (D Wi : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR P s₀, uR D s₀]
  wr : s₀.wr = [tR D s₀, scR Wi s₀]
  k_t : (keyR P s₀).Disjoint (tR D s₀)
  k_s : (keyR P s₀).Disjoint (scR Wi s₀)
  u_t : (uR D s₀).Disjoint (tR D s₀)
  u_s : (uR D s₀).Disjoint (scR Wi s₀)
  t_s : (tR D s₀).Disjoint (scR Wi s₀)

theorem pre_of {P : Params} {D Wi : Nat} {S : StreamingHash} (hS : S.stateBytes = P.N + P.B)
    (hD : S.digestBytes = D) {s₀ : State} (h : (iterK S Wi).pre s₀) : Pre P D Wi s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-! ## The parts of the scratch space -/

section
variable {P : Params} {D Wi : Nat} (hz : Sizes P D Wi)
include hz

theorem so_le : P.so ≤ 1024 := hz.dims.so.2
theorem so8 : P.so % 8 = 0 ∧ P.so ≤ 1024 := hz.dims.so
theorem saved_off {q : Reg × Nat} (hq : q ∈ saved P) : P.so ≤ q.2 ∧ q.2 + 8 ≤ P.so + 48 :=
  saved_offset hz.dims hq
theorem N_le : P.N ≤ 64 := hz.dims.N.2
theorem B_le : P.B ≤ 128 := by rcases hz.dims.B with h | h <;> omega_arith
theorem B_ge : 64 ≤ P.B := by rcases hz.dims.B with h | h <;> omega_arith

/-! Bounds the proofs use many times, proved once from `Sizes`'s fields by
`Nat` lemmas rather than by `omega` at each use. -/

theorem Sizes.N_le_B : P.N ≤ P.B := Nat.le_trans (Nat.le_add_right _ _) hz.NL
theorem Sizes.L_le_B : P.L ≤ P.B := Nat.le_trans (Nat.le_add_left _ _) hz.NL
theorem Sizes.D_le_B : D ≤ P.B := Nat.le_trans hz.DN hz.N_le_B
theorem Sizes.B_lt64 : P.B < 2 ^ 64 := Nat.lt_of_le_of_lt (B_le hz) (by decide)
theorem Sizes.B_le32 : P.B ≤ 2 ^ 32 := Nat.le_trans (B_le hz) (by decide)
theorem Sizes.N_lt64 : P.N < 2 ^ 64 := Nat.lt_of_le_of_lt hz.N_le_B hz.B_lt64
theorem Sizes.N_le32 : P.N ≤ 2 ^ 32 := Nat.le_trans hz.N_le_B hz.B_le32
theorem Sizes.D_lt64 : D < 2 ^ 64 := Nat.lt_of_le_of_lt hz.D_le_B hz.B_lt64
theorem Sizes.D_le64 : D ≤ 2 ^ 64 := Nat.le_of_lt hz.D_lt64
theorem Sizes.hvN_W : P.so + 56 + P.N ≤ Wi := Nat.le_trans (Nat.le_add_right _ _) hz.fits
theorem Sizes.hv_W : P.so + 56 ≤ Wi := Nat.le_trans (Nat.le_add_right _ _) hz.hvN_W
theorem Sizes.so_W : P.so ≤ Wi := Nat.le_trans (Nat.le_add_right _ _) hz.hv_W
theorem Sizes.W_le64 : Wi ≤ 2 ^ 64 := Nat.le_trans hz.W (by decide)
theorem Sizes.hvN_64 : P.so + 56 + P.N ≤ 2 ^ 64 := Nat.le_trans hz.hvN_W hz.W_le64
theorem Sizes.hvN_32 : P.so + 56 + P.N ≤ 2 ^ 32 := Nat.le_trans hz.hvN_W (Nat.le_trans hz.W (by decide))
theorem Sizes.hvNB_64 : P.so + 56 + P.N + P.B ≤ 2 ^ 64 := Nat.le_trans hz.fits hz.W_le64
theorem Sizes.hvNN_W : P.so + 56 + P.N + P.N ≤ Wi :=
  Nat.le_trans (Nat.add_le_add_left hz.N_le_B _) hz.fits
theorem Sizes.hvNN_64 : P.so + 56 + P.N + P.N ≤ 2 ^ 64 := Nat.le_trans hz.hvNN_W hz.W_le64
theorem Sizes.hvND_W : P.so + 56 + P.N + D ≤ Wi :=
  Nat.le_trans (Nat.add_le_add_left hz.D_le_B _) hz.fits
theorem Sizes.B_sub_D_64 : P.B - D ≤ 2 ^ 64 := Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt hz.B_lt64)
theorem Sizes.zD_B : 0 + D ≤ P.B := Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) hz.D_le_B
theorem Sizes.D_BD : D + (P.B - D) ≤ P.B := Nat.le_of_eq (Nat.add_sub_of_le hz.D_le_B)

omit hz in
theorem scr_sub (s₀ : State) {a n : Nat} (h : a + n ≤ Wi) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ (scR Wi s₀) :=
  Offset.sub_base _ h

end

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The registers during a step -/

/-- The registers `main` keeps between its pieces: ours but the count, and
the nonvolatile ones it never writes. -/
abbrev kept : List Reg := [.r26, .r27, .r28, .r29, .r30, .r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
  .r21, .r22, .r23, .r24, .r25]

theorem ne8 : ∀ r ∈ kept, r ≠ .r8 := by decide
theorem ne9 : ∀ r ∈ kept, r ≠ .r9 := by decide
theorem ne11 : ∀ r ∈ kept, r ≠ .r11 := by decide
theorem ne4 : ∀ r ∈ kept, r ≠ .r4 := by decide
theorem ne31 : ∀ r ∈ kept, r ≠ .r31 := by decide
theorem kept_preserved : ∀ r ∈ kept, r ∈ preserved := by decide
theorem untouched_kept : ∀ r ∈ untouched, r ∈ kept := by decide
theorem untouched_ne29 : ∀ r ∈ untouched, r ≠ .r29 := by decide
theorem untouched_ne0 : ∀ r ∈ untouched, r ≠ .r0 := by decide
theorem untouched_not_saved (P : Params) : ∀ r ∈ untouched, r ∉ (saved P).map Prod.fst := by
  simp only [saved, List.map_cons, List.map_nil]; decide

/-- What holds between the pieces of a step: the regions, our registers, the
nonvolatile registers we never write, the stack pointer, and memory outside
the scratch space and `T` as on entry. -/
structure Regs (P : Params) (D Wi : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = hv P s₀
  r27 : s.gpr .r27 = scr s₀
  r28 : s.gpr .r28 = blk P s₀
  r29 : s.gpr .r29 = key s₀
  r30 : s.gpr .r30 = tp s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  frame : Frame [tR D s₀, scR Wi s₀] s₀.mem s.mem

section
variable {P : Params} {D Wi : Nat} (hz : Sizes P D Wi) {s₀ : State} (hp : Pre P D Wi s₀)

/-- `Regs` after code that keeps our registers and writes only memory in the
regions it allows. -/
theorem Regs.write {s s' : State} (h : Regs P D Wi s₀ s) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hm : Frame [tR D s₀, scR Wi s₀] s.mem s'.mem) : Regs P D Wi s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := (hg _ (by decide)).trans h.r26
  r27 := (hg _ (by decide)).trans h.r27
  r28 := (hg _ (by decide)).trans h.r28
  r29 := (hg _ (by decide)).trans h.r29
  r30 := (hg _ (by decide)).trans h.r30
  cs := fun r hr => (hg r (untouched_kept r hr)).trans (h.cs r hr)
  sp := hsp.trans h.sp
  frame := h.frame.trans hm

omit hp in
/-- A part of the scratch space, as a frame of `Regs`. -/
theorem frame_scr {m m' : Mem} {a n : Nat} (h : a + n ≤ Wi)
    (hf : Frame [⟨scr s₀ + BitVec.ofNat 64 a, n⟩] m m') : Frame [tR D s₀, scR Wi s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR Wi s₀, by simp, scr_sub s₀ h⟩

include hz hp

theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ Wi) :
    InRegions s.wr (scr s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR Wi s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hz_W := hz.W; omega_arith)⟩

theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ P.B) :
    InRegions s.wr (blk P s₀ + BitVec.ofNat 64 a) n := by
  have hz_fits := hz.fits
  rw [add_ofNat]; exact in_scr hz hp hwr (by omega_arith)

theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ Wi) :
    InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := in_scr hz hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- The hash value at `key + o` into the scratch space. -/
theorem load_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {s : State} (h : Regs P D Wi s₀ s) {o : Nat}
    (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨hv P s₀, P.N⟩] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadKey P o ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have := hz.dims.N; have hz_N4 := hz.N4; have hz_fits := hz.fits
  have hn : 4 * (P.N / 4) = P.N := by omega_arith
  unfold loadKey
  refine Proof.Hmac.Stream.PPC64LE.copy32_ok (by decide) (by decide) (by decide) (by decide) o 0 (P.N / 4)
    ⟨by omega_arith, by omega_arith⟩ rest s Q
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s' g' rd' wr' sp' m' => ?_
  · rw [h.r29, h.rd, hp.rd, add_ofNat]
    exact ⟨keyR P s₀, by simp, Offset.contains_base _ (by omega_using [hj, ho]) (by omega_arith)⟩
  · rw [h.r26, h.wr, hp.wr, add_ofNat, add_ofNat]
    exact ⟨scR Wi s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · rw [h.r29, h.r26, hn, add_ofNat, Nat.add_zero]
    exact hp.k_s.sep (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (Offset.contains_base _ (hz.hvN_W) (by omega_arith))
  rw [h.r26, h.r29, hn, add_ofNat, Nat.add_zero] at m'
  refine k s' g' rd' wr' sp' (by rw [m']; exact writeBytes_frame _ _ _ (by
    rw [bytesAt_length]; exact Region.contains_self _ _)) ?_
  refine hR _ _ _ _ fun i hi => ?_
  rw [m', writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_arith),
    bytesAt_getD' _ _ hi, add_ofNat]
  exact h.frame.bytes (R := keyR P s₀) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_t
    · exact hp.k_s) (by show 2 * (P.N + P.B) ≤ 2 ^ 64; omega_arith)
    (by show o + i < 2 * (P.N + P.B); omega_using [hi, ho])

/-- A call of the compression function on the block. -/
theorem cmp_ok {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : CalleeOk H code) {s : State}
    (h : Regs P D Wi s₀ s) {Q : State → Prop}
    (k : ∀ s', Regs P D Wi s₀ s' → s'.gpr .r31 = s.gpr .r31 →
      Frame [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (hv P s₀) = H.compress (H.stateAt s.mem (hv P s₀)) (H.blockAt s.mem (blk P s₀)) →
      Q s') :
    WP isa (compressBlock name code) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ => WP.block_nil ?_)
  have h₁ := h.write (fun r hr => u₁.other r (ne4 r hr)) u₁.rd u₁.wr u₁.sp (by rw [u₁.mem]; exact Frame.refl _ _)
  have hsc : scR Wi s₀ ∈ s₁.wr := by simp [h₁.wr, hp.wr]
  refine compressAt_ok hf h₁.r26 h₁.r27 (by rw [u₁.gpr, h.r28])
    (Offset.disjoint_base _ (Nat.le_add_right _ _) (hz.hvN_64))
    (Offset.disjoint _ (.inr (Nat.le_refl _)) (hz.hvNB_64) (hz.hvN_64))
    (Offset.disjoint_base _ (by omega_arith) (hz.hvNB_64)) ?_ ?_ fun s' hrd hwr hcs hsp hfr hst => ?_
  · refine Covers.of_sub fun r hr => ⟨scR Wi s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨0, by simp, by dsimp only; omega_arith⟩
  · refine Covers.of_sub fun r hr => ⟨scR Wi s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨0, by simp, by dsimp only; omega_arith⟩
  have cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => by
    rw [hcs r hr, u₁.other r (by revert r; decide)]
  rw [u₁.mem] at hfr hst
  refine k s' (h.write (fun r hr => cs r (kept_preserved r hr))
    (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp) (hfr.sub fun r hr => ?_))
    (cs _ (by decide)) hfr hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨scR Wi s₀, by simp, scr_sub s₀ (hz.hvN_W)⟩
  · exact ⟨scR Wi s₀, by simp, Region.sub_prefix (hz.so_W)⟩

end

/-! ## Words of the block and of `T` -/

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  Proof.MdStream.PPC64LE.WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem xor_setWidth (a b : BitVec 32) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 32 = a ^^^ b := by
  rw [BitVec.setWidth_xor, setWidth32, setWidth32]

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

/-- `T ← T ⊕ U` for the first `n` 32-bit words of `T` at `tp` and `U` at `bp`. -/
theorem xor_ok {tp bp : Addr} {D : Nat} (hd : Region.Disjoint ⟨tp, D⟩ ⟨bp, D⟩) (hD : D ≤ 4096) :
    ∀ n, 4 * n ≤ D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r28 = bp → s.gpr .r30 = tp →
    (∀ k < n, InRegions (s.rd ++ s.wr) (bp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r8 → r ≠ .r9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp h30 hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_arith) _ s Q hbp h30 (fun j hj => hin j (by omega_arith))
      (fun j hj => hout j (by omega_arith)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    have hw := hout n (Nat.lt_succ_self _)
    refine wp_lwz (a := bp + BitVec.ofNat 64 (4 * n)) (by omega_arith)
      (by rw [g₁ _ (by decide) (by decide), hbp]) (by rw [rd₁, wr₁]; exact hin n (Nat.lt_succ_self _))
      fun s₂ u₂ => ?_
    refine wp_lwz (a := tp + BitVec.ofNat 64 (4 * n)) (by omega_arith)
      (by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h30])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_xor fun s₄ u₄ => ?_
    refine wp_stw (a := tp + BitVec.ofNat 64 (4 * n)) (by omega_arith)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        g₁ _ (by decide) (by decide), h30])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₅ g₅ => k s₅ (fun r h8 h9 => by
          rw [g₅.gpr, u₄.other r h8, u₃.other r h9, u₂.other r h8, g₁ r h8 h9])
        (by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem bp (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [g₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₃.mem, u₂.gpr, u₂.mem, xor_setWidth,
      writeW_xor32, m₁,
      bytesAt_writeBytes_sep (p := tp + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := bp + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (bp + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega_arith)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega_arith) (Memory.off_contains h₁ (by omega_arith) (by omega_arith))
    · omega_arith
    · intro x h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega_arith)
    · omega_arith

/-- Stores of zero (the low 32 bits of `r8`) at `r28 + a + 4 + 4 k`, for `k < n`. -/
theorem zeros_ok {a : Nat} {p : Addr} : ∀ n, a + 4 + 4 * n ≤ 2 ^ 15 →
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .r28 = p → (s.gpr .r8).setWidth 32 = 0 →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 (a + 4)) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.store .w .r8 .r28 (a + 4 + 4 * k)) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro ha rest s Q hbp hax hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega_using [ha]) _ s Q hbp hax (fun j hj => hout j (by omega_arith))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_stw (a := p + BitVec.ofNat 64 (a + 4 + 4 * n)) (by omega_using [ha]) (by rw [g₁, hbp])
      (by rw [wr₁]; exact hout n (Nat.lt_succ_self _)) fun s₂ g₂ =>
        k s₂ (by rw [g₂.gpr, g₁]) (by rw [g₂.rd, rd₁]) (by rw [g₂.wr, wr₁]) (by rw [g₂.sp, sp₁]) ?_
    rw [g₂.mem, g₁, hax, m₁, Memory.writeW_bytes _ _ (0 : BitVec 32) [0, 0, 0, 0] (by decide),
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate, add_ofNat]) (by simp; omega_using [ha]),
      Nat.mul_succ, ← List.replicate_append_replicate]
    rfl

/-- `padFrom a b` writes `0x80` and zeros from byte `a` to byte `b` of the block at `r28`. -/
theorem padFrom_ok {a b : Nat} (hab : a + 4 ≤ b) (h4 : (b - a) % 4 = 0) (hb : b ≤ 2 ^ 15)
    {s : State} {p : Addr}
    (hbp : s.gpr .r28 = p) (hout : ∀ k < (b - a) / 4, InRegions s.wr (p + BitVec.ofNat 64 (a + 4 * k)) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (p + BitVec.ofNat 64 a) ([0x80] ++ List.replicate (b - a - 1) 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (padFrom a b ++ rest)) s Q := by
  unfold padFrom
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_stw (a := p + BitVec.ofNat 64 a) (by omega_using [hb, hab]) (by rw [u₁.other _ (by decide), hbp])
    (by rw [u₁.wr]; simpa using hout 0 (by omega_arith)) fun s₂ g₂ => ?_
  refine wp_li (by decide) fun s₃ u₃ => ?_
  refine zeros_ok (a := a) ((b - a) / 4 - 1) (by omega_using [hb, hab]) rest s₃ Q
    (by rw [u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), hbp]) (by rw [u₃.gpr]; rfl)
    (fun j hj => by
      rw [u₃.wr, g₂.wr, u₁.wr, show a + 4 + 4 * j = a + 4 * (j + 1) by omega_arith]
      exact hout (j + 1) (by omega_arith))
    fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => k s₄ (fun r hr => by
      rw [g₄, u₃.other r hr, g₂.gpr, u₁.other r hr]) (by rw [rd₄, u₃.rd, g₂.rd, u₁.rd])
      (by rw [wr₄, u₃.wr, g₂.wr, u₁.wr]) (by rw [sp₄, u₃.sp, g₂.sp, u₁.sp]) ?_
  rw [m₄, u₃.mem, g₂.mem, u₁.gpr, u₁.mem,
    show ((BitVec.ofNat 64 0x80).setWidth 32 : BitVec 32) = 0x80 from rfl,
    Memory.writeW_bytes _ _ (0x80 : BitVec 32) [0x80, 0, 0, 0] (by decide),
    Memory.writeBytes_append' _ _ _ (by rw [List.length_cons, List.length_cons, List.length_cons,
      List.length_singleton, add_ofNat]) (by simp; omega_arith),
    show b - a - 1 = 3 + 4 * ((b - a) / 4 - 1) by omega_arith, ← List.replicate_append_replicate]
  rfl

/-- `padLen` writes the rest of the block at `p` (`r28`) after its first `D`
bytes, which it keeps: the padding of a `B + D`-byte message, whose length
field `P.len` stores at `r26 + N + B - L`, the block's end. -/
theorem padLen_ok {P : Params} {D : Nat} {H : Md P.B P.N P.L} (hs : ShapeD H D) (hok : H.lenOk (P.B + D))
    (hD4 : D % 4 = 0) (hL4 : P.L % 4 = 0) (hB4 : P.B % 4 = 0) (hpad : D + 4 ≤ P.B - P.L) (hB : P.B ≤ 128)
    {s : State} {p : Addr} (hbp : s.gpr .r28 = p)
    (hbx : s.gpr .r26 + BitVec.ofNat 64 (P.N + P.B - P.L) = p + BitVec.ofNat 64 (P.B - P.L))
    (hw : ∀ a n, a + n ≤ P.B → InRegions s.wr (p + BitVec.ofNat 64 a) n) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r8 → r ≠ .r11 → r ≠ .r29 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Frame [⟨p, P.B⟩] s.mem s'.mem →
      bytesAt s'.mem (p + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem p D = bytesAt s.mem p D → WP isa (.block rest) s' Q) :
    WP isa (.block (padLen P D ++ rest)) s Q := by
  unfold padLen
  simp only [List.append_assoc]
  refine padFrom_ok (a := D) (b := P.B - P.L) (by omega_arith) (by omega_arith) (by omega_using [hB]) hbp
    (fun j hj => hw _ _ (by omega_using [hj])) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  refine wp_li (by omega_using [hB, hpad]) fun s₃ u₃ => ?_
  change WP isa (.block (P.len ++ rest)) s₃ Q
  rw [WP.block_append_iff]
  refine WP.mono (hs.len s₃ ?_) fun s₄ ⟨g₄, rd₄, wr₄, sp₄, m₄⟩ => ?_
  · rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.wr, wr₂]; exact hw _ _ (by omega_using [hpad])
  rw [u₃.other _ (by decide), g₂ _ (by decide), hbx, u₃.gpr, H.lenOf_eq _ hok, u₃.mem, m₂] at m₄
  have lpz : ([0x80] ++ List.replicate (P.B - P.L - D - 1) 0 : List Byte).length = P.B - P.L - D := by
    simp; omega_using [hpad]
  have S1 : Mem.Sep p D (p + BitVec.ofNat 64 D) (P.B - P.L - D) := by
    have := Offset.sep p (d := 0) (n := D) (e := D) (k := P.B - P.L - D) (.inl (Nat.le_of_eq (Nat.zero_add _)))
      (by omega_using [hB, hpad]) (by omega_using [hB, hpad])
    rwa [add0] at this
  have S2 : ∀ {a n : Nat}, a + n ≤ P.B - P.L →
      Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 (P.B - P.L)) P.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hB]) (by omega_using [hB, hpad])
  refine k s₄ (fun r h1 h2 h3 => by rw [g₄ r h1 h2, u₃.other r h3, g₂ r h1]) (by rw [rd₄, u₃.rd, rd₂])
    (by rw [wr₄, u₃.wr, wr₂]) (by rw [sp₄, u₃.sp, sp₂]) ?_ ?_ ?_
  · rw [m₄]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [lpz]; exact Offset.contains_base _ (by omega_using [hpad]) (by omega_using [hB, hpad])
    · rw [H.lenBytes_length]; exact Offset.contains_base _ (by omega_using [hpad]) (by omega_using [hB])
  · rw [show P.B - D = (P.B - P.L - D) + P.L by omega_using [hpad], bytesAt_add, add_ofNat p,
      show D + (P.B - P.L - D) = P.B - P.L by omega_using [hpad], m₄,
      bytesAt_writeBytes_self' (H.lenBytes_length _) (by omega_using [hB, hpad]),
      bytesAt_writeBytes_sep _ _ (by rw [H.lenBytes_length]; exact S2 (by omega_using [hpad])) (by omega_using [hB]),
      bytesAt_writeBytes_self' lpz (by omega_arith), Md.tailPad,
      show P.B - P.L - 1 - D = P.B - P.L - D - 1 by omega_using []]
  · rw [m₄, bytesAt_writeBytes_sep _ _ (by
        rw [H.lenBytes_length]; have := S2 (a := 0) (n := D) (by omega_using [hpad]); rwa [add0] at this)
        (by omega_arith),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (by omega_arith)]

/-! ## The digest into the block -/

theorem blk0 (P : Params) (s₀ : State) : blk P s₀ + BitVec.ofNat 64 0 = blk P s₀ := add0 _

section
variable {P : Params} {D Wi : Nat} (hz : Sizes P D Wi) {s₀ : State} (hp : Pre P D Wi s₀)
include hz hp

/-- The digest of the hash value into the block's first `D` bytes, the padding after them as it was. -/
theorem digest_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) {s : State} (h : Regs P D Wi s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {rest : List Instr}
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [⟨blk P s₀, D⟩] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D → WP isa (.block rest) s' Q) :
    WP isa (.block (P.out ++ rest)) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN
  have hz_NL := hz.NL
  rw [WP.block_append_iff]
  refine WP.mono (hs.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  · rw [h.r26]; exact in_scr' hz hp h.wr (a := P.so + 56) (n := P.N) (hz.hvN_W)
  · rw [h.r28]; exact in_scr hz hp h.wr (hz.hvND_W)
  · rw [h.r26, h.r28]; exact Offset.disjoint _ (.inl (Nat.le_refl _)) (hz.hvN_64)
      (Nat.le_trans (Nat.add_le_add_left hz.DN _) hz.hvNN_64)
  rw [h.r28, h.r26] at m₁
  have hdl : ((H.digest (H.stateAt s.mem (hv P s₀))).take D).length = D := by
    rw [List.length_take, H.digest_length]; exact Nat.min_eq_left hz.DN
  refine k s₁ g₁ rd₁ wr₁ sp₁ ?_ ?_ ?_
  · rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
  · rw [m₁, bytesAt_writeBytes_self' hdl (hz.D_lt64)]
  · rw [m₁, bytesAt_writeBytes_sep _ _ ?_ (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hz.B_lt64), hpad]
    have := Offset.sep (blk P s₀) (d := D) (n := P.B - D) (e := 0) (k := D) (.inr (Nat.le_of_eq (Nat.zero_add _)))
      (by omega_using [this, hz_DN, hz_NL]) (by omega_using [this, hz_DN, hz_NL])
    rw [hdl]; rwa [blk0] at this

end

/-! ## A step -/

section
variable (P : Params) (D : Nat) (H : Md P.B P.N P.L) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  H.step D (H.stateAt s₀.mem (key s₀)) (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 (P.N + P.B)))

/-- What the body writes: the compression function's scratch space, the hash
value and the block, and `T`. -/
abbrev bodyR : List Region := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩, tR D s₀]

/-- Our caller's registers and our return address, saved in the scratch space. -/
def SavedAll (m : Mem) : Prop :=
  Saved P (scr s₀) s₀.gpr m ∧ m.readW (scr s₀ + BitVec.ofNat 64 (raO P)) 64 = s₀.lr

end

/-- The loop invariant, with `r` steps left. -/
structure Inv (P : Params) (D Wi : Nat) (H : Md P.B P.N P.L) (s₀ : State) (r : Nat) (s : State) : Prop
    extends Regs P D Wi s₀ s where
  r31 : s.gpr .r31 = BitVec.ofNat 64 r
  saved : SavedAll P s₀ s.mem
  pad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM P D H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) D) (bytesAt s₀.mem (tp s₀) D) =
    Spec.Pbkdf2.iterate (stepM P D H s₀) r (bytesAt s.mem (blk P s₀) D) (bytesAt s.mem (tp s₀) D)

section
variable {P : Params} {D Wi : Nat} (hz : Sizes P D Wi) {s₀ : State} (hp : Pre P D Wi s₀)
include hz hp

/-- The saved registers are outside what the body writes. -/
theorem saved_frame {m m' : Mem} (h : SavedAll P s₀ m) (hf : Frame (bodyR P D s₀) m m') :
    SavedAll P s₀ m' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits
  have rd : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 56 →
      m'.readW (scr s₀ + BitVec.ofNat 64 d) 64 = m.readW (scr s₀ + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact (hp.t_s.sub_right (scr_sub s₀ (by omega_arith))).symm
  refine ⟨fun q hq => ?_, ?_⟩
  · have hd := saved_off hz hq
    rw [← h.1 q hq]
    exact rd _ hd.1 (by show q.2 + 8 ≤ P.so + 56; omega_arith)
  · rw [← h.2]; exact rd _ (by simp only [raO]; omega_arith) (by simp only [raO]; omega_arith)

omit hz hp in
/-- A range of the scratch space from `hv` on, within what the body writes. -/
theorem sub_body {a n : Nat} (h₁ : P.so + 56 ≤ a) (h₂ : a + n ≤ P.so + 56 + P.N + P.B) :
    ∃ r' ∈ bodyR P D s₀, Region.Sub ⟨scr s₀ + BitVec.ofNat 64 a, n⟩ r' :=
  ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ h₁ (by omega_arith)⟩

omit hp in
/-- A range of the block disjoint from what the compression and loading the hash value write. -/
theorem blk_disj {a n : Nat} (h : a + n ≤ P.B) :
    ∀ r ∈ [⟨hv P s₀, P.N⟩, ⟨scr s₀, P.so⟩], Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [add_ofNat]
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inr (Nat.le_add_right _ _)) (by omega_arith) (hz.hvN_64)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- Loading the key's hash value at `key + o` and compressing the block into it. -/
theorem lc_ok {H : Md P.B P.N P.L} (hR : H.Reloc) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {o : Nat} (ho : o + P.N ≤ 2 * (P.N + P.B)) (ho4 : o % 4 = 0) {s : State} (h : Regs P D Wi s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', Regs P D Wi s₀ s' → s'.gpr .r31 = s.gpr .r31 → Frame (bodyR P D s₀) s.mem s'.mem →
      Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩] s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D →
      H.stateAt s'.mem (hv P s₀) =
        H.compress (H.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o)) (H.tailBlock D (bytesAt s.mem (blk P s₀) D)) →
      WP isa c s' Q) :
    WP isa (.block (loadKey P o)) s fun s' => WP isa (.seq (compressBlock name code) c) s' Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN
  have hz_pad := hz.pad; have hz_NL := hz.NL
  rw [← List.append_nil (loadKey P o)]
  refine load_ok hz hp hR h (o := o) ho ho4 fun s₁ g₁ rd₁ wr₁ sp₁ f₁ e₁ => WP.block_nil ?_
  have h₁ := h.write (fun r hr => g₁ r (ne8 r hr)) rd₁ wr₁ sp₁ (frame_scr (a := P.so + 56) (hz.hvN_W) f₁)
  refine WP.seq (cmp_ok hz hp hf h₁ fun s₂ h₂ r31₂ f₂ e₂ => ?_)
  have fh₁ : ∀ {a n : Nat}, a + n ≤ P.B → ∀ r ∈ [(⟨hv P s₀, P.N⟩ : Region)],
      Region.Disjoint ⟨blk P s₀ + BitVec.ofNat 64 a, n⟩ r :=
    fun h' r hr => blk_disj hz h' r (by simp at hr; simp [hr])
  have p₁ : bytesAt s₁.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D :=
    (Memory.frame_bytesAt f₁ (fh₁ (hz.D_BD)) (hz.B_sub_D_64)).trans hpad
  have u₁ : bytesAt s₁.mem (blk P s₀) D = bytesAt s.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₁ (fh₁ (a := 0) (n := D) (hz.zD_B)) (hz.D_le64); rwa [blk0] at this
  have u₂ : bytesAt s₂.mem (blk P s₀) D = bytesAt s₁.mem (blk P s₀) D := by
    have := Memory.frame_bytesAt f₂ (blk_disj hz (a := 0) (n := D) (hz.zD_B)) (hz.D_le64); rwa [blk0] at this
  rw [e₁, H.blockAt_eq (hz.D_le_B) p₁, u₁] at e₂
  have f : Frame [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N⟩] s.mem s₂.mem :=
    (f₁.mono (by simp)).trans (f₂.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)
  refine k s₂ h₂ (r31₂.trans (g₁ _ (by decide))) (f.sub fun r hr => ?_) f
    ((Memory.frame_bytesAt f₂ (blk_disj hz (hz.D_BD)) (hz.B_sub_D_64)).trans p₁) (u₂.trans u₁) e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨scr s₀, P.so⟩, by simp, fun _ h => h⟩
  · exact sub_body (Nat.le_refl _) (Nat.le_add_right _ _)

/-- The end of a step: the digest into the block, `T ← T ⊕ U` and the count. -/
theorem tail_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) {s : State} (h : Regs P D Wi s₀ s)
    (hpad : bytesAt s.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D) {Q : State → Prop}
    (k : ∀ s', Regs P D Wi s₀ s' → s'.gpr .r31 = s.gpr .r31 - BitVec.ofNat 64 1 →
      Frame (bodyR P D s₀) s.mem s'.mem →
      bytesAt s'.mem (blk P s₀ + BitVec.ofNat 64 D) (P.B - D) = H.tailPad D →
      bytesAt s'.mem (blk P s₀) D = (H.digest (H.stateAt s.mem (hv P s₀))).take D →
      bytesAt s'.mem (tp s₀) D =
        Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) D) ((H.digest (H.stateAt s.mem (hv P s₀))).take D) → Q s') :
    WP isa (.block (P.out ++ (List.range (D / 4)).flatMap xorW ++ ([.subi .r31 .r31 1] : List Instr))) s Q := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN
  have hz_D4 := hz.D4; have hz_W := hz.W; have hz_pad := hz.pad; have hz_NL := hz.NL
  rw [List.append_assoc]
  refine digest_ok hz hp hs h hpad fun s₆ g₆ rd₆ wr₆ sp₆ f₆ b₆ p₆ => ?_
  have f₆' : Frame [⟨scr s₀ + BitVec.ofNat 64 (P.so + 56 + P.N), D⟩] s.mem s₆.mem := f₆
  have h₆ := h.write (fun r hr => g₆ r (ne8 r hr) (ne11 r hr)) rd₆ wr₆ sp₆ (frame_scr (hz.hvND_W) f₆')
  have hd : Region.Disjoint (tR D s₀) ⟨blk P s₀, D⟩ := hp.t_s.sub_right (scr_sub s₀ (hz.hvND_W))
  have hD4 : 4 * (D / 4) = D := by omega_arith
  refine xor_ok hd (by omega_using [hz_pad, this]) (D / 4) (by omega_using []) _ s₆ _ h₆.r28 h₆.r30
    (fun j hj => by
      obtain ⟨r, hr, hc⟩ := in_blk hz hp h₆.wr (a := 4 * j) (n := 4) (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (fun j hj => ⟨tR D s₀, by simp [h₆.wr, hp.wr], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun s₇ g₇ rd₇ wr₇ sp₇ m₇ => ?_
  rw [hD4] at m₇
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (tp s₀) D) (bytesAt s₆.mem (blk P s₀) D)).length = D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₇ : Frame [tR D s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have h₇ := h₆.write (fun r hr => g₇ r (ne8 r hr) (ne9 r hr)) rd₇ wr₇ sp₇ (f₇.mono (by simp))
  refine wp_subi (by decide) fun s₈ u₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r hr => u₈.other r (ne31 r hr)) u₈.rd u₈.wr u₈.sp (by rw [u₈.mem]; exact Frame.refl _ _)
  have r31₇ : s₇.gpr .r31 = s.gpr .r31 := by
    rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide)]
  have hT₆ : bytesAt s₆.mem (tp s₀) D = bytesAt s.mem (tp s₀) D :=
    Memory.frame_bytesAt f₆' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.t_s.sub_right (scr_sub s₀ (hz.hvND_W))) (hz.D_le64)
  refine k s₈ h₈ (by rw [u₈.gpr, r31₇]) ?_ ?_ ?_ ?_
  · rw [u₈.mem]
    refine (f₆'.sub fun r hr => ?_).trans (f₇.mono (by simp))
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_body (Nat.le_add_right _ _) (Nat.add_le_add_left hz.D_le_B _)
  · rw [u₈.mem]
    exact (Memory.frame_bytesAt f₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.t_s.sub_right (by rw [add_ofNat]; exact scr_sub s₀ (by omega_using [hz_pad, hz_fits]))).symm)
      (hz.B_sub_D_64)).trans p₆
  · rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (hd.symm.sep (Region.contains_self _ _) (by
      rw [hxl]; exact Region.contains_self _ _)) (hz.D_lt64), b₆]
  · rw [u₈.mem, m₇, bytesAt_writeBytes_self' hxl (hz.D_lt64), hT₆, b₆]

omit hz hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) {r : Nat} {s : State} (h : Inv P D Wi H s₀ (r + 1) s) :
    WP isa (body P D name code) s fun s' =>
      eval (.nonzero .d .r31) s' = some (r != 0) ∧ Inv P D Wi H s₀ r s' := by
  have := so_le hz; have := N_le hz; have := B_le hz; have hz_fits := hz.fits; have hz_DN := hz.DN
  have hz_pad := hz.pad; have hz_NL := hz.NL
  unfold body
  refine WP.seq (lc_ok hz hp hR hf (o := 0) (by omega_using []) rfl h.toRegs h.pad
    fun s₂ h₂ r31₂ f₂ g₂ p₂ _ e₂ => ?_)
  refine WP.seq (digest_ok hz hp hs h₂ p₂ fun s₃ g₃ rd₃ wr₃ sp₃ f₃ b₃ p₃ => ?_)
  have f₃' : Frame [⟨scr s₀ + BitVec.ofNat 64 (P.so + 56 + P.N), D⟩] s₂.mem s₃.mem := f₃
  have h₃ := h₂.write (fun r hr => g₃ r (ne8 r hr) (ne11 r hr)) rd₃ wr₃ sp₃ (frame_scr (hz.hvND_W) f₃')
  refine lc_ok hz hp hR hf (o := P.N + P.B) (by omega_arith)
    (by have hz_N4 := hz.N4; rcases hz.dims.B with h | h <;> omega_arith) h₃ p₃
    fun s₅ h₅ r31₅ f₅ g₅ p₅ _ e₅ => ?_
  refine tail_ok hz hp hs h₅ p₅ fun s₈ h₈ r31₈ f₈ p₈ b₈ t₈ => ?_
  rw [e₅, b₃, e₂, add0] at b₈ t₈
  have r31₅' : s₅.gpr .r31 = BitVec.ofNat 64 (r + 1) := by
    rw [r31₅, g₃ _ (by decide) (by decide), r31₂, h.r31]
  have hlt : r + 1 < 2 ^ 64 := by
    have h_le := h.le; have := ((s₀.gpr .r5).setWidth 32).isLt; simp at *; omega_using [h_le]
  have e₈ : s₅.gpr .r31 - BitVec.ofNat 64 1 = BitVec.ofNat 64 r := by
    rw [r31₅', show BitVec.ofNat 64 1 = 1 from rfl, ofNat_pred (Nat.le_add_left _ _)]; rfl
  have fb : Frame (bodyR P D s₀) s.mem s₈.mem :=
    ((f₂.trans (f₃'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_body (Nat.le_add_right _ _) (Nat.add_le_add_left hz.D_le_B _))).trans f₅).trans f₈
  have hT₅ : bytesAt s₅.mem (tp s₀) D = bytesAt s.mem (tp s₀) D := by
    refine Memory.frame_bytesAt (rs := [⟨scr s₀, P.so⟩, ⟨hv P s₀, P.N + P.B⟩])
      (((g₂.sub fun r hr => ?_).trans (f₃'.sub fun r hr => ?_)).trans (g₅.sub fun r hr => ?_))
      (fun r hr => ?_) (hz.D_le64)
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (Nat.le_add_right _ _)⟩
    · subst hr; exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Offset.sub _ (Nat.le_add_right _ _) (by omega_arith)⟩
    · rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨hv P s₀, P.N + P.B⟩, by simp, Region.sub_prefix (Nat.le_add_right _ _)⟩
    · rcases hr with rfl | rfl
      · exact hp.t_s.sub_right (Region.sub_prefix (hz.so_W))
      · exact hp.t_s.sub_right (scr_sub s₀ (by omega_using [hz_fits]))
  rw [hT₅] at t₈
  refine ⟨?_, h₈, by rw [r31₈, e₈], saved_frame hz hp h.saved fb, p₈, by have h_le := h.le; omega_arith, ?_⟩
  · simp only [eval_nonzero, r31₈, e₈, bne, ofNat_beq_zero (by omega_arith : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl

theorem loop_ok {H : Md P.B P.N P.L} (hs : ShapeD H D) (hR : H.Reloc) {name : String} {code : Prog isa}
    (hf : CalleeOk H code) {n : Nat} {s : State} (h : Inv P D Wi H s₀ n s) :
    WP isa (.ite (.zero .d .r31) (.block []) (.loop (body P D name code) (.nonzero .d .r31))) s
      (Inv P D Wi H s₀ 0) := by
  have hlt : n < 2 ^ 64 := by
    have h_le := h.le; have := ((s₀.gpr .r5).setWidth 32).isLt; simp at *; omega_arith
  refine WP.ite (decide (n = 0)) (by change eval (.zero .d .r31) s = _; rw [eval_zero, h.r31, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega_arith⟩
    refine WP.loop (fun m s => Inv P D Wi H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hz hp hs hR hf hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega_arith, hi⟩

end

end VG.Proof.Pbkdf2.PPC64LE
