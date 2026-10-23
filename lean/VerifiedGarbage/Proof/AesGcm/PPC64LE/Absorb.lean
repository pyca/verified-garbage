module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on PPC64LE: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`n` bytes at `D` (`r18`, `r19`) into GHASH, with the accumulator at
`St + yo` and the `r20` buffered bytes at `St + 32` (`absorb_wp`): it fills
the buffer (`fill_wp`, absorbing it if full), absorbs whole blocks
(`whole_wp`) and buffers the rest (`tail_wp`), by the steps of
`Proof/Gcm/Stream.lean`. Between them, `AbsMid k` says the first `k` bytes
are absorbed and `r18`, `r19` are what is left.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gcm
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_add wp_sub wp_lsr wp_lsl wp_and)
open VG.Proof.Gather.PPC64LE (Keeps eval_zero BytesPre copyBytes_wp)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Spec.Aes (bytesAt)

/-! ## Memory outside the pieces' regions -/

/-- Bytes apart from `St` and the first 2112 bytes of `W` are kept. -/
theorem bytesAt_keep {W St : Addr} {m m' : Mem} (hf : Frame (pieceRs W St) m m') {p : Addr} {n : Nat}
    (hs : (⟨p, n⟩ : Region).Disjoint (stR St)) (hw : (⟨p, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs
    · exact hw.sub_right (Region.sub_prefix (by decide))) hn

theorem blockAt_keep {W St : Addr} {m m' : Mem} (hf : Frame (pieceRs W St) m m') {p : Addr}
    (hs : (⟨p, 16⟩ : Region).Disjoint (stR St)) (hw : (⟨p, 16⟩ : Region).Disjoint ⟨W, 2560⟩) :
    blockAt m' p = blockAt m p := by
  simp only [blockAt]; rw [bytesAt_keep hf hs hw (by decide)]

/-- The hash subkey is kept. -/
theorem hk_keep {s : State} {W St C : Addr} (h : Env s W St C) {m m' : Mem}
    (hf : Frame (pieceRs W St) m m') : hk m' C = hk m C :=
  blockAt_keep hf
    (by simpa only [BitVec.add_zero] using h.c_st (d := 240) (n := 16) (e := 0) (k := 80) (by decide) (by decide))
    (by simpa only [BitVec.add_zero] using
      h.c_w (d := 240) (n := 16) (e := 0) (k := 2560) (by decide) (by decide))

/-- A frame within the pieces' regions. -/
theorem frame_pieces {W St : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ pieceRs W St, Region.Sub r r') : Frame (pieceRs W St) m m' :=
  Frame.sub hf hs

/-! ## What `absorb` needs, and its steps -/

/-- The accumulator and the buffer. -/
abbrev yA (St : Addr) (yo : Nat) : Addr := St + BitVec.ofNat 64 yo
abbrev bA (St : Addr) : Addr := St + BitVec.ofNat 64 32

/-- What `absorb yo` needs: GHASH has absorbed `x` (with the hash subkey of
the key context), and the `n` bytes at `D` are readable and apart from `St`
and `W`. -/
structure AbsPre (s : State) (W St C : Addr) (yo : Nat) (D : Addr) (n : Nat) (x : List Byte) : Prop where
  env : Env s W St C
  hyo : yo = 0 ∨ yo = 16
  r18 : s.gpr .r18 = D
  r19 : s.gpr .r19 = BitVec.ofNat 64 n
  r20 : s.gpr .r20 = BitVec.ofNat 64 (x.length % 16)
  abs : Absorbed s.mem (yA St yo) (bA St) (hk s.mem C) x
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  dst : (⟨D, n⟩ : Region).Disjoint (stR St)
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  fit : D.toNat + n ≤ 2 ^ 64
  lt : n < 2 ^ 64

/-- After absorbing the first `k` bytes from `s₀`. -/
structure AbsMid (s₀ : State) (W St C : Addr) (yo : Nat) (D : Addr) (n : Nat) (x : List Byte) (k : Nat)
    (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame (pieceRs W St) s₀.mem s.mem
  r18 : s.gpr .r18 = D + BitVec.ofNat 64 k
  r19 : s.gpr .r19 = BitVec.ofNat 64 (n - k)
  abs : Absorbed s.mem (yA St yo) (bA St) (hk s₀.mem C) (x ++ bytesAt s₀.mem D k)
  le : k ≤ n

/-- What `absorb yo` does. -/
structure AbsPost (s₀ : State) (W St C : Addr) (yo : Nat) (D : Addr) (n : Nat) (x : List Byte)
    (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame (pieceRs W St) s₀.mem s.mem
  abs : Absorbed s.mem (yA St yo) (bA St) (hk s₀.mem C) (x ++ bytesAt s₀.mem D n)

theorem length_bytesAt' (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n :=
  Proof.AesGcm.length_bytesAt m p n

/-- Bytes written in the buffer keep the accumulator. -/
theorem keepY {s : State} {W St C : Addr} (h : Env s W St C) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    (m : Mem) {o : Nat} {xs : List Byte} (hl : o + xs.length ≤ 16) :
    blockAt (writeBytes m (St + BitVec.ofNat 64 (32 + o)) xs) (yA St yo) = blockAt m (yA St yo) := by
  simp only [blockAt]
  refine congrArg _ (Proof.Cmac.bytesAt_frame (Proof.AesGcm.writeBytes_frame' m rfl) (fun r hr => ?_)
    (by decide))
  simp only [List.mem_singleton] at hr; subst hr
  exact h.st_st (d := yo) (e := 32 + o) (by omega) (by omega) (by omega)

/-- The first `k` bytes of the data and the next `j`. -/
theorem bytesAt_split (m : Mem) (D : Addr) {k j : Nat} :
    bytesAt m D k ++ bytesAt m (D + BitVec.ofNat 64 k) j = bytesAt m D (k + j) :=
  (Proof.AesGcm.bytesAt_add m D k j).symm

theorem ofNat_shl4 {n : Nat} (hn : 16 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.shiftLeft_eq, show 2 ^ 4 = 16 from rfl, Nat.mul_comm]

theorem ofNat_and15 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 15 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 15 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem add_ofNat_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

section
variable {s₀ : State} {W St C : Addr} {yo : Nat} {D : Addr} {n : Nat} {x : List Byte}
  (hp : AbsPre s₀ W St C yo D n x)
include hp

/-- The data from `k` on, in a state the pieces lead to. -/
theorem AbsPre.data {k j : Nat} (hkj : k + j ≤ n) {m : Mem} (hf : Frame (pieceRs W St) s₀.mem m) :
    bytesAt m (D + BitVec.ofNat 64 k) j = bytesAt s₀.mem (D + BitVec.ofNat 64 k) j := by
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 k, j⟩ ⟨D, n⟩ := Offset.sub_base _ hkj
  exact bytesAt_keep hf (hp.dst.sub_left hs) (hp.dw.sub_left hs) (by have := hp.lt; omega)

theorem AbsPre.dCov {k j : Nat} (hkj : k + j ≤ n) {s : State} (hk : PK s₀ s) :
    Covers [⟨D + BitVec.ofNat 64 k, j⟩] (s.rd ++ s.wr) := by
  rw [hk.rd, hk.wr]; exact VG.Proof.Gather.PPC64LE.covers_off hp.rd hkj hp.lt

/-- The last `n - k` (fewer than 16) bytes buffered, once the first `k` are
absorbed to a whole number of blocks (or are all the data). -/
theorem tail_wp {k : Nat} {s : State} (hm : AbsMid s₀ W St C yo D n x k s) (hr : n - k < 16)
    (ha : (x.length + k) % 16 = 0 ∨ k = n) :
    WP isa absorbTail s (AbsPost s₀ W St C yo D n x) := by
  have he := hp.env.of_pk hm.pk
  unfold absorbTail
  refine WP.ite (decide (n - k = 0)) (eval_zero hm.r19 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have hk : k = n := by have := of_decide_eq_true ht; have := hm.le; omega
    subst hk
    exact WP.block_nil ⟨hm.pk, hm.frame, hm.abs⟩
  · have hk0 : n - k ≠ 0 := by simpa using hf
    have hal : (x ++ bytesAt s₀.mem D k).length % 16 = 0 := by
      rw [List.length_append, length_bytesAt']; omega
    refine WP.seq (wp_mv fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
      WP.block_nil ?_)
    have pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
    have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have hb : BytesPre s₃ (D + BitVec.ofNat 64 k) (St + BitVec.ofNat 64 32) (n - k) := by
      refine ⟨?_, ?_, ?_, by omega, by have := hp.lt; omega, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hm.r18]
      · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), he.r15]
      · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hm.r19]
      · exact hp.dCov (by omega) (hm.pk.trans pk₃)
      · rw [pk₃.wr]; exact he.stIn (by omega)
      · exact (hp.dst.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
    refine WP.mono (copyBytes_wp s₃ hb) fun s₄ ⟨m₄, _, kp₄⟩ => ⟨hm.pk.trans (pk₃.trans (PK.ofKeeps kp₄)),
      ?_, ?_⟩
    · rw [m₄, m₃]
      refine Frame.trans hm.frame (frame_pieces (Proof.AesGcm.writeBytes_frame' _ (length_bytesAt' ..))
        fun r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_st (by omega) W
    · have hd := hp.data (k := k) (j := n - k) (by omega) hm.frame
      have hsplit : bytesAt s₀.mem D n =
          bytesAt s₀.mem D k ++ bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k) := by
        rw [bytesAt_split, Nat.add_sub_cancel' hm.le]
      rw [m₄, m₃, hd, hsplit, ← List.append_assoc]
      refine absorb_tail hm.abs hal (by rw [length_bytesAt']; omega) ?_ ?_
      · have := keepY he hp.hyo s.mem (o := 0) (xs := bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k))
          (by rw [length_bytesAt']; omega)
        simpa only [Nat.add_zero] using this
      · have := Proof.AesGcm.bytesAt_writeBytes_self s.mem (bA St)
          (bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k)) (by rw [length_bytesAt']; omega)
        rw [length_bytesAt'] at this ⊢
        exact this

/-- The whole blocks of what is left absorbed, once the first `k` bytes are
absorbed to a whole number of blocks (or are all the data). -/
theorem whole_wp {k : Nat} {s : State} (hm : AbsMid s₀ W St C yo D n x k s)
    (ha : (x.length + k) % 16 = 0 ∨ k = n) :
    WP isa (absorbWhole yo) s fun s' => ∃ k', AbsMid s₀ W St C yo D n x k' s' ∧ n - k' < 16 ∧
      ((x.length + k') % 16 = 0 ∨ k' = n) := by
  have he := hp.env.of_pk hm.pk
  have hL := hp.lt
  have hle := hm.le
  unfold absorbWhole splitWhole
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => wp_and fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans
    ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r6₁ : s₁.gpr .r6 = BitVec.ofNat 64 ((n - k) / 16) := by
    rw [u₁.gpr, hm.r19, Proof.AesGcm.PPC64LE.ofNat_lsr4 (by omega)]
  have r6₆ : s₆.gpr .r6 = BitVec.ofNat 64 ((n - k) / 16) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), r6₁]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 64 (16 * ((n - k) / 16)) := by
    rw [u₂.gpr, r6₁, ofNat_shl4 (by omega)]
  have r5₆ : s₆.gpr .r5 = D + BitVec.ofNat 64 k := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hm.r18]
  have r18₆ : s₆.gpr .r18 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide),
      r7₂, u₂.other _ (by decide), u₁.other _ (by decide), hm.r18, add_ofNat_add]
  have r19₆ : s₆.gpr .r19 = BitVec.ofNat 64 (n - (k + 16 * ((n - k) / 16))) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hm.r19, ofNat_and15 (by omega)]
    congr 1; omega
  have r14₆ : s₆.gpr .r14 = W := by rw [pk₆.gpr .r14 (by decide), he.r14]
  have r15₆ : s₆.gpr .r15 = St := by rw [pk₆.gpr .r15 (by decide), he.r15]
  have r16₆ : s₆.gpr .r16 = C := by rw [pk₆.gpr .r16 (by decide), he.r16]
  refine WP.ite (decide ((n - k) / 16 = 0)) (eval_zero r6₆ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (n - k) / 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨k, ⟨hm.pk.trans pk₆, by rw [m₆]; exact hm.frame, by rw [r18₆, h0, Nat.mul_zero,
      Nat.add_zero], by rw [r19₆, h0, Nat.mul_zero, Nat.add_zero], by rw [m₆]; exact hm.abs, hm.le⟩,
      by omega, ha⟩
  · have h0 : (n - k) / 16 ≠ 0 := by simpa using hf
    have hal : (x.length + k) % 16 = 0 := ha.resolve_right (by omega)
    generalize hnb : (n - k) / 16 = nb at r6₆ r18₆ r19₆ h0
    refine WP.seq (wp_addi (by decide) (by decide) fun s₇ u₇ => wp_addi (by decide)
      (by rcases hp.hyo with h | h <;> omega) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_)
    have pk₉ : PK s₆ s₉ := (PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))
    have m₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, m₆]
    have hW0 : (⟨W, 256⟩ : Region) = ⟨W + BitVec.ofNat 64 0, 256⟩ := by rw [BitVec.add_zero]
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 k, 16 * nb⟩ ⟨D, n⟩ := Offset.sub_base _ (by omega)
    have hyo : yo + 16 ≤ 80 := by rcases hp.hyo with h | h <;> omega
    have hgp : GhPre s₉ (C + BitVec.ofNat 64 240) (yA St yo) (D + BitVec.ofNat 64 k) W nb := by
      refine ⟨?_, ?_, ?_, ?_, ?_, by omega, he.c_st (by decide) hyo, ?_,
        ((hp.dst.sub_left hsub).sub_right (Offset.sub_base _ hyo)).symm, ?_,
        ?_, by have := he.wfit; omega, ?_, ?_⟩
      · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, r16₆]
      · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r15₆]
      · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r5₆]
      · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r6₆]
      · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r14₆]
      · rw [hW0]; exact he.c_w (by decide) (by decide)
      · rw [hW0]; exact he.st_w hyo (by decide)
      · exact (hp.dw.sub_left hsub).sub_right (Region.sub_prefix (by decide))
      · rw [pk₉.rd, pk₉.wr, pk₆.rd, pk₆.wr]
        refine Covers.append_left (Covers.pair (he.cIn (d := 240) (n := 16) (by decide)) ?_)
          (Covers.pair (he.stRd hyo) ?_)
        · exact hp.dCov (by omega) hm.pk
        · rw [hW0]; exact he.wRd (by decide)
      · rw [pk₉.wr, pk₆.wr]
        refine Covers.pair (he.stIn hyo) ?_
        rw [hW0]; exact he.wIn (by decide)
    refine WP.mono (gh_call hgp) fun s' ⟨ck, hy⟩ => ⟨k + 16 * nb, ⟨hm.pk.trans (pk₆.trans
      (pk₉.trans (PK.ofCall ck))), ?_, ?_, ?_, ?_, by omega⟩, by omega, .inl (by omega)⟩
    · refine Frame.trans hm.frame (frame_pieces (m := s.mem) (by rw [← m₉]; exact ck.frame) fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_st hyo W
      · exact sub_w0 (by decide) St
    · rw [ck.saved .r18 (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), r18₆]
    · rw [ck.saved .r19 (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), r19₆]
    · have hd := hp.data (k := k) (j := 16 * nb) (by omega) hm.frame
      have hsplit : bytesAt s₀.mem D (k + 16 * nb) =
          bytesAt s₀.mem D k ++ bytesAt s₀.mem (D + BitVec.ofNat 64 k) (16 * nb) := by
        rw [bytesAt_split]
      rw [hsplit, ← List.append_assoc]
      refine absorb_whole hm.abs (by rw [List.length_append, length_bytesAt']; omega)
        (by rw [length_bytesAt']; omega) ?_
      rw [hy, m₉, blocksAt_eq, hd]
      change ghashFrom (hk s.mem C) _ _ = _
      rw [hk_keep hp.env hm.frame]

omit hp in
/-- `r5 = r20 - 16` when the buffer is full, and when not. -/
theorem sub16_full : BitVec.ofNat 64 16 - BitVec.ofNat 64 16 = BitVec.ofNat 64 0 := by decide

omit hp in
theorem sub16_lt {a : Nat} (ha : a < 16) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 16 = BitVec.ofNat 64 (2 ^ 64 + a - 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := 16) (by decide),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The buffer filled first, if it holds bytes (`o = x.length mod 16`): then
the first `k` bytes are absorbed, to a whole number of blocks or all the data. -/
theorem fill_wp (hn : n ≠ 0) :
    WP isa (absorbFill yo) s₀ fun s' => ∃ k, AbsMid s₀ W St C yo D n x k s' ∧
      ((x.length + k) % 16 = 0 ∨ k = n) := by
  have he := hp.env
  have hL := hp.lt
  have hyo : yo + 16 ≤ 80 := by rcases hp.hyo with h | h <;> omega
  have hlen := fun m p k => length_bytesAt' m p k
  unfold absorbFill
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero hp.r20 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨0, ⟨PK.refl _, Frame.refl _ _, by rw [hp.r18]; exact (BitVec.add_zero _).symm,
      by rw [hp.r19, Nat.sub_zero], ?_, Nat.zero_le _⟩, .inl (by omega)⟩
    simpa [bytesAt] using hp.abs
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    generalize hoo : x.length % 16 = o at ho
    have ho16 : o < 16 := by rw [← hoo]; exact Nat.mod_lt _ (by decide)
    unfold absorbHead
    refine WP.seq (WP.mono (minLen_wp s₀ (o := o) (n := n) (by rw [hp.r20, hoo]) hp.r19 ⟨by omega, by omega⟩ hL)
      fun s₁ ⟨r4₁, m₁, kp₁⟩ => ?_)
    generalize hff : min (16 - o) n = f at r4₁
    have hf1 : 1 ≤ f := by omega
    have hfo : o + f ≤ 16 := by omega
    have hfn : f ≤ n := by omega
    have pk₁ := PK.ofKeeps kp₁
    unfold headArgs
    refine WP.seq (wp_addi (by decide) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
      wp_add fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => WP.block_nil ?_)
    have pk₇ : PK s₁ s₇ := (PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
      ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇)))))
    have m₇ : s₇.mem = s₀.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    have g₁ : ∀ r, r ∉ VG.Proof.Gather.PPC64LE.copyRegs → s₁.gpr r = s₀.gpr r := kp₁.gpr
    have r18₁ := g₁ .r18 (by decide)
    have r19₁ := g₁ .r19 (by decide)
    have r20₁ := g₁ .r20 (by decide)
    have r15₁ := g₁ .r15 (by decide)
    have r9₇ : s₇.gpr .r9 = St + BitVec.ofNat 64 (32 + o) := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₂.other _ (by decide), r15₁, he.r15, r20₁, hp.r20, hoo, add_ofNat_add]
    have r3₇ : s₇.gpr .r3 = D := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), r18₁, hp.r18]
    have r4₇ : s₇.gpr .r4 = BitVec.ofNat 64 f := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), r4₁]
    have r18₇ : s₇.gpr .r18 = D + BitVec.ofNat 64 f := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₂.other _ (by decide), r18₁, hp.r18, r4₁]
    have r19₇ : s₇.gpr .r19 = BitVec.ofNat 64 (n - f) := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₂.other _ (by decide), r19₁, hp.r19, r4₁,
        Proof.AesGcm.PPC64LE.ofNat_sub_ofNat' hfn hL]
    have r20₇ : s₇.gpr .r20 = BitVec.ofNat 64 (o + f) := by
      rw [u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), r20₁, hp.r20, hoo, r4₁,
        ← BitVec.ofNat_add]
    have pk₀₇ : PK s₀ s₇ := pk₁.trans pk₇
    have hb : BytesPre s₇ D (St + BitVec.ofNat 64 (32 + o)) f := by
      refine ⟨r3₇, r9₇, r4₇, hf1, by omega, ?_, ?_, ?_⟩
      · have := hp.dCov (k := 0) (j := f) (by omega) pk₀₇
        rw [BitVec.add_zero] at this
        exact this
      · rw [pk₀₇.wr]; exact he.stIn (by omega)
      · exact (hp.dst.sub_left (Region.sub_prefix hfn)).sub_right (Offset.sub_base _ (by omega))
    refine WP.seq (WP.mono (copyBytes_wp s₇ hb) fun s₈ ⟨m₈, _, kp₈⟩ => ?_)
    have pk₈ : PK s₀ s₈ := pk₀₇.trans (PK.ofKeeps kp₈)
    have g₈ : ∀ r, r ∉ VG.Proof.Gather.PPC64LE.copyRegs → s₈.gpr r = s₇.gpr r := kp₈.gpr
    -- The memory after the copy.
    rw [m₇] at m₈
    generalize hd : bytesAt s₀.mem D f = d at m₈
    have hdl : d.length = f := by rw [← hd, hlen]
    have mem₈ : s₈.mem = writeBytes s₀.mem (bA St + BitVec.ofNat 64 o) d := by
      rw [m₈, show St + BitVec.ofNat 64 (32 + o) = bA St + BitVec.ofNat 64 o from
        (add_ofNat_add _ _ _).symm]
    have fr₈ : Frame (pieceRs W St) s₀.mem s₈.mem := by
      rw [mem₈]
      refine frame_pieces (Proof.AesGcm.writeBytes_frame' _ hdl) fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      rw [add_ofNat_add]; exact sub_st (by omega) W
    have hY : blockAt s₈.mem (yA St yo) = blockAt s₀.mem (yA St yo) := by
      rw [mem₈, add_ofNat_add]; exact keepY he hp.hyo _ (by omega)
    have hB : bytesAt s₈.mem (bA St) (o + f) = x.drop (whole x.length) ++ d := by
      rw [mem₈, ← hdl, Proof.AesGcm.bytesAt_writeBytes _ _ _ _ (by omega), ← hoo, hp.abs.2]
    have hk₈ : hk s₈.mem C = hk s₀.mem C := hk_keep he fr₈
    refine WP.seq (wp_subi (by decide) (by decide) fun s₉ u₉ => WP.block_nil ?_)
    have r5₉ : s₉.gpr .r5 = BitVec.ofNat 64 (o + f) - BitVec.ofNat 64 16 := by
      rw [u₉.gpr, g₈ _ (by decide), r20₇]
    have pk₉ : PK s₀ s₉ := pk₈.trans (PK.ofUpd u₉)
    have r18₉ : s₉.gpr .r18 = D + BitVec.ofNat 64 f := by rw [u₉.other _ (by decide), g₈ _ (by decide), r18₇]
    have r19₉ : s₉.gpr .r19 = BitVec.ofNat 64 (n - f) := by
      rw [u₉.other _ (by decide), g₈ _ (by decide), r19₇]
    have hal : (x ++ bytesAt s₀.mem D f).length = x.length + f := by rw [List.length_append, hlen]
    by_cases hfull : o + f = 16
    · -- The buffer is full: absorbed.
      have r5' : s₉.gpr .r5 = BitVec.ofNat 64 0 := by rw [r5₉, hfull]; exact sub16_full
      refine WP.ite true (by rw [eval_zero r5' (by decide)]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
      have he₉ := he.of_pk pk₉
      have hds : Region.Disjoint ⟨bA St, 16⟩ ⟨W, 256⟩ := by
        have := he.st_w (d := 32) (n := 16) (e := 0) (k := 256) (by decide) (by decide)
        rwa [BitVec.add_zero] at this
      have hyd : Region.Disjoint ⟨yA St yo, 16⟩ ⟨bA St, 16⟩ :=
        he.st_st (by rcases hp.hyo with h | h <;> omega) hyo (by decide)
      refine WP.mono (ghash1_wp he₉ hyo (b := .r15) (o := 32) (Db := bA St)
        (by rw [he₉.r15]) ⟨by decide, by decide, by decide⟩ (by decide) (he₉.stRd (by decide)) hyd hds) ?_
      intro s' g
      refine ⟨f, ⟨pk₉.trans g.pk, ?_, ?_, ?_, ?_, hfn⟩, .inl (by omega)⟩
      · refine Frame.trans (fr₈.trans (by rw [u₉.mem]; exact Frame.refl _ _))
          (frame_pieces g.frame fun r hr => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_st hyo W
        · exact sub_w0 (by decide) St
      · rw [g.args .r18 (by decide), r18₉]
      · rw [g.args .r19 (by decide), r19₉]
      · rw [hd]
        refine absorb_complete hp.abs (by rw [hdl]; omega) rfl ?_
        rw [g.y, u₉.mem, hY, hk₈]
        congr 2
        simp only [blockAt]
        rw [← hfull, hB]
    · -- Not full: all the data is in the buffer.
      have hnf : o + f < 16 := by omega
      have r5' : s₉.gpr .r5 = BitVec.ofNat 64 (2 ^ 64 + (o + f) - 16) := by rw [r5₉, sub16_lt hnf]
      refine WP.ite false (by rw [eval_zero r5' (by omega)]; congr 1; simp; omega)
        (fun h => absurd h (by decide)) (fun _ => ?_)
      have hfn' : f = n := by omega
      refine WP.block_nil ⟨f, ⟨pk₉, by rw [u₉.mem]; exact fr₈, r18₉, r19₉, ?_, hfn⟩, .inr hfn'⟩
      rw [hd]
      refine absorb_fill hp.abs (by rw [hdl]; omega) (by rw [u₉.mem, hY]) ?_
      rw [u₉.mem, hdl, hoo, hB, ← hoo, hp.abs.2]

/-- `absorb yo`: GHASH has absorbed the `n` bytes at `D` after `x`. -/
theorem absorb_wp : WP isa (absorb yo) s₀ (AbsPost s₀ W St C yo D n x) := by
  unfold absorb
  refine WP.ite (decide (n = 0)) (eval_zero hp.r19 hp.lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := of_decide_eq_true ht
    subst h0
    refine WP.block_nil ⟨PK.refl _, Frame.refl _ _, ?_⟩
    simpa [bytesAt] using hp.abs
  · have hn : n ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (fill_wp hp hn) fun s₁ ⟨k, hm, ha⟩ =>
      WP.seq (WP.mono (whole_wp hp hm ha) fun s₂ ⟨k', hm', hr, ha'⟩ => tail_wp hp hm' hr ha'))

end

end VG.Proof.AesGcm.PPC64LE
