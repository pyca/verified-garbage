module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Flush
public import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on PPC64LE: counter mode on a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the `n` bytes
at `D` (`r18`, `r19`) with the keystream from byte `nc` on, the length of
the text so far (`nc mod 16` in `r20`), with the counter block at `St + 48`
and the keystream block at `St + 64` (`crypt_wp`): the rest of the current
keystream block (`head_wp`), whole blocks with `vg_aes_ctr32`
(`cwhole_wp`) and the last bytes with a new keystream block (`ctail_wp`), by
the steps of `Proof/Gcm/Ctr.lean`. Between them, `CrMid k` says the first
`k` bytes are done and the rest are as they were.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gcm
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_add wp_sub wp_lsr wp_lsl wp_and wp_std)
open VG.Proof.Gather.PPC64LE (Keeps eval_zero)
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 aesWith inc32)
open VG.Spec.Aes (bytesAt)

/-- The cipher of the key schedule at `C`, for `R` rounds. -/
abbrev cph (m : Mem) (C : Addr) (R : Nat) : Block → Block := aesWith R (bytesAt m C (16 * (R + 1)))

/-- The counter block and the keystream block. -/
abbrev cbA (St : Addr) : Addr := St + BitVec.ofNat 64 48
abbrev ksA (St : Addr) : Addr := St + BitVec.ofNat 64 64

/-- The regions `crypt` writes. -/
abbrev crRs (W St D : Addr) (n : Nat) : List Region := [stR St, wR W, ⟨D, n⟩]

theorem crRs_of_pieces {W St D : Addr} {n : Nat} {m m' : Mem} (h : Frame (pieceRs W St) m m') :
    Frame (crRs W St D n) m m' :=
  Frame.mono h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

/-- What `crypt` needs: the counter state after `nc` bytes of text, and the
`n` bytes at `D` writable and apart from `St`, `W` and the key context. -/
structure CrPre (s : State) (W St C : Addr) (R : Nat) (D : Addr) (n nc : Nat) (icb : Block) : Prop where
  env : Env s W St C
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  r17 : s.gpr .r17 = BitVec.ofNat 64 R
  r18 : s.gpr .r18 = D
  r19 : s.gpr .r19 = BitVec.ofNat 64 n
  r20 : s.gpr .r20 = BitVec.ofNat 64 (nc % 16)
  ctr : Ctr s.mem (cbA St) (ksA St) (cph s.mem C R) icb nc
  wd : Covers [⟨D, n⟩] s.wr
  dst : (⟨D, n⟩ : Region).Disjoint (stR St)
  dw : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩
  dc : (⟨D, n⟩ : Region).Disjoint (cR C)
  fit : D.toNat + n ≤ 2 ^ 64
  lt : n < 2 ^ 64

/-- After the first `k` bytes from `s₀`. -/
structure CrMid (s₀ : State) (W St C : Addr) (R : Nat) (D : Addr) (n nc : Nat) (icb : Block) (k : Nat)
    (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame (crRs W St D n) s₀.mem s.mem
  r18 : s.gpr .r18 = D + BitVec.ofNat 64 k
  r19 : s.gpr .r19 = BitVec.ofNat 64 (n - k)
  ctr : Ctr s.mem (cbA St) (ksA St) (cph s₀.mem C R) icb (nc + k)
  done : bytesAt s.mem D k = xorKs (cph s₀.mem C R) icb nc (bytesAt s₀.mem D k)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 k) (n - k) = bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k)
  le : k ≤ n

/-- What `crypt` does. -/
structure CrPost (s₀ : State) (W St C : Addr) (R : Nat) (D : Addr) (n nc : Nat) (icb : Block)
    (s : State) : Prop where
  pk : PK s₀ s
  frame : Frame (crRs W St D n) s₀.mem s.mem
  ctr : Ctr s.mem (cbA St) (ksA St) (cph s₀.mem C R) icb (nc + n)
  out : bytesAt s.mem D n = xorKs (cph s₀.mem C R) icb nc (bytesAt s₀.mem D n)

/-- Equal bytes split into equal parts. -/
theorem rest_split {m m₀ : Mem} {p : Addr} {a b : Nat} (h : bytesAt m p (a + b) = bytesAt m₀ p (a + b)) :
    bytesAt m p a = bytesAt m₀ p a ∧
      bytesAt m (p + BitVec.ofNat 64 a) b = bytesAt m₀ (p + BitVec.ofNat 64 a) b := by
  rw [Proof.AesGcm.bytesAt_add, Proof.AesGcm.bytesAt_add] at h
  exact List.append_inj h (by simp [length_bytesAt'])

section
variable {s₀ : State} {W St C : Addr} {R : Nat} {D : Addr} {n nc : Nat} {icb : Block}
  (hp : CrPre s₀ W St C R D n nc icb)
include hp

/-- The key schedule is kept. -/
theorem CrPre.key {m : Mem} (hf : Frame (crRs W St D n) s₀.mem m) : cph m C R = cph s₀.mem C R := by
  have hR : 16 * (R + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have hs : Region.Sub ⟨C, 16 * (R + 1)⟩ (cR C) := Region.sub_prefix (by omega)
  have hc0 := hp.env.cs
  simp only [cph]
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.env.cs.sub_left hs
    · exact (hp.env.cw.sub_left hs).sub_right (Region.sub_prefix (by decide))
    · exact (hp.dc.sub_left (Region.sub_prefix (Nat.le_refl _))).symm.sub_left hs) (by omega)]

/-- A block of `St` is kept by writes within the data. -/
theorem CrPre.stKeep {m m' : Mem} {k j : Nat} (hkj : k + j ≤ n)
    (hf : Frame [⟨D + BitVec.ofNat 64 k, j⟩] m m') {d : Nat} (hd : d + 16 ≤ 80) :
    blockAt m' (St + BitVec.ofNat 64 d) = blockAt m (St + BitVec.ofNat 64 d) := by
  simp only [blockAt]
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hp.dst.sub_left (Offset.sub_base _ hkj)).sub_right (Offset.sub_base _ hd)).symm) (by decide)]

/-- The counter state is kept by writes within the data. -/
theorem CrPre.ctrKeep {m m' : Mem} {k j : Nat} (hkj : k + j ≤ n)
    (hf : Frame [⟨D + BitVec.ofNat 64 k, j⟩] m m') {ciph : Block → Block} {c : Nat}
    (h : Ctr m (cbA St) (ksA St) ciph icb c) : Ctr m' (cbA St) (ksA St) ciph icb c :=
  h.congr (hp.stKeep hkj hf (by decide)) (hp.stKeep hkj hf (by decide))

/-- Data bytes are kept by writes within `St` and `W`. -/
theorem CrPre.dataKeep {m m' : Mem} (hf : Frame (pieceRs W St) m m') {k j : Nat} (hkj : k + j ≤ n) :
    bytesAt m' (D + BitVec.ofNat 64 k) j = bytesAt m (D + BitVec.ofNat 64 k) j := by
  have hs : Region.Sub ⟨D + BitVec.ofNat 64 k, j⟩ ⟨D, n⟩ := Offset.sub_base _ hkj
  exact bytesAt_keep hf (hp.dst.sub_left hs) (hp.dw.sub_left hs) (by have := hp.lt; omega)

theorem CrPre.dW {k j : Nat} (hkj : k + j ≤ n) {s : State} (hk : PK s₀ s) :
    Covers [⟨D + BitVec.ofNat 64 k, j⟩] s.wr := by
  rw [hk.wr]; exact VG.Proof.Gather.PPC64LE.covers_off hp.wd hkj hp.lt

omit hp in
/-- A write of `j` bytes at `D + k` stays within the data. -/
theorem crSub {k j : Nat} (hkj : k + j ≤ n) {m m' : Mem}
    (hf : Frame [⟨D + BitVec.ofNat 64 k, j⟩] m m') : Frame (crRs W St D n) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, Offset.sub_base _ hkj⟩

/-- The `k` bytes done are kept by a write after them. -/
theorem CrPre.doneKeep {m m' : Mem} {k j : Nat} (hkj : k + j ≤ n)
    (hf : Frame [⟨D + BitVec.ofNat 64 k, j⟩] m m') : bytesAt m' D k = bytesAt m D k :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.base_disjoint D (Nat.le_refl _) (by have := hp.fit; have := hp.lt; omega))
    (by have := hp.lt; omega)

omit hp in
/-- The `k` bytes done, then `e`, the encryption of the next. -/
theorem crOut {k j : Nat} (hkj : k + j = n) {m : Mem}
    (hd : bytesAt m D k = xorKs (cph s₀.mem C R) icb nc (bytesAt s₀.mem D k))
    (he : bytesAt m (D + BitVec.ofNat 64 k) j =
      xorKs (cph s₀.mem C R) icb (nc + k) (bytesAt s₀.mem (D + BitVec.ofNat 64 k) j)) :
    bytesAt m D n = xorKs (cph s₀.mem C R) icb nc (bytesAt s₀.mem D n) := by
  rw [← hkj, ← bytesAt_split, ← bytesAt_split, hd, he, xorKs_append, length_bytesAt']

/-- The last `n - k` (fewer than 16) bytes, with a new keystream block, once
the first `k` are done to a whole number of blocks (or are all the data). -/
theorem ctail_wp {k : Nat} {s : State} (hm : CrMid s₀ W St C R D n nc icb k s) (hr : n - k < 16)
    (ha : (nc + k) % 16 = 0 ∨ k = n) :
    WP isa cryptTail s (CrPost s₀ W St C R D n nc icb) := by
  have he := hp.env.of_pk hm.pk
  have hle := hm.le
  have hL := hp.lt
  unfold cryptTail
  refine WP.ite (decide (n - k = 0)) (eval_zero hm.r19 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have hk : k = n := by have := of_decide_eq_true ht; omega
    subst hk
    exact WP.block_nil ⟨hm.pk, hm.frame, hm.ctr, hm.done⟩
  have hk0 : n - k ≠ 0 := by simpa using hf
  have hal : (nc + k) % 16 = 0 := ha.resolve_right (by omega)
  unfold tailArgs
  refine WP.seq (WP.seq (wp_li (by decide) fun s₁ u₁ => ?_))
  refine wp_std (a := ksA St) (by decide) (by decide) (by rw [u₁.other _ (by decide), he.r15])
    (by rw [u₁.wr]; exact he.stInR (d := 64) (n := 8) (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := St + BitVec.ofNat 64 72) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), he.r15])
    (by rw [u₂.wr, u₁.wr]; exact he.stInR (d := 72) (n := 8) (by decide)) fun s₃ u₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ =>
    wp_addi (by decide) (by decide) fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ =>
    WP.block_nil ?_
  have pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans
    ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans
    ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have m₉ : s₉.mem = writeBytes s.mem (ksA St) (Spec.Gcm.zeros 16) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr,
      show St + BitVec.ofNat 64 72 = ksA St + BitVec.ofNat 64 8 by rw [add_ofNat_add]]
    exact Proof.AesGcm.write_zeros16 _ _
  have frZ : Frame [⟨ksA St, 16⟩] s.mem s₉.mem := by
    rw [m₉]; exact Proof.AesGcm.writeBytes_frame' _ (by simp [Spec.Gcm.zeros])
  have g9 : ∀ r, r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r7, .r8] → s₉.gpr r = s.gpr r := fun r hr => by
    have hn : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 := by
      simpa using hr
    rw [u₉.other _ hn.2.2.2.2.2.2, u₈.other _ hn.2.2.2.2.2.1, u₇.other _ hn.2.2.2.2.1,
      u₆.other _ hn.2.2.2.1, u₅.other _ hn.2.2.1, u₄.other _ hn.2.1, u₃.gpr, u₂.gpr, u₁.other _ hn.1]
  have r17 : s.gpr .r17 = BitVec.ofNat 64 R := by rw [hm.pk.gpr .r17 (by decide), hp.r17]
  have hcp : CtrPre s₉ C R (cbA St) (ksA St) W 1 := by
    have cc : Region.Disjoint ⟨C, 240⟩ ⟨cbA St, 16⟩ := by
      have := he.c_st (d := 0) (n := 240) (e := 48) (k := 16) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    have cd : Region.Disjoint ⟨C, 240⟩ ⟨ksA St, 16 * 1⟩ := by
      have := he.c_st (d := 0) (n := 240) (e := 64) (k := 16 * 1) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hp.rounds, by omega, cc, cd, ?_,
      he.st_st (d := 48) (n := 16) (e := 64) (k := 16 * 1) (by omega) (by decide) (by decide), ?_, ?_,
      by rw [he.stToNat (by decide)]; have := he.sfit; omega, ?_, ?_⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), he.r16]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), r17]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), he.r15]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), he.r15]
    · rw [u₉.other _ (by decide), u₈.gpr]
    · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), he.r14]
    · have := he.c_w (d := 0) (n := 240) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · have := he.st_w (d := 48) (n := 16) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · have := he.st_w (d := 64) (n := 16 * 1) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · rw [pk₉.rd, pk₉.wr]
      refine Covers.append_left ?_ (Covers.cons (he.stRd (by decide))
        (Covers.pair (he.stRd (by decide)) ?_))
      · have := he.cIn (d := 0) (n := 240) (by decide); simpa only [BitVec.add_zero] using this
      · have := he.wRd (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
    · rw [pk₉.wr]
      refine Covers.cons (he.stIn (by decide)) (Covers.pair (he.stIn (by decide)) ?_)
      have := he.wIn (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
  refine WP.mono (ctr_call hcp) fun s₁₀ ⟨ck, hd₁₀, hc₁₀⟩ => ?_
  -- What the call leaves.
  have fr₁₀ : Frame (pieceRs W St) s.mem s₁₀.mem := by
    refine Frame.trans (frame_pieces frZ fun r hr => ?_) (frame_pieces ck.frame fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact sub_st (by decide) W
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_st (by decide) W
      · exact sub_st (by decide) W
      · exact sub_w0 (by decide) St
  have frs₉ : Frame (crRs W St D n) s₀.mem s₉.mem :=
    hm.frame.trans (crRs_of_pieces (frame_pieces frZ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_st (by decide) W))
  have key₉ : aesWith R (bytesAt s₉.mem C (16 * (R + 1))) = cph s₀.mem C R := hp.key frs₉
  have z₉ : blockAt s₉.mem (ksA St) = 0 := by
    have h16 := Proof.AesGcm.bytesAt_writeBytes_self s.mem (ksA St) (Spec.Gcm.zeros 16) (by decide)
    rw [show (Spec.Gcm.zeros 16).length = 16 from rfl] at h16
    simp only [blockAt]
    rw [m₉, h16]
    exact ofBytes_zeros16
  have cb₉ : blockAt s₉.mem (cbA St) = blockAt s.mem (cbA St) := by
    simp only [blockAt]
    rw [Proof.Cmac.bytesAt_frame frZ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.st_st (d := 48) (n := 16) (e := 64) (k := 16) (by omega) (by decide) (by decide))
      (by decide)]
  have hk₁₀ : blockAt s₁₀.mem (ksA St) = cph s₀.mem C R (blockAt s.mem (cbA St)) := by
    rw [blocksAt_one, blocksAt_one, z₉, key₉, cb₉] at hd₁₀
    simp only [ctr32, Spec.Gcm.keystream, List.range_one, List.map_cons, List.map_nil,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.length_singleton, List.cons.injEq,
      and_true] at hd₁₀
    rw [hd₁₀]; exact BitVec.zero_xor
  have hc' : blockAt s₁₀.mem (cbA St) = inc32 (blockAt s.mem (cbA St)) := by rw [hc₁₀, cb₉]; rfl
  have r18₁₀ : s₁₀.gpr .r18 = D + BitVec.ofNat 64 k := by
    rw [ck.saved .r18 (by decide), g9 _ (by decide), hm.r18]
  have r19₁₀ : s₁₀.gpr .r19 = BitVec.ofNat 64 (n - k) := by
    rw [ck.saved .r19 (by decide), g9 _ (by decide), hm.r19]
  have pk₁₀ : PK s₀ s₁₀ := hm.pk.trans (pk₉.trans (PK.ofCall ck))
  have he₁₀ := hp.env.of_pk pk₁₀
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁₁ u₁₁ => wp_mv fun s₁₂ u₁₂ => wp_mv fun s₁₃ u₁₃ =>
    WP.block_nil ?_)
  have pk₁₃ : PK s₁₀ s₁₃ := (PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans (PK.ofUpd u₁₃))
  have m₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hx : XorPre s₁₃ (ksA St) (D + BitVec.ofNat 64 k) (n - k) := by
    refine ⟨?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_⟩
    · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, he₁₀.r15]
    · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), r18₁₀]
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), r19₁₀]
    · rw [pk₁₃.rd, pk₁₃.wr]; exact he₁₀.stRd (by omega)
    · exact hp.dW (by omega) (pk₁₀.trans pk₁₃)
    · exact ((hp.dst.sub_left (Offset.sub_base _ (by omega))).sub_right
        (Offset.sub_base _ (by omega))).symm
  refine WP.mono (xorBytes_wp s₁₃ hx) fun s' ⟨m', _, kx⟩ => ?_
  have hdk : bytesAt s₁₀.mem (D + BitVec.ofNat 64 k) (n - k) = bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k) := by
    rw [hp.dataKeep fr₁₀ (by omega), hm.rest]
  rw [m₁₃, hdk] at m'
  generalize hd : bytesAt s₀.mem (D + BitVec.ofNat 64 k) (n - k) = d at m' hdk
  have hdl : d.length = n - k := by rw [← hd, length_bytesAt']
  obtain ⟨hz, hctr⟩ := ctr_tail hm.ctr hal hk₁₀ hc' (d := d) (by omega) (by omega)
  rw [hdl] at hz hctr
  have hxl : (xorL d (bytesAt s₁₀.mem (ksA St) (n - k))).length = n - k := by
    simp [hdl, length_bytesAt']
  have frW : Frame [⟨D + BitVec.ofNat 64 k, n - k⟩] s₁₀.mem s'.mem := by
    rw [m']; exact Proof.AesGcm.writeBytes_frame' _ hxl
  refine ⟨pk₁₀.trans (pk₁₃.trans (PK.ofKeeps kx)), ?_, ?_, ?_⟩
  · exact frs₉.trans ((crRs_of_pieces (frame_pieces ck.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_st (by decide) W
      · exact sub_st (by decide) W
      · exact sub_w0 (by decide) St)).trans (crSub (by omega) frW))
  · have := hp.ctrKeep (by omega) frW hctr
    rwa [show nc + k + (n - k) = nc + n by omega] at this
  · refine crOut (Nat.add_sub_cancel' hle) ?_ ?_
    · rw [hp.doneKeep (by omega) frW]
      have := hp.dataKeep fr₁₀ (k := 0) (j := k) (by omega)
      simp only [BitVec.add_zero] at this
      rw [this, hm.done]
    · have hw := Proof.AesGcm.bytesAt_writeBytes_self s₁₀.mem (D + BitVec.ofNat 64 k)
        (xorL d (bytesAt s₁₀.mem (ksA St) (n - k))) (by rw [hxl]; omega)
      rw [hxl] at hw
      rw [m', hw, hd]
      exact hz

/-- The whole blocks of what is left, by `vg_aes_ctr32`, once the first `k`
bytes are done to a whole number of blocks (or are all the data). -/
theorem cwhole_wp {k : Nat} {s : State} (hm : CrMid s₀ W St C R D n nc icb k s)
    (ha : (nc + k) % 16 = 0 ∨ k = n) :
    WP isa cryptWhole s fun s' => ∃ k', CrMid s₀ W St C R D n nc icb k' s' ∧ n - k' < 16 ∧
      ((nc + k') % 16 = 0 ∨ k' = n) := by
  have he := hp.env.of_pk hm.pk
  have hL := hp.lt
  have hle := hm.le
  unfold cryptWhole splitCtr
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_li (by decide) fun s₅ u₅ => wp_and fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans
    ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r7₁ : s₁.gpr .r7 = BitVec.ofNat 64 ((n - k) / 16) := by
    rw [u₁.gpr, hm.r19, Proof.AesGcm.PPC64LE.ofNat_lsr4 (by omega)]
  have r7₆ : s₆.gpr .r7 = BitVec.ofNat 64 ((n - k) / 16) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), r7₁]
  have r8₂ : s₂.gpr .r8 = BitVec.ofNat 64 (16 * ((n - k) / 16)) := by
    rw [u₂.gpr, r7₁, ofNat_shl4 (by omega)]
  have r6₆ : s₆.gpr .r6 = D + BitVec.ofNat 64 k := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hm.r18]
  have r18₆ : s₆.gpr .r18 = D + BitVec.ofNat 64 (k + 16 * ((n - k) / 16)) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide),
      r8₂, u₂.other _ (by decide), u₁.other _ (by decide), hm.r18, add_ofNat_add]
  have r19₆ : s₆.gpr .r19 = BitVec.ofNat 64 (n - (k + 16 * ((n - k) / 16))) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hm.r19, ofNat_and15 (by omega)]
    congr 1; omega
  refine WP.ite (decide ((n - k) / 16 = 0)) (eval_zero r7₆ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (n - k) / 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨k, ⟨hm.pk.trans pk₆, by rw [m₆]; exact hm.frame, by rw [r18₆, h0, Nat.mul_zero,
      Nat.add_zero], by rw [r19₆, h0, Nat.mul_zero, Nat.add_zero], by rw [m₆]; exact hm.ctr,
      by rw [m₆]; exact hm.done, by rw [m₆]; exact hm.rest, hm.le⟩, by omega, ha⟩
  have h0 : (n - k) / 16 ≠ 0 := by simpa using hf
  have hal : (nc + k) % 16 = 0 := ha.resolve_right (by omega)
  generalize hnb : (n - k) / 16 = nb at r7₆ r18₆ r19₆ h0
  have hnb' : 16 * nb ≤ n - k := by rw [← hnb]; omega
  refine WP.seq (wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_addi (by decide) (by decide) fun s₉ u₉ =>
    wp_mv fun s₁₀ u₁₀ => WP.block_nil ?_)
  have pk₁₀ : PK s₆ s₁₀ := (PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 k, 16 * nb⟩ ⟨D, n⟩ := Offset.sub_base _ (by omega)
  have pk₀ : PK s₀ s₁₀ := hm.pk.trans (pk₆.trans pk₁₀)
  have hcp : CtrPre s₁₀ C R (cbA St) (D + BitVec.ofNat 64 k) W nb := by
    have cc : Region.Disjoint ⟨C, 240⟩ ⟨cbA St, 16⟩ := by
      have := he.c_st (d := 0) (n := 240) (e := 48) (k := 16) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hp.rounds, by omega, cc, ?_, ?_, ?_, ?_, ?_,
      by have := hp.fit; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
        pk₆.gpr .r16 (by decide), he.r16]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
        pk₆.gpr .r17 (by decide), hm.pk.gpr .r17 (by decide), hp.r17]
    · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        pk₆.gpr .r15 (by decide), he.r15]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        r6₆]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        r7₆]
    · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        pk₆.gpr .r14 (by decide), he.r14]
    · exact ((hp.dc.sub_left hsub).sub_right (Region.sub_prefix (by decide))).symm
    · have := he.c_w (d := 0) (n := 240) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · exact ((hp.dst.sub_left hsub).sub_right (Offset.sub_base _ (by decide))).symm
    · have := he.st_w (d := 48) (n := 16) (e := 0) (k := 2048) (by decide) (by decide)
      simpa only [BitVec.add_zero] using this
    · exact (hp.dw.sub_left hsub).sub_right (Region.sub_prefix (by decide))
    · rw [pk₁₀.rd, pk₁₀.wr, pk₆.rd, pk₆.wr]
      refine Covers.append_left ?_ (Covers.cons (he.stRd (by decide))
        (Covers.pair (VG.Covers.right (hp.dW (by omega) hm.pk)) ?_))
      · have := he.cIn (d := 0) (n := 240) (by decide); simpa only [BitVec.add_zero] using this
      · have := he.wRd (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
    · rw [pk₁₀.wr, pk₆.wr]
      refine Covers.cons (he.stIn (by decide)) (Covers.pair (hp.dW (by omega) hm.pk) ?_)
      have := he.wIn (d := 0) (n := 2048) (by decide); simpa only [BitVec.add_zero] using this
  refine WP.mono (ctr_call hcp) fun s' ⟨ck, hd', hc'⟩ => ?_
  have frs : Frame (crRs W St D n) s₀.mem s₁₀.mem := by rw [m₁₀]; exact hm.frame
  have hkey := hp.key frs
  simp only [cph] at hkey
  rw [hkey, m₁₀] at hd'
  rw [m₁₀] at hc'
  obtain ⟨hx, hctr⟩ := ctr_whole hm.ctr hal hd' hc'
  have frC : Frame (crRs W St D n) s.mem s'.mem := by
    rw [← m₁₀]
    refine ck.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR St, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, hsub⟩
    · exact ⟨wR W, by simp, Region.sub_prefix (by decide)⟩
  -- Data outside the blocks is kept by the call.
  have keepD : ∀ {a j : Nat}, a + j ≤ n → (a + j ≤ k ∨ k + 16 * nb ≤ a) →
      bytesAt s'.mem (D + BitVec.ofNat 64 a) j = bytesAt s.mem (D + BitVec.ofNat 64 a) j := by
    intro a j haj hout
    rw [← m₁₀]
    have hs : Region.Sub ⟨D + BitVec.ofNat 64 a, j⟩ ⟨D, n⟩ := Offset.sub_base _ haj
    refine Proof.Cmac.bytesAt_frame ck.frame (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.dst.sub_left hs).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.disjoint _ (by omega) (by have := hp.fit; omega) (by have := hp.fit; omega)
    · exact (hp.dw.sub_left hs).sub_right (Region.sub_prefix (by decide))
  obtain ⟨rA, rB⟩ := rest_split (a := 16 * nb) (b := n - (k + 16 * nb))
    (by simpa only [show 16 * nb + (n - (k + 16 * nb)) = n - k by omega] using hm.rest)
  rw [add_ofNat_add] at rB
  refine ⟨k + 16 * nb, ⟨pk₀.trans (PK.ofCall ck), hm.frame.trans frC, ?_, ?_, ?_, ?_, ?_, by omega⟩,
    by omega, .inl (by omega)⟩
  · rw [ck.saved .r18 (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), r18₆]
  · rw [ck.saved .r19 (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), r19₆]
  · rwa [Nat.add_assoc] at hctr
  · refine crOut (n := k + 16 * nb) rfl ?_ ?_
    · have := keepD (a := 0) (j := k) (by omega) (.inl (by omega))
      simp only [BitVec.add_zero] at this
      rw [this, hm.done]
    · rw [hx, rA]
  · rw [keepD (by omega) (.inr (by omega)), rB]

/-- The rest of the current keystream block first, if the text so far ends
within a block (`o = nc mod 16`): then the first `k` bytes are done, to a
whole number of blocks or all the data. -/
theorem head_wp (hn : n ≠ 0) :
    WP isa cryptFill s₀ fun s' => ∃ k, CrMid s₀ W St C R D n nc icb k s' ∧
      ((nc + k) % 16 = 0 ∨ k = n) := by
  have he := hp.env
  have hL := hp.lt
  unfold cryptFill
  refine WP.ite (decide (nc % 16 = 0)) (eval_zero hp.r20 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nc % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨0, ⟨PK.refl _, Frame.refl _ _, by rw [hp.r18]; exact (BitVec.add_zero _).symm,
      by rw [hp.r19, Nat.sub_zero], hp.ctr, by simp [bytesAt, xorKs], by rw [BitVec.add_zero], Nat.zero_le _⟩,
      .inl (by omega)⟩
  have ho : nc % 16 ≠ 0 := by simpa using hf
  generalize hoo : nc % 16 = o at ho
  have ho16 : o < 16 := by rw [← hoo]; exact Nat.mod_lt _ (by decide)
  unfold cryptHead
  refine WP.seq (WP.mono (minLen_wp s₀ (o := o) (n := n) (by rw [hp.r20, hoo]) hp.r19 ⟨by omega, by omega⟩ hL)
    fun s₁ ⟨r4₁, m₁, kp₁⟩ => ?_)
  generalize hff : min (16 - o) n = f at r4₁
  have hf1 : 1 ≤ f := by omega
  have hfo : o + f ≤ 16 := by omega
  have hfn : f ≤ n := by omega
  have pk₁ := PK.ofKeeps kp₁
  have g₁ : ∀ r, r ∉ VG.Proof.Gather.PPC64LE.copyRegs → s₁.gpr r = s₀.gpr r := kp₁.gpr
  refine WP.seq (wp_addi (by decide) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_add fun s₅ u₅ => wp_sub fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s₀ s₆ := pk₁.trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : s₆.mem = s₀.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hx : XorPre s₆ (St + BitVec.ofNat 64 (64 + o)) D f := by
    refine ⟨?_, ?_, ?_, hf1, by omega, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
        u₂.other _ (by decide), g₁ _ (by decide), g₁ _ (by decide), he.r15, hp.r20, hoo, add_ofNat_add]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide), hp.r18]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), r4₁]
    · rw [pk₆.rd, pk₆.wr]; exact he.stRd (by omega)
    · have := hp.dW (k := 0) (j := f) (by omega) pk₆
      rw [BitVec.add_zero] at this
      exact this
    · exact ((hp.dst.sub_left (Region.sub_prefix hfn)).sub_right (Offset.sub_base _ (by omega))).symm
  refine WP.mono (xorBytes_wp s₆ hx) fun s' ⟨m', _, kx⟩ => ?_
  rw [m₆] at m'
  generalize hd : bytesAt s₀.mem D f = d at m'
  have hdl : d.length = f := by rw [← hd, length_bytesAt']
  have hks : St + BitVec.ofNat 64 (64 + o) = ksA St + BitVec.ofNat 64 (nc % 16) := by
    rw [hoo, add_ofNat_add]
  have hz := ctr_head hp.ctr (by omega) (d := d) (by omega)
  rw [hdl, ← hks] at hz
  have hxl : (xorL d (bytesAt s₀.mem (St + BitVec.ofNat 64 (64 + o)) f)).length = f := by
    simp [hdl, length_bytesAt']
  have frW : Frame [⟨D + BitVec.ofNat 64 0, f⟩] s₀.mem s'.mem := by
    rw [m', BitVec.add_zero]; exact Proof.AesGcm.writeBytes_frame' _ hxl
  have r18' : s'.gpr .r18 = D + BitVec.ofNat 64 f := by
    rw [kx.gpr _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide), hp.r18, r4₁]
  have r19' : s'.gpr .r19 = BitVec.ofNat 64 (n - f) := by
    rw [kx.gpr _ (by decide), u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hp.r19, r4₁,
      Proof.AesGcm.PPC64LE.ofNat_sub_ofNat' hfn hL]
  refine ⟨f, ⟨pk₆.trans (PK.ofKeeps kx), crSub (by omega) frW, r18', r19', ?_, ?_, ?_, hfn⟩, ?_⟩
  · exact hp.ctrKeep (k := 0) (by omega) frW (Ctr.head hp.ctr (by omega) (by omega))
  · have hw := Proof.AesGcm.bytesAt_writeBytes_self s₀.mem D
      (xorL d (bytesAt s₀.mem (St + BitVec.ofNat 64 (64 + o)) f)) (by rw [hxl]; omega)
    rw [hxl] at hw
    rw [m', hw, hd]
    exact hz
  · refine Proof.Cmac.bytesAt_frame frW (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    rw [BitVec.add_zero]
    exact (Offset.base_disjoint D (Nat.le_refl f) (by have := hp.fit; omega)).symm
  · by_cases h16 : o + f = 16
    · left; omega
    · right; omega

/-- `crypt`: the `n` bytes at `D` XORed with the keystream from byte `nc` on. -/
theorem crypt_wp : WP isa crypt s₀ (CrPost s₀ W St C R D n nc icb) := by
  unfold crypt
  refine WP.ite (decide (n = 0)) (eval_zero hp.r19 hp.lt) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := of_decide_eq_true ht
    subst h0
    exact WP.block_nil ⟨PK.refl _, Frame.refl _ _, hp.ctr, by simp [bytesAt, xorKs]⟩
  · have hn : n ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (head_wp hp hn) fun s₁ ⟨k, hm, ha⟩ =>
      WP.seq (WP.mono (cwhole_wp hp hm ha) fun s₂ ⟨k', hm', hr, ha'⟩ => ctail_wp hp hm' hr ha'))

end

end VG.Proof.AesGcm.PPC64LE
