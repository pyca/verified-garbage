module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-GCM on PPC64LE: padding and the lengths block (`flush`, `lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `r20`
buffered bytes with zeros in `T` (at `W + 2048`) and absorbs them
(`flush_wp`, by `absorb_pad`); `lens yo` absorbs the lengths block of `r21`
bytes of additional data and `r22` bytes of text (`lens_wp`), its two
halves stored big-endian with `stdbrx`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.Impl.AesGcm.PPC64LE VG.WriteBytes VG.Proof.Gcm
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_add wp_sub wp_lsr wp_lsl wp_and wp_std)
open VG.Proof.Gather.PPC64LE (Keeps eval_zero BytesPre copyBytes_wp)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom zeros padLen)
open VG.Spec.Aes (bytesAt)

/-- `T`, the block at `W + 2048`. -/
abbrev tA (W : Addr) : Addr := W + BitVec.ofNat 64 tO

/-- A frame within `T` is within the pieces' regions. -/
theorem sub_t {W : Addr} {d n : Nat} (hd : d + n ≤ 16) (St : Addr) :
    ∃ r' ∈ pieceRs W St, Region.Sub ⟨W + BitVec.ofNat 64 (tO + d), n⟩ r' :=
  sub_w (by unfold tO; omega) St

theorem tA_add (W : Addr) (d : Nat) : tA W + BitVec.ofNat 64 d = W + BitVec.ofNat 64 (tO + d) :=
  add_ofNat_add _ _ _

/-- The two zero doublewords of `T`. -/
theorem zeroT (m : Mem) (W : Addr) :
    (m.writeW (tA W) (BitVec.ofNat 64 0)).writeW (W + BitVec.ofNat 64 (tO + 8)) (BitVec.ofNat 64 0) =
      writeBytes m (tA W) (zeros 16) := by
  rw [← tA_add]; exact Proof.AesGcm.write_zeros16 m (tA W)

/-! ## `flush` -/

/-- What `flush yo` needs: GHASH has absorbed `x`, `x.length mod 16`
bytes buffered. -/
structure FlPre (s : State) (W St C : Addr) (yo : Nat) (x : List Byte) : Prop where
  env : Env s W St C
  hyo : yo = 0 ∨ yo = 16
  r20 : s.gpr .r20 = BitVec.ofNat 64 (x.length % 16)
  abs : Absorbed s.mem (yA St yo) (bA St) (hk s.mem C) x

/-- What a piece writing only the accumulator and `W` does to GHASH. -/
structure GhPost (s₀ : State) (W St C : Addr) (yo : Nat) (x : List Byte) (s : State) : Prop where
  pk : PK s₀ s
  args : ∀ r ∈ [Reg.r18, .r19, .r20], s.gpr r = s₀.gpr r
  frame : Frame (pieceRs W St) s₀.mem s.mem
  abs : Absorbed s.mem (yA St yo) (bA St) (hk s₀.mem C) x

theorem flush_wp {s : State} {W St C : Addr} {yo : Nat} {x : List Byte} (hp : FlPre s W St C yo x) :
    WP isa (flush yo) s (GhPost s W St C yo (x ++ zeros (padLen x.length))) := by
  have he := hp.env
  have hyo : yo + 16 ≤ 80 := by rcases hp.hyo with h | h <;> omega
  unfold flush
  refine WP.ite (decide (x.length % 16 = 0)) (eval_zero hp.r20 (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨PK.refl _, fun _ _ => rfl, Frame.refl _ _, ?_⟩
    rw [padLen_of_mod h0]
    simpa [zeros] using hp.abs
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    generalize hoo : x.length % 16 = o at ho
    have ho16 : o < 16 := by rw [← hoo]; exact Nat.mod_lt _ (by decide)
    unfold flushPre
    refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
    refine wp_std (a := tA W) (by decide) (by decide) (by rw [u₁.other _ (by decide), he.r14])
      (he.wIn (d := tO) (n := 8) (by decide) _ _ ⟨_, List.mem_singleton_self _,
        Region.contains_self _ _⟩ |> fun h => by rw [u₁.wr]; exact h) fun s₂ u₂ => ?_
    refine wp_std (a := W + BitVec.ofNat 64 (tO + 8)) (by decide) (by decide)
      (by rw [u₂.gpr, u₁.other _ (by decide), he.r14])
      (he.wIn (d := tO + 8) (n := 8) (by decide) _ _ ⟨_, List.mem_singleton_self _,
        Region.contains_self _ _⟩ |> fun h => by rw [u₂.wr, u₁.wr]; exact h) fun s₃ u₃ => ?_
    refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
      wp_mv fun s₆ u₆ => WP.block_nil ?_
    have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
    have r0₁ : s₁.gpr .r0 = BitVec.ofNat 64 0 := u₁.gpr
    have m₆ : s₆.mem = writeBytes s.mem (tA W) (zeros 16) := by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, r0₁, zeroT]
    have hb : BytesPre s₆ (bA St) (tA W) o := by
      refine ⟨?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_⟩
      · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), he.r15]
      · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), he.r14]
      · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), hp.r20, hoo]
      · rw [pk₆.rd, pk₆.wr]; exact he.stRd (by omega)
      · rw [pk₆.wr]; exact he.wIn (by unfold tO; omega)
      · exact he.st_w (by omega) (by unfold tO; omega)
    refine WP.seq (WP.mono (copyBytes_wp s₆ hb) fun s₇ ⟨m₇, _, kp₇⟩ => ?_)
    have pk₇ : PK s s₇ := pk₆.trans (PK.ofKeeps kp₇)
    have hB : bytesAt s₆.mem (bA St) o = bytesAt s.mem (bA St) o := by
      rw [m₆]
      exact Proof.Cmac.bytesAt_frame (Proof.AesGcm.writeBytes_frame' (n := 16) _ (by simp [zeros]))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact he.st_w (d := 32) (e := tO) (by omega) (by decide)) (by omega)
    generalize hxs : bytesAt s.mem (bA St) o = xs at hB
    have hxl : xs.length = o := by rw [← hxs, length_bytesAt']
    rw [hB, m₆] at m₇
    have frT : Frame [⟨tA W, 16⟩] s.mem s₇.mem := by
      rw [m₇]
      exact (Proof.AesGcm.writeBytes_frame' (n := 16) _ (by simp [zeros])).trans
        ((Proof.AesGcm.writeBytes_frame' _ hxl).sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
    have fr₇ : Frame (pieceRs W St) s.mem s₇.mem :=
      frame_pieces frT fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_w (by unfold tO; omega) St
    have hT : blockAt s₇.mem (tA W) = Spec.Gcm.ofBytes (xs ++ zeros (16 - o)) := by
      simp only [blockAt]; rw [m₇, Proof.AesGcm.bytesAt_pad _ _ _ (by omega), hxl]
    have hY : blockAt s₇.mem (yA St yo) = blockAt s.mem (yA St yo) := by
      simp only [blockAt]
      rw [Proof.Cmac.bytesAt_frame frT (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact he.st_w (d := yo) (e := tO) hyo (by decide)) (by decide)]
    have he₇ := he.of_pk pk₇
    have hds : Region.Disjoint ⟨tA W, 16⟩ ⟨W, 256⟩ := by
      have := he.w_w (d := tO) (n := 16) (e := 0) (k := 256) (.inr (by decide)) (by decide) (by decide)
      rwa [BitVec.add_zero] at this
    refine WP.mono (ghash1_wp he₇ hyo (b := .r14) (o := tO) (Db := tA W) (by rw [he₇.r14])
      ⟨by decide, by decide, by decide⟩ (by decide) (he₇.wRd (by decide))
      (he.st_w hyo (by decide)) hds) fun s' g => ⟨pk₇.trans g.pk, fun r hr => ?_, ?_, ?_⟩
    · have hn : r ∉ VG.Proof.Gather.PPC64LE.copyRegs ∧ r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r9 ∧ r ≠ .r4 := by
        revert r; decide
      rw [g.args r hr, kp₇.gpr r hn.1, u₆.other _ hn.2.2.2.2, u₅.other _ hn.2.2.2.1,
        u₄.other _ hn.2.2.1, u₃.gpr, u₂.gpr, u₁.other _ hn.2.1]
    · refine fr₇.trans (frame_pieces g.frame fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_st hyo W
      · exact sub_w0 (by decide) St
    · refine absorb_pad hp.abs (by omega) rfl ?_
      rw [g.y, hk_keep he fr₇, hY, hT, hoo, hxs]

/-! ## `lens` -/

theorem rev64_eq (w : BitVec 64) : rev64 w = byteRev64 w := rfl

/-- `8 x` modulo 2⁶⁴, stored byte-reversed, is `[8 x]₆₄`. -/
theorem le8_lsl3 {x : Nat} (hx : x < 2 ^ 64) :
    Proof.Cmac.le8 (rev64 (BitVec.ofNat 64 x <<< 3)) = Spec.Gcm.be64 (8 * x) := by
  rw [rev64_eq, le8_byteRev64]
  have : (BitVec.ofNat 64 x <<< 3).toNat = (8 * x) % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftLeft_eq,
      show 2 ^ 3 = 8 from rfl, Nat.mul_comm]
  rw [this, be64_mod]

/-- What `lens yo` needs: `a` and `c` in `r21` and `r22`. -/
structure LensPre (s : State) (W St C : Addr) (yo : Nat) (a c : Nat) : Prop where
  env : Env s W St C
  hyo : yo = 0 ∨ yo = 16
  r21 : s.gpr .r21 = BitVec.ofNat 64 a
  r22 : s.gpr .r22 = BitVec.ofNat 64 c
  ha : a < 2 ^ 64
  hc : c < 2 ^ 64

/-- What `lens yo` does: the lengths block absorbed into the accumulator. -/
structure LensPost (s₀ : State) (W St C : Addr) (yo : Nat) (a c : Nat) (s : State) : Prop where
  pk : PK s₀ s
  args : ∀ r ∈ [Reg.r18, .r19, .r20], s.gpr r = s₀.gpr r
  frame : Frame (pieceRs W St) s₀.mem s.mem
  y : blockAt s.mem (yA St yo) =
    ghashFrom (hk s₀.mem C) (blockAt s₀.mem (yA St yo)) [Spec.Gcm.ofBytes (lensBlock a c)]

theorem lens_wp {s : State} {W St C : Addr} {yo a c : Nat} (hp : LensPre s W St C yo a c) :
    WP isa (lens yo) s (LensPost s W St C yo a c) := by
  have he := hp.env
  have hyo : yo + 16 ≤ 80 := by rcases hp.hyo with h | h <;> omega
  unfold lens lensPre
  refine WP.seq (wp_lsl (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ =>
    wp_addi (by decide) (by decide) fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_li (by decide) fun s₅ u₅ => ?_)
  have r9₅ : s₅.gpr .r9 = tA W := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), he.r14]
  have pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans
    ((PK.ofUpd u₄).trans (PK.ofUpd u₅))))
  refine wp_stdbrx (ea := tA W) (by decide)
    (by rw [r9₅, u₅.other .r10 (by decide), u₄.gpr]; exact BitVec.add_zero _)
    (by rw [pk₅.wr]; exact he.wInR (d := tO) (n := 8) (by decide)) fun s₆ u₆ => ?_
  refine wp_stdbrx (ea := tA W + BitVec.ofNat 64 8) (by decide)
    (by rw [u₆.gpr, r9₅, u₅.gpr])
    (by rw [u₆.wr, pk₅.wr, tA_add]; exact he.wInR (d := tO + 8) (n := 8) (by decide))
    fun s₇ u₇ => WP.block_nil ?_
  have pk₇ : PK s s₇ := pk₅.trans ((PK.ofMupd u₆).trans (PK.ofMupd u₇))
  have r5₅ : s₅.gpr .r5 = BitVec.ofNat 64 a <<< 3 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hp.r21]
  have r6₅ : s₅.gpr .r6 = BitVec.ofNat 64 c <<< 3 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hp.r22]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hlb : (Spec.Gcm.be64 (8 * a)).length = 8 := length_be64 _
  have m₇ : s₇.mem = writeBytes s.mem (tA W) (lensBlock a c) := by
    rw [u₇.mem, u₆.gpr, u₆.mem, r5₅, r6₅, m₅, Proof.AesGcm.writeW64_eq, Proof.AesGcm.writeW64_eq,
      le8_lsl3 hp.ha, le8_lsl3 hp.hc, show tA W + BitVec.ofNat 64 8 =
        tA W + BitVec.ofNat 64 (Spec.Gcm.be64 (8 * a)).length by rw [hlb],
      writeBytes_append _ _ _ _ (by rw [hlb, length_be64]; decide)]
    rfl
  have frT : Frame [⟨tA W, 16⟩] s.mem s₇.mem := by
    rw [m₇]; exact Proof.AesGcm.writeBytes_frame' _ (length_lensBlock a c)
  have fr₇ : Frame (pieceRs W St) s.mem s₇.mem :=
    frame_pieces frT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_w (by unfold tO; omega) St
  have hT : blockAt s₇.mem (tA W) = Spec.Gcm.ofBytes (lensBlock a c) := by
    simp only [blockAt]
    rw [m₇, ← length_lensBlock a c,
      Proof.AesGcm.bytesAt_writeBytes_self _ _ _ (by rw [length_lensBlock]; decide)]
  have hY : blockAt s₇.mem (yA St yo) = blockAt s.mem (yA St yo) := by
    simp only [blockAt]
    rw [Proof.Cmac.bytesAt_frame frT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact he.st_w (d := yo) (e := tO) hyo (by decide)) (by decide)]
  have he₇ := he.of_pk pk₇
  have hds : Region.Disjoint ⟨tA W, 16⟩ ⟨W, 256⟩ := by
    have := he.w_w (d := tO) (n := 16) (e := 0) (k := 256) (.inr (by decide)) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  refine WP.mono (ghash1_wp he₇ hyo (b := .r14) (o := tO) (Db := tA W) (by rw [he₇.r14])
    ⟨by decide, by decide, by decide⟩ (by decide) (he₇.wRd (by decide))
    (he.st_w hyo (by decide)) hds) fun s' g => ⟨pk₇.trans g.pk, fun r hr => ?_, ?_, ?_⟩
  · have hn : r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by revert r; decide
    rw [g.args r hr, u₇.gpr, u₆.gpr, u₅.other _ hn.2.2.2.2, u₄.other _ hn.2.2.2.1, u₃.other _ hn.2.2.1,
      u₂.other _ hn.2.1, u₁.other _ hn.1]
  · refine fr₇.trans (frame_pieces g.frame fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_st hyo W
    · exact sub_w0 (by decide) St
  · rw [g.y, hk_keep he fr₇, hY, hT]

end VG.Proof.AesGcm.PPC64LE
